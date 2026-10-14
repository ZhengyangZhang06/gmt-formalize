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

/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
/-- **Integrability of the action integrand** (Simon Ch. 6, 3.1 (‡)).  For an integer
multiplicity triple `R = (C, θ, ξ)` in `U` and `ω ∈ 𝒟ⁿ(U)`, `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is
`Hⁿ⌞C`-integrable: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal `Hⁿ`-a.e. on `C`, so
`|⟨α, ξ(x)⟩| ≤ ‖α‖`, and the integrand is dominated by `B θ 1_{spt ω}` (`B` a bound for `‖ω‖`),
which is integrable because `spt ω` is a compact subset of `U` and `∫_{C ∩ K} θ dHⁿ < ∞` for
such `K`. -/
theorem Submission.regcomp_rim_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  set K : Set (Euclid P) := tsupport f
  /- Step 1: `ω` is continuous, bounded by some `B`, and vanishes off the compact set
  `K = spt ω ⊆ U`. -/
  have hcont : Continuous f := hsmooth.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
  /- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal gives `|⟨α, ξ(x)⟩| = |α(τ)| ≤ ‖α‖`
  for `Hⁿ`-a.e. `x ∈ C`. -/
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      ‖R.orient x α‖ ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hor⟩ := hx
    have hατ : ‖α τ‖ ≤ ‖α‖ := by
      simpa [hτ.norm_eq_one] using α.le_opNorm τ
    rcases hor with h | h
    · rw [h]
      exact hατ
    · rw [h, norm_neg]
      exact hατ
  /- Step 3: the integrand is a.e. strongly measurable (evaluation is continuous). -/
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hev : AEStronglyMeasurable (fun x => R.orient x (f x)) (μHE[n].restrict R.carrier) :=
    happly.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable)
  have hF : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (f x))
      (μHE[n].restrict R.carrier) := hθm.aestronglyMeasurable.mul hev
  /- Step 4: `B θ 1_K` is integrable, since `∫_{C ∩ K} θ dHⁿ < ∞`. -/
  have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) K (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hKm, inter_comm]
    simpa only [Real.enorm_natCast] using (R.locallyIntegrable_mult K hcpt hU).lt_top
  have hg : Integrable (fun x => B * K.indicator (fun x => (R.mult x : ℝ)) x)
      (μHE[n].restrict R.carrier) := (hθK.integrable_indicator hKm).const_mul B
  /- Step 5: `|θ ⟨ω, ξ⟩| ≤ B θ 1_K` a.e. on `C`. -/
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (f x)‖ ≤ B * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (f x)).trans (hB x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
      simp
  /- Step 6: dominated by an integrable function. -/
  exact hg.mono' hF hbound
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
/-- **`C¹` cut-off of a chart**: if `ψ` is `C¹` on an open `V ⊆ ℝᵐ` and `v₀ ∈ V`, then `ψ`
agrees on some ball `B_ρ(v₀) ⊆ V` with a map `g` that is `C¹` on all of `ℝᵐ`.  Take
`B_ε(v₀) ⊆ V`, a smooth bump `φ` with `φ = 1` on `B̄_{ε/4}(v₀)` and `φ = 0` off `B_{ε/2}(v₀)`,
`g = φ ψ` and `ρ = ε/4`.  At points of `B_ε(v₀) ⊆ V`, `g` is a product of `C¹` maps; at points
with `|v − v₀| ≥ ε`, `g` vanishes on the neighbourhood `{w : |w − v₀| > ε/2}`. -/
theorem Submission.codim1_ac_sat_c1_local_extension : ∀ (P m : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (v₀ : Euclid m), IsOpen V → ContDiffOn ℝ 1 ψ V → v₀ ∈ V → ∃ (g : Euclid m → Euclid P) (ρ : ℝ), 0 < ρ ∧ ball v₀ ρ ⊆ V ∧ ContDiff ℝ 1 g ∧ EqOn g ψ (ball v₀ ρ) := by
  intro P m V ψ v₀ hV hψ hv₀
  -- Step 1: `B_ε(v₀) ⊆ V`
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV v₀ hv₀
  -- Step 2: a smooth bump `φ` with `φ = 1` on `B̄_{ε/4}(v₀)` and `φ = 0` off `B_{ε/2}(v₀)`
  let φ : ContDiffBump v₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  -- Step 3: `g = φ ψ` and `ρ = ε / 4`, so `B_ρ(v₀) ⊆ B_ε(v₀) ⊆ V`
  refine ⟨fun v => φ v • ψ v, ε / 4, by positivity,
    (ball_subset_ball (by linarith)).trans hεV, ?_, fun v hv => ?_⟩
  · -- Step 5: `g` is `C¹` at every point `v`
    refine contDiff_iff_contDiffAt.mpr fun v => ?_
    by_cases hv : dist v v₀ < ε
    · -- (a) `v ∈ B_ε(v₀) ⊆ V`: `φ` and `ψ` are `C¹` at `v`
      exact (φ.contDiffAt (n := 1)).smul (hψ.contDiffAt (hV.mem_nhds (hεV (mem_ball.mpr hv))))
    · -- (b) `|v − v₀| ≥ ε`: `g = 0` on the neighbourhood `{w : |w − v₀| > ε/2}` of `v`
      have hO : ∀ᶠ w in 𝓝 v, ε / 2 < dist w v₀ :=
        continuousAt_const.eventually_lt (continuous_id.dist continuous_const).continuousAt
          (by linarith [not_lt.mp hv])
      refine (contDiffAt_const (c := (0 : Euclid P))).congr_of_eventuallyEq ?_
      filter_upwards [hO] with w hw
      rw [φ.zero_of_le_dist hw.le, zero_smul]
  · -- Step 4: `φ = 1` on `B̄_{ε/4}(v₀)`, so `g = ψ` on `B_ρ(v₀)`
    simp only [φ.one_of_mem_closedBall (ball_subset_closedBall hv), one_smul]
/-- **Simon Ch. 3, Lemma 1.2** (the inverse-function step of the "only if" part): if `G` is `C¹`
and `DG(x)` is injective, then `μ |a − b| ≤ |G(a) − G(b)|` on some ball `B_δ(x)`.  With
`|v| ≤ K |DG(x) v|` and `μ = 1/(2K)`, strict differentiability gives
`|G(a) − G(b) − DG(x)(a − b)| ≤ μ |a − b|` near `x`, so `|G(a) − G(b)| ≥ 2μ|a − b| − μ|a − b|`. -/
theorem Submission.codim1_rdo_c1cov_local_lower_lipschitz : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖ := by
  intro P n G x hG hinj
  -- `L = DG(x)` is injective on the finite-dimensional `ℝⁿ`: `‖v‖ ≤ K ‖L v‖`
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hbound : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ G x v‖ :=
    (fderiv ℝ G x).bound_of_antilipschitz hKL
  -- `μ = 1/(2K)`, so `‖L v‖ ≥ 2μ ‖v‖`
  set μ : ℝ := (2 * K)⁻¹ with hμ
  have hK' : (0 : ℝ) < K := hK
  have hμ0 : 0 < μ := by positivity
  -- `G` is `C¹`, so `L` is a strict derivative: `G` approximates `L` with constant `μ` near `x`
  obtain ⟨s, hs, hGs⟩ := (hG.contDiffAt.hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
    (c := ⟨μ, hμ0.le⟩) (Or.inr hμ0)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, μ, hδ, hμ0, fun a ha b hb => ?_⟩
  have h1 : ‖G a - G b - fderiv ℝ G x (a - b)‖ ≤ μ * ‖a - b‖ := hGs a (hδs ha) b (hδs hb)
  have h2 : 2 * μ * ‖a - b‖ ≤ ‖fderiv ℝ G x (a - b)‖ := by
    calc 2 * μ * ‖a - b‖ ≤ 2 * μ * (K * ‖fderiv ℝ G x (a - b)‖) := by
          gcongr
          exact hbound (a - b)
      _ = ‖fderiv ℝ G x (a - b)‖ := by
          rw [hμ]
          field_simp
  -- triangle inequality: `‖L (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - L (a - b)‖`
  have h3 : ‖fderiv ℝ G x (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - fderiv ℝ G x (a - b)‖ := by
    simpa using norm_sub_le (G a - G b) (G a - G b - fderiv ℝ G x (a - b))
  linarith
/-- A lower Lipschitz bound at a point passes to the derivative (step 1 of the `C¹`-piece tangent
argument, Simon Ch. 3, 1.6): if `U` is open, `a ∈ U`, `g` is differentiable at `a` and
`m|x − a| ≤ |g(x) − g(a)|` on `U`, then `m|v| ≤ |Dg(a)v|`.  For small `t > 0`, `a + tv ∈ U`
gives `m|v| ≤ |t⁻¹(g(a + tv) − g(a))|`, and the quotients tend to `Dg(a)v` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_c1pt_fderiv_lower_bound : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (U : Set (Euclid n)) (a : Euclid n) (m : ℝ), IsOpen U → a ∈ U → DifferentiableAt ℝ g a → (∀ x ∈ U, m * ‖x - a‖ ≤ ‖g x - g a‖) → ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := by
  intro P n g U a m hU ha hg hm v
  -- difference quotients `q(t) = t⁻¹ • (g (a + t • v) - g a)` tend to `Dg(a) v` as `t ↓ 0`
  have hq : Tendsto (fun t : ℝ => t⁻¹ • (g (a + t • v) - g a)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ g a v)) := by
    simpa only [inv_inv] using hg.hasFDerivAt.lim v (c := fun t : ℝ => t⁻¹)
      (tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero)
  -- `a + t • v → a` as `t → 0`, so `a + t • v ∈ U` for small `t` (`U` is a neighbourhood of `a`)
  have hline : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a (by simp)
  -- for small `t > 0`: `t * (m‖v‖) ≤ ‖g (a + t • v) - g a‖`, i.e. `m‖v‖ ≤ ‖q(t)‖`
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), m * ‖v‖ ≤ ‖t⁻¹ • (g (a + t • v) - g a)‖ := by
    filter_upwards [nhdsWithin_le_nhds (hline (hU.mem_nhds ha)), self_mem_nhdsWithin]
      with t htU ht
    have ht : (0 : ℝ) < t := ht
    have h := hm _ htU
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm] at h
    rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  -- the non-strict inequality passes to the limit along the nontrivial filter `𝓝[>] 0`
  exact ge_of_tendsto hq.norm hle
/-- **Simon Ch. 2, (3.2) and (3.5)** (area formula for the blow-ups of an injective regular
image): if `g` is differentiable on the Borel set `B`, injective on `B` and `Dg(a)` is injective
for `a ∈ B`, then for `s > 0`, every `z` and every `f`,
`∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + s b) f(s⁻¹(g(z + s b) − g(z))) dLⁿ(b)`, where
`B_s = {b | z + s b ∈ B}` and `J_g = √det(Dg* ∘ Dg)`.  The rescaled map
`φ(b) = s⁻¹(g(z + s b) − g(z))` is injective on `B_s` with `Dφ(b) = Dg(z + s b)` and
`φ(B_s) = η_{g(z),s}(g(B))`, so this is the area formula for `φ`.  That formula is proved in
place: the linear case (3.1), sharp `Hⁿ` estimates for maps close to an injective linear map,
a measurable partition into such pieces, and the transport of the Jacobian-weighted measure,
following the pinned SimonGMT `Chapter02.AreaApproximation`, `AreaDerivative`, `AreaFormula`
and `WeightedArea` proofs, which lie outside this file's imports. -/
theorem Submission.codim1_rdo_c1pt_rescaled_area_formula : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (B : Set (Euclid n)) (z : Euclid n) (s : ℝ) (f : Euclid P → ℝ), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ g a) → InjOn g B → (∀ a ∈ B, Injective (fderiv ℝ g a)) → 0 < s → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B), f y ∂μHE[n] = ∫ b in {b : Euclid n | z + s • b ∈ B}, Real.sqrt (((fderiv ℝ g (z + s • b)).adjoint ∘L fderiv ℝ g (z + s • b)).det) * f (s⁻¹ • (g (z + s • b) - g z)) := by
  intro P n g B z s f hB hdiff hinj hreg hs
  classical
  -- `J(L) = √det(L* ∘ L)` is the metric Jacobian of a linear map `L : ℝⁿ → ℝᴾ`
  obtain ⟨J, hJdef⟩ : ∃ J : (Euclid n →L[ℝ] Euclid P) → ℝ,
      J = fun L => Real.sqrt ((L.adjoint ∘L L).det) := ⟨_, rfl⟩
  have hJnonneg : ∀ L, 0 ≤ J L := fun L => by rw [hJdef]; exact Real.sqrt_nonneg _
  have hJcont : Continuous J := by
    rw [hJdef]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  /- Simon (3.1), the linear area formula: an injective `L` factors as `ι ∘ M` with `ι` a
  linear isometry onto its range and `M` an endomorphism of `ℝⁿ`, so
  `Hⁿ(L(A)) = Lⁿ(M(A)) = |det M| Lⁿ(A)`, and `J(L)² = det(M* M) = (det M)² ≠ 0`. -/
  have hlin : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L →
      0 < J L ∧ ∀ A : Set (Euclid n), μHE[n] (L '' A) = ENNReal.ofReal (J L) * volume A := by
    intro L hL
    have hV : Module.finrank ℝ (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) = n := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let e : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) ≃ₗᵢ[ℝ] Euclid n :=
      ((stdOrthonormalBasis ℝ _).reindex (finCongr hV)).repr
    let ιI : Euclid n →ₗᵢ[ℝ] Euclid P :=
      (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)).subtypeₗᵢ.comp e.symm.toLinearIsometry
    let M : Euclid n →L[ℝ] Euclid n := (e : _ →L[ℝ] Euclid n) ∘L L.rangeRestrict
    have hLιM : L = ιI.toContinuousLinearMap ∘L M := by
      ext1 x
      show L x = ((e.symm (e (L.rangeRestrict x)) :
        LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) : Euclid P)
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hιadj : ιI.toContinuousLinearMap.adjoint ∘L ιI.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp ιI.norm_map
    have hdetadj : (ContinuousLinearMap.adjoint M).det = M.det := by
      have h := congrArg Matrix.det (LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ) (M : Euclid n →ₗ[ℝ] Euclid n))
      rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h
      simp only [star_trivial] at h
      exact h
    have hdet : (L.adjoint ∘L L).det = M.det ^ 2 := by
      have h1 : L.adjoint ∘L L = M.adjoint ∘L M := by
        rw [hLιM, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ _ M, hιadj, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
      have h2 : (M.adjoint ∘L M).det = M.adjoint.det * M.det :=
        LinearMap.det_comp _ _
      rw [h1, h2, hdetadj, sq]
    have hJ : J L = |M.det| := by
      rw [hJdef]
      dsimp only
      rw [hdet, Real.sqrt_sq_eq_abs]
    have hMinj : LinearMap.ker (M : Euclid n →ₗ[ℝ] Euclid n) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      have h := congrArg (fun v => ((e.symm v : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) :
        Euclid P)) hxy
      simpa [M] using h
    refine ⟨?_, fun A => ?_⟩
    · rw [hJ]
      exact abs_pos.mpr (fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hMinj)
    · rw [hJ, hLιM, ContinuousLinearMap.coe_comp, Set.image_comp,
        LinearIsometry.coe_toContinuousLinearMap, ιI.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact MeasureTheory.Measure.addHaar_image_linearMap volume (M : Euclid n →ₗ[ℝ] Euclid n) A
  -- comparison of pairwise distances gives comparison of the `Hⁿ` measures of the images
  have hdistcmp : ∀ (u v : Euclid n → Euclid P) (T : Set (Euclid n)) (K : NNReal), InjOn v T →
      (∀ x ∈ T, ∀ y ∈ T, dist (u x) (u y) ≤ K * dist (v x) (v y)) →
      μHE[n] (u '' T) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (v '' T) := by
    intro u v T K hv hK
    have hh : LipschitzOnWith K (u ∘ invFunOn v T) (v '' T) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy] using hK x hx y hy
    have himage : (u ∘ invFunOn v T) '' (v '' T) = u '' T := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  /- Near an injective `L`, one radius `δ` controls both the Jacobian of nearby linear maps and
  the `Hⁿ` measure of images under maps `δ`-approximating `L`, up to a factor `q > 1`. -/
  have hradius : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
          ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
            ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
        (∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P), ApproximatesLinearOn u L T δ →
          μHE[n] (u '' T) ≤ q * μHE[n] (L '' T) ∧ μHE[n] (L '' T) ≤ q * μHE[n] (u '' T)) := by
    intro L hL q hq
    obtain ⟨K, -, hK⟩ := (L : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hqR : (1 : ℝ) < q := hq
    have hJpos := (hlin L hL).1
    have hmul : J L < (q : ℝ) * J L := lt_mul_of_one_lt_left hJpos hqR
    have hnear : ∀ᶠ L' in 𝓝 L, J L' < (q : ℝ) * J L ∧ J L < (q : ℝ) * J L' :=
      (hJcont.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hJcont.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεev : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
      (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds,
        hεev.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    -- `‖(u x - u y) - L(x - y)‖ ≤ δ K ‖L x - L y‖` on `T`
    have herror : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P),
        ApproximatesLinearOn u L T δ → ∀ x ∈ T, ∀ y ∈ T,
          ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      intro T u hu x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      calc ‖u x - u y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hu x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    refine ⟨δ, hδ, fun L' hL' => ?_, fun T u hu => ⟨?_, ?_⟩⟩
    · have hdist : dist L' L < ε := by
        rw [dist_eq_norm]
        exact hL'.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hdist
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h1.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h2.le
    · refine (hdistcmp u L T (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖u x - u y‖ ≤ ‖u x - u y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
            add_le_add (herror T u hu x hx y hy) le_rfl
          _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
      · gcongr
        rw [← ENNReal.coe_pow]
        exact ENNReal.coe_le_coe.mpr hδupper.le
    · have hδR : (δ : ℝ) * K < 1 := hδK
      have hdist : ∀ x ∈ T, ∀ y ∈ T,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (u x) (u y) := by
        intro x hx y hy
        have h1 := herror T u hu x hx y hy
        have htriangle := norm_le_norm_add_norm_sub (u x - u y) (L x - L y)
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
        linarith only [h1, htriangle]
      have huinj : InjOn u T := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      refine (hdistcmp L u T _ huinj hdist).trans ?_
      gcongr
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlower.le
  /- On almost every point of a measurable piece where `u` is `δ`-approximated by `A`, the
  derivative is `δ`-close to `A` (the density-point argument of Mathlib's
  `ApproximatesLinearOn.norm_fderiv_sub_le`, for rectangular derivatives). -/
  have hderivbound : ∀ (u : Euclid n → Euclid P) (T : Set (Euclid n)) (A : Euclid n →L[ℝ] Euclid P)
      (δ : NNReal) (u' : Euclid n → Euclid n →L[ℝ] Euclid P), ApproximatesLinearOn u A T δ →
      MeasurableSet T → (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) →
      ∀ᵐ x ∂(volume.restrict T), ‖u' x - A‖₊ ≤ δ := by
    intro u T A δ u' hf hT hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume T, ae_restrict_mem hT]
    intro x hx xT
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun w => ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - A) w‖ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖w‖ + 0) + ‖u' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ := MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one volume T x hx
      (closedBall w ε) measurableSet_closedBall (measure_closedBall_pos volume w εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ T ⊆ {y : Euclid n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xT).isLittleO εpos)
    have B₂ := (eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := x)
      (isBounded_closedBall (x := w) (r := ε)) (ball_mem_nhds x ρpos)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    obtain ⟨r, ⟨y, ⟨yT, hy⟩⟩, rρ, rpos⟩ := (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, aw, ya⟩ : ∃ a, a ∈ closedBall w ε ∧ y = x + r • a := by
      have hy' := hy
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy'
      rcases hy' with ⟨a, aw, ha⟩
      exact ⟨a, aw, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖w‖ + ε :=
      calc ‖a‖ = ‖w + (a - w)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖w‖ + ‖a - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε := by grw [mem_closedBall_iff_norm.1 aw]
    have I : r * ‖(u' x - A) a‖ ≤ r * (δ + ε) * (‖w‖ + ε) :=
      calc r * ‖(u' x - A) a‖ = ‖(u' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - A (y - x) - (u y - u x - (u' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - A (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yT _ xT) (hρ ⟨rρ hy, yT⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖w‖ + ε) := by gcongr
    calc ‖(u' x - A) w‖ = ‖(u' x - A) a + (u' x - A) (w - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(u' x - A) a‖ + ‖(u' x - A) (w - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ‖w - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at aw
          gcongr
  /- Simon (3.2), measure form: for `u` injective on a measurable `T`, differentiable along `T`
  with injective derivative `u'`, `Hⁿ(u(T)) = ∫_T J(u'(x)) dLⁿ(x)`.  Partition `T` into
  measurable pieces on which `u` is close to linear maps `A i = u'(yᵢ)`, compare on each piece
  up to a factor `q²`, sum, and let `q ↓ 1`. -/
  have hmeasure : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet T →
      (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) → (∀ x ∈ T, Injective (u' x)) → InjOn u T →
      μHE[n] (u '' T) = ∫⁻ x in T, ENNReal.ofReal (J (u' x)) := by
    intro T u u' hT hu' hreg' hinj'
    have hcmp : ∀ q : NNReal, 1 < q →
        μHE[n] (u '' T) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' T) := by
      intro q hq
      rcases eq_empty_or_nonempty T with rfl | hTne
      · simp
      have hchoice : ∀ L : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
              ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
          (∀ (T' : Set (Euclid n)) (v : Euclid n → Euclid P), ApproximatesLinearOn v L T' δ →
            μHE[n] (v '' T') ≤ q * μHE[n] (L '' T') ∧
              μHE[n] (L '' T') ≤ q * μHE[n] (v '' T'))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, h1, h2⟩ := hradius L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨1, one_pos, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u T u' hu' δ
          (fun L => (hδpos L).ne')
      have hAreg : ∀ i, Injective (A i) := by
        intro i
        obtain ⟨x, hx, hA⟩ := hactual hTne i
        rw [hA]
        exact hreg' x hx
      have hTeq : T = ⋃ i, T ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[n] (u '' T) = ∑' i, μHE[n] (u '' (T ∩ t i)) := by
        conv_lhs => rw [hTeq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj' inter_subset_left inter_subset_left
        · intro i
          apply (hT.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hu' x hx.1).continuousWithinAt.mono inter_subset_left
          · exact hinj'.mono inter_subset_left
      have hsumintegral : ∫⁻ x in T, ENNReal.ofReal (J (u' x)) =
          ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
        conv_lhs => rw [hTeq]
        exact lintegral_iUnion (fun i => hT.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[n] (u '' (T ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by
        intro i
        have hJ := (hδ (A i) (hAreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (A i) (hAreg i)).2 (T ∩ t i) u (happrox i)
        have hlinA := (hlin (A i) (hAreg i)).2 (T ∩ t i)
        rw [hlinA] at harea_upper harea_lower
        have hderiv := hderivbound u (T ∩ t i) (A i) (δ (A i)) u' (happrox i) (hT.inter (ht i))
          (fun x hx => (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
          calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ ∫⁻ _ in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (A i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).1
            _ = q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (J (A i)) * volume (T ∩ t i) ≤
            q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
          calc ENNReal.ofReal (J (A i)) * volume (T ∩ t i)
              = ∫⁻ _ in T ∩ t i, ENNReal.ofReal (J (A i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (u' x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).2
            _ = q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[n] (u '' (T ∩ t i)) ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
                rw [pow_two, mul_assoc]
        · calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (T ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc ∑' i, μHE[n] (u '' (T ∩ t i))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_mul_left
      · calc ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, μHE[n] (u '' (T ∩ t i)) := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).2
  /- Simon (3.5), Bochner form: the Jacobian-weighted measure on `S` is transported by `u`
  to `Hⁿ ⌞ u(S)`, so `∫_{u(S)} f dHⁿ = ∫_S J(u'(x)) f(u(x)) dLⁿ(x)` for every `f`. -/
  have hbochner : ∀ (S : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet S →
      (∀ x ∈ S, HasFDerivAt u (u' x) x) → (∀ x ∈ S, Injective (u' x)) → InjOn u S →
      Measurable u' → ∫ y in u '' S, f y ∂μHE[n] = ∫ x in S, J (u' x) * f (u x) := by
    intro S u u' hS hu' hreg' hinj' hmeas'
    have hcont : ContinuousOn u S := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hS hinj'
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hJm : Measurable (fun x => J (u' x)) := hJcont.measurable.comp hmeas'
    have hmap : Measure.map (S.domRestrict u)
        ((volume.withDensity (fun x => ENNReal.ofReal (J (u' x)))).comap
          (Subtype.val : S → Euclid n)) = μHE[n].restrict (u '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((S.domRestrict u) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict u) ⁻¹' t) ⊆ S := by
        rintro x ⟨w, _, rfl⟩
        exact w.property
      rw [withDensity_apply _ hBm, ← hmeasure _ u u' hBm
        (fun x hx => (hu' x (hBS hx)).hasFDerivWithinAt) (fun x hx => hreg' x (hBS hx))
        (hinj'.mono hBS), Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨hw, ⟨w, w.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    simp only [Set.domRestrict_apply, ← Function.comp_apply (f := f), ENNReal.ofReal]
    rw [← hsub.integral_map, map_comap_subtype_coe hS,
      setIntegral_withDensity_eq_setIntegral_smul₀ (hJm.real_toNNReal.aemeasurable) _ hS]
    congr with x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hJnonneg _), smul_eq_mul, comp_apply]
  -- the rescaled map `φ(b) = s⁻¹ • (g (z + s • b) - g z)` on `B_s = {b | z + s • b ∈ B}`
  have hs0 : s ≠ 0 := hs.ne'
  have hBs : MeasurableSet {b : Euclid n | z + s • b ∈ B} :=
    hB.preimage ((measurable_const_add z).comp (measurable_const_smul s))
  have hderiv : ∀ b ∈ {b : Euclid n | z + s • b ∈ B},
      HasFDerivAt (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) (fderiv ℝ g (z + s • b)) b := by
    intro b hb
    have h1 : HasFDerivAt (fun b' : Euclid n => z + s • b')
        (s • ContinuousLinearMap.id ℝ (Euclid n)) b :=
      ((hasFDerivAt_id b).const_smul s).const_add z
    refine ((((hdiff _ hb).hasFDerivAt.comp b h1).sub_const (g z)).const_smul s⁻¹).congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ hs0]
  have hinjφ : InjOn (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z))
      {b : Euclid n | z + s • b ∈ B} := by
    intro b hb b' hb' h
    have h' : g (z + s • b) = g (z + s • b') := by
      simpa [hs0] using h
    exact smul_right_injective _ hs0 (add_left_cancel (hinj hb hb' h'))
  have himage :
      (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) '' {b : Euclid n | z + s • b ∈ B} =
        Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨g (z + s • b), ⟨z + s • b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s⁻¹ • (a - z), ?_, ?_⟩
      · show z + s • s⁻¹ • (a - z) ∈ B
        rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
      · show s⁻¹ • (g (z + s • s⁻¹ • (a - z)) - g z) = s⁻¹ • (g a - g z)
        rw [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
  have hmeasf' : Measurable (fun b : Euclid n => fderiv ℝ g (z + s • b)) :=
    (measurable_fderiv ℝ g).comp ((measurable_const_add z).comp (measurable_const_smul s))
  rw [← himage, hbochner _ _ (fun b : Euclid n => fderiv ℝ g (z + s • b)) hBs hderiv
    (fun b hb => hreg _ hb) hinjφ hmeasf', hJdef]
/-- **Gram-determinant chain rule along an orthonormal frame** (the Jacobian chain rule of the area
formula, used for Simon 7.5.8).  Let `Λ : ℝᵐ → ℝᵈ` be linear and `eₖ` the standard basis of `ℝᵐ`.
(i) If `Λ` is injective, `det[⟨Λeₖ, Λeₗ⟩] > 0`.  (ii) If `σ` is an orthonormal frame spanning
`range Λ` and `Γ : ℝᵈ → ℝᴾ` is linear, `det[⟨ΓΛeₖ, ΓΛeₗ⟩] = det[⟨Γσᵢ, Γσⱼ⟩] · det[⟨Λeₖ, Λeₗ⟩]`.
Writing `Λeₗ = ∑ₐ Rₐₗ σₐ` (`Rₐₗ = ⟨σₐ, Λeₗ⟩`), `[⟨GΛeₖ, GΛeₗ⟩] = Rᵀ[⟨Gσₐ, Gσ_b⟩]R` for every
linear `G`; take `G = Γ` and `G = id`.  For (i), let `σ` be an orthonormal basis of `range Λ` (of
dimension `m`): then `det[⟨Λeₖ, Λeₗ⟩] = (det R)²`, and `R` is invertible as `Λ` is injective. -/
theorem Submission.codim1_lura_gram_det_comp_orthonormal : ∀ (m d P : ℕ) (Λ : Euclid m →L[ℝ] Euclid d), (Injective Λ → 0 < Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Λ (EuclideanSpace.single k 1)) (Λ (EuclideanSpace.single l 1)))) ∧ ∀ (Γ : Euclid d →L[ℝ] Euclid P) (σ : Fin m → Euclid d), Orthonormal ℝ σ → Submodule.span ℝ (Set.range σ) = LinearMap.range (Λ : Euclid m →ₗ[ℝ] Euclid d) → Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Γ (Λ (EuclideanSpace.single k 1))) (Γ (Λ (EuclideanSpace.single l 1)))) = Matrix.det (Matrix.of fun i j : Fin m => inner ℝ (Γ (σ i)) (Γ (σ j))) * Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Λ (EuclideanSpace.single k 1)) (Λ (EuclideanSpace.single l 1))) := by
  intro m d P Λ
  -- for an orthonormal frame `σ` of `range Λ`: `Λeₗ = ∑ₐ Rₐₗ σₐ`,
  -- `[⟨GΛeₖ, GΛeₗ⟩] = Rᵀ[⟨Gσₐ, Gσ_b⟩]R` and `det[⟨Λeₖ, Λeₗ⟩] = (det R)²` (`[⟨σₐ, σ_b⟩] = 1`)
  have frame : ∀ σ : Fin m → Euclid d, Orthonormal ℝ σ →
      Submodule.span ℝ (Set.range σ) = LinearMap.range (Λ : Euclid m →ₗ[ℝ] Euclid d) →
      ∃ R : Matrix (Fin m) (Fin m) ℝ, (∀ l, Λ (EuclideanSpace.single l 1) = ∑ a, R a l • σ a) ∧
        (∀ (Q : ℕ) (G : Euclid d →L[ℝ] Euclid Q),
          (Matrix.of fun k l : Fin m => inner ℝ (G (Λ (EuclideanSpace.single k 1)))
            (G (Λ (EuclideanSpace.single l 1)))) =
            R.transpose * (Matrix.of fun a b : Fin m => inner ℝ (G (σ a)) (G (σ b))) * R) ∧
        Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Λ (EuclideanSpace.single k 1))
          (Λ (EuclideanSpace.single l 1))) = R.det * R.det := by
    intro σ hσ hspan
    obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin m) (Fin m) ℝ,
        ∀ l, Λ (EuclideanSpace.single l 1) = ∑ a, R a l • σ a := by
      refine ⟨Matrix.of fun a l => inner ℝ (σ a) (Λ (EuclideanSpace.single l 1)), fun l => ?_⟩
      have hl : Λ (EuclideanSpace.single l 1) ∈ Submodule.span ℝ (Set.range σ) :=
        hspan ▸ LinearMap.mem_range_self (Λ : Euclid m →ₗ[ℝ] Euclid d) _
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hl
      simp only [Matrix.of_apply]
      rw [← hc]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hσ.inner_right_fintype]
    have key : ∀ (Q : ℕ) (G : Euclid d →L[ℝ] Euclid Q),
        (Matrix.of fun k l : Fin m => inner ℝ (G (Λ (EuclideanSpace.single k 1)))
          (G (Λ (EuclideanSpace.single l 1)))) =
          R.transpose * (Matrix.of fun a b : Fin m => inner ℝ (G (σ a)) (G (σ b))) * R := by
      intro Q G
      ext k l
      rw [Matrix.of_apply, hR k, hR l]
      simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
        real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    refine ⟨R, hR, key, ?_⟩
    have hone : (Matrix.of fun a b : Fin m => inner ℝ (σ a) (σ b)) = 1 := by
      ext a b
      rw [Matrix.of_apply, orthonormal_iff_ite.mp hσ a b, Matrix.one_apply]
    have h := key d (ContinuousLinearMap.id ℝ (Euclid d))
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h, hone, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose]
  refine ⟨fun hΛ => ?_, fun Γ σ hσ hspan => ?_⟩
  · -- (i): `σ` an orthonormal basis of `range Λ`, of dimension `m`; if `Rv = 0` then
    -- `Λ(∑ₗ vₗeₗ) = ∑ₐ (Rv)ₐσₐ = 0`, so `v = 0`: `det R ≠ 0`
    set W := LinearMap.range (Λ : Euclid m →ₗ[ℝ] Euclid d) with hW
    have hdim : Module.finrank ℝ W = m := by
      rw [hW, LinearMap.finrank_range_of_inj hΛ, finrank_euclideanSpace_fin]
    set b : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
    have hσ : Orthonormal ℝ (fun a => (b a : Euclid d)) :=
      b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hspan : Submodule.span ℝ (Set.range fun a => (b a : Euclid d)) = W := by
      rw [show (fun a => (b a : Euclid d)) = W.subtype ∘ b from rfl, Set.range_comp,
        Submodule.span_image, ← b.coe_toBasis, b.toBasis.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    obtain ⟨R, hR, -, hdet⟩ := frame _ hσ hspan
    rw [hdet]
    refine mul_self_pos.mpr fun h0 => ?_
    obtain ⟨v, hv, hRv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    have hsum : Λ (∑ l, v l • EuclideanSpace.single l 1) = 0 := by
      simp only [map_sum, map_smul, hR, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      refine Finset.sum_eq_zero fun a _ => ?_
      have ha : ∑ l, v l * R a l = 0 := by
        simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hRv a
      rw [ha, zero_smul]
    have hzero := hΛ (hsum.trans (map_zero Λ).symm)
    funext l
    exact Fintype.linearIndependent_iff.mp
      (EuclideanSpace.orthonormal_single (ι := Fin m) (𝕜 := ℝ)).linearIndependent v hzero l
  · -- (ii): `det(RᵀHR) = det R · det H · det R` with `H = [⟨Γσₐ, Γσ_b⟩]`
    obtain ⟨R, -, key, hdet⟩ := frame σ hσ hspan
    rw [key P Γ, hdet, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
/-- Basis independence of the Gram determinant `det(Dᵢf · Dⱼf)` of the Jacobian (Simon Ch. 6,
3.4–3.7; push-forward of an orientation in 7.1.2): if the orthonormal `n`-frame `τ` spans `Q`, then
`det(⟨L eᵢ, L eⱼ⟩) = det(⟨L τₐ, L τ_b⟩)` for `e = stdOrthonormalBasis ℝ Q`.  With
`L' = L ∘ ι_Q` and `T = L'^* L'`, the matrix of `T` in any orthonormal basis `b` of `Q` is the
Gram matrix `(⟨L bᵢ, L bⱼ⟩)`, so both determinants equal `det T`. -/
theorem Submission.dpf_det_gram_stdOrthonormalBasis_eq : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P) (τ : Fin n → Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ Q) => inner ℝ (L (stdOrthonormalBasis ℝ Q i)) (L (stdOrthonormalBasis ℝ Q j))) = Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (L (τ i)) (L (τ j))) := by
  intro P n Q L τ hτ hQ
  -- `L' = L ∘ ι_Q : Q → ℝᴾ` and the endomorphism `T = L'^* L'` of `Q`
  let L' : Q →ₗ[ℝ] Euclid P := (L : Euclid P →ₗ[ℝ] Euclid P) ∘ₗ Q.subtype
  let T : Q →ₗ[ℝ] Q := LinearMap.adjoint L' ∘ₗ L'
  -- in an orthonormal basis `b` of `Q`, the matrix of `T` is the Gram matrix `(⟨L bᵢ, L bⱼ⟩)`
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ Q),
      Matrix.det (Matrix.of fun i j : ι => inner ℝ (L (b i : Euclid P)) (L (b j : Euclid P))) =
        LinearMap.det T := by
    intro ι _ _ b
    rw [← LinearMap.det_toMatrix b.toBasis T]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    simp only [T, LinearMap.comp_apply, LinearMap.adjoint_inner_right, Matrix.of_apply]
    rfl
  -- `τ`, regarded in `Q`, is an orthonormal basis of `Q`
  have hmem : ∀ a, τ a ∈ Q := fun a => hQ ▸ Submodule.subset_span (Set.mem_range_self a)
  let τ' : Fin n → Q := fun a => ⟨τ a, hmem a⟩
  have hτ' : Orthonormal ℝ τ' := by
    rw [orthonormal_iff_ite] at hτ ⊢
    exact hτ
  have hspan' : ⊤ ≤ Submodule.span ℝ (Set.range τ') := by
    have hmap : Submodule.map Q.subtype (Submodule.span ℝ (Set.range τ')) =
        Submodule.map Q.subtype ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      exact hQ
    rw [Submodule.map_injective_of_injective Q.injective_subtype hmap]
  have h2 := key (OrthonormalBasis.mk hτ' hspan')
  simp only [OrthonormalBasis.coe_mk] at h2
  exact (key (stdOrthonormalBasis ℝ Q)).trans h2.symm
/-- **Simon Ch. 2, 4.11–4.12, (2.1)**: the Jacobian of `Φ ∘ ψ` factors through a chart.  Let
`ψ : V → W` be a local representation of `N` as in (4.1), `Q(x) = T_xN` on `N`, `v ∈ V` and `Φ`
differentiable at `ψ(v)`.  With `A = Dψ(v)`, `L = DΦ(ψ(v))` and `G(T) = det[⟨Teₖ, Teₗ⟩]`,
`G(A) > 0` and `√G(D(Φ ∘ ψ)(v)) = J^NΦ(ψ(v)) · √G(A)`, where `J^NΦ(y) = √det[⟨Lτᵢ, Lτⱼ⟩]` for
`τ = stdOrthonormalBasis ℝ (Q y)`.  Indeed `D(Φ ∘ ψ)(v) = L ∘ A` and `Q(ψ(v)) = T_{ψ(v)}N = range A`,
of dimension `m` as `A` is injective; for an orthonormal frame `σ` of `range A`,
`G(L ∘ A) = det[⟨Lσᵢ, Lσⱼ⟩] · G(A)` and `det[⟨Lσᵢ, Lσⱼ⟩] = det[⟨Lτᵢ, Lτⱼ⟩]`. -/
theorem Submission.codim1_ac_saf_chart_gram_factor : ∀ (P m r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (Q : Euclid P → Submodule ℝ (Euclid P)) (Φ : Euclid P → Euclid P) (v : Euclid m), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → (∀ x ∈ N, (Q x : Set (Euclid P)) = tangentSpace N x) → DifferentiableAt ℝ Φ (ψ v) → v ∈ V → 0 < Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ ψ v (EuclideanSpace.single k 1)) (fderiv ℝ ψ v (EuclideanSpace.single l 1))) ∧ Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ (Φ ∘ ψ) v (EuclideanSpace.single k 1)) (fderiv ℝ (Φ ∘ ψ) v (EuclideanSpace.single l 1)))) = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q (ψ v))) => inner ℝ (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) i)) (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) j)))) * Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ ψ v (EuclideanSpace.single k 1)) (fderiv ℝ ψ v (EuclideanSpace.single l 1)))) := by
  intro P m r N W V ψ Q Φ v hr hV hW hψ hinj hψV hprop hDψ hQ hΦ hv
  -- chain rule: `ψ` is `C¹` on the open set `V`, so `D(Φ ∘ ψ)(v) = DΦ(ψ(v)) ∘ Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψd : DifferentiableAt ℝ ψ v :=
    (hψ1.differentiableOn one_ne_zero v hv).differentiableAt (hV.mem_nhds hv)
  have hchain : fderiv ℝ (Φ ∘ ψ) v = (fderiv ℝ Φ (ψ v)).comp (fderiv ℝ ψ v) :=
    fderiv_comp v hΦ hψd
  -- `Q(ψ(v)) = T_{ψ(v)}N = range Dψ(v)`, as `ψ(v) ∈ ψ(V) = W ∩ N`
  have hT := Submission.chart_tangentSpace_eq_range_fderiv P m r N W V ψ v hr hV hW hψ hinj hψV
    hprop hDψ hv
  have hψvWN : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  set A : Euclid m →L[ℝ] Euclid P := fderiv ℝ ψ v
  set L : Euclid P →L[ℝ] Euclid P := fderiv ℝ Φ (ψ v)
  have hQv : Q (ψ v) = LinearMap.range (A : Euclid m →ₗ[ℝ] Euclid P) := by
    apply SetLike.coe_injective
    rw [hQ _ hψvWN.2, hT, LinearMap.coe_range]
    rfl
  -- an orthonormal frame `σ : Fin m → ℝᴾ` of `S = range A`, which has dimension `m` (`A` injective)
  have hAinj : Injective A := hDψ v hv
  set S : Submodule ℝ (Euclid P) := LinearMap.range (A : Euclid m →ₗ[ℝ] Euclid P) with hS
  have hfr : Module.finrank ℝ S = m := by
    rw [hS, LinearMap.finrank_range_of_inj (f := (A : Euclid m →ₗ[ℝ] Euclid P)) hAinj,
      finrank_euclideanSpace_fin]
  let b : OrthonormalBasis (Fin m) ℝ S := (stdOrthonormalBasis ℝ S).reindex (finCongr hfr)
  let σ : Fin m → Euclid P := fun i => (b i : Euclid P)
  have hσ : Orthonormal ℝ σ := b.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hspan : Submodule.span ℝ (Set.range σ) = S := by
    have hrange : Set.range σ = S.subtype '' Set.range b := by
      ext x
      simp [σ]
    rw [hrange, Submodule.span_image]
    have htop : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [htop, Submodule.map_top, Submodule.range_subtype]
  -- `G(A) > 0` and `G(L ∘ A) = det[⟨Lσᵢ, Lσⱼ⟩] · G(A) = det[⟨Lτᵢ, Lτⱼ⟩] · G(A)`
  have hcomp := Submission.codim1_lura_gram_det_comp_orthonormal m P P A
  have hpos := hcomp.1 hAinj
  have hmul := hcomp.2 L σ hσ hspan
  have hstd := Submission.dpf_det_gram_stdOrthonormalBasis_eq P m (Q (ψ v)) L σ hσ
    (hspan.trans hQv.symm)
  refine ⟨hpos, ?_⟩
  rw [hchain]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hmul, hstd, Real.sqrt_mul' _ hpos.le]
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable
/-- **Simon Ch. 2, (3.1)** in integral form (area formula for an injective linear map): for an
injective linear `L : ℝⁿ → ℝᴾ` and every `f`, `∫_{L(ℝⁿ)} f dHⁿ = √det(L* ∘ L) ∫_{ℝⁿ} f(Lb) dLⁿ(b)`.
Write `L = W ∘ A` with `W` a linear isometry of `ℝⁿ` onto `L(ℝⁿ)` and `A` an automorphism of `ℝⁿ`;
then `Hⁿ⌞L(ℝⁿ) = W#Lⁿ`, `Lⁿ = |det A| A#Lⁿ` and `det(L* ∘ L) = det(A* ∘ A) = (det A)²`. -/
theorem Submission.codim1_rdo_c1pt_linear_range_integral : ∀ (P n : ℕ) (L : Euclid n →L[ℝ] Euclid P) (f : Euclid P → ℝ), Injective L → ∫ y in (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = Real.sqrt ((L.adjoint ∘L L).det) * ∫ b, f (L b) := by
  intro P n L f hL
  -- `L = W ∘ A`: `W` is a linear isometry of `ℝⁿ` onto `R = L(ℝⁿ)` (via an orthonormal basis of
  -- `R`, which has dimension `n`) and `A` is a surjective endomorphism of `ℝⁿ`
  obtain ⟨W, A, hWA, hA⟩ : ∃ (W : Euclid n →ₗᵢ[ℝ] Euclid P) (A : Euclid n →L[ℝ] Euclid n),
      (∀ x, W (A x) = L x) ∧ Surjective A := by
    let R := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)
    have hrank : Module.finrank ℝ R = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Euclid n →ₗ[ℝ] Euclid P)) hL).trans
        finrank_euclideanSpace_fin
    let bv : OrthonormalBasis (Fin n) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hrank)
    refine ⟨R.subtypeₗᵢ.comp bv.repr.symm.toLinearIsometry,
      bv.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        L.codRestrict R (fun x => LinearMap.mem_range_self _ x), fun x => by simp, fun z => ?_⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bv.repr.symm z).2
    refine ⟨x, ?_⟩
    have hx' : L.codRestrict R (fun x => LinearMap.mem_range_self _ x) x = bv.repr.symm z :=
      Subtype.ext hx
    simp [hx']
  have hAinj : Injective A := fun x y h => hL (by rw [← hWA x, ← hWA y, h])
  -- `L(ℝⁿ) = W(ℝⁿ)`
  have hrange : (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) =
      Set.range W := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hA.range_comp W]
    congr 1
    funext x
    exact (hWA x).symm
  -- `Hⁿ⌞W(ℝⁿ) = W#Hⁿ` (`W` is an isometry) and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hW : ∫ y in Set.range W, f y ∂μHE[n] = ∫ x, f (W x) := by
    rw [← W.isometry.map_euclideanHausdorffMeasure,
      W.isometry.isClosedEmbedding.measurableEmbedding.integral_map,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- change of variables `x = A b` on `ℝⁿ`
  have hAcv : ∫ x, f (W x) = |A.det| * ∫ b, f (W (A b)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) hAinj.injOn (fun x => f (W x))
    rw [Set.image_univ, hA.range_eq, Measure.restrict_univ] at h
    rw [h, ← integral_const_mul]
    simp only [smul_eq_mul]
  -- `L* ∘ L = A* ∘ W* ∘ W ∘ A = A* ∘ A`, so `det (L* ∘ L) = (det A)²`
  have hdet : (L.adjoint ∘L L).det = A.det ^ 2 := by
    have hL' : L = W.toContinuousLinearMap ∘L A := ContinuousLinearMap.ext fun x => (hWA x).symm
    have h1 : L.adjoint ∘L L = A.adjoint ∘L A := by
      rw [hL', ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _), W.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have hadj : LinearMap.det (LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n)) =
        LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
        Matrix.det_conjTranspose, LinearMap.det_toMatrix, star_trivial]
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap, hadj, sq]
  rw [hrange, hW, hAcv, hdet, Real.sqrt_sq_eq_abs]
  simp only [hWA]
/-- Rescaled integrals over a `C¹` piece converge to the integral over its tangent map (proof of
Simon Ch. 3, Theorem 1.6, with a continuous weight `h`).  With `L = Dg(z)`,
`B_s = {b : z + s b ∈ B}` and `φ_s(b) = s⁻¹ (g(z + s b) − g(z))`:
`∫_{B_s} h(z + s b) f(φ_s(b)) db → h(z) ∫ f(L b) db` as `s ↓ 0`.  Take `f = 0` off `B_R(0)` and
`B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R`, `K = B̄_{R/m}(0) ⊆ B_s`, and the integrand vanishes on
`B_s \ K` because `|φ_s(b)| ≥ m|b| > R`.  On `K` it is bounded by `sup_{B̄_ρ(z)} |h| · sup |f|` and
tends pointwise to `h(z) f(L b)`, so dominated convergence applies.  Finally `f(L b) = 0` off `K`
because `|L b| ≥ m|b| > R`. -/
theorem Submission.codim1_rdo_c1pt_rescaled_integral_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), Continuous g → DifferentiableAt ℝ g z → Continuous h → IsOpen B → z ∈ B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hg hgz hh hB hzB hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Step 3: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ closedBall z ρ := by
    intro s hs hss b hb
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 4: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hB.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hρB (hKB s hs.1 hs.2.le b hb)
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 5: uniform bounds
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 6–8: dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => Continuous.aestronglyMeasurable ?_
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      exact (hh.comp hz).mul (hf.comp (((hg.comp hz).sub continuous_const).const_smul s⁻¹))
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.tendsto z).comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 9: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc

/-- **Approximate tangent space of a `C¹` piece** (Simon Ch. 3, 1.4; the step "since `x ∈ Nⱼ` and
`Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of the proof of
1.6 "⇒", chapter-03.txt lines 113–125).  Let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on
`B = B_r(c)`, `m > 0`, and `z ∈ B`.  Then `|Dg(a)v| ≥ m|v|`, so `Dg(a)` is injective for `a ∈ B`,
`g` is injective on `B` and `T = Dg(z)(ℝⁿ)` has dimension `n`.  By the area formula (Ch. 2, 3.2,
3.3, 3.5), `∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + sb) f(s⁻¹(g(z + sb) − g(z))) db` for
`s > 0`.  The Jacobian `J_g = √det(Dg* ∘ Dg)` is continuous, so these integrals tend to
`J_g(z) ∫ f(Dg(z)b) db`, which is `∫_T f dHⁿ` by the linear area formula (Ch. 2, 3.1). -/
theorem Submission.codim1_rdo_c1_piece_approxTangent : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r m : ℝ), ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt n (g '' ball c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n g c r m hg hm hlip z hz
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- a vector `x` with `m|x| ≤ 0` vanishes, since `m > 0`
  have hzero : ∀ x : Euclid n, m * ‖x‖ ≤ 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hm)
  -- Step 1, `m|v| ≤ |Dg(a)v|` for `a ∈ B`, so `Dg(a)` is injective; `g` is injective on `B`.
  have hlow : ∀ a ∈ ball c r, ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := fun a ha =>
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P n g (ball c r) a m isOpen_ball ha (hdiff a)
      fun x hx => hlip x hx a ha
  have hinj : ∀ a ∈ ball c r, Injective (fderiv ℝ g a) := by
    intro a ha v w hvw
    have h := hlow a ha (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinjOn : InjOn g (ball c r) := by
    intro a ha b hb hab
    have h := hlip a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  -- Step 2, the Jacobian `J_g(a) = √det(Dg(a)* ∘ Dg(a))` is continuous.
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hJ : Continuous fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous.comp hcont).clm_comp hcont))
  refine ⟨?_, fun f => ?_⟩
  · -- `dim T = n`
    rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P))
      (hinj z hz), finrank_euclideanSpace_fin]
  · -- Steps 3–8, `∫_T f dHⁿ = J_g(z) ∫ f(Dg(z)b) db` is the limit of the rescaled area formulas.
    rw [Submission.codim1_rdo_c1pt_linear_range_integral P n (fderiv ℝ g z) f (hinj z hz)]
    refine (Submission.codim1_rdo_c1pt_rescaled_integral_tendsto P n g
      (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det)) (ball c r) z m f
      hdiff.continuous (hdiff z) hJ isOpen_ball hz hm (fun a ha => hlip a ha z hz) (hlow z hz)
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P n g (ball c r) z s f
      measurableSet_ball (fun a _ => hdiff a) hinjOn hinj hs).symm
/-- **Simon Ch. 3, proof of 1.6 "⇒"** (p. 71, "since `x ∈ Nⱼ` and `Nⱼ` is a `C¹` submanifold"):
if `ψ` is `C¹` on the open `V ⊆ ℝᵐ`, `v₀ ∈ V` and `Dψ(v₀)` is injective, then for some `ρ > 0`
with `B_ρ(v₀) ⊆ V`, `T = Dψ(v₀)(ℝᵐ)` is the approximate tangent space of `ψ(B_ρ(v₀))` at
`ψ(v₀)`.  A globally `C¹` map `g` equals `ψ` on some `B_{ρ₁}(v₀) ⊆ V`, so `g(v₀) = ψ(v₀)` and
`Dg(v₀) = Dψ(v₀)` (equal germs).  `Dg(v₀)` is injective, so `μ|a − b| ≤ |g(a) − g(b)|` on some
`B_δ(v₀)` (Ch. 3, Lemma 1.2), and the `C¹`-piece argument applies to `g` on `B_ρ(v₀)`,
`ρ = min(ρ₁, δ)`, where `g(B_ρ(v₀)) = ψ(B_ρ(v₀))`. -/
theorem Submission.codim1_ac_sat_chart_ball_approxTangent : ∀ (P m : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (v₀ : Euclid m), IsOpen V → ContDiffOn ℝ 1 ψ V → v₀ ∈ V → Injective (fderiv ℝ ψ v₀) → ∃ ρ : ℝ, 0 < ρ ∧ ball v₀ ρ ⊆ V ∧ HasApproximateTangentSpaceAt m (ψ '' ball v₀ ρ) (ψ v₀) (LinearMap.range (fderiv ℝ ψ v₀ : Euclid m →ₗ[ℝ] Euclid P)) := by
  intro P m V ψ v₀ hV hψ hv₀ hinj
  -- Step 1, a globally `C¹` map `g` with `g = ψ` on `B_{ρ₁}(v₀) ⊆ V`
  obtain ⟨g, ρ₁, hρ₁, hρ₁V, hg, hgψ⟩ :=
    Submission.codim1_ac_sat_c1_local_extension P m V ψ v₀ hV hψ hv₀
  -- Step 2, `g = ψ` near `v₀`, so `g(v₀) = ψ(v₀)` and `Dg(v₀) = Dψ(v₀)`
  have hv₀ρ₁ : v₀ ∈ ball v₀ ρ₁ := mem_ball_self hρ₁
  have hgv₀ : g v₀ = ψ v₀ := hgψ hv₀ρ₁
  have hDg : fderiv ℝ g v₀ = fderiv ℝ ψ v₀ :=
    (hgψ.eventuallyEq_of_mem (isOpen_ball.mem_nhds hv₀ρ₁)).fderiv_eq
  -- Step 3, `Dg(v₀)` is injective, so `μ|a − b| ≤ |g(a) − g(b)|` on `B_δ(v₀)`
  obtain ⟨δ, μ, hδ, hμ, hlip⟩ :=
    Submission.codim1_rdo_c1cov_local_lower_lipschitz P m g v₀ hg (by rwa [hDg])
  -- Step 4, `ρ = min(ρ₁, δ)`: `B_ρ(v₀) ⊆ B_{ρ₁}(v₀) ⊆ V` and `B_ρ(v₀) ⊆ B_δ(v₀)`
  have hρ : 0 < min ρ₁ δ := lt_min hρ₁ hδ
  have hρρ₁ : ball v₀ (min ρ₁ δ) ⊆ ball v₀ ρ₁ := ball_subset_ball (min_le_left ρ₁ δ)
  have hρδ : ball v₀ (min ρ₁ δ) ⊆ ball v₀ δ := ball_subset_ball (min_le_right ρ₁ δ)
  refine ⟨min ρ₁ δ, hρ, hρρ₁.trans hρ₁V, ?_⟩
  -- Step 5, the `C¹` piece `g(B_ρ(v₀))` has approximate tangent space `Dg(v₀)(ℝᵐ)` at `g(v₀)`
  have h := Submission.codim1_rdo_c1_piece_approxTangent P m g v₀ (min ρ₁ δ) μ hg hμ
    (fun a ha b hb => hlip a (hρδ ha) b (hρδ hb)) v₀ (mem_ball_self hρ)
  -- Step 6, `g(B_ρ(v₀)) = ψ(B_ρ(v₀))`, `g(v₀) = ψ(v₀)` and `Dg(v₀) = Dψ(v₀)`
  rwa [(hgψ.mono hρρ₁).image_eq, hgv₀, hDg] at h
/-- **Chart localization** (Simon Ch. 2, §4, (4.1)–(4.2)).  Let `ψ` be continuous, 1:1 and proper
on `V` with `ψ(V) = W₀ ∩ N`, `W₀` open, and let `v₀ ∈ V` with `x = ψ(v₀)` in the open set `W` and
`B_ρ(v₀) ⊆ V`.  Then `N ∩ W ∩ B_δ(x) = ψ(B_ρ(v₀)) ∩ B_δ(x)` for some `δ > 0`.  Take
`δ = min(δ₁, δ₂)`, where `δ₁` is the inverse-continuity radius of `ψ` at `v₀` for `ρ` and
`B_{δ₂}(x) ⊆ W ∩ W₀`.  A point `y ∈ N ∩ W ∩ B_δ(x)` lies in `W₀ ∩ N = ψ(V)`, so `y = ψ(v)` with
`v ∈ V`, and `|ψ(v) − x| < δ₁` gives `|v − v₀| < ρ`.  Conversely `ψ(B_ρ(v₀)) ⊆ ψ(V) ⊆ N` and
`B_δ(x) ⊆ W`. -/
theorem Submission.codim1_ac_sat_chart_localization : ∀ (P m : ℕ) (N W W₀ : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (v₀ : Euclid m) (ρ : ℝ), IsOpen W → IsOpen W₀ → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W₀ ∩ N → (∀ K ⊆ W₀, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → v₀ ∈ V → ψ v₀ ∈ W → 0 < ρ → ball v₀ ρ ⊆ V → ∃ δ : ℝ, 0 < δ ∧ N ∩ W ∩ ball (ψ v₀) δ = ψ '' ball v₀ ρ ∩ ball (ψ v₀) δ := by
  intro P m N W W₀ V ψ v₀ ρ hW hW₀ hψ hinj hψV hproper hv₀ hv₀W hρ hball
  -- `ψ(V) = W₀ ∩ N` lies in `W₀` and in `N`; in particular `ψ(v₀) ∈ W₀`
  have hVW₀ : ψ '' V ⊆ W₀ := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  have hxW₀ : ψ v₀ ∈ W₀ := hVW₀ (mem_image_of_mem ψ hv₀)
  -- inverse continuity at `v₀` for `ε = ρ`: `v ∈ V` and `|ψ(v) − ψ(v₀)| < δ₁` give `|v − v₀| < ρ`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := Submission.dsmc_chart_inverse_continuity P m V W₀ ψ hψ hinj hVW₀
    hproper v₀ hv₀ ρ hρ
  -- `B_{δ₂}(ψ(v₀)) ⊆ W ∩ W₀`, hence `B_δ(ψ(v₀)) ⊆ W ∩ W₀` for `δ = min(δ₁, δ₂)`
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 (hW.inter hW₀) (ψ v₀) ⟨hv₀W, hxW₀⟩
  have hδW : ball (ψ v₀) (min δ₁ δ₂) ⊆ W ∩ W₀ :=
    (ball_subset_ball (min_le_right δ₁ δ₂)).trans hδ₂W
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, Subset.antisymm ?_ ?_⟩
  · -- `⊆`: `y ∈ W₀ ∩ N = ψ(V)`, so `y = ψ(v)` with `v ∈ V` and `|v − v₀| < ρ`
    rintro y ⟨⟨hyN, -⟩, hyδ⟩
    obtain ⟨v, hvV, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨(hδW hyδ).2, hyN⟩
    exact ⟨⟨v, mem_ball.2 (hδ₁V v hvV ((mem_ball.1 hyδ).trans_le (min_le_left δ₁ δ₂))), rfl⟩,
      hyδ⟩
  · -- `⊇`: `ψ(B_ρ(v₀)) ⊆ ψ(V) ⊆ N` and `B_δ(ψ(v₀)) ⊆ W`
    rintro _ ⟨⟨v, hv, rfl⟩, hyδ⟩
    exact ⟨⟨hVN (mem_image_of_mem ψ (hball hv)), (hδW hyδ).1⟩, hyδ⟩
/-- **Simon Ch. 3, 1.4 (locality of approximate tangent spaces)**: if `S ∩ B_δ(x) = S' ∩ B_δ(x)`
for some `δ > 0` and `Q` is the approximate tangent space of `S'` at `x`, then `Q` is also the
approximate tangent space of `S` at `x`; no measurability of `S`, `S'` is needed.  For
`f ∈ C_c(ℝᴾ)` with `spt f ⊆ B_R(0)`, `∫_T f dHⁿ = ∫_{B_R(0) ∩ T} f dHⁿ` for every set `T`, and for
`0 < r < δ / R`, `B_R(0) ∩ η_{x,r}(T) = B_R(0) ∩ η_{x,r}(T ∩ B_δ(x))`; so the blown-up integrals
over `S` and `S'` agree for all small `r > 0` and have the same limit `∫_Q f dHⁿ`. -/
theorem Submission.codim1_ac_sat_approxTangent_of_local_eq : ∀ (P n : ℕ) (S S' : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (δ : ℝ), 0 < δ → S ∩ ball x δ = S' ∩ ball x δ → HasApproximateTangentSpaceAt n S' x Q → HasApproximateTangentSpaceAt n S x Q := by
  intro P n S S' x Q δ hδ hSS' hQ
  -- Step 1: the dimension conjunct `dim Q = n` does not involve the set
  refine ⟨hQ.1, fun f => ?_⟩
  -- Step 2: `spt f ⊆ B_R(0)` for some `R > 0`, so `f` vanishes off `B_R(0)`
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_ball (0 : Euclid P)).1 f.hasCompactSupport.isBounded
  obtain ⟨R, hR, hf0⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, y ∉ ball (0 : Euclid P) R → f y = 0 :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos, fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (ball_subset_ball (le_max_left _ _) (hR₀ h))⟩
  -- Step 3: `∫_T f dHⁿ = ∫_{B_R(0) ∩ T} f dHⁿ` for every set `T`, as `B_R(0)` is Borel
  have hcut : ∀ T : Set (Euclid P),
      ∫ y in T, f y ∂μHE[n] = ∫ y in ball 0 R ∩ T, f y ∂μHE[n] := by
    intro T
    rw [← Measure.restrict_restrict measurableSet_ball]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf0).symm
  -- Step 6: it suffices that the blown-up integrals over `S'` and `S` agree for `0 < r < δ / R`
  refine (hQ.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  -- Step 4: `B_R(0) ∩ η_{x,r}(T) = B_R(0) ∩ η_{x,r}(T ∩ B_δ(x))`, as `|t − x| = r |η_{x,r}(t)|`
  have hloc : ∀ T : Set (Euclid P),
      ball 0 R ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' T =
        ball 0 R ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' (T ∩ ball x δ) := by
    intro T
    refine Subset.antisymm ?_ (inter_subset_inter_right _ (image_mono inter_subset_left))
    rintro _ ⟨hy, t, ht, rfl⟩
    refine ⟨hy, t, ⟨ht, mem_ball.2 ?_⟩, rfl⟩
    have hy' : ‖r⁻¹ • (t - x)‖ < R := mem_ball_zero_iff.1 hy
    calc dist t x = ‖t - x‖ := dist_eq_norm t x
      _ = r * ‖r⁻¹ • (t - x)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.1.le), ← mul_assoc,
          mul_inv_cancel₀ hr.1.ne', one_mul]
      _ < r * R := mul_lt_mul_of_pos_left hy' hr.1
      _ < δ := (lt_div_iff₀ hR).1 hr.2
  -- Step 5: hence, by `S ∩ B_δ(x) = S' ∩ B_δ(x)`, the two blown-up integrals coincide
  rw [hcut (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S'),
    hcut (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S), hloc S', hloc S, hSS']
/-- **Simon Ch. 2, (3.2) and (3.5) on a chart (4.1)**: let `ψ : V → W` be a local representation
of `N` as in (4.1), `Q(x) = TₓN` on `N`, and `Φ : ℝᴾ → ℝᴾ` a 1:1 `C¹` map with `DΦ` injective;
write `J(x) = √det(⟨DΦ(x)τᵢ, DΦ(x)τⱼ⟩)`, `τ` the standard orthonormal basis of `Q(x)`.  Then
`∫_{Φ(B)} g dHᵐ = ∫_B J(x) g(Φ(x)) dHᵐ(x)` for Borel `B ⊆ W ∩ N` and every `g ≥ 0`.  With
`A = V ∩ ψ⁻¹(B)` (Borel, `ψ(A) = B`), the weighted parametric area formula for `Φ ∘ ψ` and for
`ψ` turns both sides into integrals over `A` against Lebesgue measure, and the integrands agree
on `A` because `J_{Φ∘ψ} = (J ∘ ψ) · J_ψ` there. -/
theorem Submission.codim1_ac_saf_chart_area_formula : ∀ (P m r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (Q : Euclid P → Submodule ℝ (Euclid P)) (Φ : Euclid P → Euclid P), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → (∀ x ∈ N, (Q x : Set (Euclid P)) = tangentSpace N x) → ContDiff ℝ 1 Φ → Injective Φ → (∀ x, Injective (fderiv ℝ Φ x)) → ∀ B : Set (Euclid P), B ⊆ W ∩ N → MeasurableSet B → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in Φ '' B, g y ∂μHE[m] = ∫⁻ x in B, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) j))))) * g (Φ x) ∂μHE[m] := by
  intro P m r N W V ψ Q Φ hr hV hW hψ hinj hψV hprop hDψ hQ hΦ hΦinj hDΦ B hBWN hB g
  classical
  -- `ψ` is `C¹` on the open set `V`, hence differentiable on `V`; `Φ` is differentiable
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψd : ∀ v ∈ V, DifferentiableAt ℝ ψ v := fun v hv =>
    (hψ1.differentiableOn one_ne_zero v hv).differentiableAt (hV.mem_nhds hv)
  have hΦd : ∀ x, DifferentiableAt ℝ Φ x := fun x => hΦ.differentiable one_ne_zero x
  -- Step 1: the parameter set `A = V ∩ ψ⁻¹(B)` has `ψ(A) = B`
  set A : Set (Euclid m) := V ∩ ψ ⁻¹' B with hAdef
  have hAV : A ⊆ V := inter_subset_left
  have hAimg : ψ '' A = B := by
    apply Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hv.2
    · intro b hb
      have : b ∈ ψ '' V := hψV ▸ hBWN hb
      obtain ⟨v, hv, rfl⟩ := this
      exact ⟨v, ⟨hv, hb⟩, rfl⟩
  -- `A` is Borel: on `V` it is the preimage of `B` under the Borel map `ψ` on `V`, `0` off `V`
  have hAmeas : MeasurableSet A := by
    have hm : Measurable (V.piecewise ψ (fun _ => (0 : Euclid P))) :=
      ContinuousOn.measurable_piecewise hψ1.continuousOn continuousOn_const hV.measurableSet
    have : A = V ∩ (V.piecewise ψ (fun _ => (0 : Euclid P))) ⁻¹' B := by
      ext v
      simp only [hAdef, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hv, hb⟩
        exact ⟨hv, by rw [Set.piecewise_eq_of_mem _ _ _ hv]; exact hb⟩
      · rintro ⟨hv, hb⟩
        exact ⟨hv, by rw [Set.piecewise_eq_of_mem _ _ _ hv] at hb; exact hb⟩
    rw [this]
    exact hV.measurableSet.inter (hm hB)
  -- Steps 2–3: the weighted area formula for `Φ ∘ ψ` on `A` (`D(Φ ∘ ψ) = DΦ ∘ Dψ` is injective)
  have h1 := (Submission.codim1_lura_gram_area_formula m P (Φ ∘ ψ)).2 A hAmeas
    (fun v hv => (hΦd (ψ v)).comp v (hψd v (hAV hv)))
    (fun v hv => by
      rw [fderiv_comp v (hΦd (ψ v)) (hψd v (hAV hv))]
      exact (hDΦ (ψ v)).comp (hDψ v (hAV hv)))
    (fun a ha b hb hab => hinj (hAV ha) (hAV hb) (hΦinj hab)) g
  -- Step 4: the weighted area formula for `ψ` on `A` with weight `J · (g ∘ Φ)`
  have h2 := (Submission.codim1_lura_gram_area_formula m P ψ).2 A hAmeas
    (fun v hv => hψd v (hAV hv)) (fun v hv => hDψ v (hAV hv)) (hinj.mono hAV)
    (fun x => ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) j))))) * g (Φ x))
  rw [image_comp, hAimg] at h1
  rw [hAimg] at h2
  rw [h1, h2]
  -- Steps 5–6: on `A`, `J_{Φ∘ψ} = (J ∘ ψ) · J_ψ`, so the two integrands over `A` agree
  apply setLIntegral_congr_fun hAmeas
  intro v hv
  have hfac := Submission.codim1_ac_saf_chart_gram_factor P m r N W V ψ Q Φ v hr hV hW hψ hinj hψV
    hprop hDψ hQ (hΦd (ψ v)) (hAV hv)
  simp only [Function.comp_apply]
  rw [hfac.2, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  ring
/-- **Gluing a change of variables over a countable chart cover** (Simon Ch. 2, 4.11–4.13).  Let
`Φ : ℝᴾ → ℝᴾ` be continuous and injective, and let every `y ∈ N` have an open `W ∋ y` with
`∫_{Φ(B)} g dμ = ∫_B w · g ∘ Φ dμ` for all Borel `B ⊆ W ∩ N` and all `g ≥ 0`.  Then the same
holds for every Borel `B ⊆ N`.  By Lusin–Souslin, `Φ` maps Borel sets to Borel sets.  Countably
many `W_{y_k}` cover `N` (Lindelöf); the disjointed pieces `B_k ⊆ W_{y_k} ∩ N` of `B ∩ W_{y_k}`
are Borel with union `B`, and the `Φ(B_k)` are disjoint with union `Φ(B)`.  Both sides are
countably additive over disjoint Borel sets. -/
theorem Submission.codim1_ac_saf_lintegral_image_of_local : ∀ (P : ℕ) (μ : Measure (Euclid P)) (N : Set (Euclid P)) (Φ : Euclid P → Euclid P) (w : Euclid P → ℝ≥0∞), Continuous Φ → Injective Φ → (∀ y ∈ N, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧ ∀ B : Set (Euclid P), B ⊆ W ∩ N → MeasurableSet B → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in Φ '' B, g z ∂μ = ∫⁻ x in B, w x * g (Φ x) ∂μ) → ∀ B : Set (Euclid P), B ⊆ N → MeasurableSet B → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in Φ '' B, g z ∂μ = ∫⁻ x in B, w x * g (Φ x) ∂μ := by
  intro P μ N Φ w hΦc hΦinj hloc B hBN hB g
  classical
  -- Lusin–Souslin: `Φ` is continuous and injective on the Polish space `ℝᴾ`
  have hemb : MeasurableEmbedding Φ := hΦc.measurableEmbedding hΦinj
  -- `N = ∅` forces `B = ∅`, and both sides vanish
  rcases N.eq_empty_or_nonempty with hN0 | hNne
  · have hB0 : B = ∅ := subset_empty_iff.1 (hN0 ▸ hBN)
    subst hB0
    simp
  -- countably many of the neighbourhoods `W_y`, `y ∈ N`, cover `N` (Lindelöf)
  choose! Wf hWo hyW hform using hloc
  have : Nonempty N := hNne.to_subtype
  obtain ⟨j, hj⟩ := (HereditarilyLindelofSpace.isLindelof N).indexed_countable_subcover
    (fun y : N => Wf y) (fun y => hWo y y.2) (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyW y hy⟩)
  -- disjoint Borel pieces `B_k ⊆ W_{y_k} ∩ N` of `B ∩ W_{y_k}` with union `B`
  set S : ℕ → Set (Euclid P) := fun k => B ∩ Wf (j k)
  set D : ℕ → Set (Euclid P) := disjointed S with hDdef
  have hDm : ∀ k, MeasurableSet (D k) :=
    MeasurableSet.disjointed (fun k => hB.inter (hWo _ (j k).2).measurableSet)
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed S
  have hDU : ⋃ k, D k = B := by
    rw [hDdef, iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset fun k => inter_subset_left
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hj (hBN hx))
      exact mem_iUnion.2 ⟨k, hx, hk⟩
  have hDsub : ∀ k, D k ⊆ Wf (j k) ∩ N := fun k x hx =>
    ⟨(disjointed_subset S k hx).2, hBN (disjointed_subset S k hx).1⟩
  -- `Φ` is injective, so the Borel images `Φ(B_k)` are disjoint
  have hImDisj : Pairwise (Disjoint on fun k => Φ '' D k) := fun a b hab =>
    (hDdisj hab).image hΦinj.injOn (subset_univ _) (subset_univ _)
  -- countable additivity on both sides, and the local formula on each piece
  calc ∫⁻ z in Φ '' B, g z ∂μ = ∫⁻ z in ⋃ k, Φ '' D k, g z ∂μ := by rw [← image_iUnion, hDU]
    _ = ∑' k, ∫⁻ z in Φ '' D k, g z ∂μ :=
        lintegral_iUnion (fun k => hemb.measurableSet_image.2 (hDm k)) hImDisj g
    _ = ∑' k, ∫⁻ x in D k, w x * g (Φ x) ∂μ := by
        congr 1; funext k; exact hform (j k) (j k).2 (D k) (hDsub k) (hDm k) g
    _ = ∫⁻ x in ⋃ k, D k, w x * g (Φ x) ∂μ := (lintegral_iUnion hDm hDdisj _).symm
    _ = ∫⁻ x in B, w x * g (Φ x) ∂μ := by rw [hDU]

/-- **Continuity of the tangential Jacobian on a `C¹` submanifold** (Simon Ch. 2, (4.1)–(4.2) and
4.11–4.12).  Let `N ⊆ ℝᴾ` be an embedded `m`-dimensional `C¹` submanifold, `Q(x) = TₓN` for
`x ∈ N`, and `Φ : ℝᴾ → ℝᴾ` a `C¹` map; write `J(x) = √det(⟨DΦ(x)τᵢ, DΦ(x)τⱼ⟩)`, `τ` the standard
orthonormal basis of `Q(x)`.  Then `J` is continuous on `N`.  Near `y = ψ(v₀) ∈ N` take a chart
`ψ : V → W` as in (4.1) and put `γ(T) = √det(⟨Teₖ, Teₗ⟩)`, a continuous function of `T`.  By the
chart Gram factorization, `γ(Dψ) > 0` and `J ∘ ψ = γ(D(Φ ∘ ψ)) / γ(Dψ)` on `V`, which is
continuous because `Dψ` and `D(Φ ∘ ψ)` are continuous on the open set `V`.  Since `ψ⁻¹` is
continuous at `y` on `ψ(V) = W ∩ N` and `W` is open, `J` is continuous at `y` within `N`. -/
theorem Submission.codim1_ac_saf_jacobian_continuousOn : ∀ (P m : ℕ) (N : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (Φ : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 m N → (∀ x ∈ N, (Q x : Set (Euclid P)) = tangentSpace N x) → ContDiff ℝ 1 Φ → ContinuousOn (fun x => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) j))))) N := by
  intro P m N Q Φ hN hQ hΦ y hy
  -- Step 1: a chart `ψ : V → W` of `N` as in (4.1), with `y = ψ(v₀)`
  obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, hψV, hproper, hDψ⟩ := hN y hy
  have hψ1 : ContDiffOn ℝ 1 ψ V := by exact_mod_cast hψ
  obtain ⟨v₀, hv₀, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  -- Step 2: `γ(T) = √det(⟨Teₖ, Teₗ⟩)` is continuous in `T`
  set γ : (Euclid m →L[ℝ] Euclid P) → ℝ := fun T => Real.sqrt (Matrix.det (Matrix.of
    fun k l : Fin m => inner ℝ (T (EuclideanSpace.single k 1)) (T (EuclideanSpace.single l 1))))
  have hγ : Continuous γ := by
    refine Continuous.sqrt (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner
      (continuous_id.clm_apply continuous_const)
  -- Step 3: `Dψ` and `D(Φ ∘ ψ)` are continuous on the open set `V`
  have hDψc : ContinuousOn (fderiv ℝ ψ) V := hψ1.continuousOn_fderiv_of_isOpen hV le_rfl
  have hDΦψc : ContinuousOn (fderiv ℝ (Φ ∘ ψ)) V :=
    (hΦ.comp_contDiffOn hψ1).continuousOn_fderiv_of_isOpen hV le_rfl
  -- Step 4: chart Gram factorization, `γ(Dψ(v)) > 0` and `γ(D(Φ ∘ ψ)(v)) = J(ψ(v)) γ(Dψ(v))`
  have hfac : ∀ v ∈ V, 0 < γ (fderiv ℝ ψ v) ∧ γ (fderiv ℝ (Φ ∘ ψ) v) =
      Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q (ψ v))) =>
        inner ℝ (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) i))
          (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) j)))) * γ (fderiv ℝ ψ v) := by
    intro v hv
    obtain ⟨hpos, hmul⟩ := Submission.codim1_ac_saf_chart_gram_factor P m 1 N W V ψ Q Φ v le_rfl
      hV hW hψ hinj hψV hproper hDψ hQ (hΦ.differentiable one_ne_zero (ψ v)) hv
    exact ⟨Real.sqrt_pos.2 hpos, hmul⟩
  -- hence `J ∘ ψ = γ(D(Φ ∘ ψ)) / γ(Dψ)` on `V`
  have hJ : ∀ v ∈ V, Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q (ψ v))) =>
      inner ℝ (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) i))
        (fderiv ℝ Φ (ψ v) (stdOrthonormalBasis ℝ (Q (ψ v)) j)))) =
      γ (fderiv ℝ (Φ ∘ ψ) v) / γ (fderiv ℝ ψ v) := by
    intro v hv
    rw [(hfac v hv).2, mul_div_cancel_right₀ _ (hfac v hv).1.ne']
  -- Step 5: `γ(D(Φ ∘ ψ)) / γ(Dψ)` is continuous on `V`
  have hGc : ContinuousOn (fun v => γ (fderiv ℝ (Φ ∘ ψ) v) / γ (fderiv ℝ ψ v)) V :=
    (hγ.comp_continuousOn hDΦψc).div (hγ.comp_continuousOn hDψc) fun v hv => (hfac v hv).1.ne'
  -- Steps 6–7: `ψ⁻¹` is continuous at `ψ(v₀)` on `ψ(V) = W ∩ N`, and `W` is open
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hG⟩ := Metric.continuousWithinAt_iff.1 (hGc v₀ hv₀) ε hε
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  obtain ⟨δ₂, hδ₂, hinv⟩ := Submission.dsmc_chart_inverse_continuity P m V W ψ hψ1.continuousOn
    hinj hVW hproper v₀ hv₀ δ₁ hδ₁
  obtain ⟨δ₃, hδ₃, hball⟩ := Metric.isOpen_iff.1 hW (ψ v₀) hyW
  refine ⟨min δ₂ δ₃, lt_min hδ₂ hδ₃, ?_⟩
  intro y' hy' hy'd
  -- `y' = ψ(v')` with `v' ∈ V` and `|v' − v₀| < δ₁`, so `|J(y') − J(ψ(v₀))| < ε`
  obtain ⟨v', hv', rfl⟩ : y' ∈ ψ '' V :=
    hψV ▸ ⟨hball (mem_ball.2 (hy'd.trans_le (min_le_right _ _))), hy'⟩
  rw [hJ v' hv', hJ v₀ hv₀]
  exact hG hv' (hinv v' hv' (hy'd.trans_le (min_le_left _ _)))
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
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

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW

/-- **Simon 6.2.2, 6.3.1, 6.3.2(3) with `θ ≡ 1`**: a Borel, countably `m`-rectifiable `M ⊆ ℝᴾ`
with `Hᵐ(M ∩ K) < ∞` for compact `K`, oriented `Hᵐ`-a.e. by a unit orientation `η` of its
approximate tangent space, defines the integer multiplicity current `D = [[M]] = τ(M, 1, η)`:
`⟨ω, η⟩` is `Hᵐ⌞M`-integrable, `D(ω) = ∫_M ⟨ω, η⟩ dHᵐ`, and `M_W(D) ≤ μ_{τ(M,1,η)}(W) =
Hᵐ(M ∩ W)` for every `W`. -/
theorem Submission.codim1_ac_pp_unit_rectifiable_current : ∀ (P m : ℕ) (M : Set (Euclid P)) (η : Euclid P → MultiVector P m), MeasurableSet M → CountablyRectifiable m M → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → AEStronglyMeasurable η (μHE[m].restrict M) → (∀ᵐ y ∂(μHE[m].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt m M y Q ∧ IsUnitOrientationOf (η y) Q) → ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) m, IsIntegerMultiplicity D ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Integrable (fun y => η y ((ω : DifferentialForm (Euclid P) m) y)) (μHE[m].restrict M) ∧ D ω = ∫ y in M, η y ((ω : DifferentialForm (Euclid P) m) y) ∂μHE[m]) ∧ ∀ W' : Set (Euclid P), D.massOn W' ≤ μHE[m] (M ∩ W') := by
  intro P m M η hM hrect hfin hη horient
  -- the multiplicity-one triple `R = (M, 1, η)` in `ℝᴾ`; `∫_{M ∩ K} 1 dHᵐ = Hᵐ(M ∩ K) < ∞`
  let R : IMRep (univ : Set (Euclid P)) m :=
    { carrier := M
      mult := fun _ => 1
      orient := η
      measurableSet_carrier := hM
      carrier_subset := subset_univ M
      rectifiable := hrect
      measurable_mult := measurable_const
      mult_pos := fun _ _ => Nat.one_pos
      locallyIntegrable_mult := fun K hK _ => by
        simp only [Nat.cast_one, setLIntegral_const, one_mul]
        exact hfin K hK
      aestronglyMeasurable_orient := hη
      orients := horient }
  -- `D = τ(M, 1, η)` is an integer multiplicity current
  obtain ⟨D, hD⟩ := Submission.dtc_imrep_current P m univ R
  refine ⟨D, ⟨R, hD⟩, fun ω => ?_, fun W' => ?_⟩
  · -- `1 · ⟨ω, η⟩` is `Hᵐ⌞M`-integrable and `D(ω) = ∫_M 1 · ⟨ω, η⟩ dHᵐ`
    have hi := Submission.regcomp_rim_action_integrable P m univ R ω
    simp only [R, Nat.cast_one, one_mul] at hi
    refine ⟨hi, ?_⟩
    rw [hD ω]
    simp only [IMRep.action, R, Nat.cast_one, one_mul]
  · -- `M_W(D) ≤ μ_R(W)`, and `μ_R = 1 · Hᵐ⌞M`, so `μ_R(W) = Hᵐ(W ∩ M)` (`M` Borel)
    have hm := Submission.dor_ims_massOn_le_measure P m univ D R hD W'
    have hmeas : R.measure = μHE[m].restrict M := by
      simp only [IMRep.measure, R, Nat.cast_one]
      exact withDensity_one
    rw [hmeas, Measure.restrict_apply' hM, inter_comm] at hm
    exact hm

/-- **Simon Ch. 3, Lemma 1.2 ("if" part)**: an embedded `C¹` `m`-submanifold `N ⊆ ℝᴾ` is Borel
and countably `m`-rectifiable.  By Lindelöf countably many charts `ψⱼ(Vⱼ) = Wⱼ ∩ N` cover `N`.
Each open `Vⱼ ⊆ ℝᵐ` is σ-compact, so `ψⱼ(Vⱼ)` is σ-compact, hence Borel; and `ψⱼ` is Lipschitz
on each compact piece of `Vⱼ`, so extends to a Lipschitz map `ℝᵐ → ℝᴾ` (Ch. 2, 1.2).  This is
the argument of SimonGMT's `measurableSet_of_isSimonSubmanifold` and
`countablyRectifiable_of_isSimonSubmanifold`. -/
theorem Submission.codim1_ac_pp_embedded_measurable_rectifiable : ∀ (P m : ℕ) (N : Set (Euclid P)), IsEmbeddedSubmanifold 1 m N → MeasurableSet N ∧ CountablyRectifiable m N := by
  intro P m N hN
  rcases N.eq_empty_or_nonempty with rfl | hne
  · exact ⟨MeasurableSet.empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty⟩
  have : Nonempty N := hne.to_subtype
  -- a chart `ψ_y : V_y → W_y` with `ψ_y(V_y) = W_y ∩ N` at each `y ∈ N`
  choose V W ψ hV hW hyW hψ _ himg _ _ using fun y : N => hN y y.2
  -- Lindelöf: countably many `W_{c j}` cover `N`, so `N = ⋃ⱼ ψ_{c j}(V_{c j})`
  obtain ⟨c, hc⟩ := (HereditarilyLindelofSpace.isLindelof N).indexed_countable_subcover W hW
    fun y hy => mem_iUnion_of_mem ⟨y, hy⟩ (hyW ⟨y, hy⟩)
  have hNeq : N = ⋃ j, ψ (c j) '' V (c j) := by
    refine Subset.antisymm (fun y hy => ?_)
      (iUnion_subset fun j => (himg (c j)).trans_subset inter_subset_right)
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hc hy)
    exact mem_iUnion_of_mem j ((himg (c j)).symm ▸ ⟨hyj, hy⟩)
  -- each chart domain is σ-compact (open in `ℝᵐ`): `V = ⋃ₖ Kₖ` with `Kₖ` compact
  have hσ : ∀ y : N, IsSigmaCompact (V y) := fun y => by
    have : LocallyCompactSpace (V y) := (hV y).locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  rw [hNeq]
  refine ⟨MeasurableSet.iUnion fun j => ?_,
    Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ fun j => ?_⟩
  · -- Borel: `ψ(V)` is σ-compact, a countable union of compact sets
    obtain ⟨K, hK, hKeq⟩ := (hσ (c j)).image_of_continuousOn (hψ (c j)).continuousOn
    rw [← hKeq]
    exact MeasurableSet.iUnion fun k => (hK k).measurableSet
  · -- rectifiable: the `C¹` map `ψ` is Lipschitz on each compact `Kₖ ⊆ V`; extend it to `ℝᵐ`
    obtain ⟨K, hK, hKeq⟩ := hσ (c j)
    have hLip : ∀ k, ∃ L, LipschitzOnWith L (ψ (c j)) (K k) := fun k =>
      LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hK k) fun x hx => by
        obtain ⟨L, t, ht, hLt⟩ := ((hψ (c j)).contDiffAt
          ((hV (c j)).mem_nhds (hKeq ▸ mem_iUnion_of_mem k hx))).exists_lipschitzOnWith
        exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hLt⟩
    choose L hL using hLip
    choose g hg hgeq using fun k => (hL k).extend_finite_dimension
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ fun k =>
      Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hg k)).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hxk⟩ := mem_iUnion.mp (hKeq.symm ▸ hx)
    exact mem_iUnion_of_mem k ⟨x, (hgeq k hxk).symm⟩
/-- **Signed area transfer** (Simon Ch. 2, 3.5 and 4.13, stated there for `h ≥ 0`): if
`∫⁻_B g dν = ∫⁻_A ofReal(J)·(g ∘ Φ) dμ` for every `g : β → [0, ∞]` and `J ≥ 0`, then for `f`
integrable on `B`, `J·(f ∘ Φ)` is integrable on `A` and `∫_B f dν = ∫_A J·(f ∘ Φ) dμ`.  The
identity at `g = ‖f‖ₑ` gives integrability (`‖J t‖ₑ = ofReal(J)·‖t‖ₑ`); at `g = ofReal(±f)` it
matches the positive and negative parts (`ofReal(J)·ofReal(±t) = ofReal(±J t)`). -/
theorem Submission.codim1_ac_pp_setIntegral_transfer : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) (Φ : α → β) (A : Set α) (B : Set β) (J : α → ℝ) (f : β → ℝ), (∀ x, 0 ≤ J x) → (∀ g : β → ℝ≥0∞, ∫⁻ y in B, g y ∂ν = ∫⁻ x in A, ENNReal.ofReal (J x) * g (Φ x) ∂μ) → Integrable f (ν.restrict B) → AEStronglyMeasurable (fun x => J x * f (Φ x)) (μ.restrict A) → Integrable (fun x => J x * f (Φ x)) (μ.restrict A) ∧ ∫ y in B, f y ∂ν = ∫ x in A, J x * f (Φ x) ∂μ := by
  intro α β _ _ μ ν Φ A B J f hJ harea hf hmeas
  -- `∫⁻_A ‖J·(f ∘ Φ)‖ₑ dμ = ∫⁻_B ‖f‖ₑ dν < ∞`
  have hint : Integrable (fun x => J x * f (Φ x)) (μ.restrict A) := by
    refine ⟨hmeas, ?_⟩
    have h1 : ∫⁻ x in A, ‖J x * f (Φ x)‖ₑ ∂μ = ∫⁻ y in B, ‖f y‖ₑ ∂ν := by
      rw [harea (fun y => ‖f y‖ₑ)]
      congr 1
      funext x
      rw [enorm_mul, Real.enorm_of_nonneg (hJ x)]
    rw [HasFiniteIntegral, h1]
    exact hf.2
  refine ⟨hint, ?_⟩
  -- both integrals as differences of the integrals of their positive and negative parts
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    harea (fun y => ENNReal.ofReal (f y)), harea (fun y => ENNReal.ofReal (-f y))]
  congr 2
  · congr 1
    funext x
    rw [ENNReal.ofReal_mul (hJ x)]
  · congr 1
    funext x
    rw [← ENNReal.ofReal_mul (hJ x), mul_neg]
/-- **Simon Ch. 2, §4, (4.1)–(4.3)**: if `N` is an embedded `d`-dimensional `C¹` submanifold and
`Φ : ℝᴾ → ℝᴾ` is an anti-Lipschitz `C¹` bijection with `DΦ(x)` injective, then `Φ(N)` is an
embedded `d`-dimensional `C¹` submanifold and `T_{Φ(x)}Φ(N) = DΦ(x)(TₓN)` for `x ∈ N`.  `Φ⁻¹` is
Lipschitz, so `Φ` is a homeomorphism, and a chart `(V, W, ψ)` of `N` gives the chart
`(V, Φ(W), Φ ∘ ψ)` of `Φ(N)`: `Φ(W)` is open, `Φ(ψ(V)) = Φ(W) ∩ Φ(N)`, `V ∩ (Φ ∘ ψ)⁻¹(K)` is
compact because `Φ⁻¹(K) ⊆ W` is, and `D(Φ ∘ ψ) = DΦ ∘ Dψ` is injective.  The tangent spaces then
follow from `chart_tangentSpace_eq_range_fderiv` for both charts. -/
theorem Submission.codim1_ac_diffeo_image_submanifold : ∀ (P d : ℕ) (N : Set (Euclid P)) (Φ : Euclid P → Euclid P) (Λ : NNReal), IsEmbeddedSubmanifold 1 d N → ContDiff ℝ 1 Φ → Bijective Φ → (∀ x, Injective (fderiv ℝ Φ x)) → AntilipschitzWith Λ Φ → IsEmbeddedSubmanifold 1 d (Φ '' N) ∧ ∀ x ∈ N, tangentSpace (Φ '' N) (Φ x) = (fderiv ℝ Φ x) '' tangentSpace N x := by
  intro P d N Φ Λ hN hΦ hbij hDΦ hanti
  -- Step 1: `Φ` is a homeomorphism, its inverse being `Λ`-Lipschitz
  obtain ⟨H, hH⟩ : ∃ H : Euclid P ≃ₜ Euclid P, ⇑H = Φ :=
    ⟨{ toEquiv := Equiv.ofBijective Φ hbij
       continuous_toFun := hΦ.continuous
       continuous_invFun :=
        (hanti.to_rightInverse (Equiv.ofBijective Φ hbij).rightInverse_symm).continuous }, rfl⟩
  have hopen : ∀ O : Set (Euclid P), IsOpen O → IsOpen (Φ '' O) := by
    intro O hO
    rw [← hH]
    exact H.isOpenMap O hO
  have hcpt : ∀ K : Set (Euclid P), IsCompact K → IsCompact (Φ ⁻¹' K) := by
    intro K hK
    rw [← hH]
    exact H.isCompact_preimage.2 hK
  have hΦ1 : ContDiff ℝ (1 : ℕ) Φ := by exact_mod_cast hΦ
  -- Step 2: a chart `(V, W, ψ)` of `N` gives the chart `(V, Φ(W), Φ ∘ ψ)` of `Φ(N)`
  have hchart : ∀ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
      IsOpen V → IsOpen W → ContDiffOn ℝ (1 : ℕ) ψ V → InjOn ψ V → ψ '' V = W ∩ N →
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) →
      IsOpen (Φ '' W) ∧ ContDiffOn ℝ (1 : ℕ) (Φ ∘ ψ) V ∧ InjOn (Φ ∘ ψ) V ∧
        (Φ ∘ ψ) '' V = Φ '' W ∩ Φ '' N ∧
        (∀ K ⊆ Φ '' W, IsCompact K → IsCompact (V ∩ (Φ ∘ ψ) ⁻¹' K)) ∧
        ∀ z ∈ V, Injective (fderiv ℝ (Φ ∘ ψ) z) := by
    intro V W ψ hV hW hψ hinj hψV hproper hDψ
    refine ⟨hopen W hW, hΦ1.comp_contDiffOn hψ, hbij.injective.comp_injOn hinj, ?_, ?_, ?_⟩
    · -- `Φ(ψ(V)) = Φ(W ∩ N) = Φ(W) ∩ Φ(N)`, `Φ` being injective
      rw [image_comp, hψV, image_inter hbij.injective]
    · -- `Φ⁻¹(K)` is a compact subset of `W`
      intro K hKW hK
      have hK' : Φ ⁻¹' K ⊆ W := by
        intro z hz
        obtain ⟨w, hw, hwz⟩ := hKW hz
        rwa [← hbij.injective hwz]
      exact hproper _ hK' (hcpt K hK)
    · -- chain rule: `D(Φ ∘ ψ)(z) = DΦ(ψ(z)) ∘ Dψ(z)`, a composition of injective maps
      intro z hz
      have hψ1 : ContDiffOn ℝ 1 ψ V := by exact_mod_cast hψ
      have hψz : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
        ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)).hasFDerivAt
      have hΦz : HasFDerivAt Φ (fderiv ℝ Φ (ψ z)) (ψ z) :=
        (hΦ.differentiable one_ne_zero (ψ z)).hasFDerivAt
      rw [(hΦz.comp z hψz).fderiv, ContinuousLinearMap.coe_comp]
      exact (hDΦ (ψ z)).comp (hDψ z hz)
  refine ⟨?_, ?_⟩
  · -- `Φ(N)` is an embedded `d`-dimensional `C¹` submanifold
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, hψV, hproper, hDψ⟩ := hN y hy
    obtain ⟨hW', hψ', hinj', hψV', hproper', hDψ'⟩ :=
      hchart V W ψ hV hW hψ hinj hψV hproper hDψ
    exact ⟨V, Φ '' W, Φ ∘ ψ, hV, hW', mem_image_of_mem Φ hyW, hψ', hinj', hψV', hproper', hDψ'⟩
  · -- Step 3: the tangent spaces, by `chart_tangentSpace_eq_range_fderiv` for both charts
    intro x hx
    obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hinj, hψV, hproper, hDψ⟩ := hN x hx
    obtain ⟨hW', hψ', hinj', hψV', hproper', hDψ'⟩ :=
      hchart V W ψ hV hW hψ hinj hψV hproper hDψ
    obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := hψV ▸ ⟨hxW, hx⟩
    have hTN := Submission.chart_tangentSpace_eq_range_fderiv P d 1 N W V ψ v le_rfl hV hW hψ
      hinj hψV hproper hDψ hv
    have hTΦN := Submission.chart_tangentSpace_eq_range_fderiv P d 1 (Φ '' N) (Φ '' W) V
      (Φ ∘ ψ) v le_rfl hV hW' hψ' hinj' hψV' hproper' hDψ' hv
    have hψ1 : ContDiffOn ℝ 1 ψ V := by exact_mod_cast hψ
    have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
      ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
    have hΦv : HasFDerivAt Φ (fderiv ℝ Φ (ψ v)) (ψ v) :=
      (hΦ.differentiable one_ne_zero (ψ v)).hasFDerivAt
    calc tangentSpace (Φ '' N) (Φ (ψ v)) = range (fderiv ℝ (Φ ∘ ψ) v) := hTΦN
      _ = range (fderiv ℝ Φ (ψ v) ∘ fderiv ℝ ψ v) := by
        rw [(hΦv.comp v hψv).fderiv, ContinuousLinearMap.coe_comp]
      _ = fderiv ℝ Φ (ψ v) '' tangentSpace N (ψ v) := by rw [range_comp, hTN]

/-- **Approximate tangent space of an embedded `C¹` submanifold** (Simon Ch. 3, 1.4; the step
"since `x ∈ Nⱼ` and `Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`"
of the proof of 1.6 "⇒", chapter-03.txt lines 113–126).  Let `ψ : V → W₀` be a local
representation of `N` (Ch. 2, (4.1)) with `x = ψ(v₀)`, so that `Q = TₓN = Dψ(v₀)(ℝᵐ)` (Ch. 2,
(4.3)).  For a small ball `B_ρ(v₀) ⊆ V`, `Dψ(v₀)(ℝᵐ)` is the approximate tangent space of
`ψ(B_ρ(v₀))` at `x` (area formula and dominated convergence).  As `ψ` is proper and 1:1,
`N ∩ W` and `ψ(B_ρ(v₀))` agree on some ball `B_δ(x)`, and approximate tangent spaces at `x` only
depend on the set near `x`. -/
theorem Submission.codim1_ac_submanifold_approxTangent : ∀ (P m : ℕ) (N W : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 1 ≤ m → IsEmbeddedSubmanifold 1 m N → IsOpen W → x ∈ N ∩ W → (Q : Set (Euclid P)) = tangentSpace N x → HasApproximateTangentSpaceAt m (N ∩ W) x Q := by
  intro P m N W x Q _ hN hW hx hQ
  -- Step 1, a local representation `ψ : V → W₀` of `N` with `x = ψ(v₀)`
  obtain ⟨V, W₀, ψ, hV, hW₀, hxW₀, hψ, hinj, hψV, hproper, hDψ⟩ := hN x hx.1
  obtain ⟨v₀, hv₀, rfl⟩ : x ∈ ψ '' V := hψV ▸ ⟨hxW₀, hx.1⟩
  have hψ1 : ContDiffOn ℝ 1 ψ V := by exact_mod_cast hψ
  -- `Q = T_{ψ(v₀)}N = Dψ(v₀)(ℝᵐ)`
  have hQA : Q = LinearMap.range (fderiv ℝ ψ v₀ : Euclid m →ₗ[ℝ] Euclid P) := by
    refine SetLike.ext' ?_
    rw [hQ, LinearMap.coe_range, Submission.chart_tangentSpace_eq_range_fderiv P m 1 N W₀ V ψ v₀
      le_rfl hV hW₀ hψ hinj hψV hproper hDψ hv₀]
    rfl
  subst hQA
  -- Step 2, `Dψ(v₀)(ℝᵐ)` is the approximate tangent space of `ψ(B_ρ(v₀))` at `ψ(v₀)`
  obtain ⟨ρ, hρ, hρV, hT⟩ :=
    Submission.codim1_ac_sat_chart_ball_approxTangent P m V ψ v₀ hV hψ1 hv₀ (hDψ v₀ hv₀)
  -- Step 3, `N ∩ W` and `ψ(B_ρ(v₀))` agree on a ball `B_δ(ψ(v₀))`
  obtain ⟨δ, hδ, hloc⟩ := Submission.codim1_ac_sat_chart_localization P m N W W₀ V ψ v₀ ρ hW hW₀
    hψ.continuousOn hinj hψV hproper hv₀ hx.2 hρ hρV
  -- Step 4, approximate tangent spaces only depend on the set near the point
  exact Submission.codim1_ac_sat_approxTangent_of_local_eq P m (N ∩ W) (ψ '' ball v₀ ρ) (ψ v₀) _ δ
    hδ hloc hT

/-- **Area formula on an embedded `C¹` submanifold** (Simon Ch. 2, 4.11–4.13, from the parametric
area formula 3.2).  Let `N ⊆ ℝᴾ` be an embedded `m`-dimensional `C¹` submanifold, `Q(x) = T_xN`
for `x ∈ N`, and `Φ : ℝᴾ → ℝᴾ` injective and `C¹` with `DΦ(x)` injective.  Put
`J(x) = √det(⟨DΦ(x)eᵢ, DΦ(x)eⱼ⟩)`, `e` the standard orthonormal basis of `Q(x)`.  Then `J` is
continuous on `N`, and `∫_{Φ(B)} g dHᵐ = ∫_B J · (g ∘ Φ) dHᵐ` for every Borel `B ⊆ N` and every
`g ≥ 0`.  Each `y ∈ N` lies in the open set `W` of a local representation `ψ : V → W` (4.1), and
the chart area formula gives the identity for every Borel `B ⊆ W ∩ N` and every `g`; as `Φ` is
continuous and injective, these local identities glue over a countable subcover of `N`. -/
theorem Submission.codim1_ac_submanifold_area_formula : ∀ (P m : ℕ) (N : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (Φ : Euclid P → Euclid P), 1 ≤ m → IsEmbeddedSubmanifold 1 m N → (∀ x ∈ N, (Q x : Set (Euclid P)) = tangentSpace N x) → ContDiff ℝ 1 Φ → Injective Φ → (∀ x, Injective (fderiv ℝ Φ x)) → ContinuousOn (fun x => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) j))))) N ∧ ∀ B : Set (Euclid P), B ⊆ N → MeasurableSet B → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in Φ '' B, g y ∂μHE[m] = ∫⁻ x in B, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ Φ x (stdOrthonormalBasis ℝ (Q x) j))))) * g (Φ x) ∂μHE[m] := by
  intro P m N Q Φ _ hN hQ hΦ hΦinj hDΦ
  -- `J` is continuous on `N`
  refine ⟨Submission.codim1_ac_saf_jacobian_continuousOn P m N Q Φ hN hQ hΦ, ?_⟩
  -- the area formula on `N` glues from its restrictions to the chart sets `W ∩ N`
  refine Submission.codim1_ac_saf_lintegral_image_of_local P μHE[m] N Φ _ hΦ.continuous hΦinj ?_
  intro y hy
  -- `y` lies in the open set `W` of a local representation `ψ : V → W` of `N` (`r = 1`)
  obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hψinj, hψV, hproper, hDψ⟩ := hN y hy
  exact ⟨W, hW, hyW, Submission.codim1_ac_saf_chart_area_formula P m 1 N W V ψ Q Φ le_rfl hV hW
    hψ hψinj hψV hproper hDψ hQ hΦ hΦinj hDΦ⟩
/-- Steps 3–5 of the orientation push-forward (Simon 6.3.4–3.5, with the orthonormal basis of
`span v` chosen by Gram–Schmidt): a linearly independent family `v` in `ℝᴾ` has an orthonormal
frame `σ` with the same span such that `A = (⟨σᵢ, vⱼ⟩)` satisfies `det(⟨vᵢ, vⱼ⟩) = (det A)²`,
`det A ≠ 0` and `|det A| ≤ ∏ᵢ |vᵢ|`.  Gram–Schmidt in `W = span v` makes `A` the upper-triangular
matrix of `v` in an orthonormal basis of `W`, and Parseval gives `(⟨vᵢ, vⱼ⟩) = AᵀA`. -/
theorem Submission.dpf_exists_orthonormal_frame_det_gram : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Submodule.span ℝ (Set.range v) ∧ Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ^ 2 ∧ Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ≠ 0 ∧ |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| ≤ ∏ i, ‖v i‖ := by
  intro P n v hv
  set W := Submodule.span ℝ (Set.range v)
  -- `v` regarded in `W` is a linearly independent spanning family `w`
  let w : Fin n → W := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp W.subtype hv
  have hspan_w : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  -- the Gram–Schmidt orthonormal basis `b` of `W`, and `σ = b` regarded in `ℝᴾ`
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  -- `A` is the (upper-triangular) matrix of `w` in the basis `b`
  have hA : (Matrix.of fun i j => inner ℝ (σ i) (v j)) = b.toBasis.toMatrix w := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, Submodule.coe_inner]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) =
      ∏ i, inner ℝ (σ i) (v i) := by
    rw [hA, ← Module.Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    rfl
  refine ⟨σ, b.orthonormal.comp_linearIsometry W.subtypeₗᵢ, ?_, ?_, ?_, ?_⟩
  · -- `span σ = W`
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
    have hσ : Set.range σ = W.subtype '' Set.range b := Set.range_comp _ _
    rw [hσ, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
  · -- Parseval: `(⟨vᵢ, vⱼ⟩) = AᵀA`
    have hG : (Matrix.of fun i j => inner ℝ (v i) (v j)) =
        Matrix.transpose (Matrix.of fun i j => inner ℝ (σ i) (v j)) *
          Matrix.of fun i j => inner ℝ (σ i) (v j) := by
      ext i j
      have hp := b.sum_inner_mul_inner (w i) (w j)
      simp only [Submodule.coe_inner] at hp
      rw [Matrix.mul_apply, Matrix.of_apply, ← hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, real_inner_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  · -- `det A = det_b w` is a unit
    rw [hA, ← Module.Basis.det_apply]
    exact ((Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩).ne_zero
  · -- Cauchy–Schwarz on the diagonal entries
    rw [hdet, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |inner ℝ (σ i) (v i)| ≤ ‖σ i‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖v i‖ := by rw [show ‖σ i‖ = 1 from b.norm_eq_one i, one_mul]
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

/-- Orientation of the push-forward by an injective linear map (Simon Ch. 6, 3.4–3.5 and 3.7:
`L_#ξ = J η`): if `ξ` is a unit orientation of `Q`, `ζ(β) = ξ(β ∘ L)` and
`J = (det(Leₐ · Le_b))^{1/2}` for the orthonormal basis `e` of `Q`, then `0 < J ≤ ‖L‖ⁿ` and `J⁻¹ζ`
is a unit orientation of `L(Q)`.  With `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` and `σ` an orthonormal frame of
`span (Lτ) = L(Q)`, `β(Lτ) = det A · β(σ)` for `A = (⟨σᵢ, Lτⱼ⟩)`, and `J = |det A|`. -/
theorem Submission.dpf_unitOrientation_map_gramNormalized : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n) (L : Euclid P →L[ℝ] Euclid P) (J : ℝ), IsUnitOrientationOf ξ Q → Injective L → J = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ Q) => inner ℝ (L (stdOrthonormalBasis ℝ Q i)) (L (stdOrthonormalBasis ℝ Q j)))) → 0 < J ∧ J ≤ ‖L‖ ^ n ∧ IsUnitOrientationOf (J⁻¹ • ξ.comp (ContinuousAlternatingMap.compContinuousLinearMapCLM L)) (Submodule.map (L : Euclid P →ₗ[ℝ] Euclid P) Q) := by
  intro P n Q ξ L J hξ hL hJ
  -- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `Q`
  obtain ⟨τ, hτ, hτQ, hξτ⟩ := hξ
  -- `Lτ` is linearly independent; let `σ` be an orthonormal frame of `span (Lτ)` (Gram–Schmidt)
  have hv : LinearIndependent ℝ fun i => L (τ i) :=
    hτ.linearIndependent.map' (L : Euclid P →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.mpr hL)
  obtain ⟨σ, hσ, hσv, hdet, hA0, hAle⟩ :=
    Submission.dpf_exists_orthonormal_frame_det_gram P n (fun i => L (τ i)) hv
  -- `α(Lτ) = det A · α(σ)` for every `n`-covector `α`, where `A = (⟨σᵢ, Lτⱼ⟩)`: the restriction
  -- of `α` to `span σ` is `α(σ) det_σ`, and the coordinates of `Lτⱼ` in the basis `σ` are `Aᵢⱼ`
  have hcov : ∀ α : Covector (Euclid P) n, α (fun j => L (τ j)) =
      (Matrix.of fun i j => inner ℝ (σ i) (L (τ j))).det * α σ := by
    intro α
    set S := Submodule.span ℝ (Set.range σ)
    have hvS : ∀ j, L (τ j) ∈ S := fun j => by
      rw [hσv]
      exact Submodule.subset_span (Set.mem_range_self j)
    let e : Module.Basis (Fin n) ℝ S := Module.Basis.span hσ.linearIndependent
    have he : ∀ i, (e i : Euclid P) = σ i := fun i => by
      rw [Module.Basis.span_apply hσ.linearIndependent i]
    let αS : S [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap S.subtype
    let w : Fin n → S := fun j => ⟨L (τ j), hvS j⟩
    have h1 : α (fun j => L (τ j)) = αS w := rfl
    have h2 : α σ = αS e := by
      show α σ = α (fun i => (e i : Euclid P))
      congr 1
      funext i
      exact (he i).symm
    have hrepr : ∀ i j, e.repr (w j) i = inner ℝ (σ i) (L (τ j)) := by
      intro i j
      have hs : L (τ j) = ∑ l, e.repr (w j) l • σ l := by
        have := congrArg Subtype.val (e.sum_repr (w j))
        simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
        exact this.symm
      rw [hs, hσ.inner_right_fintype]
    have hmat : e.toMatrix w = Matrix.of fun i j => inner ℝ (σ i) (L (τ j)) := by
      ext i j
      rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
    have h3 : αS w = αS e * e.det w := by
      conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αS]
      rfl
    rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]
  generalize (Matrix.of fun i j => inner ℝ (σ i) (L (τ j))).det = d at hdet hA0 hAle hcov
  -- `J = √(det G(Le)) = √(det G(Lτ)) = √((det A)²) = |det A|`
  have hJd : J = |d| := by
    rw [hJ, Submission.dpf_det_gram_stdOrthonormalBasis_eq P n Q L τ hτ hτQ, hdet,
      Real.sqrt_sq_eq_abs]
  refine ⟨by rw [hJd]; exact abs_pos.mpr hA0, ?_, σ, hσ, ?_, ?_⟩
  · -- `J = |det A| ≤ ∏ᵢ ‖Lτᵢ‖ ≤ ‖L‖ⁿ`
    rw [hJd]
    refine hAle.trans ?_
    calc ∏ i, ‖L (τ i)‖ ≤ ∏ _i : Fin n, ‖L‖ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => by
            simpa [hτ.1 i] using L.le_opNorm (τ i)
      _ = ‖L‖ ^ n := by simp
  · -- `span σ = span (Lτ) = L(span τ) = L(Q)`
    rw [hσv, ← hτQ, Submodule.map_span, ← Set.range_comp]
    rfl
  · -- `(J⁻¹ζ)(α) = J⁻¹ ξ(α ∘ L) = ±J⁻¹ α(Lτ) = ±(J⁻¹ det A) α(σ)` with `J⁻¹ det A = ±1`
    have hζ : ∀ α : Covector (Euclid P) n,
        (J⁻¹ • ξ.comp (ContinuousAlternatingMap.compContinuousLinearMapCLM L)) α =
          J⁻¹ * ξ (α.compContinuousLinearMap L) := fun α => rfl
    have hατ : ∀ α : Covector (Euclid P) n, α.compContinuousLinearMap L τ = d * α σ :=
      fun α => hcov α
    have hsign : J⁻¹ * d = 1 ∨ J⁻¹ * d = -1 := by
      rw [hJd]
      rcases hA0.lt_or_gt with h | h
      · exact Or.inr (by rw [abs_of_neg h, inv_neg, neg_mul, inv_mul_cancel₀ hA0])
      · exact Or.inl (by rw [abs_of_pos h, inv_mul_cancel₀ hA0])
    rcases hξτ with hξτ | hξτ <;> rcases hsign with hs | hs
    · exact Or.inl fun α => by rw [hζ, hξτ, hατ]; linear_combination α σ * hs
    · exact Or.inr fun α => by rw [hζ, hξτ, hατ]; linear_combination α σ * hs
    · exact Or.inr fun α => by rw [hζ, hξτ, hατ]; linear_combination -α σ * hs
    · exact Or.inl fun α => by rw [hζ, hξτ, hατ]; linear_combination -α σ * hs
/-- The derivative bound behind Simon 6.2.24(2)–(3) (push-forward by a `C¹` map): if `φ` is `C¹`
on `ℝᴾ` and `φ(x) = x` off a compact set `K`, then `‖Dφ(x)‖ ≤ Λ` for some `Λ ≥ 0` and all `x`.
`Dφ` is continuous, hence bounded by some `c` on `K`; off the closed set `K`, `φ = id` near `x`,
so `Dφ(x) = id` has norm `≤ 1`.  Take `Λ = max(1, c)`. -/
theorem Submission.dpf_pfc_fderiv_norm_le_of_eq_id_off_compact : ∀ (P : ℕ) (K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsCompact K → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x, ‖fderiv ℝ φ x‖ ≤ Λ := by
  intro P K φ hK hφ hid
  -- `Dφ` is continuous, so it is bounded by some `c` on the compact set `K`
  obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max 1 c, zero_le_one.trans (le_max_left _ _), fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hc x hx).trans (le_max_right _ _)
  · -- off the closed set `K`, `φ = id` near `x`, so `Dφ(x) = id` has norm `≤ 1`
    have h : φ =ᶠ[𝓝 x] id := eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) hid
    rw [h.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
/-- Simon 6.3.1: `Hⁿ`-a.e. on `M` the orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` of an integer
multiplicity triple is a unit simple `n`-vector (`τ` orthonormal), so every `n`-covector `β`
satisfies `|⟨β, ξ(x)⟩| = |β(τ₁, …, τₙ)| ≤ ‖β‖ ∏ᵢ ‖τᵢ‖ = ‖β‖` (operator norm). -/
theorem Submission.dpf_pfc_imrep_orient_abs_apply_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ β : Covector (Euclid P) n, |R.orient x β| ≤ ‖β‖ := by
  intro P n U R
  filter_upwards [R.orients] with x hx β
  -- `ξ(x)` is `±` evaluation at an orthonormal frame `τ`
  obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
  have hβ : |β τ| ≤ ‖β‖ :=
    calc |β τ| = ‖β τ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖β‖ * ∏ i, ‖τ i‖ := β.le_opNorm τ
      _ = ‖β‖ := by rw [Finset.prod_eq_one fun i _ => hτ.1 i, mul_one]
  rcases hξ with h | h
  · rw [h β]
    exact hβ
  · rw [h β, abs_neg]
    exact hβ

/-- **Pairing bound for `τ(M, θ, ξ)`** (the estimate behind Simon 6.2.24(2)).  If `F` is
`Hⁿ⌞M`-a.e. strongly measurable, vanishes off the compact `C ⊆ U` and `‖F‖ ≤ B`, then
`θ ⟨F, ξ⟩` is `Hⁿ⌞M`-integrable and `|∫_M θ ⟨F, ξ⟩ dHⁿ| ≤ B ∫_{M ∩ C} θ dHⁿ`.  By
`dpf_pfc_imrep_orient_abs_apply_le`, `|θ ⟨F, ξ⟩| ≤ B θ 1_C` a.e., and `θ 1_C` is integrable by
the local integrability of `θ`. -/
theorem Submission.dpf_pfc_imrep_pairing_integrable_abs_le : ∀ (P n : ℕ) (U C : Set (Euclid P)) (R : IMRep U n) (F : Euclid P → Covector (Euclid P) n) (B : ℝ), IsCompact C → C ⊆ U → AEStronglyMeasurable F (μHE[n].restrict R.carrier) → (∀ x, x ∉ C → F x = 0) → (∀ x, ‖F x‖ ≤ B) → Integrable (fun x => (R.mult x : ℝ) * R.orient x (F x)) (μHE[n].restrict R.carrier) ∧ |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F x) ∂μHE[n]| ≤ B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
  intro P n U C R F B hC hCU hF hF0 hFB
  -- Step 1: `C` is measurable; step 2: `θ` is measurable
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hθm : Measurable fun x => (R.mult x : ℝ) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult
  -- Step 3: `μ.restrict C = Hⁿ⌞(M ∩ C)`
  have hres : (μHE[n].restrict R.carrier).restrict C = μHE[n].restrict (R.carrier ∩ C) := by
    rw [Measure.restrict_restrict hCm, inter_comm]
  -- Step 4: `θ` is integrable on `C`, so `g = B · 1_C θ` is integrable
  have hθC : IntegrableOn (fun x => (R.mult x : ℝ)) C (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hres]
    simpa using (R.locallyIntegrable_mult C hC hCU).lt_top
  have hg : Integrable (fun x => B * C.indicator (fun y => (R.mult y : ℝ)) x)
      (μHE[n].restrict R.carrier) :=
    ((integrable_indicator_iff hCm).2 hθC).const_mul B
  -- Step 5: `h = θ · ξ(F)` is a.e. strongly measurable
  have hh : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (F x))
      (μHE[n].restrict R.carrier) :=
    hθm.aestronglyMeasurable.mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      R.aestronglyMeasurable_orient hF)
  -- Step 6: `|h| ≤ g` a.e., by `orient_bound`
  have hdom : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (F x)‖ ≤ B * C.indicator (fun y => (R.mult y : ℝ)) x := by
    filter_upwards [Submission.dpf_pfc_imrep_orient_abs_apply_le P n U R] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (F x)).trans (hFB x)) (Nat.cast_nonneg _)
    · simp [indicator_of_notMem hxC, hF0 x hxC]
  -- Step 7: integrability
  refine ⟨hg.mono' hh hdom, ?_⟩
  -- Step 8: `∫ g dμ = B · (∫⁻_{M ∩ C} θ dHⁿ).toReal`
  have hgval : ∫ x, B * C.indicator (fun y => (R.mult y : ℝ)) x ∂(μHE[n].restrict R.carrier) =
      B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    rw [integral_const_mul, integral_indicator hCm, hres,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => Nat.cast_nonneg _)
        hθm.aestronglyMeasurable]
    simp
  -- Step 9: `|∫ h dμ| ≤ ∫ g dμ`
  rw [← Real.norm_eq_abs, ← hgval]
  exact norm_integral_le_of_norm_le hg hdom
/-- **Simon §6.1** (the test-form topology, the case `β = 0`): if `ωⱼ → 0` in `𝒟ⁿ(U)`, the
`ωⱼ` vanish outside one compact `C ⊆ U`, and `supₓ ‖ωⱼ(x)‖ → 0`.  The compact set is the one in
`TestFormOnConverges`; uniform convergence of the `0`-th iterated derivatives on `C` gives the
bound on `C`, and `ωⱼ = 0` off `C`. -/
theorem Submission.dpf_pfc_testFormOnConverges_zero_uniform : ∀ (P n : ℕ) (U : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), TestFormOnConverges ωs 0 → ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ U ∧ (∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε := by
  intro P n U ωs h
  obtain ⟨C, hC, hCU, hsupp, -, hderiv⟩ := h
  have hzero : ∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')
  refine ⟨C, hC, hCU, hzero, fun ε hε => ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hderiv 0) ε hε] with j hj x
  by_cases hx : x ∈ C
  · have hjx := hj x hx
    simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
      norm_iteratedFDeriv_zero] at hjx
    exact hjx.le
  · rw [hzero j x hx, norm_zero]
    exact hε.le

/-- **Simon 6.2.23–2.24 (2)–(3)** (chapter-06.txt lines 403–440): for a triple `R = (M, θ, ξ)` in
`U` and a `C¹` map `φ` equal to the identity off a compact `K ⊆ U`, the push-forward formula
`ω ↦ ∫_M θ(x) ⟨ω(φ(x)) ∘ Dφ(x), ξ(x)⟩ dHⁿ(x)` defines a current in `U`.  With `‖Dφ‖ ≤ Λ`, the
covector field `F_ω(x) = ω(φ(x)) ∘ Dφ(x)` is continuous, vanishes off the compact set
`tsupport ω ∪ K ⊆ U` and has `‖F_ω‖ ≤ sup ‖ω‖ · Λⁿ`; this gives integrability, hence linearity.
If `ωⱼ → 0`, then `F_{ωⱼ}` vanishes off a fixed compact `C ∪ K` and is eventually bounded by
`η Λⁿ`, which gives sequential continuity. -/
theorem Submission.dpf_pushforward_formula_current_exists : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n) (φ : Euclid P → Euclid P), IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n] := by
  intro P n U K R φ hK hKU hφ hid
  -- step 1: `‖Dφ(x)‖ ≤ Λ` for every `x`
  obtain ⟨Λ, hΛ0, hΛ⟩ := Submission.dpf_pfc_fderiv_norm_le_of_eq_id_off_compact P K φ hK hφ hid
  -- the pulled-back covector field `F ω x = ω(φ(x)) ∘ Dφ(x)`
  set F : DifferentialForm (Euclid P) n → Euclid P → Covector (Euclid P) n :=
    fun ω x => (ω (φ x)).compContinuousLinearMap (fderiv ℝ φ x) with hFdef
  have hFcont : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω → Continuous (F ω) := by
    intro ω hω
    have h := (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM (𝕜 := ℝ)
      (ι := Fin n) (G := ℝ) |>.comp (hφ.continuous_fderiv one_ne_zero)).clm_apply
      (hω.comp hφ.continuous)
    simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
      using h
  -- step 2: `‖F ω‖ ≤ B Λⁿ` when `‖ω‖ ≤ B`
  have hFnorm : ∀ (ω : DifferentialForm (Euclid P) n) (B : ℝ), (∀ y, ‖ω y‖ ≤ B) →
      ∀ x, ‖F ω x‖ ≤ B * Λ ^ n := by
    intro ω B hB x
    calc ‖F ω x‖ ≤ ‖ω (φ x)‖ * ‖fderiv ℝ φ x‖ ^ n := by
          simpa only [Fintype.card_fin] using
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le (ω (φ x)) (fderiv ℝ φ x)
      _ ≤ B * Λ ^ n := mul_le_mul (hB _) (pow_le_pow_left₀ (norm_nonneg _) (hΛ x) n)
          (pow_nonneg (norm_nonneg _) n) ((norm_nonneg _).trans (hB (φ x)))
  -- step 3: `F ω` vanishes off `C ∪ K` when `ω` vanishes off `C`
  have hFzero : ∀ (ω : DifferentialForm (Euclid P) n) (C : Set (Euclid P)),
      (∀ y, y ∉ C → ω y = 0) → ∀ x, x ∉ C ∪ K → F ω x = 0 := by
    intro ω C hC x hx
    rw [mem_union, not_or] at hx
    ext v
    simp [hFdef, hid x hx.2, hC x hx.1]
  -- `F ω x` is linear in `ω`
  have hFadd : ∀ (ω₁ ω₂ : DifferentialForm (Euclid P) n) x, F (ω₁ + ω₂) x = F ω₁ x + F ω₂ x := by
    intro ω₁ ω₂ x
    ext v
    simp [hFdef]
  have hFsmul : ∀ (c : ℝ) (ω : DifferentialForm (Euclid P) n) x, F (c • ω) x = c • F ω x := by
    intro c ω x
    ext v
    simp [hFdef]
  -- step 4: the integrand of a test form is integrable
  have hint : ∀ ω : TestFormOn U n, Integrable
      (fun x => (R.mult x : ℝ) * R.orient x (F (ω : DifferentialForm (Euclid P) n) x))
      (μHE[n].restrict R.carrier) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous ω.property.1.1
    obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
    exact (Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U
      (tsupport (ω : DifferentialForm (Euclid P) n) ∪ K) R (F ω) (B * Λ ^ n)
      (ω.property.1.2.isCompact.union hK) (union_subset ω.property.2 hKU)
      (hFcont _ hωc).aestronglyMeasurable
      (hFzero _ _ fun y hy => image_eq_zero_of_notMem_tsupport hy) (hFnorm _ _ hB)).1
  -- step 5: the action is linear
  let S₀ : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω =>
        ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F (ω : DifferentialForm (Euclid P) n) x)
          ∂μHE[n]
      map_add' := fun ω₁ ω₂ => by
        rw [← integral_add (hint ω₁) (hint ω₂)]
        congr 1
        ext x
        rw [Submodule.coe_add, hFadd, map_add, mul_add]
      map_smul' := fun c ω => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        ext x
        rw [Submodule.coe_smul, hFsmul, map_smul, smul_eq_mul, mul_left_comm] }
  -- steps 6–7: sequential continuity, and the action is the push-forward formula by definition
  refine ⟨⟨S₀, fun ωs hωs => ?_⟩, fun ω => rfl⟩
  obtain ⟨C, hC, hCU, hCzero, hsmall⟩ :=
    Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
  set I : ℝ := (∫⁻ x in R.carrier ∩ (C ∪ K), (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal
  have hI : 0 ≤ Λ ^ n * I := mul_nonneg (pow_nonneg hΛ0 n) ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε / (Λ ^ n * I + 1) := div_pos hε (by linarith)
  filter_upwards [hsmall _ hη] with j hj
  have hb := (Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U (C ∪ K) R
    (F (ωs j : DifferentialForm (Euclid P) n)) (ε / (Λ ^ n * I + 1) * Λ ^ n) (hC.union hK)
    (union_subset hCU hKU)
    (hFcont _ (ContDiff.continuous (ωs j).property.1.1)).aestronglyMeasurable
    (hFzero _ _ (hCzero j)) (hFnorm _ _ hj)).2
  rw [Real.dist_eq, sub_zero]
  calc |S₀ (ωs j)| ≤ ε / (Λ ^ n * I + 1) * Λ ^ n * I := hb
    _ = ε * (Λ ^ n * I / (Λ ^ n * I + 1)) := by ring
    _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by linarith)).2 (lt_add_one _))

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
