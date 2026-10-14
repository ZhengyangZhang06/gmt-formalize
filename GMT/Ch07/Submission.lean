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
/-- **Simon Ch. 6, 2.4–2.5 and 3.2(1)**, algebra of integer multiplicity currents.  (a) The zero
current is integer multiplicity (empty carrier).  (b) If `A = pB + qC` with `p, q ∈ ℤ`, then
`M_W(A) ≤ |p| M_W(B) + |q| M_W(C)`: `−ω` is admissible with `ω`, so `|X(ω)| ≤ M_W(X)`.  (c) If
differences of integer multiplicity currents in an open `U` are integer multiplicity, then every
finite integer combination `Y = Σᵢ mᵢSᵢ` of integer multiplicity currents is integer multiplicity
(`A + B = A − (0 − B)`), and `M_W(Y) ≤ Σᵢ |mᵢ| M_W(Sᵢ)`. -/
theorem Submission.cbr_cc_current_algebra : (∀ (P n : ℕ) (U : Set (Euclid P)), IsIntegerMultiplicity (0 : GeometricCurrentOn U n)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B C : GeometricCurrentOn U n) (p q : ℤ), (∀ ω : TestFormOn U n, A ω = (p : ℝ) * B ω + (q : ℝ) * C ω) → ∀ W : Set (Euclid P), A.massOn W ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W) ∧ ((∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (ι : Type) (F : Finset ι) (S : ι → GeometricCurrentOn U n) (m : ι → ℤ), IsOpen U → (∀ i ∈ F, IsIntegerMultiplicity (S i)) → ∃ Y : GeometricCurrentOn U n, IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U n, Y ω = ∑ i ∈ F, (m i : ℝ) * S i ω) ∧ ∀ W : Set (Euclid P), Y.massOn W ≤ ∑ i ∈ F, ((m i).natAbs : ℝ≥0∞) * (S i).massOn W) := by
  -- (a): the representation with empty carrier, zero multiplicity and zero orientation
  have hzero : ∀ (P n : ℕ) (U : Set (Euclid P)),
      IsIntegerMultiplicity (0 : GeometricCurrentOn U n) := by
    intro P n U
    refine ⟨{ carrier := ∅
              mult := fun _ => 0
              orient := fun _ => 0
              measurableSet_carrier := MeasurableSet.empty
              carrier_subset := empty_subset U
              rectifiable :=
                Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
              measurable_mult := measurable_const
              mult_pos := fun x hx => by simp at hx
              locallyIntegrable_mult := fun K _ _ => by simp
              aestronglyMeasurable_orient := aestronglyMeasurable_const
              orients := by simp }, ?_⟩
    intro ω
    simp [IMRep.action]
  -- `|X(ω)| ≤ M_W(X)` for admissible `ω`, since `−ω` is admissible as well
  have habs : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n)
      (W : Set (Euclid P)) (ω : TestFormOn U n), ω ∈ massAdmissibleOn U n W →
      ENNReal.ofReal |X ω| ≤ X.massOn W := by
    intro P n U X W ω hω
    rcases le_total 0 (X ω) with h | h
    · rw [abs_of_nonneg h]
      exact X.le_massOn hω
    · have hneg : -ω ∈ massAdmissibleOn U n W := by
        refine ⟨?_, fun x => ?_⟩
        · rw [Submodule.coe_neg, tsupport_neg]
          exact hω.1
        · rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
          exact hω.2 x
      rw [abs_of_nonpos h, ← map_neg X.toCurrent ω]
      exact X.le_massOn hneg
  -- one term `|k| |X(ω)| ≤ |k| M_W(X)` of an integer combination
  have hterm : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n) (k : ℤ)
      (W : Set (Euclid P)) (ω : TestFormOn U n), ω ∈ massAdmissibleOn U n W →
      ENNReal.ofReal (|(k : ℝ)| * |X ω|) ≤ (k.natAbs : ℝ≥0∞) * X.massOn W := by
    intro P n U X k W ω hω
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Int.cast_abs, ← Nat.cast_natAbs,
      ENNReal.ofReal_natCast]
    exact mul_le_mul' le_rfl (habs P n U X W ω hω)
  -- (b)
  have hmass : ∀ (P n : ℕ) (U : Set (Euclid P)) (A B C : GeometricCurrentOn U n) (p q : ℤ),
      (∀ ω : TestFormOn U n, A ω = (p : ℝ) * B ω + (q : ℝ) * C ω) → ∀ W : Set (Euclid P),
      A.massOn W ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W := by
    intro P n U A B C p q hA W
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    calc ENNReal.ofReal (A ω)
        ≤ ENNReal.ofReal (|(p : ℝ)| * |B ω| + |(q : ℝ)| * |C ω|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hA ω, ← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
      _ = ENNReal.ofReal (|(p : ℝ)| * |B ω|) + ENNReal.ofReal (|(q : ℝ)| * |C ω|) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W :=
          add_le_add (hterm P n U B p W ω hω) (hterm P n U C q W ω hω)
  refine ⟨hzero, hmass, ?_⟩
  -- (c)
  intro hsub P n U ι F S m hU hS
  classical
  have hsubapp : ∀ (A B : GeometricCurrentOn U n) (ω : TestFormOn U n),
      (A - B) ω = A ω - B ω := fun A B ω => rfl
  -- `A − (0 − B)` is integer multiplicity, with values `A(ω) + B(ω)`
  have hadd : ∀ A B : GeometricCurrentOn U n, IsIntegerMultiplicity A →
      IsIntegerMultiplicity B →
      IsIntegerMultiplicity (A - (0 - B)) ∧ ∀ ω, (A - (0 - B)) ω = A ω + B ω := by
    intro A B hA hB
    refine ⟨hsub P n U A (0 - B) hU hA (hsub P n U 0 B hU (hzero P n U) hB), fun ω => ?_⟩
    rw [hsubapp, hsubapp, GeometricCurrentOn.zero_apply]
    ring
  -- natural multiples `k X = X + ⋯ + X`
  have hnat : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X → ∀ k : ℕ,
      ∃ V : GeometricCurrentOn U n, IsIntegerMultiplicity V ∧ ∀ ω, V ω = (k : ℝ) * X ω := by
    intro X hX k
    induction k with
    | zero => exact ⟨0, hzero P n U, fun ω => by simp⟩
    | succ k ih =>
      obtain ⟨V, hV, hVω⟩ := ih
      obtain ⟨hV', hV'ω⟩ := hadd V X hV hX
      refine ⟨V - (0 - X), hV', fun ω => ?_⟩
      rw [hV'ω, hVω]
      push_cast
      ring
  -- integer multiples, `(−k) X = 0 − k X`
  have hint : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X → ∀ k : ℤ,
      ∃ V : GeometricCurrentOn U n, IsIntegerMultiplicity V ∧ ∀ ω, V ω = (k : ℝ) * X ω := by
    intro X hX k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · obtain ⟨V, hV, hVω⟩ := hnat X hX j
      exact ⟨V, hV, fun ω => by rw [hVω, Int.cast_natCast]⟩
    · obtain ⟨V, hV, hVω⟩ := hnat X hX j
      refine ⟨0 - V, hsub P n U 0 V hU (hzero P n U) hV, fun ω => ?_⟩
      rw [hsubapp, GeometricCurrentOn.zero_apply, hVω, Int.cast_neg, Int.cast_natCast]
      ring
  -- finite integer combinations, by induction on the index set
  have hsum : ∀ G : Finset ι, (∀ i ∈ G, IsIntegerMultiplicity (S i)) →
      ∃ Y : GeometricCurrentOn U n, IsIntegerMultiplicity Y ∧
        ∀ ω, Y ω = ∑ i ∈ G, (m i : ℝ) * S i ω := by
    intro G
    induction G using Finset.induction_on with
    | empty => exact fun _ => ⟨0, hzero P n U, fun ω => by simp⟩
    | insert j G hj ih =>
      intro hG
      obtain ⟨Y, hY, hYω⟩ := ih fun i hi => hG i (Finset.mem_insert_of_mem hi)
      obtain ⟨V, hV, hVω⟩ := hint (S j) (hG j (Finset.mem_insert_self j G)) (m j)
      obtain ⟨hY', hY'ω⟩ := hadd Y V hY hV
      refine ⟨Y - (0 - V), hY', fun ω => ?_⟩
      rw [hY'ω, hYω, hVω, Finset.sum_insert hj]
      ring
  obtain ⟨Y, hY, hYω⟩ := hsum F hS
  refine ⟨Y, hY, hYω, fun W => ?_⟩
  -- the mass bound, from `Y(ω) ≤ Σᵢ |mᵢ| |Sᵢ(ω)|` for admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (Y ω)
      ≤ ENNReal.ofReal (∑ i ∈ F, |(m i : ℝ)| * |S i ω|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hYω]
        exact Finset.sum_le_sum fun i _ => by rw [← abs_mul]; exact le_abs_self _
    _ = ∑ i ∈ F, ENNReal.ofReal (|(m i : ℝ)| * |S i ω|) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity
    _ ≤ ∑ i ∈ F, ((m i).natAbs : ℝ≥0∞) * (S i).massOn W :=
        Finset.sum_le_sum fun i _ => hterm P n U (S i) (m i) W ω hω
/-- **`H¹` on a line** (Simon Ch. 6, 2.2 and 2.4).  For a unit vector `τ`, `φ(u) = a + uτ` is an
isometry `ℝ → ℝᴾ` (`|φ(u) − φ(v)| = |u − v| |τ|`), hence a closed and so measurable embedding, and
`φ(A)` is Borel for Borel `A`.  On `ℝ`, `μHE[1]` is Lebesgue measure, and `μHE[1]` is preserved by
isometries: `H¹(φ(A)) = H¹(A) = L¹(A)`, and `φ_#L¹ = H¹⌞range φ` gives `H¹⌞φ(A) = φ_#(L¹⌞A)`, so
`∫_{φ(A)} h dH¹ = ∫_A h(a + uτ) du` for every `h` (change of variables along an embedding). -/
theorem Submission.cbr_cc_seg_line_hausdorff : ∀ (P : ℕ) (a τ : Euclid P), ‖τ‖ = 1 → ∀ A : Set ℝ, MeasurableSet A → MeasurableSet ((fun u : ℝ => a + u • τ) '' A) ∧ μHE[1] ((fun u : ℝ => a + u • τ) '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in (fun u : ℝ => a + u • τ) '' A, h x ∂μHE[1] = ∫ u in A, h (a + u • τ) := by
  intro P a τ hτ A hA
  set φ : ℝ → Euclid P := fun u => a + u • τ with hφ
  -- Step 1: `φ` is an isometry, `|φ(u) − φ(v)| = |(u − v)τ| = |u − v|`
  have hiso : Isometry φ := by
    refine Isometry.of_dist_eq fun u v => ?_
    rw [hφ, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hτ,
      mul_one]
  -- Step 2: hence a closed, so measurable, embedding, and `φ(A)` is Borel
  have hemb : MeasurableEmbedding φ := hiso.isClosedEmbedding.measurableEmbedding
  have hmeas : MeasurableSet (φ '' A) := hemb.measurableSet_image.mpr hA
  -- Step 3: on `ℝ`, `μHE[1]` is Lebesgue measure
  have hvol : (μHE[1] : Measure ℝ) = volume := by
    simpa only [Module.finrank_self] using
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  refine ⟨hmeas, ?_, fun h => ?_⟩
  -- Step 4: isometry invariance, `H¹(φ(A)) = H¹(A) = L¹(A)`
  · rw [hiso.euclideanHausdorffMeasure_image, hvol]
  -- Step 5: `H¹⌞φ(A) = (H¹⌞range φ)⌞φ(A) = (φ_#H¹)⌞φ(A) = φ_#(H¹⌞A) = φ_#(L¹⌞A)`
  · have hrestr : (μHE[1] : Measure (Euclid P)).restrict (φ '' A) = (volume.restrict A).map φ :=
      calc (μHE[1] : Measure (Euclid P)).restrict (φ '' A)
          = ((μHE[1] : Measure (Euclid P)).restrict (range φ)).restrict (φ '' A) := by
            rw [Measure.restrict_restrict hmeas, inter_eq_left.mpr (image_subset_range φ A)]
        _ = ((μHE[1] : Measure ℝ).map φ).restrict (φ '' A) := by
            rw [hiso.map_euclideanHausdorffMeasure]
        _ = (volume.restrict A).map φ := by
            rw [hemb.restrict_map, hemb.injective.preimage_image, hvol]
    -- Step 6: change of variables along the measurable embedding `φ`, for every `h`
    rw [hrestr, hemb.integral_map]

/-- **Approximate tangent line of an open segment** (Simon Ch. 3, 1.4).  If `|τ| = 1`, the open
segment `I = {a + uτ : 0 < u < ℓ}` has approximate tangent space `span{τ}` at every point
`x = a + s₀τ` of `I`.  Let `f ∈ C_c` vanish outside `B̄_ρ(0)` and `0 < r < min(s₀, ℓ − s₀)/ρ`.
Then `η_{x,r}(I) ⊆ span{τ}`, and every `y = cτ` with `f(y) ≠ 0` equals `η_{x,r}(a + (s₀ + rc)τ)`
with `s₀ + rc ∈ (0, ℓ)`.  So `∫_{η_{x,r}(I)} f dH¹ = ∫_{span{τ}} f dH¹` for all small `r > 0`. -/
theorem Submission.cbr_cc_seg_open_segment_tangent : ∀ (P : ℕ) (a τ : Euclid P) (ℓ : ℝ), ‖τ‖ = 1 → ∀ x ∈ (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ, HasApproximateTangentSpaceAt 1 ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) x (Submodule.span ℝ {τ}) := by
  intro P a τ ℓ hτ x hx
  -- Step 1: `x = a + s₀τ` with `0 < s₀ < ℓ`, and `dim span{τ} = 1` since `τ ≠ 0`
  obtain ⟨s₀, ⟨hs₀, hs₀ℓ⟩, rfl⟩ := hx
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  refine ⟨finrank_span_singleton hτ0, fun f => ?_⟩
  -- Step 2: `f y ≠ 0` implies `|y| ≤ ρ`
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
    f.hasCompactSupport.isCompact.isBounded
  set ρ := max R₀ 1
  have hρpos : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfρ : ∀ y, f y ≠ 0 → ‖y‖ ≤ ρ := by
    intro y hy
    have h := hR₀ (subset_tsupport f hy)
    rw [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  -- Step 3: `δ = min(s₀, ℓ - s₀)` and `0 < r < δ/ρ`
  set δ := min s₀ (ℓ - s₀)
  have hδpos : 0 < δ := lt_min hs₀ (sub_pos.mpr hs₀ℓ)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδpos hρpos)] with r hr
  obtain ⟨hr0, hrδ⟩ := hr
  have hrρ : r * ρ < δ := by rwa [lt_div_iff₀ hρpos] at hrδ
  -- Step 4: `η_r(a + uτ) = (r⁻¹(u - s₀))τ`, so `η_r(I) ⊆ span{τ}`
  have hη : ∀ u : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (a + s₀ • τ) r (a + u • τ) =
      (r⁻¹ * (u - s₀)) • τ := by
    intro u
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, mul_smul, sub_smul, add_sub_add_left_eq_sub]
  have hsub : Poincare.SimonGMT.Chapter03.blowUpMap (a + s₀ • τ) r ''
      ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) ⊆ (Submodule.span ℝ {τ} : Set (Euclid P)) := by
    rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨_, (hη u).symm⟩
  -- Step 6: `span{τ}` is closed, so the two integrals agree once `f = 0` on `span{τ} \ η_r(I)`
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (Submodule.closed_of_finiteDimensional _).measurableSet.nullMeasurableSet hsub
    (Eventually.of_forall fun y hy => ?_)
  -- Step 5: if `y = cτ` and `f y ≠ 0`, then `y = η_r(a + (s₀ + rc)τ)` with `s₀ + rc ∈ (0, ℓ)`
  by_contra hfy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy.1
  have hc : |c| ≤ ρ := by
    have h := hfρ _ hfy
    rwa [norm_smul, hτ, mul_one, Real.norm_eq_abs] at h
  have hrc : |r * c| < δ := by
    rw [abs_mul, abs_of_pos hr0]
    exact (mul_le_mul_of_nonneg_left hc hr0.le).trans_lt hrρ
  have hδs₀ : δ ≤ s₀ := min_le_left _ _
  have hδℓ : δ ≤ ℓ - s₀ := min_le_right _ _
  obtain ⟨hrc₁, hrc₂⟩ := abs_lt.mp hrc
  refine hy.2 ⟨a + (s₀ + r * c) • τ, ⟨s₀ + r * c, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
  rw [hη, add_sub_cancel_left, inv_mul_cancel_left₀ hr0.ne']

/-- **Fundamental theorem of calculus for a `0`-form along a segment** (Simon Ch. 6, 2.3: Stokes'
theorem `∂T(ω) = T(dω)` in dimension one).  For a smooth `0`-form `g` on `ℝᴾ`, `a, v ∈ ℝᴾ` and
`ℓ ≥ 0`, `∫_{(0,ℓ)} dg(a + uv)(v) du = g(a + ℓv)⟨⟩ − g(a)⟨⟩`.  The function `ĝ = g(·)⟨⟩` is
smooth, and `dg(y)(v) = Dĝ(y)v` since `removeNth 0` of a `1`-tuple is the empty tuple `⟨⟩`.  By
the chain rule `u ↦ ĝ(a + uv)` has the continuous derivative `Dĝ(a + uv)v`, and the FTC on
`[0, ℓ]` concludes (`(0, ℓ)` and `(0, ℓ]` differ by a null set). -/
theorem Submission.cbr_cc_seg_zero_form_ftc : ∀ (P : ℕ) (g : DifferentialForm (Euclid P) 0), IsSmoothForm g → ∀ (a v : Euclid P) (ℓ : ℝ), 0 ≤ ℓ → ∫ u in Ioo 0 ℓ, exteriorDerivative g (a + u • v) (fun _ => v) = g (a + ℓ • v) (fun i => i.elim0) - g a (fun i => i.elim0) := by
  intro P g hg a v ℓ hℓ
  set e : Fin 0 → Euclid P := fun i => i.elim0
  -- (1) `ĝ = g(·)⟨⟩ = ev_⟨⟩ ∘ g` is smooth
  have hĝ := (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ e).contDiff.comp hg
  have hĝd : Differentiable ℝ (fun y => g y e) := hĝ.differentiable (by simp)
  -- (2) `dg(y)(v) = Dĝ(y)v`: `removeNth 0` of a `1`-tuple is the empty tuple
  have hd : ∀ y, exteriorDerivative g y (fun _ => v) = fderiv ℝ (fun z => g z e) y v := by
    intro y
    rw [exteriorDerivative_apply ((hg.differentiable (by simp)) y), Fin.sum_univ_one]
    have hrm : (Fin.removeNth (0 : Fin 1) fun _ : Fin 1 => v) = e := Subsingleton.elim _ _
    simp [hrm]
  -- (3) chain rule: `d/du ĝ(a + uv) = Dĝ(a + uv)v`
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u => g (a + u • v) e)
      (fderiv ℝ (fun z => g z e) (a + u • v) v) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => a + u • v) v u := by
      simpa using ((hasDerivAt_id u).smul_const v).const_add a
    exact (hĝd (a + u • v)).hasFDerivAt.comp_hasDerivAt u h1
  -- (4) the derivative is continuous in `u`, hence interval integrable
  have hcont : Continuous (fun u : ℝ => fderiv ℝ (fun z => g z e) (a + u • v) v) :=
    ((hĝ.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  -- (5) `∫_{(0,ℓ)} = ∫_0^ℓ` for `ℓ ≥ 0`, then the FTC
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ]
  simp only [hd]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 ℓ), zero_smul, add_zero]
/-- **The oriented open segment as an integer multiplicity triple** (Simon 6.2.2, 6.3.1).  For a
unit vector `τ` and `ℓ > 0`, the triple `R = (I, 1, ζ₀)` with `I = φ((0, ℓ))`, `φ(u) = a + uτ`, and
`ζ₀ = τ` (`⟨α, ζ₀⟩ = α(τ)`) is an `IMRep` of degree `1` in `ℝᴾ`.  `I` is Borel with `H¹(I) = ℓ`
and `∫_I h dH¹ = ∫₀^ℓ h(a + uτ) du` (`line_hausdorff`); it lies in the range of the `1`-Lipschitz
map `w ↦ a + w₀τ`, so it is countably `1`-rectifiable; `ζ₀` orients `span{τ}`, the approximate
tangent space of `I` at each of its points (`open_segment_tangent`).  Hence `I ⊆ [a, a + ℓτ]`,
`μ_R(ℝᴾ) = H¹(I) < ∞`, and `R(ω) = ∫_I ω(x)(τ) dH¹(x) = ∫₀^ℓ ω(a + uτ)(τ) du`. -/
theorem Submission.cbr_cc_seg_segment_imrep : ∀ (P : ℕ) (a τ : Euclid P) (ℓ : ℝ), ‖τ‖ = 1 → 0 < ℓ → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.carrier ⊆ segment ℝ a (a + ℓ • τ) ∧ R.measure univ < ∞ ∧ ∀ ω : DifferentialForm (Euclid P) 1, R.action ω = ∫ u in Ioo 0 ℓ, ω (a + u • τ) (fun _ => τ) := by
  intro P a τ ℓ hτ hℓ
  -- Step 1: `I = φ((0, ℓ))` is Borel, `H¹(I) = ℓ < ∞`, and `∫_I h dH¹ = ∫₀^ℓ h ∘ φ`
  obtain ⟨hImeas, hIvol, hIint⟩ :=
    Submission.cbr_cc_seg_line_hausdorff P a τ hτ (Ioo 0 ℓ) measurableSet_Ioo
  have hIfin : μHE[1] ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) < ∞ := by
    rw [hIvol, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  -- Step 2: `ζ₀ = (α ↦ α(τ))` is a unit orientation of `span{τ}`
  let ζ₀ : MultiVector P 1 := ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => τ)
  have hζ₀ : IsUnitOrientationOf ζ₀ (Submodule.span ℝ {τ}) := by
    refine ⟨fun _ => τ, ?_, by rw [range_const], Or.inl fun α => rfl⟩
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, ite_eq_left rfl, real_inner_self_eq_norm_sq, hτ, one_pow]
  -- Step 3: `I` lies in the range of the `1`-Lipschitz map `w ↦ a + w₀τ`
  have hrect : CountablyRectifiable 1 ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) := by
    let F : EuclideanSpace ℝ (Fin 1) → Euclid P := fun w => a + w 0 • τ
    have hF : LipschitzWith 1 F := by
      refine LipschitzWith.of_dist_le_mul fun w w' => ?_
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
      calc ‖F w - F w'‖ = ‖(w - w') 0‖ := by
            simp only [F, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hτ, mul_one,
              PiLp.sub_apply]
        _ ≤ ‖w - w'‖ := PiLp.norm_apply_le _ _
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hF).mono ?_
    rintro _ ⟨u, -, rfl⟩
    exact ⟨EuclideanSpace.single 0 u, by simp [F]⟩
  -- Step 4: the triple `R = (I, 1, ζ₀)`
  let R : IMRep (univ : Set (Euclid P)) 1 :=
    { carrier := (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ
      mult := fun _ => 1
      orient := fun _ => ζ₀
      measurableSet_carrier := hImeas
      carrier_subset := subset_univ _
      rectifiable := hrect
      measurable_mult := measurable_const
      mult_pos := fun _ _ => Nat.one_pos
      locallyIntegrable_mult := fun K _ _ => by
        rw [Nat.cast_one, setLIntegral_one]
        exact (lt_of_le_of_lt (measure_mono inter_subset_left) hIfin).ne
      aestronglyMeasurable_orient := aestronglyMeasurable_const
      orients := ae_restrict_of_forall_mem hImeas fun x hx =>
        ⟨_, Submission.cbr_cc_seg_open_segment_tangent P a τ ℓ hτ x hx, hζ₀⟩ }
  refine ⟨R, ?_, ?_, ?_⟩
  -- Step 5: `I ⊆ [a, a + ℓτ]`, via `φ(u) = a + (u/ℓ)((a + ℓτ) − a)` with `u/ℓ ∈ [0, 1]`
  · rintro _ ⟨u, ⟨hu0, huℓ⟩, rfl⟩
    rw [segment_eq_image']
    refine ⟨u / ℓ, ⟨div_nonneg hu0.le hℓ.le, (div_le_one hℓ).mpr huℓ.le⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ u hℓ.ne']
  -- Step 6: `μ_R(ℝᴾ) = H¹(I) < ∞`
  · show ((μHE[1].restrict ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ)).withDensity
      fun _ => ((1 : ℕ) : ℝ≥0∞)) univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Nat.cast_one,
      setLIntegral_one]
    exact hIfin
  -- Step 7: `R(ω) = ∫_I ω(x)(τ) dH¹(x) = ∫₀^ℓ ω(a + uτ)(τ) du`
  · intro ω
    show ∫ x in (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ, ((1 : ℕ) : ℝ) * ζ₀ (ω x) ∂μHE[1] = _
    rw [Nat.cast_one]
    simp only [one_mul, ζ₀, ContinuousAlternatingMap.apply_apply]
    exact hIint fun x => ω x fun _ => τ

/-- **The segment current `[[a, b]]`** (Simon Ch. 6, 2.2 and 3.1).  Assuming (MR), i.e.
`M_W(T) = μ_R(W)` for `T = τ(R)`, every pair `a, b ∈ ℝᴾ` bounds an integer multiplicity
`S ∈ 𝒟₁(ℝᴾ)` with `∂S = δ_b − δ_a`, `M(S) < ∞` and `spt S ⊆ [a, b]`.  If `a = b`, `S = 0`
(`current_algebra` (a), (b), `support_vanish`).  Otherwise let `ℓ = |b − a|`, `τ = ℓ⁻¹(b − a)`, so
`a + ℓτ = b`, and let `S = τ(R)` for the triple `R = (I, 1, τ)` on the open segment
`I = {a + uτ : 0 < u < ℓ} ⊆ [a, b]` (`segment_imrep`, `imrep_current`).  Then
`∂S(g) = S(dg) = ∫₀^ℓ dg(a + uτ)(τ) du = g(b)⟨⟩ − g(a)⟨⟩` (`zero_form_ftc`), `M(S) = μ_R(ℝᴾ) < ∞`
by (MR), and `S(ω) = 0` once `spt ω` misses the compact `[a, b]`, so `spt S ⊆ [a, b]`. -/
theorem Submission.dmcbr_cc_segment_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P : ℕ) (a b : Euclid P), ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) 1, IsIntegerMultiplicity S ∧ (∀ g : TestFormOn (univ : Set (Euclid P)) 0, S.boundary g = (g : DifferentialForm (Euclid P) 0) b (fun i => i.elim0) - (g : DifferentialForm (Euclid P) 0) a (fun i => i.elim0)) ∧ S.mass < ∞ ∧ S.support ⊆ segment ℝ a b := by
  intro hMR P a b
  by_cases hab : a = b
  · -- Case `a = b`: `S = 0`, integer multiplicity by `current_algebra` (a)
    subst hab
    refine ⟨0, Submission.cbr_cc_current_algebra.1 P 1 univ, fun g => ?_, ?_, ?_⟩
    · -- `∂0(g) = 0 = g(a)⟨⟩ − g(a)⟨⟩`
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply, sub_self]
    · -- `M(0) ≤ |0| M(0) + |0| M(0) = 0` by `current_algebra` (b)
      show (0 : GeometricCurrentOn (univ : Set (Euclid P)) 1).massOn univ < ∞
      refine (Submission.cbr_cc_current_algebra.2.1 P 1 univ 0 0 0 0 0 (fun ω => by simp)
        univ).trans_lt ?_
      simp
    · -- `0` kills every form, so `spt 0 ⊆ {a} = [a, a]`
      rw [segment_same]
      exact (Submission.rsd_cmr_support_subset_of_vanish P 1 univ _ 0 isOpen_univ
        isCompact_singleton (subset_univ _) fun ω _ => rfl).1
  · -- Case `a ≠ b`: `ℓ = |b − a| > 0`, `τ = ℓ⁻¹(b − a)` is a unit vector and `a + ℓτ = b`
    set ℓ : ℝ := ‖b - a‖
    have hℓ : 0 < ℓ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
    set τ : Euclid P := ℓ⁻¹ • (b - a) with hτdef
    have hτ : ‖τ‖ = 1 := by
      rw [hτdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hℓ]
      exact inv_mul_cancel₀ hℓ.ne'
    have hb : a + ℓ • τ = b := by
      rw [hτdef, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul, add_sub_cancel]
    -- the triple `R = (I, 1, τ)` on the open segment `I ⊆ [a, b]`, and its current `S = τ(R)`
    obtain ⟨R, hRc, hRm, hRa⟩ := Submission.cbr_cc_seg_segment_imrep P a τ ℓ hτ hℓ
    obtain ⟨S, hS⟩ := Submission.dtc_imrep_current P 1 univ R
    rw [hb] at hRc
    refine ⟨S, ⟨R, hS⟩, fun g => ?_, ?_, ?_⟩
    · -- `∂S(g) = S(dg) = ∫_{(0,ℓ)} dg(a + uτ)(τ) du = g(a + ℓτ)⟨⟩ − g(a)⟨⟩`
      rw [GeometricCurrentOn.boundary_apply, hS]
      change R.action (exteriorDerivative (g : DifferentialForm (Euclid P) 0)) = _
      rw [hRa, Submission.cbr_cc_seg_zero_form_ftc P _ g.property.1.1 a τ ℓ hℓ.le, hb]
    · -- `M(S) = M_{ℝᴾ}(S) = μ_R(ℝᴾ) < ∞` by (MR) with `U = W = ℝᴾ`
      show S.massOn univ < ∞
      rw [hMR P 1 univ S R isOpen_univ hS univ isOpen_univ]
      exact hRm
    · -- `[a, b]` is compact, and `S(ω) = 0` if `spt ω` misses `[a, b] ⊇ I`
      have hK : IsCompact (segment ℝ a b) := by
        rw [segment_eq_image]
        exact isCompact_Icc.image (by fun_prop)
      refine (Submission.rsd_cmr_support_subset_of_vanish P 1 univ (segment ℝ a b) S isOpen_univ
        hK (subset_univ _) fun ω hω => ?_).1
      rw [hS, IMRep.action]
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [image_eq_zero_of_notMem_tsupport (disjoint_right.mp hω (hRc hx)), map_zero, mul_zero]
/-- **Degree-0 integer multiplicity triples** (Simon Ch. 3, 1.1 and 1.4; Ch. 6, 3.1; `H⁰` is
counting measure, Ch. 2).  For `R = (M, θ, ξ) ∈ IMRep U 0`: (i) `M` is countable, since the null
set of the rectifiable cover has `H⁰`-measure `≥ 1` unless empty and `ℝ⁰` is a point; (ii) for
compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dH⁰ < ∞` and `H⁰(M ∩ K) ≤ μ_R(K)` as `θ ≥ 1` on `M`, so
`M ∩ K` is finite; (iii) each point of `M` has `H⁰⌞M`-mass `1`, so the a.e. orientation property
holds everywhere on `M`, and `ξ(x)` maps the constant covector `1` to `±1`, so `ξ(x) ≠ 0`;
(iv) for `U` open, carrier points have `μ_R`-mass `θ(x) ≥ 1`, and a point of `U \ M` has a
neighbourhood missing the locally finite `M`, so `U ∩ spt μ_R = M`. -/
theorem Submission.dor_zdm_imrep_zero_structure : ∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0), R.carrier.Countable ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → (R.carrier ∩ K).Finite ∧ R.measure K ≠ ∞) ∧ (∀ x ∈ R.carrier, (∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q) ∧ R.orient x ≠ 0) ∧ (IsOpen U → U ∩ R.measure.support = R.carrier) := by
  intro P U R
  -- `H⁰ = μH[0]`: points have mass `1` and nonempty sets mass `≥ 1`
  have hpt : ∀ z : Euclid P, μHE[0] ({z} : Set (Euclid P)) = 1 := fun z => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hne : ∀ S : Set (Euclid P), S.Nonempty → 1 ≤ μHE[0] S := fun S hS => by
    rw [Measure.euclideanHausdorffMeasure_zero]
    exact Measure.one_le_hausdorffMeasure_zero_of_nonempty hS
  -- (i) the null set `M₀` of the rectifiable cover is empty and each `F_j(ℝ⁰)` is a point
  have hcount : R.carrier.Countable := by
    obtain ⟨M₀, hM₀, F, -, hcover⟩ := R.rectifiable
    have hM₀e : M₀ = ∅ := by
      by_contra h
      have h1 := hne M₀ (Set.nonempty_iff_ne_empty.2 h)
      rw [hM₀] at h1
      simp at h1
    rw [hM₀e, Set.empty_union] at hcover
    exact Set.Countable.mono hcover
      (Set.countable_iUnion fun j => (Set.subsingleton_range (F j)).countable)
  -- (ii) `μ_R(K) = ∫_{M ∩ K} θ dH⁰ < ∞`, and `H⁰(M ∩ K) ≤ μ_R(K)` since `θ ≥ 1` on `M`
  have hloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      (R.carrier ∩ K).Finite ∧ R.measure K ≠ ∞ := by
    intro K hK hKU
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[0] := by
      rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    have hfin : μHE[0] (R.carrier ∩ K) ≠ ∞ := by
      refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
      calc μHE[0] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, 1 ∂μHE[0] := (setLIntegral_one _).symm
        _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[0] :=
          setLIntegral_mono' (R.measurableSet_carrier.inter hKm) fun x hx => by
            exact_mod_cast R.mult_pos x hx.1
    refine ⟨?_, by rw [hmeas]; exact R.locallyIntegrable_mult K hK hKU⟩
    -- an infinite `M ∩ K` contains `m`-point sets of `H⁰`-measure `m` for every `m`
    by_contra hinf
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hfin
    obtain ⟨t, hts, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf m
    have ht : μHE[0] (t : Set (Euclid P)) = t.card := by
      rw [← sum_measure_singleton]
      simp only [hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hle := measure_mono (μ := μHE[0]) hts
    rw [ht] at hle
    exact absurd hle (not_le.2 hm)
  -- (iii) every point of `M` has `H⁰⌞M`-mass `1`, so the a.e. property holds at each point
  have horient : ∀ x ∈ R.carrier, (∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q) ∧
      R.orient x ≠ 0 := by
    intro x hx
    have hQ : ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
      by_contra hnot
      have h1 : (μHE[0].restrict R.carrier) {x} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.2 hnot) (ae_iff.1 R.orients)
      rw [Measure.restrict_apply' R.measurableSet_carrier, Set.singleton_inter_of_mem hx, hpt] at h1
      exact one_ne_zero h1
    refine ⟨hQ, fun h0 => ?_⟩
    -- `ξ(x)` maps the constant `0`-covector `1` to `±1`
    obtain ⟨Q, -, τ, -, -, hξ⟩ := hQ
    rcases hξ with h | h
    · have h1 := h (ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ))
      simp [h0, ContinuousAlternatingMap.constOfIsEmpty_apply] at h1
    · have h1 := h (ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ))
      simp [h0, ContinuousAlternatingMap.constOfIsEmpty_apply] at h1
  refine ⟨hcount, hloc, horient, fun hU => Set.Subset.antisymm ?_ fun x hx => ?_⟩
  · -- (iv, ⊆) a point of `U \ M` has a neighbourhood missing the finite set `M ∩ B̄_{ε/2}(x)`
    rintro x ⟨hxU, hxs⟩
    by_contra hxM
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
    have hcb : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hF := (hloc _ (isCompact_closedBall x (ε / 2)) hcb).1
    have hN : (R.carrier ∩ closedBall x (ε / 2))ᶜ ∩ closedBall x (ε / 2) ∈ 𝓝 x :=
      Filter.inter_mem (hF.isClosed.isOpen_compl.mem_nhds fun h => hxM h.1)
        (closedBall_mem_nhds x (half_pos hε))
    have h0 : (μHE[0].restrict R.carrier)
        ((R.carrier ∩ closedBall x (ε / 2))ᶜ ∩ closedBall x (ε / 2)) = 0 := by
      rw [Measure.restrict_apply' R.measurableSet_carrier]
      convert measure_empty (μ := (μHE[0] : Measure (Euclid P)))
      exact Set.eq_empty_iff_forall_notMem.2 fun z ⟨⟨h1, h2⟩, h3⟩ => h1 ⟨h3, h2⟩
    exact ((Measure.mem_support_iff_forall x).1 hxs _ hN).ne'
      (withDensity_absolutelyContinuous _ _ h0)
  · -- (iv, ⊇) a carrier point has `μ_R`-mass `θ(x) ≥ 1`
    refine ⟨R.carrier_subset hx, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    have hx1 : R.measure {x} = R.mult x := by
      rw [IMRep.measure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
        Measure.restrict_apply' R.measurableSet_carrier, Set.singleton_inter_of_mem hx, hpt,
        mul_one]
    calc (0 : ℝ≥0∞) < R.mult x := by exact_mod_cast R.mult_pos x hx
      _ = R.measure {x} := hx1.symm
      _ ≤ R.measure N := measure_mono (Set.singleton_subset_iff.2 (mem_of_mem_nhds hN))
/-- **Degree-0 unit orientations** (Simon 6.1.1, 6.1.7; 6.2.2).  If `ξ ∈ Λ₀(ℝᴾ)` orients `Q`,
i.e. `⟨α, ξ⟩ = ±α(τ)` for every `0`-covector `α`, with `τ : Fin 0 → ℝᴾ` orthonormal spanning `Q`,
then `⟨α, ξ⟩ = s α(())` with `s = ±1`, since `τ` is the empty family `()`. -/
theorem Submission.regcomp_cop_zdr_unitOrientation_zero : ∀ (P : ℕ) (ξ : MultiVector P 0) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ∃ s : ℝ, |s| = 1 ∧ ∀ α : Covector (Euclid P) 0, ξ α = s * α (fun i => i.elim0) := by
  intro P ξ Q hξ
  obtain ⟨τ, -, -, h | h⟩ := hξ
  -- `Fin 0 → ℝᴾ` has exactly one element, so `τ = ()`
  · exact ⟨1, abs_one, fun α => by rw [h α, one_mul, Subsingleton.elim τ fun i => i.elim0]⟩
  · exact ⟨-1, by rw [abs_neg, abs_one],
      fun α => by rw [h α, neg_one_mul, Subsingleton.elim τ fun i => i.elim0]⟩
/-- **Integrals over a finite set against `H⁰`** (`H⁰` is counting measure, Simon Ch. 2).  Since
`μHE[0] = μH[0]`, every point has `H⁰`-mass `1`; so `f` is integrable on each singleton, hence on
the finite union `F = ⋃_{x ∈ F} {x}`, and `∫_F f dH⁰ = Σ_{x ∈ F} H⁰({x}) f(x) = Σ_{x ∈ F} f(x)`. -/
theorem Submission.cbr_cc_zcs_setIntegral_finset_hausdorff_zero : ∀ (P : ℕ) (F : Finset (Euclid P)) (f : Euclid P → ℝ), ∫ x in (F : Set (Euclid P)), f x ∂μHE[0] = ∑ x ∈ F, f x := by
  intro P F f
  -- `H⁰ = μH[0]`: every point has `H⁰`-mass `1`
  have hpt : ∀ x : Euclid P, μHE[0] ({x} : Set (Euclid P)) = 1 := fun x => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  -- `f` is integrable on each singleton, hence on the finite union `F = ⋃_{x ∈ F} {x}`
  have hint : IntegrableOn f (F : Set (Euclid P)) μHE[0] := by
    rw [← Set.biUnion_of_singleton (F : Set (Euclid P)), Finset.set_biUnion_coe,
      integrableOn_finset_iUnion]
    exact fun x _ => integrableOn_singleton enorm_ne_top (by rw [hpt]; exact ENNReal.one_lt_top)
  -- `∫_F f dH⁰ = Σ_{x ∈ F} H⁰.real({x}) • f(x)`, and `H⁰.real({x}) = 1`
  rw [setIntegral_finset F hint]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
/-- **Compactly supported integer multiplicity `0`-currents are finite sums of point masses**
(Simon Ch. 6, 3.1; `H⁰` is counting measure, Ch. 2).  Let `S = τ(M, θ, ξ)` in `ℝᴾ` with `spt S`
compact.  `S` kills every test form supported in its open zero region `G = ℝᴾ \ spt S`, so
`μ_R(G) = M_G(S) = 0` by the mass identity; as `M = spt μ_R`, this gives `M ⊆ spt S`, and
`M = M ∩ spt S` is finite.  At each `x ∈ M`, `ξ(x) = ±⟨·⟩`, so
`S(g) = ∫_M θ ⟨g, ξ⟩ dH⁰ = Σ_{x ∈ M} ±θ(x) g(x)⟨⟩`. -/
theorem Submission.dmcbr_cc_zero_current_finite_sum : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) 0), IsIntegerMultiplicity S → IsCompact S.support → ∃ (F : Finset (Euclid P)) (m : Euclid P → ℤ), (↑F : Set (Euclid P)) ⊆ S.support ∧ ∀ g : TestFormOn (univ : Set (Euclid P)) 0, S g = ∑ x ∈ F, (m x : ℝ) * (g : DifferentialForm (Euclid P) 0) x (fun i => i.elim0) := by
  rintro hMR hVO P S ⟨R, hR⟩ hK
  obtain ⟨-, hloc, horient, hspt⟩ := Submission.dor_zdm_imrep_zero_structure P univ R
  -- `S` vanishes on its open zero region `G = ℝᴾ \ spt S`, so `μ_R(G) = M_G(S) = 0`
  have hG : R.measure S.zeroRegion = 0 := by
    rw [← hMR P 0 univ S R isOpen_univ hR _ S.isOpen_zeroRegion]
    refine nonpos_iff_eq_zero.1 (sSup_le ?_)
    rintro r ⟨ω, hω, rfl⟩
    dsimp only
    rw [hVO P 0 univ S ω (Set.disjoint_of_subset_left hω.1 disjoint_sdiff_self_right),
      ENNReal.ofReal_zero]
  -- carrier points lie in `spt μ_R`, hence outside `G`: `M ⊆ spt S`
  have hsub : R.carrier ⊆ S.support := fun x hx => by
    rw [GeometricCurrentOn.support, Set.mem_sdiff]
    refine ⟨mem_univ x, fun hxG => ?_⟩
    rw [← hspt isOpen_univ] at hx
    exact ((Measure.mem_support_iff_forall x).1 hx.2 _ (S.isOpen_zeroRegion.mem_nhds hxG)).ne' hG
  -- `M = M ∩ spt S` is finite, `spt S` being compact
  have hfin : R.carrier.Finite := by
    have h := (hloc _ hK (subset_univ _)).1
    rwa [Set.inter_eq_left.2 hsub] at h
  obtain ⟨F, hF⟩ := hfin.exists_finset_coe
  -- `ξ(x) = ±⟨·⟩` at every carrier point
  have hsign : ∀ x ∈ R.carrier, ∃ σ : ℤ, ∀ α : Covector (Euclid P) 0,
      R.orient x α = (σ : ℝ) * α (fun i => i.elim0) := fun x hx => by
    obtain ⟨Q, -, hQ⟩ := (horient x hx).1
    obtain ⟨s, hs, hξ⟩ := Submission.regcomp_cop_zdr_unitOrientation_zero P (R.orient x) Q hQ
    rcases (abs_eq zero_le_one).1 hs with rfl | rfl
    · exact ⟨1, fun α => by rw [hξ α, Int.cast_one]⟩
    · exact ⟨-1, fun α => by rw [hξ α, Int.cast_neg, Int.cast_one]⟩
  choose! σ hσ using hsign
  -- `S(g) = ∫_M θ ⟨g, ξ⟩ dH⁰ = Σ_{x ∈ M} θ(x) σ(x) g(x)⟨⟩`
  refine ⟨F, fun x => σ x * R.mult x, hF ▸ hsub, fun g => ?_⟩
  rw [hR g, IMRep.action, ← hF, Submission.cbr_cc_zcs_setIntegral_finset_hausdorff_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hσ x (hF ▸ Finset.mem_coe.2 hx)]
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
/-- **Integrability and zeroth-order bound of the pairing `∫_E ⟨ω, ξ⟩ dμ`** (Simon 6.2.4–6.2.5,
`μ⌞E ∧ ξ` as a current; used for restrictions of currents in the slicing argument of 7.2.4).
If `|⟨α, ξ(x)⟩| ≤ |α|` for every `n`-covector `α` and `μ`-a.e. `x`, and the continuous form
`ω` vanishes off a measurable `K` with `μ(K) < ∞` and `|ω| ≤ ε`, then `|ξ(ω)| ≤ ε 1_K`
`μ`-a.e., so `ξ(ω)` is `μ⌞E`-integrable and `|∫_E ξ(ω) dμ| ≤ ε μ(K ∩ E) ≤ ε μ(K)`. -/
theorem Submission.cmcs_rc_pairing_integrable_abs_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E K : Set (Euclid P)) (ω : DifferentialForm (Euclid P) n) (ε : ℝ), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Continuous ω → MeasurableSet K → μ K < ∞ → (∀ x, x ∉ K → ω x = 0) → (∀ x, covectorEuclideanNorm (ω x) ≤ ε) → Integrable (fun x => ξ x (ω x)) (μ.restrict E) ∧ |∫ x in E, ξ x (ω x) ∂μ| ≤ ε * (μ K).toReal := by
  intro P n μ ξ E K ω ε hξm hξb hω hK hμK hzero hε
  -- Step 1: `ε ≥ 0`
  have hε0 : 0 ≤ ε := (covectorEuclideanNorm_nonneg _).trans (hε 0)
  -- Step 2: `F x = ξ x (ω x)` is a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => ξ x (ω x)) μ :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n)
      (F := ℝ)).continuous.comp_aestronglyMeasurable₂ (g := fun Λ α => Λ α) hξm
      hω.aestronglyMeasurable
  -- Step 3: `‖F x‖ ≤ K.indicator ε x` a.e.
  have hbd : ∀ᵐ x ∂μ, ‖ξ x (ω x)‖ ≤ K.indicator (fun _ => ε) x := by
    filter_upwards [hξb] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs]
      exact (hx (ω x)).trans (hε x)
    · rw [indicator_of_notMem hxK, hzero x hxK, map_zero, norm_zero]
  -- Step 4: the dominating function is integrable
  have hg : Integrable (K.indicator (fun _ => ε)) μ :=
    (integrableOn_const hμK.ne).integrable_indicator hK
  -- Step 5: integrability of `F`, then on `μ.restrict E`
  have hint : Integrable (fun x => ξ x (ω x)) μ := hg.mono' hmeas hbd
  refine ⟨hint.restrict, ?_⟩
  -- Step 6: `‖∫_E F‖ ≤ ∫_E g = ν.real K * ε`
  have h1 : ‖∫ x in E, ξ x (ω x) ∂μ‖ ≤ ∫ x in E, K.indicator (fun _ => ε) x ∂μ :=
    norm_integral_le_of_norm_le hg.restrict (ae_restrict_of_ae hbd)
  rw [integral_indicator_const ε hK, smul_eq_mul] at h1
  -- Step 7: `ν K = μ (K ∩ E) ≤ μ K`, multiply by `ε ≥ 0`
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hε0
  rw [measureReal_def, Measure.restrict_apply hK]
  exact ENNReal.toReal_mono hμK.ne (measure_mono inter_subset_left)
/-- **A linear functional on `𝒟ⁿ(U)` with zeroth-order bounds is a current** (Simon 6.2.1; used
for the restricted currents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` in the slicing argument behind 7.2.4).  Suppose
every compact `K ⊆ U` has a `c` with `|L(ω)| ≤ c M` whenever `spt ω ⊆ K` and `‖ω(x)‖ ≤ M` for all
`x`.  Take `S = L`.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K ⊆ U`, the order-`0`
part of the uniform convergence on `K` gives `‖ωⱼ(x)‖ ≤ η` for large `j`.  Off `K` this holds
because `ωⱼ(x) = 0`.  With `η = δ / (|c| + 1)`, `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`. -/
theorem Submission.cmcs_rc_order_zero_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ (ω : TestFormOn U n) (M : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) → |L ω| ≤ c * M) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = L ω := by
  intro P n U L hL
  -- Step 1: `S = ⟨L, h⟩`, so `S ω = L ω` and only `L(ωⱼ) → 0` for `ωⱼ → 0` remains
  refine ⟨⟨L, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 2: the common compact support `K ⊆ U` and the constant `c` for `K`
  obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
  obtain ⟨c, hc⟩ := hL K hK hKU
  -- Step 3: order-`0` uniform convergence on `K`, to the zero form
  have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
  have hz : ∀ x, iteratedFDeriv ℝ 0
      ((0 : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 := by
    intro x
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hη : 0 < δ / (|c| + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 _ hη)
  refine ⟨N, fun j hj => ?_⟩
  -- Steps 3–4: `‖ωⱼ(x)‖ ≤ η` on `K` by uniform convergence, and off `K` since `ωⱼ(x) = 0`
  have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ / (|c| + 1) := by
    intro x
    by_cases hx : x ∈ K
    · have h := hN j hj x hx
      rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
      exact h.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
      exact hη.le
  -- Step 5: `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ c * (δ / (|c| + 1)) := hc (ωs j) _ (hsupp j) hsmall
    _ ≤ |c| * (δ / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hη.le
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- **Restriction of a measure-represented current** (Simon Ch. 6, 2.9:
`T ⌞ A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`), for an arbitrary pair `(μ, ξ)` and an arbitrary set `E`: if `μ` is
finite on compact subsets of `U` and `ξ` is `μ`-a.e. strongly measurable with
`|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for `μ`-a.e. `x`, then
`ω ↦ ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` is a current in `U`.  By `rsd_mw_tfa_norm_props`, `|α| ≤ C ‖α‖`.
For `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, `cmcs_rc_pairing_integrable_abs_le` then
gives integrability on `μ ⌞ E` and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`.  The functional is linear
(`integral_add`, `integral_const_mul`), and `cmcs_rc_order_zero_current` turns the order-zero
bound into Simon's sequential continuity. -/
theorem Submission.cmcs_restrict_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
  intro P n U μ ξ E hμK hξm hξb
  -- Step 1: `|α| ≤ C ‖α‖` for every `n`-covector `α`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Steps 2 and 4: for `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, the pairing is
  -- `μ ⌞ E`-integrable and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`
  have hpair : ∀ (ω : TestFormOn U n) (K : Set (Euclid P)) (M : ℝ), IsCompact K → K ⊆ U →
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K →
      (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) →
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) ∧
        |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| ≤ C * M * (μ K).toReal := by
    intro ω K M hK hKU hsupp hM
    exact Submission.cmcs_rc_pairing_integrable_abs_le P n μ ξ E K
      (ω : DifferentialForm (Euclid P) n) (C * M) hξm hξb ω.property.1.1.continuous
      hK.measurableSet (hμK K hK hKU)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h))
      (fun x => (hC _).trans (mul_le_mul_of_nonneg_left (hM x) hC0))
  -- Step 2: every test form is admissible, with `K = tsupport ω` and `M = sup ‖ω‖ < ∞`
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) := by
    intro ω
    obtain ⟨M, hM⟩ := ω.property.1.1.continuous.bounded_above_of_compact_support ω.property.1.2
    exact (hpair ω _ M ω.property.1.2 ω.property.2 subset_rfl hM).1
  -- Step 3: `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` is linear
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω₁) (hint ω₂)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  -- Steps 4 and 5: the order-zero bound with `c_K = C μ(K)` makes `L` a current
  obtain ⟨S, hS⟩ := Submission.cmcs_rc_order_zero_current P n U L fun K hK hKU =>
    ⟨C * (μ K).toReal, fun ω M hsupp hM => by
      calc |L ω| = |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| := rfl
        _ ≤ C * M * (μ K).toReal := (hpair ω K M hK hKU hsupp hM).2
        _ = C * (μ K).toReal * M := by ring⟩
  exact ⟨S, hS⟩
/-- **Level splitting of a test form** (a step in the proof of Simon Ch. 6, 4.8,
`spt ⟨T, f, t₊⟩ ⊆ spt T ∩ {f = t}`).  If `tsupport η` misses the level set `{f = t}` of a
continuous `f`, then `η = η₁ + η₂` with test forms `η₁ = χ η` supported in `{f < t}` and
`η₂ = (1 - χ) η` supported in `{t < f}`.  Here `χ` is a smooth Urysohn function equal to `1` on
`K₋ = tsupport η ∩ {f ≤ t}` and to `0` on `K₊ = tsupport η ∩ {t ≤ f}`; these closed sets are
disjoint, with `K₋ ⊆ {f < t}` and `K₊ ⊆ {t < f}`, because `tsupport η` misses `{f = t}`. -/
theorem Submission.cmcs_ss_testForm_level_split : ∀ (P n : ℕ) (U : Set (Euclid P)) (f : Euclid P → ℝ) (t : ℝ) (η : TestFormOn U n), Continuous f → Disjoint (tsupport (η : DifferentialForm (Euclid P) n)) {x | f x = t} → ∃ η₁ η₂ : TestFormOn U n, η = η₁ + η₂ ∧ tsupport (η₁ : DifferentialForm (Euclid P) n) ⊆ {x | f x < t} ∧ tsupport (η₂ : DifferentialForm (Euclid P) n) ⊆ {x | t < f x} := by
  intro P n U f t η hf hη
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := η.property
  set e : DifferentialForm (Euclid P) n := (η : DifferentialForm (Euclid P) n)
  -- the closed halves `K₋ = K ∩ {f ≤ t}` and `K₊ = K ∩ {t ≤ f}` of `K = tsupport η` are
  -- disjoint, since `K` misses `{f = t}`
  have hKl : IsClosed (tsupport e ∩ {x | f x ≤ t}) :=
    (isClosed_tsupport e).inter (isClosed_le hf continuous_const)
  have hKu : IsClosed (tsupport e ∩ {x | t ≤ f x}) :=
    (isClosed_tsupport e).inter (isClosed_le continuous_const hf)
  have hd : Disjoint (tsupport e ∩ {x | t ≤ f x}) (tsupport e ∩ {x | f x ≤ t}) :=
    Set.disjoint_left.2 fun x hxu hxl => Set.disjoint_left.1 hη hxu.1 (le_antisymm hxl.2 hxu.2)
  -- a smooth `χ` with `χ = 0` on `K₊` and `χ = 1` on `K₋`
  obtain ⟨χ, hχ, -, hχ₀, hχ₁⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hKu hKl hd
  -- `χ η` and `(1 - χ) η` are test forms in `U`, with sum `η`
  have h₁ : (fun x => χ x • e x) ∈ TestFormOn U n :=
    ⟨⟨hχ.smul hsmooth, hcpt.smul_left (f := χ)⟩, (tsupport_smul_subset_right χ e).trans hU⟩
  have h₂ : (fun x => (1 - χ x) • e x) ∈ TestFormOn U n :=
    ⟨⟨(contDiff_const.sub hχ).smul hsmooth, hcpt.smul_left (f := fun x => 1 - χ x)⟩,
      (tsupport_smul_subset_right (fun x => 1 - χ x) e).trans hU⟩
  refine ⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext (funext fun x => ?_), ?_, ?_⟩
  · change e x = χ x • e x + (1 - χ x) • e x
    rw [← add_smul, add_sub_cancel, one_smul]
  · -- `support (χ η) ⊆ K₋`, a closed subset of `{f < t}`
    have hs : support (fun x => χ x • e x) ⊆ tsupport e ∩ {x | f x ≤ t} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show f x ≤ t from le_of_not_ge fun h => ?_⟩
      exact left_ne_zero_of_smul hx ((hχ₀ x).1 ⟨he, h⟩)
    exact (closure_minimal hs hKl).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h
  · -- `support ((1 - χ) η) ⊆ K₊`, a closed subset of `{t < f}`
    have hs : support (fun x => (1 - χ x) • e x) ⊆ tsupport e ∩ {x | t ≤ f x} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show t ≤ f x from le_of_not_ge fun h => left_ne_zero_of_smul hx ?_⟩
      rw [(hχ₁ x).1 ⟨he, h⟩, sub_self]
    exact (closure_minimal hs hKu).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h.symm
/-- Restriction commutes with the boundary on forms supported in the restricting set (Simon 6.4.6,
used for 4.8): let `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`, and let `A = T⌞S`,
`B = (∂T)⌞S` be given by the same integrals over `S`.  Then `∂A(θ) = B(θ)` whenever
`spt θ ⊆ S`.  Off `S` both `θ` and `dθ` vanish (`spt dθ ⊆ spt θ`), so both integrals over `S`
are integrals over `ℝᴾ`, and `∂A(θ) = A(dθ) = T(dθ) = ∂T(θ) = B(θ)`. -/
theorem Submission.cmcs_ss_boundary_eq_of_tsupport_subset : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, tsupport (θ : DifferentialForm (Euclid P) k) ⊆ S → A.boundary θ = B θ := by
  intro P k U T μ μ' ξ ξ' S A B hT hbT hA hB θ hθ
  -- `θ` and `dθ` vanish off `S`, as `spt dθ ⊆ spt θ ⊆ S`
  have hθ0 : ∀ x, x ∉ S → (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hθ h)
  have hdθ0 : ∀ x, x ∉ S → exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      hx (hθ (tsupport_exteriorDerivative_subset _ h))
  -- so, `ξ x` and `ξ' x` being linear, both integrals over `S` are integrals over `ℝᴾ`
  have hAT : ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ =
      ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hdθ0 x hx, map_zero]
  have hBT : ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' =
      ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hθ0 x hx, map_zero]
  -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ = ∫ ⟨dθ, ξ⟩ dμ = T(dθ) = ∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`
  -- `= ∫_S ⟨θ, ξ'⟩ dμ' = B(θ)`
  calc A.boundary θ = A (exteriorDerivativeTestOn U k θ) := GeometricCurrentOn.boundary_apply A θ
    _ = ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hA _
    _ = ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hAT
    _ = T (exteriorDerivativeTestOn U k θ) := (hT (exteriorDerivativeTestOn U k θ)).symm
    _ = T.boundary θ := (GeometricCurrentOn.boundary_apply T θ).symm
    _ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hbT θ
    _ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hBT.symm
    _ = B θ := (hB θ).symm
/-- Simon Ch. 6, 4.6–4.8 (support of the slice `∂(T⌞S) − (∂T)⌞S`, `S = {f < t}`): if
`A(ω) = ∫_S ⟨ω, ξ⟩ dμ` and `B(θ) = ∫_S ⟨θ, ξ'⟩ dμ'`, then `∂A(θ) = A(dθ) = 0` and `B(θ) = 0`
whenever `spt θ` misses `S`, because `θ` and `dθ` (`spt dθ ⊆ spt θ`) vanish on `S`. -/
theorem Submission.cmcs_ss_boundary_vanish_of_disjoint : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, Disjoint (tsupport (θ : DifferentialForm (Euclid P) k)) S → A.boundary θ = 0 ∧ B θ = 0 := by
  intro P k U μ μ' ξ ξ' S A B hA hB θ hθ
  -- `θ` vanishes on `S`, and so does `dθ`, as `tsupport dθ ⊆ tsupport θ`
  have hθS : ∀ x ∈ S, (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hθ.notMem_of_mem_right hx)
  have hdθS : ∀ x ∈ S, exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun hx' =>
      hθ.notMem_of_mem_right hx (tsupport_exteriorDerivative_subset _ hx')
  refine ⟨?_, ?_⟩
  · -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ`
    rw [GeometricCurrentOn.boundary_apply, hA]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    change ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) = 0
    rw [hdθS x hx, map_zero]
  · rw [hB]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [hθS x hx, map_zero]

/-- **Simon Ch. 6, 4.8** (support of a slice): if `T = ξ μ` and `∂T = ξ' μ'` in `U`,
`A = T ⌞ {f < t}` and `B = (∂T) ⌞ {f < t}` (`f` continuous), then `∂A(η) = B(η)` for every
`η ∈ 𝒟ᵏ(U)` whose support misses the level set `{f = t}`; i.e. the slice `∂A − B` lives on
`{f = t}`.  Split `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {f > t}`
(`cmcs_ss_testForm_level_split`).  Below the level `∂A(η₁) = ∂T(η₁) = B(η₁)`
(`cmcs_ss_boundary_eq_of_tsupport_subset`); above it `∂A(η₂) = 0 = B(η₂)`
(`cmcs_ss_boundary_vanish_of_disjoint`), as `{f > t}` misses `{f < t}`.  Conclude by linearity
of `∂A` and `B`. -/
theorem Submission.cmcs_slice_support : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), Continuous f → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ η : TestFormOn U k, Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → A.boundary η = B η := by
  intro P k U T μ μ' ξ ξ' f t A B hf hT hbT hA hB η hη
  -- `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {t < f}`
  obtain ⟨η₁, η₂, rfl, h₁, h₂⟩ := Submission.cmcs_ss_testForm_level_split P k U f t η hf hη
  -- below the level: `∂A(η₁) = ∂T(η₁) = B(η₁)`
  have e₁ : A.boundary η₁ = B η₁ :=
    Submission.cmcs_ss_boundary_eq_of_tsupport_subset P k U T μ μ' ξ ξ' {x | f x < t} A B
      hT hbT hA hB η₁ h₁
  -- above the level: `∂A(η₂) = 0 = B(η₂)`, since `spt η₂ ⊆ {t < f}` misses `{f < t}`
  obtain ⟨e₂, e₂'⟩ := Submission.cmcs_ss_boundary_vanish_of_disjoint P k U μ μ' ξ ξ'
    {x | f x < t} A B hA hB η₂ (Set.disjoint_left.2 fun x hx hx' =>
      lt_asymm (show t < f x from h₂ hx) (show f x < t from hx'))
  -- `∂A` and `B` are linear
  rw [A.boundary.toCurrent.map_add, B.toCurrent.map_add, e₁, e₂, e₂']
/-- Integrability of the pairing `x ↦ ⟨ω(x), ξ(x)⟩`: if `μ` is finite on compact subsets of `U`,
`ξ` is `μ`-a.e. strongly measurable with `|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for
`μ`-a.e. `x`, and `ω ∈ 𝒟ⁿ(U)`, then `x ↦ ⟨ω(x), ξ(x)⟩` is `μ`-integrable.  The coefficient norm
`|ω(x)|` is continuous with compact support, hence bounded by some `M`, so the pairing is
dominated by `M` times the indicator of `spt ω`, which is integrable as `μ(spt ω) < ∞`. -/
theorem Submission.cmcs_smp_pairing_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (ω : TestFormOn U n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ := by
  intro P n U μ ξ ω hμ hξm hξ
  obtain ⟨w, ⟨hws, hwcs⟩, hwU⟩ := ω
  change Integrable (fun x => ξ x (w x)) μ
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous with compact support, hence bounded by some `M`
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  -- `(Λ, α) ↦ Λ α` is continuous, so the pairing is a.e. strongly measurable
  have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hmeas : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    hev.comp_aestronglyMeasurable₂ hξm hwc.aestronglyMeasurable
  -- domination by `M` times the indicator of `spt w`, integrable as `μ(spt w) < ∞`
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport w).measurableSet).2
    (integrableOn_const (hμ _ hwcs hwU).ne)) hmeas ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs]
  by_cases hxK : x ∈ tsupport w
  · rw [indicator_of_mem hxK]
    exact (hx (w x)).trans ((Real.le_norm_self _).trans (hM x))
  · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    simp
/-- **Dominated convergence for level cut-offs** (step 5 of the slice mass bound in the proof of
Simon 7.2.4, cut-offs `g_h` of the level set `{f < t}`).  If `F` is `μ`-integrable, `f` is
measurable and, for `0 < h < 1`, `g_h` is a.e. strongly measurable with `|g_h| ≤ C`, `g_h = 1` on
`{f ≤ t − h}` and `g_h = 0` on `{t ≤ f}`, then `∫ g_h F dμ → ∫_{f < t} F dμ` as `h → 0+`.
Along `𝓝[>] 0` eventually `0 < h < 1`, so `|g_h F| ≤ C|F|` (integrable); for each `x`,
`g_h(x)F(x)` is eventually `1_{f<t}(x)F(x)` (for `h < min (t − f x) 1` if `f x < t`, for all
`h ∈ (0, 1)` if `t ≤ f x`); dominated convergence along the countably generated `𝓝[>] 0`. -/
theorem Submission.cmcs_smp_cutoff_integral_tendsto : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F f : Euclid P → ℝ) (t C : ℝ) (g : ℝ → Euclid P → ℝ), Integrable F μ → Measurable f → (∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) μ) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, |g h x| ≤ C) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, f x ≤ t - h → g h x = 1) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, t ≤ f x → g h x = 0) → Tendsto (fun h : ℝ => ∫ x, g h x * F x ∂μ) (𝓝[>] 0) (𝓝 (∫ x in {x | f x < t}, F x ∂μ)) := by
  intro P μ F f t C g hF hf hgm hgC hg1 hg0
  -- Step 2: eventually along `𝓝[>] 0`, `h ∈ (0, 1)`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- Step 1: `{f < t}` is measurable, so the limit is `∫ 1_{f<t} F dμ`
  have hs : MeasurableSet {x | f x < t} := measurableSet_lt hf measurable_const
  rw [← integral_indicator hs]
  -- Step 6: dominated convergence with the integrable bound `C‖F‖`
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖F x‖) ?_ ?_ ?_ ?_
  · -- Step 3: `g_h F` is a.e. strongly measurable for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    exact (hgm h hh.1 hh.2).mul hF.aestronglyMeasurable
  · -- Step 4: `|g_h F| ≤ C|F|` for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hgC h hh.1 hh.2 x) (norm_nonneg _)
  · exact hF.norm.const_mul C
  · -- Step 5: `g_h(x)F(x)` is eventually equal to `1_{f<t}(x)F(x)`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : f x < t
    · rw [indicator_of_mem (show x ∈ {x | f x < t} from hx)]
      have hpos : 0 < min (t - f x) 1 := lt_min (by linarith) one_pos
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with h hh
      obtain ⟨h0, h1⟩ := hh
      have h1' : h < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      have h2 : h < t - f x := lt_of_lt_of_le h1 (min_le_left _ _)
      rw [hg1 h h0 h1' x (by linarith), one_mul]
    · rw [indicator_of_notMem (show x ∉ {x | f x < t} from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with h hh
      rw [hg0 h hh.1 hh.2 x (not_lt.1 hx), zero_mul]
/-- **Simon Ch. 6, 4.9** (end of its proof, p. 158, where `b ↓ a` and then `ε ↓ 0`): if
`Φ(h) → z` as `h ↓ 0` and `|Φ(h)| ≤ L / (h (1 − h/2)) · v(h)` for `0 < h < 1`, then
`z ≤ L · liminf_{h ↓ 0} h⁻¹ v(h)` in `[0, ∞]`.  For `r > 1` eventually `(1 − h/2)⁻¹ < r`, so
`|z| = liminf |Φ(h)| ≤ r · L · liminf h⁻¹ v(h)`; then let `r ↓ 1`. -/
theorem Submission.cmcs_smp_liminf_bound : ∀ (L : NNReal) (z : ℝ) (Φ : ℝ → ℝ) (v : ℝ → ℝ≥0∞), Tendsto Φ (𝓝[>] 0) (𝓝 z) → (∀ h : ℝ, 0 < h → h < 1 → ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h) → ENNReal.ofReal z ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0) := by
  intro L z Φ v hΦ hb
  set X := (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0)
  -- step 1: `(0, 1) ∈ 𝓝[>] 0`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- step 2: `ofReal |Φ h| → ofReal |z|`
  have hlimΦ : Tendsto (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |z|)) :=
    ENNReal.tendsto_ofReal hΦ.abs
  -- step 3: `ofReal z ≤ ofReal r * X` for every `r > 1`
  have key : ∀ r : ℝ, 1 < r → ENNReal.ofReal z ≤ ENNReal.ofReal r * X := by
    intro r hr
    -- 3a: `(1 - h / 2)⁻¹ → 1`, so eventually `(1 - h / 2)⁻¹ < r`
    have hcont : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝 0) (𝓝 (1 - 0 / 2)⁻¹) :=
        (tendsto_const_nhds.sub (tendsto_id.div_const 2)).inv₀ (by norm_num)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hevr : ∀ᶠ h in 𝓝[>] (0 : ℝ), (1 - h / 2)⁻¹ < r := hcont.eventually (gt_mem_nhds hr)
    calc ENNReal.ofReal z ≤ ENNReal.ofReal |z| := ENNReal.ofReal_le_ofReal (le_abs_self z)
      _ = liminf (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) := hlimΦ.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)))
            (𝓝[>] 0) := by
          -- 3b, 3c: the eventual pointwise bound and monotonicity of `liminf`
          refine liminf_le_liminf ?_
          filter_upwards [hev, hevr] with h ⟨h0, h1⟩ hhr
          have h2 : 0 < 1 - h / 2 := by linarith
          have heq : (L : ℝ) / (h * (1 - h / 2)) = (1 - h / 2)⁻¹ * ((L : ℝ) * h⁻¹) := by
            field_simp
          calc ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h :=
                hb h h0 h1
            _ = ENNReal.ofReal (1 - h / 2)⁻¹ * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                rw [heq, ENNReal.ofReal_mul (inv_nonneg.2 h2.le),
                  ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]
                ring
            _ ≤ ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                gcongr
      _ = ENNReal.ofReal r * X := by
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  -- step 4: let `r ↓ 1`
  by_cases hXtop : X = ⊤
  · rw [hXtop]
    exact le_top
  · have htend : Tendsto (fun r : ℝ => ENNReal.ofReal r * X) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal 1 * X)) :=
      ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_ofReal tendsto_id).mono_left nhdsWithin_le_nhds) (Or.inr hXtop)
    simpa using ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun r hr => key r hr)
/-- Strip estimate (Simon Ch. 6, 4.11: the bound for the right side `R` of 4.11): if `‖Dg‖ ≤ c`,
`Dg` vanishes off `S`, `spt η ⊆ W` and `|η| ≤ 1`, then `∫⁻ ‖Dg‖ |η| dμ ≤ c μ(W ∩ S)`.  The
integrand is dominated by `c 𝟙_{W ∩ S}`: on `W \ S` it vanishes because `Dg = 0`, off `W` because
`η = 0`.  No measurability is needed, as `∫⁻ c 𝟙_A dμ ≤ c μ(A)` for every set `A`. -/
theorem Submission.cmcs_smp_strip_lintegral_le : ∀ (P k : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (W S : Set (Euclid P)) (c : ℝ), (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → tsupport η ⊆ W → (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ∂μ ≤ ENNReal.ofReal c * μ (W ∩ S) := by
  intro P k μ g η W S c hc hS hW hη
  -- the integrand is dominated by the indicator of `W ∩ S` with value `ofReal c`
  refine le_trans (lintegral_mono fun x => ?_)
    (lintegral_indicator_const_le (W ∩ S) (ENNReal.ofReal c))
  show ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ≤
    (W ∩ S).indicator (fun _ => ENNReal.ofReal c) x
  by_cases hx : x ∈ W ∩ S
  · rw [indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal
      ((mul_le_of_le_one_right (norm_nonneg _) (hη x)).trans (hc x))
  · rw [indicator_of_notMem hx]
    -- off `W ∩ S` a factor vanishes: `Dg(x) = 0` on `W \ S` and `η(x) = 0` off `W`
    have h0 : ‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x) = 0 := by
      by_cases hxW : x ∈ W
      · obtain hD | hD := eq_or_ne (fderiv ℝ g x) 0
        · rw [hD, norm_zero, zero_mul]
        · exact absurd ⟨hxW, hS x hD⟩ hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxW (hW h)
        rw [hηx, covectorEuclideanNorm_zero, mul_zero]
    rw [h0, ENNReal.ofReal_zero]
/-- **Simon 6.4.11** (Leibniz rule behind the cutoff identity
`T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω)`): if `g` and the `k`-form `η` are differentiable
at `x`, then `d(gη)(x) = g(x) dη(x) + dg(x) ∧ η(x)`, where `dg(x) ∧ η(x)` is the alternation of
`v ↦ Dg(x)(v) η(x)`.  Unfold `d = extDeriv = alternatizeUncurryFin ∘ fderiv`, apply the product
rule `fderiv_fun_smul`, and use additivity and `ℝ`-homogeneity of `alternatizeUncurryFin`. -/
theorem Submission.cmcs_cd_extDeriv_smul_leibniz : ∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)) := by
  intro P k g η x hg hη
  -- `d θ x = alternatizeUncurryFin (fderiv ℝ θ x)` by definition
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => g y • η y) x) =
    g x • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) +
      ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))
  -- product rule, then linearity of the alternation
  rw [fderiv_fun_smul hg hη, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- **Simon Ch. 6, 4.11** (the multiplier step behind `T(γ∘f dω)` and `T(d(γ∘f ω))`): test forms
in `U` are closed under multiplication by `C^∞` functions.  For `ω ∈ 𝒟ⁿ(U)` and `g ∈ C^∞`, the
form `gω` is `C^∞`; it vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω ⊆ U`, and `spt(gω)` is
compact as a closed subset of the compact set `spt ω`.  Neither openness of `U` nor compact
support of `g` is needed. -/
theorem Submission.cmcs_cd_smul_mem_testFormOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (ω : TestFormOn U n), ContDiff ℝ (⊤ : ℕ∞) g → (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n := by
  intro P n U g ω hg
  -- `ω ∈ 𝒟ⁿ(U)`: `ω` is `C^∞`, `spt ω` is compact and `spt ω ⊆ U`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := hω.1.1
  have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
  -- `gω` vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω`
  have hsub : tsupport (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ⊆
      tsupport (ω : DifferentialForm (Euclid P) n) :=
    tsupport_smul_subset_right (fun x => g x) _
  -- `spt(gω)` is a closed subset of the compact set `spt ω`
  have hcpt : IsCompact (tsupport fun x => g x • (ω : DifferentialForm (Euclid P) n) x) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
  exact ⟨⟨hg.smul hsmooth, hcpt⟩, hsub.trans hω.2⟩

/-- **Simon 6.4.11, the cut-off defect identity**, with a smooth `g` in place of `γ ∘ f` and with
`T`, `∂T` written through integral representations `T = ξ μ`, `∂T = ξ' μ'`: for `g ∈ C^∞` and
`η ∈ 𝒟^k(U)`, `T(g dη) − ∂T(gη) = −T(dg ∧ η)`, where
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`.  The forms `gη` and `g dη` are test forms by
`cmcs_cd_smul_mem_testFormOn`, and `d(gη) − g dη = dg ∧ η` pointwise by the Leibniz rule
`cmcs_cd_extDeriv_smul_leibniz`.  Every equality of integrals is a representation hypothesis or
`integral_congr_ae` for a pointwise identity, so no integrability is needed. -/
theorem Submission.cmcs_cd_defect_identity : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hT hbT hg
  -- Step 1: the test forms `dη`, `gη`, `g dη` and `d(gη)`
  let dη : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k η
  let ηg : TestFormOn U k :=
    ⟨fun x => g x • (η : DifferentialForm (Euclid P) k) x,
      Submission.cmcs_cd_smul_mem_testFormOn P k U g η hg⟩
  let ωg : TestFormOn U (k + 1) :=
    ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k + 1)) x,
      Submission.cmcs_cd_smul_mem_testFormOn P (k + 1) U g dη hg⟩
  let dηg : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k ηg
  -- Step 2: the first integral is `T(g dη)`
  have h1 : ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ =
      T ωg := by
    rw [hT ωg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) =
      ξ x (g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 3: the second integral is `∂T(gη) = T(d(gη))`
  have h2 : ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = T dηg := by
    rw [show T dηg = T.boundary ηg from (GeometricCurrentOn.boundary_apply T ηg).symm, hbT ηg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) =
      ξ' x (g x • (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 4: pointwise, `d(gη) − g dη = dg ∧ η` by the Leibniz rule
  have h3 : ∀ x, ((dηg - ωg : TestFormOn U (k + 1)) : DifferentialForm (Euclid P) (k + 1)) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x)) := by
    intro x
    have hgx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    have hηx : DifferentiableAt ℝ (η : DifferentialForm (Euclid P) k) x :=
      η.property.1.1.differentiable (by simp) x
    change exteriorDerivative (fun y => g y • (η : DifferentialForm (Euclid P) k) y) x -
      g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x = _
    rw [Submission.cmcs_cd_extDeriv_smul_leibniz P k g _ x hgx hηx]
    abel
  -- Step 5: linearity of `T`
  have h4 : T ωg - T dηg = -T (dηg - ωg) := by
    have hsub := LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) dηg ωg
    change T.toCurrent ωg - T.toCurrent dηg = -T.toCurrent (dηg - ωg)
    rw [hsub]
    ring
  -- Steps 6 and 7: `T(d(gη) − g dη)` as an integral
  rw [h1, h2, h4, hT]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (ξ x) (h3 x))
/-- **Orthonormal basis adapted to a linear functional** (used for the wedge-norm bound
`|β ∧ γ| ≤ ‖β‖ |γ|`, Simon 6.1): for a continuous linear functional `β` on `ℝᴾ` and `i₀ : Fin P`
there is an orthonormal basis `f` of `ℝᴾ` with `β(f_{i₀}) = ‖β‖` and `β(f_i) = 0` for `i ≠ i₀`.
Write `β = ⟨b, ·⟩` (Riesz, `‖b‖ = ‖β‖`).  If `b = 0`, the standard basis `e` works.  Otherwise the
reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ`, `u = ‖b‖⁻¹ b`, maps `e_{i₀}` to `u`, and `f = R ∘ e` has
`β(f_i) = ‖b‖ ⟨R e_{i₀}, R e_i⟩ = ‖b‖ ⟨e_{i₀}, e_i⟩`. -/
theorem Submission.cmcs_wn_adapted_orthonormalBasis : ∀ (P : ℕ) (β : Euclid P →L[ℝ] ℝ) (i₀ : Fin P), ∃ f : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, β (f i) = if i = i₀ then ‖β‖ else 0 := by
  intro P β i₀
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Riesz representative: `β x = ⟪b, x⟫` and `‖b‖ = ‖β‖`
  set b : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm β with hb
  have hβb : ∀ x, β x = inner ℝ b x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hnorm : ‖b‖ = ‖β‖ := by
    rw [hb, LinearIsometryEquiv.norm_map]
  by_cases hb0 : b = 0
  · -- `β = 0`: the standard basis works
    refine ⟨e, fun i => ?_⟩
    have h0 : ‖β‖ = 0 := by rw [← hnorm, hb0, norm_zero]
    rw [hβb, hb0, inner_zero_left, h0, ite_self]
  · -- `u = ‖b‖⁻¹ b` is a unit vector and `b = ‖b‖ u`
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    set u : Euclid P := ‖b‖⁻¹ • b with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbpos.ne']
    have hbu : b = ‖b‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
    -- the reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ` maps `e_{i₀}` to `u`
    have he : ‖e i₀‖ = 1 := e.orthonormal.1 i₀
    set R := (ℝ ∙ (e i₀ - u))ᗮ.reflection
    have hR : R (e i₀) = u := Submodule.reflection_sub (he.trans hu.symm)
    -- `f = R ∘ e`: `β(f_i) = ‖b‖ ⟪R e_{i₀}, R e_i⟫ = ‖β‖ ⟪e_{i₀}, e_i⟫`
    refine ⟨e.map R, fun i => ?_⟩
    rw [OrthonormalBasis.map_apply, hβb, hbu, real_inner_smul_left, ← hR,
      LinearIsometryEquiv.inner_map_map, hnorm, orthonormal_iff_ite.mp e.orthonormal i₀ i]
    by_cases hi : i = i₀
    · rw [ite_eq_left hi.symm, ite_eq_left hi, mul_one]
    · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi, mul_zero]
/-- **`β ∧ γ` on tuples of a family adapted to `β`** (Simon 6.1.1–1.3; step 4 of the proof of
`|β ∧ γ| ≤ ‖β‖ |γ|`): if `β(v_a) = c` for `a = i₀` and `β(v_a) = 0` otherwise, then for every
`j : Fin (k + 1) → Fin P`, `(β ∧ γ)(v_{j(0)}, …, v_{j(k)})² ≤ c² Σ_{i, j(i) = i₀} γ(v ∘ ĵᵢ)²`,
where `ĵᵢ = i.removeNth j` deletes the `i`-th entry of `j`.  By definition
`(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`.  A repeated index in `j` makes `v ∘ j`
non-injective, so the left side vanishes (alternation); otherwise at most one `i₁` has
`j(i₁) = i₀`, only `i₁` contributes to either side, and `((−1)^{i₁})² = 1`. -/
theorem Submission.cmcs_wn_tuple_sq_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k) (v : Fin P → Euclid P) (i₀ : Fin P) (c : ℝ), Function.Injective v → (∀ i : Fin P, β (v i) = if i = i₀ then c else 0) → ∀ j : Fin (k + 1) → Fin P, (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ) (fun m => v (j m))) ^ 2 ≤ c ^ 2 * ∑ i : Fin (k + 1), if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0 := by
  intro P k β γ v i₀ c _hv hβ j
  classical
  -- the right side is `c²` times a sum of squares and zeros
  have hRHS : 0 ≤ c ^ 2 * ∑ i : Fin (k + 1),
      (if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0) :=
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  by_cases hj : Injective j
  · -- `(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`, with `β(v_{j(i)}) = c [j(i) = i₀]`
    have hexp : ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
        (fun m => v (j m)) = ∑ i : Fin (k + 1),
          (-1 : ℝ) ^ (i : ℕ) *
            ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smulRight_apply, hβ (j i)]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rfl
    rw [hexp]
    by_cases hex : ∃ i₁, j i₁ = i₀
    · -- `j` is injective, so `i₁` is the only index with `j(i₁) = i₀`
      obtain ⟨i₁, hi₁⟩ := hex
      have huniq : ∀ i, i ≠ i₁ → j i ≠ i₀ := fun i hi h => hi (hj (h.trans hi₁.symm))
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by rw [ite_eq_right (huniq i hi)]; ring)
          (fun h => absurd (Finset.mem_univ i₁) h),
        Finset.sum_eq_single i₁ (fun i _ hi => ite_eq_right (huniq i hi))
          (fun h => absurd (Finset.mem_univ i₁) h),
        ite_eq_left hi₁, ite_eq_left hi₁]
      have hsign : ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      refine le_of_eq ?_
      calc ((-1 : ℝ) ^ (i₁ : ℕ) * (c * γ (fun m => v (i₁.removeNth j m)))) ^ 2
          = ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 * (c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2) := by
            ring
        _ = c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2 := by rw [hsign, one_mul]
    · -- no index hits `i₀`: every term vanishes
      have h0 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
          ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [ite_eq_right fun h => hex ⟨i, h⟩]; ring
      rw [h0]
      simpa using hRHS
  · -- a repeated index makes `v ∘ j` non-injective, and `β ∧ γ` is alternating
    have hvj : ¬ Injective (fun m => v (j m)) := fun h => hj (Injective.of_comp (f := v) h)
    rw [ContinuousAlternatingMap.map_eq_zero_of_not_injective _ _ hvj]
    simpa using hRHS
/-- **Fibres of `j ↦ removeNth i j`** (the counting step of the bound `|β ∧ γ| ≤ ‖β‖ |γ|` for the
Euclidean norm of covectors, Simon Ch. 6, 1.1–1.3, 1.15): for `i₀ : Fin P` and
`F : (Fin k → Fin P) → ℝ`,
`Σ_{j : Fin (k+1) → Fin P} Σ_i [j i = i₀] F(removeNth i j) = (k + 1) Σ_{j' : Fin k → Fin P} F j'`.
For fixed `i`, `j ↦ (j i, removeNth i j)` is a bijection onto `Fin P × (Fin k → Fin P)`
(`Fin.insertNthEquiv`), so only `j i = i₀` survives and each of the `k + 1` indices `i`
contributes `Σ_{j'} F j'`. -/
theorem Submission.cmcs_wn_removeNth_fiber_sum : ∀ (k P : ℕ) (i₀ : Fin P) (F : (Fin k → Fin P) → ℝ), ∑ j : Fin (k + 1) → Fin P, ∑ i : Fin (k + 1), (if j i = i₀ then F (i.removeNth j) else 0) = ((k : ℝ) + 1) * ∑ j' : Fin k → Fin P, F j' := by
  intro k P i₀ F
  rw [Finset.sum_comm]
  -- for fixed `i`, reindex along `j ↦ (j i, removeNth i j)`; only `j i = i₀` survives
  have hfib : ∀ i : Fin (k + 1),
      ∑ j : Fin (k + 1) → Fin P, (if j i = i₀ then F (i.removeNth j) else 0) =
        ∑ j' : Fin k → Fin P, F j' := by
    intro i
    rw [Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Fin P) i).symm
      (fun j => if j i = i₀ then F (i.removeNth j) else 0)
      (fun p => if p.1 = i₀ then F p.2 else 0) fun _ => rfl,
      Fintype.sum_prod_type, Fintype.sum_eq_single i₀]
    · simp
    · intro x hx
      simp [hx]
  -- each of the `k + 1` indices `i` contributes `Σ_{j'} F j'`
  rw [Finset.sum_congr rfl fun i _ => hfib i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add_one]
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **`|β ∧ γ| ≤ ‖β‖ |γ|`** (Simon 6.1.1–1.3 and 1.15): for a linear functional `β` and a
`k`-covector `γ` on `ℝᴾ`, the Euclidean coefficient norm of the `(k+1)`-covector
`β ∧ γ = alternatizeUncurryFin (β.smulRight γ)` is at most `‖β‖ |γ|`.  Take an orthonormal basis
`f` with `β(fᵢ) = ‖β‖ [i = i₀]`; then `(β ∧ γ)(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²`.
Summing over `j`, each `j' : Fin k → Fin P` arises as `i.removeNth j` with `j i = i₀` for exactly
`k + 1` pairs `(i, j)`, so `(k+1)! |β ∧ γ|² ≤ ‖β‖² (k+1) k! |γ|²` by
`regcomp_covector_sq_sum_orthonormalBasis` in degrees `k + 1` and `k`.  For `P = 0` there are no
coordinate tuples and `|β ∧ γ| = 0`. -/
theorem Submission.cmcs_wedge_norm_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k), covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)) ≤ ‖β‖ * covectorEuclideanNorm γ := by
  intro P k β γ
  classical
  set ω := ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
  have hrhs : 0 ≤ ‖β‖ * covectorEuclideanNorm γ :=
    mul_nonneg (norm_nonneg β) (covectorEuclideanNorm_nonneg γ)
  rcases Nat.eq_zero_or_pos P with hP | hP
  · -- `P = 0`: there is no tuple `Fin (k + 1) → Fin 0`, so `|ω| = 0`
    subst hP
    have h0 : covectorEuclideanNorm ω = 0 := by
      simp [covectorEuclideanNorm]
    rw [h0]
    exact hrhs
  · -- an orthonormal basis `f` with `β(fᵢ) = ‖β‖ [i = i₀]`
    set i₀ : Fin P := ⟨0, hP⟩
    obtain ⟨f, hf⟩ := Submission.cmcs_wn_adapted_orthonormalBasis P β i₀
    -- `ω(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²` for every `j`
    have hle : ∑ j : Fin (k + 1) → Fin P, (ω (fun m => f (j m))) ^ 2 ≤
        ∑ j : Fin (k + 1) → Fin P, ‖β‖ ^ 2 * ∑ i : Fin (k + 1),
          (if j i = i₀ then (γ (fun m => f (i.removeNth j m))) ^ 2 else 0) :=
      Finset.sum_le_sum fun j _ => Submission.cmcs_wn_tuple_sq_le P k β γ f i₀ ‖β‖
        f.orthonormal.linearIndependent.injective hf j
    -- count the fibres of `j ↦ i.removeNth j`, then `Σ_j α(f ∘ j)² = m! |α|²` for `m = k + 1, k`
    rw [← Finset.mul_sum,
      Submission.cmcs_wn_removeNth_fiber_sum k P i₀ (fun j' => (γ (fun m => f (j' m))) ^ 2),
      Submission.regcomp_covector_sq_sum_orthonormalBasis P (k + 1) ω f,
      Submission.regcomp_covector_sq_sum_orthonormalBasis P k γ f] at hle
    -- cancel `(k+1)! = (k+1) k! > 0`
    have hpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hsq : covectorEuclideanNorm ω ^ 2 ≤ (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hpos
      calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm ω ^ 2
          ≤ ‖β‖ ^ 2 * (((k : ℝ) + 1) * ((k.factorial : ℝ) * covectorEuclideanNorm γ ^ 2)) := hle
        _ = ((k + 1).factorial : ℝ) * (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
          push_cast [Nat.factorial_succ]
          ring
    exact (sq_le_sq₀ (covectorEuclideanNorm_nonneg ω) hrhs).mp hsq

/-- **Simon Ch. 6, 4.11 (p. 158), the estimate of the cutoff defect**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')` with `|⟨α, ξ⟩| ≤ |α|` `μ`-a.e.: for a `C^∞` function `g`
and `η ∈ 𝒟ᵏ(U)`, `|∫ g ⟨dη, ξ⟩ dμ − ∫ g ⟨η, ξ'⟩ dμ'| ≤ ∫ |Dg| |η| dμ` in `[0, ∞]`.  The left side
is `|T(g dη) − ∂T(gη)| = |T(dg ∧ η)| = |∫ ⟨dg ∧ η, ξ⟩ dμ|` (`cmcs_cd_defect_identity`, with
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`), which is at most `∫ |⟨dg ∧ η, ξ⟩| dμ` whether
or not the integrand is integrable; and `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|` `μ`-a.e. by the bound
on `ξ` and `cmcs_wedge_norm_le`. -/
theorem Submission.cmcs_cutoff_defect_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ENNReal.ofReal |∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ'| ≤ ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm ((η : DifferentialForm (Euclid P) k) x)) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hξ hT hbT hg
  -- Simon 4.11: `T(g dη) − ∂T(gη) = −T(dg ∧ η) = −∫ ⟨dg ∧ η, ξ⟩ dμ`
  rw [Submission.cmcs_cd_defect_identity P k U T μ μ' ξ ξ' g η hT hbT hg, abs_neg,
    ← Real.enorm_eq_ofReal_abs]
  -- `‖∫ G dμ‖ₑ ≤ ∫⁻ ‖G‖ₑ dμ` for every `G`, integrable or not; then bound `G` `μ`-a.e.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hξ] with x hx
  -- `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|`
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((hx _).trans (Submission.cmcs_wedge_norm_le P k _ _))
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]

/-- **Smoothing of Lipschitz functions** (Simon Ch. 6, 4.8–4.9: use `f^{(σ)}` in place of a
Lipschitz `f`): a `K`-Lipschitz `g` on `ℝᴾ` and `σ > 0` give a `C^∞` function `g'` with
`‖Dg'‖ ≤ K`, `|g' − g| ≤ Kσ`, and `g'(x) = c` whenever `g ≡ c` on `B_σ(x)`.  Take the normalized
mollifier `ψ` (`support ψ ⊆ B_σ(0)`) and `g' = ψ ⋆ g`, `g'(x) = ∫ ψ(y) g(x − y) dy`: it is `C^∞`
(`ψ` is smooth with compact support, `g` is continuous) and `K`-Lipschitz, so `‖Dg'‖ ≤ K`.  The
last two claims are `dist_convolution_le` on `B_σ(x)`, with `ε = Kσ`, `z₀ = g(x)` and with
`ε = 0`, `z₀ = c`.  (`ContDiffBump.normed` and its convolution lemmas are outside the import
closure.) -/
theorem Submission.cmcs_lipschitz_smoothing : ∀ (P : ℕ) (g : Euclid P → ℝ) (K : NNReal) (σ : ℝ), LipschitzWith K g → 0 < σ → ∃ g' : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g' ∧ (∀ x, ‖fderiv ℝ g' x‖ ≤ K) ∧ (∀ x, |g' x - g x| ≤ K * σ) ∧ ∀ (x : Euclid P) (c : ℝ), (∀ y ∈ ball x σ, g y = c) → g' x = c := by
  intro P g K σ hg hσ
  obtain ⟨ψ, hψd, hψs, hψ0, hψ1, hψb⟩ := Submission.dgcr_stc_exists_normalized_mollifier P σ hσ
  -- `g' = ψ ⋆ g`
  have hconv : (fun x => ∫ y, ψ y * g (x - y)) =
      convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine ⟨fun x => ∫ y, ψ y * g (x - y), ?_, fun x => ?_, fun x => ?_, fun x c hc => ?_⟩
  · rw [hconv]
    exact hψs.contDiff_convolution_left _ hψd hg.continuous.locallyIntegrable
  · exact norm_fderiv_le_of_lipschitz ℝ
      (Submission.cmcs_ls_mollify_lipschitz P ψ g K hψd.continuous hψs hψ0 hψ1 hg)
  · -- `dist (g y) (g x) ≤ K ‖y − x‖ ≤ Kσ` on `B_σ(x)`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (mul_nonneg K.coe_nonneg hσ.le) hψb hψ0 hψ1 hg.continuous.aestronglyMeasurable
      (fun y hy => (hg.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg))
    rwa [← hconv, Real.dist_eq] at h
  · -- `g ≡ c` on `B_σ(x)`, so `dist (g' x) c ≤ 0`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := c) le_rfl hψb hψ0 hψ1
      hg.continuous.aestronglyMeasurable (fun y hy => by rw [hc y hy, dist_self])
    rw [← hconv] at h
    exact dist_le_zero.1 h

/-- **Smooth cut-off between two levels of a Lipschitz function** (Simon Ch. 6, proof of 4.9, with
`f^{(σ)}` in place of `f`).  If `f : ℝᴾ → ℝ` is `L`-Lipschitz, `t ∈ ℝ` and `0 < h < 1`, there is a
`C^∞` function `g` with `|g| ≤ 2`, `‖Dg‖ ≤ L/(h(1 − h/2))`, `g = 1` on `{f ≤ t − h}`, `g = 0` on
`{f ≥ t}` and `Dg = 0` off the strip `{t − h < f < t}`.  With `δ = h²/4` and
`w = h − 2δ = h(1 − h/2)`, the clamp `G = max 0 (min 1 ((t − δ − f)/w))` is `(L/w)`-Lipschitz,
`G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`; `g` is its smoothing at scale
`σ = δ/(2(L + 1))` (`cmcs_lipschitz_smoothing`), so `|g − G| ≤ Lσ/w ≤ 1`.  As `2Lσ < δ`, `G` is
constant on `B_{2σ}(x)` when `f x ≤ t − h` or `t ≤ f x`; by locality `g` is then constant on
`B_σ(x)`, so `Dg(x) = 0`. -/
theorem Submission.cmcs_level_cutoff : ∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (t h : ℝ), LipschitzWith L f → 0 < h → h < 1 → ∃ g : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧ (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧ (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
  intro P f L t h hf h0 h1
  -- parameters `δ = h²/4`, `w = h − 2δ = h(1 − h/2)` and `σ = δ/(2(L + 1))`, so `2Lσ < δ`
  set δ : ℝ := h ^ 2 / 4 with hδ
  set w : ℝ := h * (1 - h / 2) with hw
  have hw0 : 0 < w := mul_pos h0 (by linarith)
  have hδ0 : 0 < δ := by positivity
  have hL0 : (0 : ℝ) ≤ L := L.2
  set σ : ℝ := δ / (2 * ((L : ℝ) + 1)) with hσ
  have hσ0 : 0 < σ := by positivity
  have h2Lσ : 2 * (L : ℝ) * σ < δ := by
    rw [hσ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the clamped profile `G = max 0 (min 1 ((t − δ − f)/w))`: `(L/w)`-Lipschitz, `|G| ≤ 1`,
  -- `G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`
  set G : Euclid P → ℝ := fun x => max 0 (min 1 ((t - δ - f x) / w)) with hGdef
  set K : NNReal := L * Real.toNNReal w⁻¹ with hK
  have hKr : (K : ℝ) = L / w := by
    rw [hK, NNReal.coe_mul, Real.coe_toNNReal _ (inv_pos.2 hw0).le, div_eq_mul_inv]
  have hG : LipschitzWith K G := by
    have hlin : LipschitzWith K fun x => (t - δ - f x) / w := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hxy := hf.dist_le_mul x y
      rw [Real.dist_eq] at hxy
      rw [Real.dist_eq, hKr, show (t - δ - f x) / w - (t - δ - f y) / w = (f y - f x) / w by ring,
        abs_div, abs_of_pos hw0, abs_sub_comm, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hxy hw0.le
    exact (hlin.const_min 1).const_max 0
  have hG01 : ∀ y, |G y| ≤ 1 := by
    intro y
    simp only [hGdef]
    rw [abs_le]
    exact ⟨by linarith [le_max_left 0 (min 1 ((t - δ - f y) / w))],
      max_le zero_le_one (min_le_left _ _)⟩
  have hG1 : ∀ y, f y < t - h + δ → G y = 1 := by
    intro y hy
    have : 1 ≤ (t - δ - f y) / w := by rw [le_div_iff₀ hw0]; linarith
    simp [hGdef, min_eq_left this]
  have hG0 : ∀ y, t - δ < f y → G y = 0 := by
    intro y hy
    have : (t - δ - f y) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
    simp only [hGdef]
    exact max_eq_left ((min_le_right _ _).trans this)
  -- smoothing of `G` at scale `σ`
  obtain ⟨g, hgs, hgd, hga, hgl⟩ := Submission.cmcs_lipschitz_smoothing P G K σ hG hσ0
  -- plateaus: if `G = c` on `B_{2σ}(x)`, then `g = c` on `B_σ(x)`, so `g x = c` and `Dg(x) = 0`
  have hnear : ∀ x, ∀ c : ℝ, (∀ y ∈ ball x (2 * σ), G y = c) → g x = c ∧ fderiv ℝ g x = 0 := by
    intro x c hc
    have hball : ∀ x' ∈ ball x σ, g x' = c := fun x' hx' => hgl x' c fun y hy => hc y (by
      rw [mem_ball] at hx' hy ⊢
      linarith [dist_triangle y x' x])
    have hev : g =ᶠ[𝓝 x] fun _ => c := Filter.eventually_of_mem (ball_mem_nhds x hσ0) hball
    exact ⟨hball x (mem_ball_self hσ0), hev.fderiv_eq.trans (fderiv_const_apply c)⟩
  -- on `B_{2σ}(x)`, `|f y − f x| ≤ L |y − x| < 2Lσ < δ`
  have hclose : ∀ x, ∀ y ∈ ball x (2 * σ), |f y - f x| < δ := by
    intro x y hy
    have hd := hf.dist_le_mul y x
    rw [Real.dist_eq] at hd
    rw [mem_ball] at hy
    have : (L : ℝ) * dist y x ≤ L * (2 * σ) := mul_le_mul_of_nonneg_left hy.le hL0
    linarith
  have hlow : ∀ x, f x ≤ t - h → g x = 1 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 1 fun y hy => hG1 y (by linarith [(abs_lt.1 (hclose x y hy)).2])
  have hup : ∀ x, t ≤ f x → g x = 0 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 0 fun y hy => hG0 y (by linarith [(abs_lt.1 (hclose x y hy)).1])
  refine ⟨g, hgs, fun x => ?_, fun x => (hgd x).trans_eq hKr, fun x hx => ?_,
    fun x hx => (hlow x hx).1, fun x hx => (hup x hx).1⟩
  · -- `|g| ≤ |G| + Kσ ≤ 2`, as `Kσ = Lδ/(2(L + 1)w) ≤ 1` (`δ ≤ 2w`)
    have hKσ : (K : ℝ) * σ ≤ 1 := by
      rw [hKr, hσ, div_mul_div_comm, div_le_one (by positivity)]
      have hδw : δ ≤ 2 * w := by rw [hδ, hw]; nlinarith
      nlinarith
    linarith [abs_sub_abs_le_abs_sub (g x) (G x), hga x, hG01 x]
  · -- `Dg = 0` on both plateaus, so `Dg(x) ≠ 0` forces `t − h < f x < t`
    by_contra hcon
    rcases not_and_or.1 hcon with hc | hc
    · exact hx (hlow x (not_lt.1 hc)).2
    · exact hx (hup x (not_lt.1 hc)).2

/-- **Mass of a slice, pointwise in `t`** (Simon 6.4.9, proved as in 6.4.11): let `T = ξ μ`,
`∂T = ξ' μ'` with `|ξ|, |ξ'| ≤ 1`, let `f` be `L`-Lipschitz, and let `A = T ⌞ {f < t}`,
`B = (∂T) ⌞ {f < t}`.  Then `M_W(∂A − B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})`.
For an admissible `η` and `h ∈ (0, 1)`, the smooth cut-off `g_h` of `cmcs_level_cutoff` gives
`Φ_h = ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ'` with `|Φ_h| ≤ ∫ |Dg_h| |η| dμ ≤ c_h μ(W ∩ S_h)`,
`c_h = L / (h(1 − h/2))`, `S_h = {t − h < f < t}` (`cmcs_cutoff_defect_bound`,
`cmcs_smp_strip_lintegral_le`); `Φ_h → (∂A − B)(η)` by dominated convergence
(`cmcs_smp_cutoff_integral_tendsto`), and `cmcs_smp_liminf_bound` passes to the liminf. -/
theorem Submission.cmcs_slice_mass_pointwise : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k) (W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (A.boundary - B).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro P k U T μ μ' ξ ξ' f L t A B W hμ hμ' hξm hξm' hξ hξ' hT hbT hf hA hB
  -- Step 3: a cut-off `g h` for every `h ∈ (0, 1)` (junk value `0` for other `h`).
  have hcut : ∀ h : ℝ, ∃ g : Euclid P → ℝ, 0 < h → h < 1 →
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧
        (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧
        (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧
        (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
    intro h
    by_cases hh : 0 < h ∧ h < 1
    · obtain ⟨g, hg⟩ := Submission.cmcs_level_cutoff P f L t h hf hh.1 hh.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨0, fun h0 h1 => (hh ⟨h0, h1⟩).elim⟩
  choose g hg using hcut
  -- Step 1: it suffices to bound `ofReal ((∂A − B) η)` for one admissible `η`.
  apply sSup_le
  rintro r ⟨η, ⟨hηW, hη1⟩, rfl⟩
  have hZ : (A.boundary - B) η =
      (∫ x in {x | f x < t}, ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' := by
    change A (exteriorDerivativeTestOn U k η) - B η = _
    rw [hA, hB]
    rfl
  -- Step 2: `F = ξ(dη)` is `μ`-integrable and `F' = ξ'(η)` is `μ'`-integrable.
  have hF : Integrable
      (fun x => ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x)) μ :=
    Submission.cmcs_smp_pairing_integrable P (k + 1) U μ ξ (exteriorDerivativeTestOn U k η)
      hμ hξm hξ
  have hF' : Integrable (fun x => ξ' x ((η : DifferentialForm (Euclid P) k) x)) μ' :=
    Submission.cmcs_smp_pairing_integrable P k U μ' ξ' η hμ' hξm' hξ'
  -- Step 5: `Φ h → (∂A − B)(η)` as `h ↓ 0`, by dominated convergence for each integral.
  have hfm : Measurable f := hf.continuous.measurable
  have hgm : ∀ ν : Measure (Euclid P), ∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) ν :=
    fun _ h h0 h1 => (hg h h0 h1).1.continuous.aestronglyMeasurable
  have hlim : Tendsto (fun h : ℝ =>
      (∫ x, g h x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x, g h x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ')
      (𝓝[>] 0) (𝓝 ((A.boundary - B) η)) := by
    rw [hZ]
    exact (Submission.cmcs_smp_cutoff_integral_tendsto P μ _ f t 2 g hF hfm (hgm μ)
      (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
      (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2)).sub
      (Submission.cmcs_smp_cutoff_integral_tendsto P μ' _ f t 2 g hF' hfm (hgm μ')
        (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
        (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2))
  -- Steps 4 and 6: `ofReal |Φ h| ≤ ofReal (L / (h (1 − h/2))) μ(W ∩ S_h)` for `h ∈ (0, 1)`,
  -- then pass to the liminf.
  refine Submission.cmcs_smp_liminf_bound L ((A.boundary - B) η) _
    (fun h => μ (W ∩ {x | t - h < f x ∧ f x < t})) hlim fun h h0 h1 => ?_
  obtain ⟨hgs, -, hgd, hgS, -, -⟩ := hg h h0 h1
  exact (Submission.cmcs_cutoff_defect_bound P k U T μ μ' ξ ξ' (g h) η hξ hT hbT hgs).trans
    (Submission.cmcs_smp_strip_lintegral_le P k μ (g h) (η : DifferentialForm (Euclid P) k) W
      {x | t - h < f x ∧ f x < t} _ hgd hgS hηW hη1)
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
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

/-- **Simon Ch. 6, remark before 4.10** (integrated lower left Dini derivative).  For monotone
`F : ℝ → ℝ`, the lower integral over `(a, b)` of `D(t) = liminf_{h → 0+} (F(t) - F(t - h)) / h`
is at most `F(b) - F(a)`.  `F` is differentiable a.e. (Lebesgue), and at a point of
differentiability the left difference quotients tend to `F'(t)`, so `D = F'` a.e.  Changing the
integrand on a null set needs no measurability of `D`, and `∫_(a,b) F' ≤ F(b) - F(a)` is
`cmcs_smi_lintegral_ofReal_deriv_le`. -/
theorem Submission.cmcs_smi_lintegral_left_dini_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  -- `D = ofReal ∘ deriv F` at every point of differentiability, hence a.e.
  have hae : ∀ᵐ t, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) =
      ENNReal.ofReal (deriv F t) := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    have hlim : Tendsto (fun h : ℝ => (F t - F (t - h)) / h) (𝓝[>] 0) (𝓝 (deriv F t)) := by
      refine (ht.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]
      ring
    exact (ENNReal.tendsto_ofReal hlim).liminf_eq
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) := lintegral_congr_ae (ae_restrict_of_ae hae)
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_ofReal_deriv_le F a b hF

/-- **Simon Ch. 6, the remark deriving 4.10 from 4.9, for a measure on `ℝ`.**  For any measure
`ν` on `ℝ`, `∫⁻_{(a,b)} liminf_{h → 0+} h⁻¹ ν((t − h, t)) dt ≤ ν((a, b))` (Simon applies this to
`ν((s, t)) = M_W(T ⌞ {s < f < t})`).  When `ν((a, b)) < ∞`, `F(s) = ν((a, min s b))` is finite
and monotone, with `F a = 0` and `F b = ν((a, b))`.  For `0 < h < t − a`, additivity on
`(a, t − h) ∪ (t − h, t) ⊆ (a, t)` gives `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`, so the left
density is at most the lower left Dini derivative of `F`, whose integral
`cmcs_smi_lintegral_left_dini_le` bounds by `F b − F a`. -/
theorem Submission.cmcs_smi_lintegral_left_density_le : ∀ (ν : Measure ℝ) (a b : ℝ), ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤ ν (Ioo a b) := by
  intro ν a b
  by_cases hN : ν (Ioo a b) = ∞
  · rw [hN]
    exact le_top
  -- the distribution function `F(s) = ν((a, min s b))` of `ν` on `(a, b)`
  set F : ℝ → ℝ := fun s => (ν (Ioo a (min s b))).toReal with hFdef
  have hfin : ∀ s, ν (Ioo a (min s b)) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hN (measure_mono (Ioo_subset_Ioo_right (min_le_right s b)))
  have hFmono : Monotone F := fun s s' hss' =>
    ENNReal.toReal_mono (hfin s') (measure_mono (Ioo_subset_Ioo_right (min_le_min_right b hss')))
  have hofF : ∀ s, ENNReal.ofReal (F s) = ν (Ioo a (min s b)) := fun s =>
    ENNReal.ofReal_toReal (hfin s)
  have hFa : F a = 0 := by
    simp only [hFdef]
    rw [Ioo_eq_empty (not_lt.2 (min_le_left a b)), measure_empty, ENNReal.toReal_zero]
  have hFb : F b = (ν (Ioo a b)).toReal := by
    simp only [hFdef, min_self]
  -- the strip estimate: for `0 < h < t − a`, `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`
  have hstrip : ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a),
      ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t) ≤ ENNReal.ofReal ((F t - F (t - h)) / h) := by
    intro t ht h hh
    have hmt : min t b = t := min_eq_left ht.2.le
    have hmth : min (t - h) b = t - h := min_eq_left (by linarith [hh.1, ht.2])
    have hunion : ν (Ioo a (t - h)) + ν (Ioo (t - h) t) ≤ ν (Ioo a t) := by
      rw [← measure_union _ measurableSet_Ioo]
      · refine measure_mono (union_subset ?_ ?_)
        · exact Ioo_subset_Ioo_right (by linarith [hh.1])
        · exact Ioo_subset_Ioo_left (by linarith [hh.2])
      · rw [Set.disjoint_left]
        intro x hx1 hx2
        linarith [hx1.2, hx2.1]
    have hle : ν (Ioo (t - h) t) ≤ ENNReal.ofReal (F t - F (t - h)) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hofF, hofF, hmt, hmth]
      refine ENNReal.le_sub_of_add_le_left ?_ hunion
      rw [← hmth]
      exact hfin (t - h)
    calc ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)
        ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)) := mul_le_mul_right hle _
      _ = ENNReal.ofReal ((F t - F (t - h)) / h) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hh.1.le), div_eq_inv_mul]
  -- `(0, t − a) ∈ 𝓝[>] 0`, so the strip estimate compares the two liminfs on `(a, b)`
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤
        liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) := by
    intro t ht
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact hstrip t ht h hh
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_left_dini_le F a b hFmono
    _ = ν (Ioo a b) := by rw [hFb, hFa, sub_zero, ENNReal.ofReal_toReal hN]

/-- **Simon Ch. 6, 4.10** (integrated slice-mass bound, with `μ(W ∩ {a < f < s})` in place of
`M_W(T⌞{a < f < s})`): if `m(t) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})` for every
`t ∈ (a, b)`, then `∫⁻_{(a,b)} m ≤ L · μ(W ∩ {a < f < b})`.  The push-forward `ν = f_#(μ⌞W)` has
`ν((s, t)) = μ(W ∩ {s < f < t})`, so the hypothesis reads
`m(t) ≤ L · liminf_{h↓0} h⁻¹ ν((t − h, t))`; pull `L` out of the lower integral (`L ≠ ∞`) and bound
the integrated lower left density of `ν` by `ν((a, b))` (`cmcs_smi_lintegral_left_density_le`).
No measurability of `m` is needed. -/
theorem Submission.cmcs_slice_mass_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (W : Set (Euclid P)) (L : NNReal) (m : ℝ → ℝ≥0∞) (a b : ℝ), Measurable f → MeasurableSet W → (∀ t ∈ Ioo a b, m t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∫⁻ t in Ioo a b, m t ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by
  intro P μ f W L m a b hf _hW hm
  -- `ν = f_#(μ⌞W)`, so `ν((s, t)) = μ(f⁻¹(s, t) ∩ W) = μ(W ∩ {s < f < t})`
  set ν : Measure ℝ := (μ.restrict W).map f with hν
  have hνI : ∀ s t : ℝ, ν (Ioo s t) = μ (W ∩ {x | s < f x ∧ f x < t}) := by
    intro s t
    rw [hν, Measure.map_apply hf measurableSet_Ioo,
      Measure.restrict_apply (hf measurableSet_Ioo), Set.inter_comm]
    rfl
  calc ∫⁻ t in Ioo a b, m t
      ≤ ∫⁻ t in Ioo a b, (L : ℝ≥0∞) *
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => by simpa only [hνI] using hm t ht
    _ = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b,
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (L : ℝ≥0∞) * ν (Ioo a b) :=
        mul_le_mul_right (Submission.cmcs_smi_lintegral_left_density_le ν a b) _
    _ = (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by rw [hνI]

/-- **Simon Ch. 6, 4.6–4.10 (slicing by a Lipschitz function, pp. 157–158)**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')`: `A_t = T ⌞ {f < t}` and `B_t = (∂T) ⌞ {f < t}` (2.9, taken
through the given representations) are currents in `U`, and the slice `⟨T, f, t₋⟩ = ∂A_t − B_t`
(4.6) vanishes on forms supported off `{f = t}` (4.8), has
`M_W(⟨T, f, t₋⟩) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` (4.9), and
`∫⁻_{(a,b)} M_W(⟨T, f, t₋⟩) dt ≤ L · μ(W ∩ {a < f < b})` (4.10).  `A_t`, `B_t` are chosen by
`cmcs_restrict_current`; 4.8 is `cmcs_slice_support` (`f` is continuous); 4.9 is
`cmcs_slice_mass_pointwise`; 4.10 is `cmcs_slice_mass_integral` applied to `t ↦ M_W(∂A_t − B_t)`
and the bound 4.9 (`f` is measurable, `W` open hence measurable). -/
theorem Submission.cmc_slice_mass_bounds : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b})) := by
  intro P k U T μ μ' ξ ξ' f L _hU hμ hμ' hξm hξm' hξ hξ' hT hbT hf
  -- `A t = T ⌞ {f < t}` and `B t = (∂T) ⌞ {f < t}` (Simon 2.9)
  choose A hA using fun t : ℝ =>
    Submission.cmcs_restrict_current P (k + 1) U μ ξ {x | f x < t} hμ hξm hξ
  choose B hB using fun t : ℝ =>
    Submission.cmcs_restrict_current P k U μ' ξ' {x | f x < t} hμ' hξm' hξ'
  -- Simon 4.9, for every `W` and `t`
  have hpt : ∀ (W : Set (Euclid P)) (t : ℝ), ((A t).boundary - B t).massOn W ≤
      (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ *
        μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := fun W t =>
    Submission.cmcs_slice_mass_pointwise P k U T μ μ' ξ ξ' f L t (A t) (B t) W hμ hμ' hξm hξm'
      hξ hξ' hT hbT hf (hA t) (hB t)
  refine ⟨A, B, hA, hB, fun t η hη => ?_, fun W t _ => hpt W t, fun W a b hW => ?_⟩
  · -- Simon 4.8
    exact Submission.cmcs_slice_support P k U T μ μ' ξ ξ' f t (A t) (B t) hf.continuous hT hbT
      (hA t) (hB t) η hη
  · -- Simon 4.10, from 4.9 on `(a, b)`
    exact Submission.cmcs_slice_mass_integral P μ f W L
      (fun t => ((A t).boundary - B t).massOn W) a b hf.continuous.measurable hW.measurableSet
      fun t _ => hpt W t
/-- Restricted representing integrals are determined by the represented current (closure theorem,
Simon Ch. 6, 8.2–8.3, as used for 7.2.4): if `∫ ⟨ω, ξ₁⟩ dμ₁ = ∫ ⟨ω, ξ₂⟩ dμ₂ + ∫ ⟨ω, ξ₃⟩ dμ₃` for
every `ω ∈ 𝒟ᵏ(U)`, the same identity holds for the integrals over every Borel set `B`.  For fixed
`ω` the integrands are integrable (bounded by `|ω|`, which vanishes off the compact `spt ω ⊆ U`).
Testing the hypothesis with `gω`, `g` smooth, and letting `g = (1 - f)ʲ ↓ 𝟙_F` (`f` smooth,
`0 ≤ f ≤ 1`, with support `ℝᴾ \ F`) gives the identity on closed sets `F` by dominated
convergence; Dynkin's π-λ theorem extends it to all Borel sets. -/
theorem Submission.cbr_setIntegral_eq_of_integral_eq : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃ := by
  intro P k U μ₁ μ₂ μ₃ ξ₁ ξ₂ ξ₃ _hU hμ₁ hμ₂ hμ₃ hξ₁ hξ₂ hξ₃ hb₁ hb₂ hb₃ heq B ω hB
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := ω.property.1.1
  have hwc : HasCompactSupport w := ω.property.1.2
  have hwU : tsupport w ⊆ U := ω.property.2
  -- Step 1: `x ↦ ξ x (w x)` is integrable: it vanishes off the compact set `tsupport w ⊆ U` and
  -- is bounded by `sup |w|`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖covectorEuclideanNorm (w x)‖ ≤ C := by
    refine Continuous.bounded_above_of_compact_support ?_
      (hwc.comp_left (g := fun α : Covector (Euclid P) k => covectorEuclideanNorm α)
        (covectorEuclideanNorm_zero P k))
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    exact Continuous.if_const _ ((hws.continuous.eval_const _).pow 2) continuous_const
  have hint : ∀ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k),
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ →
      (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) →
      Integrable (fun x => ξ x (w x)) μ := by
    intro μ ξ hμ hξ hb
    have hsupp : support (fun x => ξ x (w x)) ⊆ tsupport w := by
      intro x hx
      by_contra hxw
      exact hx (by simp [image_eq_zero_of_notMem_tsupport hxw])
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    refine Measure.integrableOn_of_bounded (M := C) (hμ _ hwc hwU).ne
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξ
        hws.continuous.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_of_ae hb] with x hx
    rw [Real.norm_eq_abs]
    exact (hx (w x)).trans ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hC x))
  have hi₁ := hint μ₁ ξ₁ hμ₁ hξ₁ hb₁
  have hi₂ := hint μ₂ ξ₂ hμ₂ hξ₂ hb₂
  have hi₃ := hint μ₃ ξ₃ hμ₃ hξ₃ hb₃
  -- Step 2: testing the hypothesis with the test form `g • w`, `g` smooth.
  have hmul : ∀ g : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      ∫ x, g x * ξ₁ x (w x) ∂μ₁ = ∫ x, g x * ξ₂ x (w x) ∂μ₂ + ∫ x, g x * ξ₃ x (w x) ∂μ₃ := by
    intro g hg
    have hmem : (fun x => g x • w x) ∈ testFormOnSubmodule U k :=
      ⟨⟨hg.smul hws, hwc.mono' ((subset_tsupport _).trans (tsupport_smul_subset_right g w))⟩,
        (tsupport_smul_subset_right g w).trans hwU⟩
    simpa only [Submodule.coe_mk, map_smul, smul_eq_mul] using heq ⟨fun x => g x • w x, hmem⟩
  -- Step 3: closed sets, by smooth approximation of the indicator and dominated convergence.
  have hclosed : ∀ F : Set (Euclid P), IsClosed F →
      ∫ x in F, ξ₁ x (w x) ∂μ₁ = ∫ x in F, ξ₂ x (w x) ∂μ₂ + ∫ x in F, ξ₃ x (w x) ∂μ₃ := by
    intro F hF
    obtain ⟨f, hfs, hfd, hfr⟩ := hF.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
    have hgd : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (1 - f x) ^ n) :=
      fun n => (contDiff_const.sub hfd).pow n
    have hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := fun x => hfr ⟨x, rfl⟩
    have hgb : ∀ (n : ℕ) x, ‖(1 - f x) ^ n‖ ≤ 1 := by
      intro n x
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hf01 x).2])]
      exact pow_le_one₀ (by linarith [(hf01 x).2]) (by linarith [(hf01 x).1])
    have hlim : ∀ (μ : Measure (Euclid P)) (h : Euclid P → ℝ), Integrable h μ →
        Tendsto (fun n : ℕ => ∫ x, (1 - f x) ^ n * h x ∂μ) atTop (𝓝 (∫ x in F, h x ∂μ)) := by
      intro μ h hh
      rw [← integral_indicator hF.measurableSet]
      refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) (fun n => ?_) hh.norm
        (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · exact (hgd n).continuous.aestronglyMeasurable.mul hh.aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hgb n x)
      · by_cases hx : x ∈ F
        · have hfx : f x = 0 := Function.notMem_support.mp (by rw [hfs]; exact fun h => h hx)
          simp [hfx, hx]
        · have hfx : f x ≠ 0 := Function.mem_support.mp (by rw [hfs]; exact hx)
          have hpos : 0 < f x := lt_of_le_of_ne (hf01 x).1 (Ne.symm hfx)
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - f x)
            (by linarith [(hf01 x).2]) (by linarith)).mul_const (h x)
          simpa [hx] using this
    exact tendsto_nhds_unique (hlim μ₁ _ hi₁)
      (((hlim μ₂ _ hi₂).add (hlim μ₃ _ hi₃)).congr fun n => (hmul _ (hgd n)).symm)
  -- Step 4: Dynkin's π-λ theorem extends the identity from closed sets to all Borel sets.
  have hall : ∀ (t : Set (Euclid P)) (_ : MeasurableSet t),
      ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃ := by
    refine MeasurableSpace.induction_on_inter (s := {s | IsClosed s})
      (C := fun t _ =>
        ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃)
      ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
      (by simp) (fun t ht => hclosed t ht) (fun t htm ht => ?_) (fun f hfd hfm hf => ?_)
    · have e₁ := integral_add_compl htm hi₁
      have e₂ := integral_add_compl htm hi₂
      have e₃ := integral_add_compl htm hi₃
      have e := heq ω
      linarith
    · exact (hasSum_integral_iUnion hfm hfd hi₁.integrableOn).unique
        (((hasSum_integral_iUnion hfm hfd hi₂.integrableOn).add
          (hasSum_integral_iUnion hfm hfd hi₃.integrableOn)).congr_fun fun n => hf n)
  exact hall B hB
/-- **A compactly supported integer multiplicity filling of an integer multiplicity boundary**
(Simon Ch. 6, proof of 8.2: the general case reduces to `∂T = 0`).  Let `d < P` and let
`T ∈ 𝒟_{d+1}(ℝᴾ)` have compact support, with `∂T` integer multiplicity and `M(∂T) < ∞`.  `T`
kills the forms `dη` with `spt η ∩ spt T = ∅`, so `spt ∂T ⊆ spt T` is compact.  For `d = m + 1`,
the isoperimetric filling (`m + 1 = d < P`) fills the cycle `∂T` by an integer multiplicity `Y`
supported in a bounded thickening of `spt ∂T`.  For `d = 0`, `∂T = Σ_{x ∈ F} m(x) δ_x`, and
`Σ_{x ∈ F} m(x) = 0` (test `∂T` on a bump `0`-form `≡ 1` near `spt T`), so
`Y = Σ_{x ∈ F} m(x) [[0, x]]` has `∂Y = ∂T` and support in the compact `⋃_{x ∈ F} [0, x]`. -/
theorem Submission.dtc_bc_tc_cl_cc_compact_im_filling : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support) → ∀ (P d : ℕ), d < P → ∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), IsCompact T.support → T.boundary.mass < ∞ → IsIntegerMultiplicity T.boundary → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), IsIntegerMultiplicity Y ∧ Y.boundary = T.boundary ∧ Y.mass < ∞ ∧ IsCompact Y.support := by
  intro hMR hIMC hVO hISO P d hdP T hTc hbm hbim
  -- `spt ∂T ⊆ spt T`, and `spt ∂T` is compact
  obtain ⟨hbsub, hbc⟩ := Submission.rsd_cmr_support_subset_of_vanish P d univ T.support
    T.boundary isOpen_univ hTc (subset_univ _) fun η hη => by
      rw [GeometricCurrentOn.boundary_apply]
      exact hVO P (d + 1) univ T (exteriorDerivativeTestOn univ d η) (Disjoint.mono_left
        (tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) d)) hη)
  rcases d with _ | m
  · -- Case `d = 0`: `∂T = Σ_{x ∈ F} m(x) δ_x`
    obtain ⟨F, m, hF, hsum⟩ :=
      Submission.dmcbr_cc_zero_current_finite_sum hMR hVO P T.boundary hbim hbc
    have hFT : ∀ x ∈ F, x ∈ T.support := fun x hx => hbsub (hF hx)
    -- `Σ_{x ∈ F} m(x) = 0`, testing `∂T` on a bump `0`-form `≡ 1` near `spt T`
    obtain ⟨ρ, hρ, hTρ⟩ := hTc.isBounded.subset_ball_lt 0 (0 : Euclid P)
    let ψ : ContDiffBump (0 : Euclid P) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
    let gf : DifferentialForm (Euclid P) 0 := fun y =>
      ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (ψ y)
    have hg : IsTestForm gf ∧ tsupport gf ⊆ univ :=
      ⟨⟨(ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)).contDiff.comp
          ψ.contDiff,
        ψ.hasCompactSupport.comp_left
          (map_zero (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)))⟩,
        subset_univ _⟩
    let g : TestFormOn (univ : Set (Euclid P)) 0 := ⟨gf, hg⟩
    have hdg : ∀ y ∈ ball (0 : Euclid P) ρ, exteriorDerivative gf y = 0 := by
      intro y hy
      have hψ : fderiv ℝ ψ y = 0 :=
        (ψ.eventuallyEq_one_of_mem_ball hy).fderiv_eq.trans (fderiv_const_apply 1)
      show extDeriv (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (ψ x))
        y = 0
      rw [extDeriv_constOfIsEmpty, hψ]
      ext v
      simp
    have hTg : T.boundary g = 0 := by
      rw [GeometricCurrentOn.boundary_apply]
      refine hVO P (0 + 1) univ T (exteriorDerivativeTestOn univ 0 g)
        (Disjoint.mono ?_ hTρ disjoint_compl_left)
      exact closure_minimal (fun y hy hyρ => hy (hdg y hyρ)) isOpen_ball.isClosed_compl
    have htot : ∑ x ∈ F, (m x : ℝ) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun x hx => ?_) ((hsum g).symm.trans hTg)
      show (m x : ℝ) = (m x : ℝ) * ψ x
      rw [ψ.one_of_mem_closedBall (ball_subset_closedBall (hTρ (hFT x hx))), mul_one]
    -- segments `S_x` with `∂S_x = δ_x − δ_0` and `spt S_x ⊆ [0, x]`
    choose S hSim hSb hSm hSsupp using Submission.dmcbr_cc_segment_current hMR P (0 : Euclid P)
    -- `Y = Σ_{x ∈ F} m(x) S_x` is integer multiplicity
    obtain ⟨Y, hYim, hYeval, hYmass⟩ :=
      Submission.cbr_cc_current_algebra.2.2 hIMC P 1 univ (Euclid P) F S m isOpen_univ
        fun x _ => hSim x
    refine ⟨Y, hYim, ?_, ?_, ?_⟩
    · -- `∂Y = ∂T`
      ext η
      calc Y.boundary η
          = ∑ x ∈ F, (m x : ℝ) * S x (exteriorDerivativeTestOn univ 0 η) := by
            rw [GeometricCurrentOn.boundary_apply]
            exact hYeval (exteriorDerivativeTestOn univ 0 η)
        _ = ∑ x ∈ F, ((m x : ℝ) * (η : DifferentialForm (Euclid P) 0) x (fun i => i.elim0) -
              (m x : ℝ) * (η : DifferentialForm (Euclid P) 0) 0 (fun i => i.elim0)) :=
            Finset.sum_congr rfl fun x _ => by
              rw [← mul_sub, ← hSb x η, GeometricCurrentOn.boundary_apply]
        _ = ∑ x ∈ F, (m x : ℝ) * (η : DifferentialForm (Euclid P) 0) x (fun i => i.elim0) -
              (∑ x ∈ F, (m x : ℝ)) * (η : DifferentialForm (Euclid P) 0) 0 (fun i => i.elim0) := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = T.boundary η := by rw [htot, zero_mul, sub_zero, hsum η]
    · -- `M(Y) ≤ Σ_{x ∈ F} |m(x)| M(S_x) < ∞`
      exact (hYmass univ).trans_lt (ENNReal.sum_lt_top.2 fun x _ =>
        ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hSm x))
    · -- `Y` vanishes off the compact `⋃_{x ∈ F} [0, x]`
      have hC : IsCompact (⋃ x ∈ F, segment ℝ (0 : Euclid P) x) :=
        F.isCompact_biUnion fun x _ => by
          rw [segment_eq_image_lineMap]
          exact isCompact_Icc.image AffineMap.lineMap_continuous
      refine (Submission.rsd_cmr_support_subset_of_vanish P 1 univ _ Y isOpen_univ hC
        (subset_univ _) fun ω hω => ?_).2
      rw [hYeval ω]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [hVO P 1 univ (S x) ω (hω.mono_right ((hSsupp x).trans
        (subset_iUnion₂ (s := fun x (_ : x ∈ F) => segment ℝ (0 : Euclid P) x) x hx))), mul_zero]
  · -- Case `d = m + 1`: fill the cycle `Z = ∂T` by the isoperimetric filling, `m + 1 < P`
    obtain ⟨c, -, hfill⟩ := hISO P m hdP
    obtain ⟨Y, hYim, hYb, hYm, hYsupp⟩ :=
      hfill T.boundary hbim hbc (GeometricCurrentOn.boundary_boundary T) hbm
    refine ⟨Y, hYim, hYb, hYm.trans_lt ENNReal.ofReal_lt_top, ?_⟩
    -- `Y` vanishes off the compact closure of a bounded thickening of `spt Z`
    exact (Submission.rsd_cmr_support_subset_of_vanish P (m + 2) univ _ Y isOpen_univ
      hbc.isBounded.thickening.isCompact_closure (subset_univ _) fun ω hω =>
        hVO P (m + 2) univ Y ω (hω.mono_right (hYsupp.trans subset_closure))).2

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
