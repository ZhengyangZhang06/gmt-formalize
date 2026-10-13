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

/-- Coordinate functionals of a locally bounded `L : C_c(X, ℝᵈ) → ℝ`: `Λᵢ(f) = L(f • eᵢ)` is
linear and locally bounded with the same constants.  `T f := f.compLeft (t ↦ t • eᵢ)` is linear
with `(T f)(x) = f(x) • eᵢ`, `tsupport (T f) ⊆ tsupport f` and `‖(T f)(x)‖ = |f(x)|`;
take `Λᵢ := L ∘ T`. -/
theorem Submission.cmr_vr_coordinate_functional : ∀ (X : Type) [TopologicalSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∀ i : Fin d, ∃ Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ, (∀ (f : CompactlySupportedContinuousMap X ℝ) (g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d))), (∀ x, g x = f x • EuclideanSpace.single i (1 : ℝ)) → L g = Λ f) ∧ ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M := by
  intro X _ d L hL i
  -- `c t = t • eᵢ` is continuous and `c 0 = 0`, so `T f := f.compLeft c` has `(T f) x = f x • eᵢ`
  let c : C(ℝ, EuclideanSpace ℝ (Fin d)) :=
    ⟨fun t => t • EuclideanSpace.single i (1 : ℝ), continuous_id.smul continuous_const⟩
  have hc0 : c 0 = 0 := zero_smul ℝ _
  have hT : ∀ (f : CompactlySupportedContinuousMap X ℝ) (x : X),
      f.compLeft c x = f x • EuclideanSpace.single i (1 : ℝ) :=
    fun f x => CompactlySupportedContinuousMap.compLeft_apply hc0 f x
  -- `T` is linear (pointwise, then extensionality); `Λ := L ∘ T`
  let T : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ]
      CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) :=
    { toFun := fun f => f.compLeft c
      map_add' := fun f₁ f₂ => CompactlySupportedContinuousMap.ext fun x => by
        simp only [hT, CompactlySupportedContinuousMap.add_apply, add_smul]
      map_smul' := fun r f => CompactlySupportedContinuousMap.ext fun x => by
        simp only [hT, CompactlySupportedContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul,
          mul_smul] }
  refine ⟨L ∘ₗ T, fun f g hg => ?_, fun K hK => ?_⟩
  · -- `g = T f` by extensionality
    exact congrArg L (CompactlySupportedContinuousMap.ext fun x => (hg x).trans (hT f x).symm)
  · -- `tsupport (T f) ⊆ tsupport f ⊆ K` and `‖(T f) x‖ = |f x| ≤ 1`: same constant `M`
    obtain ⟨M, hM⟩ := hL K hK
    refine ⟨M, fun f hf hf1 => hM (T f) ?_ fun x => ?_⟩
    · have hTf : ⇑(T f) = fun x => f x • EuclideanSpace.single i (1 : ℝ) := funext (hT f)
      rw [hTf]
      exact (tsupport_smul_subset_left _ _).trans hf
    · show ‖f.compLeft c x‖ ≤ 1
      rw [hT, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      exact hf1 x
/-- Jordan decomposition of a locally bounded `Λ : C_c(X, ℝ) → ℝ`.  For `f : C_c(X, ℝ≥0)` put
`V f := sup {Λ h : |h| ≤ f}` (bounded above by rescaling the local bound on `tsupport f`).  `V` is
additive (clamp `h₁ := (h ⊓ f) ⊔ (-f)`) and `ℝ≥0`-homogeneous, so `V̂ := toRealPositiveLinear V`
is positive; `V̂ + Λ` is positive since `-k` is admissible for `k ≥ 0`, and `Λ = (V̂ + Λ) - V̂`. -/
theorem Submission.cmr_vr_jordan_decomposition : ∀ (X : Type) [TopologicalSpace X] (Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M) → ∃ Λ₁ Λ₂ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, Λ f = Λ₁ f - Λ₂ f := by
  intro X _ Λ hΛ
  -- scaled bound: `tsupport f ⊆ K`, `|f| ≤ s` give `|Λ f| ≤ s * M_K` (`s = 0`, else rescale)
  have hscale : ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ (f : CompactlySupportedContinuousMap X ℝ)
      (s : ℝ), tsupport f ⊆ K → 0 ≤ s → (∀ x, |f x| ≤ s) → |Λ f| ≤ s * M := by
    intro K hK
    obtain ⟨M, hM⟩ := hΛ K hK
    refine ⟨M, fun f s hfK hs hfs => ?_⟩
    rcases hs.eq_or_lt with rfl | hspos
    · have hf0 : f = 0 := by
        ext x
        simpa using hfs x
      simp [hf0]
    · have hsub : tsupport (s⁻¹ • f) ⊆ K :=
        (tsupport_smul_subset_right (fun _ : X => s⁻¹) f).trans hfK
      have hbd : ∀ x, |(s⁻¹ • f) x| ≤ 1 := by
        intro x
        rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, abs_mul,
          abs_of_pos (inv_pos.mpr hspos)]
        calc s⁻¹ * |f x| ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left (hfs x) (inv_pos.mpr hspos).le
          _ = 1 := inv_mul_cancel₀ hspos.ne'
      have h1 := hM _ hsub hbd
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hspos)] at h1
      have := (inv_mul_le_iff₀ hspos).mp h1
      linarith
  -- `A f = {h : |h| ≤ f}` contains `0`, and `Λ '' A f` is bounded above: members of `A f` have
  -- `tsupport h ⊆ tsupport f` and `|h| ≤ max C 0` with `C` a bound for `f`
  let A : CompactlySupportedContinuousMap X NNReal → Set (CompactlySupportedContinuousMap X ℝ) :=
    fun f => {h | ∀ x, |h x| ≤ (f x : ℝ)}
  have hA0 : ∀ f, (0 : CompactlySupportedContinuousMap X ℝ) ∈ A f := by
    intro f x
    simp
  have hbdd : ∀ f, BddAbove (Λ '' A f) := by
    intro f
    obtain ⟨M, hM⟩ := hscale (tsupport f) f.hasCompactSupport.isCompact
    obtain ⟨C, hC⟩ := f.toReal.continuous.bounded_above_of_compact_support
      f.toReal.hasCompactSupport
    refine ⟨max C 0 * M, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have hsupp : tsupport h ⊆ tsupport f := by
      apply closure_mono
      intro x hx hfx
      apply hx
      have := hh x
      rw [hfx] at this
      simpa using this
    have hbd : ∀ x, |h x| ≤ max C 0 := by
      intro x
      refine (hh x).trans ((le_abs_self _).trans ?_)
      have h' : ‖f.toReal x‖ ≤ C := hC x
      rw [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    exact (le_abs_self _).trans (hM h _ hsupp (le_max_right _ _) hbd)
  -- the variation `V f = sup (Λ '' A f) ≥ Λ 0 = 0`
  let V : CompactlySupportedContinuousMap X NNReal → ℝ := fun f => sSup (Λ '' A f)
  have hle : ∀ f, ∀ h ∈ A f, Λ h ≤ V f := fun f h hh => le_csSup (hbdd f) ⟨h, hh, rfl⟩
  have hVle : ∀ f (c : ℝ), (∀ h ∈ A f, Λ h ≤ c) → V f ≤ c := by
    intro f c hc
    exact csSup_le ⟨0, 0, hA0 f, map_zero Λ⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
  have hV0 : ∀ f, 0 ≤ V f := fun f => by simpa using hle f 0 (hA0 f)
  -- additivity: `≤` by the clamp `h₁ = (h ⊓ f) ⊔ (-f)`, `h - h₁ ∈ A g`; `≥` by `h₁ + h₂ ∈ A (f + g)`
  have hadd : ∀ f g, V (f + g) = V f + V g := by
    intro f g
    apply le_antisymm
    · apply hVle
      intro h hh
      let h₁ : CompactlySupportedContinuousMap X ℝ := (h ⊓ f.toReal) ⊔ (-f.toReal)
      have hpt : ∀ x, |h₁ x| ≤ (f x : ℝ) ∧ |(h - h₁) x| ≤ (g x : ℝ) := by
        intro x
        have hx := hh x
        have hf0 : (0 : ℝ) ≤ f x := (f x).2
        have hg0 : (0 : ℝ) ≤ g x := (g x).2
        simp only [CompactlySupportedContinuousMap.add_apply, NNReal.coe_add] at hx
        simp only [h₁, CompactlySupportedContinuousMap.sub_apply,
          CompactlySupportedContinuousMap.sup_apply, CompactlySupportedContinuousMap.inf_apply,
          CompactlySupportedContinuousMap.neg_apply, CompactlySupportedContinuousMap.toReal_apply]
        rw [abs_le] at hx ⊢
        rw [abs_le]
        rcases le_total (h x) (f x) with h1 | h1
        · rw [min_eq_left h1]
          rcases le_total (h x) (-(f x : ℝ)) with h2 | h2
          · rw [max_eq_right h2]
            constructor <;> constructor <;> linarith
          · rw [max_eq_left h2]
            constructor <;> constructor <;> linarith
        · rw [min_eq_right h1, max_eq_left (by linarith)]
          constructor <;> constructor <;> linarith
      have h1mem : h₁ ∈ A f := fun x => (hpt x).1
      have h2mem : h - h₁ ∈ A g := fun x => (hpt x).2
      have e : Λ h = Λ h₁ + Λ (h - h₁) := by rw [map_sub]; ring
      rw [e]
      exact add_le_add (hle f h₁ h1mem) (hle g _ h2mem)
    · have key : V f ≤ V (f + g) - V g := by
        apply hVle
        intro h₁ hh₁
        have : V g ≤ V (f + g) - Λ h₁ := by
          apply hVle
          intro h₂ hh₂
          have hmem : h₁ + h₂ ∈ A (f + g) := by
            intro x
            simp only [CompactlySupportedContinuousMap.add_apply, NNReal.coe_add]
            exact (abs_add_le _ _).trans (add_le_add (hh₁ x) (hh₂ x))
          have := hle _ _ hmem
          rw [map_add] at this
          linarith
        linarith
      linarith
  -- homogeneity: `A 0 = {0}`; for `c > 0`, `h ↦ c⁻¹ • h` maps `A (c • f)` into `A f`
  have hzero : V 0 = 0 := by
    apply le_antisymm _ (hV0 0)
    apply hVle
    intro h hh
    have : h = 0 := by
      ext x
      simpa using hh x
    simp [this]
  have hsmul_le : ∀ (c : NNReal) f, V (c • f) ≤ c * V f := by
    intro c f
    rcases eq_or_ne c 0 with rfl | hc
    · simp [hzero]
    have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    apply hVle
    intro h hh
    have hmem : (c : ℝ)⁻¹ • h ∈ A f := by
      intro x
      have := hh x
      simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, NNReal.coe_mul] at this
      rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hcpos)]
      rw [inv_mul_le_iff₀ hcpos]
      exact this
    have := hle f _ hmem
    rw [map_smul, smul_eq_mul] at this
    exact (inv_mul_le_iff₀ hcpos).mp this
  have hsmul : ∀ (c : NNReal) f, V (c • f) = c * V f := by
    intro c f
    rcases eq_or_ne c 0 with rfl | hc
    · simp [hzero]
    have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    apply le_antisymm (hsmul_le c f)
    have h := hsmul_le c⁻¹ (c • f)
    rw [inv_smul_smul₀ hc, NNReal.coe_inv] at h
    exact (le_inv_mul_iff₀ hcpos).mp h
  -- `V` is `ℝ≥0`-linear; `V̂ := toRealPositiveLinear V` is a positive functional on `C_c(X, ℝ)`
  let W : CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    { toFun := fun f => ⟨V f, hV0 f⟩
      map_add' := fun f g => NNReal.eq (hadd f g)
      map_smul' := fun c f => NNReal.eq (hsmul c f) }
  let Vh := CompactlySupportedContinuousMap.toRealPositiveLinear W
  -- `V̂ + Λ` is positive: for `k ≥ 0`, `V̂ k = V k⁺` and `-k ∈ A k⁺`, so `-Λ k ≤ V̂ k`
  have hdom : ∀ k : CompactlySupportedContinuousMap X ℝ, 0 ≤ k → 0 ≤ Vh k + Λ k := by
    intro k hk
    have hkeq : k.nnrealPart.toReal = k := by
      ext x
      rw [CompactlySupportedContinuousMap.toReal_apply,
        CompactlySupportedContinuousMap.nnrealPart_apply]
      exact Real.coe_toNNReal _ (hk x)
    have hVk : Vh k = V k.nnrealPart := by
      have := CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal W k.nnrealPart
      rw [hkeq] at this
      exact this
    have hmem : -k ∈ A k.nnrealPart := by
      intro x
      rw [CompactlySupportedContinuousMap.neg_apply, abs_neg,
        CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal _ (hk x)]
      exact (abs_of_nonneg (hk x)).le
    have := hle _ _ hmem
    rw [map_neg] at this
    rw [hVk]
    linarith
  refine ⟨PositiveLinearMap.mk₀ (Vh.toLinearMap + Λ) hdom, Vh, fun f => ?_⟩
  show Λ f = (Vh f + Λ f) - Vh f
  ring
/-- Common dominating measure (the common density step of the vector Riesz representation behind
the mass representation of currents, Simon Ch. 6, 2.7–2.8, used for Simon 7.2.4): if every `aᵢ`
and `bᵢ` (`i ∈ Fin m`) is finite on compact sets, then so is `μ₀ := ∑ᵢ (aᵢ + bᵢ)`, and
`aᵢ ≪ μ₀`, `bᵢ ≪ μ₀`.  Indeed `μ₀(s) = ∑ᵢ (aᵢ(s) + bᵢ(s))` for every set `s`, so `μ₀(K)` is a
finite sum of finite terms for compact `K`, and `μ₀(s) = 0` forces `aᵢ(s) = bᵢ(s) = 0`. -/
theorem Submission.cmr_vr_cd_dominating_measure : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] (m : ℕ) (a b : Fin m → Measure X), (∀ i, IsFiniteMeasureOnCompacts (a i)) → (∀ i, IsFiniteMeasureOnCompacts (b i)) → ∃ μ₀ : Measure X, IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, a i ≪ μ₀) ∧ ∀ i, b i ≪ μ₀ := by
  intro X _ _ m a b ha hb
  -- Step 1: `μ₀ := ∑ᵢ (aᵢ + bᵢ)` has `μ₀(s) = ∑ᵢ (aᵢ(s) + bᵢ(s))` for every set `s`
  have hμ₀ : ∀ s : Set X, (∑ i, (a i + b i)) s = ∑ i, (a i s + b i s) := fun s => by
    simp only [Measure.finsetSum_apply, Measure.add_apply]
  refine ⟨∑ i, (a i + b i), ⟨fun K hK => ?_⟩, fun i s hs => ?_, fun i s hs => ?_⟩
  -- Step 2: for compact `K`, `μ₀(K)` is a finite sum of finite terms
  · rw [hμ₀, ENNReal.sum_lt_top]
    exact fun i _ =>
      ENNReal.add_lt_top.2 ⟨(ha i).lt_top_of_isCompact hK, (hb i).lt_top_of_isCompact hK⟩
  -- Step 3: if `μ₀(s) = 0`, every summand `aᵢ(s) + bᵢ(s)` vanishes
  · rw [hμ₀, Finset.sum_eq_zero_iff] at hs
    exact (add_eq_zero.1 (hs i (Finset.mem_univ i))).1
  · rw [hμ₀, Finset.sum_eq_zero_iff] at hs
    exact (add_eq_zero.1 (hs i (Finset.mem_univ i))).2
/-- **Radon–Nikodym density on `C_c`.**  If `μ₀`, `ξ` are finite on compact subsets of a locally
compact second countable space and `ξ ≪ μ₀`, then `ξ` has a measurable density `g`, `μ₀`-integrable
on compact sets, with `f·g` `μ₀`-integrable and `∫ f dξ = ∫ f g dμ₀` for every `f ∈ C_c(X, ℝ)`.
`X` is σ-compact, so `μ₀`, `ξ` are σ-finite and `ξ = μ₀.withDensity δ` for `δ = ξ.rnDeriv μ₀`
(the singular part vanishes since `ξ ≪ μ₀`), with `δ < ∞` `μ₀`-a.e.  Take `g = δ.toReal`: on a
compact `K`, `∫⁻_K δ dμ₀ < ∞` because `ξ(K) < ∞`.  A bounded `f` with compact support times `g` is
integrable on `tsupport f` and vanishes outside it.  The `T2Space` hypothesis is not used. -/
theorem Submission.cmr_vr_cd_density_representation : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ₀ ξ : Measure X), IsFiniteMeasureOnCompacts μ₀ → IsFiniteMeasureOnCompacts ξ → ξ ≪ μ₀ → ∃ g : X → ℝ, Measurable g ∧ (∀ K : Set X, IsCompact K → IntegrableOn g K μ₀) ∧ ∀ f : CompactlySupportedContinuousMap X ℝ, Integrable (fun x => f x * g x) μ₀ ∧ ∫ x, f x ∂ξ = ∫ x, f x * g x ∂μ₀ := by
  intro X _ _ _ _ _ _ μ₀ ξ hμ₀ hξ hac
  -- `X` is σ-compact, so both measures are σ-finite and `(ξ, μ₀)` has a Lebesgue decomposition
  have : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite μ₀ := SigmaFinite.of_isFiniteMeasureOnCompacts μ₀
  have : SigmaFinite ξ := SigmaFinite.of_isFiniteMeasureOnCompacts ξ
  -- `ξ = μ₀.withDensity δ` with `δ = dξ/dμ₀` measurable and `μ₀`-a.e. finite
  set δ : X → ℝ≥0∞ := ξ.rnDeriv μ₀
  have hδm : Measurable δ := Measure.measurable_rnDeriv ξ μ₀
  have hξδ : ξ = μ₀.withDensity δ := by
    have h := Measure.haveLebesgueDecomposition_add ξ μ₀
    rwa [Measure.singularPart_eq_zero_of_ac hac, zero_add] at h
  have hδlt : ∀ᵐ x ∂μ₀, δ x < ∞ := Measure.rnDeriv_lt_top ξ μ₀
  -- `g = δ.toReal` is integrable on compact sets: `∫⁻_K δ dμ₀ < ∞` since `ξ(K) < ∞`
  have hgK : ∀ K : Set X, IsCompact K → IntegrableOn (fun x => (δ x).toReal) K μ₀ := by
    intro K hK
    have hlin : ∫⁻ x in K, δ x ∂μ₀ < ∞ :=
      Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top μ₀ hK.measure_lt_top.ne
    exact integrable_toReal_of_lintegral_ne_top hδm.aemeasurable hlin.ne
  refine ⟨fun x => (δ x).toReal, hδm.ennreal_toReal, hgK, fun f => ⟨?_, ?_⟩⟩
  -- `f` is bounded, so `f·g` is integrable on `tsupport f`, and it vanishes outside
  · obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
    have hon : IntegrableOn (fun x => f x * (δ x).toReal) (tsupport f) μ₀ :=
      Integrable.bdd_mul (c := C) (hgK _ f.hasCompactSupport.isCompact)
        (map_continuous f).measurable.aestronglyMeasurable (Eventually.of_forall hC)
    refine hon.integrable_of_forall_notMem_eq_zero fun x hx => ?_
    simp [image_eq_zero_of_notMem_tsupport hx]
  -- `∫ f dξ = ∫ δ.toReal • f dμ₀`
  · rw [hξδ, integral_withDensity_eq_integral_toReal_smul hδm hδlt]
    congr 1
    funext x
    exact (smul_eq_mul _ _).trans (mul_comm _ _)

/-- Common dominating measure and densities for finitely many pairs of positive functionals
(Riesz–Markov–Kakutani; Rudin, *Real and Complex Analysis*, Thm 2.14 and 6.10).  Let `X` be
locally compact, Hausdorff and second countable with its Borel σ-algebra, and let `Λ₁ᵢ, Λ₂ᵢ`
(`i ∈ Fin m`) be positive linear functionals on `C_c(X, ℝ)`.  Then there are a measure `μ₀`,
finite on compact sets, and measurable `ρᵢ`, `μ₀`-integrable on compact sets, with
`Λ₁ᵢ f - Λ₂ᵢ f = ∫ f ρᵢ dμ₀` for all `f ∈ C_c(X, ℝ)`.

Proof sketch:
* `bᵢ := rieszMeasure Λ₁ᵢ` and `aᵢ := rieszMeasure Λ₂ᵢ` are regular, hence finite on compact
  sets, and `∫ f dbᵢ = Λ₁ᵢ f`, `∫ f daᵢ = Λ₂ᵢ f`.
* `cmr_vr_cd_dominating_measure` gives a compact-finite `μ₀` with `aᵢ ≪ μ₀` and `bᵢ ≪ μ₀`.
* `cmr_vr_cd_density_representation` gives locally integrable densities `gaᵢ`, `gbᵢ` with
  `∫ f daᵢ = ∫ f gaᵢ dμ₀`, `∫ f dbᵢ = ∫ f gbᵢ dμ₀`, both integrands integrable.
* With `ρᵢ := gbᵢ - gaᵢ`, linearity of the integral gives the representation. -/
theorem Submission.cmr_vr_common_density : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (Λ₁ Λ₂ : Fin m → (CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)), ∃ (μ₀ : Measure X) (ρ : Fin m → X → ℝ), IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, Measurable (ρ i)) ∧ (∀ i, ∀ K : Set X, IsCompact K → IntegrableOn (ρ i) K μ₀) ∧ ∀ (i : Fin m) (f : CompactlySupportedContinuousMap X ℝ), Λ₁ i f - Λ₂ i f = ∫ x, f x * ρ i x ∂μ₀ := by
  intro X _ _ _ _ _ _ m Λ₁ Λ₂
  -- Step 1 (RMK): the Riesz measures are regular, hence finite on compact sets
  have ha : ∀ i, IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure (Λ₂ i)) :=
    fun _ => inferInstance
  have hb : ∀ i, IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure (Λ₁ i)) :=
    fun _ => inferInstance
  -- Step 2: a common compact-finite measure `μ₀` with `aᵢ ≪ μ₀` and `bᵢ ≪ μ₀`
  obtain ⟨μ₀, hμ₀, hac_a, hac_b⟩ := Submission.cmr_vr_cd_dominating_measure X m
    (fun i => RealRMK.rieszMeasure (Λ₂ i)) (fun i => RealRMK.rieszMeasure (Λ₁ i)) ha hb
  -- Step 3: locally integrable densities `gaᵢ`, `gbᵢ` of `aᵢ`, `bᵢ` with respect to `μ₀`
  choose ga hga_meas hga_int hga_rep using fun i =>
    Submission.cmr_vr_cd_density_representation X μ₀ (RealRMK.rieszMeasure (Λ₂ i)) hμ₀ (ha i)
      (hac_a i)
  choose gb hgb_meas hgb_int hgb_rep using fun i =>
    Submission.cmr_vr_cd_density_representation X μ₀ (RealRMK.rieszMeasure (Λ₁ i)) hμ₀ (hb i)
      (hac_b i)
  -- Step 4: `ρᵢ := gbᵢ - gaᵢ` and linearity of the integral
  refine ⟨μ₀, fun i => gb i - ga i, hμ₀, fun i => (hgb_meas i).sub (hga_meas i),
    fun i K hK => (hgb_int i K hK).sub (hga_int i K hK), fun i f => ?_⟩
  obtain ⟨hgb_f, hgb_eq⟩ := hgb_rep i f
  obtain ⟨hga_f, hga_eq⟩ := hga_rep i f
  calc Λ₁ i f - Λ₂ i f
      = ∫ x, f x ∂(RealRMK.rieszMeasure (Λ₁ i)) - ∫ x, f x ∂(RealRMK.rieszMeasure (Λ₂ i)) := by
        rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    _ = ∫ x, f x * gb i x ∂μ₀ - ∫ x, f x * ga i x ∂μ₀ := by rw [hgb_eq, hga_eq]
    _ = ∫ x, (f x * gb i x - f x * ga i x) ∂μ₀ := (integral_sub hgb_f hga_f).symm
    _ = ∫ x, f x * (gb i - ga i) x ∂μ₀ := by simp only [Pi.sub_apply, mul_sub]
/-- Assembly of coordinate densities (vector Riesz representation, coordinate step): if the
`i`-th coordinate functional `f ↦ L(f eᵢ)` has density `ρᵢ` w.r.t. `μ₀` for each `i`, then `L` has
the vector density `ν = Σᵢ ρᵢ eᵢ`, i.e. `L g = ∫ ⟨g, ν⟩ dμ₀`.  Write `g = Σᵢ gᵢ eᵢ` with
`gᵢ = ⟨g, eᵢ⟩ ∈ C_c(X)`; each `gᵢ ρᵢ` is integrable (bounded continuous times integrable on the
compact `tsupport gᵢ`, zero outside it), so the finite sum and the integral commute. -/
theorem Submission.cmr_vr_coordinate_assembly : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ) (μ₀ : Measure X) (ρ : Fin d → X → ℝ), (∀ i, Measurable (ρ i)) → (∀ i, ∀ K : Set X, IsCompact K → IntegrableOn (ρ i) K μ₀) → (∀ (i : Fin d) (f : CompactlySupportedContinuousMap X ℝ) (g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d))), (∀ x, g x = f x • EuclideanSpace.single i (1 : ℝ)) → L g = ∫ x, f x * ρ i x ∂μ₀) → ∃ ν : X → EuclideanSpace ℝ (Fin d), Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀ := by
  intro X _ _ _ d L μ₀ ρ hρm hρi hL
  -- `ν = Σᵢ ρᵢ eᵢ`
  refine ⟨fun x => ∑ i, ρ i x • EuclideanSpace.single i (1 : ℝ),
    Finset.measurable_sum _ fun i _ => (hρm i).smul_const _,
    fun K hK => integrable_finsetSum _ fun i _ => (hρi i K hK).smul_const _, fun g => ?_⟩
  -- the coordinates `gᵢ = g(·)ᵢ ∈ C_c(X, ℝ)` and `Gᵢ = gᵢ eᵢ ∈ C_c(X, H)`
  obtain ⟨gc, hgc⟩ : ∃ gc : Fin d → CompactlySupportedContinuousMap X ℝ, ∀ i x, gc i x = g x i :=
    ⟨fun i => g.compLeft (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      fun i x => CompactlySupportedContinuousMap.compLeft_apply (by simp) g x⟩
  obtain ⟨G, hG⟩ : ∃ G : Fin d → CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)),
      ∀ i x, G i x = gc i x • EuclideanSpace.single i (1 : ℝ) :=
    ⟨fun i => (gc i).compLeft ⟨fun t => t • EuclideanSpace.single i (1 : ℝ), by fun_prop⟩,
      fun i x => CompactlySupportedContinuousMap.compLeft_apply (zero_smul ℝ _) (gc i) x⟩
  -- `g = Σᵢ Gᵢ`
  have hsum : g = ∑ i, G i := by
    ext x j
    simp [hG, hgc, Pi.single_apply]
  -- each `gᵢ ρᵢ` is integrable: bounded continuous times integrable on the compact `tsupport gᵢ`
  have hint : ∀ i, Integrable (fun x => gc i x * ρ i x) μ₀ := by
    intro i
    obtain ⟨C, hC⟩ := (gc i).continuous.bounded_above_of_compact_support (gc i).hasCompactSupport
    have hK : IntegrableOn (fun x => gc i x * ρ i x) (tsupport (gc i)) μ₀ :=
      Integrable.bdd_mul (hρi i _ (gc i).hasCompactSupport.isCompact)
        (gc i).continuous.aestronglyMeasurable (Eventually.of_forall hC)
    exact hK.integrable_of_forall_notMem_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  calc L g = ∑ i, L (G i) := (congrArg L hsum).trans (map_sum L G Finset.univ)
    _ = ∑ i, ∫ x, gc i x * ρ i x ∂μ₀ := Finset.sum_congr rfl fun i _ => hL i (gc i) (G i) (hG i)
    _ = ∫ x, ∑ i, gc i x * ρ i x ∂μ₀ := (integral_finsetSum _ fun i _ => hint i).symm
    _ = ∫ x, inner ℝ (g x) (∑ i, ρ i x • EuclideanSpace.single i (1 : ℝ)) ∂μ₀ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_right, EuclideanSpace.inner_single_right, hgc, conj_trivial, one_mul, mul_comm]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
