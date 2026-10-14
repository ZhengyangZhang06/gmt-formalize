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

/-- **Simon Ch. 6, proof of 5.1, step 4** (with `n = m + 1`): a point `x ∈ ℝᴾ` of the lattice
`(m + 1)`-skeleton `L_{m+1}` (at least `P − (m + 1)` integer coordinates) that is not in the
`m`-skeleton `L_m` (fewer than `P − m` integer coordinates) lies on an open unit lattice
`(m + 1)`-face.  The set `J` of integer coordinates of `x` has `P = m + 1 + |J|`, so its
complement is the range of a strictly increasing `ι : Fin (m + 1) → Fin P`.  With `b = ⌊x⌋`
and `y_j = fract(x_{ι(j)})`, which lies in `(0, 1)` as `x_{ι(j)} ∉ ℤ`, coordinatewise
`b + Σⱼ yⱼ e_{ι(j)} = x`: `⌊xᵢ⌋ = xᵢ` for `i ∈ J`, `⌊xᵢ⌋ + fract(xᵢ) = xᵢ` for `i = ι(j₀)`. -/
theorem Submission.dimred_mbl_dtfrsd_skeleton_point_on_open_face : ∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) = x := by
  classical
  rintro P m x ⟨s, hsP, hs⟩ hnot
  -- Step 1: the set `J` of integer coordinates of `x`
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin P), ∀ i, i ∈ J ↔ ∃ z : ℤ, x i = z :=
    ⟨Finset.univ.filter fun i => ∃ z : ℤ, x i = z, fun i => by simp⟩
  -- Steps 2–4: `s ⊆ J` gives `P ≤ m + 1 + |J|`, and `J` itself is not admissible in (ii), so
  -- `m + |J| < P`; hence `|Jᶜ| = P − |J| = m + 1`
  have hcard : Jᶜ.card = m + 1 := by
    have h1 : s.card ≤ J.card := Finset.card_le_card fun i hi => (hJ i).2 (hs i hi)
    have h2 : ¬ P ≤ m + J.card := fun h => hnot ⟨J, h, fun i hi => (hJ i).1 hi⟩
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  -- Step 5: the increasing enumeration `ι` of `Jᶜ`
  obtain ⟨ι, hιmono, hιJ, hιrange⟩ : ∃ ι : Fin (m + 1) → Fin P,
      StrictMono ι ∧ (∀ j, ι j ∉ J) ∧ ∀ i, i ∉ J → ∃ j, ι j = i := by
    refine ⟨Jᶜ.orderEmbOfFin hcard, (Jᶜ.orderEmbOfFin hcard).strictMono,
      fun j => Finset.mem_compl.1 (Jᶜ.orderEmbOfFin_mem hcard j), fun i hi => ?_⟩
    have hrange : i ∈ Set.range (Jᶜ.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.2 hi
    exact hrange
  -- Steps 6–7: `p = (ι, ⌊x⌋)` and `y_j = fract(x_{ι(j)}) ∈ (0, 1)`, since `x_{ι(j)} ∉ ℤ`
  refine ⟨(ι, fun i => ⌊x i⌋), WithLp.toLp 2 fun j => Int.fract (x (ι j)), hιmono,
    fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [PiLp.toLp_apply]
    exact Int.fract_pos.2 fun h => hιJ j ((hJ (ι j)).2 ⟨_, h⟩)
  · rw [PiLp.toLp_apply]
    exact Int.fract_lt_one _
  -- Step 8: the `i`-th coordinate is `⌊xᵢ⌋ + Σⱼ [i = ι(j)] fract(x_{ι(j)}) = xᵢ`
  refine PiLp.ext fun i => ?_
  simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ J
  · -- (a) `i ∈ J`: no `ι(j)` equals `i`, and `⌊xᵢ⌋ = xᵢ` as `xᵢ ∈ ℤ`
    obtain ⟨z, hz⟩ := (hJ i).1 hi
    rw [Finset.sum_eq_zero, add_zero, hz, Int.floor_intCast]
    exact fun j _ => ite_eq_right fun h : i = ι j => hιJ j (h ▸ hi)
  · -- (b) `i = ι(j₀)`: only the `j₀` summand survives, and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ`
    obtain ⟨j₀, rfl⟩ := hιrange i hi
    rw [Finset.sum_eq_single j₀, ite_eq_left rfl, Int.floor_add_fract]
    · exact fun j _ hj => ite_eq_right fun h => hj (hιmono.injective h.symm)
    · exact fun h => absurd (Finset.mem_univ j₀) h
/-- Only finitely many unit lattice faces `b + Σⱼ [0, 1] e_{ι(j)}` (`b ∈ ℤᴾ`, `ι : Fin k → Fin P`
arbitrary) meet a compact `K ⊆ ℝᴾ` (Simon Ch. 6, §5).  If `‖x‖ ≤ ρ` on `K` and
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)} ∈ K` with `y ∈ [0, 1]ᵏ`, then `Φ(y)ᵢ = bᵢ + Sᵢ` with `0 ≤ Sᵢ ≤ k`
and `|Φ(y)ᵢ| ≤ ρ`, so `|bᵢ| ≤ ⌈ρ⌉ + k`: the set lies in the finite set `(all ι) × [-N, N]ᴾ`. -/
theorem Submission.dimred_mbl_dtfrsd_faces_meeting_compact_finite : ∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ K}.Finite := by
  intro P k K hK
  -- `K` is bounded: `‖x‖ ≤ ρ` for `x ∈ K`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  -- the set lies in `(Fin k → Fin P) × [-N, N]ᴾ`, `N = ⌈ρ⌉ + k`, which is finite
  refine (Set.finite_univ.prod (Set.Finite.pi fun _ =>
    Set.finite_Icc (-(⌈ρ⌉ + k)) (⌈ρ⌉ + k))).subset ?_
  rintro ⟨ι, b⟩ ⟨y, hy, hxK⟩
  refine ⟨Set.mem_univ _, fun i _ => ?_⟩
  -- coordinate formula `Φ(y)ᵢ = bᵢ + Sᵢ`, `Sᵢ = Σⱼ [i = ι j] yⱼ`
  have hcoord : (WithLp.toLp 2 (fun i => (b i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) i =
      (b i : ℝ) + ∑ j, if i = ι j then y j else 0 := by
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  -- `|bᵢ + Sᵢ| = |Φ(y)ᵢ| ≤ ‖Φ(y)‖ ≤ ρ`
  have hxi : |(b i : ℝ) + ∑ j, if i = ι j then y j else 0| ≤ ρ := by
    rw [← hcoord, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans (hρ _ hxK)
  -- `0 ≤ Sᵢ ≤ k`: each of the `k` summands lies in `[0, 1]`
  have hS0 : 0 ≤ ∑ j, if i = ι j then y j else 0 :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> linarith [(hy j).1]
  have hS1 : (∑ j, if i = ι j then y j else 0) ≤ k :=
    calc (∑ j, if i = ι j then y j else 0) ≤ ∑ _j : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> linarith [(hy j).2]
      _ = k := by simp
  -- hence `-(⌈ρ⌉ + k) ≤ bᵢ ≤ ⌈ρ⌉ + k`
  obtain ⟨h1, h2⟩ := abs_le.mp hxi
  have hc := Int.le_ceil ρ
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have : ((-(⌈ρ⌉ + k) : ℤ) : ℝ) ≤ b i := by push_cast; linarith
    exact_mod_cast this
  · have : (b i : ℝ) ≤ ((⌈ρ⌉ + k : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
/-- **Simon Ch. 6, 1.1, 3.1 and Ch. 3, 1.4**: on a Borel set `E` lying in the coordinate `n`-plane
`{a : aᵢ = cᵢ for i ∉ range ι}`, the orientation `ξ` of an integer multiplicity triple
`(M, θ, ξ)` in an open `U` is `Hⁿ`-a.e. on `M ∩ E` a Borel sign `σ ∈ {−1, 0, 1}` times the
coordinate `n`-vector `e_ι = e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`, `⟨α, e_ι⟩ = α(e_{ι(1)}, …, e_{ι(n)})`.
This is assumed: (IMC-b) the restriction of `(M, θ, ξ)` to `M ∩ E` is a triple with the same
`ξ`; (PO) a unit orientation of an approximate tangent plane at `x` of a set whose points agree
with `x` off `range ι` is `±e_ι`.  By (IMC-b), `ξ(x)` orients an approximate tangent plane of
`M ∩ E` at `Hⁿ`-a.e. `x ∈ M ∩ E`; points of `E` agree with `x` off `range ι`, so (PO) gives
`ξ(x) = ±e_ι`.  For a strongly measurable version `ξ̃` of `ξ`, `σ = 1` on `{ξ̃ = e_ι}`,
`σ = −1` on `{ξ̃ ≠ e_ι, ξ̃ = −e_ι}` and `σ = 0` elsewhere is Borel (the operator-norm topology
on `n`-vectors is metrizable), and `ξ = ξ̃ = σ e_ι` `Hⁿ`-a.e. on `M ∩ E`. -/
theorem Submission.dimred_mbl_dtfrsd_coordinate_plane_orientation_sign : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ι : Fin n → Fin P) (c : Euclid P) (E : Set (Euclid P)), IsOpen U → StrictMono ι → MeasurableSet E → (∀ a ∈ E, ∀ i, (∀ j, ι j ≠ i) → a i = c i) → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  classical
  intro hIMC hPO P n U R ι c E hU hι hE hEc
  have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
  -- (IMC-b): the restriction `R'` of `R` to `M ∩ E` keeps `ξ`, so `Hⁿ`-a.e. on `M ∩ E`, `ξ(x)`
  -- orients an approximate tangent plane of `M ∩ E` at `x`
  obtain ⟨_, R', _, hR'c, _, hR'o⟩ := hIMC P n U R E hU hE
  have h1 := R'.orients
  rw [hR'c, hR'o] at h1
  -- (PO): `ξ(x) = ±e_ι` a.e. on `M ∩ E`, as all points of `E` agree with `x` off `range ι`
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)),
      (∀ α : Covector (Euclid P) n,
        R.orient x α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨
      ∀ α : Covector (Euclid P) n,
        R.orient x α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    filter_upwards [h1, ae_restrict_mem hME] with x hxQ hx
    obtain ⟨Q, hQ, hξQ⟩ := hxQ
    refine hPO P n ι (R.carrier ∩ E) x Q (R.orient x) hι (fun a ha i hi => ?_) hQ hξQ
    rw [hEc a ha.2 i hi, hEc x hx.2 i hi]
  -- a strongly measurable version `ξ̃` of `ξ`; `ξ = ξ̃` a.e. on `M`, hence on `M ∩ E`
  obtain ⟨ξt, hξt, h3⟩ : ∃ ξt : Euclid P → MultiVector P n, StronglyMeasurable ξt ∧
      R.orient =ᵐ[μHE[n].restrict R.carrier] ξt :=
    ⟨_, R.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      R.aestronglyMeasurable_orient.ae_eq_mk⟩
  have h3' : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), R.orient x = ξt x :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left h3
  -- the coordinate `n`-vector `e_ι`
  obtain ⟨e, he⟩ : ∃ e : MultiVector P n, ∀ α : Covector (Euclid P) n,
      e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) :=
    ⟨ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _, fun α => rfl⟩
  -- the operator-norm topology on `n`-vectors is metrizable, so `{ξ̃ = ±e_ι}` are Borel
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    ⟨⟨(inferInstance : PseudoMetricSpace (MultiVector P n)).toUniformSpace, rfl,
      @EMetric.instIsCountablyGeneratedUniformity _
        (inferInstance : PseudoMetricSpace (MultiVector P n)).toPseudoEMetricSpace⟩⟩
  have hm1 : MeasurableSet {x | ξt x = e} := hξt.measurableSet_eq_fun stronglyMeasurable_const
  have hm2 : MeasurableSet {x | ξt x = -e} := hξt.measurableSet_eq_fun stronglyMeasurable_const
  -- `σ = 1` on `{ξ̃ = e_ι}`, `σ = −1` on `{ξ̃ ≠ e_ι, ξ̃ = −e_ι}`, `σ = 0` elsewhere
  refine ⟨fun x => if ξt x = e then 1 else if ξt x = -e then -1 else 0,
    Measurable.ite hm1 measurable_const (Measurable.ite hm2 measurable_const measurable_const),
    fun x => ?_, ?_⟩
  · dsimp only
    split_ifs <;> simp
  · filter_upwards [h2, h3'] with x hx hxt α
    rcases hx with h | h
    · -- `ξ(x) = e_ι`, so `ξ̃(x) = e_ι` and `σ(x) = 1`
      have hte : ξt x = e :=
        hxt.symm.trans (ContinuousLinearMap.ext fun β => (h β).trans (he β).symm)
      rw [ite_eq_left hte, h α, Int.cast_one, one_mul]
    · -- `ξ(x) = −e_ι`, so `ξ̃(x) = −e_ι`; `σ(x) = 1` only if also `ξ̃(x) = e_ι`
      have hte : ξt x = -e :=
        hxt.symm.trans (ContinuousLinearMap.ext fun β => by rw [h β, neg_apply, he β])
      by_cases hte' : ξt x = e
      · rw [ite_eq_left hte', Int.cast_one, one_mul, hxt, hte', he α]
      · rw [ite_eq_right hte', ite_eq_left hte, Int.cast_neg, Int.cast_one, neg_one_mul, h α]

/-- **Simon Ch. 6, proof of 5.1, (27)–(28) (p. 167)**, on one open face of the unit lattice: let
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` be an isometry, `Q₁ = (0, 1)ⁿ` and `F̆ = Φ_p(Q₁)`.  Then
`τ(M, θ, ξ)⌞F̆`, pulled back to `Q₁`, is `u(y) ⟨ω(Φ_p(y)), e_{ι(0)} ∧ ⋯ ∧ e_{ι(n−1)}⟩ dy` for an
integer-valued `u ∈ L¹(Q₁)` with `∫_{Q₁} |u| ≤ μ_V(F̆)`.  `F̆` is Borel and lies in the coordinate
plane through `b`, so `coordinate_plane_orientation_sign` gives `ξ = σ e_{ι(0)} ∧ ⋯ ∧ e_{ι(n−1)}`
`Hⁿ`-a.e. on `M ∩ F̆`, with `σ` integer-valued and `|σ| ≤ 1`.  Take `u = (1_M θ σ) ∘ Φ_p`: isometry
invariance of `μHE` and `μHE = Lⁿ` on `ℝⁿ` give `Hⁿ⌞F̆ = Φ_p#(Lⁿ⌞Q₁)`, and `μ_V(F̆) < ∞` because
`F̆` lies in the compact set `Φ_p([0, 1]ⁿ)`. -/
theorem Submission.dimred_mbl_dtfrsd_face_density : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} ∧ ENNReal.ofReal (∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∫ x in R.carrier ∩ (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = ∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, u y * (ω : DifferentialForm (Euclid P) n) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro hIMC hPO P n R p hι hiso
  -- name the parametrization `Φ = Φ_p`, the open cube `Q₁` and the frame `Ep = E_p`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid n → Euclid P, Φ = fun y : Euclid n =>
      WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Set (Euclid n), Q₁ = {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} :=
    ⟨_, rfl⟩
  obtain ⟨Ep, hEp⟩ : ∃ Ep : Fin n → Euclid P,
      Ep = fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hΦiso : Isometry Φ := by rw [hΦ]; exact hiso
  suffices H : ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u Q₁ ∧
      ENNReal.ofReal (∫ y in Q₁, |u y|) ≤ R.measure (Φ '' Q₁) ∧
      ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
        ∫ x in R.carrier ∩ Φ '' Q₁,
            (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
          ∫ y in Q₁, u y * (ω : DifferentialForm (Euclid P) n) (Φ y) Ep by
    subst hΦ hQ₁ hEp
    exact H
  -- `Q₁` is open, `Φ` is a measurable embedding (an isometry), so `F̆ = Φ(Q₁)` is Borel
  have hQ₁meas : MeasurableSet Q₁ := by
    have hopen : IsOpen Q₁ := by
      have : Q₁ = ⋂ i, {y : Euclid n | 0 < y i ∧ y i < 1} := by
        rw [hQ₁]; ext y; simp
      rw [this]
      refine isOpen_iInter_of_finite fun i => ?_
      have hc : Continuous fun y : Euclid n => y i := by fun_prop
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    exact hopen.measurableSet
  have hΦme : MeasurableEmbedding Φ := hΦiso.isClosedEmbedding.measurableEmbedding
  have hFmeas : MeasurableSet (Φ '' Q₁) := hΦme.measurableSet_image.2 hQ₁meas
  have hMmeas : MeasurableSet R.carrier := R.measurableSet_carrier
  -- `F̆` lies in the coordinate plane through `b`: `aᵢ = bᵢ` for `a ∈ F̆` and `i ∉ range ι`
  have hplane : ∀ a ∈ Φ '' Q₁, ∀ i, (∀ j, p.1 j ≠ i) →
      a i = (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) : Euclid P) i := by
    rintro a ⟨y, -, rfl⟩ i hi
    rw [hΦ]
    simp [Ne.symm (hi _)]
  -- `ξ = σ E_p`, `|σ| ≤ 1`, `Hⁿ`-a.e. on `M ∩ F̆`
  obtain ⟨σ, hσmeas, hσle, hσae⟩ :=
    Submission.dimred_mbl_dtfrsd_coordinate_plane_orientation_sign hIMC hPO P n univ R p.1
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (Φ '' Q₁) isOpen_univ hι hFmeas hplane
  rw [← hEp] at hσae
  -- change of variables: `Hⁿ⌞F̆ = Φ#(Lⁿ⌞Q₁)`
  have hrestr : μHE[n].restrict (Φ '' Q₁) =
      Measure.map Φ ((volume : Measure (Euclid n)).restrict Q₁) := by
    rw [← Measure.restrict_restrict_of_subset (image_subset_range Φ Q₁),
      ← hΦiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      hΦme.restrict_map, hΦme.injective.preimage_image]
  have hcov : ∀ f : Euclid P → ℝ, ∫ x in Φ '' Q₁, f x ∂μHE[n] = ∫ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hΦme.integral_map]
  have hlcov : ∀ f : Euclid P → ℝ≥0∞, ∫⁻ x in Φ '' Q₁, f x ∂μHE[n] = ∫⁻ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hΦme.lintegral_map]
  -- the density `g = 1_M θ σ` (so `u = g ∘ Φ`) and the weight `θ' = 1_M θ`
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℝ,
      g = R.carrier.indicator (fun x => (R.mult x : ℝ) * (σ x : ℝ)) := ⟨_, rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ' : Euclid P → ℝ≥0∞,
      θ' = R.carrier.indicator (fun x => (R.mult x : ℝ≥0∞)) := ⟨_, rfl⟩
  have hgM : ∀ x ∈ R.carrier, g x = (R.mult x : ℝ) * (σ x : ℝ) := fun x hx => by
    rw [hg]; exact indicator_of_mem hx _
  have hg0 : ∀ x ∉ R.carrier, g x = 0 := fun x hx => by
    rw [hg]; exact indicator_of_notMem hx _
  have hgmeas : Measurable g := by
    rw [hg]
    refine Measurable.indicator ?_ hMmeas
    exact ((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).mul
      ((Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp hσmeas)
  have hgint : ∀ x, ∃ z : ℤ, g x = z := by
    intro x
    by_cases hx : x ∈ R.carrier
    · exact ⟨(R.mult x : ℤ) * σ x, by rw [hgM x hx]; push_cast; ring⟩
    · exact ⟨0, by rw [hg0 x hx]; simp⟩
  have hgle : ∀ x, ENNReal.ofReal |g x| ≤ θ' x := by
    intro x
    by_cases hx : x ∈ R.carrier
    · rw [hgM x hx, hθ', indicator_of_mem hx, abs_mul, Nat.abs_cast]
      have h1 : |(σ x : ℝ)| ≤ 1 := by exact_mod_cast hσle x
      calc ENNReal.ofReal ((R.mult x : ℝ) * |(σ x : ℝ)|) ≤ ENNReal.ofReal (R.mult x : ℝ) :=
            ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (Nat.cast_nonneg _) h1)
        _ = (R.mult x : ℝ≥0∞) := ENNReal.ofReal_natCast _
    · rw [hg0 x hx, hθ', indicator_of_notMem hx]; simp
  -- `μ_V(F̆) = ∫_{F̆} 1_M θ dHⁿ = ∫_{Q₁} θ' ∘ Φ`
  have hmass : R.measure (Φ '' Q₁) = ∫⁻ y in Q₁, θ' (Φ y) := by
    rw [← hlcov θ', hθ', IMRep.measure, ← withDensity_indicator hMmeas,
      withDensity_apply _ hFmeas]
  -- `μ_V(F̆) ≤ μ_V(Φ([0, 1]ⁿ)) < ∞` by local integrability of `θ`
  have hfin : R.measure (Φ '' Q₁) < ∞ := by
    obtain ⟨C, hCc, hQC⟩ : ∃ C : Set (Euclid n), IsCompact C ∧ Q₁ ⊆ C := by
      refine ⟨WithLp.toLp 2 '' (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1),
        (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _), ?_⟩
      intro y hy
      rw [hQ₁] at hy
      exact ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
    have hKc : IsCompact (Φ '' C) := hCc.image hΦiso.continuous
    have hKfin : R.measure (Φ '' C) ≠ ∞ := by
      rw [IMRep.measure, withDensity_apply _ hKc.measurableSet,
        Measure.restrict_restrict hKc.measurableSet, inter_comm]
      exact R.locallyIntegrable_mult _ hKc (subset_univ _)
    exact lt_of_le_of_lt (measure_mono (image_mono hQC)) hKfin.lt_top
  -- integrability of `u = g ∘ Φ` on `Q₁` and `∫_{Q₁} |u| ≤ μ_V(F̆)`
  have hlint : ∫⁻ y in Q₁, ENNReal.ofReal |g (Φ y)| ≤ R.measure (Φ '' Q₁) := by
    rw [hmass]
    exact lintegral_mono fun y => hgle (Φ y)
  have huint : Integrable (fun y => g (Φ y)) ((volume : Measure (Euclid n)).restrict Q₁) := by
    refine ⟨(hgmeas.comp hΦiso.continuous.measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hlint hfin
  refine ⟨fun y => g (Φ y), fun y => hgint (Φ y), huint, ?_, fun ω => ?_⟩
  · exact (ofReal_integral_eq_lintegral_ofReal huint.abs
      (Eventually.of_forall fun y => abs_nonneg _)).trans_le hlint
  -- `∫_{M ∩ F̆} θ ⟨ω, ξ⟩ dHⁿ = ∫_{F̆} g ω(E_p) dHⁿ = ∫_{Q₁} u ω(Φ ·)(E_p)`
  calc ∫ x in R.carrier ∩ Φ '' Q₁,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
      = ∫ x in R.carrier ∩ Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x Ep ∂μHE[n] := by
        refine integral_congr_ae ?_
        filter_upwards [hσae, ae_restrict_mem (hMmeas.inter hFmeas)] with x hx hxm
        rw [hx, hgM x hxm.1]
        ring
    _ = ∫ x in Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x Ep ∂μHE[n] := by
        refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hFmeas inter_subset_right
          ?_).symm
        intro x hx
        rw [hg0 x (fun h => hx.2 ⟨h, hx.1⟩), zero_mul]
    _ = ∫ y in Q₁, g (Φ y) * (ω : DifferentialForm (Euclid P) n) (Φ y) Ep :=
        hcov (fun x => g x * (ω : DifferentialForm (Euclid P) n) x Ep)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
