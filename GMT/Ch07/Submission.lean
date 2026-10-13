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

namespace Submission

/-- Fundamental theorem of calculus for a Lipschitz `u` along the line `τ ↦ p + τ v`: if `u` is
differentiable at `p + τ v` for a.e. `τ ∈ [a, b]`, then
`u(p + b v) − u(p + a v) = ∫_a^b Du(p + τ v) v dτ`.  The difference quotients of
`φ(τ) = u(p + τ v)` are bounded by `L ‖v‖`, so dominated convergence takes their integrals to
`∫_a^b Du(p + τ v) v`; the same integrals are boundary averages of `φ`, which tend to
`φ(b) − φ(a)`. -/
theorem dorag_ha_rb_line_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (p v : Euclid n) (a b : ℝ), LipschitzWith L u → (∀ᵐ τ : ℝ, τ ∈ Set.uIcc a b → DifferentiableAt ℝ u (p + τ • v)) → u (p + b • v) - u (p + a • v) = ∫ τ in a..b, fderiv ℝ u (p + τ • v) v := by
  intro n u L p v a b hu hdiff
  -- `φ τ = u (p + τ • v)` is continuous and `L ‖v‖`-Lipschitz
  set φ : ℝ → ℝ := fun τ => u (p + τ • v) with hφ
  have hφcont : Continuous φ :=
    hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hφlip : ∀ s t : ℝ, |φ s - φ t| ≤ L * ‖v‖ * |s - t| := by
    intro s t
    have h := hu.dist_le_mul (p + s • v) (p + t • v)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs] at h
    calc |φ s - φ t| ≤ L * (|s - t| * ‖v‖) := h
      _ = L * ‖v‖ * |s - t| := by ring
  -- chain rule along the line
  have hderiv : ∀ τ : ℝ, DifferentiableAt ℝ u (p + τ • v) →
      HasDerivAt φ (fderiv ℝ u (p + τ • v) v) τ := by
    intro τ hτ
    have hγ : HasDerivAt (fun t : ℝ => p + t • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add p
    exact hτ.hasFDerivAt.comp_hasDerivAt τ hγ
  -- dominated convergence for the difference quotients
  have hlim1 : Tendsto (fun h : ℝ => ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)) (𝓝[>] 0)
      (𝓝 (∫ τ in a..b, fderiv ℝ u (p + τ • v) v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (L : ℝ) * ‖v‖) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards with h
      exact (((hφcont.comp (continuous_id.add continuous_const)).sub hφcont).const_smul
        h⁻¹).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      filter_upwards with τ _
      have hh' : (0 : ℝ) < h := hh
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hh']
      have := hφlip (τ + h) τ
      rw [add_sub_cancel_left, abs_of_pos hh'] at this
      calc h⁻¹ * |φ (τ + h) - φ τ| ≤ h⁻¹ * (L * ‖v‖ * h) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hh'.le)
        _ = L * ‖v‖ := by field_simp
    · filter_upwards [hdiff] with τ hτ hτ'
      exact (hderiv τ (hτ (uIoc_subset_uIcc hτ'))).tendsto_slope_zero_right
  -- the difference quotients integrate to boundary averages
  set F : ℝ → ℝ := fun x => ∫ τ in (0 : ℝ)..x, φ τ with hF
  have hFint : ∀ s t : ℝ, ∫ τ in s..t, φ τ = F t - F s := by
    intro s t
    exact (intervalIntegral.integral_interval_sub_left (hφcont.intervalIntegrable _ _)
      (hφcont.intervalIntegrable _ _)).symm
  have hkey : ∀ h : ℝ, ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)
      = h⁻¹ • (F (b + h) - F b) - h⁻¹ • (F (a + h) - F a) := by
    intro h
    have hi : IntervalIntegrable (fun τ => φ (τ + h)) volume a b :=
      (hφcont.comp (continuous_id.add continuous_const)).intervalIntegrable a b
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_sub hi
      (hφcont.intervalIntegrable a b), intervalIntegral.integral_comp_add_right (fun τ => φ τ) h,
      hFint, hFint]
    simp only [smul_eq_mul]
    ring
  have hFd : ∀ x : ℝ, HasDerivAt F (φ x) x := fun x =>
    (hφcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hlim2 : Tendsto (fun h : ℝ => ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)) (𝓝[>] 0)
      (𝓝 (φ b - φ a)) := by
    simp_rw [hkey]
    exact (hFd b).tendsto_slope_zero_right.sub (hFd a).tendsto_slope_zero_right
  exact tendsto_nhds_unique hlim2 hlim1


/-- FTC along rays through the origin: for an `L`-Lipschitz `u` and a.e. `x`,
`u(x) − u(tx) = ∫_t^1 Du(σx)x dσ` for every `t`.  By Rademacher the differentiability set `D` of
`u` is measurable and conull.  For `σ ≠ 0` the dilation `x ↦ σx` pulls null sets back to null sets
(Haar scaling), so a.e. `x` has `σx ∈ D`; `σ = 0` is a null exception in `ℝ`.  Swapping the two
a.e. quantifiers (`Measure.ae_ae_comm`, `{(σ, x) : σx ∈ D}` being measurable) gives a.e. `x` with
`σx ∈ D` for a.e. `σ`, and for such `x` the line FTC `Submission.dorag_ha_rb_line_ftc` with
`p = 0`, `v = x` applies for every `t`. -/
theorem Submission.dorag_ha_rb_ray_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ x : Euclid n, ∀ t : ℝ, u x - u (t • x) = ∫ σ in t..1, fderiv ℝ u (σ • x) x := by
  intro n u L hu
  -- for `σ ≠ 0`, a.e. `x` has `σ • x` in the (conull) differentiability set
  have hσ : ∀ᵐ σ : ℝ, ∀ᵐ x : Euclid n, DifferentiableAt ℝ u (σ • x) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with σ hσ
    exact (Measure.quasiMeasurePreserving_smul volume hσ).ae hu.ae_differentiableAt
  -- swap the quantifiers: `{(σ, x) | DifferentiableAt ℝ u (σ • x)}` is measurable
  have hx : ∀ᵐ x : Euclid n, ∀ᵐ σ : ℝ, DifferentiableAt ℝ u (σ • x) :=
    (Measure.ae_ae_comm (p := fun (σ : ℝ) (x : Euclid n) => DifferentiableAt ℝ u (σ • x))
      ((continuous_smul (M := ℝ) (X := Euclid n)).measurable
        (measurableSet_of_differentiableAt ℝ u))).1 hσ
  filter_upwards [hx] with x hx t
  have h := Submission.dorag_ha_rb_line_ftc n u L 0 x t 1 hu (by
    filter_upwards [hx] with σ hσ _
    rwa [zero_add])
  simpa only [zero_add, one_smul] using h

/-- Dilation averaging on the boundary annulus `A_s = B₁(0) \ B_{1-s}(0)`: for measurable
`F ≥ 0` integrable on `B₁(0)` and `0 < s ≤ 1/2`,
`∫_{A_s} ∫_{1/2}^1 F(t x) dt dx ≤ 2^(n+1) s ∫_{B₁(0)} F`.  In lower integrals: Tonelli, the
substitution `y = t x` (Jacobian `t⁻ⁿ ≤ 2ⁿ`), Tonelli again, and for each `y` the admissible
`t` lie in `(‖y‖, ‖y‖ / (1 - s)]`, of length `≤ 2 s`, and only when `‖y‖ < 1`. -/
theorem dorag_ha_rb_dilation_average : ∀ (n : ℕ) (F : Euclid n → ℝ) (s : ℝ), Measurable F → (∀ y, 0 ≤ F y) → IntegrableOn F (ball (0 : Euclid n) 1) → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), (∫ t in (1 / 2 : ℝ)..1, F (t • x)) ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y := by
  intro n F s hF hF0 hFi hs hs2
  have hC0 : 0 ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y :=
    mul_nonneg (mul_nonneg (by positivity) hs.le) (integral_nonneg hF0)
  rw [← ENNReal.ofReal_le_ofReal_iff hC0]
  -- `ofReal` of a Bochner integral is at most the lower integral of `ofReal`
  have step1 : ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
      ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
    calc ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
        ≤ ‖∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          (∫ t in (1 / 2 : ℝ)..1, F (t • x))‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ‖∫ t in (1 / 2 : ℝ)..1, F (t • x)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
          refine lintegral_mono fun x => ?_
          rw [intervalIntegral.integral_of_le (by norm_num)]
          calc ‖∫ t in Ioc (1 / 2 : ℝ) 1, F (t • x)‖ₑ
              ≤ ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ‖F (t • x)‖ₑ := enorm_integral_le_lintegral_enorm _
            _ = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
              congr 1; ext t; exact Real.enorm_eq_ofReal (hF0 _)
  -- Tonelli
  have hmeas : Measurable (fun p : Euclid n × ℝ => ENNReal.ofReal (F (p.2 • p.1))) :=
    (hF.comp (measurable_snd.smul measurable_fst)).ennreal_ofReal
  have step2 : ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x))
      = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x)) :=
    lintegral_lintegral_swap hmeas.aemeasurable
  -- the region `{(t, y) : t (1 - s) ≤ ‖y‖ < t}` and the integrand on it
  obtain ⟨T, hT⟩ : ∃ T : Set (ℝ × Euclid n), T = {p | p.1 * (1 - s) ≤ ‖p.2‖ ∧ ‖p.2‖ < p.1} :=
    ⟨_, rfl⟩
  have hTm : MeasurableSet T := hT ▸
    (measurableSet_le (measurable_fst.mul_const _) measurable_snd.norm).inter
      (measurableSet_lt measurable_snd.norm measurable_fst)
  obtain ⟨H, hH⟩ : ∃ H : ℝ × Euclid n → ℝ≥0∞, H = T.indicator (fun p => ENNReal.ofReal (F p.2)) :=
    ⟨_, rfl⟩
  have hHm : Measurable H := hH ▸ (hF.comp measurable_snd).ennreal_ofReal.indicator hTm
  -- change of variables `y = t x`
  have step3 : ∀ t ∈ Ioc (1 / 2 : ℝ) 1,
      ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), ENNReal.ofReal (F (t • x))
        ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht.1
    have hmem : ∀ x : Euclid n,
        x ∈ ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s) ↔ (t, t • x) ∈ T := by
      intro x
      rw [hT]
      simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨mul_le_mul_of_nonneg_left h2 ht0.le, mul_lt_of_lt_one_right ht0 h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_mul_lt_mul_left (by linarith) ht0.le, le_of_mul_le_mul_left h1 ht0⟩
    have hind : (ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s)).indicator
        (fun x => ENNReal.ofReal (F (t • x))) = fun x => H (t, t • x) := by
      ext x
      rw [hH]
      by_cases hx : x ∈ ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s)
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hHt : Measurable fun y : Euclid n => H (t, y) := hHm.comp measurable_prodMk_left
    have hjac : ENNReal.ofReal |(t ^ Module.finrank ℝ (Euclid n))⁻¹| ≤ ENNReal.ofReal (2 ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity), ← inv_pow]
      have : t⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
      exact pow_le_pow_left₀ (by positivity) this n
    calc ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), ENNReal.ofReal (F (t • x))
        = ∫⁻ x, H (t, t • x) := by
          rw [← lintegral_indicator (measurableSet_ball.diff measurableSet_ball), hind]
      _ = ∫⁻ y, H (t, y) ∂(Measure.map (t • ·) volume) :=
          (lintegral_map hHt (measurable_const_smul t)).symm
      _ = ENNReal.ofReal |(t ^ Module.finrank ℝ (Euclid n))⁻¹| * ∫⁻ y, H (t, y) := by
          rw [Measure.map_addHaar_smul volume ht0.ne', lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) := by gcongr
  have step4 : ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x))
      ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := by
    calc ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ENNReal.ofReal (F (t • x))
        ≤ ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) :=
          setLIntegral_mono' measurableSet_Ioc step3
      _ = ENNReal.ofReal (2 ^ n) * ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ y, H (t, y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := by
          rw [lintegral_lintegral_swap (f := fun t y => H (t, y)) hHm.aemeasurable]
  -- length of the admissible parameter interval
  have step5 : ∀ y : Euclid n, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
      ≤ (ball (0 : Euclid n) 1).indicator
          (fun y => ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y)) y := by
    intro y
    have hSm : MeasurableSet {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} :=
      (measurableSet_le (measurable_id.mul_const _) measurable_const).inter
        (measurableSet_lt measurable_const measurable_id)
    have hHy : (fun t => H (t, y)) = {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t}.indicator
        (fun _ => ENNReal.ofReal (F y)) := by
      ext t
      rw [hH, hT]
      simp only [indicator, mem_ofPred_eq]
    rw [hHy, lintegral_indicator_const hSm, Measure.restrict_apply hSm]
    by_cases hy : ‖y‖ < 1
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), mul_comm]
      gcongr
      have h1s : 0 < 1 - s := by linarith
      calc volume ({t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} ∩ Ioc (1 / 2 : ℝ) 1)
          ≤ volume (Ioc ‖y‖ (‖y‖ / (1 - s))) := by
            apply measure_mono
            rintro t ⟨⟨h1, h2⟩, -⟩
            exact ⟨h2, (le_div_iff₀ h1s).2 h1⟩
        _ = ENNReal.ofReal (‖y‖ / (1 - s) - ‖y‖) := Real.volume_Ioc
        _ ≤ ENNReal.ofReal (2 * s) := by
            apply ENNReal.ofReal_le_ofReal
            rw [sub_le_iff_le_add, div_le_iff₀ h1s]
            nlinarith [mul_pos hs (show 0 < 2 - 2 * s - ‖y‖ by linarith)]
    · rw [indicator_of_notMem (by simpa using hy)]
      have hempty : {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} ∩ Ioc (1 / 2 : ℝ) 1 = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, h2⟩, -, h4⟩
        exact hy (h2.trans_le h4)
      rw [hempty, measure_empty, mul_zero]
  have step6 : ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
      ≤ ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y) := by
    calc ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
        ≤ ∫⁻ y, (ball (0 : Euclid n) 1).indicator
          (fun y => ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y)) y := lintegral_mono step5
      _ = ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y) :=
          lintegral_indicator measurableSet_ball _
      _ = ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hBeq : ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y)
      = ENNReal.ofReal (∫ y in ball (0 : Euclid n) 1, F y) :=
    (ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF0)).symm
  calc ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
      ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := step1
    _ = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x)) := step2
    _ ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := step4
    _ ≤ ENNReal.ofReal (2 ^ n) *
        (ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y)) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y) := by
        rw [hBeq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Submission

/-- Step 3 (boundary layer) of the Rellich compactness argument on the unit ball, used for the
harmonic approximation in Allard's theorem (Simon 7.4.3): for `L`-Lipschitz `u : ℝⁿ → ℝ` and
`0 < s ≤ 1/2`, the annulus `A_s = B₁ \ B_{1-s}` satisfies
`∫_{A_s} u² ≤ 2^{n+3} s (∫_{B₁} u² + ∫_{B₁} ‖Du‖²)`.  Along a.e. ray
`u(x) - u(tx) = ∫_t^1 Du(σx)x dσ` (`Submission.dorag_ha_rb_ray_ftc`), so Cauchy–Schwarz on
`[1/2, 1]` gives `u(x)² ≤ 4 ∫_{1/2}^1 u(tx)² dt + ∫_{1/2}^1 ‖Du(tx)‖² dt` for `x ∈ B₁`;
integrate over `A_s` and average over dilations (`Submission.dorag_ha_rb_dilation_average`). -/
theorem Submission.dorag_ha_rb_boundary_layer : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (s : ℝ), LipschitzWith L u → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), u x ^ 2 ≤ 2 ^ (n + 3) * s * ((∫ x in ball (0 : Euclid n) 1, u x ^ 2) + ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) := by
  intro n u L s hu hs hs2
  set B : Set (Euclid n) := ball (0 : Euclid n) 1
  set A : Set (Euclid n) := B \ ball (0 : Euclid n) (1 - s)
  have hBm : MeasurableSet B := measurableSet_ball
  have hAm : MeasurableSet A := hBm.diff measurableSet_ball
  have hBfin : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hcont : Continuous u := hu.continuous
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- `‖Du‖ ≤ L` everywhere and `|u| ≤ |u 0| + L` on the closed unit ball
  have hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ L := fun y => norm_fderiv_le_of_lipschitz ℝ hu
  have hu_bd : ∀ y : Euclid n, ‖y‖ ≤ 1 → |u y| ≤ |u 0| + L := by
    intro y hy
    have h1 : dist (u y) (u 0) ≤ L * dist y 0 := hu.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at h1
    have h2 : (L : ℝ) * ‖y‖ ≤ L := mul_le_of_le_one_right L.coe_nonneg hy
    have h3 := abs_sub_abs_le_abs_sub (u y) (u 0)
    linarith
  have hsq_bd : ∀ y : Euclid n, ‖y‖ ≤ 1 → ‖u y ^ 2‖ ≤ (|u 0| + L) ^ 2 := fun y hy => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu_bd y hy) 2
  have hDsq_bd : ∀ y : Euclid n, ‖‖fderiv ℝ u y‖ ^ 2‖ ≤ (L : ℝ) ^ 2 := fun y => by
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDu y) 2
  -- a bounded measurable function is interval integrable
  have hii : ∀ (f : ℝ → ℝ) (C : ℝ) (a b : ℝ), Measurable f → (∀ σ, ‖f σ‖ ≤ C) →
      IntervalIntegrable f volume a b := fun f C a b hf hC =>
    (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
      (Eventually.of_forall hC)
  -- `u²` and `‖Du‖²` are measurable, nonnegative and integrable on `B`
  have hmF₁ : Measurable fun y => u y ^ 2 := (hcont.pow 2).measurable
  have hmF₂ : Measurable fun y => ‖fderiv ℝ u y‖ ^ 2 := by fun_prop
  have hiF₁ : IntegrableOn (fun y => u y ^ 2) B := by
    refine Measure.integrableOn_of_bounded (M := (|u 0| + L) ^ 2) hBfin
      hmF₁.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hBm] with y hy
    exact hsq_bd y (mem_ball_zero_iff.mp hy).le
  have hiF₂ : IntegrableOn (fun y => ‖fderiv ℝ u y‖ ^ 2) B :=
    Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2) hBfin hmF₂.aestronglyMeasurable
      (Eventually.of_forall hDsq_bd)
  -- the dilation averages `I₁(x) = ∫_{1/2}^1 u(tx)² dt` and `J(x) = ∫_{1/2}^1 ‖Du(tx)‖² dt`
  set I₁ : Euclid n → ℝ := fun x => ∫ t in (1 / 2 : ℝ)..1, u (t • x) ^ 2
  set J : Euclid n → ℝ := fun x => ∫ t in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (t • x)‖ ^ 2
  -- the pointwise estimate on a ray along which the fundamental theorem of calculus holds
  have key : ∀ x : Euclid n, ‖x‖ ≤ 1 →
      (∀ t : ℝ, u x - u (t • x) = ∫ σ in t..1, fderiv ℝ u (σ • x) x) →
      u x ^ 2 ≤ 4 * I₁ x + J x := by
    intro x hx hray
    have hgm : Measurable fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖ := by fun_prop
    have hgi : ∀ a b : ℝ, IntervalIntegrable (fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖) volume a b :=
      fun a b => hii _ L a b hgm fun σ => by rw [norm_norm]; exact hDu _
    have hg2i : IntervalIntegrable (fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖ ^ 2) volume (1 / 2) 1 :=
      hii _ ((L : ℝ) ^ 2) _ _ (hgm.pow_const 2) fun σ => hDsq_bd _
    set γ : ℝ := ∫ σ in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (σ • x)‖ with hγ
    -- (a) `|u(x) - u(tx)| ≤ ∫_t^1 ‖Du(σx)‖ dσ ≤ γ` for `t ∈ [1/2, 1]`
    have ha : ∀ t ∈ Icc (1 / 2 : ℝ) 1, |u x - u (t • x)| ≤ γ := by
      intro t ht
      rw [hray t, ← Real.norm_eq_abs]
      calc ‖∫ σ in t..1, fderiv ℝ u (σ • x) x‖
          ≤ ∫ σ in t..1, ‖fderiv ℝ u (σ • x)‖ :=
            intervalIntegral.norm_integral_le_of_norm_le ht.2
              (Eventually.of_forall fun σ _ => ((fderiv ℝ u (σ • x)).le_opNorm x).trans
                (mul_le_of_le_one_right (norm_nonneg _) hx)) (hgi t 1)
        _ ≤ γ := intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
              (Eventually.of_forall fun σ => norm_nonneg _) (hgi _ _)
    -- (b) `u(x)² ≤ 2u(tx)² + 2γ²`
    have hb : ∀ t ∈ Icc (1 / 2 : ℝ) 1, u x ^ 2 ≤ 2 * u (t • x) ^ 2 + 2 * γ ^ 2 := by
      intro t ht
      have h1 := abs_le.mp (ha t ht)
      have h2 : (u x - u (t • x)) ^ 2 ≤ γ ^ 2 := sq_le_sq' h1.1 h1.2
      linarith [sq_nonneg (2 * u (t • x) - u x)]
    -- (c) Cauchy–Schwarz on `[1/2, 1]`: integrating `4γ‖Du(σx)‖ ≤ ‖Du(σx)‖² + 4γ²` gives
    -- `4γ² ≤ J(x) + 2γ²`
    have hc : 2 * γ ^ 2 ≤ J x := by
      have h1 : ∫ σ in (1 / 2 : ℝ)..1, 4 * γ * ‖fderiv ℝ u (σ • x)‖ ≤
          ∫ σ in (1 / 2 : ℝ)..1, (‖fderiv ℝ u (σ • x)‖ ^ 2 + 4 * γ ^ 2) :=
        intervalIntegral.integral_mono_on hhalf ((hgi _ _).const_mul _)
          (hg2i.add intervalIntegrable_const)
          fun σ _ => by linarith [sq_nonneg (‖fderiv ℝ u (σ • x)‖ - 2 * γ)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hg2i
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, ← hγ] at h1
      have hJx : J x = ∫ σ in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (σ • x)‖ ^ 2 := rfl
      linarith
    -- (d) averaging (b) over `t ∈ [1/2, 1]` gives `u(x)² ≤ 4I₁(x) + 2γ²`
    have hd : (1 - 1 / 2 : ℝ) * u x ^ 2 ≤ 2 * I₁ x + (1 - 1 / 2) * (2 * γ ^ 2) := by
      have hcu : Continuous fun t : ℝ => u (t • x) ^ 2 := by fun_prop
      have h1 : ∫ t in (1 / 2 : ℝ)..1, u x ^ 2 ≤
          ∫ t in (1 / 2 : ℝ)..1, (2 * u (t • x) ^ 2 + 2 * γ ^ 2) :=
        intervalIntegral.integral_mono_on hhalf intervalIntegrable_const
          (((hcu.intervalIntegrable _ _).const_mul 2).add intervalIntegrable_const) hb
      rw [intervalIntegral.integral_const, intervalIntegral.integral_add
        ((hcu.intervalIntegrable _ _).const_mul 2) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
        smul_eq_mul] at h1
      have hI₁x : I₁ x = ∫ t in (1 / 2 : ℝ)..1, u (t • x) ^ 2 := rfl
      linarith
    linarith
  -- `I₁` and `J` are strongly measurable (Fubini) and bounded on `B`, hence integrable on `A`
  have hI₁m : StronglyMeasurable I₁ := by
    have h : Measurable fun p : Euclid n × ℝ => u (p.2 • p.1) ^ 2 := by fun_prop
    convert h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (1 / 2 : ℝ) 1))
      using 1
    funext x
    exact intervalIntegral.integral_of_le hhalf
  have hJm : StronglyMeasurable J := by
    have h : Measurable fun p : Euclid n × ℝ => ‖fderiv ℝ u (p.2 • p.1)‖ ^ 2 := by fun_prop
    convert h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (1 / 2 : ℝ) 1))
      using 1
    funext x
    exact intervalIntegral.integral_of_le hhalf
  have hI₁A : IntegrableOn I₁ A := by
    refine (Measure.integrableOn_of_bounded (M := (|u 0| + L) ^ 2 * |1 - 1 / 2|) hBfin
      hI₁m.aestronglyMeasurable ?_).mono_set sdiff_subset
    filter_upwards [ae_restrict_mem hBm] with x hx
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hsq_bd _ ?_
    rw [uIoc_of_le hhalf] at ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    nlinarith [ht.2, norm_nonneg x]
  have hJA : IntegrableOn J A :=
    (Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2 * |1 - 1 / 2|) hBfin
      hJm.aestronglyMeasurable (Eventually.of_forall fun x =>
        intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hDsq_bd _)).mono_set
      sdiff_subset
  -- integrate the pointwise estimate over `A`
  have hae : ∀ᵐ x ∂(volume.restrict A), u x ^ 2 ≤ 4 * I₁ x + J x := by
    filter_upwards [ae_restrict_mem hAm,
      ae_restrict_of_ae (Submission.dorag_ha_rb_ray_ftc n u L hu)] with x hxA hray
    exact key x (mem_ball_zero_iff.mp hxA.1).le hray
  have hmain : ∫ x in A, u x ^ 2 ≤ ∫ x in A, (4 * I₁ x + J x) :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg (u x))
      ((hI₁A.const_mul 4).add hJA) hae
  rw [integral_add (hI₁A.const_mul 4) hJA, integral_const_mul] at hmain
  -- average over dilations, then `4 · 2^{n+1} = 2^{n+3}`
  have hdil₁ : ∫ x in A, I₁ x ≤ 2 ^ (n + 1) * s * ∫ y in B, u y ^ 2 :=
    Submission.dorag_ha_rb_dilation_average n (fun y => u y ^ 2) s hmF₁ (fun y => sq_nonneg _)
      hiF₁ hs hs2
  have hdil₂ : ∫ x in A, J x ≤ 2 ^ (n + 1) * s * ∫ y in B, ‖fderiv ℝ u y‖ ^ 2 :=
    Submission.dorag_ha_rb_dilation_average n (fun y => ‖fderiv ℝ u y‖ ^ 2) s hmF₂
      (fun y => sq_nonneg _) hiF₂ hs hs2
  have hJB : 0 ≤ 2 ^ (n + 1) * s * ∫ y in B, ‖fderiv ℝ u y‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hs.le) (setIntegral_nonneg hBm fun y _ => sq_nonneg _)
  have h2 : (2 : ℝ) ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
  rw [h2]
  linarith
/-- **FTC along translates of a Lipschitz function, for a.e. base point.**  If `u : ℝⁿ → ℝ` is
`L`-Lipschitz and `z ∈ ℝⁿ`, then `u(p + z) − u(p) = ∫₀¹ Du(p + τz)z dτ` for a.e. `p ∈ ℝⁿ`.  By
Rademacher's theorem the measurable set `D` of differentiability points of `u` is conull, so by
translation invariance `p + τz ∈ D` for a.e. `p`, for every `τ`.  Fubini for the null set of the
measurable set `{(p, τ) : p + τz ∈ D}` then gives, for a.e. `p`, `p + τz ∈ D` for a.e. `τ`: the
hypothesis of the line FTC `Submission.dorag_ha_rb_line_ftc` with `v = z`, `a = 0`, `b = 1`. -/
theorem Submission.dorag_ha_rb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (z : Euclid n), LipschitzWith L u → ∀ᵐ p : Euclid n, u (p + z) - u p = ∫ τ in (0 : ℝ)..1, fderiv ℝ u (p + τ • z) z := by
  intro n u L z hu
  -- step 1: the set `D` of differentiability points of `u` is measurable and conull (Rademacher)
  have hD : MeasurableSet {y : Euclid n | DifferentiableAt ℝ u y} :=
    measurableSet_of_differentiableAt ℝ u
  have hae : ∀ᵐ y : Euclid n, DifferentiableAt ℝ u y := hu.ae_differentiableAt
  -- step 2: for every `τ`, `p ↦ p + τz` preserves Lebesgue measure, so `p + τz ∈ D` for a.e. `p`
  have hτ : ∀ τ : ℝ, ∀ᵐ p : Euclid n, DifferentiableAt ℝ u (p + τ • z) := fun τ =>
    (measurePreserving_add_right volume (τ • z)).quasiMeasurePreserving.ae hae
  -- step 3: `{(p, τ) : p + τz ∈ D}` is measurable, so Fubini lets us swap the a.e. quantifiers
  have hmeas : MeasurableSet {q : Euclid n × ℝ | DifferentiableAt ℝ u (q.1 + q.2 • z)} :=
    hD.preimage (measurable_fst.add (measurable_snd.smul_const z))
  have hp : ∀ᵐ p : Euclid n, ∀ᵐ τ : ℝ, DifferentiableAt ℝ u (p + τ • z) :=
    (Measure.ae_ae_comm (p := fun p τ => DifferentiableAt ℝ u (p + τ • z)) hmeas).2
      (Eventually.of_forall hτ)
  -- step 4: the line FTC with `v = z`, `a = 0`, `b = 1`, and `1 • z = z`, `p + 0 • z = p`
  filter_upwards [hp] with p hp
  have h := Submission.dorag_ha_rb_line_ftc n u L p z 0 1 hu (hp.mono fun τ hτ _ => hτ)
  rwa [one_smul, zero_smul, add_zero] at h

/-- **`L²` translation estimate** (cf. Gilbarg–Trudinger, Lemma 7.23; Evans, §5.8.2, Theorem 3),
for Rellich's theorem in the proof of the harmonic approximation lemma (Simon Ch. 5, 3.1, p. 114:
"by Rellich's theorem (see [GT01])").  If `u` is Lipschitz on `ℝⁿ` and `r + ‖w‖ ≤ R`, then
`∫_{B_r} (u(x) − u(x − w))² ≤ ‖w‖² ∫_{B_R} ‖Du‖²`: for a.e. `x`,
`u(x) − u(x − w) = ∫₀¹ Du(x − w + τw)w dτ`; Cauchy–Schwarz on `(0, 1]` bounds its square by
`‖w‖² ∫₀¹ ‖Du(x − w + τw)‖² dτ`; for `x ∈ B_r` the segment lies in `B_R`; integrating over `B_r`,
Fubini and translation invariance of Lebesgue measure give the bound. -/
theorem Submission.dorag_ha_rb_translation_l2 : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (w : Euclid n) (r R : ℝ), LipschitzWith L u → r + ‖w‖ ≤ R → ∫ x in ball (0 : Euclid n) r, (u x - u (x - w)) ^ 2 ≤ ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n u L w r R hu hrR
  -- Step 1: `G_R = 1_{B_R} ‖Du‖²`: measurable, `0 ≤ G_R ≤ L²`, integrable, `∫ G_R = ∫_{B_R} ‖Du‖²`
  obtain ⟨GR, hGR⟩ : ∃ GR : Euclid n → ℝ,
      GR = (ball (0 : Euclid n) R).indicator fun y => ‖fderiv ℝ u y‖ ^ 2 := ⟨_, rfl⟩
  have hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ L := fun y => norm_fderiv_le_of_lipschitz ℝ hu
  have hG_meas : Measurable fun y => ‖fderiv ℝ u y‖ ^ 2 := (measurable_fderiv ℝ u).norm.pow_const 2
  have hG_le : ∀ y, ‖fderiv ℝ u y‖ ^ 2 ≤ (L : ℝ) ^ 2 := fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (hDu y) 2
  have hGR_meas : Measurable GR := by
    rw [hGR]; exact hG_meas.indicator measurableSet_ball
  have hGR_nonneg : ∀ y, 0 ≤ GR y := fun y => by
    rw [hGR]; exact indicator_nonneg (fun y _ => sq_nonneg _) y
  have hGR_le : ∀ y, GR y ≤ (L : ℝ) ^ 2 := fun y => by
    by_cases hy : y ∈ ball (0 : Euclid n) R
    · rw [hGR, indicator_of_mem hy]; exact hG_le y
    · rw [hGR, indicator_of_notMem hy]; positivity
  have hGR_int : Integrable GR := by
    rw [hGR, integrable_indicator_iff measurableSet_ball]
    refine IntegrableOn.of_bound measure_ball_lt_top hG_meas.aestronglyMeasurable ((L : ℝ) ^ 2)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hG_le y
  have hGR_eq : ∫ y, GR y = ∫ y in ball (0 : Euclid n) R, ‖fderiv ℝ u y‖ ^ 2 := by
    rw [hGR]; exact integral_indicator measurableSet_ball
  -- Step 2: the segment FTC transported by `x ↦ x − w`: for a.e. `x`,
  -- `u x − u (x − w) = ∫_{(0, 1]} Du(x − w + τw)w dτ`
  have hftc : ∀ᵐ x : Euclid n, u x - u (x - w) =
      ∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w := by
    filter_upwards [(measurePreserving_sub_right volume w).quasiMeasurePreserving.ae
      (Submission.dorag_ha_rb_segment_ftc n u L w hu)] with x hx
    have hx' : u (x - w + w) - u (x - w) = ∫ τ in (0 : ℝ)..1, fderiv ℝ u (x - w + τ • w) w := hx
    rwa [sub_add_cancel, intervalIntegral.integral_of_le zero_le_one] at hx'
  -- Step 3: Cauchy–Schwarz on `(0, 1]`, via `0 ≤ ∫ (h − c)² = ∫ h² − c²` for `c = ∫ h`
  have hvol : volume.real (Ioc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  have hCS : ∀ h : ℝ → ℝ, IntegrableOn h (Ioc (0 : ℝ) 1) →
      IntegrableOn (fun τ => h τ ^ 2) (Ioc (0 : ℝ) 1) →
      (∫ τ in Ioc (0 : ℝ) 1, h τ) ^ 2 ≤ ∫ τ in Ioc (0 : ℝ) 1, h τ ^ 2 := by
    intro h hi hi2
    set c := ∫ τ in Ioc (0 : ℝ) 1, h τ with hc
    have i1 : Integrable (fun τ => 2 * c * h τ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      Integrable.const_mul hi _
    have i2 : Integrable (fun τ => h τ ^ 2 - 2 * c * h τ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      Integrable.sub hi2 i1
    have hexp : ∫ τ in Ioc (0 : ℝ) 1, (h τ - c) ^ 2 = (∫ τ in Ioc (0 : ℝ) 1, h τ ^ 2) - c ^ 2 := by
      have e : (fun τ => (h τ - c) ^ 2) = fun τ => (h τ ^ 2 - 2 * c * h τ) + c ^ 2 := by
        funext τ; ring
      rw [e, integral_add i2 (integrable_const _), integral_sub hi2 i1, integral_const_mul,
        setIntegral_const, hvol, one_smul, ← hc]
      ring
    have h0 : 0 ≤ ∫ τ in Ioc (0 : ℝ) 1, (h τ - c) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc fun τ _ => sq_nonneg _
    linarith
  -- pointwise bounds `|Du(y)w| ≤ ‖Du(y)‖‖w‖` and `(Du(y)w)² ≤ ‖w‖² ‖Du(y)‖²`
  have hDuw : ∀ y, |fderiv ℝ u y w| ≤ ‖fderiv ℝ u y‖ * ‖w‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact (fderiv ℝ u y).le_opNorm w
  have hsq : ∀ y, fderiv ℝ u y w ^ 2 ≤ ‖w‖ ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := fun y => by
    calc fderiv ℝ u y w ^ 2 = |fderiv ℝ u y w| ^ 2 := (sq_abs _).symm
      _ ≤ (‖fderiv ℝ u y‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hDuw y) 2
      _ = ‖w‖ ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := by ring
  -- Step 4: for `x ∈ B_r` and `τ ∈ (0, 1]`, `x − w + τw = x − (1 − τ)w ∈ B_R`
  have hseg : ∀ x ∈ ball (0 : Euclid n) r, ∀ τ ∈ Ioc (0 : ℝ) 1,
      x - w + τ • w ∈ ball (0 : Euclid n) R := by
    intro x hx τ hτ
    rw [mem_ball_zero_iff] at hx ⊢
    have e : x - w + τ • w = x - (1 - τ) • w := by rw [sub_smul, one_smul]; abel
    have h1 : (1 - τ) * ‖w‖ ≤ ‖w‖ :=
      mul_le_of_le_one_left (norm_nonneg w) (by linarith [hτ.1])
    rw [e]
    calc ‖x - (1 - τ) • w‖ ≤ ‖x‖ + ‖(1 - τ) • w‖ := norm_sub_le _ _
      _ = ‖x‖ + (1 - τ) * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hτ.2)]
      _ < r + ‖w‖ := by linarith
      _ ≤ R := hrR
  -- the integrand `F(x, τ) = G_R(x − w + τw)` on `B_r × (0, 1]`
  have hF_meas : Measurable fun p : Euclid n × ℝ => GR (p.1 - w + p.2 • w) :=
    hGR_meas.comp ((measurable_fst.sub_const w).add (measurable_snd.smul_const w))
  have hint01 : ∀ x : Euclid n, IntegrableOn (fun τ : ℝ => GR (x - w + τ • w)) (Ioc (0 : ℝ) 1) :=
    fun x => IntegrableOn.of_bound measure_Ioc_lt_top
      (hGR_meas.comp ((measurable_id.smul_const w).const_add (x - w))).aestronglyMeasurable
      ((L : ℝ) ^ 2) (ae_of_all _ fun τ => by
        rw [Real.norm_of_nonneg (hGR_nonneg _)]; exact hGR_le _)
  -- Steps 3 and 4: for a.e. `x ∈ B_r`, `(u x − u (x − w))² ≤ ‖w‖² ∫_{(0, 1]} F(x, τ) dτ`
  have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) r)), (u x - u (x - w)) ^ 2 ≤
      ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hftc] with x hx hxr
    have hm : Measurable fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w :=
      (measurable_fderiv_apply_const ℝ u w).comp ((measurable_id.smul_const w).const_add (x - w))
    have hi : IntegrableOn (fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w) (Ioc (0 : ℝ) 1) :=
      IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable ((L : ℝ) * ‖w‖)
        (ae_of_all _ fun τ => (Real.norm_eq_abs _).le.trans ((hDuw _).trans
          (mul_le_mul_of_nonneg_right (hDu _) (norm_nonneg w))))
    have hi2 : IntegrableOn (fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w ^ 2) (Ioc (0 : ℝ) 1) :=
      IntegrableOn.of_bound measure_Ioc_lt_top (hm.pow_const 2).aestronglyMeasurable
        (‖w‖ ^ 2 * (L : ℝ) ^ 2) (ae_of_all _ fun τ => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact (hsq _).trans (mul_le_mul_of_nonneg_left (hG_le _) (sq_nonneg _)))
    rw [hx]
    calc (∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w) ^ 2
        ≤ ∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w ^ 2 := hCS _ hi hi2
      _ ≤ ∫ τ in Ioc (0 : ℝ) 1, ‖w‖ ^ 2 * GR (x - w + τ • w) := by
          refine setIntegral_mono_on hi2 (Integrable.const_mul (hint01 x) _) measurableSet_Ioc
            fun τ hτ => ?_
          rw [hGR, indicator_of_mem (hseg x hxr τ hτ)]
          exact hsq _
      _ = ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) := integral_const_mul _ _
  -- Step 5: `F` is bounded on the finite measure space `B_r × (0, 1]`, hence integrable
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hF_int : Integrable (fun p : Euclid n × ℝ => GR (p.1 - w + p.2 • w))
      ((volume.restrict (ball (0 : Euclid n) r)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable ((L : ℝ) ^ 2)
      (ae_of_all _ fun p => by rw [Real.norm_of_nonneg (hGR_nonneg _)]; exact hGR_le _)
  have hΦ_int : Integrable (fun x => ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w))
      (volume.restrict (ball (0 : Euclid n) r)) := hF_int.integral_prod_left
  -- Step 6: Fubini and translation invariance: `∫_{B_r} ∫_{(0, 1]} F ≤ ∫ G_R`
  have hΦ_le : ∫ x in ball (0 : Euclid n) r, ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) ≤
      ∫ y, GR y := by
    rw [integral_integral_swap (f := fun x τ => GR (x - w + τ • w)) hF_int]
    calc ∫ τ in Ioc (0 : ℝ) 1, ∫ x in ball (0 : Euclid n) r, GR (x - w + τ • w)
        ≤ ∫ τ in Ioc (0 : ℝ) 1, ∫ y, GR y := by
          refine integral_mono_of_nonneg
            (ae_of_all _ fun τ => integral_nonneg fun x => hGR_nonneg _) (integrable_const _)
            (ae_of_all _ fun τ => ?_)
          have e : (fun x => GR (x - w + τ • w)) = fun x => GR (x + (τ • w - w)) := by
            funext x; congr 1; abel
          calc ∫ x in ball (0 : Euclid n) r, GR (x - w + τ • w) ≤ ∫ x, GR (x - w + τ • w) :=
                setIntegral_le_integral (by rw [e]; exact hGR_int.comp_add_right _)
                  (ae_of_all _ fun x => hGR_nonneg _)
            _ = ∫ y, GR y := by rw [e, integral_add_right_eq_self]
      _ = ∫ y, GR y := by rw [setIntegral_const, hvol, one_smul]
  -- Step 7: combine
  calc ∫ x in ball (0 : Euclid n) r, (u x - u (x - w)) ^ 2
      ≤ ∫ x in ball (0 : Euclid n) r, ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hΦ_int.const_mul _) hpt
    _ = ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) r, ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) :=
        integral_const_mul _ _
    _ ≤ ‖w‖ ^ 2 * ∫ y, GR y := mul_le_mul_of_nonneg_left hΦ_le (sq_nonneg _)
    _ = ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ u x‖ ^ 2 := by rw [hGR_eq]

/-- **Interior `L²` error of a mollification** (step (2a) of the Rellich ball argument): if
`u : ℝⁿ → ℝ` is Lipschitz, `ρ ≥ 0` is continuous, vanishes where `‖z‖ ≥ 1` and has `∫ ρ = 1`,
and `0 < ε ≤ s`, then `v(x) = ∫ u(x − εz) ρ(z) dz` satisfies
`∫_{B_{1−s}} (u − v)² ≤ ε² ∫_{B_1} ‖Du‖²`.  Weighted Jensen gives
`(u(x) − v(x))² ≤ ∫ (u(x) − u(x − εz))² ρ(z) dz`; the integrand is dominated by `(Lε‖z‖)² ρ(z)`,
so Fubini swaps the integrals, and `Submission.dorag_ha_rb_translation_l2` (`r = 1 − s`, `R = 1`,
`w = εz`, `‖εz‖ ≤ ε ≤ s` where `ρ(z) ≠ 0`) bounds each inner integral by `ε² ∫_{B_1} ‖Du‖²`. -/
theorem Submission.dorag_ha_rb_mollify_l2 : ∀ (n : ℕ) (u ρ : Euclid n → ℝ) (L : NNReal) (ε s : ℝ), LipschitzWith L u → Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → 0 < ε → ε ≤ s → ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n u ρ L ε s hu hρc hρ0 hρ1 hρint hε hεs
  have huc : Continuous u := hu.continuous
  -- step 1: `ρ` vanishes off `closedBall 0 1`, so `g ρ` is integrable for every continuous `g`
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz =>
      hρ1 z (not_le.mp (by simpa using hz)).le
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  have hgρ : ∀ g : Euclid n → ℝ, Continuous g → Integrable fun z => g z * ρ z := fun g hg =>
    (hg.mul hρc).integrable_of_hasCompactSupport (hρcs.mul_left (f := g))
  -- step 2: `u(x) − v(x) = ∫ (u(x) − u(x − εz)) ρ(z) dz`, as `∫ ρ = 1`
  have hrep : ∀ x, u x - ∫ z, u (x - ε • z) * ρ z = ∫ z, (u x - u (x - ε • z)) * ρ z := by
    intro x
    simp_rw [sub_mul]
    rw [integral_sub (hρi.const_mul (u x)) (hgρ (fun z => u (x - ε • z)) (by fun_prop)),
      integral_const_mul, hρint, mul_one]
  -- step 3: weighted Jensen, `(∫ g ρ)² ≤ ∫ g² ρ`, from `0 ≤ ∫ (g − c)² ρ = ∫ g² ρ − c²`
  have hjensen : ∀ g : Euclid n → ℝ, Continuous g →
      (∫ z, g z * ρ z) ^ 2 ≤ ∫ z, g z ^ 2 * ρ z := by
    intro g hg
    obtain ⟨c, hc⟩ : ∃ c, ∫ z, g z * ρ z = c := ⟨_, rfl⟩
    have h0 : 0 ≤ ∫ z, (g z - c) ^ 2 * ρ z :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hρ0 z)
    have e : (fun z => (g z - c) ^ 2 * ρ z) =
        fun z => g z ^ 2 * ρ z - 2 * c * (g z * ρ z) + c ^ 2 * ρ z := by
      funext z
      ring
    have i1 : Integrable fun z => g z ^ 2 * ρ z := hgρ (fun z => g z ^ 2) (hg.pow 2)
    have i2 : Integrable fun z => 2 * c * (g z * ρ z) := (hgρ g hg).const_mul (2 * c)
    have i3 : Integrable fun z => g z ^ 2 * ρ z - 2 * c * (g z * ρ z) := i1.sub i2
    rw [e, integral_add i3 (hρi.const_mul (c ^ 2)), integral_sub i1 i2, integral_const_mul,
      integral_const_mul, hc, hρint] at h0
    rw [hc]
    nlinarith
  -- step 4: `|u(x) − u(x − εz)| ≤ Lε‖z‖`, so the integrand is dominated by `(Lε‖z‖)² ρ(z)`,
  -- which is integrable on `B_{1−s} × ℝⁿ`
  have hlip : ∀ x z : Euclid n, |u x - u (x - ε • z)| ≤ L * (ε * ‖z‖) := by
    intro x z
    have h := hu.dist_le_mul x (x - ε • z)
    rwa [Real.dist_eq, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg hε.le] at h
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) (1 - s))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (uncurry fun x z => (u x - u (x - ε • z)) ^ 2 * ρ z)
      ((volume.restrict (ball (0 : Euclid n) (1 - s))).prod volume) := by
    refine ((hgρ (fun z => (L * (ε * ‖z‖)) ^ 2) (by fun_prop)).comp_snd
      (volume.restrict (ball (0 : Euclid n) (1 - s)))).mono'
      (show Continuous fun p : Euclid n × Euclid n => (u p.1 - u (p.1 - ε • p.2)) ^ 2 * ρ p.2
        by fun_prop).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    show ‖(u p.1 - u (p.1 - ε • p.2)) ^ 2 * ρ p.2‖ ≤ (L * (ε * ‖p.2‖)) ^ 2 * ρ p.2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ0 _))]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.2 ((hlip _ _).trans (le_abs_self _))) (hρ0 _)
  -- step 5: Jensen pointwise, then Fubini; step 6: the translation estimate for `‖z‖ < 1`
  -- (`ρ(z) = 0` otherwise); step 7: `∫ ρ = 1`
  calc ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2
      ≤ ∫ x in ball (0 : Euclid n) (1 - s), ∫ z, (u x - u (x - ε • z)) ^ 2 * ρ z := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          hint.integral_prod_left (ae_of_all _ fun x => ?_)
        show (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ∫ z, (u x - u (x - ε • z)) ^ 2 * ρ z
        rw [hrep x]
        exact hjensen (fun z => u x - u (x - ε • z)) (by fun_prop)
    _ = ∫ z, ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2 * ρ z :=
        integral_integral_swap hint
    _ ≤ ∫ z, ε ^ 2 * (∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) * ρ z := by
        refine integral_mono hint.integral_prod_right (hρi.const_mul _) fun z => ?_
        show ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2 * ρ z ≤
          ε ^ 2 * (∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) * ρ z
        rw [integral_mul_const]
        rcases le_or_gt 1 ‖z‖ with hz | hz
        · simp [hρ1 z hz]
        have hw : ‖ε • z‖ ≤ ε := by
          rw [norm_smul, Real.norm_of_nonneg hε.le]
          exact mul_le_of_le_one_right hε.le hz.le
        refine mul_le_mul_of_nonneg_right ?_ (hρ0 z)
        calc ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2
            ≤ ‖ε • z‖ ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 :=
              Submission.dorag_ha_rb_translation_l2 n u L (ε • z) (1 - s) 1 hu (by linarith)
          _ ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw 2)
                (integral_nonneg fun x => sq_nonneg _)
    _ = ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
        rw [integral_const_mul, hρint, mul_one]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
