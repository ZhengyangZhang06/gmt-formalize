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

/-- **Simon, Ch. 6, proof of 5.1** ((29)–(30): subtracting `β [[F]]` does not change the boundary
in `F̊`).  If `g : ℝⁿ → ℝⁿ` is `C¹` with compact support in the open unit cube `Q₁ = (0, 1)ⁿ`, then
`∫_{Q₁} div g = 0`.  `Dg` vanishes off `tsupport g ⊆ Q₁`, so the integral over `Q₁` is the
integral over `ℝⁿ`; in the standard basis `div g = Σᵢ ∂ᵢ gᵢ`, and each `∫ ∂ᵢ gᵢ = 0` by
integration by parts against the constant `1` (the compactly supported `C¹` component `gᵢ` is
Lipschitz). -/
theorem Submission.cmcdt_cbm_integral_div_eq_zero : ∀ (m : ℕ) (g : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) = 0 := by
  intro m g hg hgc hgQ
  -- `Dg` vanishes off `tsupport g ⊆ Q₁`, so the integral over `Q₁` is the integral over `ℝⁿ`
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_]
  swap
  · have h0 : fderiv ℝ g y = 0 := by
      by_contra h
      exact hy (hgQ (support_fderiv_subset ℝ h))
    rw [h0, ContinuousLinearMap.toLinearMap_zero, map_zero]
  -- `div g = Σᵢ ∂ᵢ gᵢ` in the standard basis `eᵢ`
  let e := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have htr : ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) =
      ∑ i, (fderiv ℝ g y (e i)) i := by
    intro y
    rw [LinearMap.trace_eq_sum_inner _ e]
    simp only [e, EuclideanSpace.basisFun_inner, ContinuousLinearMap.coe_coe]
  simp_rw [htr]
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    -- the `i`-th component `gᵢ` is `C¹` with compact support, hence Lipschitz
    let u : Euclid (m + 1) → ℝ := fun y => g y i
    have hu : ContDiff ℝ 1 u := (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hg
    have huc : HasCompactSupport u := hgc.comp_left (g := fun v : Euclid (m + 1) => v i) (by simp)
    obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport huc hu one_ne_zero
    -- integration by parts against the constant `1`
    have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume)
      (LipschitzWith.const (1 : ℝ)) hC huc (-e i)
    have h1 : ∀ x, lineDeriv ℝ (fun _ : Euclid (m + 1) => (1 : ℝ)) x (-e i) = 0 := fun x =>
      ((hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt (-e i)).lineDeriv
    have h2 : ∀ x, lineDeriv ℝ u x (-(-e i)) = fderiv ℝ g x (e i) i := by
      intro x
      rw [neg_neg]
      exact (((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x
        (hdiff x).hasFDerivAt).hasLineDerivAt (e i)).lineDeriv
    simp only [h1, h2, zero_mul, integral_zero, mul_one] at key
    exact key.symm
  · intro i _
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · fun_prop
    · exact (hgc.fderiv ℝ).comp_left
        (g := fun L : Euclid (m + 1) →L[ℝ] Euclid (m + 1) => L (e i) i) (by simp)
/-- The open unit cube `Q₁ = {y : 0 < yᵢ < 1 ∀ i}` of `ℝ^{m+1}` has Lebesgue measure `1`.  The
coordinate map `ofLp : ℝ^{m+1} → (Fin (m + 1) → ℝ)` is measure preserving and `Q₁` is the
preimage of the measurable box `∏ᵢ (0, 1)`, whose volume is `∏ᵢ (1 − 0) = 1`. -/
theorem Submission.cmcdt_cbm_bvp_unit_cube_volume : ∀ m : ℕ, volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro m
  have hset : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
  simp
/-- **Oscillation bound passes to `L¹` limits** (step 2 of the BV Poincaré inequality on cubes,
cf. Simon Ch. 2, 2.7).  Let `Q_δ = {z : δ < z_i < 1 − δ ∀ i}` with `δ ≥ 0`, `u` integrable on
`Q₁ = {y : 0 < y_i < 1 ∀ i}`, and `v_k` continuous with
`∫_{Q_δ}∫_{Q_δ} |v_k(x) − v_k(y)| dy dx ≤ K` and `ε_k = ∫_{Q_δ} |v_k − u| → 0`.  Then
`∫_{Q_δ}∫_{Q_δ} |u(x) − u(y)| dy dx ≤ K`.  `Q_δ ⊆ Q₁` lies in the compact box `[0, 1]^{m+1}`, so
`μ = vol⌞Q_δ` is finite and `u, v_k ∈ L¹(μ)`; `(x, y) ↦ |v_k(x) − v_k(y)|` is `μ ⊗ μ`-integrable
(Fubini).  Integrating `|u(x) − u(y)| ≤ |v_k(x) − v_k(y)| + |u(x) − v_k(x)| + |v_k(y) − u(y)|`
twice gives `D(u) ≤ K + 2 vol(Q_δ) ε_k`; let `k → ∞`. -/
theorem Submission.cmcdt_cbm_bvp_osc_le_of_l1_approx : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (v : ℕ → Euclid (m + 1) → ℝ) (δ K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → 0 ≤ δ → (∀ k, Continuous (v k)) → (∀ k, ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - v k y| ≤ K) → Tendsto (fun k => ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - u x|) atTop (𝓝 0) → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K := by
  intro m u v δ K hu hδ hv hK hlim
  set S : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- `Q_δ ⊆ Q₁`, using `δ ≥ 0`
  have hSQ : S ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun z hz i =>
    ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- `Q₁` lies in the compact closed box `toLp '' [0, 1]^{m+1}`
  have hKc : IsCompact ((WithLp.toLp 2) ''
      (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) : Set (Fin (m + 1) → ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  have hSK : S ⊆ (WithLp.toLp 2) ''
      (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) : Set (Fin (m + 1) → ℝ)) :=
    fun z hz => ⟨z.ofLp, ⟨fun j => (hSQ hz j).1.le, fun j => (hSQ hz j).2.le⟩, rfl⟩
  -- hence `μ = vol⌞Q_δ` is a finite measure, and `u` and every `v k` are `μ`-integrable
  have hSfin : volume S < ∞ := (measure_mono hSK).trans_lt hKc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin.ne
  have huS : Integrable u (volume.restrict S) := hu.mono_set hSQ
  have hvS : ∀ k, Integrable (v k) (volume.restrict S) := fun k =>
    ((hv k).continuousOn.integrableOn_compact hKc).mono_set hSK
  -- `D(u) ≤ D(v k) + 2 vol(Q_δ) ε_k ≤ K + 2 vol(Q_δ) ε_k`
  have key : ∀ k, ∫ x in S, ∫ y in S, |u x - u y| ≤
      K + 2 * volume.real S * ∫ x in S, |v k x - u x| := by
    intro k
    have hw := hvS k
    have hwu : Integrable (fun x => |v k x - u x|) (volume.restrict S) := (hw.sub huS).abs
    have huw : Integrable (fun x => |u x - v k x|) (volume.restrict S) := (huS.sub hw).abs
    -- Fubini: `x ↦ ∫_{Q_δ} |v k x - v k y| dy` is integrable
    have hg : Integrable (fun x => ∫ y in S, |v k x - v k y|) (volume.restrict S) :=
      ((hw.comp_fst (volume.restrict S)).sub
        (hw.comp_snd (volume.restrict S))).abs.integral_prod_left
    -- inner integral, for fixed `x`
    have inner : ∀ x, ∫ y in S, |u x - u y| ≤
        (∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x| +
          ∫ y in S, |v k y - u y| := by
      intro x
      have h1 : Integrable (fun y => |v k x - v k y|) (volume.restrict S) :=
        ((integrable_const (v k x)).sub hw).abs
      have h2 : Integrable (fun y => |v k x - v k y| + |u x - v k x|) (volume.restrict S) :=
        h1.add (integrable_const |u x - v k x|)
      calc ∫ y in S, |u x - u y|
          ≤ ∫ y in S, (|v k x - v k y| + |u x - v k x| + |v k y - u y|) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
              (h2.add hwu) (Eventually.of_forall fun y => ?_)
            calc |u x - u y| = |(v k x - v k y) + (u x - v k x) + (v k y - u y)| := by ring_nf
              _ ≤ |v k x - v k y| + |u x - v k x| + |v k y - u y| := abs_add_three _ _ _
        _ = (∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x| +
              ∫ y in S, |v k y - u y| := by
            rw [integral_add h2 hwu, integral_add h1 (integrable_const _), setIntegral_const,
              smul_eq_mul]
    -- outer integral
    have hg2 : Integrable (fun x => (∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x|)
        (volume.restrict S) :=
      hg.add (huw.const_mul _)
    have hsymm : ∫ x in S, |u x - v k x| = ∫ x in S, |v k x - u x| := by
      congr 1
      funext x
      exact abs_sub_comm _ _
    calc ∫ x in S, ∫ y in S, |u x - u y|
        ≤ ∫ x in S, ((∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x| +
            ∫ y in S, |v k y - u y|) := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun x => integral_nonneg fun y => abs_nonneg _)
            (hg2.add (integrable_const _)) (Eventually.of_forall inner)
      _ = (∫ x in S, ∫ y in S, |v k x - v k y|) + volume.real S * (∫ x in S, |u x - v k x|) +
            volume.real S * ∫ y in S, |v k y - u y| := by
          rw [integral_add hg2 (integrable_const _), integral_add hg (huw.const_mul _),
            integral_const_mul, setIntegral_const, smul_eq_mul]
      _ = (∫ x in S, ∫ y in S, |v k x - v k y|) +
            2 * volume.real S * ∫ x in S, |v k x - u x| := by
          rw [hsymm]
          ring
      _ ≤ K + 2 * volume.real S * ∫ x in S, |v k x - u x| := by
          linarith [hK k]
  -- let `k → ∞`
  have hlim' : Tendsto (fun k => K + 2 * volume.real S * ∫ x in S, |v k x - u x|) atTop
      (𝓝 (K + 2 * volume.real S * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
  rw [mul_zero, add_zero] at hlim'
  exact ge_of_tendsto' hlim' key

/-- **Exhausting `Q₁` by the inner cubes `Q_δ`** (the limit `δ ↓ 0` in the cube Poincaré
inequality, Simon Ch. 2, 2.7, where `U` is first replaced by an inner set
`W = {x ∈ U : dist(x, ∂U) > σ}`): if `u` is integrable on `Q₁ = (0, 1)ⁿ` and
`∫_{Q_δ}∫_{Q_δ} |u(x) − u(y)| dy dx ≤ K` for every inner cube `Q_δ = (δ, 1 − δ)ⁿ`, `0 < δ < 1/2`,
then `∫_{Q₁}∫_{Q₁} |u(x) − u(y)| dy dx ≤ K`.  As `vol(Q₁) = 1`, `|u(x) − u(y)|` is integrable on
`Q₁ × Q₁`; the products `Q_{δⱼ} × Q_{δⱼ}`, `δⱼ = 1/(j + 3)`, increase to `Q₁ × Q₁`, so by Fubini
and continuity of the integral along increasing unions the double integrals over `Q_{δⱼ}` tend
to the one over `Q₁`. -/
theorem Submission.cmcdt_cbm_bvp_osc_le_of_inner_cubes : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K) → ∫ x in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u x - u y| ≤ K := by
  intro m u K hu hK
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  let Q : ℝ → Set (Euclid (m + 1)) := fun δ => {z | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- step 1: every `Q δ` is measurable
  have hQm : ∀ δ : ℝ, MeasurableSet (Q δ) := by
    intro δ
    have hQ : Q δ = ⋂ i, ({z : Euclid (m + 1) | δ < z i} ∩ {z | z i < 1 - δ}) := by
      ext z; simp [Q]
    rw [hQ]
    refine MeasurableSet.iInter fun i => ?_
    have hc : Measurable fun z : Euclid (m + 1) => z i :=
      (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) i).measurable
    exact (measurableSet_lt measurable_const hc).inter (measurableSet_lt hc measurable_const)
  -- step 2: `|u x - u y|` is integrable on `Q₁ × Q₁`, since `vol(Q₁) = 1`
  have hu' : Integrable u (volume.restrict Q₁) := hu
  have : IsFiniteMeasure (volume.restrict Q₁) := isFiniteMeasure_restrict.2 (by
    rw [hQ₁, Submission.cmcdt_cbm_bvp_unit_cube_volume m]; exact ENNReal.one_ne_top)
  let F : Euclid (m + 1) × Euclid (m + 1) → ℝ := fun p => |u p.1 - u p.2|
  have hFi : IntegrableOn F (Q₁ ×ˢ Q₁) ((volume : Measure (Euclid (m + 1))).prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact ((hu'.comp_fst _).sub (hu'.comp_snd _)).abs
  -- step 3: the cubes `Q (δ j)`, `δ j = 1 / (j + 3)`, increase
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 3)
  have hδpos : ∀ j, 0 < δ j := fun j => by positivity
  have hδlt : ∀ j, δ j < 1 / 2 := fun j =>
    one_div_lt_one_div_of_lt (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hδanti : Antitone δ := fun j k hjk =>
    one_div_le_one_div_of_le (by positivity) (by simpa using (Nat.cast_le.2 hjk : (j : ℝ) ≤ k))
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  have hQmono : Monotone fun j => Q (δ j) := fun j k hjk z hz i =>
    ⟨(hδanti hjk).trans_lt (hz i).1, (hz i).2.trans_le (by linarith [hδanti hjk])⟩
  -- step 4: they exhaust `Q₁`
  have hU : ⋃ j, Q (δ j) = Q₁ := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun j z hz i =>
      ⟨(hδpos j).trans (hz i).1, (hz i).2.trans (by linarith [hδpos j])⟩) fun x hx => ?_
    have hev : ∀ᶠ j in atTop, ∀ i, δ j < x i ∧ x i < 1 - δ j := by
      refine Filter.eventually_all.2 fun i => ?_
      filter_upwards [hδlim.eventually_lt_const (hx i).1,
        hδlim.eventually_lt_const (sub_pos.2 (hx i).2)] with j h1 h2
      exact ⟨h1, by linarith⟩
    obtain ⟨j, hj⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  -- step 5: the products `Q (δ j) × Q (δ j)` increase to `Q₁ × Q₁`
  let s : ℕ → Set (Euclid (m + 1) × Euclid (m + 1)) := fun j => Q (δ j) ×ˢ Q (δ j)
  have hsm : ∀ j, MeasurableSet (s j) := fun j => (hQm _).prod (hQm _)
  have hsmono : Monotone s := fun j k hjk => Set.prod_mono (hQmono hjk) (hQmono hjk)
  have hsU : ⋃ j, s j = Q₁ ×ˢ Q₁ := by
    rw [Set.iUnion_prod_of_monotone hQmono hQmono, hU]
  -- steps 6-7: Fubini on each `s j` and continuity along the increasing union
  have hlim := tendsto_setIntegral_of_monotone
    (μ := (volume : Measure (Euclid (m + 1))).prod volume) (f := F) hsm hsmono (hsU ▸ hFi)
  rw [hsU, setIntegral_prod F hFi] at hlim
  have hD : ∀ j, ∫ p in s j, F p ∂(volume : Measure (Euclid (m + 1))).prod volume =
      ∫ x in Q (δ j), ∫ y in Q (δ j), |u x - u y| := fun j =>
    setIntegral_prod F (hFi.mono_set (hsU ▸ Set.subset_iUnion s j))
  -- step 8: pass to the limit in `D(δ j) ≤ K`
  exact le_of_tendsto' (hlim.congr hD) fun j => hK (δ j) (hδpos j) (hδlt j)
/-- **Mean deviation is bounded by the double-integral oscillation** (step 4 of the BV Poincaré
inequality on cubes, cf. Simon Ch. 2, 2.7).  If `vol(S) = 1` and `u` is integrable on `S`, then,
with `c = ∫_S u`, `∫_S |u − c| ≤ ∫_S ∫_S |u(x) − u(y)| dy dx`.  `μ = vol⌞S` is a probability
measure, so `u(x) − c = ∫_S (u(x) − u(y)) dy` and `|u(x) − c| ≤ ∫_S |u(x) − u(y)| dy`; the right
side is integrable in `x` (Fubini), and integrating over `S` gives the claim. -/
theorem Submission.cmcdt_cbm_bvp_mean_dev_le_osc : ∀ (m : ℕ) (S : Set (Euclid (m + 1))) (u : Euclid (m + 1) → ℝ), volume S = 1 → IntegrableOn u S → ∫ x in S, |u x - ∫ y in S, u y| ≤ ∫ x in S, ∫ y in S, |u x - u y| := by
  intro m S u hS hu
  -- `μ = vol⌞S` is a probability measure, since `μ univ = vol S = 1`
  have : IsProbabilityMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ, hS]⟩
  have hSr : volume.real S = 1 := by rw [measureReal_def, hS, ENNReal.toReal_one]
  have huS : Integrable u (volume.restrict S) := hu
  -- Fubini: `x ↦ ∫_S |u x - u y| dy` is integrable on `S`
  have hg : Integrable (fun x => ∫ y in S, |u x - u y|) (volume.restrict S) :=
    ((huS.comp_fst (volume.restrict S)).sub
      (huS.comp_snd (volume.restrict S))).abs.integral_prod_left
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hg
    (Eventually.of_forall fun x => ?_)
  -- for fixed `x`, `u x - c = ∫_S (u x - u y) dy`, hence `|u x - c| ≤ ∫_S |u x - u y| dy`
  have hx : ∫ y in S, (u x - u y) = u x - ∫ y in S, u y := by
    rw [integral_sub (integrable_const _) huS, setIntegral_const, hSr, one_smul]
  calc |u x - ∫ y in S, u y| = |∫ y in S, (u x - u y)| := by rw [hx]
    _ ≤ ∫ y in S, |u x - u y| := abs_integral_le_integral_abs
/-- A continuous `f` on `ℝᵏ` is bounded and integrable on the open unit cube
`Q₁ = {0 < yᵢ < 1}`.  The closed cube `K = {0 ≤ yᵢ ≤ 1}`, the image of the compact box `Icc 0 1`
of `Fin k → ℝ` under `toLp`, is compact and contains `Q₁`; a continuous function is bounded on
`K` and integrable on `K` for the Haar measure `volume`, hence on `Q₁`. -/
theorem Submission.cmcdt_cbm_bvt_cube_cont_bound : ∀ (k : ℕ) (f : Euclid k → ℝ), Continuous f → (∃ M : ℝ, ∀ y ∈ {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ M) ∧ IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} := by
  intro k f hf
  -- the closed cube `K = {0 ≤ yᵢ ≤ 1}` is the image of the compact box `Icc 0 1` of `Fin k → ℝ`
  have hK : IsCompact (WithLp.toLp 2 '' Icc (0 : Fin k → ℝ) 1 : Set (Euclid k)) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  have hQK : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ⊆ WithLp.toLp 2 '' Icc (0 : Fin k → ℝ) 1 :=
    fun y hy => ⟨WithLp.ofLp y, ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩, WithLp.toLp_ofLp 2 y⟩
  -- `f` is bounded and integrable on the compact `K`, hence on `Q₁ ⊆ K`
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨⟨M, fun y hy => by simpa only [Real.norm_eq_abs] using hM y (hQK hy)⟩,
    (hf.continuousOn.integrableOn_compact hK).mono_set hQK⟩
/-- **L¹ limit of an affine bound** (step 2 of the BV trace estimate).  If
`|∫_S v_k h| ≤ A + B ∫_S |v_k|` for all `k`, `B ≥ 0`, `|h| ≤ M` on `S` and `v_k → w` in `L¹(S)`,
then `|∫_S w h| ≤ A + B ∫_S |w|`: with `ε_k = ∫_S |v_k − w|`,
`|∫_S w h − ∫_S v_k h| ≤ M ε_k` and `∫_S |v_k| ≤ ∫_S |w| + ε_k`, so
`|∫_S w h| ≤ A + B ∫_S |w| + (B + M) ε_k` for every `k`; let `k → ∞`. -/
theorem Submission.cmcdt_cbm_bvt_l1_limit : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (v : ℕ → α → ℝ) (w h : α → ℝ) (A B M : ℝ), MeasurableSet S → 0 ≤ B → (∀ k, IntegrableOn (v k) S μ) → IntegrableOn w S μ → AEStronglyMeasurable h (μ.restrict S) → (∀ x ∈ S, |h x| ≤ M) → Tendsto (fun k => ∫ x in S, |v k x - w x| ∂μ) atTop (𝓝 0) → (∀ k, |∫ x in S, v k x * h x ∂μ| ≤ A + B * ∫ x in S, |v k x| ∂μ) → |∫ x in S, w x * h x ∂μ| ≤ A + B * ∫ x in S, |w x| ∂μ := by
  intro α _ μ S v w h A B M hS hB hv hw hh hM hlim hbd
  -- `|h| ≤ M` holds `μ⌞S`-a.e., so `w h` and `v_k h` are integrable on `S`
  have hMae : ∀ᵐ x ∂(μ.restrict S), ‖h x‖ ≤ M :=
    (ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]
      exact hM x hx)
  have hwh : IntegrableOn (fun x => w x * h x) S μ := Integrable.mul_bdd hw hh hMae
  have hvh : ∀ k, IntegrableOn (fun x => v k x * h x) S μ := fun k =>
    Integrable.mul_bdd (hv k) hh hMae
  -- for every `k`: `|∫_S w h| ≤ A + B ∫_S |w| + (B + M) ε_k`
  have hk : ∀ k, |∫ x in S, w x * h x ∂μ| ≤
      A + B * (∫ x in S, |w x| ∂μ) + (B + M) * ∫ x in S, |v k x - w x| ∂μ := by
    intro k
    -- `|∫_S w h − ∫_S v_k h| ≤ M ε_k`
    have hdiff : |(∫ x in S, w x * h x ∂μ) - ∫ x in S, v k x * h x ∂μ| ≤
        M * ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_sub hwh (hvh k)]
      calc |∫ x in S, (w x * h x - v k x * h x) ∂μ|
          ≤ ∫ x in S, |w x * h x - v k x * h x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ x in S, M * |v k x - w x| ∂μ := by
          refine integral_mono_ae (hwh.sub (hvh k)).abs (((hv k).sub hw).abs.const_mul M) ?_
          filter_upwards [hMae] with x hx
          rw [← sub_mul, abs_mul, abs_sub_comm, mul_comm]
          exact mul_le_mul_of_nonneg_right (by rwa [Real.norm_eq_abs] at hx) (abs_nonneg _)
        _ = M * ∫ x in S, |v k x - w x| ∂μ := integral_const_mul M _
    -- `∫_S |v_k| ≤ ∫_S |w| + ε_k`
    have hwi : IntegrableOn (fun x => |w x|) S μ := hw.abs
    have hvwi : IntegrableOn (fun x => |v k x - w x|) S μ := ((hv k).sub hw).abs
    have hvw : ∫ x in S, |v k x| ∂μ ≤ (∫ x in S, |w x| ∂μ) + ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_add hwi hvwi]
      refine integral_mono (hv k).abs (hwi.add hvwi) fun x => ?_
      calc |v k x| = |w x + (v k x - w x)| := by rw [add_sub_cancel]
        _ ≤ |w x| + |v k x - w x| := abs_add_le _ _
    have htri : |∫ x in S, w x * h x ∂μ| ≤
        |∫ x in S, v k x * h x ∂μ| + |(∫ x in S, w x * h x ∂μ) - ∫ x in S, v k x * h x ∂μ| := by
      have := abs_add_le (∫ x in S, v k x * h x ∂μ)
        ((∫ x in S, w x * h x ∂μ) - ∫ x in S, v k x * h x ∂μ)
      rwa [add_sub_cancel] at this
    linarith [hbd k, mul_le_mul_of_nonneg_left hvw hB]
  -- let `k → ∞`: `ε_k → 0`
  have hT : Tendsto (fun k => A + B * (∫ x in S, |w x| ∂μ) + (B + M) * ∫ x in S, |v k x - w x| ∂μ)
      atTop (𝓝 (A + B * (∫ x in S, |w x| ∂μ) + (B + M) * 0)) :=
    tendsto_const_nhds.add (hlim.const_mul (B + M))
  rw [mul_zero, add_zero] at hT
  exact ge_of_tendsto' hT hk
/-- Exhaustion of the open unit cube `Q₁ = {0 < yᵢ < 1}` by the shrunken cubes
`Q_δ = {δ < zᵢ < 1 - δ}`: if `f` is integrable on `Q₁`, then `∫_{Q_δ} f → ∫_{Q₁} f` as `δ → 0⁺`.
For `δ > 0`, `∫_{Q_δ} f = ∫_{Q₁} 1_{Q_δ} f`, and every `y ∈ Q₁` lies in `Q_δ` for all small
`δ > 0`; dominated convergence on `Q₁` with bound `|f|` concludes. -/
theorem Submission.cmcdt_cbm_bvt_cube_exhaust : ∀ (k : ℕ) (f : Euclid k → ℝ), IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} → Tendsto (fun δ : ℝ => ∫ y in {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}, f y) (𝓝[>] 0) (𝓝 (∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, f y)) := by
  intro k f hf
  -- each `{z | ∀ i, a < z i ∧ z i < b}` is a finite intersection of open half-spaces
  have hmeas : ∀ a b : ℝ, MeasurableSet {z : Euclid k | ∀ i, a < z i ∧ z i < b} := by
    intro a b
    have h : {z : Euclid k | ∀ i, a < z i ∧ z i < b} =
        ⋂ i, ({z : Euclid k | a < z i} ∩ {z : Euclid k | z i < b}) := by
      ext z
      simp
    rw [h]
    refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => ?_)
    exact (isOpen_lt continuous_const (PiLp.continuous_apply _ _ i)).inter
      (isOpen_lt (PiLp.continuous_apply _ _ i) continuous_const)
  -- for `δ > 0`, `∫_{Q_δ} f = ∫_{Q₁} 1_{Q_δ} f`
  have heq : (fun δ : ℝ => ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1},
      {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}.indicator f y) =ᶠ[𝓝[>] 0]
      fun δ : ℝ => ∫ y in {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}, f y := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [setIntegral_indicator (hmeas _ _), inter_eq_right.2]
    intro z hz i
    exact ⟨hδ.trans (hz i).1, (hz i).2.trans (by linarith)⟩
  refine Tendsto.congr' heq ?_
  -- dominated convergence on `Q₁` with bound `|f|`
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
    (Eventually.of_forall fun δ => hf.aestronglyMeasurable.indicator (hmeas _ _))
    (Eventually.of_forall fun δ => Eventually.of_forall fun y => norm_indicator_le_norm_self _ _)
    hf.norm ?_
  rw [ae_restrict_iff' (by simpa using hmeas 0 1)]
  refine Eventually.of_forall fun y hy => tendsto_const_nhds.congr' ?_
  -- every `y ∈ Q₁` lies in `Q_δ` for all small `δ > 0`
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, δ < y i ∧ y i < 1 - δ := by
    rw [Filter.eventually_all]
    intro i
    have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < y i := eventually_lt_nhds (hy i).1
    have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 1 - y i := eventually_lt_nhds (by linarith [(hy i).2])
    exact nhdsWithin_le_nhds ((h1.and h2).mono fun δ h => ⟨h.1, by linarith [h.2]⟩)
  filter_upwards [hev] with δ hδ
  exact (indicator_of_mem (show y ∈ {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} from hδ) f).symm
/-- **Adjoint identity for mollification** (Simon Ch. 2, 2.5).  If `η : ℝᴾ → ℝ` is `C¹` with
compact support, `η̌(z) = η(−z)`, and `u`, `s` are integrable, then
`∫ D(η ⋆ u)(x)(s x) dx = −∫ u div(η̌ ⋆ s)`, where `div G = trace DG`.  Differentiating under the
integral, `D(η ⋆ u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz` and, since `Dη̌(y) = −Dη(−y)`,
`div(η̌ ⋆ s)(z) = −∫ Dη(x − z)(s x) dx`; Fubini applies to `Dη(x − z)(s x) u(z)`, which is
dominated by `C ‖s x‖ |u z|` with `C = sup ‖Dη‖`. -/
theorem Submission.cmcdt_cbm_sa_mollify_adjoint : ∀ (P : ℕ) (η u : Euclid P → ℝ) (s : Euclid P → Euclid P), ContDiff ℝ 1 η → HasCompactSupport η → Integrable u → Integrable s → ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ (convolution (fun z => η (-z)) s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z : Euclid P →ₗ[ℝ] Euclid P) := by
  intro P η u s hη hηc hu hs
  -- Step 1: `Dη` is continuous with compact support, hence bounded by some `C`.
  have hDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDcs : HasCompactSupport (fderiv ℝ η) := hηc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 2: `η̌ = η ∘ (−id)` is `C¹` with compact support, and `Dη̌(y) = −Dη(−y)` (chain rule).
  set ηr : Euclid P → ℝ := fun z => η (-z)
  have hηr : ContDiff ℝ 1 ηr := hη.comp contDiff_neg
  have hηrc : HasCompactSupport ηr := hηc.comp_homeomorph (Homeomorph.neg (Euclid P))
  have hDrc : Continuous (fderiv ℝ ηr) := hηr.continuous_fderiv one_ne_zero
  have hDrcs : HasCompactSupport (fderiv ℝ ηr) := hηrc.fderiv ℝ
  have hDr : ∀ y, fderiv ℝ ηr y = -fderiv ℝ η (-y) := by
    intro y
    have h1 : HasFDerivAt ηr ((fderiv ℝ η (-y)).comp (-ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hη.differentiable one_ne_zero) (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
    rw [h1.fderiv]
    ext v
    simp
  -- Step 3: `D(η ⋆ u)(x) = (Dη ⋆ u)(x)`, so `D(η ⋆ u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz`.
  have hLHS : ∀ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) =
      ∫ z, fderiv ℝ η (x - z) (s x) * u z := by
    intro x
    rw [(hηc.hasFDerivAt_convolution_left _ hη hu.locallyIntegrable x).fderiv, convolution_eq_swap,
      ContinuousLinearMap.integral_apply
        ((hDcs.convolutionExists_left _ hDc hu.locallyIntegrable x).integrable_swap)]
    simp
  -- Step 4: `div(η̌ ⋆ s)(z) = trace D(η̌ ⋆ s)(z) = ∫ Dη̌(z − x)(s x) dx`: the trace `T` is a
  -- continuous linear functional, and the trace of the rank-one map `v ↦ a(v) w` is `a(w)`.
  have hRHS : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (convolution ηr s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
        Euclid P →ₗ[ℝ] Euclid P) = ∫ x, fderiv ℝ ηr (z - x) (s x) := by
    let T : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid P) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have hTA : ∀ A : Euclid P →L[ℝ] Euclid P,
        T A = LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) := fun A => rfl
    have hrk : ∀ (a : Euclid P →L[ℝ] ℝ) (w : Euclid P), T (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w) = a w := by
      intro a w
      have h : ((ContinuousLinearMap.precompL (Euclid P)
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w :
            Euclid P →L[ℝ] Euclid P) : Euclid P →ₗ[ℝ] Euclid P) =
          (a : Euclid P →ₗ[ℝ] ℝ).smulRight w := by
        ext v
        simp
      rw [hTA, h, LinearMap.trace_smulRight]
      rfl
    intro z
    rw [(hηrc.hasFDerivAt_convolution_left _ hηr hs.locallyIntegrable z).fderiv,
      convolution_eq_swap]
    have hT := ContinuousLinearMap.integral_comp_comm T
      ((hDrcs.convolutionExists_left (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P)) hDrc
          hs.locallyIntegrable z).integrable_swap)
    simp_rw [hrk] at hT
    exact hT.symm
  -- Step 5: Fubini for `H(x, z) = Dη(x − z)(s x) u(z)`, dominated by `C ‖s x‖ |u z|`.
  have hint : Integrable (uncurry fun x z => fderiv ℝ η (x - z) (s x) * u z)
      ((volume : Measure (Euclid P)).prod volume) := by
    refine Integrable.mono' ((hs.norm.mul_prod hu.norm).const_mul C) ?_ (Eventually.of_forall ?_)
    · exact ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
        hs.aestronglyMeasurable.comp_fst
        (hDc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hu.aestronglyMeasurable.comp_snd
    · rintro ⟨x, z⟩
      simp only [uncurry_apply_pair, norm_mul]
      calc ‖fderiv ℝ η (x - z) (s x)‖ * ‖u z‖ ≤ (C * ‖s x‖) * ‖u z‖ := by
            gcongr
            exact ((fderiv ℝ η (x - z)).le_opNorm (s x)).trans (by gcongr; exact hC _)
        _ = C * (‖s x‖ * ‖u z‖) := by ring
  -- Step 6: combine, using `Dη̌(z − x) = −Dη(x − z)` to identify the swapped integral.
  calc ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x)
      = ∫ x, ∫ z, fderiv ℝ η (x - z) (s x) * u z := by simp_rw [hLHS]
    _ = ∫ z, ∫ x, fderiv ℝ η (x - z) (s x) * u z := integral_integral_swap hint
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P)
          (fderiv ℝ (convolution ηr s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
            Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_neg]
      congr 1
      funext z
      rw [hRHS z, ← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      rw [hDr, neg_sub, neg_apply]
      ring
/-- Convolving with a probability density `k ≥ 0`, `∫ k = 1`, does not increase the `L¹` norm:
`∫⁻ ‖k ⋆ g‖ₑ ≤ ∫⁻ ‖g‖ₑ` (Young's inequality `‖k ⋆ g‖₁ ≤ ‖k‖₁ ‖g‖₁`).  As `∫ k = 1 ≠ 0`, `k` is
integrable and `∫⁻ ‖k‖ₑ = ofReal (∫ k) = 1`.  Pointwise `‖(k ⋆ g)(x)‖ₑ ≤ ∫⁻ ‖k t‖ₑ ‖g (x - t)‖ₑ dt`;
Tonelli and translation invariance of Lebesgue measure turn the right side, integrated in `x`,
into `(∫⁻ ‖k‖ₑ) (∫⁻ ‖g‖ₑ)`. -/
theorem Submission.cmcdt_cbm_sa_ml_l1_contraction : ∀ (n : ℕ) (k g : Euclid n → ℝ), (∀ z, 0 ≤ k z) → ∫ z, k z = 1 → AEStronglyMeasurable g volume → ∫⁻ x, ‖convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ := by
  intro n k g hk0 hk1 hg
  -- `k` is integrable because `∫ k = 1 ≠ 0`, and it has unit mass `∫⁻ ‖k‖ₑ = 1`.
  have hk_int : Integrable k := integrable_of_integral_eq_one hk1
  have hk_mass : ∫⁻ t, ‖k t‖ₑ = 1 := by
    rw [lintegral_enorm_of_nonneg hk0,
      ← ofReal_integral_eq_lintegral_ofReal hk_int (ae_of_all _ hk0), hk1, ENNReal.ofReal_one]
  -- The convolution integrand is jointly a.e.-measurable, as Tonelli requires.
  have hmeas : AEMeasurable (uncurry fun (x t : Euclid n) => ‖k t‖ₑ * ‖g (x - t)‖ₑ)
      (volume.prod volume) := by
    refine (hk_int.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hg).enorm.congr (ae_of_all _ fun p => ?_)
    simp [uncurry]
  calc ∫⁻ x, ‖convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
      ≤ ∫⁻ x, ∫⁻ t, ‖k t‖ₑ * ‖g (x - t)‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [convolution_def]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun t => ?_
        simp
    _ = ∫⁻ t, ∫⁻ x, ‖k t‖ₑ * ‖g (x - t)‖ₑ := lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ‖k t‖ₑ * ∫⁻ x, ‖g x‖ₑ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top,
          lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t]
    _ = (∫⁻ t, ‖k t‖ₑ) * ∫⁻ x, ‖g x‖ₑ := lintegral_mul_const'' _ hk_int.aestronglyMeasurable.enorm
    _ = ∫⁻ x, ‖g x‖ₑ := by rw [hk_mass, one_mul]
/-- Uniform `L¹` approximate identity for a continuous compactly supported `h : ℝⁿ → ℝ`: for
`ε > 0` there is `r > 0` with `∫⁻ ‖ρ ⋆ h - h‖ₑ ≤ ε` for every `ρ ≥ 0` with `∫ ρ = 1` and
`spt ρ ⊆ B_r(0)`.  Take `tsupport h ⊆ B̄_R(0)`, `S = B̄_{R+1}(0)`, `η = ε / (Lⁿ(S) + 1)`, and by
uniform continuity `r ≤ 1` with `|h(y) - h(x)| < η` for `|y - x| < r`.  On `S`,
`dist_convolution_le` gives `|ρ ⋆ h - h| ≤ η`; off `S`, `h` and `ρ ⋆ h` vanish.  Integrating,
`∫⁻ ‖ρ ⋆ h - h‖ₑ ≤ η Lⁿ(S) ≤ ε`. -/
theorem Submission.cmcdt_cbm_sa_ml_compact_support_approx : ∀ (n : ℕ) (h : Euclid n → ℝ), Continuous h → HasCompactSupport h → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ ρ : Euclid n → ℝ, (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid n) r → ∫⁻ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ ≤ ENNReal.ofReal ε := by
  intro n h hc hcs ε hε
  -- `tsupport h ⊆ B̄_R(0)`; the error lives in the compact set `S = B̄_{R+1}(0)`
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : Euclid n)
  set S : Set (Euclid n) := closedBall (0 : Euclid n) (R + 1) with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hSfin : volume S ≠ ∞ := measure_closedBall_lt_top.ne
  set V : ℝ := (volume S).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  -- the pointwise tolerance `η = ε / (V + 1)`, and `r ≤ 1` from uniform continuity
  set η : ℝ := ε / (V + 1) with hη
  have hη0 : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hδh⟩ :=
    Metric.uniformContinuous_iff.1 (hcs.uniformContinuous_of_continuous hc) η hη0
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro ρ hρ0 hρ1 hρs
  have hzero : ∀ y : Euclid n, R < ‖y‖ → h y = 0 := by
    intro y hy
    by_contra hne
    have : y ∈ closedBall (0 : Euclid n) R := hR (subset_tsupport h hne)
    rw [mem_closedBall_zero_iff] at this
    linarith
  -- pointwise bound by `η` on `S`, and `0` off `S`
  have hpt : ∀ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ ≤
      S.indicator (fun _ => ENNReal.ofReal η) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal (dist_convolution_le hη0.le hρs hρ0 hρ1
        hc.aestronglyMeasurable fun y hy => (hδh ?_).le)
      exact lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _)
    · rw [indicator_of_notMem hx]
      rw [hS, mem_closedBall_zero_iff, not_le] at hx
      have hconv : convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
        rw [convolution_def]
        refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
        by_cases ht : ρ t = 0
        · simp [ht]
        · have ht' : ‖t‖ < 1 :=
            lt_of_lt_of_le (mem_ball_zero_iff.1 (hρs ht)) (min_le_right _ _)
          have hxt : R < ‖x - t‖ := by
            have := norm_sub_norm_le x t
            linarith
          simp [hzero _ hxt]
      rw [hconv, hzero x (by linarith), sub_zero, enorm_zero]
  calc ∫⁻ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ
      ≤ ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal η) x := lintegral_mono hpt
    _ = ENNReal.ofReal η * volume S := lintegral_indicator_const hSm _
    _ = ENNReal.ofReal (η * V) := by
        rw [ENNReal.ofReal_mul hη0.le, hV, ENNReal.ofReal_toReal hSfin]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- **`L¹` approximate identity** (Simon 2.5: mollifications converge in `L¹`).  For integrable
`f` on `ℝⁿ` and `ε > 0` there is `r > 0` with `∫ |ρ ⋆ f − f| ≤ ε` for every continuous `ρ ≥ 0`
with `∫ ρ = 1` and `spt ρ ⊆ B_r(0)`.  `volume` is regular, so `f` is `L¹`-close to a continuous
compactly supported `h` (indicators of sets of finite measure are approximated by Urysohn
functions); `Submission.cmcdt_cbm_sa_ml_compact_support_approx` gives `r` for `h`, and in
`ρ ⋆ f − f = ρ ⋆ (f − h) + (ρ ⋆ h − h) − (f − h)` the first term is at most `∫ |f − h|` by
`Submission.cmcdt_cbm_sa_ml_l1_contraction`. -/
theorem Submission.cmcdt_cbm_sa_mollify_l1 : ∀ (n : ℕ) (f : Euclid n → ℝ), Integrable f → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ ρ : Euclid n → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid n) r → ∫⁻ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ ≤ ENNReal.ofReal ε := by
  intro n f hf ε hε
  have hε4 : 0 < ε / 4 := by positivity
  -- Density: `volume` is regular, so for measurable `s` of finite measure an Urysohn function
  -- `φ`, equal to `1` on a compact `F ⊆ s` and to `0` off an open `V ⊇ s`, has compact support
  -- and `|φ c − 1_s c| ≤ |1_{V \ F} c|` with `vol (V \ F)` small; hence some continuous `h` with
  -- compact support has `∫ |f − h| ≤ ε / 4`
  have hind : ∀ (c : ℝ) ⦃s : Set (Euclid n)⦄, MeasurableSet s → volume s < ∞ →
      ∀ {δ : ℝ≥0∞}, δ ≠ 0 → ∃ φ : Euclid n → ℝ,
        eLpNorm (φ - s.indicator fun _ => c) 1 volume ≤ δ ∧
          (Continuous φ ∧ HasCompactSupport φ) := by
    intro c s hs hsfin δ hδ
    obtain ⟨η, hη, hηδ⟩ := exists_eLpNorm_indicator_le (μ := (volume : Measure (Euclid n)))
      ENNReal.one_ne_top c hδ
    have hη2 : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_pos.2 hη).ne').ne'
    obtain ⟨F, hFs, hF, hsF⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne hη2
    obtain ⟨V, hsV, hV, -, hVs⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne hη2
    obtain ⟨φ, hφF, hφV, hφcs, hφ⟩ :=
      exists_continuous_one_zero_of_isCompact hF hV.isClosed_compl
        (disjoint_compl_right_iff_subset.2 (hFs.trans hsV))
    have hφc : Continuous fun x => φ x * c := φ.continuous.mul continuous_const
    refine ⟨fun x => φ x * c, (eLpNorm_mono (hφc.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator hs)) fun x => ?_).trans (hηδ (V \ F) ?_
      (hV.measurableSet.diff hF.measurableSet).nullMeasurableSet), hφc, hφcs.mul_right⟩
    · -- pointwise: `0` on `F` and off `V`, at most `|c|` on `V \ F`
      show ‖φ x * c - s.indicator (fun _ => c) x‖ ≤ ‖(V \ F).indicator (fun _ => c) x‖
      by_cases hxF : x ∈ F
      · rw [hφF hxF, indicator_of_mem (hFs hxF), Pi.one_apply, one_mul, sub_self, norm_zero]
        exact norm_nonneg _
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ F from ⟨hxV, hxF⟩)]
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs]
          calc ‖φ x * c - c‖ = |φ x - 1| * ‖c‖ := by
                rw [← sub_one_mul, norm_mul, Real.norm_eq_abs]
            _ ≤ 1 * ‖c‖ := by
                gcongr
                rw [abs_le]
                constructor <;> linarith [(hφ x).1, (hφ x).2]
            _ = ‖c‖ := one_mul _
        · rw [indicator_of_notMem hxs, sub_zero, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (hφ x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφ x).2
      · rw [hφV (mem_compl hxV), Pi.zero_apply, zero_mul,
          indicator_of_notMem fun h => hxV (hsV h), sub_zero, norm_zero]
        exact norm_nonneg _
    · -- `V \ F ⊆ (V \ s) ∪ (s \ F)`
      calc volume (V \ F) ≤ volume ((V \ s) ∪ (s \ F)) := measure_mono fun x hx => by
            by_cases hxs : x ∈ s
            exacts [Or.inr ⟨hxs, hx.2⟩, Or.inl ⟨hx.1, hxs⟩]
        _ ≤ volume (V \ s) + volume (s \ F) := measure_union_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add hVs.le hsF.le
        _ = η := ENNReal.add_halves _
  obtain ⟨h, hfh, hhc, hhcs⟩ := (memLp_one_iff_integrable.2 hf).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun _ _ h₁ h₂ => ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩) (ENNReal.ofReal_pos.2 hε4).ne'
  have hh : Integrable h := hhc.integrable_of_hasCompactSupport hhcs
  have hfh' : Integrable (f - h) := hf.sub hh
  rw [eLpNorm_one_eq_lintegral_enorm hfh'.aestronglyMeasurable] at hfh
  -- The compactly supported case gives `r`, chosen before `ρ`
  obtain ⟨r, hr, hB⟩ :=
    Submission.cmcdt_cbm_sa_ml_compact_support_approx n h hhc hhcs (ε / 4) hε4
  refine ⟨r, hr, fun ρ hρc hρ0 hρ1 hρs => ?_⟩
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) r) fun x hx =>
      by_contra fun hne => hx (ball_subset_closedBall (hρs hne))
  -- `ρ ⋆ f = ρ ⋆ (f − h) + ρ ⋆ h`; both convolutions exist everywhere and are continuous
  have hex₁ := hρcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hfh'.locallyIntegrable
  have hex₂ := hρcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hh.locallyIntegrable
  have hc₁ := hρcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hfh'.locallyIntegrable
  have hc₂ := hρcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hh.locallyIntegrable
  -- The triangle inequality, then `ε / 4` for each of the three terms
  have hpt : ∀ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ ≤
      ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ + ‖(f - h) x‖ₑ := by
    intro x
    have hsplit := (hex₁ x).distrib_add (hex₂ x)
    rw [sub_add_cancel] at hsplit
    rw [hsplit, show ∀ a b : ℝ, a + b - f x = a + (b - h x) - (f - h) x from fun a b => by
      rw [Pi.sub_apply]; ring]
    exact enorm_sub_le.trans (add_le_add (enorm_add_le _ _) le_rfl)
  have hm₁ : AEMeasurable
      (fun x => ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) volume :=
    hc₁.enorm.measurable.aemeasurable
  have hm₂ : AEMeasurable
      (fun x => ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ) volume :=
    (hc₁.enorm.add (hc₂.sub hhc).enorm).measurable.aemeasurable
  calc ∫⁻ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ
      ≤ ∫⁻ x, (‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
          ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ + ‖(f - h) x‖ₑ) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) +
          (∫⁻ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ) +
          ∫⁻ x, ‖(f - h) x‖ₑ := by
        rw [lintegral_add_left' hm₂, lintegral_add_left' hm₁]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
        gcongr
        · exact (Submission.cmcdt_cbm_sa_ml_l1_contraction n ρ (f - h) hρ0 hρ1
            hfh'.aestronglyMeasurable).trans hfh
        · exact hB ρ hρ0 hρ1 hρs
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add (by positivity) hε4.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
/-- **Segment estimate for `C¹` functions.**  For `v ∈ C¹(ℝⁿ)` and `x, y ∈ ℝⁿ`,
`|v(x) − v(y)| ≤ ‖x − y‖ ∫₀¹ ‖Dv((1 − t)y + tx)‖ dt`.  Along `p(t) = (1 − t)y + tx` the chain rule
gives `(v ∘ p)'(t) = Dv(p(t))(x − y)`, which is continuous in `t`; the fundamental theorem of
calculus, `|∫ f| ≤ ∫ |f|` and the operator-norm bound `|Dv(p(t))(x − y)| ≤ ‖x − y‖ ‖Dv(p(t))‖`
finish the proof. -/
theorem Submission.cmcdt_cbm_sp_segment_bound : ∀ (n : ℕ) (v : Euclid n → ℝ) (x y : Euclid n), ContDiff ℝ 1 v → |v x - v y| ≤ ‖x - y‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ := by
  intro n v x y hv
  have hdiff : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  -- the segment `p(t) = (1 - t) • y + t • x`, with `p 0 = y`, `p 1 = x` and `p' = x - y`
  obtain ⟨p, hp⟩ : ∃ p : ℝ → Euclid n, p = fun t => (1 - t) • y + t • x := ⟨_, rfl⟩
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hpd : ∀ t, HasDerivAt p (x - y) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) • y) ((-1 : ℝ) • y) t :=
      ((hasDerivAt_id t).const_sub 1).smul_const y
    have h2 : HasDerivAt (fun t : ℝ => t • x) ((1 : ℝ) • x) t := (hasDerivAt_id t).smul_const x
    rw [hp]
    convert h1.add h2 using 1
    simp only [neg_smul, one_smul]
    abel
  -- chain rule: `(v ∘ p)'(t) = Dv(p(t))(x - y)`, a continuous function of `t`
  have hγ : ∀ t, HasDerivAt (fun t => v (p t)) (fderiv ℝ v (p t) (x - y)) t := fun t =>
    (hdiff (p t)).hasFDerivAt.comp_hasDerivAt t (hpd t)
  have hγc : Continuous fun t => fderiv ℝ v (p t) (x - y) :=
    (hcont.comp hpc).clm_apply continuous_const
  -- fundamental theorem of calculus
  have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ v (p t) (x - y) = v x - v y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hγ t)
      (hγc.intervalIntegrable 0 1)]
    simp [hp]
  have hpt : ∀ t, (1 - t) • y + t • x = p t := fun t => by rw [hp]
  simp only [hpt]
  rw [← hftc, ← Real.norm_eq_abs]
  calc ‖∫ t in (0 : ℝ)..1, fderiv ℝ v (p t) (x - y)‖
      ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p t) (x - y)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, ‖x - y‖ * ‖fderiv ℝ v (p t)‖ := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact hγc.norm.intervalIntegrable 0 1
        · exact (continuous_const.mul (hcont.comp hpc).norm).intervalIntegrable 0 1
        · intro t _
          rw [mul_comm]
          exact (fderiv ℝ v (p t)).le_opNorm (x - y)
    _ = ‖x - y‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p t)‖ :=
        intervalIntegral.integral_const_mul _ _
/-- **Slice bound on a convex set.**  For convex measurable `Q ⊆ ℝⁿ`, measurable `g ≥ 0` and
`t ∈ [0, 1]`, `∫_Q ∫_Q g((1 − t)y + tx) dy dx ≤ 2ⁿ Lⁿ(Q) ∫_Q g`.  If `s ≥ 1/2` and `c + sQ ⊆ Q`,
the Haar scaling `v ↦ sv` and translation invariance give
`∫_Q g(c + sv) dv ≤ ∫ (1_Q g)(c + sv) dv = s⁻ⁿ ∫_Q g ≤ 2ⁿ ∫_Q g`.  By convexity of `Q`, this applies
in `y` (`c = tx`, `s = 1 − t`) when `t ≤ 1/2`, and in `x` after Tonelli (`c = (1 − t)y`, `s = t`)
when `t ≥ 1/2`; integrating the constant bound over `Q` gives the claim. -/
theorem Submission.cmcdt_cbm_sp_convex_slice_bound : ∀ (n : ℕ) (Q : Set (Euclid n)) (g : Euclid n → ℝ≥0∞), Convex ℝ Q → MeasurableSet Q → Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
  intro n Q g hQc hQm hg t ht
  obtain ⟨ht0, ht1⟩ := ht
  -- One-variable bound: if `s ≥ 1/2` and `c + s • Q ⊆ Q`, then `∫_Q g(c + s v) dv ≤ 2ⁿ ∫_Q g`.
  have key : ∀ (c : Euclid n) (s : ℝ), 1 / 2 ≤ s →
      (∀ v ∈ Q, c + s • v ∈ Q) →
      ∫⁻ v in Q, g (c + s • v) ≤ 2 ^ n * ∫⁻ z in Q, g z := by
    intro c s hs hcs
    have hs0 : 0 < s := by linarith
    obtain ⟨F, hFdef⟩ : ∃ F : Euclid n → ℝ≥0∞, F = Q.indicator g := ⟨_, rfl⟩
    have hF : Measurable F := hFdef ▸ hg.indicator hQm
    -- change of variables `v ↦ s • v` (Haar scaling) followed by translation invariance
    have hcv : ∫⁻ v, F (c + s • v) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, F z := by
      have h1 : ∫⁻ w, F (c + w) ∂(Measure.map (fun v : Euclid n => s • v) volume)
          = ∫⁻ v, F (c + s • v) :=
        lintegral_map (hF.comp (measurable_const_add c)) (measurable_const_smul s)
      rw [← h1, Measure.map_addHaar_smul volume hs0.ne', lintegral_smul_measure,
        lintegral_add_left_eq_self F c, finrank_euclideanSpace_fin, smul_eq_mul]
    have hs2 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 two_pos]
      linarith
    calc ∫⁻ v in Q, g (c + s • v)
        = ∫⁻ v in Q, F (c + s • v) := by
          refine setLIntegral_congr_fun hQm fun v hv => ?_
          rw [hFdef, Set.indicator_of_mem (hcs v hv)]
      _ ≤ ∫⁻ v, F (c + s • v) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in Q, g z := by
          rw [hcv, hFdef, lintegral_indicator hQm]
      _ ≤ 2 ^ n * ∫⁻ z in Q, g z := by
          gcongr
          calc ENNReal.ofReal |(s ^ n)⁻¹| = ENNReal.ofReal s⁻¹ ^ n := by
                rw [abs_of_pos (by positivity), ← inv_pow, ENNReal.ofReal_pow (by positivity)]
            _ ≤ ENNReal.ofReal 2 ^ n := by gcongr
            _ = 2 ^ n := by rw [ENNReal.ofReal_ofNat]
  -- the integrand is jointly measurable
  have hmeas : Measurable (fun p : Euclid n × Euclid n => g ((1 - t) • p.2 + t • p.1)) :=
    hg.comp (by fun_prop)
  rcases le_total (1 / 2 : ℝ) t with h | h
  · -- `t ≥ 1/2`: Tonelli, then change variables in `x` with `c = (1 - t) • y`, `s = t`
    rw [lintegral_lintegral_swap (f := fun x y => g ((1 - t) • y + t • x)) hmeas.aemeasurable]
    calc ∫⁻ y in Q, ∫⁻ x in Q, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in Q, 2 ^ n * ∫⁻ z in Q, g z := by
          refine setLIntegral_mono' hQm fun y hy => ?_
          refine key ((1 - t) • y) t h fun v hv => ?_
          exact hQc hy hv (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          rw [setLIntegral_const]
          ring
  · -- `t ≤ 1/2`: change variables in `y` with `c = t • x`, `s = 1 - t`
    calc ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in Q, 2 ^ n * ∫⁻ z in Q, g z := by
          refine setLIntegral_mono' hQm fun x hx => ?_
          calc ∫⁻ y in Q, g ((1 - t) • y + t • x)
              = ∫⁻ y in Q, g (t • x + (1 - t) • y) :=
                lintegral_congr fun y => by rw [add_comm]
            _ ≤ 2 ^ n * ∫⁻ z in Q, g z := by
                refine key (t • x) (1 - t) (by linarith) fun v hv => ?_
                rw [add_comm]
                exact hQc hv hx (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          rw [setLIntegral_const]
          ring

/-- **Poincaré inequality for `C¹` functions on a convex set.**  If `Q ⊆ ℝⁿ` is convex and
measurable, `‖x - y‖ ≤ d` on `Q` and `v` is `C¹`, then
`∫_Q ∫_Q |v(x) - v(y)| ≤ 2ⁿ d Lⁿ(Q) ∫_Q ‖Dv‖`.  For `x, y ∈ Q`,
`cmcdt_cbm_sp_segment_bound` and `‖x - y‖ ≤ d` give
`|v(x) - v(y)| ≤ d ∫₀¹ ‖Dv((1 - t)y + tx)‖ dt`.  Integrate over `Q × Q` and move the
`t`-integral outside (Tonelli); then `cmcdt_cbm_sp_convex_slice_bound` bounds each slice by
`2ⁿ Lⁿ(Q) ∫_Q ‖Dv‖`.  As `Q` is bounded and `‖Dv‖` is continuous, the bound is finite, so it
passes from `ℝ≥0∞` to `ℝ`. -/
theorem Submission.cmcdt_cbm_sp_convex_poincare : ∀ (n : ℕ) (Q : Set (Euclid n)) (v : Euclid n → ℝ) (d : ℝ), Convex ℝ Q → MeasurableSet Q → 0 ≤ d → (∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ d) → ContDiff ℝ 1 v → ∫ x in Q, ∫ y in Q, |v x - v y| ≤ 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
  intro n Q v d hQc hQm hd hdiam hv
  have hseg := Submission.cmcdt_cbm_sp_segment_bound n v
  have hslice := Submission.cmcdt_cbm_sp_convex_slice_bound n Q
  have hcont : Continuous v := hv.continuous
  -- Step 1: `Q` is bounded, so `Lⁿ(Q) < ∞`, and `∫_Q g < ∞` for `g = ofReal ‖Dv‖`
  have hFc : Continuous fun z => ‖fderiv ℝ v z‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hQb : Bornology.IsBounded Q :=
    Metric.isBounded_iff.2 ⟨d, fun x hx y hy => by rw [dist_eq_norm]; exact hdiam x hx y hy⟩
  have hQfin : volume Q < ∞ := hQb.measure_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ closure Q, ‖‖fderiv ℝ v z‖‖ ≤ C :=
    hQb.isCompact_closure.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal ‖fderiv ℝ v z‖ :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal ‖fderiv ℝ v z‖ := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hFc.measurable.ennreal_ofReal
  have hJ : ∫⁻ z in Q, g z ≠ ∞ := by
    have h1 : ∫⁻ z in Q, g z ≤ ∫⁻ _ in Q, ENNReal.ofReal C :=
      setLIntegral_mono' hQm fun z hz => by
        rw [hgx]
        exact ENNReal.ofReal_le_ofReal (by simpa using hC z (subset_closure hz))
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin)).ne
  -- Step 2: for `x, y ∈ Q`, `|v x - v y| ≤ d ∫_(0,1] ‖Dv((1 - t) y + t x)‖ dt`
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    intro x hx y hy
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => norm_nonneg _
    have h1 : |v x - v y| ≤ d * G :=
      (hseg x y hv).trans (mul_le_mul_of_nonneg_right (hdiam x hx y hy) hG)
    -- `G` is the integral over `(0, 1]` of a nonnegative function
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ v ((1 - t) • y + t • x)‖)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hFc.comp h).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => norm_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal |v x - v y| ≤ ENNReal.ofReal (d * G) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal d * ENNReal.ofReal G := ENNReal.ofReal_mul hd
      _ ≤ _ := by gcongr
  -- Step 3: Tonelli moves the `t`-integral outside
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in Q, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in Q, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in Q, g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  -- Step 4: integrate step 2 over `Q × Q` and bound each slice by `convex_slice_bound`
  have hI : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y|
        ≤ ∫⁻ x in Q, ∫⁻ y in Q,
            ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => hpt x hx y hy
      _ = ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q,
            g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [hswap]
      _ ≤ ENNReal.ofReal d * ∫⁻ _ in Ioc (0 : ℝ) 1, 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hQc hQm hg t (Ioc_subset_Icc_self ht)) _
      _ = ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  -- Step 5: the bound is finite, so it passes to Bochner integrals
  have hK : Measurable fun x : Euclid n => ∫⁻ y in Q, ENNReal.ofReal |v x - v y| := by
    have h : Continuous fun p : Euclid n × Euclid n => |v p.1 - v p.2| := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal |v p.1 - v p.2|)
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in Q, |v x - v y| =
      (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => abs_nonneg _)
      (by fun_prop : Continuous fun y => |v x - v y|).aestronglyMeasurable
  have hrhs : ∫ z in Q, ‖fderiv ℝ v z‖ = (∫⁻ z in Q, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => norm_nonneg _)
      hFc.aestronglyMeasurable]
    simp only [hgx]
  have hfin : ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hQfin.ne) hJ)
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      = ∫ x in Q, (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := by simp only [hinner]
    _ = (∫⁻ x in Q, ENNReal.ofReal (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z)).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hd]
        ring
/-- **Geometry of the open cube** `Q_δ = {z : δ < zᵢ < 1 − δ for all i} ⊂ ℝⁿ`, `δ ≥ 0`.  `Q_δ` is
convex (coordinatewise convex combinations), measurable (a finite intersection of sets cut out by
the continuous coordinates), has diameter at most `√n` (`|xᵢ − yᵢ| < 1 − 2δ ≤ 1`), and
`Lⁿ(Q_δ) ≤ 1`, since `Q_δ ⊆ ofLp⁻¹(∏ᵢ (0, 1))` and `ofLp` is measure preserving. -/
theorem Submission.cmcdt_cbm_sp_cube_geometry : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → Convex ℝ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ∧ MeasurableSet {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ∧ (∀ x ∈ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}, ∀ y ∈ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖x - y‖ ≤ Real.sqrt n) ∧ volume {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ≤ 1 := by
  intro n δ hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- convexity: `a xᵢ + b yᵢ − δ = a (xᵢ − δ) + b (yᵢ − δ) > 0`, and likewise below `1 − δ`
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab i => ?_
    have hxi := hx i
    have hyi := hy i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    constructor
    · nlinarith [mul_pos ha (sub_pos.2 hxi.1), mul_pos hb (sub_pos.2 hyi.1)]
    · nlinarith [mul_pos ha (sub_pos.2 hxi.2), mul_pos hb (sub_pos.2 hyi.2)]
  · -- measurability: `Q_δ = ⋂ᵢ {δ < zᵢ} ∩ {zᵢ < 1 − δ}` with continuous coordinates
    have hc : ∀ i : Fin n, Continuous fun z : Euclid n => z i := fun i => by fun_prop
    have : {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} =
        ⋂ i, ({z : Euclid n | δ < z i} ∩ {z : Euclid n | z i < 1 - δ}) := by
      ext z; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hc i).measurable).inter
        (measurableSet_lt (hc i).measurable measurable_const)
  · -- diameter: `(xᵢ − yᵢ)² ≤ 1` for each `i`, so `‖x − y‖ ≤ √(∑ᵢ 1) = √n`
    intro x hx y hy
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖(x - y) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hxi := hx i
          have hyi := hy i
          simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = n := by simp
  · -- volume: `Q_δ ⊆ ofLp⁻¹(∏ᵢ (0, 1))`, and `ofLp` is measure preserving
    have hsub : {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆
        WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) := by
      intro z hz
      simp only [mem_preimage, mem_univ_pi, mem_Ioo]
      intro i
      exact ⟨by linarith [(hz i).1], by linarith [(hz i).2]⟩
    calc volume {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}
        ≤ volume (WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) : Set (Euclid n)) :=
          measure_mono hsub
      _ = volume (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) :=
          (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
            (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet
      _ = 1 := by rw [Real.volume_pi_Ioo]; simp

/-- **Poincaré inequality for `C¹` functions on the cube** `Q_δ = {z : δ < zᵢ < 1 − δ for all i}`
`⊂ ℝⁿ`, `n = m + 1`, `δ ≥ 0`: `∫_{Q_δ} ∫_{Q_δ} |v(x) − v(y)| dy dx ≤ 2ⁿ √n ∫_{Q_δ} ‖Dv‖`.  `Q_δ` is
convex and measurable, with diameter at most `√n` and `Lⁿ(Q_δ) ≤ 1`; the convex Poincaré
inequality with `d = √n` bounds the left side by `2ⁿ √n Lⁿ(Q_δ) ∫_{Q_δ} ‖Dv‖ ≤ 2ⁿ √n ∫_{Q_δ} ‖Dv‖`.
-/
theorem Submission.cmcdt_cbm_smooth_poincare : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x - v y| ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v δ hv hδ
  obtain ⟨hconv, hmeas, hdiam, hvol⟩ := Submission.cmcdt_cbm_sp_cube_geometry (m + 1) δ hδ
  set Q := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  have hvol' : (volume Q).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      ≤ 2 ^ (m + 1) * Real.sqrt ↑(m + 1) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ :=
        -- the convex Poincaré inequality with `d = √n`
        Submission.cmcdt_cbm_sp_convex_poincare (m + 1) Q v (Real.sqrt ↑(m + 1)) hconv hmeas
          (Real.sqrt_nonneg _) hdiam hv
    _ ≤ 2 ^ (m + 1) * Real.sqrt ↑(m + 1) * 1 * ∫ x in Q, ‖fderiv ℝ v x‖ := by gcongr
    _ = 2 ^ (m + 1) * Real.sqrt (m + 1) * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        rw [mul_one, Nat.cast_add_one]
/-- The open unit cube `Q₁ = {y : 0 < yᵢ < 1 for all i}` of `ℝᵏ` has Lebesgue measure `1`: it is
the preimage of the box `∏ᵢ (0, 1)` under the measure-preserving coordinate map
`ofLp : ℝᵏ → (Fin k → ℝ)`, and `vol ∏ᵢ (0, 1) = ∏ᵢ (1 − 0) = 1` (the empty product if `k = 0`). -/
theorem Submission.cmcdt_cbm_im_cube_volume : ∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro k
  -- `Q₁` is the preimage under `ofLp` of the measurable box `B = ∏ᵢ (0, 1)`
  have hB : MeasurableSet (univ.pi fun _ : Fin k => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQ : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin k => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  -- `ofLp` preserves volume, and `vol B = ∏ᵢ ofReal (1 - 0) = 1`
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hB.nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp
/-- **Simon, proof of Ch. 6, 5.1, (31)** (integer median): an integer-valued `μ`-a.e.-measurable
`u` on a probability space has an integer `β` with `μ{u ≥ β} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`.
`F(t) = μ{u ≤ t}` is nondecreasing, tends to `1` along `ℕ` (continuity from below) and to `0`
along `−ℕ` (continuity from above, the sets `{u ≤ t}` being `μ`-null-measurable), so
`{z ∈ ℤ : F(z) ≥ 1/2}` has a least element `β`; then `F(β − 1) < 1/2`, and as `u` is
integer-valued, `{u ≥ β} = {u ≤ β − 1}ᶜ` has measure `1 − F(β − 1) > 1/2`. -/
theorem Submission.cmcdt_cbm_im_integer_median_exists : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ), IsProbabilityMeasure μ → AEMeasurable u μ → (∀ x, ∃ z : ℤ, u x = z) → ∃ β : ℤ, 1 / 2 ≤ μ.real {x | (β : ℝ) ≤ u x} ∧ 1 / 2 ≤ μ.real {x | u x ≤ (β : ℝ)} := by
  intro X _ μ u _ hu hint
  -- the sublevel sets `{u ≤ t}` are null-measurable, and `F(t) = μ{u ≤ t}` is nondecreasing
  have hnm : ∀ t : ℝ, NullMeasurableSet {x | u x ≤ t} μ := fun t =>
    hu.nullMeasurableSet_preimage measurableSet_Iic
  have hmono : ∀ s t : ℝ, s ≤ t → μ.real {x | u x ≤ s} ≤ μ.real {x | u x ≤ t} :=
    fun s t hst => measureReal_mono fun x (hx : u x ≤ s) => hx.trans hst
  -- upper tail: `F(n) → 1` (continuity from below)
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, 1 / 2 < μ.real {x | u x ≤ (n : ℝ)} := by
    have hm : Monotone fun n : ℕ => {x | u x ≤ (n : ℝ)} :=
      fun m n hmn x (hx : u x ≤ m) => hx.trans (Nat.cast_le.mpr hmn)
    have hU : (⋃ n : ℕ, {x | u x ≤ (n : ℝ)}) = univ :=
      eq_univ_of_forall fun x => mem_iUnion.mpr (exists_nat_ge (u x))
    have h := tendsto_measure_iUnion_atTop (μ := μ) hm
    rw [hU, measure_univ] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
    rw [ENNReal.toReal_one] at h'
    exact (h'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
  -- lower tail: `F(-n) → 0` (continuity from above)
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, μ.real {x | u x ≤ -(n : ℝ)} < 1 / 2 := by
    have hm : Antitone fun n : ℕ => {x | u x ≤ -(n : ℝ)} :=
      fun m n hmn x (hx : u x ≤ -(n : ℝ)) => hx.trans (neg_le_neg (Nat.cast_le.mpr hmn))
    have hI : (⋂ n : ℕ, {x | u x ≤ -(n : ℝ)}) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (-u x)
      have hxn : u x ≤ -(n : ℝ) := mem_iInter.mp hx n
      linarith
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => hnm _) hm ⟨0, measure_ne_top _ _⟩
    rw [hI, measure_empty] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    exact (h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  -- `β`: the least integer `z` with `F(z) ≥ 1/2`
  obtain ⟨β, hβ, hβmin⟩ := Int.exists_least_of_bdd
    (P := fun z : ℤ => 1 / 2 ≤ μ.real {x | u x ≤ (z : ℝ)})
    ⟨-(n₀ : ℤ), fun z hz => by
      by_contra hlt
      have hz' : (z : ℝ) ≤ -(n₀ : ℝ) := by exact_mod_cast (not_le.mp hlt).le
      linarith [hmono _ _ hz']⟩
    ⟨n₁, by exact_mod_cast hn₁.le⟩
  refine ⟨β, ?_, hβ⟩
  -- `F(β - 1) < 1/2` by minimality
  have hβ1 : μ.real {x | u x ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 := by
    by_contra h
    have := hβmin (β - 1) (not_lt.mp h)
    omega
  -- `u` is integer-valued, so `{β ≤ u} = {u ≤ β - 1}ᶜ`
  have hset : {x | (β : ℝ) ≤ u x} = {x | u x ≤ ((β - 1 : ℤ) : ℝ)}ᶜ := by
    ext x
    obtain ⟨z, hz⟩ := hint x
    rw [mem_compl_iff, mem_ofPred, mem_ofPred, hz, Int.cast_le, Int.cast_le]
    omega
  rw [hset, probReal_compl_eq_one_sub₀ (hnm _)]
  linarith
/-- **A median minimizes the mean absolute deviation.**  If `μ` is a probability measure, `u` is
`μ`-integrable and `β` is a median of `u` (`μ{β ≤ u} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`), then
`∫ |u − β| dμ ≤ ∫ |u − c| dμ` for every `c`.  For `c ≥ β` take `s = {u ≤ β}`, `d = c − β`; for
`c < β` take `s = {β ≤ u}`, `d = β − c`.  Then `|u − c| − |u − β|` equals `d` on `s` and is
`≥ −d` off `s` (triangle inequality), so integrating `d (2·1_s − 1) ≤ |u − c| − |u − β|` gives
`∫ |u − c| − ∫ |u − β| ≥ d (2μ(s) − 1) ≥ 0`. -/
theorem Submission.cmcdt_cbm_im_median_minimizes : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → ∀ c : ℝ, ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ := by
  intro X _ μ u β _ hu hge hle c
  -- every `|u − a|` is integrable
  have hint : ∀ a : ℝ, Integrable (fun x => |u x - a|) μ := fun a =>
    (hu.sub (integrable_const a)).abs
  -- key step: integrate `d (2·1_s − 1) ≤ |u − c| − |u − β|`, using `μ(s) ≥ 1/2` and `d ≥ 0`
  have key : ∀ s : Set X, NullMeasurableSet s μ → 1 / 2 ≤ μ.real s → ∀ d : ℝ, 0 ≤ d →
      (∀ x, s.indicator (fun _ => 2 * d) x - d ≤ |u x - c| - |u x - β|) →
      ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ := by
    intro s hs hs2 d hd hpt
    have hind : Integrable (s.indicator fun _ => 2 * d) μ :=
      (integrable_const (2 * d)).indicator₀ hs
    have h : ∫ x, (s.indicator (fun _ => 2 * d) x - d) ∂μ ≤ ∫ x, (|u x - c| - |u x - β|) ∂μ :=
      integral_mono (hind.sub (integrable_const d)) ((hint c).sub (hint β)) hpt
    rw [integral_sub hind (integrable_const d), integral_sub (hint c) (hint β),
      integral_indicator₀ hs, setIntegral_const, integral_const, probReal_univ, smul_eq_mul,
      smul_eq_mul, one_mul] at h
    nlinarith
  rcases le_or_gt β c with hc | hc
  · -- `c ≥ β`: `s = {u ≤ β}`, `d = c − β`
    refine key {x | u x ≤ β} (hu.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic) hle
      (c - β) (sub_nonneg.mpr hc) fun x => ?_
    by_cases hx : u x ≤ β
    · rw [indicator_of_mem (show x ∈ {x | u x ≤ β} from hx), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
    · rw [indicator_of_notMem (show x ∉ {x | u x ≤ β} from hx)]
      have := abs_sub_le (u x) c β
      rw [abs_of_nonneg (sub_nonneg.mpr hc)] at this
      linarith
  · -- `c < β`: `s = {β ≤ u}`, `d = β − c`
    refine key {x | β ≤ u x} (hu.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici) hge
      (β - c) (sub_nonneg.mpr hc.le) fun x => ?_
    by_cases hx : β ≤ u x
    · rw [indicator_of_mem (show x ∈ {x | β ≤ u x} from hx), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
    · rw [indicator_of_notMem (show x ∉ {x | β ≤ u x} from hx)]
      have := abs_sub_le (u x) c β
      rw [abs_of_nonpos (sub_nonpos.mpr hc.le)] at this
      linarith
/-- **Simon Ch. 6, proof of 5.1, (35)**: a median `β` of an integrable `u` on a probability space
(`μ{β ≤ u} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`, Simon's (31)) satisfies `|β| ≤ 2 ∫ |u| dμ`.  According to
the sign of `β`, one of the two median halves lies in `{|β| ≤ |u|}`, so Markov's inequality for
`|u|` at level `|β|` gives `|β| / 2 ≤ ∫ |u| dμ`. -/
theorem Submission.cmcdt_cbm_im_median_abs_le : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → |β| ≤ 2 * ∫ x, |u x| ∂μ := by
  intro X _ μ u β _ hu hge hle
  -- Markov's inequality for `|u|` at level `|β|`
  have hM : |β| * μ.real {x | |β| ≤ |u x|} ≤ ∫ x, |u x| ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg (u x)) hu.abs |β|
  -- one of the two median halves lies in `{|β| ≤ |u|}`
  have hhalf : 1 / 2 ≤ μ.real {x | |β| ≤ |u x|} := by
    rcases le_or_gt 0 β with hβ | hβ
    · refine hge.trans (measureReal_mono fun x (hx : β ≤ u x) => ?_)
      show |β| ≤ |u x|
      rw [abs_of_nonneg hβ, abs_of_nonneg (hβ.trans hx)]
      exact hx
    · refine hle.trans (measureReal_mono fun x (hx : u x ≤ β) => ?_)
      show |β| ≤ |u x|
      rw [abs_of_neg hβ, abs_of_neg (hx.trans_lt hβ)]
      exact neg_le_neg hx
  linarith [mul_le_mul_of_nonneg_left hhalf (abs_nonneg β)]
/-- **Simon, proof of Ch. 6, 5.1, (31) and (35)** (integer median on the unit cube): an
integer-valued `u` integrable on `Q₁ = (0, 1)ⁿ` has an integer median `β`, which minimizes
`c ↦ ∫_{Q₁} |u − c|` and satisfies `|β| ≤ 2 ∫_{Q₁} |u|`.  As `vol(Q₁) = 1`, `μ = vol⌞Q₁` is a
probability measure; `β` is an integer median of `u` for `μ`, and a median minimizes the mean
absolute deviation and is bounded by twice the mean of `|u|`. -/
theorem Submission.cmcdt_cbm_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, (∀ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c|) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hint hu
  -- `μ = vol⌞Q₁` is a probability measure, since `vol(Q₁) = 1`
  have hμ : IsProbabilityMeasure
      (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.cmcdt_cbm_im_cube_volume]⟩
  -- an integer median `β` of `u` for `μ`
  obtain ⟨β, hge, hle⟩ := Submission.cmcdt_cbm_im_integer_median_exists _ _ u hμ
    hu.integrable.aemeasurable hint
  -- `β` minimizes `c ↦ ∫_{Q₁} |u − c|` and `|β| ≤ 2 ∫_{Q₁} |u|`
  exact ⟨β, Submission.cmcdt_cbm_im_median_minimizes _ _ u β hμ hu hge hle,
    Submission.cmcdt_cbm_im_median_abs_le _ _ u β hμ hu hge hle⟩
/-- **Continuous functions are integrable on open boxes** (fact (F3) in the proof of the smooth
trace estimate on a cube, cf. Simon 2.8–2.9).  The open box `{z : a < z_j < b ∀ j}` lies in the
image under `toLp 2` of the closed order interval `Icc (fun _ => a) (fun _ => b)` of
`Fin n → ℝ`, which is compact, and a continuous function is integrable on a compact set
(`ContinuousOn.integrableOn_compact`). -/
theorem Submission.cmcdt_cbm_st_box_integrableOn : ∀ (n : ℕ) (h : Euclid n → ℝ) (a b : ℝ), Continuous h → IntegrableOn h {z : Euclid n | ∀ j, a < z j ∧ z j < b} := by
  intro n h a b hh
  -- the open box lies in the closed box `K = toLp '' Icc (fun _ => a) (fun _ => b)`
  have hsub : {z : Euclid n | ∀ j, a < z j ∧ z j < b} ⊆
      (WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ)) :=
    fun z hz => ⟨z.ofLp, ⟨fun j => (hz j).1.le, fun j => (hz j).2.le⟩, rfl⟩
  -- `K` is compact: a closed order interval of `Fin n → ℝ` under the continuous map `toLp 2`
  have hKc : IsCompact ((WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  exact (hh.continuousOn.integrableOn_compact hKc).mono_set hsub
/-- Coordinate slicing (Fubini in the `i`-th coordinate) on the open cube
`Q = {z : a < z_j < b ∀ j}` of `ℝ^{m+1}`.  Write `ι(t, y) = toLp 2 (Fin.insertNth i t y)` (the
point with `i`-th coordinate `t` and remaining coordinates `y`) and `Q' = {y : a < y_k < b ∀ k}`
in `ℝ^m`.  If `a ≤ b` and `h` is integrable on `Q`, then `y ↦ ∫_a^b h(ι(t, y)) dt` is integrable
on `Q'` and `∫_Q h = ∫_{Q'} ∫_a^b h(ι(t, y)) dt dy`.  `(t, y) ↦ ι(t, y)` is the inverse of
`MeasurableEquiv.piFinSuccAbove` followed by `toLp 2`, a measure-preserving equivalence
`ℝ × ℝ^m ≃ ℝ^{m+1}` that maps `(a, b) × Q'` onto `Q`; then use Fubini with outer variable `y`. -/
theorem Submission.cmcdt_cbm_st_slice_integral : ∀ (m : ℕ) (i : Fin (m + 1)) (a b : ℝ) (h : Euclid (m + 1) → ℝ), a ≤ b → IntegrableOn h {z : Euclid (m + 1) | ∀ j, a < z j ∧ z j < b} → IntegrableOn (fun y : Fin m → ℝ => ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y))) {y : Fin m → ℝ | ∀ j, a < y j ∧ y j < b} ∧ ∫ x in {z : Euclid (m + 1) | ∀ j, a < z j ∧ z j < b}, h x = ∫ y in {y : Fin m → ℝ | ∀ j, a < y j ∧ y j < b}, ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
  intro m i a b h hab hint
  set Q : Set (Euclid (m + 1)) := {z | ∀ j, a < z j ∧ z j < b} with hQ
  set Q' : Set (Fin m → ℝ) := {y | ∀ j, a < y j ∧ y j < b} with hQ'
  -- `E (t, y) = toLp 2 (insertNth i t y)`: a measure-preserving equivalence `ℝ × ℝ^m ≃ ℝ^{m+1}`
  let E : ℝ × (Fin m → ℝ) ≃ᵐ Euclid (m + 1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm.trans
      (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ))
  have hE : MeasurePreserving E (volume.prod volume) volume :=
    (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
  have hEapply : ∀ p : ℝ × (Fin m → ℝ), E p = WithLp.toLp 2 (Fin.insertNth i p.1 p.2) :=
    fun p => rfl
  -- `E⁻¹(Q) = (a, b) × Q'`
  have hpre : E ⁻¹' Q = Ioo a b ×ˢ Q' := by
    ext ⟨t, y⟩
    simp only [Set.mem_preimage, hEapply, Q, Q', Set.mem_prod, Set.mem_Ioo, Set.mem_ofPred_eq]
    rw [Fin.forall_iff_succAbove i]
    simp
  have hint' : Integrable (fun p => h (E p))
      ((volume.restrict (Ioo a b)).prod (volume.restrict Q')) := by
    rw [Measure.prod_restrict, ← hpre]
    exact (hE.integrableOn_comp_preimage E.measurableEmbedding).2 hint
  -- for `a ≤ b` the inner integral over `(a, b)` is the interval integral `∫_a^b`
  have hinner : ∀ y : Fin m → ℝ, ∫ t in Ioo a b, h (E (t, y)) =
      ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
    intro y
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    rfl
  refine ⟨?_, ?_⟩
  · have := hint'.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ x in Q, h x = ∫ p in E ⁻¹' Q, h (E p) ∂(volume.prod volume) :=
          (hE.setIntegral_preimage_emb E.measurableEmbedding h Q).symm
      _ = ∫ p, h (E p) ∂((volume.restrict (Ioo a b)).prod (volume.restrict Q')) := by
          rw [hpre, Measure.prod_restrict]
      _ = ∫ y in Q', ∫ t in Ioo a b, h (E (t, y)) := integral_prod_symm _ hint'
      _ = ∫ y in Q', ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
          simp only [hinner]
/-- **One-dimensional boundary term and trace estimate** (the one-dimensional core of the trace
estimate behind Simon Ch. 2, 2.8–2.9).  If `a < b`, `φ, γ` are `C¹` and `|γ| ≤ 1`, then
`|∫_a^b (φγ)'| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|`.  By the fundamental theorem of calculus
the left side is `|φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(a)| + |φ(b)|`.  For `c, t ∈ [a, b]`,
`|φ(c)| ≤ |φ(t)| + ∫_a^b |φ'|`; averaging over `t ∈ [a, b]` gives
`|φ(c)| ≤ (b − a)⁻¹ ∫_a^b |φ| + ∫_a^b |φ'|`, applied at `c = a` and `c = b`. -/
theorem Submission.cmcdt_cbm_st_interval_bound : ∀ (φ γ : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 γ → (∀ t, |γ t| ≤ 1) → a < b → |∫ t in a..b, deriv (fun s => φ s * γ s) t| ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
  intro φ γ a b hφ hγ hγb hab
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hpc : ContDiff ℝ 1 (fun s => φ s * γ s) := hφ.mul hγ
  -- Step 1: fundamental theorem of calculus for the product
  have hftc : ∫ t in a..b, deriv (fun s => φ s * γ s) t = φ b * γ b - φ a * γ a :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => (hpc.differentiable one_ne_zero) t)
      ((hpc.continuous_deriv le_rfl).intervalIntegrable _ _)
  -- Step 2: the one-dimensional trace inequality at a point `c ∈ [a, b]`
  have htrace : ∀ c ∈ Icc a b,
      |φ c| ≤ (b - a)⁻¹ * (∫ t in a..b, |φ t|) + ∫ t in a..b, |deriv φ t| := by
    intro c hc
    set D := ∫ t in a..b, |deriv φ t| with hD
    -- 2a: `|φ(c)| ≤ |φ(t)| + D` for `t ∈ [a, b]`, by FTC on the segment between `t` and `c`
    have hpt : ∀ t ∈ Icc a b, |φ c| ≤ |φ t| + D := by
      intro t ht
      have hsub : φ c - φ t = ∫ s in t..c, deriv φ s :=
        (intervalIntegral.integral_deriv_eq_sub (fun s _ => hφd s)
          (hφ'c.intervalIntegrable _ _)).symm
      have hle : |∫ s in t..c, deriv φ s| ≤ D := by
        have habs : |∫ s in t..c, deriv φ s| ≤ |∫ s in t..c, (|deriv φ s|)| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_abs_integral_norm (f := deriv φ) (a := t) (b := c)
              (μ := volume))
        refine habs.trans ?_
        rcases le_total t c with htc | hct
        · rw [abs_of_nonneg (intervalIntegral.integral_nonneg htc fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval ht.1 htc hc.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
        · rw [intervalIntegral.integral_symm, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg hct fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval hc.1 hct ht.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
      calc |φ c| = |φ t + (φ c - φ t)| := by ring_nf
        _ ≤ |φ t| + |φ c - φ t| := abs_add_le _ _
        _ ≤ |φ t| + D := by rw [hsub]; gcongr
    -- 2b: average over `t ∈ [a, b]`
    have hint : ∫ t in a..b, |φ c| ≤ ∫ t in a..b, (|φ t| + D) :=
      intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
        ((hφd.continuous.abs.add continuous_const).intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const, intervalIntegral.integral_add
      (hφd.continuous.abs.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at hint
    -- 2c: divide by `b - a > 0`
    have hba : 0 < b - a := sub_pos.mpr hab
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hba]
    nlinarith
  -- Step 3: `|φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(b)| + |φ(a)|`, then Step 2 at `c = a` and `c = b`
  have hA := htrace a ⟨le_rfl, hab.le⟩
  have hB := htrace b ⟨hab.le, le_rfl⟩
  rw [hftc]
  have hγa := hγb a
  have hγb' := hγb b
  calc |φ b * γ b - φ a * γ a| ≤ |φ b * γ b| + |φ a * γ a| := abs_sub _ _
    _ = |φ b| * |γ b| + |φ a| * |γ a| := by rw [abs_mul, abs_mul]
    _ ≤ |φ b| * 1 + |φ a| * 1 := by gcongr
    _ = |φ b| + |φ a| := by ring
    _ ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
        have : 2 / (b - a) = (b - a)⁻¹ + (b - a)⁻¹ := by ring
        rw [this]; linarith

/-- **One-coordinate divergence and trace estimate on `Q_δ`** (steps 2–4 of the smooth trace
estimate on a cube, cf. Simon 2.8–2.9).  For `C¹` functions `v, g` on `ℝ^{m+1}` with `|g| ≤ 1` and
`0 ≤ δ ≤ 1/4`, `|∫_{Q_δ} D(vg)(x)e_i dx| ≤ 4 ∫_{Q_δ} |v| + 2 ∫_{Q_δ} ‖Dv‖`.  Slice `Q_δ` along the
coordinate `i` (`cmcdt_cbm_st_slice_integral`); on each line `t ↦ ι(t, y)` the one-dimensional
boundary and trace estimate (`cmcdt_cbm_st_interval_bound`) applies, the side length
`1 − 2δ ≥ 1/2` gives `2/(1 − 2δ) ≤ 4`, and `|Dv(x)e_i| ≤ ‖Dv(x)‖`; then integrate over the
slice variable `y`. -/
theorem Submission.cmcdt_cbm_st_coord_bound : ∀ (m : ℕ) (v g : Euclid (m + 1) → ℝ) (i : Fin (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 g → (∀ y, |g y| ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)| ≤ 4 * (∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, |v x|) + 2 * ∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v g i δ hv hg hgb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ} with hQ
  set Q' : Set (Fin m → ℝ) := {y : Fin m → ℝ | ∀ j, δ < y j ∧ y j < 1 - δ} with hQ'
  have hab : δ < 1 - δ := by linarith
  -- the line `t ↦ ι t y` through the slice point `y` in direction `e_i`
  set ι : ℝ → (Fin m → ℝ) → Euclid (m + 1) := fun t y => WithLp.toLp 2 (Fin.insertNth i t y)
    with hι
  have hι_affine : ∀ t y, ι t y = ι 0 y + t • EuclideanSpace.single i 1 := by
    intro t y
    ext j
    induction j using Fin.succAboveCases i with
    | x => simp [ι]
    | p j => simp [ι, Fin.succAbove_ne]
  have hι_deriv : ∀ t y, HasDerivAt (fun s => ι s y) (EuclideanSpace.single i 1) t := by
    intro t y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (ι 0 y)
  have hι_cd : ∀ y, ContDiff ℝ 1 (fun s => ι s y) := by
    intro y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hvg : ContDiff ℝ 1 (fun y => v y * g y) := hv.mul hg
  set F : Euclid (m + 1) → ℝ := fun x => fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)
    with hF
  set H : Euclid (m + 1) → ℝ := fun x => 4 * |v x| + 2 * ‖fderiv ℝ v x‖ with hH
  have hFc : Continuous F := (hvg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvc : Continuous fun x => |v x| := hv.continuous.abs
  have hDvc : Continuous fun x => ‖fderiv ℝ v x‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hHc : Continuous H := (continuous_const.mul hvc).add (continuous_const.mul hDvc)
  obtain ⟨-, hFslice⟩ := Submission.cmcdt_cbm_st_slice_integral m i δ (1 - δ) F hab.le
    (Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hFc)
  obtain ⟨hHint, hHslice⟩ := Submission.cmcdt_cbm_st_slice_integral m i δ (1 - δ) H hab.le
    (Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hHc)
  have hHsplit : ∫ x in Q, H x = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [integral_add ((Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hvc).const_mul 4)
      ((Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hDvc).const_mul 2),
      integral_const_mul, integral_const_mul]
  -- the one-dimensional estimate on each line
  have hline : ∀ y, |∫ t in δ..(1 - δ), F (ι t y)| ≤ ∫ t in δ..(1 - δ), H (ι t y) := by
    intro y
    have hφ : ContDiff ℝ 1 (fun s => v (ι s y)) := hv.comp (hι_cd y)
    have hγ : ContDiff ℝ 1 (fun s => g (ι s y)) := hg.comp (hι_cd y)
    have hderiv_prod : ∀ t, deriv (fun s => v (ι s y) * g (ι s y)) t = F (ι t y) := by
      intro t
      have := ((hvg.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have hderiv_v : ∀ t, deriv (fun s => v (ι s y)) t =
        fderiv ℝ v (ι t y) (EuclideanSpace.single i 1) := by
      intro t
      have := ((hv.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have h1 := Submission.cmcdt_cbm_st_interval_bound (fun s => v (ι s y)) (fun s => g (ι s y))
      δ (1 - δ) hφ hγ (fun t => hgb _) hab
    simp only [hderiv_prod, hderiv_v] at h1
    have hcoef : 2 / (1 - δ - δ) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hint_nonneg : 0 ≤ ∫ t in δ..(1 - δ), |v (ι t y)| :=
      intervalIntegral.integral_nonneg hab.le fun t _ => abs_nonneg _
    have hcont_v : Continuous fun t => |v (ι t y)| := hφ.continuous.abs
    have hcont_Dv : Continuous fun t => ‖fderiv ℝ v (ι t y)‖ := hDvc.comp (hι_cd y).continuous
    have hcont_dv : Continuous fun t => |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| :=
      (((hv.continuous_fderiv one_ne_zero).comp (hι_cd y).continuous).clm_apply
        continuous_const).abs
    have hmono : ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| ≤
        ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      refine intervalIntegral.integral_mono_on hab.le (hcont_dv.intervalIntegrable _ _)
        (hcont_Dv.intervalIntegrable _ _) fun t _ => ?_
      have := (fderiv ℝ v (ι t y)).le_opNorm (EuclideanSpace.single i 1)
      rw [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] at this
      exact this
    have hHline : ∫ t in δ..(1 - δ), H (ι t y) =
        4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      simp only [H]
      rw [intervalIntegral.integral_add ((hcont_v.intervalIntegrable _ _).const_mul 4)
        ((hcont_Dv.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hHline]
    calc |∫ t in δ..(1 - δ), F (ι t y)|
        ≤ 2 / (1 - δ - δ) * (∫ t in δ..(1 - δ), |v (ι t y)|) +
            2 * ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| := h1
      _ ≤ 4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
        gcongr
  calc |∫ x in Q, F x|
      = |∫ y in Q', ∫ t in δ..(1 - δ), F (ι t y)| := by rw [hFslice]
    _ ≤ ∫ y in Q', |∫ t in δ..(1 - δ), F (ι t y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Q', ∫ t in δ..(1 - δ), H (ι t y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hHint
          (Eventually.of_forall hline)
    _ = ∫ x in Q, H x := hHslice.symm
    _ = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := hHsplit
/-- **Product rule for the divergence**, at one point (step 1 of the smooth trace estimate on a
cube, cf. Simon Ch. 2, 2.8).  If `v : ℝⁿ → ℝ` and `G : ℝⁿ → ℝⁿ` (`ℝⁿ = Euclid (m + 1)`) are
differentiable at `x`, then `v(x) div G(x) = Σᵢ Dᵢ(v Gᵢ)(x) − Dv(x) G(x)`, where
`div G(x) = trace DG(x)` and `Dᵢ` is the derivative along `eᵢ = EuclideanSpace.single i 1`.
In the standard orthonormal basis `trace DG(x) = Σᵢ (DG(x) eᵢ)ᵢ`; the product rule gives
`Dᵢ(v Gᵢ)(x) = v(x) (DG(x) eᵢ)ᵢ + Gᵢ(x) Dv(x) eᵢ`, and `Σᵢ Gᵢ(x) Dv(x) eᵢ = Dv(x) G(x)`. -/
theorem Submission.cmcdt_cbm_st_div_product : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (x : Euclid (m + 1)), DifferentiableAt ℝ v x → DifferentiableAt ℝ G x → v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = ∑ i, fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) - fderiv ℝ v x (G x) := by
  intro m v G x hv hG
  -- derivative of the coordinate `Gᵢ = projᵢ ∘ G`
  have hGi : ∀ i : Fin (m + 1), HasFDerivAt (fun y => G y i)
      ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x)) x := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x hG.hasFDerivAt
  -- product rule, evaluated at `eᵢ`
  have hprod : ∀ i : Fin (m + 1),
      fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) =
        v x * (fderiv ℝ G x (EuclideanSpace.single i 1)) i +
          G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    intro i
    have h : HasFDerivAt (fun y => v y * G y i)
        (v x • (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x) +
          G x i • fderiv ℝ v x) x := hv.hasFDerivAt.mul (hGi i)
    rw [h.fderiv]
    simp
  -- trace in the standard orthonormal basis
  have htrace : LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      ∑ i, (fderiv ℝ G x (EuclideanSpace.single i 1)) i := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    simp
  -- `G x = Σᵢ (G x)ᵢ eᵢ`, hence `Dv(x) (G x) = Σᵢ (G x)ᵢ Dv(x) eᵢ`
  have hexp : G x = ∑ i, G x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hDvG : fderiv ℝ v x (G x) = ∑ i, G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hexp]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [htrace, hDvG, Finset.mul_sum]
  simp only [hprod, Finset.sum_add_distrib]
  ring

/-- **Smooth trace estimate on the cube `Q_δ`** (step 5 of the cube BV median estimate, smooth
part; the smooth case of Simon Ch. 2, 2.8–2.9).  Let `n = m + 1`, `0 ≤ δ ≤ 1/4` and
`Q_δ = {y : δ < y_i < 1 − δ ∀ i}`.  For `C¹` maps `v : ℝⁿ → ℝ` and `G : ℝⁿ → ℝⁿ` with `|G| ≤ 1`,
`|∫_{Q_δ} v div G| ≤ (2n + 1) ∫_{Q_δ} ‖Dv‖ + 4n ∫_{Q_δ} |v|`, where `div G = trace DG`.
By the product rule (`cmcdt_cbm_st_div_product`), `v div G = Σᵢ Dᵢ(v Gᵢ) − Dv(G)`, and all terms
are continuous, hence integrable on `Q_δ` (`cmcdt_cbm_st_box_integrableOn`).  Each coordinate
term satisfies `|∫_{Q_δ} Dᵢ(v Gᵢ)| ≤ 4 ∫_{Q_δ} |v| + 2 ∫_{Q_δ} ‖Dv‖` (`cmcdt_cbm_st_coord_bound`
with `g = Gᵢ`, `|Gᵢ| ≤ |G| ≤ 1`), and `|Dv(G)| ≤ ‖Dv‖`.  Summing over the `n` coordinates gives
the bound. -/
theorem Submission.cmcdt_cbm_smooth_trace : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 G → (∀ y, ‖G y‖ ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x)| ≤ (2 * (m + 1) + 1) * (∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖) + 4 * (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x| := by
  intro m v G δ hv hG hGb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} with hQ
  -- the coordinates `Gᵢ` of `G` are `C¹`, with `|Gᵢ| ≤ ‖G‖ ≤ 1`
  have hGi : ∀ i : Fin (m + 1), ContDiff ℝ 1 (fun y => G y i) := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  have hGib : ∀ (i : Fin (m + 1)) (y : Euclid (m + 1)), |G y i| ≤ 1 := fun i y => by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (G y) i).trans (hGb y)
  -- `Fᵢ = Dᵢ(v Gᵢ)`, `D = Dv(G)` and `‖Dv‖` are continuous, hence integrable on `Q_δ`
  set F : Fin (m + 1) → Euclid (m + 1) → ℝ :=
    fun i x => fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) with hF
  set D : Euclid (m + 1) → ℝ := fun x => fderiv ℝ v x (G x) with hD
  have hFc : ∀ i, Continuous (F i) := fun i =>
    ((hv.mul (hGi i)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : Continuous D := (hv.continuous_fderiv one_ne_zero).clm_apply hG.continuous
  have hFint : ∀ i, IntegrableOn (F i) Q := fun i =>
    Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ (hFc i)
  have hDint : IntegrableOn D Q := Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hDc
  have hDvint : IntegrableOn (fun x => ‖fderiv ℝ v x‖) Q :=
    Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ (hv.continuous_fderiv one_ne_zero).norm
  -- step 1: `∫ v div G = Σᵢ ∫ Fᵢ − ∫ D`
  have hpt : ∀ x, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = (∑ i, F i x) - D x :=
    fun x => Submission.cmcdt_cbm_st_div_product m v G x (hv.differentiable one_ne_zero x)
      (hG.differentiable one_ne_zero x)
  have hsplit : ∫ x in Q, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      (∑ i, ∫ x in Q, F i x) - ∫ x in Q, D x := by
    simp only [hpt]
    rw [integral_sub (integrable_finsetSum _ fun i _ => hFint i) hDint,
      integral_finsetSum _ fun i _ => hFint i]
  -- step 2: each coordinate term is bounded by `4 ∫ |v| + 2 ∫ ‖Dv‖`
  have hcoord : ∀ i, |∫ x in Q, F i x| ≤
      4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := fun i =>
    Submission.cmcdt_cbm_st_coord_bound m v (fun y => G y i) i δ hv (hGi i) (hGib i) hδ0 hδ1
  -- step 3: `|∫ Dv(G)| ≤ ∫ ‖Dv‖`, since `‖G‖ ≤ 1`
  have hDbound : |∫ x in Q, D x| ≤ ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hDvint (Eventually.of_forall fun x => ?_)
    calc ‖D x‖ ≤ ‖fderiv ℝ v x‖ * ‖G x‖ := (fderiv ℝ v x).le_opNorm (G x)
      _ ≤ ‖fderiv ℝ v x‖ * 1 := mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _)
      _ = ‖fderiv ℝ v x‖ := mul_one _
  -- step 4: sum over the `m + 1` coordinates
  rw [hsplit]
  calc |(∑ i, ∫ x in Q, F i x) - ∫ x in Q, D x|
      ≤ |∑ i, ∫ x in Q, F i x| + |∫ x in Q, D x| := abs_sub _ _
    _ ≤ (∑ i, |∫ x in Q, F i x|) + |∫ x in Q, D x| :=
        add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ (∑ _i : Fin (m + 1), (4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖)) +
          ∫ x in Q, ‖fderiv ℝ v x‖ :=
        add_le_add (Finset.sum_le_sum fun i _ => hcoord i) hDbound
    _ = (2 * (m + 1) + 1) * (∫ x in Q, ‖fderiv ℝ v x‖) + 4 * (m + 1) * ∫ x in Q, |v x| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Smoothing a field `s` with `|s| ≤ 1` and `s = 0` off `Q_δ` by a nonnegative unit-mass `C^∞`
kernel `ρ` supported in `B_σ(0)`, `σ < δ`, gives a `C^∞` field `ρ ⋆ s` with `|ρ ⋆ s| ≤ 1` whose
topological support is compact and lies in `Q₁` (the mollification step of Simon Ch. 2, 2.5 and
2.7, as used in the proof of the deformation theorem, Ch. 6, 5.1).  The support of `ρ ⋆ s` lies
in the closed box `{δ − σ ≤ y_i ≤ 1 − δ + σ}`, which is compact and contained in `Q₁`. -/
theorem cmcdt_cbm_sa_smoothed_field : ∀ (m : ℕ) (δ σ : ℝ) (ρ : Euclid (m + 1) → ℝ) (s : Euclid (m + 1) → Euclid (m + 1)), 0 < σ → σ < δ → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid (m + 1)) σ → AEStronglyMeasurable s volume → (∀ x, ‖s x‖ ≤ 1) → (∀ x, x ∉ {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} → s x = 0) → ContDiff ℝ (⊤ : ℕ∞) (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ HasCompactSupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ tsupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∧ ∀ y, ‖convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume y‖ ≤ 1 := by
  intro m δ σ ρ s hσ hσδ hρ hρ0 hρ1 hρs hs hs1 hs0
  -- Step 1: `ρ` vanishes off `closedBall 0 σ`, so it has compact support and is integrable.
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) σ) fun x hx => ?_
    by_contra h
    exact hx (ball_subset_closedBall (hρs h))
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  -- Step 2: `s` is measurable and bounded by `1`, hence integrable on compact sets.
  have hsl : LocallyIntegrable s volume := by
    rw [locallyIntegrable_iff]
    exact fun K hK => Measure.integrableOn_of_bounded hK.measure_lt_top.ne hs
      (Eventually.of_forall hs1)
  -- Step 3: `ρ` is `C^∞` with compact support and `s` is locally integrable, so `ρ ⋆ s` is `C^∞`.
  have hG : ContDiff ℝ (⊤ : ℕ∞) (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hρc.contDiff_convolution_left _ hρ hsl
  -- Step 4: `‖ρ t • s (y − t)‖ ≤ ρ t` and `∫ ρ = 1`.
  have hbd : ∀ y, ‖convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume y‖ ≤ 1 := by
    intro y
    rw [convolution_def]
    refine (norm_integral_le_of_norm_le hρi (Eventually.of_forall fun t => ?_)).trans hρ1.le
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact mul_le_of_le_one_right (hρ0 t) (hs1 _)
  -- Step 5: `support (ρ ⋆ s) ⊆ support s + support ρ ⊆ Q_δ + B_σ(0)` lies in the box `P`,
  -- since `|t_i| ≤ |t| < σ`.
  set P : Set (Euclid (m + 1)) := {y | ∀ i, δ - σ ≤ y i ∧ y i ≤ 1 - δ + σ}
  have hsupp : support (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ P := by
    intro y hy
    obtain ⟨a, ha, t, ht, rfl⟩ :=
      support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ) hy
    have ha' : ∀ i, δ < a i ∧ a i < 1 - δ := by
      by_contra h
      exact ha (hs0 a h)
    have ht' : ‖t‖ < σ := mem_ball_zero_iff.mp (hρs ht)
    intro i
    have hti : |t i| < σ := lt_of_le_of_lt (PiLp.norm_apply_le t i) ht'
    obtain ⟨h1, h2⟩ := abs_lt.mp hti
    obtain ⟨h3, h4⟩ := ha' i
    simp only [PiLp.add_apply]
    constructor <;> linarith
  -- Step 6: `P` is compact (the preimage of a product of intervals under `PiLp.homeomorph`)
  -- and lies in `Q₁` because `0 < δ − σ` and `1 − δ + σ < 1`.
  have hPc : IsCompact P := by
    have h := (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi fun _ : Fin (m + 1) => isCompact_Icc (a := δ - σ) (b := 1 - δ + σ))
    convert h using 1
    ext y
    simp only [mem_preimage, mem_univ_pi, mem_Icc]
    rfl
  have hPQ : P ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro y hy i
    obtain ⟨h1, h2⟩ := hy i
    constructor <;> linarith
  -- Step 7: `tsupport (ρ ⋆ s)` is a closed subset of the compact set `P ⊆ Q₁`.
  have hts : tsupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ P :=
    closure_minimal hsupp hPc.isClosed
  exact ⟨hG, hPc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hPQ, hbd⟩

end Submission

/-- **Mollification does not increase the variation on `Q_δ`** (the duality step of Simon
Ch. 2, 2.5 (4)–(5)).  Let `u` be integrable on the open unit cube `Q₁` with `∫_{Q₁} u div g ≤ V`
for every smooth compactly supported field `g` with `spt g ⊆ Q₁` and `|g| ≤ 1`, and let `ρ ≥ 0`
be a smooth kernel with `∫ρ = 1` and `spt ρ ⊆ B_σ(0)`, `0 < σ < δ`.  Then `f = ρ ⋆ 1_{Q₁}u`
satisfies `∫_{Q_δ} ‖Df‖ ≤ V`.  With `w` the Riesz representative of `Df` and the unit field
`s = 1_{Q_δ} w/|w|`, the field `G = ρ̌ ⋆ s` (`ρ̌(z) = ρ(−z)`) is admissible
(`cmcdt_cbm_sa_smoothed_field`), and `cmcdt_cbm_sa_mollify_adjoint` gives
`∫_{Q_δ} ‖Df‖ = ∫ Df(s) = −∫_{Q₁} u div G ≤ V`, the last step by testing with `−G`. -/
theorem Submission.cmcdt_cbm_sa_grad_bound : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ σ : ℝ) (ρ : Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < σ → σ < δ → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid (m + 1)) σ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ (convolution ρ ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ V := by
  intro m u V δ σ ρ hu hV hσ hσδ hρ hρ0 hρ1 hρs
  set Q1 : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set Qδ : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- Step 0(b): the cubes are measurable (finite intersections of coordinate half-spaces)
  have hcoord : ∀ i : Fin (m + 1), Measurable (fun y : Euclid (m + 1) => y i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hcube : ∀ a b : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    have : {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} =
        ⋂ i, ({y : Euclid (m + 1) | a < y i} ∩ {y | y i < b}) := by
      ext y; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hcoord i)).inter
        (measurableSet_lt (hcoord i) measurable_const)
  have hQ1m : MeasurableSet Q1 := hcube 0 1
  have hQδm : MeasurableSet Qδ := hcube δ (1 - δ)
  -- Step 0(c), 0(d): `Q_δ ⊆ Q₁ ⊆ closedBall 0 √n`, so both have finite measure
  have hQδQ1 : Qδ ⊆ Q1 := fun y hy i => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  have hQ1fin : volume Q1 < ∞ := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))).2 ⟨Real.sqrt (m + 1), ?_⟩
      |>.measure_lt_top
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := hy i
          rw [Real.norm_eq_abs, abs_of_pos h1.1]
          nlinarith [h1.1, h1.2]
      _ = (m + 1 : ℝ) := by simp
  have hQδfin : volume Qδ < ∞ := (measure_mono hQδQ1).trans_lt hQ1fin
  -- Step 0(e): `ū = 1_{Q₁}u` is integrable
  set ub : Euclid (m + 1) → ℝ := Q1.indicator u with hub
  have hub_int : Integrable ub := (integrable_indicator_iff hQ1m).2 hu
  -- Step 0(f): `ρ` is `C¹` with compact support (`spt ρ ⊆ closedBall 0 σ`)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) σ) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall (hρs h))
  have hρC1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast le_top)
  -- Step 2: the Riesz representative `w` of `Df` and the unit field `s = 1_{Q_δ} |w|⁻¹ w`
  set f : Euclid (m + 1) → ℝ := convolution ρ ub (ContinuousLinearMap.lsmul ℝ ℝ) volume
  set w : Euclid (m + 1) → Euclid (m + 1) :=
    fun x => (InnerProductSpace.toDual ℝ (Euclid (m + 1))).symm (fderiv ℝ f x)
  have hw_meas : Measurable w :=
    (InnerProductSpace.toDual ℝ (Euclid (m + 1))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)
  have hw_norm : ∀ x, ‖w x‖ = ‖fderiv ℝ f x‖ := fun x => LinearIsometryEquiv.norm_map _ _
  have hw_apply : ∀ x, fderiv ℝ f x (w x) = ‖w x‖ ^ 2 := fun x => by
    rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq]
  set s : Euclid (m + 1) → Euclid (m + 1) := Qδ.indicator (fun x => ‖w x‖⁻¹ • w x) with hs
  have hs_meas : Measurable s := ((hw_meas.norm.inv).smul hw_meas).indicator hQδm
  have hs_le : ∀ x, ‖s x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ Qδ
    · rw [hs, Set.indicator_of_mem hx, norm_smul, norm_inv, norm_norm]
      by_cases h0 : ‖w x‖ = 0
      · simp [h0]
      · rw [inv_mul_cancel₀ h0]
    · rw [hs, Set.indicator_of_notMem hx, norm_zero]; exact zero_le_one
  have hs_zero : ∀ x, x ∉ Qδ → s x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hs_int : Integrable s := by
    rw [hs, integrable_indicator_iff hQδm]
    exact Measure.integrableOn_of_bounded (M := 1) hQδfin.ne
      ((hw_meas.norm.inv).smul hw_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [norm_smul, norm_inv, norm_norm]
        by_cases h0 : ‖w x‖ = 0
        · simp [h0]
        · rw [inv_mul_cancel₀ h0])
  -- Step 2(e): `Df(x)(s(x)) = 1_{Q_δ}(x) ‖Df(x)‖`
  have hs_apply : ∀ x, fderiv ℝ f x (s x) = Qδ.indicator (fun x => ‖fderiv ℝ f x‖) x := by
    intro x
    by_cases hx : x ∈ Qδ
    · rw [hs, Set.indicator_of_mem hx, Set.indicator_of_mem hx, map_smul, hw_apply,
        smul_eq_mul, ← hw_norm]
      by_cases h0 : ‖w x‖ = 0
      · simp [h0]
      · field_simp
    · rw [hs, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, map_zero]
  -- Step 3: the reflected kernel `ρ̌(z) = ρ(−z)` satisfies the kernel hypotheses
  have hρr_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ (-z)) := hρ.comp contDiff_neg
  have hρr_nonneg : ∀ z, 0 ≤ (fun z => ρ (-z)) z := fun z => hρ0 (-z)
  have hρr_int : ∫ z, (fun z => ρ (-z)) z = 1 := by
    simp only
    rw [integral_neg_eq_self]
    exact hρ1
  have hρr_supp : support (fun z => ρ (-z)) ⊆ ball (0 : Euclid (m + 1)) σ := by
    intro z hz
    have h := hρs (show -z ∈ support ρ from hz)
    simpa using h
  -- Step 4: the smoothed field `G = ρ̌ ⋆ s` is admissible
  set G : Euclid (m + 1) → Euclid (m + 1) :=
    convolution (fun z => ρ (-z)) s (ContinuousLinearMap.lsmul ℝ ℝ) volume
  obtain ⟨hG_smooth, hG_cpt, hG_tsupp, hG_le⟩ :=
    Submission.cmcdt_cbm_sa_smoothed_field m δ σ (fun z => ρ (-z)) s hσ hσδ hρr_smooth
      hρr_nonneg hρr_int hρr_supp hs_meas.aestronglyMeasurable hs_le hs_zero
  -- Step 5: testing the variation hypothesis with `−G` gives `−∫_{Q₁} u div G ≤ V`
  have h5 := hV (-G) hG_smooth.neg hG_cpt.neg (by rw [tsupport_neg]; exact hG_tsupp)
    (fun y => by rw [Pi.neg_apply, norm_neg]; exact hG_le y)
  have h5' : -∫ y in Q1, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) ≤ V := by
    rw [← integral_neg]
    convert h5 using 3 with y
    rw [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg, mul_neg]
  -- Step 6: the adjoint identity `∫ Df(s) = −∫ ū div G`
  have h6 := Submission.cmcdt_cbm_sa_mollify_adjoint (m + 1) ρ ub s hρC1 hρc hub_int hs_int
  -- Step 7: `∫ ū div G = ∫_{Q₁} u div G`
  have h7 : ∫ z, ub z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) =
      ∫ z in Q1, u z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) := by
    rw [← integral_indicator hQ1m]
    congr 1
    funext z
    by_cases hz : z ∈ Q1
    · simp [hub, hz]
    · simp [hub, hz]
  -- Step 8: `∫_{Q_δ} ‖Df‖ = ∫ Df(s) = −∫_{Q₁} u div G ≤ V`
  calc ∫ x in Qδ, ‖fderiv ℝ f x‖
      = ∫ x, Qδ.indicator (fun x => ‖fderiv ℝ f x‖) x := (integral_indicator hQδm).symm
    _ = ∫ x, fderiv ℝ f x (s x) := by
        congr 1
        funext x
        exact (hs_apply x).symm
    _ = -∫ z, ub z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) := h6
    _ = -∫ z in Q1, u z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) := by rw [h7]
    _ ≤ V := h5'

/-- **Smooth approximation with the variation bound on `Q_δ`** (Simon Ch. 2, 2.5, as used in the
proof of 2.7 and of the deformation theorem, Ch. 6, 5.1).  If `u` is integrable on `Q₁` and
`∫_{Q₁} u div g ≤ V` for every smooth compactly supported field `g` with `spt g ⊆ Q₁` and
`|g| ≤ 1`, then for `δ > 0` the mollifications `v_k = ρ_k ⋆ 1_{Q₁}u` are `C^∞` and satisfy
`∫_{Q_δ} ‖Dv_k‖ ≤ V` and `∫_{Q_δ} |v_k − u| → 0`.  Here `ρ_k` is the unit-mass normalization of
the bump of radius `σ_k = δ/(k + 2) < δ`; the bound is `cmcdt_cbm_sa_grad_bound`, and since
`1_{Q₁}u = u` on `Q_δ ⊆ Q₁`, the convergence follows from `cmcdt_cbm_sa_mollify_l1` as
`σ_k → 0`. -/
theorem Submission.cmcdt_cbm_smooth_approx : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → ∃ v : ℕ → Euclid (m + 1) → ℝ, (∀ k, ContDiff ℝ 1 (v k)) ∧ (∀ k, ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ (v k) x‖ ≤ V) ∧ Tendsto (fun k => ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - u x|) atTop (𝓝 0) := by
  intro m u V δ hu hV hδ
  set Q1 : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set Qδ : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- Step 0: the cubes are measurable, `Q_δ ⊆ Q₁`, and `ū = 1_{Q₁}u` is integrable
  have hcoord : ∀ i : Fin (m + 1), Measurable (fun y : Euclid (m + 1) => y i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hcube : ∀ a b : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    have : {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} =
        ⋂ i, ({y : Euclid (m + 1) | a < y i} ∩ {y | y i < b}) := by
      ext y; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hcoord i)).inter
        (measurableSet_lt (hcoord i) measurable_const)
  have hQ1m : MeasurableSet Q1 := hcube 0 1
  have hQδm : MeasurableSet Qδ := hcube δ (1 - δ)
  have hQδQ1 : Qδ ⊆ Q1 := fun y hy i => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  set ub : Euclid (m + 1) → ℝ := Q1.indicator u
  have hub_int : Integrable ub := (integrable_indicator_iff hQ1m).2 hu
  -- Step 1: radii `σ_k = δ/(k + 2) ∈ (0, δ)` and kernels `ρ_k = b_k / ∫ b_k`, where `b_k` is the
  -- `C^∞` bump with `b_k = 1` on `B_{σ_k/2}(0)`, `0 ≤ b_k ≤ 1` and `support b_k = B_{σ_k}(0)`
  set σ : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2)
  have hσ0 : ∀ k, 0 < σ k := fun k => div_pos hδ (by positivity)
  have hσδ : ∀ k, σ k < δ := fun k =>
    div_lt_self hδ (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  let b : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    ⟨σ k / 2, σ k, half_pos (hσ0 k), half_lt_self (hσ0 k)⟩
  have hb_int : ∀ k, 0 < ∫ y, b k y := fun k => by
    refine (integral_pos_iff_support_of_nonneg (b k).nonneg'
      ((b k).continuous.integrable_of_hasCompactSupport (b k).hasCompactSupport)).2 ?_
    rw [(b k).support_eq]
    exact measure_ball_pos volume _ (b k).rOut_pos
  set ρ : ℕ → Euclid (m + 1) → ℝ := fun k x => b k x / ∫ y, b k y
  have hρ_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k) := fun k => (b k).contDiff.div_const _
  have hρ_nonneg : ∀ k z, 0 ≤ ρ k z := fun k z => div_nonneg (b k).nonneg (hb_int k).le
  have hρ_one : ∀ k, ∫ z, ρ k z = 1 := fun k => by
    show ∫ z, b k z / ∫ y, b k y = 1
    rw [integral_div, div_self (hb_int k).ne']
  have hρ_supp : ∀ k, support (ρ k) = ball (0 : Euclid (m + 1)) (σ k) := fun k => by
    show support (fun x => b k x / ∫ y, b k y) = ball 0 (b k).rOut
    rw [support_div, (b k).support_eq, support_const (hb_int k).ne', inter_univ]
  have hρ_cpt : ∀ k, HasCompactSupport (ρ k) := fun k =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) (σ k)) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((hρ_supp k).subset h))
  -- Step 2: `v_k = ρ_k ⋆ ū` is `C^∞` (differentiation under the integral sign), hence `C¹`
  refine ⟨fun k => convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun k => ?_,
    fun k => ?_, ?_⟩
  · exact ((hρ_cpt k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρ_smooth k)
      hub_int.locallyIntegrable).of_le (by exact_mod_cast le_top)
  -- Step 3: the variation bound `∫_{Q_δ} ‖Dv_k‖ ≤ V`, since `0 < σ_k < δ`
  · exact Submission.cmcdt_cbm_sa_grad_bound m u V δ (σ k) (ρ k) hu hV (hσ0 k) (hσδ k) (hρ_smooth k)
      (hρ_nonneg k) (hρ_one k) (hρ_supp k).subset
  -- Step 4: given `ε > 0`, `cmcdt_cbm_sa_mollify_l1` gives `r > 0` with `‖ρ ⋆ ū − ū‖₁ ≤ ε/2` for
  -- unit-mass kernels supported in `B_r(0)`; `σ_k ≤ r` for `k ≥ N > δ/r`, and `ū = u` on `Q_δ`
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨r, hr, hL1⟩ :=
      Submission.cmcdt_cbm_sa_mollify_l1 (m + 1) ub hub_int (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_gt (δ / r)
    refine ⟨N, fun k hk => ?_⟩
    have hσr : σ k ≤ r := by
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
      have h1 : δ < r * ((k : ℝ) + 2) := by
        rw [mul_comm]
        exact (div_lt_iff₀ hr).1 (by linarith)
      exact (div_le_iff₀ (by positivity)).2 h1.le
    have hL := hL1 (ρ k) (hρ_smooth k).continuous (hρ_nonneg k) (hρ_one k)
      ((hρ_supp k).subset.trans (ball_subset_ball hσr))
    rw [dist_zero_right]
    calc ‖∫ x in Qδ, |convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x|‖
        ≤ (∫⁻ x in Qδ, ENNReal.ofReal
            ‖|convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x|‖).toReal :=
          norm_integral_le_lintegral_norm _
      _ = (∫⁻ x in Qδ,
            ‖convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume x - ub x‖ₑ).toReal := by
          congr 1
          refine setLIntegral_congr_fun hQδm fun x hx => ?_
          have hx1 : ub x = u x := indicator_of_mem (hQδQ1 hx) u
          rw [hx1, Real.norm_eq_abs, abs_abs, Real.enorm_eq_ofReal_abs]
      _ ≤ ε / 2 := ENNReal.toReal_le_of_le_ofReal (half_pos hε).le
          ((setLIntegral_le_lintegral _ _).trans hL)
      _ < ε := half_lt_self hε

/-- **BV Poincaré inequality on the unit cube** (Simon Ch. 2, 2.7, as used for the first line of
(32) in the proof of Ch. 6, 5.1).  Let `n = m + 1` and `Q_δ = (δ, 1 − δ)ⁿ`, `Q₁ = Q_0`.  If
`u ∈ L¹(Q₁)` and `∫_{Q₁} u div g ≤ V` for all `g ∈ C^∞_c(Q₁; ℝⁿ)` with `|g| ≤ 1`, then
`∫_{Q₁} |u − c| ≤ 2^{n+1} √n V` for the mean `c = ∫_{Q₁} u`.  Testing with `g = 0` gives
`V ≥ 0`.  For `0 < δ < 1/2` the `C¹` functions `v_k` of `cmcdt_cbm_smooth_approx` have
`∫_{Q_δ} |Dv_k| ≤ V` and `v_k → u` in `L¹(Q_δ)`, so `cmcdt_cbm_smooth_poincare` bounds their
oscillation `∫_{Q_δ}∫_{Q_δ} |v_k(x) − v_k(y)|` by `K = 2ⁿ√n V`, and the bound passes to `u`
(`cmcdt_cbm_bvp_osc_le_of_l1_approx`), then to `Q₁` as `δ ↓ 0`
(`cmcdt_cbm_bvp_osc_le_of_inner_cubes`).  As `|Q₁| = 1`, `∫_{Q₁} |u − c|` is at most the
oscillation of `u` over `Q₁` (`cmcdt_cbm_bvp_mean_dev_le_osc`), and `K ≤ 2^{n+1}√n V`. -/
theorem Submission.cmcdt_cbm_bv_poincare : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c| ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := by
  intro m u V hu hV
  -- Step 0: `V ≥ 0`, testing with `g = 0`
  have hV0 : 0 ≤ V := by
    simpa using hV 0 contDiff_zero_fun .zero (by simp only [tsupport_zero, empty_subset])
      (by simp)
  -- Step 2: for `0 < δ < 1/2` the oscillation of `u` over `Q_δ` is at most `K = 2ⁿ√n V`
  have hδ : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ},
        ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤
        2 ^ (m + 1) * Real.sqrt (m + 1) * V := by
    intro δ hδ _
    obtain ⟨v, hv, hvV, hvu⟩ := Submission.cmcdt_cbm_smooth_approx m u V δ hu hV hδ
    refine Submission.cmcdt_cbm_bvp_osc_le_of_l1_approx m u v δ _ hu hδ.le
      (fun k => (hv k).continuous) (fun k => ?_) hvu
    exact (Submission.cmcdt_cbm_smooth_poincare m (v k) δ (hv k) hδ.le).trans
      (mul_le_mul_of_nonneg_left (hvV k) (by positivity))
  -- Steps 3–4: let `δ ↓ 0`, then compare with the mean `c = ∫_{Q₁} u` (`|Q₁| = 1`)
  refine ⟨∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y, ?_⟩
  calc _ ≤ ∫ x in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u x - u y| :=
        Submission.cmcdt_cbm_bvp_mean_dev_le_osc m _ u
          (Submission.cmcdt_cbm_bvp_unit_cube_volume m) hu
    _ ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) * V :=
        Submission.cmcdt_cbm_bvp_osc_le_of_inner_cubes m u _ hu hδ
    _ ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := by
      gcongr
      · norm_num
      · omega
/-- **Trace estimate on the unit cube** (step 5 of the median argument; it replaces the appeal to
Simon Ch. 2, 2.8–2.9 in the second line of (32) in the proof of Ch. 6, 5.1).  `div G = tr DG` is
continuous, so `|div G| ≤ M` on `Q₁`.  For `δ ∈ (0, 1/4)` the `C¹` functions `v_k` of
`cmcdt_cbm_smooth_approx` have `∫_{Q_δ} ‖Dv_k‖ ≤ V` and `v_k → w` in `L¹(Q_δ)`, so the smooth
estimate `cmcdt_cbm_smooth_trace` on `Q_δ` passes to `w` (`cmcdt_cbm_bvt_l1_limit`); `Q_δ ⊆ Q₁`
bounds `∫_{Q_δ} |w|` by `∫_{Q₁} |w|`, and `δ → 0⁺` by `cmcdt_cbm_bvt_cube_exhaust`. -/
theorem Submission.cmcdt_cbm_bv_trace : ∀ (m : ℕ) (w : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn w {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ (2 * (m + 1) + 1) * V + 4 * (m + 1) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w y| := by
  intro m w V hw hV G hG hG1
  -- the cubes `{a < z_i < b}` are open, and `Q_δ ⊆ Q₁` for `δ ≥ 0`
  have hopen : ∀ a b : ℝ, IsOpen {z : Euclid (m + 1) | ∀ i, a < z i ∧ z i < b} := by
    intro a b
    simp only [ofPred_forall, ofPred_and]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hsub : ∀ δ : ℝ, 0 ≤ δ → {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun δ hδ z hz i =>
    ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- `div G = tr ∘ DG` is continuous, hence bounded by `M` on `Q₁`
  have hdc : Continuous fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
    ((LinearMap.trace ℝ (Euclid (m + 1))).comp
      (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional.comp
      (hG.continuous_fderiv one_ne_zero)
  obtain ⟨⟨M, hM⟩, -⟩ := Submission.cmcdt_cbm_bvt_cube_cont_bound (m + 1) _ hdc
  -- for `δ ∈ (0, 1/4)`: `|∫_{Q_δ} w div G| ≤ (2n + 1) V + 4n ∫_{Q₁} |w|`
  have hδbound : ∀ δ ∈ Ioo (0 : ℝ) (1 / 4),
      |∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ},
          w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (2 * (m + 1) + 1) * V +
          4 * (m + 1) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w y| := by
    rintro δ ⟨hδ0, hδ⟩
    have hQ := hsub δ hδ0.le
    -- `C¹` approximations `v_k → w` in `L¹(Q_δ)` with `∫_{Q_δ} ‖Dv_k‖ ≤ V`
    obtain ⟨v, hv, hvV, hvw⟩ := Submission.cmcdt_cbm_smooth_approx m w V δ hw hV hδ0
    refine (Submission.cmcdt_cbm_bvt_l1_limit volume _ v w
      (fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)) ((2 * (m + 1) + 1) * V)
      (4 * (m + 1)) M (hopen δ (1 - δ)).measurableSet (by positivity)
      (fun k => (Submission.cmcdt_cbm_bvt_cube_cont_bound (m + 1) (v k)
        (hv k).continuous).2.mono_set hQ)
      (hw.mono_set hQ) hdc.aestronglyMeasurable (fun y hy => hM y (hQ hy)) hvw
      fun k => ?_).trans ?_
    · -- the smooth estimate on `Q_δ`, with `∫_{Q_δ} ‖Dv_k‖ ≤ V`
      refine (Submission.cmcdt_cbm_smooth_trace m (v k) G δ (hv k) hG hG1 hδ0.le hδ.le).trans ?_
      gcongr _ * ?_ + _
      exact hvV k
    · -- `∫_{Q_δ} |w| ≤ ∫_{Q₁} |w|`
      gcongr _ + _ * ?_
      exact setIntegral_mono_set (Integrable.abs hw) (ae_of_all _ fun y => abs_nonneg (w y))
        (ae_of_all _ hQ)
  -- `δ → 0⁺`: `∫_{Q_δ} w div G → ∫_{Q₁} w div G`, with `w div G` integrable on `Q₁`
  have hwG : IntegrableOn (fun y => w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    Integrable.mul_bdd hw hdc.aestronglyMeasurable
      (ae_restrict_of_forall_mem (hopen 0 1).measurableSet fun y hy => hM y hy)
  exact le_of_tendsto (Submission.cmcdt_cbm_bvt_cube_exhaust (m + 1) _ hwG).abs
    (Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)) hδbound)

end GMT.Ch07
