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

/-- **Simon Ch. 6, proof of Lemma 5.4, step (6a)** (segment argument): if
`|f(w) − f(wₜ)| ≤ K|w − wₜ|` for `w` near each point `wₜ = x + t(y − x)`, `t ∈ [0, 1]`, of the
segment `[x, y]`, then `|f(y) − f(x)| ≤ K|y − x|`.  With `g(t) = x + t(y − x)`, the local bounds
make `f ∘ g` continuous on `[0, 1]`, so `S = {t : |f(g(t)) − f(x)| ≤ Kt|y − x|}` meets `[0, 1]`
in a closed set; `0 ∈ S`, and the local bound at `g(t)` gives `(t, t + δ) ⊆ S` for `t ∈ S`.
Continuous induction gives `[0, 1] ⊆ S`, and `t = 1` is the claim. -/
theorem Submission.cmcdtsr_segment_lipschitz : ∀ (P : ℕ) (f : Euclid P → Euclid P) (x y : Euclid P) (K : ℝ), 0 ≤ K → (∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ w in 𝓝 (x + t • (y - x)), dist (f w) (f (x + t • (y - x))) ≤ K * dist w (x + t • (y - x))) → dist (f y) (f x) ≤ K * dist y x := by
  intro P f x y K hK hloc
  -- the segment `g(t) = x + t(y − x)`, with `|g(s) − g(t)| = |s − t| |y − x|`
  let g : ℝ → Euclid P := fun t => x + t • (y - x)
  have hgcont : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hgdist : ∀ s t : ℝ, dist (g s) (g t) = |s - t| * dist y x := by
    intro s t
    simp only [g, dist_eq_norm]
    rw [show x + s • (y - x) - (x + t • (y - x)) = (s - t) • (y - x) by rw [sub_smul]; abel,
      norm_smul, Real.norm_eq_abs]
  -- the local bounds make `f` continuous at each `g(t)`, hence `f ∘ g` continuous on `[0, 1]`
  have hfcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun s => f (g s)) t := by
    intro t ht
    have hft : ContinuousAt f (g t) := by
      rw [Metric.continuousAt_iff']
      intro ε hε
      have hball : ∀ᶠ w in 𝓝 (g t), dist w (g t) < ε / (K + 1) :=
        Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hloc t ht, hball] with w h1 h2
      calc dist (f w) (f (g t)) ≤ K * dist w (g t) := h1
        _ ≤ K * (ε / (K + 1)) := by gcongr
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
    exact hft.comp hgcont.continuousAt
  have hcontOn : ContinuousOn (fun t => dist (f (g t)) (f x) - K * t * dist y x) (Icc 0 1) := by
    intro t ht
    apply ContinuousWithinAt.sub
    · have hca : ContinuousAt (fun s => dist (f (g s)) (f x)) t :=
        (hfcont t ht).dist continuousAt_const
      exact hca.continuousWithinAt
    · exact ((continuous_const.mul continuous_id).mul continuous_const).continuousWithinAt
  -- `S ∩ [0, 1]` is closed and `0 ∈ S`
  let S : Set ℝ := {t | dist (f (g t)) (f x) ≤ K * t * dist y x}
  have hS_closed : IsClosed (S ∩ Icc 0 1) := by
    have := hcontOn.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
    convert this using 1
    ext t
    simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, sub_nonpos]
    tauto
  have h0 : (0 : ℝ) ∈ S := by
    show dist (f (x + (0 : ℝ) • (y - x))) (f x) ≤ K * 0 * dist y x
    simp
  -- right extension: for `t ∈ S ∩ [0, 1)`, the local bound at `g(t)` gives `(t, t + δ) ⊆ S`
  have hstep : ∀ t ∈ S ∩ Ico (0 : ℝ) 1, S ∈ 𝓝[>] t := by
    rintro t ⟨htS, ht⟩
    have hev : ∀ᶠ s in 𝓝 t, dist (f (g s)) (f (g t)) ≤ K * dist (g s) (g t) :=
      (hgcont.tendsto t).eventually (hloc t ⟨ht.1, ht.2.le⟩)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hst
    have hst' : t < s := hst
    have htS' : dist (f (g t)) (f x) ≤ K * t * dist y x := htS
    show dist (f (g s)) (f x) ≤ K * s * dist y x
    calc dist (f (g s)) (f x) ≤ dist (f (g s)) (f (g t)) + dist (f (g t)) (f x) :=
          dist_triangle _ _ _
      _ ≤ K * dist (g s) (g t) + K * t * dist y x := add_le_add hs htS'
      _ = K * s * dist y x := by rw [hgdist, abs_of_pos (sub_pos.mpr hst')]; ring
  -- continuous induction on `[0, 1]`, evaluated at `t = 1`
  have h1 : (1 : ℝ) ∈ S :=
    IsClosed.Icc_subset_of_forall_mem_nhdsWithin hS_closed h0 hstep ⟨zero_le_one, le_rfl⟩
  have h1' : dist (f (g 1)) (f x) ≤ K * 1 * dist y x := h1
  rwa [show g 1 = y by simp [g], mul_one] at h1'
/-- **Simon Ch. 6, proof of Lemma 5.4, step 5** (local finiteness of the unit cubical grid): the
points `y` near `x` lie in one of the finitely many closed unit cubes `z + [0, 1]ᴾ`, `z ∈ ℤᴾ`,
that contain `x`.  In one dimension the intervals `[k, k + 1] ∋ t` with `k ∈ {⌊t⌋ − 1, ⌊t⌋}`
cover the neighbourhood `(⌊t⌋, ⌊t⌋ + 1)` of `t` if `t ∉ ℤ`, and `(t − 1, t + 1)` if `t ∈ ℤ`.
`Z` is the set of corners in the finite product `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`.
For `y` in the intersection of the finitely many coordinate neighbourhoods, the corner is chosen
coordinate by coordinate. -/
theorem Submission.cmcdtsr_cube_cover : ∀ (P : ℕ) (x : Euclid P), ∃ Z : Finset (Fin P → ℤ), (∀ z ∈ Z, ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) ∧ ∀ᶠ y : Euclid P in 𝓝 x, ∃ z ∈ Z, ∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1 := by
  intro P x
  classical
  -- step 2: the corners in `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`
  let T : Fin P → Finset ℤ := fun i => {⌊x i⌋ - 1, ⌊x i⌋}
  refine ⟨(Fintype.piFinset T).filter fun z => ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1,
    fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
  -- step 1: the intervals `[k, k + 1] ∋ xᵢ`, `k ∈ Tᵢ`, cover a neighbourhood of `xᵢ`
  have h1d : ∀ i, ∀ᶠ t in 𝓝 (x i), ∃ k ∈ T i,
      ((k : ℝ) ≤ x i ∧ x i ≤ k + 1) ∧ (k : ℝ) ≤ t ∧ t ≤ k + 1 := by
    intro i
    have hfl : (⌊x i⌋ : ℝ) ≤ x i := Int.floor_le (x i)
    have hfl' : x i < ⌊x i⌋ + 1 := Int.lt_floor_add_one (x i)
    have hk : ⌊x i⌋ ∈ T i := by simp [T]
    have hk' : ⌊x i⌋ - 1 ∈ T i := by simp [T]
    rcases hfl.lt_or_eq with hlt | heq
    · -- `xᵢ ∉ ℤ`: `[⌊xᵢ⌋, ⌊xᵢ⌋ + 1]` contains the neighbourhood `(⌊xᵢ⌋, ⌊xᵢ⌋ + 1)`
      filter_upwards [Ioo_mem_nhds hlt hfl'] with t ht
      exact ⟨⌊x i⌋, hk, ⟨hfl, hfl'.le⟩, ht.1.le, ht.2.le⟩
    · -- `xᵢ ∈ ℤ`: `[xᵢ − 1, xᵢ] ∪ [xᵢ, xᵢ + 1]` contains the neighbourhood `(xᵢ − 1, xᵢ + 1)`
      filter_upwards [Ioo_mem_nhds (sub_one_lt (x i)) (lt_add_one (x i))] with t ht
      rcases le_total t (x i) with hle | hge
      · refine ⟨⌊x i⌋ - 1, hk', ?_⟩
        push_cast
        exact ⟨⟨by linarith, by linarith⟩, by linarith [ht.1], by linarith⟩
      · exact ⟨⌊x i⌋, hk, ⟨hfl, hfl'.le⟩, by linarith, by linarith [ht.2]⟩
  -- step 3: pull back along the continuous coordinates and intersect the finitely many
  -- neighbourhoods
  have hall : ∀ᶠ y : Euclid P in 𝓝 x, ∀ i, ∃ k ∈ T i,
      ((k : ℝ) ≤ x i ∧ x i ≤ k + 1) ∧ (k : ℝ) ≤ y i ∧ y i ≤ k + 1 :=
    eventually_all.mpr fun i => ((PiLp.continuous_apply 2 _ i).tendsto x).eventually (h1d i)
  -- step 4: choose the corner coordinate by coordinate
  filter_upwards [hall] with y hy
  choose k hkT hk using hy
  exact ⟨k, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hkT, fun i => (hk i).1⟩,
    fun i => (hk i).2⟩
/-- **Simon, Ch. 6, proof of Lemma 5.4** (the cube centre `b + a` and the planes through it lie in
the dual skeleton).  Let `L*(a)` be the set of points with at least `m + 2` coordinates in `a + ℤ`
and `d := dist(x, L*(a))`.  At most `m + 1` coordinates satisfy `|xᵢ − bᵢ − aᵢ| < d/√(m + 2)`:
moving `m + 2` of them to `bᵢ + aᵢ` would give `w ∈ L*(a)` with
`|x − w|² < (m + 2) d²/(m + 2) = d²`, contradicting `d ≤ |x − w|`. -/
theorem Submission.cmcdtsr_dual_dist_count : ∀ (P m : ℕ) (a x : Euclid P) (b : Fin P → ℤ), (Finset.univ.filter (fun i => |x i - b i - a i| < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} / Real.sqrt (m + 2))).card ≤ m + 1 := by
  intro P m a x b
  set L : Set (Euclid P) :=
    {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  set d := infDist x L
  -- otherwise keep exactly `m + 2` coordinates with `|xᵢ − bᵢ − aᵢ| < d/√(m + 2)`
  by_contra! hcon
  obtain ⟨s, hsS, hscard⟩ := Finset.exists_subset_card_eq (n := m + 2) hcon
  -- moving them to `bᵢ + aᵢ` gives a point `w ∈ L*(a)`, so `d ≤ |x − w|`
  let w : Euclid P := WithLp.toLp 2 fun i => if i ∈ s then (b i : ℝ) + a i else x i
  have hw : ∀ i, w i = if i ∈ s then (b i : ℝ) + a i else x i := fun i => rfl
  have hwL : w ∈ L := ⟨s, hscard.ge, fun i hi => ⟨b i, by rw [hw i, ite_eq_left hi]; ring⟩⟩
  have hdw : d ≤ dist x w := infDist_le_dist_of_mem hwL
  -- `|x − w|² = Σ_{i ∈ s} (xᵢ − bᵢ − aᵢ)² < (m + 2) d²/(m + 2) = d²`
  have hm : (0 : ℝ) < m + 2 := by positivity
  have hsum : ∑ i, dist (x i) (w i) ^ 2 = ∑ i ∈ s, (x i - b i - a i) ^ 2 := by
    rw [← Finset.sum_subset (f := fun i => dist (x i) (w i) ^ 2) (Finset.subset_univ s)
      fun i _ hi => by simp [hw i, hi]]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hw i, ite_eq_left hi, Real.dist_eq, sq_abs]
    ring
  have hlt : ∑ i ∈ s, (x i - b i - a i) ^ 2 < d ^ 2 :=
    calc ∑ i ∈ s, (x i - b i - a i) ^ 2 < ∑ _i ∈ s, (d / √(m + 2)) ^ 2 := by
          refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) fun i hi => ?_
          have hi' := (Finset.mem_filter.mp (hsS hi)).2
          rw [← sq_abs]
          gcongr
      _ = d ^ 2 := by
          rw [Finset.sum_const, hscard, nsmul_eq_mul, div_pow, Real.sq_sqrt hm.le]
          push_cast
          field_simp
  have hxw : dist x w < d := by
    rw [EuclideanSpace.dist_eq, hsum]
    calc √(∑ i ∈ s, (x i - b i - a i) ^ 2) < √(d ^ 2) :=
          Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _) hlt
      _ = d := Real.sqrt_sq infDist_nonneg
  exact lt_irrefl d (hdw.trans_lt hxw)
/-- **Simon Ch. 6, proof of Lemma 5.4** (centres of faces and radial retractions).  For the face
`F = {y : b_k ≤ y_k ≤ b_k + 1 (k ∈ J), y_i = b_i (i ∉ J)}` with centre `a_F`,
`(a_F)_k = b_k + a_k` (`|a_k − 1/2| < 1/4`), let
`N(y) = max_{k ∈ J} max((y_k − b_k − a_k)/(1 − a_k), (b_k + a_k − y_k)/a_k)` be the gauge of
`y − a_F` and `ψ_F(y) = a_F + (y − a_F)/N(y)`.  For `x ∈ F \ {a_F}`: `|x_k − b_k − a_k| ≤ N(x)`
(`k ∈ J`), `0 < N(x) ≤ 1`, `ψ_F(x) ∈ ∂F`, `ψ_F(x) = x` if `x ∈ ∂F`, and
`|ψ_F(y) − ψ_F(x)| ≤ (1 + 4√|J|)/N(x) · |y − x|` for `y ∈ F \ {a_F}`, because `N` is
`4`-Lipschitz and `|y − a_F| ≤ √|J| N(y)`. -/
theorem Submission.cmcdtsr_face_radial : ∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (ψF : Euclid P → Euclid P), (∀ y : Euclid P, ∀ i, ψF y i = if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) / J.sup' hJ (fun k => max ((y k - b k - a k) / (1 - a k)) ((b k + a k - y k) / a k)) else y i) → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → (∃ i ∈ J, x i ≠ b i + a i) → (∀ k ∈ J, |x k - b k - a k| ≤ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))) ∧ 0 < J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ∧ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ≤ 1 ∧ (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧ (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧ ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧ ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) → (∃ i ∈ J, y i ≠ b i + a i) → dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) * dist y x := by
  intro P a ha b J hJ ψF hψ x hx hne
  -- the gauge `N(u)` of `u − a_F`, kept opaque
  obtain ⟨N, hN⟩ : ∃ N : Euclid P → ℝ, ∀ u : Euclid P,
      J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) = N u :=
    ⟨fun u => J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)),
      fun _ => rfl⟩
  have hψN : ∀ u : Euclid P, ∀ i, ψF u i =
      if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N u else u i := by
    intro u i
    rw [hψ u i, hN u]
  rw [hN x]
  -- step 0: `1/4 < a_k < 3/4`
  have ha' : ∀ i, 1 / 4 < a i ∧ a i < 3 / 4 := by
    intro i
    have := abs_lt.mp (ha i)
    constructor <;> linarith [this.1, this.2]
  -- `N(u)` dominates each of its terms, and is the largest term
  have hterm : ∀ u : Euclid P, ∀ k ∈ J,
      max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k) ≤ N u := by
    intro u k hk
    rw [← hN u]
    exact Finset.le_sup' (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) hk
  -- step 1: `|u_k − b_k − a_k| ≤ N(u)` for `k ∈ J`
  have habs : ∀ u : Euclid P, ∀ k ∈ J, |u k - b k - a k| ≤ N u := by
    intro u k hk
    obtain ⟨h1, h2⟩ := ha' k
    refine le_trans ?_ (hterm u k hk)
    rcases le_or_gt 0 (u k - b k - a k) with ht | ht
    · rw [abs_of_nonneg ht]
      apply le_max_of_le_left
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ a k)]
    · rw [abs_of_neg ht]
      apply le_max_of_le_right
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_pos (neg_pos.mpr ht) (by linarith : (0 : ℝ) < 1 - a k)]
  -- step 2: `N ≤ 1` on `F`, and `N > 0` off the centre
  have hle1 : ∀ u : Euclid P,
      (∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i)) → N u ≤ 1 := by
    intro u hu
    rw [← hN u]
    refine Finset.sup'_le hJ _ (fun k hk => ?_)
    obtain ⟨h1, h2⟩ := ha' k
    obtain ⟨hu1, hu2⟩ := (hu k).1 hk
    apply max_le
    · rw [div_le_one (by linarith)]; linarith
    · rw [div_le_one (by linarith)]; linarith
  have hpos : ∀ u : Euclid P, (∃ i ∈ J, u i ≠ b i + a i) → 0 < N u := by
    rintro u ⟨i, hi, hui⟩
    have h0 : u i - b i - a i ≠ 0 := fun h => hui (by linarith)
    exact (abs_pos.mpr h0).trans_le (habs u i hi)
  have hNx := hpos x hne
  refine ⟨habs x, hNx, hle1 x hx, ?_, ?_, ?_, ?_⟩
  · -- step 3: `ψ_F(x) ∈ F`
    intro i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · rw [hψN x i, ite_eq_left hi]
      obtain ⟨h1, h2⟩ := ha' i
      have hq := hterm x i hi
      have hp1 := (le_max_left _ _).trans hq
      have hp2 := (le_max_right _ _).trans hq
      rw [div_le_iff₀ (by linarith)] at hp1 hp2
      have e1 : -(a i) ≤ (x i - b i - a i) / N x := by
        rw [le_div_iff₀ hNx]; linarith
      have e2 : (x i - b i - a i) / N x ≤ 1 - a i := by
        rw [div_le_iff₀ hNx]; linarith
      constructor <;> linarith
    · rw [hψN x i, ite_eq_right hi]
      exact (hx i).2 hi
  · -- step 4: a coordinate attaining the maximum is pushed to `b_i` or `b_i + 1`
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hJ
      (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))
    have heq' : N x = max ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) := by
      rw [← hN x]; exact heq
    refine ⟨i, hi, ?_⟩
    rw [hψN x i, ite_eq_left hi]
    obtain ⟨h1, h2⟩ := ha' i
    rcases max_choice ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) with hm | hm
    · right
      rw [hm] at heq'
      have ht : x i - b i - a i = N x * (1 - a i) := by
        rw [heq', div_mul_cancel₀ _ (by linarith : (1 : ℝ) - a i ≠ 0)]
      have : (x i - b i - a i) / N x = 1 - a i := by
        rw [div_eq_iff hNx.ne']; linarith
      rw [this]; ring
    · left
      rw [hm] at heq'
      have ht : b i + a i - x i = N x * a i := by
        rw [heq', div_mul_cancel₀ _ (by linarith : a i ≠ 0)]
      have : (x i - b i - a i) / N x = -(a i) := by
        rw [div_eq_iff hNx.ne']; linarith
      rw [this]; ring
  · -- step 5: on `∂F`, `N(x) = 1` and `ψ_F(x) = x`
    rintro ⟨i, hi, hbi⟩
    obtain ⟨h1, h2⟩ := ha' i
    have hq := hterm x i hi
    have hN1 : N x = 1 := by
      apply le_antisymm (hle1 x hx)
      rcases hbi with h | h
      · have : (b i + a i - x i) / a i = 1 := by
          rw [h, div_eq_one_iff_eq (by linarith)]; ring
        linarith [le_max_right ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i)]
      · have : (x i - b i - a i) / (1 - a i) = 1 := by
          rw [h, div_eq_one_iff_eq (by linarith)]; ring
        linarith [le_max_left ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i)]
    ext k
    rw [hψN x k, hN1]
    split_ifs <;> ring
  · -- steps 6–8: the radial estimate
    intro y hy hney
    have hNy := hpos y hney
    have hNx0 : N x ≠ 0 := hNx.ne'
    have hNy0 : N y ≠ 0 := hNy.ne'
    -- step 6: `N` is `4`-Lipschitz
    have hlip : ∀ u v : Euclid P, N u ≤ N v + 4 * dist u v := by
      intro u v
      rw [← hN u]
      refine Finset.sup'_le hJ _ (fun k hk => ?_)
      obtain ⟨h1, h2⟩ := ha' k
      have hd : |u k - v k| ≤ dist u v := by
        have := PiLp.dist_apply_le u v k
        rwa [Real.dist_eq] at this
      have hdn : 0 ≤ dist u v := dist_nonneg
      have hq := hterm v k hk
      have hp1 := (le_max_left _ _).trans hq
      have hp2 := (le_max_right _ _).trans hq
      apply max_le
      · have e : (u k - b k - a k) / (1 - a k) =
            (v k - b k - a k) / (1 - a k) + (u k - v k) / (1 - a k) := by
          rw [← add_div]; congr 1; ring
        have : (u k - v k) / (1 - a k) ≤ 4 * dist u v := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [le_abs_self (u k - v k),
            mul_nonneg hdn (by linarith : (0 : ℝ) ≤ 4 * (1 - a k) - 1)]
        linarith
      · have e : (b k + a k - u k) / a k = (b k + a k - v k) / a k + (v k - u k) / a k := by
          rw [← add_div]; congr 1; ring
        have : (v k - u k) / a k ≤ 4 * dist u v := by
          rw [div_le_iff₀ (by linarith)]
          have : |v k - u k| ≤ dist u v := by rw [abs_sub_comm]; exact hd
          nlinarith [le_abs_self (v k - u k), mul_nonneg hdn (by linarith : (0 : ℝ) ≤ 4 * a k - 1)]
        linarith
    have hlipxy : |N x - N y| ≤ 4 * dist y x := by
      have l1 := hlip x y
      have l2 := hlip y x
      rw [dist_comm] at l1
      rw [abs_le]; constructor <;> linarith
    -- step 7: `w = y − a_F` (supported in `J`) has `|w| ≤ √|J| N(y)`
    let W : Euclid P := WithLp.toLp 2 (fun k => if k ∈ J then y k - b k - a k else 0)
    have hWk : ∀ k, W k = if k ∈ J then y k - b k - a k else 0 := fun k => rfl
    have hW : ‖W‖ ≤ Real.sqrt J.card * N y := by
      rw [EuclideanSpace.norm_eq]
      have h1 : ∑ k, ‖W k‖ ^ 2 = ∑ k ∈ J, ‖W k‖ ^ 2 :=
        (Finset.sum_subset (Finset.subset_univ J)
          (fun k _ hk => by rw [hWk k, ite_eq_right hk]; simp)).symm
      have h2 : ∑ k ∈ J, ‖W k‖ ^ 2 ≤ J.card • N y ^ 2 := by
        apply Finset.sum_le_card_nsmul
        intro k hk
        rw [hWk k, ite_eq_left hk, Real.norm_eq_abs, sq_abs]
        have := habs y k hk
        nlinarith [abs_nonneg (y k - b k - a k), sq_abs (y k - b k - a k)]
      rw [nsmul_eq_mul] at h2
      calc Real.sqrt (∑ k, ‖W k‖ ^ 2) ≤ Real.sqrt ((J.card : ℝ) * N y ^ 2) :=
            Real.sqrt_le_sqrt (h1 ▸ h2)
        _ = Real.sqrt J.card * N y := by
            rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hNy.le]
    -- step 8: `ψ_F(y) − ψ_F(x) = (y − x)/N(x) + (1/N(y) − 1/N(x)) w`
    have hdecomp : ψF y - ψF x = (1 / N x) • (y - x) + (1 / N y - 1 / N x) • W := by
      ext k
      rw [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply,
        hψN x k, hψN y k, hWk k, smul_eq_mul, smul_eq_mul]
      by_cases hk : k ∈ J
      · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk]
        field_simp
        ring
      · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, (hx k).2 hk, (hy k).2 hk]
        ring
    have hfrac : |1 / N y - 1 / N x| * N y = |N x - N y| / N x := by
      rw [div_sub_div _ _ hNy0 hNx0, abs_div, abs_of_pos (mul_pos hNy hNx)]
      field_simp
    rw [dist_eq_norm, hdecomp]
    calc ‖(1 / N x) • (y - x) + (1 / N y - 1 / N x) • W‖
        ≤ ‖(1 / N x) • (y - x)‖ + ‖(1 / N y - 1 / N x) • W‖ := norm_add_le _ _
      _ = (1 / N x) * dist y x + |1 / N y - 1 / N x| * ‖W‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr hNx), dist_eq_norm]
      _ ≤ (1 / N x) * dist y x + |1 / N y - 1 / N x| * (Real.sqrt J.card * N y) := by
          gcongr
      _ = (1 / N x) * dist y x + (|N x - N y| / N x) * Real.sqrt J.card := by
          rw [← hfrac]; ring
      _ ≤ (1 / N x) * dist y x + (4 * dist y x / N x) * Real.sqrt J.card := by
          gcongr
      _ = (1 + 4 * Real.sqrt J.card) / N x * dist y x := by ring

/-- **Simon Ch. 6, proof of Lemma 5.4: the composite of the face retractions** (chapter-06.txt,
lines 1508–1546).  For `a` with `|aᵢ − 1/2| < 1/4` there are maps `Ψ_k : ℝᴾ → ℝᴾ` with
`Ψ_{m+1} = id` and `Ψ_j(x) = Ψ_{j−1}(ψ_F(x))` for every `j`-face `F = F(b, J)`, `m + 2 ≤ j ≤ P`,
and `x ∈ F`, where `ψ_F` is the radial retraction of `F` from its centre onto `∂F` (Simon's
`ψ^{(j)} := ⋃ ψ_F` and `ψ^{(m+2)} ∘ ⋯ ∘ ψ^{(j)}`).  Two distinct `j`-faces through `u` meet where
`u` has a coordinate `uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, in each of them, and there both retractions
are the identity (`cmcdtsr_face_radial`); so the step map `φ_j` retracting along any `j`-face
through `u` is well defined, and `Ψ_k := Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`. -/
theorem Submission.cmcdtsr_face_retraction_family : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) ∧ ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) else x i) → Ψ j x = Ψ (j - 1) y := by
  classical
  intro P m a ha
  -- `u ∈ F(b, J)`
  let InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop := fun b J u =>
    ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i)
  -- the radial retraction `R_{b,J}` of `F(b, J)` from its centre onto `∂F(b, J)` (`id` if `J = ∅`)
  let R : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Euclid P := fun b J u =>
    if hJ : J.Nonempty then
      WithLp.toLp 2 fun i => if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
        else u i
    else u
  have hR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (u : Euclid P) (i : Fin P),
      R b J u i = if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
        else u i := by
    intro b J hJ u i
    simp only [R, dite_eq_left hJ, PiLp.toLp_apply]
  -- Step 1: if two distinct faces of the same dimension contain `u`, then `u` has a coordinate
  -- `uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, on the boundary of the first one
  have hbd : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
      InF b J u → InF b' J' u → (b, J) ≠ (b', J') → ∃ i ∈ J, u i = b i ∨ u i = b i + 1 := by
    intro b b' J J' u hcard hu hu' hne
    by_cases hJJ : J = J'
    · -- same free coordinates: `bᵢ ≠ b'ᵢ` for some `i ∈ J` and `uᵢ ∈ [bᵢ, bᵢ + 1] ∩ [b'ᵢ, b'ᵢ + 1]`
      subst hJJ
      obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h : b = b' => hne (by rw [h])
      by_cases hiJ : i ∈ J
      · refine ⟨i, hiJ, ?_⟩
        obtain ⟨h1, h2⟩ := (hu i).1 hiJ
        obtain ⟨h3, h4⟩ := (hu' i).1 hiJ
        rcases lt_or_gt_of_ne hi with hlt | hlt
        · have : (b i : ℝ) + 1 ≤ b' i := by exact_mod_cast hlt
          right; linarith
        · have : (b' i : ℝ) + 1 ≤ b i := by exact_mod_cast hlt
          left; linarith
      · exact absurd (Int.cast_injective (((hu i).2 hiJ).symm.trans ((hu' i).2 hiJ))) hi
    · -- `J ⊄ J'`: for `i ∈ J \ J'` the coordinate `uᵢ = b'ᵢ ∈ [bᵢ, bᵢ + 1]` is an integer
      obtain ⟨i, hiJ, hiJ'⟩ := Finset.not_subset.mp fun hsub =>
        hJJ (Finset.eq_of_subset_of_card_le hsub hcard.ge)
      refine ⟨i, hiJ, ?_⟩
      obtain ⟨h1, h2⟩ := (hu i).1 hiJ
      rw [(hu' i).2 hiJ'] at h1 h2 ⊢
      have h1' : b i ≤ b' i := Int.cast_le.mp h1
      have h2' : b' i ≤ b i + 1 := by
        rw [← Int.cast_le (R := ℝ), Int.cast_add, Int.cast_one]
        exact h2
      rcases h1'.eq_or_lt with h | h
      · left; rw [← h]
      · right; rw [le_antisymm h2' (Int.add_one_le_of_lt h), Int.cast_add, Int.cast_one]
  -- Step 2: at such points `R_{b,J}` is the identity (`cmcdtsr_face_radial`; `1/4 < aᵢ < 3/4`
  -- keeps `u` off the centre), so all faces of the same dimension through `u` agree
  have hfix : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P), InF b J u →
      (∃ i ∈ J, u i = b i ∨ u i = b i + 1) → R b J u = u := by
    rintro b J u hu ⟨i, hiJ, hbi⟩
    have hJ : J.Nonempty := ⟨i, hiJ⟩
    have hai := abs_lt.mp (ha i)
    have hne : ∃ i ∈ J, u i ≠ b i + a i := ⟨i, hiJ, by
      rcases hbi with h | h <;> rw [h] <;> intro h' <;> linarith [hai.1, hai.2]⟩
    exact (Submission.cmcdtsr_face_radial P a ha b J hJ (R b J) (hR b J hJ) u hu
      hne).2.2.2.2.2.1 ⟨i, hiJ, hbi⟩
  have hcons : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
      InF b J u → InF b' J' u → R b J u = R b' J' u := by
    intro b b' J J' u hcard hu hu'
    by_cases h : (b, J) = (b', J')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    · rw [hfix b J u hu (hbd b b' J J' u hcard hu hu' h),
        hfix b' J' u hu' (hbd b' b J' J u hcard.symm hu' hu (Ne.symm h))]
  -- Step 3: the step map `φ_j` applies the retraction of a chosen `j`-face through `u`
  let φ : ℕ → Euclid P → Euclid P := fun j u =>
    if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = j ∧ InF p.1 p.2 u then
      R h.choose.1 h.choose.2 u
    else u
  -- Step 4: `Ψ_k = id` for `k ≤ m + 1` and `Ψ_k = Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`
  let Ψ : ℕ → Euclid P → Euclid P := fun k =>
    Nat.rec (motive := fun _ => Euclid P → Euclid P) id
      (fun k Ψk => if k + 1 ≤ m + 1 then id else Ψk ∘ φ (k + 1)) k
  refine ⟨Ψ, fun x => ?_, ?_⟩
  · show (if m + 1 ≤ m + 1 then id else Ψ m ∘ φ (m + 1)) x = x
    rw [ite_eq_left le_rfl]
    rfl
  -- Step 5: for `x ∈ F(b, J)` the chosen face gives `φ_j(x) = R_{b,J}(x) = y`
  · intro j hj _ b J hJ hcard x hx y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr ((Nat.zero_lt_succ _).trans_le hj)
    have hk : ¬k + 1 ≤ m + 1 := Nat.not_le.mpr hj
    show (if k + 1 ≤ m + 1 then id else Ψ k ∘ φ (k + 1)) x = Ψ (k + 1 - 1) y
    rw [ite_eq_right hk, Nat.add_sub_cancel]
    have hex : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x :=
      ⟨(b, J), hcard, hx⟩
    show Ψ k (if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x then
      R h.choose.1 h.choose.2 x else x) = Ψ k y
    rw [dite_eq_left hex, hcons _ b _ J x (hex.choose_spec.1.trans hcard.symm) hex.choose_spec.2 hx]
    congr 1
    ext i
    rw [hR b J hJ x i, hy i]
/-- **Pointwise Lipschitz bound by induction over the face dimension** (Simon Ch. 6, proof of
Lemma 5.4, claim (3), p. 162; step 5 of the skeleton retraction).  For `b ∈ ℤᴾ` and `J` let
`F(b, J) = {x : bᵢ ≤ xᵢ ≤ bᵢ + 1 (i ∈ J), xᵢ = bᵢ (i ∉ J)}`, with centre `a_F` (`bᵢ + aᵢ` on `J`),
gauge `N_{b,J}` and radial retraction `ψ_{b,J}(x) = a_F + (x − a_F)/N_{b,J}(x)` onto `∂F(b, J)`.
If `Ψ_{m+1} = id` and `Ψ_j = Ψ_{j−1} ∘ ψ_{b,J}` on every `j`-face, `m + 2 ≤ j ≤ P`, then at every
`x ∈ F(b, J)` with at most `m + 1` coordinates `i ∈ J` within `ρ` of the centre, `Ψ_j(x)` lies in
`F(b, J)`, has at least `P − m − 1` integer coordinates, and `Ψ_j` is `c/ρ`-Lipschitz at `x` on
`F(b, J)`, `c = (1 + 4√P)ᴾ`.  Induction on `j`, with constant `K ^ (j − m − 1)`, `K = 1 + 4√P`:
a coordinate `ρ`-far from the centre gives `N_{b,J}(x) ≥ ρ`, and `cmcdtsr_face_radial` gives the
radial bound `(1 + 4√j)/N_{b,J}(x)`.  In the step, `y₀ = ψ_{b,J}(x)` lies on the `(j − 1)`-faces
through it, where the counting condition holds with radius `ρ/N_{b,J}(x)`; for `y` near `x`,
`ψ_{b,J}(y)` stays on these faces, and the factors `N_{b,J}(x)` cancel. -/
theorem Submission.cmcdtsr_face_count_induction : ∀ (P m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) → (∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) else x i) → Ψ j x = Ψ (j - 1) y) → ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ ρ : ℝ, 0 < ρ → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 → (∀ i, (i ∈ J → (b i : ℝ) ≤ Ψ j x i ∧ Ψ j x i ≤ b i + 1) ∧ (i ∉ J → Ψ j x i = b i)) ∧ (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧ ∀ᶠ y in 𝓝[{w : Euclid P | ∀ i, (i ∈ J → (b i : ℝ) ≤ w i ∧ w i ≤ b i + 1) ∧ (i ∉ J → w i = b i)}] x, dist (Ψ j y) (Ψ j x) ≤ c / ρ * dist y x := by
  intro P m
  have hK1 : (1 : ℝ) ≤ 1 + 4 * Real.sqrt P := by
    have := Real.sqrt_nonneg (P : ℝ); linarith
  have hc : ∀ n : ℕ, (0 : ℝ) < 1 + 4 * Real.sqrt n := fun n => by positivity
  refine ⟨(1 + 4 * Real.sqrt P) ^ P, by positivity, ?_⟩
  intro a ha Ψ hΨ0 hrec
  -- the face `F(b, J)`, its gauge `N_{b,J}` and its radial retraction `ψ_{b,J}`
  obtain ⟨InF, hInF⟩ : ∃ InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop, ∀ b J u,
      InF b J u ↔ ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i) :=
    ⟨fun b J u => ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i),
      fun _ _ _ => Iff.rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : (Fin P → ℤ) → ∀ J : Finset (Fin P), J.Nonempty → Euclid P → ℝ,
      ∀ b J hJ u, N b J hJ u =
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) :=
    ⟨fun b J hJ u =>
      J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)),
      fun _ _ _ _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (Fin P → ℤ) → ∀ J : Finset (Fin P), J.Nonempty → Euclid P → Euclid P,
      ∀ b J hJ u i, R b J hJ u i =
        if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i :=
    ⟨fun b J hJ u => WithLp.toLp 2 fun i =>
      if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i,
      fun _ _ _ _ _ => rfl⟩
  -- the recursion: `Ψ_j = Ψ_{j−1} ∘ ψ_{b,J}` on `F(b, J)`
  have hrec' : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P))
      (hJ : J.Nonempty), J.card = j → ∀ u, InF b J u → Ψ j u = Ψ (j - 1) (R b J hJ u) :=
    fun j hj hjP b J hJ hcard u hu =>
      hrec j hj hjP b J hJ hcard u ((hInF b J u).1 hu) (R b J hJ u) fun i => by rw [hR, hN]
  -- `cmcdtsr_face_radial` for `ψ_{b,J}`
  have FR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (x : Euclid P),
      InF b J x → (∃ i ∈ J, x i ≠ b i + a i) →
      (∀ k ∈ J, |x k - b k - a k| ≤ N b J hJ x) ∧ 0 < N b J hJ x ∧ InF b J (R b J hJ x) ∧
      (∃ i ∈ J, R b J hJ x i = b i ∨ R b J hJ x i = b i + 1) ∧
      ∀ y, InF b J y → (∃ i ∈ J, y i ≠ b i + a i) →
        dist (R b J hJ y) (R b J hJ x) ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := by
    intro b J hJ x hx hne
    obtain ⟨h1, h2, -, h3, h4, -, h6⟩ := Submission.cmcdtsr_face_radial P a ha b J hJ (R b J hJ)
      (fun y i => by rw [hR, hN]) x ((hInF b J x).1 hx) hne
    rw [hN, hInF]
    exact ⟨h1, h2, h3, h4, fun y hy hne' => h6 y ((hInF b J y).1 hy) hne'⟩
  -- 1(a): `|J| ≥ m + 2` and the counting condition give a coordinate `ρ`-far from the centre
  have exists_far : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), m + 2 ≤ J.card →
      ∀ (u : Euclid P) (ρ : ℝ), (J.filter (fun i => |u i - b i - a i| < ρ)).card ≤ m + 1 →
      ∃ i ∈ J, ρ ≤ |u i - b i - a i| := by
    intro b J hJc u ρ hcount
    by_contra h
    have hall : ∀ i ∈ J, |u i - b i - a i| < ρ := fun i hi => not_le.mp fun h' => h ⟨i, hi, h'⟩
    rw [Finset.filter_true_of_mem hall] at hcount
    omega
  have ne_centre : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P) (ρ : ℝ), 0 < ρ →
      (∃ i ∈ J, ρ ≤ |u i - b i - a i|) → ∃ i ∈ J, u i ≠ b i + a i := by
    rintro b J u ρ hρ ⟨i, hi, hf⟩
    refine ⟨i, hi, fun he => ?_⟩
    rw [he, show (b i : ℝ) + a i - b i - a i = 0 by ring, abs_zero] at hf
    linarith
  have count_le : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u v : Euclid P) (ρ ρ' : ℝ),
      (∀ i ∈ J', |v i - b' i - a i| < ρ' → i ∈ J ∧ |u i - b i - a i| < ρ) →
      (J'.filter (fun i => |v i - b' i - a i| < ρ')).card ≤
        (J.filter (fun i => |u i - b i - a i| < ρ)).card := by
    intro b b' J J' u v ρ ρ' h
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact h i hi.1 hi.2
  -- 1(b): the counting condition passes to nearby points with radius `ρ / 2`
  have count_near : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (x y : Euclid P) (ρ : ℝ),
      dist y x < ρ / 2 → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      (J.filter (fun i => |y i - b i - a i| < ρ / 2)).card ≤ m + 1 := by
    intro b J x y ρ hyx hcount
    refine (count_le b b J J x y ρ (ρ / 2) fun i hi h' => ⟨hi, ?_⟩).trans hcount
    have hd : |x i - y i| ≤ dist y x := by
      rw [dist_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le x y i
    calc |x i - b i - a i| = |(x i - y i) + (y i - b i - a i)| := by ring_nf
      _ ≤ |x i - y i| + |y i - b i - a i| := abs_add_le _ _
      _ < ρ := by linarith
  -- Claim(j), by induction on `j ≥ m + 2`, with constant `K ^ (j - m - 1)`, `K = 1 + 4√P`
  have hclaim : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j →
      ∀ x, InF b J x → ∀ ρ : ℝ, 0 < ρ → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      InF b J (Ψ j x) ∧
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧
      ∃ δ > 0, ∀ y, InF b J y → dist y x < δ →
        dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      -- 2. base case: `Ψ_{m+2} = ψ_{b,J}` on `F(b, J)`
      intro hP b J hcard x hx ρ hρ hcount
      have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
      have hΨ : ∀ u, InF b J u → Ψ (m + 2) u = R b J hJ u := fun u hu => by
        rw [hrec' (m + 2) le_rfl hP b J hJ hcard u hu, show m + 2 - 1 = m + 1 by omega, hΨ0]
      obtain ⟨i, hi, hfar⟩ := exists_far b J (by omega) x ρ hcount
      obtain ⟨F1, -, F3, F4, F6⟩ := FR b J hJ x hx (ne_centre b J x ρ hρ ⟨i, hi, hfar⟩)
      have hNρ : ρ ≤ N b J hJ x := hfar.trans (F1 i hi)
      refine ⟨?_, ?_, ?_⟩
      · rw [hΨ x hx]; exact F3
      · -- the coordinates off `J` and one boundary coordinate in `J` are integers
        obtain ⟨i₀, hi₀, hbd⟩ := F4
        refine ⟨insert i₀ (Finset.univ \ J), ?_, fun k hk => ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hi₀]),
            Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ, Fintype.card_fin,
            hcard]
          omega
        · rw [hΨ x hx]
          rcases Finset.mem_insert.mp hk with rfl | hk'
          · rcases hbd with h | h
            · exact ⟨b k, h⟩
            · exact ⟨b k + 1, by rw [h]; push_cast; ring⟩
          · exact ⟨b k, ((hInF b J _).1 F3 k).2 (Finset.mem_sdiff.mp hk').2⟩
      · refine ⟨ρ / 2, by positivity, fun y hy hyx => ?_⟩
        have hney := ne_centre b J y (ρ / 2) (by positivity)
          (exists_far b J (by omega) y (ρ / 2) (count_near b J x y ρ hyx hcount))
        have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
          Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
        rw [hΨ y hy, hΨ x hx, show m + 2 - m - 1 = 1 by omega, pow_one]
        calc dist (R b J hJ y) (R b J hJ x)
            ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := F6 y hy hney
          _ ≤ (1 + 4 * Real.sqrt P) / ρ * dist y x := by
            apply mul_le_mul_of_nonneg_right _ dist_nonneg
            exact div_le_div₀ (by positivity) (by linarith) hρ hNρ
    | succ j hj ih =>
      -- 3. inductive step `j → j + 1`
      intro hP b J hcard x hx ρ hρ hcount
      have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
      have hΨ : ∀ u, InF b J u → Ψ (j + 1) u = Ψ j (R b J hJ u) := fun u hu => by
        rw [hrec' (j + 1) (by omega) hP b J hJ hcard u hu, Nat.add_sub_cancel]
      obtain ⟨i, hi, hfar⟩ := exists_far b J (by omega) x ρ hcount
      obtain ⟨F1, Fpos, F3, F4, F6⟩ := FR b J hJ x hx (ne_centre b J x ρ hρ ⟨i, hi, hfar⟩)
      have hNρ : ρ ≤ N b J hJ x := hfar.trans (F1 i hi)
      have hy₀k : ∀ k ∈ J, R b J hJ x k - b k - a k = (x k - b k - a k) / N b J hJ x := by
        intro k hk
        rw [hR, ite_eq_left hk]; ring
      have hΨx : Ψ (j + 1) x = Ψ j (R b J hJ x) := hΨ x hx
      -- `y₀ = ψ_{b,J}(x) = a_F + (x − a_F) / N_{b,J}(x)`
      obtain ⟨Nx, hNx⟩ : ∃ t, N b J hJ x = t := ⟨_, rfl⟩
      obtain ⟨y₀, hy₀⟩ : ∃ y, R b J hJ x = y := ⟨_, rfl⟩
      rw [hNx] at Fpos hNρ hy₀k F6
      rw [hy₀] at F3 F4 hy₀k hΨx F6
      have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
        Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
      -- (i) the `j`-faces `F(b^{i,β}, J ∖ {i})`, `β ∈ {bᵢ, bᵢ + 1}`, lie in `F(b, J)` and contain
      -- the points of `F(b, J)` with `i`-th coordinate `β`
      have hGsub : ∀ i' ∈ J, ∀ β : ℤ, b i' ≤ β → β ≤ b i' + 1 → ∀ u,
          InF (Function.update b i' β) (J.erase i') u → InF b J u := by
        intro i' hi' β hβ1 hβ2 u hu
        rw [hInF] at hu ⊢
        intro k
        by_cases hk : k = i'
        · subst hk
          have hu2 := (hu k).2 (Finset.notMem_erase k J)
          rw [Function.update_self] at hu2
          refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hi' h⟩
          · rw [hu2]; exact_mod_cast hβ1
          · rw [hu2]
            have h2 : ((β : ℤ) : ℝ) ≤ ((b k + 1 : ℤ) : ℝ) := Int.cast_le.mpr hβ2
            push_cast at h2 ⊢
            linarith
        · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
          have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
          obtain ⟨h1, h2⟩ := hu k
          rw [hupd, hmem] at h1 h2
          exact ⟨h1, h2⟩
      have hGmem : ∀ i' u, InF b J u → ∀ β : ℤ, u i' = β →
          InF (Function.update b i' β) (J.erase i') u := by
        intro i' u hu β hβ
        rw [hInF] at hu ⊢
        intro k
        by_cases hk : k = i'
        · subst hk
          refine ⟨fun h => absurd h (Finset.notMem_erase k J), fun _ => ?_⟩
          rw [Function.update_self]; exact hβ
        · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
          have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
          rw [hupd, hmem]
          exact hu k
      -- (ii) at `y₀` the counting condition holds on these faces with radius `ρ / N_{b,J}(x)`
      have hρN : 0 < ρ / Nx := div_pos hρ Fpos
      have hGcount : ∀ i' (β : ℤ),
          ((J.erase i').filter (fun k => |y₀ k - Function.update b i' β k - a k| < ρ / Nx)).card
            ≤ m + 1 := by
        intro i' β
        refine (count_le b (Function.update b i' β) J (J.erase i') x y₀ ρ (ρ / Nx)
          fun k hk h' => ?_).trans hcount
        obtain ⟨hki, hkJ⟩ := Finset.mem_erase.mp hk
        refine ⟨hkJ, ?_⟩
        rw [Function.update_of_ne hki, hy₀k k hkJ, abs_div, abs_of_pos Fpos] at h'
        exact (div_lt_div_iff_of_pos_right Fpos).mp h'
      -- (iii) Claim(j) on every face through `y₀`
      have hIH : ∀ i' ∈ J, ∀ β : ℤ, y₀ i' = β →
          InF (Function.update b i' β) (J.erase i') (Ψ j y₀) ∧
          (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j y₀ i = z) ∧
          ∃ δ > 0, ∀ y', InF (Function.update b i' β) (J.erase i') y' → dist y' y₀ < δ →
            dist (Ψ j y') (Ψ j y₀) ≤
              (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀ :=
        fun i' hi' β hβ => ih (by omega) (Function.update b i' β) (J.erase i')
          (by rw [Finset.card_erase_of_mem hi', hcard, Nat.add_sub_cancel]) y₀
          (hGmem i' y₀ F3 β hβ) (ρ / Nx) hρN (hGcount i' β)
      -- (A) and (B) from a face through `y₀`
      obtain ⟨i₁, hi₁, hbd₁⟩ := F4
      obtain ⟨β₁, hβ₁a, hβ₁b, hβ₁e⟩ : ∃ β : ℤ, b i₁ ≤ β ∧ β ≤ b i₁ + 1 ∧ y₀ i₁ = β := by
        rcases hbd₁ with h | h
        · exact ⟨b i₁, le_rfl, by omega, h⟩
        · exact ⟨b i₁ + 1, by omega, le_rfl, by rw [h]; push_cast; ring⟩
      obtain ⟨hA₁, hB₁, -⟩ := hIH i₁ hi₁ β₁ hβ₁e
      refine ⟨?_, ?_, ?_⟩
      · rw [hΨx]; exact hGsub i₁ hi₁ β₁ hβ₁a hβ₁b _ hA₁
      · rw [hΨx]; exact hB₁
      -- (iv) one radius `η` serves every face through `y₀` and avoids the other faces
      have hev : ∀ᶠ y' in 𝓝 y₀, ∀ i' ∈ J, ∀ e : Bool,
          (y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
            InF (Function.update b i' (if e then b i' + 1 else b i')) (J.erase i') y' →
            dist (Ψ j y') (Ψ j y₀) ≤
              (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀) ∧
          (y₀ i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
            y' i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ)) := by
        rw [Filter.eventually_all_finset]
        intro i' hi'
        rw [Filter.eventually_all]
        intro e
        by_cases hβ : y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ)
        · obtain ⟨-, -, δ', hδ', hbd⟩ := hIH i' hi' _ hβ
          filter_upwards [Metric.ball_mem_nhds y₀ hδ'] with y' hy'
          exact ⟨fun _ hG => hbd y' hG (Metric.mem_ball.mp hy'), fun h => absurd hβ h⟩
        · have hpos : 0 < |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| :=
            abs_pos.mpr (sub_ne_zero.mpr hβ)
          filter_upwards [Metric.ball_mem_nhds y₀ hpos] with y' hy'
          refine ⟨fun h => absurd h hβ, fun _ heq => ?_⟩
          have h1 : |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| ≤ dist y' y₀ := by
            rw [← heq, abs_sub_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le _ _ _
          exact absurd (Metric.mem_ball.mp hy') (not_lt.mpr h1)
      obtain ⟨η, hη, hηQ⟩ := Metric.eventually_nhds_iff.mp hev
      -- (v), (vi): for `y` near `x`, `ψ_{b,J}(y)` is `η`-close to `y₀` on a face through `y₀`
      have hc1 := hc J.card
      refine ⟨min (ρ / 2) (η * Nx / (1 + 4 * Real.sqrt J.card)),
        lt_min (half_pos hρ) (div_pos (mul_pos hη Fpos) hc1), fun y hy hyx => ?_⟩
      have hyx1 : dist y x < ρ / 2 := lt_of_lt_of_le hyx (min_le_left _ _)
      have hyx2 : dist y x < η * Nx / (1 + 4 * Real.sqrt J.card) :=
        lt_of_lt_of_le hyx (min_le_right _ _)
      have hney := ne_centre b J y (ρ / 2) (by positivity)
        (exists_far b J (by omega) y (ρ / 2) (count_near b J x y ρ hyx1 hcount))
      obtain ⟨-, -, F3y, F4y, -⟩ := FR b J hJ y hy hney
      have hd := F6 y hy hney
      have hdη : dist (R b J hJ y) y₀ < η := by
        refine hd.trans_lt ?_
        rw [div_mul_eq_mul_div, div_lt_iff₀ Fpos, mul_comm (1 + 4 * Real.sqrt J.card)]
        exact (lt_div_iff₀ hc1).mp hyx2
      obtain ⟨i₂, hi₂, hbd₂⟩ := F4y
      obtain ⟨e, he⟩ : ∃ e : Bool,
          R b J hJ y i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
        rcases hbd₂ with h | h
        · exact ⟨false, by simp [h]⟩
        · exact ⟨true, by simp [h]⟩
      obtain ⟨hQ1, hQ2⟩ := hηQ hdη i₂ hi₂ e
      have hy₀β : y₀ i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
        by_contra hcon
        exact hQ2 hcon he
      have hbound := hQ1 hy₀β (hGmem i₂ _ F3y _ he)
      rw [hΨ y hy, hΨx]
      calc dist (Ψ j (R b J hJ y)) (Ψ j y₀)
          ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist (R b J hJ y) y₀ := hbound
        _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) *
              ((1 + 4 * Real.sqrt J.card) / Nx * dist y x) := by gcongr
        _ = (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt J.card) / ρ * dist y x *
              (Nx * Nx⁻¹) := by rw [div_div_eq_mul_div]; ring
        _ = (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt J.card) / ρ * dist y x := by
            rw [mul_inv_cancel₀ Fpos.ne', mul_one]
        _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt P) / ρ * dist y x := by
            gcongr
        _ = (1 + 4 * Real.sqrt P) ^ (j + 1 - m - 1) / ρ * dist y x := by
            rw [show j + 1 - m - 1 = j - m - 1 + 1 by omega, pow_succ]
  -- 0. `K ^ (j - m - 1) ≤ K ^ P = c`, and `𝓝[F(b, J)] x` contains a `δ`-ball of `F(b, J)`
  intro j hj hjP b J hcard x hx ρ hρ hcount
  obtain ⟨hA, hB, δ, hδ, hC⟩ := hclaim j hj hjP b J hcard x ((hInF b J x).2 hx) ρ hρ hcount
  refine ⟨(hInF b J _).1 hA, hB, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy hyF
  calc dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x :=
        hC y ((hInF b J y).2 hyF) (Metric.mem_ball.mp hy)
    _ ≤ (1 + 4 * Real.sqrt P) ^ P / ρ * dist y x := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      apply div_le_div_of_nonneg_right _ hρ.le
      exact pow_le_pow_right₀ hK1 (by omega)

/-- **Simon Ch. 6, Lemma 5.4** (retraction onto the `n`-skeleton away from the dual skeleton,
`n = m + 1 < P`).  `ψ := Ψ_P` is the composite of the glued radial face retractions
(`cmcdtsr_face_retraction_family`).  If `u` lies in a closed unit cube `z + [0,1]^P` and
`d(u) := dist(u, L*(a)) > 0`, then `cmcdtsr_dual_dist_count` gives the counting condition with
`ρ = d(u)/√(m+2)`, so `cmcdtsr_face_count_induction` (`j = P`, `J = univ`) keeps `ψ(u)` in that
cube (hence `|ψ(u) − u| ≤ √P`), puts it in the `n`-skeleton, and bounds
`|ψ(y) − ψ(u)| ≤ (√(m+2)·c₀/d(u))|y − u|` for `y` in the cube near `u`; by `cmcdtsr_cube_cover`
the finitely many cubes through `u` cover a neighbourhood of `u`.  If `d(x), d(y) ≥ r` and
`|x − y| < r/2`, then `d > r/2` on `[x, y]` (`d` is 1-Lipschitz) and `cmcdtsr_segment_lipschitz`
applies with `K = 2√(m+2)·c₀/r`; otherwise `|ψ(x) − ψ(y)| ≤ 2√P + |x − y| ≤ ((4√P + 1)/r)|x − y|`.
So `c = 2√(m+2)·c₀ + 4√P + 1`. -/
theorem Submission.cmcdt_skeleton_retraction : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y := by
  intro P m hmP
  obtain ⟨c₀, hc₀, hind⟩ := Submission.cmcdtsr_face_count_induction P m
  have hs : 0 < Real.sqrt (m + 2) := Real.sqrt_pos.2 (by positivity)
  have hsc : 0 ≤ Real.sqrt (m + 2) * c₀ := by positivity
  refine ⟨2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1, by positivity, fun a ha => ?_⟩
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := Submission.cmcdtsr_face_retraction_family P m a ha
  set L : Set (Euclid P) :=
    {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- the closed unit cube `z + [0,1]^P` is the `P`-face `F(z, univ)`
  have hface : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      ∀ i : Fin P, (i ∈ Finset.univ → (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) ∧
        (i ∉ Finset.univ → u i = z i) :=
    fun z u hu i => ⟨fun _ => hu i, fun h => absurd (Finset.mem_univ i) h⟩
  -- a closed unit cube has diameter `√P`
  have hdiam : ∀ (z : Fin P → ℤ) (u v : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      (∀ i, (z i : ℝ) ≤ v i ∧ v i ≤ z i + 1) → dist u v ≤ Real.sqrt P := by
    intro z u v hu hv
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (u i) (v i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : dist (u i) (v i) ≤ 1 := by
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
          nlinarith [dist_nonneg (x := u i) (y := v i)]
      _ = P := by simp
  -- step 5 on one cube: `face_induction` with `j = P`, `J = univ` and `ρ = d(u)/√(m+2)`
  have hcube : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      0 < infDist u L → (∀ i, (z i : ℝ) ≤ Ψ P u i ∧ Ψ P u i ≤ z i + 1) ∧
        (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ k : ℤ, Ψ P u i = k) ∧
        ∀ᶠ y : Euclid P in 𝓝 u, (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) →
          dist (Ψ P y) (Ψ P u) ≤ Real.sqrt (m + 2) * c₀ / infDist u L * dist y u := by
    intro z u hu hd
    obtain ⟨hA, hB, hC⟩ := hind a ha Ψ hΨ₀ hΨ P (by omega) le_rfl z Finset.univ (by simp) u
      (hface z u hu) _ (div_pos hd hs) (Submission.cmcdtsr_dual_dist_count P m a u z)
    refine ⟨fun i => (hA i).1 (Finset.mem_univ i), hB, ?_⟩
    filter_upwards [eventually_nhdsWithin_iff.1 hC] with y hy hyz
    exact (hy (hface z y hyz)).trans_eq (by rw [div_div_eq_mul_div, mul_comm c₀])
  -- the pointwise bound `D̄ψ(u) ≤ √(m+2)·c₀/d(u)`: the cubes through `u` cover a neighbourhood
  have hloc : ∀ u : Euclid P, 0 < infDist u L → ∀ᶠ y : Euclid P in 𝓝 u,
      dist (Ψ P y) (Ψ P u) ≤ Real.sqrt (m + 2) * c₀ / infDist u L * dist y u := by
    intro u hu
    obtain ⟨Z, hZu, hZ⟩ := Submission.cmcdtsr_cube_cover P u
    have hall : ∀ᶠ y : Euclid P in 𝓝 u, ∀ z ∈ Z, (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) →
        dist (Ψ P y) (Ψ P u) ≤ Real.sqrt (m + 2) * c₀ / infDist u L * dist y u :=
      (eventually_all_finset Z).2 fun z hz => (hcube z u (hZu z hz) hu).2.2
    filter_upwards [hall, hZ] with y hy hyZ
    obtain ⟨z, hz, hyz⟩ := hyZ
    exact hy z hz hyz
  -- (i): `x` and `ψ(x)` lie in the cube `⌊x⌋ + [0,1]^P`
  have hI : ∀ x : Euclid P, 0 < infDist x L →
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ P x i = z) ∧
        dist (Ψ P x) x ≤ Real.sqrt P := by
    intro x hx
    have hfl : ∀ i, ((⌊x i⌋ : ℤ) : ℝ) ≤ x i ∧ x i ≤ ⌊x i⌋ + 1 :=
      fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    obtain ⟨hA, hB, -⟩ := hcube (fun i => ⌊x i⌋) x hfl hx
    exact ⟨hB, hdiam (fun i => ⌊x i⌋) (Ψ P x) x hA hfl⟩
  refine ⟨Ψ P, hI, fun r hr hr4 x y hx hy => ?_⟩
  rcases lt_or_ge (dist x y) (r / 2) with hxy | hxy
  · -- (6a): `d > r/2` on `[x, y]`, where `ψ` is locally `(2√(m+2)·c₀/r)`-Lipschitz
    have hseg : dist (Ψ P y) (Ψ P x) ≤ 2 * Real.sqrt (m + 2) * c₀ / r * dist y x := by
      refine Submission.cmcdtsr_segment_lipschitz P (Ψ P) x y (2 * Real.sqrt (m + 2) * c₀ / r)
        (by positivity) fun t ht => ?_
      have hxw : dist x (x + t • (y - x)) ≤ dist x y := by
        calc dist x (x + t • (y - x)) = t * dist x y := by
              rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg ht.1, dist_comm, dist_eq_norm]
          _ ≤ dist x y := mul_le_of_le_one_left dist_nonneg ht.2
      have hdw : r / 2 < infDist (x + t • (y - x)) L := by
        linarith [infDist_le_infDist_add_dist (x := x) (y := x + t • (y - x)) (s := L)]
      have hdw₀ : 0 < infDist (x + t • (y - x)) L := by linarith
      filter_upwards [hloc (x + t • (y - x)) hdw₀] with w hw
      refine hw.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [div_le_div_iff₀ hdw₀ hr]
      nlinarith [mul_le_mul_of_nonneg_left hdw.le hsc]
    rw [dist_comm, dist_comm x]
    refine hseg.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hr.le)
      dist_nonneg)
    linarith [Real.sqrt_nonneg (P : ℝ)]
  · -- (6b): `|ψ(x) − ψ(y)| ≤ |ψ(x) − x| + |x − y| + |y − ψ(y)| ≤ 2√P + |x − y|`
    have h1 := (hI x (by linarith)).2
    have h2 := (hI y (by linarith)).2
    calc dist (Ψ P x) (Ψ P y) ≤ dist (Ψ P x) x + dist x y + dist y (Ψ P y) :=
          dist_triangle4 _ _ _ _
      _ ≤ 2 * Real.sqrt P + dist x y := by rw [dist_comm y]; linarith
      _ ≤ (2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1) / r * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        nlinarith [mul_nonneg hsc (dist_nonneg (x := x) (y := y)),
          mul_nonneg (Real.sqrt_nonneg (P : ℝ)) (by linarith : (0 : ℝ) ≤ 4 * dist x y - 2 * r),
          mul_nonneg (dist_nonneg (x := x) (y := y)) (by linarith : (0 : ℝ) ≤ 1 - r)]
/-- **Tube about the shifted dual skeleton** (Simon Ch. 6, proof of 5.1, the identity before
display (6), inclusion `⊆`).  Let `L*(a)` be the set of `w` with `w_i − a_i ∈ ℤ` for at least
`m + 2` indices `i`.  It contains `a`, so `infDist x L*(a) < r` gives `w ∈ L*(a)` with
`|x − w| < r`.  Enumerate `m + 2` of the indices of `w` by `e`, and put
`z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`.  Then
`Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k (x_{e(k)} − w_{e(k)})² ≤ |x − w|² < r²`. -/
theorem Submission.cmcdt_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
  classical
  intro P m hPm a x r hx
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- Steps 1–2: `a ∈ L*(a)` (all `P ≥ m + 2` indices), so some `w ∈ L*(a)` has `|x − w| < r`
  have hne : L.Nonempty := ⟨a, Finset.univ, by simp; omega, fun i _ => ⟨0, by simp⟩⟩
  obtain ⟨w, ⟨s, hs, hsz⟩, hxw⟩ := (infDist_lt_iff hne).1 hx
  -- Step 3: `m + 2` of the indices in `s`, enumerated injectively by `e`
  obtain ⟨J, hJs, hJ⟩ := Finset.exists_subset_card_eq hs
  let e : Fin (m + 2) → Fin P := fun k => J.orderEmbOfFin hJ k
  have he : Function.Injective e := (J.orderEmbOfFin hJ).injective
  have hes : ∀ k, e k ∈ s := fun k => hJs (J.orderEmbOfFin_mem hJ k)
  -- Step 4: `z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`
  choose z hz using fun k => hsz (e k) (hes k)
  refine ⟨e, he, z, ?_⟩
  have hterm : ∀ k, x (e k) - a (e k) - z k = x (e k) - w (e k) := fun k => by
    rw [← hz k]; ring
  -- Step 5: the `m + 2` selected squares are among the `P` nonnegative squares
  have hsub : ∑ k, (x (e k) - w (e k)) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    have := Finset.sum_map Finset.univ ⟨e, he⟩ (fun i => (x i - w i) ^ 2)
    simp only [Function.Embedding.coeFn_mk] at this
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  -- Step 6: `Σ_i (x_i − w_i)² = |x − w|²`
  have hdist : ∑ i, (x i - w i) ^ 2 = dist x w ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.dist_eq, sq_abs]
  have h0 : 0 ≤ dist x w := dist_nonneg
  -- Step 7
  calc ∑ k, (x (e k) - a (e k) - z k) ^ 2 = ∑ k, (x (e k) - w (e k)) ^ 2 := by
        simp_rw [hterm]
    _ ≤ ∑ i, (x i - w i) ^ 2 := hsub
    _ = dist x w ^ 2 := hdist
    _ < r ^ 2 := by nlinarith
/-- **Simon, Ch. 6, proof of 5.1** ((1)–(4) and the summation after them: the bad set of centres
is small).  Let `ρ` be a finite measure on `ℝᵈ` and `β > 0`.  Call a centre `g` of the open cube
`(1/4, 3/4)ᵈ` bad if `β rᵈ ρ(ℝᵈ) < ρ(O_r(g))` for some `r ∈ (0, 1/4]`, where
`O_r(g) = {y : |y − g − z| < r for some z ∈ ℤᵈ}` is the open `r`-neighbourhood of `g + ℤᵈ`.  Then
the bad set has Lebesgue measure at most `10ᵈ/β`.  Vitali's covering lemma gives bad centres `b`
with pairwise disjoint sup-metric balls `B(b, r_b)` such that the balls `B(b, 3r_b)` cover the bad
set.  The sets `O_{r_b}(b)` are then pairwise disjoint as well, so `Σ_b β r_bᵈ ≤ 1`, and the
bad set has measure at most `Σ_b (6r_b)ᵈ ≤ 6ᵈ/β`. -/
theorem Submission.cmcdt_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)}
  -- step 1: the periodic sets `O_r(g)` are open
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- step 2: if `ρ(ℝᵈ) = 0` the bad set is empty
  by_cases h0 : ρ univ = 0
  · have : Bad = ∅ := by
      ext g
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨-, r, -, -, hr⟩
      rw [h0, mul_zero, measure_mono_null (subset_univ _) h0] at hr
      exact lt_irrefl _ hr
    rw [this, measure_empty]
    exact bot_le
  have hfin : ρ univ ≠ ∞ := measure_ne_top ρ univ
  -- step 3: a radius `r_g` for every bad centre `g`
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- step 4: Vitali's covering lemma for the balls `B(g, r_g)`, with `τ = 2`
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- step 5: `u` is countable
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- step 6: the balls `B(b, 3 r_b)`, `b ∈ u`, cover the bad set
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- step 7: the periodic sets `O_{r_b}(b)`, `b ∈ u`, are pairwise disjoint
  have hcoord : ∀ (y g : Fin d → ℝ) (r : ℝ) (z : Fin d → ℤ),
      ∑ k, (y k - g k - z k) ^ 2 < r ^ 2 → 0 < r → ∀ k, |y k - g k - z k| < r := by
    intro y g r z h hr k
    have hk : (y k - g k - z k) ^ 2 < r ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (y i - g i - z i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)) h
    exact abs_lt_of_sq_lt_sq hk hr.le
  have hOdisj : u.PairwiseDisjoint fun b => O b (rad b) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨z', hz'⟩
    have hb0 := hrad0 b (huBad hb)
    have hb'0 := hrad0 b' (huBad hb')
    have h1 := hcoord y b (rad b) z hz hb0
    have h2 := hcoord y b' (rad b') z' hz' hb'0
    have hr1 := hrad1 b (huBad hb)
    have hr2 := hrad1 b' (huBad hb')
    -- the centres lie in `(1/4, 3/4)ᵈ` and the radii are `≤ 1/4`, so the integer shifts agree
    have hzz : z = z' := by
      funext k
      have a1 := abs_lt.1 (h1 k)
      have a2 := abs_lt.1 (h2 k)
      have a3 := abs_lt.1 ((huBad hb).1 k)
      have a4 := abs_lt.1 ((huBad hb').1 k)
      have c1 : (z k : ℝ) < z' k + 1 := by linarith
      have c2 : (z' k : ℝ) < z k + 1 := by linarith
      have c1' : z k < z' k + 1 := by exact_mod_cast c1
      have c2' : z' k < z k + 1 := by exact_mod_cast c2
      omega
    subst hzz
    -- then `y − z` lies in both balls `B(b, r_b)` and `B(b', r_{b'})`
    have hv : (fun k => y k - z k) ∈ ball b (rad b) ∩ ball b' (rad b') := by
      constructor
      · rw [mem_ball, dist_pi_lt_iff hb0]
        intro k
        rw [Real.dist_eq]
        have := h1 k
        rwa [show y k - z k - b k = y k - b k - z k by ring]
      · rw [mem_ball, dist_pi_lt_iff hb'0]
        intro k
        rw [Real.dist_eq]
        have := h2 k
        rwa [show y k - z k - b' k = y k - b' k - z k by ring]
    exact (Set.disjoint_left.1 (hudisj hb hb' hne)) hv.1 hv.2
  -- step 8: `S = Σ_{b ∈ u} β r_bᵈ ≤ 1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d)
  have hSle : S ≤ 1 := by
    have hsum : S * ρ univ ≤ 1 * ρ univ := by
      calc S * ρ univ = ∑' b : u, ENNReal.ofReal (β * rad b ^ d) * ρ univ :=
            (ENNReal.tsum_mul_right).symm
        _ ≤ ∑' b : u, ρ (O b (rad b)) :=
            ENNReal.tsum_le_tsum fun b => (hradlt b (huBad b.2)).le
        _ = ρ (⋃ b ∈ u, O b (rad b)) :=
            (measure_biUnion hucount hOdisj fun b _ => (hOopen _ _).measurableSet).symm
        _ ≤ ρ univ := measure_mono (subset_univ _)
        _ = 1 * ρ univ := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left h0 hfin).1 hsum
  -- step 9: the volume estimate
  calc volume Bad ≤ volume (⋃ b ∈ u, ball b (3 * rad b)) := measure_mono hBadsub
    _ ≤ ∑' b : u, volume (ball (b : Fin d → ℝ) (3 * rad b)) := measure_biUnion_le _ hucount _
    _ = ∑' b : u, ENNReal.ofReal (6 ^ d / β) * ENNReal.ofReal (β * rad b ^ d) := by
        refine tsum_congr fun b => ?_
        have hb0 := hrad0 b (huBad b.2)
        rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (6 ^ d / β) * S := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (6 ^ d / β) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (10 ^ d / β) := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        norm_num
/-- **Simon, Ch. 6, proof of 5.1** ((5) and the choice of `a`, cube version).  If sets
`E_e ⊆ ℝ^d`, one for each map `e : Fin d → Fin P`, have total Lebesgue outer measure
`< (1/2)^P`, then some `a` in the open cube `(1/4, 3/4)^P` has `(a_{e(k)})_k ∉ E_e` for every
injective `e`.  By Fubini over the coordinates in `range e` and the rest, the centres in the cube
whose `e`-projection lies in `E_e` have volume `≤ L^d(E_e)`; the cube has volume `(1/2)^P`, so the
union bound leaves a good centre. -/
theorem Submission.cmcdt_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
  classical
  intro P d E hsum
  -- Step 2 (Fubini): for injective `e`, the points of the cube whose `e`-projection lies in `F`
  -- have volume at most `volume F`
  have fubini : ∀ e : Fin d → Fin P, Function.Injective e → ∀ F : Set (Fin d → ℝ),
      volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ≤
        volume F := by
    intro e he F
    let p : Fin P → Prop := fun i => i ∈ range e
    let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    have hΦ : MeasurePreserving Φ := by
      convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    let σ : Fin d ≃ {i // p i} := Equiv.ofInjective e he
    let ψ := (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm
    have hψ : MeasurePreserving ψ :=
      (volume_measurePreserving_piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm _
    have hψapp : ∀ u k, ψ u k = u (σ k) := by
      intro u k
      simp [ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    let G : Set ({i // p i} → ℝ) := ψ ⁻¹' F
    let H : Set ({i // ¬ p i} → ℝ) := Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)
    have hsub : {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ⊆
        Φ ⁻¹' (G ×ˢ H) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, fun i _ => hx1 i⟩
      show ψ (fun i => x i) ∈ F
      have : ψ (fun i : {i // p i} => x i) = fun k => x (e k) := by
        funext k; rw [hψapp]; rfl
      rw [this]; exact hx2
    have hG : volume G = volume F := hψ.measure_preimage_equiv F
    have hH : volume H ≤ 1 := by
      rw [Real.volume_pi_Ioo]
      refine Finset.prod_le_one fun i _ => ?_
      rw [ENNReal.ofReal_le_one]; norm_num
    calc volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F}
        ≤ volume (Φ ⁻¹' (G ×ˢ H)) := measure_mono hsub
      _ = volume (G ×ˢ H) := hΦ.measure_preimage_equiv _
      _ = volume G * volume H := by
          rw [Measure.volume_eq_prod]; exact Measure.prod_prod G H
      _ ≤ volume G * 1 := by gcongr
      _ = volume F := by rw [mul_one, hG]
  have hI : ∀ t : ℝ, |t - 1 / 2| < 1 / 4 ↔ t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro t
    rw [abs_sub_lt_iff, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- Step 1: the open cube `Q` in `Euclid P` has volume `(1/2)^P`
  let Q : Set (Euclid P) := {a | ∀ i, a i ∈ Ioo (1 / 4 : ℝ) (3 / 4)}
  have hofLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin P)
  have hQ : volume Q = ENNReal.ofReal ((1 / 2) ^ P) := by
    have : Q = (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
        (Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext a; simp [Q, Set.mem_pi]
    rw [this, hofLp.measure_preimage_equiv, Real.volume_pi_Ioo, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  -- Step 3: the sets of centres with a bad projection
  let A : (Fin d → Fin P) → Set (Euclid P) := fun e =>
    {a | Function.Injective e ∧ a ∈ Q ∧ (fun k => a (e k)) ∈ E e}
  have hA : ∀ e, volume (A e) ≤ volume (E e) := by
    intro e
    by_cases he : Function.Injective e
    · have hsub : A e ⊆ (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
          {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ E e} := by
        rintro a ⟨-, haQ, haE⟩
        exact ⟨haQ, haE⟩
      calc volume (A e) ≤ _ := measure_mono hsub
        _ = _ := hofLp.measure_preimage_equiv _
        _ ≤ volume (E e) := fubini e he (E e)
    · have : A e = ∅ := by
        ext a; simp only [mem_empty_iff_false, iff_false]; exact fun h => he h.1
      rw [this, measure_empty]; exact bot_le
  -- Steps 4–5: union bound and choice of `a`
  by_contra hcon
  push Not at hcon
  have hcov : Q ⊆ ⋃ e, A e := by
    intro a haQ
    obtain ⟨e, he, haE⟩ := hcon a fun i => (hI _).2 (haQ i)
    exact mem_iUnion.2 ⟨e, he, haQ, haE⟩
  have : volume Q < volume Q :=
    calc volume Q ≤ volume (⋃ e, A e) := measure_mono hcov
      _ ≤ ∑ e, volume (A e) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ e, volume (E e) := Finset.sum_le_sum fun e _ => hA e
      _ < ENNReal.ofReal ((1 / 2) ^ P) := hsum
      _ = volume Q := hQ.symm
  exact lt_irrefl _ this

/-- **Simon 6.5.1, proof, (1)–(7): a good centre for the shifted dual skeleton.**  For
`m + 1 < P` there is `C = C(P, m)` such that any two finite measures `μ, μ'` on `ℝᴾ` have a common
centre `a ∈ (1/4, 3/4)ᴾ` for which the `r`-tube about
`L*(a) = {w : wᵢ − aᵢ ∈ ℤ for at least m + 2 indices i}` has `μ`-measure `≤ C r^{m+2} μ(ℝᴾ)` and
`μ'`-measure `≤ C r^{m+2} μ'(ℝᴾ)` for every `r ∈ (0, 1/4]`.  Put `d = m + 2`,
`K = #(Fin d → Fin P)`, `β = 2K·10ᵈ·2ᴾ + 1` and `prj_e x = (x_{e k})_k`.  The bad centres `E_e` of
the image measures `prj_e#μ`, `prj_e#μ'` have volume `≤ 2·10ᵈ/β` (`cmcdt_gc_bad_set_volume`), so
`Σ_e |E_e| ≤ 2K·10ᵈ/β < (1/2)ᴾ` and `cmcdt_gc_cube_selection` gives `a` with `prj_e a ∉ E_e` for
every injective `e`.  The tube lies in `⋃_e prj_e⁻¹(O_r(prj_e a))` (`cmcdt_gc_tube_cover`), where
`O_r(g)` is the union of the balls `B_r(g + z)`, `z ∈ ℤᵈ`; each piece has `ν`-measure
`≤ β rᵈ ν(ℝᴾ)` because `prj_e a` is not bad for `prj_e#ν`, hence `C = Kβ`. -/
theorem Submission.cmcdt_good_center : ∀ (P m : ℕ), m + 1 < P → ∃ C : NNReal, ∀ μ μ' : Measure (Euclid P), IsFiniteMeasure μ → IsFiniteMeasure μ' → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ univ ∧ μ' {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ' univ := by
  classical
  intro P m hPm
  -- the constants `K = #(Fin (m + 2) → Fin P)`, `β = 2K·10^{m+2}·2ᴾ + 1` and `C = Kβ`
  set K : ℕ := Fintype.card (Fin (m + 2) → Fin P) with hK
  set β : ℝ := 2 * K * 10 ^ (m + 2) * 2 ^ P + 1 with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨Real.toNNReal (K * β), ?_⟩
  intro μ μ' hμ hμ'
  -- the coordinate projections `prj_e x = (x_{e k})_k`
  let prj : (Fin (m + 2) → Fin P) → Euclid P → (Fin (m + 2) → ℝ) := fun e x k => x (e k)
  have hprj : ∀ e, Measurable (prj e) := fun e =>
    (continuous_pi fun k => PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (e k)).measurable
  -- the bad centres `g ∈ (1/4, 3/4)^{m+2}` of `ρ`: `ρ(O_r(g)) > β r^{m+2} ρ(ℝ^{m+2})` for some
  -- `r ∈ (0, 1/4]`
  let Bad : Measure (Fin (m + 2) → ℝ) → Set (Fin (m + 2) → ℝ) := fun ρ =>
    {g | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ (m + 2)) * ρ univ <
        ρ {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}}
  let E : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
    Bad (μ.map (prj e)) ∪ Bad (μ'.map (prj e))
  have hE : ∀ e, volume (E e) ≤ 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := by
    intro e
    calc volume (E e) ≤ volume (Bad (μ.map (prj e))) + volume (Bad (μ'.map (prj e))) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (10 ^ (m + 2) / β) + ENNReal.ofReal (10 ^ (m + 2) / β) :=
          add_le_add (Submission.cmcdt_gc_bad_set_volume (m + 2) _ inferInstance β hβpos)
            (Submission.cmcdt_gc_bad_set_volume (m + 2) _ inferInstance β hβpos)
      _ = 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := (two_mul _).symm
  -- so the bad sets have total volume `≤ 2K·10^{m+2}/β < (1/2)ᴾ`
  have hsum : ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) := by
    calc ∑ e, volume (E e) ≤ ∑ _e : Fin (m + 2) → Fin P, 2 * ENNReal.ofReal (10 ^ (m + 2) / β) :=
          Finset.sum_le_sum fun e _ => hE e
      _ = ENNReal.ofReal (2 * K * 10 ^ (m + 2) / β) := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal ((1 / 2) ^ P) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), div_lt_iff₀ hβpos, hβ]
          have h2 : ((1 : ℝ) / 2) ^ P * 2 ^ P = 1 := by
            rw [← mul_pow]; norm_num
          have h3 : (0 : ℝ) < (1 / 2) ^ P := by positivity
          have h4 : ((1 : ℝ) / 2) ^ P * (2 * K * 10 ^ (m + 2) * 2 ^ P + 1) =
              2 * K * 10 ^ (m + 2) * ((1 / 2) ^ P * 2 ^ P) + (1 / 2) ^ P := by ring
          rw [h4, h2]
          linarith
  -- a centre `a ∈ (1/4, 3/4)ᴾ` none of whose projections `prj_e a` (`e` injective) is bad
  obtain ⟨a, ha, hgood⟩ := Submission.cmcdt_gc_cube_selection P (m + 2) E hsum
  refine ⟨a, ha, ?_⟩
  intro r hr0 hr1
  have key : ∀ ν : Measure (Euclid P),
      (∀ e : Fin (m + 2) → Fin P, Function.Injective e → prj e a ∉ Bad (ν.map (prj e))) →
      ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤
        (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
    intro ν hνgood
    -- the periodic unions of balls `O_e = O_r(prj_e a)` and the pieces `T_e = prj_e⁻¹(O_e)`
    -- (`e` injective) of the tube
    let O : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
      {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - prj e a k - z k) ^ 2 < r ^ 2}
    let T : (Fin (m + 2) → Fin P) → Set (Euclid P) := fun e =>
      {x | Function.Injective e ∧ prj e x ∈ O e}
    have hcover : {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ⊆ ⋃ e, T e := by
      intro x hx
      obtain ⟨e, he, z, hz⟩ := Submission.cmcdt_gc_tube_cover P m hPm a x r hx
      exact mem_iUnion.2 ⟨e, he, z, hz⟩
    -- `ν(T_e) ≤ prj_e#ν(O_e) ≤ β r^{m+2} ν(ℝᴾ)`, since `prj_e a` is not bad for `prj_e#ν`
    have hT : ∀ e, ν (T e) ≤ ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
      intro e
      by_cases he : Function.Injective e
      · have hsub : T e ⊆ prj e ⁻¹' O e := fun x hx => hx.2
        have hcube : ∀ k, |prj e a k - 1 / 2| < 1 / 4 := fun k => ha (e k)
        have hle : (ν.map (prj e)) (O e) ≤
            ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := by
          by_contra hlt
          exact hνgood e he ⟨hcube, r, hr0, hr1, not_le.1 hlt⟩
        calc ν (T e) ≤ ν (prj e ⁻¹' O e) := measure_mono hsub
          _ ≤ (ν.map (prj e)) (O e) := Measure.le_map_apply (hprj e).aemeasurable _
          _ ≤ ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := hle
          _ = ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
              rw [Measure.map_apply (hprj e) MeasurableSet.univ, preimage_univ]
      · have : T e = ∅ := by
          ext x
          simp only [mem_empty_iff_false, iff_false]
          exact fun hx => he hx.1
        rw [this, measure_empty]
        exact bot_le
    -- finite subadditivity over the `K` maps `e`
    calc ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
          ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ ν (⋃ e, T e) := measure_mono hcover
      _ ≤ ∑ e, ν (T e) := measure_iUnion_fintype_le ν T
      _ ≤ ∑ _e : Fin (m + 2) → Fin P, ENNReal.ofReal (β * r ^ (m + 2)) * ν univ :=
          Finset.sum_le_sum fun e _ => hT e
      _ = (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            show ((Real.toNNReal (K * β) : ℝ≥0∞)) = ENNReal.ofReal (K * β) from rfl,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact ⟨key μ fun e he h => hgood e he (Or.inl h), key μ' fun e he h => hgood e he (Or.inr h)⟩
/-- Integer median of an integer-valued function of bounded variation on the open unit cube
(the BV facts used in Simon 6.5.1, (26)–(33)): the Poincaré inequality, the bound on the median
and the boundary estimate.  The proof works with translations: for a smooth `ψ` supported in an
open `S` whose segments `S + [0, 1] h` stay in the cube, the field `(∫₀¹ ψ(· - τh) dτ) h` is
admissible, which bounds `∫ (u(x + h) - u(x)) ψ(x) dx`; a duality argument (smooth cut-offs and
inner regularity) turns this into an `L¹` bound for translation differences.  Integrating over
`h` gives the Poincaré inequality, the least integer `β` with `|{u ≤ β}| ≥ 1/2` is a median, and
difference quotients of `G` together with slab estimates near the faces give the boundary bound. -/
theorem Submission.dtc_bc_tc_cl_dfm_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
  intro m
  /- Step 1: duality.  If `|∫ f ψ| ≤ B` for all smooth `ψ` with compact support in the open set
  `S` and `|ψ| ≤ 1`, then `∫_S |f| ≤ 2 B`: smooth cut-offs give `|∫_K f| ≤ B` for compact
  `K ⊆ S`, inner regularity extends this to measurable subsets, and we split `S` by the sign of
  `f`. -/
  have hdual : ∀ (f : Euclid (m + 1) → ℝ) (S : Set (Euclid (m + 1))) (B : ℝ), Integrable f →
      Measurable f → IsOpen S → volume S ≠ ⊤ →
      (∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
        (∀ x, |ψ x| ≤ 1) → |∫ x, f x * ψ x| ≤ B) → ∫ x in S, |f x| ≤ 2 * B := by
    intro f S B hf hfm hSo hSfin hB
    have H1 : ∀ K, IsCompact K → K ⊆ S → |∫ x in K, f x| ≤ B := by
      intro K hK hKS
      obtain ⟨δ, hδ, hδS⟩ := hK.exists_cthickening_subset_open hSo hKS
      have hr : ∀ k : ℕ, 0 < δ / (k + 2) := fun k => by positivity
      have hrδ : ∀ k : ℕ, δ / (k + 2) ≤ δ := fun k =>
        div_le_self hδ.le (by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)])
      choose ψ hψsm hψr hψs hψ1 using fun k : ℕ =>
        exists_contDiff_support_eq_eq_one_iff (n := ⊤)
          (isOpen_thickening : IsOpen (thickening (δ / (k + 2)) K))
          hK.isClosed (self_subset_thickening (hr k) K)
      have htsupp : ∀ k, tsupport (ψ k) ⊆ cthickening (δ / (k + 2)) K := fun k => by
        rw [tsupport, hψs k]; exact closure_thickening_subset_cthickening _ _
      have hψabs : ∀ k x, |ψ k x| ≤ 1 := fun k x => by
        have := hψr k (mem_range_self x)
        rw [abs_le]; exact ⟨by linarith only [this.1], this.2⟩
      have hbd : ∀ k, |∫ x, f x * ψ k x| ≤ B := fun k => hB (ψ k) (hψsm k)
          ((hK.cthickening).of_isClosed_subset (isClosed_tsupport _) (htsupp k))
          ((htsupp k).trans ((cthickening_mono (hrδ k) K).trans hδS)) (hψabs k)
      have hlim : Tendsto (fun k => ∫ x, f x * ψ k x) atTop (𝓝 (∫ x, K.indicator f x)) := by
        refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
          (fun k => hf.aestronglyMeasurable.mul (hψsm k).continuous.aestronglyMeasurable) hf.abs
          (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hψabs k x)
        · by_cases hx : x ∈ K
          · rw [indicator_of_mem hx]
            have : ∀ k, ψ k x = 1 := fun k => (hψ1 k x).1 hx
            simp only [this, mul_one, tendsto_const_nhds]
          · rw [indicator_of_notMem hx]
            obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hx
            have hev : ∀ᶠ k : ℕ in atTop, ψ k x = 0 := by
              obtain ⟨k₀, hk₀⟩ := exists_nat_gt (δ / ε)
              filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
              have hxt : x ∉ thickening (δ / (k + 2)) K := by
                intro hxt
                obtain ⟨y, hyK, hxy⟩ := mem_thickening_iff.1 hxt
                have hk2 : (k₀:ℝ) ≤ k := by exact_mod_cast hk
                have hk' : δ < ε * ((k:ℝ) + 2) := by
                  rw [div_lt_iff₀ hε] at hk₀
                  have := mul_le_mul_of_nonneg_right hk2 hε.le
                  linarith only [hk₀, this, hε]
                have : δ / (k + 2) < ε := by
                  rw [div_lt_iff₀ (by positivity)]; linarith only [hk']
                exact hball (mem_ball.2 (by rw [dist_comm]; linarith only [hxy, this])) hyK
              rw [← hψs k] at hxt
              exact notMem_support.1 hxt
            exact tendsto_const_nhds.congr' (by
              filter_upwards [hev] with k hk; rw [hk, mul_zero])
      rw [integral_indicator hK.isClosed.measurableSet] at hlim
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have H2 : ∀ T, MeasurableSet T → T ⊆ S → |∫ x in T, f x| ≤ B := by
      intro T hT hTS
      have hTfin : volume T ≠ ⊤ := ne_top_of_le_ne_top hSfin (measure_mono hTS)
      have : ∀ j : ℕ, ∃ K ⊆ T, IsCompact K ∧ volume T < volume K + ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
        fun j => hT.exists_isCompact_lt_add hTfin
          (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      choose K hKT hKc hKlt using this
      have hdiff : Tendsto (fun j => volume (T \ K j)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) (fun _ => bot_le)
          (fun j => ?_)
        rw [Function.comp_apply, measure_sdiff (hKT j)
          (hKc j).isClosed.measurableSet.nullMeasurableSet
          (ne_top_of_le_ne_top hTfin (measure_mono (hKT j)))]
        exact tsub_le_iff_left.2 (hKlt j).le
      have hconv := hf.tendsto_setIntegral_nhds_zero hdiff
      have hle : ∀ j, |∫ x in T, f x| ≤ B + |∫ x in T \ K j, f x| := fun j => by
        rw [← union_sdiff_cancel (hKT j), setIntegral_union disjoint_sdiff_right
          (hT.diff (hKc j).isClosed.measurableSet) hf.integrableOn hf.integrableOn,
          union_sdiff_cancel (hKT j)]
        have := H1 (K j) (hKc j) ((hKT j).trans hTS)
        exact (abs_add_le _ _).trans (by linarith only [this])
      have hconv' : Tendsto (fun j => B + |∫ x in T \ K j, f x|) atTop (𝓝 (B + |0|)) :=
        tendsto_const_nhds.add ((continuous_abs.tendsto 0).comp hconv)
      rw [abs_zero, add_zero] at hconv'
      exact ge_of_tendsto' hconv' hle
    have hP : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hfm
    have hSm := hSo.measurableSet
    have e : ∫ x in S, |f x| =
        (∫ x in S ∩ {x | 0 ≤ f x}, f x) - ∫ x in S \ {x | 0 ≤ f x}, f x := by
      rw [← integral_inter_add_sdiff hP hf.abs.integrableOn, sub_eq_add_neg, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun (hSm.inter hP) (fun x hx => abs_of_nonneg hx.2)
      · exact setIntegral_congr_fun (hSm.diff hP) (fun x hx => abs_of_neg (not_le.1 hx.2))
    rw [e]
    have h1 := H2 _ (hSm.inter hP) inter_subset_left
    have h2 := H2 _ (hSm.diff hP) sdiff_subset
    linarith only [h1, h2, le_abs_self (∫ x in S ∩ {x | 0 ≤ f x}, f x),
      neg_abs_le (∫ x in S \ {x | 0 ≤ f x}, f x)]
  /- Step 2: the segment average `Ψ z = ∫₀¹ ψ (z - τ h) dτ` of a smooth compactly supported `ψ`
  is smooth, and its derivative in the direction `h` is `ψ z - ψ (z - h)`. -/
  have hΨd : ∀ (h : Euclid (m + 1)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ z, HasFDerivAt (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h))
        (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) z := by
    intro h F _ _ _ ψ hψ hψc z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hψc.fderiv ℝ)
    have hsc : Continuous fun τ : ℝ => τ • h := continuous_id.smul continuous_const
    have hcont : ∀ x : Euclid (m + 1), Continuous fun τ : ℝ => ψ (x - τ • h) := fun x =>
      hψ.continuous.comp (continuous_const.sub hsc)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (μ := volume.restrict (Ioc (0:ℝ) 1)) (F := fun x τ => ψ (x - τ • h))
      (F' := fun x τ => fderiv ℝ ψ (x - τ • h)) (bound := fun _ => C) (s := univ)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable
    · exact (hcont z).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact ((hdc.comp (continuous_const.sub hsc)).stronglyMeasurable
        (h := secondCountableTopologyEither_of_left ℝ _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun τ x _ => hC _
    · exact integrableOn_const (by simp)
    · refine Filter.Eventually.of_forall fun τ x _ => ?_
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x - τ • h)) (x - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 := h1.comp x ((hasFDerivAt_id x).sub_const (τ • h))
      rwa [ContinuousLinearMap.comp_id] at h2
  have hΨs : ∀ (h : Euclid (m + 1)) (k : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ContDiff ℝ k (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) := by
    intro h k
    induction k with
    | zero =>
      intro F _ _ _ ψ hψ hψc
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
        (hΨd h F ψ hψ hψc z).continuousAt)
    | succ k ih =>
      intro F _ _ _ ψ hψ hψc
      have hfd : fderiv ℝ (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) =
          fun z => ∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h) :=
        funext fun z => (hΨd h F ψ hψ hψc z).fderiv
      refine contDiff_succ_iff_fderiv.2 ⟨fun z => (hΨd h F ψ hψ hψc z).differentiableAt,
        fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
      rw [hfd]
      exact ih (Euclid (m + 1) →L[ℝ] F) (fderiv ℝ ψ) (contDiff_infty_iff_fderiv.1 hψ).2
        (hψc.fderiv ℝ)
  have hΨh : ∀ (h : Euclid (m + 1)) (ψ : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ∀ z, (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) h = ψ z - ψ (z - h) := by
    intro h ψ hψ z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    have hLc : Continuous fun τ : ℝ => fderiv ℝ ψ (z - τ • h) :=
      hdc.comp (continuous_const.sub (continuous_id.smul continuous_const))
    rw [ContinuousLinearMap.integral_apply (hLc.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      ← intervalIntegral.integral_of_le zero_le_one]
    have hderiv : ∀ τ ∈ uIcc (0:ℝ) 1, HasDerivAt (fun τ : ℝ => ψ (z - τ • h))
        (-(fderiv ℝ ψ (z - τ • h) h)) τ := by
      intro τ _
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (z - τ • h)) (z - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 : HasDerivAt (fun τ : ℝ => z - τ • h) (-h) τ := by
        have := ((hasDerivAt_id τ).smul_const h).const_sub z
        rwa [one_smul] at this
      have := h1.comp_hasDerivAt τ h2
      rwa [map_neg] at this
    have hint : IntervalIntegrable (fun τ : ℝ => -(fderiv ℝ ψ (z - τ • h) h)) volume 0 1 :=
      (((ContinuousLinearMap.apply ℝ ℝ h).continuous.comp hLc).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_neg, one_smul, zero_smul, sub_zero] at this
    linarith only [this]
  /- Step 3: the constants: `R` bounds the diameter of the cube, `CP` is the Poincaré constant. -/
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = m + 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR_def]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨CP, hCP_def⟩ : ∃ CP : ℝ,
      CP = 4 * R * (volume (closedBall (0 : Euclid (m + 1)) R)).toReal := ⟨_, rfl⟩
  have hCP : 0 ≤ CP := by rw [hCP_def]; positivity
  refine ⟨CP + (m + 1) * (10 + 4 * CP) + 1, by positivity, ?_⟩
  intro u V hint huQ hV
  set Q := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} with hQ_def
  /- Step 4: the cube, `V ≥ 0`, and a measurable version `ub` of `u 1_Q`. -/
  have hQo : IsOpen Q := by
    have : Q = ⋂ i, {y : Euclid (m + 1) | 0 < y i ∧ y i < 1} := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_iInter]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQvol : volume Q = 1 := by
    have : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ => Ioo (0:ℝ) 1) := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_preimage, mem_univ_pi, mem_Ioo]
    rw [this, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hQfin : volume Q ≠ ⊤ := by rw [hQvol]; exact ENNReal.one_ne_top
  have hV0 : 0 ≤ V := by
    have := hV (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa using this
  obtain ⟨ub, hub_meas, hub_int, hub_zero, hub_ae⟩ : ∃ ub : Euclid (m + 1) → ℝ, Measurable ub ∧
      Integrable ub ∧ (∀ y ∉ Q, ub y = 0) ∧ ∀ᵐ y ∂(volume.restrict Q), ub y = u y := by
    refine ⟨Q.indicator (huQ.aestronglyMeasurable.mk u),
      huQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator hQm, ?_,
      fun y hy => indicator_of_notMem hy _, ?_⟩
    · rw [integrable_indicator_iff hQm]
      exact huQ.congr huQ.aestronglyMeasurable.ae_eq_mk
    · filter_upwards [huQ.aestronglyMeasurable.ae_eq_mk, ae_restrict_mem hQm] with y hy hyQ
      rw [indicator_of_mem hyQ, ← hy]
  /- Step 5: the weak translation estimate.  If `S` is open, `S + [0, 1] h ⊆ Q`, and every line
  parallel to `h` meets `S` in parameter length `≤ lam`, then the field
  `g = (lam ‖h‖)⁻¹ Ψ h` is admissible and `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`. -/
  have hweak : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam → h ≠ 0 →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      (∀ x, |ψ x| ≤ 1) → -∫ x, (ub (x + h) - ub x) * ψ x ≤ lam * ‖h‖ * V := by
    intro S h lam hSo hseg hlam hh0 hmult ψ hψ hψc hψS hψ1
    have hA : 0 < lam * ‖h‖ := mul_pos hlam (norm_pos_iff.2 hh0)
    obtain ⟨Ψ, hΨ_def⟩ : ∃ Ψ : Euclid (m + 1) → ℝ,
        Ψ = fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : Euclid (m + 1) → Euclid (m + 1),
        g = fun z => ((lam * ‖h‖)⁻¹ * Ψ z) • h := ⟨_, rfl⟩
    have hΨsm : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
      rw [hΨ_def]; exact contDiff_infty.2 fun k => hΨs h k ℝ ψ hψ hψc
    have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := by
      rw [hg_def]; exact (contDiff_const.mul hΨsm).smul contDiff_const
    -- `g` is supported in the compact set `spt ψ + [0, 1] h ⊆ Q`
    obtain ⟨K, hK_def⟩ : ∃ K : Set (Euclid (m + 1)),
        K = (fun p : Euclid (m + 1) × ℝ => p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0:ℝ) 1) :=
      ⟨_, rfl⟩
    have hKc : IsCompact K := by
      rw [hK_def]
      exact (hψc.isCompact.prod isCompact_Icc).image
        (continuous_fst.add (continuous_snd.smul continuous_const))
    have hKQ : K ⊆ Q := by
      rw [hK_def]
      rintro _ ⟨⟨x, τ⟩, ⟨hx, hτ⟩, rfl⟩
      exact hseg x (hψS hx) τ hτ
    have hgK : ∀ z ∉ K, g z = 0 := by
      intro z hz
      have : Ψ z = 0 := by
        rw [hΨ_def]
        refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
        by_contra hne
        refine hz (hK_def ▸ ⟨⟨z - τ • h, τ⟩, ⟨subset_tsupport _ hne, Ioc_subset_Icc_self hτ⟩, ?_⟩)
        exact sub_add_cancel z (τ • h)
      rw [hg_def]; simp only [this, mul_zero, zero_smul]
    have hgc : HasCompactSupport g := HasCompactSupport.intro hKc hgK
    have hgQ : tsupport g ⊆ Q := (closure_minimal (fun z hz => by
      by_contra hzK; exact hz (hgK z hzK)) hKc.isClosed).trans hKQ
    -- `|Ψ| ≤ lam`, hence `‖g‖ ≤ 1`
    have hΨb : ∀ z, |Ψ z| ≤ lam := by
      intro z
      have hmeas : MeasurableSet {τ : ℝ | z - τ • h ∈ S} :=
        (hSo.preimage (continuous_const.sub (continuous_id.smul continuous_const))).measurableSet
      rw [hΨ_def]
      calc |∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)| = ‖∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)‖ := rfl
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, ‖ψ (z - τ • h)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _)
            ((integrable_indicator_iff hmeas).2 (integrable_const (1:ℝ)).integrableOn) ?_
          refine Filter.Eventually.of_forall fun τ => ?_
          show ‖ψ (z - τ • h)‖ ≤ {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ
          by_cases hτ : z - τ • h ∈ S
          · rw [indicator_of_mem (show τ ∈ {τ : ℝ | z - τ • h ∈ S} from hτ), Pi.one_apply]
            exact hψ1 (z - τ • h)
          · rw [indicator_of_notMem (show τ ∉ {τ : ℝ | z - τ • h ∈ S} from hτ),
              image_eq_zero_of_notMem_tsupport (fun h' => hτ (hψS h')), norm_zero]
        _ = (volume.restrict (Ioc (0:ℝ) 1)).real {τ : ℝ | z - τ • h ∈ S} :=
          integral_indicator_one hmeas
        _ ≤ lam := by
          rw [Measure.real, Measure.restrict_apply hmeas]
          exact ENNReal.toReal_le_of_le_ofReal hlam.le (hmult z)
    have hgb : ∀ z, ‖g z‖ ≤ 1 := by
      intro z
      rw [hg_def, norm_smul, norm_mul, norm_inv, Real.norm_of_nonneg hA.le, Real.norm_eq_abs]
      calc (lam * ‖h‖)⁻¹ * |Ψ z| * ‖h‖ ≤ (lam * ‖h‖)⁻¹ * lam * ‖h‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΨb z) (inv_nonneg.2 hA.le))
              (norm_nonneg h)
        _ = 1 := by rw [mul_assoc, inv_mul_cancel₀ hA.ne']
    -- `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`
    have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z) =
        (lam * ‖h‖)⁻¹ * (ψ z - ψ (z - h)) := by
      intro z
      have hd : HasFDerivAt g (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
          fderiv ℝ ψ (z - τ • h)).smulRight h) z := by
        rw [hg_def, hΨ_def]
        exact ((hΨd h ℝ ψ hψ hψc z).const_mul (lam * ‖h‖)⁻¹).smul_const h
      rw [hd.fderiv]
      refine (LinearMap.trace_smulRight (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
        fderiv ℝ ψ (z - τ • h) : Euclid (m + 1) →L[ℝ] ℝ) : Euclid (m + 1) →ₗ[ℝ] ℝ) h).trans ?_
      rw [ContinuousLinearMap.coe_coe, smul_apply, hΨh h ψ hψ z, smul_eq_mul]
    -- the hypothesis applied to `g`
    have hψb : ∀ x, ‖ψ x‖ ≤ 1 := hψ1
    have hint1 : Integrable fun x => ub x * ψ x :=
      hub_int.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hψb)
    have hint2 : Integrable fun x => ub x * ψ (x - h) :=
      hub_int.mul_bdd (hψ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => hψb _)
    have hint3 : Integrable fun x => ub (x + h) * ψ x :=
      (hub_int.comp_add_right h).mul_bdd hψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hψb)
    have key := hV g hgsm hgc hgQ hgb
    have e1 : ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) =
        (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
      calc ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)
          = ∫ y in Q, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) := by
            refine integral_congr_ae ?_
            filter_upwards [hub_ae] with y hy
            rw [htr y, hy]
        _ = ∫ y, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
              rw [hub_zero y hy, zero_mul]
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ y, ub y * ψ (y - h)) := by
            rw [← integral_sub hint1 hint2, ← integral_const_mul]
            congr 1; funext y; ring
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ x, ub (x + h) * ψ x) := by
            congr 2
            rw [← integral_add_right_eq_self (fun y => ub y * ψ (y - h)) h]
            simp only [add_sub_cancel_right]
        _ = (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
            rw [← integral_sub hint1 hint3, ← integral_neg]
            congr 2; funext x; ring
    rw [e1] at key
    have := mul_le_mul_of_nonneg_left key hA.le
    rwa [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
  /- Step 6: the `L¹` translation estimate `∫_S |ub (x + h) - ub x| ≤ 2 lam ‖h‖ V`. -/
  have hGEN : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∫ x in S, |ub (x + h) - ub x| ≤ 2 * (lam * ‖h‖ * V) := by
    intro S h lam hSo hseg hlam hmult
    by_cases hh : h = 0
    · subst hh; simp
    have hSQ : S ⊆ Q := fun x hx => by
      have := hseg x hx 0 ⟨le_rfl, zero_le_one⟩; rwa [zero_smul, add_zero] at this
    have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hSQ)
    refine hdual (fun x => ub (x + h) - ub x) S (lam * ‖h‖ * V)
      ((hub_int.comp_add_right h).sub hub_int)
      ((hub_meas.comp (measurable_add_const h)).sub hub_meas) hSo hSfin ?_
    intro ψ hψ hψc hψS hψ1
    have h1 := hweak S h lam hSo hseg hlam hh hmult ψ hψ hψc hψS hψ1
    have h2 := hweak S h lam hSo hseg hlam hh hmult (-ψ) hψ.neg hψc.neg
      (by rwa [tsupport_neg]) (fun x => by rw [Pi.neg_apply, abs_neg]; exact hψ1 x)
    have e2 : ∫ x, (ub (x + h) - ub x) * (-ψ) x = -∫ x, (ub (x + h) - ub x) * ψ x := by
      rw [← integral_neg]; congr 1; funext x; rw [Pi.neg_apply]; ring
    rw [e2] at h2
    rw [abs_le]; constructor <;> linarith only [h1, h2]
  clear hweak hdual hΨh hΨs hΨd
  /- Step 7: the Poincaré inequality.  Translating `y = x + h` and swapping the integrals,
  `∫_Q ∫_Q |ub y - ub x| ≤ ∫_{‖h‖ ≤ R} 2 ‖h‖ V dh`. -/
  have hnormle : ∀ v : Euclid (m + 1), (∀ i, |v i| ≤ 1) → ‖v‖ ≤ R := by
    intro v hv
    have h1 : ‖v‖ ^ 2 ≤ R := by
      rw [EuclideanSpace.norm_sq_eq, hR_def]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1:ℝ) := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]; exact (sq_le_one_iff_abs_le_one _).2 (hv i)
        _ = m + 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
              Nat.cast_add, Nat.cast_one]
    exact (sq_le_sq₀ (norm_nonneg v) hR.le).1 (h1.trans (le_self_pow₀ hR1 two_ne_zero))
  have hnorm : ∀ x h : Euclid (m + 1), x ∈ Q → x + h ∈ Q → ‖h‖ ≤ R := fun x h hx hxh =>
    hnormle h fun i => by
      have h1 := hx i; have h2 := hxh i
      rw [PiLp.add_apply] at h2
      rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hnormQ : ∀ y ∈ Q, ‖y‖ ≤ R := fun y hy =>
    hnormle y fun i => abs_le.2 ⟨by linarith only [(hy i).1], (hy i).2.le⟩
  have hsegA : ∀ h : Euclid (m + 1), ∀ x ∈ (fun x => x + h) ⁻¹' Q ∩ Q,
      ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q := by
    rintro h x ⟨hxh, hx⟩ τ ⟨hτ0, hτ1⟩ i
    have h1 := hx i; have h2 := hxh i
    rw [PiLp.add_apply] at h2
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases le_total 0 (h i) with hhi | hhi
    · have p1 := mul_nonneg hτ0 hhi
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) hhi
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
    · have p1 := mul_nonneg hτ0 (neg_nonneg.2 hhi)
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) (neg_nonneg.2 hhi)
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
  have hAo : ∀ h : Euclid (m + 1), IsOpen ((fun x => x + h) ⁻¹' Q ∩ Q) := fun h =>
    (hQo.preimage (continuous_id.add continuous_const)).inter hQo
  have hTR : ∀ h : Euclid (m + 1),
      ∫ x in (fun x => x + h) ⁻¹' Q ∩ Q, |ub (x + h) - ub x| ≤ 2 * (‖h‖ * V) := by
    intro h
    have := hGEN _ h 1 (hAo h) (hsegA h) one_pos (fun z => by
      rw [ENNReal.ofReal_one]
      exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_one]))
    rwa [one_mul] at this
  have hJ : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| ≤
      ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) := by
    have hΦ : (Function.uncurry fun x h : Euclid (m + 1) =>
          Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) =
        {p : Euclid (m + 1) × Euclid (m + 1) | p.2 + p.1 ∈ Q}.indicator
          (fun p => ENNReal.ofReal |ub (p.2 + p.1) - ub p.1|) := by
      funext ⟨x, h⟩
      simp only [Function.uncurry_apply_pair, Set.indicator_apply, mem_ofPred_eq]
    have hΦm : Measurable (Function.uncurry fun x h : Euclid (m + 1) =>
        Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) := by
      rw [hΦ]
      exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        ((hub_meas.comp (measurable_snd.add measurable_fst)).sub
          (hub_meas.comp measurable_fst)))).indicator
        (hQm.preimage (measurable_snd.add measurable_fst))
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x|
        = ∫⁻ x in Q, ∫⁻ h, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_indicator hQm, lintegral_add_right_eq_self]
      _ = ∫⁻ h, ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) :=
          lintegral_lintegral_swap hΦm.aemeasurable
      _ ≤ ∫⁻ h, (closedBall (0 : Euclid (m + 1)) R).indicator
            (fun _ => ENNReal.ofReal (2 * (R * V))) h := by
          refine lintegral_mono fun h => ?_
          have hAm := (hAo h).measurableSet
          have e1 : ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) =
              ∫⁻ x in (fun x => x + h) ⁻¹' Q ∩ Q, ENNReal.ofReal |ub (x + h) - ub x| := by
            rw [← Measure.restrict_restrict (hQm.preimage (measurable_add_const h)),
              ← lintegral_indicator (hQm.preimage (measurable_add_const h))]
            refine lintegral_congr fun x => ?_
            rw [add_comm h x]
            by_cases hx : x + h ∈ Q
            · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ (fun x => x + h) ⁻¹' Q from hx)]
            · rw [indicator_of_notMem hx,
                indicator_of_notMem (show x ∉ (fun x => x + h) ⁻¹' Q from hx)]
          have hint : IntegrableOn (fun x => |ub (x + h) - ub x|) ((fun x => x + h) ⁻¹' Q ∩ Q) :=
            ((hub_int.comp_add_right h).sub hub_int).abs.integrableOn
          rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => abs_nonneg _)]
          by_cases hh : h ∈ closedBall (0 : Euclid (m + 1)) R
          · rw [indicator_of_mem hh]
            refine ENNReal.ofReal_le_ofReal ((hTR h).trans ?_)
            have : ‖h‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hh
            have := mul_le_mul_of_nonneg_right this hV0
            linarith only [this]
          · rw [indicator_of_notMem hh]
            have hempty : (fun x => x + h) ⁻¹' Q ∩ Q = ∅ := by
              refine Set.eq_empty_of_forall_notMem fun x hx => hh ?_
              rw [mem_closedBall, dist_zero_right]; exact hnorm x h hx.2 hx.1
            rw [hempty, Measure.restrict_empty, integral_zero_measure, ENNReal.ofReal_zero]
      _ = ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) :=
          lintegral_indicator_const measurableSet_closedBall _
  clear hsegA hAo hnormle
  /- Step 8: the integer median `β`: the least integer with `|{ub ≤ β} ∩ Q| ≥ 1/2`. -/
  have hμprob : IsProbabilityMeasure (volume.restrict Q) :=
    isProbabilityMeasure_iff.2 (by rw [Measure.restrict_apply_univ, hQvol])
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = ∫ y in Q, |ub y| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM_def ▸ integral_nonneg fun y => abs_nonneg _
  have hmarkov : ∀ ε : ℝ, ε * (volume.restrict Q).real {y | ε ≤ |ub y|} ≤ M := fun ε =>
    hM_def ▸ mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
      hub_int.integrableOn.abs ε
  have hmeasle : ∀ c : ℝ, MeasurableSet {y | ub y ≤ c} := fun c =>
    measurableSet_le hub_meas measurable_const
  have hmeasge : ∀ c : ℝ, MeasurableSet {y | c ≤ ub y} := fun c =>
    measurableSet_le measurable_const hub_meas
  have hlow : ∀ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} → -(2 * M) ≤ k := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (volume.restrict Q).real {y | ub y ≤ k} ≤
        (volume.restrict Q).real {y | -(k:ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y (hy : ub y ≤ k) => by
        show -(k:ℝ) ≤ |ub y|; linarith only [hy, neg_abs_le (ub y)])
    have h3 := mul_le_mul_of_nonneg_left (hk.trans h1)
      (by linarith only [hlt, hM0] : (0:ℝ) ≤ -(k:ℝ))
    linarith only [hmarkov (-(k:ℝ)), h3, hlt]
  have hex : ∃ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} := by
    refine ⟨⌊2 * M⌋ + 1, ?_⟩
    have hk₀ : 2 * M < ((⌊2 * M⌋ + 1 : ℤ) : ℝ) := by
      rw [Int.cast_add, Int.cast_one]; exact Int.lt_floor_add_one _
    have h2 : (volume.restrict Q).real {y | ub y ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y hy => by
        rw [mem_compl_iff, mem_ofPred_eq, not_le] at hy
        exact hy.le.trans (le_abs_self _))
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    by_contra h4
    rw [not_le] at h4
    have h5 := mul_le_mul_of_nonneg_left (show 1/2 ≤ (volume.restrict Q).real
      {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} by linarith only [h2, h3, h4])
      (by linarith only [hk₀, hM0] : (0:ℝ) ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    linarith only [h5, hmarkov ((⌊2 * M⌋ + 1 : ℤ) : ℝ), hk₀]
  obtain ⟨β, hβP, hβmin⟩ := Int.exists_least_of_bdd ⟨⌊-(2 * M)⌋, fun k hk =>
    Int.cast_le.1 ((Int.floor_le _).trans (hlow k hk))⟩ hex
  have hβge : 1/2 ≤ (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
    have hβ1 : ¬ (1/2 ≤ (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}) := fun h => by
      have := hβmin (β - 1) h; omega
    rw [not_le] at hβ1
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((β - 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    have h4 : (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
      rw [measureReal_def, measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hub_ae] with y hy
      intro hy'
      obtain ⟨z, hz⟩ := hint y
      rw [mem_compl_iff, mem_ofPred_eq, not_le, hy, hz] at hy'
      show (β:ℝ) ≤ ub y
      rw [hy, hz]
      have : β - 1 < z := by exact_mod_cast hy'
      exact_mod_cast (show β ≤ z by omega)
    linarith only [h3, h4, hβ1]
  have hβabs : |(β:ℝ)| ≤ 2 * M := by
    rcases le_or_gt 0 (β:ℝ) with h0 | h0
    · rw [abs_of_nonneg h0]
      have h2 : (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} ≤
          (volume.restrict Q).real {y | (β:ℝ) ≤ |ub y|} :=
        measureReal_mono fun y (hy : (β:ℝ) ≤ ub y) => hy.trans (le_abs_self _)
      linarith only [mul_le_mul_of_nonneg_left (hβge.trans h2) h0, hmarkov β]
    · rw [abs_of_neg h0]; linarith only [hlow β hβP]
  have hhalf : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → 1/2 ≤ (volume.restrict Q).real s →
      (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) := by
    intro s hs h
    rw [← Measure.restrict_apply hs, ← ofReal_measureReal (measure_ne_top _ _)]
    calc (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hhalf1 := hhalf _ (hmeasle β) hβP
  have hhalf2 := hhalf _ (hmeasge β) hβge
  -- `|ub x - β| ≤ 2 ∫_Q |ub y - ub x| dy`, since `β` is a median
  have hpt : ∀ x, ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
    intro x
    have hhalf' : ∀ a : ℝ≥0∞, a = 2 * (a * (1/2)) := fun a => by
      rw [one_div, mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
        mul_one]
    have hgm : Measurable fun y => ENNReal.ofReal |ub y - ub x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hub_meas.sub measurable_const))
    have key : ∀ s : Set (Euclid (m + 1)), (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) →
        (∀ y ∈ s, |ub x - β| ≤ |ub y - ub x|) →
        ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
      intro s hs hle
      rw [hhalf' (ENNReal.ofReal |ub x - β|)]
      refine mul_le_mul_right ?_ 2
      calc ENNReal.ofReal |ub x - β| * (1/2) ≤ ENNReal.ofReal |ub x - β| * volume (s ∩ Q) :=
            mul_le_mul_right hs _
        _ = ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub x - β| := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub y - ub x| :=
            setLIntegral_mono hgm fun y hy => ENNReal.ofReal_le_ofReal (hle y hy.1)
        _ ≤ ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono_set inter_subset_right
    rcases le_total (β:ℝ) (ub x) with hx | hx
    · refine key _ hhalf1 fun y (hy : ub y ≤ β) => ?_
      rw [abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm]
      exact (by linarith only [hy] : ub x - β ≤ ub x - ub y).trans (le_abs_self _)
    · refine key _ hhalf2 fun y (hy : (β:ℝ) ≤ ub y) => ?_
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx)]
      exact (by linarith only [hy] : β - ub x ≤ ub y - ub x).trans (le_abs_self _)
  have hP1 : ∫ y in Q, |ub y - β| ≤ CP * V := by
    have hlin : ∫⁻ x in Q, ENNReal.ofReal |ub x - β| ≤
        2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R)) := by
      calc ∫⁻ x in Q, ENNReal.ofReal |ub x - β|
          ≤ ∫⁻ x in Q, 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono hpt
        _ = 2 * ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| :=
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
        _ ≤ _ := mul_le_mul_right hJ 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => |ub y - (β:ℝ)|)
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (continuous_abs.measurable.comp (hub_meas.sub measurable_const)).aestronglyMeasurable]
    calc (∫⁻ x in Q, ENNReal.ofReal |ub x - β|).toReal
        ≤ (2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne)) hlin
      _ = CP * V := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofNat, hCP_def]; ring
  have hβM : |(β:ℝ)| ≤ 2 * ∫ y in Q, |u y| := by
    have : ∫ y in Q, |u y| = M := by
      rw [hM_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hβabs
  clear hpt hhalf hhalf1 hhalf2 hlow hex hβmin hβge hβP hβabs hmarkov hJ hmeasle hmeasge hμprob
    hM0 hM_def hint
  /- Step 9: slabs `{y ∈ Q | a < y i < a + s}`.  Translating along `e i` compares the integrals
  of `|ub - β|` over two slabs of width `s` up to `2 s V`; averaging over the `N` slabs of width
  `1/N` bounds a boundary slab by `(∫_Q |ub - β| + 2 V) / N`. -/
  have hcoord : ∀ (i j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
      (x + t • EuclideanSpace.single i (1:ℝ)) j = if j = i then x j + t else x j := by
    intro i j x t
    by_cases hj : j = i <;> simp [hj]
  have hslabo : ∀ (i : Fin (m + 1)) (a s : ℝ),
      IsOpen {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := by
    intro i a s
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact hQo.inter ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
  have hslab : ∀ (i : Fin (m + 1)) (s a a' : ℝ), 0 < s → 0 ≤ a → a + s ≤ 1 → 0 ≤ a' →
      a' + s ≤ 1 →
      ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s}, |ub y - β| ≤
        (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s}, |ub y - β|) +
          2 * (s * V) := by
    intro i s a a' hs ha has ha' has'
    rcases eq_or_ne a a' with haa | haa
    · subst haa; linarith only [mul_nonneg hs.le hV0]
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = a' - a := ⟨_, rfl⟩
    have ht : t ≠ 0 := by rw [ht_def]; exact sub_ne_zero.2 (Ne.symm haa)
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (r : ℝ),
        (x + r • e) j = if j = i then x j + r else x j := by
      subst he_def; exact fun j x r => hcoord i j x r
    obtain ⟨S, hS_def⟩ : ∃ S : Set (Euclid (m + 1)),
        S = {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := ⟨_, rfl⟩
    obtain ⟨S', hS'_def⟩ : ∃ S' : Set (Euclid (m + 1)),
        S' = {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s} := ⟨_, rfl⟩
    rw [← hS_def, ← hS'_def]
    have hSo : IsOpen S := hS_def ▸ hslabo i a s
    have hSm : MeasurableSet S := hSo.measurableSet
    have hS'm : MeasurableSet S' := (hS'_def ▸ hslabo i a' s).measurableSet
    have hSfin : volume S ≠ ⊤ := by
      refine ne_top_of_le_ne_top hQfin (measure_mono fun y hy => ?_)
      rw [hS_def] at hy; exact hy.1
    have hnh : ‖t • e‖ = |t| := by
      rw [he_def, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hmem : ∀ x, x ∈ S ↔ x + t • e ∈ S' := by
      intro x
      rw [hS_def, hS'_def]
      show (x ∈ Q ∧ a < x i ∧ x i < a + s) ↔
        (x + t • e ∈ Q ∧ a' < (x + t • e) i ∧ (x + t • e) i < a' + s)
      rw [hce, ite_eq_left rfl]
      constructor
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        rw [hce]; split_ifs with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha', has']
        · exact hxQ j
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        have := hxQ j
        rw [hce] at this
        split_ifs at this with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha, has]
        · exact this
    have hgen := hGEN S (t • e) (s / |t|) hSo (by
        rintro x hx τ ⟨hτ0, hτ1⟩ j
        rw [hS_def] at hx
        obtain ⟨hxQ, h1, h2⟩ := hx
        rw [smul_smul, hce]
        split_ifs with hj
        · subst hj
          have e1 : τ * t = τ * a' - τ * a := by rw [ht_def]; ring
          have p1 := mul_nonneg (sub_nonneg.2 hτ1) ha
          have p2 := mul_nonneg hτ0 ha'
          have p3 := mul_nonneg (sub_nonneg.2 hτ1) (by linarith only [has] : (0:ℝ) ≤ 1 - a - s)
          have p4 := mul_nonneg hτ0 (by linarith only [has'] : (0:ℝ) ≤ 1 - a' - s)
          constructor <;> linarith only [h1, h2, e1, p1, p2, p3, p4]
        · exact hxQ j) (div_pos hs (abs_pos.2 ht)) (fun z => by
        have hsub : {τ : ℝ | z - τ • (t • e) ∈ S} ∩ Ioc (0:ℝ) 1 ⊆
            (fun τ => t * τ) ⁻¹' Ioo (z i - a - s) (z i - a) := by
          rintro τ ⟨hτ, -⟩
          rw [mem_ofPred_eq, hS_def] at hτ
          have h1 := hτ.2
          have hzi : (z - τ • (t • e)) i = z i - τ * t := by
            rw [smul_smul, sub_eq_add_neg, ← neg_smul, hce, ite_eq_left rfl, ← sub_eq_add_neg]
          rw [hzi] at h1
          rw [mem_preimage, mem_Ioo, mul_comm]
          exact ⟨by linarith only [h1.2], by linarith only [h1.1]⟩
        refine (measure_mono hsub).trans (le_of_eq ?_)
        rw [Real.volume_preimage_mul_left ht, Real.volume_Ioo, ← ENNReal.ofReal_mul (abs_nonneg _),
          abs_inv, show z i - a - (z i - a - s) = s by ring, div_eq_inv_mul])
    rw [hnh, div_mul_cancel₀ s (abs_ne_zero.2 ht)] at hgen
    have htrans : ∫ x in S, |ub (x + t • e) - β| = ∫ y in S', |ub y - β| := by
      rw [← integral_indicator hSm, ← integral_indicator hS'm,
        ← integral_add_right_eq_self (fun y => S'.indicator (fun y => |ub y - β|) y) (t • e)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hi1 : IntegrableOn (fun x => |ub (x + t • e) - β|) S :=
      ((hub_int.comp_add_right (t • e)).integrableOn.sub (integrableOn_const hSfin)).abs
    have hi2 : IntegrableOn (fun x => |ub (x + t • e) - ub x|) S :=
      ((hub_int.comp_add_right (t • e)).sub hub_int).abs.integrableOn
    calc ∫ y in S, |ub y - β|
        ≤ ∫ x in S, (|ub (x + t • e) - ub x| + |ub (x + t • e) - β|) := by
          refine setIntegral_mono_on ((hub_int.integrableOn.sub (integrableOn_const hSfin)).abs)
            (hi2.add hi1) hSm fun x _ => ?_
          have := abs_sub_le (ub x) (ub (x + t • e)) β
          rwa [abs_sub_comm (ub x) (ub (x + t • e))] at this
      _ = (∫ x in S, |ub (x + t • e) - ub x|) + ∫ x in S, |ub (x + t • e) - β| :=
          integral_add hi2 hi1
      _ ≤ (∫ y in S', |ub y - β|) + 2 * (s * V) := by rw [htrans]; linarith only [hgen]
  have hstrip : ∀ (i : Fin (m + 1)) (N : ℕ), 1 ≤ N → ∀ a : ℝ, 0 ≤ a → a + 1 / N ≤ 1 →
      (N:ℝ) * ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
        (∫ y in Q, |ub y - β|) + 2 * V := by
    intro i N hN a ha haN
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    have hk : ∀ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
          (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N},
            |ub y - β|) + 2 * (1 / N * V) := fun k hk =>
      hslab i (1 / N) a (k / N) (one_div_pos.2 hNpos) ha haN
        (div_nonneg (Nat.cast_nonneg k) hNpos.le)
        (by rw [← add_div, div_le_one hNpos]
            exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hk))
    have hsum := Finset.sum_le_sum hk
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hsum
    have hdisj : (↑(Finset.range N) : Set ℕ).Pairwise (Disjoint on fun k : ℕ =>
        {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}) := by
      intro k _ k' _ hkk'
      rw [Function.onFun, Set.disjoint_left]
      rintro y ⟨_, h1, h2⟩ ⟨_, h1', h2'⟩
      rcases lt_or_gt_of_ne hkk' with hlt | hlt
      · have : (k:ℝ) / N + 1 / N ≤ k' / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2, h1']
      · have : (k':ℝ) / N + 1 / N ≤ k / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2', h1]
    have hint : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hunion : ∑ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}, |ub y - β|
          ≤ ∫ y in Q, |ub y - β| := by
      rw [← integral_biUnion_finset (Finset.range N) (fun k _ => (hslabo i _ _).measurableSet)
        hdisj (fun k _ => hint.mono_set (fun y hy => hy.1))]
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_
      refine LE.le.eventuallySubset ?_
      intro y hy
      rw [mem_iUnion₂] at hy
      obtain ⟨k, _, hy⟩ := hy
      exact hy.1
    have : (N:ℝ) * (2 * (1 / N * V)) = 2 * V := by
      rw [mul_left_comm, ← mul_assoc (N:ℝ), mul_one_div_cancel hNpos.ne', one_mul]
    linarith only [hsum, hunion, this]
  clear hslab hGEN
  /- Step 10: difference quotients.  For `F` continuous with `|F| ≤ 1` and `s = 1/(2N)`,
  `∫_Q (ub - β) (F (· + s e) - F) / s` is the integral of `F` against the difference
  `w (· - s e) - w` of `w = (ub - β) 1_Q`, which is controlled by a translation estimate and the
  two boundary slabs. -/
  have hDQ : ∀ (i : Fin (m + 1)) (F : Euclid (m + 1) → ℝ), Continuous F → (∀ y, |F y| ≤ 1) →
      ∀ N : ℕ, 1 ≤ N →
      |∫ y in Q, (ub y - β) * ((2 * N : ℝ) *
        (F (y + (2 * N : ℝ)⁻¹ • EuclideanSpace.single i (1:ℝ)) - F y))|
        ≤ 10 * V + 4 * ∫ y in Q, |ub y - β| := by
    intro i F hFc hF1 N hN
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
        (x + t • e) j = if j = i then x j + t else x j := by
      subst he_def; exact fun j x t => hcoord i j x t
    have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 * N := ⟨_, rfl⟩
    rw [← he_def, ← hc_def]
    have hc : 0 < c := hc_def ▸ mul_pos two_pos hNpos
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = c⁻¹ := ⟨_, rfl⟩
    rw [← hs_def]
    have hs : 0 < s := hs_def ▸ inv_pos.2 hc
    have hcs : c * s = 1 := hs_def ▸ mul_inv_cancel₀ hc.ne'
    have hsN : s < 1 / N := by
      rw [hs_def, hc_def, one_div]
      exact inv_strictAnti₀ hNpos (by linarith only [hNpos])
    have hcm : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)),
        (x - s • e) j = if j = i then x j - s else x j := by
      intro j x
      rw [sub_eq_add_neg, ← neg_smul, hce, ← sub_eq_add_neg]
    obtain ⟨wb, hwb_def⟩ : ∃ wb : Euclid (m + 1) → ℝ, wb = Q.indicator fun y => ub y - β :=
      ⟨_, rfl⟩
    have hwb_int : Integrable wb := hwb_def ▸
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).integrable_indicator hQm
    have hFb : ∀ y, ‖F y‖ ≤ 1 := hF1
    have hi1 : Integrable fun y => wb y * F (y + s • e) :=
      hwb_int.mul_bdd (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => hFb _)
    have hi2 : Integrable fun y => wb y * F y :=
      hwb_int.mul_bdd hFc.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
    have hi3 : Integrable fun x => wb (x - s • e) * F x :=
      (hwb_int.comp_sub_right (s • e)).mul_bdd hFc.aestronglyMeasurable
        (Filter.Eventually.of_forall hFb)
    have e1 : ∫ y in Q, (ub y - β) * (c * (F (y + s • e) - F y)) =
        c * ∫ x, (wb (x - s • e) - wb x) * F x := by
      rw [← integral_indicator hQm]
      have : ∀ y, Q.indicator (fun y => (ub y - β) * (c * (F (y + s • e) - F y))) y =
          c * (wb y * F (y + s • e) - wb y * F y) := fun y => by
        rw [indicator_mul_left, ← hwb_def]; ring
      simp only [this]
      rw [integral_const_mul, integral_sub hi1 hi2,
        ← integral_sub_right_eq_self (fun y => wb y * F (y + s • e)) (s • e)]
      simp only [sub_add_cancel]
      rw [← integral_sub hi3 hi2]
      simp only [sub_mul]
    -- the pointwise bound: interior differences and the two boundary slabs
    obtain ⟨A, hA_def⟩ : ∃ A : Set (Euclid (m + 1)), A = (fun x => x + s • e) ⁻¹' Q ∩ Q :=
      ⟨_, rfl⟩
    obtain ⟨S0, hS0_def⟩ : ∃ S0 : Set (Euclid (m + 1)),
        S0 = {y : Euclid (m + 1) | y ∈ Q ∧ (0:ℝ) < y i ∧ y i < 0 + 1 / N} := ⟨_, rfl⟩
    obtain ⟨S1, hS1_def⟩ : ∃ S1 : Set (Euclid (m + 1)),
        S1 = {y : Euclid (m + 1) | y ∈ Q ∧ (1 - 1 / N : ℝ) < y i ∧ y i < (1 - 1 / N) + 1 / N} :=
      ⟨_, rfl⟩
    have hAm : MeasurableSet A := hA_def ▸ (hQm.preimage (measurable_add_const _)).inter hQm
    have hS0m : MeasurableSet S0 := hS0_def ▸ (hslabo i _ _).measurableSet
    have hS1m : MeasurableSet S1 := hS1_def ▸ (hslabo i _ _).measurableSet
    have hpt : ∀ x, |wb (x - s • e) - wb x| ≤
        A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) +
          S0.indicator (fun y => |ub y - β|) x +
          S1.indicator (fun y => |ub y - β|) (x - s • e) := by
      intro x
      have n1 := indicator_nonneg (fun z _ => abs_nonneg (ub (z + s • e) - ub z)) (x - s • e)
        (s := A)
      have n2 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) x (s := S0)
      have n3 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) (x - s • e) (s := S1)
      rw [hwb_def]
      by_cases hx : x ∈ Q <;> by_cases hxs : x - s • e ∈ Q
      · have hA : x - s • e ∈ A := by rw [hA_def]; exact ⟨by rwa [mem_preimage, sub_add_cancel], hxs⟩
        rw [indicator_of_mem hx, indicator_of_mem hxs, indicator_of_mem hA, sub_add_cancel,
          show ub (x - s • e) - (β:ℝ) - (ub x - β) = -(ub x - ub (x - s • e)) by ring, abs_neg]
        linarith only [n2, n3]
      · have hS0 : x ∈ S0 := by
          rw [hS0_def]
          refine ⟨hx, (hx i).1, ?_⟩
          by_contra hge
          rw [not_lt] at hge
          apply hxs
          intro j
          rw [hcm]
          split_ifs with hj
          · subst hj; constructor <;> linarith only [(hx j).2, hge, hsN, hs]
          · exact hx j
        rw [indicator_of_mem hx, indicator_of_notMem hxs, indicator_of_mem hS0, zero_sub, abs_neg]
        linarith only [n1, n3]
      · have hS1 : x - s • e ∈ S1 := by
          rw [hS1_def]
          refine ⟨hxs, ?_, ?_⟩
          · by_contra hle
            rw [not_lt, hcm, ite_eq_left rfl] at hle
            apply hx
            intro j
            have := hxs j
            rw [hcm] at this
            split_ifs at this with hj
            · subst hj; constructor <;> linarith only [this.1, hle, hsN, hs]
            · exact this
          · have := (hxs i).2; linarith only [this]
        rw [indicator_of_notMem hx, indicator_of_mem hxs, indicator_of_mem hS1, sub_zero]
        linarith only [n1, n2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hxs, sub_zero, abs_zero]
        linarith only [n1, n2, n3]
    -- integrate the three terms
    have hg1 : Integrable fun z => |ub (z + s • e) - ub z| :=
      ((hub_int.comp_add_right _).sub hub_int).abs
    have hg2 : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hT1i : Integrable fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) :=
      (hg1.indicator hAm).comp_sub_right (s • e)
    have hT2i : Integrable (S0.indicator fun y => |ub y - β|) :=
      (hg2.mono_set (fun y hy => by rw [hS0_def] at hy; exact hy.1)).integrable_indicator hS0m
    have hT3i : Integrable fun x => S1.indicator (fun y => |ub y - β|) (x - s • e) :=
      ((hg2.mono_set (fun y hy => by rw [hS1_def] at hy; exact hy.1)).integrable_indicator
        hS1m).comp_sub_right (s • e)
    have hI1 : ∫ x, A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) ≤ 2 * (s * V) := by
      rw [integral_sub_right_eq_self (fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) x)
        (s • e), integral_indicator hAm, hA_def]
      have := hTR (s • e)
      rwa [norm_smul, hne, mul_one, Real.norm_of_nonneg hs.le] at this
    have hI3 : ∫ x, S1.indicator (fun y => |ub y - β|) (x - s • e) = ∫ y in S1, |ub y - β| := by
      rw [integral_sub_right_eq_self (fun x => S1.indicator (fun y => |ub y - β|) x) (s • e),
        integral_indicator hS1m]
    have hb2 : (N:ℝ) * ∫ y in S0, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS0_def ▸
      hstrip i N hN 0 le_rfl (by rw [zero_add, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
    have hb3 : (N:ℝ) * ∫ y in S1, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS1_def ▸
      hstrip i N hN (1 - 1 / N) (by rw [sub_nonneg, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
        (by rw [sub_add_cancel])
    have hmain : ∫ x, |wb (x - s • e) - wb x| ≤
        2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β| := by
      refine (integral_mono ((hwb_int.comp_sub_right _).sub hwb_int).abs
        ((hT1i.add hT2i).add hT3i) hpt).trans ?_
      rw [integral_add' (hT1i.add hT2i) hT3i, integral_add' hT1i hT2i, integral_indicator hS0m, hI3]
      linarith only [hI1]
    have hbound : |∫ x, (wb (x - s • e) - wb x) * F x| ≤ ∫ x, |wb (x - s • e) - wb x| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hwb_int.comp_sub_right _).sub hwb_int).abs
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF1 x)
    rw [e1, abs_mul, abs_of_pos hc]
    have h5 := mul_le_mul_of_nonneg_left (hbound.trans hmain) hc.le
    have h6 : c * (2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β|) =
        2 * (c * s) * V + 2 * ((N:ℝ) * ∫ y in S0, |ub y - β|) +
          2 * ((N:ℝ) * ∫ y in S1, |ub y - β|) := by
      rw [hc_def]; ring
    rw [h6, hcs] at h5
    linarith only [h5, hb2, hb3]
  clear hstrip hslabo hcoord hTR
  /- Step 11: the boundary estimate (3): write `div G = ∑ᵢ ∂ᵢ Gᵢ` and pass to the limit in the
  difference quotients by dominated convergence. -/
  obtain ⟨I, hI_def⟩ : ∃ I : ℝ, I = ∫ y in Q, |ub y - β| := ⟨_, rfl⟩
  rw [← hI_def] at hDQ hP1
  have hwi : IntegrableOn (fun y => ub y - β) Q :=
    hub_int.integrableOn.sub (integrableOn_const hQfin)
  have h3 : ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) →
      |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (m + 1) * (10 * V + 4 * I) := by
    intro G hG hG1
    have hG1' : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
    have hdG : Continuous (fderiv ℝ G) := hG1'.continuous_fderiv one_ne_zero
    have hGd : ∀ y, HasFDerivAt G (fderiv ℝ G y) y := fun y =>
      (hG1'.differentiable one_ne_zero y).hasFDerivAt
    have hterm : ∀ i : Fin (m + 1),
        |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| ≤
          10 * V + 4 * I := by
      intro i
      obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
      rw [← he_def]
      have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
      obtain ⟨Fi, hFi_def⟩ : ∃ Fi : Euclid (m + 1) → ℝ, Fi = fun y => G y i := ⟨_, rfl⟩
      have hFid : ∀ y, HasFDerivAt Fi ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y)) y :=
        fun y => by
          rw [hFi_def]; exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y (hGd y)
      have hFic : Continuous Fi := by
        rw [hFi_def]; exact (EuclideanSpace.proj i).continuous.comp hG.continuous
      have hFi1 : ∀ y, |Fi y| ≤ 1 := fun y => by
        rw [hFi_def, ← Real.norm_eq_abs]; exact (PiLp.norm_apply_le (G y) i).trans (hG1 y)
      have hdFc : Continuous fun y => (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y) :=
        continuous_const.clm_comp hdG
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) (R + 1)).exists_bound_of_continuousOn
        hdFc.continuousOn
      have hC' : ∀ y ∈ closedBall (0 : Euclid (m + 1)) (R + 1), ‖fderiv ℝ Fi y‖ ≤ C :=
        fun y hy => by rw [(hFid y).fderiv]; exact hC y hy
      have hmvt : ∀ y ∈ Q, ∀ t : ℝ, 0 < t → |Fi (y + t • e) - Fi y| ≤ C * t ∨ 1 < t := by
        intro y hy t ht0
        rcases le_or_gt t 1 with ht1 | ht1
        · left
          have hny := hnormQ y hy
          have hyK : y ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]; linarith only [hny]
          have hyK' : y + t • e ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le]
            linarith only [hny, ht1]
          have := (convex_closedBall (0 : Euclid (m + 1)) (R + 1)).norm_image_sub_le_of_norm_fderiv_le
            (fun z _ => (hFid z).differentiableAt) hC' hyK hyK'
          rwa [add_sub_cancel_left, norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le,
            Real.norm_eq_abs] at this
        · right; exact ht1
      obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun N => 2 * ((N + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
      have hcpos : ∀ N, 0 < c N := fun N => by
        rw [hc_def]; exact mul_pos two_pos (Nat.cast_pos.2 N.succ_pos)
      have hc1 : ∀ N, ¬ 1 < (c N)⁻¹ := fun N => by
        rw [not_lt, inv_le_one₀ (hcpos N), hc_def]
        have : (1:ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.one_le_cast.2 N.succ_pos
        linarith only [this]
      have hctend : Tendsto (fun N => ‖c N‖) atTop atTop := by
        have : (fun N => ‖c N‖) = fun N : ℕ => 2 * ((N + 1 : ℕ) : ℝ) := by
          funext N; rw [Real.norm_of_nonneg (hcpos N).le, hc_def]
        rw [this]
        exact Tendsto.const_mul_atTop two_pos
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have hlim : Tendsto
          (fun N => ∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y)))
          atTop (𝓝 (∫ y in Q, (ub y - β) * (fderiv ℝ G y e) i)) := by
        refine tendsto_integral_of_dominated_convergence (fun y => |ub y - β| * C) (fun N => ?_)
          (hwi.abs.mul_const C) (fun N => ?_) ?_
        · exact (hub_meas.sub measurable_const).aestronglyMeasurable.mul
            (continuous_const.mul ((hFic.comp (continuous_id.add continuous_const)).sub
              hFic)).aestronglyMeasurable
        · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun y hy => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hcpos N)]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := (hmvt y hy (c N)⁻¹ (inv_pos.2 (hcpos N))).resolve_right (hc1 N)
          calc c N * |Fi (y + (c N)⁻¹ • e) - Fi y| ≤ c N * (C * (c N)⁻¹) :=
                mul_le_mul_of_nonneg_left this (hcpos N).le
            _ = C := by rw [mul_comm C, ← mul_assoc, mul_inv_cancel₀ (hcpos N).ne', one_mul]
        · refine Filter.Eventually.of_forall fun y => ?_
          have := (hFid y).lim e hctend
          simp only [smul_eq_mul] at this
          exact this.const_mul _
      have hbd : ∀ N, |∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y))| ≤
          10 * V + 4 * I := fun N => by
        have := hDQ i Fi hFic hFi1 (N + 1) (by omega)
        rwa [← he_def, show (2 * ((N + 1 : ℕ) : ℝ)) = c N by rw [hc_def]] at this
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have htr : ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∑ i, (fderiv ℝ G y (EuclideanSpace.single i 1)) i := by
      intro y
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis]
      simp [Matrix.trace, LinearMap.toMatrix_apply]
    have hint_i : ∀ i : Fin (m + 1), Integrable
        (fun y => (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i) (volume.restrict Q) := by
      intro i
      have hcont : Continuous fun y => (fderiv ℝ G y (EuclideanSpace.single i 1)) i :=
        (EuclideanSpace.proj i).continuous.comp (hdG.clm_apply continuous_const)
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) R).exists_bound_of_continuousOn
        hcont.continuousOn
      refine hwi.mul_bdd hcont.aestronglyMeasurable ((ae_restrict_iff' hQm).2
        (Filter.Eventually.of_forall fun y hy => hC y ?_))
      rw [mem_closedBall, dist_zero_right]; exact hnormQ y hy
    calc |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)|
        = |∑ i, ∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| := by
          rw [← integral_finsetSum _ fun i _ => hint_i i]
          congr 2; funext y
          rw [htr y, Finset.mul_sum]
      _ ≤ ∑ i, |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), (10 * V + 4 * I) := Finset.sum_le_sum fun i _ => hterm i
      _ = (m + 1) * (10 * V + 4 * I) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
            Nat.cast_one]
  /- Conclusion. -/
  have hm0 : (0:ℝ) ≤ m + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
  have hcV : CP * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have := mul_nonneg hm0 (by linarith only [hCP] : (0:ℝ) ≤ 10 + 4 * CP)
    linarith only [this]
  refine ⟨β, ?_, hβM, ?_⟩
  · have : ∫ y in Q, |u y - β| = I := by
      rw [hI_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hP1.trans hcV
  · intro G hG hG1
    have : ∫ y in Q, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
      integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]
    refine (h3 G hG hG1).trans ?_
    have h1 : (m + 1) * (10 * V + 4 * I) ≤ (m + 1) * (10 * V + 4 * (CP * V)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP1]) hm0
    have h2 : (m + 1) * (10 * V + 4 * (CP * V)) = (m + 1) * (10 + 4 * CP) * V := by ring
    have h4 : (m + 1) * (10 + 4 * CP) * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V :=
      mul_le_mul_of_nonneg_right (by linarith only [hCP]) hV0
    linarith only [h1, h2, h4]
/-- **Dilation pull-back of a test form** (Simon 6.2.23 for `f = δ_λ`, `δ_λ(x) = λx`, `λ ≠ 0`):
`δ_λ^#ω = affinePullbackForm (λ·id) 0 ω` is again a test form on `ℝᴾ`, and
`(δ_λ^#ω)(x) = λᵏ ω(λx)` as `k`-covectors.  `x ↦ λx` is a homeomorphism, hence proper, so the
pull-back preserves compactly supported smooth forms; multilinearity of the covector `ω(λx)`
pulls `λ` out of each of its `k` slots. -/
theorem Submission.cmcdt_dil_pullback_testForm : ∀ (P k : ℕ) (lam : ℝ), lam ≠ 0 → ∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) ∧ ∀ x : Euclid P, (η : DifferentialForm (Euclid P) k) x = lam ^ k • (ω : DifferentialForm (Euclid P) k) (lam • x) := by
  intro P k lam hlam ω
  -- Step 1: `x ↦ 0 + (λ·id)x = λx` is a homeomorphism, hence a proper map.
  have hproper : IsProperMap
      (fun x : Euclid P => (0 : Euclid P) + (lam • ContinuousLinearMap.id ℝ (Euclid P)) x) := by
    convert (Homeomorph.smulOfNeZero (α := Euclid P) lam hlam).isProperMap using 1
    funext x
    simp
  -- Step 2: the pull-back along the proper map is a test form, trivially supported in `univ`.
  refine ⟨⟨affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0
      (ω : DifferentialForm (Euclid P) k),
    affinePullbackForm_isTestForm _ _ hproper ω.property.1, subset_univ _⟩, rfl, fun x => ?_⟩
  -- Steps 3–4: `η(x)(v) = ω(λx)(λv₁, …, λvₖ) = (∏ᵢ λ) ω(λx)(v) = λᵏ ω(λx)(v)` for every `v`.
  have hx : (0 : Euclid P) + (lam • ContinuousLinearMap.id ℝ (Euclid P)) x = lam • x := by
    simp
  ext v
  have hv : (lam • ContinuousLinearMap.id ℝ (Euclid P)) ∘ v = fun i => lam • v i := by
    funext i
    simp
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hx, hv,
    ContinuousAlternatingMap.map_smul_univ, Fin.prod_const, ContinuousAlternatingMap.smul_apply]

/-- **Mass under the dilation push-forward** (step 5 of the proof of
`Submission.cmcdt_dilation_pushforward`; Simon 6.5.3, chapter-06.txt lines 1458–1460: the changes
of scale `x ↦ λ⁻¹x` and `x ↦ λx` scale the masses of `k`-currents by `λ^{∓k}`).  Let `λ > 0` and
`X, Y ∈ 𝒟_k(ℝᴾ)` with `Y(ω) = X(η)` whenever `η = δ_λ^#ω`, i.e. `Y = δ_{λ#}X` for `δ_λ(x) = λx`
(6.2.23).  Then `M(Y) = λᵏ M(X)` in `[0, ∞]`, with no finiteness assumption.  By
`Submission.cmcdt_dil_pullback_testForm`, `δ_μ^#ω` is a test form with `(δ_μ^#ω)(x) = μᵏ ω(μx)`
for `μ ≠ 0`.  (1) For admissible `ω`, `η' = λ⁻ᵏ δ_λ^#ω` has `η'(x) = ω(λx)`, so it is admissible
and `Y(ω) = X(δ_λ^#ω) = λᵏ X(η') ≤ λᵏ M(X)`.  (2) For admissible `η`, `ω = λᵏ δ_{λ⁻¹}^#η` has
`ω(y) = η(λ⁻¹y)`, so it is admissible, and `δ_λ^#ω = λᵏ η`; thus `λᵏ X(η) = Y(ω) ≤ M(Y)`, and
`λᵏ M(X) ≤ M(Y)` because multiplication by `λᵏ` commutes with suprema in `[0, ∞]`. -/
theorem Submission.cmcdt_dil_mass_eq : ∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → Y.mass = ENNReal.ofReal (lam ^ k) * X.mass := by
  intro P k lam hlam X Y hXY
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hpow : 0 < lam ^ k := pow_pos hlam k
  apply le_antisymm
  -- Step 1: `M(Y) ≤ λᵏ M(X)`.  Fix an admissible `ω`.
  · refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (Y ω) ≤ ENNReal.ofReal (lam ^ k) * X.mass
    -- (a) `η = δ_λ^#ω` is a test form with `η(x) = λᵏ ω(λx)`, and `Y(ω) = X(η)`.
    obtain ⟨η, hηω, hη⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hlam0 ω
    -- (b) `η' = λ⁻ᵏ η` has `η'(x) = ω(λx)`, so it is admissible.
    have hη' : (lam ^ k)⁻¹ • η ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      change covectorEuclideanNorm ((lam ^ k)⁻¹ • (η : DifferentialForm (Euclid P) k) x) ≤ 1
      rw [hη x, smul_smul, inv_mul_cancel₀ hpow.ne', one_smul]
      exact hω.2 (lam • x)
    -- (c) `X(η) = λᵏ X(η')` by linearity.
    have hXη : X η = lam ^ k * X ((lam ^ k)⁻¹ • η) := by
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul]
    -- (d) `Y(ω) = λᵏ X(η') ≤ λᵏ M(X)`.
    rw [hXY ω η hηω, hXη, ENNReal.ofReal_mul hpow.le]
    exact mul_le_mul_right (X.le_massOn hη') _
  -- Step 2: `λᵏ M(X) ≤ M(Y)`, where `λᵏ M(X)` is the supremum of `λᵏ X(η)` over admissible `η`.
  · show ENNReal.ofReal (lam ^ k) * sSup ((fun ω => ENNReal.ofReal (X ω)) ''
      massAdmissibleOn (univ : Set (Euclid P)) k univ) ≤ Y.mass
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨η, hη, rfl⟩
    show ENNReal.ofReal (lam ^ k) * ENNReal.ofReal (X η) ≤ Y.mass
    -- (a) `ζ = δ_{λ⁻¹}^#η` and `ω = λᵏ ζ`, so `ω(y) = η(λ⁻¹y)`.
    obtain ⟨ζ, -, hζ⟩ := Submission.cmcdt_dil_pullback_testForm P k lam⁻¹ (inv_ne_zero hlam0) η
    have hω : ∀ y, ((lam ^ k • ζ : TestFormOn (univ : Set (Euclid P)) k) :
        DifferentialForm (Euclid P) k) y = (η : DifferentialForm (Euclid P) k) (lam⁻¹ • y) := by
      intro y
      change lam ^ k • (ζ : DifferentialForm (Euclid P) k) y = _
      rw [hζ y, smul_smul, ← mul_pow, mul_inv_cancel₀ hlam0, one_pow, one_smul]
    -- (b) `ω` is admissible.
    have hωadm : lam ^ k • ζ ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      refine ⟨subset_univ _, fun y => ?_⟩
      rw [hω y]
      exact hη.2 (lam⁻¹ • y)
    -- (c) `η₂ = δ_λ^#ω` satisfies `η₂(x) = λᵏ ω(λx) = λᵏ η(x)`, i.e. `η₂ = λᵏ η`.
    obtain ⟨η₂, hη₂ω, hη₂⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hlam0 (lam ^ k • ζ)
    have hη₂η : η₂ = lam ^ k • η := by
      refine Subtype.ext (funext fun x => ?_)
      change (η₂ : DifferentialForm (Euclid P) k) x = lam ^ k • (η : DifferentialForm (Euclid P) k) x
      rw [hη₂ x, hω, inv_smul_smul₀ hlam0]
    -- (d) `λᵏ X(η) = X(η₂) = Y(ω) ≤ M(Y)`.
    calc ENNReal.ofReal (lam ^ k) * ENNReal.ofReal (X η)
        = ENNReal.ofReal (Y (lam ^ k • ζ)) := by
          rw [hXY (lam ^ k • ζ) η₂ hη₂ω, hη₂η, map_smul, smul_eq_mul, ENNReal.ofReal_mul hpow.le]
      _ ≤ Y.mass := Y.le_massOn hωadm
/-- **Support of the dilation push-forward**: step 6 of the proof of `cmcdt_dilation_pushforward`
(`spt T` as in Simon 6.2.11, chapter-06.txt lines 296–302; change of scale as in 6.5.3, lines
1458–1460).  If `λ > 0` and `Y(ω) = X(δ_λ^#ω)` for all test forms `ω` (`Y = δ_{λ#}X`,
`δ_λ(x) = λx`), then `spt Y = λ spt X`.  As `δ_λ^#ω = λᵏ ω(λ·)`, `tsupport δ_λ^#ω ⊆
δ_λ⁻¹(tsupport ω)`, so `Y` vanishes on `λW` whenever `X` vanishes on `W`; as `δ_λ^#δ_{λ⁻¹}^#η = η`,
`X` vanishes on `λ⁻¹W` whenever `Y` vanishes on `W`.  Hence `Z_Y = λZ_X`, and `δ_λ` is a
bijection of `ℝᴾ`. -/
theorem Submission.cmcdt_dil_support_eq : ∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → Y.support = (fun x => lam • x) '' X.support := by
  intro P k lam hlam X Y hrel
  have hne : lam ≠ 0 := hlam.ne'
  have hne' : lam⁻¹ ≠ 0 := inv_ne_zero hne
  -- Step 0(b): if `η(x) = μᵏ ω(μx)` for all `x`, then `tsupport η ⊆ δ_μ⁻¹(tsupport ω)`.
  have htsupp : ∀ (μ : ℝ) (ω η : TestFormOn (univ : Set (Euclid P)) k),
      (∀ x, (η : DifferentialForm (Euclid P) k) x =
        μ ^ k • (ω : DifferentialForm (Euclid P) k) (μ • x)) →
      tsupport (η : DifferentialForm (Euclid P) k) ⊆
        (fun x => μ • x) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) k) := by
    intro μ ω η h
    refine closure_minimal (fun x hx => ?_)
      ((isClosed_tsupport _).preimage (continuous_const_smul μ))
    refine mem_preimage.2 (subset_tsupport _ fun h0 => hx ?_)
    rw [h x, h0, smul_zero]
  -- Step 0(c): each test form `η` has `ζ = δ_{λ⁻¹}^#η` with `X(η) = Y(ζ)`, since `δ_λ^#ζ = η`,
  -- and `tsupport ζ ⊆ δ_{λ⁻¹}⁻¹(tsupport η)` by Step 0(b).
  have hinv : ∀ η : TestFormOn (univ : Set (Euclid P)) k,
      ∃ ζ : TestFormOn (univ : Set (Euclid P)) k, X η = Y ζ ∧
        tsupport (ζ : DifferentialForm (Euclid P) k) ⊆
          (fun x => lam⁻¹ • x) ⁻¹' tsupport (η : DifferentialForm (Euclid P) k) := by
    intro η
    obtain ⟨ζ, -, hζ⟩ := Submission.cmcdt_dil_pullback_testForm P k lam⁻¹ hne' η
    obtain ⟨η₂, hη₂, hη₂ζ⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hne ζ
    have hη₂η : η₂ = η := by
      refine Subtype.ext (funext fun x => ?_)
      rw [hη₂ζ x, hζ, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul,
        inv_smul_smul₀ hne]
    exact ⟨ζ, by rw [hrel ζ η₂ hη₂, hη₂η], htsupp lam⁻¹ η ζ hζ⟩
  -- Steps 1 and 2 share one argument: if every `ω` has `η` with `A(ω) = B(η)` and
  -- `tsupport η ⊆ δ_μ⁻¹(tsupport ω)`, then `δ_μ(Z_B) ⊆ Z_A`.  For `x ∈ W` with `B` vanishing on
  -- `W`, `δ_μ(W)` is open with compact closure (Step 0(a)) and `A` vanishes on it, because
  -- `tsupport ω ⊆ δ_μ(W)` gives `tsupport η ⊆ δ_μ⁻¹(δ_μ(W)) = W`.
  have hzero : ∀ μ : ℝ, μ ≠ 0 → ∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) k,
      (∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ η : TestFormOn (univ : Set (Euclid P)) k,
        A ω = B η ∧ tsupport (η : DifferentialForm (Euclid P) k) ⊆
          (fun x => μ • x) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) k)) →
      (fun x => μ • x) '' B.zeroRegion ⊆ A.zeroRegion := by
    rintro μ hμ A B hAB _ ⟨x, ⟨W, ⟨hWo, hWc, -, hWv⟩, hxW⟩, rfl⟩
    have hK : IsCompact ((fun x => μ • x) '' closure W) := hWc.image (continuous_const_smul μ)
    refine ⟨(fun x => μ • x) '' W, ⟨isOpenMap_smul₀ hμ W hWo,
      hK.of_isClosed_subset isClosed_closure (closure_minimal (image_mono subset_closure)
        hK.isClosed), subset_univ _, fun ω hω => ?_⟩, mem_image_of_mem _ hxW⟩
    obtain ⟨η, hAB', hηω⟩ := hAB ω
    rw [hAB']
    exact hWv η (hηω.trans ((preimage_mono hω).trans
      ((smul_right_injective (Euclid P) hμ).preimage_image W).subset))
  -- Step 1: `δ_λ(Z_X) ⊆ Z_Y`, taking `η = δ_λ^#ω` from `cmcdt_dil_pullback_testForm`.
  have h1 : (fun x => lam • x) '' X.zeroRegion ⊆ Y.zeroRegion := by
    refine hzero lam hne Y X fun ω => ?_
    obtain ⟨η, hη, hηω⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hne ω
    exact ⟨η, hrel ω η hη, htsupp lam ω η hηω⟩
  -- Step 2: `δ_{λ⁻¹}(Z_Y) ⊆ Z_X` by Step 0(c), so `y = λ(λ⁻¹y) ∈ δ_λ(Z_X)` for `y ∈ Z_Y`.
  have h2 : (fun x => lam⁻¹ • x) '' Y.zeroRegion ⊆ X.zeroRegion := hzero lam⁻¹ hne' X Y hinv
  have hZ : Y.zeroRegion = (fun x => lam • x) '' X.zeroRegion :=
    Subset.antisymm
      (fun y hy => ⟨lam⁻¹ • y, h2 (mem_image_of_mem _ hy), smul_inv_smul₀ hne y⟩) h1
  -- Step 3: `δ_λ` is a bijection, so `spt Y = univ \ δ_λ(Z_X) = δ_λ(univ \ Z_X) = δ_λ(spt X)`.
  unfold GeometricCurrentOn.support
  rw [hZ, image_sdiff (smul_right_injective (Euclid P) hne),
    image_univ_of_surjective (f := fun x : Euclid P => lam • x)
      fun y => ⟨lam⁻¹ • y, smul_inv_smul₀ hne y⟩]
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Integer multiplicity is preserved by the dilation push-forward** `δ_{λ#}`, `δ_λ(x) = λx`,
`λ > 0` (step 7 of the proof of `cmcdt_dilation_pushforward`; compare Simon 6.3.3).  If
`Y(ω) = X(δ_λ^#ω)` and `X = τ(M, θ, ξ)`, then `Y = τ(λM, θ(·/λ), ξ(·/λ))`, with
`λM = δ_{λ⁻¹}⁻¹(M)`.  The change of variables `(δ_λ)_#(Hᵏ⌞M) = λ⁻ᵏ Hᵏ⌞λM` transfers local
integrability, measurability and orientation (`T_{λx}(λM) = TₓM`), and `δ_λ^#ω(x) = λᵏω(λx)`
gives `Y(ω) = λᵏλ⁻ᵏ ∫_{λM} θ(·/λ) ⟨ω, ξ(·/λ)⟩ dHᵏ`.  This holds in every degree `k`. -/
theorem Submission.cmcdt_dil_isIntegerMultiplicity : ∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → IsIntegerMultiplicity X → IsIntegerMultiplicity Y := by
  intro P k lam hlam X Y hXY ⟨R, hR⟩
  have hlam0 : lam ≠ 0 := hlam.ne'
  -- `δ_λ` is a homeomorphism, hence a measurable embedding, and `δ_λ⁻¹(δ_{λ⁻¹}⁻¹(S)) = S`
  have hT : MeasurableEmbedding (fun x : Euclid P => lam • x) :=
    (Homeomorph.smulOfNeZero lam hlam0).measurableEmbedding
  have hpre : ∀ S : Set (Euclid P),
      (fun x : Euclid P => lam • x) ⁻¹' ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' S) = S := by
    intro S
    ext x
    simp only [mem_preimage, inv_smul_smul₀ hlam0]
  have hc0 : ENNReal.ofReal (lam⁻¹ ^ k) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 hlam) k)).ne'
  -- change of variables on `M' = δ_{λ⁻¹}⁻¹(M)`: `(δ_λ)_#(Hᵏ⌞M) = λ⁻ᵏ Hᵏ⌞M'` and
  -- `∫_M g(λz) dHᵏ(z) = λ⁻ᵏ ∫_{M'} g dHᵏ`
  obtain ⟨hcv1, -, hcv3⟩ := Submission.euclid_hausdorff_dilation_change_of_variables P k lam hlam
    ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier)
  rw [hpre] at hcv1 hcv3
  -- rectifiability: `M' ⊆ δ_{λ⁻¹}⁻¹(M₀) ∪ ⋃ⱼ range (λFⱼ)`, with `Hᵏ(δ_{λ⁻¹}⁻¹(M₀)) = λᵏHᵏ(M₀) = 0`
  have hrect : CountablyRectifiable k ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier) := by
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun y : Euclid P => lam⁻¹ • y) ⁻¹' M₀, ?_, fun j z => lam • F j z, fun j => ?_,
      fun y hy => ?_⟩
    · rw [preimage_smul₀ (inv_ne_zero hlam0),
        Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero (inv_ne_zero hlam0)), hM₀,
        smul_zero]
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨‖lam‖₊ * K, (lipschitzWith_smul lam).comp hK⟩
    · have hy' : lam⁻¹ • y ∈ R.carrier := hy
      rcases hcover hy' with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, z, hz⟩ := mem_iUnion.1 h1
        exact Or.inr (mem_iUnion.2 ⟨j, z, by simp only [hz, smul_inv_smul₀ hlam0]⟩)
  -- local integrability: `∫⁻_{M ∩ δ_λ⁻¹(K)} θ dHᵏ = λ⁻ᵏ ∫⁻_{M' ∩ K} θ(·/λ) dHᵏ`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier ∩ K,
        (R.mult (lam⁻¹ • x) : ℝ≥0∞) ∂μHE[k] ≠ ∞ := by
    intro K hK _ htop
    have hKc : IsCompact ((fun x : Euclid P => lam • x) ⁻¹' K) :=
      (Homeomorph.smulOfNeZero lam hlam0).isCompact_preimage.2 hK
    have h := (Submission.euclid_hausdorff_dilation_change_of_variables P k lam hlam
      ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier ∩ K)).2.1
      (fun y => (R.mult (lam⁻¹ • y) : ℝ≥0∞))
    rw [preimage_inter, hpre] at h
    simp only [inv_smul_smul₀ hlam0] at h
    rw [htop, ENNReal.mul_top hc0] at h
    exact R.locallyIntegrable_mult _ hKc (subset_univ _) h
  -- measurability: `ξ(·/λ) ∘ δ_λ = ξ`, and `Hᵏ⌞M' ≪ λ⁻ᵏ Hᵏ⌞M' = (δ_λ)_#(Hᵏ⌞M)`
  have hmeas : AEStronglyMeasurable (fun y : Euclid P => R.orient (lam⁻¹ • y))
      (μHE[k].restrict ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier)) := by
    have h : AEStronglyMeasurable (fun y : Euclid P => R.orient (lam⁻¹ • y))
        (Measure.map (fun x : Euclid P => lam • x) (μHE[k].restrict R.carrier)) := by
      rw [hT.aestronglyMeasurable_map_iff]
      have he : ((fun y : Euclid P => R.orient (lam⁻¹ • y)) ∘ fun x : Euclid P => lam • x) =
          R.orient := by
        funext x
        simp only [Function.comp_apply, inv_smul_smul₀ hlam0]
      rw [he]
      exact R.aestronglyMeasurable_orient
    rw [hcv1] at h
    exact h.mono_ac (Measure.absolutelyContinuous_smul hc0)
  -- orientation: `T_{λx}M' = TₓM` (dilation invariance, `dilation 0 λ⁻¹ = δ_λ`) and
  -- `ξ(λx/λ) = ξ(x)`, transferred from `Hᵏ⌞M`-a.e. `x` to `Hᵏ⌞M'`-a.e. `y = λx`
  have hdil : dilation (0 : Euclid P) lam⁻¹ = fun y => lam • y := by
    funext y
    simp [dilation, dilationCLM]
  have himg : (fun y : Euclid P => lam • y) '' R.carrier =
      (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_preimage, inv_smul_smul₀ hlam0] using hx
    · intro hy
      exact ⟨lam⁻¹ • y, hy, smul_inv_smul₀ hlam0 y⟩
  have hor : ∀ᵐ y ∂(μHE[k].restrict ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier)),
      ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt k ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier) y Q ∧
          IsUnitOrientationOf (R.orient (lam⁻¹ • y)) Q := by
    refine (Measure.ae_ennreal_smul_measure_iff hc0).1 ?_
    rw [← hcv1, hT.ae_map_iff]
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, hQ, hξ⟩ := hx
    refine ⟨Q, ?_, ?_⟩
    · have h := Submission.dtc_approxTangent_dilation P k R.carrier 0 x lam⁻¹ Q
        (inv_pos.2 hlam) hQ
      rwa [hdil, himg] at h
    · rwa [inv_smul_smul₀ hlam0]
  refine ⟨{ carrier := (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier
            mult := fun y => R.mult (lam⁻¹ • y)
            orient := fun y => R.orient (lam⁻¹ • y)
            measurableSet_carrier :=
              (continuous_const_smul lam⁻¹).measurable R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := hrect
            measurable_mult := R.measurable_mult.comp (continuous_const_smul lam⁻¹).measurable
            mult_pos := fun y hy => R.mult_pos _ hy
            locallyIntegrable_mult := hint
            aestronglyMeasurable_orient := hmeas
            orients := hor }, fun ω => ?_⟩
  -- representation: `Y(ω) = X(η)` with `η(x) = λᵏω(λx)` (pullback test form), then change of
  -- variables with `g(y) = θ(y/λ) ⟨ω(y), ξ(y/λ)⟩`
  obtain ⟨η, hη, hηx⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hlam0 ω
  rw [hXY ω η hη, hR η]
  show ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((η : DifferentialForm (Euclid P) k) x)
      ∂μHE[k] = ∫ y in (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier,
        (R.mult (lam⁻¹ • y) : ℝ) * R.orient (lam⁻¹ • y) ((ω : DifferentialForm (Euclid P) k) y)
          ∂μHE[k]
  have h3 := hcv3 fun y => (R.mult (lam⁻¹ • y) : ℝ) *
    R.orient (lam⁻¹ • y) ((ω : DifferentialForm (Euclid P) k) y)
  simp only [inv_smul_smul₀ hlam0] at h3
  calc ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((η : DifferentialForm (Euclid P) k) x)
        ∂μHE[k]
      = ∫ x in R.carrier, lam ^ k * ((R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) k) (lam • x))) ∂μHE[k] := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hηx x, map_smul, smul_eq_mul]
        ring
    _ = lam ^ k * ∫ x in R.carrier, (R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) k) (lam • x)) ∂μHE[k] :=
        integral_const_mul _ _
    _ = lam ^ k * (lam⁻¹ ^ k * ∫ y in (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier,
          (R.mult (lam⁻¹ • y) : ℝ) *
            R.orient (lam⁻¹ • y) ((ω : DifferentialForm (Euclid P) k) y) ∂μHE[k]) := by
        rw [h3]
    _ = _ := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlam0, one_pow, one_mul]

/-- **Push-forward by the dilations `δ_λ(x) = λx` of `ℝᴾ`** (Simon Ch. 6, 2.23–2.24, used for the
changes of scale in 5.3).  `dil_k(λ, X) = δ_{λ#}X`, `δ_{λ#}X(ω) = X(δ_λ^#ω)`, is the push-forward
along the proper affine map `x ↦ 0 + (λ·id)x`; for `λ = 0` it is `X` (never used).  For `λ > 0` it
is additive, is inverted by `dil(λ⁻¹, ·)` because `(δ_λ^#ω)(x) = λᵏω(λx)`, and commutes with `∂`
(2.24(1)).  Mass scales by `λᵏ`, supports scale by `λ` and integer multiplicity is preserved; the
three children prove these for every `Y` with `Y(ω) = X(δ_λ^#ω)`. -/
theorem Submission.cmcdt_dilation_pushforward : ∀ P : ℕ, ∃ dil : ∀ k : ℕ, ℝ → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (lam : ℝ), 0 < lam → (∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam (X - Y) = dil k lam X - dil k lam Y) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam⁻¹ (dil k lam X) = X) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).mass = ENNReal.ofReal (lam ^ k) * X.mass) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).support = (fun x => lam • x) '' X.support) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, IsIntegerMultiplicity X → IsIntegerMultiplicity (dil k lam X)) ∧ ∀ X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (dil (k + 1) lam X).boundary = dil k lam X.boundary := by
  intro P
  classical
  -- Step 1: for `λ ≠ 0`, `x ↦ 0 + (λ·id)x = λx` is a homeomorphism, hence proper.
  have hprop : ∀ lam : ℝ, lam ≠ 0 → IsProperMap
      (fun x : Euclid P => (0 : Euclid P) + (lam • ContinuousLinearMap.id ℝ (Euclid P)) x) := by
    intro lam h
    convert (Homeomorph.smulOfNeZero (α := Euclid P) lam h).isProperMap using 1
    funext x
    simp
  -- `dil_k(λ, X) := δ_{λ#}X`; the domain `(x ↦ 0 + λx)⁻¹' univ` of `δ_{λ#}` lies in `univ`
  let D : ∀ k : ℕ, ℝ → GeometricCurrentOn (univ : Set (Euclid P)) k →
      GeometricCurrentOn (univ : Set (Euclid P)) k := fun k lam X =>
    if h : lam ≠ 0 then
      GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid P)))
        (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (hprop lam h)
        (X.restrictDomain (subset_univ _))
    else X
  have hD : ∀ (k : ℕ) (lam : ℝ) (h : lam ≠ 0) (X : GeometricCurrentOn (univ : Set (Euclid P)) k),
      D k lam X = GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid P)))
        (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (hprop lam h)
        (X.restrictDomain (subset_univ _)) := by
    intro k lam h X
    exact dite_eq_left h
  -- `δ_{λ#}X(ω) = X(η)` whenever `η = δ_λ^#ω`: the hypothesis of the mass, support and integer
  -- multiplicity children
  have hrel : ∀ (k : ℕ) (lam : ℝ) (h : lam ≠ 0) (X : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (ω η : TestFormOn (univ : Set (Euclid P)) k),
      (η : DifferentialForm (Euclid P) k) = affinePullbackForm
        (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) →
      D k lam X ω = X η := by
    intro k lam h X ω η hη
    rw [hD k lam h X, GeometricCurrentOn.affinePushforward_apply,
      GeometricCurrentOn.restrictDomain_apply]
    congr 1
    apply Subtype.ext
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe, hη]
  refine ⟨D, fun k lam hlam => ?_⟩
  have hne : lam ≠ 0 := hlam.ne'
  have hne' : lam⁻¹ ≠ 0 := inv_ne_zero hne
  refine ⟨fun X Y => ?_, fun X => ?_, fun X => ?_, fun X => ?_, fun X hX => ?_, fun X => ?_⟩
  -- (1), step 2: linearity, since the difference of currents acts pointwise
  · apply GeometricCurrentOn.ext
    intro ω
    rw [hD k lam hne, hD k lam hne, hD k lam hne]
    rfl
  -- (2), step 3: `(δ_λ^#δ_{λ⁻¹}^#ω)(x) = λᵏ(λ⁻¹)ᵏ ω(λ⁻¹λx) = ω(x)`
  · apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨η₁, hη₁, hη₁'⟩ := Submission.cmcdt_dil_pullback_testForm P k lam⁻¹ hne' ω
    obtain ⟨η₂, hη₂, hη₂'⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hne η₁
    rw [hrel k lam⁻¹ hne' (D k lam X) ω η₁ hη₁, hrel k lam hne X η₁ η₂ hη₂]
    congr 1
    apply Subtype.ext
    funext x
    rw [hη₂', hη₁', smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul,
      inv_smul_smul₀ hne]
  -- (3), step 5: `M(δ_{λ#}X) = λᵏ M(X)`
  · exact Submission.cmcdt_dil_mass_eq P k lam hlam X (D k lam X) (hrel k lam hne X)
  -- (4), step 6: `spt δ_{λ#}X = λ spt X`
  · exact Submission.cmcdt_dil_support_eq P k lam hlam X (D k lam X) (hrel k lam hne X)
  -- (5), step 7: `δ_{λ#}X` is integer multiplicity, represented by `(λM, θ(·/λ), ξ(·/λ))`
  · exact Submission.cmcdt_dil_isIntegerMultiplicity P k lam hlam X (D k lam X)
      (hrel k lam hne X) hX
  -- (6), step 4: `∂δ_{λ#} = δ_{λ#}∂` (2.24(1)); restricting the domain commutes with `∂` by
  -- definition
  · rw [hD (k + 1) lam hne, hD k lam hne, GeometricCurrentOn.boundary_affinePushforward]
    congr 1

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
