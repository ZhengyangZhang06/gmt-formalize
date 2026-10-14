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

/-- A set of finite `H⁰`-measure is countably `0`-rectifiable (Simon Ch. 3, Definition 1.1, case
`n = 0`).  `H⁰ = μH[0]` gives every point mass `1`, so an infinite `M` would contain `k`-point
subsets of measure `k` for every `k ∈ ℕ`; hence `M` is finite.  Each point `x` is the range of the
constant (`0`-Lipschitz) map `ℝ⁰ → ℝᴾ`, and `M = ⋃₀ {{x} : x ∈ M}` is a countable union of such
ranges. -/
theorem Submission.cbrr_rectifiable_dim_zero : ∀ (P : ℕ) (M : Set (Euclid P)), μHE[0] M ≠ ∞ → CountablyRectifiable 0 M := by
  intro P M hM
  -- Step 1: `μHE[0] = μH[0]`, and `μH[0] {x} = 1`
  rw [Measure.euclideanHausdorffMeasure_zero] at hM
  -- Step 2: `M` is finite; otherwise it has `⌈r⌉₊`-point subsets for every `r`, so `μH[0] M = ∞`
  have hfin : M.Finite := by
    by_contra hinf
    refine hM (ENNReal.eq_top_of_forall_nnreal_le fun r => ?_)
    obtain ⟨s, hsM, hs⟩ := Set.Infinite.exists_subset_card_eq hinf ⌈r⌉₊
    calc (r : ℝ≥0∞) ≤ (⌈r⌉₊ : ℝ≥0∞) := by exact_mod_cast Nat.le_ceil r
      _ = ∑ x ∈ s, μH[0] ({x} : Set (Euclid P)) := by
        simp only [Measure.hausdorffMeasure_zero_singleton, Finset.sum_const, nsmul_eq_mul,
          mul_one, hs]
      _ = μH[0] (s : Set (Euclid P)) := sum_measure_singleton
      _ ≤ μH[0] M := measure_mono hsM
  -- Step 3: each `{x}` is the range of the constant `0`-Lipschitz map `ℝ⁰ → ℝᴾ`
  have hpt : ∀ S ∈ (fun x : Euclid P => ({x} : Set (Euclid P))) '' M,
      CountablyRectifiable 0 S := by
    rintro _ ⟨x, -, rfl⟩
    simpa only [range_const] using Poincare.SimonGMT.Chapter03.countablyRectifiable_range (n := 0)
      (LipschitzWith.const (α := Euclid 0) x)
  -- Step 4: `M = ⋃₀ {{x} : x ∈ M}` is a countable union of countably `0`-rectifiable sets
  have h := Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hfin.countable.image _) hpt
  rwa [Set.sUnion_image, Set.biUnion_of_singleton] at h
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD
/-- Lower density bound at a point with an approximate tangent plane (Simon Ch. 3, 1.5(3), and
Ch. 4, 4.10(1)): if `Q` is the approximate tangent space of `M` at `x`, `n ≥ 1` and `c < ωₙ`, then
`c ρⁿ ≤ Hⁿ(M ∩ B̄_ρ(x))` for all small `ρ > 0`.  Choose `ε > 0` with `c (1 + ε)ⁿ < ωₙ` and test
against `ψ(y) = max 0 (min 1 ((1 + ε − |y|)/ε))`, so `1_{B̄₁(0)} ≤ ψ ≤ 1_{B̄_{1+ε}(0)}`.  A linear
isometry `ℝⁿ → ℝᴾ` onto `Q` gives `∫_Q ψ dHⁿ ≥ Hⁿ(Q ∩ B₁(0)) = ωₙ`, while
`∫_{η_{x,r}(M)} ψ dHⁿ ≤ Hⁿ(B̄_{1+ε}(0) ∩ η_{x,r}(M)) = r⁻ⁿ Hⁿ(M ∩ B̄_{(1+ε)r}(x))`; the blow-up
integrals converge to `∫_Q ψ dHⁿ`, and `ρ = (1 + ε) r`. -/
theorem Submission.doragm_approxTangent_lower_density : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → HasApproximateTangentSpaceAt n M x Q → ∀ c : ℝ≥0∞, c < unitBallVolume n → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal (ρ ^ n) ≤ μHE[n] (M ∩ closedBall x ρ) := by
  intro P n M x Q _hn hQ c hc
  -- Step 1: `ωₙ < ∞`, so `c < ∞`; choose `ε > 0` with `c (1 + ε)ⁿ < ωₙ`
  have hω_top : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcont : Tendsto (fun ε : ℝ => c * ENNReal.ofReal ((1 + ε) ^ n)) (𝓝 0) (𝓝 c) := by
    have h1 : Tendsto (fun ε : ℝ => (1 + ε) ^ n) (𝓝 0) (𝓝 1) := by
      have hc1 : Continuous fun ε : ℝ => (1 + ε) ^ n := by fun_prop
      simpa using hc1.tendsto 0
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h1) (Or.inr hc_top)
  obtain ⟨ε, hεω, hε⟩ := ((hcont.eventually (gt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  set A : ℝ := 1 + ε
  have hA : 0 < A := by linarith
  -- Step 2: the test function `ψ(y) = max 0 (min 1 ((1 + ε − |y|)/ε))`
  have hψcs : HasCompactSupport (fun y : Euclid P => max 0 (min 1 ((A - ‖y‖) / ε))) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) A) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have hneg : (A - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    rw [min_eq_right (hneg.le.trans zero_le_one), max_eq_left hneg.le]
  let ψ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 ((A - ‖y‖) / ε)), continuous_const.max
      (continuous_const.min ((continuous_const.sub continuous_norm).div_const ε))⟩, hψcs⟩
  have hψ_apply : ∀ y, ψ y = max 0 (min 1 ((A - ‖y‖) / ε)) := fun y => rfl
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => le_max_left _ _
  have hψle1 : ∀ y, ψ y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hψ1 : ∀ y : Euclid P, ‖y‖ ≤ 1 → ψ y = 1 := by
    intro y hy
    have hge : 1 ≤ (A - ‖y‖) / ε := by rw [le_div_iff₀ hε]; linarith
    rw [hψ_apply, min_eq_left hge, max_eq_right zero_le_one]
  have hψ_out : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) A → ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have hneg : (A - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    rw [hψ_apply, min_eq_right (hneg.le.trans zero_le_one), max_eq_left hneg.le]
  -- Step 3: `Hⁿ(Q ∩ B₁(0)) = ωₙ`, via a linear isometry `ℝⁿ → ℝᴾ` onto `Q`
  have hplane : μHE[n] (ball (0 : Euclid P) 1 ∩ (Q : Set (Euclid P))) = unitBallVolume n := by
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ.1)
    have hj : Isometry (Q.subtypeₗᵢ ∘ b.repr.symm) := Q.subtypeₗᵢ.isometry.comp b.repr.symm.isometry
    have himg : (Q.subtypeₗᵢ ∘ b.repr.symm) '' ball (0 : Euclid n) 1 =
        ball (0 : Euclid P) 1 ∩ (Q : Set (Euclid P)) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨?_, (b.repr.symm v).2⟩
        rw [mem_ball_zero_iff] at hv ⊢
        rwa [Function.comp_apply, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]
      · rintro ⟨hy, hyQ⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_ball_zero_iff] at hy ⊢
          rwa [LinearIsometryEquiv.norm_map, ← Submodule.norm_coe]
        · simp
    rw [← himg, hj.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rfl
  have hL : (unitBallVolume n).toReal ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hQ.1
    calc (unitBallVolume n).toReal
        = ∫ y in ball (0 : Euclid P) 1, ψ y ∂((μHE[n] : Measure (Euclid P)).restrict Q) := by
          rw [setIntegral_congr_fun measurableSet_ball
            (fun y hy => hψ1 y (mem_ball_zero_iff.mp hy).le),
            setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
            Measure.restrict_apply measurableSet_ball, hplane]
      _ ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] :=
          setIntegral_le_integral ψ.integrable (Eventually.of_forall hψ0)
  -- the blow-up integrals `a(r) = ∫_{η_r(M)} ψ dHⁿ` converge to `∫_Q ψ dHⁿ ≥ ωₙ > c (1 + ε)ⁿ`
  have hcA_top : c * ENNReal.ofReal (A ^ n) ≠ ∞ := ne_top_of_lt hεω
  have hcA_lt : (c * ENNReal.ofReal (A ^ n)).toReal < ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] :=
    (ENNReal.toReal_strict_mono hω_top hεω).trans_le hL
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (c * ENNReal.ofReal (A ^ n)).toReal <
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n] :=
    (hQ.2 ψ).eventually (lt_mem_nhds hcA_lt)
  -- Step 4: `ofReal (a(r)) ≤ Hⁿ(B̄_A(0) ∩ η_r(M)) = r⁻ⁿ Hⁿ(M ∩ B̄_{rA}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] T := by
    intro r hr T
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' T =
        AffineMap.homothety (0 : Euclid P) r⁻¹ '' ((fun y : Euclid P => y - x) '' T) := by
      rw [Set.image_image]
      refine Set.image_congr fun y _ => ?_
      change r⁻¹ • (y - x) = _
      rw [AffineMap.homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]
    have hτ : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Euclid P) (inv_ne_zero hr.ne'),
      hτ.euclideanHausdorffMeasure_image, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
      Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hball : ∀ r : ℝ, 0 < r → closedBall (0 : Euclid P) A ∩
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (r * A)) := by
    intro r hr
    have hmem : ∀ y : Euclid P, Poincare.SimonGMT.Chapter03.blowUpMap x r y ∈
        closedBall (0 : Euclid P) A ↔ y ∈ closedBall x (r * A) := by
      intro y
      change r⁻¹ • (y - x) ∈ closedBall (0 : Euclid P) A ↔ y ∈ closedBall x (r * A)
      rw [mem_closedBall_zero_iff, mem_closedBall, dist_eq_norm, norm_smul,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, ← div_eq_inv_mul, div_le_iff₀ hr, mul_comm A r]
    ext y
    constructor
    · rintro ⟨hyB, z, hzM, rfl⟩
      exact ⟨z, ⟨hzM, (hmem z).mp hyB⟩, rfl⟩
    · rintro ⟨z, ⟨hzM, hzB⟩, rfl⟩
      exact ⟨(hmem z).mpr hzB, z, hzM, rfl⟩
  have hupper : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]) ≤
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
    intro r hr
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hψ0)
      ψ.continuous.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal_le.trans ?_
    calc ∫⁻ y, ENNReal.ofReal (ψ y)
          ∂((μHE[n] : Measure (Euclid P)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        ≤ ∫⁻ y, (closedBall (0 : Euclid P) A).indicator 1 y
          ∂((μHE[n] : Measure (Euclid P)).restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) A
          · rw [indicator_of_mem hy, Pi.one_apply]
            exact ENNReal.ofReal_le_one.mpr (hψle1 y)
          · rw [hψ_out y hy, ENNReal.ofReal_zero]
            exact zero_le
      _ = μHE[n] (closedBall (0 : Euclid P) A ∩
            Poincare.SimonGMT.Chapter03.blowUpMap x r '' M) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall]
      _ = ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
          rw [hball r hr, hscale r hr]
  -- Step 5: `c (rA)ⁿ ≤ Hⁿ(M ∩ B̄_{rA}(x))` for small `r > 0`; reparametrize `ρ = rA`
  have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * ENNReal.ofReal ((r * A) ^ n) ≤ μHE[n] (M ∩ closedBall x (r * A)) := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have h1 : c * ENNReal.ofReal (A ^ n) ≤
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
      rw [← ENNReal.ofReal_toReal hcA_top]
      exact (ENNReal.ofReal_le_ofReal hr.le).trans (hupper r hr0')
    calc c * ENNReal.ofReal ((r * A) ^ n)
        = c * ENNReal.ofReal (A ^ n) * ENNReal.ofReal r ^ n := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr0'.le n), ENNReal.ofReal_pow hr0'.le,
            mul_comm (ENNReal.ofReal r ^ n), mul_assoc]
      _ ≤ ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) * ENNReal.ofReal r ^ n := by
          gcongr
      _ = μHE[n] (M ∩ closedBall x (r * A)) := by
          rw [mul_comm (ENNReal.ofReal (r⁻¹) ^ n), mul_assoc, ← mul_pow,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hr0'.le), inv_mul_cancel₀ hr0'.ne',
            ENNReal.ofReal_one, one_pow, mul_one]
  have htend : Tendsto (fun ρ : ℝ => ρ / A) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const A).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact div_pos hρ hA
  filter_upwards [htend.eventually hev2] with ρ hρ
  rwa [div_mul_cancel₀ ρ hA.ne'] at hρ
/-- **`Hⁿ` of a disc in an `n`-plane**: if `Q ⊆ ℝᴾ` is an `n`-dimensional subspace and `r ≥ 0`, then
`Hⁿ(Q ∩ B̄_r(0)) = rⁿ ωₙ`.  An orthonormal basis of `Q` gives a linear isometry `j : ℝⁿ → ℝᴾ`
with `j(B̄_r(0)) = Q ∩ B̄_r(0)`; `Hⁿ` is invariant under isometries and equals Lebesgue measure on
`ℝⁿ`, and `Lⁿ(B̄_r(0)) = rⁿ Lⁿ(B₁(0))`. -/
theorem Submission.cbrr_tcd_plane_closedBall_measure : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ r : ℝ, 0 ≤ r → μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 r) = ENNReal.ofReal (r ^ n) * unitBallVolume n := by
  intro P n Q hQ r hr
  -- Step 1: an orthonormal basis `b` of `Q` indexed by `Fin n`
  let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
  -- Step 2: the isometry `j = ι ∘ b.repr.symm : ℝⁿ → ℝᴾ`
  have hj : Isometry (Q.subtypeₗᵢ ∘ b.repr.symm) := Q.subtypeₗᵢ.isometry.comp b.repr.symm.isometry
  -- Step 3: `j(B̄_r(0)) = Q ∩ B̄_r(0)`
  have himg : (Q.subtypeₗᵢ ∘ b.repr.symm) '' closedBall (0 : Euclid n) r =
      (Q : Set (Euclid P)) ∩ closedBall 0 r := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(b.repr.symm v).2, ?_⟩
      rw [mem_closedBall_zero_iff] at hv ⊢
      rwa [Function.comp_apply, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]
    · rintro ⟨hyQ, hy⟩
      refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff] at hy ⊢
        rwa [LinearIsometryEquiv.norm_map, ← Submodule.norm_coe]
      · simp
  -- Steps 4–7: isometry invariance, `Hⁿ = Lⁿ` on `ℝⁿ`, Haar scaling, and `ωₙ = Lⁿ(B₁(0))`
  rw [← himg, hj.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall _ _ hr,
    finrank_euclideanSpace_fin]
  rfl
/-- **Cutoff for the cone `X = {y : 2|p_Q y| < |y|}`**: for a subspace `Q ⊆ ℝᴾ` and `δ > 0` there
is `f ∈ C_c(ℝᴾ)` with `0 ≤ f ≤ 1`, `f = 1` on `X ∩ B₁(0)` and `f = 0` on `Q \ B̄_δ(0)`.  With
`s = δ/4` take `f = φχ`, `φ(y) = max(0, min(1, 1 + ((3/4)|y| − |p_Q y|)/s))` and
`χ(y) = max(0, min(1, 2 − |y|))`; `f` vanishes outside `B̄₂(0)`. -/
theorem Submission.cbrr_tcd_cone_cutoff_exists : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (δ : ℝ), 0 < δ → ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, (∀ y, 0 ≤ f y) ∧ (∀ y, f y ≤ 1) ∧ (∀ y : Euclid P, 2 * ‖Q.starProjection y‖ < ‖y‖ → ‖y‖ < 1 → f y = 1) ∧ ∀ y ∈ Q, δ < ‖y‖ → f y = 0 := by
  intro P Q δ hδ
  -- Step 1: `s = δ/4`, `h(y) = (3/4)|y| − |p_Q y|`, `φ = max(0, min(1, 1 + h/s))`,
  -- `χ = max(0, min(1, 2 − |y|))`.
  set s : ℝ := δ / 4 with hs_def
  have hs : 0 < s := by positivity
  let φ : Euclid P → ℝ := fun y => max 0 (min 1 (1 + (3 / 4 * ‖y‖ - ‖Q.starProjection y‖) / s))
  let χ : Euclid P → ℝ := fun y => max 0 (min 1 (2 - ‖y‖))
  -- Step 2: `φ` and `χ` are continuous (`p_Q` is a continuous linear map).
  have hφ : Continuous φ :=
    continuous_const.max (continuous_const.min (continuous_const.add
      (((continuous_const.mul continuous_norm).sub Q.starProjection.continuous.norm).div_const s)))
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  -- Step 3: `χ`, hence `φχ`, vanishes outside the compact ball `B̄₂(0)`.
  have hsupp : HasCompactSupport fun y => φ y * χ y := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 2) fun y hy => ?_
    rw [mem_closedBall_zero_iff, not_le] at hy
    have hχy : χ y = 0 := by
      simp only [χ]
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    simp [hχy]
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    { toFun := fun y => φ y * χ y
      continuous_toFun := hφ.mul hχ
      hasCompactSupport' := hsupp }
  have hf : ∀ y, f y = φ y * χ y := fun _ => rfl
  -- Step 4: `max(0, min(1, a)) ∈ [0, 1]`, so `0 ≤ φ, χ ≤ 1` and `0 ≤ φχ ≤ φ ≤ 1`.
  have hclamp : ∀ a : ℝ, 0 ≤ max 0 (min 1 a) ∧ max 0 (min 1 a) ≤ 1 := fun a =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  refine ⟨f, fun y => ?_, fun y => ?_, fun y hX hB => ?_, fun y hyQ hyδ => ?_⟩
  · rw [hf]
    exact mul_nonneg (hclamp _).1 (hclamp _).1
  · rw [hf]
    calc φ y * χ y ≤ φ y * 1 := mul_le_mul_of_nonneg_left (hclamp _).2 (hclamp _).1
      _ = φ y := mul_one _
      _ ≤ 1 := (hclamp _).2
  -- Step 5: if `2|p_Q y| < |y| < 1` then `h(y) > |y|/4 ≥ 0`, so `φ(y) = 1`; and `χ(y) = 1`.
  · have hh : 0 ≤ (3 / 4 * ‖y‖ - ‖Q.starProjection y‖) / s :=
      div_nonneg (by linarith [norm_nonneg y]) hs.le
    have hφy : φ y = 1 := by
      simp only [φ]
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    have hχy : χ y = 1 := by
      simp only [χ]
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    rw [hf, hφy, hχy, one_mul]
  -- Step 6: if `y ∈ Q` and `|y| > δ` then `p_Q y = y`, so `1 + h(y)/s = 1 − |y|/δ < 0` and
  -- `φ(y) = 0`.
  · have hp : Q.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hyQ
    have hneg : 1 + (3 / 4 * ‖y‖ - ‖y‖) / s < 0 := by
      have h1 : (3 / 4 * ‖y‖ - ‖y‖) / s = -(‖y‖ / δ) := by
        rw [hs_def]
        field_simp
        ring
      have h2 : 1 < ‖y‖ / δ := (one_lt_div hδ).mpr hyδ
      linarith
    have hφy : φ y = 0 := by
      simp only [φ]
      rw [hp, min_eq_right (by linarith), max_eq_left hneg.le]
    rw [hf, hφy, zero_mul]
/-- **`Hⁿ` under the blow-up map `η_{x,r}(y) = r⁻¹(y − x)`, `r > 0`**: `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)`
for every `S ⊆ ℝᴾ`, the scaling used in the proof of Simon Ch. 3, Theorem 1.6 "⇒".  `η_{x,r}` is
the translation `y ↦ y + (−x)`, an isometry, followed by the dilation `z ↦ r⁻¹z`, and
`Hⁿ(cT) = |c|ⁿ Hⁿ(T)` for `c ≠ 0`. -/
theorem Submission.rsd_cmr_ir_blowUp_image_measure : ∀ (P n : ℕ) (x : Euclid P) (r : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] S := by
  intro P n x r S hr
  -- `η_{x,r}(S) = r⁻¹ • (S + (−x))`: `η_{x,r}(y) = r⁻¹ • (y − x)` and `y − x = y + (−x)`.
  have hS : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
      (fun z => r⁻¹ • z) '' ((fun y => y + -x) '' S) := by
    rw [Set.image_image]
    rfl
  -- `Hⁿ(r⁻¹ • T) = ‖r⁻¹‖₊ⁿ • Hⁿ(T)`, translation invariance, and `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n` for `r > 0`.
  rw [hS, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
    (isometry_add_right (-x)).euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul,
    ← ENNReal.ofReal_coe_nnreal]
  congr 2
  simp [abs_of_pos hr]

/-- **Small-scale upper bound at an approximate tangent point**: if `Q` is the approximate tangent
space of `M` at `x` (Simon Ch. 3, 1.4), `Hⁿ(M) < ∞`, and `f ∈ C_c(ℝᴾ)` satisfies `f ≥ 0` and
`f ≥ 1` on the measurable set `U`, then `Hⁿ(M ∩ η_{x,r}⁻¹(U)) ≤ t rⁿ` for all small `r > 0`
whenever `∫_Q f dHⁿ < t`.  Indeed `Hⁿ(η_{x,r}(M) ∩ U) ≤ ∫_{η_{x,r}(M)} f dHⁿ → ∫_Q f dHⁿ`, and
`η_{x,r}(M) ∩ U = η_{x,r}(M ∩ η_{x,r}⁻¹(U))` has measure `r⁻ⁿ Hⁿ(M ∩ η_{x,r}⁻¹(U))`. -/
theorem Submission.cbrr_tcd_blowUp_preimage_le_of_testFunction : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (U : Set (Euclid P)) (f : CompactlySupportedContinuousMap (Euclid P) ℝ), μHE[n] M ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → MeasurableSet U → (∀ y, 0 ≤ f y) → (∀ y ∈ U, 1 ≤ f y) → ∀ t : ℝ≥0∞, ENNReal.ofReal (∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]) < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), μHE[n] (M ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' U) ≤ t * ENNReal.ofReal (r ^ n) := by
  intro P n M x Q U f hM hT hU hf0 hfU t ht
  -- `t = ∞`: the right-hand side is `∞` for every `r > 0`.
  rcases eq_or_ne t ∞ with rfl | htop
  · filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ENNReal.top_mul (ENNReal.ofReal_pos.2 (pow_pos hr n)).ne']
    exact le_top
  -- `∫_Q f dHⁿ < t`, and `∫_{η_{x,r}(M)} f dHⁿ → ∫_Q f dHⁿ`, so eventually `∫_{η_{x,r}(M)} f < t`.
  have hL : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] < t.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (integral_nonneg hf0) htop).1 ht
  filter_upwards [self_mem_nhdsWithin, (hT.2 f).eventually (gt_mem_nhds hL)] with r hr hI
  have hr0 : (0 : ℝ) < r := hr
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r
  -- `Hⁿ(η_{x,r}(M)) = r⁻ⁿ Hⁿ(M) < ∞`, so `f` is integrable for `Hⁿ⌞η_{x,r}(M)`.
  have hfin : μHE[n] (η '' M) ≠ ∞ := by
    rw [Submission.rsd_cmr_ir_blowUp_image_measure P n x r M hr0]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  have : IsFiniteMeasure (μHE[n].restrict (η '' M)) := isFiniteMeasure_restrict.2 hfin
  have hint : Integrable f (μHE[n].restrict (η '' M)) := f.integrable
  -- `Hⁿ(η_{x,r}(M) ∩ U) = ∫ 1_U d(Hⁿ⌞η_{x,r}(M)) ≤ ∫_{η_{x,r}(M)} f dHⁿ ≤ t`.
  have hle : μHE[n] (η '' M ∩ U) ≤ t := by
    calc μHE[n] (η '' M ∩ U) = μHE[n].restrict (η '' M) U := by
          rw [Measure.restrict_apply hU, Set.inter_comm]
      _ = ∫⁻ y, U.indicator 1 y ∂(μHE[n].restrict (η '' M)) := (lintegral_indicator_one hU).symm
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict (η '' M)) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ U
          · rw [Set.indicator_of_mem hy, Pi.one_apply]
            exact ENNReal.one_le_ofReal.2 (hfU y hy)
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y in η '' M, f y ∂μHE[n]) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0)).symm
      _ ≤ ENNReal.ofReal t.toReal := ENNReal.ofReal_le_ofReal hI.le
      _ = t := ENNReal.ofReal_toReal htop
  -- `η_{x,r}(M) ∩ U = η_{x,r}(M ∩ η_{x,r}⁻¹(U))`, whose measure is `r⁻ⁿ Hⁿ(M ∩ η_{x,r}⁻¹(U))`.
  have hscale : μHE[n] (η '' M ∩ U) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ η ⁻¹' U) := by
    rw [← Set.image_inter_preimage]
    exact Submission.rsd_cmr_ir_blowUp_image_measure P n x r _ hr0
  have hcancel : ENNReal.ofReal (r ^ n) * ENNReal.ofReal (r⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr0.le n), ← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow,
      ENNReal.ofReal_one]
  calc μHE[n] (M ∩ η ⁻¹' U)
      = ENNReal.ofReal (r ^ n) * (ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ η ⁻¹' U)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ ENNReal.ofReal (r ^ n) * t := by
        rw [← hscale]
        gcongr
    _ = t * ENNReal.ofReal (r ^ n) := mul_comm _ _

/-- **Vanishing density in the cone about the normal space** (Simon Ch. 3, Remark 1.5(3), second
half, and formula (6) in the proof of Theorem 1.6): if `Q` is the approximate tangent space of `M`
at `x`, `n ≥ 1` and `Hⁿ(M) < ∞`, then for every `t > 0`, `Hⁿ(M ∩ X(x) ∩ B_ρ(x)) ≤ t ρⁿ` for all
small `ρ > 0`, where `X(x) = {z : 2|p_Q(z − x)| < |z − x|} = X_{1/2}((TₓM)^⊥, x)`.  Choose `δ > 0`
with `Hⁿ(Q ∩ B̄_δ(0)) = δⁿωₙ < t` and `f ∈ C_c` with `0 ≤ f ≤ 1`, `f = 1` on `X ∩ B₁(0)` and
`f = 0` on `Q \ B̄_δ(0)`.  Then `∫_Q f dHⁿ ≤ Hⁿ(Q ∩ B̄_δ(0)) < t`, so the blow-up bound gives
`Hⁿ(M ∩ η_{x,r}⁻¹(X ∩ B₁(0))) ≤ t rⁿ` for small `r > 0`, and `η_{x,r}⁻¹(X ∩ B₁(0)) = X(x) ∩ B_r(x)`. -/
theorem Submission.cbrr_tangent_cone_density_zero : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → μHE[n] M ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → ∀ t : ℝ≥0∞, 0 < t → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (M ∩ ({z | 2 * ‖Q.starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ)) ≤ t * ENNReal.ofReal (ρ ^ n) := by
  intro P n M x Q hn hM hQ t ht
  -- Step 1: `ωₙ < ∞` and `n ≥ 1`, so `δⁿωₙ → 0` as `δ → 0`; choose `δ > 0` with `δⁿωₙ < t`, so
  -- that `Hⁿ(Q ∩ B̄_δ(0)) = δⁿωₙ < t` (`dim Q = n`)
  have hω_top : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ n) * unitBallVolume n) (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun δ : ℝ => δ ^ n) (𝓝 0) (𝓝 0) := by
      have h := (continuous_pow n).tendsto (0 : ℝ)
      rwa [zero_pow hn.ne'] at h
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h0) (Or.inr hω_top)
    rwa [ENNReal.ofReal_zero, zero_mul] at h
  obtain ⟨δ, hδt, hδ⟩ := ((hlim.eventually (gt_mem_nhds ht)).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  have hδ0 : 0 < δ := hδ
  have hplane : μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 δ) < t := by
    rw [Submission.cbrr_tcd_plane_closedBall_measure P n Q hQ.1 δ hδ0.le]
    exact hδt
  -- Step 2: the cutoff `f ∈ C_c`: `0 ≤ f ≤ 1`, `f = 1` on `X ∩ B₁(0)`, `f = 0` on `Q \ B̄_δ(0)`
  obtain ⟨f, hf0, hf1, hfX, hfQ⟩ := Submission.cbrr_tcd_cone_cutoff_exists P Q δ hδ0
  -- Step 3: `ofReal (∫_Q f dHⁿ) ≤ ∫⁻_Q ofReal ∘ f dHⁿ ≤ Hⁿ(Q ∩ B̄_δ(0)) < t`, as
  -- `ofReal ∘ f ≤ 1_{B̄_δ(0)}` on `Q`
  have hQm : MeasurableSet (Q : Set (Euclid P)) := Q.closed_of_finiteDimensional.measurableSet
  have hint : ENNReal.ofReal (∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]) < t := by
    refine lt_of_le_of_lt ?_ hplane
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0)
      f.continuous.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal_le.trans ?_
    calc ∫⁻ y in (Q : Set (Euclid P)), ENNReal.ofReal (f y) ∂μHE[n]
        ≤ ∫⁻ y in (Q : Set (Euclid P)), (closedBall (0 : Euclid P) δ).indicator 1 y ∂μHE[n] := by
          refine setLIntegral_mono' hQm fun y hy => ?_
          by_cases hyδ : y ∈ closedBall (0 : Euclid P) δ
          · rw [indicator_of_mem hyδ, Pi.one_apply]
            exact ENNReal.ofReal_le_one.mpr (hf1 y)
          · rw [mem_closedBall_zero_iff, not_le] at hyδ
            rw [hfQ y hy hyδ, ENNReal.ofReal_zero]
            exact zero_le
      _ = μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 δ) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- Step 4: the blow-up bound for the open set `U = X ∩ B₁(0)`, on which `f = 1`
  set U : Set (Euclid P) := {y | 2 * ‖Q.starProjection y‖ < ‖y‖} ∩ ball 0 1
  have hU : IsOpen U :=
    (isOpen_lt (continuous_const.mul Q.starProjection.continuous.norm) continuous_norm).inter
      isOpen_ball
  have hfU : ∀ y ∈ U, 1 ≤ f y := fun y hy => (hfX y hy.1 (mem_ball_zero_iff.mp hy.2)).ge
  filter_upwards [Submission.cbrr_tcd_blowUp_preimage_le_of_testFunction P n M x Q U f hM hQ
    hU.measurableSet hf0 hfU t hint, self_mem_nhdsWithin] with r hr hr0
  -- Step 5: for `r > 0`, `η_{x,r}⁻¹(X ∩ B₁(0)) = X(x) ∩ B_r(x)`, since `η_{x,r}(z) = r⁻¹(z − x)`,
  -- `p_Q` is linear and `|r⁻¹v| = r⁻¹|v|`
  have hr0' : 0 < r := hr0
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr0'
  have hset : {z | 2 * ‖Q.starProjection (z - x)‖ < ‖z - x‖} ∩ ball x r =
      Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' U := by
    ext z
    have hnorm : ‖r⁻¹ • (z - x)‖ = r⁻¹ * ‖z - x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hrinv.le]
    have hproj : ‖Q.starProjection (r⁻¹ • (z - x))‖ = r⁻¹ * ‖Q.starProjection (z - x)‖ := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg hrinv.le]
    change 2 * ‖Q.starProjection (z - x)‖ < ‖z - x‖ ∧ dist z x < r ↔
      2 * ‖Q.starProjection (r⁻¹ • (z - x))‖ < ‖r⁻¹ • (z - x)‖ ∧ dist (r⁻¹ • (z - x)) 0 < 1
    rw [dist_eq_norm, dist_eq_norm, sub_zero, hproj, hnorm, mul_left_comm,
      mul_lt_mul_iff_right₀ hrinv, inv_mul_lt_iff₀ hr0', mul_one]
  rw [hset]
  exact hr

/-- **Lusin's theorem for an a.e. strongly measurable map, keeping an a.e. property** (the closed
set `F` of Simon Ch. 3, proof of Theorem 1.6 "⇐", (4)): if `A` is measurable with `μ(A) < ∞`,
`f : ℝᴾ → Y` is `μ⌞A`-a.e. strongly measurable into a pseudo-metrizable, second-countable `Y` and
`p` holds `μ⌞A`-a.e., then for every `η ≠ 0` there is a compact `K ⊆ A` with `μ(A \ K) < η` on
which `p` holds and `f` is continuous.  With the Borel σ-algebra on `Y`, the strongly measurable
representative `g` of `f` is measurable.  The bad set `Z = {f ≠ g} ∪ {¬p}` has
`μ(Z ∩ A) = μ⌞A(Z) = 0`, so a measurable `μ`-null `N ⊇ Z ∩ A` leaves `A \ N`, on which `f = g`
and `p` hold.  Lusin's theorem for `g` on `A \ N` gives `K`, and `A \ K ⊆ N ∪ ((A \ N) \ K)`. -/
theorem Submission.cbrr_ud_lusin_of_aestronglyMeasurable : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y] [SecondCountableTopology Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Y) (p : Euclid P → Prop), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f (μ.restrict A) → (∀ᵐ x ∂(μ.restrict A), p x) → ∀ η : ℝ≥0∞, η ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < η ∧ (∀ x ∈ K, p x) ∧ ContinuousOn f K := by
  intro P Y _ _ _ μ A f p hA hμA hf hp η hη
  -- Step 1: give `Y` its Borel σ-algebra; the strongly measurable representative `g = hf.mk f`
  -- of `f` is then measurable, and `f = g` `μ⌞A`-a.e.
  borelize Y
  have hg : Measurable (hf.mk f) := hf.measurable_mk
  -- Step 2: the bad set `Z = {f ≠ g} ∪ {¬p}` has `μ (Z ∩ A) = μ⌞A Z = 0`; a measurable `μ`-null
  -- `N ⊇ Z ∩ A` leaves the measurable `A \ N`, on which `f = g` and `p` hold
  have hZ : μ ({x | ¬(f x = hf.mk f x ∧ p x)} ∩ A) = 0 := by
    rw [← Measure.restrict_apply' hA]
    exact ae_iff.mp (hf.ae_eq_mk.and hp)
  obtain ⟨N, hZN, hN, hN0⟩ := exists_measurable_superset_of_null hZ
  have hgood : ∀ x ∈ A \ N, f x = hf.mk f x ∧ p x := fun x hx =>
    not_not.mp fun h => hx.2 (hZN ⟨h, hx.1⟩)
  -- Step 3: Lusin's theorem for `g` on `A \ N`: a compact `K ⊆ A \ N` with `μ ((A \ N) \ K) < η`
  -- on which `g` is continuous
  obtain ⟨K, hK, hKA, hKμ, hgK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ N)
    (hf.mk f) η hg (hA.diff hN) (measure_ne_top_of_subset sdiff_subset hμA) hη
  -- Step 4: `f = g` and `p` hold on `K ⊆ A \ N`, and `A \ K ⊆ N ∪ (A \ N) \ K` with `μ N = 0`
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, fun x hx => (hgood x (hKA hx)).2,
    hgK.congr fun x hx => (hgood x (hKA hx)).1⟩
  calc μ (A \ K)
      ≤ μ (N ∪ (A \ N) \ K) := by
        refine measure_mono fun x hx => ?_
        by_cases hxN : x ∈ N
        · exact Or.inl hxN
        · exact Or.inr ⟨⟨hx.1, hxN⟩, hx.2⟩
    _ ≤ μ N + μ ((A \ N) \ K) := measure_union_le _ _
    _ = μ ((A \ N) \ K) := by rw [hN0, zero_add]
    _ < η := hKμ
/-- **Upper semicontinuity of closed-ball mass** (for Egoroff's theorem in Simon Ch. 3, proof of
Theorem 1.6, (7)–(8)): for a finite measure `μ` on `ℝᴾ`, `ρ ∈ ℝ` and `s ∈ [0, ∞]`, the set
`{y : s ≤ μ(B̄_ρ(y))}` is closed.  If `yᵢ → y` and `s ≤ μ(B̄_ρ(yᵢ))` for all `i`, the open
complements `U = B̄_ρ(y)ᶜ` and `Uᵢ = B̄_ρ(yᵢ)ᶜ` satisfy `1_U ≤ liminf 1_{Uᵢ}`, so Fatou's lemma
gives `μ(U) ≤ liminf μ(Uᵢ) ≤ μ(ℝᴾ) − s`; as `μ` is finite and `s ≤ μ(ℝᴾ)`,
`μ(B̄_ρ(y)) = μ(ℝᴾ) − μ(U) ≥ s`. -/
theorem Submission.cbrr_ud_isClosed_closedBall_mass_ge : ∀ (P : ℕ) (μ : Measure (Euclid P)) [IsFiniteMeasure μ] (ρ : ℝ) (s : ℝ≥0∞), IsClosed {y : Euclid P | s ≤ μ (closedBall y ρ)} := by
  intro P μ _ ρ s
  -- Step 1: `ℝᴾ` is a sequential space; let `yᵢ → y` with `s ≤ μ(B̄_ρ(yᵢ))` for all `i`
  refine IsSeqClosed.isClosed fun ys y hys hlim => ?_
  replace hys : ∀ i, s ≤ μ (closedBall (ys i) ρ) := hys
  show s ≤ μ (closedBall y ρ)
  -- Step 2: the complements `U = B̄_ρ(y)ᶜ` and `Uᵢ = B̄_ρ(yᵢ)ᶜ` are open, hence Borel
  have hU : ∀ x : Euclid P, MeasurableSet (closedBall x ρ)ᶜ :=
    fun x => measurableSet_closedBall.compl
  -- Step 3: `1_U ≤ liminf 1_{Uᵢ}`: if `|z − y| > ρ`, then `|z − yᵢ| > ρ` for all large `i`
  have hpt : ∀ z, (closedBall y ρ)ᶜ.indicator 1 z ≤
      liminf (fun i => (closedBall (ys i) ρ)ᶜ.indicator (1 : Euclid P → ℝ≥0∞) z) atTop := by
    intro z
    by_cases hz : z ∈ closedBall y ρ
    · rw [indicator_of_notMem (not_not.mpr hz)]
      exact zero_le
    · rw [mem_closedBall, not_le] at hz
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [(tendsto_const_nhds.dist hlim).eventually (lt_mem_nhds hz)] with i hi
      rw [indicator_of_mem (not_le.mpr hz), indicator_of_mem (not_le.mpr hi)]
  -- Step 4: Fatou's lemma gives `μ(U) ≤ liminf μ(Uᵢ)`
  have hfatou : μ (closedBall y ρ)ᶜ ≤ liminf (fun i => μ (closedBall (ys i) ρ)ᶜ) atTop :=
    calc μ (closedBall y ρ)ᶜ = ∫⁻ z, (closedBall y ρ)ᶜ.indicator 1 z ∂μ :=
          (lintegral_indicator_one (hU y)).symm
      _ ≤ ∫⁻ z, liminf (fun i => (closedBall (ys i) ρ)ᶜ.indicator 1 z) atTop ∂μ :=
          lintegral_mono hpt
      _ ≤ liminf (fun i => ∫⁻ z, (closedBall (ys i) ρ)ᶜ.indicator 1 z ∂μ) atTop :=
          lintegral_liminf_le fun i => measurable_one.indicator (hU (ys i))
      _ = liminf (fun i => μ (closedBall (ys i) ρ)ᶜ) atTop := by
          simp_rw [lintegral_indicator_one (hU _)]
  -- Step 5: `μ(Uᵢ) = μ(ℝᴾ) − μ(B̄_ρ(yᵢ)) ≤ μ(ℝᴾ) − s` for every `i`, so `μ(U) ≤ μ(ℝᴾ) − s`
  have hUle : μ (closedBall y ρ)ᶜ ≤ μ univ - s := by
    refine hfatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun i => ?_))
    rw [measure_compl measurableSet_closedBall (measure_ne_top _ _)]
    exact tsub_le_tsub_left (hys i) _
  -- Step 6: `s ≤ μ(B̄_ρ(y₀)) ≤ μ(ℝᴾ) < ∞`, so
  -- `μ(B̄_ρ(y)) = μ(ℝᴾ) − μ(U) ≥ μ(ℝᴾ) − (μ(ℝᴾ) − s) = s`
  have hs : s ≤ μ univ := (hys 0).trans (measure_mono (subset_univ _))
  calc s = μ univ - (μ univ - s) := (ENNReal.sub_sub_cancel (measure_ne_top _ _) hs).symm
    _ ≤ μ univ - μ (closedBall y ρ)ᶜ := tsub_le_tsub_left hUle _
    _ = μ (closedBall y ρ) := by
        rw [← measure_compl (hU y) (measure_ne_top _ _), compl_compl]
/-- **Closed cone-mass sublevel sets** (Simon Ch. 3, proof of Theorem 1.6 "⇐", (7)–(8); this
closedness replaces the measurability of the functions `q_k` there).  Let `F` be closed and
`w ↦ p_{Q(w)}` continuous on `F`, and put `S(w) = X(w) ∩ B_ρ(w)`, where
`X(w) = {z : 2|p_{Q(w)}(z − w)| < |z − w|}`.  Then `{x ∈ F : μ(S(x)) ≤ s}` is closed.  Let
`xᵢ → x` in this set; then `x ∈ F`.  Each `S(w)` is open.  As `p_{Q(xᵢ)} → p_{Q(x)}`, every
`z ∈ S(x)` lies in `S(xᵢ)` for all large `i`, so `1_{S(x)} ≤ liminf 1_{S(xᵢ)}`.  Fatou's lemma
gives `μ(S(x)) ≤ liminf μ(S(xᵢ)) ≤ s`. -/
theorem Submission.cbrr_ud_isClosed_cone_mass_le : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (ρ : ℝ) (s : ℝ≥0∞), IsClosed F → ContinuousOn (fun x => (Q x).starProjection) F → IsClosed {x | x ∈ F ∧ μ ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ s} := by
  intro P μ F Q ρ s hF hQ
  -- Step 1: sequential closedness; the limit `x` of the `xᵢ ∈ F` lies in the closed set `F`
  refine IsSeqClosed.isClosed fun xs x hxs hx => ?_
  have hxsF : ∀ i, xs i ∈ F := fun i => (hxs i).1
  have hxF : x ∈ F := hF.mem_of_tendsto hx (Eventually.of_forall hxsF)
  refine ⟨hxF, ?_⟩
  set S : Euclid P → Set (Euclid P) := fun w =>
    {z | 2 * ‖(Q w).starProjection (z - w)‖ < ‖z - w‖} ∩ ball w ρ
  change μ (S x) ≤ s
  -- Step 2: every `S(w) = X(w) ∩ B_ρ(w)` is open, hence measurable
  have hSm : ∀ w, MeasurableSet (S w) := fun w =>
    ((isOpen_lt (continuous_const.mul ((Q w).starProjection.continuous.comp
      (continuous_id.sub continuous_const)).norm) (continuous_id.sub continuous_const).norm).inter
      isOpen_ball).measurableSet
  -- Step 3: `xᵢ → x` within `F`, where `w ↦ p_{Q(w)}` is continuous
  have hxW : Tendsto xs atTop (𝓝[F] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, Eventually.of_forall hxsF⟩
  -- Step 4: `2|p_{Q(xᵢ)}(z − xᵢ)| − |z − xᵢ| → 2|p_{Q(x)}(z − x)| − |z − x| < 0` and
  -- `|z − xᵢ| → |z − x| < ρ`, so every `z ∈ S(x)` lies in `S(xᵢ)` for all large `i`
  have hev : ∀ z ∈ S x, ∀ᶠ i in atTop, z ∈ S (xs i) := by
    intro z hz
    have hcont : ContinuousWithinAt
        (fun w => 2 * ‖(Q w).starProjection (z - w)‖ - ‖z - w‖) F x :=
      (continuousWithinAt_const.mul ((hQ x hxF).clm_apply
        (continuousWithinAt_const.sub continuousWithinAt_id)).norm).sub
        (continuousWithinAt_const.sub continuousWithinAt_id).norm
    have h1 := (hcont.tendsto.comp hxW).eventually (gt_mem_nhds (sub_neg.mpr hz.1))
    have h2 := (tendsto_const_nhds.dist hx).eventually (gt_mem_nhds (mem_ball.mp hz.2))
    filter_upwards [h1, h2] with i hi1 hi2
    exact ⟨sub_neg.mp hi1, hi2⟩
  -- Step 5: `1_{S(x)} ≤ liminf 1_{S(xᵢ)}` pointwise, and Fatou's lemma
  calc μ (S x) = ∫⁻ z, (S x).indicator 1 z ∂μ := (lintegral_indicator_one (hSm x)).symm
    _ ≤ ∫⁻ z, liminf (fun i => (S (xs i)).indicator 1 z) atTop ∂μ := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ S x
        · rw [indicator_of_mem hz]
          refine le_liminf_of_le (by isBoundedDefault) ?_
          filter_upwards [hev z hz] with i hi
          rw [indicator_of_mem hi]
        · rw [indicator_of_notMem hz]
          exact zero_le
    _ ≤ liminf (fun i => ∫⁻ z, (S (xs i)).indicator 1 z ∂μ) atTop :=
        lintegral_liminf_le fun i => measurable_one.indicator (hSm (xs i))
    _ = liminf (fun i => μ (S (xs i))) atTop := by simp_rw [lintegral_indicator_one (hSm _)]
    _ ≤ s := liminf_le_of_frequently_le' (Frequently.of_forall fun i => (hxs i).2)
/-- Uniform version of an eventual property on a set of finite measure (Simon Ch. 3, proof of 1.6
“⇐”, (7)–(9): Egoroff's theorem carried out on sets).  If `μ(F) < ∞`, every `T ρ` with `ρ > 0`
is closed and each `x ∈ F` lies in `T ρ` for all small `ρ > 0`, then for `η ≠ 0` there are
`E ⊆ F` with `μ(F \ E) < η` and `δ > 0` such that `E ⊆ T ρ` whenever `0 < ρ < δ`.  The Borel
sets `G_k = F ∩ ⋂_{0 < ρ < 1/(k+1)} T ρ` increase to `F`, so `μ(F \ G_k) → 0` by continuity
from above; take `E = G_k` and `δ = 1/(k+1)` for a large `k`. -/
theorem Submission.cbrr_ud_uniformize_eventually : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F : Set (Euclid P)) (T : ℝ → Set (Euclid P)), MeasurableSet F → μ F ≠ ∞ → (∀ ρ : ℝ, 0 < ρ → IsClosed (T ρ)) → (∀ x ∈ F, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), x ∈ T ρ) → ∀ η : ℝ≥0∞, η ≠ 0 → ∃ (E : Set (Euclid P)) (δ : ℝ), E ⊆ F ∧ 0 < δ ∧ μ (F \ E) < η ∧ ∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → x ∈ T ρ := by
  intro P μ F T hF hμF hT hev η hη
  -- `G_k = F ∩ ⋂_{0 < ρ < 1/(k+1)} T ρ` is Borel, each `T ρ` with `ρ > 0` being closed
  let G : ℕ → Set (Euclid P) := fun k => F ∩ ⋂ ρ ∈ Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)), T ρ
  have hG : ∀ k, MeasurableSet (G k) := fun k =>
    hF.inter (isClosed_biInter fun ρ hρ => hT ρ hρ.1).measurableSet
  -- `G_k` increases with `k`, so `F \ G_k` decreases
  have hanti : Antitone fun k => F \ G k := fun i j hij =>
    sdiff_subset_sdiff_right (inter_subset_inter_right F
      (biInter_subset_biInter_left (Ioo_subset_Ioo_right (Nat.one_div_le_one_div hij))))
  -- `⋃_k G_k = F`: a point of `F` lies in `T ρ` for `0 < ρ < r`, and `1/(k+1) < r` for some `k`
  have hempty : ⋂ k, F \ G k = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have hxF : x ∈ F := (mem_iInter.mp hx 0).1
    obtain ⟨r, hr, hrT⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp (hev x hxF)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
    exact (mem_iInter.mp hx k).2 ⟨hxF, mem_iInter₂.mpr fun ρ hρ => hrT ⟨hρ.1, hρ.2.trans hk⟩⟩
  -- continuity from above: `μ (F \ G_k) → μ ∅ = 0`
  have hlim : Tendsto (fun k => μ (F \ G k)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hF.diff (hG k)).nullMeasurableSet)
      hanti ⟨0, measure_ne_top_of_subset sdiff_subset hμF⟩
    rwa [hempty, measure_empty] at h
  -- some `k` has `μ (F \ G_k) < η`; take `E = G_k` and `δ = 1/(k+1)`
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.mpr hη))).exists
  exact ⟨G k, 1 / ((k : ℝ) + 1), inter_subset_left, Nat.one_div_pos_of_nat, hk,
    fun x hx ρ hρ hρk => mem_iInter₂.mp hx.2 ρ ⟨hρ, hρk⟩⟩
/-- **Uniform lower density and cone bounds on a set of almost full measure** (Simon Ch. 3, proof
of Theorem 1.6 “⇐”, (4)–(9)).  Let `μ = Hⁿ⌞M` with `Hⁿ(M) < ∞`, let `x ↦ p_{Q(x)}` be `μ`-a.e.
strongly measurable and let `Q(x)` be the approximate tangent space of `M` at `μ`-a.e. `x`.  If
`ofReal a < ωₙ`, `b > 0` and `ε > 0`, there are `E ⊆ M` with `Hⁿ(M \ E) < ε` and `δ > 0` such that
for `x ∈ E` and `0 < ρ < δ`: `dim Q(x) = n`, `aρⁿ ≤ μ(B̄_ρ(x))` and `μ(X(x) ∩ B_ρ(x)) ≤ bρⁿ`,
where `X(x) = {z : 2|p_{Q(x)}(z − x)| < |z − x|}`.  Lusin's theorem gives a compact `K ⊆ M` of
tangent points with `Hⁿ(M \ K) < ε/2` on which `x ↦ p_{Q(x)}` is continuous.  The set `T_ρ` of
points of `K` with both bounds at radius `ρ` is closed, and each `x ∈ K` lies in `T_ρ` for all
small `ρ > 0` by the lower density and cone density bounds.  Uniformizing gives `E ⊆ K` with
`Hⁿ(K \ E) < ε/2` and `δ > 0` with `E ⊆ T_ρ` for `0 < ρ < δ`. -/
theorem Submission.cbrr_uniform_density_on_large_set : ∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), 0 < n → MeasurableSet M → μHE[n] M ≠ ∞ → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → ∀ (a b ε : ℝ), ENNReal.ofReal a < unitBallVolume n → 0 < b → 0 < ε → ∃ (E : Set (Euclid P)) (δ : ℝ), E ⊆ M ∧ 0 < δ ∧ μHE[n] (M \ E) < ENNReal.ofReal ε ∧ (∀ x ∈ E, Module.finrank ℝ (Q x) = n) ∧ (∀ y ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (a * ρ ^ n) ≤ (μHE[n].restrict M) (closedBall y ρ)) ∧ ∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → (μHE[n].restrict M) ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n) := by
  intro P n M Q hn hM hMfin hQm hQt a b ε ha hb hε
  -- Step 1: `μ = Hⁿ⌞M` is finite, and `ofReal (ε/2) ≠ 0`
  have : IsFiniteMeasure (μHE[n].restrict M) := isFiniteMeasure_restrict.mpr hMfin
  have hε2 : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  -- Step 2: Lusin's theorem: a compact `K ⊆ M` of tangent points with `Hⁿ(M \ K) < ε/2`, on which
  -- `x ↦ p_{Q(x)}` is continuous
  obtain ⟨K, hK, hKM, hMK, hKt, hKc⟩ := Submission.cbrr_ud_lusin_of_aestronglyMeasurable P
    μHE[n] M (fun x => (Q x).starProjection) (fun x => HasApproximateTangentSpaceAt n M x (Q x))
    hM hMfin hQm hQt (ENNReal.ofReal (ε / 2)) hε2
  -- Step 3: `T_ρ = {y : ofReal(aρⁿ) ≤ μ(B̄_ρ(y))} ∩ {x ∈ K : μ(X(x) ∩ B_ρ(x)) ≤ ofReal(bρⁿ)}` is
  -- closed: closed-ball mass is upper semicontinuous, and cone mass is lower semicontinuous on the
  -- closed set `K`, where `x ↦ p_{Q(x)}` is continuous
  set T : ℝ → Set (Euclid P) := fun ρ =>
    {y | ENNReal.ofReal (a * ρ ^ n) ≤ (μHE[n].restrict M) (closedBall y ρ)} ∩
      {x | x ∈ K ∧ (μHE[n].restrict M) ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩
        ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n)}
  have hTc : ∀ ρ : ℝ, 0 < ρ → IsClosed (T ρ) := fun ρ _ =>
    (Submission.cbrr_ud_isClosed_closedBall_mass_ge P (μHE[n].restrict M) ρ
      (ENNReal.ofReal (a * ρ ^ n))).inter
      (Submission.cbrr_ud_isClosed_cone_mass_le P (μHE[n].restrict M) K Q ρ
        (ENNReal.ofReal (b * ρ ^ n)) hK.isClosed hKc)
  -- Step 4: every `x ∈ K` lies in `T_ρ` for all small `ρ > 0`, by the lower density bound with
  -- `c = ofReal a` and the cone density bound with `t = ofReal b`; here `μ(S) = Hⁿ(M ∩ S)` and
  -- `ofReal(cρⁿ) = ofReal c · ofReal ρⁿ` (`ρⁿ ≥ 0`)
  have hTev : ∀ x ∈ K, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), x ∈ T ρ := by
    intro x hx
    filter_upwards [Submission.doragm_approxTangent_lower_density P n M x (Q x) hn (hKt x hx)
      (ENNReal.ofReal a) ha, Submission.cbrr_tangent_cone_density_zero P n M x (Q x) hn hMfin
      (hKt x hx) (ENNReal.ofReal b) (ENNReal.ofReal_pos.mpr hb), self_mem_nhdsWithin]
      with ρ hρa hρb hρ
    have hρn : 0 ≤ ρ ^ n := pow_nonneg (le_of_lt (show 0 < ρ from hρ)) n
    refine ⟨?_, hx, ?_⟩
    · show ENNReal.ofReal (a * ρ ^ n) ≤ (μHE[n].restrict M) (closedBall x ρ)
      rw [ENNReal.ofReal_mul' hρn, Measure.restrict_apply' hM, inter_comm]
      exact hρa
    · show (μHE[n].restrict M) ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤
        ENNReal.ofReal (b * ρ ^ n)
      rw [ENNReal.ofReal_mul hb.le, Measure.restrict_apply' hM, inter_comm]
      exact hρb
  -- Step 5: uniformize: `E ⊆ K` with `Hⁿ(K \ E) < ε/2` and `δ > 0` with `E ⊆ T_ρ` for `0 < ρ < δ`
  obtain ⟨E, δ, hEK, hδ, hKE, hET⟩ := Submission.cbrr_ud_uniformize_eventually P μHE[n] K T
    hK.isClosed.measurableSet (measure_ne_top_of_subset hKM hMfin) hTc hTev
    (ENNReal.ofReal (ε / 2)) hε2
  -- Step 6: `E ⊆ K ⊆ M` consists of tangent points, both bounds come from `T_ρ`, and
  -- `M \ E ⊆ (M \ K) ∪ (K \ E)`, so `Hⁿ(M \ E) < ε/2 + ε/2 = ε`
  refine ⟨E, δ, hEK.trans hKM, hδ, ?_, fun x hx => (hKt x (hEK hx)).1,
    fun y hy ρ hρ hρδ => (hET y hy ρ hρ hρδ).1, fun x hx ρ hρ hρδ => (hET x hx ρ hρ hρδ).2.2⟩
  calc μHE[n] (M \ E)
      ≤ μHE[n] ((M \ K) ∪ (K \ E)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxK : x ∈ K
        · exact Or.inr ⟨hxK, hx.2⟩
        · exact Or.inl ⟨hx.1, hxK⟩
    _ ≤ μHE[n] (M \ K) + μHE[n] (K \ E) := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hMK hKE
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
/-- Finite `ε`-net of `n`-planes in the projection operator norm (Simon Ch. 3, proof of 1.6, the
choice of `π₁, …, π_N`): there are `n`-dimensional subspaces `T₁, …, T_N` of `ℝᴾ` such that every
`n`-dimensional `Q` has `‖p_Q − p_{T_j}‖ < ε` for some `j`.  The rank-`n` orthogonal projections
lie in the closed unit ball of the finite-dimensional space `L(ℝᴾ)`, so they are totally bounded
and finitely many of them are `ε`-dense among them; write those as `p_{T_j}`. -/
theorem Submission.cbrr_projection_net : ∀ (P n : ℕ) (ε : ℝ), 0 < ε → ∃ (N : ℕ) (T : Fin N → Submodule ℝ (Euclid P)), (∀ j, Module.finrank ℝ (T j) = n) ∧ ∀ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n → ∃ j, ‖Q.starProjection - (T j).starProjection‖ < ε := by
  intro P n ε hε
  -- the rank-`n` orthogonal projections lie in the closed unit ball, so they form a totally
  -- bounded set
  have hS : TotallyBounded ((fun Q : Submodule ℝ (Euclid P) => Q.starProjection) ''
      {Q | Module.finrank ℝ Q = n}) :=
    (isCompact_closedBall (0 : Euclid P →L[ℝ] Euclid P) 1).totallyBounded.subset (by
      rintro _ ⟨Q, -, rfl⟩
      simpa using Q.starProjection_norm_le)
  -- finitely many of them are `ε`-dense among them
  obtain ⟨t, htS, htfin, hcover⟩ := finite_approx_of_totallyBounded hS ε hε
  have ht : ∀ L ∈ t, ∃ T : Submodule ℝ (Euclid P), Module.finrank ℝ T = n ∧ T.starProjection = L :=
    fun L hL => htS hL
  choose! T hT using ht
  -- enumerate them
  obtain ⟨N, ⟨e⟩⟩ := @Finite.exists_equiv_fin t htfin.to_subtype
  refine ⟨N, fun j => T (e.symm j), fun j => (hT _ (e.symm j).2).1, fun Q hQ => ?_⟩
  obtain ⟨L, hL, hQL⟩ := mem_iUnion₂.1 (hcover ⟨Q, hQ, rfl⟩)
  refine ⟨e ⟨L, hL⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [(hT L hL).2, ← dist_eq_norm]
  exact hQL
/-- **Cone claim (10) in the proof of Simon Ch. 3, Theorem 1.6 "⇐"**, with the corrected constant
`b·16ⁿ < a`.  Suppose `μ(B̄_ρ(y)) ≥ aρⁿ` for `y ∈ E` and `μ(X(x) ∩ B_ρ(x)) ≤ bρⁿ` for `x ∈ E`,
`0 < ρ < δ`, where `X(x) = {z : 2|p_{Q(x)}(z − x)| < |z − x|}`.  If `x, y ∈ E`,
`‖p_{Q(x)} − p_T‖ < 1/16` and `|y − x| < δ/2`, then `|y − x| ≤ 4|p_T(y − x)|`.  Otherwise
`σ = |y − x|` has `B̄_{σ/8}(y) ⊆ X(x) ∩ B_{2σ}(x)`, so `a(σ/8)ⁿ ≤ b(2σ)ⁿ = b·16ⁿ(σ/8)ⁿ`. -/
theorem Submission.cbrr_cone_claim : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (E : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (T : Submodule ℝ (Euclid P)) (a b δ : ℝ), 0 < a → b * 16 ^ n < a → (∀ y ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (a * ρ ^ n) ≤ μ (closedBall y ρ)) → (∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n)) → ∀ x ∈ E, ∀ y ∈ E, ‖(Q x).starProjection - T.starProjection‖ < 1 / 16 → ‖y - x‖ < δ / 2 → ‖y - x‖ ≤ 4 * ‖T.starProjection (y - x)‖ := by
  intro P n μ E Q T a b δ ha hab hlow hup x hx y hy hQT hyx
  -- Step 1: suppose `4|p_T(y − x)| < σ := |y − x|`; then `0 < σ < δ/2`.
  refine not_lt.mp fun hcon => ?_
  set σ := ‖y - x‖
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hcon
  -- `|p_{Q(x)}(y − x)| ≤ |p_T(y − x)| + ‖p_{Q(x)} − p_T‖σ < σ/4 + σ/16`.
  have hQy : ‖(Q x).starProjection (y - x)‖ < σ / 4 + σ / 16 := by
    have hsplit : (Q x).starProjection (y - x) =
        T.starProjection (y - x) + ((Q x).starProjection - T.starProjection) (y - x) := by
      simp
    have hop : ‖((Q x).starProjection - T.starProjection) (y - x)‖ < σ / 16 := by
      calc ‖((Q x).starProjection - T.starProjection) (y - x)‖
          ≤ ‖(Q x).starProjection - T.starProjection‖ * σ := ContinuousLinearMap.le_opNorm _ _
        _ < 1 / 16 * σ := by gcongr
        _ = σ / 16 := by ring
    rw [hsplit]
    calc ‖T.starProjection (y - x) + ((Q x).starProjection - T.starProjection) (y - x)‖
        ≤ ‖T.starProjection (y - x)‖ + ‖((Q x).starProjection - T.starProjection) (y - x)‖ :=
          norm_add_le _ _
      _ < σ / 4 + σ / 16 := by linarith
  -- Step 2: `B̄_{σ/8}(y) ⊆ X(x) ∩ B_{2σ}(x)`.
  have hsub : closedBall y (σ / 8) ⊆
      {z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x (2 * σ) := by
    intro z hz
    have hzy : ‖z - y‖ ≤ σ / 8 := by rwa [mem_closedBall, dist_eq_norm] at hz
    have hdecomp : z - x = (y - x) + (z - y) := by abel
    -- `|p_{Q(x)}(z − x)| ≤ |p_{Q(x)}(y − x)| + |z − y| < 7σ/16`.
    have hQz : ‖(Q x).starProjection (z - x)‖ < 7 * σ / 16 := by
      calc ‖(Q x).starProjection (z - x)‖
          = ‖(Q x).starProjection (y - x) + (Q x).starProjection (z - y)‖ := by
            rw [hdecomp, map_add]
        _ ≤ ‖(Q x).starProjection (y - x)‖ + ‖(Q x).starProjection (z - y)‖ := norm_add_le _ _
        _ ≤ ‖(Q x).starProjection (y - x)‖ + ‖z - y‖ := by
            gcongr; exact (Q x).norm_starProjection_apply_le _
        _ < 7 * σ / 16 := by linarith
    -- `7σ/8 ≤ |z − x| ≤ 9σ/8 < 2σ`.
    have hlow' : σ - ‖z - y‖ ≤ ‖z - x‖ := by
      have := norm_sub_le (z - x) (z - y)
      have h' : (z - x) - (z - y) = y - x := by abel
      rw [h'] at this
      linarith
    have hup' : ‖z - x‖ ≤ σ + ‖z - y‖ := by
      rw [hdecomp]; exact norm_add_le _ _
    refine ⟨?_, ?_⟩
    · show 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖
      linarith
    · rw [mem_ball, dist_eq_norm]
      linarith
  -- Step 3: the density bounds at `y` (radius `σ/8`) and at `x` (radius `2σ`).
  have key : ENNReal.ofReal (a * (σ / 8) ^ n) ≤ ENNReal.ofReal (b * (2 * σ) ^ n) :=
    (hlow y hy (σ / 8) (by positivity) (by linarith)).trans
      ((measure_mono hsub).trans (hup x hx (2 * σ) (by positivity) (by linarith)))
  -- Step 4: `a(σ/8)ⁿ > 0` forces `a(σ/8)ⁿ ≤ b(2σ)ⁿ = b·16ⁿ(σ/8)ⁿ`, so `a ≤ b·16ⁿ`.
  have hs : 0 < (σ / 8) ^ n := by positivity
  have key' : a * (σ / 8) ^ n ≤ b * (2 * σ) ^ n :=
    (ENNReal.ofReal_le_ofReal_iff'.mp key).resolve_right (not_le.mpr (by positivity))
  have h16 : b * (2 * σ) ^ n = b * 16 ^ n * (σ / 8) ^ n := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    ring
  rw [h16] at key'
  have : a ≤ b * 16 ^ n := le_of_mul_le_mul_right key' hs
  linarith
/-- Lipschitz cover under the cone condition (Simon Ch. 3, proof of 1.6, with the extension
theorem Ch. 2, 1.2): if `T ⊆ ℝᴾ` is an `n`-dimensional subspace and `|y − x| ≤ C |p_T(y − x)|` for
all `x, y ∈ D`, then `D ⊆ F(ℝⁿ)` for a Lipschitz `F : ℝⁿ → ℝᴾ`.  With a linear isometry
`ι : T ≅ ℝⁿ` put `L = ι ∘ p_T`, so `|Lv − Lw| = |p_T(v − w)|`; `L` is injective on `D` and its
inverse on `L(D)` is `max C 0`-Lipschitz.  Extend this inverse (McShane, coordinatewise) to a
Lipschitz `F : ℝⁿ → ℝᴾ`; then `F(Lx) = x` for `x ∈ D`. -/
theorem Submission.cbrr_lipschitz_cover_of_cone_condition : ∀ (P n : ℕ) (T : Submodule ℝ (Euclid P)) (D : Set (Euclid P)) (C : ℝ), Module.finrank ℝ T = n → (∀ x ∈ D, ∀ y ∈ D, ‖y - x‖ ≤ C * ‖T.starProjection (y - x)‖) → ∃ F : Euclid n → Euclid P, (∃ K : NNReal, LipschitzWith K F) ∧ D ⊆ range F := by
  intro P n T D C hT hD
  -- Step 1: the cone condition with the constant `K = max C 0 ≥ 0`
  obtain ⟨K, hK⟩ : ∃ K : NNReal, ∀ x ∈ D, ∀ y ∈ D, ‖y - x‖ ≤ K * ‖T.starProjection (y - x)‖ :=
    ⟨C.toNNReal, fun x hx y hy => (hD x hx y hy).trans <| by
      rw [Real.coe_toNNReal']
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)⟩
  -- Step 2: the chart `L = ι ∘ p_T : ℝᴾ → ℝⁿ`, `ι : T ≅ ℝⁿ` a linear isometry
  let ι : T ≃ₗᵢ[ℝ] Euclid n := ((stdOrthonormalBasis ℝ T).reindex (finCongr hT)).repr
  let L : Euclid P → Euclid n := fun v => ι (T.orthogonalProjectionOnto v)
  have hL : ∀ x ∈ D, ∀ y ∈ D, ‖y - x‖ ≤ K * ‖L y - L x‖ := by
    intro x hx y hy
    have h : ‖L y - L x‖ = ‖T.starProjection (y - x)‖ := by
      simp only [L, ← map_sub, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply,
        Submodule.norm_coe]
    rw [h]
    exact hK x hx y hy
  -- Step 3: `L` is injective on `D`, with a `K`-Lipschitz inverse `g` on `L(D)`
  have hinj : InjOn L D := by
    intro x hx y hy hxy
    have h := hL x hx y hy
    rw [hxy, sub_self, norm_zero, mul_zero] at h
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp h)).symm
  let g : Euclid n → Euclid P := invFunOn L D
  have hgL : ∀ x ∈ D, g (L x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  have hg : LipschitzOnWith K g (L '' D) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hgL x hx, hgL y hy, dist_eq_norm, dist_eq_norm]
    exact hL y hy x hx
  -- Step 4: extend `g` to a Lipschitz `F : ℝⁿ → ℝᴾ` (McShane in each coordinate)
  obtain ⟨F, hF, hFg⟩ := hg.extend_finite_dimension
  -- Step 5: `F (L x) = g (L x) = x` for `x ∈ D`
  refine ⟨F, ⟨_, hF⟩, fun x hx => ⟨L x, ?_⟩⟩
  rw [← hFg (mem_image_of_mem L hx), hgL x hx]

/-- Rectifiability from uniform density bounds (Simon Ch. 3, proof of Theorem 1.6, steps
(6)–(10) and the final cover).  Take a `1/16`-net `T₁, …, T_N` of `n`-planes and a dense sequence
`(u_q)` in `ℝᴾ`, and cut `E` into the countably many pieces
`D_{j,q} = {x ∈ E : ‖p_{Q(x)} − p_{T_j}‖ < 1/16} ∩ B_{δ/4}(u_q)`.  Two points of `D_{j,q}` are
closer than `δ/2`, so the cone claim gives `|y − x| ≤ 4 |p_{T_j}(y − x)|` on `D_{j,q}`, and
`D_{j,q}` lies in a single Lipschitz image `F_{j,q}(ℝⁿ)`.  The pieces cover `E`, so `E` lies in a
countable union of Lipschitz images of `ℝⁿ`.  (Simon covers a compact `E` by finitely many balls
`B_{δ/4}(x₀)`; centres from a dense sequence make compactness unnecessary.) -/
theorem Submission.cbrr_rectifiable_of_uniform_density : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (E : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (a b δ : ℝ), 0 < a → b * 16 ^ n < a → 0 < δ → (∀ x ∈ E, Module.finrank ℝ (Q x) = n) → (∀ y ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (a * ρ ^ n) ≤ μ (closedBall y ρ)) → (∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n)) → CountablyRectifiable n E := by
  intro P n μ E Q a b δ ha hab hδ hQ hlow hup
  -- Step 1: a `1/16`-net `T₁, …, T_N` of `n`-planes
  obtain ⟨N, T, hT, hnet⟩ := Submission.cbrr_projection_net P n (1 / 16) (by norm_num)
  -- Step 2: a dense sequence `(u_q)` of centres
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Euclid P)
  -- Step 3: the pieces `D_{j,q}`
  let D : Fin N × ℕ → Set (Euclid P) := fun p =>
    {x | x ∈ E ∧ ‖(Q x).starProjection - (T p.1).starProjection‖ < 1 / 16} ∩ ball (u p.2) (δ / 4)
  -- Step 4: the cone condition on each piece, whose points are less than `δ / 2` apart
  have hcone : ∀ p, ∀ x ∈ D p, ∀ y ∈ D p, ‖y - x‖ ≤ 4 * ‖(T p.1).starProjection (y - x)‖ := by
    rintro ⟨j, q⟩ x ⟨⟨hxE, hxj⟩, hxq⟩ y ⟨⟨hyE, -⟩, hyq⟩
    refine Submission.cbrr_cone_claim P n μ E Q (T j) a b δ ha hab hlow hup x hxE y hyE hxj ?_
    rw [mem_ball] at hxq hyq
    calc ‖y - x‖ = dist y x := (dist_eq_norm y x).symm
      _ ≤ dist y (u q) + dist x (u q) := dist_triangle_right y x (u q)
      _ < δ / 4 + δ / 4 := add_lt_add hyq hxq
      _ = δ / 2 := by ring
  -- Step 5: each piece lies in one Lipschitz image `F_{j,q}(ℝⁿ)`
  choose F hF hDF using fun p : Fin N × ℕ =>
    Submission.cbrr_lipschitz_cover_of_cone_condition P n (T p.1) (D p) 4 (hT p.1) (hcone p)
  -- Step 6: the pieces cover `E`
  have hcover : E ⊆ ⋃₀ range fun p => range (F p) := by
    intro x hx
    obtain ⟨j, hj⟩ := hnet (Q x) (hQ x hx)
    obtain ⟨q, hq⟩ := hu.exists_dist_lt x (by positivity : (0 : ℝ) < δ / 4)
    exact mem_sUnion.2 ⟨range (F (j, q)), mem_range_self _, hDF (j, q) ⟨⟨hx, hj⟩, mem_ball.2 hq⟩⟩
  -- Step 7: the countably many Lipschitz images are countably `n`-rectifiable, hence so is `E`
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
    (countable_range fun p => range (F p)) ?_).mono hcover
  rintro _ ⟨p, rfl⟩
  obtain ⟨K, hK⟩ := hF p
  exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range hK

/-- **Approximate tangent spaces imply rectifiability** (Simon Ch. 3, Theorem 1.6 “⇐”).  Let
`Hⁿ(M) < ∞`, let `x ↦ p_{Q(x)}` be `Hⁿ⌞M`-a.e. strongly measurable and let `Q(x)` be the
approximate tangent space of `M` at `Hⁿ`-a.e. `x ∈ M`; then `M` is countably `n`-rectifiable.  For
`n = 0`, `M` is finite.  For `n > 0` fix `0 < a` with `a < ωₙ` and `b = a/2/16ⁿ`, so
`b·16ⁿ = a/2 < a`.  For every `m` the uniform lower density and cone bounds hold on some `E_m ⊆ M`
with `Hⁿ(M \ E_m) < 1/(m+1)`, so `E_m` is countably `n`-rectifiable.  Then `M \ ⋃ E_m` is
`Hⁿ`-null, and `M` lies in this null set together with countably many Lipschitz images. -/
theorem Submission.dtc_bc_tc_cl_rectifiable_of_approx_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), MeasurableSet M → μHE[n] M ≠ ∞ → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → CountablyRectifiable n M := by
  intro P n M Q hM hMfin hQm hQt
  -- Step 1: for `n = 0` the set `M` is finite
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Submission.cbrr_rectifiable_dim_zero P M hMfin
  -- Step 2: constants `0 < a` with `ofReal a < ωₙ` and `b = a/2/16ⁿ > 0`, so `b·16ⁿ = a/2 < a`
  obtain ⟨a, -, ha, haω⟩ := ENNReal.lt_iff_exists_real_btwn.mp
    (measure_ball_pos volume (0 : Euclid n) one_pos : 0 < unitBallVolume n)
  rw [ENNReal.ofReal_pos] at ha
  have hb : 0 < a / 2 / 16 ^ n := by positivity
  have hab : a / 2 / 16 ^ n * 16 ^ n < a := by
    rw [div_mul_cancel₀ _ (by positivity : (16 : ℝ) ^ n ≠ 0)]
    exact half_lt_self ha
  -- Step 3: for every `m`, the uniform density and cone bounds hold on some `E_m ⊆ M` with
  -- `Hⁿ(M \ E_m) < 1/(m+1)`, so `E_m` is countably `n`-rectifiable
  have hE : ∀ m : ℕ, ∃ E : Set (Euclid P), μHE[n] (M \ E) < ENNReal.ofReal (1 / ((m : ℝ) + 1)) ∧
      CountablyRectifiable n E := by
    intro m
    obtain ⟨E, δ, -, hδ, hME, hQE, hlow, hup⟩ := Submission.cbrr_uniform_density_on_large_set P n
      M Q hn hM hMfin hQm hQt a (a / 2 / 16 ^ n) (1 / ((m : ℝ) + 1)) haω hb Nat.one_div_pos_of_nat
    exact ⟨E, hME, Submission.cbrr_rectifiable_of_uniform_density P n (μHE[n].restrict M) E Q a
      (a / 2 / 16 ^ n) δ ha hab hδ hQE hlow hup⟩
  choose E hME hErect using hE
  -- Step 4: `M \ ⋃ E_m ⊆ M \ E_m` has `Hⁿ`-measure `< 1/(m+1)` for every `m`, so it is null
  have hlim := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  rw [ENNReal.ofReal_zero] at hlim
  have hnull : μHE[n] (M \ ⋃ m, E m) = 0 := nonpos_iff_eq_zero.mp <| ge_of_tendsto' hlim fun m =>
    (measure_mono (sdiff_subset_sdiff_right (subset_iUnion E m))).trans (hME m).le
  -- Step 5: `M ⊆ (M \ ⋃ E_m) ∪ ⋃ E_m`, a null set together with countably many Lipschitz images
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion E hErect
  refine ⟨M₀ ∪ (M \ ⋃ m, E m), measure_union_null hM₀ hnull, F, hF, fun x hx => ?_⟩
  by_cases hxE : x ∈ ⋃ m, E m
  · exact (hcover hxE).imp_left Or.inl
  · exact Or.inl (Or.inr ⟨hx, hxE⟩)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
