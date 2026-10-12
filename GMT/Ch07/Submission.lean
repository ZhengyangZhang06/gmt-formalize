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

/-- **Simon 7.5.11, covering step** (chapter-07.txt lines 1001–1004): a compact `μH[m]`-null set
`Z ⊆ ℝᴾ` is covered by finitely many open balls `B_{σⱼ}(pⱼ)` with `pⱼ ∈ Z`, `0 < σⱼ < δ` and
`Σⱼ σⱼ^m < ε`.  If `m = 0`, `μH[0]{x} = 1` forces `Z = ∅`.  If `m ≥ 1`, `hausdorffMeasure_apply`
gives a cover `(tₙ)` of mesh `≤ δ/2` with `Σ' diam(tₙ)^m < η = ε/2^{m+2}`.  Each `tₙ` meeting `Z`
lies in the ball of radius `σₙ = diam tₙ + δ'2^{-(n+1)}` (`δ' = min(δ/2, 1, η)`) about a point of
`tₙ ∩ Z`, and `σₙ^m ≤ 2^m(diam(tₙ)^m + δ'2^{-(n+1)})`; a finite subcover has `Σ σⱼ^m < ε/2`. -/
theorem Submission.regcomp_null_compact_ball_cover : ∀ (P m : ℕ) (Z : Set (Euclid P)), IsCompact Z → μH[(m : ℝ)] Z = 0 → ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ (J : ℕ) (p : Fin J → Euclid P) (σ : Fin J → ℝ), (∀ j, p j ∈ Z) ∧ (∀ j, 0 < σ j ∧ σ j < δ) ∧ Z ⊆ ⋃ j, ball (p j) (σ j) ∧ ∑ j, σ j ^ m < ε := by
  intro P m Z hZc hZ ε δ hε hδ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- Step 1: `m = 0`, so `μH[0]{x} = 1` forces `Z = ∅` and the empty family works
    have hZe : Z = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have h1 : μH[((0 : ℕ) : ℝ)] ({x} : Set (Euclid P)) ≤ μH[((0 : ℕ) : ℝ)] Z :=
        measure_mono (singleton_subset_iff.2 hx)
      rw [hZ, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton] at h1
      exact one_ne_zero (le_antisymm h1 bot_le)
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp [hZe],
      by simpa using hε⟩
  -- Step 2: the constants `η = ε/2^{m+2}` and `δ' = min(δ/2, 1, η)`
  set η : ℝ := ε / 2 ^ (m + 2) with hη_def
  have hη : 0 < η := by positivity
  set δ' : ℝ := min (δ / 2) (min 1 η)
  have hδ' : 0 < δ' := lt_min (by positivity) (lt_min one_pos hη)
  have hδ'δ : δ' ≤ δ / 2 := min_le_left _ _
  have hδ'1 : δ' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'η : δ' ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  -- Step 3: a cover `(tₙ)` with `diam tₙ ≤ δ/2` and `Σ' [tₙ ≠ ∅] diam(tₙ)^m < η`, from the
  -- infimum at scale `r = δ/2` in `hausdorffMeasure_apply`, which is `≤ μH[m](Z) = 0`
  have hr : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have hinf : (⨅ (t : ℕ → Set (Euclid P)) (_ : Z ⊆ ⋃ n, t n)
      (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal (δ / 2)),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ)) < ENNReal.ofReal η := by
    have hle := le_iSup₂_of_le (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
      ⨅ (t : ℕ → Set (Euclid P)) (_ : Z ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ)) (ENNReal.ofReal (δ / 2)) hr le_rfl
    rw [← Measure.hausdorffMeasure_apply, hZ] at hle
    exact hle.trans_lt (ENNReal.ofReal_pos.2 hη)
  simp only [iInf_lt_iff] at hinf
  obtain ⟨t, hZt, htd, hsum⟩ := hinf
  -- `dₙ = diam tₙ ∈ [0, δ/2]` as a real number
  have hd_fin : ∀ n, ediam (t n) ≠ ∞ := fun n => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htd n)
  set d : ℕ → ℝ := fun n => (ediam (t n)).toReal
  have hd_nonneg : ∀ n, 0 ≤ d n := fun n => ENNReal.toReal_nonneg
  have hd_le : ∀ n, d n ≤ δ / 2 := fun n => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htd n)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- Step 4: radii `σₙ = dₙ + τₙ`, `τₙ = δ'2^{-(n+1)}`, centred at `qᵢ ∈ tᵢ ∩ Z` for `i ∈ I`
  set τ : ℕ → ℝ := fun n => δ' / 2 * (1 / 2) ^ n
  have hτ_pos : ∀ n, 0 < τ n := fun n => by positivity
  have hτ_le : ∀ n, τ n ≤ δ' / 2 := fun n => by
    have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc τ n = δ' / 2 * (1 / 2) ^ n := rfl
      _ ≤ δ' / 2 * 1 := by gcongr
      _ = δ' / 2 := mul_one _
  set σ : ℕ → ℝ := fun n => d n + τ n
  -- (a) `0 < σₙ ≤ δ/2 + δ/4 < δ`
  have hσ_pos : ∀ n, 0 < σ n := fun n => add_pos_of_nonneg_of_pos (hd_nonneg n) (hτ_pos n)
  have hσ_lt : ∀ n, σ n < δ := fun n => by
    have := hd_le n; have := hτ_le n; simp only [σ]; linarith
  let I := {n : ℕ // (t n ∩ Z).Nonempty}
  choose q hq using fun i : I => i.2
  -- (b), (c) `z ∈ Z` lies in some `tₙ`, so `n ∈ I` and `dist(z, qₙ) ≤ dₙ < σₙ`
  have hcov : Z ⊆ ⋃ i : I, ball (q i) (σ i) := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hZt hz)
    refine mem_iUnion.2 ⟨⟨n, z, hn, hz⟩, ?_⟩
    rw [mem_ball]
    have h1 : edist z (q ⟨n, z, hn, hz⟩) ≤ ediam (t n) :=
      edist_le_ediam_of_mem hn (hq ⟨n, z, hn, hz⟩).1
    have h2 : dist z (q ⟨n, z, hn, hz⟩) ≤ d n := by
      rw [dist_edist]; exact ENNReal.toReal_mono (hd_fin n) h1
    have := hτ_pos n
    simp only [σ]
    linarith
  -- (d) `σₙ ≤ 2 max(dₙ, τₙ)` and `τₙ^m ≤ τₙ` (`τₙ ≤ 1`, `m ≥ 1`), so `σₙ^m ≤ 2^m (dₙ^m + τₙ)`
  have hσm : ∀ n, σ n ^ m ≤ 2 ^ m * (d n ^ m + τ n) := fun n => by
    have hτ1 : τ n ≤ 1 := by have := hτ_le n; linarith
    have hτm : τ n ^ m ≤ τ n := pow_le_of_le_one (hτ_pos n).le hτ1 (by omega)
    have hmax : σ n ≤ 2 * max (d n) (τ n) := by
      have := le_max_left (d n) (τ n); have := le_max_right (d n) (τ n); simp only [σ]; linarith
    have hmaxm : max (d n) (τ n) ^ m ≤ d n ^ m + τ n ^ m := by
      rcases le_total (d n) (τ n) with h | h
      · rw [max_eq_right h]; have := pow_nonneg (hd_nonneg n) m; linarith
      · rw [max_eq_left h]; have := pow_nonneg (hτ_pos n).le m; linarith
    calc σ n ^ m ≤ (2 * max (d n) (τ n)) ^ m := pow_le_pow_left₀ (hσ_pos n).le hmax m
      _ = 2 ^ m * max (d n) (τ n) ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (d n ^ m + τ n) := by gcongr; linarith
  -- Step 5: a finite subcover `S ⊆ I` of the compact set `Z`
  obtain ⟨S, hS⟩ := hZc.elim_finite_subcover (fun i : I => ball (q i) (σ i))
    (fun _ => isOpen_ball) hcov
  -- `Σ_{i ∈ S} dᵢ^m ≤ Σ' [tₙ ≠ ∅] diam(tₙ)^m < η`, as `tᵢ ≠ ∅` for `i ∈ I`
  have hsumd : ∑ i ∈ S, d i ^ m < η := by
    have h1 : ∑ i ∈ S, ENNReal.ofReal (d i ^ m) ≤
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ) := by
      calc ∑ i ∈ S, ENNReal.ofReal (d i ^ m)
          = ∑ n ∈ S.map (Embedding.subtype _), ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ) := by
            rw [Finset.sum_map]
            refine Finset.sum_congr rfl fun i _ => ?_
            have hne : (t i).Nonempty := i.2.mono inter_subset_left
            simp only [Embedding.subtype_apply]
            rw [iSup_pos hne, ENNReal.rpow_natCast, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (hd_fin i)]
        _ ≤ _ := ENNReal.sum_le_tsum _
    have h2 : ENNReal.ofReal (∑ i ∈ S, d i ^ m) < ENNReal.ofReal η := by
      rw [ENNReal.ofReal_sum_of_nonneg (s := S) (f := fun i : I => d i ^ m)
        (fun i _ => pow_nonneg (hd_nonneg (i : ℕ)) m)]
      exact h1.trans_lt hsum
    exact (ENNReal.ofReal_lt_ofReal_iff hη).1 h2
  -- `Σ_{i ∈ S} τᵢ ≤ (δ'/2) Σₙ 2^{-n} = δ' ≤ η`
  have hsumτ : ∑ i ∈ S, τ i ≤ δ' := by
    have hg : ∑ i ∈ S, (1 / 2 : ℝ) ^ (i : ℕ) ≤ 2 := by
      calc ∑ i ∈ S, (1 / 2 : ℝ) ^ (i : ℕ) = ∑ n ∈ S.map (Embedding.subtype _), (1 / 2 : ℝ) ^ n := by
            rw [Finset.sum_map]; rfl
        _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
            Summable.sum_le_tsum _ (fun _ _ => by positivity) summable_geometric_two
        _ = 2 := tsum_geometric_two
    calc ∑ i ∈ S, τ i = δ' / 2 * ∑ i ∈ S, (1 / 2 : ℝ) ^ (i : ℕ) := by rw [Finset.mul_sum]
      _ ≤ δ' / 2 * 2 := by gcongr
      _ = δ' := by ring
  -- `Σ_{i ∈ S} σᵢ^m ≤ 2^m (Σ dᵢ^m + Σ τᵢ) < 2^m (η + η) = ε/2 < ε`
  have hsumσ : ∑ i ∈ S, σ i ^ m < ε := by
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    calc ∑ i ∈ S, σ i ^ m ≤ ∑ i ∈ S, 2 ^ m * (d i ^ m + τ i) :=
          Finset.sum_le_sum fun i _ => hσm i
      _ = 2 ^ m * (∑ i ∈ S, d i ^ m + ∑ i ∈ S, τ i) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ < 2 ^ m * (η + η) := by
          have hlt : ∑ i ∈ S, d i ^ m + ∑ i ∈ S, τ i < η + η := by linarith
          exact mul_lt_mul_of_pos_left hlt h2m
      _ = ε / 2 := by rw [hη_def, pow_add]; field_simp; ring
      _ < ε := by linarith
  -- Step 6: enumerate `S` as `Fin J`, `J = |S|`
  let e := S.equivFin
  refine ⟨S.card, fun j => q (e.symm j), fun j => σ (e.symm j), fun j => (hq _).2,
    fun j => ⟨hσ_pos _, hσ_lt _⟩, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hiS, hzi⟩ := mem_iUnion₂.1 (hS hz)
    refine mem_iUnion.2 ⟨e ⟨i, hiS⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hzi
  · calc ∑ j, σ (e.symm j : I) ^ m = ∑ i : S, σ (i : I) ^ m :=
          Equiv.sum_comp e.symm (fun i : S => σ (i : I) ^ m)
      _ = ∑ i ∈ S, σ i ^ m := Finset.sum_coe_sort S (fun i : I => σ i ^ m)
      _ < ε := hsumσ
/-- The cut-off `ζ` in the proof of **Simon 7.5.11** (chapter-07.txt lines 1006–1011), with the
correction `ζ = ∏ⱼ (1 - φⱼ)`; the book prints `ζ = ∏ φⱼ`.  Here `φⱼ(x) = φ₀(σⱼ⁻¹ (x - pⱼ))`, where
the smooth bump `φ₀` equals `1` on `B̄(0, 1)` and has support `B(0, 3/2)`, and `c₀` is a Lipschitz
constant of `φ₀`.  Then `1 - ζ ≤ Σⱼ φⱼ ≤ Σⱼ 1_{B(pⱼ, 2σⱼ)}` and
`‖Dζ‖ ≤ Σⱼ ‖Dφⱼ‖ ≤ Σⱼ (c₀/σⱼ) 1_{B(pⱼ, 2σⱼ)}`. -/
theorem Submission.regcomp_smooth_cutoff_product : ∀ (P : ℕ), ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (J : ℕ) (p : Fin J → Euclid P) (σ : Fin J → ℝ), (∀ j, 0 < σ j) → ∃ ζ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ j, ∀ x ∈ ball (p j) (σ j), ζ x = 0) ∧ (∀ x, 1 - ζ x ≤ ∑ j, (ball (p j) (2 * σ j)).indicator (fun _ => (1 : ℝ)) x) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ ∑ j, (ball (p j) (2 * σ j)).indicator (fun _ => c₀ / σ j) x := by
  intro P
  -- Step 1: the model bump `φ₀` (`rIn = 1`, `rOut = 3/2`) and a Lipschitz constant `c₀ = L`
  let φ₀ : ContDiffBump (0 : Euclid P) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  have hφ₀s : ContDiff ℝ (⊤ : ℕ∞) φ₀ := φ₀.contDiff
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ₀.hasCompactSupport hφ₀s
    (by simp)
  refine ⟨L, L.coe_nonneg, fun J p σ hσ => ?_⟩
  -- Step 2: the rescaled bumps `φⱼ(x) = φ₀(σⱼ⁻¹ (x - pⱼ))`
  have hbump : ∀ j, ∃ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      (∀ x ∈ ball (p j) (σ j), φ x = 1) ∧
      (∀ x, φ x ≤ (ball (p j) (2 * σ j)).indicator (fun _ => (1 : ℝ)) x) ∧
      ∀ x, ‖fderiv ℝ φ x‖ ≤ (ball (p j) (2 * σ j)).indicator (fun _ => (L : ℝ) / σ j) x := by
    intro j
    have hs := hσ j
    -- (c) `φⱼ(y) = 0` once `dist(y, pⱼ) > (3/2) σⱼ`
    have hφ0 : ∀ y : Euclid P, 3 / 2 * σ j < dist y (p j) → φ₀ ((σ j)⁻¹ • (y - p j)) = 0 := by
      intro y hy
      apply notMem_support.1
      rw [φ₀.support_eq, mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hs.le), not_lt]
      change 3 / 2 ≤ (σ j)⁻¹ * ‖y - p j‖
      rw [← dist_eq_norm, le_inv_mul_iff₀ hs]
      linarith
    -- (d) `φⱼ` is `(c₀/σⱼ)`-Lipschitz
    have hlip : LipschitzWith (L * (Real.toNNReal (σ j))⁻¹)
        fun y : Euclid P => φ₀ ((σ j)⁻¹ • (y - p j)) := by
      refine hL.comp (LipschitzWith.of_dist_le_mul fun y z => ?_)
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hs.le), NNReal.coe_inv, Real.coe_toNNReal _ hs.le]
    refine ⟨fun x => φ₀ ((σ j)⁻¹ • (x - p j)),
      hφ₀s.comp ((contDiff_id.sub contDiff_const).const_smul _),
      fun x => ⟨φ₀.nonneg, φ₀.le_one⟩, fun x hx => ?_, fun x => ?_, fun x => ?_⟩
    · -- (b) `φⱼ = 1` on `B(pⱼ, σⱼ)`
      apply φ₀.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      change (σ j)⁻¹ * ‖x - p j‖ ≤ 1
      rw [mem_ball, dist_eq_norm] at hx
      rw [inv_mul_le_iff₀ hs]
      linarith
    · -- `φⱼ ≤ 1_{B(pⱼ, 2σⱼ)}`
      by_cases hx : x ∈ ball (p j) (2 * σ j)
      · rw [indicator_of_mem hx]
        exact φ₀.le_one
      · rw [indicator_of_notMem hx]
        rw [mem_ball, not_lt] at hx
        exact (hφ0 x (by linarith)).le
    · -- `‖Dφⱼ‖ ≤ (c₀/σⱼ) 1_{B(pⱼ, 2σⱼ)}`: `φⱼ` vanishes near every `x ∉ B(pⱼ, 2σⱼ)`
      by_cases hx : x ∈ ball (p j) (2 * σ j)
      · rw [indicator_of_mem hx]
        refine (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq ?_
        rw [NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hs.le, div_eq_mul_inv]
      · rw [indicator_of_notMem hx]
        rw [mem_ball, not_lt] at hx
        have hev : (fun y : Euclid P => φ₀ ((σ j)⁻¹ • (y - p j))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          have hopen : IsOpen {y : Euclid P | 3 / 2 * σ j < dist y (p j)} :=
            isOpen_lt continuous_const (continuous_id.dist continuous_const)
          filter_upwards [hopen.mem_nhds (show 3 / 2 * σ j < dist x (p j) by linarith)]
            with y hy
          exact hφ0 y hy
        rw [hev.fderiv_eq, fderiv_const_apply, norm_zero]
  choose φ hφs hφ01 hφ1 hφind hφd using hbump
  -- the factors `1 - φⱼ` are smooth with values in `[0, 1]`
  have hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun y => 1 - φ j y) := fun j => contDiff_const.sub (hφs j)
  have hf01 : ∀ j x, 0 ≤ 1 - φ j x ∧ 1 - φ j x ≤ 1 := fun j x =>
    ⟨sub_nonneg.2 (hφ01 j x).2, sub_le_self _ (hφ01 j x).1⟩
  -- Step 3: `ζ = ∏ⱼ (1 - φⱼ)`
  refine ⟨fun x => ∏ j, (1 - φ j x), contDiff_prod fun j _ => hfs j,
    fun x => ⟨Finset.prod_nonneg fun j _ => (hf01 j x).1,
      Finset.prod_le_one₀ (fun j _ => (hf01 j x).1) fun j _ => (hf01 j x).2⟩,
    fun j x hx => Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hφ1 j x hx, sub_self]),
    fun x => ?_, fun x => ?_⟩
  · -- Step 4: `1 - ∏ (1 - aᵢ) ≤ Σ aᵢ` for `aᵢ ∈ [0, 1]`, by induction over finite index sets
    have key : ∀ s : Finset (Fin J), 1 - ∏ j ∈ s, (1 - φ j x) ≤ ∑ j ∈ s, φ j x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert k s hk ih =>
        rw [Finset.prod_insert hk, Finset.sum_insert hk]
        have hP0 : 0 ≤ ∏ j ∈ s, (1 - φ j x) := Finset.prod_nonneg fun j _ => (hf01 j x).1
        have hP1 : ∏ j ∈ s, (1 - φ j x) ≤ 1 :=
          Finset.prod_le_one₀ (fun j _ => (hf01 j x).1) fun j _ => (hf01 j x).2
        nlinarith [(hφ01 k x).1, (hφ01 k x).2]
    exact (key Finset.univ).trans (Finset.sum_le_sum fun j _ => hφind j x)
  · -- Step 5: product rule, `‖Dζ‖ ≤ Σⱼ ‖D(1 - φⱼ)‖ = Σⱼ ‖Dφⱼ‖`
    rw [fderiv_finsetProd fun j _ => ((hfs j).differentiable (by simp)) x]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, fderiv_const_sub, norm_neg]
    have h1 : ‖∏ i ∈ Finset.univ.erase j, (1 - φ i x)‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => (hf01 i x).1)]
      exact Finset.prod_le_one₀ (fun i _ => (hf01 i x).1) fun i _ => (hf01 i x).2
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hφd j x)
/-- **Simon 7.5.11, identity (2)** (chapter-07.txt lines 996–999), localised by a partition of
unity.  Let `∂T = 0`, `T₁(θ) = ∫_{M₁} ⟨θ, ξ⟩ dH^{m+1}`, and let every `z ∈ M₁` have an open
`G ∋ z` on which `T₁ = c T`.  If `closure M₁ ∩ spt η ⊆ M₁`, then `∂T₁(η) = 0`: finitely many such
`G` cover the compact set `closure M₁ ∩ spt η`; for a smooth partition of unity `(ψᵢ)` on a
neighbourhood of it subordinate to them, `(1 - Σ ψᵢ) η` vanishes near `M₁`, so
`T₁(d((1 - Σ ψᵢ) η)) = 0`, while `T₁(d(ψᵢ η)) = cᵢ ∂T(ψᵢ η) = 0`. -/
theorem Submission.regcomp_localized_boundary_zero : ∀ (P m : ℕ) (U M₁ : Set (Euclid P)) (T T₁ : GeometricCurrentOn U (m + 1)) (ξ : Euclid P → MultiVector P (m + 1)), T.boundary = 0 → (∀ ω : TestFormOn U (m + 1), T₁ ω = ∫ x in M₁, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) → (∀ z ∈ M₁, ∃ G : Set (Euclid P), IsOpen G ∧ z ∈ G ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ G → T₁ ω = c * T ω) → ∀ η : TestFormOn U m, closure M₁ ∩ tsupport (η : DifferentialForm (Euclid P) m) ⊆ M₁ → T₁.boundary η = 0 := by
  intro P m U M₁ T T₁ ξ h1 h2 h4 η hη
  classical
  -- Step 1: `K₁ = closure M₁ ∩ tsupport η` is closed in the compact `tsupport η`.
  have hηc : IsCompact (tsupport (η : DifferentialForm (Euclid P) m)) := η.property.1.2
  have hK₁ : IsCompact (closure M₁ ∩ tsupport (η : DifferentialForm (Euclid P) m)) :=
    IsCompact.inter_left hηc isClosed_closure
  -- Step 2: finitely many of the (h4) neighbourhoods `G z`, `z ∈ K₁ ⊆ M₁`, cover `K₁`.
  choose! G hGo hzG c hc using h4
  obtain ⟨t, ht⟩ := hK₁.elim_finite_subcover
    (fun z : (closure M₁ ∩ tsupport (η : DifferentialForm (Euclid P) m) : Set (Euclid P)) =>
      G (z : Euclid P))
    (fun z => hGo z (hη z.2))
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hzG x (hη hx)⟩)
  have hWo : IsOpen (⋃ i ∈ t, G
      ((i : (closure M₁ ∩ tsupport (η : DifferentialForm (Euclid P) m) : Set (Euclid P))) :
        Euclid P)) :=
    isOpen_biUnion fun z _ => hGo z (hη z.2)
  -- Step 3: an open `O₁ ⊇ K₁` with `closure O₁ ⊆ ⋃ G`, and a smooth partition of unity
  -- `(ψ_i)` on `closure O₁` subordinate to the `G`; `χ = Σ ψ_i` is `1` on `O₁`.
  obtain ⟨O₁, hO₁o, hKO, hOW, -⟩ := exists_open_between_and_isCompact_closure hK₁ hWo ht
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := modelWithCornersSelf ℝ (Euclid P)) (M := Euclid P) (isClosed_closure (s := O₁))
    (fun i : t => G ((i : _) : Euclid P)) (fun i => hGo _ (hη i.1.2)) (by
      intro x hx
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hOW hx)
      exact mem_iUnion.2 ⟨⟨z, hz⟩, hxz⟩)
  have hψs : ∀ i : t, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ i) := fun i =>
    contMDiff_iff_contDiff.1 (ψ i).contMDiff
  obtain ⟨χ, hχ⟩ : ∃ χ : Euclid P → ℝ, χ = fun x => ∑ i : t, ψ i x := ⟨_, rfl⟩
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
    rw [hχ]; exact ContDiff.sum fun i _ => hψs i
  have hχ1 : ∀ x ∈ O₁, χ x = 1 := fun x hx => by
    rw [hχ]
    show ∑ i : t, ψ i x = 1
    rw [← finsum_eq_sum_of_fintype]
    exact ψ.sum_eq_one (subset_closure hx)
  -- Step 4: `η = (1 - χ) η + Σ ψ_i η`, each summand a test form in `U`.
  have hmk : ∀ f : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      ∃ θ : TestFormOn U m, (θ : DifferentialForm (Euclid P) m) =
        fun x => f x • (η : DifferentialForm (Euclid P) m) x := by
    intro f hf
    obtain ⟨⟨hs, hcpt⟩, hU⟩ := η.property
    have hs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (η : DifferentialForm (Euclid P) m) := hs
    have hcpt' : IsCompact (tsupport (η : DifferentialForm (Euclid P) m)) := hcpt
    have hsub : tsupport (fun x => f x • (η : DifferentialForm (Euclid P) m) x) ⊆
        tsupport (η : DifferentialForm (Euclid P) m) := tsupport_smul_subset_right _ _
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => f x • (η : DifferentialForm (Euclid P) m) x) := hf.smul hs'
    have hcc : IsCompact (tsupport (fun x => f x • (η : DifferentialForm (Euclid P) m) x)) :=
      IsCompact.of_isClosed_subset hcpt' (isClosed_tsupport _) hsub
    exact ⟨⟨fun x => f x • (η : DifferentialForm (Euclid P) m) x,
      ⟨⟨hsm, hcc⟩, hsub.trans hU⟩⟩, rfl⟩
  have h1χ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => 1 - χ x) := contDiff_const.sub hχs
  obtain ⟨η₀, hη₀⟩ := hmk (fun x => 1 - χ x) h1χ
  choose ηi hηi using fun i : t => hmk (ψ i) (hψs i)
  have hη₀x : ∀ x, (η₀ : DifferentialForm (Euclid P) m) x =
      (1 - χ x) • (η : DifferentialForm (Euclid P) m) x := fun x => congrFun hη₀ x
  have hηix : ∀ i x, (ηi i : DifferentialForm (Euclid P) m) x =
      ψ i x • (η : DifferentialForm (Euclid P) m) x := fun i x => congrFun (hηi i) x
  have hdecomp : η = η₀ + ∑ i : t, ηi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply, hη₀x]
    simp only [hηix]
    rw [← Finset.sum_smul, ← add_smul]
    have hsum : 1 - χ x + ∑ i : t, ψ i x = 1 := by rw [hχ]; ring
    rw [hsum, one_smul]
  -- Step 5: `(1 - χ) η` vanishes near every point of `M₁`, so `∂T₁ ((1 - χ) η) = 0` by (h2).
  have h0 : T₁.boundary η₀ = 0 := by
    rw [GeometricCurrentOn.boundary_apply, h2]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hx0 : x ∉ tsupport (η₀ : DifferentialForm (Euclid P) m) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      by_cases hxη : x ∈ tsupport (η : DifferentialForm (Euclid P) m)
      · have hxO : x ∈ O₁ := hKO ⟨subset_closure hx, hxη⟩
        filter_upwards [hO₁o.mem_nhds hxO] with y hy
        rw [hη₀x, hχ1 y hy, sub_self, zero_smul, Pi.zero_apply]
      · filter_upwards [(notMem_tsupport_iff_eventuallyEq).1 hxη] with y hy
        rw [hη₀x, hy, Pi.zero_apply, smul_zero]
    have hdx : x ∉ tsupport (exteriorDerivative (η₀ : DifferentialForm (Euclid P) m)) :=
      fun h => hx0 (tsupport_exteriorDerivative_subset _ h)
    change ξ x (exteriorDerivative (η₀ : DifferentialForm (Euclid P) m) x) = 0
    rw [image_eq_zero_of_notMem_tsupport hdx, map_zero]
  -- Step 6: `tsupport d(ψ_i η) ⊆ G z_i`, so `∂T₁ (ψ_i η) = c z_i * ∂T (ψ_i η) = 0` by (h4), (h1).
  have hi : ∀ i : t, T₁.boundary (ηi i) = 0 := by
    intro i
    have hs1 : tsupport (ηi i : DifferentialForm (Euclid P) m) ⊆ tsupport (ψ i) := by
      rw [hηi i]
      exact tsupport_smul_subset_left _ _
    have hsupp : tsupport ((exteriorDerivativeTestOn U m (ηi i) : TestFormOn U (m + 1)) :
        DifferentialForm (Euclid P) (m + 1)) ⊆ G ((i : _) : Euclid P) := by
      change tsupport (exteriorDerivative (ηi i : DifferentialForm (Euclid P) m)) ⊆ _
      exact (tsupport_exteriorDerivative_subset _).trans (hs1.trans (hψ i))
    rw [GeometricCurrentOn.boundary_apply, hc _ (hη i.1.2) _ hsupp,
      ← GeometricCurrentOn.boundary_apply, h1, GeometricCurrentOn.zero_apply, mul_zero]
  -- Step 7: linearity of `∂T₁`.
  have hlin : T₁.boundary η = T₁.boundary η₀ + ∑ i : t, T₁.boundary (ηi i) := by
    conv_lhs => rw [hdecomp]
    rw [map_add, map_sum]
  rw [hlin, h0, Finset.sum_eq_zero fun i _ => hi i, add_zero]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
