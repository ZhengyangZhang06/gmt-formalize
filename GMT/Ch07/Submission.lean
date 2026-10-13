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
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩

/-- **Splitting the multiplicity of an integer multiplicity triple** (Simon 7.5.11, proof).  Let
`R = (C, θ, ξ)`, `R₁ = (C₁, θ₁, ξ)` and `R₂ = (C₂, θ₂, ξ)` be triples in `U` with `C₁, C₂ ⊆ C`
and `θ = 1_{C₁} θ₁ + 1_{C₂} θ₂` on `C`.  Then the weights add, `θ Hⁿ⌞C = θ₁ Hⁿ⌞C₁ + θ₂ Hⁿ⌞C₂`,
and so do the actions, `τ(C, θ, ξ)(ω) = τ(C₁, θ₁, ξ)(ω) + τ(C₂, θ₂, ξ)(ω)` for `ω ∈ 𝒟ⁿ(U)`: the
densities agree `Hⁿ⌞C`-a.e., and the integrands of `R₁`, `R₂` are integrable
(`Submission.regcomp_rim_action_integrable`), so the integral over `C` splits. -/
theorem Submission.regcomp_rim_imrep_split : ∀ (P n : ℕ) (U : Set (Euclid P)) (R R₁ R₂ : IMRep U n), R₁.carrier ⊆ R.carrier → R₂.carrier ⊆ R.carrier → R₁.orient = R.orient → R₂.orient = R.orient → (∀ x ∈ R.carrier, R.mult x = R₁.carrier.indicator R₁.mult x + R₂.carrier.indicator R₂.mult x) → R.measure = R₁.measure + R₂.measure ∧ ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = R₁.action (ω : DifferentialForm (Euclid P) n) + R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R R₁ R₂ h₁ h₂ ho₁ ho₂ hθ
  have hC₁ : MeasurableSet R₁.carrier := R₁.measurableSet_carrier
  have hC₂ : MeasurableSet R₂.carrier := R₂.measurableSet_carrier
  refine ⟨?_, fun ω => ?_⟩
  · /- Measures: `θ = 1_{C₁} θ₁ + 1_{C₂} θ₂` `Hⁿ⌞C`-a.e. as `ℝ≥0∞`-valued densities, so
    `θ Hⁿ⌞C = θ₁ Hⁿ⌞(C₁ ∩ C) + θ₂ Hⁿ⌞(C₂ ∩ C)`, and `Cᵢ ∩ C = Cᵢ`. -/
    have hae : (fun x => (R.mult x : ℝ≥0∞)) =ᵐ[μHE[n].restrict R.carrier]
        R₁.carrier.indicator (fun x => (R₁.mult x : ℝ≥0∞)) +
          R₂.carrier.indicator (fun x => (R₂.mult x : ℝ≥0∞)) := by
      filter_upwards [ae_restrict_mem R.measurableSet_carrier] with x hx
      rw [hθ x hx, Nat.cast_add, Pi.add_apply]
      congr 1
      · by_cases h : x ∈ R₁.carrier <;> simp [h]
      · by_cases h : x ∈ R₂.carrier <;> simp [h]
    have hm₁ : Measurable (R₁.carrier.indicator fun x => (R₁.mult x : ℝ≥0∞)) :=
      (measurable_from_nat.comp R₁.measurable_mult).indicator hC₁
    unfold IMRep.measure
    rw [withDensity_congr_ae hae, withDensity_add_left hm₁, withDensity_indicator hC₁,
      withDensity_indicator hC₂, Measure.restrict_restrict hC₁, Measure.restrict_restrict hC₂,
      inter_eq_left.mpr h₁, inter_eq_left.mpr h₂]
  · /- Actions: with `Fᵢ = θᵢ ⟨ω, ξ⟩`, `θ ⟨ω, ξ⟩ = 1_{C₁} F₁ + 1_{C₂} F₂` on `C`, and each
    `1_{Cᵢ} Fᵢ` is `Hⁿ⌞C`-integrable, so `∫_C θ ⟨ω, ξ⟩ = ∫_{C ∩ C₁} F₁ + ∫_{C ∩ C₂} F₂`. -/
    set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
    set F₁ : Euclid P → ℝ := fun x => (R₁.mult x : ℝ) * R₁.orient x (f x)
    set F₂ : Euclid P → ℝ := fun x => (R₂.mult x : ℝ) * R₂.orient x (f x)
    have hF₁ : Integrable (R₁.carrier.indicator F₁) (μHE[n].restrict R.carrier) :=
      (IntegrableOn.integrable_indicator (Submission.regcomp_rim_action_integrable P n U R₁ ω)
        hC₁).restrict
    have hF₂ : Integrable (R₂.carrier.indicator F₂) (μHE[n].restrict R.carrier) :=
      (IntegrableOn.integrable_indicator (Submission.regcomp_rim_action_integrable P n U R₂ ω)
        hC₂).restrict
    have hpt : EqOn (fun x => (R.mult x : ℝ) * R.orient x (f x))
        (fun x => R₁.carrier.indicator F₁ x + R₂.carrier.indicator F₂ x) R.carrier := by
      intro x hx
      simp only [F₁, F₂, hθ x hx, Nat.cast_add, ho₁, ho₂]
      by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier <;>
        simp [hx₁, hx₂, add_mul]
    calc R.action f
        = ∫ x in R.carrier, (R₁.carrier.indicator F₁ x + R₂.carrier.indicator F₂ x) ∂μHE[n] :=
          setIntegral_congr_fun R.measurableSet_carrier hpt
      _ = ∫ x in R.carrier, R₁.carrier.indicator F₁ x ∂μHE[n] +
            ∫ x in R.carrier, R₂.carrier.indicator F₂ x ∂μHE[n] := integral_add hF₁ hF₂
      _ = ∫ x in R.carrier ∩ R₁.carrier, F₁ x ∂μHE[n] +
            ∫ x in R.carrier ∩ R₂.carrier, F₂ x ∂μHE[n] := by
          rw [setIntegral_indicator hC₁, setIntegral_indicator hC₂]
      _ = R₁.action f + R₂.action f := by
          rw [inter_eq_right.mpr h₁, inter_eq_right.mpr h₂]
          rfl
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in `U`** (Simon
Ch. 1, Remark 3.7(2); chapter-01.txt lines 705–711).  If `U ⊆ ℝᴾ` is open and `S` is Borel with
`Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ U ∖ S`,
`Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B_{r_y}(y)` with
`B̄_{r_y}(y) ⊆ U` cover `U` (Lindelöf); the finite-measure version applies to each piece
`S ∩ B_{r_y}(y)`, and near `x ∈ B_{r_y}(y)` the piece agrees with `S`. -/
theorem Submission.regcomp_atl_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U`.
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2 and 3, the finite-measure theorem on each piece `S ∩ B(y, r y)`, simultaneously
  -- for the countably many `y ∈ D`.
  have hpiece : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ ball y (r y) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    apply Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball)
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right S ball_subset_closedBall))
  -- Step 4, localization: for small `ρ`, `B̄(x, ρ) ⊆ B(y, r y)`, so the piece agrees with `S`.
  filter_upwards [hpiece] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov hxU)
  obtain ⟨ε, hε, hεy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεy)]
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]

/-- Locality of approximate tangent spaces (Simon 3.1.5(2), from the proof of 3.1.6 "⇒"): if
`A ⊆ B` are Borel, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B \ A) ∩ B̄_ρ(x))/ρⁿ → 0` as `ρ ↓ 0`, then
`B` and `A` have the same approximate tangent spaces at `x`.  For `f ∈ C_c(ℝᴾ)` with `|f| ≤ C`
and `f = 0` off `B̄_R(0)`, and `0 < r < r₀/R`, the integrals of `f` over `η_{x,r}(B)` and
`η_{x,r}(A)` differ by at most `C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ((B \ A) ∩ B̄_{rR}(x))`,
which tends to `0` as `r ↓ 0`. -/
theorem Submission.regcomp_atl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n B A x fun f => ?_
  -- `‖f‖ ≤ C` everywhere, and `f = 0` off `B̄_R(0)` with `R > 0`
  obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₁, hR₁⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₁ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₁ 1)
  have hf0 : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (closedBall_subset_closedBall (le_max_left R₁ 1) (hR₁ (subset_tsupport f hne)))
  -- the bound `C r⁻ⁿ Hⁿ((B \ A) ∩ B̄_{rR}(x))` tends to `0` as `r ↓ 0`
  have hlim : Tendsto (fun r : ℝ => C * ((ENNReal.ofReal r)⁻¹ ^ n *
      μHE[n] ((B \ A) ∩ closedBall x (r * R))).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ)) R hR hdens)
    rw [ENNReal.toReal_zero] at h
    have h' := h.const_mul C
    rw [mul_zero] at h'
    exact h'
  refine squeeze_zero_norm' ?_ hlim
  -- for `0 < r < r₀ / R` the fixed-scale comparison applies, and the scaling identity rewrites
  -- its bound
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
  have hrR : r * R ≤ r₀ := ((lt_div_iff₀ hR).1 hr.2).le
  have hBfin : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ := by
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R B hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr.1).ne'))
      (ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hrR))))
  have key := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n A B x r R C f
    (map_continuous f) hA hB hAB hr.1 hBfin hC hf0
  rwa [Submission.regcomp_atl_blowUp_measure_scaling P n x r R (B \ A) hr.1] at key

/-- Almost-everywhere locality of approximate tangent spaces (Simon Ch. 3, Remark 1.5(2), from the
proof of 3.1.6 "⇒"): if `U` is open, `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for compact
`K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces at `x`.
The upper density theorem in `U` (Simon Ch. 1, Remark 3.7(2)) applied to `B \ A` gives
`Hⁿ((B \ A) ∩ B̄_ρ(x))/ρⁿ → 0` for `Hⁿ`-a.e. `x ∈ A ⊆ U \ (B \ A)`; at such `x` choose `r₀ > 0`
with `B̄_{r₀}(x) ⊆ U`, so that `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and compare the blow-ups of `B` and `A`. -/
theorem Submission.regcomp_approx_tangent_locality : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: `B \ A` has zero `n`-density at `Hⁿ`-a.e. `x ∈ U \ (B \ A)`
  have hdens := Submission.regcomp_atl_local_density_zero P n U (B \ A) hU (hB.diff hA)
    fun K hK hKU => ne_top_of_le_ne_top (hfin K hK hKU)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 2: pass to `Hⁿ⌞A`, almost every point of which lies in `A`
  filter_upwards [ae_restrict_of_ae hdens, ae_restrict_mem hA] with x hx hxA
  have hxU : x ∈ U := hBU (hAB hxA)
  -- Step 3: a closed ball `B̄_{r₀}(x) ⊆ U`, `r₀ = ε / 2`, on which `Hⁿ⌞B` is finite
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  have hsub : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Step 4: the pointwise comparison of the blow-ups of `B` and `A`
  exact Submission.regcomp_atl_tangent_iff_of_density_zero P n A B x (ε / 2) hA hB hAB
    (half_pos hε) (hfin _ (isCompact_closedBall x (ε / 2)) hsub) (hx hxU fun h => h.2 hxA)
/-- **Radial retraction onto the closed unit ball is nonexpansive towards the ball** (step 0(d)
of `regcomp_exists_smooth_unit_form_approx`).  If `‖y‖ ≤ 1`, then
`‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖`: for `‖x‖ ≤ 1` the retraction fixes `x`; for `s = ‖x‖ > 1`,
`‖x - y‖² - ‖s⁻¹ • x - y‖² = s² - 1 - 2(1 - s⁻¹)⟨x, y⟩ ≥ (s - 1)²` by Cauchy–Schwarz. -/
theorem Submission.regcomp_norm_radial_retraction_sub_le : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E), ‖y‖ ≤ 1 → ‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖ := by
  intro E _ _ x y hy
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · -- Step 1: if `‖x‖ ≤ 1`, the retraction fixes `x`.
    rw [max_eq_left hx, inv_one, one_smul]
  · -- Steps 2–5: `s = ‖x‖ > 1`; compare the squared distances.
    rw [max_eq_right hx.le]
    have hs : 0 < ‖x‖ := one_pos.trans hx
    -- Cauchy–Schwarz with `‖y‖ ≤ 1`: `⟨x, y⟩ ≤ s`; and `s⁻¹ < 1`, `s⁻¹ s = 1`.
    have hxy : inner ℝ x y ≤ ‖x‖ :=
      (real_inner_le_norm x y).trans (mul_le_of_le_one_right hs.le hy)
    have hinv : ‖x‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    have hcancel : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hs.ne'
    -- `‖s⁻¹ • x - y‖² = 1 - 2s⁻¹⟨x, y⟩ + ‖y‖²`.
    have h2 : ‖‖x‖⁻¹ • x - y‖ ^ 2 = 1 - 2 * (‖x‖⁻¹ * inner ℝ x y) + ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hs), hcancel, one_pow]
    -- The difference of the squares is at least `(s - 1)² ≥ 0`.
    have key : ‖‖x‖⁻¹ • x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [h2, norm_sub_sq_real]
      nlinarith [mul_nonneg (sub_nonneg.2 hinv.le) (sub_nonneg.2 hxy), sq_nonneg (‖x‖ - 1)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 key

/-- **The Euclidean coefficient norm** `|α|_E = covectorEuclideanNorm α` on `Λⁿ(ℝᴾ)` (Simon
6.1.15) is a continuous seminorm dominated by the operator norm, and the radial retraction
`v ↦ (max 1 |v|_E)⁻¹ v` onto its unit ball does not increase the distance to points of that ball.

The coefficient map `Φ α = (ev_j α)_j ∈ ℓ²(Fin n → Fin P)`, with
`ev_j α = α(e_{j 0}, …, e_{j (n-1)})` for increasing `j` and `0` otherwise, is continuous linear
with `‖Φ α‖ = |α|_E` (`EuclideanSpace.norm_eq`).  So (i)–(iii) are those of `‖·‖ ∘ Φ`, (iv) holds
with `c = 1 + ‖Φ‖`, and (v) is `regcomp_norm_radial_retraction_sub_le` for `x = Φ v`, `y = Φ b`. -/
theorem Submission.regcomp_covectorEuclideanNorm_seminorm_retract : ∀ (P n : ℕ), ∃ c : ℝ, 0 < c ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) ∧ (∀ α β : Covector (Euclid P) n, covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β) ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ c * ‖α‖) ∧ ∀ v b : Covector (Euclid P) n, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm ((max 1 (covectorEuclideanNorm v))⁻¹ • v - b) ≤ covectorEuclideanNorm (v - b) := by
  intro P n
  classical
  -- `ev j α = α(e_{j 0}, …, e_{j (n-1)})` for increasing `j`, and `0` otherwise
  let ev : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun j =>
    if StrictMono j then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
        (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (j i))
    else 0
  -- the coefficient map `Φ : Λⁿ → ℓ²(Fin n → Fin P)`
  let Φ : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    (EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi ev)
  have hΦ : ∀ α, ‖Φ α‖ = covectorEuclideanNorm α := by
    intro α
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : StrictMono j <;> simp [Φ, ev, hj]
  refine ⟨1 + ‖Φ‖, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_norm.comp Φ.continuous).congr hΦ
  · intro α β
    simpa only [← hΦ, map_add] using norm_add_le (Φ α) (Φ β)
  · intro t α
    simp only [← hΦ, map_smul, norm_smul, Real.norm_eq_abs]
  · intro α
    rw [← hΦ]
    exact (Φ.le_opNorm α).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg α))
  · intro v b hb
    rw [← hΦ] at hb
    simp only [← hΦ, map_sub, map_smul]
    exact Submission.regcomp_norm_radial_retraction_sub_le (EuclideanSpace ℝ (Fin n → Fin P))
      (Φ v) (Φ b) hb
/-- Operator norm of an `n`-covector from its values on the standard basis: if
`|α(e_{j(0)}, …, e_{j(n−1)})| ≤ C` for every `j : Fin n → Fin P` (`e` the standard orthonormal
basis of `ℝᴾ`), then `‖α‖ ≤ Pⁿ C`.  Expanding each `v_k = Σᵢ (v_k)ᵢ eᵢ`, multilinearity gives
`α(v) = Σ_r (Π_k (v_k)_{r(k)}) α(e ∘ r)` over the `Pⁿ` tuples `r : Fin n → Fin P`, and
`|(v_k)ᵢ| ≤ ‖v_k‖` bounds each term by `C Π_k ‖v_k‖`. -/
theorem Submission.regcomp_covector_opNorm_le_of_basis_bound : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (C : ℝ), 0 ≤ C → (∀ j : Fin n → Fin P, |α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))| ≤ C) → ‖α‖ ≤ (P : ℝ) ^ n * C := by
  intro P n α C hC hbound
  refine ContinuousAlternatingMap.opNorm_le_bound α (by positivity) fun v => ?_
  -- multilinear expansion in the standard basis
  have hexp : α v = ∑ r : Fin n → Fin P,
      (∏ k, v k (r k)) * α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (r k)) := by
    conv_lhs => rw [show v = fun k => ∑ i, v k i • EuclideanSpace.basisFun (Fin P) ℝ i from
      funext fun k => ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (v k)).symm]
    rw [α.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [α.map_smul_univ, smul_eq_mul]
  rw [hexp]
  calc ‖∑ r : Fin n → Fin P,
        (∏ k, v k (r k)) * α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (r k))‖
      ≤ ∑ r : Fin n → Fin P,
        ‖(∏ k, v k (r k)) * α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (r k))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _r : Fin n → Fin P, (∏ k, ‖v k‖) * C := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_mul, norm_prod]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
        · exact Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ =>
            PiLp.norm_apply_le (v k) (r k)
        · simpa [Real.norm_eq_abs] using hbound r
    _ = (P : ℝ) ^ n * C * ∏ k, ‖v k‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **Smooth unit approximation inside the support.**  Let `f : ℝᴾ → Λⁿ(ℝᴾ)` be continuous with
compact support and `|f|_E ≤ 1`, where `|·|_E = covectorEuclideanNorm` (Simon 6.1.15).  For every
`κ > 0` there is a test form `h` with `support h ⊆ support f`, `|h|_E ≤ 1` and `|h - f|_E ≤ κ`.

Take `c` with `|α|_E ≤ c ‖α‖` from `regcomp_covectorEuclideanNorm_seminorm_retract` and
`δ = min (1/2) (κ/2)`.  Smooth partitions of unity give a `C^∞` map `h` with
`‖h - (1 - δ) • f‖ < δ / c` that vanishes wherever `f` does.  This is the argument of Mathlib's
`Continuous.exists_contDiff_approx`, run in place because `Mathlib.Geometry.Manifold.SmoothApprox`
is outside the contract imports.  So `tsupport h ⊆ tsupport f` is compact,
`|h|_E < δ + (1 - δ) = 1` and `|h - f|_E < δ + δ ≤ κ`. -/
theorem Submission.regcomp_exists_smooth_unit_form_support_approx : ∀ (P n : ℕ) (f : Euclid P → Covector (Euclid P) n), Continuous f → HasCompactSupport f → (∀ z, covectorEuclideanNorm (f z) ≤ 1) → ∀ κ : ℝ, 0 < κ → ∃ h : DifferentialForm (Euclid P) n, IsTestForm h ∧ support h ⊆ support f ∧ (∀ z, covectorEuclideanNorm (h z) ≤ 1) ∧ ∀ z, covectorEuclideanNorm (h z - f z) ≤ κ := by
  intro P n f hf hfc hf1 κ hκ
  -- (0) `|·|_E` is a seminorm with `|α|_E ≤ c ‖α‖`
  obtain ⟨c, hc, -, hadd, hsmul, hle, -⟩ :=
    Submission.regcomp_covectorEuclideanNorm_seminorm_retract P n
  -- (1) `δ = min (1/2) (κ/2)`
  obtain ⟨δ, hδ0, hδ1, hδκ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 2 * δ ≤ κ :=
    ⟨min (1 / 2) (κ / 2), lt_min (by norm_num) (half_pos hκ), min_le_left _ _, by
      linarith [min_le_right (1 / 2 : ℝ) (κ / 2)]⟩
  -- (2) a `C^∞` `g` with `dist (g x) ((1 - δ) • f x) < δ / c`, and `g x = 0` where `f x = 0`
  have hr : 0 < δ / c := div_pos hδ0 hc
  have hFc : Continuous fun x => (1 - δ) • f x := hf.const_smul (1 - δ)
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := ⊤)
    (modelWithCornersSelf ℝ (Euclid P))
    (t := fun x => {y | dist y ((1 - δ) • f x) < δ / c ∧ (f x = 0 → y = 0)})
    (fun x => (convex_ball ((1 - δ) • f x) (δ / c)).inter
      (convex_singleton (0 : Covector (Euclid P) n)).setOfPred_const_imp)
    (fun x => by
      have h1 : ∀ᶠ y in 𝓝 x, dist ((1 - δ) • f x) ((1 - δ) • f y) < δ / c :=
        (hFc.continuousAt.eventually_mem (ball_mem_nhds _ hr)).mono fun y hy => mem_ball'.1 hy
      have h2 : ∀ᶠ y in 𝓝 x,
          dist ((1 - δ) • f x) ((1 - δ) • f y) < δ / c ∧ (f y = 0 → (1 - δ) • f x = 0) := by
        by_cases hx : f x = 0
        · exact h1.mono fun y hy => ⟨hy, fun _ => by rw [hx, smul_zero]⟩
        · exact (h1.and (hf.continuousAt.eventually_ne hx)).mono fun y hy =>
            ⟨hy.1, fun h => absurd h hy.2⟩
      exact ⟨_, h2, fun _ => (1 - δ) • f x, contMDiffOn_const, fun y hy => hy⟩)
  -- (3) `support g ⊆ support f`
  have hsupp : support g ⊆ support f := fun x hx hfx => hx ((hg x).2 hfx)
  -- (5) `|g x - (1 - δ) • f x|_E < δ`
  have hgF : ∀ x, covectorEuclideanNorm (g x - (1 - δ) • f x) < δ := by
    intro x
    calc covectorEuclideanNorm (g x - (1 - δ) • f x) ≤ c * ‖g x - (1 - δ) • f x‖ := hle _
      _ = c * dist (g x) ((1 - δ) • f x) := by rw [dist_eq_norm]
      _ < c * (δ / c) := mul_lt_mul_of_pos_left (hg x).1 hc
      _ = δ := by field_simp
  -- (6) `|g z|_E ≤ δ + (1 - δ) = 1`
  have hunit : ∀ z, covectorEuclideanNorm (g z) ≤ 1 := by
    intro z
    calc covectorEuclideanNorm (g z)
        = covectorEuclideanNorm ((g z - (1 - δ) • f z) + (1 - δ) • f z) := by rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (g z - (1 - δ) • f z) + covectorEuclideanNorm ((1 - δ) • f z) :=
          hadd _ _
      _ = covectorEuclideanNorm (g z - (1 - δ) • f z) + (1 - δ) * covectorEuclideanNorm (f z) := by
          rw [hsmul, abs_of_nonneg (by linarith)]
      _ ≤ δ + (1 - δ) * 1 :=
          add_le_add (hgF z).le (mul_le_mul_of_nonneg_left (hf1 z) (by linarith))
      _ = 1 := by ring
  -- (7) `|g z - f z|_E ≤ δ + δ ≤ κ`
  have happrox : ∀ z, covectorEuclideanNorm (g z - f z) ≤ κ := by
    intro z
    have hsplit : g z - f z = (g z - (1 - δ) • f z) + (-δ) • f z := by
      module
    calc covectorEuclideanNorm (g z - f z)
        = covectorEuclideanNorm ((g z - (1 - δ) • f z) + (-δ) • f z) := by rw [hsplit]
      _ ≤ covectorEuclideanNorm (g z - (1 - δ) • f z) + covectorEuclideanNorm ((-δ) • f z) :=
          hadd _ _
      _ = covectorEuclideanNorm (g z - (1 - δ) • f z) + δ * covectorEuclideanNorm (f z) := by
          rw [hsmul, abs_neg, abs_of_pos hδ0]
      _ ≤ δ + δ * 1 := add_le_add (hgF z).le (mul_le_mul_of_nonneg_left (hf1 z) hδ0.le)
      _ ≤ κ := by linarith
  -- (4), (8) `tsupport g ⊆ tsupport f` is compact, so `g` is a test form
  exact ⟨g, ⟨g.contMDiff.contDiff, hfc.mono hsupp⟩, hsupp, hunit, happrox⟩

/-- **Continuous unit-form approximation in `L¹(ν)`**, the first stage of the approximation of
unit covector fields by test forms behind the mass formula `M_W(τ(M, θ, ξ)) = ∫_{M ∩ W} θ dHⁿ`
(Simon 6.3.2(3); Euclidean coefficient norm `|·|_E` of 6.1.15, 6.2.4).  Let `ν` be finite, `O`
open, `K ⊆ O` compact, and `g` a `ν`-integrable `n`-covector field with `|g|_E ≤ 1` and `g = 0`
off `K`.  Then for `ε > 0` some continuous `f` with compact support in `O` has `|f|_E ≤ 1` and
`∫ |f − g|_E dν ≤ ε`.  `ν` is regular, so `g` has a continuous `L¹(ν)`-approximation `g₀`
(indicators of measurable sets are approximated by Urysohn functions); cut it off by an Urysohn
function `χ`, equal to `1` on `K` and to `0` off `int L` for a compact `L` with `K ⊆ int L`,
`L ⊆ O`; then compose with the radial retraction `v ↦ (max 1 |v|_E)⁻¹ v` onto the unit
`|·|_E`-ball, which does not increase `|·|_E`-distances to points of that ball. -/
theorem Submission.regcomp_exists_continuous_unit_form_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (O K : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen O → IsCompact K → K ⊆ O → Integrable g ν → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → (∀ x, x ∉ K → g x = 0) → ∀ ε : ℝ, 0 < ε → ∃ f : Euclid P → Covector (Euclid P) n, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ (∀ z, covectorEuclideanNorm (f z) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (f x - g x)) ∂ν ≤ ENNReal.ofReal ε := by
  intro P n ν O K g hν hO hK hKO hg hg1 hgK ε hε
  -- Step 0: the norm facts and the radial retraction `π v = (max 1 |v|_E)⁻¹ • v`
  obtain ⟨c, hc, hcont, -, hsmul, hle, hretr⟩ :=
    Submission.regcomp_covectorEuclideanNorm_seminorm_retract P n
  let π : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun v => (max 1 (covectorEuclideanNorm v))⁻¹ • v
  have hmax : ∀ v : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm v) :=
    fun v => zero_lt_one.trans_le (le_max_left _ _)
  have hπc : Continuous π :=
    ((continuous_const.max hcont).inv₀ fun v => (hmax v).ne').smul continuous_id
  have hπ1 : ∀ v, covectorEuclideanNorm (π v) ≤ 1 := fun v => by
    change covectorEuclideanNorm ((max 1 (covectorEuclideanNorm v))⁻¹ • v) ≤ 1
    rw [hsmul, abs_of_pos (inv_pos.2 (hmax v)), inv_mul_le_iff₀ (hmax v), mul_one]
    exact le_max_right _ _
  -- Step 1: `ν` is finite, hence regular.  For measurable `s`, an Urysohn function `φ`, equal to
  -- `1` on a compact `F ⊆ s` and to `0` off an open `V ⊇ s`, has `‖φ • a − 1_s a‖ ≤ ‖1_{V \ F} a‖`
  -- with `ν (V \ F)` small; so by density some continuous `g₀` has `∫ ‖g − g₀‖ dν ≤ ε / c`, and
  -- as `|·|_E ≤ c ‖·‖`, `∫ |g₀ − g|_E dν ≤ ε`
  have hind : ∀ (a : Covector (Euclid P) n) ⦃s : Set (Euclid P)⦄, MeasurableSet s → ν s < ∞ →
      ∀ {δ : ℝ≥0∞}, δ ≠ 0 → ∃ φ : Euclid P → Covector (Euclid P) n,
        eLpNorm (φ - s.indicator fun _ => a) 1 ν ≤ δ ∧ Continuous φ := by
    intro a s hs _ δ hδ
    obtain ⟨η, hη, hηδ⟩ := exists_eLpNorm_indicator_le (μ := ν) ENNReal.one_ne_top a hδ
    have hη2 : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_pos.2 hη).ne').ne'
    obtain ⟨F, hFs, hF, hsF⟩ := hs.exists_isCompact_sdiff_lt (measure_ne_top ν s) hη2
    obtain ⟨V, hsV, hV, -, hVs⟩ := hs.exists_isOpen_sdiff_lt (measure_ne_top ν s) hη2
    obtain ⟨φ, hφF, hφV, -, hφ⟩ := exists_continuous_one_zero_of_isCompact hF hV.isClosed_compl
      (disjoint_compl_right_iff_subset.2 (hFs.trans hsV))
    have hφc : Continuous fun x => φ x • a := φ.continuous.smul continuous_const
    refine ⟨fun x => φ x • a, (eLpNorm_mono (hφc.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator hs)) fun x => ?_).trans (hηδ (V \ F) ?_
      (hV.measurableSet.diff hF.measurableSet).nullMeasurableSet), hφc⟩
    · -- pointwise: `0` on `F` and off `V`, at most `‖a‖` on `V \ F`
      show ‖φ x • a - s.indicator (fun _ => a) x‖ ≤ ‖(V \ F).indicator (fun _ => a) x‖
      by_cases hxF : x ∈ F
      · rw [hφF hxF, indicator_of_mem (hFs hxF), Pi.one_apply, one_smul, sub_self, norm_zero]
        exact norm_nonneg _
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ F from ⟨hxV, hxF⟩)]
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs]
          calc ‖φ x • a - a‖ = ‖(φ x - 1) • a‖ := by rw [sub_smul (φ x) 1 a, one_smul]
            _ = |φ x - 1| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ 1 * ‖a‖ := by
                gcongr
                rw [abs_le]
                constructor <;> linarith [(hφ x).1, (hφ x).2]
            _ = ‖a‖ := one_mul _
        · rw [indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hφ x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφ x).2
      · rw [hφV (mem_compl hxV), Pi.zero_apply, zero_smul,
          indicator_of_notMem fun h => hxV (hsV h), sub_zero, norm_zero]
        exact norm_nonneg _
    · -- `V \ F ⊆ (V \ s) ∪ (s \ F)`
      calc ν (V \ F) ≤ ν ((V \ s) ∪ (s \ F)) := measure_mono fun x hx => by
            by_cases hxs : x ∈ s
            exacts [Or.inr ⟨hxs, hx.2⟩, Or.inl ⟨hx.1, hxs⟩]
        _ ≤ ν (V \ s) + ν (s \ F) := measure_union_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add hVs.le hsF.le
        _ = η := ENNReal.add_halves _
  obtain ⟨g₀, hgg₀, hg₀c⟩ := (memLp_one_iff_integrable.2 hg).induction_dense ENNReal.one_ne_top
    Continuous hind (fun _ _ h₁ h₂ => h₁.add h₂) (ENNReal.ofReal_pos.2 (div_pos hε hc)).ne'
  rw [eLpNorm_one_eq_lintegral_enorm (hg.aestronglyMeasurable.sub hg₀c.aestronglyMeasurable)]
    at hgg₀
  have h₀ : ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₀ x - g x)) ∂ν ≤ ENNReal.ofReal ε :=
    calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₀ x - g x)) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal c * ‖(g - g₀) x‖ₑ ∂ν := lintegral_mono fun x => by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul hc.le, Pi.sub_apply, norm_sub_rev]
          exact ENNReal.ofReal_le_ofReal (hle _)
      _ = ENNReal.ofReal c * ∫⁻ x, ‖(g - g₀) x‖ₑ ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (ε / c) := by gcongr
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_mul hc.le, mul_div_cancel₀ _ hc.ne']
  -- Step 2: a compact `L` with `K ⊆ int L`, `L ⊆ O`, and an Urysohn cutoff `χ`, `1` on `K` and
  -- `0` off `int L`; since `g = χ • g`, `|χ • g₀ − g|_E = χ |g₀ − g|_E ≤ |g₀ − g|_E`
  obtain ⟨L, hL, hKL, hLO⟩ := exists_compact_between hK hO hKO
  obtain ⟨χ, hχK, hχL, -, hχ⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.2 hKL)
  have hχ0 : ∀ x, x ∉ L → χ x = 0 := fun x hx => hχL fun hx' => hx (interior_subset hx')
  have hgχ : ∀ x, χ x • g x = g x := by
    intro x
    by_cases hx : x ∈ K
    · rw [hχK hx, Pi.one_apply, one_smul]
    · rw [hgK x hx, smul_zero]
  have h₁ : ∀ x, covectorEuclideanNorm (χ x • g₀ x - g x) ≤ covectorEuclideanNorm (g₀ x - g x) :=
    fun x => calc covectorEuclideanNorm (χ x • g₀ x - g x)
        = covectorEuclideanNorm (χ x • (g₀ x - g x)) := by rw [smul_sub, hgχ x]
      _ = χ x * covectorEuclideanNorm (g₀ x - g x) := by rw [hsmul, abs_of_nonneg (hχ x).1]
      _ ≤ covectorEuclideanNorm (g₀ x - g x) :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ x).2
  -- Step 3: `f = π ∘ (χ • g₀)` is continuous, vanishes off `L` (`π 0 = 0`) and has `|f|_E ≤ 1`
  have hfL : support (fun x => π (χ x • g₀ x)) ⊆ L := fun x hx => by
    by_contra hxL
    exact hx (show π (χ x • g₀ x) = 0 by rw [hχ0 x hxL, zero_smul]; exact smul_zero _)
  have hfL' : tsupport (fun x => π (χ x • g₀ x)) ⊆ L := closure_minimal hfL hL.isClosed
  refine ⟨fun x => π (χ x • g₀ x), hπc.comp (χ.continuous.smul hg₀c),
    hL.of_isClosed_subset (isClosed_tsupport _) hfL', hfL'.trans hLO, fun z => hπ1 _, ?_⟩
  -- Step 4: `|f − g|_E ≤ |χ • g₀ − g|_E ≤ |g₀ − g|_E` pointwise, as `|g|_E ≤ 1`; integrate
  exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    ((hretr _ _ (hg1 x)).trans (h₁ x))).trans h₀
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

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- **A unit covector attaining `1` on an orthonormal frame** (Simon (6.1.1); step 1(b) of the
mass formula, Remark 6.3.2(3)): every orthonormal `τ₁, …, τₙ` in `ℝᴾ` admits an `n`-covector `β`
with `|β|_E = 1` and `β(τ) = 1`.  Take the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors
`⟨τᵢ, ·⟩`, so `β(τ) = det 1 = 1`.  Extend `τ` to an orthonormal basis `f` of `ℝᴾ` with
`f ∘ ι = τ`, `ι = Fin.castLE`.  Then `β(f ∘ j) = sgn π` if `j = ι ∘ π` for a permutation `π`,
and `β(f ∘ j) = 0` otherwise (a zero column, or a repeated vector), so `Σ_j β(f ∘ j)² = n!`;
`regcomp_covector_sq_sum_orthonormalBasis` turns this into `n! = n! |β|_E²`. -/
theorem Submission.regcomp_exists_covector_eval_orthonormal_eq_one : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β = 1 ∧ β τ = 1 := by
  intro P n τ hτ
  classical
  -- Step 1: the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors `⟨τᵢ, ·⟩` (Simon (6.1.1))
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) n, ∀ v : Fin n → Euclid P,
      β v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun i => (innerSL ℝ (τ i) : Euclid P →L[ℝ] ℝ).toLinearMap
    let g : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hg : ∀ v, g v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      intro v
      rw [← Matrix.det_transpose]
      show Matrix.det (Matrix.of fun a b => L (v a) b) = _
      congr 1
    have hcont : Continuous fun v : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i k
      exact Continuous.inner (f := fun _ => τ i) (g := fun v : Fin n → Euclid P => v k)
        continuous_const (continuous_apply k)
    refine ⟨{ g with cont := ?_ }, hg⟩
    have : (g : (Fin n → Euclid P) → ℝ) =
        fun v => Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := funext hg
    simpa [this] using hcont
  -- Step 2: by orthonormality `(⟨τᵢ, τ_k⟩) = 1`, so `β(τ) = det 1 = 1`
  have hβτ : β τ = 1 := by
    have hone : (Matrix.of fun i k => inner ℝ (τ i) (τ k) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext i k
      rw [Matrix.of_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.mp hτ i k
    rw [hβ, hone, Matrix.det_one]
  -- Step 3: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 4: `β(f ∘ j)² = 1` if `j = ι ∘ π` for a permutation `π`, and `0` otherwise
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), β (fun k => f (Φ π k)) ^ 2 = 1 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : β (τ ∘ π) = Equiv.Perm.sign π • β τ := β.toAlternatingMap.map_perm τ π
    rw [h1, h2, hβτ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hzero : ∀ j : Fin n → Fin P, j ∉ Finset.univ.image Φ → β (fun k => f (j k)) ^ 2 = 0 := by
    intro j hj
    have hj' : ∀ π, Φ π ≠ j := fun π hπ => hj (Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ⟩)
    rw [sq_eq_zero_iff]
    by_cases hr : ∀ k, j k ∈ range ι
    · -- `j = ι ∘ ρ` with `ρ` not a permutation, hence not injective: `f ∘ j` repeats a vector
      choose ρ hρ using hr
      have hρ' : ¬ Injective ρ := fun hinj =>
        hj' (Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hinj)) (funext hρ)
      refine β.map_eq_zero_of_not_injective _ fun hinj => hρ' fun a b hab => hinj ?_
      exact congrArg f ((hρ a).symm.trans ((congrArg ι hab).trans (hρ b)))
    · -- some `j k₀ ∉ range ι`: column `k₀` of `(⟨τᵢ, f (j k)⟩)` vanishes
      obtain ⟨k₀, hk₀⟩ := not_forall.mp hr
      rw [hβ]
      refine Matrix.det_eq_zero_of_column_eq_zero k₀ fun i => ?_
      rw [Matrix.of_apply, ← hfι i, f.inner_eq_ite, ite_eq_right fun h => hk₀ ⟨i, h⟩]
  have hsum : ∑ j : Fin n → Fin P, β (fun k => f (j k)) ^ 2 = n.factorial := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) fun j _ hj => hzero j hj,
      Finset.sum_image fun π _ π' _ h => hΦ h]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- Step 5: `n! = n! |β|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`, so `|β|_E = 1`
  have hsq := Submission.regcomp_covector_sq_sum_orthonormalBasis P n β f
  rw [hsum] at hsq
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine ⟨β, (pow_eq_one_iff_of_nonneg (covectorEuclideanNorm_nonneg β) two_ne_zero).mp ?_, hβτ⟩
  exact mul_left_cancel₀ hfac (by rw [← hsq, mul_one])
/-- **Simon Ch. 6, 1.7 and 1.15**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has dual Euclidean coefficient norm exactly one: `|ξ(α)| = |α(τ)| ≤ |α|_E` for every
`n`-covector `α`, and `ξ(±β₀) = 1` for a covector `β₀` with `|β₀|_E = 1` and `β₀(τ) = 1`
(`+β₀` for the sign `+`, `−β₀` for the sign `−`, using `|−β₀|_E = |β₀|_E`). -/
theorem Submission.regcomp_unit_orientation_pairing : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ β = 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  obtain ⟨β₀, hβ₀, hβ₀τ⟩ := Submission.regcomp_exists_covector_eval_orthonormal_eq_one P n τ hτ
  rcases hξ with h | h
  · -- `ξ(α) = α(τ)`: take `β = β₀`
    refine ⟨fun α => ?_, β₀, hβ₀.le, ?_⟩
    · rw [h α]
      exact Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    · rw [h β₀, hβ₀τ]
  · -- `ξ(α) = −α(τ)`: `|ξ(α)| = |α(τ)|`, and take `β = −β₀`
    refine ⟨fun α => ?_, -β₀, ?_, ?_⟩
    · rw [h α, abs_neg]
      exact Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    · rw [covectorEuclideanNorm_neg]
      exact hβ₀.le
    · rw [h (-β₀), ContinuousAlternatingMap.neg_apply, hβ₀τ, neg_neg]
/-- **A dense sequence in the Euclidean unit ball of `n`-covectors.**  There are `bₖ ∈ Λⁿ(ℝᴾ)`
with `|bₖ|_E ≤ 1` such that every `β` with `|β|_E ≤ 1` lies in the closure of `{bₖ}` (normed
topology of `Λⁿ`; `|·|_E` is the Euclidean coefficient norm of Simon (6.1.15)).

`Λⁿ` is finite dimensional, since `α ↦ (α(e_{J(0)}, …, e_{J(n−1)}))_J` is linear and injective
(a multilinear map is determined by its values on basis vectors).  Hence `Λⁿ` is proper, second
countable and separable, so the ball `B = {|β|_E ≤ 1}` contains a countable `D` with
`B ⊆ closure D`.  `D` is nonempty as `0 ∈ B`, so `D` is the range of a sequence. -/
theorem Submission.regcomp_covector_unit_ball_dense_seq : ∀ (P n : ℕ), ∃ b : ℕ → Covector (Euclid P) n, (∀ k, covectorEuclideanNorm (b k) ≤ 1) ∧ ∀ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 → β ∈ closure (Set.range b) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `ev α = (α(e ∘ J))_J`, linear since addition and scaling of covectors are pointwise
  let ev : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α J => α fun i => e (J i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `ev` is injective, so `Λⁿ` is finite dimensional
  have : FiniteDimensional ℝ (Covector (Euclid P) n) :=
    FiniteDimensional.of_injective ev fun α β h =>
      ContinuousAlternatingMap.toAlternatingMap_injective <|
        AlternatingMap.coe_multilinearMap_injective <|
          Module.Basis.ext_multilinear (fun _ => e) fun J => congr_fun h J
  -- `Λⁿ` is separable, so `B` has a countable subset `D` with `B ⊆ closure D`
  obtain ⟨D, hDB, hDc, hBD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace
    {β : Covector (Euclid P) n | covectorEuclideanNorm β ≤ 1}).exists_countable_dense_subset
  -- `0 ∈ B ⊆ closure D`, so `D` is nonempty
  have hD : D.Nonempty := closure_nonempty_iff.1 ⟨0, hBD (by simp)⟩
  -- enumerate `D = range b`
  obtain ⟨b, rfl⟩ := hDc.exists_eq_range hD
  exact ⟨b, fun k => hDB (Set.mem_range_self k), fun β hβ => hBD hβ⟩
/-- **First-hit selection** (step 4 of the proof of the near-maximizer lemma for Simon 7.5.11):
for Borel sets `A k ⊆ ℝᴾ` and covectors `b k` there is a strongly measurable `g` with
`g = b k` on `A k \ ⋃_{i<k} A i` and `g = 0` off `⋃ₖ A k`.  With `C 0 = (⋃ₖ A k)ᶜ`,
`C (k + 1) = A k`, the first-hit index `N(x) = min {N | x ∈ C N}` is measurable
(`measurable_find`), and `g = b' ∘ N` for `b' 0 = 0`, `b' (k + 1) = b k`. -/
theorem Submission.regcomp_covector_first_hit_selection : ∀ (P n : ℕ) (A : ℕ → Set (Euclid P)) (b : ℕ → Covector (Euclid P) n), (∀ k, MeasurableSet (A k)) → ∃ g : Euclid P → Covector (Euclid P) n, StronglyMeasurable g ∧ ∀ x, (g x = 0 ∧ ∀ k, x ∉ A k) ∨ ∃ k, x ∈ A k ∧ g x = b k := by
  intro P n A b hA
  classical
  -- the augmented measurable family `C 0 = (⋃ₖ A k)ᶜ`, `C (k + 1) = A k` covers `ℝᴾ`
  obtain ⟨C, hC0, hCs⟩ : ∃ C : ℕ → Set (Euclid P), C 0 = (⋃ k, A k)ᶜ ∧ ∀ k, C (k + 1) = A k :=
    ⟨fun N => Nat.rec (motive := fun _ => Set (Euclid P)) (⋃ k, A k)ᶜ (fun k _ => A k) N, rfl,
      fun _ => rfl⟩
  have hCm : ∀ N, MeasurableSet (C N) := by
    intro N
    cases N with
    | zero => rw [hC0]; exact (MeasurableSet.iUnion hA).compl
    | succ k => rw [hCs]; exact hA k
  have hcov : ∀ x, ∃ N, x ∈ C N := by
    intro x
    by_cases hx : ∃ k, x ∈ A k
    · obtain ⟨k, hk⟩ := hx
      exact ⟨k + 1, by rw [hCs]; exact hk⟩
    · exact ⟨0, by rw [hC0, mem_compl_iff, mem_iUnion]; exact hx⟩
  -- the first-hit index is measurable, and `g = b' ∘ N` with `b' 0 = 0`, `b' (k + 1) = b k`
  have hNm : Measurable fun x => Nat.find (hcov x) := measurable_find hcov hCm
  obtain ⟨b', hb'0, hb's⟩ : ∃ b' : ℕ → Covector (Euclid P) n, b' 0 = 0 ∧ ∀ k, b' (k + 1) = b k :=
    ⟨fun N => Nat.rec (motive := fun _ => Covector (Euclid P) n) 0 (fun k _ => b k) N, rfl,
      fun _ => rfl⟩
  refine ⟨fun x => b' (Nat.find (hcov x)),
    (StronglyMeasurable.of_discrete (f := b')).comp_measurable hNm, fun x => ?_⟩
  have hspec := Nat.find_spec (hcov x)
  show (b' (Nat.find (hcov x)) = 0 ∧ ∀ k, x ∉ A k) ∨ ∃ k, x ∈ A k ∧ b' (Nat.find (hcov x)) = b k
  generalize Nat.find (hcov x) = N at hspec ⊢
  cases N with
  | zero =>
    rw [hC0, mem_compl_iff, mem_iUnion] at hspec
    exact Or.inl ⟨hb'0, fun k hk => hspec ⟨k, hk⟩⟩
  | succ k =>
    rw [hCs] at hspec
    exact Or.inr ⟨k, hspec, hb's k⟩

/-- **A near-maximizing covector field** (step 3.1 of the proof of the mass formula
`M_W(T) = μ_T(W)` for Simon 7.5.11): if `μ`-a.e. `ξ(x)` attains the value `1` on the Euclidean
unit ball `B = {|β|_E ≤ 1}` of `Λⁿ(ℝᴾ)`, then for every `η > 0` there is a strongly measurable
`g : ℝᴾ → B` with `⟨g(x), ξ(x)⟩ ≥ 1 - η` for `μ`-a.e. `x`.

Take a sequence `bₖ ∈ B` dense in `B` and a strongly measurable `ξ̃ = ξ` `μ`-a.e.; the sets
`Aₖ = {x | 1 - η < ξ̃(x)(bₖ)}` are measurable.  Let `g = bₖ` on `Aₖ \ ⋃_{i<k} Aᵢ` and `g = 0`
off `⋃ₖ Aₖ`.  For a.e. `x`, `{β' | 1 - η < ξ(x)(β')}` is an open neighbourhood of some `β ∈ B`,
so it contains some `bₖ`, i.e. `x ∈ Aₖ`; hence `g(x) = bⱼ` with `x ∈ Aⱼ`. -/
theorem Submission.regcomp_covector_field_near_maximizer : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (η : ℝ), 0 < η → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ x β = 1) → ∃ g : Euclid P → Covector (Euclid P) n, StronglyMeasurable g ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ᵐ x ∂μ, 1 - η ≤ ξ x (g x) := by
  intro P n μ ξ η hη hξ hmax
  -- a sequence `bₖ ∈ B` dense in `B`
  obtain ⟨b, hbB, hbd⟩ := Submission.regcomp_covector_unit_ball_dense_seq P n
  -- `Aₖ = {x | 1 - η < ξ̃(x)(bₖ)}` for the strongly measurable version `ξ̃ = hξ.mk ξ`
  let A : ℕ → Set (Euclid P) := fun k => {x | 1 - η < hξ.mk ξ x (b k)}
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    measurableSet_lt measurable_const
      ((ContinuousLinearMap.apply ℝ ℝ (b k)).continuous.comp_stronglyMeasurable
        hξ.stronglyMeasurable_mk).measurable
  -- `g = bₖ` on `Aₖ \ ⋃_{i<k} Aᵢ` and `g = 0` off `⋃ₖ Aₖ`
  obtain ⟨g, hg, hgA⟩ := Submission.regcomp_covector_first_hit_selection P n A b hA
  refine ⟨g, hg, fun x => ?_, ?_⟩
  · -- `g(x) ∈ {0} ∪ {bₖ} ⊆ B`
    rcases hgA x with ⟨h0, -⟩ | ⟨k, -, hk⟩
    · rw [h0, covectorEuclideanNorm_zero]
      exact zero_le_one
    · rw [hk]
      exact hbB k
  · filter_upwards [hmax, hξ.ae_eq_mk] with x ⟨β, hβB, hβ⟩ hx
    -- the open set `{β' | 1 - η < ξ(x)(β')}` contains `β ∈ closure (range b)`, hence some `bₖ`
    obtain ⟨_, hk, k, rfl⟩ := mem_closure_iff.1 (hbd β hβB) {β' | 1 - η < ξ x β'}
      (isOpen_lt continuous_const (ξ x).continuous) (by rw [mem_ofPred_eq, hβ]; linarith)
    rw [mem_ofPred_eq, hx] at hk
    -- so `x ∈ ⋃ₖ Aₖ`, and `g(x) = bⱼ` with `x ∈ Aⱼ`
    rcases hgA x with ⟨-, hxA⟩ | ⟨j, hj, hgj⟩
    · exact (hxA k hk).elim
    · rw [hgj, hx]
      exact le_of_lt hj

/-- **Upper mass bound for `T = τ(M, θ, ξ)`** (one half of Simon Ch. 6, Remark 3.2(3); mass
(6.2.5)).  If `R = (C, θ, ξ)` represents `T` in `U`, then `M_W(T) ≤ (θ Hⁿ⌞C)(W)` for every
`W ⊆ ℝᴾ`.  For an admissible `ω` put `S = spt ω ⊆ W`, a closed (hence Borel) set.  A.e. on `C`
the orientation `ξ(x)` is a unit `n`-vector, so `|⟨ω(x), ξ(x)⟩| ≤ |ω(x)| ≤ 1`, and
`⟨ω(x), ξ(x)⟩ = 0` off `S`; hence `|θ⟨ω, ξ⟩| ≤ θ 1_S` a.e. on `C`, and
`T(ω) ≤ ∫_C |θ⟨ω, ξ⟩| dHⁿ ≤ ∫_{C ∩ S} θ dHⁿ = (θ Hⁿ⌞C)(S) ≤ (θ Hⁿ⌞C)(W)`. -/
theorem Submission.regcomp_imrep_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  refine sSup_le ?_
  rintro _ ⟨ω, ⟨hωW, hω⟩, rfl⟩
  -- `S = spt ω` is closed, hence Borel, and `S ⊆ W`
  set S := tsupport (ω : DifferentialForm (Euclid P) n)
  have hS : MeasurableSet S := (isClosed_tsupport _).measurableSet
  -- a.e. on `C`: `‖θ ⟨ω, ξ⟩‖ₑ ≤ θ 1_S`, by the unit orientation pairing and `|ω|_E ≤ 1`
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤
        S.indicator (fun x => (R.mult x : ℝ≥0∞)) x := by
    filter_upwards [R.orients] with x hxQ
    obtain ⟨Q, -, hQ⟩ := hxQ
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, enorm_mul, Real.enorm_natCast]
      refine mul_le_of_le_one_right zero_le ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (((Submission.regcomp_unit_orientation_pairing P n (R.orient x) Q hQ).1 _).trans (hω x))
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  calc ENNReal.ofReal (T ω) ≤ ‖T ω‖ₑ := Real.ofReal_le_enorm _
    _ ≤ ∫⁻ x in R.carrier,
          ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n] := by
      rw [hR ω]
      exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in R.carrier, S.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] :=
      lintegral_mono_ae hbound
    _ = R.measure S := by
      rw [lintegral_indicator hS, IMRep.measure, withDensity_apply _ hS]
    _ ≤ R.measure W := measure_mono hωW
/-- **Smooth unit forms approximating a unit covector field in `L¹(ν)`** (used in the proof of the
mass formula `M_W(T) = μ_T(W)`, with `ν = μ_T⌞O`).  Let `ν` be finite, `O` open, `K ⊆ O` compact
and `g` an a.e. strongly measurable field with `|g|_E ≤ 1` vanishing off `K`.  Then for every
`ε > 0` some test form `h` has `tsupport h ⊆ O`, `|h|_E ≤ 1` and `∫|h − g|_E dν < ε`.
On a standard basis tuple `e ∘ j`, `|α(e ∘ j)| ≤ |α|_E` (orthonormal if `j` is injective, `0`
otherwise), so `‖α‖ ≤ Pⁿ|α|_E` and `g` is bounded, hence integrable.  Approximate `g` within `ε/4`
in `L¹(ν)` by a continuous unit field `f` with compact support in `O`
(`regcomp_exists_continuous_unit_form_approx`), then `f` uniformly within
`κ = ε/(4(1 + ν(ℝᴾ)))` by a unit test form `h` with `support h ⊆ support f`
(`regcomp_exists_smooth_unit_form_support_approx`); the error is `≤ κ ν(ℝᴾ) + ε/4 ≤ ε/2`. -/
theorem Submission.regcomp_exists_smooth_unit_form_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (O K : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen O → IsCompact K → K ⊆ O → AEStronglyMeasurable g ν → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → (∀ x, x ∉ K → g x = 0) → ∀ ε : ℝ, 0 < ε → ∃ h : DifferentialForm (Euclid P) n, IsTestForm h ∧ tsupport h ⊆ O ∧ (∀ z, covectorEuclideanNorm (h z) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ∂ν < ENNReal.ofReal ε := by
  intro P n ν O K g hν hO hK hKO hg hg1 hgK ε hε
  -- step 0(a): the triangle inequality for `|·|_E`
  obtain ⟨-, -, -, hadd, -, -, -⟩ := Submission.regcomp_covectorEuclideanNorm_seminorm_retract P n
  -- step 0(c): `‖α‖ ≤ Pⁿ|α|_E`, as `|α(e ∘ j)| ≤ |α|_E` for every `j : Fin n → Fin P`
  have hop : ∀ α : Covector (Euclid P) n, ‖α‖ ≤ (P : ℝ) ^ n * covectorEuclideanNorm α := by
    intro α
    refine Submission.regcomp_covector_opNorm_le_of_basis_bound P n α _
      (covectorEuclideanNorm_nonneg α) fun j => ?_
    by_cases hj : Injective j
    · -- `e ∘ j` is orthonormal
      exact Submission.regcomp_covector_eval_orthonormal_le P n α _
        ((EuclideanSpace.basisFun (Fin P) ℝ).orthonormal.comp j hj)
    · -- `e ∘ j` has a repeated entry, so `α(e ∘ j) = 0`
      have hv : ¬Injective fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k) :=
        fun he => hj fun a b hab => he (congrArg (EuclideanSpace.basisFun (Fin P) ℝ) hab)
      rw [α.map_eq_zero_of_not_injective _ hv, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  -- step 1: `‖g x‖ ≤ Pⁿ`, so `g` is `ν`-integrable
  have hgi : Integrable g ν :=
    Integrable.of_bound hg ((P : ℝ) ^ n) (Eventually.of_forall fun x =>
      (hop (g x)).trans (mul_le_of_le_one_right (by positivity) (hg1 x)))
  -- steps 1–3: a continuous unit field `f`, compactly supported in `O`, `ε/4`-close to `g`
  obtain ⟨f, hfc, hfcs, hfO, hf1, hfg⟩ := Submission.regcomp_exists_continuous_unit_form_approx
    P n ν O K g hν hO hK hKO hgi hg1 hgK (ε / 4) (by positivity)
  -- step 4: a unit test form `h` with `support h ⊆ support f` and `|h − f|_E ≤ κ`
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ε / (4 * (1 + (ν univ).toReal)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  obtain ⟨h, hh, hhf, hh1, hhκ⟩ :=
    Submission.regcomp_exists_smooth_unit_form_support_approx P n f hfc hfcs hf1 κ hκ0
  refine ⟨h, hh, (closure_mono hhf).trans hfO, hh1, ?_⟩
  -- step 5: `|h − g|_E ≤ κ + |f − g|_E` pointwise, and `κ ν(ℝᴾ) ≤ ε/4`
  have hpt : ∀ x, ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ≤
      ENNReal.ofReal κ + ENNReal.ofReal (covectorEuclideanNorm (f x - g x)) := by
    intro x
    rw [← ENNReal.ofReal_add hκ0.le (covectorEuclideanNorm_nonneg _),
      ← sub_add_sub_cancel (h x) (f x) (g x)]
    exact ENNReal.ofReal_le_ofReal ((hadd _ _).trans (add_le_add (hhκ x) le_rfl))
  have hκν : ENNReal.ofReal κ * ν univ ≤ ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← ENNReal.ofReal_mul hκ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc κ * (ν univ).toReal ≤ κ * (1 + (ν univ).toReal) :=
          mul_le_mul_of_nonneg_left (by linarith) hκ0.le
      _ = ε / 4 := by
          rw [hκ, div_mul_eq_mul_div,
            mul_div_mul_right ε 4 (show 1 + (ν univ).toReal ≠ 0 by positivity)]
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal κ + ENNReal.ofReal (covectorEuclideanNorm (f x - g x))) ∂ν :=
        lintegral_mono hpt
    _ = ENNReal.ofReal κ * ν univ +
          ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (f x - g x)) ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := add_le_add hκν hfg
    _ = ENNReal.ofReal (ε / 4 + ε / 4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- **Lower mass bound for `T = τ(C, θ, ξ)`** (the other half of Simon Ch. 6, Remark 3.2(3);
mass (6.2.5)).  If `R = (C, θ, ξ)` represents `T` in the open set `U`, then
`(θ Hⁿ⌞C)(W) ≤ M_W(T)` for every open `W`.  Since `C ⊆ U`, `μ = θ Hⁿ⌞C` is carried by `U`, so it
suffices to bound `μ(K)` for compact `K ⊆ W ∩ U` (compact exhaustion of `W ∩ U`).  Choose a compact
`L` with `K ⊆ O := int L` and `L ⊆ W ∩ U`, so `μ(L) < ∞`.  For `η ∈ (0, 1)` take a measurable
near-maximizing covector field `g = 1_K g₀` (`|g|_E ≤ 1`, `⟨g, ξ⟩ ≥ 1 - η` a.e. on `C ∩ K`) and
a smooth form `h` supported in `O` with `|h|_E ≤ 1` and `∫ |h - g|_E d(μ⌞O) < η`; `h` is
admissible for `M_W(T)`, and `T(h) = ∫ θ⟨h, ξ⟩ dHⁿ⌞C ≥ (1 - η) μ(K) - η` because
`|⟨α, ξ⟩| ≤ |α|_E` a.e. on `C`.  Letting `η ↓ 0` gives `μ(K) ≤ M_W(T)`. -/
theorem Submission.regcomp_imrep_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  -- notation: `μC = Hⁿ⌞C`, `θ`, and `μ = R.measure = θ μC`
  set μC : Measure (Euclid P) := μHE[n].restrict R.carrier with hμC
  set θ : Euclid P → ℝ≥0∞ := fun x => (R.mult x : ℝ≥0∞) with hθ
  have hμ : R.measure = μC.withDensity θ := rfl
  have hθm : Measurable θ := by
    have := R.measurable_mult
    fun_prop
  have hθrm : Measurable fun x => (R.mult x : ℝ) := by
    have := R.measurable_mult
    fun_prop
  -- step 1: a.e. on `C`, `|⟨α, ξ⟩| ≤ |α|_E` and `⟨β, ξ⟩ = 1` for some `|β|_E ≤ 1`
  have hpair : ∀ᵐ x ∂μC, (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
      ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.regcomp_unit_orientation_pairing P n (R.orient x) Q hQ
  -- the Euclidean coefficient norm is continuous
  have hnormc : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- key estimate: `μ(K) ≤ M_W(T)` for every compact `K ⊆ W ∩ U`
  have hKey : ∀ K : Set (Euclid P), IsCompact K → K ⊆ W ∩ U → R.measure K ≤ T.massOn W := by
    intro K hK hKWU
    obtain ⟨L, hL, hKL, hLWU⟩ := exists_compact_between hK (hW.inter hU) hKWU
    set O := interior L
    have hOL : O ⊆ L := interior_subset
    have hLm : MeasurableSet L := hL.measurableSet
    have hKm : MeasurableSet K := hK.measurableSet
    have hLU : L ⊆ U := hLWU.trans inter_subset_right
    have hLW : L ⊆ W := hLWU.trans inter_subset_left
    have hKL' : K ⊆ L := hKL.trans hOL
    have hμL : R.measure L < ∞ := by
      rw [hμ, withDensity_apply _ hLm, hμC, Measure.restrict_restrict hLm, inter_comm]
      exact (R.locallyIntegrable_mult L hL hLU).lt_top
    have hνfin : IsFiniteMeasure (R.measure.restrict O) :=
      isFiniteMeasure_restrict.2 ((measure_mono hOL).trans_lt hμL).ne
    have hμK : R.measure K ≠ ∞ := ((measure_mono hKL').trans_lt hμL).ne
    set m := (R.measure K).toReal with hm
    -- integrability of functions dominated by `θ 1_L`
    have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f μC →
        (∀ᵐ x ∂μC, ‖f x‖ₑ ≤ L.indicator θ x) → Integrable f μC := by
      intro f hf hfb
      refine ⟨hf, ?_⟩
      calc ∫⁻ x, ‖f x‖ₑ ∂μC ≤ ∫⁻ x, L.indicator θ x ∂μC := lintegral_mono_ae hfb
        _ = R.measure L := by rw [lintegral_indicator hLm, hμ, withDensity_apply _ hLm]
        _ < ∞ := hμL
    -- pointwise domination of `θ ⟨a, ξ⟩` for `|a|_E ≤ 1`, `a = 0` off `L`
    have hpt : ∀ x, (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) →
        ∀ a : Covector (Euclid P) n, covectorEuclideanNorm a ≤ 1 → (x ∉ L → a = 0) →
        ‖(R.mult x : ℝ) * R.orient x a‖ₑ ≤ L.indicator θ x := by
      intro x hx a ha ha0
      by_cases hxL : x ∈ L
      · rw [indicator_of_mem hxL, enorm_mul, Real.enorm_natCast]
        refine mul_le_of_le_one_right zero_le ?_
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 ((hx a).trans ha)
      · rw [indicator_of_notMem hxL, ha0 hxL, map_zero, mul_zero, enorm_zero]
    -- `∫ θ 1_K dμC = μ(K)`
    have hKi : Integrable (K.indicator fun x => (R.mult x : ℝ)) μC := by
      refine hint _ (hθrm.indicator hKm).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, indicator_of_mem (hKL' hxK), Real.enorm_natCast]
      · rw [indicator_of_notMem hxK, enorm_zero]
        exact zero_le
    have hKint : ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μC = m := by
      rw [integral_indicator hKm, integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => Nat.cast_nonneg _) hθrm.aestronglyMeasurable, hm, hμ,
        withDensity_apply _ hKm]
      simp only [ENNReal.ofReal_natCast, hθ]
    -- step 2: for every `η ∈ (0, 1)`, `(1 - η) μ(K) - η ≤ M_W(T)`
    have hη : ∀ η : ℝ, 0 < η → η < 1 → ENNReal.ofReal ((1 - η) * m - η) ≤ T.massOn W := by
      intro η hη0 hη1
      obtain ⟨g₀, hg₀m, hg₀1, hg₀η⟩ := Submission.regcomp_covector_field_near_maximizer P n μC
        R.orient η hη0 R.aestronglyMeasurable_orient (hpair.mono fun x hx => hx.2)
      set g : Euclid P → Covector (Euclid P) n := K.indicator g₀ with hg
      have hgm : StronglyMeasurable g := hg₀m.indicator hKm
      have hg0 : ∀ x, x ∉ K → g x = 0 := fun x hx => indicator_of_notMem hx _
      have hg1 : ∀ x, covectorEuclideanNorm (g x) ≤ 1 := by
        intro x
        by_cases hx : x ∈ K
        · rw [hg, indicator_of_mem hx]
          exact hg₀1 x
        · rw [hg0 x hx, covectorEuclideanNorm_zero]
          exact zero_le_one
      obtain ⟨h, hh, hhO, hh1, hhg⟩ := Submission.regcomp_exists_smooth_unit_form_approx P n
        (R.measure.restrict O) O K g hνfin isOpen_interior hK hKL hgm.aestronglyMeasurable hg1 hg0
        η hη0
      have hhL : tsupport h ⊆ L := hhO.trans hOL
      have hh0 : ∀ x, x ∉ L → h x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport fun hx' => hx (hhL hx')
      have hhc : Continuous h := hh.1.continuous
      -- the admissible test form `ω = h`
      let ω : TestFormOn U n := ⟨h, hh, hhL.trans hLU⟩
      have hωadm : ω ∈ massAdmissibleOn U n W := ⟨hhL.trans hLW, hh1⟩
      have hTω : T ω = ∫ x, (R.mult x : ℝ) * R.orient x (h x) ∂μC := hR ω
      -- integrability of `θ ⟨h, ξ⟩` and `θ ⟨g, ξ⟩`
      have hGi : Integrable (fun x => (R.mult x : ℝ) * R.orient x (h x)) μC := by
        refine hint _ (hθrm.aestronglyMeasurable.mul ((continuous_fst.clm_apply
          continuous_snd).comp_aestronglyMeasurable
            (R.aestronglyMeasurable_orient.prodMk hhc.aestronglyMeasurable))) ?_
        filter_upwards [hpair] with x hx
        exact hpt x hx.1 (h x) (hh1 x) (hh0 x)
      have hFi : Integrable (fun x => (R.mult x : ℝ) * R.orient x (g x)) μC := by
        refine hint _ (hθrm.aestronglyMeasurable.mul ((continuous_fst.clm_apply
          continuous_snd).comp_aestronglyMeasurable
            (R.aestronglyMeasurable_orient.prodMk hgm.aestronglyMeasurable))) ?_
        filter_upwards [hpair] with x hx
        exact hpt x hx.1 (g x) (hg1 x) fun hxL => hg0 x fun hxK => hxL (hKL' hxK)
      -- `∫ θ ⟨g, ξ⟩ dμC ≥ (1 - η) μ(K)`
      have hFlow : (1 - η) * m ≤ ∫ x, (R.mult x : ℝ) * R.orient x (g x) ∂μC := by
        rw [← hKint, ← integral_const_mul]
        refine integral_mono_ae (hKi.const_mul _) hFi ?_
        filter_upwards [hg₀η] with x hx
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK, hg, indicator_of_mem hxK, mul_comm]
          exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
        · rw [indicator_of_notMem hxK, hg0 x hxK, map_zero, mul_zero, mul_zero]
      -- `|∫ θ ⟨h - g, ξ⟩ dμC| < η`
      have hdiff : |∫ x, (R.mult x : ℝ) * R.orient x (h x) ∂μC -
          ∫ x, (R.mult x : ℝ) * R.orient x (g x) ∂μC| < η := by
        have hmeas : Measurable fun x => ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) :=
          (hnormc.comp_stronglyMeasurable
            (hhc.stronglyMeasurable.sub hgm)).measurable.ennreal_ofReal
        rw [← integral_sub hGi hFi, ← ENNReal.ofReal_lt_ofReal_iff hη0, ← Real.enorm_eq_ofReal_abs]
        calc ‖∫ x, ((R.mult x : ℝ) * R.orient x (h x) - (R.mult x : ℝ) * R.orient x (g x)) ∂μC‖ₑ
            ≤ ∫⁻ x, ‖(R.mult x : ℝ) * R.orient x (h x) - (R.mult x : ℝ) * R.orient x (g x)‖ₑ ∂μC :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ x, θ x * ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ∂μC := by
              refine lintegral_mono_ae ?_
              filter_upwards [hpair] with x hx
              rw [← mul_sub, ← map_sub, enorm_mul, Real.enorm_natCast, Real.enorm_eq_ofReal_abs]
              gcongr
              exact hx.1 _
          _ = ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ∂R.measure := by
              rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hθm hmeas]
              rfl
          _ = ∫⁻ x in O, ENNReal.ofReal (covectorEuclideanNorm (h x - g x)) ∂R.measure := by
              refine (setLIntegral_eq_of_support_subset fun x hx => ?_).symm
              by_contra hxO
              refine hx ?_
              dsimp only
              rw [image_eq_zero_of_notMem_tsupport fun hx' => hxO (hhO hx'),
                hg0 x fun hx' => hxO (hKL hx'), sub_zero, covectorEuclideanNorm_zero,
                ENNReal.ofReal_zero]
          _ < ENNReal.ofReal η := hhg
      have hTlow : (1 - η) * m - η ≤ T ω := by
        rw [hTω]
        have := (abs_lt.1 hdiff).1
        linarith
      exact (ENNReal.ofReal_le_ofReal hTlow).trans (T.le_massOn hωadm)
    -- step 3: let `η ↓ 0`
    have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal ((1 - η) * m - η)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal m)) := by
      have : Tendsto (fun η : ℝ => (1 - η) * m - η) (𝓝 0) (𝓝 ((1 - 0) * m - 0)) :=
        ((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).sub tendsto_id
      rw [sub_zero, sub_zero, one_mul] at this
      exact (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((1 - η) * m - η) ≤ T.massOn W := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with η hη'
      exact hη η hη'.1 hη'.2
    have := le_of_tendsto hlim hev
    rwa [hm, ENNReal.ofReal_toReal hμK] at this
  -- compact exhaustion of `W ∩ U`
  obtain ⟨F, hFc, hFsub, hFU, hFmono⟩ := (hW.inter hU).exists_iUnion_isClosed
  have hWU : R.measure (W ∩ U) ≤ T.massOn W := by
    have hexh : ⋃ j : ℕ, F j ∩ closedBall 0 j = W ∩ U := by
      refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFsub j)) ?_
      intro x hx
      rw [← hFU, mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := exists_nat_ge (max (i : ℝ) ‖x‖)
      refine mem_iUnion.2 ⟨j, hFmono (Nat.cast_le.1 ((le_max_left _ _).trans hj)) hi, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact (le_max_right _ _).trans hj
    have hmono : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
      inter_subset_inter (hFmono hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
    rw [← hexh, hmono.measure_iUnion]
    exact iSup_le fun j => hKey _ ((isCompact_closedBall 0 _).inter_left (hFc j))
      (inter_subset_left.trans (hFsub j))
  -- `μ` is carried by `U`
  have hUc : R.measure Uᶜ = 0 := by
    rw [hμ]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [hμC, Measure.restrict_apply' R.measurableSet_carrier,
      (disjoint_compl_left_iff_subset.2 R.carrier_subset).inter_eq, measure_empty]
  rw [← measure_inter_conull hUc]
  exact hWU

/-- **The mass formula for integer multiplicity currents** (Simon Ch. 6, Remark 3.2(3); mass
(6.2.5)): if `U ⊆ ℝᴾ` is open and `T = τ(C, θ, ξ)` in `U`, then for every open `W ⊆ ℝᴾ`
`M_W(T) = μ_T(W) = ∫_{C ∩ W} θ dHⁿ`, with the Euclidean coefficient norm `|·|_E` in `M_W`.

Step 2 of the proof gives `M_W(T) ≤ μ_T(W)` (`regcomp_imrep_massOn_le_measure`, which needs no
openness), and step 3 gives `μ_T(W) ≤ M_W(T)` for open `U`, `W`
(`regcomp_imrep_measure_le_massOn`).  Both values lie in `[0, ∞]`, so they are equal. -/
theorem Submission.regcomp_imrep_mass_formula : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := by
  intro P n U T R hU hR W hW
  -- step 2 `M_W(T) ≤ μ_T(W)` and step 3 `μ_T(W) ≤ M_W(T)`
  exact le_antisymm (Submission.regcomp_imrep_massOn_le_measure P n U T R hR W)
    (Submission.regcomp_imrep_measure_le_massOn P n U T R hU hR W hW)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
