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

/-- Fubini–Tonelli on the cylinder `Â = {z ∈ ℝ^{n+1} : z₀ ∈ (0, 1), tail z ∈ A}` for Borel
`A ⊆ ℝⁿ`.  The map `e(u, t) = (t, u₁, …, uₙ)`, the composite of the swap `ℝⁿ × ℝ ≃ ℝ × ℝⁿ`,
`id × ofLp`, the inverse of `piFinSuccAbove · 0` (i.e. `Fin.cons`) and `toLp`, is a
measure-preserving measurable equivalence `ℝⁿ × ℝ ≃ᵐ ℝ^{n+1}` with `e⁻¹(Â) = A × (0, 1)`.  Hence
`Â` is Borel, and change of variables along `e` followed by Tonelli (resp. Fubini) on the product
set `A × (0, 1)` gives the iterated lower Lebesgue (resp. Bochner) integrals. -/
theorem Submission.cmcdt_lpi_cyl_fubini : ∀ (n : ℕ) (A : Set (Euclid n)), MeasurableSet A → MeasurableSet {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} ∧ (∀ f : Euclid (n + 1) → ℝ≥0∞, Measurable f → ∫⁻ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))) ∧ ∀ f : Euclid (n + 1) → ℝ, IntegrableOn f {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → ∫ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫ u in A, ∫ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) := by
  intro n A hA
  set Ah := {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
    (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} with hAh_def
  -- the measurable equivalence `e : ℝⁿ × ℝ ≃ᵐ ℝ^{n+1}`, `(u, t) ↦ (t, u)`
  let e : (Euclid n × ℝ) ≃ᵐ Euclid (n + 1) :=
    (MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm)).trans
      (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))
  have he : ∀ p : Euclid n × ℝ, e p = WithLp.toLp 2 (Fin.cons p.2 (WithLp.ofLp p.1)) := by
    rintro ⟨u, t⟩
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    exact ⟨rfl, rfl⟩
  -- each factor of `e` preserves Lebesgue measure
  have hmp : MeasurePreserving e volume volume := by
    have h1 : MeasurePreserving
        (MeasurableEquiv.prodComm : (Euclid n × ℝ) ≃ᵐ (ℝ × Euclid n)) volume volume :=
      Measure.measurePreserving_swap
    have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm) volume volume :=
      (MeasurePreserving.id volume).prod
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))
    have h3 : MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
    have h4 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)) volume volume := by
      have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))).symm _
      simpa using this
    exact h4.comp (h3.comp (h2.comp h1))
  -- `e⁻¹(Â) = A × (0, 1)`
  have hpre : e ⁻¹' Ah = A ×ˢ Ioo (0 : ℝ) 1 := by
    ext ⟨u, t⟩
    simp [Ah, he, and_comm]
  have hAhm : MeasurableSet Ah := by
    have : Ah = e.symm ⁻¹' (A ×ˢ Ioo (0 : ℝ) 1) := by
      rw [← hpre]; ext z; simp
    rw [this]
    exact e.symm.measurable (hA.prod measurableSet_Ioo)
  refine ⟨hAhm, ?_, ?_⟩
  · intro f hf
    rw [← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding f Ah, hpre]
    rw [Measure.volume_eq_prod, setLIntegral_prod]
    · simp only [he]
    · exact (hf.comp e.measurable).aemeasurable
  · intro f hf
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding f Ah, hpre]
    rw [Measure.volume_eq_prod, setIntegral_prod]
    · simp only [he]
    · rw [← Measure.volume_eq_prod, ← hpre]
      exact (hmp.integrableOn_comp_preimage e.measurableEmbedding).2 hf
/-- The radial retraction onto the closed ball `B̄ = {z : ‖z‖ ≤ ρ}` of `ℝᴾ`, `r(y) = y` for
`‖y‖ ≤ ρ` and `r(y) = (ρ/‖y‖)•y` otherwise, maps `ℝᴾ` into `B̄`, fixes `B̄` and is 1-Lipschitz.
It is the nearest-point projection onto `B̄`: `⟪x - r x, z - r x⟫ ≤ 0` for `z ∈ B̄`, since
`x - r x` is a nonnegative multiple of `x` and `⟪x, z⟫ ≤ ρ‖x‖ = ⟪x, r x⟫`.  Adding these
inequalities for `(x, z) = (x, r y)` and `(y, r x)` gives
`‖r x - r y‖² ≤ ⟪x - y, r x - r y⟫ ≤ ‖x - y‖ ‖r x - r y‖`. -/
theorem Submission.ecf_cp_ball_retraction : ∀ (P : ℕ) (ρ : ℝ), 0 < ρ → ∃ r : Euclid P → Euclid P, LipschitzWith 1 r ∧ (∀ y, ‖r y‖ ≤ ρ) ∧ ∀ y, ‖y‖ ≤ ρ → r y = y := by
  intro P ρ hρ
  -- `r y = y` on the ball `‖y‖ ≤ ρ` and `r y = (ρ / ‖y‖) • y` outside it
  obtain ⟨r, hr_in, hr_out⟩ : ∃ r : Euclid P → Euclid P, (∀ y, ‖y‖ ≤ ρ → r y = y) ∧
      ∀ y, ρ < ‖y‖ → r y = (ρ / ‖y‖) • y :=
    ⟨fun y => if ‖y‖ ≤ ρ then y else (ρ / ‖y‖) • y, fun y hy => ite_eq_left hy,
      fun y hy => ite_eq_right (not_le.mpr hy)⟩
  -- `‖r y‖ ≤ ρ`: outside the ball, `‖r y‖ = (ρ / ‖y‖) * ‖y‖ = ρ`
  have hr_le : ∀ y, ‖r y‖ ≤ ρ := by
    intro y
    rcases le_or_gt ‖y‖ ρ with hy | hy
    · rw [hr_in y hy]
      exact hy
    · have hy0 : 0 < ‖y‖ := hρ.trans hy
      rw [hr_out y hy, norm_smul_of_nonneg (div_nonneg hρ.le hy0.le), div_mul_cancel₀ _ hy0.ne']
  -- variational inequality `⟪x - r x, z - r x⟫ ≤ 0` for `‖z‖ ≤ ρ`
  have hvar : ∀ x z : Euclid P, ‖z‖ ≤ ρ → inner ℝ (x - r x) (z - r x) ≤ 0 := by
    intro x z hz
    rcases le_or_gt ‖x‖ ρ with hx | hx
    · rw [hr_in x hx, sub_self, inner_zero_left]
    · have hx0 : 0 < ‖x‖ := hρ.trans hx
      have hc : 0 ≤ 1 - ρ / ‖x‖ := by
        rw [sub_nonneg, div_le_one hx0]
        exact hx.le
      -- `x - r x = (1 - ρ / ‖x‖) • x` and `⟪x, z⟫ ≤ ρ ‖x‖ = ⟪x, r x⟫`
      have hxz : inner ℝ x z ≤ ρ * ‖x‖ :=
        calc inner ℝ x z ≤ ‖x‖ * ‖z‖ := real_inner_le_norm x z
          _ ≤ ‖x‖ * ρ := by gcongr
          _ = ρ * ‖x‖ := mul_comm _ _
      have hxx : ρ / ‖x‖ * ‖x‖ ^ 2 = ρ * ‖x‖ := by
        field_simp
      rw [hr_out x hx, show x - (ρ / ‖x‖) • x = (1 - ρ / ‖x‖) • x by rw [sub_smul, one_smul],
        real_inner_smul_left, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
        hxx]
      exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
  refine ⟨r, LipschitzWith.mk_one fun x y => ?_, hr_le, hr_in⟩
  rw [dist_eq_norm, dist_eq_norm]
  -- adding the variational inequalities for `(x, r y)` and `(y, r x)`
  have h1 := hvar x (r y) (hr_le y)
  have h2 := hvar y (r x) (hr_le x)
  have hkey : ‖r x - r y‖ ^ 2 ≤ inner ℝ (x - y) (r x - r y) := by
    have e : inner ℝ (x - y) (r x - r y) = ‖r x - r y‖ ^ 2 - inner ℝ (x - r x) (r y - r x)
        - inner ℝ (y - r y) (r x - r y) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  -- Cauchy–Schwarz, then cancel `‖r x - r y‖` (the case `r x = r y` is trivial)
  have hcs : inner ℝ (x - y) (r x - r y) ≤ ‖x - y‖ * ‖r x - r y‖ := real_inner_le_norm _ _
  nlinarith [norm_nonneg (r x - r y), norm_nonneg (x - y)]
/-- **Gram determinant of a scaled cone frame** (the cone Jacobian behind Simon 6.2.30 and 6.3.10
for `h(t, x) = t x`).  For `a ∈ ℝᴾ`, `w = (w₀, …, w_{k-1})` and every real `t`,
`Γ(a, t w) = (tᵏ)² Γ(a, w)`, where `Γ(v) = det (⟨vᵢ, vⱼ⟩)ᵢⱼ`.  With `d = (1, t, …, t)` and
`D = diag d`, `(a, t w)ₗ = dₗ (a, w)ₗ`, so bilinearity of the inner product gives
`M(a, t w) = D M(a, w) D` for the Gram matrices, and `det D = ∏ₗ dₗ = tᵏ`. -/
theorem Submission.ecf_cp_gc_det_smul : ∀ (P k : ℕ) (a : Euclid P) (w : Fin k → Euclid P) (t : ℝ), Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) i) ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) j)) = (t ^ k) ^ 2 * Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i) ((Fin.cons a w : Fin (k + 1) → Euclid P) j)) := by
  intro P k a w t
  -- Step 1: with `d = (1, t, …, t)`, `(a, t • w)_l = d_l • (a, w)_l` for every `l`
  let d : Fin (k + 1) → ℝ := Fin.cons 1 fun _ => t
  have hscale : ∀ l : Fin (k + 1), (Fin.cons a (t • w) : Fin (k + 1) → Euclid P) l =
      d l • (Fin.cons a w : Fin (k + 1) → Euclid P) l := by
    intro l
    refine Fin.cases ?_ (fun i => ?_) l
    · simp only [d, Fin.cons_zero, one_smul]
    · simp only [d, Fin.cons_succ, Pi.smul_apply]
  -- Step 2: `M(a, t • w) = D * M(a, w) * D` with `D = diagonal d`, by bilinearity
  have hcong : (Matrix.of fun i j : Fin (k + 1) =>
        inner ℝ ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) i)
          ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) j)) =
      Matrix.diagonal d * (Matrix.of fun i j : Fin (k + 1) =>
        inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i)
          ((Fin.cons a w : Fin (k + 1) → Euclid P) j)) * Matrix.diagonal d := by
    ext l m
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    rw [hscale l, hscale m, real_inner_smul_left, real_inner_smul_right]
    ring
  -- Step 3: `det D = ∏ₗ dₗ = d₀ * ∏_{i < k} t = tᵏ`
  have hD : (Matrix.diagonal d).det = t ^ k := by
    rw [Matrix.det_diagonal, Fin.prod_univ_succ]
    simp only [d, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_fin, one_mul]
  -- Step 4: `Γ(a, t • w) = tᵏ * Γ(a, w) * tᵏ = (tᵏ)² * Γ(a, w)`
  rw [hcong, Matrix.det_mul, Matrix.det_mul, hD]
  ring
/-- Shear invariance of the Gram determinant: `Γ(a − Σₗ cₗwₗ, w) = Γ(a, w)`, where
`Γ(v) = det (⟨vᵢ, vⱼ⟩)ᵢⱼ` and `(x, w) = (x, w₀, …, w_{k−1})`.  Let `E` be the matrix whose column
`0` is `(1, −c₀, …, −c_{k−1})` and whose other columns are those of the identity.  Then
`(a − Σₗ cₗwₗ, w)ⱼ = Σₗ Eₗⱼ (a, w)ₗ`, so by bilinearity `M(a − Σₗ cₗwₗ, w) = Eᵀ M(a, w) E`; `E` is
lower triangular with unit diagonal, so `det E = 1`. -/
theorem Submission.ecf_cp_gc_det_shear : ∀ (P k : ℕ) (a : Euclid P) (w : Fin k → Euclid P) (c : Fin k → ℝ), Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons (a - ∑ l, c l • w l) w : Fin (k + 1) → Euclid P) i) ((Fin.cons (a - ∑ l, c l • w l) w : Fin (k + 1) → Euclid P) j)) = Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i) ((Fin.cons a w : Fin (k + 1) → Euclid P) j)) := by
  intro P k a w c
  set v : Fin (k + 1) → Euclid P := Fin.cons a w
  -- column `0` of `E` is `(1, -c₀, …, -c_{k-1})`, the other columns are those of the identity
  set E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := Matrix.of fun l j =>
    if j = 0 then (Fin.cons 1 (-c) : Fin (k + 1) → ℝ) l else if l = j then 1 else 0
  -- `(a - ∑ c_l w_l, w)` is `v` recombined by the columns of `E`
  have hcomb : ∀ j, (Fin.cons (a - ∑ l, c l • w l) w : Fin (k + 1) → Euclid P) j =
      ∑ l, E l j • v l := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [E, v, Fin.sum_univ_succ, sub_eq_add_neg, neg_smul]
    · simp [E, v, Fin.succ_ne_zero]
  -- `E` is lower triangular with unit diagonal
  have hdetE : E.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular E fun l j hlj => ?_]
    · refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = 0 <;> simp [E, hi]
    · have hlj' : l < j := OrderDual.toDual_lt_toDual.mp hlj
      have hj : j ≠ 0 := ((Fin.zero_le l).trans_lt hlj').ne'
      simp [E, hj, hlj'.ne]
  -- bilinearity: `M(a - ∑ c_l w_l, w) = Eᵀ M(a, w) E`
  calc _ = (E.transpose * (Matrix.of fun i j : Fin (k + 1) => inner ℝ (v i) (v j)) * E).det := by
        congr 1
        ext i j
        simp only [Matrix.of_apply, hcomb, sum_inner, inner_sum, real_inner_smul_left,
          real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetE, one_mul, mul_one]
/-- If `b` is orthogonal to every `w j`, the Gram determinant of `(b, w 0, …, w (k - 1))` is
`‖b‖²` times that of `w`.  Row 0 of the Gram matrix `M` is `(‖b‖², 0, …, 0)`, so the Laplace
expansion along row 0 leaves only `‖b‖² · det (M.submatrix Fin.succ Fin.succ)`, and this minor
is the Gram matrix of `w` (for `k = 0` it is the empty matrix, of determinant `1`). -/
theorem Submission.ecf_cp_gc_det_orth : ∀ (P k : ℕ) (b : Euclid P) (w : Fin k → Euclid P), (∀ j : Fin k, inner ℝ b (w j) = 0) → Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons b w : Fin (k + 1) → Euclid P) i) ((Fin.cons b w : Fin (k + 1) → Euclid P) j)) = ‖b‖ ^ 2 * Matrix.det (Matrix.of fun i j : Fin k => inner ℝ (w i) (w j)) := by
  intro P k b w hbw
  -- Laplace expansion along row 0, with the `j = 0` term split off
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  -- `M 0 0 = ‖b‖²` and `M 0 (j + 1) = ⟪b, w j⟫ = 0`, so only the `j = 0` term survives
  simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hbw, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
    real_inner_self_eq_norm_sq]
  -- the `j = 0` minor `M.submatrix Fin.succ Fin.succ` has entries `⟪w i, w j⟫` (`Fin.cons_succ`)
  rfl
/-- **Orthogonal residual against a finite family.**  For `a ∈ ℝᴾ` and any `w₀, …, w_{k-1} ∈ ℝᴾ`
(not necessarily independent) there are `c₀, …, c_{k-1} ∈ ℝ` such that `a' = a - ∑ₗ cₗ wₗ` is
orthogonal to every `w_j` and `‖a'‖ ≤ ‖a‖`.  Take `∑ₗ cₗ wₗ = π a` for the orthogonal projection
`π` onto the (finite-dimensional, hence complete) span `W` of the `wₗ`: then `a - π a ⊥ W`, and
Pythagoras for `a = (a - π a) + π a` gives `‖a - π a‖² ≤ ‖a‖²`. -/
theorem Submission.ecf_cp_gc_orth_residual : ∀ (P k : ℕ) (a : Euclid P) (w : Fin k → Euclid P), ∃ c : Fin k → ℝ, (∀ j : Fin k, inner ℝ (a - ∑ l, c l • w l) (w j) = 0) ∧ ‖a - ∑ l, c l • w l‖ ≤ ‖a‖ := by
  intro P k a w
  -- `π a ∈ W = span (range w)` is a linear combination `∑ₗ cₗ wₗ`
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((Submodule.span ℝ (range w)).starProjection_apply_mem a)
  refine ⟨c, fun j => ?_, ?_⟩
  · -- `a - π a ⊥ w_j`, since `w_j ∈ W`
    rw [hc]
    exact Submodule.starProjection_inner_eq_zero a (w j) (Submodule.subset_span (mem_range_self j))
  · -- Pythagoras: `‖a‖² = ‖a - π a‖² + ‖π a‖²`
    rw [hc]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.starProjection_inner_eq_zero a _
        ((Submodule.span ℝ (range w)).starProjection_apply_mem a))
    rw [sub_add_cancel] at hp
    rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), hp]
    exact le_add_of_nonneg_right (mul_self_nonneg _)

/-- The cone Jacobian (Simon 6.2.30, 6.3.10 for `h(t, x) = t x`).  Write `Γ(v) = det[⟨vᵢ, vⱼ⟩]`
for the Gram determinant of a family `v`, `J = √Γ`, and `(a, w) = Fin.cons a w`.
(i) `Γ(a, t·w) = (tᵏ)²·Γ(a, w)`, so `J(a, t·w) = tᵏ·J(a, w)` for `t ≥ 0`.
(ii) For the residual `a' = a - ∑ cₗ wₗ` of `a` orthogonal to every `wⱼ`, with `‖a'‖ ≤ ‖a‖`, shear
invariance and the orthogonal block formula give `Γ(a, w) = Γ(a', w) = ‖a'‖²·Γ(w)`, so
`J(a, w) = ‖a'‖·J(w) ≤ ‖a‖·J(w)`.  No independence of `w` is needed. -/
theorem Submission.ecf_cp_gram_cone : ∀ (P k : ℕ) (a : Euclid P) (w : Fin k → Euclid P), (∀ t : ℝ, 0 ≤ t → Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) i) ((Fin.cons a (t • w) : Fin (k + 1) → Euclid P) j))) = t ^ k * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i) ((Fin.cons a w : Fin (k + 1) → Euclid P) j)))) ∧ Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (k + 1) => inner ℝ ((Fin.cons a w : Fin (k + 1) → Euclid P) i) ((Fin.cons a w : Fin (k + 1) → Euclid P) j))) ≤ ‖a‖ * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin k => inner ℝ (w i) (w j))) := by
  intro P k a w
  refine ⟨fun t ht => ?_, ?_⟩
  · -- (i): `√((tᵏ)²·Γ) = √((tᵏ)²)·√Γ = tᵏ·√Γ`, as `tᵏ ≥ 0`
    have h := congrArg Real.sqrt (Submission.ecf_cp_gc_det_smul P k a w t)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg ht k)] at h
    exact h
  · -- (ii): `Γ(a, w) = Γ(a', w) = ‖a'‖²·Γ(w)`, then `√(‖a'‖²·Γ(w)) = ‖a'‖·√Γ(w)`
    obtain ⟨c, horth, hle⟩ := Submission.ecf_cp_gc_orth_residual P k a w
    have h := congrArg Real.sqrt ((Submission.ecf_cp_gc_det_shear P k a w c).symm.trans
      (Submission.ecf_cp_gc_det_orth P k _ w horth))
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
    exact h.trans_le (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _))

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
