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

/-- **Difference quotients and `C^{1,α}`** (Hölder form of the difference-quotient method,
Gilbarg–Trudinger §7.11).  If, for unit `v` and `0 < |t| < h₀`, the quotients
`t⁻¹ (f (x + t v) - f x)` are bounded by `C` and `α`-Hölder with constant `C` on `B = B_R(x₀)`,
then `f` is `C¹` on `B`, `‖Df‖ ≤ C` and `‖Df(x) - Df(y)‖ ≤ C ‖x - y‖^α`.
With `w = t v` the hypotheses say `‖f(x + w) - f(x)‖ ≤ C‖w‖` and
`‖f(x + w) - f(x) - (f(y + w) - f(y))‖ ≤ C‖w‖ ‖x - y‖^α` for `‖w‖ < h₀`; with `y = x + a` this
bounds the second differences of `f` at `x` by `C‖w‖ ‖a‖^α`.  The segment averages and coordinate
increments of the accepted proof are replaced by Hyers' dyadic limits (PNAS 27 (1941), 222–224):
consecutive quotients `2ⁿ(f(x + 2⁻ⁿw) - f(x))` differ by `2ⁿ` times a second difference with
increments `2⁻ⁿ⁻¹w`, of size `≤ (C/2)‖w‖^(1+α) ρⁿ⁺¹`, `ρ = 2^(-α) < 1`.  So they converge to some
`L w` with `‖f(x + w) - f(x) - L w‖ = O(‖w‖^(1+α))`.  `L` is additive (second differences vanish in
the limit) and `‖L w‖ ≤ C‖w‖`, so it is continuous linear and `Df(x) = L`.  The bounds `C` and
`C‖x - y‖^α` pass to the limit, and Hölder continuity of `Df` gives `C¹`.  Continuity of `f` is not
used: the first bound already makes `f` Lipschitz near each point of `B`. -/
theorem Submission.codim1_hcp_sr_difference_quotient : ∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → ∀ (f : Euclid m → (Euclid m →L[ℝ] Euclid k)) (x₀ : Euclid m) (R h₀ C : ℝ), 0 < R → 0 < h₀ → ContinuousOn f (ball x₀ R) → (∀ v : Euclid m, ‖v‖ = 1 → ∀ t : ℝ, t ≠ 0 → |t| < h₀ → (∀ x ∈ ball x₀ R, ‖t⁻¹ • (f (x + t • v) - f x)‖ ≤ C) ∧ ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖t⁻¹ • (f (x + t • v) - f x) - t⁻¹ • (f (y + t • v) - f y)‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 f (ball x₀ R) ∧ (∀ x ∈ ball x₀ R, ‖fderiv ℝ f x‖ ≤ C) ∧ ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ ^ α := by
  intro m k α hm hα f x₀ R h₀ C hR hh₀ _ hq
  -- the hypotheses in increment form, `w = t • v`
  have H : ∀ w : Euclid m, ‖w‖ < h₀ → (∀ x ∈ ball x₀ R, ‖f (x + w) - f x‖ ≤ C * ‖w‖) ∧
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
        ‖f (x + w) - f x - (f (y + w) - f y)‖ ≤ C * ‖w‖ * ‖x - y‖ ^ α := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hv : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hw' : ‖w‖ • ‖w‖⁻¹ • w = w := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    obtain ⟨h1, h2⟩ := hq _ hv ‖w‖ hn.ne' (by rwa [abs_norm])
    rw [hw'] at h1 h2
    refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · have := h1 x hx
      rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hn] at this
      linarith
    · have := h2 x hx y hy
      rw [← smul_sub (‖w‖⁻¹) (f (x + w) - f x) (f (y + w) - f y), norm_smul, norm_inv, norm_norm,
        inv_mul_le_iff₀ hn] at this
      exact this.trans (le_of_eq (by ring))
  -- `C ≥ 0`, tested on a unit vector
  have hC : 0 ≤ C := by
    have hv : ‖EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)‖ = 1 := by simp
    exact (norm_nonneg _).trans ((hq _ hv (h₀ / 2) (by positivity)
      (by rw [abs_of_pos (by positivity)]; linarith)).1 x₀ (mem_ball_self hR))
  -- dyadic scaling: `‖2⁻ⁿ w‖ = 2⁻ⁿ ‖w‖`, `‖2⁻ⁿ w‖ ^ α = ρⁿ ‖w‖ ^ α` with `ρ = 2^(-α) < 1`
  set ρ : ℝ := ((2 : ℝ) ^ α)⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hα)
  have h2n : ∀ n : ℕ, ‖(2 : ℝ) ^ n‖ = (2 : ℝ) ^ n := fun n => Real.norm_of_nonneg (by positivity)
  have hnorm : ∀ (n : ℕ) (w : Euclid m), ‖((2 : ℝ) ^ n)⁻¹ • w‖ = ((2 : ℝ) ^ n)⁻¹ * ‖w‖ :=
    fun n w => norm_smul_of_nonneg (by positivity) w
  have hpow : ∀ (n : ℕ) (w : Euclid m), ‖((2 : ℝ) ^ n)⁻¹ • w‖ ^ α = ρ ^ n * ‖w‖ ^ α := by
    intro n w
    rw [hnorm, Real.mul_rpow (by positivity) (norm_nonneg _), Real.inv_rpow (by positivity),
      ← Real.rpow_natCast_mul (by norm_num), mul_comm (n : ℝ) α,
      Real.rpow_mul_natCast (by norm_num), hρ, inv_pow]
  have hsmall : ∀ (w : Euclid m) (ε : ℝ), 0 < ε → ∀ᶠ n : ℕ in atTop, ‖((2 : ℝ) ^ n)⁻¹ • w‖ < ε := by
    intro w ε hε
    have h : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * ‖w‖) atTop (𝓝 (0 * ‖w‖)) :=
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).mul_const _
    rw [zero_mul] at h
    filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn
    rwa [hnorm]
  -- at each `x ∈ B`: the dyadic quotients `2ⁿ (f (x + 2⁻ⁿ w) - f x)` converge to `L w`, and
  -- `f` has derivative `L` at `x`
  have main : ∀ x ∈ ball x₀ R, ∃ L : Euclid m →L[ℝ] (Euclid m →L[ℝ] Euclid k), HasFDerivAt f L x ∧
      (∀ w, ‖L w‖ ≤ C * ‖w‖) ∧
      ∀ w, Tendsto (fun n : ℕ => (2 : ℝ) ^ n • (f (x + ((2 : ℝ) ^ n)⁻¹ • w) - f x)) atTop
        (𝓝 (L w)) := by
    intro x hx
    set r := min h₀ (R - dist x x₀) with hr
    have hr0 : 0 < r := lt_min hh₀ (sub_pos.2 (mem_ball.1 hx))
    have hrh : r ≤ h₀ := min_le_left _ _
    have hrB : ∀ a : Euclid m, ‖a‖ < r → x + a ∈ ball x₀ R := by
      intro a ha
      rw [mem_ball]
      calc dist (x + a) x₀ ≤ dist (x + a) x + dist x x₀ := dist_triangle _ _ _
        _ = ‖a‖ + dist x x₀ := by rw [dist_eq_norm, add_sub_cancel_left]
        _ < R := by linarith [min_le_right h₀ (R - dist x x₀)]
    -- increments `Φ w = f (x + w) - f x` and their second differences
    set Φ : Euclid m → (Euclid m →L[ℝ] Euclid k) := fun w => f (x + w) - f x with hΦ
    have hS : ∀ a b : Euclid m, ‖a‖ < r → ‖b‖ < h₀ →
        ‖Φ (a + b) - Φ a - Φ b‖ ≤ C * ‖b‖ * ‖a‖ ^ α := by
      intro a b ha hb
      have h := (H b hb).2 (x + a) (hrB a ha) x hx
      rw [add_sub_cancel_left] at h
      convert h using 2
      simp only [hΦ, add_assoc]
      abel
    -- the dyadic quotients `u w n = 2ⁿ Φ (2⁻ⁿ w)`
    set u : Euclid m → ℕ → (Euclid m →L[ℝ] Euclid k) :=
      fun w n => (2 : ℝ) ^ n • Φ (((2 : ℝ) ^ n)⁻¹ • w) with hu
    -- `u w n - u w (n + 1) = 2ⁿ (Φ (2w') - 2 Φ w')`, `w' = 2⁻ⁿ⁻¹ w`: a geometric Cauchy estimate
    have hgeo : ∀ w : Euclid m, ‖w‖ < r → ∀ n : ℕ,
        dist (u w n) (u w (n + 1)) ≤ (C / 2 * ‖w‖ * ‖w‖ ^ α * ρ) * ρ ^ n := by
      intro w hw n
      have hw'w : ‖((2 : ℝ) ^ (n + 1))⁻¹ • w‖ ≤ ‖w‖ := by
        rw [hnorm]
        exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))
      have h2 : ((2 : ℝ) ^ n)⁻¹ • w = ((2 : ℝ) ^ (n + 1))⁻¹ • w + ((2 : ℝ) ^ (n + 1))⁻¹ • w := by
        rw [← add_smul]; congr 1; rw [pow_succ]; field_simp; ring
      have hdiff : u w n - u w (n + 1) = (2 : ℝ) ^ n • (Φ (((2 : ℝ) ^ (n + 1))⁻¹ • w +
          ((2 : ℝ) ^ (n + 1))⁻¹ • w) - Φ (((2 : ℝ) ^ (n + 1))⁻¹ • w) -
          Φ (((2 : ℝ) ^ (n + 1))⁻¹ • w)) := by
        simp only [hu]
        rw [h2]
        module
      rw [dist_eq_norm, hdiff, norm_smul, h2n]
      calc (2 : ℝ) ^ n * ‖Φ (((2 : ℝ) ^ (n + 1))⁻¹ • w + ((2 : ℝ) ^ (n + 1))⁻¹ • w) -
            Φ (((2 : ℝ) ^ (n + 1))⁻¹ • w) - Φ (((2 : ℝ) ^ (n + 1))⁻¹ • w)‖
          ≤ (2 : ℝ) ^ n * (C * ‖((2 : ℝ) ^ (n + 1))⁻¹ • w‖ * ‖((2 : ℝ) ^ (n + 1))⁻¹ • w‖ ^ α) :=
            mul_le_mul_of_nonneg_left (hS _ _ (hw'w.trans_lt hw)
              ((hw'w.trans_lt hw).trans_le hrh)) (by positivity)
        _ = (C / 2 * ‖w‖ * ‖w‖ ^ α * ρ) * ρ ^ n := by
            rw [hpow, hnorm]; field_simp; ring
    -- for small `w` the limit exists and is within `O(‖w‖ ^ (1 + α))` of `Φ w`
    have hlim0 : ∀ w : Euclid m, ‖w‖ < r → ∃ a, Tendsto (u w) atTop (𝓝 a) ∧
        ‖Φ w - a‖ ≤ C / 2 * ‖w‖ * ‖w‖ ^ α * ρ / (1 - ρ) := by
      intro w hw
      obtain ⟨a, ha⟩ :=
        cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ρ _ hρ1 (hgeo w hw))
      refine ⟨a, ha, ?_⟩
      have h := dist_le_of_le_geometric_of_tendsto₀ ρ _ hρ1 (hgeo w hw) ha
      have hu0 : u w 0 = Φ w := by simp [hu]
      rwa [dist_eq_norm, hu0] at h
    -- for every `w`: `u w (n + N) = 2ᴺ u (2⁻ᴺ w) n`
    have hlim : ∀ w : Euclid m, ∃ a, Tendsto (u w) atTop (𝓝 a) := by
      intro w
      obtain ⟨N, hN⟩ := (hsmall w r hr0).exists
      obtain ⟨a, ha, -⟩ := hlim0 _ hN
      refine ⟨(2 : ℝ) ^ N • a, (tendsto_add_atTop_iff_nat N).1 ?_⟩
      have e : ∀ n, u w (n + N) = (2 : ℝ) ^ N • u (((2 : ℝ) ^ N)⁻¹ • w) n := by
        intro n
        have e1 : ((2 : ℝ) ^ (n + N))⁻¹ • w = ((2 : ℝ) ^ n)⁻¹ • ((2 : ℝ) ^ N)⁻¹ • w := by
          rw [smul_smul, pow_add, mul_inv]
        simp only [hu]
        rw [e1, smul_smul, pow_add, mul_comm ((2 : ℝ) ^ n), mul_smul]
      simp_rw [e]
      exact ha.const_smul _
    choose Lf hLf using hlim
    -- `Lf` is additive: second differences of `u` vanish in the limit
    have hadd : ∀ a b, Lf (a + b) = Lf a + Lf b := by
      intro a b
      have h1 : Tendsto (fun n => u (a + b) n - u a n - u b n) atTop
          (𝓝 (Lf (a + b) - Lf a - Lf b)) := ((hLf _).sub (hLf _)).sub (hLf _)
      have h2 : Tendsto (fun n => u (a + b) n - u a n - u b n) atTop (𝓝 0) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        simp only [sub_zero]
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
          (g := fun n => C * ‖b‖ * (ρ ^ n * ‖a‖ ^ α)) ?_
        · filter_upwards [hsmall a r hr0, hsmall b h₀ hh₀] with n ha hb
          have e : u (a + b) n - u a n - u b n = (2 : ℝ) ^ n • (Φ (((2 : ℝ) ^ n)⁻¹ • a +
              ((2 : ℝ) ^ n)⁻¹ • b) - Φ (((2 : ℝ) ^ n)⁻¹ • a) - Φ (((2 : ℝ) ^ n)⁻¹ • b)) := by
            simp only [hu, smul_add]
            module
          rw [e, norm_smul, h2n]
          calc (2 : ℝ) ^ n * ‖Φ (((2 : ℝ) ^ n)⁻¹ • a + ((2 : ℝ) ^ n)⁻¹ • b) -
                Φ (((2 : ℝ) ^ n)⁻¹ • a) - Φ (((2 : ℝ) ^ n)⁻¹ • b)‖
              ≤ (2 : ℝ) ^ n * (C * ‖((2 : ℝ) ^ n)⁻¹ • b‖ * ‖((2 : ℝ) ^ n)⁻¹ • a‖ ^ α) :=
                mul_le_mul_of_nonneg_left (hS _ _ ha hb) (by positivity)
            _ = C * ‖b‖ * (ρ ^ n * ‖a‖ ^ α) := by rw [hpow, hnorm]; field_simp
        · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (‖a‖ ^ α)).const_mul
            (C * ‖b‖)
          rwa [zero_mul, mul_zero] at h
      have h := tendsto_nhds_unique h1 h2
      rwa [sub_sub, sub_eq_zero] at h
    -- `‖Lf w‖ ≤ C ‖w‖`
    have hbd : ∀ w, ‖Lf w‖ ≤ C * ‖w‖ := by
      intro w
      refine le_of_tendsto (hLf w).norm ?_
      filter_upwards [hsmall w h₀ hh₀] with n hn
      simp only [hu]
      rw [norm_smul, h2n]
      calc (2 : ℝ) ^ n * ‖Φ (((2 : ℝ) ^ n)⁻¹ • w)‖
          ≤ (2 : ℝ) ^ n * (C * ‖((2 : ℝ) ^ n)⁻¹ • w‖) :=
            mul_le_mul_of_nonneg_left ((H _ hn).1 x hx) (by positivity)
        _ = C * ‖w‖ := by rw [hnorm]; field_simp
    -- the continuous linear map
    let Lm : Euclid m →+ (Euclid m →L[ℝ] Euclid k) := AddMonoidHom.mk' Lf hadd
    have hLc : Continuous Lm := AddMonoidHomClass.continuous_of_bound Lm C hbd
    refine ⟨Lm.toRealLinearMap hLc, ?_, hbd, hLf⟩
    -- differentiability: `‖Φ w - Lf w‖ ≤ K ‖w‖ ^ α ‖w‖` for small `w`
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have hK : Tendsto (fun w : Euclid m => C / 2 * ρ / (1 - ρ) * ‖w‖ ^ α) (𝓝 0) (𝓝 0) := by
      have h := ((continuous_norm.rpow_const (fun _ => Or.inr hα.le)).tendsto
        (0 : Euclid m)).const_mul (C / 2 * ρ / (1 - ρ))
      rwa [norm_zero, Real.zero_rpow hα.ne', mul_zero] at h
    filter_upwards [hK.eventually (ge_mem_nhds hε), ball_mem_nhds (0 : Euclid m) hr0] with w hw hwr
    rw [mem_ball_zero_iff] at hwr
    obtain ⟨a, ha, hab⟩ := hlim0 w hwr
    have hae : a = Lf w := tendsto_nhds_unique ha (hLf w)
    calc ‖f (x + w) - f x - (Lm.toRealLinearMap hLc) w‖ = ‖Φ w - a‖ := by rw [hae]; rfl
      _ ≤ C / 2 * ‖w‖ * ‖w‖ ^ α * ρ / (1 - ρ) := hab
      _ = (C / 2 * ρ / (1 - ρ) * ‖w‖ ^ α) * ‖w‖ := by ring
      _ ≤ ε * ‖w‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
  choose! L hL hLb hLt using main
  have hfd : ∀ x ∈ ball x₀ R, fderiv ℝ f x = L x := fun x hx => (hL x hx).fderiv
  -- the α-Hölder bound passes to the limit of the dyadic quotients
  have hhold : ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ w,
      ‖(L x - L y) w‖ ≤ C * ‖x - y‖ ^ α * ‖w‖ := by
    intro x hx y hy w
    rw [sub_apply]
    refine le_of_tendsto ((hLt x hx w).sub (hLt y hy w)).norm ?_
    filter_upwards [hsmall w h₀ hh₀] with n hn
    rw [← smul_sub ((2 : ℝ) ^ n) (f (x + ((2 : ℝ) ^ n)⁻¹ • w) - f x)
      (f (y + ((2 : ℝ) ^ n)⁻¹ • w) - f y), norm_smul, h2n]
    calc (2 : ℝ) ^ n * ‖f (x + ((2 : ℝ) ^ n)⁻¹ • w) - f x - (f (y + ((2 : ℝ) ^ n)⁻¹ • w) - f y)‖
        ≤ (2 : ℝ) ^ n * (C * ‖((2 : ℝ) ^ n)⁻¹ • w‖ * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left ((H _ hn).2 x hx y hy) (by positivity)
      _ = C * ‖x - y‖ ^ α * ‖w‖ := by rw [hnorm]; field_simp
  refine ⟨?_, fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball,
      contDiffOn_zero]
    refine ⟨fun x hx => (hL x hx).differentiableAt.differentiableWithinAt, by simp, fun x hx => ?_⟩
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (g := fun y => C * ‖y - x‖ ^ α) ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [hfd y hy, hfd x hx]
      exact ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)) (hhold y hy x hx)
    · have hc : Continuous fun y : Euclid m => C * ‖y - x‖ ^ α :=
        continuous_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const
          fun _ => Or.inr hα.le)
      have h := hc.tendsto x
      rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  · rw [hfd x hx]
    exact ContinuousLinearMap.opNorm_le_bound _ hC (hLb x hx)
  · rw [hfd x hx, hfd y hy]
    exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
      (hhold x hx y hy)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
