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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
