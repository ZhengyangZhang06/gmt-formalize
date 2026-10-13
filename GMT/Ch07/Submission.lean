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

/-- **Fibre sums of `Hⁿ`-a.e. equal weights agree `Lⁿ`-a.e.** (Simon Ch. 2, 1.8(i): Lipschitz
images of `Hⁿ`-null sets are `Hⁿ`-null).  Let `S ⊆ V`, `F = G` on `V` with `G` Lipschitz, and
`h = h'` `Hⁿ⌞S`-a.e.  Enlarge `{h ≠ h'}` to a Borel `Hⁿ⌞S`-null set `N`; then `Hⁿ(N ∩ S) = 0`, so
`F(N ∩ S) = G(N ∩ S)` is `Hⁿ = Lⁿ`-null.  For `y ∉ F(N ∩ S)` every `x ∈ S` with `F(x) = y` lies
outside `N`, so `h(x) = h'(x)` and the fibre sums `Σ_{x ∈ S, F(x) = y}` of `h` and `h'` agree. -/
theorem Submission.idtp_caf_paf_fiberSum_ae_congr : ∀ (P n : ℕ) (S V : Set (Euclid P)) (F G : Euclid P → Euclid n) (LG : NNReal) (h h' : Euclid P → ℝ≥0∞), S ⊆ V → LipschitzWith LG G → EqOn F G V → h =ᵐ[μHE[n].restrict S] h' → (fun y : Euclid n => ∑' x : ↥(S ∩ F ⁻¹' {y}), h x) =ᵐ[volume] (fun y : Euclid n => ∑' x : ↥(S ∩ F ⁻¹' {y}), h' x) := by
  intro P n S V F G LG h h' hSV hG hFG hh
  -- a Borel `Hⁿ⌞S`-null set `N ⊇ {h ≠ h'}`; then `Hⁿ(N ∩ S) = 0`
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hh)
  rw [Measure.restrict_apply hNmeas] at hN0
  -- `F(N ∩ S) = G(N ∩ S)` is `Hⁿ`-null (Lipschitz image), i.e. `Lⁿ`-null
  have hFG' : F '' (N ∩ S) = G '' (N ∩ S) := image_congr fun x hx => hFG (hSV hx.2)
  have hM : volume (F '' (N ∩ S)) = 0 := by
    rw [hFG', ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    refine le_antisymm ?_ zero_le
    calc μHE[n] (G '' (N ∩ S)) ≤ (LG : ℝ≥0∞) ^ n * μHE[n] (N ∩ S) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hG.lipschitzOnWith
      _ = 0 := by rw [hN0, mul_zero]
  -- off `F(N ∩ S)` every fibre point lies outside `N`, where `h = h'`
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hM] with y hy
  refine tsum_congr fun x => ?_
  by_contra hne
  exact hy ⟨x, ⟨hNsub hne, x.2.1⟩, x.2.2⟩
/-- **Weighted area formula, fibre side** (Simon Ch. 2, §3, (3.4)–(3.5), for the Lipschitz map
`Φ : ℝⁿ → ℝⁿ`).  Let `g` be continuous and injective on the Borel set `A`, let `F ∘ g = Φ` on `A`
with `Φ` Lipschitz, and let `h ≥ 0` be Borel.  Then `y ↦ Σ_{x ∈ g(A), F(x) = y} h(x)` is
`Lⁿ`-a.e. measurable and its integral is `∫_A |det DΦ(a)| h(g(a)) dLⁿ(a)`.  The carrier fibre
over `y` is `g(A ∩ Φ⁻¹{y})`, so the fibre sum is `Σ_{a ∈ A, Φ(a) = y} h(g(a))`.  The formula for
`Φ` is proved in place from Mathlib's change of variables, as the SimonGMT area formula is not
available in this file.  Off the null images of the non-differentiability set (Rademacher and
the Lipschitz image bound) and of the critical set (Sard), the fibre sum splits over a countable
partition of `A` into pieces on which `Φ` is injective, and on each piece the injective change
of variables formula applies. -/
theorem Submission.idtp_caf_paf_fiber_side : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (A : Set (Euclid n)) (F : Euclid P → Euclid n) (Φ : Euclid n → Euclid n) (LΦ : NNReal) (h : Euclid P → ℝ≥0∞), Continuous g → MeasurableSet A → InjOn g A → LipschitzWith LΦ Φ → (∀ a ∈ A, F (g a) = Φ a) → Measurable h → AEMeasurable (fun y : Euclid n => ∑' x : ↥(g '' A ∩ F ⁻¹' {y}), h x) volume ∧ ∫⁻ y, (∑' x : ↥(g '' A ∩ F ⁻¹' {y}), h x) ∂volume = ∫⁻ a in A, ENNReal.ofReal |LinearMap.det (fderiv ℝ Φ a : Euclid n →ₗ[ℝ] Euclid n)| * h (g a) ∂volume := by
  intro P n g A F Φ LΦ h hg hA hgA hΦ hFg hh
  -- the weight `w = h ∘ g` on the parameter side is Borel
  set w : Euclid n → ℝ≥0∞ := fun a => h (g a)
  have hw : Measurable w := hh.comp hg.measurable
  -- `g(A) ∩ F⁻¹{y} = g(A ∩ Φ⁻¹{y})`, and `tsum_image` reindexes the fibre sum
  have hfib : ∀ y, (∑' x : ↥(g '' A ∩ F ⁻¹' {y}), h x) = ∑' a : ↥(A ∩ Φ ⁻¹' {y}), w a := by
    intro y
    have hset : g '' A ∩ F ⁻¹' {y} = g '' (A ∩ Φ ⁻¹' {y}) := by
      ext x
      simp only [mem_inter_iff, mem_image, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hy⟩
        exact ⟨a, ⟨ha, (hFg a ha).symm.trans hy⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hy⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, (hFg a ha).trans hy⟩
    rw [hset, tsum_image h (hgA.mono inter_subset_left)]
  simp only [hfib]
  -- `D`: differentiability points of `Φ`; `s`: the points of `A ∩ D` with `det DΦ ≠ 0`
  set D : Set (Euclid n) := {x | DifferentiableAt ℝ Φ x}
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ Φ
  have hdetm : Measurable fun x => (fderiv ℝ Φ x).det :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ Φ)
  set s : Set (Euclid n) := A ∩ D ∩ {x | (fderiv ℝ Φ x).det ≠ 0}
  have hsm : MeasurableSet s := (hA.inter hDm).inter (hdetm (measurableSet_singleton 0).compl)
  -- precision `r B` with `r B * ‖B⁻¹‖ < 1` whenever `B` is invertible
  let r : (Euclid n →L[ℝ] Euclid n) → NNReal := fun B =>
    if hB : B.det ≠ 0 then
      (‖((B.toContinuousLinearEquivOfDetNeZero hB).symm : Euclid n →L[ℝ] Euclid n)‖₊ + 1)⁻¹
    else 1
  have rpos : ∀ B, r B ≠ 0 := by
    intro B
    simp only [r]
    split_ifs
    · exact inv_ne_zero (by positivity)
    · exact one_ne_zero
  -- a countable measurable partition of `s` into pieces `S k` on which `Φ` is close to `B k`
  obtain ⟨t, B, ht_disj, ht_meas, hst, happrox, hB⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ s (fderiv ℝ Φ)
      (fun x hx => (hx.1.2 : DifferentiableAt ℝ Φ x).hasFDerivAt.hasFDerivWithinAt) r rpos
  set S : ℕ → Set (Euclid n) := fun k => s ∩ t k
  have hSm : ∀ k, MeasurableSet (S k) := fun k => hsm.inter (ht_meas k)
  have hSdisj : Pairwise (Disjoint on S) := fun i j hij =>
    (ht_disj hij).mono inter_subset_right inter_subset_right
  have hSU : ⋃ k, S k = s := by
    simp only [S, ← inter_iUnion]
    exact inter_eq_left.mpr hst
  have hSder : ∀ k, ∀ x ∈ S k, HasFDerivWithinAt Φ (fderiv ℝ Φ x) (S k) x := fun k x hx =>
    (hx.1.1.2 : DifferentiableAt ℝ Φ x).hasFDerivAt.hasFDerivWithinAt
  -- `Φ` is injective on each piece: `B k = DΦ(z)` is invertible and `r (B k) * ‖(B k)⁻¹‖ < 1`
  have hSinj : ∀ k, InjOn Φ (S k) := by
    intro k x hx y hy hxy
    obtain ⟨z, hz, hBz⟩ := hB ⟨x, hx.1⟩ k
    have hdet : (B k).det ≠ 0 := hBz ▸ hz.2
    set e := (B k).toContinuousLinearEquivOfDetNeZero hdet
    set N : ℝ := ‖(e.symm : Euclid n →L[ℝ] Euclid n)‖
    have hr : ((r (B k) : NNReal) : ℝ) = (N + 1)⁻¹ := by
      simp only [r, dite_eq_left hdet, NNReal.coe_inv, NNReal.coe_add, coe_nnnorm,
        NNReal.coe_one, N, e]
    have happ := happrox k x hx y hy
    rw [hxy, sub_self, zero_sub, norm_neg, hr] at happ
    have h1 : ‖x - y‖ ≤ N * ‖B k (x - y)‖ := by
      have hxy' : e.symm (B k (x - y)) = x - y := by
        rw [show B k (x - y) = e (x - y) from rfl, ContinuousLinearEquiv.symm_apply_apply]
      calc ‖x - y‖ = ‖(e.symm : Euclid n →L[ℝ] Euclid n) (B k (x - y))‖ := by
              rw [ContinuousLinearEquiv.coe_coe, hxy']
        _ ≤ N * ‖B k (x - y)‖ := (e.symm : Euclid n →L[ℝ] Euclid n).le_opNorm _
    have hN : 0 ≤ N := norm_nonneg _
    have h2 : ‖x - y‖ ≤ N * ((N + 1)⁻¹ * ‖x - y‖) :=
      h1.trans (mul_le_mul_of_nonneg_left happ hN)
    have h3 : ‖x - y‖ ≤ 0 := by
      have hN1 : 0 < N + 1 := by linarith
      have h4 : N * ((N + 1)⁻¹ * ‖x - y‖) = ‖x - y‖ - (N + 1)⁻¹ * ‖x - y‖ := by
        field_simp
        ring
      rw [h4] at h2
      have h5 : (N + 1)⁻¹ * ‖x - y‖ ≤ 0 := by linarith
      have h6 : 0 < (N + 1)⁻¹ := inv_pos.mpr hN1
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)
  -- `G k y`: the fibre sum of `w` over `S k ∩ Φ⁻¹{y}`, which has at most one point
  set G : ℕ → Euclid n → ℝ≥0∞ := fun k y => ∑' a, (S k ∩ Φ ⁻¹' {y}).indicator w a
  have hG_apply : ∀ k, ∀ x ∈ S k, G k (Φ x) = w x := by
    intro k x hx
    simp only [G]
    rw [tsum_eq_single x]
    · exact indicator_of_mem (show x ∈ S k ∩ Φ ⁻¹' {Φ x} from ⟨hx, rfl⟩) w
    · intro a hax
      exact indicator_of_notMem (fun ha => hax (hSinj k ha.1 hx ha.2)) w
  have hG_zero : ∀ k y, y ∉ Φ '' S k → G k y = 0 := by
    intro k y hy
    simp only [G]
    exact (tsum_congr fun a => indicator_of_notMem (fun ha => hy ⟨a, ha.1, ha.2⟩) w).trans
      tsum_zero
  have hG_meas : ∀ k, Measurable (G k) := by
    intro k
    have hemb := measurableEmbedding_of_fderivWithin (hSm k) (hSder k) (hSinj k)
    have hGe : G k = Function.extend ((S k).domRestrict Φ) (fun x => w x) 0 := by
      funext y
      by_cases hy : ∃ x : S k, (S k).domRestrict Φ x = y
      · obtain ⟨x, rfl⟩ := hy
        rw [hemb.injective.extend_apply]
        exact hG_apply k x x.2
      · rw [extend_apply' _ _ _ hy, hG_zero k y]
        · rfl
        · rintro ⟨x, hx, rfl⟩
          exact hy ⟨⟨x, hx⟩, rfl⟩
    rw [hGe]
    exact hemb.measurable_extend (hw.comp measurable_subtype_coe) measurable_const
  -- injective change of variables on each piece
  have hG_int : ∀ k, ∫⁻ y, G k y =
      ∫⁻ x in S k, ENNReal.ofReal |(fderiv ℝ Φ x).det| * w x := by
    intro k
    rw [← setLIntegral_eq_of_support_subset (s := Φ '' S k) (fun y hy => by
        by_contra hy'
        exact hy (hG_zero k y hy')),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hSm k) (hSder k) (hSinj k)]
    exact setLIntegral_congr_fun (hSm k) (fun x hx => by rw [hG_apply k x hx])
  -- null images: of `Dᶜ` (Rademacher, Lipschitz image bound) and of the critical set (Sard)
  have hDc : volume Dᶜ = 0 := ae_iff.mp (hΦ.ae_differentiableAt (μ := volume))
  have hnull1 : volume (Φ '' Dᶜ) = 0 := by
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hΦ.lipschitzOnWith (s := Dᶜ))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hDc, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  have hnull2 : volume (Φ '' (A ∩ D ∩ {x | (fderiv ℝ Φ x).det = 0})) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun x hx => (hx.1.2 : DifferentiableAt ℝ Φ x).hasFDerivAt.hasFDerivWithinAt)
      (fun x hx => hx.2)
  -- off these null sets, the fibre sum over `A` splits over the pieces
  have hae : ∀ᵐ y ∂volume, (∑' a : ↥(A ∩ Φ ⁻¹' {y}), w a) = ∑' k, G k y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_union_null hnull1 hnull2)] with y hy
    rw [tsum_subtype (A ∩ Φ ⁻¹' {y}) w]
    simp only [G]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ A ∩ Φ ⁻¹' {y}
    · have haD : a ∈ D := by
        by_contra hD
        exact hy (Or.inl ⟨a, hD, ha.2⟩)
      have hadet : (fderiv ℝ Φ a).det ≠ 0 := by
        intro h0
        exact hy (Or.inr ⟨a, ⟨⟨ha.1, haD⟩, h0⟩, ha.2⟩)
      have has : a ∈ s := ⟨⟨ha.1, haD⟩, hadet⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hst has)
      rw [indicator_of_mem ha, tsum_eq_single k]
      · exact (indicator_of_mem (show a ∈ S k ∩ Φ ⁻¹' {y} from ⟨⟨has, hk⟩, ha.2⟩) w).symm
      · intro j hj
        exact indicator_of_notMem (fun haj => Set.disjoint_left.mp (ht_disj hj) haj.1.2 hk) w
    · rw [indicator_of_notMem ha]
      exact ((tsum_congr fun k => indicator_of_notMem
        (fun hak => ha ⟨hak.1.1.1.1, hak.2⟩) w).trans tsum_zero).symm
  have hGsum : Measurable fun y => ∑' k, G k y := Measurable.tsum hG_meas
  refine ⟨hGsum.aemeasurable.congr (Filter.EventuallyEq.symm hae), ?_⟩
  rw [lintegral_congr_ae hae, lintegral_tsum (fun k => (hG_meas k).aemeasurable)]
  simp only [hG_int]
  rw [← lintegral_iUnion hSm hSdisj, hSU]
  -- the integrand vanishes a.e. on `A \ s`
  rw [← inter_eq_left.mpr (show s ⊆ A from fun x hx => hx.1.1), ← setLIntegral_indicator hsm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (hΦ.ae_differentiableAt (μ := volume)), ae_restrict_mem hA]
    with x hxD hxA
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs]
  · rw [indicator_of_notMem hxs]
    have h0 : (fderiv ℝ Φ x).det = 0 := by
      by_contra h0
      exact hxs ⟨⟨hxA, hxD⟩, h0⟩
    have h0' : LinearMap.det (fderiv ℝ Φ x : Euclid n →ₗ[ℝ] Euclid n) = 0 := h0
    simp [h0']
/-- **Carrier side of the area formula on one piece** (Simon Ch. 3, 2.4–2.5, with the injective
area formula of Ch. 2, §3).  Let `g : ℝⁿ → ℝᴾ` be Lipschitz, injective on the Borel set `A` and
differentiable at every point of `A`, let `F = G` on an open `V ⊇ g(A)` with `F` differentiable on
`g(A)`, and let `T(g(a)) = range Dg(a)` for a.e. `a ∈ A`.  With `u` the standard orthonormal basis
of `T(x)` and `J_T(x) = √det(DF(x)uᵢ · DF(x)uⱼ)`, every `h ≥ 0` has
`∫_{g(A)} J_T h dHⁿ = ∫_A |det D(G ∘ g)| h ∘ g dLⁿ`.

The area formula is proved inline.  `J L = √det(L eᵢ · L eⱼ)` is the Jacobian of a linear
`L : ℝᵐ → Y`; for injective `L`, `L = ι ∘ M` with `ι` an isometry and `J L = |det M|`, so
`Hᵐ(L(S)) = J L · Hᵐ(S)`.  On pieces where `g` is close to an injective linear map, Hausdorff
measure of the image is comparable to `J`, giving `Hⁿ(g(E)) = ∫_E J(Dg)` where `Dg` is injective;
where `Dg` is not injective, the graphs `x ↦ (g x, εx)` show `Hⁿ(g(E)) = 0` as `ε → 0`.  A.e. on
`A`, `D(G ∘ g)(a) = DF(g(a)) ∘ Dg(a)` and comparing volumes of the image of the unit ball gives
`|det D(G ∘ g)(a)| = J_T(g(a)) · J(Dg(a))`. -/
theorem Submission.idtp_caf_paf_carrier_side : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (A : Set (Euclid n)) (Lg : NNReal) (V : Set (Euclid P)) (F G : Euclid P → Euclid n) (T : Euclid P → Submodule ℝ (Euclid P)) (h : Euclid P → ℝ≥0∞), LipschitzWith Lg g → MeasurableSet A → InjOn g A → (∀ a ∈ A, DifferentiableAt ℝ g a) → IsOpen V → g '' A ⊆ V → EqOn F G V → (∀ x ∈ g '' A, DifferentiableAt ℝ F x) → (∀ᵐ a ∂(volume.restrict A), T (g a) = LinearMap.range (fderiv ℝ g a : Euclid n →ₗ[ℝ] Euclid P)) → ∫⁻ x in g '' A, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (T x)) => inner ℝ (fderiv ℝ F x (stdOrthonormalBasis ℝ (T x) i)) (fderiv ℝ F x (stdOrthonormalBasis ℝ (T x) j))))) * h x ∂μHE[n] = ∫⁻ a in A, ENNReal.ofReal |LinearMap.det (fderiv ℝ (G ∘ g) a : Euclid n →ₗ[ℝ] Euclid n)| * h (g a) ∂volume := by
  classical
  -- the Jacobian `J L = √det(L eᵢ · L eⱼ)` of a linear map `L : ℝᵐ → Y`
  obtain ⟨Jac, hJac⟩ : ∃ Jac : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y],
      (EuclideanSpace ℝ (Fin m) →L[ℝ] Y) → ℝ,
      ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
        (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y),
        Jac L = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin m =>
          inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1)))) :=
    ⟨fun {m} {_} [_] [_] L => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin m =>
      inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1)))),
      fun _ => rfl⟩
  have jac_nonneg : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y), 0 ≤ Jac L := by
    intro m Y _ _ L
    rw [hJac]
    exact Real.sqrt_nonneg _
  -- an injective `L` factors as `ι ∘ M` with `ι` an isometry, and `J L = |det M| ≠ 0`
  have jac_factor : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y), Injective L →
      ∃ (ι : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] Y)
        (M : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
        (∀ x, ι (M x) = L x) ∧ Jac L = |LinearMap.det M| ∧ LinearMap.det M ≠ 0 := by
    intro m Y _ _ _ L hL
    have hW : Module.finrank ℝ (LinearMap.range (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    obtain ⟨u⟩ : Nonempty (OrthonormalBasis (Fin m) ℝ
        (LinearMap.range (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y))) :=
      ⟨(stdOrthonormalBasis ℝ _).reindex (finCongr hW)⟩
    obtain ⟨ι, M, hιM⟩ : ∃ (ι : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] Y)
        (M : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)), ∀ x, ι (M x) = L x := by
      refine ⟨(LinearMap.range (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y)).subtypeₗᵢ.comp
          u.repr.symm.toLinearIsometry,
        u.repr.toLinearEquiv.toLinearMap ∘ₗ (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y).rangeRestrict,
        fun x => ?_⟩
      change ((u.repr.symm (u.repr ((L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y).rangeRestrict x)) :
        LinearMap.range (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y)) : Y) = L x
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hdetM : LinearMap.det M ≠ 0 := by
      rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      rw [← hιM x, ← hιM y, hxy]
    refine ⟨ι, M, hιM, ?_, hdetM⟩
    have hgram : (Matrix.of fun i j : Fin m =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))) =
        Matrix.transpose (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin m) ℝ).toBasis M) *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis M := by
      ext i j
      rw [Matrix.of_apply, ← hιM, ← hιM, LinearIsometry.inner_map_map, Matrix.mul_apply,
        PiLp.inner_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, RCLike.inner_apply, conj_trivial]
      ring
    rw [hJac, hgram, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, ← sq,
      Real.sqrt_sq_eq_abs]
  -- the linear area formula `Hᵈ(L(S)) = J L · Hᵈ(S)` for injective `L` (`d = m`)
  have linear_area : ∀ {m d : ℕ}, m = d → ∀ {Y : Type} [NormedAddCommGroup Y]
      [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
      (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y), Injective L →
      ∀ (s : Set (EuclideanSpace ℝ (Fin m))), μHE[d] (L '' s) = ENNReal.ofReal (Jac L) * μHE[d] s := by
    intro m d hd Y _ _ _ _ _ L hL s
    subst hd
    obtain ⟨ι, M, hιM, hJ, -⟩ := jac_factor L hL
    have himage : L '' s = ι '' (M '' s) := by
      rw [image_image]
      exact image_congr fun x _ => (hιM x).symm
    rw [himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hJ]
  have jac_eq_zero : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y), ¬ Injective L → Jac L = 0 := by
    intro m Y _ _ L hL
    obtain ⟨w, hw0, hLw⟩ : ∃ w, w ≠ 0 ∧ L w = 0 := by
      have hker : LinearMap.ker (L : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Y) ≠ ⊥ := fun h =>
        hL (LinearMap.ker_eq_bot.mp h)
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
      exact ⟨w, hw0, hw⟩
    have hdet : Matrix.det (Matrix.of fun i j : Fin m =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))) = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun j => w j, ?_, ?_⟩
      · intro h
        apply hw0
        ext j
        exact congrFun h j
      · ext i
        have hw : w = ∑ j, w j • EuclideanSpace.single j (1 : ℝ) := by
          ext k
          simp [Finset.sum_apply, Pi.single_apply]
        have : ∑ j, inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1)) * w j
            = inner ℝ (L (EuclideanSpace.single i 1)) (L w) := by
          conv_rhs => rw [hw]
          simp [map_sum, map_smul, inner_sum, inner_smul_right, mul_comm]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [this, hLw, inner_zero_right]
    rw [hJac, hdet, Real.sqrt_zero]
  have jac_pos : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y), Injective L → 0 < Jac L := by
    intro m Y _ _ _ L hL
    obtain ⟨ι, M, -, hJ, hdet⟩ := jac_factor L hL
    rw [hJ]
    exact abs_pos.mpr hdet
  have continuous_jac : ∀ {m : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y],
      Continuous (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] Y => Jac L) := by
    intro m Y _ _
    simp only [hJac]
    apply Real.continuous_sqrt.comp
    apply Continuous.matrix_det
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.of_apply]
    exact ((ContinuousLinearMap.apply ℝ Y _).continuous).inner
      ((ContinuousLinearMap.apply ℝ Y _).continuous)
  -- comparing pairwise distances compares Hausdorff measures of images
  have image_le_of_dist_le : ∀ {X Z : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
      [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [Nonempty X]
      {f g : X → Z} {s : Set X} {K : NNReal}, InjOn g s →
      (∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y)) →
      ∀ (d : ℕ), μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] (g '' s) := by
    intro X Z _ _ _ _ _ _ _ f g s K hg hfg d
    have hh : LipschitzOnWith K (f ∘ invFunOn g s) (g '' s) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hg.leftInvOn_invFunOn hx,
        hg.leftInvOn_invFunOn hy] using hfg x hx y hy
    have himage : (f ∘ invFunOn g s) '' (g '' s) = f '' s := by
      rw [image_comp, hg.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d hh
  -- sharp comparisons for a map approximating an injective linear map
  have approx_upper : ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
      {f : EuclideanSpace ℝ (Fin n) → Y} {L : EuclideanSpace ℝ (Fin n) →L[ℝ] Y}
      {s : Set (EuclideanSpace ℝ (Fin n))} {δ K : NNReal},
      ApproximatesLinearOn f L s δ → AntilipschitzWith K L →
      μHE[n] (f '' s) ≤ ((1 + δ * K : NNReal) : ℝ≥0∞) ^ n * (ENNReal.ofReal (Jac L) * μHE[n] s) := by
    intro n Y _ _ _ _ _ f L s δ K hf hL
    rw [← linear_area rfl L hL.injective s]
    apply image_le_of_dist_le hL.injective.injOn
    intro x hx y hy
    have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
      simpa only [dist_eq_norm] using hL.le_mul_dist x y
    have herror : ‖f x - f y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      calc
        _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = _ := by ring
    simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
    calc
      ‖f x - f y‖ ≤ ‖f x - f y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
      _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add herror le_rfl
      _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
  have approx_lower : ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
      {f : EuclideanSpace ℝ (Fin n) → Y} {L : EuclideanSpace ℝ (Fin n) →L[ℝ] Y}
      {s : Set (EuclideanSpace ℝ (Fin n))} {δ K : NNReal},
      ApproximatesLinearOn f L s δ → AntilipschitzWith K L → δ * K < 1 →
      ENNReal.ofReal (Jac L) * μHE[n] s ≤
        (((1 - δ * K)⁻¹ : NNReal) : ℝ≥0∞) ^ n * μHE[n] (f '' s) := by
    intro n Y _ _ _ _ _ f L s δ K hf hL hδ
    have hδR : (δ : ℝ) * K < 1 := hδ
    have hdist : ∀ x ∈ s, ∀ y ∈ s, dist (L x) (L y) ≤
        ((1 - δ * K)⁻¹ : NNReal) * dist (f x) (f y) := by
      intro x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm] using hL.le_mul_dist x y
      have herror : ‖f x - f y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
        calc
          _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
          _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
          _ = _ := by ring
      have htriangle : ‖L x - L y‖ ≤ ‖f x - f y‖ + ‖f x - f y - (L x - L y)‖ := by
        simpa only [norm_sub_rev, add_comm] using
          (norm_le_norm_sub_add (L x - L y) (f x - f y))
      simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le,
        NNReal.coe_one, NNReal.coe_mul, inv_mul_eq_div]
      apply (le_div_iff₀ (sub_pos.mpr hδR)).mpr
      nlinarith
    have hfinj : InjOn f s := by
      intro x hx y hy hxy
      apply hL.injective
      apply dist_le_zero.mp
      simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
    rw [← linear_area rfl L hL.injective s]
    exact image_le_of_dist_le hfinj hdist _
  -- one radius controlling both the image measure and the Jacobians of nearby maps
  have radius_area : ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
      (L : EuclideanSpace ℝ (Fin n) →L[ℝ] Y), Injective L → ∀ {q : NNReal}, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : EuclideanSpace ℝ (Fin n) →L[ℝ] Y, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (Jac B) ≤ q * ENNReal.ofReal (Jac L) ∧
          ENNReal.ofReal (Jac L) ≤ q * ENNReal.ofReal (Jac B)) ∧
        (∀ (s : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → Y),
          ApproximatesLinearOn f L s δ →
          μHE[n] (f '' s) ≤ q * (ENNReal.ofReal (Jac L) * μHE[n] s) ∧
            ENNReal.ofReal (Jac L) * μHE[n] s ≤ q * μHE[n] (f '' s)) := by
    intro n Y _ _ _ _ _ L hL q hq
    obtain ⟨K, _, hK⟩ := (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Y).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 := by
      exact (continuousAt_id.mul continuousAt_const).eventually_lt
        continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q := by
      exact ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hJ : 0 < Jac L := jac_pos L hL
    have hqR : (1 : ℝ) < q := hq
    have hmul : Jac L < (q : ℝ) * Jac L := by nlinarith
    have hnear : ∀ᶠ B : EuclideanSpace ℝ (Fin n) →L[ℝ] Y in 𝓝 L,
        Jac B < (q : ℝ) * Jac L ∧ Jac L < (q : ℝ) * Jac B :=
      (continuous_jac.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt
          (continuousAt_const.mul continuous_jac.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      have hεnhds : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
      filter_upwards [self_mem_nhdsWithin,
        hsmall.filter_mono nhdsWithin_le_nhds, hupper.filter_mono nhdsWithin_le_nhds,
        hlower.filter_mono nhdsWithin_le_nhds, hεnhds.filter_mono nhdsWithin_le_nhds]
        with δ hδ hsmall hupper hlower hδε
      exact ⟨hδ, hsmall, hupper, hlower, hδε⟩
    obtain ⟨δ, hδ, hδsmall, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, ?_, fun s f hf => ⟨?_, ?_⟩⟩
    · intro B hB
      have hdist : dist B L < ε := by
        rw [dist_eq_norm]
        exact hB.trans_lt hδε
      obtain ⟨hupper, hlower⟩ := hnear hdist
      constructor
      · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal hupper.le
      · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal hlower.le
    · refine (approx_upper hf hK).trans ?_
      gcongr
      exact_mod_cast hδupper.le
    · refine (approx_lower hf hK hδsmall).trans ?_
      gcongr
      exact_mod_cast hδlower.le
  -- on a.e. point of an approximation piece the derivative is close to the linear map
  have approx_fderiv : ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      {f : EuclideanSpace ℝ (Fin n) → Y} {s : Set (EuclideanSpace ℝ (Fin n))}
      {A : EuclideanSpace ℝ (Fin n) →L[ℝ] Y} {δ : NNReal},
      ApproximatesLinearOn f A s δ → MeasurableSet s →
      ∀ (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] Y),
      (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) →
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict s, ‖f' x - A‖₊ ≤ δ := by
    intro n Y _ _ f s A δ hf hs f' hf'
    open scoped Pointwise in
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume s, ae_restrict_mem hs]
    intro x hx xs
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
      have :
          Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
            (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto
          (((continuous_const.add continuous_id).mul (continuous_const.add continuous_id)).add
            (continuous_const.mul continuous_id)) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume s x hx _ measurableSet_closedBall
        (Metric.measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ s ⊆ {y | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 ((hf' x xs).isLittleO.bound εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
        ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
          {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc
        ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc
        r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
          simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
          simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, sub_apply, map_smul,
            smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
        _ = r * (δ + ε) * ‖a‖ := by
          simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc
      ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
        congr 1
        simp only [sub_apply, map_sub]
        abel
      _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
        apply add_le_add
        · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
        · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
        rw [mem_closedBall_iff_norm'] at az
        gcongr
  -- the area formula with injective derivative, up to a factor `q²`
  have regular_comparison : ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
      {s : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → Y}
      {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] Y},
      MeasurableSet s → (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) →
      (∀ x ∈ s, Injective (f' x)) → InjOn f s → ∀ {q : NNReal}, 1 < q →
      μHE[n] (f '' s) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s, ENNReal.ofReal (Jac (f' x)) ∂volume ∧
        (∫⁻ x in s, ENNReal.ofReal (Jac (f' x)) ∂volume) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (f '' s) := by
    intro n Y _ _ _ _ _ s f f' hs hf' hreg hinj q hq
    rcases eq_empty_or_nonempty s with rfl | hsne
    · simp
    have hchoice : ∀ L : EuclideanSpace ℝ (Fin n) →L[ℝ] Y, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
        (∀ B : EuclideanSpace ℝ (Fin n) →L[ℝ] Y, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (Jac B) ≤ q * ENNReal.ofReal (Jac L) ∧
          ENNReal.ofReal (Jac L) ≤ q * ENNReal.ofReal (Jac B)) ∧
        (∀ (t : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → Y),
          ApproximatesLinearOn g L t δ →
          μHE[n] (g '' t) ≤ q * (ENNReal.ofReal (Jac L) * μHE[n] t) ∧
            ENNReal.ofReal (Jac L) * μHE[n] t ≤ q * μHE[n] (g '' t))) := by
      intro L
      by_cases hL : Injective L
      · obtain ⟨δ, hδ, hJ, harea⟩ := radius_area L hL hq
        exact ⟨δ, hδ, fun _ => ⟨hJ, harea⟩⟩
      · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
    choose δ hδpos hδ using hchoice
    obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf'
        δ (fun L => (hδpos L).ne')
    have hLreg (i : ℕ) : Injective (L i) := by
      obtain ⟨x, hx, hL⟩ := hactual hsne i
      rw [hL]
      exact hreg x hx
    have hseq : s = ⋃ i, s ∩ t i := by
      rw [← inter_iUnion]
      exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
    have hsumimage : μHE[n] (f '' s) = ∑' i, μHE[n] (f '' (s ∩ t i)) := by
      conv_lhs => rw [hseq, image_iUnion]
      apply measure_iUnion
      · intro i j hij
        exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
          hinj inter_subset_left inter_subset_left
      · intro i
        apply (hs.inter (ht i)).image_of_continuousOn_injOn
        · exact (fun x hx => (hf' x hx.1).continuousWithinAt.mono inter_subset_left)
        · exact hinj.mono inter_subset_left
    have hsumintegral :
        (∫⁻ x in s, ENNReal.ofReal (Jac (f' x)) ∂volume) =
          ∑' i, ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume := by
      conv_lhs => rw [hseq]
      exact lintegral_iUnion (fun i => hs.inter (ht i))
        (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
    have hvol : (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    have hpiece (i : ℕ) :
        μHE[n] (f '' (s ∩ t i)) ≤ (q : ℝ≥0∞) ^ 2 *
            ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume ∧
          (∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (f '' (s ∩ t i)) := by
      have hJ := (hδ (L i) (hLreg i)).1
      obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (s ∩ t i) f (happrox i)
      rw [hvol] at harea_upper harea_lower
      have hderiv := approx_fderiv (happrox i) (hs.inter (ht i)) f'
        (fun x hx => (hf' x hx.1).mono inter_subset_left)
      have hJupper :
          (∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume) ≤
            q * (ENNReal.ofReal (Jac (L i)) * volume (s ∩ t i)) := by
        calc
          _ ≤ ∫⁻ _ in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (Jac (L i)) ∂volume := by
            apply lintegral_mono_ae
            filter_upwards [hderiv] with x hx
            exact (hJ (f' x) hx).1
          _ = _ := by rw [setLIntegral_const, mul_assoc]
      have hJlower : ENNReal.ofReal (Jac (L i)) * volume (s ∩ t i) ≤
          q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume := by
        calc
          _ = ∫⁻ _ in s ∩ t i, ENNReal.ofReal (Jac (L i)) ∂volume :=
            (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (Jac (f' x)) ∂volume := by
            apply lintegral_mono_ae
            filter_upwards [hderiv] with x hx
            exact (hJ (f' x) hx).2
          _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
      constructor
      · calc
          _ ≤ q * (ENNReal.ofReal (Jac (L i)) * volume (s ∩ t i)) := harea_upper
          _ ≤ q * (q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume) := by gcongr
          _ = _ := by rw [pow_two, mul_assoc]
      · calc
          _ ≤ q * (ENNReal.ofReal (Jac (L i)) * volume (s ∩ t i)) := hJupper
          _ ≤ q * (q * μHE[n] (f '' (s ∩ t i))) := by gcongr
          _ = _ := by rw [pow_two, mul_assoc]
    rw [hsumimage, hsumintegral]
    constructor
    · calc
        _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac (f' x)) ∂volume :=
          ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
        _ = _ := ENNReal.tsum_mul_left
    · calc
        _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (f '' (s ∩ t i)) :=
          ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
        _ = _ := ENNReal.tsum_mul_left
  -- the area formula with injective derivative
  have regular_area : ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
      {s : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → Y}
      {f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] Y},
      MeasurableSet s → (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) →
      (∀ x ∈ s, Injective (f' x)) → InjOn f s →
      μHE[n] (f '' s) = ∫⁻ x in s, ENNReal.ofReal (Jac (f' x)) ∂volume := by
    intro n Y _ _ _ _ _ s f f' hs hf' hreg hinj
    have hlimit (a : ℝ≥0∞) :
        Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (regular_comparison hs hf' hreg hinj hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (regular_comparison hs hf' hreg hinj hq).2
  -- critical points: the graphs `x ↦ (f x, εx)` have injective derivatives and shrinking area
  have critical_finite : ∀ {P n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
      {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin P)}, MeasurableSet s →
      (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, ¬ Injective (fderiv ℝ f x)) →
      volume s ≠ ⊤ → ∀ {B : ℝ}, (∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ B) → μHE[n] (f '' s) = 0 := by
    intro P n s f hs hf hcrit hfinite B hB
    obtain ⟨G, hGapply, hGcont, hGderiv⟩ : ∃ G : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin P)) → ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ]
          WithLp 2 (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin n))),
        (∀ L ε x, G L ε x = WithLp.toLp 2 (L x, ε • x)) ∧
        Continuous (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin P)) × ℝ =>
          G p.1 p.2) ∧
        ∀ (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin P))
          (x : EuclideanSpace ℝ (Fin n)), HasFDerivAt f L x → ∀ ε : ℝ,
            HasFDerivAt (fun y => (WithLp.toLp 2 (f y, ε • y) :
              WithLp 2 (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin n)))) (G L ε) x := by
      refine ⟨fun L ε => (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin P))
          (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.comp
          (L.prod (ε • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))),
        fun _ _ _ => rfl, ?_, ?_⟩
      · apply Continuous.clm_comp continuous_const
        exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
          (continuous_fst.prodMk (continuous_snd.smul continuous_const))
      · intro L x hL ε
        exact (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin P))
          (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.hasFDerivAt.comp
          x (hL.prodMk ((hasFDerivAt_id x).const_smul ε))
    have hc : Continuous (fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin P)) × ℝ =>
        Jac (G p.1 p.2)) := continuous_jac.comp hGcont
    have hzero : ∀ x ∈ s, Jac (G (fderiv ℝ f x) 0) = 0 := by
      intro x hx
      apply jac_eq_zero
      intro hg
      apply hcrit x hx
      intro y z hyz
      apply hg
      rw [hGapply, hGapply, zero_smul, zero_smul, hyz]
    have hgraph : ∀ ε : ℝ, ε ≠ 0 →
        μHE[n] (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal (Jac (G (fderiv ℝ f x) ε)) ∂volume := by
      intro ε hε
      have hinj : Injective (fun y : EuclideanSpace ℝ (Fin n) => (WithLp.toLp 2 (f y, ε • y) :
          WithLp 2 (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin n)))) := by
        intro x y h
        have he : ε • x = ε • y := congrArg WithLp.snd h
        exact (smul_right_injective _ hε) he
      have hp : LipschitzWith 1 (WithLp.fst :
          WithLp 2 (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin n)) →
            EuclideanSpace ℝ (Fin P)) :=
        LipschitzWith.of_dist_le_mul (fun x y => by
          rw [NNReal.coe_one, one_mul]; exact WithLp.dist_fst_le x y)
      have himg : f '' s = WithLp.fst '' ((fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (f y, ε • y) :
            WithLp 2 (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin n)))) '' s) := by
        rw [image_image]
        rfl
      have hproj := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hp.lipschitzOnWith (s := (fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (f y, ε • y) :
            WithLp 2 (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin n)))) '' s))
      rw [ENNReal.coe_one, one_pow, one_mul, ← himg] at hproj
      refine hproj.trans_eq ?_
      refine regular_area hs (fun x hx => (hGderiv _ x (hf x hx).hasFDerivAt ε).hasFDerivWithinAt)
        (fun x _ y z h => ?_) hinj.injOn
      rw [hGapply, hGapply] at h
      have he : ε • y = ε • z := congrArg WithLp.snd h
      exact (smul_right_injective _ hε) he
    obtain ⟨C, hC⟩ := ((isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin P)) B).prod
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).exists_bound_of_continuousOn hc.continuousOn
    have hlim : Tendsto (fun ε : ℝ => ∫⁻ x in s,
        ENNReal.ofReal (Jac (G (fderiv ℝ f x) ε)) ∂volume) (𝓝[>] 0) (𝓝 0) := by
      have hmeas (ε : ℝ) : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Jac (G (fderiv ℝ f x) ε))) :=
        (hc.measurable.comp ((measurable_fderiv ℝ f).prodMk measurable_const)).ennreal_ofReal
      have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ x ∂volume.restrict s,
          ENNReal.ofReal (Jac (G (fderiv ℝ f x) ε)) ≤ ENNReal.ofReal C := by
        have hnear : Icc (-1 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds
          (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
        filter_upwards [hnear] with ε hε
        filter_upwards [ae_restrict_mem hs] with x hx
        apply ENNReal.ofReal_le_ofReal
        exact (le_abs_self _).trans (hC ⟨fderiv ℝ f x, ε⟩
          ⟨by simpa only [mem_closedBall, dist_zero_right] using hB x hx, hε⟩)
      have hfin : (∫⁻ _ : EuclideanSpace ℝ (Fin n), ENNReal.ofReal C ∂volume.restrict s) ≠ ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
      have hpoint : ∀ᵐ x ∂volume.restrict s,
          Tendsto (fun ε : ℝ => ENNReal.ofReal (Jac (G (fderiv ℝ f x) ε))) (𝓝[>] 0) (𝓝 0) := by
        filter_upwards [ae_restrict_mem hs] with x hx
        have hc' : Continuous (fun ε : ℝ => ENNReal.ofReal (Jac (G (fderiv ℝ f x) ε))) :=
          ENNReal.continuous_ofReal.comp (hc.comp (continuous_const.prodMk continuous_id))
        have h0 := (hc'.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        rwa [hzero x hx, ENNReal.ofReal_zero] at h0
      have := tendsto_lintegral_filter_of_dominated_convergence
        (fun _ : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal C)
        (Eventually.of_forall hmeas) hbound hfin hpoint
      rwa [lintegral_zero] at this
    apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hgraph ε (ne_of_gt hε)
  have critical : ∀ {P n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
      {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin P)}, MeasurableSet s →
      (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, ¬ Injective (fderiv ℝ f x)) →
      μHE[n] (f '' s) = 0 := by
    intro P n s f hs hf hcrit
    have hnull (k : ℕ) : μHE[n] (f '' (s ∩ closedBall 0 k ∩ {x | ‖fderiv ℝ f x‖ ≤ k})) = 0 := by
      apply critical_finite ((hs.inter measurableSet_closedBall).inter
          (measurableSet_le (measurable_fderiv ℝ f).norm measurable_const))
        (fun x hx => hf x hx.1.1) (fun x hx => hcrit x hx.1.1)
      · exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne
          (measure_mono (fun _ hx => hx.1.2))
      · exact fun _ hx => hx.2
    have hcover : s ⊆ ⋃ k : ℕ, s ∩ closedBall 0 k ∩ {x | ‖fderiv ℝ f x‖ ≤ k} := by
      intro x hx
      obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x‖ ‖fderiv ℝ f x‖)
      refine mem_iUnion.mpr ⟨k, ⟨hx, ?_⟩, (le_max_right _ _).trans hk.le⟩
      simpa only [mem_closedBall, dist_zero_right] using (le_max_left _ _).trans hk.le
    apply measure_mono_null (image_mono hcover)
    rw [image_iUnion]
    exact measure_iUnion_null hnull
  -- the area formula for sets `E ⊆ A`
  have area_set : ∀ {P n : ℕ} {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin P)}
      {A : Set (EuclideanSpace ℝ (Fin n))}, InjOn g A → (∀ a ∈ A, DifferentiableAt ℝ g a) →
      ∀ {E : Set (EuclideanSpace ℝ (Fin n))}, MeasurableSet E → E ⊆ A →
      μHE[n] (g '' E) = ∫⁻ x in E, ENNReal.ofReal (Jac (fderiv ℝ g x)) ∂volume := by
    intro P n g A hgi hgd E hE hEA
    have hSm : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | Jac (fderiv ℝ g x) ≠ 0} :=
      (measurableSet_eq_fun (continuous_jac.measurable.comp (measurable_fderiv ℝ g))
        measurable_const).compl
    have hreg : μHE[n] (g '' (E ∩ {x | Jac (fderiv ℝ g x) ≠ 0})) =
        ∫⁻ x in E ∩ {x | Jac (fderiv ℝ g x) ≠ 0}, ENNReal.ofReal (Jac (fderiv ℝ g x)) ∂volume :=
      regular_area (hE.inter hSm)
        (fun x hx => (hgd x (hEA hx.1)).hasFDerivAt.hasFDerivWithinAt)
        (fun x hx => by
          by_contra hni
          exact hx.2 (jac_eq_zero _ hni))
        (hgi.mono (inter_subset_left.trans hEA))
    have hcrit : μHE[n] (g '' (E \ {x | Jac (fderiv ℝ g x) ≠ 0})) = 0 :=
      critical (hE.diff hSm) (fun x hx => hgd x (hEA hx.1))
        (fun x hx hinj => hx.2 (jac_pos _ hinj).ne')
    have hzero : ∫⁻ x in E \ {x | Jac (fderiv ℝ g x) ≠ 0},
        ENNReal.ofReal (Jac (fderiv ℝ g x)) ∂volume = 0 := by
      have h0 : ∀ x ∈ E \ {x | Jac (fderiv ℝ g x) ≠ 0},
          ENNReal.ofReal (Jac (fderiv ℝ g x)) = 0 := fun x hx => by
        have hx0 : Jac (fderiv ℝ g x) = 0 := not_not.mp hx.2
        rw [hx0, ENNReal.ofReal_zero]
      rw [setLIntegral_congr_fun (hE.diff hSm) h0, lintegral_zero]
    rw [← lintegral_inter_add_sdiff _ E hSm, hzero, add_zero, ← hreg]
    apply le_antisymm
    · calc μHE[n] (g '' E)
          = μHE[n] (g '' (E ∩ {x | Jac (fderiv ℝ g x) ≠ 0}) ∪
              g '' (E \ {x | Jac (fderiv ℝ g x) ≠ 0})) := by
            rw [← image_union, inter_union_sdiff]
        _ ≤ μHE[n] (g '' (E ∩ {x | Jac (fderiv ℝ g x) ≠ 0})) +
              μHE[n] (g '' (E \ {x | Jac (fderiv ℝ g x) ≠ 0})) := measure_union_le _ _
        _ = _ := by rw [hcrit, add_zero]
    · exact measure_mono (image_mono inter_subset_left)
  -- the weighted area formula (no measurability of the weight)
  have area_weighted : ∀ {P n : ℕ} {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin P)}
      {A : Set (EuclideanSpace ℝ (Fin n))}, MeasurableSet A → InjOn g A →
      (∀ a ∈ A, DifferentiableAt ℝ g a) → ∀ (w : EuclideanSpace ℝ (Fin P) → ℝ≥0∞),
      ∫⁻ y in g '' A, w y ∂μHE[n] =
        ∫⁻ x in A, ENNReal.ofReal (Jac (fderiv ℝ g x)) * w (g x) ∂volume := by
    intro P n g A hA hgi hgd w
    have hcont : ContinuousOn g A := fun x hx => (hgd x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hA hgi
    have hsub := MeasurableEmbedding.subtype_coe hA
    have hJm : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Jac (fderiv ℝ g x))) :=
      (continuous_jac.measurable.comp (measurable_fderiv ℝ g)).ennreal_ofReal
    have hmap : Measure.map (A.domRestrict g)
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (fun x => ENNReal.ofReal (Jac (fderiv ℝ g x)))).comap (Subtype.val : A → _)) =
        (μHE[n] : Measure (EuclideanSpace ℝ (Fin P))).restrict (g '' A) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hB : MeasurableSet (Subtype.val '' ((A.domRestrict g) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBs : Subtype.val '' ((A.domRestrict g) ⁻¹' t) ⊆ A := by
        rintro x ⟨u, _, rfl⟩
        exact u.property
      rw [withDensity_apply _ hB, ← area_set hgi hgd hB hBs, Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨hu, ⟨u, u.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.lintegral_map]
    change (∫⁻ x : A, (fun x : EuclideanSpace ℝ (Fin n) => w (g x)) x ∂
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (fun x => ENNReal.ofReal (Jac (fderiv ℝ g x)))).comap (Subtype.val : A → _))) = _
    rw [lintegral_subtype_comap hA (fun x : EuclideanSpace ℝ (Fin n) => w (g x)),
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hA]
    · rfl
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    · exact hJm.aemeasurable
  -- `|det (B ∘ L)| = √det(B uᵢ · B uⱼ) · J L` for `u` the standard basis of `range L`
  have stepA : ∀ {P n : ℕ} (B : EuclideanSpace ℝ (Fin P) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin P))
      (T : Submodule ℝ (EuclideanSpace ℝ (Fin P))),
      T = LinearMap.range (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin P)) →
      |LinearMap.det ((B.comp L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| =
        Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ T) =>
          inner ℝ (B (stdOrthonormalBasis ℝ T i)) (B (stdOrthonormalBasis ℝ T j)))) * Jac L := by
    intro P n B L T hT
    obtain ⟨ιu, hιiso, hιsingle, hιmem, hιsurj⟩ : ∃ ιu : EuclideanSpace ℝ (Fin (Module.finrank ℝ T))
        →L[ℝ] EuclideanSpace ℝ (Fin P), Isometry ιu ∧
        (∀ i, ιu (EuclideanSpace.single i 1) = stdOrthonormalBasis ℝ T i) ∧
        (∀ v, ιu v ∈ T) ∧ (∀ y ∈ T, ∃ v, ιu v = y) := by
      refine ⟨(T.subtypeₗᵢ.comp
          (stdOrthonormalBasis ℝ T).repr.symm.toLinearIsometry).toContinuousLinearMap,
        (T.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ T).repr.symm.toLinearIsometry).isometry,
        fun i => ?_, fun v => ?_, fun y hy => ?_⟩
      · change ((((stdOrthonormalBasis ℝ T).repr.symm (EuclideanSpace.single i 1)) : T) :
          EuclideanSpace ℝ (Fin P)) = _
        rw [OrthonormalBasis.repr_symm_single]
      · exact ((stdOrthonormalBasis ℝ T).repr.symm v).2
      · refine ⟨(stdOrthonormalBasis ℝ T).repr ⟨y, hy⟩, ?_⟩
        change ((((stdOrthonormalBasis ℝ T).repr.symm
          ((stdOrthonormalBasis ℝ T).repr ⟨y, hy⟩)) : T) : EuclideanSpace ℝ (Fin P)) = y
        rw [LinearIsometryEquiv.symm_apply_apply]
    have hJT : Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ T) =>
          inner ℝ (B (stdOrthonormalBasis ℝ T i)) (B (stdOrthonormalBasis ℝ T j)))) =
        Jac (B.comp ιu) := by
      rw [hJac]
      simp only [ContinuousLinearMap.comp_apply, hιsingle]
    rw [hJT]
    by_cases hL : Injective L
    · have hdim : Module.finrank ℝ T = n := by
        rw [hT, LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
      by_cases hBι : Injective (B.comp ιu)
      · -- compare the volumes of the image of the unit ball
        have hball0 : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
          (measure_ball_pos volume _ one_pos).ne'
        have hballtop : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
          measure_ball_lt_top.ne
        have hvol : (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) = volume :=
          EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
        have hS : ιu '' (ιu ⁻¹' (L '' ball 0 1)) = L '' ball 0 1 := by
          apply image_preimage_eq_of_subset
          rintro _ ⟨x, -, rfl⟩
          obtain ⟨v, hv⟩ := hιsurj (L x) (hT ▸ LinearMap.mem_range_self _ x)
          exact ⟨v, hv⟩
        have h1 := Measure.addHaar_image_linearMap volume
          ((B.comp L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
            EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (ball 0 1)
        have h2 : (B.comp L) '' ball 0 1 = (B.comp ιu) '' (ιu ⁻¹' (L '' ball 0 1)) := by
          rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp, image_comp,
            image_comp, hS]
        have h3 := linear_area hdim (B.comp ιu) hBι (ιu ⁻¹' (L '' ball 0 1))
        have h4 := linear_area rfl L hL (ball 0 1)
        have h5 : μHE[n] (ιu ⁻¹' (L '' ball 0 1)) = μHE[n] (L '' ball 0 1) := by
          rw [← hιiso.euclideanHausdorffMeasure_image, hS]
        change volume ((B.comp L) '' ball 0 1) = _ at h1
        rw [h2, ← hvol, h3, h5, h4, hvol] at h1
        rw [← mul_assoc, ← ENNReal.ofReal_mul (jac_nonneg _)] at h1
        have h6 := (ENNReal.mul_left_inj hball0 hballtop).mp h1
        rw [ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (jac_nonneg _) (jac_nonneg _))
          (abs_nonneg _)] at h6
        exact h6.symm
      · rw [jac_eq_zero _ hBι, zero_mul, abs_eq_zero, LinearMap.det_eq_zero_iff_ker_ne_bot]
        intro hker
        apply hBι
        intro v w hvw
        obtain ⟨x, hx⟩ : ιu v ∈ LinearMap.range
            (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin P)) := hT ▸ hιmem v
        obtain ⟨y, hy⟩ : ιu w ∈ LinearMap.range
            (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin P)) := hT ▸ hιmem w
        have hxy : x = y := by
          have hinj := LinearMap.ker_eq_bot.mp hker
          apply hinj
          change B (L x) = B (L y)
          rw [show L x = ιu v from hx, show L y = ιu w from hy]
          exact hvw
        apply hιiso.injective
        rw [← hx, ← hy, hxy]
    · rw [jac_eq_zero _ hL, mul_zero, abs_eq_zero, LinearMap.det_eq_zero_iff_ker_ne_bot]
      intro hker
      apply hL
      intro x y hxy
      have hinj := LinearMap.ker_eq_bot.mp hker
      apply hinj
      change B (L x) = B (L y)
      rw [hxy]
  -- the statement: apply the weighted area formula to `g`, then compare integrands a.e.
  intro P n g A Lg V F G T h hg hA hgi hgd hV hgV hFG hFd hT
  rw [area_weighted hA hgi hgd]
  refine lintegral_congr_ae ?_
  filter_upwards [hT, ae_restrict_mem hA] with a hTa ha
  have hFG' : F =ᶠ[𝓝 (g a)] G :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds (hgV (mem_image_of_mem g ha))) hFG
  rw [fderiv_comp a ((hFd (g a) (mem_image_of_mem g ha)).congr_of_eventuallyEq hFG'.symm)
      (hgd a ha), ← hFG'.fderiv_eq, stepA _ _ _ hTa, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
