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

theorem Submission.dorag_gc_graph_slope_le_projection : ∀ (n k P : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (A₁ A₂ : Euclid n →L[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ‖A₁‖ ≤ 1 / 4 → ‖A₂‖ ≤ 1 / 4 → ∑ i : Fin n, ‖(A₁ - A₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 4 * ∑ j : Fin P, ‖(LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₁.toLinearMap)).starProjection (EuclideanSpace.single j (1 : ℝ)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₂.toLinearMap)).starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  intro n k P ι ι' A₁ A₂ horth hA₁ hA₂
  set T₁ := LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₁.toLinearMap) with hT₁
  set T₂ := LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₂.toLinearMap) with hT₂
  set X : Euclid P →L[ℝ] Euclid P := T₁.starProjection - T₂.starProjection with hX
  have pyth : ∀ (v : Euclid n) (b : Euclid k), ‖ι v + ι' b‖ ^ 2 = ‖v‖ ^ 2 + ‖b‖ ^ 2 := by
    intro v b
    rw [norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]; ring
  have hXsa : ∀ u u' : Euclid P, inner ℝ (X u) u' = inner ℝ u (X u') := by
    intro u u'
    simp only [hX, sub_apply, inner_sub_left, inner_sub_right,
      Submodule.inner_starProjection_left_eq_right]
  set q : Euclid n → Euclid P := fun x => ι x + ι' (A₁ x) with hq
  -- pointwise estimate
  have hpt : ∀ x, ‖(A₁ - A₂) x‖ ^ 2 ≤ 17 / 16 * ‖X (q x)‖ ^ 2 := by
    intro x
    have hqT₁ : q x ∈ T₁ := ⟨x, by simp [hq]⟩
    have hP₁ : T₁.starProjection (q x) = q x := (Submodule.starProjection_eq_self_iff).2 hqT₁
    have hmem : T₂.starProjection (q x) ∈ T₂ := Submodule.starProjection_apply_mem _ _
    obtain ⟨w, hw⟩ := hmem
    have hw' : T₂.starProjection (q x) = ι w + ι' (A₂ w) := by
      rw [← hw]; simp
    have hXq : X (q x) = ι (x - w) + ι' (A₁ x - A₂ w) := by
      rw [hX, sub_apply, hP₁, hw']
      simp only [hq, map_sub]; abel
    have hnorm : ‖X (q x)‖ ^ 2 = ‖x - w‖ ^ 2 + ‖A₁ x - A₂ w‖ ^ 2 := by rw [hXq, pyth]
    have htri : ‖(A₁ - A₂) x‖ ≤ ‖A₁ x - A₂ w‖ + 1 / 4 * ‖x - w‖ := by
      have hsplit : (A₁ - A₂) x = (A₁ x - A₂ w) + A₂ (w - x) := by
        simp only [sub_apply, map_sub]; abel
      rw [hsplit]
      calc ‖(A₁ x - A₂ w) + A₂ (w - x)‖ ≤ ‖A₁ x - A₂ w‖ + ‖A₂ (w - x)‖ := norm_add_le _ _
        _ ≤ ‖A₁ x - A₂ w‖ + ‖A₂‖ * ‖w - x‖ := by gcongr; exact A₂.le_opNorm _
        _ ≤ ‖A₁ x - A₂ w‖ + 1 / 4 * ‖x - w‖ := by
            rw [norm_sub_rev w x]; gcongr
    rw [hnorm]
    have h0 := norm_nonneg ((A₁ - A₂) x)
    nlinarith [norm_nonneg (A₁ x - A₂ w), norm_nonneg (x - w),
      sq_nonneg (‖A₁ x - A₂ w‖ / 4 - ‖x - w‖), mul_self_le_mul_self h0 htri]
  -- frame bound
  have hframe : ∀ y : Euclid P, ∑ i : Fin n, (inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) y) ^ 2
      ≤ 17 / 16 * ‖y‖ ^ 2 := by
    intro y
    set a : Euclid n := (ι.toContinuousLinearMap.adjoint) y with ha
    set b : Euclid k := (ι'.toContinuousLinearMap.adjoint) y with hb
    set c : Euclid n := (A₁.adjoint) b with hc
    have hcoord : ∀ i, inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) y = (a + c) i := by
      intro i
      have e1 : inner ℝ (ι (EuclideanSpace.single i (1 : ℝ))) y =
          inner ℝ (EuclideanSpace.single i (1 : ℝ)) a := by
        rw [ha, ContinuousLinearMap.adjoint_inner_right]; rfl
      have e2 : inner ℝ (ι' (A₁ (EuclideanSpace.single i (1 : ℝ)))) y =
          inner ℝ (EuclideanSpace.single i (1 : ℝ)) c := by
        rw [hc, ContinuousLinearMap.adjoint_inner_right, hb,
          ContinuousLinearMap.adjoint_inner_right]; rfl
      simp only [hq, inner_add_left, e1, e2, EuclideanSpace.inner_single_left, map_one,
        one_mul, PiLp.add_apply]
    have hsum : ∑ i : Fin n, (inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) y) ^ 2 = ‖a + c‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoord i, Real.norm_eq_abs, sq_abs]
    have hcb : ‖c‖ ≤ 1 / 4 * ‖b‖ := by
      calc ‖c‖ ≤ ‖A₁.adjoint‖ * ‖b‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 / 4 * ‖b‖ := by
            gcongr
            rw [LinearIsometryEquiv.norm_map]; exact hA₁
    have hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      set u := ι a + ι' b with hu
      have hu2 : ‖u‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := pyth a b
      have huy : inner ℝ u y = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
        rw [hu, inner_add_left]
        have e1 : inner ℝ (ι a) y = inner ℝ a a := by
          rw [show inner ℝ (ι a) y = inner ℝ (ι.toContinuousLinearMap a) y from rfl,
            ← ContinuousLinearMap.adjoint_inner_right]
        have e2 : inner ℝ (ι' b) y = inner ℝ b b := by
          rw [show inner ℝ (ι' b) y = inner ℝ (ι'.toContinuousLinearMap b) y from rfl,
            ← ContinuousLinearMap.adjoint_inner_right]
        rw [e1, e2, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have hle : ‖u‖ ^ 2 ≤ ‖u‖ * ‖y‖ := by
        rw [hu2, ← huy]; exact real_inner_le_norm u y
      have hu0 := norm_nonneg u
      have hy0 := norm_nonneg y
      have : ‖u‖ ≤ ‖y‖ := by
        rcases hu0.lt_or_eq with h | h
        · nlinarith
        · rw [← h]; exact hy0
      rw [← hu2]; nlinarith
    rw [hsum]
    have hn := norm_add_le a c
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg (a + c),
      sq_nonneg (‖a‖ / 4 - ‖b‖), mul_self_le_mul_self (norm_nonneg (a + c)) hn]
  -- summation
  have hpar : ∀ v : Euclid P, ‖v‖ ^ 2 = ∑ j : Fin P, (inner ℝ v (EuclideanSpace.single j (1 : ℝ))) ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [EuclideanSpace.inner_single_right]; simp
  calc ∑ i : Fin n, ‖(A₁ - A₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
      ≤ ∑ i : Fin n, 17 / 16 * ‖X (q (EuclideanSpace.single i (1 : ℝ)))‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hpt _
    _ = 17 / 16 * ∑ j : Fin P, ∑ i : Fin n,
          (inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) (X (EuclideanSpace.single j (1 : ℝ)))) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hpar]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hXsa]
    _ ≤ 17 / 16 * ∑ j : Fin P, 17 / 16 * ‖X (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        gcongr with j
        exact hframe _
    _ ≤ 4 * ∑ j : Fin P, ‖T₁.starProjection (EuclideanSpace.single j (1 : ℝ)) -
          T₂.starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc]
        have hs : 0 ≤ ∑ j : Fin P, ‖X (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
          Finset.sum_nonneg fun j _ => sq_nonneg _
        have : ∑ j : Fin P, ‖X (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 = ∑ j : Fin P,
            ‖T₁.starProjection (EuclideanSpace.single j (1 : ℝ)) -
              T₂.starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
          simp [hX]
        rw [← this]
        nlinarith
/-- **Graph push-forward bound** (the inequality half of the area formula used in the graph-`C¹`
argument).  Let `Φ(v) = z + ι v + ι'(f v)` with `ι`, `ι'` isometric embeddings with orthogonal
ranges and `f` continuous, and suppose `Φ(A) ⊆ spt μ ∩ W`, where `Hⁿ((spt μ ∩ W) ∖ M) = 0` and
`μ = θ Hⁿ⌞M`.  Then `Φ_#(Lⁿ⌞A) ≤ μ⌞Φ(A)`: `π(x) = ι*(x − z)` is a `1`-Lipschitz left inverse of
`Φ`, so `Lⁿ(Z) = Hⁿ(π(Φ(Z))) ≤ Hⁿ(Φ(Z))`, and `Hⁿ ≤ μ` on subsets of `spt μ ∩ W` because
`(spt μ ∩ W) ∖ M` is `Hⁿ`-null and `θ ≥ 1` on `M`. -/
theorem Submission.dorag_gc_graph_map_volume_le_measure : ∀ (n k P : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (f : Euclid n → Euclid k) (z : Euclid P) (A : Set (Euclid n)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → Continuous f → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ v ∈ A, z + ι v + ι' (f v) ∈ R.measure.support ∩ W) → Measure.map (fun v => z + ι v + ι' (f v)) (volume.restrict A) ≤ R.measure.restrict ((fun v => z + ι v + ι' (f v)) '' A) := by
  intro n k P U W R ι ι' f z A horth hf hnull hA
  set Φ : Euclid n → Euclid P := fun v => z + ι v + ι' (f v) with hΦ
  have hΦc : Continuous Φ := by
    simp only [hΦ]
    exact (continuous_const.add ι.continuous).add (ι'.continuous.comp hf)
  -- 1. a 1-Lipschitz left inverse `π(x) = ι*(x − z)` of `Φ`
  set π : Euclid P → Euclid n := fun x => (ι.toContinuousLinearMap.adjoint) (x - z) with hπ
  have hπΦ : ∀ v, π (Φ v) = v := by
    intro v
    apply ext_inner_left ℝ
    intro u
    have hsub : z + ι v + ι' (f v) - z = ι v + ι' (f v) := by abel
    simp only [hπ, hΦ, ContinuousLinearMap.adjoint_inner_right,
      LinearIsometry.coe_toContinuousLinearMap, hsub, inner_add_right, LinearIsometry.inner_map_map]
    rw [horth u (f v), add_zero]
  have hπlip : LipschitzWith 1 π := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [hπ, dist_eq_norm, NNReal.coe_one, one_mul]
    rw [← map_sub, sub_sub_sub_cancel_right]
    calc ‖(ι.toContinuousLinearMap.adjoint) (x - y)‖
        ≤ ‖ι.toContinuousLinearMap.adjoint‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x - y‖ := by
          gcongr
          rw [LinearIsometryEquiv.norm_map]
          exact ι.norm_toContinuousLinearMap_le
      _ = ‖x - y‖ := one_mul _
  -- 2. `Lⁿ(Z) ≤ Hⁿ(Φ(Z))`, since `π(Φ(Z)) = Z` and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hvol : ∀ Z : Set (Euclid n), volume Z ≤ μHE[n] (Φ '' Z) := by
    intro Z
    have h1 : π '' (Φ '' Z) = Z := by
      rw [image_image]; simp [hπΦ]
    have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hπlip.lipschitzOnWith (s := Φ '' Z))
    rw [h1] at h2
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
    simpa using h2
  -- 3. `Hⁿ(T) ≤ μ(T)` for `T ⊆ spt μ ∩ W`, through a measurable hull of `T`
  have hHle : ∀ T ⊆ R.measure.support ∩ W, μHE[n] T ≤ R.measure T := by
    intro T hT
    set T' := toMeasurable R.measure T with hT'
    have hT'm : MeasurableSet T' := measurableSet_toMeasurable _ _
    calc μHE[n] T ≤ μHE[n] ((T' ∩ R.carrier) ∪ ((R.measure.support ∩ W) \ R.carrier)) := by
          apply measure_mono
          intro x hx
          by_cases hxM : x ∈ R.carrier
          · exact Or.inl ⟨subset_toMeasurable _ _ hx, hxM⟩
          · exact Or.inr ⟨hT hx, hxM⟩
      _ ≤ μHE[n] (T' ∩ R.carrier) + μHE[n] ((R.measure.support ∩ W) \ R.carrier) :=
          measure_union_le _ _
      _ = μHE[n] (T' ∩ R.carrier) := by rw [hnull, add_zero]
      _ ≤ R.measure T' := by
          unfold IMRep.measure
          rw [withDensity_apply _ hT'm, Measure.restrict_restrict hT'm]
          calc μHE[n] (T' ∩ R.carrier) = ∫⁻ _ in T' ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[n] := by
                simp
            _ ≤ ∫⁻ x in T' ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
                apply setLIntegral_mono' (hT'm.inter R.measurableSet_carrier)
                intro x hx
                exact_mod_cast R.mult_pos x hx.2
      _ = R.measure T := measure_toMeasurable _
  -- 4. test on measurable `Y`: `Lⁿ(Φ⁻¹(Y) ∩ A) ≤ μ(Φ(Φ⁻¹(Y) ∩ A)) ≤ μ(Y ∩ Φ(A))`
  rw [Measure.le_iff]
  intro Y hY
  rw [Measure.map_apply hΦc.measurable hY, Measure.restrict_apply (hΦc.measurable hY),
    Measure.restrict_apply hY]
  calc volume (Φ ⁻¹' Y ∩ A) ≤ μHE[n] (Φ '' (Φ ⁻¹' Y ∩ A)) := hvol _
    _ ≤ R.measure (Φ '' (Φ ⁻¹' Y ∩ A)) := hHle _ (by
        rintro _ ⟨v, hv, rfl⟩; exact hA v hv.2)
    _ ≤ R.measure (Y ∩ Φ '' A) := measure_mono (by
        rintro _ ⟨v, hv, rfl⟩; exact ⟨hv.1, v, hv.2, rfl⟩)
theorem Submission.dorag_gc_decay_plane_eq_approxTangent : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → ∀ᵐ x ∂R.measure, x ∈ W → ∀ (S : Submodule ℝ (Euclid P)) (s₀ K : ℝ), 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ y in closedBall x s, ENNReal.ofReal (∑ i : Fin P, ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → S = approxTangentPlane n R.carrier x := by
  -- generic facts, proved in a small context
  have aux_vec : ∀ (m : ℕ) (a b c : Euclid m), ‖a - b‖ ^ 2 ≤ 2 * ‖c - a‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
    intro m a b c
    have htri : ‖a - b‖ ≤ ‖c - a‖ + ‖c - b‖ := by
      calc ‖a - b‖ = ‖(c - b) - (c - a)‖ := by congr 1; abel
        _ ≤ ‖c - b‖ + ‖c - a‖ := norm_sub_le _ _
        _ = ‖c - a‖ + ‖c - b‖ := add_comm _ _
    nlinarith [norm_nonneg (a - b), norm_nonneg (c - a), norm_nonneg (c - b),
      sq_nonneg (‖c - a‖ - ‖c - b‖)]
  have aux_expand : ∀ (m : ℕ) (x : Euclid m), x = ∑ i : Fin m, x i • EuclideanSpace.single i (1 : ℝ) := by
    intro m x
    ext j; simp [Pi.single_apply]
  have aux_HS : ∀ (m : ℕ) (A : Euclid m →L[ℝ] Euclid m), ‖A‖ ≤ 2 →
      ∑ i : Fin m, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * m * ‖A‖ := by
    intro m A hA
    have h1 : ∀ i : Fin m, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * ‖A‖ := by
      intro i
      have hle : ‖A (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖A‖ := by
        simpa using A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
      have h0 := norm_nonneg (A (EuclideanSpace.single i (1 : ℝ)))
      nlinarith [norm_nonneg A]
    calc ∑ i : Fin m, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ ∑ _i : Fin m, 2 * ‖A‖ :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * m * ‖A‖ := by simp; ring
  intro P n U W R κ hW hWU hP hdens
  -- notation for the tangent projection field
  obtain ⟨p, hpdef⟩ : ∃ p : Euclid P → (Euclid P →L[ℝ] Euclid P),
      p = fun x => (approxTangentPlane n R.carrier x).starProjection := ⟨_, rfl⟩
  have hpx : ∀ x, p x = (approxTangentPlane n R.carrier x).starProjection := fun x => by rw [hpdef]
  have hpP : AEStronglyMeasurable p R.measure := by rw [hpdef]; exact hP
  have hpn : ∀ x, ‖p x‖ ≤ 1 := fun x => by rw [hpx]; exact Submodule.starProjection_norm_le _
  -- finiteness of μ on compact subsets of U
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    unfold IMRep.measure
    rw [withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  -- Step 1: Lebesgue points of p at μ-a.e. point of W
  have hleb : ∀ᵐ x ∂R.measure, x ∈ W → Tendsto (fun r => (∫⁻ y in closedBall x r, ‖p y - p x‖ₑ ∂R.measure) /
      R.measure (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    have hr : ∀ x : W, ∃ r : ℝ, 0 < r ∧ closedBall (x : Euclid P) r ⊆ W := by
      intro x
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x x.2
      exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
    choose r hr0 hrW using hr
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : W => ball (x : Euclid P) (r x / 2)) (fun _ => isOpen_ball)
    have hloc : ∀ i : W, ∀ᵐ x ∂R.measure, x ∈ ball (i : Euclid P) (r i / 2) →
        Tendsto (fun ρ => (∫⁻ y in closedBall x ρ, ‖p y - p x‖ₑ ∂R.measure) /
          R.measure (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) := by
      intro i
      have hBfin : R.measure (ball (i : Euclid P) (r i / 2)) ≠ ∞ :=
        (lt_of_le_of_lt (measure_mono (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith [hr0 i]))))
          (hfin _ (isCompact_closedBall _ _) ((hrW i).trans hWU))).ne
      have : IsFiniteMeasure (R.measure.restrict (ball (i : Euclid P) (r i / 2))) :=
        isFiniteMeasure_restrict.2 hBfin
      have hint : LocallyIntegrable p (R.measure.restrict (ball (i : Euclid P) (r i / 2))) :=
        (Integrable.of_bound hpP.restrict 1 (Eventually.of_forall hpn)).locallyIntegrable
      have h1 := (Besicovitch.vitaliFamily
        (R.measure.restrict (ball (i : Euclid P) (r i / 2)))).ae_tendsto_lintegral_enorm_sub_div hint
      rw [ae_restrict_iff' measurableSet_ball] at h1
      filter_upwards [h1] with x hx hxB
      have h2 := (hx hxB).comp (Besicovitch.tendsto_filterAt _ x)
      refine h2.congr' ?_
      have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), closedBall x ρ ⊆ ball (i : Euclid P) (r i / 2) := by
        have hd : 0 < r i / 2 - dist x i := by
          rw [mem_ball] at hxB; linarith
        filter_upwards [Ioo_mem_nhdsGT hd] with ρ hρ
        exact closedBall_subset_ball' (by linarith [hρ.2])
      filter_upwards [hev] with ρ hρ
      simp only [Function.comp]
      rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hρ,
        Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 hρ]
    have hall : ∀ᵐ x ∂R.measure, ∀ i ∈ T, x ∈ ball (i : Euclid P) (r i / 2) →
        Tendsto (fun ρ => (∫⁻ y in closedBall x ρ, ‖p y - p x‖ₑ ∂R.measure) /
          R.measure (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) :=
      (ae_ball_iff hTc).2 fun i _ => hloc i
    filter_upwards [hall] with x hx hxW
    have hxU : x ∈ ⋃ i ∈ T, ball (i : Euclid P) (r i / 2) := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨x, hxW⟩, mem_ball_self (half_pos (hr0 _))⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxU
    exact hx i hi hxi
  -- Step 2: the pointwise argument at good points
  have hsupp : ∀ᵐ x ∂R.measure, x ∈ R.measure.support :=
    measure_eq_zero_iff_ae_notMem.1 Measure.measure_compl_support |>.mono fun x hx => by
      simpa using hx
  have hωpos : (0 : ℝ≥0∞) < unitBallVolume n := measure_ball_pos _ _ one_pos
  have hωfin : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  filter_upwards [hleb, hsupp] with x hxleb hxs hxW S s₀ K hs₀ hdec
  obtain ⟨t₀, ht₀, hball₀⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ closedBall x t₀ ⊆ W := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  set Δ : ℝ := ∑ i : Fin P, ‖p x (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
    with hΔ
  have hΔ0 : 0 ≤ Δ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmeasI : AEMeasurable (fun y => ‖p y - p x‖ₑ) R.measure :=
    (hpP.sub aestronglyMeasurable_const).enorm
  -- the key inequality for small s
  have hkey : ∀ s : ℝ, 0 < s → s ≤ min s₀ t₀ →
      ENNReal.ofReal Δ ≤ (4 * P) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) /
        R.measure (closedBall x s)) + 2 * (ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n) := by
    intro s hs hsle
    have hss₀ : s ≤ s₀ := hsle.trans (min_le_left _ _)
    have hst₀ : s ≤ t₀ := hsle.trans (min_le_right _ _)
    have hsubW : closedBall x s ⊆ W := (closedBall_subset_closedBall hst₀).trans hball₀
    have hμpos : 0 < R.measure (closedBall x s) :=
      (Measure.mem_support_iff_forall x).1 hxs _ (closedBall_mem_nhds x hs)
    have hμfin : R.measure (closedBall x s) ≠ ∞ :=
      (hfin _ (isCompact_closedBall _ _) (hsubW.trans hWU)).ne
    -- pointwise bound
    have hpt : ∀ y, ENNReal.ofReal Δ ≤ (4 * P) * ‖p y - p x‖ₑ + 2 * ENNReal.ofReal (∑ i : Fin P,
        ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      intro y
      have hA : ‖p y - p x‖ ≤ 2 := by
        calc ‖p y - p x‖ ≤ ‖p y‖ + ‖p x‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (hpn y) (hpn x)
          _ = 2 := by norm_num
      have hHS := aux_HS P (p y - p x) hA
      have hreal : Δ ≤ 2 * (∑ i : Fin P, ‖(p y - p x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
          2 * (∑ i : Fin P, ‖p y (EuclideanSpace.single i (1 : ℝ)) -
            S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
        rw [hΔ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by
          simpa only [sub_apply] using aux_vec P (p x (EuclideanSpace.single i 1))
            (S.starProjection (EuclideanSpace.single i 1)) (p y (EuclideanSpace.single i 1))
      have hreal2 : Δ ≤ 4 * P * ‖p y - p x‖ + 2 * (∑ i : Fin P, ‖p y (EuclideanSpace.single i (1 : ℝ)) -
            S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
        nlinarith [hreal, hHS]
      calc ENNReal.ofReal Δ ≤ ENNReal.ofReal (4 * P * ‖p y - p x‖ + 2 * (∑ i : Fin P,
            ‖p y (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
            ENNReal.ofReal_le_ofReal hreal2
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by norm_num), ofReal_norm, hpx y]
            simp
    have hint : R.measure (closedBall x s) * ENNReal.ofReal Δ ≤
        (4 * P) * (∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) + 2 * ENNReal.ofReal (K * s ^ (n + 1)) := by
      rw [mul_comm, ← setLIntegral_const]
      calc _ ≤ ∫⁻ y in closedBall x s, ((4 * P) * ‖p y - p x‖ₑ + 2 * ENNReal.ofReal (∑ i : Fin P,
            ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ∂R.measure := lintegral_mono hpt
        _ = (4 * P) * (∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) + 2 * ∫⁻ y in closedBall x s,
            ENNReal.ofReal (∑ i : Fin P,
            ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
            rw [lintegral_add_left' ((hmeasI.restrict).const_mul _),
              lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top P)),
              lintegral_const_mul' _ _ (by simp)]
        _ ≤ _ := by gcongr; exact hdec s hs hss₀
    -- lower density
    have hlow := hdens x hxs s hs hsubW
    have hdiv : ENNReal.ofReal (K * s ^ (n + 1)) / R.measure (closedBall x s) ≤
        ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n := by
      rw [ENNReal.div_le_iff hμpos.ne' hμfin]
      calc ENNReal.ofReal (K * s ^ (n + 1)) ≤ ENNReal.ofReal (max K 0 * s ^ (n + 1)) :=
            ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _)
        _ = ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n * unitBallVolume n /
              ENNReal.ofReal (Real.exp (κ * s) / s ^ n) := by
            rw [ENNReal.div_mul_cancel hωpos.ne' hωfin, ← ENNReal.ofReal_div_of_pos (by positivity)]
            congr 1
            field_simp
            ring
        _ ≤ ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n * R.measure (closedBall x s) := by
            rw [mul_div_assoc]
            gcongr
            rw [ENNReal.div_le_iff (by positivity) ENNReal.ofReal_ne_top, mul_comm]
            exact hlow
    calc ENNReal.ofReal Δ = R.measure (closedBall x s) * ENNReal.ofReal Δ / R.measure (closedBall x s) := by
          rw [mul_comm, ENNReal.mul_div_cancel_right hμpos.ne' hμfin]
      _ ≤ ((4 * P) * (∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) + 2 * ENNReal.ofReal (K * s ^ (n + 1))) /
            R.measure (closedBall x s) := by gcongr
      _ = (4 * P) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) / R.measure (closedBall x s)) +
            2 * (ENNReal.ofReal (K * s ^ (n + 1)) / R.measure (closedBall x s)) := by
          rw [ENNReal.add_div, mul_div_assoc, mul_div_assoc]
      _ ≤ _ := by gcongr
  -- passing to the limit
  have hlim : Tendsto (fun s => (4 * P) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) /
        R.measure (closedBall x s)) + 2 * (ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s => (4 * (P : ℝ≥0∞)) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) /
        R.measure (closedBall x s))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hxleb hxW)
        (Or.inr (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top P)))
    have h2 : Tendsto (fun s : ℝ => 2 * (ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n))
        (𝓝[>] 0) (𝓝 0) := by
      have h3 : Tendsto (fun s : ℝ => ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s)))) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun s : ℝ => max K 0 * (s * Real.exp (κ * s))) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun s : ℝ => max K 0 * (s * Real.exp (κ * s))) := by fun_prop
          simpa using hc.tendsto 0
        simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.div_const h3 (Or.inr hωpos.ne')) (Or.inr (by simp))
    simpa using h1.add h2
  have hΔle : ENNReal.ofReal Δ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hs₀ ht₀)] with s hs
    exact hkey s hs.1 hs.2.le
  have hΔz : Δ = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hΔle bot_le)) hΔ0
  have hcomp : ∀ i : Fin P, p x (EuclideanSpace.single i (1 : ℝ)) = S.starProjection (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hΔz i (Finset.mem_univ _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))
  have hpeq : ∀ v, p x v = S.starProjection v := by
    intro v
    rw [aux_expand P v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hcomp i]
  ext v
  rw [← Submodule.starProjection_eq_self_iff (K := S), ← Submodule.starProjection_eq_self_iff
    (K := approxTangentPlane n R.carrier x), ← hpx x, hpeq v]
/-- **Campanato's criterion for the derivative** (steps 6 and 7 of the graph-`C¹` argument).  Let
`n ≥ 1`, `Ω ⊆ ℝⁿ` open, `C ≥ 0`, `s₁ > 0`, and suppose that for `Lⁿ`-a.e. `v ∈ Ω`, `f` is
differentiable at `v` and `∫_{B_s(v)} |Df(w) − Df(v)|² dw ≤ C s^{n+1}` for `0 < s ≤ s₁`, where
`|A|² = Σᵢ |A eᵢ|²`.  On the good set `G` of such `v`, averaging
`|Df(v₁) − Df(v₂)|² ≤ 2 |Df(w) − Df(v₁)|² + 2 |Df(w) − Df(v₂)|²` over the ball of radius `d / 2`
about the midpoint (`d = |v₁ − v₂| ≤ s₁`) gives `‖Df(v₁) − Df(v₂)‖² ≤ 2^{n+2} C ωₙ⁻¹ d`, so `Df` is
uniformly continuous on `G`.  As `Ω ∖ G` is null, `G` is dense in `Ω`, and `g = extendFrom G Df` is
continuous on `Ω`, equals `Df` on `G`, and hence is the derivative of `f` at a.e. point of `Ω`. -/
theorem Submission.dorag_gc_campanato_continuous_deriv : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (Ω : Set (Euclid n)) (C s₁ : ℝ), 0 < n → IsOpen Ω → 0 ≤ C → 0 < s₁ → (∀ᵐ v ∂volume, v ∈ Ω → DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ → ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal (C * s ^ (n + 1))) → ∃ g : Euclid n → (Euclid n →L[ℝ] Euclid k), ContinuousOn g Ω ∧ ∀ᵐ v ∂volume, v ∈ Ω → HasFDerivAt f (g v) v := by
  -- scalar and vector inequalities proved in an empty context
  have aux_vec : ∀ (m : ℕ) (a b c : Euclid m), ‖a - b‖ ^ 2 ≤ 2 * ‖c - a‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
    intro m a b c
    have htri : ‖a - b‖ ≤ ‖c - a‖ + ‖c - b‖ := by
      calc ‖a - b‖ = ‖(c - b) - (c - a)‖ := by congr 1; abel
        _ ≤ ‖c - b‖ + ‖c - a‖ := norm_sub_le _ _
        _ = ‖c - a‖ + ‖c - b‖ := add_comm _ _
    nlinarith [norm_nonneg (a - b), norm_nonneg (c - a), norm_nonneg (c - b),
      sq_nonneg (‖c - a‖ - ‖c - b‖)]
  have aux_div : ∀ (d ω C X : ℝ) (m : ℕ), 0 < d → 0 < ω →
      (d / 2) ^ m * ω * X ≤ 4 * (C * d ^ (m + 1)) → X ≤ 2 ^ (m + 2) * C / ω * d := by
    intro d ω C X m hd hω h
    have hpos : 0 < (d / 2) ^ m * ω := by positivity
    have e : 4 * (C * d ^ (m + 1)) = (d / 2) ^ m * ω * (2 ^ (m + 2) * C / ω * d) := by
      rw [div_pow, pow_succ, pow_succ 2 (m + 1), pow_succ 2 m]
      field_simp
      ring
    rw [e] at h
    exact le_of_mul_le_mul_left h hpos
  have aux_eps : ∀ (M ε t : ℝ), 0 ≤ M → 0 < ε → 0 ≤ t → t < ε ^ 2 / (M + 1) → M * t < ε ^ 2 := by
    intro M ε t hM hε ht h
    have h1 : M * t ≤ M * (ε ^ 2 / (M + 1)) := by gcongr
    have h2 : M * (ε ^ 2 / (M + 1)) < ε ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε, sq_pos_of_pos hε]
    linarith
  intro n k f Ω C s₁ hn hΩ hC hs₁ hcamp
  have : Nontrivial (Euclid n) := by
    have : 0 < Module.finrank ℝ (Euclid n) := by simp [hn]
    exact Module.nontrivial_of_finrank_pos this
  obtain ⟨G, hG⟩ : ∃ G : Set (Euclid n), G = {v | v ∈ Ω ∧ (DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n,
        ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        ENNReal.ofReal (C * s ^ (n + 1)))} := ⟨_, rfl⟩
  have hnull : volume (Ω \ G) = 0 := by
    rw [ae_iff] at hcamp
    refine measure_mono_null (fun v hv => ?_) hcamp
    rw [hG] at hv
    exact fun h => hv.2 ⟨hv.1, h hv.1⟩
  have hGmem : ∀ v ∈ G, v ∈ Ω ∧ DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n,
        ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        ENNReal.ofReal (C * s ^ (n + 1)) := fun v hv => by rw [hG] at hv; exact hv
  clear hcamp hG
  have hHSnn : ∀ A : Euclid n →L[ℝ] Euclid k,
      0 ≤ ∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    fun A => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hop : ∀ A : Euclid n →L[ℝ] Euclid k,
      ‖A‖ ^ 2 ≤ ∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    intro A
    have hbound : ‖A‖ ≤ Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
      have hx : x = ∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ) := by
        ext j; simp [Pi.single_apply]
      calc ‖A x‖ = ‖∑ i : Fin n, x i • A (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hx]
            simp [map_sum, map_smul]
        _ ≤ ∑ i : Fin n, ‖x i‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_smul]
        _ ≤ Real.sqrt (∑ i : Fin n, ‖x i‖ ^ 2) *
              Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖x‖ := by
            rw [EuclideanSpace.norm_eq, mul_comm]
    calc ‖A‖ ^ 2 ≤ (Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ^ 2 := by
          gcongr
      _ = _ := Real.sq_sqrt (hHSnn A)
  have hmeas : ∀ A : Euclid n →L[ℝ] Euclid k, Measurable fun w => ENNReal.ofReal
      (∑ i : Fin n, ‖(fderiv ℝ f w - A) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro A
    have hc : Continuous fun B : Euclid n →L[ℝ] Euclid k =>
        ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by fun_prop
    exact ENNReal.measurable_ofReal.comp (hc.measurable.comp ((measurable_fderiv ℝ f).sub_const A))
  have hωpos : (0 : ℝ≥0∞) < volume (ball (0 : Euclid n) 1) := measure_ball_pos _ _ one_pos
  have hωfin : volume (ball (0 : Euclid n) 1) ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = (volume (ball (0 : Euclid n) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ ENNReal.toReal_pos hωpos.ne' hωfin
  have hωeq : volume (ball (0 : Euclid n) 1) = ENNReal.ofReal ω := by
    rw [hωdef]; exact (ENNReal.ofReal_toReal hωfin).symm
  -- pointwise inequality for the Hilbert–Schmidt squares
  have hpt : ∀ v₁ v₂ w : Euclid n,
      ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f v₁ - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        2 * ENNReal.ofReal (∑ i : Fin n,
          ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        2 * ENNReal.ofReal (∑ i : Fin n,
          ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro v₁ v₂ w
    have hreal : ∑ i : Fin n, ‖(fderiv ℝ f v₁ - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤
        2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by
        simpa only [sub_apply] using aux_vec k
          (fderiv ℝ f v₁ (EuclideanSpace.single i 1))
          (fderiv ℝ f v₂ (EuclideanSpace.single i 1)) (fderiv ℝ f w (EuclideanSpace.single i 1))
    calc _ ≤ ENNReal.ofReal
          (2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
          2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          simp
  -- Hölder estimate on G
  have hHolder : ∀ v₁ ∈ G, ∀ v₂ ∈ G, 0 < dist v₁ v₂ → dist v₁ v₂ ≤ s₁ →
      ‖fderiv ℝ f v₁ - fderiv ℝ f v₂‖ ^ 2 ≤ 2 ^ (n + 2) * C / ω * dist v₁ v₂ := by
    intro v₁ h₁ v₂ h₂ hd hds
    have hm1 : dist (midpoint ℝ v₁ v₂) v₁ = dist v₁ v₂ / 2 := by
      rw [dist_midpoint_left, Real.norm_eq_abs, abs_two]; ring
    have hm2 : dist (midpoint ℝ v₁ v₂) v₂ = dist v₁ v₂ / 2 := by
      rw [dist_midpoint_right, Real.norm_eq_abs, abs_two]; ring
    have hsub1 : ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2) ⊆ ball v₁ (dist v₁ v₂) :=
      ball_subset_ball' (by rw [hm1]; linarith)
    have hsub2 : ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2) ⊆ ball v₂ (dist v₁ v₂) :=
      ball_subset_ball' (by rw [hm2]; linarith)
    have hint : volume (ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2)) * ENNReal.ofReal (∑ i : Fin n,
        ‖(fderiv ℝ f v₁ - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        4 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) := by
      rw [mul_comm, ← setLIntegral_const]
      calc _ ≤ ∫⁻ w in ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2), (2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
            2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
            lintegral_mono fun w => hpt v₁ v₂ w
        _ = (∫⁻ w in ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) +
            ∫⁻ w in ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
            lintegral_add_left ((hmeas _).const_mul 2) _
        _ ≤ (∫⁻ w in ball v₁ (dist v₁ v₂), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) +
            ∫⁻ w in ball v₂ (dist v₁ v₂), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
            add_le_add (lintegral_mono_set hsub1) (lintegral_mono_set hsub2)
        _ = 2 * (∫⁻ w in ball v₁ (dist v₁ v₂), ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) +
            2 * ∫⁻ w in ball v₂ (dist v₁ v₂), ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [lintegral_const_mul _ (hmeas _), lintegral_const_mul _ (hmeas _)]
        _ ≤ 2 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) + 2 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) :=
            by
              gcongr
              · exact (hGmem v₁ h₁).2.2 _ hd hds
              · exact (hGmem v₂ h₂).2.2 _ hd hds
        _ = 4 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) := by ring
    rw [Measure.addHaar_ball _ _ (by linarith : (0 : ℝ) ≤ dist v₁ v₂ / 2), finrank_euclideanSpace_fin, hωeq,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
    exact (hop _).trans (aux_div _ _ _ _ n hd hω hint)
  -- uniform continuity of the derivative on G
  have hUC : UniformContinuousOn (fderiv ℝ f) G := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    have hM0 : 0 ≤ 2 ^ (n + 2) * C / ω := by positivity
    refine ⟨min s₁ (ε ^ 2 / (2 ^ (n + 2) * C / ω + 1)),
      lt_min hs₁ (div_pos (pow_pos hε 2) (by linarith)), fun a ha b hb hab => ?_⟩
    rcases (dist_nonneg : 0 ≤ dist a b).lt_or_eq with hpos | hzero
    · have h1 := hHolder a ha b hb hpos (hab.le.trans (min_le_left _ _))
      have h3 : ‖fderiv ℝ f a - fderiv ℝ f b‖ ^ 2 < ε ^ 2 :=
        lt_of_le_of_lt h1 (aux_eps _ _ _ hM0 hε dist_nonneg (lt_of_lt_of_le hab (min_le_right _ _)))
      rw [dist_eq_norm]
      exact (abs_lt_of_sq_lt_sq' h3 hε.le).2
    · have : a = b := dist_eq_zero.1 hzero.symm
      subst this
      simpa using hε
  -- density of G in Ω
  have hdense : Ω ⊆ closure G := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hsub : ball x ε ∩ Ω ⊆ Ω \ G := fun y hy => ⟨hy.2, fun hyG => by
      have := hcon y hyG
      have hy1 : dist y x < ε := hy.1
      rw [dist_comm] at hy1
      exact absurd hy1 (not_lt.2 this)⟩
    have hpos : 0 < volume (ball x ε ∩ Ω) :=
      (isOpen_ball.inter hΩ).measure_pos _ ⟨x, mem_ball_self hε, hx⟩
    exact absurd (measure_mono_null hsub hnull) hpos.ne'
  -- the continuous extension
  have hlim : ∀ x ∈ Ω, ∃ y, Tendsto (fderiv ℝ f) (𝓝[G] x) (𝓝 y) := by
    intro x hx
    have : (𝓝[G] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense hx)
    have hc : Cauchy (map (fderiv ℝ f) (𝓝[G] x)) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
      refine ⟨fderiv ℝ f '' (G ∩ ball x (δ / 2)), ?_, ?_⟩
      · rw [mem_map]
        refine mem_of_superset (inter_mem_nhdsWithin G (ball_mem_nhds x (half_pos hδ))) ?_
        intro y hy
        exact ⟨y, hy, rfl⟩
      · rintro _ ⟨a, ⟨haG, hax⟩, rfl⟩ _ ⟨b, ⟨hbG, hbx⟩, rfl⟩
        refine hδ' a haG b hbG ?_
        rw [mem_ball] at hax hbx
        calc dist a b ≤ dist a x + dist b x := dist_triangle_right _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add hax hbx
          _ = δ := by ring
    obtain ⟨y, hy⟩ := CompleteSpace.complete hc
    exact ⟨y, hy⟩
  refine ⟨extendFrom G (fderiv ℝ f), continuousOn_extendFrom hdense hlim, ?_⟩
  have hext := extendFrom_extends hUC.continuousOn
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) hnull
  simp only [mem_ofPred_eq, not_imp] at hv
  refine ⟨hv.1, fun hvG => hv.2 ?_⟩
  rw [hext v hvG]
  exact (hGmem v hvG).2.1.hasFDerivAt

theorem Submission.dorag_gc_graph_tangent_ae : ∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (κ : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (z : Euclid (n + k)) (a : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ v : Euclid n, x = z + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ 1 / 4 * ‖v - w‖) → f 0 = 0 → 0 < a → closedBall z a ⊆ W → R.measure.support ∩ closedBall z a = range (fun v => z + ι v + ι' (f v)) ∩ closedBall z a → ∀ᵐ v ∂volume, v ∈ ball (0 : Euclid n) (4 * a / 5) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier (z + ι v + ι' (f v)) = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) ∧ ∀ (S : Submodule ℝ (Euclid (n + k))) (s₀ K : ℝ), 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall (z + ι v + ι' (f v)) s, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → S = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) := by
  intro n k U W R κ ι ι' f z a hW hWU hP hdens hnull htan horth hfL hf0 ha hball hspt
  set Φ : Euclid n → Euclid (n + k) := fun v => z + ι v + ι' (f v) with hΦ
  -- Step 1 (geometry): `f` is `¼`-Lipschitz, so `f` and `Φ` are continuous, and for `|v| < 4a/5`,
  -- `|Φ(v) − z|² = |v|² + |f(v)|² ≤ (17/16)|v|² < a²`, so `Φ(v) ∈ spt μ ∩ B_a(z) ⊆ spt μ ∩ W`.
  have hLip : LipschitzWith (1 / 4 : NNReal) f :=
    LipschitzWith.of_dist_le_mul fun v w => by simpa [dist_eq_norm] using hfL v w
  have hfc : Continuous f := hLip.continuous
  have hΦc : Continuous Φ := by
    simp only [hΦ]
    fun_prop
  have hgeo : ∀ v ∈ ball (0 : Euclid n) (4 * a / 5), Φ v ∈ R.measure.support ∩ W := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    have hfv : ‖f v‖ ≤ 1 / 4 * ‖v‖ := by simpa [hf0] using hfL v 0
    have hsq : ‖Φ v - z‖ ^ 2 = ‖v‖ ^ 2 + ‖f v‖ ^ 2 := by
      have hΦz : Φ v - z = ι v + ι' (f v) := by
        simp only [hΦ]
        abel
      rw [hΦz, norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]
      ring
    have h1 : ‖f v‖ ^ 2 ≤ (1 / 4 * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfv 2
    have h2 : ‖v‖ ^ 2 ≤ (4 * a / 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv.le 2
    have hle : ‖Φ v - z‖ ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    have hmem : Φ v ∈ range Φ ∩ closedBall z a :=
      ⟨mem_range_self v, mem_closedBall_iff_norm.2 (abs_le_of_sq_le_sq' hle ha.le).2⟩
    rw [← hspt] at hmem
    exact ⟨hmem.1, hball hmem.2⟩
  -- Step 2 (transfer): graph_pushforward gives `Φ_#(Lⁿ⌞B̆_{4a/5}(0)) ≤ μ⌞Φ(B̆_{4a/5}(0)) ≤ μ`, so a
  -- property of `μ`-a.e. `x` holds at `Φ(v)` for `Lⁿ`-a.e. `v ∈ B̆_{4a/5}(0)`.
  have hmap := Submission.dorag_gc_graph_map_volume_le_measure n k (n + k) U W R ι ι' f z
    (ball (0 : Euclid n) (4 * a / 5)) horth hfc hnull hgeo
  have htransfer : ∀ Q : Euclid (n + k) → Prop, (∀ᵐ x ∂R.measure, Q x) →
      ∀ᵐ v ∂volume, v ∈ ball (0 : Euclid n) (4 * a / 5) → Q (Φ v) := by
    intro Q hQ
    have hQ' : ∀ᵐ x ∂(Measure.map Φ (volume.restrict (ball (0 : Euclid n) (4 * a / 5)))), Q x :=
      ae_mono (hmap.trans Measure.restrict_le_self) hQ
    exact (ae_restrict_iff' measurableSet_ball).1 (ae_of_ae_map hΦc.measurable.aemeasurable hQ')
  -- Step 3 (`htan` for `μ`): `μ⌞W = (Hⁿ⌞(M ∩ W)).withDensity θ ≪ Hⁿ⌞(M ∩ W)`.
  have htanμ : ∀ᵐ x ∂R.measure, x ∈ W → ∀ v : Euclid n, x = z + ι v + ι' (f v) →
      DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x =
        LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) := by
    have hac : R.measure.restrict W ≪ μHE[n].restrict (R.carrier ∩ W) := by
      unfold IMRep.measure
      rw [restrict_withDensity hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
        inter_comm]
      exact withDensity_absolutelyContinuous _ _
    exact (ae_restrict_iff' hW.measurableSet).1 (hac.ae_le htan)
  -- Step 4 (decay planes): by decay_plane, at `μ`-a.e. `x ∈ W` every plane `S` with a tilt-excess
  -- decay bound at `x` is `TₓM`.
  have hdecay := Submission.dorag_gc_decay_plane_eq_approxTangent (n + k) n U W R κ hW hWU hP
    hdens
  -- Step 5: combine Steps 3 and 4 at `x = Φ(v) ∈ W`, with the witness `v`.
  filter_upwards [htransfer _ (htanμ.and hdecay)] with v hv hvB
  obtain ⟨htv, hdv⟩ := hv hvB
  have hΦW : Φ v ∈ W := (hgeo v hvB).2
  obtain ⟨hdiff, hT⟩ := htv hΦW v rfl
  exact ⟨hdiff, hT, fun S s₀ K hs₀ hS => (hdv hΦW S s₀ K hs₀ hS).trans hT⟩
theorem Submission.dorag_gc_graph_slope_le_projection : ∀ (n k P : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (A₁ A₂ : Euclid n →L[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ‖A₁‖ ≤ 1 / 4 → ‖A₂‖ ≤ 1 / 4 → ∑ i : Fin n, ‖(A₁ - A₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 4 * ∑ j : Fin P, ‖(LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₁.toLinearMap)).starProjection (EuclideanSpace.single j (1 : ℝ)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₂.toLinearMap)).starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  intro n k P ι ι' A₁ A₂ horth hA₁ hA₂
  set T₁ := LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₁.toLinearMap) with hT₁
  set T₂ := LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ A₂.toLinearMap) with hT₂
  set X : Euclid P →L[ℝ] Euclid P := T₁.starProjection - T₂.starProjection with hX
  have pyth : ∀ (v : Euclid n) (b : Euclid k), ‖ι v + ι' b‖ ^ 2 = ‖v‖ ^ 2 + ‖b‖ ^ 2 := by
    intro v b
    rw [norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]; ring
  have hXsa : ∀ u u' : Euclid P, inner ℝ (X u) u' = inner ℝ u (X u') := by
    intro u u'
    simp only [hX, sub_apply, inner_sub_left, inner_sub_right,
      Submodule.inner_starProjection_left_eq_right]
  set q : Euclid n → Euclid P := fun x => ι x + ι' (A₁ x) with hq
  -- pointwise estimate
  have hpt : ∀ x, ‖(A₁ - A₂) x‖ ^ 2 ≤ 17 / 16 * ‖X (q x)‖ ^ 2 := by
    intro x
    have hqT₁ : q x ∈ T₁ := ⟨x, by simp [hq]⟩
    have hP₁ : T₁.starProjection (q x) = q x := (Submodule.starProjection_eq_self_iff).2 hqT₁
    have hmem : T₂.starProjection (q x) ∈ T₂ := Submodule.starProjection_apply_mem _ _
    obtain ⟨w, hw⟩ := hmem
    have hw' : T₂.starProjection (q x) = ι w + ι' (A₂ w) := by
      rw [← hw]; simp
    have hXq : X (q x) = ι (x - w) + ι' (A₁ x - A₂ w) := by
      rw [hX, sub_apply, hP₁, hw']
      simp only [hq, map_sub]; abel
    have hnorm : ‖X (q x)‖ ^ 2 = ‖x - w‖ ^ 2 + ‖A₁ x - A₂ w‖ ^ 2 := by rw [hXq, pyth]
    have htri : ‖(A₁ - A₂) x‖ ≤ ‖A₁ x - A₂ w‖ + 1 / 4 * ‖x - w‖ := by
      have hsplit : (A₁ - A₂) x = (A₁ x - A₂ w) + A₂ (w - x) := by
        simp only [sub_apply, map_sub]; abel
      rw [hsplit]
      calc ‖(A₁ x - A₂ w) + A₂ (w - x)‖ ≤ ‖A₁ x - A₂ w‖ + ‖A₂ (w - x)‖ := norm_add_le _ _
        _ ≤ ‖A₁ x - A₂ w‖ + ‖A₂‖ * ‖w - x‖ := by gcongr; exact A₂.le_opNorm _
        _ ≤ ‖A₁ x - A₂ w‖ + 1 / 4 * ‖x - w‖ := by
            rw [norm_sub_rev w x]; gcongr
    rw [hnorm]
    have h0 := norm_nonneg ((A₁ - A₂) x)
    nlinarith [norm_nonneg (A₁ x - A₂ w), norm_nonneg (x - w),
      sq_nonneg (‖A₁ x - A₂ w‖ / 4 - ‖x - w‖), mul_self_le_mul_self h0 htri]
  -- frame bound
  have hframe : ∀ y : Euclid P, ∑ i : Fin n, (inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) y) ^ 2
      ≤ 17 / 16 * ‖y‖ ^ 2 := by
    intro y
    set a : Euclid n := (ι.toContinuousLinearMap.adjoint) y with ha
    set b : Euclid k := (ι'.toContinuousLinearMap.adjoint) y with hb
    set c : Euclid n := (A₁.adjoint) b with hc
    have hcoord : ∀ i, inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) y = (a + c) i := by
      intro i
      have e1 : inner ℝ (ι (EuclideanSpace.single i (1 : ℝ))) y =
          inner ℝ (EuclideanSpace.single i (1 : ℝ)) a := by
        rw [ha, ContinuousLinearMap.adjoint_inner_right]; rfl
      have e2 : inner ℝ (ι' (A₁ (EuclideanSpace.single i (1 : ℝ)))) y =
          inner ℝ (EuclideanSpace.single i (1 : ℝ)) c := by
        rw [hc, ContinuousLinearMap.adjoint_inner_right, hb,
          ContinuousLinearMap.adjoint_inner_right]; rfl
      simp only [hq, inner_add_left, e1, e2, EuclideanSpace.inner_single_left, map_one,
        one_mul, PiLp.add_apply]
    have hsum : ∑ i : Fin n, (inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) y) ^ 2 = ‖a + c‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoord i, Real.norm_eq_abs, sq_abs]
    have hcb : ‖c‖ ≤ 1 / 4 * ‖b‖ := by
      calc ‖c‖ ≤ ‖A₁.adjoint‖ * ‖b‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 / 4 * ‖b‖ := by
            gcongr
            rw [LinearIsometryEquiv.norm_map]; exact hA₁
    have hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      set u := ι a + ι' b with hu
      have hu2 : ‖u‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := pyth a b
      have huy : inner ℝ u y = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
        rw [hu, inner_add_left]
        have e1 : inner ℝ (ι a) y = inner ℝ a a := by
          rw [show inner ℝ (ι a) y = inner ℝ (ι.toContinuousLinearMap a) y from rfl,
            ← ContinuousLinearMap.adjoint_inner_right]
        have e2 : inner ℝ (ι' b) y = inner ℝ b b := by
          rw [show inner ℝ (ι' b) y = inner ℝ (ι'.toContinuousLinearMap b) y from rfl,
            ← ContinuousLinearMap.adjoint_inner_right]
        rw [e1, e2, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have hle : ‖u‖ ^ 2 ≤ ‖u‖ * ‖y‖ := by
        rw [hu2, ← huy]; exact real_inner_le_norm u y
      have hu0 := norm_nonneg u
      have hy0 := norm_nonneg y
      have : ‖u‖ ≤ ‖y‖ := by
        rcases hu0.lt_or_eq with h | h
        · nlinarith
        · rw [← h]; exact hy0
      rw [← hu2]; nlinarith
    rw [hsum]
    have hn := norm_add_le a c
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg (a + c),
      sq_nonneg (‖a‖ / 4 - ‖b‖), mul_self_le_mul_self (norm_nonneg (a + c)) hn]
  -- summation
  have hpar : ∀ v : Euclid P, ‖v‖ ^ 2 = ∑ j : Fin P, (inner ℝ v (EuclideanSpace.single j (1 : ℝ))) ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [EuclideanSpace.inner_single_right]; simp
  calc ∑ i : Fin n, ‖(A₁ - A₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
      ≤ ∑ i : Fin n, 17 / 16 * ‖X (q (EuclideanSpace.single i (1 : ℝ)))‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hpt _
    _ = 17 / 16 * ∑ j : Fin P, ∑ i : Fin n,
          (inner ℝ (q (EuclideanSpace.single i (1 : ℝ))) (X (EuclideanSpace.single j (1 : ℝ)))) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hpar]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hXsa]
    _ ≤ 17 / 16 * ∑ j : Fin P, 17 / 16 * ‖X (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        gcongr with j
        exact hframe _
    _ ≤ 4 * ∑ j : Fin P, ‖T₁.starProjection (EuclideanSpace.single j (1 : ℝ)) -
          T₂.starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc]
        have hs : 0 ≤ ∑ j : Fin P, ‖X (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
          Finset.sum_nonneg fun j _ => sq_nonneg _
        have : ∑ j : Fin P, ‖X (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 = ∑ j : Fin P,
            ‖T₁.starProjection (EuclideanSpace.single j (1 : ℝ)) -
              T₂.starProjection (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
          simp [hX]
        rw [← this]
        nlinarith

theorem Submission.dorag_gc_graph_slope_campanato : ∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (κ : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (z : Euclid (n + k)) (a s₀ K : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ v : Euclid n, x = z + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ 1 / 4 * ‖v - w‖) → f 0 = 0 → 0 < a → 0 < s₀ → closedBall z a ⊆ W → R.measure.support ∩ closedBall z a = range (fun v => z + ι v + ι' (f v)) ∩ closedBall z a → (∀ ξ ∈ R.measure.support ∩ closedBall z a, ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall ξ s, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → ∃ C s₁ : ℝ, 0 ≤ C ∧ 0 < s₁ ∧ ∀ᵐ v ∂volume, v ∈ ball (0 : Euclid n) (a / 2) → DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ → ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal (C * s ^ (n + 1)) := by
  intro n k U W R κ ι ι' f z a s₀ K hW hWU hP hdens hnull htan horth hfL hf0 ha hs₀ hball hspt hdecay
  set Φ : Euclid n → Euclid (n + k) := fun v => z + ι v + ι' (f v) with hΦdef
  have hLip : LipschitzWith (1 / 4 : NNReal) f := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    simpa [dist_eq_norm] using hfL v w
  have hfc : Continuous f := hLip.continuous
  have hΦc : Continuous Φ := by
    simp only [hΦdef]; fun_prop
  -- `|Φ(v) − Φ(w)|² = |v − w|² + |f(v) − f(w)|² ≤ (17/16)|v − w|²`
  have hsq : ∀ v w, ‖Φ v - Φ w‖ ^ 2 = ‖v - w‖ ^ 2 + ‖f v - f w‖ ^ 2 := by
    intro v w
    have : Φ v - Φ w = ι (v - w) + ι' (f v - f w) := by
      simp only [hΦdef, map_sub]; abel
    rw [this, norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]
    ring
  have hΦlip : ∀ v w, ‖Φ v - Φ w‖ ^ 2 ≤ 17 / 16 * ‖v - w‖ ^ 2 := by
    intro v w
    rw [hsq]
    have h2 : ‖f v - f w‖ ^ 2 ≤ (1 / 4 * ‖v - w‖) ^ 2 := by gcongr; exact hfL v w
    nlinarith
  -- for `|v| < 4a/5`, `Φ(v) ∈ spt μ ∩ W` and `Φ(v) ∈ B_a(z)`
  have hgeo : ∀ v ∈ ball (0 : Euclid n) (4 * a / 5),
      Φ v ∈ R.measure.support ∩ W ∧ Φ v ∈ closedBall z a := by
    intro v hv
    have hv' : ‖v‖ < 4 * a / 5 := by simpa using hv
    have hΦ0 : Φ 0 = z := by simp [hΦdef, hf0]
    have h1 : ‖Φ v - z‖ ^ 2 ≤ a ^ 2 := by
      have := hΦlip v 0
      rw [hΦ0, sub_zero] at this
      have h3 : ‖v‖ ^ 2 ≤ (4 * a / 5) ^ 2 := by gcongr
      nlinarith [norm_nonneg v]
    have hle : ‖Φ v - z‖ ≤ a := by
      nlinarith [norm_nonneg (Φ v - z), sq_nonneg (‖Φ v - z‖ - a), sq_nonneg (‖Φ v - z‖ + a)]
    have hcb : Φ v ∈ closedBall z a := by simpa [dist_eq_norm] using hle
    have hmem : Φ v ∈ range Φ ∩ closedBall z a := ⟨⟨v, rfl⟩, hcb⟩
    rw [← hspt] at hmem
    exact ⟨⟨hmem.1, hball hmem.2⟩, hcb⟩
  -- good parameters: a.e. `v` with `|v| < 4a/5` (graph_tangent_ae)
  have hT := Submission.dorag_gc_graph_tangent_ae n k U W R κ ι ι' f z a hW hWU hP hdens hnull htan
    horth hfL hf0 ha hball hspt
  refine ⟨2 ^ (n + 3) * max K 0, min (s₀ / 2) (a / 8), by positivity, by positivity, ?_⟩
  filter_upwards [hT] with v hv hvball
  have hv' : ‖v‖ < a / 2 := by simpa using hvball
  have hvΩ : v ∈ ball (0 : Euclid n) (4 * a / 5) := by
    simp only [mem_ball, dist_zero_right]; linarith
  obtain ⟨hdiff, -, hSv⟩ := hv hvΩ
  refine ⟨hdiff, fun s hs hs₁ => ?_⟩
  have hs2 : s ≤ s₀ / 2 := le_trans hs₁ (min_le_left _ _)
  have hs8 : s ≤ a / 8 := le_trans hs₁ (min_le_right _ _)
  obtain ⟨hξ, hξball⟩ := hgeo v hvΩ
  -- the decay plane at `ξ = Φ(v)` is `graph Df(v)`
  obtain ⟨S, -, hS⟩ := hdecay (Φ v) ⟨hξ.1, hξball⟩
  have hSeq := hSv S s₀ K hs₀ hS
  have hsub : ball v s ⊆ ball (0 : Euclid n) (4 * a / 5) := by
    intro w hw
    simp only [mem_ball, dist_zero_right] at hw ⊢
    rw [dist_eq_norm] at hw
    calc ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by
            simpa using norm_add_le (w - v) v
      _ < s + a / 2 := by linarith
      _ < 4 * a / 5 := by linarith
  set wt : Euclid (n + k) → ℝ≥0∞ := fun x => ENNReal.ofReal (∑ i : Fin (n + k),
    ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
      S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) with hwt
  -- pointwise: `|Df(w) − Df(v)|² ≤ 4|p_{Φ(w)} − p_S|²` for a.e. `w ∈ B̆ⁿ_s(v)` (graph_projection)
  have hae : ∀ᵐ w ∂(volume.restrict (ball v s)),
      ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
        ≤ 4 * wt (Φ w) := by
    have h1 : ∀ᵐ w ∂(volume.restrict (ball v s)), w ∈ ball (0 : Euclid n) (4 * a / 5) →
        DifferentiableAt ℝ f w ∧ approxTangentPlane n R.carrier (Φ w) =
          LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f w).toLinearMap) ∧ _ :=
      ae_restrict_of_ae hT
    filter_upwards [h1, ae_restrict_mem measurableSet_ball] with w hw hwb
    obtain ⟨-, htw, -⟩ := hw (hsub hwb)
    have hA := Submission.dorag_gc_graph_slope_le_projection n k (n + k) ι ι' (fderiv ℝ f w)
      (fderiv ℝ f v) horth (by simpa using norm_fderiv_le_of_lipschitz ℝ hLip)
      (by simpa using norm_fderiv_le_of_lipschitz ℝ hLip)
    -- `starProjection` depends on the submodule through its instance, so rewrite via congruence
    have key : ∀ (K₁ K₂ : Submodule ℝ (Euclid (n + k))) [K₁.HasOrthogonalProjection]
        [K₂.HasOrthogonalProjection], K₁ = K₂ → K₁.starProjection = K₂.starProjection := by
      intro K₁ K₂ _ _ h; subst h; rfl
    rw [key _ _ htw.symm, key _ _ hSeq.symm] at hA
    rw [hwt]
    simp only
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hA
  -- `Φ(B̆ⁿ_s(v)) ⊆ B_{2s}(ξ)`
  have himage : Φ '' ball v s ⊆ closedBall (Φ v) (2 * s) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hΦlip w v
    have h2 : ‖w - v‖ ^ 2 ≤ s ^ 2 := by gcongr
    nlinarith [norm_nonneg (Φ w - Φ v), norm_nonneg (w - v)]
  -- `Φ_#(Lⁿ⌞B̆ⁿ_s(v)) ≤ μ⌞Φ(B̆ⁿ_s(v))` (graph_pushforward)
  have hmap := Submission.dorag_gc_graph_map_volume_le_measure n k (n + k) U W R ι ι' f z
    (ball v s) horth hfc hnull (fun w hw => (hgeo w (hsub hw)).1)
  have hwtm : AEMeasurable wt R.measure := by
    have hc : Continuous (fun T : Euclid (n + k) →L[ℝ] Euclid (n + k) => ENNReal.ofReal (∑ i : Fin (n + k),
        ‖T (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    exact hc.measurable.comp_aemeasurable hP.aemeasurable
  have hwtm' : AEMeasurable wt (Measure.map Φ (volume.restrict (ball v s))) :=
    hwtm.mono_measure (hmap.trans Measure.restrict_le_self)
  calc ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n,
          ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
        ≤ ∫⁻ w in ball v s, 4 * wt (Φ w) := lintegral_mono_ae hae
    _ = 4 * ∫⁻ w in ball v s, wt (Φ w) := by
        rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
    _ = 4 * ∫⁻ x, wt x ∂(Measure.map Φ (volume.restrict (ball v s))) := by
        rw [lintegral_map' hwtm' hΦc.measurable.aemeasurable]
    _ ≤ 4 * ∫⁻ x, wt x ∂(R.measure.restrict (closedBall (Φ v) (2 * s))) := by
        gcongr
        exact hmap.trans (Measure.restrict_mono himage le_rfl)
    _ ≤ 4 * ENNReal.ofReal (K * (2 * s) ^ (n + 1)) := by
        gcongr
        exact hS (2 * s) (by positivity) (by linarith)
    _ ≤ ENNReal.ofReal (2 ^ (n + 3) * max K 0 * s ^ (n + 1)) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have hsp : 0 ≤ s ^ (n + 1) := by positivity
        have : 4 * (K * (2 * s) ^ (n + 1)) = 2 ^ (n + 3) * K * s ^ (n + 1) := by
          rw [mul_pow, pow_succ 2 (n + 2), pow_succ 2 (n + 1)]; ring
        rw [this]
        gcongr
        exact le_max_left _ _
/-- **`C¹` criterion for Lipschitz maps** (step 7 of the graph-`C¹` argument).  If `f : ℝⁿ → ℝᵏ`
is Lipschitz, `Ω` is open, `g` is continuous on `Ω` and `Df(v) = g(v)` for `Lⁿ`-a.e. `v ∈ Ω`, then
`Df(x) = g(x)` at *every* `x ∈ Ω`, so `f` is `C¹` on `Ω`.  Mollify with the normalized tent kernels
`ϱ_t = (t − |y|)⁺ / ∫ (t − |y|)⁺`: differentiating under the integral (Rademacher) gives
`D(f ∗ ϱ_t)(x) = ∫ ϱ_t(y) Df(x − y) dy = ∫ ϱ_t(y) g(x − y) dy` once `B_t(x) ⊆ Ω`, which tends to
`g` locally uniformly on `Ω`; `f ∗ ϱ_t → f` pointwise, and the uniform-limit theorem for
derivatives (`hasFDerivAt_of_tendstoLocallyUniformlyOn`) gives `Df = g` on `Ω`. -/
theorem Submission.dorag_gc_contDiffOn_of_ae_hasFDerivAt : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (L : NNReal) (Ω : Set (Euclid n)) (g : Euclid n → (Euclid n →L[ℝ] Euclid k)), 0 < n → LipschitzWith L f → IsOpen Ω → ContinuousOn g Ω → (∀ᵐ v ∂volume, v ∈ Ω → HasFDerivAt f (g v) v) → ContDiffOn ℝ 1 f Ω := by
  intro n k f L Ω g hn hf hΩ hg hae
  -- 1. it suffices that `f` has derivative `g x` at every `x ∈ Ω`
  suffices H : ∀ x ∈ Ω, HasFDerivAt f (g x) x by
    have hfd : ∀ x ∈ Ω, fderiv ℝ f x = g x := fun x hx => (H x hx).fderiv
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (H x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hg.congr hfd
  -- 2. tent kernels `ϱ_t ≥ 0`, vanishing for `t ≤ |y|`, with `∫ ϱ_t = 1`
  set τ : ℝ → Euclid n → ℝ := fun t y => max (t - ‖y‖) 0 with hτ
  have hτc : ∀ t, Continuous (τ t) := fun t =>
    (continuous_const.sub continuous_norm).max continuous_const
  have hτ0 : ∀ t y, t ≤ ‖y‖ → τ t y = 0 := fun t y h => max_eq_right (by linarith)
  have hτnn : ∀ t y, 0 ≤ τ t y := fun t y => le_max_right _ _
  have hτcs : ∀ t, HasCompactSupport (τ t) := fun t =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) t) (fun y hy => by
      rw [mem_closedBall_zero_iff, not_le] at hy
      exact hτ0 t y hy.le)
  have hIpos : ∀ t, 0 < t → 0 < ∫ y, τ t y := fun t ht =>
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Euclid n)) (hτc t)
      (hτcs t) (fun y => hτnn t y) (by simp [hτ, ht])
  set ρ : ℝ → Euclid n → ℝ := fun t y => τ t y / ∫ y, τ t y with hρ
  have hρc : ∀ t, Continuous (ρ t) := fun t => (hτc t).div_const _
  have hρ0 : ∀ t y, t ≤ ‖y‖ → ρ t y = 0 := fun t y h => by simp [hρ, hτ0 t y h]
  have hρnn : ∀ t, 0 < t → ∀ y, 0 ≤ ρ t y := fun t ht y => div_nonneg (hτnn t y) (hIpos t ht).le
  have hρcs : ∀ t, HasCompactSupport (ρ t) := fun t =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) t) (fun y hy => by
      rw [mem_closedBall_zero_iff, not_le] at hy
      exact hρ0 t y hy.le)
  have hρi : ∀ t, Integrable (ρ t) := fun t => (hρc t).integrable_of_hasCompactSupport (hρcs t)
  have hρint : ∀ t, 0 < t → ∫ y, ρ t y = 1 := fun t ht => by
    simp only [hρ]
    rw [integral_div, div_self (hIpos t ht).ne']
  -- 3. the a.e. statements pulled back along the measure-preserving map `y ↦ x - y`
  have hdiffae : ∀ x : Euclid n, ∀ᵐ y ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f (x - y) :=
    fun x => (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      hf.ae_differentiableAt
  have hgae : ∀ x : Euclid n, ∀ᵐ y ∂(volume : Measure (Euclid n)),
      x - y ∈ Ω → HasFDerivAt f (g (x - y)) (x - y) :=
    fun x => (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hae
  -- 4. `D(f ∗ ϱ_t)(x) = ∫ ϱ_t(y) Df(x - y) dy` (differentiation under the integral)
  have hD : ∀ t, 0 < t → ∀ x, Integrable (fun y => ρ t y • fderiv ℝ f (x - y)) ∧
      HasFDerivAt (fun x' => ∫ y, ρ t y • f (x' - y)) (∫ y, ρ t y • fderiv ℝ f (x - y)) x := by
    intro t ht x
    have hcont : ∀ x', Continuous (fun y => ρ t y • f (x' - y)) := fun x' =>
      (hρc t).smul (hf.continuous.comp (continuous_const.sub continuous_id))
    refine hasFDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (s := univ)
      (bound := fun y => (L : ℝ) * ρ t y) univ_mem
      (Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable)
      ((hcont x).integrable_of_hasCompactSupport ((hρcs t).smul_right))
      (((hρc t).measurable.smul ((measurable_fderiv ℝ f).comp
        (measurable_const.sub measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_) ((hρi t).const_mul _) ?_
    · refine LipschitzOnWith.of_dist_le_mul fun a _ b _ => ?_
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (hρnn t ht y), Real.coe_nnabs, abs_of_nonneg (by
          have := hρnn t ht y; positivity)]
      calc ρ t y * ‖f (a - y) - f (b - y)‖ ≤ ρ t y * (L * ‖(a - y) - (b - y)‖) :=
            mul_le_mul_of_nonneg_left
              (by simpa [dist_eq_norm] using hf.dist_le_mul (a - y) (b - y)) (hρnn t ht y)
        _ = L * ρ t y * ‖a - b‖ := by rw [sub_sub_sub_cancel_right]; ring
    · filter_upwards [hdiffae x] with y hy
      have h1 : HasFDerivAt (fun x' => f (x' - y)) (fderiv ℝ f (x - y)) x := by
        have := hy.hasFDerivAt.comp x (hasFDerivAt_sub_const y)
        rw [ContinuousLinearMap.comp_id] at this
        exact this
      exact h1.const_smul (ρ t y)
  -- 5. if `B_t(x) ⊆ Ω`, then `Df(x - y) = g(x - y)` for a.e. `y` with `ϱ_t(y) ≠ 0`
  have haeq : ∀ t, 0 < t → ∀ x, closedBall x t ⊆ Ω →
      (fun y => ρ t y • fderiv ℝ f (x - y)) =ᵐ[volume] (fun y => ρ t y • g (x - y)) := by
    intro t ht x hx
    filter_upwards [hgae x] with y hy
    by_cases hyt : ‖y‖ < t
    · have hxy : x - y ∈ Ω := hx (by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hyt.le)
      rw [(hy hxy).fderiv]
    · show ρ t y • fderiv ℝ f (x - y) = ρ t y • g (x - y)
      rw [hρ0 t y (not_lt.1 hyt)]
      exact (zero_smul ℝ (fderiv ℝ f (x - y))).trans (zero_smul ℝ (g (x - y))).symm
  -- 6. `|D(f ∗ ϱ_t)(x) - g(x)| ≤ sup_{|y| < t} |g(x - y) - g(x)|` when `B_t(x) ⊆ Ω`
  have hest : ∀ t, 0 < t → ∀ x, closedBall x t ⊆ Ω → ∀ ε : ℝ,
      (∀ y : Euclid n, ‖y‖ < t → ‖g (x - y) - g x‖ ≤ ε) →
      ‖(∫ y, ρ t y • fderiv ℝ f (x - y)) - g x‖ ≤ ε := by
    intro t ht x hx ε hε
    have hint2 : Integrable (fun y => ρ t y • g (x - y)) := (hD t ht x).1.congr (haeq t ht x hx)
    rw [integral_congr_ae (haeq t ht x hx)]
    have hgx : g x = ∫ y, ρ t y • g x := by rw [integral_smul_const, hρint t ht, one_smul]
    rw [hgx, ← integral_sub hint2 ((hρi t).smul_const _)]
    calc ‖∫ y, (ρ t y • g (x - y) - ρ t y • g x)‖ ≤ ∫ y, ρ t y * ε :=
          norm_integral_le_of_norm_le ((hρi t).mul_const ε) (Eventually.of_forall fun y => by
            rw [show ρ t y • g (x - y) - ρ t y • g x = ρ t y • (g (x - y) - g x) from
              (smul_sub _ _ _).symm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρnn t ht y)]
            by_cases hyt : ‖y‖ < t
            · exact mul_le_mul_of_nonneg_left (hε y hyt) (hρnn t ht y)
            · rw [hρ0 t y (not_lt.1 hyt)]; simp)
      _ = ε := by rw [integral_mul_const, hρint t ht, one_mul]
  -- 7. along `t_m = 1 / (m + 1)`, `D(f ∗ ϱ_{t_m}) → g` locally uniformly on `Ω`
  set tm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with htm
  have htm_pos : ∀ m, 0 < tm m := fun m => by positivity
  have htm_lim : Tendsto tm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hloc : TendstoLocallyUniformlyOn
      (fun m x => ∫ y, ρ (tm m) y • fderiv ℝ f (x - y)) g atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff]
    intro ε hε x₁ hx₁
    obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.1 hΩ x₁ hx₁
    have hr : 0 < ρ₁ / 3 := by positivity
    have hcb : closedBall x₁ (2 * (ρ₁ / 3)) ⊆ Ω :=
      (closedBall_subset_ball (by linarith)).trans hball
    have huc := (isCompact_closedBall x₁ (2 * (ρ₁ / 3))).uniformContinuousOn_of_continuous
      (hg.mono hcb)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (by positivity)
    refine ⟨ball x₁ (ρ₁ / 3), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x₁ hr), ?_⟩
    have hev : ∀ᶠ m in atTop, tm m < min δ (ρ₁ / 3) := htm_lim (Iio_mem_nhds (lt_min hδ hr))
    filter_upwards [hev] with m hm y hy
    rw [mem_ball] at hy
    have hm1 : tm m < δ := lt_of_lt_of_le hm (min_le_left _ _)
    have hm2 : tm m < ρ₁ / 3 := lt_of_lt_of_le hm (min_le_right _ _)
    have hsub : closedBall y (tm m) ⊆ closedBall x₁ (2 * (ρ₁ / 3)) :=
      closedBall_subset_closedBall' (by linarith)
    rw [dist_eq_norm, norm_sub_rev]
    calc ‖(∫ w, ρ (tm m) w • fderiv ℝ f (y - w)) - g y‖ ≤ ε / 2 := by
          refine hest (tm m) (htm_pos m) y (hsub.trans hcb) (ε / 2) fun w hw => ?_
          have h1 : y - w ∈ closedBall x₁ (2 * (ρ₁ / 3)) := hsub (by
            rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hw.le)
          have h2 : y ∈ closedBall x₁ (2 * (ρ₁ / 3)) := hsub (mem_closedBall_self (htm_pos m).le)
          have h3 : dist (y - w) y < δ := by
            rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; linarith
          have := hδ' (y - w) h1 y h2 h3
          rw [dist_eq_norm] at this
          exact this.le
      _ < ε := half_lt_self hε
  -- 8. `|(f ∗ ϱ_t)(x) - f(x)| ≤ L t`, so `f ∗ ϱ_{t_m} → f` pointwise
  have hpt : ∀ x, Tendsto (fun m => ∫ y, ρ (tm m) y • f (x - y)) atTop (𝓝 (f x)) := by
    intro x
    have hbound : ∀ m, ‖(∫ y, ρ (tm m) y • f (x - y)) - f x‖ ≤ L * tm m := by
      intro m
      have ht := htm_pos m
      have hint : Integrable (fun y => ρ (tm m) y • f (x - y)) :=
        ((hρc _).smul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((hρcs _).smul_right)
      have hfx : f x = ∫ y, ρ (tm m) y • f x := by rw [integral_smul_const, hρint _ ht, one_smul]
      rw [hfx, ← integral_sub hint ((hρi _).smul_const _)]
      calc ‖∫ y, (ρ (tm m) y • f (x - y) - ρ (tm m) y • f x)‖ ≤ ∫ y, ρ (tm m) y * (L * tm m) :=
            norm_integral_le_of_norm_le ((hρi _).mul_const _) (Eventually.of_forall fun y => by
              rw [show ρ (tm m) y • f (x - y) - ρ (tm m) y • f x = ρ (tm m) y • (f (x - y) - f x) from
                (smul_sub _ _ _).symm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρnn _ ht y)]
              by_cases hyt : ‖y‖ < tm m
              · refine mul_le_mul_of_nonneg_left ?_ (hρnn _ ht y)
                calc ‖f (x - y) - f x‖ ≤ L * ‖(x - y) - x‖ := by
                      simpa [dist_eq_norm] using hf.dist_le_mul (x - y) x
                  _ ≤ L * tm m := by
                      rw [sub_sub_cancel_left, norm_neg]; gcongr
              · rw [hρ0 _ y (not_lt.1 hyt)]; simp)
        _ = L * tm m := by rw [integral_mul_const, hρint _ ht, one_mul]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) hbound ?_
    simpa using htm_lim.const_mul (L : ℝ)
  -- 9. the uniform-limit theorem for derivatives
  intro x hx
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hloc
    (fun m x' _ => (hD (tm m) (htm_pos m) x').2) (fun x' _ => hpt x') hx
/-- **Simon Ch. 4, §3 (p. 90)**, the cutoff `φ` chosen after (3.3), with `1 + ε = A`: for `A > 1`
there is a `C¹` nonincreasing `φ` with `0 ≤ φ ≤ 1`, `φ ≡ 1` on `(-∞, 1]`, `φ ≡ 0` on `[A, ∞)`,
`φ' ≤ 0`, and `φ'(u) ≠ 0` only for `1 < u < A`.  Take `φ(u) = Ψ((A − u)/(A − 1))` for Mathlib's
smooth transition `Ψ` (`Ψ = 0` on `(-∞, 0]`, `Ψ = 1` on `[1, ∞)`, monotone).  `φ` is antitone, so
`φ' ≤ 0`; on the plateaus `u` is a global extremum of `φ`, so `φ'(u) = 0`. -/
theorem Submission.doragm_sab_cutoff_profile : ∀ (A : ℝ), 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, u ≤ 1 → φ u = 1) ∧ (∀ u, A ≤ u → φ u = 0) ∧ (∀ u, deriv φ u ≤ 0) ∧ (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A) := by
  intro A hA
  -- `a = A − 1 > 0` and `φ(u) = Ψ((A − u)/a)` for the smooth transition `Ψ`
  have ha : 0 < A - 1 := sub_pos.2 hA
  set φ : ℝ → ℝ := fun u => Real.smoothTransition ((A - u) / (A - 1))
  -- `u ↦ (A − u)/a` is antitone and `Ψ` is monotone
  have hanti : Antitone φ := fun u v huv =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_left huv A) ha.le)
  have hbd : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1 := fun u =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `u ≤ 1` gives `(A − u)/a ≥ 1`, and `A ≤ u` gives `(A − u)/a ≤ 0`
  have h1 : ∀ u, u ≤ 1 → φ u = 1 := fun u hu =>
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ ha).2 (by linarith))
  have h0 : ∀ u, A ≤ u → φ u = 0 := fun u hu =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
  refine ⟨φ, ?_, hanti, hbd, h1, h0, fun u => hanti.deriv_nonpos, fun u hu => ?_⟩
  · -- `Ψ` is `C^∞` and `u ↦ (A − u)/a` is affine
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  · -- on the plateaus `u` is a global maximum (`φ u = 1`) or minimum (`φ u = 0`), so `φ'(u) = 0`
    by_contra hcon
    rcases le_or_gt u 1 with hu1 | hu1
    · refine hu (IsLocalMax.deriv_eq_zero ?_)
      exact (isMaxOn_univ_iff.2 fun v => (h1 u hu1).symm ▸ (hbd v).2).isLocalMax Filter.univ_mem
    · have hAu : A ≤ u := not_lt.1 fun h => hcon ⟨hu1, h⟩
      refine hu (IsLocalMin.deriv_eq_zero ?_)
      exact (isMinOn_univ_iff.2 fun v => (h0 u hAu).symm ▸ (hbd v).1).isLocalMin Filter.univ_mem
/-- **Integrating-factor comparison on `[s, t]`** (Simon Ch. 4, 3.16, p. 92: the integrating-factor
step, done here by comparing derivatives).  If `n I − τ I' + τ J = −h`, `|h| ≤ cτI`,
`J ≥ 0` and `G' ≤ J/τⁿ ≤ K G'` on `[s, t]` (`c ≥ 0`, `0 < s < t`), then with
`Φ_b(σ) = e^{bσ} σ⁻ⁿ I(σ)`: `G(t) − G(s) ≤ Φ_c(t) − Φ_c(s)` and
`Φ_{−c}(t) − Φ_{−c}(s) ≤ K (G(t) − G(s))`.  By the quotient rule and `(E)`,
`Φ_b' = e^{bτ}τ⁻ⁿ (J + bI + h/τ)`; since `cI + h/τ ≥ 0 ≥ −cI + h/τ` and `e^{−cτ} ≤ 1 ≤ e^{cτ}`,
`Φ_c − G` and `K G − Φ_{−c}` have nonnegative derivative, hence are nondecreasing on `[s, t]`. -/
theorem Submission.doragm_sab_exp_ratio_compare : ∀ (n : ℕ) (c K s t : ℝ) (I I' G G' J h : ℝ → ℝ), 0 ≤ c → 0 < s → s < t → (∀ τ ∈ Icc s t, HasDerivAt I (I' τ) τ) → (∀ τ ∈ Icc s t, HasDerivAt G (G' τ) τ) → (∀ τ ∈ Icc s t, (n : ℝ) * I τ - τ * I' τ + τ * J τ = -h τ) → (∀ τ ∈ Icc s t, |h τ| ≤ c * τ * I τ) → (∀ τ ∈ Icc s t, 0 ≤ J τ) → (∀ τ ∈ Icc s t, G' τ ≤ J τ / τ ^ n) → (∀ τ ∈ Icc s t, J τ / τ ^ n ≤ K * G' τ) → G t - G s ≤ Real.exp (c * t) / t ^ n * I t - Real.exp (c * s) / s ^ n * I s ∧ Real.exp (-(c * t)) / t ^ n * I t - Real.exp (-(c * s)) / s ^ n * I s ≤ K * (G t - G s) := by
  intro n c K s t I I' G G' J h hc hs hst hI hG hE hH hJ hC1 hC2
  -- every `τ ∈ [s, t]` is positive
  have hpos : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => hs.trans_le hτ.1
  -- `Φ_b(σ) = e^{bσ}/σⁿ · I(σ)` has derivative `e^{bτ}/τⁿ · (J + bI + h/τ)`, by `(E)`
  have hΦ : ∀ b : ℝ, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => Real.exp (b * σ) / σ ^ n * I σ)
      (Real.exp (b * τ) / τ ^ n * (J τ + b * I τ + h τ / τ)) τ := by
    intro b τ hτ
    have hτ0 : τ ≠ 0 := (hpos τ hτ).ne'
    have he : HasDerivAt (fun σ => Real.exp (b * σ)) (Real.exp (b * τ) * b) τ := by
      simpa using ((hasDerivAt_id τ).const_mul b).exp
    have hd := (he.fun_div (hasDerivAt_pow n τ) (pow_ne_zero n hτ0)).fun_mul (hI τ hτ)
    convert hd using 1
    have hI' : I' τ = ((n : ℝ) * I τ + τ * J τ + h τ) / τ := by
      field_simp
      linarith [hE τ hτ]
    rw [hI']
    rcases n with _ | m
    · simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, one_pow, div_one, zero_add]
      field_simp
      ring
    · simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]
      field_simp
      ring
  -- a nonnegative derivative on `[s, t]` gives `f s ≤ f t`
  have hmono : ∀ f f' : ℝ → ℝ, (∀ τ ∈ Icc s t, HasDerivAt f (f' τ) τ) →
      (∀ τ ∈ Icc s t, 0 ≤ f' τ) → f s ≤ f t := by
    intro f f' hf hf'
    have hmon : MonotoneOn f (Icc s t) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc s t)
        (fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt) (fun τ hτ => ?_) (fun τ hτ => ?_)
      · rw [interior_Icc] at hτ
        exact (hf τ (Ioo_subset_Icc_self hτ)).hasDerivWithinAt
      · rw [interior_Icc] at hτ
        exact hf' τ (Ioo_subset_Icc_self hτ)
    exact hmon (left_mem_Icc.2 hst.le) (right_mem_Icc.2 hst.le) hst.le
  -- `|h| ≤ cτI` gives `cI + h/τ ≥ 0` and `−cI + h/τ ≤ 0`
  have hsign : ∀ τ ∈ Icc s t, 0 ≤ c * I τ + h τ / τ ∧ -c * I τ + h τ / τ ≤ 0 := by
    intro τ hτ
    have hτ0 := hpos τ hτ
    obtain ⟨hl, hu⟩ := abs_le.1 (hH τ hτ)
    have h1 : -(c * I τ) ≤ h τ / τ := by
      rw [le_div_iff₀ hτ0]; linarith
    have h2 : h τ / τ ≤ c * I τ := by
      rw [div_le_iff₀ hτ0]; linarith
    constructor <;> linarith
  constructor
  · -- (a): `Φ_c' ≥ e^{cτ} J/τⁿ ≥ J/τⁿ ≥ G'`, so `Φ_c − G` is nondecreasing
    have key := hmono (fun σ => Real.exp (c * σ) / σ ^ n * I σ - G σ)
      (fun τ => Real.exp (c * τ) / τ ^ n * (J τ + c * I τ + h τ / τ) - G' τ)
      (fun τ hτ => (hΦ c τ hτ).fun_sub (hG τ hτ)) (fun τ hτ => by
        have hτn : 0 < τ ^ n := pow_pos (hpos τ hτ) n
        have hJn : 0 ≤ J τ / τ ^ n := div_nonneg (hJ τ hτ) hτn.le
        have hexp : 1 ≤ Real.exp (c * τ) := Real.one_le_exp (mul_nonneg hc (hpos τ hτ).le)
        have hA : 0 ≤ Real.exp (c * τ) / τ ^ n * (c * I τ + h τ / τ) :=
          mul_nonneg (div_nonneg (Real.exp_pos _).le hτn.le) (hsign τ hτ).1
        have hB : J τ / τ ^ n ≤ Real.exp (c * τ) * (J τ / τ ^ n) := le_mul_of_one_le_left hJn hexp
        have hsplit : Real.exp (c * τ) / τ ^ n * (J τ + c * I τ + h τ / τ) =
            Real.exp (c * τ) * (J τ / τ ^ n) + Real.exp (c * τ) / τ ^ n * (c * I τ + h τ / τ) := by
          ring
        rw [hsplit]
        linarith [hC1 τ hτ])
    linarith
  · -- (b): `Φ_{−c}' ≤ e^{−cτ} J/τⁿ ≤ J/τⁿ ≤ K G'`, so `K G − Φ_{−c}` is nondecreasing
    have key := hmono (fun σ => K * G σ - Real.exp (-c * σ) / σ ^ n * I σ)
      (fun τ => K * G' τ - Real.exp (-c * τ) / τ ^ n * (J τ + -c * I τ + h τ / τ))
      (fun τ hτ => ((hG τ hτ).const_mul K).fun_sub (hΦ (-c) τ hτ)) (fun τ hτ => by
        have hτn : 0 < τ ^ n := pow_pos (hpos τ hτ) n
        have hJn : 0 ≤ J τ / τ ^ n := div_nonneg (hJ τ hτ) hτn.le
        have hexp : Real.exp (-c * τ) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [hpos τ hτ])
        have hA : Real.exp (-c * τ) / τ ^ n * (-c * I τ + h τ / τ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.exp_pos _).le hτn.le) (hsign τ hτ).2
        have hB : Real.exp (-c * τ) * (J τ / τ ^ n) ≤ J τ / τ ^ n := mul_le_of_le_one_left hJn hexp
        have hsplit : Real.exp (-c * τ) / τ ^ n * (J τ + -c * I τ + h τ / τ) =
            Real.exp (-c * τ) * (J τ / τ ^ n) + Real.exp (-c * τ) / τ ^ n * (-c * I τ + h τ / τ) := by
          ring
        rw [hsplit]
        linarith [hC2 τ hτ])
    simp only [neg_mul] at key
    linarith
/-- **The mean-curvature term of a radial cutoff** (Simon Ch. 4, 3.16): if `φ ≥ 0` vanishes on
`[A, ∞)`, `τ > 0` and `‖H‖ ≤ κ`, then
`|∫ φ(|x − y|/τ) ⟨x − y, H x⟩ dμ| ≤ A κ τ ∫ φ(|x − y|/τ) dμ`.  Where `φ(|x − y|/τ) ≠ 0`,
`|x − y| < Aτ`, so Cauchy–Schwarz bounds the integrand by the integrable `Aκτ φ(|x − y|/τ)`. -/
theorem Submission.doragm_sab_curvature_term_le : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (H : Euclid P → Euclid P) (φ : ℝ → ℝ) (κ A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u) → (∀ u, A ≤ u → φ u = 0) → (∀ x, ‖H x‖ ≤ κ) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → |∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂μ| ≤ A * κ * τ * ∫ x, φ (‖x - y‖ / τ) ∂μ := by
  intro P μ y H φ κ A τ hτ hφ hφA hH hint
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hH 0)
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hint.const_mul (A * κ * τ)) (ae_of_all μ fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hφ _)]
  by_cases h0 : φ (‖x - y‖ / τ) = 0
  · simp [h0]
  have hr : ‖x - y‖ ≤ A * τ :=
    ((div_lt_iff₀ hτ).mp (lt_of_not_ge fun hA => h0 (hφA _ hA))).le
  calc φ (‖x - y‖ / τ) * ‖inner ℝ (x - y) (H x)‖
      ≤ φ (‖x - y‖ / τ) * (‖x - y‖ * κ) :=
        mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hH x) (norm_nonneg _))) (hφ _)
    _ ≤ φ (‖x - y‖ / τ) * (A * τ * κ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hκ) (hφ _)
    _ = A * κ * τ * φ (‖x - y‖ / τ) := by ring
/-- **Simon Ch. 4, 3.5 (p. 90)**, comparison of the scale-derivative weights.  With
`r = |x − y|`, `d = −(r/τ²)·φ'(r/τ) ≥ 0` and `q = N/max(s, r)ⁿ`: where `φ'(r/τ) ≠ 0` we have
`τ < r < Aτ`, so `max(s, r) = r` and `r⁻ⁿ ≤ τ⁻ⁿ ≤ Aⁿr⁻ⁿ`; multiplying by `d·N ≥ 0` and
integrating gives `0 ≤ ∫ d·N dμ` and `∫ d·q dμ ≤ (∫ d·N dμ)/τⁿ ≤ Aⁿ ∫ d·q dμ`. -/
theorem Submission.doragm_sab_deriv_weight_squeeze : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (N : Euclid P → ℝ) (A s τ : ℝ), 1 < A → 0 < s → s ≤ τ → (∀ u, deriv φ u ≤ 0) → (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A) → (∀ x, 0 ≤ N x) → Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) μ → Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x) μ → 0 ≤ ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ ∧ ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂μ ≤ (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ) / τ ^ n ∧ (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ) / τ ^ n ≤ A ^ n * ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂μ := by
  intro P n μ y φ N A s τ hA hs hsτ hφ' hsupp hN hq hD
  have hτ : 0 < τ := hs.trans_le hsτ
  -- `d·N ≥ 0`: `r/τ² ≥ 0` and `φ' ≤ 0` give `d ≥ 0`, and `N ≥ 0`
  have hDnn : ∀ x, 0 ≤ -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x := fun x =>
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (by positivity)) (hφ' _)) (hN x)
  -- pointwise, `d·q ≤ d·N/τⁿ ≤ Aⁿ·d·q`
  have hpt : ∀ x,
      -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ≤
          -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x / τ ^ n ∧
        -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x / τ ^ n ≤
          A ^ n * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) := by
    intro x
    by_cases h0 : deriv φ (‖x - y‖ / τ) = 0
    · -- `d(x) = 0`, so all three terms vanish
      simp [h0]
    · -- `1 < r/τ < A`, so `τ < r < Aτ` and `max(s, r) = r`
      obtain ⟨h1, h2⟩ := hsupp _ h0
      have hr1 : τ < ‖x - y‖ := (one_lt_div₀ hτ).1 h1
      have hr2 : ‖x - y‖ < A * τ := (div_lt_iff₀ hτ).1 h2
      have hr : 0 < ‖x - y‖ := hτ.trans hr1
      have hrA : ‖x - y‖ ^ n ≤ A ^ n * τ ^ n :=
        (pow_le_pow_left₀ hr.le hr2.le n).trans_eq (mul_pow A τ n)
      rw [max_eq_right (hsτ.trans hr1.le), ← mul_div_assoc]
      have hDx := hDnn x
      generalize -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x = D at hDx ⊢
      refine ⟨div_le_div_of_nonneg_left hDx (pow_pos hτ n) (pow_le_pow_left₀ hτ.le hr1.le n), ?_⟩
      -- `D/τⁿ ≤ Aⁿ·D/rⁿ ⟺ D·rⁿ ≤ Aⁿ·D·τⁿ`, from `rⁿ ≤ (Aτ)ⁿ` and `D ≥ 0`
      rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hτ n) (pow_pos hr n)]
      calc D * ‖x - y‖ ^ n ≤ D * (A ^ n * τ ^ n) := mul_le_mul_of_nonneg_left hrA hDx
        _ = A ^ n * D * τ ^ n := by ring
  refine ⟨integral_nonneg hDnn, ?_, ?_⟩
  · -- `∫ d·q ≤ ∫ d·N/τⁿ = (∫ d·N)/τⁿ`
    rw [← integral_div]
    exact integral_mono hq (hD.div_const _) fun x => (hpt x).1
  · -- `(∫ d·N)/τⁿ = ∫ d·N/τⁿ ≤ ∫ Aⁿ·d·q = Aⁿ ∫ d·q`
    rw [← integral_div, ← integral_const_mul]
    exact integral_mono (hD.div_const _) (hq.const_mul _) fun x => (hpt x).2
/-- **Simon Ch. 4, (3.5)–(3.6) (p. 90)**, the passage from the smoothed to the sharp masses: if
`0 ≤ φ ≤ 1`, `φ ≡ 1` on `(-∞, 1]` and `φ ≡ 0` on `[A, ∞)`, then pointwise
`1_{B̄_τ(y)} ≤ φ(|x − y|/τ) ≤ 1_{B̄_{Aτ}(y)}`, so `μ(B̄_τ(y)) ≤ ∫ φ(|x − y|/τ) dμ ≤ μ(B̄_{Aτ}(y))`
in `[0, ∞]` (`ofReal ∫ f = ∫⁻ ofReal f` for integrable `f ≥ 0`; no finiteness of `μ` is needed). -/
theorem Submission.doragm_sab_cutoff_mass_sandwich : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → μ (closedBall y τ) ≤ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ∧ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ≤ μ (closedBall y (A * τ)) := by
  intro P μ y φ A τ hτ hbd h1 h0 hint
  -- `ofReal ∫ f dμ = ∫⁻ ofReal f dμ` for the integrable `f(x) = φ(|x − y|/τ) ≥ 0`, and
  -- `μ(B̄_ρ(y)) = ∫⁻ 1_{B̄_ρ(y)} dμ` since closed balls are measurable
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hbd _).1),
    ← lintegral_indicator_one (measurableSet_closedBall : MeasurableSet (closedBall y τ)),
    ← lintegral_indicator_one (measurableSet_closedBall : MeasurableSet (closedBall y (A * τ)))]
  refine ⟨lintegral_mono fun x => ?_, lintegral_mono fun x => ?_⟩
  · -- on `B̄_τ(y)`, `|x − y|/τ ≤ 1`, so `φ(|x − y|/τ) = 1`
    by_cases hx : x ∈ closedBall y τ
    · rw [indicator_of_mem hx, Pi.one_apply,
        h1 _ ((div_le_one hτ).2 (mem_closedBall_iff_norm.1 hx)), ENNReal.ofReal_one]
    · rw [indicator_of_notMem hx]
      exact zero_le
  · -- `φ ≤ 1` everywhere, and off `B̄_{Aτ}(y)`, `|x − y|/τ > A`, so `φ(|x − y|/τ) = 0`
    by_cases hx : x ∈ closedBall y (A * τ)
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hbd _).2
    · rw [mem_closedBall_iff_norm, not_le] at hx
      rw [h0 _ ((le_div_iff₀ hτ).2 hx.le), ENNReal.ofReal_zero]
      exact zero_le
/-- The cutoff increment `Δ = ∫ φ(r/t) q dμ - ∫ φ(r/s) q dμ`, `r = ‖x - y‖`, lies between two
annular integrals of `F` (Simon Ch. 4, 3.5): `Δ ≥ 0` and, in `[0, ∞]`,
`∫⁻_{B̄_t(y) \ B̄_{As}(y)} F ≤ Δ ≤ ∫⁻_{B̄_{At}(y) \ B̄_s(y)} F`.  The point is that
`g = (φ(r/t) - φ(r/s)) q` is `≥ 0`, equals `q = F` on the first annulus and vanishes off the
second. -/
theorem Submission.doragm_sab_annulus_increment_sandwich : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q F : Euclid P → ℝ) (A s t : ℝ), 1 < A → 0 < s → s ≤ t → Antitone φ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → (∀ x, 0 ≤ q x) → (∀ x, s < ‖x - y‖ → F x = q x) → Integrable (fun x => φ (‖x - y‖ / s) * q x) μ → Integrable (fun x => φ (‖x - y‖ / t) * q x) μ → 0 ≤ (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ ∧ (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ∧ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ≤ ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (F x) ∂μ := by
  intro P μ y φ q F A s t hA hs hst hφ hφ01 hφ1 hφ0 hq hFq hint_s hint_t
  have ht : 0 < t := hs.trans_le hst
  -- Step 1: `Δ = ∫ g dμ` for the integrable `g = φ(r/t) q - φ(r/s) q`
  set g : Euclid P → ℝ := fun x => φ (‖x - y‖ / t) * q x - φ (‖x - y‖ / s) * q x with hg_def
  have hΔ : (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ = ∫ x, g x ∂μ :=
    (integral_sub hint_t hint_s).symm
  -- Step 2: `g ≥ 0`, as `r/t ≤ r/s` and `φ` is antitone; so `ofReal Δ = ∫⁻ ofReal g`
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x =>
    sub_nonneg.2 (mul_le_mul_of_nonneg_right
      (hφ (div_le_div_of_nonneg_left (norm_nonneg _) hs hst)) (hq x))
  have hg_int : Integrable g μ := hint_t.sub hint_s
  rw [hΔ, ofReal_integral_eq_lintegral_ofReal hg_int (Eventually.of_forall hg_nonneg)]
  refine ⟨integral_nonneg hg_nonneg, ?_, ?_⟩
  · -- Step 3: on `B̄_t(y) \ B̄_{As}(y)`, `φ(r/t) = 1`, `φ(r/s) = 0` and `r > As > s`, so `g = q = F`
    calc (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ)
        = ∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (g x) ∂μ := by
          refine setLIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
            fun x hx => ?_
          simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, not_le] at hx
          have h1 : φ (‖x - y‖ / t) = 1 := hφ1 _ ((div_le_one ht).2 hx.1)
          have h0 : φ (‖x - y‖ / s) = 0 := hφ0 _ ((le_div_iff₀ hs).2 hx.2.le)
          simp only [hg_def, h1, h0, hFq x ((lt_mul_of_one_lt_left hs hA).trans hx.2), one_mul,
            zero_mul, sub_zero]
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := setLIntegral_le_lintegral _ _
  · -- Step 4: `ofReal g ≤ 1_{B̄_{At}(y) \ B̄_s(y)} ofReal F` pointwise
    rw [← lintegral_indicator (measurableSet_closedBall.diff measurableSet_closedBall)]
    refine lintegral_mono fun x => ?_
    rcases le_or_gt ‖x - y‖ s with hrs | hsr
    · -- `r ≤ s ≤ t`: `φ(r/t) = φ(r/s) = 1`, so `g = 0`
      have h1t : φ (‖x - y‖ / t) = 1 := hφ1 _ ((div_le_one ht).2 (hrs.trans hst))
      have h1s : φ (‖x - y‖ / s) = 1 := hφ1 _ ((div_le_one hs).2 hrs)
      refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
      simp only [hg_def, h1t, h1s, sub_self, le_refl]
    rcases le_or_gt ‖x - y‖ (A * t) with hrAt | hAtr
    · -- `s < r ≤ At`: `x` lies in the annulus, where `g ≤ φ(r/t) q ≤ q = F`
      have hx : x ∈ closedBall y (A * t) \ closedBall y s := by
        simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, not_le]
        exact ⟨hrAt, hsr⟩
      rw [indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht1 := mul_le_mul_of_nonneg_right (hφ01 (‖x - y‖ / t)).2 (hq x)
      have hs0 := mul_nonneg (hφ01 (‖x - y‖ / s)).1 (hq x)
      simp only [hg_def, hFq x hsr]
      linarith
    · -- `r > At`: `φ(r/t) = 0`, so `g = -φ(r/s) q ≤ 0`
      have h0t : φ (‖x - y‖ / t) = 0 := hφ0 _ ((le_div_iff₀ ht).2 hAtr.le)
      have hs0 := mul_nonneg (hφ01 (‖x - y‖ / s)).1 (hq x)
      refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
      simp only [hg_def, h0t, zero_mul]
      linarith
/-- **Simon Ch. 4, 3.4 and 3.16** (differentiating `ρ ↦ ∫ φ(r/ρ) dμ` under the integral sign):
for a `C¹` cutoff `φ` vanishing on `[A, ∞)` and a bounded weight `q`, with `0 < τ`, `Aτ < R₀`
and `ν(B̄_{R₀}(y)) < ∞`, the integrands `φ(|x - y|/τ) q` and `-(|x - y|/τ²) φ'(|x - y|/τ) q` are
`ν`-integrable and `σ ↦ ∫ φ(|x - y|/σ) q dν` has derivative `∫ -(|x - y|/τ²) φ'(|x - y|/τ) q dν`
at `τ`.  For `σ ∈ (τ/2, R₀/A)` both integrands vanish off `B̄_{R₀}(y)` and are bounded on it
uniformly in `σ`, so dominated differentiation applies. -/
theorem Submission.doragm_radial_cutoff_hasDerivAt : ∀ (P : ℕ) (ν : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q : Euclid P → ℝ) (A B τ R₀ : ℝ), ContDiff ℝ 1 φ → (∀ u, A ≤ u → φ u = 0) → 0 < A → 0 < τ → A * τ < R₀ → ν (closedBall y R₀) ≠ ∞ → AEStronglyMeasurable q ν → (∀ x, ‖q x‖ ≤ B) → Integrable (fun x => φ (‖x - y‖ / τ) * q x) ν ∧ Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * q x) ν ∧ HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) * q x ∂ν) (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * q x ∂ν) τ := by
  intro P ν y φ q A B τ R₀ hφ hφA hA hτ hAτ hν hq hqB
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  -- `φ' = 0` on `(A, ∞)`, where `φ` vanishes identically
  have hφ'A : ∀ u, A < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun v hv => hφA v (le_of_lt hv)
    rw [h.deriv_eq, deriv_const]
  have hR₀ : 0 < R₀ := (mul_pos hA hτ).trans hAτ
  -- bounds `C₀`, `C₁` for `|φ|`, `|φ'|` on `[0, 2R₀/τ]`
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * R₀ / τ)) hφ.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * R₀ / τ)) hφ'c.continuousOn
  have h0K : (0 : ℝ) ∈ Icc 0 (2 * R₀ / τ) := ⟨le_rfl, by positivity⟩
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0 h0K)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 h0K)
  -- the neighbourhood `(τ/2, R₀/A)` of `τ`
  have hτs : τ ∈ Ioo (τ / 2) (R₀ / A) := ⟨by linarith, by rw [lt_div_iff₀ hA]; linarith⟩
  have hs : Ioo (τ / 2) (R₀ / A) ∈ 𝓝 τ := Ioo_mem_nhds hτs.1 hτs.2
  -- for `σ ∈ (τ/2, R₀/A)`: off `B̄_{R₀}(y)`, `|x - y|/σ > A`; on it, `|x - y|/σ ∈ [0, 2R₀/τ]`
  have hout : ∀ σ ∈ Ioo (τ / 2) (R₀ / A), ∀ x ∉ closedBall y R₀, A < ‖x - y‖ / σ := by
    rintro σ ⟨hσ1, hσ2⟩ x hx
    rw [mem_closedBall_iff_norm, not_le] at hx
    rw [lt_div_iff₀ hA] at hσ2
    have hσ : 0 < σ := by linarith
    rw [lt_div_iff₀ hσ]
    linarith
  have hin : ∀ σ ∈ Ioo (τ / 2) (R₀ / A), ∀ x ∈ closedBall y R₀,
      ‖x - y‖ / σ ∈ Icc 0 (2 * R₀ / τ) := by
    rintro σ ⟨hσ1, -⟩ x hx
    rw [mem_closedBall_iff_norm] at hx
    have hσ : 0 < σ := by linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ hσ hτ]
    nlinarith [norm_nonneg (x - y)]
  -- the integrands `F σ`, their `σ`-derivatives `F' σ`, and their measurability
  set F : ℝ → Euclid P → ℝ := fun σ x => φ (‖x - y‖ / σ) * q x with hF
  set F' : ℝ → Euclid P → ℝ := fun σ x => -(‖x - y‖ / σ ^ 2) * deriv φ (‖x - y‖ / σ) * q x
    with hF'
  have hr : Continuous fun x : Euclid P => ‖x - y‖ := (continuous_id.sub continuous_const).norm
  have hF_meas : ∀ σ, AEStronglyMeasurable (F σ) ν := fun σ =>
    (hφ.continuous.comp (hr.div_const σ)).aestronglyMeasurable.mul hq
  have hF'_meas : ∀ σ, AEStronglyMeasurable (F' σ) ν := fun σ =>
    ((hr.div_const _).neg.mul (hφ'c.comp (hr.div_const σ))).aestronglyMeasurable.mul hq
  -- constant multiples of `1_{B̄_{R₀}(y)}` are integrable, as `ν(B̄_{R₀}(y)) < ∞`
  have hind : ∀ c : ℝ, Integrable ((closedBall y R₀).indicator fun _ => c) ν := fun c =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hν)
  -- (a): `|F τ| ≤ C₀ B 1_{B̄_{R₀}(y)}`
  have hF_int : Integrable (F τ) ν := by
    refine (hind (C₀ * B)).mono' (hF_meas τ) (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall y R₀
    · rw [Set.indicator_of_mem hx, hF]
      simp only
      rw [norm_mul]
      exact mul_le_mul (hC₀ _ (hin τ hτs x hx)) (hqB x) (norm_nonneg _) hC₀0
    · rw [Set.indicator_of_notMem hx, hF]
      simp only
      rw [hφA _ (hout τ hτs x hx).le, zero_mul, norm_zero]
  -- domination: `|F' σ| ≤ (R₀/(τ/2)²) C₁ B 1_{B̄_{R₀}(y)}` for `σ ∈ (τ/2, R₀/A)`
  have h_bound : ∀ᵐ x ∂ν, ∀ σ ∈ Ioo (τ / 2) (R₀ / A),
      ‖F' σ x‖ ≤ (closedBall y R₀).indicator (fun _ => R₀ / (τ / 2) ^ 2 * C₁ * B) x := by
    refine ae_of_all _ fun x σ hσs => ?_
    have hσ : 0 < σ := by linarith [hσs.1]
    by_cases hx : x ∈ closedBall y R₀
    · rw [Set.indicator_of_mem hx, hF']
      simp only
      rw [norm_mul, norm_mul, norm_neg, Real.norm_of_nonneg (by positivity)]
      have hrσ : ‖x - y‖ / σ ^ 2 ≤ R₀ / (τ / 2) ^ 2 :=
        calc ‖x - y‖ / σ ^ 2 ≤ R₀ / σ ^ 2 := by gcongr; exact mem_closedBall_iff_norm.1 hx
          _ ≤ R₀ / (τ / 2) ^ 2 := by gcongr; exact hσs.1.le
      exact mul_le_mul (mul_le_mul hrσ (hC₁ _ (hin σ hσs x hx)) (norm_nonneg _) (by positivity))
        (hqB x) (norm_nonneg _) (mul_nonneg (by positivity) hC₁0)
    · rw [Set.indicator_of_notMem hx, hF']
      simp only
      rw [hφ'A _ (hout σ hσs x hx), mul_zero, zero_mul, norm_zero]
  -- `∂_σ φ(|x - y|/σ) = -(|x - y|/σ²) φ'(|x - y|/σ)`
  have h_diff : ∀ᵐ x ∂ν, ∀ σ ∈ Ioo (τ / 2) (R₀ / A), HasDerivAt (F · x) (F' σ x) σ := by
    refine ae_of_all _ fun x σ hσs => ?_
    have hσ : σ ≠ 0 := by linarith [hσs.1]
    have h1 : HasDerivAt (fun σ => ‖x - y‖ / σ) (-(‖x - y‖ / σ ^ 2)) σ := by
      convert (hasDerivAt_inv hσ).const_mul ‖x - y‖ using 1
      · funext σ
        rw [div_eq_mul_inv]
      · ring
    have h2 : HasDerivAt (fun σ => φ (‖x - y‖ / σ))
        (deriv φ (‖x - y‖ / σ) * -(‖x - y‖ / σ ^ 2)) σ :=
      (hφd _).hasDerivAt.comp σ h1
    convert h2.mul_const (q x) using 1
    rw [hF']
    ring
  -- (b), (c): dominated differentiation under the integral sign
  obtain ⟨hF'_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall hF_meas) hF_int (hF'_meas τ) h_bound (hind _) h_diff
  exact ⟨hF_int, hF'_int, hderiv⟩
/-- The radial test field `X(x) = φ(|x − y|/τ)(x − y)` (Simon Ch. 4, 3.2–3.3, cutoff
`γ(r) = φ(r/τ)`) is `C¹` with compact support in `B̄_{Aτ}(y)`: it equals `x − y` on `B_τ(y)`, and
away from `y` the norm `|x − y|` is smooth. -/
theorem Submission.doragm_rfv_radial_field_c1 : ∀ (P : ℕ) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → ContDiff ℝ 1 (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ HasCompactSupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ) := by
  intro P y φ A τ hφ hφ1 hφA hτ
  -- (iii) off `B̄_{Aτ}(y)` we have `A ≤ ‖x - y‖ / τ`, so `φ (‖x - y‖ / τ) = 0`
  have hsupp : tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ) := by
    refine closure_minimal (support_subset_iff'.2 fun x hx => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have hA : A ≤ ‖x - y‖ / τ := (le_div_iff₀ hτ).2 hx.le
    simp [hφA _ hA]
  -- (ii) a closed subset of the compact ball `B̄_{Aτ}(y)` is compact
  refine ⟨?_, (isCompact_closedBall y (A * τ)).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp⟩
  -- (i) `C¹` at every point
  rw [contDiff_iff_contDiffAt]
  intro x
  have hsub : ContDiffAt ℝ 1 (fun z : Euclid P => z - y) x := contDiffAt_id.sub contDiffAt_const
  by_cases hxy : x = y
  · -- near `y` we have `‖z - y‖ / τ < 1`, so the field is `z ↦ z - y`
    subst hxy
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds x hτ] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z - x‖ / τ ≤ 1 := (div_le_one hτ).2 hz.le
    simp [hφ1 _ h1]
  · -- away from `y` the norm `z ↦ ‖z - y‖` is smooth, since `x - y ≠ 0`
    have hnorm : ContDiffAt ℝ 1 (fun z : Euclid P => ‖z - y‖) x := hsub.norm ℝ (sub_ne_zero.2 hxy)
    exact (hφ.comp_contDiffAt x (hnorm.div_const τ)).smul hsub
/-- **Trace of the derivative of a radial field** (Simon Ch. 4, 3.2 and the identity after it,
with a subspace `Q` in place of `TₓM`; chapter-04.txt lines 225–262).  Let `φ` be `C¹` with
`φ = 1` on `(-∞, 1]`, `τ > 0`, `X(z) = φ(|z − y|/τ)(z − y)`, `p = Q.starProjection`, `v = x − y`
and `r = |v|`.  Then `trace(p ∘ DX(x)) = dim Q · φ(r/τ) + (r/τ) φ'(r/τ) (1 − |v − p v|²/r²)`.
`p` is a projection onto `Q`, so `trace p = dim Q` (`LinearMap.IsProj.trace`).  At `x = y` the
field is `z ↦ z − y` on `B_τ(y)`, so `DX(y) = I` and both sides equal `dim Q`.  For `x ≠ y`,
`DX(x) = φ(r/τ) I + φ'(r/τ) τ⁻¹ r⁻¹ ⟨v, ·⟩ v` (`|z − y| = √(|z − y|²)`, chain and product
rules), the rank-one part has trace `φ'(r/τ) τ⁻¹ r⁻¹ ⟨v, p v⟩` (`LinearMap.trace_smulRight`), and
`⟨v, p v⟩ = r² − |v − p v|²` since `v − p v ⊥ p v`. -/
theorem Submission.doragm_rfv_trace_radial_field : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (y x : Euclid P) (φ : ℝ → ℝ) (τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → 0 < τ → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) x).toLinearMap) = (Module.finrank ℝ Q : ℝ) * φ (‖x - y‖ / τ) + ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) - Q.starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) := by
  intro P Q y x φ τ hφ hφ1 hτ
  -- `p = Q.starProjection` is a projection onto `Q`, so its trace is `dim Q`.
  have htr : LinearMap.trace ℝ (Euclid P) Q.starProjection.toLinearMap = Module.finrank ℝ Q :=
    LinearMap.IsProj.trace ⟨fun w => Q.starProjection_apply_mem w,
      fun w hw => Submodule.starProjection_eq_self_iff.mpr hw⟩
  by_cases hxy : x = y
  · -- On `B(y, τ)` the field is `z ↦ z - y`, whose derivative is the identity.
    subst hxy
    have hev : (fun z : Euclid P => φ (‖z - x‖ / τ) • (z - x)) =ᶠ[𝓝 x] fun z => z - x := by
      filter_upwards [Metric.ball_mem_nhds x hτ] with z hz
      rw [hφ1 _ ((div_le_one hτ).mpr (mem_ball_iff_norm.mp hz).le), one_smul]
    rw [hev.fderiv_eq, fderiv_sub_const, fderiv_fun_id]
    simp [htr, hφ1 0 zero_le_one]
  · -- Derivative of `z ↦ ‖z - y‖` at `x ≠ y`, via `√(‖z - y‖²)`.
    have hr0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hsub : HasFDerivAt (fun z : Euclid P => z - y) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const y
    have hnorm := hsub.norm_sq.sqrt (pow_ne_zero 2 hr0.ne')
    have hsqrt : (fun z : Euclid P => √(‖z - y‖ ^ 2)) = fun z => ‖z - y‖ :=
      funext fun z => Real.sqrt_sq (norm_nonneg _)
    rw [hsqrt] at hnorm
    -- Chain rule for `c(z) = φ(‖z - y‖ / τ)`, then the product rule for `c(z) • (z - y)`.
    have hφd : HasDerivAt (fun t => φ (t / τ)) (deriv φ (‖x - y‖ / τ) * (1 / τ)) ‖x - y‖ :=
      ((hφ.differentiable one_ne_zero) _).hasDerivAt.comp _
        (HasDerivAt.div_const (hasDerivAt_id' ‖x - y‖) τ)
    have hX := (hφd.comp_hasFDerivAt x hnorm).smul hsub
    rw [show (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) =
      ((fun t => φ (t / τ)) ∘ fun z => ‖z - y‖) • fun z => z - y from rfl, hX.fderiv]
    -- `p ∘ (a I + ℓ(·) v) = a p + ℓ(·) p v`; the rank-one part has trace `ℓ(p v)`.
    have key : ∀ (a : ℝ) (ℓ : Euclid P →L[ℝ] ℝ) (v : Euclid P),
        LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ
          (a • ContinuousLinearMap.id ℝ (Euclid P) + ℓ.smulRight v).toLinearMap) =
          a * Module.finrank ℝ Q + ℓ (Q.starProjection v) := by
      intro a ℓ v
      have hcomp : Q.starProjection.toLinearMap ∘ₗ
          (a • ContinuousLinearMap.id ℝ (Euclid P) + ℓ.smulRight v).toLinearMap =
          a • Q.starProjection.toLinearMap +
            (ℓ : Euclid P →ₗ[ℝ] ℝ).smulRight (Q.starProjection v) := by
        ext w
        simp
      rw [hcomp, map_add, map_smul, htr, LinearMap.trace_smulRight, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
    -- Pythagoras: `⟨v, p v⟩ = ‖v‖² - ‖v - p v‖²`, as `v - p v ⊥ p v`.
    have hinner : inner ℝ (x - y) (Q.starProjection (x - y)) =
        ‖x - y‖ ^ 2 - ‖(x - y) - Q.starProjection (x - y)‖ ^ 2 := by
      have h0 := Submodule.starProjection_inner_eq_zero (K := Q) (x - y)
        (Q.starProjection (x - y)) (Q.starProjection_apply_mem _)
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0
      rw [norm_sub_sq_real (x - y) (Q.starProjection (x - y))]
      linarith
    rw [key]
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
      Real.sqrt_sq (norm_nonneg _), hinner]
    field_simp
    ring
/-- **Simon Ch. 4, 2.2 and 4.1.1**: for `R = (M, θ, ξ)` and `X ∈ C¹_c(U; ℝᴾ)` with `x ↦ p_{TₓM}`
`μ_R`-measurable, `div_M X` is `μ_R`-integrable and `δV(X) = ∫_M θ div_M X dHⁿ = ∫ div_M X dμ_R`,
`μ_R = θ Hⁿ⌞M`.  `div_M X(x) = tr(p_{TₓM} ∘ DX(x))` is bounded by `‖tr‖ ‖DX(x)‖`, and it vanishes
off the compact `spt X ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dsmc_firstVariation_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure ∧ R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
  intro P n U R X hX hcpt hU hp
  -- the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and `div_M X(x) = tr(p_x ∘ DX(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ x, tangentialDivergence n R.carrier X x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ X x) := fun x => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hD : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- `div_M X` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
      (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp.aestronglyMeasurable
      hD.aestronglyMeasurable
  -- `|div_M X(x)| ≤ ‖tr‖ C 1_K(x)`, `K = spt X`, `C = sup ‖DX‖`
  obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hcpt.fderiv ℝ)
  have hKm : MeasurableSet (tsupport X) := (isClosed_tsupport X).measurableSet
  have hbound : ∀ x, ‖tangentialDivergence n R.carrier X x‖ ≤
      (tsupport X).indicator (fun _ => ‖tr‖ * C) x := by
    intro x
    rw [hdiv]
    by_cases hxK : x ∈ tsupport X
    · rw [Set.indicator_of_mem hxK]
      refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _) zero_le_one
    · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
        ContinuousLinearMap.comp_zero, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport X) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport X) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.firstVariation]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
/-- The approximate tangent planes `TₓM` of `R = τ(M, θ, ξ)` are `n`-dimensional for `μ_R`-a.e.
`x`: by `R.orients`, `Hⁿ⌞M`-a.e. `x` has an approximate tangent plane (Simon Ch. 3, 1.4), which is
`n`-dimensional by definition, and `μ_R = θ Hⁿ⌞M ≪ Hⁿ⌞M`. -/
theorem Submission.dorag_aa_ae_finrank_approxTangentPlane : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
  intro P n U R
  -- `μ_R = θ Hⁿ⌞M ≪ Hⁿ⌞M`, and `Hⁿ⌞M`-a.e. `x` has an approximate tangent plane
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le R.orients] with x hx
  obtain ⟨Q, hQ, -⟩ := hx
  -- `TₓM` is then the chosen approximate tangent plane, whose dimension is `n`
  have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
  rw [approxTangentPlane, dite_eq_left h]
  exact h.choose_spec.finrank_eq
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1

/-- **Simon Ch. 4, 3.2–3.3 with generalized mean curvature (3.14)**: the radial first-variation
identity.  The radial field `X(x) = φ(r/τ)(x − y)`, `r = |x − y|`, is `C¹` with support in
`B̄_{Aτ}(y) ⊆ W`, so `∫ div_M X dμ = δV(X) = −∫ X · H dμ` (2.2, and 3.14 (★) in `W`), and
wherever `dim TₓM = n`, i.e. `μ`-a.e., `div_M X = n φ(r/τ) + (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²)`, where
`|(Dr)^⊥|² = |(x − y) − p_{TₓM}(x − y)|²/r²` (3.2).  Both terms are `μ`-integrable: `φ(r/τ)` is
continuous and vanishes off `B̄_{Aτ}(y)`, which has finite `μ`-measure, and the second term is
`div_M X − n φ(r/τ)` `μ`-a.e. -/
theorem Submission.doragm_radial_first_variation : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → closedBall y (A * τ) ⊆ W → (n : ℝ) * (∫ x, φ (‖x - y‖ / τ) ∂R.measure) + (∫ x, ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ∂R.measure) = -∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure := by
  intro P n U W R H _ hWU hp hH y φ A τ hφ h1 h0 hτ hball
  -- `X(x) = φ(r/τ)(x − y)` is `C¹`, with compact support in `B̄_{Aτ}(y) ⊆ W ⊆ U`
  obtain ⟨hXc, hXcpt, hXK⟩ := Submission.doragm_rfv_radial_field_c1 P y φ A τ hφ h1 h0 hτ
  have hXW := hXK.trans hball
  -- `δV(X) = −∫ X · H dμ` by hypothesis, and `δV(X) = ∫ div_M X dμ` with `div_M X ∈ L¹(μ)`
  have hmc := hH _ hXc hXcpt hXW
  obtain ⟨hint, hfv⟩ := Submission.dsmc_firstVariation_eq_integral P n U R _ hXc hXcpt
    (hXW.trans hWU) hp.aemeasurable
  -- `div_M X = n φ(r/τ) + (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²)` wherever `dim TₓM = n`, i.e. `μ`-a.e.
  have hdiv : (fun x => tangentialDivergence n R.carrier
      (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) x) =ᵐ[R.measure] fun x =>
      (n : ℝ) * φ (‖x - y‖ / τ) + ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) *
        (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
          ‖x - y‖ ^ 2) := by
    filter_upwards [Submission.dorag_aa_ae_finrank_approxTangentPlane P n U R] with x hx
    have htr := Submission.doragm_rfv_trace_radial_field P (approxTangentPlane n R.carrier x) y x
      φ τ hφ h1 hτ
    rw [hx] at htr
    exact htr
  -- `φ(r/τ)` is continuous and vanishes off the compact `K = B̄_{Aτ}(y)`, and `μ(K) < ∞`
  have hK : IsCompact (closedBall y (A * τ)) := isCompact_closedBall y (A * τ)
  have hKfin := (Submission.rsd_imrep_compact_measure_ne_top P n U R _ hK (hball.trans hWU)).2
  have hf₁c : Continuous fun x : Euclid P => φ (‖x - y‖ / τ) :=
    hφ.continuous.comp ((continuous_id.sub continuous_const).norm.div_const τ)
  have hf₁0 : ∀ x, x ∉ closedBall y (A * τ) → φ (‖x - y‖ / τ) = 0 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact h0 _ ((le_div_iff₀ hτ).2 hx.le)
  obtain ⟨C, hC⟩ := hf₁c.bounded_above_of_compact_support (HasCompactSupport.intro hK hf₁0)
  have hf₁ : Integrable (fun x : Euclid P => φ (‖x - y‖ / τ)) R.measure := by
    refine ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const (C := C) hKfin)).mono'
      hf₁c.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall y (A * τ)
    · rw [indicator_of_mem hx]
      exact hC x
    · rw [indicator_of_notMem hx, hf₁0 x hx, norm_zero]
  -- the second term is `div_M X − n φ(r/τ)` `μ`-a.e., hence integrable as well
  have hf₂ : Integrable (fun x => ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) *
      (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
        ‖x - y‖ ^ 2)) R.measure := by
    refine (hint.sub (hf₁.const_mul (n : ℝ))).congr ?_
    filter_upwards [hdiv] with x hx
    simp only [Pi.sub_apply, hx, add_sub_cancel_left]
  -- `n ∫ φ(r/τ) dμ + ∫ (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²) dμ = ∫ div_M X dμ = δV(X) = −∫ X · H dμ`
  rw [← integral_const_mul, ← integral_add (hf₁.const_mul _) hf₂, ← integral_congr_ae hdiv,
    ← hfv, hmc]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => real_inner_smul_left _ _ _)

/-- **Simon Ch. 4, 3.4–3.5 and 3.16** (smoothed annular monotonicity bounds, `|H| ≤ κ`): if
`A > 1`, `0 < s < t` and `B̄_{At}(y) ⊆ W`, then with `c = Aκ` and
`F_y = |(x − y) − p_x(x − y)|²/|x − y|^{n+2}`,
`∫_{B̄_t∖B̄_{As}} F_y dμ + e^{cs}s⁻ⁿμ(B̄_s) ≤ e^{ct}t⁻ⁿμ(B̄_{At})` and
`e^{−ct}t⁻ⁿμ(B̄_t) ≤ e^{−cs}s⁻ⁿμ(B̄_{As}) + Aⁿ∫_{B̄_{At}∖B̄_s} F_y dμ` in `[0, ∞]`.  For the profile
`φ`, `N = |(x − y) − p_x(x − y)|²/|x − y|²` and `q = N/max(s, |x − y|)ⁿ`, the scale functions
`I(τ) = ∫ φ(r/τ) dμ` and `G(τ) = ∫ φ(r/τ) q dμ` satisfy `n I − τ I' + τ J' = −h` (radial first
variation), `|h| ≤ Aκτ I` and `G' ≤ τ⁻ⁿ J' ≤ Aⁿ G'` on `[s, t]`; the integrating-factor comparison
bounds `G(t) − G(s)`, which lies between the two annular integrals, while `I(τ)` lies between
`μ(B̄_τ)` and `μ(B̄_{Aτ})`. -/
theorem Submission.doragm_smoothed_annular_bounds : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (A s t : ℝ), 1 < A → 0 < s → s < t → closedBall y (A * t) ⊆ W → (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (A * κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n) * R.measure (closedBall y (A * t)) ∧ ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n) * R.measure (closedBall y (A * s)) + ENNReal.ofReal (A ^ n) * ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure := by
  intro P n U W R H κ hW hWU hp _ hκ hFV y A s t hA hs hst hball
  -- Step 1: `A > 0`, `t > 0`, and `c = Aκ ≥ 0` because `κ ≥ ‖H 0‖ ≥ 0`
  have hA0 : 0 < A := zero_lt_one.trans hA
  have ht : 0 < t := hs.trans hst
  have hc : 0 ≤ A * κ := mul_nonneg hA0.le ((norm_nonneg _).trans (hκ 0))
  -- a radius `R₀ = δ + At > At` with `B̄_{R₀}(y) ⊆ W`; this compact subset of `U` has finite mass
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_closedBall y (A * t)).exists_cthickening_subset_open hW hball
  rw [cthickening_closedBall hδ.le (mul_pos hA0 ht).le] at hδW
  have hAτR₀ : ∀ τ ∈ Icc s t, A * τ < δ + A * t := fun τ hτ =>
    (mul_le_mul_of_nonneg_left hτ.2 hA0.le).trans_lt (lt_add_of_pos_left _ hδ)
  have hμR₀ : R.measure (closedBall y (δ + A * t)) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall _ _) (hδW.trans hWU)
  -- Step 2: the cutoff profile `φ`
  obtain ⟨φ, hφC, hφanti, hφbd, hφ1, hφ0, hφ'le, hφ'ne⟩ :=
    Submission.doragm_sab_cutoff_profile A hA
  -- Step 3: `N = |(x - y) - p_x(x - y)|²/|x - y|² ∈ [0, 1]` and `q = N/max(s, |x - y|)ⁿ ∈ [0, s⁻ⁿ]`
  obtain ⟨N, hN⟩ : ∃ N : Euclid P → ℝ, ∀ x, N x =
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hN01 : ∀ x, 0 ≤ N x ∧ N x ≤ 1 := by
    intro x
    rw [hN]
    refine ⟨by positivity,
      div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)⟩
    -- `v - p_x v` is the projection of `v` onto `(TₓM)^⊥`
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_starProjection_apply_le _ _
  have hr : Continuous fun x : Euclid P => ‖x - y‖ := (continuous_id.sub continuous_const).norm
  have hNm : AEStronglyMeasurable N R.measure := by
    have hpx : AEStronglyMeasurable
        (fun x => (approxTangentPlane n R.carrier x).starProjection (x - y)) R.measure :=
      (ContinuousLinearMap.id ℝ (Euclid P →L[ℝ] Euclid P)).aestronglyMeasurable_comp₂ hp
        (continuous_id.sub continuous_const).aestronglyMeasurable
    rw [show N = _ from funext hN]
    exact ((((continuous_id.sub continuous_const).aestronglyMeasurable.sub hpx).norm.aemeasurable
      |>.pow_const 2).div (hr.pow 2).measurable.aemeasurable).aestronglyMeasurable
  have hqm : AEStronglyMeasurable (fun x => N x / (max s ‖x - y‖) ^ n) R.measure :=
    (hNm.aemeasurable.div
      ((continuous_const.max hr).pow n).measurable.aemeasurable).aestronglyMeasurable
  have hq0 : ∀ x, 0 ≤ N x / (max s ‖x - y‖) ^ n := fun x =>
    div_nonneg (hN01 x).1 (pow_nonneg (hs.le.trans (le_max_left _ _)) n)
  have hqB : ∀ x, ‖N x / (max s ‖x - y‖) ^ n‖ ≤ 1 / s ^ n := by
    intro x
    rw [Real.norm_of_nonneg (hq0 x)]
    have hsn : 0 < s ^ n := pow_pos hs n
    have hDs : s ^ n ≤ (max s ‖x - y‖) ^ n := pow_le_pow_left₀ hs.le (le_max_left _ _) n
    calc N x / (max s ‖x - y‖) ^ n ≤ 1 / (max s ‖x - y‖) ^ n :=
          div_le_div_of_nonneg_right (hN01 x).2 (hsn.le.trans hDs)
      _ ≤ 1 / s ^ n := one_div_le_one_div_of_le hsn hDs
  -- `q = F_y` where `|x - y| > s`
  have hFq : ∀ x, s < ‖x - y‖ →
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)
        = N x / (max s ‖x - y‖) ^ n := by
    intro x hx
    rw [max_eq_right hx.le, hN]
    ring
  -- Step 4: integrability and `τ`-derivatives of the cutoff integrals (weights `1`, `q`, `N`)
  have hcd1 : ∀ τ ∈ Icc s t, Integrable (fun x => φ (‖x - y‖ / τ)) R.measure ∧
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ)) R.measure ∧
      HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) ∂R.measure)
        (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure) τ := fun τ hτ => by
    simpa only [mul_one] using Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ
      (fun _ => 1) A 1 τ (δ + A * t) hφC hφ0 hA0 (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀
      aestronglyMeasurable_const (fun _ => by simp)
  have hcdq : ∀ τ ∈ Icc s t,
      Integrable (fun x => φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) R.measure ∧
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) *
        (N x / (max s ‖x - y‖) ^ n)) R.measure ∧
      HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)
        (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)
          ∂R.measure) τ := fun τ hτ =>
    Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ
      (fun x => N x / (max s ‖x - y‖) ^ n) A (1 / s ^ n) τ (δ + A * t) hφC hφ0 hA0
      (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀ hqm hqB
  have hcdN : ∀ τ ∈ Icc s t,
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x) R.measure :=
    fun τ hτ => (Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ N A 1 τ (δ + A * t)
      hφC hφ0 hA0 (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀ hNm
      (fun x => by rw [Real.norm_of_nonneg (hN01 x).1]; exact (hN01 x).2)).2.1
  -- Step 5: the identity `(E)`: `n I − τ I' + τ J' = −h` on `[s, t]`, from the radial first
  -- variation and `(r/τ) φ'(r/τ) (1 − N) = (−τ)(−(r/τ²) φ'(r/τ)) + τ (−(r/τ²) φ'(r/τ)) N`
  have hE : ∀ τ ∈ Icc s t, (n : ℝ) * (∫ x, φ (‖x - y‖ / τ) ∂R.measure)
      - τ * (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure)
      + τ * (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂R.measure)
      = -∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure := by
    intro τ hτ
    have hτ0 : 0 < τ := hs.trans_le hτ.1
    have hrv := Submission.doragm_radial_first_variation P n U W R H hW hWU hp hFV y φ A τ
      hφC hφ1 hφ0 hτ0
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hτ.2 hA0.le)).trans hball)
    have hsplit : ∫ x, ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) -
        (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ∂R.measure
        = ∫ x, (-τ * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ)) +
          τ * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x)) ∂R.measure := by
      congr 1
      ext x
      rw [← hN x]
      generalize deriv φ (‖x - y‖ / τ) = d
      field_simp
      ring
    rw [hsplit, integral_add ((hcd1 τ hτ).2.1.const_mul _) ((hcdN τ hτ).const_mul _),
      integral_const_mul, integral_const_mul] at hrv
    linarith
  -- Steps 6–7: the curvature bound `|h| ≤ Aκτ I` and the comparison `G' ≤ τ⁻ⁿ J' ≤ Aⁿ G'`
  have hsq := fun τ (hτ : τ ∈ Icc s t) =>
    Submission.doragm_sab_deriv_weight_squeeze P n R.measure y φ N A s τ hA hs hτ.1 hφ'le hφ'ne
      (fun x => (hN01 x).1) (hcdq τ hτ).2.1 (hcdN τ hτ)
  -- Steps 8–9: the integrating-factor comparison on `[s, t]`
  obtain ⟨ha, hb⟩ := Submission.doragm_sab_exp_ratio_compare n (A * κ) (A ^ n) s t
    (fun τ => ∫ x, φ (‖x - y‖ / τ) ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure)
    (fun τ => ∫ x, φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)
      ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂R.measure)
    (fun τ => ∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure)
    hc hs hst (fun τ hτ => (hcd1 τ hτ).2.2) (fun τ hτ => (hcdq τ hτ).2.2) hE
    (fun τ hτ => Submission.doragm_sab_curvature_term_le P R.measure y H φ κ A τ
      (hs.trans_le hτ.1) (fun u => (hφbd u).1) hφ0 hκ (hcd1 τ hτ).1)
    (fun τ hτ => (hsq τ hτ).1) (fun τ hτ => (hsq τ hτ).2.1) (fun τ hτ => (hsq τ hτ).2.2)
  -- Step 10: `μ(B̄_τ) ≤ I(τ) ≤ μ(B̄_{Aτ})` at `τ = s, t`, and the annular comparison
  have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
  obtain ⟨hms, hmAs⟩ :=
    Submission.doragm_sab_cutoff_mass_sandwich P R.measure y φ A s hs hφbd hφ1 hφ0 (hcd1 s hsI).1
  obtain ⟨hmt, hmAt⟩ :=
    Submission.doragm_sab_cutoff_mass_sandwich P R.measure y φ A t ht hφbd hφ1 hφ0 (hcd1 t htI).1
  obtain ⟨hΔ, hX, hY⟩ := Submission.doragm_sab_annulus_increment_sandwich P R.measure y φ
    (fun x => N x / (max s ‖x - y‖) ^ n)
    (fun x => ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
      ‖x - y‖ ^ (n + 2)) A s t hA hs hst.le hφanti hφbd hφ1 hφ0 hq0 hFq (hcdq s hsI).1
    (hcdq t htI).1
  beta_reduce at ha hb hΔ hX hY
  have hIs : 0 ≤ ∫ x, φ (‖x - y‖ / s) ∂R.measure := integral_nonneg fun x => (hφbd _).1
  -- Steps 11–12: combine in `[0, ∞]`
  refine ⟨?_, ?_⟩
  · calc _ ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) +
          ENNReal.ofReal (Real.exp (A * κ * s) / s ^ n) *
            ENNReal.ofReal (∫ x, φ (‖x - y‖ / s) ∂R.measure) := by gcongr
      _ = ENNReal.ofReal (((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) +
          Real.exp (A * κ * s) / s ^ n * ∫ x, φ (‖x - y‖ / s) ∂R.measure) := by
        rw [ENNReal.ofReal_add hΔ (mul_nonneg (by positivity) hIs),
          ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n * ∫ x, φ (‖x - y‖ / t) ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n) *
          ENNReal.ofReal (∫ x, φ (‖x - y‖ / t) ∂R.measure) := ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by gcongr
  · calc _ ≤ ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n) *
          ENNReal.ofReal (∫ x, φ (‖x - y‖ / t) ∂R.measure) := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n * ∫ x, φ (‖x - y‖ / t) ∂R.measure) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n * (∫ x, φ (‖x - y‖ / s) ∂R.measure) +
          A ^ n * ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n) *
            ENNReal.ofReal (∫ x, φ (‖x - y‖ / s) ∂R.measure) +
          ENNReal.ofReal (A ^ n) *
            ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
              ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hIs) (mul_nonneg (by positivity) hΔ),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by gcongr

/-- **Annular monotonicity with bounded mean curvature** (Simon Ch. 4, 3.5 → 3.6 and 3.17,
"letting `ε ↓ 0`").  Let `μ = θ Hⁿ⌞M`, `|H| ≤ κ`,
`F_y(x) = |(x − y) − p_{TₓM}(x − y)|²/|x − y|^{n+2}` and `0 < s < t` with `B̄_t(y) ⊆ W`.  Then
(M1) `∫_{B̄_t∖B̄_s} F_y dμ + e^{κs} s⁻ⁿ μ(B̄_s) ≤ e^{κt} t⁻ⁿ μ(B̄_t)` and
(M2) `e^{−κt} t⁻ⁿ μ(B̄_t) ≤ e^{−κs} s⁻ⁿ μ(B̄_s) + ∫_{B̄_t∖B̄_s} F_y dμ`.

Choose `δ₀ > 0` with `B̄_{t+δ₀}(y) ⊆ W` and the widths `A_m = 1 + (δ₀/t)/(m + 1) ↓ 1`, and apply
the smoothed bounds `Submission.doragm_smoothed_annular_bounds` with `A = A_m`.  As `m → ∞`,
`μ(B̄_{A_mρ}) → μ(B̄_ρ)` by continuity from above (`μ(B̄_{t+δ₀}) < ∞`).  For `ν = F_y μ` the inner
annuli `B̄_t∖B̄_{A_ms}` increase to `B̄_t∖B̄_s`, and the outer annuli `B̄_{A_mt}∖B̄_s` decrease to
it with `ν(B̄_{A_0t}∖B̄_s) ≤ s⁻ⁿ μ(B̄_{A_0t}) < ∞`, because `F_y(x) ≤ |x − y|⁻ⁿ`.  The coefficients
converge, and `e^{κs} ≤ e^{A_mκs}` as `κ ≥ 0`; passing to the limit gives (M1) and (M2). -/
theorem Submission.doragm_annular_monotonicity : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) ∧ ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * R.measure (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure := by
  intro P n U W R H κ hW hWU hp hH hHκ hFV y s t hs hst hBt
  have hsm := Submission.doragm_smoothed_annular_bounds P n U W R H κ hW hWU hp hH hHκ hFV y
  have ht : 0 < t := hs.trans hst
  -- `κ ≥ 0`, since `‖H y‖ ≤ κ`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ y)
  -- `μ` is finite on compact subsets of `U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Step 1: `B̄_{t+δ₀}(y) ⊆ W`, so `μ(B̄_ρ(y)) < ∞` for `ρ ≤ t + δ₀`
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := (isCompact_closedBall y t).exists_cthickening_subset_open hW hBt
  rw [cthickening_closedBall hδ₀.le ht.le] at hδ₀W
  have hfinB : ∀ ρ, ρ ≤ δ₀ + t → R.measure (closedBall y ρ) ≠ ∞ := fun ρ hρ =>
    hfin _ (isCompact_closedBall y ρ) ((closedBall_subset_closedBall hρ).trans (hδ₀W.trans hWU))
  -- Step 2: the widths `A_m = 1 + (δ₀/t)/(m + 1)`: `A_m > 1`, `A_m ↓ 1` and `A_m t ≤ t + δ₀`
  obtain ⟨A, hA1, hAanti, hAlim, hAt⟩ : ∃ A : ℕ → ℝ, (∀ m, 1 < A m) ∧ Antitone A ∧
      Tendsto A atTop (𝓝 1) ∧ ∀ m, A m * t ≤ δ₀ + t := by
    have hc : 0 < δ₀ / t := div_pos hδ₀ ht
    have he : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
    have he1 : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ≤ 1 := fun m =>
      (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    refine ⟨fun m => 1 + δ₀ / t * (1 / ((m : ℝ) + 1)), fun m => ?_, fun i j hij => ?_, ?_,
      fun m => ?_⟩
    · dsimp only
      linarith [mul_pos hc (he m)]
    · have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
      have := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1) hij') hc.le
      dsimp only
      linarith
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ₀ / t)).const_add 1
      rwa [mul_zero, add_zero] at h
    · have h2 : (1 + δ₀ / t * (1 / ((m : ℝ) + 1))) * t = t + δ₀ * (1 / ((m : ℝ) + 1)) := by
        field_simp
      dsimp only
      rw [h2]
      linarith [mul_le_mul_of_nonneg_left (he1 m) hδ₀.le]
  have hBA : ∀ m, closedBall y (A m * t) ⊆ W := fun m =>
    (closedBall_subset_closedBall (hAt m)).trans hδ₀W
  -- Step 3: for `0 < ρ ≤ t`, the balls `B̄_{A_mρ}` decrease to `B̄_ρ`, so
  -- `μ(B̄_{A_mρ}) → μ(B̄_ρ)` (continuity from above)
  have hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ t →
      Antitone (fun m => closedBall y (A m * ρ)) ∧
      (⋂ m, closedBall y (A m * ρ)) = closedBall y ρ ∧
      Tendsto (fun m => R.measure (closedBall y (A m * ρ))) atTop
        (𝓝 (R.measure (closedBall y ρ))) := by
    intro ρ hρ hρt
    have hanti : Antitone (fun m => closedBall y (A m * ρ)) := fun i j hij =>
      closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (hAanti hij) hρ.le)
    have hinter : (⋂ m, closedBall y (A m * ρ)) = closedBall y ρ := by
      ext x
      simp only [mem_iInter, mem_closedBall]
      refine ⟨fun h => ?_, fun h m => h.trans (le_mul_of_one_le_left hρ.le (hA1 m).le)⟩
      have hlim : Tendsto (fun m => A m * ρ) atTop (𝓝 (1 * ρ)) := hAlim.mul_const ρ
      rw [one_mul] at hlim
      exact ge_of_tendsto' hlim h
    have hfin0 : R.measure (closedBall y (A 0 * ρ)) ≠ ∞ :=
      hfinB _ ((mul_le_mul_of_nonneg_left hρt (by linarith [hA1 0])).trans (hAt 0))
    have h := tendsto_measure_iInter_atTop (μ := R.measure)
      (fun m => measurableSet_closedBall.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rw [hinter] at h
    exact ⟨hanti, hinter, h⟩
  obtain ⟨hanti_s, hinter_s, hlim_s⟩ := hball s hs hst.le
  obtain ⟨hanti_t, hinter_t, hlim_t⟩ := hball t ht le_rfl
  have hfin_s : R.measure (closedBall y s) ≠ ∞ := hfinB s (by linarith)
  have hfin_t : R.measure (closedBall y t) ≠ ∞ := hfinB t (by linarith)
  -- `ν = F_y μ`, so that `∫⁻_S F_y dμ = ν(S)` for Borel `S`
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Euclid P), ∀ S, MeasurableSet S →
      ∫⁻ x in S, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection
        (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure = ν S :=
    ⟨_, fun S hS => (withDensity_apply _ hS).symm⟩
  have hmeas : ∀ a b : ℝ, MeasurableSet (closedBall y a \ closedBall y b) := fun a b =>
    measurableSet_closedBall.diff measurableSet_closedBall
  -- the smoothed bounds (i'_m) and (ii'_m), with the annular integrals written via `ν`
  have hbd : ∀ m, ν (closedBall y t \ closedBall y (A m * s)) +
        ENNReal.ofReal (Real.exp (A m * κ * s) / s ^ n) * R.measure (closedBall y s) ≤
        ENNReal.ofReal (Real.exp (A m * κ * t) / t ^ n) * R.measure (closedBall y (A m * t)) ∧
      ENNReal.ofReal (Real.exp (-(A m * κ * t)) / t ^ n) * R.measure (closedBall y t) ≤
        ENNReal.ofReal (Real.exp (-(A m * κ * s)) / s ^ n) * R.measure (closedBall y (A m * s)) +
        ENNReal.ofReal (A m ^ n) * ν (closedBall y (A m * t) \ closedBall y s) := by
    intro m
    rw [← hν _ (hmeas _ _), ← hν _ (hmeas _ _)]
    exact hsm (A m) s t (hA1 m) hs hst (hBA m)
  -- Step 4(a): the inner annuli `B̄_t∖B̄_{A_ms}` increase to `B̄_t∖B̄_s`
  have hin : Tendsto (fun m => ν (closedBall y t \ closedBall y (A m * s))) atTop
      (𝓝 (ν (closedBall y t \ closedBall y s))) := by
    have hmono : Monotone fun m => closedBall y t \ closedBall y (A m * s) := fun i j hij =>
      sdiff_subset_sdiff_right (hanti_s hij)
    have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [← Set.sdiff_iInter, hinter_s] at h
  -- Step 4(b): `F_y(x) ≤ |x − y|⁻ⁿ ≤ s⁻ⁿ` off `B̄_s`, as `|v − p v| ≤ |v|`
  have hF : ∀ x : Euclid P, x ∉ closedBall y s →
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
        ‖x - y‖ ^ (n + 2) ≤ 1 / s ^ n := by
    intro x hx
    rw [mem_closedBall, not_le, dist_eq_norm] at hx
    have hr : 0 < ‖x - y‖ := hs.trans hx
    have hperp : ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ≤
        ‖x - y‖ := by
      rw [← Submodule.starProjection_orthogonal_val]
      exact Submodule.norm_starProjection_apply_le _ _
    calc ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
          ‖x - y‖ ^ (n + 2)
        ≤ ‖x - y‖ ^ 2 / ‖x - y‖ ^ (n + 2) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hperp 2) (by positivity)
      _ = 1 / ‖x - y‖ ^ n := by
          rw [pow_add, div_mul_eq_div_div_swap, div_self (pow_ne_zero 2 hr.ne')]
      _ ≤ 1 / s ^ n := one_div_le_one_div_of_le (pow_pos hs n) (pow_le_pow_left₀ hs.le hx.le n)
  -- Step 4(b): the outer annuli `B̄_{A_mt}∖B̄_s` decrease to `B̄_t∖B̄_s`, the first having
  -- `ν(B̄_{A_0t}∖B̄_s) ≤ s⁻ⁿ μ(B̄_{A_0t}) < ∞`
  have hout : Tendsto (fun m => ν (closedBall y (A m * t) \ closedBall y s)) atTop
      (𝓝 (ν (closedBall y t \ closedBall y s))) := by
    have hanti' : Antitone fun m => closedBall y (A m * t) \ closedBall y s := fun i j hij =>
      sdiff_subset_sdiff_left (hanti_t hij)
    have hinter' : (⋂ m, closedBall y (A m * t) \ closedBall y s) =
        closedBall y t \ closedBall y s := by
      rw [← hinter_t]
      ext x
      simp only [mem_iInter, Set.mem_sdiff]
      exact ⟨fun h => ⟨fun m => (h m).1, (h 0).2⟩, fun h m => ⟨h.1 m, h.2⟩⟩
    have hle : ν (closedBall y (A 0 * t) \ closedBall y s) ≤
        ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t)) := by
      rw [← hν _ (hmeas _ _)]
      calc ∫⁻ x in closedBall y (A 0 * t) \ closedBall y s, ENNReal.ofReal
            (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
              ‖x - y‖ ^ (n + 2)) ∂R.measure
          ≤ ∫⁻ _ in closedBall y (A 0 * t) \ closedBall y s, ENNReal.ofReal (1 / s ^ n)
              ∂R.measure :=
            setLIntegral_mono' (hmeas _ _) fun x hx => ENNReal.ofReal_le_ofReal (hF x hx.2)
        _ = ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t) \ closedBall y s) :=
            setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t)) :=
            mul_le_mul' le_rfl (measure_mono sdiff_subset)
    have hfin' : ν (closedBall y (A 0 * t) \ closedBall y s) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinB _ (hAt 0))) hle
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun m => (hmeas _ _).nullMeasurableSet) hanti' ⟨0, hfin'⟩
    rwa [hinter'] at h
  -- Step 5: the coefficients converge
  have hAκ : Tendsto (fun m => A m * κ) atTop (𝓝 κ) := by
    have h := hAlim.mul_const κ
    rwa [one_mul] at h
  have hexp : ∀ ρ : ℝ,
      Tendsto (fun m => ENNReal.ofReal (Real.exp (A m * κ * ρ) / ρ ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n))) ∧
      Tendsto (fun m => ENNReal.ofReal (Real.exp (-(A m * κ * ρ)) / ρ ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(κ * ρ)) / ρ ^ n))) := fun ρ =>
    ⟨ENNReal.tendsto_ofReal (((hAκ.mul_const ρ).rexp).div_const _),
      ENNReal.tendsto_ofReal (((hAκ.mul_const ρ).neg.rexp).div_const _)⟩
  have hpow : Tendsto (fun m => ENNReal.ofReal (A m ^ n)) atTop (𝓝 1) := by
    have h := ENNReal.tendsto_ofReal (hAlim.pow n)
    rwa [one_pow, ENNReal.ofReal_one] at h
  rw [hν _ (hmeas _ _)]
  constructor
  · -- Step 6, (M1): `e^{κs} ≤ e^{A_mκs}`; pass to the limit in (i'_m)
    refine le_of_tendsto_of_tendsto' (hin.add tendsto_const_nhds)
      (ENNReal.Tendsto.mul (hexp t).1 (Or.inr hfin_t) hlim_t (Or.inr ENNReal.ofReal_ne_top))
      fun m => ?_
    have hcoef : ENNReal.ofReal (Real.exp (κ * s) / s ^ n) ≤
        ENNReal.ofReal (Real.exp (A m * κ * s) / s ^ n) := by
      refine ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (pow_pos hs n).le)
      rw [mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg hκ hs.le) (hA1 m).le
    exact le_trans (add_le_add le_rfl (mul_le_mul' hcoef le_rfl)) (hbd m).1
  · -- Step 7, (M2): pass to the limit in (ii'_m)
    have h := le_of_tendsto_of_tendsto'
      (ENNReal.Tendsto.mul_const (hexp t).2 (Or.inr hfin_t))
      ((ENNReal.Tendsto.mul (hexp s).2 (Or.inr hfin_s) hlim_s (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.mul hpow (Or.inl one_ne_zero) hout (Or.inr ENNReal.one_ne_top)))
      fun m => (hbd m).2
    rwa [one_mul] at h
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

/-- **Unit lower bound for the monotone ball ratio at support points** (Simon Ch. 4, 3.8–3.11
and 4.10(1)).  Let `μ = θ Hⁿ⌞M`, and let `f_z(ρ) = e^{κρ} ρ^{−n} μ(B_ρ(z))` be nondecreasing in
`ρ` whenever `B_ρ(z) ⊆ W`.  Then `ωₙ ≤ f_y(t)` for every `y ∈ spt μ` and `t > 0` with
`B_t(y) ⊆ W`.

Suppose `f_y(t) < ωₙ`.  By continuity from above there is `δ > 0` with `B_{t+δ}(y) ⊆ W` and
`b = e^{κt} t^{−n} μ(B_{t+δ}(y)) < c < ωₙ` for some `c`.  As `y ∈ spt μ`, `μ(B_δ(y)) > 0`, so
`B_δ(y)` contains a point `x` at which `M` has an approximate tangent space (`μ`-a.e. point does).
Then `Submission.doragm_approxTangent_lower_density` gives `c σⁿ ≤ Hⁿ(M ∩ B_σ(x))` for some
`0 < σ < t`.  Since `e^{κσ} ≥ 1`, `θ ≥ 1` on `M` and `B_t(x) ⊆ B_{t+δ}(y)`, monotonicity at `x`
gives `c ≤ f_x(σ) ≤ f_x(t) ≤ b`, a contradiction. -/
theorem Submission.doragm_support_ball_ratio_ge : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (κ : ℝ), 0 < n → IsOpen W → W ⊆ U → 0 ≤ κ → (∀ (z : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall z t ⊆ W → ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall z s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall z t)) → ∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
  intro P n U W R κ hn hW hWU hκ hmono y hy t ht hyt
  -- `μ ≥ Hⁿ⌞M` on measurable sets, since `θ ≥ 1` on `M`
  have hHμ : ∀ S : Set (Euclid P), MeasurableSet S → μHE[n] (R.carrier ∩ S) ≤ R.measure S := by
    intro S hS
    rw [IMRep.measure, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_comm,
      ← setLIntegral_one]
    apply setLIntegral_mono' (hS.inter R.measurableSet_carrier)
    intro x hx
    exact_mod_cast R.mult_pos x hx.2
  -- `μ` is finite on compact subsets of `U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- `μ`-a.e. point has an approximate tangent space, as `μ ≪ Hⁿ⌞M`
  have hgood : ∀ᵐ x ∂R.measure, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (R.orients.mono fun x ⟨Q, hQ, _⟩ => ⟨Q, hQ⟩)
  -- suppose `f_y(t) < ωₙ`
  by_contra hlt
  rw [not_le] at hlt
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (κ * t) / t ^ n)
  -- `B_{t+δ₀}(y) ⊆ W`, and `μ(B_{t+δ₀/(m+1)}(y)) → μ(B_t(y))` by continuity from above
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := (isCompact_closedBall y t).exists_cthickening_subset_open hW hyt
  rw [cthickening_closedBall hδ₀.le ht.le] at hδ₀W
  have hanti : Antitone (fun m : ℕ => closedBall y (t + δ₀ / ((m : ℝ) + 1))) := by
    intro i j hij
    apply closedBall_subset_closedBall
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have : δ₀ / ((j : ℝ) + 1) ≤ δ₀ / ((i : ℝ) + 1) :=
      div_le_div_of_nonneg_left hδ₀.le hi hij'
    linarith
  have hinter : (⋂ m : ℕ, closedBall y (t + δ₀ / ((m : ℝ) + 1))) = closedBall y t := by
    ext z
    simp only [mem_iInter, mem_closedBall]
    constructor
    · intro h
      have hlim : Tendsto (fun m : ℕ => t + δ₀ * (1 / ((m : ℝ) + 1))) atTop (𝓝 (t + δ₀ * 0)) :=
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ₀)
      rw [mul_zero, add_zero] at hlim
      exact ge_of_tendsto' hlim fun m => by rw [mul_one_div]; exact h m
    · intro h m
      have : 0 < δ₀ / ((m : ℝ) + 1) := by positivity
      linarith
  have hfin0 : R.measure (closedBall y (t + δ₀ / (((0 : ℕ) : ℝ) + 1))) ≠ ∞ := by
    apply hfin _ (isCompact_closedBall _ _)
    refine Subset.trans (closedBall_subset_closedBall ?_) (hδ₀W.trans hWU)
    simp only [Nat.cast_zero, zero_add, div_one]
    linarith
  have hT : Tendsto (fun m : ℕ => A * R.measure (closedBall y (t + δ₀ / ((m : ℝ) + 1)))) atTop
      (𝓝 (A * R.measure (closedBall y t))) := by
    have h := tendsto_measure_iInter_atTop (μ := R.measure)
      (fun m => measurableSet_closedBall.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rw [hinter] at h
    exact ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top)
  -- fix `δ = δ₀/(m+1)` with `b = A μ(B_{t+δ}(y)) < c < ωₙ`
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds hlt)).exists
  set δ : ℝ := δ₀ / ((m : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  have hδδ₀ : δ ≤ δ₀ := div_le_self hδ₀.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  obtain ⟨c, hbc, hcω⟩ := exists_between hm
  -- `y ∈ spt μ`, so `B_δ(y)` has positive measure and contains a point `x` with a tangent space
  have hpos : R.measure (ball y δ) ≠ 0 :=
    ((Measure.mem_support_iff_forall y).1 hy _ (ball_mem_nhds y hδ)).ne'
  obtain ⟨x, hx, Q, hQ⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hgood)
  -- `B_t(x) ⊆ B_{t+δ}(y) ⊆ W`
  have hxy : dist x y < δ := mem_ball.1 hx
  have hBx : closedBall x t ⊆ closedBall y (t + δ) := closedBall_subset_closedBall' (by linarith)
  have hBxW : closedBall x t ⊆ W :=
    hBx.trans ((closedBall_subset_closedBall (by linarith)).trans hδ₀W)
  -- the tangent lower density at `x`: `c σⁿ ≤ Hⁿ(M ∩ B_σ(x))` for some `0 < σ < t`
  obtain ⟨σ, hσc, hσ0, hσt⟩ :=
    ((Submission.doragm_approxTangent_lower_density P n R.carrier x Q hn hQ c hcω).and
      (Ioo_mem_nhdsGT ht)).exists
  have hσn : 0 < σ ^ n := pow_pos hσ0 n
  have hcoef : ENNReal.ofReal (1 / σ ^ n) ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) :=
    ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (Real.one_le_exp (mul_nonneg hκ hσ0.le)) hσn.le)
  have hone : ENNReal.ofReal (1 / σ ^ n) * ENNReal.ofReal (σ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hσn.ne', ENNReal.ofReal_one]
  -- `c ≤ f_x(σ) ≤ f_x(t) ≤ b < c`
  have key : c ≤ A * R.measure (closedBall y (t + δ)) :=
    calc c = ENNReal.ofReal (1 / σ ^ n) * (c * ENNReal.ofReal (σ ^ n)) := by
          rw [mul_comm c, ← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * μHE[n] (R.carrier ∩ closedBall x σ) :=
          mul_le_mul' hcoef hσc
      _ ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (closedBall x σ) :=
          mul_le_mul' le_rfl (hHμ _ measurableSet_closedBall)
      _ ≤ A * R.measure (closedBall x t) := hmono x σ t hσ0 hσt hBxW
      _ ≤ A * R.measure (closedBall y (t + δ)) := mul_le_mul' le_rfl (measure_mono hBx)
  exact absurd (key.trans_lt hbc) (lt_irrefl c)
/-- **The approximate tangent projection is `μ_V`-measurable** (Simon Ch. 3, 1.4 and 1.5(1);
Ch. 6, 3.1).  For `R = (M, θ, ξ)` with weight `μ_V = θ Hⁿ⌞M`, `x ↦ p_{TₓM}` is `μ_V`-a.e. strongly
measurable.  Since `μ_V ≪ Hⁿ⌞M`, it suffices to prove this for `Hⁿ⌞M`.  By uniqueness of
approximate tangent planes, `TₓM` is `Hⁿ⌞M`-a.e. the plane oriented by `ξ(x)`.  A unit simple
`n`-vector `ζ = ±τ₁ ∧ ⋯ ∧ τₙ` determines its plane: if also `ζ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` and
`y ⊥ span τ'`, the `n`-covector `α(u) = det(⟨cₖ, uⱼ⟩)`, where `c` is `τ` with `τᵢ` replaced by `y`,
gives `±⟨y, τᵢ⟩ = ±α(τ) = ζ(α) = ±α(τ') = 0`, so `τᵢ ∈ span τ'`.  Hence `p_{TₓM} = G(ξ(x))` a.e.,
where `G(ζ)` is the projection onto the plane of `ζ` (`0` if there is none).  `G` is Borel:
`Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` is continuous on the compact set `Ω` of orthonormal frames and signs, and
`G(Φ(τ, s)) = Σₖ ⟨τₖ, ·⟩ τₖ` is continuous, so for closed `t`,
`G⁻¹(t) = Φ(Ω ∩ (G ∘ Φ)⁻¹(t)) ∪ (Φ(Ω)ᶜ ∩ {0 ∈ t})` is Borel. -/
theorem Submission.dorag_approxTangent_starProjection_aesm : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n U R
  classical
  -- `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`, so it suffices to prove measurability for `Hⁿ⌞M`
  refine AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (μHE[n].restrict R.carrier) fun x => (R.mult x : ℝ≥0∞)) ?_
  -- `ev τ = (α ↦ α(τ₁, …, τₙ))`, a continuous alternating map of `τ`
  let ev : Euclid P [⋀^Fin n]→L[ℝ] MultiVector P n :=
    (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
  have hev : ∀ (τ : Fin n → Euclid P) (α : Covector (Euclid P) n), ev τ α = α τ :=
    fun τ α => rfl
  -- `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` on the compact set `Ω` of orthonormal frames and signs `s = ±1`
  let Φ : (Fin n → Euclid P) × ℝ → MultiVector P n := fun ω => ω.2 • ev ω.1
  have hΦc : Continuous Φ := continuous_snd.smul (ev.coe_continuous.comp continuous_fst)
  let Ω : Set ((Fin n → Euclid P) × ℝ) := {τ | Orthonormal ℝ τ} ×ˢ {1, -1}
  have hΩ : IsCompact Ω := by
    refine IsCompact.prod (isCompact_of_isClosed_isBounded ?_ ?_) (Set.toFinite _).isCompact
    · have hset : {τ : Fin n → Euclid P | Orthonormal ℝ τ} =
          ⋂ i, ⋂ j, {τ | inner ℝ (τ i) (τ j) = if i = j then (1 : ℝ) else 0} := by
        ext τ
        simp [orthonormal_iff_ite]
      rw [hset]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
    · refine (isBounded_iff_subset_closedBall 0).mpr ⟨1, fun τ hτ => ?_⟩
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hτ.1 i).le
  -- `ζ` orients `Q` iff `ζ = Φ(τ, s)` for a point `(τ, s)` of `Ω` with `span τ = Q`
  have horient : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q ↔ ∃ ω ∈ Ω, Φ ω = ζ ∧ Submodule.span ℝ (range ω.1) = Q := by
    intro ζ Q
    constructor
    · rintro ⟨τ, hτ, hQ, h | h⟩
      · refine ⟨(τ, 1), ⟨hτ, Or.inl rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
      · refine ⟨(τ, -1), ⟨hτ, Or.inr rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
    · rintro ⟨⟨τ, s⟩, ⟨hτ, hs⟩, rfl, hQ⟩
      refine ⟨τ, hτ, hQ, ?_⟩
      rcases hs with rfl | rfl
      · left
        intro α
        simp [Φ, hev]
      · right
        intro α
        simp [Φ, hev]
  -- the `n`-covector `u ↦ det(⟨cₖ, uⱼ⟩)ₖⱼ`
  have hdet : ∀ c : Fin n → Euclid P, ∃ α : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, α u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
    intro c
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => (innerSL ℝ (c k)).toLinearMap
    let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hA : ∀ u : Fin n → Euclid P, A u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
      intro u
      rw [← Matrix.det_transpose]
      rfl
    have hAc : Continuous fun u : Fin n → Euclid P => A u := by
      simp only [hA]
      exact Continuous.matrix_det (continuous_matrix fun k j => by
        simp only [Matrix.of_apply]
        exact continuous_const.inner (continuous_apply j))
    exact ⟨{ A with cont := hAc }, hA⟩
  -- a unit simple `n`-vector determines its plane: if `ζ` orients `span τ` and `span τ'`, then
  -- each `τᵢ` is orthogonal to `(span τ')ᗮ`
  have hle : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q ≤ Q' := by
    rintro ζ Q Q' ⟨τ, hτ, rfl, hζ⟩ ⟨τ', hτ', rfl, hζ'⟩
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ')),
      Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨α, hα⟩ := hdet (Function.update τ i y)
    -- `α(τ)` is the determinant of the identity matrix with row `i` replaced by `(⟨y, τⱼ⟩)ⱼ`
    have h1 : α τ = inner ℝ y (τ i) := by
      rw [hα]
      have hM : (Matrix.of fun k j => inner ℝ (Function.update τ i y k) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => inner ℝ y (τ j)) := by
        ext k j
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk, Matrix.one_apply, orthonormal_iff_ite.mp hτ k j]
      rw [hM, ← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
        ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    -- row `i` of the matrix of `α(τ')` is `(⟨y, τ'ⱼ⟩)ⱼ = 0`
    have h2 : α τ' = 0 := by
      rw [hα]
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      simp only [Matrix.of_apply, Function.update_self]
      rw [real_inner_comm]
      exact hy _ (Submodule.subset_span ⟨j, rfl⟩)
    have h3 : ζ α = 0 := by
      rcases hζ' with h | h <;> simp [h, h2]
    rcases hζ with h | h
    · rw [← h1, ← h, h3]
    · have h4 := h α
      rw [h3] at h4
      rw [← h1]
      linarith
  have huniq : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q = Q' :=
    fun ζ Q Q' h h' => le_antisymm (hle ζ Q Q' h h') (hle ζ Q' Q h' h)
  -- the projection onto the span of an orthonormal frame `τ` is `Σₖ ⟨τₖ, ·⟩ τₖ`, continuous in `τ`
  let F : (Fin n → Euclid P) × ℝ → (Euclid P →L[ℝ] Euclid P) :=
    fun ω => ∑ k, (innerSL ℝ (ω.1 k)).smulRight (ω.1 k)
  have hFapply : ∀ ω v, F ω v = ∑ k, inner ℝ (ω.1 k) v • ω.1 k := by
    intro ω v
    simp [F]
  have hFc : Continuous F := by
    refine continuous_clm_apply.mpr fun v => ?_
    simp only [hFapply]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hFproj : ∀ ω ∈ Ω, (Submodule.span ℝ (range ω.1)).starProjection = F ω := by
    rintro ⟨τ, s⟩ ⟨hτ, -⟩
    refine ContinuousLinearMap.ext fun v => ?_
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hFapply]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨j, rfl⟩
        rw [hFapply, inner_sub_left, sum_inner]
        simp [inner_smul_left, orthonormal_iff_ite.mp hτ, real_inner_comm]
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx
        rw [inner_smul_right, hx, mul_zero]
  -- `G ζ` is the projection onto the plane oriented by `ζ` (`0` if there is none)
  let G : MultiVector P n → (Euclid P →L[ℝ] Euclid P) := fun ζ =>
    if h : ∃ Q, IsUnitOrientationOf ζ Q then h.choose.starProjection else 0
  have hGQ : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → G ζ = Q.starProjection := by
    intro ζ Q hQ
    have hex : ∃ Q, IsUnitOrientationOf ζ Q := ⟨Q, hQ⟩
    simp only [G, dite_eq_left hex]
    rw [huniq _ _ _ hex.choose_spec hQ]
  have hGΦ : ∀ ω ∈ Ω, G (Φ ω) = F ω := fun ω hω => by
    rw [hGQ _ _ ((horient _ _).mpr ⟨ω, hω, rfl, rfl⟩), hFproj ω hω]
  -- `G` is Borel: for closed `t`, `G⁻¹(t)` is the compact set `Φ(Ω ∩ F⁻¹(t))` together with the
  -- complement of the compact set `Φ(Ω)` (if `0 ∈ t`)
  have hG : Measurable G := by
    refine measurable_of_isClosed fun t ht => ?_
    have hset : G ⁻¹' t = Φ '' (Ω ∩ F ⁻¹' t) ∪
        ((Φ '' Ω)ᶜ ∩ {_ζ | (0 : Euclid P →L[ℝ] Euclid P) ∈ t}) := by
      ext ζ
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
        Set.mem_compl_iff]
      by_cases h : ∃ Q, IsUnitOrientationOf ζ Q
      · obtain ⟨Q, hQ⟩ := h
        obtain ⟨ω, hω, hΦω, -⟩ := (horient ζ Q).mp hQ
        have hGζ : G ζ = F ω := by
          rw [← hΦω]
          exact hGΦ ω hω
        constructor
        · intro hζt
          exact Or.inl ⟨ω, ⟨hω, by rwa [← hGζ]⟩, hΦω⟩
        · rintro (⟨ω', ⟨hω', hω't⟩, hΦω'⟩ | ⟨hn, -⟩)
          · rw [← hΦω', hGΦ ω' hω']
            exact hω't
          · exact absurd ⟨ω, hω, hΦω⟩ hn
      · have hGζ : G ζ = 0 := dite_eq_right h
        have hn : ¬∃ ω, ω ∈ Ω ∧ Φ ω = ζ := fun ⟨ω, hω, hΦω⟩ =>
          h ⟨_, (horient ζ _).mpr ⟨ω, hω, hΦω, rfl⟩⟩
        rw [hGζ]
        constructor
        · intro h0
          exact Or.inr ⟨hn, h0⟩
        · rintro (⟨ω', ⟨hω', -⟩, hΦω'⟩ | ⟨-, h0⟩)
          · exact absurd ⟨ω', hω', hΦω'⟩ hn
          · exact h0
    rw [hset]
    exact ((hΩ.inter_right (ht.preimage hFc)).image hΦc).isClosed.measurableSet.union
      ((hΩ.image hΦc).isClosed.measurableSet.compl.inter (MeasurableSet.const _))
  -- `Hⁿ⌞M`-a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes),
  -- so `p_{TₓM} = G(ξ(x))`
  have hae : (fun x => (approxTangentPlane n R.carrier x).starProjection)
      =ᵐ[μHE[n].restrict R.carrier] G ∘ R.orient := by
    filter_upwards [R.orients] with x ⟨Q, hQ, hor⟩
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    have h1 : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    rw [Function.comp_apply, hGQ _ _ hor, h1]
  -- `G ∘ ξ` is a.e. measurable, with values in the finite-dimensional space `End(ℝᴾ)`
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  exact ((hG.comp_aemeasurable R.aestronglyMeasurable_orient.aemeasurable).aestronglyMeasurable
    ).congr hae.symm

/-- **Monotonicity inequalities and the unit density lower bound** for bounded generalized mean
curvature (Simon Ch. 4, 3.16–3.17 with `‖H‖ ≤ κ`, and 4.10(1)).  Let `μ = θ Hⁿ⌞M` have generalized
mean curvature `H` in `W`, and let `F_y(x) = |p_x^⊥(x − y)|² / |x − y|^{n+2}`.
(1) The annular inequalities (M1) and (M2) are `Submission.doragm_annular_monotonicity` at
`P = n + k`.  The map `x ↦ p_x` is `μ`-measurable by
`Submission.dorag_approxTangent_starProjection_aesm`.
(2) Let `y ∈ spt μ`.  Since `κ ≥ ‖H 0‖ ≥ 0` and (M1) makes `ρ ↦ e^{κρ} ρ^{−n} μ(B_ρ(z))`
nondecreasing, `Submission.doragm_support_ball_ratio_ge` gives `e^{κs} s^{−n} μ(B_s(y)) ≥ ωₙ`.
With (M1) this yields `∫_{B_t(y) \ B_s(y)} F_y dμ + ωₙ ≤ e^{κt} t^{−n} μ(B_t(y))` for `0 < s < t`.
For `s = t/(m + 2)` the annuli increase to `B_t(y) \ {y}`, and `F_y(y) = 0`.  Monotone convergence
for the measure `F_y μ` therefore gives (D). -/
theorem Submission.dorag_monotonicity_density : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → (∀ (y : Euclid (n + k)) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) ∧ ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * R.measure (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) ∧ ∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
  intro n k hn U W R H κ hW hWU hH hHκ hFV
  -- (1) is the annular monotonicity, with `x ↦ p_x` measurable by the sibling lemma
  have hann := Submission.doragm_annular_monotonicity (n + k) n U W R H κ hW hWU
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hH hHκ hFV
  refine ⟨hann, fun y hy t ht hyt => ?_⟩
  -- `κ ≥ ‖H 0‖ ≥ 0`, and dropping the annular term of (M1) makes `ρ ↦ e^{κρ} ρ^{-n} μ(B_ρ(z))`
  -- nondecreasing, so this ratio is at least `ωₙ` at the support point `y`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hratio := Submission.doragm_support_ball_ratio_ge (n + k) n U W R κ hn hW hWU hκ
    (fun z s t hs hst hzt => le_add_self.trans (hann z s t hs hst hzt).1) y hy
  -- the integrand `F_y`, which vanishes at `y` because `‖0‖ ^ (n + 2) = 0`
  set F : Euclid (n + k) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
      ‖x - y‖ ^ (n + 2)) with hF
  have hFy : F y = 0 := by simp [hF]
  -- for `0 < s < t`: `∫_{B_t(y) \ B_s(y)} F_y dμ + ωₙ ≤ e^{κt} t^{-n} μ(B_t(y))`
  have hannulus : ∀ s, 0 < s → s < t →
      (∫⁻ x in closedBall y t \ closedBall y s, F x ∂R.measure) + unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
    fun s hs hst => (add_le_add le_rfl
      (hratio s hs ((closedBall_subset_closedBall hst.le).trans hyt))).trans
        (hann y s t hs hst hyt).1
  -- the annuli `B_t(y) \ B_{t/(m+2)}(y)` increase and cover `B_t(y) \ {y}`
  let A : ℕ → Set (Euclid (n + k)) := fun m => closedBall y t \ closedBall y (t / (m + 2))
  have hA : Monotone A := fun m m' hmm' => Set.sdiff_subset_sdiff_right
    (closedBall_subset_closedBall (div_le_div_of_nonneg_left ht.le (by positivity) (by gcongr)))
  have hcover : closedBall y t ⊆ (⋃ m, A m) ∪ {y} := by
    intro x hx
    by_cases hxy : x = y
    · exact Or.inr hxy
    have hd : 0 < dist x y := dist_pos.mpr hxy
    obtain ⟨m, hm⟩ := exists_nat_gt (t / dist x y)
    refine Or.inl (mem_iUnion.mpr ⟨m, hx, fun hxm => ?_⟩)
    rw [mem_closedBall, le_div_iff₀ (by positivity)] at hxm
    rw [div_lt_iff₀ hd] at hm
    nlinarith
  -- monotone convergence for the measure `F_y μ`
  have hν : ∀ s, MeasurableSet s → R.measure.withDensity F s = ∫⁻ x in s, F x ∂R.measure :=
    fun s hs => withDensity_apply F hs
  calc (∫⁻ x in closedBall y t, F x ∂R.measure) + unitBallVolume n
      = R.measure.withDensity F (closedBall y t) + unitBallVolume n := by
        rw [hν _ measurableSet_closedBall]
    _ ≤ (⨆ m, R.measure.withDensity F (A m)) + unitBallVolume n := by
        refine add_le_add ?_ le_rfl
        calc R.measure.withDensity F (closedBall y t)
            ≤ R.measure.withDensity F ((⋃ m, A m) ∪ {y}) := measure_mono hcover
          _ ≤ R.measure.withDensity F (⋃ m, A m) + R.measure.withDensity F {y} :=
            measure_union_le _ _
          _ = ⨆ m, R.measure.withDensity F (A m) := by
            rw [hA.measure_iUnion, hν _ (measurableSet_singleton y), lintegral_singleton, hFy,
              zero_mul, add_zero]
    _ = ⨆ m, (R.measure.withDensity F (A m) + unitBallVolume n) := ENNReal.iSup_add _
    _ ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
        refine iSup_le fun m => ?_
        have hm : (1 : ℝ) < m + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
        rw [hν (A m) (measurableSet_closedBall.diff measurableSet_closedBall)]
        exact hannulus _ (div_pos ht (by linarith)) (div_lt_self ht hm)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
