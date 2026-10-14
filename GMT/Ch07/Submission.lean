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

set_option maxHeartbeats 1000000 in
/-- **Campanato's `C^{1,α}` estimate for `Δw = div F`** (the Schauder theory invoked in Simon's
proof of Ch. 5, 7.1; Giaquinta–Martinazzi 2012, §§5.1–5.4).  Harmonic replacement in `B_ρ(x)` and
harmonic decay give the comparison inequalities for `Φ(x,r) = ∫_{B_r(x)} |Dw - (Dw)_{x,r}|²` and
`Ψ(x,r) = ∫_{B_r(x)} |Dw|²` (Hilbert–Schmidt norms); a Caccioppoli estimate with the test map `η²w`
bounds `Ψ(x, R/8)`; the iteration lemma gives `Ψ ≲ r^{m-α}`, then `Φ ≲ r^{m+α}`, so `Dw` is
`α/2`-Hölder and bounded on `B_{3R/8}(x₀)`; a second Campanato pass gives `Φ ≲ r^{m+2α}`, and
Campanato's criterion yields the `α`-Hölder bound on `B_{R/4}(x₀)`.  As elaborated, (H_F) reads
`∫|F - c|² ≤ ε₁ ∫_{B_ρ(x)} (|Dw - (Dw)_{x,ρ}|² + Kρ^{2α} ∫_{B_ρ(x)} (|Dw|² + Kρ^{m+2α}))` (the
set-integral notation absorbs the trailing sums); for `ρ ≤ R/8` this still gives the comparison
inequality, with a constant depending on `K` and `R`. -/
theorem Submission.codim1_hcp_sr_c1alpha_estimate : ∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α < 1 → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K R : ℝ, 0 ≤ K → 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k) (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) → ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) → (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) → (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R → ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤ ε₁ * ∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2 + K * ρ ^ (2 * α) * ∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2 + K * ρ ^ ((m : ℝ) + 2 * α)) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := by
  have hrepl := Submission.codim1_hcp_sr_harmonic_replacement
  have hdecay := Submission.codim1_hcp_sr_harmonic_decay
  have hcamp := Submission.codim1_hcp_sr_campanato_lemmas
  intro m k α hm hα0 hα1
  obtain ⟨hcampI, hcampII⟩ := hcamp
  obtain ⟨Cd, hCd, hdec⟩ := hdecay m k hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have amgm : ∀ p q : ℝ, p * q ≤ p ^ 2 / 2 + q ^ 2 / 2 := fun p q => by
    have h := sq_nonneg (p - q)
    rw [sub_sq] at h
    linarith
  -- the squared Hilbert–Schmidt norm `|A|² = Σⱼ |A eⱼ|²`
  obtain ⟨hs, hs_def⟩ : ∃ hs : (Euclid m →L[ℝ] Euclid k) → ℝ, ∀ A,
      hs A = ∑ j : Fin m, ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hs_nonneg : ∀ A, 0 ≤ hs A := fun A => by rw [hs_def]; positivity
  have hs_cont : Continuous hs := by
    have : hs = fun A => ∑ j : Fin m, ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := funext hs_def
    rw [this]; fun_prop
  have hs_le : ∀ A, hs A ≤ m * ‖A‖ ^ 2 := by
    intro A
    rw [hs_def]
    calc ∑ j : Fin m, ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ ∑ _j : Fin m, ‖A‖ ^ 2 := by
          gcongr with j
          calc ‖A (EuclideanSpace.single j (1 : ℝ))‖
              ≤ ‖A‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = m * ‖A‖ ^ 2 := by simp
  have hs_add : ∀ A B, hs (A + B) ≤ 2 * hs A + 2 * hs B := by
    intro A B
    simp only [hs_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    gcongr with j
    rw [add_apply]
    have h1 := norm_add_le (A (EuclideanSpace.single j (1 : ℝ))) (B (EuclideanSpace.single j (1 : ℝ)))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := sq_nonneg (‖A (EuclideanSpace.single j (1 : ℝ))‖ - ‖B (EuclideanSpace.single j (1 : ℝ))‖)
    rw [add_sq] at h2
    rw [sub_sq] at h3
    linarith
  have hs_sub_comm : ∀ A B, hs (A - B) = hs (B - A) := by
    intro A B
    simp only [hs_def, sub_apply, norm_sub_rev]
  -- `|A|_op² ≤ c_N |A|²` (equivalence of norms on `L(ℝᵐ, ℝᵏ)`)
  obtain ⟨cN, hcN0, hN1⟩ : ∃ cN : ℝ, 0 ≤ cN ∧ ∀ A : Euclid m →L[ℝ] Euclid k, ‖A‖ ^ 2 ≤ cN * hs A := by
    let v := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    refine ⟨(Fintype.card (Fin m) • ‖(v.equivFunL : Euclid m →L[ℝ] (Fin m → ℝ))‖) ^ 2,
      by positivity, fun A => ?_⟩
    have h1 : ∀ i, ‖A (v i)‖ ≤ Real.sqrt (hs A) := by
      intro i
      apply Real.le_sqrt_of_sq_le
      rw [hs_def]
      have hv : v i = EuclideanSpace.single i (1 : ℝ) := by
        simp [v, EuclideanSpace.basisFun_apply]
      rw [hv]
      exact Finset.single_le_sum (f := fun j => ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have h2 := v.opNorm_le (Real.sqrt_nonneg _) h1
    calc ‖A‖ ^ 2 ≤ (Fintype.card (Fin m) • ‖(v.equivFunL : Euclid m →L[ℝ] (Fin m → ℝ))‖
          * Real.sqrt (hs A)) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt (hs_nonneg A)]
  -- `|B_r(x)| = ω rᵐ`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, ω = (volume (ball (0 : Euclid m) 1)).toReal := ⟨_, rfl⟩
  have hω_pos : 0 < ω := by
    rw [hω_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hvol : ∀ (x : Euclid m) (r : ℝ), 0 < r → volume.real (ball x r) = ω * r ^ m := by
    intro x r hr
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hω_def, mul_comm]
  have hvolpos : ∀ (x : Euclid m) (r : ℝ), 0 < r → 0 < volume.real (ball x r) := fun x r hr => by
    rw [hvol x r hr]; positivity
  -- the mean minimizes `c ↦ ∫_S |f - c|²`
  have hMP : ∀ (S : Set (Euclid m)) (f : Euclid m → (Euclid m →L[ℝ] Euclid k))
      (c : Euclid m →L[ℝ] Euclid k), MeasurableSet S → volume S ≠ ∞ → 0 < volume.real S →
      IntegrableOn f S → IntegrableOn (fun z => hs (f z)) S →
      ∫ z in S, hs (f z - ⨍ z' in S, f z') ≤ ∫ z in S, hs (f z - c) := by
    intro S f c hS hSfin hSpos hf hf2
    set a := ⨍ z' in S, f z' with ha
    set d := a - c with hd
    let Λ : (Euclid m →L[ℝ] Euclid k) →L[ℝ] ℝ := ∑ j : Fin m,
      (innerSL ℝ (d (EuclideanSpace.single j (1 : ℝ)))).comp
        (ContinuousLinearMap.apply ℝ (Euclid k) (EuclideanSpace.single j (1 : ℝ)))
    have hΛ : ∀ A, Λ A = ∑ j : Fin m,
        inner ℝ (d (EuclideanSpace.single j (1 : ℝ))) (A (EuclideanSpace.single j (1 : ℝ))) := by
      intro A
      simp [Λ, sum_apply, innerSL_apply_apply]
    have hpt : ∀ z, hs (f z - c) = hs (f z - a) + 2 * Λ (f z - a) + hs d := by
      intro z
      simp only [hs_def, hΛ, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (f z - c) (EuclideanSpace.single j (1 : ℝ)) =
          (f z - a) (EuclideanSpace.single j (1 : ℝ)) + d (EuclideanSpace.single j (1 : ℝ)) := by
        simp only [hd, sub_apply]; abel
      rw [this, norm_add_sq_real, real_inner_comm]
    have hmeas : AEStronglyMeasurable (fun z => f z - a) (volume.restrict S) :=
      hf.aestronglyMeasurable.sub aestronglyMeasurable_const
    have hfa_int : IntegrableOn (fun z => f z - a) S := hf.sub (integrableOn_const hSfin)
    have hfa2 : IntegrableOn (fun z => hs (f z - a)) S := by
      refine Integrable.mono' ((hf2.const_mul 2).add (integrableOn_const hSfin (C := 2 * hs (-a))))
        (hs_cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg (hs_nonneg _), sub_eq_add_neg]
      exact hs_add _ _
    have hΛint : IntegrableOn (fun z => Λ (f z - a)) S := Λ.integrable_comp hfa_int
    have hΛ0 : ∫ z in S, Λ (f z - a) = 0 := by
      rw [Λ.integral_comp_comm hfa_int, integral_sub hf (integrableOn_const hSfin), setIntegral_const,
        ha, setAverage_eq, smul_inv_smul₀ hSpos.ne', sub_self, map_zero]
    calc ∫ z in S, hs (f z - a) ≤ (∫ z in S, hs (f z - a)) + 2 * (∫ z in S, Λ (f z - a))
          + volume.real S * hs d := by
          rw [hΛ0, mul_zero, add_zero]
          exact le_add_of_nonneg_right (mul_nonneg hSpos.le (hs_nonneg d))
      _ = ∫ z in S, hs (f z - c) := by
          have e1 : ∫ z in S, hs (f z - c) = ∫ z in S, (hs (f z - a) + 2 * Λ (f z - a) + hs d) :=
            integral_congr_ae (ae_of_all _ fun z => hpt z)
          have e2 : ∫ z in S, (hs (f z - a) + 2 * Λ (f z - a) + hs d) =
              (∫ z in S, (hs (f z - a) + 2 * Λ (f z - a))) + ∫ _z in S, hs d :=
            integral_add (hfa2.add (hΛint.const_mul 2)) (integrableOn_const hSfin)
          have e3 : ∫ z in S, (hs (f z - a) + 2 * Λ (f z - a)) =
              (∫ z in S, hs (f z - a)) + ∫ z in S, 2 * Λ (f z - a) :=
            integral_add hfa2 (hΛint.const_mul 2)
          rw [e1, e2, e3, integral_const_mul, setIntegral_const, smul_eq_mul]
  -- a fixed cutoff profile `η₀ ∈ C_c^∞(B₁(0))`, `η₀ = 1` on `B_{1/2}(0)`, `|Dη₀| ≤ M₀`
  obtain ⟨η₀, hη₀in, hη₀out⟩ : ∃ η₀ : ContDiffBump (0 : Euclid m), η₀.rIn = 1 / 2 ∧ η₀.rOut = 1 :=
    ⟨⟨1 / 2, 1, by norm_num, by norm_num⟩, rfl, rfl⟩
  obtain ⟨M₀, hM₀⟩ := ((η₀.contDiff (n := 1)).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (η₀.hasCompactSupport.fderiv ℝ)
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  -- the constants of the iteration lemmas
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = (4 * Cd + 2) * m * (cN + 1) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hA₁e : A₁ = (4 * Cd + 2) * m * cN + (4 * Cd + 2) * m := by rw [hA₁]; ring
  have hA₁m : 0 ≤ (4 * Cd + 2) * (m : ℝ) * cN := by positivity
  have hA₁a : 4 * Cd ≤ A₁ := by
    have h1 : (4 * Cd + 2) * 1 ≤ (4 * Cd + 2) * m :=
      mul_le_mul_of_nonneg_left hmR (by positivity)
    linarith
  have hA₁b : (4 * Cd + 2) * m * cN ≤ A₁ := by
    have : 0 ≤ (4 * Cd + 2) * (m : ℝ) := by positivity
    linarith
  have hA₁c : (4 * Cd + 2) * m ≤ A₁ := by linarith
  obtain ⟨εa, ca, hεa, hca, hIa⟩ := hcampI A₁ m (m - α) hA₁0 (by linarith) (by linarith)
  obtain ⟨εb, cb, hεb, hcb, hIb⟩ := hcampI A₁ (m + 2) (m + α) hA₁0 (by linarith) (by linarith)
  obtain ⟨εc, cc, hεc, hcc, hIc⟩ := hcampI A₁ (m + 2) (m + 2 * α) hA₁0 (by linarith) (by linarith)
  obtain ⟨C₀', hC₀', hII'⟩ := hcampII m k (α / 2) hm (by linarith) (by linarith)
  obtain ⟨C₀'', hC₀'', hII''⟩ := hcampII m k α hm hα0 hα1.le
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ,
      ε₁ = min (min 1 (εa / 2)) (min (min εb εc) (1 / (24 * m * (cN + 1)))) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by
    rw [hε₁]
    exact lt_min (lt_min one_pos (by linarith)) (lt_min (lt_min hεb hεc) (by positivity))
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₁a : ε₁ ≤ εa / 2 := by rw [hε₁]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε₁b : ε₁ ≤ εb := by
    rw [hε₁]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε₁c : ε₁ ≤ εc := by
    rw [hε₁]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε₁m : ε₁ ≤ 1 / (24 * m * (cN + 1)) := by
    rw [hε₁]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hε₁sq' : ε₁ ^ 2 ≤ ε₁ := by rw [sq]; exact mul_le_of_le_one_right hε₁0.le hε₁1
  have hε₁sq : 2 * ε₁ ^ 2 ≤ εa := by linarith
  have hε₁cacc : 6 * m * cN * ε₁ ^ 2 ≤ 1 / 4 := by
    have h1 : ε₁ * (24 * m * (cN + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hε₁m; linarith
    have h3 : 6 * m * cN * ε₁ ^ 2 ≤ 6 * m * cN * ε₁ :=
      mul_le_mul_of_nonneg_left hε₁sq' (by positivity)
    have h4 : 0 ≤ 6 * (m : ℝ) * ε₁ := by positivity
    have e : (6 * m * (cN + 1) * ε₁ : ℝ) = 6 * m * cN * ε₁ + 6 * m * ε₁ := by ring
    have e2 : (6 * m * (cN + 1) * ε₁ : ℝ) = (ε₁ * (24 * m * (cN + 1))) / 4 := by ring
    linarith
  refine ⟨ε₁, hε₁0, ?_⟩
  intro K R hK hR
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = R / 8 := ⟨_, rfl⟩
  have hR₁0 : 0 < R₁ := by rw [hR₁]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ,
      K₁ = ω * K * R₁ ^ m * cN + ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  obtain ⟨Ccacc, hCcacc⟩ : ∃ Ccacc : ℝ,
      Ccacc = 2 * (6 * m * K ^ 2 + 17 * m * (M₀ * (R / 4)⁻¹) ^ 2 * K ^ 2) * (ω * (R / 4) ^ m) :=
    ⟨_, rfl⟩
  obtain ⟨B₃, hB₃⟩ : ∃ B₃ : ℝ, B₃ = 2 * A₁ * K ^ 2 * ω * R₁ ^ α := ⟨_, rfl⟩
  have hB₃0 : 0 ≤ B₃ := by rw [hB₃]; positivity
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = ca * (Ccacc / R₁ ^ ((m : ℝ) - α) + B₃) := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃, hCcacc]; positivity
  obtain ⟨B₅, hB₅⟩ : ∃ B₅ : ℝ, B₅ = A₁ * K₁ * (C₃ + R₁ ^ α) := ⟨_, rfl⟩
  have hB₅0 : 0 ≤ B₅ := by rw [hB₅]; positivity
  obtain ⟨C₅, hC₅⟩ : ∃ C₅ : ℝ,
      C₅ = cb * (C₃ * R₁ ^ ((m : ℝ) - α) / R₁ ^ ((m : ℝ) + α) + B₅) := ⟨_, rfl⟩
  have hC₅0 : 0 ≤ C₅ := by rw [hC₅]; positivity
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = C₀' * Real.sqrt (cN * C₅) * (R / 16) ^ (α / 2) := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  obtain ⟨C₆, hC₆⟩ : ∃ C₆ : ℝ,
      C₆ = 2 * H ^ 2 + 2 * cN * C₃ * (R / 16) ^ ((m : ℝ) - α) / (ω * (R / 16) ^ m) := ⟨_, rfl⟩
  have hC₆0 : 0 ≤ C₆ := by rw [hC₆]; positivity
  obtain ⟨B₈, hB₈⟩ : ∃ B₈ : ℝ, B₈ = A₁ * K₁ * (m * C₆ * ω + 1) := ⟨_, rfl⟩
  have hB₈0 : 0 ≤ B₈ := by rw [hB₈]; positivity
  obtain ⟨C₈, hC₈⟩ : ∃ C₈ : ℝ,
      C₈ = cc * (m * C₆ * ω * R₁ ^ m / R₁ ^ ((m : ℝ) + 2 * α) + B₈) := ⟨_, rfl⟩
  have hC₈0 : 0 ≤ C₈ := by rw [hC₈]; positivity
  refine ⟨max (Real.sqrt C₆) (max (C₀'' * Real.sqrt (cN * C₈)) (2 * Real.sqrt C₆ * (16 / R) ^ α)),
    le_max_of_le_left (Real.sqrt_nonneg _), ?_⟩
  intro x₀ w F hw hF hwK hFK hHF hweak
  have hDw : ContinuousOn (fderiv ℝ w) (ball x₀ R) := hw.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Euclid m → ℝ → ℝ, ∀ x r,
      Ψ x r = ∫ z in ball x r, hs (fderiv ℝ w z) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid m → ℝ → ℝ, ∀ x r,
      Φ x r = ∫ z in ball x r, hs (fderiv ℝ w z - ⨍ z' in ball x r, fderiv ℝ w z') :=
    ⟨_, fun _ _ => rfl⟩
  -- `|F|² ≤ 2ε₁² c_N |Dw|² + 2K²`
  have hF2 : ∀ z ∈ ball x₀ R, ‖F z‖ ^ 2 ≤ 2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2 := by
    intro z hz
    have h1 : ‖F z‖ ^ 2 ≤ (ε₁ * ‖fderiv ℝ w z‖ + K) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hFK z hz) 2
    have h2 : ε₁ ^ 2 * ‖fderiv ℝ w z‖ ^ 2 ≤ ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) :=
      mul_le_mul_of_nonneg_left (hN1 _) (sq_nonneg _)
    have h3 := amgm (ε₁ * ‖fderiv ℝ w z‖) K
    have h4 : (ε₁ * ‖fderiv ℝ w z‖ + K) ^ 2 =
        ε₁ ^ 2 * ‖fderiv ℝ w z‖ ^ 2 + 2 * ((ε₁ * ‖fderiv ℝ w z‖) * K) + K ^ 2 := by ring
    have h5 : (ε₁ * ‖fderiv ℝ w z‖) ^ 2 = ε₁ ^ 2 * ‖fderiv ℝ w z‖ ^ 2 := by ring
    linarith
  -- integrability on balls `B_r(x)` with `B̄_r(x) ⊆ B_R(x₀)`
  have hgood : ∀ (x : Euclid m) (r : ℝ), closedBall x r ⊆ ball x₀ R →
      IntegrableOn (fderiv ℝ w) (ball x r) ∧
      (∀ c, IntegrableOn (fun z => hs (fderiv ℝ w z - c)) (ball x r)) ∧
      IntegrableOn (fun z => hs (fderiv ℝ w z)) (ball x r) := by
    intro x r hxr
    have hc : ContinuousOn (fderiv ℝ w) (closedBall x r) := hDw.mono hxr
    exact ⟨(hc.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall,
      fun c => ((hs_cont.comp_continuousOn (hc.sub continuousOn_const)).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall,
      ((hs_cont.comp_continuousOn hc).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall⟩
  have hΨ0 : ∀ x r, 0 ≤ Ψ x r := fun x r => by
    rw [hΨ]; exact setIntegral_nonneg measurableSet_ball fun z _ => hs_nonneg _
  have hΦ0 : ∀ x r, 0 ≤ Φ x r := fun x r => by
    rw [hΦ]; exact setIntegral_nonneg measurableSet_ball fun z _ => hs_nonneg _
  have hΦΨ : ∀ x r, 0 < r → closedBall x r ⊆ ball x₀ R → Φ x r ≤ Ψ x r := by
    intro x r hr hxr
    obtain ⟨h1, -, h3⟩ := hgood x r hxr
    rw [hΦ, hΨ]
    calc _ ≤ ∫ z in ball x r, hs (fderiv ℝ w z - 0) :=
          hMP _ _ 0 measurableSet_ball measure_ball_lt_top.ne (hvolpos x r hr) h1 h3
      _ = _ := by simp_rw [sub_zero]
  have hΨmono : ∀ x r ρ, r ≤ ρ → closedBall x ρ ⊆ ball x₀ R → Ψ x r ≤ Ψ x ρ := by
    intro x r ρ hrρ hxρ
    rw [hΨ, hΨ]
    exact setIntegral_mono_set (hgood x ρ hxρ).2.2 (ae_of_all _ fun z => hs_nonneg _)
      (ball_subset_ball hrρ).eventuallyLE
  have hΦmono : ∀ x r ρ, 0 < r → r ≤ ρ → closedBall x ρ ⊆ ball x₀ R → Φ x r ≤ Φ x ρ := by
    intro x r ρ hr hrρ hxρ
    have hxr : closedBall x r ⊆ ball x₀ R := (closedBall_subset_closedBall hrρ).trans hxρ
    obtain ⟨h1, -, h3⟩ := hgood x r hxr
    rw [hΦ, hΦ]
    calc _ ≤ ∫ z in ball x r, hs (fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z') :=
          hMP _ _ _ measurableSet_ball measure_ball_lt_top.ne (hvolpos x r hr) h1 h3
      _ ≤ _ := setIntegral_mono_set ((hgood x ρ hxρ).2.1 _) (ae_of_all _ fun z => hs_nonneg _)
          (ball_subset_ball hrρ).eventuallyLE
  have hΦop : ∀ x r, closedBall x r ⊆ ball x₀ R →
      ∫ z in ball x r, ‖fderiv ℝ w z - ⨍ z' in ball x r, fderiv ℝ w z'‖ ^ 2 ≤ cN * Φ x r := by
    intro x r hxr
    have hc : ContinuousOn (fderiv ℝ w) (closedBall x r) := hDw.mono hxr
    rw [hΦ, ← integral_const_mul]
    exact setIntegral_mono_on
      ((((hc.sub continuousOn_const).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall)
      (((hgood x r hxr).2.1 _).const_mul cN) measurableSet_ball (fun z _ => hN1 _)
  have hΨop : ∀ x r, closedBall x r ⊆ ball x₀ R →
      ∫ z in ball x r, ‖fderiv ℝ w z‖ ^ 2 ≤ cN * Ψ x r := by
    intro x r hxr
    have hc : ContinuousOn (fderiv ℝ w) (closedBall x r) := hDw.mono hxr
    rw [hΨ, ← integral_const_mul]
    exact setIntegral_mono_on
      (((hc.norm.pow 2).integrableOn_compact (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall)
      ((hgood x r hxr).2.2.const_mul cN) measurableSet_ball (fun z _ => hN1 _)
  -- Caccioppoli: `Ψ(x, R/8) ≤ C_cacc` for `x ∈ B_{R/2}(x₀)`
  have hcacc : ∀ x ∈ ball x₀ (R / 2), Ψ x R₁ ≤ Ccacc := by
    intro x hx
    rw [hΨ, hR₁, hCcacc]
    obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = R / 4 := ⟨_, rfl⟩
    rw [← hρ_def]
    have hρ : 0 < ρ := by rw [hρ_def]; positivity
    have hxd : dist x x₀ < R / 2 := hx
    have hcl : closedBall x ρ ⊆ ball x₀ R := closedBall_subset_ball' (by rw [hρ_def]; linarith)
    have hbx : ball x ρ ⊆ ball x₀ R := ball_subset_closedBall.trans hcl
    -- the cutoff `η(y) = η₀((y - x)/ρ)`
    obtain ⟨η, hη_def⟩ : ∃ η : Euclid m → ℝ, η = fun y => η₀ (ρ⁻¹ • (y - x)) := ⟨_, rfl⟩
    have hη_cd : ContDiff ℝ 1 η := by
      rw [hη_def]
      exact (η₀.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)
    have hη01 : ∀ y, 0 ≤ η y ∧ η y ≤ 1 := fun y => by rw [hη_def]; exact ⟨η₀.nonneg, η₀.le_one⟩
    have hη1 : ∀ y ∈ ball x (R / 8), η y = 1 := by
      intro y hy
      rw [hη_def]
      apply η₀.one_of_mem_closedBall
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),
        hη₀in, inv_mul_le_iff₀ hρ, hρ_def]
      linarith
    have hη0 : ∀ y, y ∉ ball x ρ → η y = 0 := by
      intro y hy
      rw [hη_def]
      apply η₀.zero_of_le_dist
      rw [mem_ball, dist_eq_norm, not_lt] at hy
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le), hη₀out,
        le_inv_mul_iff₀ hρ]
      linarith
    have hDη : ∀ y, ‖fderiv ℝ η y‖ ≤ M₀ * ρ⁻¹ := by
      intro y
      have hA : HasFDerivAt (fun y : Euclid m => ρ⁻¹ • (y - x))
          (ρ⁻¹ • ContinuousLinearMap.id ℝ (Euclid m)) y :=
        ((hasFDerivAt_id y).sub_const x).const_smul ρ⁻¹
      have hB : HasFDerivAt (η₀ : Euclid m → ℝ) (fderiv ℝ η₀ (ρ⁻¹ • (y - x))) (ρ⁻¹ • (y - x)) :=
        ((η₀.contDiff (n := 1)).differentiable (by norm_num) _).hasFDerivAt
      have hC := hB.comp y hA
      rw [hη_def]
      rw [show (fun y => η₀ (ρ⁻¹ • (y - x))) =
        (η₀ : Euclid m → ℝ) ∘ (fun y : Euclid m => ρ⁻¹ • (y - x)) from rfl, hC.fderiv]
      calc ‖(fderiv ℝ η₀ (ρ⁻¹ • (y - x))).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ (Euclid m))‖
          ≤ ‖fderiv ℝ η₀ (ρ⁻¹ • (y - x))‖ * ‖ρ⁻¹ • ContinuousLinearMap.id ℝ (Euclid m)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M₀ * ρ⁻¹ := by
            gcongr
            · exact hM₀ _
            · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
              calc ρ⁻¹ * ‖ContinuousLinearMap.id ℝ (Euclid m)‖ ≤ ρ⁻¹ * 1 := by
                    gcongr; exact ContinuousLinearMap.norm_id_le
                _ = ρ⁻¹ := mul_one _
    -- the test map `ζ = η² w`
    obtain ⟨ζ, hζ_def⟩ : ∃ ζ : Euclid m → Euclid k, ζ = fun y => (η y * η y) • w y := ⟨_, rfl⟩
    have hζ0 : ∀ y, y ∉ ball x ρ → ζ y = 0 := fun y hy => by rw [hζ_def]; simp [hη0 y hy]
    have hζ_cd : ContDiff ℝ 1 ζ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy : y ∈ ball x₀ R
      · rw [hζ_def]
        exact ((hη_cd.contDiffAt).mul hη_cd.contDiffAt).smul (hw.contDiffAt (isOpen_ball.mem_nhds hy))
      · have hy' : y ∉ closedBall x ρ := fun h => hy (hcl h)
        have : ζ =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy'] with z hz
          exact hζ0 z (fun h => hz (ball_subset_closedBall h))
        exact contDiffAt_const.congr_of_eventuallyEq this
    have hζ_supp : support ζ ⊆ closedBall x ρ := fun y hy => by
      by_contra h
      exact hy (hζ0 y (fun h' => h (ball_subset_closedBall h')))
    have hζ_cs : HasCompactSupport ζ :=
      HasCompactSupport.intro (isCompact_closedBall x ρ)
        (fun y hy => hζ0 y (fun h => hy (ball_subset_closedBall h)))
    have hζ_ts : tsupport ζ ⊆ ball x₀ R := (closure_minimal hζ_supp isClosed_closedBall).trans hcl
    have hζD : ∀ y ∈ ball x₀ R, ∀ v, fderiv ℝ ζ y v =
        (η y * η y) • fderiv ℝ w y v + (2 * η y * fderiv ℝ η y v) • w y := by
      intro y hy v
      have hηd : HasFDerivAt η (fderiv ℝ η y) y := (hη_cd.differentiable (by norm_num) y).hasFDerivAt
      have hwd : HasFDerivAt w (fderiv ℝ w y) y :=
        ((hw.differentiableOn (by norm_num)) y hy |>.differentiableAt
          (isOpen_ball.mem_nhds hy)).hasFDerivAt
      have hζd := (hηd.mul hηd).smul hwd
      rw [hζ_def, show (fun y => (η y * η y) • w y) = (η * η) • w from rfl, hζd.fderiv]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        Pi.mul_apply]
      congr 1
      rw [← add_smul]
      congr 1
      ring
    -- the weak equation tested with `ζ`, localized to `B_ρ(x)`
    have hW := hweak ζ hζ_cd hζ_cs hζ_ts
    have hζD0 : ∀ y ∈ ball x₀ R, y ∉ ball x ρ → fderiv ℝ ζ y = 0 := by
      intro y hy hy'
      ext1 v
      rw [hζD y hy v, hη0 y hy']
      simp
    have eL : ∫ y in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
        (fun y hy => by simp [hζD0 y hy.1 hy.2])
    have eR : ∫ y in ball x₀ R, ∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
        (fun y hy => by simp [hζD0 y hy.1 hy.2])
    have hW' := eL.symm.trans (hW.trans eR)
    -- integrability on `B_ρ(x)`
    have hζc : Continuous (fderiv ℝ ζ) := hζ_cd.continuous_fderiv (by norm_num)
    have hDwc : ContinuousOn (fderiv ℝ w) (closedBall x ρ) := hDw.mono hcl
    have hFc : ContinuousOn F (closedBall x ρ) := hF.mono hcl
    have hLint : IntegrableOn (fun y => ∑ j : Fin m, inner ℝ
        (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) (ball x ρ) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall x ρ)
        (continuousOn_finsetSum _ fun j _ => (hDwc.clm_apply continuousOn_const).inner
          (hζc.continuousOn.clm_apply continuousOn_const))).mono_set ball_subset_closedBall
    have hRint : IntegrableOn (fun y => ∑ j : Fin m, inner ℝ
        (F y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) (ball x ρ) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall x ρ)
        (continuousOn_finsetSum _ fun j _ => (hFc.clm_apply continuousOn_const).inner
          (hζc.continuousOn.clm_apply continuousOn_const))).mono_set ball_subset_closedBall
    have hPint : IntegrableOn (fun y => η y * η y * hs (fderiv ℝ w y)) (ball x ρ) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall x ρ)
        ((hη_cd.continuous.continuousOn.mul hη_cd.continuous.continuousOn).mul
          (hs_cont.comp_continuousOn hDwc))).mono_set ball_subset_closedBall
    -- the pointwise estimate of the integrand of `∫ η² |Dw|² = ∫ (R - L + η² |Dw|²)`
    set G := M₀ * ρ⁻¹ with hG
    have hG0 : 0 ≤ G := by positivity
    have hpt : ∀ y ∈ ball x ρ,
        (∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y) ≤
        η y * η y * hs (fderiv ℝ w y) / 2 + (6 * m * K ^ 2 + 17 * m * G ^ 2 * K ^ 2) := by
      intro y hy
      have hyR : y ∈ ball x₀ R := hbx hy
      obtain ⟨he0, he1⟩ := hη01 y
      have hwy : ‖w y‖ ≤ K := hwK y hyR
      have hee : 0 ≤ η y * η y := mul_nonneg he0 he0
      have hper : ∀ j : Fin m,
          inner ℝ (F y (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
          - inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
          + η y * η y * ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
          η y * η y * (3 * ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 / 4) + 17 * G ^ 2 * K ^ 2 := by
        intro j
        set f := F y (EuclideanSpace.single j (1 : ℝ))
        set a := fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))
        set t := fderiv ℝ η y (EuclideanSpace.single j (1 : ℝ))
        set e := η y
        have ht : |t| ≤ G := by
          calc |t| = ‖fderiv ℝ η y (EuclideanSpace.single j (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖fderiv ℝ η y‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖fderiv ℝ η y‖ := by simp
            _ ≤ G := hDη y
        rw [hζD y hyR, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        have i1 : inner ℝ f a ≤ ‖f‖ * ‖a‖ := real_inner_le_norm f a
        have i2 : |inner ℝ f (w y)| ≤ ‖f‖ * K :=
          (abs_real_inner_le_norm f (w y)).trans (mul_le_mul_of_nonneg_left hwy (norm_nonneg _))
        have i3 : |inner ℝ a (w y)| ≤ ‖a‖ * K :=
          (abs_real_inner_le_norm a (w y)).trans (mul_le_mul_of_nonneg_left hwy (norm_nonneg _))
        have b1 : e * e * inner ℝ f a ≤ e * e * (2 * ‖f‖ ^ 2 + ‖a‖ ^ 2 / 8) := by
          apply mul_le_mul_of_nonneg_left _ hee
          calc inner ℝ f a ≤ ‖f‖ * ‖a‖ := i1
            _ = (2 * ‖f‖) * (‖a‖ / 2) := by ring
            _ ≤ (2 * ‖f‖) ^ 2 / 2 + (‖a‖ / 2) ^ 2 / 2 := amgm _ _
            _ = 2 * ‖f‖ ^ 2 + ‖a‖ ^ 2 / 8 := by ring
        have b2 : 2 * e * t * inner ℝ f (w y) ≤ e * e * ‖f‖ ^ 2 + G ^ 2 * K ^ 2 := by
          calc 2 * e * t * inner ℝ f (w y) ≤ |2 * e * t * inner ℝ f (w y)| := le_abs_self _
            _ = 2 * e * (|t| * |inner ℝ f (w y)|) := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0, abs_two]; ring
            _ ≤ 2 * e * (G * (‖f‖ * K)) := by gcongr
            _ = 2 * ((e * ‖f‖) * (G * K)) := by ring
            _ ≤ 2 * ((e * ‖f‖) ^ 2 / 2 + (G * K) ^ 2 / 2) := by gcongr; exact amgm _ _
            _ = e * e * ‖f‖ ^ 2 + G ^ 2 * K ^ 2 := by ring
        have b3 : -(2 * e * t * inner ℝ a (w y)) ≤ e * e * (‖a‖ ^ 2 / 8) + 16 * G ^ 2 * K ^ 2 := by
          calc -(2 * e * t * inner ℝ a (w y)) ≤ |2 * e * t * inner ℝ a (w y)| := neg_le_abs _
            _ = 2 * e * (|t| * |inner ℝ a (w y)|) := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0, abs_two]; ring
            _ ≤ 2 * e * (G * (‖a‖ * K)) := by gcongr
            _ = 2 * ((e * ‖a‖ / 4) * (4 * G * K)) := by ring
            _ ≤ 2 * ((e * ‖a‖ / 4) ^ 2 / 2 + (4 * G * K) ^ 2 / 2) := by gcongr; exact amgm _ _
            _ = e * e * (‖a‖ ^ 2 / 16) + 16 * G ^ 2 * K ^ 2 := by ring
            _ ≤ e * e * (‖a‖ ^ 2 / 8) + 16 * G ^ 2 * K ^ 2 := by
                have : 0 ≤ e * e * ‖a‖ ^ 2 := by positivity
                linarith
        have e1 : e * e * ‖a‖ ^ 2 = e * e * ‖a‖ ^ 2 := rfl
        linarith [b1, b2, b3]
      -- `∑ |F e_j|² ≤ m |F|²` and `|F|² ≤ 2ε₁² c_N |Dw|²_HS + 2K²`
      have hFs : ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ m * ‖F y‖ ^ 2 := by
        have := hs_le (F y); rwa [hs_def] at this
      have hFy : ‖F y‖ ≤ ε₁ * ‖fderiv ℝ w y‖ + K := hFK y hyR
      have hsy := hs_nonneg (fderiv ℝ w y)
      have hF2 : ‖F y‖ ^ 2 ≤ 2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w y)) + 2 * K ^ 2 := by
        have h1 : ‖F y‖ ^ 2 ≤ (ε₁ * ‖fderiv ℝ w y‖ + K) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hFy 2
        have h2 : ε₁ ^ 2 * ‖fderiv ℝ w y‖ ^ 2 ≤ ε₁ ^ 2 * (cN * hs (fderiv ℝ w y)) :=
          mul_le_mul_of_nonneg_left (hN1 _) (sq_nonneg _)
        have h3 := amgm (ε₁ * ‖fderiv ℝ w y‖) K
        have h4 : (ε₁ * ‖fderiv ℝ w y‖ + K) ^ 2 =
            ε₁ ^ 2 * ‖fderiv ℝ w y‖ ^ 2 + 2 * ((ε₁ * ‖fderiv ℝ w y‖) * K) + K ^ 2 := by ring
        have h5 : (ε₁ * ‖fderiv ℝ w y‖) ^ 2 = ε₁ ^ 2 * ‖fderiv ℝ w y‖ ^ 2 := by ring
        linarith
      have hee1 : η y * η y ≤ 1 := by
        calc η y * η y ≤ 1 * 1 := mul_le_mul he1 he1 he0 zero_le_one
          _ = 1 := one_mul 1
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have hFsum : η y * η y * (3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≤
          η y * η y * hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2 := by
        have h3 : 3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
            6 * m * cN * ε₁ ^ 2 * hs (fderiv ℝ w y) + 6 * m * K ^ 2 := by
          have := mul_le_mul_of_nonneg_left hF2 hm0
          have e : (m : ℝ) * (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w y)) + 2 * K ^ 2) * 3 =
              6 * m * cN * ε₁ ^ 2 * hs (fderiv ℝ w y) + 6 * m * K ^ 2 := by ring
          linarith [hFs]
        have h4 : 6 * m * cN * ε₁ ^ 2 * hs (fderiv ℝ w y) ≤ hs (fderiv ℝ w y) / 4 := by
          have := mul_le_mul_of_nonneg_right hε₁cacc hsy
          linarith
        have h5 : 0 ≤ 6 * m * K ^ 2 := by positivity
        have h6 : 3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
            hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2 := by linarith
        calc η y * η y * (3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            ≤ η y * η y * (hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2) :=
              mul_le_mul_of_nonneg_left h6 hee
          _ = η y * η y * hs (fderiv ℝ w y) / 4 + η y * η y * (6 * m * K ^ 2) := by ring
          _ ≤ η y * η y * hs (fderiv ℝ w y) / 4 + 1 * (6 * m * K ^ 2) := by
              gcongr
          _ = η y * η y * hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2 := by ring
      calc (∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
            (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y)
          = ∑ j : Fin m, (inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
              - inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
              + η y * η y * ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
            rw [hs_def, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ ≤ ∑ j : Fin m, (η y * η y * (3 * ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
              + ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 / 4) + 17 * G ^ 2 * K ^ 2) :=
            Finset.sum_le_sum fun j _ => hper j
        _ = η y * η y * (3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
              + η y * η y * hs (fderiv ℝ w y) / 4 + m * (17 * G ^ 2 * K ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              hs_def]
            ring
        _ ≤ η y * η y * hs (fderiv ℝ w y) / 2 + (6 * m * K ^ 2 + 17 * m * G ^ 2 * K ^ 2) := by
            linarith [hFsum]
    -- integrate and absorb
    have hVρ : volume.real (ball x ρ) = ω * ρ ^ m := hvol x ρ hρ
    have hsub : ball x (R / 8) ⊆ ball x ρ := ball_subset_ball (by rw [hρ_def]; linarith)
    have hP0 : ∀ y, 0 ≤ η y * η y * hs (fderiv ℝ w y) := fun y =>
      mul_nonneg (mul_nonneg (hη01 y).1 (hη01 y).1) (hs_nonneg _)
    have hQint : IntegrableOn (fun y => (∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y))
        (ball x ρ) := (hRint.sub hLint).add hPint
    have hP_eq : ∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) =
        ∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y)) := by
      have e1 : ∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y)) =
        (∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))))) +
        ∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) := integral_add (hRint.sub hLint) hPint
      have e2 : ∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))) =
        (∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        ∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := integral_sub hRint hLint
      rw [e1, e2, hW']
      ring
    set c₁ := 6 * (m : ℝ) * K ^ 2 + 17 * m * G ^ 2 * K ^ 2 with hc₁
    have hbound : ∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) ≤
        ∫ y in ball x ρ, (η y * η y * hs (fderiv ℝ w y) / 2 + c₁) := by
      rw [hP_eq]
      exact setIntegral_mono_on hQint ((hPint.div_const 2).add (integrableOn_const measure_ball_lt_top.ne))
        measurableSet_ball hpt
    have hsplit : ∫ y in ball x ρ, (η y * η y * hs (fderiv ℝ w y) / 2 + c₁) =
        (∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y)) / 2 + volume.real (ball x ρ) * c₁ := by
      have e1 : ∫ y in ball x ρ, (η y * η y * hs (fderiv ℝ w y) / 2 + c₁) =
          (∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) / 2) + ∫ _y in ball x ρ, c₁ :=
        integral_add (hPint.div_const 2) (integrableOn_const measure_ball_lt_top.ne)
      rw [e1, integral_div, setIntegral_const, smul_eq_mul]
    rw [hsplit, hVρ] at hbound
    calc ∫ z in ball x (R / 8), hs (fderiv ℝ w z)
        = ∫ z in ball x (R / 8), η z * η z * hs (fderiv ℝ w z) :=
          setIntegral_congr_fun measurableSet_ball (fun z hz => by simp [hη1 z hz])
      _ ≤ ∫ z in ball x ρ, η z * η z * hs (fderiv ℝ w z) :=
          setIntegral_mono_set hPint (ae_of_all _ hP0) hsub.eventuallyLE
      _ ≤ 2 * c₁ * (ω * ρ ^ m) := by linarith
  -- comparison with the harmonic replacement (Campanato's inequalities (C1'), (C2'))
  have hcomp : ∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → ρ ≤ R₁ → dist x x₀ + 2 * ρ < R →
      ∀ r, 0 < r → r ≤ ρ →
      Φ x r ≤ A₁ * ((r / ρ) ^ ((m : ℝ) + 2) + ε₁) * Φ x ρ
          + A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) ∧
      Ψ x r ≤ A₁ * ((r / ρ) ^ (m : ℝ) + 2 * ε₁ ^ 2) * Ψ x ρ
          + 2 * A₁ * K ^ 2 * ω * ρ ^ (m : ℝ) := by
    intro x ρ hρ hρR₁ hxρ r hr hrρ
    have hball2 : ball x (2 * ρ) ⊆ ball x₀ R := ball_subset_ball' (by linarith)
    have hcl : closedBall x ρ ⊆ ball x₀ R := closedBall_subset_ball' (by linarith)
    have hbx : ball x ρ ⊆ ball x₀ R := ball_subset_closedBall.trans hcl
    have hsubr : ball x r ⊆ ball x ρ := ball_subset_ball hrρ
    -- the equation holds weakly in `B_ρ(x)`
    have hweak' : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball x ρ →
        ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w z (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) =
        ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (F z (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) := by
      intro ζ hζ hζc hζs
      have h := hweak ζ hζ hζc (hζs.trans hbx)
      have hzero : ∀ z, z ∉ ball x ρ → fderiv ℝ ζ z = 0 := fun z hz => by
        by_contra hne
        exact hz (hζs (support_fderiv_subset ℝ hne))
      have eL : ∫ z in ball x₀ R, ∑ j : Fin m,
            inner ℝ (fderiv ℝ w z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) =
          ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
          (fun z hz => by simp [hzero z hz.2])
      have eR : ∫ z in ball x₀ R, ∑ j : Fin m, inner ℝ (F z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) =
          ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (F z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
          (fun z hz => by simp [hzero z hz.2])
      rw [← eL, ← eR]
      exact h
    -- the harmonic replacement `h` of `w` in `B_ρ(x)`
    obtain ⟨h, hsm, hharm, hDint, hDle⟩ := hrepl m k hm x ρ (2 * ρ) w F hρ (by linarith)
      (hw.mono hball2) (hF.mono hball2) hweak'
    have hDint' : IntegrableOn (fun z => hs (fderiv ℝ w z - fderiv ℝ h z)) (ball x ρ) := by
      simpa only [hs_def] using hDint
    have hDle' : ∀ c, ∫ z in ball x ρ, hs (fderiv ℝ w z - fderiv ℝ h z) ≤
        ∫ z in ball x ρ, hs (F z - c) := by
      intro c; simpa only [hs_def] using hDle c
    obtain ⟨D, hD⟩ : ∃ D, D = ∫ z in ball x ρ, hs (fderiv ℝ w z - fderiv ℝ h z) := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by
      rw [hD]; exact setIntegral_nonneg measurableSet_ball fun z _ => hs_nonneg _
    have hDr : ∫ z in ball x r, hs (fderiv ℝ w z - fderiv ℝ h z) ≤ D := by
      rw [hD]
      exact setIntegral_mono_set hDint' (ae_of_all _ fun z => hs_nonneg _) hsubr.eventuallyLE
    -- integrability in `B_ρ(x)`
    obtain ⟨hwint, hwint2c, hwint2⟩ := hgood x ρ hcl
    have hDh : ContinuousOn (fderiv ℝ h) (ball x ρ) :=
      (hsm 1).continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
    have hDhm : AEStronglyMeasurable (fderiv ℝ h) (volume.restrict (ball x ρ)) :=
      hDh.aestronglyMeasurable measurableSet_ball
    have hhint2 : IntegrableOn (fun z => hs (fderiv ℝ h z)) (ball x ρ) := by
      refine Integrable.mono' ((hwint2.const_mul 2).add (hDint'.const_mul 2))
        (hs_cont.comp_aestronglyMeasurable hDhm) (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg (hs_nonneg _)]
      have := hs_add (fderiv ℝ w z) (fderiv ℝ h z - fderiv ℝ w z)
      rw [show fderiv ℝ w z + (fderiv ℝ h z - fderiv ℝ w z) = fderiv ℝ h z by abel,
        hs_sub_comm (fderiv ℝ h z) (fderiv ℝ w z)] at this
      exact this
    have hhint : IntegrableOn (fderiv ℝ h) (ball x ρ) := by
      refine Integrable.mono' ((integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).add
        (hhint2.const_mul cN)) hDhm (ae_of_all _ fun z => ?_)
      have h1 := hN1 (fderiv ℝ h z)
      have h2 := amgm ‖fderiv ℝ h z‖ 1
      have h3 : 0 ≤ cN * hs (fderiv ℝ h z) := mul_nonneg hcN0 (hs_nonneg _)
      show ‖fderiv ℝ h z‖ ≤ 1 + cN * hs (fderiv ℝ h z)
      linarith
    have hhint2c : ∀ c, IntegrableOn (fun z => hs (fderiv ℝ h z - c)) (ball x ρ) := fun c => by
      refine Integrable.mono' ((hhint2.const_mul 2).add
        (integrableOn_const measure_ball_lt_top.ne (C := 2 * hs (-c))))
        (hs_cont.comp_aestronglyMeasurable (hDhm.sub aestronglyMeasurable_const))
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg (hs_nonneg _), sub_eq_add_neg]
      exact hs_add _ _
    -- harmonic decay
    have hhint2' : IntegrableOn (fun z => ∑ j : Fin m,
        ‖fderiv ℝ h z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x ρ) := by
      simpa only [hs_def] using hhint2
    obtain ⟨hdec1, hdec2⟩ := hdec x ρ h hρ hsm hharm hhint2' r hr hrρ
    have hdec1' : ∫ z in ball x r, hs (fderiv ℝ h z - ⨍ z' in ball x r, fderiv ℝ h z') ≤
        Cd * (r / ρ) ^ (m + 2) *
          ∫ z in ball x ρ, hs (fderiv ℝ h z - ⨍ z' in ball x ρ, fderiv ℝ h z') := by
      simpa only [hs_def] using hdec1
    have hdec2' : ∫ z in ball x r, hs (fderiv ℝ h z) ≤
        Cd * (r / ρ) ^ m * ∫ z in ball x ρ, hs (fderiv ℝ h z) := by
      simpa only [hs_def] using hdec2
    have hq : 0 ≤ r / ρ := by positivity
    have hq1 : r / ρ ≤ 1 := (div_le_one hρ).mpr hrρ
    have hqa : (r / ρ) ^ (m + 2) ≤ 1 := pow_le_one₀ hq hq1
    have hqb : (r / ρ) ^ m ≤ 1 := pow_le_one₀ hq hq1
    have hΦρ0 := hΦ0 x ρ
    have hΨρ0 := hΨ0 x ρ
    -- (C1): `Φ(r) ≤ 4C_d (r/ρ)^{m+2} Φ(ρ) + (4C_d + 2) D`
    have hC1 : Φ x r ≤ 4 * Cd * (r / ρ) ^ (m + 2) * Φ x ρ + (4 * Cd + 2) * D := by
      set ahr := ⨍ z' in ball x r, fderiv ℝ h z' with hahr
      set awρ := ⨍ z' in ball x ρ, fderiv ℝ w z' with hawρ
      have s1 : Φ x r ≤ ∫ z in ball x r, hs (fderiv ℝ w z - ahr) := by
        rw [hΦ]
        exact hMP _ _ _ measurableSet_ball measure_ball_lt_top.ne (hvolpos x r hr)
          (hwint.mono_set hsubr) (hwint2.mono_set hsubr)
      have s2 : ∫ z in ball x r, hs (fderiv ℝ w z - ahr) ≤
          2 * (∫ z in ball x r, hs (fderiv ℝ h z - ahr)) + 2 * D := by
        have i1 : ∫ z in ball x r, hs (fderiv ℝ w z - ahr) ≤
            ∫ z in ball x r, (2 * hs (fderiv ℝ h z - ahr)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) :=
          setIntegral_mono_on ((hwint2c ahr).mono_set hsubr)
            ((((hhint2c ahr).mono_set hsubr).const_mul 2).add ((hDint'.mono_set hsubr).const_mul 2))
            measurableSet_ball (fun z _ => by
              have := hs_add (fderiv ℝ h z - ahr) (fderiv ℝ w z - fderiv ℝ h z)
              rwa [show fderiv ℝ h z - ahr + (fderiv ℝ w z - fderiv ℝ h z) = fderiv ℝ w z - ahr by
                abel] at this)
        have i2 : ∫ z in ball x r, (2 * hs (fderiv ℝ h z - ahr)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) =
            2 * (∫ z in ball x r, hs (fderiv ℝ h z - ahr))
              + 2 * ∫ z in ball x r, hs (fderiv ℝ w z - fderiv ℝ h z) := by
          rw [integral_add (((hhint2c ahr).mono_set hsubr).const_mul 2)
            ((hDint'.mono_set hsubr).const_mul 2), integral_const_mul, integral_const_mul]
        linarith [hDr]
      have s3 : ∫ z in ball x ρ, hs (fderiv ℝ h z - ⨍ z' in ball x ρ, fderiv ℝ h z') ≤
          2 * Φ x ρ + 2 * D := by
        have i1 := hMP (ball x ρ) (fderiv ℝ h) awρ measurableSet_ball measure_ball_lt_top.ne
          (hvolpos x ρ hρ) hhint hhint2
        have i2 : ∫ z in ball x ρ, hs (fderiv ℝ h z - awρ) ≤
            ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z - awρ)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) :=
          setIntegral_mono_on (hhint2c awρ) (((hwint2c awρ).const_mul 2).add (hDint'.const_mul 2))
            measurableSet_ball (fun z _ => by
              have := hs_add (fderiv ℝ w z - awρ) (fderiv ℝ h z - fderiv ℝ w z)
              rwa [show fderiv ℝ w z - awρ + (fderiv ℝ h z - fderiv ℝ w z) = fderiv ℝ h z - awρ by
                abel, hs_sub_comm (fderiv ℝ h z) (fderiv ℝ w z)] at this)
        have i3 : ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z - awρ)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) = 2 * Φ x ρ + 2 * D := by
          rw [integral_add ((hwint2c awρ).const_mul 2) (hDint'.const_mul 2), integral_const_mul,
            integral_const_mul, hΦ, hD]
        linarith
      have s4 : ∫ z in ball x r, hs (fderiv ℝ h z - ahr) ≤
          Cd * (r / ρ) ^ (m + 2) * (2 * Φ x ρ + 2 * D) :=
        hdec1'.trans (by gcongr)
      have s5 : Cd * (r / ρ) ^ (m + 2) * D ≤ Cd * D := by
        calc Cd * (r / ρ) ^ (m + 2) * D = (Cd * D) * (r / ρ) ^ (m + 2) := by ring
          _ ≤ (Cd * D) * 1 := mul_le_mul_of_nonneg_left hqa (by positivity)
          _ = Cd * D := mul_one _
      have e : Cd * (r / ρ) ^ (m + 2) * (2 * Φ x ρ + 2 * D) =
          2 * (Cd * (r / ρ) ^ (m + 2) * Φ x ρ) + 2 * (Cd * (r / ρ) ^ (m + 2) * D) := by ring
      have e2 : 4 * Cd * (r / ρ) ^ (m + 2) * Φ x ρ = 4 * (Cd * (r / ρ) ^ (m + 2) * Φ x ρ) := by ring
      linarith
    -- (C2): `Ψ(r) ≤ 4C_d (r/ρ)^m Ψ(ρ) + (4C_d + 2) D`
    have hC2 : Ψ x r ≤ 4 * Cd * (r / ρ) ^ m * Ψ x ρ + (4 * Cd + 2) * D := by
      have s1 : Ψ x r ≤ 2 * (∫ z in ball x r, hs (fderiv ℝ h z)) + 2 * D := by
        have i1 : Ψ x r ≤ ∫ z in ball x r, (2 * hs (fderiv ℝ h z)
            + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) := by
          rw [hΨ]
          exact setIntegral_mono_on (hwint2.mono_set hsubr)
            (((hhint2.mono_set hsubr).const_mul 2).add ((hDint'.mono_set hsubr).const_mul 2))
            measurableSet_ball
            (fun z _ => by
              have := hs_add (fderiv ℝ h z) (fderiv ℝ w z - fderiv ℝ h z)
              rwa [show fderiv ℝ h z + (fderiv ℝ w z - fderiv ℝ h z) = fderiv ℝ w z by abel] at this)
        have i2 : ∫ z in ball x r, (2 * hs (fderiv ℝ h z)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) =
            2 * (∫ z in ball x r, hs (fderiv ℝ h z))
              + 2 * ∫ z in ball x r, hs (fderiv ℝ w z - fderiv ℝ h z) := by
          rw [integral_add ((hhint2.mono_set hsubr).const_mul 2)
            ((hDint'.mono_set hsubr).const_mul 2), integral_const_mul, integral_const_mul]
        linarith [hDr]
      have s2 : ∫ z in ball x ρ, hs (fderiv ℝ h z) ≤ 2 * Ψ x ρ + 2 * D := by
        have i1 : ∫ z in ball x ρ, hs (fderiv ℝ h z) ≤
            ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z) + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) :=
          setIntegral_mono_on hhint2 ((hwint2.const_mul 2).add (hDint'.const_mul 2))
            measurableSet_ball (fun z _ => by
              have := hs_add (fderiv ℝ w z) (fderiv ℝ h z - fderiv ℝ w z)
              rwa [show fderiv ℝ w z + (fderiv ℝ h z - fderiv ℝ w z) = fderiv ℝ h z by abel,
                hs_sub_comm (fderiv ℝ h z) (fderiv ℝ w z)] at this)
        have i2 : ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) = 2 * Ψ x ρ + 2 * D := by
          rw [integral_add (hwint2.const_mul 2) (hDint'.const_mul 2), integral_const_mul,
            integral_const_mul, hΨ, hD]
        linarith
      have s3 : ∫ z in ball x r, hs (fderiv ℝ h z) ≤ Cd * (r / ρ) ^ m * (2 * Ψ x ρ + 2 * D) :=
        hdec2'.trans (by gcongr)
      have s5 : Cd * (r / ρ) ^ m * D ≤ Cd * D := by
        calc Cd * (r / ρ) ^ m * D = (Cd * D) * (r / ρ) ^ m := by ring
          _ ≤ (Cd * D) * 1 := mul_le_mul_of_nonneg_left hqb (by positivity)
          _ = Cd * D := mul_one _
      have e : Cd * (r / ρ) ^ m * (2 * Ψ x ρ + 2 * D) =
          2 * (Cd * (r / ρ) ^ m * Ψ x ρ) + 2 * (Cd * (r / ρ) ^ m * D) := by ring
      have e2 : 4 * Cd * (r / ρ) ^ m * Ψ x ρ = 4 * (Cd * (r / ρ) ^ m * Ψ x ρ) := by ring
      linarith
    -- `D ≤ ∫ |F - c|²_HS` for the constant `c` of (H_F), and for `c = 0`
    have hFint : ∀ c, IntegrableOn (fun z => hs (F z - c)) (ball x ρ) := fun c =>
      ((hs_cont.comp_continuousOn ((hF.mono hcl).sub continuousOn_const)).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hV := hvol x ρ hρ
    have hρm : ρ ^ m ≤ R₁ ^ m := pow_le_pow_left₀ hρ.le hρR₁ m
    have hρ2α : ρ ^ (2 * α) ≤ R₁ ^ (2 * α) := Real.rpow_le_rpow hρ.le hρR₁ (by positivity)
    obtain ⟨c, hc⟩ := hHF x ρ hρ hcl
    have hop1 : IntegrableOn (fun z => ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2)
        (ball x ρ) :=
      ((((hDw.mono hcl).sub continuousOn_const).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hop2 : IntegrableOn (fun z => ‖fderiv ℝ w z‖ ^ 2) (ball x ρ) :=
      ((((hDw.mono hcl).norm.pow 2)).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hinner : ∫ z in ball x ρ, (‖fderiv ℝ w z‖ ^ 2 + K * ρ ^ ((m : ℝ) + 2 * α)) =
        (∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2) + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)) := by
      rw [integral_add hop2 (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
        smul_eq_mul, hV]
    rw [hinner] at hc
    have houter : ∫ z in ball x ρ, (‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2
        + K * ρ ^ (2 * α) * ((∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2)
          + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))) =
        (∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2)
          + ω * ρ ^ m * (K * ρ ^ (2 * α) * ((∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2)
            + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))) := by
      rw [integral_add hop1 (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
        smul_eq_mul, hV]
    rw [houter] at hc
    set Φop := ∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2 with hΦop_def
    set Ψop := ∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2 with hΨop_def
    have hΦop' : Φop ≤ cN * Φ x ρ := hΦop x ρ hcl
    have hΨop' : Ψop ≤ cN * Ψ x ρ := hΨop x ρ hcl
    have hΨop0 : 0 ≤ Ψop := setIntegral_nonneg measurableSet_ball (fun z _ => by positivity)
    have hFc : ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤
        ε₁ * cN * Φ x ρ + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) := by
      refine hc.trans ?_
      have t1 : ε₁ * Φop ≤ ε₁ * (cN * Φ x ρ) := mul_le_mul_of_nonneg_left hΦop' hε₁0.le
      have t2 : ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop)) ≤
          (ω * K * R₁ ^ m * cN) * (ρ ^ (2 * α) * Ψ x ρ) := by
        have a1 : 0 ≤ K * ρ ^ (2 * α) := by positivity
        have a3 : 0 ≤ K * ρ ^ (2 * α) * Ψop := mul_nonneg a1 hΨop0
        have a4 : ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop) ≤
            ω * R₁ ^ m * (K * ρ ^ (2 * α) * (cN * Ψ x ρ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hρm hω_pos.le)
            (mul_le_mul_of_nonneg_left hΨop' a1) a3 (by positivity)
        have a5 : 0 ≤ ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop) := mul_nonneg (by positivity) a3
        calc ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop))
            ≤ 1 * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop)) := mul_le_mul_of_nonneg_right hε₁1 a5
          _ ≤ ω * R₁ ^ m * (K * ρ ^ (2 * α) * (cN * Ψ x ρ)) := by rw [one_mul]; exact a4
          _ = (ω * K * R₁ ^ m * cN) * (ρ ^ (2 * α) * Ψ x ρ) := by ring
      have t3 : ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) ≤
          (ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α)) * ρ ^ ((m : ℝ) + 2 * α) := by
        have a0 : 0 ≤ ρ ^ ((m : ℝ) + 2 * α) := by positivity
        have a1 : ρ ^ m * ρ ^ m ≤ R₁ ^ m * R₁ ^ m := mul_le_mul hρm hρm (by positivity) (by positivity)
        have a2 : ρ ^ m * ρ ^ m * ρ ^ (2 * α) ≤ R₁ ^ m * R₁ ^ m * R₁ ^ (2 * α) :=
          mul_le_mul a1 hρ2α (by positivity) (by positivity)
        have a5 : 0 ≤ ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))) := by
          positivity
        calc ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))))
            ≤ 1 * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) :=
              mul_le_mul_of_nonneg_right hε₁1 a5
          _ = (ω ^ 2 * K ^ 2 * ρ ^ ((m : ℝ) + 2 * α)) * (ρ ^ m * ρ ^ m * ρ ^ (2 * α)) := by ring
          _ ≤ (ω ^ 2 * K ^ 2 * ρ ^ ((m : ℝ) + 2 * α)) * (R₁ ^ m * R₁ ^ m * R₁ ^ (2 * α)) :=
              mul_le_mul_of_nonneg_left a2 (by positivity)
          _ = (ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α)) * ρ ^ ((m : ℝ) + 2 * α) := by ring
      have t4 : (ω * K * R₁ ^ m * cN) * (ρ ^ (2 * α) * Ψ x ρ) ≤ K₁ * (ρ ^ (2 * α) * Ψ x ρ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hK₁]
        have : 0 ≤ ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α) := by positivity
        linarith
      have t5 : (ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α)) * ρ ^ ((m : ℝ) + 2 * α) ≤
          K₁ * ρ ^ ((m : ℝ) + 2 * α) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hK₁]
        have : 0 ≤ ω * K * R₁ ^ m * cN := by positivity
        linarith
      have e : ε₁ * (Φop + ω * ρ ^ m * (K * ρ ^ (2 * α) * (Ψop
            + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) =
          ε₁ * Φop + ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop))
            + ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) := by
        ring
      rw [e]
      have e2 : K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) =
          K₁ * (ρ ^ (2 * α) * Ψ x ρ) + K₁ * ρ ^ ((m : ℝ) + 2 * α) := by ring
      have e3 : ε₁ * (cN * Φ x ρ) = ε₁ * cN * Φ x ρ := by ring
      linarith
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hFc2 : IntegrableOn (fun z => ‖F z - c‖ ^ 2) (ball x ρ) :=
      ((((hF.mono hcl).sub continuousOn_const).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hDc : D ≤ m * (ε₁ * cN * Φ x ρ + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by
      calc D ≤ ∫ z in ball x ρ, hs (F z - c) := by rw [hD]; exact hDle' c
        _ ≤ ∫ z in ball x ρ, (m : ℝ) * ‖F z - c‖ ^ 2 :=
            setIntegral_mono_on (hFint c) (hFc2.const_mul _) measurableSet_ball
              (fun z _ => hs_le _)
        _ = m * ∫ z in ball x ρ, ‖F z - c‖ ^ 2 := integral_const_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hFc hm0
    have hFb_int : IntegrableOn
        (fun z => (m : ℝ) * (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2)) (ball x ρ) :=
      (((hwint2.const_mul cN).const_mul (2 * ε₁ ^ 2)).add
        (integrableOn_const measure_ball_lt_top.ne)).const_mul _
    have hDF : D ≤ m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m)) := by
      calc D ≤ ∫ z in ball x ρ, hs (F z - 0) := by rw [hD]; exact hDle' 0
        _ ≤ ∫ z in ball x ρ, (m : ℝ) * (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2) :=
            setIntegral_mono_on (hFint 0) hFb_int
              measurableSet_ball (fun z hz => by
                rw [sub_zero]
                exact (hs_le _).trans (mul_le_mul_of_nonneg_left (hF2 z (hbx hz)) hm0))
        _ = m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m)) := by
            have e1 : ∫ z in ball x ρ, (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2) =
                (∫ z in ball x ρ, 2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z))) + ∫ _z in ball x ρ, 2 * K ^ 2 :=
              integral_add ((hwint2.const_mul cN).const_mul _)
                (integrableOn_const measure_ball_lt_top.ne)
            rw [integral_const_mul, e1, integral_const_mul, integral_const_mul, setIntegral_const,
              smul_eq_mul, hV, ← hΨ]
            ring
    -- conclusion
    have hqr : (r / ρ) ^ ((m : ℝ) + 2) = (r / ρ) ^ (m + 2) := by norm_cast
    have hqr' : (r / ρ) ^ (m : ℝ) = (r / ρ) ^ m := Real.rpow_natCast _ _
    have hρr : ρ ^ (m : ℝ) = ρ ^ m := Real.rpow_natCast _ _
    have hX0 : 0 ≤ ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α) := by positivity
    constructor
    · rw [hqr]
      have u1 : 4 * Cd * (r / ρ) ^ (m + 2) * Φ x ρ ≤ A₁ * (r / ρ) ^ (m + 2) * Φ x ρ := by
        gcongr
      have u2 : (4 * Cd + 2) * D ≤ (4 * Cd + 2) * (m * (ε₁ * cN * Φ x ρ
          + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)))) := by gcongr
      have u4 : ((4 * Cd + 2) * m * cN) * (ε₁ * Φ x ρ) ≤ A₁ * (ε₁ * Φ x ρ) := by gcongr
      have u5 : ((4 * Cd + 2) * m) * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) ≤
          A₁ * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by gcongr
      have e1 : (4 * Cd + 2) * (m * (ε₁ * cN * Φ x ρ
          + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)))) =
          ((4 * Cd + 2) * m * cN) * (ε₁ * Φ x ρ)
            + ((4 * Cd + 2) * m) * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by ring
      have e2 : A₁ * ((r / ρ) ^ (m + 2) + ε₁) * Φ x ρ
          + A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) =
          A₁ * (r / ρ) ^ (m + 2) * Φ x ρ + A₁ * (ε₁ * Φ x ρ)
            + A₁ * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by ring
      linarith
    · rw [hqr', hρr]
      have u1 : 4 * Cd * (r / ρ) ^ m * Ψ x ρ ≤ A₁ * (r / ρ) ^ m * Ψ x ρ := by gcongr
      have u2 : (4 * Cd + 2) * D ≤
          (4 * Cd + 2) * (m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m))) := by gcongr
      have u4 : ((4 * Cd + 2) * m * cN) * (2 * ε₁ ^ 2 * Ψ x ρ) ≤ A₁ * (2 * ε₁ ^ 2 * Ψ x ρ) := by
        gcongr
      have u5 : ((4 * Cd + 2) * m) * (2 * K ^ 2 * (ω * ρ ^ m)) ≤ A₁ * (2 * K ^ 2 * (ω * ρ ^ m)) := by
        gcongr
      have e1 : (4 * Cd + 2) * (m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m))) =
          ((4 * Cd + 2) * m * cN) * (2 * ε₁ ^ 2 * Ψ x ρ)
            + ((4 * Cd + 2) * m) * (2 * K ^ 2 * (ω * ρ ^ m)) := by ring
      have e2 : A₁ * ((r / ρ) ^ m + 2 * ε₁ ^ 2) * Ψ x ρ + 2 * A₁ * K ^ 2 * ω * ρ ^ m =
          A₁ * (r / ρ) ^ m * Ψ x ρ + A₁ * (2 * ε₁ ^ 2 * Ψ x ρ)
            + A₁ * (2 * K ^ 2 * (ω * ρ ^ m)) := by ring
      linarith
  -- Step 3 (Morrey decay): `Ψ(x, r) ≤ C₃ r^{m-α}` on `B_{R/2}(x₀)`, `r ≤ R₁`
  have hstep3 : ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ R₁ → Ψ x r ≤ C₃ * r ^ ((m : ℝ) - α) := by
    intro x hx r hr hrR₁
    have hxd : dist x x₀ < R / 2 := hx
    have hgoodρ : ∀ ρ, ρ ≤ R₁ → closedBall x ρ ⊆ ball x₀ R := fun ρ hρ =>
      closedBall_subset_ball' (by rw [hR₁] at hρ; linarith)
    have key := hIa (Ψ x) R₁ (2 * ε₁ ^ 2) B₃ (by positivity) hε₁sq hB₃0
      (fun s _ _ => hΨ0 x s)
      (fun s ρ _ hsρ hρR => hΨmono x s ρ hsρ (hgoodρ ρ hρR))
      (fun s ρ hs hsρ hρR => by
        have hρ : 0 < ρ := hs.trans_le hsρ
        have h := (hcomp x ρ hρ hρR (by rw [hR₁] at hρR; linarith) s hs hsρ).2
        have hsplit : ρ ^ (m : ℝ) = ρ ^ α * ρ ^ ((m : ℝ) - α) := by
          rw [← Real.rpow_add hρ]; ring_nf
        have hρα : ρ ^ α ≤ R₁ ^ α := Real.rpow_le_rpow hρ.le hρR hα0.le
        have : 2 * A₁ * K ^ 2 * ω * ρ ^ (m : ℝ) ≤ B₃ * ρ ^ ((m : ℝ) - α) := by
          rw [hsplit, hB₃]
          calc 2 * A₁ * K ^ 2 * ω * (ρ ^ α * ρ ^ ((m : ℝ) - α))
              = 2 * A₁ * K ^ 2 * ω * ρ ^ α * ρ ^ ((m : ℝ) - α) := by ring
            _ ≤ 2 * A₁ * K ^ 2 * ω * R₁ ^ α * ρ ^ ((m : ℝ) - α) := by gcongr
        linarith)
      r R₁ hr hrR₁ le_rfl
    have hcx := hcacc x hx
    rw [Real.div_rpow hr.le hR₁0.le] at key
    calc Ψ x r ≤ ca * (r ^ ((m : ℝ) - α) / R₁ ^ ((m : ℝ) - α) * Ψ x R₁
          + B₃ * r ^ ((m : ℝ) - α)) := key
      _ ≤ ca * (r ^ ((m : ℝ) - α) / R₁ ^ ((m : ℝ) - α) * Ccacc + B₃ * r ^ ((m : ℝ) - α)) := by
          gcongr
      _ = C₃ * r ^ ((m : ℝ) - α) := by rw [hC₃]; ring
  -- Step 4 (first Campanato pass): `Φ(x, r) ≤ C₅ r^{m+α}` on `B_{R/2}(x₀)`, `r ≤ R₁`
  have hstep4 : ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ R₁ → Φ x r ≤ C₅ * r ^ ((m : ℝ) + α) := by
    intro x hx r hr hrR₁
    have hxd : dist x x₀ < R / 2 := hx
    have hgoodρ : ∀ ρ, ρ ≤ R₁ → closedBall x ρ ⊆ ball x₀ R := fun ρ hρ =>
      closedBall_subset_ball' (by rw [hR₁] at hρ; linarith)
    have key := hIb (Φ x) R₁ ε₁ B₅ hε₁0.le hε₁b hB₅0
      (fun s _ _ => hΦ0 x s)
      (fun s ρ hs hsρ hρR => hΦmono x s ρ hs hsρ (hgoodρ ρ hρR))
      (fun s ρ hs hsρ hρR => by
        have hρ : 0 < ρ := hs.trans_le hsρ
        have h := (hcomp x ρ hρ hρR (by rw [hR₁] at hρR; linarith) s hs hsρ).1
        have hΨρ := hstep3 x hx ρ hρ hρR
        have e1 : ρ ^ (2 * α) * ρ ^ ((m : ℝ) - α) = ρ ^ ((m : ℝ) + α) := by
          rw [← Real.rpow_add hρ]; ring_nf
        have e2 : ρ ^ ((m : ℝ) + 2 * α) = ρ ^ α * ρ ^ ((m : ℝ) + α) := by
          rw [← Real.rpow_add hρ]; ring_nf
        have hρα : ρ ^ α ≤ R₁ ^ α := Real.rpow_le_rpow hρ.le hρR hα0.le
        have : A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) ≤
            B₅ * ρ ^ ((m : ℝ) + α) := by
          have h1 : ρ ^ (2 * α) * Ψ x ρ ≤ C₃ * ρ ^ ((m : ℝ) + α) := by
            calc ρ ^ (2 * α) * Ψ x ρ ≤ ρ ^ (2 * α) * (C₃ * ρ ^ ((m : ℝ) - α)) := by gcongr
              _ = C₃ * (ρ ^ (2 * α) * ρ ^ ((m : ℝ) - α)) := by ring
              _ = C₃ * ρ ^ ((m : ℝ) + α) := by rw [e1]
          have h2 : ρ ^ ((m : ℝ) + 2 * α) ≤ R₁ ^ α * ρ ^ ((m : ℝ) + α) := by
            rw [e2]; gcongr
          rw [hB₅]
          calc A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))
              ≤ A₁ * K₁ * (C₃ * ρ ^ ((m : ℝ) + α) + R₁ ^ α * ρ ^ ((m : ℝ) + α)) := by gcongr
            _ = A₁ * K₁ * (C₃ + R₁ ^ α) * ρ ^ ((m : ℝ) + α) := by ring
        linarith)
      r R₁ hr hrR₁ le_rfl
    have hΦR₁ : Φ x R₁ ≤ C₃ * R₁ ^ ((m : ℝ) - α) :=
      (hΦΨ x R₁ hR₁0 (hgoodρ R₁ le_rfl)).trans (hstep3 x hx R₁ hR₁0 le_rfl)
    rw [Real.div_rpow hr.le hR₁0.le] at key
    calc Φ x r ≤ cb * (r ^ ((m : ℝ) + α) / R₁ ^ ((m : ℝ) + α) * Φ x R₁
          + B₅ * r ^ ((m : ℝ) + α)) := key
      _ ≤ cb * (r ^ ((m : ℝ) + α) / R₁ ^ ((m : ℝ) + α) * (C₃ * R₁ ^ ((m : ℝ) - α))
          + B₅ * r ^ ((m : ℝ) + α)) := by gcongr
      _ = C₅ * r ^ ((m : ℝ) + α) := by rw [hC₅]; ring
  -- Step 5: `Dw` is `α/2`-Hölder on `B_{R/2}(x₀)` at scale `R₁/2`, and bounded on `B_{3R/8}(x₀)`
  have hhol1 : ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2), ‖x - y‖ ≤ R₁ / 2 →
      ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C₀' * Real.sqrt (cN * C₅) * ‖x - y‖ ^ (α / 2) :=
    hII' (fderiv ℝ w) x₀ (R / 2) R₁ (cN * C₅) (by positivity) hR₁0 (by positivity)
      (hDw.mono (closedBall_subset_ball (by rw [hR₁]; linarith)))
      (fun x hx ρ hρ hρR => by
        have hxd : dist x x₀ < R / 2 := hx
        have hxr : closedBall x ρ ⊆ ball x₀ R :=
          closedBall_subset_ball' (by rw [hR₁] at hρR; linarith)
        calc _ ≤ cN * Φ x ρ := hΦop x ρ hxr
          _ ≤ cN * (C₅ * ρ ^ ((m : ℝ) + α)) := by gcongr; exact hstep4 x hx ρ hρ hρR
          _ = cN * C₅ * ρ ^ ((m : ℝ) + 2 * (α / 2)) := by
              rw [show 2 * (α / 2) = α by ring]; ring)
  have hsup : ∀ x ∈ ball x₀ (3 * R / 8), ‖fderiv ℝ w x‖ ^ 2 ≤ C₆ := by
    intro x hx
    have hxd : dist x x₀ < 3 * R / 8 := hx
    have hx2 : x ∈ ball x₀ (R / 2) := by rw [mem_ball]; linarith
    have hr : 0 < R / 16 := by positivity
    have hrR₁ : R / 16 ≤ R₁ := by rw [hR₁]; linarith
    have hxr : closedBall x (R / 16) ⊆ ball x₀ R := closedBall_subset_ball' (by linarith)
    obtain ⟨-, -, h3⟩ := hgood x (R / 16) hxr
    have hpt : ∀ z ∈ ball x (R / 16),
        ‖fderiv ℝ w x‖ ^ 2 ≤ 2 * H ^ 2 + 2 * cN * hs (fderiv ℝ w z) := by
      intro z hz
      have hzd : dist z x < R / 16 := hz
      have hz2 : z ∈ ball x₀ (R / 2) := by
        rw [mem_ball]; linarith [dist_triangle z x x₀]
      have hxz' : ‖x - z‖ < R / 16 := by rw [← dist_eq_norm, dist_comm]; exact hzd
      have hxz : ‖x - z‖ ≤ R₁ / 2 := by rw [hR₁]; linarith
      have h1 := hhol1 x hx2 z hz2 hxz
      have h2 : ‖x - z‖ ^ (α / 2) ≤ (R / 16) ^ (α / 2) :=
        Real.rpow_le_rpow (norm_nonneg _) hxz'.le (by positivity)
      have h3' : ‖fderiv ℝ w x - fderiv ℝ w z‖ ≤ H := by
        rw [hH]
        calc _ ≤ C₀' * Real.sqrt (cN * C₅) * ‖x - z‖ ^ (α / 2) := h1
          _ ≤ C₀' * Real.sqrt (cN * C₅) * (R / 16) ^ (α / 2) := by gcongr
      have h4 : ‖fderiv ℝ w x‖ ≤ H + ‖fderiv ℝ w z‖ := by
        calc ‖fderiv ℝ w x‖ = ‖(fderiv ℝ w x - fderiv ℝ w z) + fderiv ℝ w z‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖fderiv ℝ w x - fderiv ℝ w z‖ + ‖fderiv ℝ w z‖ := norm_add_le _ _
          _ ≤ H + ‖fderiv ℝ w z‖ := by linarith
      have h5 := hN1 (fderiv ℝ w z)
      have h6 : ‖fderiv ℝ w x‖ ^ 2 ≤ (H + ‖fderiv ℝ w z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h4 2
      have h7 := amgm H ‖fderiv ℝ w z‖
      have e : (H + ‖fderiv ℝ w z‖) ^ 2 = H ^ 2 + 2 * (H * ‖fderiv ℝ w z‖) + ‖fderiv ℝ w z‖ ^ 2 := by
        ring
      linarith
    have hint : ∫ _z in ball x (R / 16), ‖fderiv ℝ w x‖ ^ 2 ≤
        ∫ z in ball x (R / 16), (2 * H ^ 2 + 2 * cN * hs (fderiv ℝ w z)) :=
      setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne)
        ((integrableOn_const measure_ball_lt_top.ne).add (h3.const_mul (2 * cN)))
        measurableSet_ball hpt
    have e1 : ∫ z in ball x (R / 16), (2 * H ^ 2 + 2 * cN * hs (fderiv ℝ w z)) =
        (∫ _z in ball x (R / 16), 2 * H ^ 2) + ∫ z in ball x (R / 16), 2 * cN * hs (fderiv ℝ w z) :=
      integral_add (integrableOn_const measure_ball_lt_top.ne) (h3.const_mul (2 * cN))
    rw [e1, setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, integral_const_mul,
      ← hΨ, hvol x (R / 16) hr] at hint
    have hΨr := hstep3 x hx2 (R / 16) hr hrR₁
    have hVpos : 0 < ω * (R / 16) ^ m := by positivity
    have h1 : ω * (R / 16) ^ m * ‖fderiv ℝ w x‖ ^ 2 ≤
        ω * (R / 16) ^ m * (2 * H ^ 2) + 2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) := by
      have : 2 * cN * Ψ x (R / 16) ≤ 2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) := by gcongr
      linarith
    have h2 : ‖fderiv ℝ w x‖ ^ 2 - 2 * H ^ 2 ≤
        2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) / (ω * (R / 16) ^ m) := by
      rw [le_div_iff₀ hVpos]
      linarith
    have e : 2 * cN * C₃ * (R / 16) ^ ((m : ℝ) - α) / (ω * (R / 16) ^ m) =
        2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) / (ω * (R / 16) ^ m) := by ring
    rw [hC₆]
    linarith
  -- Step 6 (second Campanato pass): `Φ(x, r) ≤ C₈ r^{m+2α}` on `B_{R/4}(x₀)`, `r ≤ R₁`
  have hstep6 : ∀ x ∈ ball x₀ (R / 4), ∀ r, 0 < r → r ≤ R₁ →
      Φ x r ≤ C₈ * r ^ ((m : ℝ) + 2 * α) := by
    intro x hx r hr hrR₁
    have hxd : dist x x₀ < R / 4 := hx
    have hgoodρ : ∀ ρ, ρ ≤ R₁ → closedBall x ρ ⊆ ball x₀ R := fun ρ hρ =>
      closedBall_subset_ball' (by rw [hR₁] at hρ; linarith)
    have hΨb : ∀ ρ, 0 < ρ → ρ ≤ R₁ → Ψ x ρ ≤ m * C₆ * ω * ρ ^ m := by
      intro ρ hρ hρR
      obtain ⟨-, -, h3⟩ := hgood x ρ (hgoodρ ρ hρR)
      rw [hΨ]
      calc ∫ z in ball x ρ, hs (fderiv ℝ w z) ≤ ∫ _z in ball x ρ, (m : ℝ) * C₆ :=
            setIntegral_mono_on h3 (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball
              (fun z hz => by
                have hzd : dist z x < ρ := hz
                have hz3 : z ∈ ball x₀ (3 * R / 8) := by
                  rw [mem_ball]; rw [hR₁] at hρR; linarith [dist_triangle z x x₀]
                calc hs (fderiv ℝ w z) ≤ m * ‖fderiv ℝ w z‖ ^ 2 := hs_le _
                  _ ≤ m * C₆ := by gcongr; exact hsup z hz3)
        _ = m * C₆ * ω * ρ ^ m := by rw [setIntegral_const, smul_eq_mul, hvol x ρ hρ]; ring
    have key := hIc (Φ x) R₁ ε₁ B₈ hε₁0.le hε₁c hB₈0
      (fun s _ _ => hΦ0 x s)
      (fun s ρ hs hsρ hρR => hΦmono x s ρ hs hsρ (hgoodρ ρ hρR))
      (fun s ρ hs hsρ hρR => by
        have hρ : 0 < ρ := hs.trans_le hsρ
        have h := (hcomp x ρ hρ hρR (by rw [hR₁] at hρR; linarith) s hs hsρ).1
        have hΨρ := hΨb ρ hρ hρR
        have e1 : ρ ^ (2 * α) * ρ ^ m = ρ ^ ((m : ℝ) + 2 * α) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hρ]; ring_nf
        have : A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) ≤
            B₈ * ρ ^ ((m : ℝ) + 2 * α) := by
          have h1 : ρ ^ (2 * α) * Ψ x ρ ≤ m * C₆ * ω * ρ ^ ((m : ℝ) + 2 * α) := by
            calc ρ ^ (2 * α) * Ψ x ρ ≤ ρ ^ (2 * α) * (m * C₆ * ω * ρ ^ m) := by gcongr
              _ = m * C₆ * ω * (ρ ^ (2 * α) * ρ ^ m) := by ring
              _ = m * C₆ * ω * ρ ^ ((m : ℝ) + 2 * α) := by rw [e1]
          rw [hB₈]
          calc A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))
              ≤ A₁ * K₁ * (m * C₆ * ω * ρ ^ ((m : ℝ) + 2 * α) + ρ ^ ((m : ℝ) + 2 * α)) := by
                gcongr
            _ = A₁ * K₁ * (m * C₆ * ω + 1) * ρ ^ ((m : ℝ) + 2 * α) := by ring
        linarith)
      r R₁ hr hrR₁ le_rfl
    have hΦR₁ : Φ x R₁ ≤ m * C₆ * ω * R₁ ^ m :=
      (hΦΨ x R₁ hR₁0 (hgoodρ R₁ le_rfl)).trans (hΨb R₁ hR₁0 le_rfl)
    rw [Real.div_rpow hr.le hR₁0.le] at key
    calc Φ x r ≤ cc * (r ^ ((m : ℝ) + 2 * α) / R₁ ^ ((m : ℝ) + 2 * α) * Φ x R₁
          + B₈ * r ^ ((m : ℝ) + 2 * α)) := key
      _ ≤ cc * (r ^ ((m : ℝ) + 2 * α) / R₁ ^ ((m : ℝ) + 2 * α) * (m * C₆ * ω * R₁ ^ m)
          + B₈ * r ^ ((m : ℝ) + 2 * α)) := by gcongr
      _ = C₈ * r ^ ((m : ℝ) + 2 * α) := by rw [hC₈]; ring
  -- Step 7: `Dw` is `α`-Hölder on `B_{R/4}(x₀)` at scale `R₁/2`
  have hhol2 : ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4), ‖x - y‖ ≤ R₁ / 2 →
      ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C₀'' * Real.sqrt (cN * C₈) * ‖x - y‖ ^ α :=
    hII'' (fderiv ℝ w) x₀ (R / 4) R₁ (cN * C₈) (by positivity) hR₁0 (by positivity)
      (hDw.mono (closedBall_subset_ball (by rw [hR₁]; linarith)))
      (fun x hx ρ hρ hρR => by
        have hxd : dist x x₀ < R / 4 := hx
        have hxr : closedBall x ρ ⊆ ball x₀ R :=
          closedBall_subset_ball' (by rw [hR₁] at hρR; linarith)
        calc _ ≤ cN * Φ x ρ := hΦop x ρ hxr
          _ ≤ cN * (C₈ * ρ ^ ((m : ℝ) + 2 * α)) := by gcongr; exact hstep6 x hx ρ hρ hρR
          _ = cN * C₈ * ρ ^ ((m : ℝ) + 2 * α) := by ring)
  -- conclusion
  have hbd : ∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ Real.sqrt C₆ := by
    intro x hx
    have hx' : x ∈ ball x₀ (3 * R / 8) := ball_subset_ball (by linarith) hx
    calc ‖fderiv ℝ w x‖ = Real.sqrt (‖fderiv ℝ w x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt C₆ := Real.sqrt_le_sqrt (hsup x hx')
  refine ⟨fun x hx => (hbd x hx).trans (le_max_left _ _), fun x hx y hy => ?_⟩
  by_cases hxy : ‖x - y‖ ≤ R₁ / 2
  · calc ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C₀'' * Real.sqrt (cN * C₈) * ‖x - y‖ ^ α :=
          hhol2 x hx y hy hxy
      _ ≤ max (Real.sqrt C₆) (max (C₀'' * Real.sqrt (cN * C₈)) (2 * Real.sqrt C₆ * (16 / R) ^ α))
          * ‖x - y‖ ^ α := by
          gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  · rw [not_le] at hxy
    have h3 : 1 ≤ (16 / R) ^ α * ‖x - y‖ ^ α := by
      rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]
      apply Real.one_le_rpow _ hα0.le
      rw [hR₁] at hxy
      rw [div_mul_eq_mul_div, le_div_iff₀ hR]
      linarith
    calc ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ ‖fderiv ℝ w x‖ + ‖fderiv ℝ w y‖ := norm_sub_le _ _
      _ ≤ 2 * Real.sqrt C₆ := by linarith [hbd x hx, hbd y hy]
      _ ≤ 2 * Real.sqrt C₆ * ((16 / R) ^ α * ‖x - y‖ ^ α) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = 2 * Real.sqrt C₆ * (16 / R) ^ α * ‖x - y‖ ^ α := by ring
      _ ≤ max (Real.sqrt C₆) (max (C₀'' * Real.sqrt (cN * C₈)) (2 * Real.sqrt C₆ * (16 / R) ^ α))
          * ‖x - y‖ ^ α := by
          gcongr; exact (le_max_right _ _).trans (le_max_right _ _)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
