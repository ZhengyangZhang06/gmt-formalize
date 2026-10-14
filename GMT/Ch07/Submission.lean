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

/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Total variation of a smooth function by duality with smooth test fields** (parent step 5:
`∫_W |Dw|` is bounded by the supremum of `∫ Dw · g` over `C^∞` fields `g` with compact support in
`W` and `|g| ≤ 1`).  Let `F = (Dw(·) eᵢ)ᵢ` be the gradient field of `w`, so `⟪F, h⟫ = Dw · h` and
`|F| = ‖Dw‖`; `F` is `C^∞`, and bounded by `M` on the compact set `closure W`.  Given `ε > 0`, the
smooth cut-off `rsd_mw_tfa_smooth_cutoff` (for `vol⌞W`) gives `χ ∈ C_c^∞(W)` with `0 ≤ χ ≤ 1` and
`vol (W ∩ {χ ≠ 1}) < ε`.  The field `g = χ F / √(|F|² + ε²)` is admissible, and
`Dw · g = ψ := χ |F|² / √(|F|² + ε²)`, which vanishes off `W`, so `∫_W ψ ≤ V`.  On `W`,
`|F| ≤ ψ + |M| 1_{χ ≠ 1} + ε` (if `χ = 1`, use `a ≤ a² / √(a² + ε²) + ε`; otherwise `|F| ≤ M`).
Integrating, `∫_W |F| ≤ V + (|M| + vol W) ε`, and `ε → 0` gives the claim. -/
theorem Submission.dor_lmb_fcd_cp_smooth_duality : ∀ (P : ℕ) (w : Euclid P → ℝ) (W : Set (Euclid P)) (V : ℝ), IsOpen W → Bornology.IsBounded W → ContDiff ℝ (⊤ : ℕ∞) w → (∀ g : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ W → (∀ y, ‖g y‖ ≤ 1) → ∫ y, fderiv ℝ w y (g y) ≤ V) → ∫ y in W, ‖fderiv ℝ w y‖ ≤ V := by
  intro P w W V hWo hWb hw hV
  -- Step 1: the gradient field `F y = (Dw(y) eᵢ)ᵢ`, with `⟪F y, h⟫ = Dw(y) h` and `‖F y‖ = ‖Dw(y)‖`
  set F : Euclid P → Euclid P :=
    fun y => WithLp.toLp 2 (fun i => fderiv ℝ w y (EuclideanSpace.single i 1))
  have hinner : ∀ y h, inner ℝ (F y) h = fderiv ℝ w y h := by
    intro y h
    have hh : h = ∑ i, h i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hh]
    simp [F, PiLp.inner_apply, map_sum, map_smul]
  have hFc : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ w y) :=
      hw.fderiv_right (by exact_mod_cast le_top)
    have : ContDiff ℝ (⊤ : ℕ∞) (fun y => (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)).symm
        (fun i => fderiv ℝ w y (EuclideanSpace.single i 1))) := by
      apply (LinearEquiv.toContinuousLinearEquiv
        (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)).symm).contDiff.comp
      exact contDiff_pi.2 fun i => hD.clm_apply contDiff_const
    simpa [F] using this
  have hFn : ∀ y, ‖F y‖ = ‖fderiv ℝ w y‖ := by
    intro y
    have hdual : InnerProductSpace.toDual ℝ (Euclid P) (F y) = fderiv ℝ w y := by
      ext h
      simp [InnerProductSpace.toDual_apply_apply, hinner]
    rw [← hdual, LinearIsometryEquiv.norm_map]
  simp_rw [← hFn]
  -- Step 2: `vol W < ∞`, `closure W` is compact, `‖F‖ ≤ M` on `closure W`, `‖F‖` integrable on `W`
  have hWm : volume W < ∞ := hWb.measure_lt_top
  have hWc : IsCompact (closure W) := hWb.isCompact_closure
  obtain ⟨M, hM⟩ := hWc.exists_bound_of_continuousOn hFc.continuous.continuousOn
  have hFi : IntegrableOn (fun y => ‖F y‖) W :=
    (hFc.continuous.norm.continuousOn.integrableOn_compact hWc).mono_set subset_closure
  -- the scalar inequality `a ≤ a² / S + ε` for `a ≤ S ≤ a + ε`
  have alg : ∀ ε a S : ℝ, 0 < S → a ≤ S → S ≤ a + ε → a ≤ S⁻¹ * a ^ 2 + ε := by
    intro ε a S hS haS hSa
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hS]
    nlinarith [sq_nonneg (S - a), mul_nonneg hS.le (sub_nonneg.2 hSa)]
  -- Step 3: for every `ε > 0`, `∫_W ‖F‖ ≤ V + (|M| + vol W) ε`
  have key : ∀ ε : ℝ, 0 < ε → ∫ y in W, ‖F y‖ ≤ V + (|M| + volume.real W) * ε := by
    intro ε hε
    -- the smooth cut-off `χ` with compact support in `W` and `vol (W ∩ {χ ≠ 1}) < ε`
    have hfin : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWm.ne
    obtain ⟨χ, hχ, hχc, hχW, hχ01, hχm⟩ :=
      Submission.rsd_mw_tfa_smooth_cutoff P (volume.restrict W) W hfin hWo
        (by rw [Measure.restrict_apply' hWo.measurableSet, compl_inter_self, measure_empty]) ε hε
    -- the regularised length `s = √(‖F‖² + ε²)` and the test field `g = χ s⁻¹ F`
    set s : Euclid P → ℝ := fun y => √(‖F y‖ ^ 2 + ε ^ 2)
    have hspos : ∀ y, 0 < s y := by
      intro y
      show 0 < √(‖F y‖ ^ 2 + ε ^ 2)
      positivity
    have hsc : ContDiff ℝ (⊤ : ℕ∞) s :=
      ((hFc.norm_sq ℝ).add contDiff_const).sqrt fun y =>
        (by positivity : (0 : ℝ) < ‖F y‖ ^ 2 + ε ^ 2).ne'
    have hFs : ∀ y, ‖F y‖ ≤ s y := by
      intro y
      show ‖F y‖ ≤ √(‖F y‖ ^ 2 + ε ^ 2)
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg ε))
    have hsF : ∀ y, s y ≤ ‖F y‖ + ε := by
      intro y
      show √(‖F y‖ ^ 2 + ε ^ 2) ≤ ‖F y‖ + ε
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_nonneg (norm_nonneg (F y)) hε.le]
    have hgc : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y • ((s y)⁻¹ • F y)) :=
      hχ.smul ((hsc.inv fun y => (hspos y).ne').smul hFc)
    have hgcs : HasCompactSupport (fun y => χ y • ((s y)⁻¹ • F y)) :=
      hχc.smul_right (f' := fun y => (s y)⁻¹ • F y)
    have hgt : tsupport (fun y => χ y • ((s y)⁻¹ • F y)) ⊆ W :=
      (tsupport_smul_subset_left χ fun y => (s y)⁻¹ • F y).trans hχW
    have hg1 : ∀ y, ‖χ y • ((s y)⁻¹ • F y)‖ ≤ 1 := by
      intro y
      have hc0 : 0 ≤ (s y)⁻¹ * ‖F y‖ := mul_nonneg (inv_nonneg.2 (hspos y).le) (norm_nonneg _)
      have hc1 : (s y)⁻¹ * ‖F y‖ ≤ 1 := by
        rw [inv_mul_le_iff₀ (hspos y), mul_one]
        exact hFs y
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hχ01 y).1,
        Real.norm_of_nonneg (inv_nonneg.2 (hspos y).le)]
      exact (mul_le_of_le_one_left hc0 (hχ01 y).2).trans hc1
    -- `Dw(y) (g y) = ψ y := χ y s(y)⁻¹ ‖F y‖²`; `ψ` vanishes off `W`, so `∫_W ψ ≤ V`
    set ψ : Euclid P → ℝ := fun y => χ y * ((s y)⁻¹ * ‖F y‖ ^ 2)
    have hDg : ∀ y, fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) = ψ y := by
      intro y
      show fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) = χ y * ((s y)⁻¹ * ‖F y‖ ^ 2)
      rw [← hinner, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hψ0W : ∀ y ∉ W, ψ y = 0 := by
      intro y hy
      have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hχW h)
      show χ y * ((s y)⁻¹ * ‖F y‖ ^ 2) = 0
      rw [h0, zero_mul]
    have hψV : ∫ y in W, ψ y ≤ V := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hψ0W]
      calc ∫ y, ψ y = ∫ y, fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) := by simp_rw [hDg]
        _ ≤ V := hV (fun y => χ y • ((s y)⁻¹ • F y)) hgc hgcs hgt hg1
    -- pointwise on `W`: `‖F‖ ≤ ψ + |M| 1_{χ ≠ 1} + ε`
    have hEm : MeasurableSet {x | χ x ≠ 1} :=
      (isOpen_ne_fun hχ.continuous continuous_const).measurableSet
    have hpt : ∀ y ∈ W,
        ‖F y‖ ≤ ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y + ε := by
      intro y hy
      by_cases hy1 : χ y = 1
      · have hyE : y ∉ {x | χ x ≠ 1} := fun h => h hy1
        rw [indicator_of_notMem hyE, add_zero]
        show ‖F y‖ ≤ χ y * ((s y)⁻¹ * ‖F y‖ ^ 2) + ε
        rw [hy1, one_mul]
        exact alg ε _ _ (hspos y) (hFs y) (hsF y)
      · have hyE : y ∈ {x | χ x ≠ 1} := hy1
        rw [indicator_of_mem hyE]
        have hψ0 : 0 ≤ ψ y :=
          mul_nonneg (hχ01 y).1 (mul_nonneg (inv_nonneg.2 (hspos y).le) (sq_nonneg _))
        have h1 := hM y (subset_closure hy)
        have h2 := le_abs_self M
        show ‖F y‖ ≤ ψ y + |M| + ε
        linarith
    -- integrate over `W`
    have hψc : Continuous ψ :=
      hχ.continuous.mul ((hsc.continuous.inv₀ fun y => (hspos y).ne').mul
        (hFc.continuous.norm.pow 2))
    have hψi : IntegrableOn ψ W :=
      (hψc.continuousOn.integrableOn_compact hWc).mono_set subset_closure
    have hEi : IntegrableOn (Set.indicator {x | χ x ≠ 1} fun _ => |M|) W :=
      (integrableOn_const hWm.ne).indicator hEm
    have hψEi : IntegrableOn (fun y => ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y) W :=
      hψi.add hEi
    have hεi : IntegrableOn (fun _ => ε) W := integrableOn_const hWm.ne
    have hEε : (volume.restrict W).real {x | χ x ≠ 1} ≤ ε :=
      (ENNReal.toReal_lt_of_lt_ofReal hχm).le
    calc ∫ y in W, ‖F y‖
        ≤ ∫ y in W, (ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y + ε) :=
          setIntegral_mono_on hFi (hψEi.add hεi) hWo.measurableSet hpt
      _ = (∫ y in W, ψ y) + (∫ y in W, Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y) +
            ∫ y in W, ε := by
          rw [integral_add hψEi hεi, integral_add hψi hEi]
      _ = (∫ y in W, ψ y) + (volume.restrict W).real {x | χ x ≠ 1} * |M| +
            volume.real W * ε := by
          rw [integral_indicator_const _ hEm, setIntegral_const, smul_eq_mul, smul_eq_mul]
      _ ≤ V + (|M| + volume.real W) * ε := by
          nlinarith [mul_le_mul_of_nonneg_right hEε (abs_nonneg M)]
  -- Step 4: let `ε → 0`
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hL : 0 ≤ volume.real W := measureReal_nonneg
  have hpos : 0 < |M| + volume.real W + 1 := by positivity
  have h1 := key (η / (|M| + volume.real W + 1)) (div_pos hη hpos)
  have h2 : (|M| + volume.real W) * (η / (|M| + volume.real W + 1)) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith
  linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Integer median of an integer-valued function on the open unit cube `Q₁ ⊆ ℝ^{m+1}` (Simon
Ch. 6, 5.1, (31) and (35)): some `β ∈ ℤ` has `Lⁿ(Q₁ ∩ {β ≤ u}) ≥ 1/2`, `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`
and `|β| ≤ 2 ∫_{Q₁} |u|`.  `β` is the least integer with `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`; integrality
makes `{β ≤ u}` the complement of `{u ≤ β - 1}`, and Chebyshev's inequality for `|u|` gives both
the existence of `β` and the bound. -/
theorem dor_lmb_fcd_cp_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | (β : ℝ) ≤ u y}) ∧ 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | u y ≤ (β : ℝ)}) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hZ hu
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ
  -- Step 0: `Q₁` is the preimage of the box `(0, 1)ⁿ` under the measure-preserving coordinate map,
  -- so it is measurable with `Lⁿ(Q₁) = 1`.
  have hbox : MeasurableSet (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQeq : Q = WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hQm : MeasurableSet Q := by
    rw [hQeq]
    exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable hbox
  have hQ1 : volume Q = 1 := by
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage hbox.nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp
  -- Work with the probability measure `μ = Lⁿ⌞Q₁`; `Lⁿ(Q₁ ∩ s) = μ(s)` for every set `s`.
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q with hμQ
  have hμ : ∀ s, volume (Q ∩ s) = μ s := fun s => by
    rw [hμQ, Measure.restrict_apply' hQm, inter_comm]
  have hμuniv : μ univ = 1 := by rw [← hμ, inter_univ, hQ1]
  have : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.one_lt_top⟩
  simp only [hμ]
  set I := ∫ y, |u y| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  -- Chebyshev: `ε μ({ε ≤ |u|}) ≤ ∫ |u| dμ`; no measurability of `u` is needed.
  have hmarkov : ∀ ε : ℝ, ε * μ.real {y | ε ≤ |u y|} ≤ I := fun ε =>
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
      (Integrable.abs (μ := μ) hu) ε
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
  -- Tails: for `N > 2 ∫ |u|`, `μ({N ≤ |u|}) < 1/2`.
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * I)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by linarith) hN
  have htail : μ {y | (N : ℝ) ≤ |u y|} < 1 / 2 := by
    have h1 := hmarkov N
    have h2 : μ.real {y | (N : ℝ) ≤ |u y|} < 1 / 2 := not_le.1 fun h => by nlinarith
    rw [← hhalf, measureReal_def] at h2
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by norm_num)).1 h2
  -- `μ(A) + μ(B) ≥ 1` and `μ(B) < 1/2` force `μ(A) ≥ 1/2`.
  have hcompl : ∀ a b : ℝ≥0∞, 1 ≤ a + b → b < 1 / 2 → 1 / 2 ≤ a := by
    intro a b hab hb
    refine not_lt.1 fun h => ?_
    have h' := ENNReal.add_lt_add h hb
    rw [ENNReal.add_halves] at h'
    exact absurd hab (not_le.2 h')
  -- Steps 1–2: the least integer `β` with `μ({u ≤ β}) ≥ 1/2` (Simon (31)).  It exists since
  -- `μ({u ≤ N}) ≥ 1/2` while `μ({u ≤ z}) < 1/2` for `z < -N`.
  have hS : ∃ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} := by
    refine ⟨N, hcompl _ (μ {y | u y ≤ ((N : ℤ) : ℝ)}ᶜ) (hμuniv ▸ measure_univ_le_add_compl _)
      (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail)⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, Int.cast_natCast] at hy ⊢
    exact hy.le.trans (le_abs_self _)
  have hSb : ∃ b : ℤ, ∀ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} → b ≤ z := by
    refine ⟨-N, fun z hz => not_lt.1 fun hlt => ?_⟩
    have hz' : (z : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hlt.le
    refine absurd hz (not_le.2 (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail))
    simp only [mem_ofPred_eq] at hy ⊢
    linarith [neg_abs_le (u y)]
  obtain ⟨β, hβ, hβmin⟩ := Int.exists_least_of_bdd hSb hS
  have hβ1 : μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 :=
    not_le.1 fun h => by have := hβmin (β - 1) h; omega
  -- Step 3: by integrality `{β ≤ u}ᶜ = {u ≤ β - 1}`, so `μ({β ≤ u}) ≥ 1 - μ({u ≤ β - 1}) ≥ 1/2`.
  have hup : 1 / 2 ≤ μ {y | (β : ℝ) ≤ u y} := by
    refine hcompl _ _ ?_ hβ1
    calc (1 : ℝ≥0∞) = μ univ := hμuniv.symm
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | (β : ℝ) ≤ u y}ᶜ := measure_univ_le_add_compl _
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} := by
        gcongr
        intro y hy
        simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hy ⊢
        obtain ⟨k, hk⟩ := hZ y
        rw [hk] at hy ⊢
        have hk' : k < β := by exact_mod_cast hy
        have hk'' : k ≤ β - 1 := by omega
        exact_mod_cast hk''
  refine ⟨β, hup, hβ, ?_⟩
  -- Step 4 (Simon (35)): `{|β| ≤ |u|}` contains `{β ≤ u}` (`β ≥ 0`) or `{u ≤ β}` (`β ≤ 0`), so it
  -- has measure `≥ 1/2`, and Chebyshev gives `|β| / 2 ≤ ∫ |u|`.
  have hbig : 1 / 2 ≤ μ {y | |(β : ℝ)| ≤ |u y|} := by
    rcases le_total 0 β with h0 | h0
    · refine hup.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (0 : ℝ) ≤ β := by exact_mod_cast h0
      rw [abs_of_nonneg h0']
      exact hy.trans (le_abs_self _)
    · refine hβ.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (β : ℝ) ≤ 0 := by exact_mod_cast h0
      rw [abs_of_nonpos h0']
      exact (neg_le_neg hy).trans (neg_le_abs _)
  have hbig' : 1 / 2 ≤ μ.real {y | |(β : ℝ)| ≤ |u y|} := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) hbig
    rwa [hhalf, ← measureReal_def] at h
  have h4 := hmarkov |(β : ℝ)|
  nlinarith [abs_nonneg (β : ℝ)]
/-- Deviation from a `θ`-median `β` is controlled by the double-integral oscillation (Simon Ch. 2,
Lemma 2.7, proof): `∫_W |v − β| ≤ (1 + θ⁻¹) |W|⁻¹ ∫_W ∫_W |v(x) − v(y)|`.  With the mean
`v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`; Markov's inequality on the half
`{β ≤ v}` or `{v ≤ β}` on the far side of `β` from `v̄` gives `|W| |v̄ − β| ≤ θ⁻¹ ∫_W |v − v̄|`. -/
theorem dor_lmb_fcd_cp_median_deviation : ∀ (P : ℕ) (W : Set (Euclid P)) (v : Euclid P → ℝ) (β θ : ℝ), MeasurableSet W → volume W ≠ ∞ → IntegrableOn v W → 0 < θ → θ * (volume W).toReal ≤ (volume (W ∩ {y | β ≤ v y})).toReal → θ * (volume W).toReal ≤ (volume (W ∩ {y | v y ≤ β})).toReal → ∫ y in W, |v y - β| ≤ (1 + θ⁻¹) * ((volume W).toReal)⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
  intro P W v β θ hW hWfin hv hθ hge hle
  -- `volume⌞W` is a finite measure; write `m = |W|`
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hWfin
  set m := (volume W).toReal
  -- Step 0: if `|W| = 0`, then `volume⌞W = 0` and both sides vanish
  rcases (ENNReal.toReal_nonneg : 0 ≤ m).eq_or_lt with hm | hm
  · have hW0 : volume W = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hm.symm).resolve_right hWfin
    simp [Measure.restrict_eq_zero.mpr hW0]
  -- Step 1: integrability; the partial integral is integrable by Fubini
  have hvi : Integrable v (volume.restrict W) := hv
  have hint : ∀ c : ℝ, Integrable (fun x => |v x - c|) (volume.restrict W) := fun c =>
    (hvi.sub (integrable_const c)).abs
  have hprod : Integrable (fun p : Euclid P × Euclid P => |v p.1 - v p.2|)
      ((volume.restrict W).prod (volume.restrict W)) :=
    ((hvi.comp_fst _).sub (hvi.comp_snd _)).abs
  have hG : Integrable (fun x => ∫ y in W, |v x - v y|) (volume.restrict W) :=
    hprod.integral_prod_left
  -- Step 2: with the mean `v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`
  set vbar := m⁻¹ * ∫ y in W, v y with hvbar
  have hpt : ∀ x, |v x - vbar| ≤ m⁻¹ * ∫ y in W, |v x - v y| := by
    intro x
    have h1 : ∫ y in W, (v x - v y) = m * v x - ∫ y in W, v y := by
      rw [integral_sub (integrable_const _) hvi, integral_const, measureReal_restrict_apply_univ,
        smul_eq_mul]
      rfl
    have h2 : v x - vbar = m⁻¹ * ∫ y in W, (v x - v y) := by
      rw [h1, hvbar, mul_sub, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
    rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hm)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hm.le)
  have hJ : ∫ x in W, |v x - vbar| ≤ m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
    rw [← integral_const_mul]
    exact integral_mono (hint vbar) (hG.const_mul _) hpt
  -- Step 3: `|v − v̄| ≥ |β − v̄|` on the half on the far side of `β`, which has measure `≥ θ|W|`
  set I := ∫ x in W, |v x - vbar| with hI
  have hmeas : θ * m ≤ (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} := by
    rcases le_total vbar β with hb | hb
    · refine hge.trans ?_
      rw [show (volume (W ∩ {y | β ≤ v y})).toReal = (volume.restrict W).real {y | β ≤ v y} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : β ≤ v x) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (by linarith)]
      linarith
    · refine hle.trans ?_
      rw [show (volume (W ∩ {y | v y ≤ β})).toReal = (volume.restrict W).real {y | v y ≤ β} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : v x ≤ β) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonpos (sub_nonpos.mpr hb), abs_of_nonpos (by linarith)]
      linarith
  -- Markov's inequality for `|v − v̄|` at level `|β − v̄|`
  have hM : |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} ≤ I :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hint vbar) _
  have hmed : m * |vbar - β| ≤ θ⁻¹ * I := by
    rw [abs_sub_comm, le_inv_mul_iff₀ hθ]
    calc θ * (m * |β - vbar|) = |β - vbar| * (θ * m) := by ring
      _ ≤ |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} :=
        mul_le_mul_of_nonneg_left hmeas (abs_nonneg _)
      _ ≤ I := hM
  -- Step 4: triangle inequality `|v − β| ≤ |v − v̄| + |v̄ − β|`
  have htri : ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := by
    have h3 : ∫ y in W, (|v y - vbar| + |vbar - β|) = I + m * |vbar - β| := by
      rw [integral_add (hint vbar) (integrable_const _), integral_const,
        measureReal_restrict_apply_univ, smul_eq_mul]
      rfl
    rw [← h3]
    exact integral_mono (hint β) ((hint vbar).add (integrable_const _))
      fun y => abs_sub_le (v y) vbar β
  calc ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := htri
    _ ≤ I + θ⁻¹ * I := by linarith
    _ = (1 + θ⁻¹) * I := by ring
    _ ≤ (1 + θ⁻¹) * (m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y|) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (1 + θ⁻¹) * m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by ring
/-- Fubini identity for mixed points on the cube `Q_δ = {y | ∀ i, δ < y i < 1 - δ}`: if `a_k(x, y)`
takes the coordinates `j < k` from `y` and the others from `x`, then
`∫_{Q_δ} ∫_{Q_δ} h(a_k(x, y)) dy dx = vol(Q_δ) ∫_{Q_δ} h`.  The swap `σ` exchanging `x_j` and `y_j`
for `j < k` is an involution preserving `vol ⊗ vol` (a factorwise product of swaps and identities)
and `Q_δ × Q_δ`, so Fubini on the finite measure space `Q_δ × Q_δ` turns the left side into
`∫_{Q_δ × Q_δ} h(x)`. -/
theorem dor_lmb_fcd_cp_mixed_point_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) = (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- the coordinate swap on `(Fin (m+1) → ℝ)²`
  have hτ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      ((fun j => if j < k then p.2 j else p.1 j), (fun j => if j < k then p.1 j else p.2 j)))
      (volume.prod volume) (volume.prod volume) := by
    set A := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1))
    have hA : MeasurePreserving A (Measure.pi fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
        ((volume : Measure (Fin (m + 1) → ℝ)).prod volume) :=
      measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1)) (fun _ => volume) (fun _ => volume)
    let f : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ := fun j => if j < k then Prod.swap else id
    have hf : ∀ j, MeasurePreserving (f j) ((volume : Measure ℝ).prod volume)
        ((volume : Measure ℝ).prod volume) := by
      intro j
      by_cases hj : j < k
      · simp only [f, hj, ite_true]
        exact Measure.measurePreserving_swap
      · simp only [f, hj, ite_false]
        exact MeasurePreserving.id _
    have hP := measurePreserving_pi (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
      (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume) hf
    have hcomp := (hA.comp hP).comp hA.symm
    convert hcomp using 1
    funext p
    ext j
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  -- the same swap on `Euclid (m+1) × Euclid (m+1)`
  set σ : Euclid (m + 1) × Euclid (m + 1) → Euclid (m + 1) × Euclid (m + 1) := fun p =>
    (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j),
      WithLp.toLp 2 (fun j => if j < k then p.1 j else p.2 j)) with hσdef
  have hσ : MeasurePreserving σ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (PiLp.volume_preserving_ofLp (Fin (m + 1)))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (PiLp.volume_preserving_toLp (Fin (m + 1)))
    have := (h2.comp hτ).comp h1
    convert this using 1
    funext p
    rfl
  have hσσ : ∀ p, σ (σ p) = p := by
    intro p
    ext j
    · by_cases hj : j < k <;> simp [hσdef, hj]
    · by_cases hj : j < k <;> simp [hσdef, hj]
  let σe : (Euclid (m + 1) × Euclid (m + 1)) ≃ᵐ (Euclid (m + 1) × Euclid (m + 1)) :=
    { toFun := σ
      invFun := σ
      left_inv := hσσ
      right_inv := hσσ
      measurable_toFun := hσ.measurable
      measurable_invFun := hσ.measurable }
  have hemb : MeasurableEmbedding σ := σe.measurableEmbedding
  have hpre : σ ⁻¹' (Q ×ˢ Q) = Q ×ˢ Q := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hσdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
  have hQm : MeasurableSet Q := by
    have : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y; simp [hQ]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (by fun_prop)).inter (measurableSet_lt (by fun_prop) measurable_const)
  have hσQ : MeasurePreserving σ ((volume.prod volume).restrict (Q ×ˢ Q))
      ((volume.prod volume).restrict (Q ×ˢ Q)) := by
    have := hσ.restrict_preimage_emb hemb (Q ×ˢ Q)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict Q) =
      ((volume : Measure (Euclid (m + 1))).prod volume).restrict (Q ×ˢ Q) :=
    Measure.prod_restrict Q Q
  have hQfin : volume Q ≠ ∞ := by
    have hb : Bornology.IsBounded Q := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))]
      refine ⟨Real.sqrt (((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2), fun y hy => ?_⟩
      rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (|δ| + |1 - δ|) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := hy i
            rw [Real.norm_eq_abs]
            have h1 : |y i| ≤ |δ| + |1 - δ| := by
              rw [abs_le]
              constructor <;> cases abs_cases δ <;> cases abs_cases (1 - δ) <;> linarith [this.1, this.2]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = ((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2 := by simp
    exact hb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2 hQfin
  -- integrability of `p ↦ h p.1` on `Q × Q`
  have hint1 : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => h p.1)
      ((volume.restrict Q).prod (volume.restrict Q)) := hh.comp_fst (volume.restrict Q)
  have hint2 : Integrable (fun p => h (σ p).1) ((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr] at hint1 ⊢
    exact (hσQ.integrable_comp_emb hemb).2 hint1
  -- compute
  have e1 : ∫ x in Q, ∫ y in Q, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) =
      ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr]
    exact hσQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      (volume Q).toReal * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    rw [integral_const_mul]
  rw [e1, e2, e3]
/-- Fubini along the `k`-th coordinate of the cube `Q_δ = (δ, 1 − δ)^{m+1}` (Simon Ch. 2,
proof of Lemma 2.7): for `h` integrable on `Q_δ`,
`∫_{Q_δ} ∫_δ^{1−δ} h(x[k ↦ t]) dt dx = (1 − 2δ) ∫_{Q_δ} h`.  The slice swap
`ρ(x, t) = (x[k ↦ t], x_k)` is a measure-preserving involution of `Euclid (m + 1) × ℝ` that maps
`Q_δ × (δ, 1 − δ)` onto itself. -/
theorem dor_lmb_fcd_cp_slice_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ t in Ioo δ (1 - δ), h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) = (1 - 2 * δ) * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- Step 0: if `δ ≥ 1/2` the cube is empty and both sides vanish.
  rcases le_or_gt (1 / 2) δ with hδ | hδ
  · have hQe : Q = ∅ := by
      ext y
      simp only [hQ, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, fun h0 => by linarith [h0.1, h0.2]⟩
    simp [hQe]
  -- Step 2: the slice swap on `(Fin (m + 1) → ℝ) × ℝ` preserves volume.  Under
  -- `piFinSuccAbove` it is `((a, b), c) ↦ ((c, b), a)`, a composition of swaps and
  -- reassociations.
  have hρ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × ℝ => (Function.update p.1 k p.2, p.1 k))
      (volume.prod volume) (volume.prod volume) := by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    have he : MeasurePreserving e (volume : Measure (Fin (m + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    set T : (ℝ × (Fin m → ℝ)) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ := fun q => ((q.2, q.1.2), q.1.1) with hTdef
    have hT : MeasurePreserving T (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) := by
      have s1 : MeasurePreserving (Prod.map Prod.swap id : (ℝ × (Fin m → ℝ)) × ℝ → ((Fin m → ℝ) × ℝ) × ℝ)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have s2 := measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)
      have s3 : MeasurePreserving (Prod.map id Prod.swap : (Fin m → ℝ) × (ℝ × ℝ) → (Fin m → ℝ) × (ℝ × ℝ))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume)) :=
        (MeasurePreserving.id _).prod Measure.measurePreserving_swap
      have s4 := (measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)).symm
      have s5 : MeasurePreserving (Prod.map Prod.swap id : ((Fin m → ℝ) × ℝ) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have := s5.comp (s4.comp (s3.comp (s2.comp s1)))
      convert this using 1
      funext q
      rfl
    have hE2 : MeasurePreserving (e.prodCongr (MeasurableEquiv.refl ℝ))
        ((volume : Measure (Fin (m + 1) → ℝ)).prod (volume : Measure ℝ))
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
      he.prod (MeasurePreserving.id _)
    have hfull := (hE2.symm.comp hT).comp hE2
    convert hfull using 1
    funext p
    ext j
    · simp only [Function.comp, e, T]
      simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
    · simp [e, T, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
  -- Steps 1–2: the same map `ρ` on `Euclid (m + 1) × ℝ` (via `ofLp`/`toLp`) is a
  -- measure-preserving involution, hence a measurable embedding.
  set ρ : Euclid (m + 1) × ℝ → Euclid (m + 1) × ℝ := fun p =>
    (WithLp.toLp 2 (Function.update (WithLp.ofLp p.1) k p.2), p.1 k) with hρdef
  have hρE : MeasurePreserving ρ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have := (h2.comp hρ).comp h1
    convert this using 1
    funext p
    rfl
  have hρρ : ∀ p, ρ (ρ p) = p := by
    intro p
    ext j
    · by_cases hj : j = k
      · subst hj; simp [hρdef]
      · simp [hρdef]
    · simp [hρdef]
  let ρe : (Euclid (m + 1) × ℝ) ≃ᵐ (Euclid (m + 1) × ℝ) :=
    { toFun := ρ
      invFun := ρ
      left_inv := hρρ
      right_inv := hρρ
      measurable_toFun := hρE.measurable
      measurable_invFun := hρE.measurable }
  have hemb : MeasurableEmbedding ρ := ρe.measurableEmbedding
  -- Step 3: `ρ⁻¹(Q × I) = Q × I`, so `ρ` preserves `(vol⌞Q) ⊗ (vol⌞I)`.
  set I : Set ℝ := Ioo δ (1 - δ) with hI
  have hpre : ρ ⁻¹' (Q ×ˢ I) = Q ×ˢ I := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hρdef, hI, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · simpa using h1 k
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · exact h1 k
  have hρQ : MeasurePreserving ρ ((volume.prod volume).restrict (Q ×ˢ I))
      ((volume.prod volume).restrict (Q ×ˢ I)) := by
    have := hρE.restrict_preimage_emb hemb (Q ×ˢ I)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict I) =
      ((volume : Measure (Euclid (m + 1))).prod (volume : Measure ℝ)).restrict (Q ×ˢ I) :=
    Measure.prod_restrict Q I
  -- Step 4: `(x, t) ↦ h x` and `(x, t) ↦ h (x[k ↦ t])` are integrable on `Q × I`.
  have hfinI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.2 (by simp [hI])
  have hint1 : Integrable (fun p : Euclid (m + 1) × ℝ => h p.1)
      ((volume.restrict Q).prod (volume.restrict I)) := hh.comp_fst (volume.restrict I)
  have hint2 : Integrable (fun p => h (ρ p).1) ((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr] at hint1 ⊢
    exact (hρQ.integrable_comp_emb hemb).2 hint1
  -- Step 5: Fubini, the change of variables `ρ`, and `vol(I) = 1 − 2δ`.
  have e1 : ∫ x in Q, ∫ t in I, h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) =
      ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr]
    exact hρQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      (1 - 2 * δ) * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hI, Real.volume_Ioo]
    rw [integral_const_mul, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [e1, e2, e3]
/-- One coordinate step of the Poincaré inequality on the cube `Q_δ`: the points
`a_k(x, y)`, `b_k(x, y)` differ only in the `k`-th coordinate, so by the fundamental theorem of
calculus `|v(a_k) − v(b_k)| ≤ Φ(a_k) := ∫_{(δ, 1−δ)} |∂_k v(a_k[t])| dt`.  Integrating, the
mixed-point identity gives `∫∫ Φ(a_k) = |Q_δ| ∫_{Q_δ} Φ` and the slice identity gives
`∫_{Q_δ} Φ = (1 − 2δ) ∫_{Q_δ} |∂_k v|`. -/
theorem dor_lmb_fcd_cp_coordinate_step : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ) (k : Fin (m + 1)), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) - v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤ (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |fderiv ℝ v x (EuclideanSpace.single k 1)| := by
  intro m v δ k hv _ _
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- `Q` is open, and contained in the compact cube `K = [δ, 1 − δ]^{m+1}`.
  have hQo : IsOpen Q := by
    have hQi : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y
      simp [hQ]
    rw [hQi]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  set K : Set (Euclid (m + 1)) := WithLp.toLp 2 '' Set.pi univ fun _ => Icc δ (1 - δ)
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hQK : Q ⊆ K := fun y hy => ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
  -- `∂_k v` is continuous.
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hgc : Continuous fun p : Euclid (m + 1) => |fderiv ℝ v p (EuclideanSpace.single k 1)| :=
    (hfd.clm_apply continuous_const).abs
  -- `p[t]`, the point `p` with `k`-th coordinate `t`, is `p + (t − p_k) e_k`.
  have hupd : ∀ (p : Euclid (m + 1)) (t : ℝ),
      WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t) =
        p + (t - p k) • EuclideanSpace.single k (1 : ℝ) := by
    intro p t
    ext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  -- `Φ(p) = ∫_{(δ, 1−δ)} |∂_k v(p[t])| dt` is continuous.
  set Φ : Euclid (m + 1) → ℝ := fun p => ∫ t in Ioo δ (1 - δ),
    |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t)) (EuclideanSpace.single k 1)|
    with hΦ
  have hΦc : Continuous Φ := by
    have hGc : Continuous fun z : Euclid (m + 1) × ℝ =>
        |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp z.1) k z.2))
          (EuclideanSpace.single k 1)| := by
      simp_rw [hupd]
      exact hgc.comp (by fun_prop)
    have hΦ' : Φ = fun p => ∫ t in Icc δ (1 - δ),
        |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t))
          (EuclideanSpace.single k 1)| := by
      funext p
      exact integral_Icc_eq_integral_Ioo.symm
    rw [hΦ']
    exact continuous_parametric_integral_of_continuous
      (f := fun p t => |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t))
        (EuclideanSpace.single k 1)|) hGc isCompact_Icc
  -- `(x, y) ↦ Φ(a_k(x, y))` is continuous.
  have hac : Continuous fun z : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j) : Euclid (m + 1)) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => by fun_prop) (fun _ => by fun_prop)
  have hFc : Continuous fun z : Euclid (m + 1) × Euclid (m + 1) =>
      Φ (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j)) := hΦc.comp hac
  -- Integrability: continuous functions are integrable on the compact `K ⊇ Q`.
  have hI1 : IntegrableOn (fun p => |fderiv ℝ v p (EuclideanSpace.single k 1)|) Q :=
    (hgc.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hI2 : IntegrableOn Φ Q := (hΦc.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hI3 : ∀ x : Euclid (m + 1), IntegrableOn
      (fun y : Euclid (m + 1) => Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j))) Q :=
    fun x => ((hFc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      hKc).mono_set hQK
  have hI4 : IntegrableOn (fun x : Euclid (m + 1) =>
      ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j))) Q := by
    have hprod : Integrable (fun z : Euclid (m + 1) × Euclid (m + 1) =>
        Φ (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j)))
        ((volume.restrict Q).prod (volume.restrict Q)) := by
      rw [Measure.prod_restrict]
      exact (hFc.continuousOn.integrableOn_compact (hKc.prod hKc)).mono_set (prod_mono hQK hQK)
    exact hprod.integral_prod_left
  -- Step 1: the fundamental theorem of calculus along `t ↦ a_k[t]`.
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q,
      |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤
        Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := by
    intro x hx y hy
    set a : Euclid (m + 1) := WithLp.toLp 2 (fun j => if j < k then y j else x j) with ha
    set ℓ : ℝ → Euclid (m + 1) := fun t => a + (t - a k) • EuclideanSpace.single k (1 : ℝ)
      with hℓ
    have hak : a k = x k := by simp [ha]
    have hℓx : ℓ (x k) = a := by simp [hℓ, hak]
    have hℓy : ℓ (y k) = WithLp.toLp 2 (fun j => if j ≤ k then y j else x j) := by
      ext j
      rcases lt_trichotomy j k with h | h | h
      · simp [hℓ, ha, h, le_of_lt h, ne_of_lt h]
      · subst h
        simp [hℓ, ha]
      · simp [hℓ, ha, not_lt.2 (le_of_lt h), not_le.2 h, (ne_of_lt h).symm]
    have hℓd : ∀ t, HasDerivAt ℓ (EuclideanSpace.single k (1 : ℝ)) t := by
      intro t
      have := (((hasDerivAt_id' t).sub_const (a k)).smul_const
        (EuclideanSpace.single k (1 : ℝ))).const_add a
      rw [one_smul] at this
      exact this
    have hderiv : ∀ t, HasDerivAt (fun t => v (ℓ t))
        (fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)) t := fun t =>
      ((hv.differentiable one_ne_zero (ℓ t)).hasFDerivAt).comp_hasDerivAt t (hℓd t)
    have hcont : Continuous fun t => fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1) :=
      (hfd.comp (by fun_prop)).clm_apply continuous_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable (x k) (y k))
    simp only [hℓx, hℓy] at hftc
    have hsub : Set.uIoc (x k) (y k) ⊆ Ioo δ (1 - δ) := by
      intro t ht
      rcases Set.mem_uIoc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [(hx k).1], by linarith [(hy k).2]⟩
      · exact ⟨by linarith [(hy k).1], by linarith [(hx k).2]⟩
    rw [abs_sub_comm, ← hftc]
    calc |∫ t in x k..y k, fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)|
        = ‖∫ t in x k..y k, fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ (t : ℝ) in Set.uIoc (x k) (y k), ‖fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ (t : ℝ) in Ioo δ (1 - δ), ‖fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          setIntegral_mono_set
            (hcont.norm.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
            (Eventually.of_forall fun t => norm_nonneg _) hsub.eventuallyLE
      _ = Φ a := by
          simp only [hΦ, hℓ, ← hupd, Real.norm_eq_abs]
  -- Step 3: integrate the pointwise bound.
  have hstep : ∫ x in Q, ∫ y in Q, |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤
      ∫ x in Q, ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun x => integral_nonneg fun y => abs_nonneg _) hI4 ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hI3 x) ?_
    filter_upwards [ae_restrict_mem hQm] with y hy
    exact hpt x hx y hy
  -- Steps 4–6: the mixed-point and slice identities.
  calc _ ≤ ∫ x in Q, ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := hstep
    _ = (volume Q).toReal * ∫ x in Q, Φ x :=
        Submission.dor_lmb_fcd_cp_mixed_point_integral m δ k Φ hI2
    _ = (volume Q).toReal *
        ((1 - 2 * δ) * ∫ x in Q, |fderiv ℝ v x (EuclideanSpace.single k 1)|) := by
        congr 1
        exact Submission.dor_lmb_fcd_cp_slice_integral m δ k
          (fun p => |fderiv ℝ v p (EuclideanSpace.single k 1)|) hI1
    _ = _ := by ring
/-- **Poincaré inequality on the cube `Q_δ = (δ, 1 − δ)^{m+1}` for `C¹` functions** (the "usual
Poincaré inequality for smooth functions" invoked in Simon Ch. 2, proof of Lemma 2.7, here on a
cube of side `1 − 2δ`):
`∫_Q ∫_Q |v(x) − v(y)| dy dx ≤ (m + 1)(1 − 2δ) Lⁿ(Q) ∫_Q ‖Dv‖`.  Along the coordinate path from
`x` to `y`, `v x − v y` telescopes into the `m + 1` coordinate steps bounded by
`dor_lmb_fcd_cp_coordinate_step`; every integrand is continuous on the compact cube
`[δ, 1 − δ]^{m+1} ⊇ Q`, hence integrable, and `|Dv(x) eₖ| ≤ ‖Dv(x)‖`. -/
theorem dor_lmb_fcd_cp_smooth_poincare : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v x - v y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v δ hv hδ0 hδ
  -- Step 1: telescoping along the coordinate path `W₀ = x, …, W_{m+1} = y`
  have htel : ∀ x y : Euclid (m + 1), v x - v y = ∑ k : Fin (m + 1),
      (v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))) := by
    intro x y
    set W : ℕ → Euclid (m + 1) :=
      fun n => WithLp.toLp 2 (fun j => if (j : ℕ) < n then y j else x j) with hW
    have h0 : W 0 = x := by
      simp [hW]
    have hN : W (m + 1) = y := by
      have hlt : ∀ j : Fin (m + 1), (j : ℕ) < m + 1 := fun j => j.is_lt
      simp only [hW, hlt, ite_true]
    have hk : ∀ k : Fin (m + 1),
        v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
          v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j)) = v (W k) - v (W (k + 1)) := by
      intro k
      have e1 : (fun j : Fin (m + 1) => if j < k then y j else x j) =
          (fun j : Fin (m + 1) => if (j : ℕ) < (k : ℕ) then y j else x j) := by
        funext j
        simp only [Fin.lt_def]
      have e2 : (fun j : Fin (m + 1) => if j ≤ k then y j else x j) =
          (fun j : Fin (m + 1) => if (j : ℕ) < (k : ℕ) + 1 then y j else x j) := by
        funext j
        simp only [Fin.le_iff_val_le_val, Nat.lt_succ_iff]
      rw [e1, e2]
    rw [Finset.sum_congr rfl (fun k _ => hk k),
      Fin.sum_univ_eq_sum_range (fun n => v (W n) - v (W (n + 1))) (m + 1),
      Finset.sum_range_sub', h0, hN]
  have habs : ∀ x y : Euclid (m + 1), |v x - v y| ≤ ∑ k : Fin (m + 1),
      |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| := by
    intro x y
    rw [htel x y]
    exact Finset.abs_sum_le_sum_abs _ _
  -- Step 2: integrability; `Q_δ` lies in the compact cube `K = [δ, 1 − δ]^{m+1}`
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  set K : Set (Euclid (m + 1)) := {y | ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ}
  have hQK : Q ⊆ K := fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hKc : IsCompact K := by
    have hKeq : K = WithLp.toLp 2 '' Set.pi univ (fun _ : Fin (m + 1) => Icc δ (1 - δ)) := by
      ext y
      constructor
      · intro hy
        exact ⟨WithLp.ofLp y, fun i _ => hy i, rfl⟩
      · rintro ⟨z, hz, rfl⟩ i
        exact hz i (mem_univ i)
    rw [hKeq]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hint : ∀ g : Euclid (m + 1) → ℝ, Continuous g → IntegrableOn g Q :=
    fun g hg => (hg.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hint2 : ∀ F : Euclid (m + 1) × Euclid (m + 1) → ℝ, Continuous F →
      Integrable F ((volume.restrict Q).prod (volume.restrict Q)) := by
    intro F hF
    rw [Measure.prod_restrict]
    exact (hF.continuousOn.integrableOn_compact (hKc.prod hKc)).mono_set (prod_mono hQK hQK)
  -- the coordinate points depend continuously on `(x, y)`
  have hlt : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j) : Euclid (m + 1)) := by
    intro k
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_snd)
      fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have hle : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j ≤ k then p.2 j else p.1 j) : Euclid (m + 1)) := by
    intro k
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_snd)
      fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have hF0 : Continuous fun p : Euclid (m + 1) × Euclid (m + 1) => |v p.1 - v p.2| :=
    ((hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)).abs
  have hFk : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      |v (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then p.2 j else p.1 j))| :=
    fun k => ((hv.continuous.comp (hlt k)).sub (hv.continuous.comp (hle k))).abs
  have hfac : 0 ≤ (1 - 2 * δ) * (volume Q).toReal :=
    mul_nonneg (by linarith) ENNReal.toReal_nonneg
  -- Steps 3–4: integrate the telescoping bound, apply `coordinate_step`, and `|Dv eₖ| ≤ ‖Dv‖`
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      ≤ ∫ x in Q, ∑ k : Fin (m + 1), ∫ y in Q,
          |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
            v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| := by
        refine integral_mono (hint2 _ hF0).integral_prod_left
          (integrable_finsetSum _ fun k _ => (hint2 _ (hFk k)).integral_prod_left) fun x => ?_
        have hx : ∀ k : Fin (m + 1), IntegrableOn (fun y : Euclid (m + 1) =>
            |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
              v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))|) Q :=
          fun k => hint _ ((hFk k).comp (Continuous.prodMk_right x))
        exact (integral_mono (hint _ (hF0.comp (Continuous.prodMk_right x)))
          (integrable_finsetSum _ fun k _ => hx k) (habs x)).trans_eq
          (integral_finsetSum _ fun k _ => hx k)
    _ = ∑ k : Fin (m + 1), ∫ x in Q, ∫ y in Q,
          |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
            v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| :=
        integral_finsetSum _ fun k _ => (hint2 _ (hFk k)).integral_prod_left
    _ ≤ ∑ k : Fin (m + 1), (1 - 2 * δ) * (volume Q).toReal *
          ∫ x in Q, |fderiv ℝ v x (EuclideanSpace.single k 1)| :=
        Finset.sum_le_sum fun k _ => Submission.dor_lmb_fcd_cp_coordinate_step m v δ k hv hδ0 hδ
    _ ≤ ∑ _k : Fin (m + 1), (1 - 2 * δ) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ hfac
        have hDv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
        refine integral_mono (hint _ (hDv.clm_apply continuous_const).abs) (hint _ hDv.norm)
          fun x => ?_
        calc |fderiv ℝ v x (EuclideanSpace.single k 1)|
            = ‖fderiv ℝ v x (EuclideanSpace.single k 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ v x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ := (fderiv ℝ v x).le_opNorm _
          _ = ‖fderiv ℝ v x‖ := by simp
    _ = ((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
/-- Mollification by an even `C¹` kernel `η` with compact support commutes with `D` and is
self-adjoint: `∫ D(η * u)(x)(s x) dx = −∫ u div(η * s)` for integrable `u`, `s` (Simon Ch. 2,
Lemma 2.5).  Both derivatives are convolutions with the odd, bounded `Dη`, and Fubini applies to
`Dη(x − z)(s x) u(z)`, which is dominated by `C ‖s x‖ |u z|`. -/
theorem codim1_rdo_dg_sp_mollifier_adjoint : ∀ (P : ℕ) (η u : Euclid P → ℝ) (s : Euclid P → Euclid P), ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, η (-z) = η z) → Integrable u → Integrable s → ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z : Euclid P →ₗ[ℝ] Euclid P) := by
  intro P η u s hη hηc heven hu hs
  -- Step 0: `Dη` is continuous with compact support, hence bounded by some `C`.
  have hDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDcs : HasCompactSupport (fderiv ℝ η) := hηc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 1: `η` is even, so `Dη` is odd (chain rule for `η = η ∘ (−id)`).
  have hodd : ∀ y, fderiv ℝ η (-y) = -fderiv ℝ η y := by
    intro y
    have h1 : HasFDerivAt (η ∘ fun z => -z)
        ((fderiv ℝ η (-y)).comp (-ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hη.differentiable one_ne_zero) (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
    rw [show (η ∘ fun z => -z) = η from funext heven] at h1
    ext v
    rw [h1.fderiv]
    simp
  -- Step 2: `D(η * u)(x) = (Dη * u)(x)`, so `D(η * u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz`.
  have hLHS : ∀ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) =
      ∫ z, fderiv ℝ η (x - z) (s x) * u z := by
    intro x
    rw [(hηc.hasFDerivAt_convolution_left _ hη hu.locallyIntegrable x).fderiv, convolution_eq_swap,
      ContinuousLinearMap.integral_apply
        ((hDcs.convolutionExists_left _ hDc hu.locallyIntegrable x).integrable_swap)]
    simp
  -- Step 3: `div(η * s)(z) = trace D(η * s)(z) = ∫ Dη(z − x)(s x) dx`: the trace `T` is a
  -- continuous linear functional, and the trace of the rank-one map `v ↦ a(v) w` is `a(w)`.
  have hRHS : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
        Euclid P →ₗ[ℝ] Euclid P) = ∫ x, fderiv ℝ η (z - x) (s x) := by
    let T : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid P) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have hTA : ∀ A : Euclid P →L[ℝ] Euclid P,
        T A = LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) := fun A => rfl
    have hrk : ∀ (a : Euclid P →L[ℝ] ℝ) (w : Euclid P), T (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w) = a w := by
      intro a w
      have h : ((ContinuousLinearMap.precompL (Euclid P)
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w :
            Euclid P →L[ℝ] Euclid P) : Euclid P →ₗ[ℝ] Euclid P) =
          (a : Euclid P →ₗ[ℝ] ℝ).smulRight w := by
        ext v
        simp
      rw [hTA, h, LinearMap.trace_smulRight]
      rfl
    intro z
    rw [(hηc.hasFDerivAt_convolution_left _ hη hs.locallyIntegrable z).fderiv, convolution_eq_swap]
    have hT := ContinuousLinearMap.integral_comp_comm T
      ((hDcs.convolutionExists_left (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P)) hDc
          hs.locallyIntegrable z).integrable_swap)
    simp_rw [hrk] at hT
    exact hT.symm
  -- Step 4: Fubini for `H(x, z) = Dη(x − z)(s x) u(z)`, dominated by `C ‖s x‖ |u z|`.
  have hint : Integrable (uncurry fun x z => fderiv ℝ η (x - z) (s x) * u z)
      ((volume : Measure (Euclid P)).prod volume) := by
    refine Integrable.mono' ((hs.norm.mul_prod hu.norm).const_mul C) ?_ (Eventually.of_forall ?_)
    · exact ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
        hs.aestronglyMeasurable.comp_fst
        (hDc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hu.aestronglyMeasurable.comp_snd
    · rintro ⟨x, z⟩
      simp only [uncurry_apply_pair, norm_mul]
      calc ‖fderiv ℝ η (x - z) (s x)‖ * ‖u z‖ ≤ (C * ‖s x‖) * ‖u z‖ := by
            gcongr
            exact ((fderiv ℝ η (x - z)).le_opNorm (s x)).trans (by gcongr; exact hC _)
        _ = C * (‖s x‖ * ‖u z‖) := by ring
  -- Step 5: combine, using `Dη(z − x) = −Dη(x − z)` to identify the swapped integral.
  calc ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x)
      = ∫ x, ∫ z, fderiv ℝ η (x - z) (s x) * u z := by simp_rw [hLHS]
    _ = ∫ z, ∫ x, fderiv ℝ η (x - z) (s x) * u z := integral_integral_swap hint
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P)
          (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
            Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_neg]
      congr 1
      funext z
      rw [hRHS z, ← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      rw [← neg_sub x z, hodd, neg_apply]
      ring

/-- Simon Ch. 2, Lemma 2.5 on the cube `Q₁ = (0, 1)^{m+1}`: if `∫_{Q₁} u div g ≤ V` for every
smooth `g` with compact support in `Q₁` and `|g| ≤ 1`, then `u_η = η * 1_{Q₁} u` is smooth and
`∫_{Q_δ} |Du_η| ≤ V` whenever `spt η ⊆ B_δ(0)`.  For `g` with compact support in `Q_δ`, the
mollified field `G = η * g` is admissible, and `∫ Du_η · g = −∫_{Q₁} u div G = ∫_{Q₁} u div(−G)`. -/
theorem dor_lmb_fcd_cp_mollified_variation : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → (∀ z, 0 ≤ η z) → (∀ z, η (-z) = η z) → ∫ z, η z = 1 → support η ⊆ ball (0 : Euclid (m + 1)) δ → ContDiff ℝ (⊤ : ℕ∞) (convolution η (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ (convolution η (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ V := by
  intro m u V δ η hu hH hδ hη hηc hη0 heven hη1 hηs
  -- Step 0: `{y : a < yᵢ < b for all i}` is open, a finite intersection of open slabs.
  have hopen : ∀ a b : ℝ, IsOpen {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hQ₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    (hopen 0 1).measurableSet
  have hũ : Integrable ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) :=
    hu.integrable_indicator hQ₁
  -- Step 1: `1_{Q₁} u` is integrable, so `u_η` is smooth.
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (convolution η
      ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_left _ hη hũ.locallyIntegrable
  -- Step 2: `Q_δ` is open and bounded: it lies in the closed ball of radius `√(m + 1)`.
  have hbdd : Bornology.IsBounded {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} := by
    refine (isBounded_closedBall (x := (0 : Euclid (m + 1))) (r := √((m : ℝ) + 1))).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h0 : 0 < y i := by linarith [(hy i).1]
          have h1 : y i < 1 := by linarith [(hy i).2]
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = (m : ℝ) + 1 := by simp
  -- Step 3: by `smooth_duality` it suffices to bound `∫ Du_η · g` for admissible `g` in `Q_δ`.
  refine ⟨hsmooth, Submission.dor_lmb_fcd_cp_smooth_duality (m + 1) _ _ V (hopen δ (1 - δ)) hbdd
    hsmooth fun g hg hgc hgs hg1 => ?_⟩
  -- Step 4: `G = η * g` is smooth, compactly supported in `Q₁`, and `|G| ≤ 1`.
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_left _ hη hg.continuous.locallyIntegrable
  have hGc : HasCompactSupport (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.convolution _ hgc
  have hGs : tsupport (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    -- `spt G ⊆ spt η + spt g ⊆ B̄_δ(0) + Q_δ ⊆ Q₁`, the middle set being compact.
    refine (closure_minimal ((support_convolution_subset (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1))).trans
      (add_subset_add (subset_tsupport η) (subset_tsupport g)))
      (hηc.isCompact.add hgc.isCompact).isClosed).trans ?_
    rintro _ ⟨z, hz, q, hq, rfl⟩ i
    have hz' : ‖z‖ ≤ δ :=
      mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall (closure_mono hηs hz))
    have hzi : |z i| ≤ δ := by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le z i).trans hz'
    have hqi := hgs hq i
    rw [PiLp.add_apply]
    constructor <;> linarith [(abs_le.mp hzi).1, (abs_le.mp hzi).2, hqi.1, hqi.2]
  have hG1 : ∀ x, ‖convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ ≤ 1 := by
    intro x
    rw [convolution_def]
    calc ‖∫ t, ContinuousLinearMap.lsmul ℝ ℝ (η t) (g (x - t))‖ ≤ ∫ t, η t :=
          norm_integral_le_of_norm_le (hη.continuous.integrable_of_hasCompactSupport hηc)
            (Eventually.of_forall fun t => by
              rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (hη0 t)]
              exact mul_le_of_le_one_right (hη0 t) (hg1 _))
      _ = 1 := hη1
  -- Step 5: `mollifier_adjoint` gives `∫ Du_η · g = −∫ 1_{Q₁} u div G`.
  have hadj := codim1_rdo_dg_sp_mollifier_adjoint (m + 1) η
    ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) g
    (hη.of_le (by exact_mod_cast le_top)) hηc heven hũ
    (hg.continuous.integrable_of_hasCompactSupport hgc)
  -- Step 6: (H) for `−G` reads `−∫_{Q₁} u div G ≤ V`, since `div(−G) = −div G`.
  have hneg := hH (-convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) hGsmooth.neg hGc.neg
    (by rwa [tsupport_neg]) fun y => by rw [Pi.neg_apply, norm_neg]; exact hG1 y
  simp only [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg, mul_neg,
    integral_neg] at hneg
  rw [← integral_indicator hQ₁] at hneg
  simp_rw [indicator_mul_left] at hneg
  rw [hadj]
  exact hneg
/-- BV Poincaré inequality on the cube `Q_δ = (δ, 1 − δ)^{m+1}` in double-integral form (cf. the
proof of Simon Ch. 2, Lemma 2.7): if `∫_{Q₁} u div g ≤ V` for all smooth `g` with compact support
in `Q₁ = (0, 1)^{m+1}` and `|g| ≤ 1`, then `∫_{Q_δ} ∫_{Q_δ} |u(x) − u(y)| ≤ (m + 1)(1 − 2δ)|Q_δ| V`.
The mollifications `v_k = η_k ∗ 1_{Q₁}u` satisfy this bound by the smooth inequality, and
`v_k → u` a.e. on `Q_δ`, so Fatou's lemma on `Q_δ × Q_δ` passes it to `u`. -/
theorem dor_lmb_fcd_cp_bv_poincare : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : ℕ → Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → δ < 1 / 2 → (∀ k, ContDiff ℝ (⊤ : ℕ∞) (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ k, support (η k) ⊆ ball (0 : Euclid (m + 1)) δ) → (∀ᵐ x ∂volume, Tendsto (fun k => (convolution (η k) (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) atTop (𝓝 ((Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) x))) → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |u x - u y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * V := by
  intro m u V δ η hu hH hδ hδ2 hη hηc hη0 hηe hη1 hηs hlim
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  set C : ℝ := ((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal
  set v : ℕ → Euclid (m + 1) → ℝ := fun k =>
    convolution (η k) (Q₁.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- Step 1: each `v k` is smooth with `∫_Q ‖D v_k‖ ≤ V` (sibling `mollified_variation`).
  have hmv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ ∫ x in Q, ‖fderiv ℝ (v k) x‖ ≤ V := fun k =>
    Submission.dor_lmb_fcd_cp_mollified_variation m u V δ (η k) hu hH hδ (hη k) (hηc k)
      (hη0 k) (hηe k) (hη1 k) (hηs k)
  have hV : 0 ≤ V := (integral_nonneg fun x => norm_nonneg _).trans (hmv 0).2
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 1 - 2 * δ := by linarith
    positivity
  -- Step 2: the smooth Poincaré inequality for `v k` (sibling `smooth_poincare`).
  have hD : ∀ k, ∫ x in Q, ∫ y in Q, |v k x - v k y| ≤ C * V := fun k =>
    (Submission.dor_lmb_fcd_cp_smooth_poincare m (v k) δ
      ((hmv k).1.of_le (by exact_mod_cast le_top)) hδ.le hδ2).trans
      (mul_le_mul_of_nonneg_left (hmv k).2 hC0)
  -- `Q` is a measurable subset of `Q₁` contained in a compact ball.
  have hQQ₁ : Q ⊆ Q₁ := fun y hy i => ⟨hδ.trans (hy i).1, (hy i).2.trans (by linarith)⟩
  have hQm : MeasurableSet Q := by
    have hc : ∀ i : Fin (m + 1), Measurable fun y : Euclid (m + 1) => y i := fun i => by fun_prop
    have hQi : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y
      rw [mem_iInter]
      exact Iff.rfl
    rw [hQi]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hc i)).inter (measurableSet_lt (hc i) measurable_const)
  have hQK : Q ⊆ closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1)) := by
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have h1 := (hy i).1
          have h2 := (hy i).2
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = m + 1 := by simp
  have hK : IsCompact (closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1))) :=
    isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.2 ((measure_mono hQK).trans_lt hK.measure_lt_top).ne
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q
  -- Integrability on `Q × Q`.
  have huQ : Integrable u μ := hu.mono_set hQQ₁
  have hF : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|) (μ.prod μ) :=
    ((huQ.comp_fst μ).sub (huQ.comp_snd μ)).abs
  have hFk : ∀ k, Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => |v k p.1 - v k p.2|)
      (μ.prod μ) := fun k => by
    have hvk : Integrable (v k) μ :=
      (((hmv k).1.continuous.continuousOn).integrableOn_compact hK).mono_set hQK
    exact ((hvk.comp_fst μ).sub (hvk.comp_snd μ)).abs
  -- Step 3: `v k → u` a.e. on `Q`, hence `|v k x - v k y| → |u x - u y|` a.e. on `Q × Q`.
  have hlimQ : ∀ᵐ x ∂μ, Tendsto (fun k => v k x) atTop (𝓝 (u x)) := by
    filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem hQm] with x hx hxQ
    rwa [indicator_of_mem (hQQ₁ hxQ)] at hx
  have hlimP : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun k => ENNReal.ofReal |v k p.1 - v k p.2|) atTop
      (𝓝 (ENNReal.ofReal |u p.1 - u p.2|)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlimQ,
      Measure.quasiMeasurePreserving_snd.ae hlimQ] with p h1 h2
    exact ENNReal.tendsto_ofReal (h1.sub h2).abs
  -- Steps 4–5: Fatou's lemma on `Q × Q` and Fubini.
  have hFatou : ∫⁻ p, ENNReal.ofReal |u p.1 - u p.2| ∂(μ.prod μ) ≤ ENNReal.ofReal (C * V) :=
    calc ∫⁻ p, ENNReal.ofReal |u p.1 - u p.2| ∂(μ.prod μ)
        = ∫⁻ p, liminf (fun k => ENNReal.ofReal |v k p.1 - v k p.2|) atTop ∂(μ.prod μ) :=
          lintegral_congr_ae (hlimP.mono fun p hp => hp.liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ p, ENNReal.ofReal |v k p.1 - v k p.2| ∂(μ.prod μ)) atTop :=
          lintegral_liminf_le' fun k => (hFk k).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (C * V) := liminf_le_of_frequently_le' (Frequently.of_forall fun k => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hFk k) (ae_of_all _ fun p => abs_nonneg _),
            integral_prod _ (hFk k)]
          exact ENNReal.ofReal_le_ofReal (hD k))
  have hfin : ENNReal.ofReal (∫ x in Q, ∫ y in Q, |u x - u y|) ≤ ENNReal.ofReal (C * V) := by
    rw [← integral_prod (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|) hF,
      ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun p => abs_nonneg _)]
    exact hFatou
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 hV)).1 hfin
/-- Shrinking the unit cube `Q₁ = (0, 1)ᵐ⁺¹` to `Q_δ = (δ, 1 − δ)ᵐ⁺¹` while keeping half of the
`L¹` norm of `f` (Simon Ch. 2, proof of Lemma 2.7).  The cubes `Q_{1/(j+4)}` are open and
increase to `Q₁`, so continuity of the measure from above and of the integral along increasing
unions give one `j` for both the layer bound and the integral bound. -/
theorem dor_lmb_fcd_cp_shrinking : ∀ (m : ℕ) (f : Euclid (m + 1) → ℝ), IntegrableOn f {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} ≤ 1 ∧ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \ {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}) ≤ 1 / 4 ∧ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |f y| := by
  intro m f hf
  -- Step 1: `Q_t` is open, `Q_t ⊆ Q₁` for `t ≥ 0`, and `volume Q₁ = 1`.
  have hopen : ∀ t : ℝ, IsOpen {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} := by
    intro t
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hmeas : ∀ t : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} :=
    fun t => (hopen t).measurableSet
  have hmeas₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    simpa using hmeas 0
  have hsub : ∀ t : ℝ, 0 ≤ t → {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun t ht y hy i =>
    ⟨ht.trans_lt (hy i).1, (hy i).2.trans_le (by linarith)⟩
  have hvol₁ : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
    have hpre : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
        WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Set.mem_pi]
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  -- Step 2: `δ_j = 1/(j+4)` decreases to `0`, and the cubes `Q_{δ_j}` increase to `Q₁`.
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun j : ℕ => 1 / ((j : ℝ) + 4) := ⟨_, rfl⟩
  have hδpos : ∀ j, 0 < δ j := fun j => by rw [hδdef]; positivity
  have hδle : ∀ j, δ j ≤ 1 / 4 := fun j => by
    simp only [hδdef]
    gcongr
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hδanti : Antitone δ := fun j k hjk => by
    simp only [hδdef]
    gcongr
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    rw [hδdef]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hmono : Monotone fun j => {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j} :=
    fun j k hjk y hy i =>
      ⟨(hδanti hjk).trans_lt (hy i).1, (hy i).2.trans_le (by linarith [hδanti hjk])⟩
  have hunion : ⋃ j, {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j} =
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    refine Subset.antisymm (iUnion_subset fun j => hsub _ (hδpos j).le) fun y hy => ?_
    have hev : ∀ᶠ j in atTop, ∀ i, δ j < y i ∧ y i < 1 - δ j := by
      rw [eventually_all]
      intro i
      filter_upwards [(tendsto_order.1 hδlim).2 _ (hy i).1,
        (tendsto_order.1 hδlim).2 _ (sub_pos.2 (hy i).2)] with j hj₁ hj₂
      exact ⟨hj₁, by linarith⟩
    obtain ⟨j, hj⟩ := hev.exists
    exact mem_iUnion.2 ⟨j, hj⟩
  -- Step 3: continuity from above, `volume (Q₁ \ Q_{δ_j}) → 0`.
  have hlayer : Tendsto (fun j => volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
      {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j})) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := volume)
      (s := fun j => {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
        {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j})
      (fun j => (hmeas₁.diff (hmeas _)).nullMeasurableSet)
      (fun j k hjk => Set.sdiff_subset_sdiff_right (hmono hjk))
      ⟨0, ((measure_mono Set.sdiff_subset).trans_lt (by rw [hvol₁]; exact ENNReal.one_lt_top)).ne⟩
    rw [← Set.sdiff_iUnion, hunion, Set.sdiff_self, measure_empty] at h
    exact h
  have hev₁ : ∀ᶠ j in atTop, volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
      {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}) < 1 / 4 :=
    (tendsto_order.1 hlayer).2 _ (by norm_num)
  -- Step 4: continuity of the integral, `∫_{Q_{δ_j}} |f| → ∫_{Q₁} |f|`.
  have hint : Tendsto (fun j => ∫ y in {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}, |f y|)
      atTop (𝓝 (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y|)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume) (f := fun y => |f y|)
      (fun j => hmeas (δ j)) hmono (by rw [hunion]; exact hf.abs)
    rw [hunion] at h
    exact h
  have hev₂ : ∀ᶠ j in atTop, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤
      2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}, |f y| := by
    rcases (integral_nonneg fun y => abs_nonneg (f y) :
        0 ≤ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y|).eq_or_lt with h₀ | hpos
    · exact Eventually.of_forall fun j => by
        rw [← h₀]
        exact mul_nonneg zero_le_two (integral_nonneg fun y => abs_nonneg (f y))
    · filter_upwards [(tendsto_order.1 hint).1 _ (half_lt_self hpos)] with j hj
      linarith
  -- Step 5: one `j` works for both bounds.
  obtain ⟨j, hj₁, hj₂⟩ := (hev₁.and hev₂).exists
  exact ⟨δ j, hδpos j, hδle j, (measure_mono (hsub _ (hδpos j).le)).trans hvol₁.le, hj₁.le, hj₂⟩

end Submission

end GMT.Ch07
