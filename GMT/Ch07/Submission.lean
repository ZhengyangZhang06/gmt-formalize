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

/-- **A covector vanishing on all increasing tuples of standard basis vectors is zero**
(definiteness of the Euclidean coefficient norm).  With `e` the standard basis of `ℝᴾ`, an
alternating map is determined by its values `α(e_{J(0)}, …, e_{J(n-1)})` on injective
`J : Fin n → Fin P`.  For such `J`, `σ = Tuple.sort J` makes `J ∘ σ` monotone and injective, hence
strictly increasing, so `0 = α(e_{J ∘ σ}) = sign σ • α(e_J)` with `sign σ = ±1`. -/
theorem Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords : ∀ (P n : ℕ) (α : Covector (Euclid P) n), (∀ I : Fin n → Fin P, StrictMono I → α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) = 0) → α = 0 := by
  intro P n α h
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 1: it suffices to check `α(e_J) = 0` for injective `J`
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine e.ext_alternating fun J hJ => ?_
  show α (fun i => e (J i)) = (0 : ℝ)
  -- Step 2: sorting `J` gives a strictly increasing `J ∘ σ`
  have hmono : StrictMono (J ∘ Tuple.sort J) :=
    (Tuple.monotone_sort J).strictMono_of_injective (hJ.comp (Tuple.sort J).injective)
  -- Step 3: `0 = α(e_J ∘ σ) = sign σ • α(e_J)`, and `sign σ = ±1`
  have h1 : α.toAlternatingMap ((fun i => e (J i)) ∘ Tuple.sort J) = 0 := h _ hmono
  rw [AlternatingMap.map_perm] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort J)) with hs | hs <;> simpa [hs] using h1
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **The Euclidean coefficient norm is a continuous seminorm dominated by the operator norm**
(Simon Ch. 6, 1.15 and 2.4; used by the smooth approximation of test forms behind the mass of
`τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})`
for strictly increasing `I : Fin n → Fin P` and `c_I α = 0` otherwise.  Then
`covectorEuclideanNorm α = ‖v α‖` for the coefficient vector
`v α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)`, which is linear in `α`; this gives the
triangle inequality and homogeneity.  `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖` gives the bound with
`C = √(card (Fin n → Fin P))`, and then the norm is `C`-Lipschitz, hence continuous. -/
theorem Submission.rsd_mw_tfa_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
  intro P n
  classical
  -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
    if StrictMono I then α (fun i => e (I i)) else 0
  let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
    WithLp.toLp 2 (fun I => c I α)
  have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [v, c, e, hI]
  -- Step 2: `v` is additive and `ℝ`-homogeneous
  have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
    intro α α'
    simp only [v, ← WithLp.toLp_add]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
    intro t α
    simp only [v, ← WithLp.toLp_smul]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
  have h1 : ∀ α α' : Covector (Euclid P) n,
      covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
    intro α α'
    rw [hN, hN, hN, hadd]
    exact norm_add_le _ _
  -- Step 4: (ii), homogeneity of the Euclidean norm
  have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
  -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
  have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
    intro I α
    by_cases hI : StrictMono I
    · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
    · simp [c, hI]
  -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
  have h3 : ∀ α : Covector (Euclid P) n,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
    intro α
    have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
      Finset.sum_le_sum fun I _ => by
        simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
    rw [hN, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
  have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
      (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
    intro α α'
    have ha : covectorEuclideanNorm α ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
      simpa only [sub_add_cancel] using h1 (α - α') α'
    have hb : covectorEuclideanNorm α' ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
      have h := h1 (α' - α) α
      rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
    have hC := h3 (α - α')
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    constructor <;> linarith
  exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
    (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩

/-- The operator norm of an `n`-covector on `ℝᴾ` is at most a constant times its Euclidean
coefficient norm: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_I`, set to `0` on tuples `I` that are not
strictly increasing, is linear and injective on the finite-dimensional space `Λⁿ(ℝᴾ)`, hence
antilipschitz, and each of its coordinates is at most `covectorEuclideanNorm α` in absolute
value. -/
theorem Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm : ∀ (P n : ℕ), ∃ K : ℝ, 0 < K ∧ ∀ α : Covector (Euclid P) n, ‖α‖ ≤ K * covectorEuclideanNorm α := by
  intro P n
  classical
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  -- `L α = (α(e ∘ I))_I` on strictly increasing `I`, and `0` elsewhere
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I =>
        if StrictMono I then α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i) else 0
      map_add' := fun α β => by
        funext I
        by_cases hI : StrictMono I <;> simp [hI]
      map_smul' := fun c α => by
        funext I
        by_cases hI : StrictMono I <;> simp [hI] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro α hα
    refine Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords P n α fun I hI => ?_
    simpa [L, hI] using congrFun hα I
  obtain ⟨K, hKpos, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨K, NNReal.coe_pos.2 hKpos, fun α => ?_⟩
  have h1 : ‖α‖ ≤ K * ‖L α‖ := by
    simpa using hK.le_mul_dist α 0
  -- `|α(e ∘ I)| ≤ covectorEuclideanNorm α`: one summand of the sum under the square root
  have h2 : ‖L α‖ ≤ covectorEuclideanNorm α := by
    refine (pi_norm_le_iff_of_nonneg (covectorEuclideanNorm_nonneg α)).2 fun I => ?_
    by_cases hI : StrictMono I
    · have hs := Finset.single_le_sum (f := fun J : Fin n → Fin P =>
        if StrictMono J then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) ^ 2 else 0)
        (fun J _ => by split_ifs <;> positivity) (Finset.mem_univ I)
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hI, ↓reduceIte, Real.norm_eq_abs]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by simpa [hI] using hs)
    · simp [L, hI, covectorEuclideanNorm_nonneg]
  calc ‖α‖ ≤ K * ‖L α‖ := h1
    _ ≤ K * covectorEuclideanNorm α := by gcongr

/-- **The norm on `n`-vectors dual to the Euclidean coefficient norm** (step 1 of the density
representation of a cycle).  Let `|α|` be the Euclidean coefficient norm on `Λⁿ(ℝᴾ)`,
`B = {β : |β| ≤ 1}` and `N ζ = sup ζ(B)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper, and `B`
is closed (`|·|` is continuous) and bounded (`‖β‖ ≤ K |β| ≤ K`), hence compact; so the supremum
is attained, and `0 ∈ B` gives `N ζ ≥ 0`.  If `|α| = 0` then `‖α‖ ≤ K |α| = 0`; otherwise
`±|α|⁻¹ α ∈ B` gives `|ζ α| ≤ N ζ |α|`.  Finally, if `ζ β = N ζ` with `β ∈ B`, then
`N ζ ≤ ζ' β + ‖ζ - ζ'‖ ‖β‖ ≤ N ζ' + K ‖ζ - ζ'‖`, so `N` is `K`-Lipschitz, hence continuous. -/
theorem Submission.cbr_ci_dr_multivector_dual_norm : ∀ (P n : ℕ), ∃ N : MultiVector P n → ℝ, Continuous N ∧ (∀ ζ : MultiVector P n, 0 ≤ N ζ) ∧ (∀ (ζ : MultiVector P n) (α : Covector (Euclid P) n), |ζ α| ≤ N ζ * covectorEuclideanNorm α) ∧ (∀ ζ : MultiVector P n, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ β = N ζ) := by
  intro P n
  -- Steps 3–4: `Λⁿ(ℝᴾ)` is finite-dimensional (hence proper), `|·|` is continuous and
  -- absolutely homogeneous, and `‖α‖ ≤ K |α|`
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  obtain ⟨-, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨K, hK, hnorm⟩ := Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm P n
  -- Step 5: the unit ball `B` of `|·|` contains `0`, lies in `closedBall 0 K` and is compact
  let B := {β : Covector (Euclid P) n | covectorEuclideanNorm β ≤ 1}
  have h0B : (0 : Covector (Euclid P) n) ∈ B := by
    show covectorEuclideanNorm (0 : Covector (Euclid P) n) ≤ 1
    rw [covectorEuclideanNorm_zero]
    exact zero_le_one
  have hBK : ∀ β ∈ B, ‖β‖ ≤ K := fun β hβ =>
    (hnorm β).trans (mul_le_of_le_one_right hK.le hβ)
  have hBc : IsCompact B :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : Covector (Euclid P) n)) (r := K)).subset
        fun β hβ => mem_closedBall_zero_iff.mpr (hBK β hβ))
  -- Step 6: `N ζ = sup ζ(B)` is attained on `B` and bounds `ζ` on `B`
  have hmem : ∀ ζ : MultiVector P n, ∃ β ∈ B, ζ β = sSup (ζ '' B) := fun ζ =>
    (hBc.image ζ.continuous).sSup_mem ⟨ζ 0, 0, h0B, rfl⟩
  have hle : ∀ ζ : MultiVector P n, ∀ β ∈ B, ζ β ≤ sSup (ζ '' B) := fun ζ β hβ =>
    le_csSup (hBc.image ζ.continuous).bddAbove ⟨β, hβ, rfl⟩
  refine ⟨fun ζ => sSup (ζ '' B), ?_, fun ζ => ?_, fun ζ α => ?_, hmem⟩
  · -- Step 9: `N ζ ≤ N ζ' + K ‖ζ - ζ'‖`, so `N` is `K`-Lipschitz
    refine (LipschitzWith.of_le_add_mul' (f := fun ζ : MultiVector P n => sSup (ζ '' B)) K
      fun ζ ζ' => ?_).continuous
    obtain ⟨β, hβ, hζβ⟩ := hmem ζ
    have h1 : ζ β - ζ' β ≤ ‖ζ - ζ'‖ * K := by
      have h := (ζ - ζ').le_opNorm β
      rw [sub_apply, Real.norm_eq_abs] at h
      exact (le_abs_self _).trans
        (h.trans (mul_le_mul_of_nonneg_left (hBK β hβ) (norm_nonneg _)))
    have h2 := hle ζ' β hβ
    rw [dist_eq_norm ζ ζ']
    show sSup (ζ '' B) ≤ sSup (ζ' '' B) + K * ‖ζ - ζ'‖
    linarith
  · -- Step 7: `0 ∈ B` and `ζ 0 = 0`
    exact (map_zero ζ).symm.le.trans (hle ζ 0 h0B)
  · -- Step 8: if `|α| = 0` then `α = 0`; otherwise rescale `α` into `B`
    show |ζ α| ≤ sSup (ζ '' B) * covectorEuclideanNorm α
    rcases (covectorEuclideanNorm_nonneg α).eq_or_lt with h | h
    · have hα : ‖α‖ ≤ 0 := by
        have h' := hnorm α
        rwa [← h, mul_zero] at h'
      rw [norm_le_zero_iff.mp hα, map_zero, abs_zero, covectorEuclideanNorm_zero, mul_zero]
    · have hβ : (covectorEuclideanNorm α)⁻¹ • α ∈ B := by
        show covectorEuclideanNorm ((covectorEuclideanNorm α)⁻¹ • α) ≤ 1
        rw [hsmul, abs_inv, abs_of_pos h, inv_mul_cancel₀ h.ne']
      have hβ' : -((covectorEuclideanNorm α)⁻¹ • α) ∈ B := by
        show covectorEuclideanNorm (-((covectorEuclideanNorm α)⁻¹ • α)) ≤ 1
        rw [covectorEuclideanNorm_neg]
        exact hβ
      have h1 := hle ζ _ hβ
      have h2 := hle ζ _ hβ'
      rw [map_neg] at h2
      calc |ζ α| = covectorEuclideanNorm α * |ζ ((covectorEuclideanNorm α)⁻¹ • α)| := by
            rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h,
              mul_inv_cancel_left₀ h.ne']
        _ ≤ covectorEuclideanNorm α * sSup (ζ '' B) :=
            mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, h1⟩) h.le
        _ = sSup (ζ '' B) * covectorEuclideanNorm α := mul_comm _ _

/-- **The mass identity forces the representing `n`-vector field to attain `1` a.e.** (Simon Ch. 6,
2.7–2.8: in `T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T` with `μ_T(U) = M(T)`, `|T⃗| = 1` `μ_T`-a.e.).  Let `Γ ∈ 𝒟ₙ(ℝᴾ)`,
`μ` finite with `M(Γ) = μ(ℝᴾ)`, and `ξ` `μ`-a.e. strongly measurable with `|ξ(x)(α)| ≤ |α|` a.e.
and `Γ(ω) = ∫ ξ(x)(ω(x)) dμ`.  For the dual norm `N` of `|·|` on `n`-vectors, `f = N ∘ ξ` has
`0 ≤ f ≤ 1` a.e.; every mass-admissible `ω` gives `Γ(ω) ≤ ∫ f dμ`, so `μ(ℝᴾ) = M(Γ) ≤ ∫ f dμ`.
Hence `∫ (1 − f) dμ = 0`, `f = 1` a.e., and a covector `β` attaining `N(ξ(x))` has `|β| ≤ 1`
and `ξ(x)(β) = 1`. -/
theorem Submission.cbr_ci_dr_ae_unit_attained_of_mass_eq : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ univ < ∞ → Γ.massOn univ = μ univ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ x β = 1 := by
  intro P n Γ μ ξ hμ hmass hξ hbound hrep
  -- (1) the dual norm `N` of `|·|` on `n`-vectors (sibling `dual_norm`); `μ` is finite
  obtain ⟨N, hNc, hN0, hNle, hNatt⟩ := Submission.cbr_ci_dr_multivector_dual_norm P n
  have : IsFiniteMeasure μ := ⟨hμ⟩
  -- (2) `f = N ∘ ξ` satisfies `0 ≤ f ≤ 1` a.e. and is integrable
  have hf_le : ∀ᵐ x ∂μ, N (ξ x) ≤ 1 := by
    filter_upwards [hbound] with x hx
    obtain ⟨β, hβ, hξβ⟩ := hNatt (ξ x)
    calc N (ξ x) = ξ x β := hξβ.symm
      _ ≤ |ξ x β| := le_abs_self _
      _ ≤ covectorEuclideanNorm β := hx β
      _ ≤ 1 := hβ
  have hf_int : Integrable (fun x => N (ξ x)) μ := by
    refine Integrable.of_bound (hNc.comp_aestronglyMeasurable hξ) 1 ?_
    filter_upwards [hf_le] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (hN0 _)]
  -- (3) every mass-admissible `ω` has `Γ(ω) = ∫ ξ(ω) dμ ≤ ∫ f dμ`, as `|ξ(x)(ω(x))| ≤ f(x)`
  have hadm : ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid P)) n univ,
      Γ ω ≤ ∫ x, N (ξ x) ∂μ := by
    intro ω hω
    have hgN : ∀ x, |ξ x ((ω : DifferentialForm (Euclid P) n) x)| ≤ N (ξ x) := fun x =>
      (hNle (ξ x) _).trans (mul_le_of_le_one_right (hN0 _) (hω.2 x))
    have hg_meas : AEStronglyMeasurable
        (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hξ.prodMk ω.property.1.1.continuous.aestronglyMeasurable)
    have hg_int : Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ :=
      hf_int.mono' hg_meas (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hgN x))
    rw [hrep ω]
    exact integral_mono hg_int hf_int fun x => (le_abs_self _).trans (hgN x)
  -- (4) `μ(ℝᴾ) = M(Γ) ≤ ∫ f dμ`
  have hmass_le : μ univ ≤ ENNReal.ofReal (∫ x, N (ξ x) ∂μ) := by
    rw [← hmass]
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hadm ω hω)
  have hreal : μ.real univ ≤ ∫ x, N (ξ x) ∂μ :=
    ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => hN0 _) hmass_le
  -- (5) `∫ (1 − f) dμ = μ(ℝᴾ) − ∫ f dμ ≤ 0` with `1 − f ≥ 0` a.e., so `f = 1` a.e.
  have hsub_nonneg : 0 ≤ᵐ[μ] fun x => 1 - N (ξ x) := by
    filter_upwards [hf_le] with x hx
    exact sub_nonneg.2 hx
  have hsub_zero : ∫ x, (1 - N (ξ x)) ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hsub_nonneg)
    rw [integral_sub (integrable_const 1) hf_int, integral_const, smul_eq_mul, mul_one]
    exact sub_nonpos.2 hreal
  have hae : (fun x => 1 - N (ξ x)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hsub_nonneg ((integrable_const 1).sub hf_int)).1 hsub_zero
  -- (6) where `N(ξ(x)) = 1`, the covector attaining `N(ξ(x))` is the required `β`
  filter_upwards [hae] with x hx
  obtain ⟨β, hβ, hξβ⟩ := hNatt (ξ x)
  refine ⟨β, hβ, ?_⟩
  have h1 : 1 - N (ξ x) = 0 := hx
  rw [hξβ]
  linarith
/-- **Bounded strongly measurable modification of an `n`-vector field** (the Borel normalized
field `ξ₀ / max(1, |ξ₀|*)` of the density representation).  If `ξ` is `μ`-a.e. strongly
measurable and `|⟨α, ξ(x)⟩| ≤ |α|` for `μ`-a.e. `x` and every `n`-covector `α`
(`|·| = covectorEuclideanNorm`), then some strongly measurable `ζ` satisfies the bound at every
`x` and agrees with `ξ` `μ`-a.e.  With `N = |·|*` the dual norm of
`cbr_ci_dr_multivector_dual_norm` and `ξ₀` a strongly measurable version of `ξ`, take
`ζ = max(1, N ∘ ξ₀)⁻¹ • ξ₀`: it is a continuous function of `ξ₀`, `|ζ(x)(α)| ≤ |α|` because
`N(ξ₀(x)) ≤ max(1, N(ξ₀(x)))`, and `ζ = ξ₀ = ξ` wherever `ξ₀ = ξ` and `ξ` is bounded, since
there `N(ξ) ≤ 1` by attainment of `N` on the unit ball. -/
theorem Submission.cbr_ci_dr_bounded_stronglyMeasurable_modification : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ ζ : Euclid P → MultiVector P n, StronglyMeasurable ζ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) ∧ ζ =ᵐ[μ] ξ := by
  intro P n μ ξ hξm hξb
  -- Step 1: the dual norm `N` on `n`-vectors (`dual_norm`)
  obtain ⟨N, hNc, -, hNle, hNatt⟩ := Submission.cbr_ci_dr_multivector_dual_norm P n
  -- Step 2: an `n`-vector `η` with `|η(α)| ≤ |α|` for all `α` has `N(η) ≤ 1` (attainment)
  have hN1 : ∀ η : MultiVector P n,
      (∀ α : Covector (Euclid P) n, |η α| ≤ covectorEuclideanNorm α) → N η ≤ 1 := by
    intro η hη
    obtain ⟨β, hβ, hηβ⟩ := hNatt η
    calc N η = η β := hηβ.symm
      _ ≤ |η β| := le_abs_self _
      _ ≤ covectorEuclideanNorm β := hη β
      _ ≤ 1 := hβ
  -- Step 3: the normalization `η ↦ max(1, N(η))⁻¹ • η` is continuous (denominator `≥ 1`)
  have hm : ∀ η : MultiVector P n, 0 < max 1 (N η) := fun η =>
    zero_lt_one.trans_le (le_max_left _ _)
  have hFc : Continuous fun η : MultiVector P n => (max 1 (N η))⁻¹ • η :=
    ((continuous_const.max hNc).inv₀ fun η => (hm η).ne').smul continuous_id
  -- Step 4: `ζ := max(1, N ∘ ξ₀)⁻¹ • ξ₀` for a strongly measurable version `ξ₀` of `ξ`
  obtain ⟨ξ₀, hξ₀, hξξ₀⟩ : ∃ ξ₀ : Euclid P → MultiVector P n, StronglyMeasurable ξ₀ ∧
      ξ =ᵐ[μ] ξ₀ :=
    ⟨hξm.mk ξ, hξm.stronglyMeasurable_mk, hξm.ae_eq_mk⟩
  refine ⟨fun x => (max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x, hFc.comp_stronglyMeasurable hξ₀, ?_, ?_⟩
  · -- Step 5: with `m = max(1, N(ξ₀ x))`, `|ζ(x)(α)| = m⁻¹ |ξ₀(x)(α)| ≤ m⁻¹ N(ξ₀ x) |α| ≤ |α|`
    intro x α
    show |((max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x) α| ≤ covectorEuclideanNorm α
    rw [smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 (hm (ξ₀ x))),
      inv_mul_le_iff₀ (hm (ξ₀ x))]
    exact (hNle (ξ₀ x) α).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (covectorEuclideanNorm_nonneg α))
  · -- Step 6: where `ξ₀ = ξ` and `ξ` is bounded, `N(ξ₀ x) ≤ 1`, so `m = 1` and `ζ(x) = ξ(x)`
    filter_upwards [hξξ₀, hξb] with x hx hxb
    show (max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x = ξ x
    rw [← hx, max_eq_left (hN1 (ξ x) hxb), inv_one, one_smul]
/-- Positive lower `n`-density of a finite measure forces finite `Hⁿ`-measure (Vitali `5r`-covering,
used for Simon 7.2.4 via the density representation): if `μ(ℝᴾ) < ∞` and
`liminf_{r↓0} μ(B_r(x))/(ωₙrⁿ) ≥ η > 0` for every `x ∈ A`, then `Hⁿ(A) < ∞`.  At scale `k`, choose
radii `rₖ(x) < 1/(k+1)` with `c rₖ(x)ⁿ ≤ μ(B̄_{rₖ(x)}(x))`, `c = (η/2)ωₙ`; the Vitali subfamily
`uₖ ⊆ A` is countable and disjoint, so `Σ_{uₖ} rₖⁿ ≤ μ(ℝᴾ)/c`, and the enlarged balls
`B̄_{5rₖ(b)}(b)` cover `A` with `Σ diamⁿ ≤ 10ⁿ μ(ℝᴾ)/c`. -/
theorem Submission.cbr_ci_dr_euclideanHausdorff_lt_top_of_lower_density : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (η : ℝ), 0 < η → μ univ < ∞ → (∀ x ∈ A, ENNReal.ofReal η ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → μHE[n] A < ∞ := by
  intro P n μ A η hη hμ hA
  -- `c = (η/2) ωₙ ∈ (0, ∞)`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  set c : ℝ≥0∞ := ENNReal.ofReal (η / 2) * unitBallVolume n with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (half_pos hη)).ne' hω0
  have hctop : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop
  -- arbitrarily small radii `ρ` with `c ρⁿ ≤ μ(B̄_ρ(x))`
  have hgood : ∀ x ∈ A, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
      c * ENNReal.ofReal (ρ ^ n) ≤ μ (closedBall x ρ) := by
    intro x hx δ hδ
    have hlt : ENNReal.ofReal (η / 2) < liminf (fun r : ℝ =>
        μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) :=
      ((ENNReal.ofReal_lt_ofReal_iff hη).2 (half_lt_self hη)).trans_le (hA x hx)
    obtain ⟨ρ, hρ, hρδ⟩ :=
      ((eventually_lt_of_lt_liminf hlt).and (Ioo_mem_nhdsGT hδ)).exists
    refine ⟨ρ, hρδ.1, hρδ.2, ?_⟩
    calc c * ENNReal.ofReal (ρ ^ n)
        = ENNReal.ofReal (η / 2) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
          rw [hc, mul_assoc]
      _ ≤ μ (ball x ρ) := ENNReal.mul_le_of_le_div hρ.le
      _ ≤ μ (closedBall x ρ) := measure_mono ball_subset_closedBall
  -- radii `rₖ(x) < 1/(k+1)` at every scale `k`
  choose! r hr0 hrδ hrμ using fun (k : ℕ) (x : Euclid P) (hx : x ∈ A) =>
    hgood x hx (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  -- Vitali subfamilies `uₖ ⊆ A`; they are countable since the balls have nonempty interior
  have hvit : ∀ k : ℕ, ∃ u ⊆ A, (u.PairwiseDisjoint fun a => closedBall a (r k a)) ∧
      ∀ a ∈ A, ∃ b ∈ u, closedBall a (r k a) ⊆ closedBall b (5 * r k b) := fun k =>
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A (fun a => a) (r k)
      (1 / ((k : ℝ) + 1)) (fun a ha => (hrδ k a ha).le) 5 (by norm_num)
  choose u huA hudisj hucov using hvit
  have hucount : ∀ k, (u k).Countable := fun k =>
    (hudisj k).countable_of_nonempty_interior fun a ha =>
      (nonempty_ball.2 (hr0 k a (huA k ha))).mono
        (interior_maximal ball_subset_closedBall isOpen_ball)
  have : ∀ k, Countable (u k) := fun k => (hucount k).to_subtype
  -- `Σ_{b ∈ uₖ} rₖ(b)ⁿ ≤ μ(ℝᴾ)/c` by disjointness
  have hsum : ∀ k, ∑' b : u k, ENNReal.ofReal (r k b ^ n) ≤ μ univ / c := by
    intro k
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop), mul_comm, ← ENNReal.tsum_mul_left]
    calc ∑' b : u k, c * ENNReal.ofReal (r k b ^ n)
        ≤ ∑' b : u k, μ (closedBall (b : Euclid P) (r k b)) :=
          ENNReal.tsum_le_tsum fun b => hrμ k b (huA k b.2)
      _ = μ (⋃ b ∈ u k, closedBall b (r k b)) :=
          (measure_biUnion (hucount k) (hudisj k) fun b _ => measurableSet_closedBall).symm
      _ ≤ μ univ := measure_mono (subset_univ _)
  -- `diam B̄_{5rₖ(b)}(b) ≤ 10 rₖ(b)`
  have hdiam : ∀ k, ∀ b ∈ u k,
      ediam (closedBall b (5 * r k b)) ≤ ENNReal.ofReal (10 * r k b) := by
    intro k b _
    refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
    calc dist y z ≤ dist y b + dist z b := dist_triangle_right y z b
      _ ≤ 5 * r k b + 5 * r k b := add_le_add (mem_closedBall.1 hy) (mem_closedBall.1 hz)
      _ = 10 * r k b := by ring
  set Λ : ℝ≥0∞ := ENNReal.ofReal (10 ^ n) * (μ univ / c) with hΛ
  have hΛtop : Λ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.div_lt_top hμ.ne hc0)
  -- `μH[n](A) ≤ Λ` from the covers `{B̄_{5rₖ(b)}(b)}_{b ∈ uₖ}` of mesh `≤ 10/(k+1)`
  have hH : μH[n] A ≤ Λ := by
    have htend :
        Tendsto (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (10 : ℝ))
      rw [mul_zero] at h
      simpa using ENNReal.tendsto_ofReal h
    refine (Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) A (l := atTop)
      (ι := fun k => u k) _ htend (fun k b => closedBall (b : Euclid P) (5 * r k b))
      (Eventually.of_forall fun k b => (hdiam k b b.2).trans (ENNReal.ofReal_le_ofReal ?_))
      (Eventually.of_forall fun k a ha => ?_)).trans ?_
    · have := hrδ k b (huA k b.2)
      linarith
    · obtain ⟨b, hb, hab⟩ := hucov k a ha
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hab (mem_closedBall_self (hr0 k a ha).le)⟩
    · refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
      calc ∑' b : u k, ediam (closedBall (b : Euclid P) (5 * r k b)) ^ (n : ℝ)
          ≤ ∑' b : u k, ENNReal.ofReal (10 ^ n) * ENNReal.ofReal (r k b ^ n) := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            have h0 : 0 ≤ r k b := (hr0 k b (huA k b.2)).le
            rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
              ENNReal.ofReal_pow (by positivity)]
            exact pow_le_pow_left₀ bot_le (hdiam k b b.2) n
        _ = ENNReal.ofReal (10 ^ n) * ∑' b : u k, ENNReal.ofReal (r k b ^ n) :=
            ENNReal.tsum_mul_left
        _ ≤ Λ := by rw [hΛ]; gcongr; exact hsum k
  -- `μHE[n] = s • μH[n]` with a finite scalar `s`
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hH.trans_lt hΛtop)
/-- Radon–Nikodym with a carrier: if `μ` is finite, `μ(M₀ᶜ) = 0`, `ν(M₀) < ∞` and `μ ≪ ν`, then
`μ = (ν⌞M)·θ` for a Borel `M ⊆ M₀` and a Borel `θ > 0` on `M`.  With `ν₀ = ν⌞M₀` (finite) and
`h = dμ/dν₀`, `μ ≪ ν₀` gives `μ = ν₀·h` with `h < ∞` `ν₀`-a.e.; take
`M = M₀ ∩ {0 < h < ∞}` and `θ = 1_M · h.toReal`, so that `h = 1_M · ofReal θ` `ν₀`-a.e. -/
theorem Submission.cbr_ci_dr_withDensity_carrier_of_absolutelyContinuous : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (M₀ : Set (Euclid P)), μ univ < ∞ → MeasurableSet M₀ → ν M₀ < ∞ → μ M₀ᶜ = 0 → (∀ E : Set (Euclid P), ν E = 0 → μ E = 0) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ), MeasurableSet M ∧ M ⊆ M₀ ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ μ = (ν.restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) := by
  intro P μ ν M₀ hμ hM₀ hνM₀ hμM₀c hac
  -- `μ` and `ν₀ = ν⌞M₀` are finite
  have : IsFiniteMeasure μ := ⟨hμ⟩
  have : IsFiniteMeasure (ν.restrict M₀) := isFiniteMeasure_restrict.mpr hνM₀.ne
  -- `μ ≪ ν₀`: `ν₀(E) = ν(E ∩ M₀)` and `μ(M₀ᶜ) = 0`
  have hμν₀ : μ ≪ ν.restrict M₀ := by
    intro E hE
    rw [Measure.restrict_apply' hM₀] at hE
    rw [← inter_union_compl E M₀]
    exact measure_union_null (hac _ hE) (measure_mono_null inter_subset_right hμM₀c)
  -- Radon–Nikodym: `μ = ν₀·h` with `h = dμ/dν₀` Borel and `h < ∞` `ν₀`-a.e.
  obtain ⟨h, hh, hμh, hh_lt⟩ : ∃ h : Euclid P → ℝ≥0∞, Measurable h ∧
      μ = (ν.restrict M₀).withDensity h ∧ ∀ᵐ x ∂(ν.restrict M₀), h x < ∞ := by
    refine ⟨μ.rnDeriv (ν.restrict M₀), Measure.measurable_rnDeriv _ _, ?_,
      Measure.rnDeriv_lt_top _ _⟩
    have hdec := Measure.haveLebesgueDecomposition_add μ (ν.restrict M₀)
    rwa [Measure.singularPart_eq_zero_of_ac hμν₀, zero_add] at hdec
  -- the carrier `M = M₀ ∩ {0 < h} ∩ {h < ∞}` and the density `θ = 1_M · h.toReal`
  set M : Set (Euclid P) := M₀ ∩ {x | 0 < h x} ∩ {x | h x < ∞}
  have hM : MeasurableSet M :=
    (hM₀.inter (measurableSet_lt measurable_const hh)).inter (measurableSet_lt hh measurable_const)
  have hMM₀ : M ⊆ M₀ := fun x hx => hx.1.1
  refine ⟨M, M.indicator fun x => (h x).toReal, hM, hMM₀, hh.ennreal_toReal.indicator hM,
    fun x hx => ?_, ?_⟩
  · rw [indicator_of_mem hx]
    exact ENNReal.toReal_pos hx.1.2.ne' hx.2.ne
  -- `h = 1_M · ofReal θ` `ν₀`-a.e., since `ν₀`-a.e. `x ∈ M₀` and `h x < ∞`
  have hae : h =ᵐ[ν.restrict M₀]
      M.indicator fun x => ENNReal.ofReal (M.indicator (fun x => (h x).toReal) x) := by
    filter_upwards [ae_restrict_mem hM₀, hh_lt] with x hxM₀ hxlt
    by_cases hxM : x ∈ M
    · rw [indicator_of_mem hxM, indicator_of_mem hxM, ENNReal.ofReal_toReal hxlt.ne]
    · rw [indicator_of_notMem hxM]
      exact nonpos_iff_eq_zero.mp (not_lt.mp fun hpos => hxM ⟨⟨hxM₀, hpos⟩, hxlt⟩)
  -- `μ = ν₀·(1_M · ofReal θ) = (ν₀⌞M)·ofReal θ = (ν⌞M)·ofReal θ`
  rw [hμh, withDensity_congr_ae hae, withDensity_indicator hM,
    Measure.restrict_restrict_of_subset hMM₀]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
