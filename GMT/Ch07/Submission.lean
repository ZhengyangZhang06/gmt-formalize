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

/-- An open `U ⊆ ℝᴾ` is exhausted by the compact sets `Kᵢ = B̄(0, i) \ thickening((i + 1)⁻¹, Uᶜ)`
(the exhaustion in the proof of Simon 1.4.16): `Kᵢ ⊆ U`, since a point of `Uᶜ` lies in every
positive thickening of `Uᶜ`; a compact `C ⊆ U` has a margin `δ > 0` with `thickening δ C ⊆ U` and
a radius `R` with `C ⊆ B̄(0, R)`, so `C ⊆ Kₘ` once `R ≤ m` and `(m + 1)⁻¹ < δ`. -/
theorem Submission.cbr_ct_vs_compact_exhaustion : ∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i := by
  intro P U hU
  refine ⟨fun i => closedBall (0 : Euclid P) i \ thickening ((i : ℝ) + 1)⁻¹ Uᶜ,
    fun i => (isCompact_closedBall _ _).diff isOpen_thickening, fun i x hx => ?_,
    fun C hC hCU => ?_⟩
  · by_contra hxU
    exact hx.2 (self_subset_thickening (by positivity) _ hxU)
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Euclid P)
    obtain ⟨m, hm⟩ := exists_nat_ge (max R δ⁻¹)
    have hmδ : ((m : ℝ) + 1)⁻¹ < δ := inv_lt_of_inv_lt₀ hδ (by linarith [le_max_right R δ⁻¹])
    refine ⟨m, fun x hx => ⟨closedBall_subset_closedBall ((le_max_left R δ⁻¹).trans hm) (hR hx),
      fun hxt => ?_⟩⟩
    -- a point `y ∉ U` within `(m + 1)⁻¹ < δ` of `x ∈ C` would lie in `thickening δ C ⊆ U`
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hxt
    exact hy (hδU (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
/-- **Simon 1.4.16, one compact piece** (the Alaoglu step of the proof, corrected to a genuine
subsequence).  If `K ⊆ ℝᴾ` is compact and `supⱼ μⱼ(K) < ∞`, there is a strictly increasing `θ`
such that `∫ f dμ_{θ(j)}` converges for every continuous `f` with `tsupport f ⊆ K`.  As `f`
vanishes off `K`, `∫ f dμⱼ = ∫_K f dμⱼ`.  The step functions `g (n, L) x = L[m]` (`m` the first
index with `|x - dₘ| < 1/(n+1)`, `(dₘ)` dense in `ℝᴾ`, `L` a list of rationals) form a countable
family that is uniformly dense on `K` for such `f`.  Sequential compactness of a countable product
of compact intervals gives one subsequence along which every `∫_K g dμⱼ` converges, and a `3ε`
argument makes `∫_K f dμ_{θ(j)}` Cauchy. -/
theorem Submission.cbr_ct_vs_compact_piece_subseq : ∀ (P : ℕ) (K : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsCompact K → ⨆ j, μs j K < ∞ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (θ j))) atTop (𝓝 c) := by
  classical
  intro P K μs hK hM
  -- `M = supⱼ μⱼ(K)` as a real number
  set M : ℝ := (⨆ j, μs j K).toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hμK : ∀ j, μs j K ≤ ⨆ j, μs j K := fun j => le_iSup (fun j => μs j K) j
  have hμKfin : ∀ j, μs j K < ∞ := fun j => lt_of_le_of_lt (hμK j) hM
  have hμKM : ∀ j, (μs j).real K ≤ M := fun j => ENNReal.toReal_mono hM.ne (hμK j)
  -- a dense sequence `d` in `ℝᴾ`: every `x` is within `1/(n+1)` of some `d m`
  set d : ℕ → Euclid P := TopologicalSpace.denseSeq (Euclid P)
  have hr : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  have hcov : ∀ (n : ℕ) (x : Euclid P), ∃ m, dist x (d m) < 1 / ((n : ℝ) + 1) :=
    fun n x => (TopologicalSpace.denseRange_denseSeq (Euclid P)).exists_dist_lt x (hr n)
  -- the countable test family `g (n, L) x = L[m]`, `m` the first index with
  -- `dist x (d m) < 1/(n+1)`; it is measurable and bounded by `B (n, L) = ∑ |L[i]|`
  let g : ℕ × List ℚ → Euclid P → ℝ := fun k x =>
    ((k.2.getD (Nat.find (hcov k.1 x)) 0 : ℚ) : ℝ)
  have hgm : ∀ k, Measurable (g k) := fun k =>
    Measurable.find (f := fun m _ => ((k.2.getD m 0 : ℚ) : ℝ)) (fun _ => measurable_const)
      (fun _ => measurableSet_ball) (hcov k.1)
  let B : ℕ × List ℚ → ℝ := fun k => (k.2.map (fun q : ℚ => |(q : ℝ)|)).sum
  have hgB : ∀ k x, |g k x| ≤ B k := by
    have key : ∀ (L : List ℚ) (m : ℕ),
        |((L.getD m 0 : ℚ) : ℝ)| ≤ (L.map (fun q : ℚ => |(q : ℝ)|)).sum := by
      intro L
      induction L with
      | nil => intro m; simp
      | cons a L ih =>
        intro m
        have hs : 0 ≤ (L.map (fun q : ℚ => |(q : ℝ)|)).sum := List.sum_nonneg (by simp)
        cases m with
        | zero =>
          simp only [List.getD_cons_zero, List.map_cons, List.sum_cons]
          linarith
        | succ m =>
          simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
          linarith [ih m, abs_nonneg (a : ℝ)]
    exact fun k x => key k.2 _
  -- every admissible `f` is uniformly approximated on `K` by the test family
  have happrox : ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K →
      ∀ ε > 0, ∃ k, ∀ x ∈ K, |f x - g k x| ≤ ε := by
    intro f hf hfK ε hε
    have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
      (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun m => ball (d m) (1 / ((n : ℝ) + 1)))
      (fun _ => isOpen_ball) (fun x _ => mem_iUnion.mpr (hcov n x))
    choose q hq using fun m => Rat.denseRange_cast.exists_dist_lt (f (d m)) (half_pos hε)
    refine ⟨(n, (List.range (t.sup id + 1)).map q), fun x hx => ?_⟩
    obtain ⟨m, hmt, hxm⟩ := mem_iUnion₂.mp (ht hx)
    have hlt : Nat.find (hcov n x) < t.sup id + 1 :=
      Nat.lt_succ_of_le ((Nat.find_min' (hcov n x) hxm).trans (Finset.le_sup (f := id) hmt))
    have h1 := hfδ ((Nat.find_spec (hcov n x)).trans hn)
    have h2 := hq (Nat.find (hcov n x))
    rw [Real.dist_eq] at h1 h2
    have hg : g (n, (List.range (t.sup id + 1)).map q) x = q (Nat.find (hcov n x)) := by
      simp only [g, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
        Option.map_some, Option.getD_some]
    rw [hg]
    linarith [abs_sub_le (f x) (f (d (Nat.find (hcov n x)))) (q (Nat.find (hcov n x)) : ℝ)]
  -- the test integrals `v j k = ∫_K g k dμⱼ` satisfy `|v j k| ≤ B k * M`
  have hgi : ∀ j k, IntegrableOn (g k) K (μs j) := fun j k =>
    Measure.integrableOn_of_bounded (hμKfin j).ne (hgm k).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hgB k x))
  let v : ℕ → ℕ × List ℚ → ℝ := fun j k => ∫ x in K, g k x ∂(μs j)
  have hvB : ∀ j k, |v j k| ≤ B k * M := by
    intro j k
    rw [← Real.norm_eq_abs]
    calc ‖∫ x in K, g k x ∂(μs j)‖ ≤ B k * (μs j).real K :=
          norm_setIntegral_le_of_norm_le_const (hμKfin j)
            (fun x _ => (Real.norm_eq_abs _).trans_le (hgB k x))
      _ ≤ B k * M := mul_le_mul_of_nonneg_left (hμKM j) ((abs_nonneg _).trans (hgB k 0))
  -- diagonal selection: `(v j)ⱼ` lies in the compact `∏ₖ [-B k M, B k M]`, which is
  -- first countable since `ℕ × List ℚ` is countable
  obtain ⟨a, -, θ, hθ, hlim⟩ :=
    (isCompact_univ_pi fun k : ℕ × List ℚ =>
      isCompact_Icc (a := -(B k * M)) (b := B k * M)).tendsto_subseq
      (x := v) fun j => Set.mem_univ_pi.mpr fun k => abs_le.mp (hvB j k)
  have hconv : ∀ k, Tendsto (fun j => v (θ j) k) atTop (𝓝 (a k)) := tendsto_pi_nhds.mp hlim
  refine ⟨θ, hθ, fun f hf hfK => ?_⟩
  -- `f` vanishes off `K`, so `∫ f dμⱼ = ∫_K f dμⱼ`; and `f` is bounded
  have hf0 : ∀ x ∉ K, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfK h)
  have hfK' : ∀ j, ∫ x, f x ∂(μs j) = ∫ x in K, f x ∂(μs j) := fun j =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero hf0).symm
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support
    (hK.of_isClosed_subset (isClosed_tsupport f) hfK)
  have hfi : ∀ j, IntegrableOn f K (μs j) := fun j =>
    Measure.integrableOn_of_bounded (hμKfin j).ne hf.aestronglyMeasurable (ae_of_all _ hC)
  -- `∫ f dμⱼ` is `η M`-close to a test integral, uniformly in `j`
  have hclose : ∀ η > 0, ∃ k, ∀ j, dist (∫ x, f x ∂(μs j)) (v j k) ≤ η * M := by
    intro η hη
    obtain ⟨k, hk⟩ := happrox f hf hfK η hη
    refine ⟨k, fun j => ?_⟩
    rw [hfK' j, dist_eq_norm, ← integral_sub (hfi j) (hgi j k)]
    calc ‖∫ x in K, (f x - g k x) ∂(μs j)‖ ≤ η * (μs j).real K :=
          norm_setIntegral_le_of_norm_le_const (hμKfin j)
            (fun x hx => (Real.norm_eq_abs _).trans_le (hk x hx))
      _ ≤ η * M := mul_le_mul_of_nonneg_left (hμKM j) hη.le
  -- hence `(∫ f dμ_{θ j})ⱼ` is Cauchy, so it converges
  have hcauchy : CauchySeq (fun j => ∫ x, f x ∂(μs (θ j))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := hclose (ε / (3 * (M + 1))) (by positivity)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hconv k).cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hk (θ m)
    have h2 := hk (θ n)
    have h3 := hN m hm n hn
    have hη : ε / (3 * (M + 1)) * M ≤ ε / 3 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc dist (∫ x, f x ∂(μs (θ m))) (∫ x, f x ∂(μs (θ n)))
        ≤ dist (∫ x, f x ∂(μs (θ m))) (v (θ m) k) + dist (v (θ m) k) (v (θ n) k) +
            dist (v (θ n) k) (∫ x, f x ∂(μs (θ n))) := dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm (v (θ n) k)]; linarith
  exact cauchySeq_tendsto_of_complete hcauchy
/-- **Diagonal subsequence** (Simon Ch. 1, proof of 4.16, chapter-01.txt lines 1767–1768: "By
choosing the subsequences successively and taking a diagonal sequence, we then get a subsequence
`μ_{k'}` …").  If every strictly increasing `ψ` has a strictly increasing refinement `ψ ∘ θ` along
which `s i` converges for all `i ∈ F m`, then one strictly increasing `φ` makes `s i ∘ φ` converge
for every `m` and every `i ∈ F m`.  Successive refinements `ψ₀ = Θ 0 id`,
`ψ_{m+1} = ψ_m ∘ Θ (m + 1) ψ_m` give the diagonal `φ j = ψ_j j`, whose tail
`φ (m + k) = ψ_m (τ_k (m + k))` is a subsequence of `ψ_m`. -/
theorem Submission.cbr_ct_vs_diagonal_subseq : ∀ (ι : Type) (F : ℕ → Set ι) (s : ι → ℕ → ℝ), (∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (ψ (θ j))) atTop (𝓝 c)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (φ j)) atTop (𝓝 c) := by
  intro ι F s h
  -- Step 2: choice `Θ m ψ` of a strictly increasing refinement of `ψ` convergent on `F m`
  choose Θ hΘ hΘconv using h
  -- Step 3: `ψ₀ = Θ 0 id`, `ψ_{m+1} = ψ_m ∘ Θ (m + 1) ψ_m`, carried with `StrictMono`
  let ψ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun m =>
    Nat.rec ⟨Θ 0 id strictMono_id, hΘ 0 id strictMono_id⟩
      (fun m p => ⟨p.1 ∘ Θ (m + 1) p.1 p.2, p.2.comp (hΘ (m + 1) p.1 p.2)⟩) m
  have hgood : ∀ m, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i ((ψ m).1 j)) atTop (𝓝 c) := by
    intro m
    cases m with
    | zero => exact hΘconv 0 id strictMono_id
    | succ m => exact hΘconv (m + 1) (ψ m).1 (ψ m).2
  -- Step 4: `ψ_{m+k} = ψ_m ∘ τ` with `τ` strictly increasing
  have hfac : ∀ m k, ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ n, (ψ (m + k)).1 n = (ψ m).1 (τ n) := by
    intro m k
    induction k with
    | zero => exact ⟨id, strictMono_id, fun n => rfl⟩
    | succ k ih =>
      obtain ⟨τ, hτ, hτeq⟩ := ih
      exact ⟨τ ∘ Θ (m + k + 1) (ψ (m + k)).1 (ψ (m + k)).2, hτ.comp (hΘ _ _ _),
        fun n => hτeq (Θ (m + k + 1) (ψ (m + k)).1 (ψ (m + k)).2 n)⟩
  -- Step 5: the diagonal `φ j = ψ_j j`; `ψ_{j+1} (j + 1) = ψ_j (Θ _ _ _ (j + 1)) ≥ ψ_j (j + 1)`
  let φ : ℕ → ℕ := fun j => (ψ j).1 j
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun j =>
    ((ψ j).2 (Nat.lt_add_one j)).trans_le
      ((ψ j).2.monotone (hΘ (j + 1) (ψ j).1 (ψ j).2).le_apply)
  refine ⟨φ, hφ, fun m i hi => ?_⟩
  -- Step 6: `φ (m + k) = ψ_m (σ k)` with `σ k = τ_k (m + k)` strictly increasing
  choose τ hτ hτeq using hfac m
  have hφτ : ∀ k, φ (m + k) = (ψ m).1 (τ k (m + k)) := fun k => hτeq k (m + k)
  have hσ : StrictMono fun k => τ k (m + k) := strictMono_nat_of_lt_succ fun k => by
    have h1 : φ (m + k) < φ (m + (k + 1)) := hφ (Nat.lt_add_one (m + k))
    rw [hφτ, hφτ] at h1
    exact (ψ m).2.lt_iff_lt.mp h1
  -- Step 7: compose with `σ → ∞` and undo the index shift by `m`
  obtain ⟨c, hc⟩ := hgood m i hi
  refine ⟨c, (tendsto_add_atTop_iff_nat m).mp ((hc.comp hσ.tendsto_atTop).congr fun k => ?_)⟩
  show s i ((ψ m).1 (τ k (m + k))) = s i (φ (k + m))
  rw [add_comm k m, hφτ]

/-- **Vague selection on an open set** (Simon Ch. 1, Theorem 4.16 and its proof, chapter-01.txt
lines 1750–1778, for `X = U` open in `ℝᴾ`).  If `supⱼ μⱼ(K) < ∞` for every compact `K ⊆ U`, one
strictly increasing `φ` makes `∫ f dμ_{φ(j)}` converge for every continuous `f` with compact
support in `U`.  Exhaust `U` by compact `Kₘ ⊆ U`; the one-piece selection (the Alaoglu step,
corrected to a genuine subsequence) refines any strictly increasing `ψ` on `Kₘ`, because
`supⱼ μ_{ψ(j)}(Kₘ) ≤ supⱼ μⱼ(Kₘ) < ∞`, and the diagonal argument yields `φ`.  The compact
`tsupport f ⊆ U` lies in some `Kₘ`. -/
theorem Submission.cbr_vague_convergent_subseq : ∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 c) := by
  intro P U μs hU hμ
  -- Step 1: compact `Kₘ ⊆ U` such that every compact subset of `U` lies in some `Kₘ`
  obtain ⟨K, hK, hKU, hKC⟩ := Submission.cbr_ct_vs_compact_exhaustion P U hU
  -- Steps 2–6: diagonal subsequence for `F m = {f | f continuous, tsupport f ⊆ Kₘ}` and
  -- `s f j = ∫ f dμⱼ`; Claim A refines `ψ` on `Kₘ`, as `supⱼ μ_{ψ(j)}(Kₘ) ≤ supⱼ μⱼ(Kₘ) < ∞`
  obtain ⟨φ, hφ, hconv⟩ := Submission.cbr_ct_vs_diagonal_subseq (Euclid P → ℝ)
    (fun m => {f | Continuous f ∧ tsupport f ⊆ K m}) (fun f j => ∫ x, f x ∂(μs j))
    fun m ψ _ => by
      obtain ⟨θ, hθ, hθc⟩ := Submission.cbr_ct_vs_compact_piece_subseq P (K m)
        (fun j => μs (ψ j)) (hK m)
        ((iSup_comp_le (fun j => μs j (K m)) ψ).trans_lt (hμ (K m) (hK m) (hKU m)))
      exact ⟨θ, hθ, fun f hf => hθc f hf.1 hf.2⟩
  -- Step 7: the compact `tsupport f ⊆ U` lies in some `Kₘ`
  refine ⟨φ, hφ, fun f hf hfc hfU => ?_⟩
  obtain ⟨m, hm⟩ := hKC (tsupport f) hfc.isCompact hfU
  exact hconv m f ⟨hf, hm⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
