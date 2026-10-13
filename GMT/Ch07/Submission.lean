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

/-- **Coordinate projections of `Hⁿ`-null sets are Lebesgue-null** (parent step 3).  For
injective `I : Fin n → Fin P` the coordinate projection `q x = (x (I k))ₖ : ℝᴾ → ℝⁿ` is
`1`-Lipschitz (the squares summed over `image I` are among those summed over `Fin P`), so
`μH[n] (q '' C) ≤ μH[n] C`.  `μHE[n] = c • μH[n]` with one nonzero constant `c` on every space,
and `μHE[n] = volume` on `ℝⁿ`; hence `μHE[n] C = 0` gives `volume (q '' C) = 0`.  No compactness
of `C` is needed. -/
theorem Submission.cmr_volume_coordProj_image_null : ∀ (P n : ℕ) (I : Fin n → Fin P) (C : Set (Euclid P)), Function.Injective I → μHE[n] C = 0 → volume ((fun x : Euclid P => (WithLp.toLp 2 (fun k => x (I k)) : Euclid n)) '' C) = 0 := by
  intro P n I C hI hC
  set q : Euclid P → Euclid n := fun x => WithLp.toLp 2 (fun k => x (I k))
  -- `q` is 1-Lipschitz: the squares summed over `image I` are among those summed over `Fin P`
  have hq : LipschitzWith 1 q := by
    refine LipschitzWith.mk_one fun x y => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ k, dist ((q x).ofLp k) ((q y).ofLp k) ^ 2
        = ∑ k, dist (x.ofLp (I k)) (y.ofLp (I k)) ^ 2 := rfl
      _ = ∑ l ∈ Finset.univ.image I, dist (x.ofLp l) (y.ofLp l) ^ 2 := by
        rw [Finset.sum_image fun _ _ _ _ h => hI h]
      _ ≤ ∑ l, dist (x.ofLp l) (y.ofLp l) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  -- `μHE[n] = c • μH[n]` with `c ≠ 0`, so `μH[n] C = 0`
  have hc : (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
      μH[(n : ℝ)] : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at hC
  have hC' : μH[(n : ℝ)] C = 0 := (mul_eq_zero.mp hC).resolve_left hc
  -- `μH[n] (q '' C) ≤ 1 ^ n * μH[n] C = 0`
  have hqC : μH[(n : ℝ)] (q '' C) = 0 := by
    have h := hq.hausdorffMeasure_image_le (Nat.cast_nonneg n) C
    rw [hC', mul_zero] at h
    exact nonpos_iff_eq_zero.mp h
  -- on `ℝⁿ`, `volume = μHE[n] = c • μH[n]`
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hqC, smul_zero]
/-- **Simon 6.2.36** (`μ_T ≪ Hⁿ` for locally normal `T`; mass bound for the divergence
integral): let `T ∈ 𝒟_{m+1}(U)` satisfy `T(ω) = ∫ ⟨ω, ξ⟩ dμ`, and let `η`, `ζ` be test forms
supported in `spt b ⊆ W ⊆ U` with `|η|, |ζ| ≤ K` and `dη = b D θ + ζ`.  Then `ω = dη − ζ` is
a test form in `U` with `ω(x) = b(x) D(x) θ`, so `∫_W b ⟨θ, ξ⟩ D dμ = T(ω) = ∂T(η) − T(ζ)`,
and the evaluation bound gives `|∫_W b ⟨θ, ξ⟩ D dμ| ≤ K (M_W(∂T) + M_W(T))`. -/
theorem Submission.cmr_abs_integral_div_le_mass : ∀ (P m : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (m + 1)) (θ : Covector (Euclid P) (m + 1)) (b D : Euclid P → ℝ) (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)) (K : ℝ), W ⊆ U → T.massOn W ≠ ∞ → T.boundary.massOn W ≠ ∞ → (∀ ω : TestFormOn U (m + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μ) → (∀ (k : ℕ) (S : GeometricCurrentOn U k) (ω : TestFormOn U k) (r : ℝ), S.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) k) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ r) → |S ω| ≤ r * (S.massOn W).toReal) → tsupport b ⊆ W → IsTestForm η → IsTestForm ζ → tsupport η ⊆ tsupport b → tsupport ζ ⊆ tsupport b → (∀ x, covectorEuclideanNorm (η x) ≤ K) → (∀ x, covectorEuclideanNorm (ζ x) ≤ K) → (∀ x, exteriorDerivative η x = (b x * D x) • θ + ζ x) → |∫ x, b x * ξ x θ * D x ∂(μ.restrict W)| ≤ K * ((T.boundary.massOn W).toReal + (T.massOn W).toReal) := by
  intro P m U W T μ ξ θ b D η ζ K hWU hT hbT hrep hEB hb hη hζ hηb hζb hηK hζK hd
  -- `η`, `ζ` are test forms in `U`, supported in `spt b ⊆ W`
  have hηW : tsupport η ⊆ W := hηb.trans hb
  have hζW : tsupport ζ ⊆ W := hζb.trans hb
  let η' : TestFormOn U m := ⟨η, hη, hηW.trans hWU⟩
  let ζ' : TestFormOn U (m + 1) := ⟨ζ, hζ, hζW.trans hWU⟩
  -- `ω = dη − ζ` has `ω(x) = b(x) D(x) θ`
  have hω : ∀ x, ((exteriorDerivativeTestOn U m η' - ζ' : TestFormOn U (m + 1)) :
      DifferentialForm (Euclid P) (m + 1)) x = (b x * D x) • θ := by
    intro x
    change exteriorDerivative η x - ζ x = _
    rw [hd x, add_sub_cancel_right]
  -- `T(ω) = ∂T(η) − T(ζ)`, and the evaluation bound controls both terms
  have hTω : T (exteriorDerivativeTestOn U m η' - ζ') = T.boundary η' - T ζ' := by
    rw [GeometricCurrentOn.boundary_apply]
    exact map_sub T.toCurrent _ _
  have h1 : |T.boundary η'| ≤ K * (T.boundary.massOn W).toReal :=
    hEB m T.boundary η' K hbT hηW hηK
  have h2 : |T ζ'| ≤ K * (T.massOn W).toReal := hEB (m + 1) T ζ' K hT hζW hζK
  -- `b = 0` off `W`, so the integral over `W` is `T(ω)`
  have hint : ∫ x, b x * ξ x θ * D x ∂(μ.restrict W) =
      T (exteriorDerivativeTestOn U m η' - ζ') := by
    rw [hrep, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · congr 1
      funext x
      rw [hω x, map_smul, smul_eq_mul]
      ring
    · intro x hx
      have hbx : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hb h)
      rw [hbx, zero_mul, zero_mul]
  rw [hint, hTω, mul_add]
  exact (abs_sub _ _).trans (add_le_add h1 h2)
/-- Localization of the null-set argument (steps 5 and 6 of the null-set step of the mass
representation used for Simon 7.2.4): let `W ⊆ ℝᴾ` be open with `μ(W) < ∞`, `f` `μ`-a.e. strongly
measurable with `|f| ≤ c`, `q : ℝᴾ → ℝⁿ` measurable and `N ⊆ ℝⁿ` measurable.  Assume (TD): for a
finite `ν` and `ν`-integrable `h`, a bound `|∫ h · div g(q) dν| ≤ Λ` over all smooth compactly
supported `g` with `‖g‖ ≤ 1` forces `∫_{q⁻¹(N)} h dν = 0`; and (DB): for every smooth `b` compactly
supported in `W` such a bound holds for `h = b f` and `ν = μ⌞W`.  Then `f = 0` `μ`-a.e. on
`W ∩ q⁻¹(N)`.  The function `F := 1_{q⁻¹(N)} f` is bounded, hence locally integrable on `W`;
since `b` vanishes off `W`, (DB) and (TD) give `∫ b F dμ = ∫_{q⁻¹(N)} b f d(μ⌞W) = 0` for every
such `b`, and `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `F = 0` `μ`-a.e. on
`W`. -/
theorem Submission.cmr_ae_zero_of_div_bounds : ∀ (P n : ℕ) (W : Set (Euclid P)) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (q : Euclid P → Euclid n) (N : Set (Euclid n)) (c : ℝ), IsOpen W → μ W < ∞ → AEStronglyMeasurable f μ → (∀ x, |f x| ≤ c) → Measurable q → MeasurableSet N → (∀ (ν : Measure (Euclid P)) (h : Euclid P → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∫ x in q ⁻¹' N, h x ∂ν = 0) → (∀ b : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ W → ∃ Λ : ℝ, ∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, b x * f x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂(μ.restrict W)| ≤ Λ) → ∀ᵐ x ∂μ, x ∈ W → q x ∈ N → f x = 0 := by
  intro P n W μ f q N c hW hμW hf hfc hq hN hTD hDB
  -- Step 1: `A := q⁻¹(N)` is measurable, `μ⌞W` is finite, `c ≥ 0`
  have hA : MeasurableSet (q ⁻¹' N) := hq hN
  have : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.2 hμW.ne
  have hc : 0 ≤ c := (abs_nonneg _).trans (hfc 0)
  -- Step 2: `F := 1_A f` is bounded by `c`, hence locally integrable on `W`
  have hFb : ∀ x, ‖(q ⁻¹' N).indicator f x‖ ≤ c := by
    intro x
    by_cases hx : x ∈ q ⁻¹' N
    · rw [indicator_of_mem hx, Real.norm_eq_abs]
      exact hfc x
    · rw [indicator_of_notMem hx, norm_zero]
      exact hc
  have hFloc : LocallyIntegrableOn ((q ⁻¹' N).indicator f) W μ :=
    IntegrableOn.locallyIntegrableOn
      (Integrable.of_bound (hf.indicator hA).restrict c (Eventually.of_forall hFb))
  -- Step 4: localization, once the integrals of step 3 vanish
  have hF0 : ∀ᵐ x ∂μ, x ∈ W → (q ⁻¹' N).indicator f x = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hFloc ?_
    -- Step 3: `∫ b • F dμ = 0` for smooth `b` compactly supported in `W`
    intro b hb hbc hbW
    -- (a) `h := b f` is `μ⌞W`-integrable
    obtain ⟨B, hB⟩ := hb.continuous.bounded_above_of_compact_support hbc
    have hh : Integrable (fun x => b x * f x) (μ.restrict W) := by
      refine Integrable.of_bound (hb.continuous.aestronglyMeasurable.mul hf.restrict) (B * c)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs (f x)]
      exact mul_le_mul (hB x) (hfc x) (abs_nonneg _) ((norm_nonneg _).trans (hB x))
    -- (b) (DB) and (TD) give `∫_A b f d(μ⌞W) = 0`
    obtain ⟨Λ, hΛ⟩ := hDB b hb hbc hbW
    have h0 : ∫ x in q ⁻¹' N, b x * f x ∂(μ.restrict W) = 0 :=
      hTD (μ.restrict W) (fun x => b x * f x) Λ inferInstance hh hΛ
    -- (c) `b` vanishes off `W`, so `∫ b • F dμ = ∫ b • F d(μ⌞W)`
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (hbW hx'), zero_smul]]
    -- (d) `b • F = 1_A (b f)`, and (e) conclude
    have hbF : (fun x => b x • (q ⁻¹' N).indicator f x) =
        (q ⁻¹' N).indicator fun x => b x * f x := by
      funext x
      by_cases hx : x ∈ q ⁻¹' N
      · rw [indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    rw [hbF, integral_indicator hA]
    exact h0
  -- Step 5: on `W ∩ q⁻¹(N)`, `f = F = 0`
  filter_upwards [hF0] with x hx hxW hxN
  rw [← indicator_of_mem (show x ∈ q ⁻¹' N from hxN) f]
  exact hx hxW
/-- **The mass measure vanishes where the orientation vanishes** (parent step 8 of the
representation `T = μ_T ∧ ξ⃗`).  Let `W ⊇ C` be measurable with `μ(W) < ∞` and `M_W(T) = μ(W)`,
let `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x` and all covectors `α` (`|·|_E` is
`covectorEuclideanNorm`), and let `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)` for every test form `ω`.  If
`ξ = 0` `μ`-a.e. on `C`, then `μ(C) = 0`.  Fix an admissible `ω`, i.e. `tsupport ω ⊆ W` and
`|ω|_E ≤ 1`, and let `f(x) = ⟨ω(x), ξ(x)⟩`.  For `μ`-a.e. `x`, `|f(x)| ≤ 1_{W \ C}(x)`: `f = 0`
on `C` (where `ξ = 0`) and off `W` (where `ω = 0`), and `|f| ≤ |ω|_E ≤ 1` on `W \ C`.  Hence
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_{W \ C} dμ = μ(W \ C)`, whether or not `f` is integrable.
Taking the supremum gives `μ(W) = M_W(T) ≤ μ(W \ C)`, and `μ(W \ C) + μ(C) = μ(W)` with
`μ(W \ C) < ∞` forces `μ(C) = 0`. -/
theorem Submission.cmr_measure_null_of_orient_ae_zero : ∀ (P n : ℕ) (U W C : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), MeasurableSet W → MeasurableSet C → C ⊆ W → μ W < ∞ → T.massOn W = μ W → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → (∀ᵐ x ∂μ, x ∈ C → ξ x = 0) → μ C = 0 := by
  intro P n U W C T μ ξ hW hC hCW hμW hmass hξ hT hzero
  -- Step 1: `M_W(T) ≤ μ(W \ C)`; it suffices to bound `ofReal (T ω)` for each admissible `ω`
  have hle : T.massOn W ≤ μ (W \ C) := by
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    -- `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_{W \ C}(x)` for `μ`-a.e. `x`
    have hpt : ∀ᵐ x ∂μ,
        ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ (W \ C).indicator 1 x := by
      filter_upwards [hzero] with x hx
      by_cases hxC : x ∈ C
      · rw [hx hxC, zero_apply, enorm_zero]
        exact zero_le
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem (show x ∈ W \ C from ⟨hxW, hxC⟩), Pi.one_apply,
          Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
      · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hω.1 h), map_zero, enorm_zero]
        exact zero_le
    calc ENNReal.ofReal (T ω)
        = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
      _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, (W \ C).indicator 1 x ∂μ := lintegral_mono_ae hpt
      _ = μ (W \ C) := lintegral_indicator_one (hW.diff hC)
  -- Step 2: cancel the finite `μ(W \ C)` in `μ(W \ C) + μ(C) = μ(W) ≤ μ(W \ C) + 0`
  have hsplit : μ (W \ C) + μ C = μ W := by
    simpa only [inter_eq_right.mpr hCW] using measure_sdiff_add_inter (μ := μ) W hC
  have hfin : μ (W \ C) ≠ ∞ := ((measure_mono Set.sdiff_subset).trans_lt hμW).ne
  refine nonpos_iff_eq_zero.mp ((ENNReal.add_le_add_iff_left hfin).mp ?_)
  rw [hsplit, add_zero, ← hmass]
  exact hle
/-- Null sets from compact null sets (last step of the proof that the mass measure `μ_T` of a
locally normal current vanishes on `Hⁿ`-null sets, Simon 6.2.36, used for 7.2.4): let `U ⊆ ℝᴾ` be
open and `μ`, `ν` measures on `ℝᴾ` with `μ(ℝᴾ \ U) = 0`, `μ(K) < ∞` for compact `K ⊆ U`, and
`μ(C) = 0` for every compact `C ⊆ U` with `ν(C) = 0`.  Then every `ν`-null set is `μ`-null.
Take a measurable `ν`-null hull `E' ⊇ E` and exhaust `U` by the compact sets `Fᵢ ∩ B̄ⱼ(0)`,
`Fᵢ ⊆ U` closed.  Each `μ⌞(Fᵢ ∩ B̄ⱼ(0))` is finite, hence inner regular, so `μ(E' ∩ Fᵢ ∩ B̄ⱼ(0)) > 0`
would give a compact `C ⊆ E'` with `μ(C ∩ Fᵢ ∩ B̄ⱼ(0)) > 0`, contradicting the hypothesis. -/
theorem Submission.cmr_null_of_compact_null : ∀ (P : ℕ) (U : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ν C = 0 → μ C = 0) → ∀ E : Set (Euclid P), ν E = 0 → μ E = 0 := by
  intro P U μ ν hU hUc hfin hnull E hE
  -- Step 1: a measurable `ν`-null hull `E' ⊇ E`
  obtain ⟨E', hEE', hE'm, hE'⟩ := exists_measurable_superset_of_null hE
  -- Step 2: `U = ⋃ₚ Kₚ` with `K_{(i,j)} = Fᵢ ∩ B̄ⱼ(0)` compact, `Fᵢ ⊆ U` closed
  obtain ⟨F, hFc, hFU, hFun, -⟩ := hU.exists_iUnion_isClosed
  have hK : ∀ p : ℕ × ℕ, IsCompact (F p.1 ∩ closedBall (0 : Euclid P) p.2) := fun p =>
    (isCompact_closedBall _ _).inter_left (hFc p.1)
  have hKU : ∀ p : ℕ × ℕ, F p.1 ∩ closedBall (0 : Euclid P) p.2 ⊆ U := fun p =>
    inter_subset_left.trans (hFU p.1)
  have hcover : U ⊆ ⋃ p : ℕ × ℕ, F p.1 ∩ closedBall (0 : Euclid P) p.2 := by
    intro x hx
    rw [← hFun] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge (dist x 0)
    exact mem_iUnion.2 ⟨(i, j), hi, mem_closedBall.2 hj⟩
  -- Step 3: `μ(E' ∩ Kₚ) = 0` for every `p`, by inner regularity of the finite `μ⌞Kₚ`
  have hpiece : ∀ p : ℕ × ℕ, μ (E' ∩ (F p.1 ∩ closedBall (0 : Euclid P) p.2)) = 0 := by
    intro p
    set K := F p.1 ∩ closedBall (0 : Euclid P) p.2
    have : IsFiniteMeasure (μ.restrict K) :=
      isFiniteMeasure_restrict.2 (hfin K (hK p) (hKU p)).ne
    by_contra hne
    have hpos : 0 < μ.restrict K E' := by
      rw [Measure.restrict_apply hE'm]
      exact pos_iff_ne_zero.2 hne
    obtain ⟨C, hCE', hCc, hCpos⟩ := hE'm.exists_lt_isCompact_of_ne_top (measure_ne_top _ _) hpos
    rw [Measure.restrict_apply hCc.isClosed.measurableSet] at hCpos
    have hC0 : μ (C ∩ K) = 0 :=
      hnull (C ∩ K) (hCc.inter_right (hK p).isClosed) (inter_subset_right.trans (hKU p))
        (measure_mono_null (inter_subset_left.trans hCE') hE')
    exact hCpos.ne' hC0
  -- Step 4: `E ⊆ E' ⊆ Uᶜ ∪ ⋃ₚ (E' ∩ Kₚ)`, a `μ`-null set
  refine measure_mono_null hEE' (measure_mono_null (t := Uᶜ ∪
    ⋃ p : ℕ × ℕ, E' ∩ (F p.1 ∩ closedBall (0 : Euclid P) p.2)) ?_
    (measure_union_null hUc (measure_iUnion_null hpiece)))
  intro x hx
  by_cases hxU : x ∈ U
  · obtain ⟨p, hp⟩ := mem_iUnion.1 (hcover hxU)
    exact Or.inr (mem_iUnion.2 ⟨p, hx, hp⟩)
  · exact Or.inl hxU
/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))
/-- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
`n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
formula, and the Leibniz formula with `|x(l)| ≤ ‖x‖` gives `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`, so
`θ⁰` is continuous. -/
theorem Submission.cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
  intro P n I
  -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => x (I k)
      map_add' := fun x y => by
        funext k
        simp
      map_smul' := fun c x => by
        funext k
        simp }
  -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
  let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
  have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  -- Step 4: the Leibniz formula, `|sign σ| = 1` and `|x(l)| ≤ ‖x‖` give
  -- `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`
  have hbound : ∀ v : Fin n → Euclid P, ‖θ₀ v‖ ≤ (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
    intro v
    rw [hθ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, ‖v j‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| =
              ∏ j, |v j (I (σ j))| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [hσ]
          gcongr with j
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (v j) (I (σ j))
      _ = (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  -- Step 5: `θ = θ⁰.mkContinuous n!` is an `n`-covector with the same values as `θ⁰`
  exact ⟨θ₀.mkContinuous (n.factorial : ℝ) hbound, hθ₀⟩
/-- **Kronecker property of the determinant covectors** (Simon 6.1, chapter-06.txt lines 22–47:
`dxʲ(v) = vⱼ`, `dx^{i₁} ∧ ⋯ ∧ dx^{iₙ}(v₁, …, vₙ) = det(dx^{iₖ}(vⱼ))` (1.1), and
`ω_α = ω(e_{i₁}, …, e_{iₙ})` for the basis `{dx^α : α ∈ I_{n,P}}` (1.2)): if `I`, `J` are strictly
increasing and `θ(v) = det (v_j(I k))_{k,j}`, then `θ(e_{J 1}, …, e_{J n}) = δ_{IJ}`.  The matrix
of `θ(e_J)` has entries `[I k = J j]`.  It is the identity if `I = J`.  Otherwise some `I k₀` is
not a value of `J` (else `range I ⊆ range J`, both have `n` elements, so the ranges agree and the
strictly increasing maps agree), and row `k₀` vanishes. -/
theorem Submission.cmr_cc_det_covector_basis_kronecker : ∀ (P n : ℕ) (I J : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → StrictMono J → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → θ (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 := by
  intro P n I J θ hI hJ hθ
  -- Step 1: `θ(e_J) = det M` with `M k j = e_{J j}(I k)`
  rw [hθ]
  -- Step 2: `M k j = e_{J j}(I k) = if I k = J j then 1 else 0`
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hIJ : I = J
  · -- Step 3: if `I = J`, injectivity of `J` gives `M = 1`, so `det M = 1`
    rw [ite_eq_left hIJ]
    subst hIJ
    refine (congrArg Matrix.det ?_).trans Matrix.det_one
    ext k j
    simp only [Matrix.of_apply, Matrix.one_apply, hI.injective.eq_iff]
  · -- Step 4: if `I ≠ J`, some `I k₀` is not a value of `J`: otherwise `range I ⊆ range J`,
    -- both ranges have `n` elements, so they are equal and `I = J`
    rw [ite_eq_right hIJ]
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, I k₀ ∉ Set.range J := by
      by_contra hcon
      have hsub : Set.range I ⊆ Set.range J := by
        rintro _ ⟨k, rfl⟩
        by_contra hk
        exact hcon ⟨k, hk⟩
      have hcard : (Set.range J).ncard ≤ (Set.range I).ncard :=
        ((Set.ncard_range_of_injective hJ.injective).trans
          (Set.ncard_range_of_injective hI.injective).symm).le
      exact hIJ ((hI.range_inj_of_wellFoundedLT hJ).1 (Set.eq_of_subset_of_ncard_le hsub hcard))
    -- Step 5: row `k₀` of `M` vanishes, so `det M = 0`
    refine Matrix.det_eq_zero_of_row_eq_zero k₀ fun j => ?_
    simp only [Matrix.of_apply]
    exact ite_eq_right fun hEq => hk₀ ⟨j, hEq.symm⟩
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]

/-- **Simon 6.1.2, 6.1.5, 6.1.15** (the coefficient norm is Euclidean): `n`-covectors on `ℝᴾ`
with `|α|_E = (Σ_I α(e_I)²)^{1/2}`, `I` strictly increasing, form a Euclidean space `ℝᵈ`.  The
coefficient map `A α = (α(e_I))_I` (zero off the increasing `I`) into `ℝ^{Fin n → Fin P}` has
`‖A α‖ = |α|_E`, and it is injective by the Gram bound `|α v| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}`.
An orthonormal basis of `range A` identifies it isometrically with `ℝᵈ`; then covectors are
finite-dimensional, so this linear equivalence is continuous. -/
theorem Submission.cmr_covector_euclidean_equiv : ∀ (P n : ℕ), ∃ (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖ := by
  intro P n
  -- the coefficient map `A α = (α(e_I))_I`, zero off the strictly increasing `I`
  let A : Covector (Euclid P) n →ₗ[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    { toFun := fun α => WithLp.toLp 2 (fun I => if StrictMono I then
        α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) else 0)
      map_add' := fun α β => by
        ext I
        simp only [PiLp.add_apply, ContinuousAlternatingMap.add_apply]
        split_ifs <;> simp
      map_smul' := fun t α => by
        ext I
        simp only [PiLp.smul_apply, ContinuousAlternatingMap.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        split_ifs <;> simp }
  -- `‖A α‖ = |α|_E`
  have hnorm : ∀ α, ‖A α‖ = covectorEuclideanNorm α := by
/-- **Jacobi's trace identity for column replacement** (parent fact (F3) of the divergence form
of the mass representation).  Let `M = (u j k)_{k,j}` be the matrix with columns `u j`.
Replacing column `i` by `A (u i)` and summing the determinants over `i` gives `tr(A) · det M`.
With `B` the matrix of `A` in the standard basis `e` of `ℝⁿ`, column `i` of `B M` is `A (u i)`,
so by Cramer's rule the `i`-th determinant is `(adj M · B M)_{i,i}`; then
`tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr B = det M · tr A`. -/
theorem Submission.cmr_df_det_update_sum_trace : ∀ (n : ℕ) (A : Euclid n →ₗ[ℝ] Euclid n) (u : Fin n → Euclid n), ∑ i : Fin n, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) = LinearMap.trace ℝ (Euclid n) A * Matrix.det (Matrix.of fun k j => u j k) := by
  intro n A u
  -- the standard basis `e` of `ℝⁿ`, the matrix `M` with columns `u j`, the matrix `B` of `A`
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => u j k
  let B := LinearMap.toMatrix e e A
  -- Step 1: `A (u i) k = (B M)_{k,i}`, from `B *ᵥ e.repr x = e.repr (A x)` and `e.repr x = x`
  have hA : ∀ i k, A (u i) k = (B * M) k i := by
    intro i k
    have := congrFun (LinearMap.toMatrix_mulVec_repr e e A (u i)) k
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, e, B, M] using this.symm
  -- Step 2: the `i`-th summand is `det (M.updateCol i (B M)_{·,i}) = (adj M · B M)_{i,i}` (Cramer)
  have hcol : ∀ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
      (M.adjugate * (B * M)) i i := by
    intro i
    have h1 : (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
        M.updateCol i (fun k => (B * M) k i) := by
      ext k j
      by_cases hj : j = i
      · subst hj
        simp [hA]
      · simp [hj, M]
    rw [h1, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  -- Step 3: `tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr A`
  calc ∑ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k)
      = Matrix.trace (M.adjugate * (B * M)) := by
        simp only [hcol, Matrix.trace, Matrix.diag_apply]
    _ = Matrix.trace (B * (M * M.adjugate)) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = LinearMap.trace ℝ (Euclid n) A * M.det := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
          LinearMap.trace_eq_matrix_trace ℝ e A, mul_comm]

/-- **Coordinate form of `Σᵢ (-1)ⁱ θ(L wᵢ, w₀, …, ŵᵢ, …, w_m) = tr(A) θ(w)`** (the trace step of
the divergence-form computation behind the mass representation in Simon 7.2.4).  Let `θ` be the
`(m+1)`-covector `θ(v) = det (v j (I k))_{k,j}` on `ℝᴾ`, let `A` be linear on `ℝ^{m+1}`, and let
`L : ℝᴾ → ℝᴾ` satisfy `(L v)(I k) = (A (p v))_k` with `p v = (v (I k))_k`.  Moving `L wᵢ` from
the front to slot `i` costs `(-1)ⁱ`, so the `i`-th term is `θ(w)` with `wᵢ` replaced by `L wᵢ`.
In the coordinates `uⱼ = p wⱼ` it is the determinant of `u` with its `i`-th column replaced by
`A uᵢ`.  Jacobi's identity `Submission.cmr_df_det_update_sum_trace` sums these determinants to
`tr(A) det u`, and `det u = θ(w)`. -/
theorem Submission.cmr_df_cons_sum_trace : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (L : Euclid P → Euclid P), (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → (∀ (v : Euclid P) (k : Fin (m + 1)), L v (I k) = A (WithLp.toLp 2 (fun k' => v (I k'))) k) → ∀ w : Fin (m + 1) → Euclid P, ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons (L (w i)) (i.removeNth w)) = LinearMap.trace ℝ (Euclid (m + 1)) A * θ w := by
  intro P m I θ A L hθ hL w
  -- Step 1: sign rule, `(-1)ⁱ θ(x, w₀, …, ŵᵢ, …, w_m) = θ(w with wᵢ replaced by x)`
  have h1 : ∀ (i : Fin (m + 1)) (x : Euclid P),
      (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons x (i.removeNth w)) = θ (Function.update w i x) := by
    intro i x
    rw [← Fin.insertNth_removeNth, ContinuousAlternatingMap.map_insertNth, zsmul_eq_mul]
    push_cast
    rfl
  -- the coordinate columns `uⱼ = p wⱼ ∈ ℝ^{m+1}`
  let u : Fin (m + 1) → Euclid (m + 1) := fun j => WithLp.toLp 2 (fun k => w j (I k))
  -- Step 2: the `i`-th term is `det u` with its `i`-th column replaced by `A uᵢ`, entrywise
  have h2 : ∀ i : Fin (m + 1), θ (Function.update w i (L (w i))) =
      Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) := by
    intro i
    rw [hθ]
    congr 1
    ext k j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, u]
    · simp [Function.update_of_ne hj, u]
  -- Step 4: `det u = θ(w)`
  have h4 : Matrix.det (Matrix.of fun k j => u j k) = θ w := (hθ w).symm
  -- Step 3: Jacobi's identity
  simp_rw [h1, h2]
  rw [Submission.cmr_df_det_update_sum_trace (m + 1) A u, h4]
/-- **Exterior derivative of a function times a contracted covector** (used for the divergence
form in the mass-representation step of Simon 7.2.4).  If `b : ℝᴾ → ℝ` and `G : ℝᴾ → ℝᴾ` are
differentiable at `x` and `θ` is a fixed `(m+1)`-covector, then `η(y) = b(y) θ(G(y), ·)` has
`dη(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ (Db(x)wᵢ · θ(G(x), ŵᵢ) + b(x) · θ(DG(x)wᵢ, ŵᵢ))`, where `ŵᵢ` is
`(w₀, …, w_m)` with `wᵢ` removed: each term of the alternating sum differentiates
`y ↦ b(y) θ(G(y), ŵᵢ)` by the product and chain rules. -/
theorem Submission.cmr_df_extDeriv_smul_curryLeft : ∀ (P m : ℕ) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ) (G : Euclid P → Euclid P) (x : Euclid P), DifferentiableAt ℝ b x → DifferentiableAt ℝ G x → ∀ w : Fin (m + 1) → Euclid P, exteriorDerivative (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w))) := by
  intro P m θ b G x hb hG w
  have hc : DifferentiableAt ℝ (fun y => ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    (ContinuousAlternatingMap.curryLeft θ).differentiableAt.comp x hG
  have hη : DifferentiableAt ℝ (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    hb.smul hc
  rw [exteriorDerivative_apply hη w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_continuousAlternatingMap_apply_const_apply hη, fderiv_fun_smul hb hc,
    fderiv_fun_comp x (ContinuousAlternatingMap.curryLeft θ).differentiableAt hG,
    ContinuousLinearMap.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    smul_eq_mul, zsmul_eq_mul]
  simp only [Matrix.vecCons]
  push_cast
  ring
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
    simp only [A, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    split_ifs <;> simp
  -- `A` is injective: `|α|_E = 0` forces `α v = 0` by the Gram bound
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have h0 : covectorEuclideanNorm α = 0 := by rw [← hnorm, hα, norm_zero]
    ext v
    have hv := (Submission.covectorEuclideanNorm_gram_bounds P n).1 α v
    rw [h0, zero_mul] at hv
    simpa using abs_nonpos_iff.mp hv
  -- identify `range A` isometrically with `ℝᵈ` through an orthonormal basis
  let S := LinearMap.range A
  let b := stdOrthonormalBasis ℝ S
  let e₀ : Covector (Euclid P) n ≃ₗ[ℝ] S := LinearEquiv.ofInjective A hinj
  let c₀ : Covector (Euclid P) n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S)) :=
    e₀.trans b.repr.toLinearEquiv
  have hc₀ : ∀ α, ‖c₀ α‖ = covectorEuclideanNorm α := by
    intro α
    have h1 : c₀ α = b.repr (e₀ α) := rfl
    rw [h1, LinearIsometryEquiv.norm_map, ← Submodule.norm_coe, LinearEquiv.ofInjective_apply,
      hnorm]
  -- covectors are finite-dimensional, so `c₀` is continuous
  have : FiniteDimensional ℝ (Covector (Euclid P) n) := LinearEquiv.finiteDimensional c₀.symm
  refine ⟨Module.finrank ℝ S, c₀.toContinuousLinearEquiv, fun α => ?_⟩
  rw [LinearEquiv.coe_toContinuousLinearEquiv', hc₀]

/-- **Simon 6.1.1–1.2** (coordinate covectors): (a) for every `I` the coordinate covector
`dx^I(v) = det(v_j(I k))_{k,j}` exists; (b) an `n`-vector vanishing on `dx^I` for every strictly
increasing `I` vanishes.  Every `n`-covector expands as `α = Σ_I α(e_I) dx^I` over strictly
increasing `I`: by `dx^I(e_J) = δ_IJ` the remainder vanishes on every `e_J`, so its coefficient
norm `|·|_E` is `0`, and `|·|_E` is the norm of a linear isomorphism onto `ℝᵈ`. -/
theorem Submission.cmr_coordinate_covectors_span : ∀ (P n : ℕ), (∀ I : Fin n → Fin P, ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) ∧ ∀ ζ : MultiVector P n, (∀ (I : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ζ θ = 0) → ζ = 0 := by
  intro P n
  refine ⟨Submission.cmr_cc_det_covector_exists P n, fun ζ hζ => ?_⟩
  classical
  -- `θ I = dx^I` for every `I`
  choose θ hθ using Submission.cmr_cc_det_covector_exists P n
  -- `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`
  have hδ : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      θ I (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 :=
    fun I J hI hJ => Submission.cmr_cc_det_covector_basis_kronecker P n I J (θ I) hI hJ (hθ I)
  -- `α = Σ_I α(e_I) dx^I` over strictly increasing `I`
  have hexp : ∀ α : Covector (Euclid P) n, α = ∑ I : Fin n → Fin P,
      if StrictMono I then α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) • θ I
      else 0 := by
    intro α
    obtain ⟨α', hα'⟩ : ∃ α', α' = α - ∑ I : Fin n → Fin P,
        if StrictMono I then α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) • θ I
        else 0 := ⟨_, rfl⟩
    -- `α'(e_J) = α(e_J) - Σ_I α(e_I) δ_IJ = 0` for strictly increasing `J`
    have hJ : ∀ J : Fin n → Fin P, StrictMono J →
        α' (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = 0 := by
      intro J hJ
      rw [hα', ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.sum_apply,
        Finset.sum_eq_single J, ite_eq_left hJ, ContinuousAlternatingMap.smul_apply,
        hδ J J hJ hJ, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
      · intro I _ hIJ
        split_ifs with hI
        · rw [ContinuousAlternatingMap.smul_apply, hδ I J hI hJ, ite_eq_right hIJ, smul_zero]
        · rfl
      · intro h
        exact absurd (Finset.mem_univ J) h
    -- so `|α'|_E = 0`, and `α' = 0` as `|·|_E` is the norm of a linear isomorphism onto `ℝᵈ`
    have hnorm : covectorEuclideanNorm α' = 0 := by
      unfold covectorEuclideanNorm
      rw [Finset.sum_eq_zero fun I _ => ?_, Real.sqrt_zero]
      split_ifs with hI
      · rw [hJ I hI, sq, mul_zero]
      · rfl
    obtain ⟨d, c, hc⟩ := Submission.cmr_covector_euclidean_equiv P n
    have hc0 : c α' = 0 := norm_eq_zero.mp ((hc α').symm.trans hnorm)
    rw [c.map_eq_zero_iff, hα'] at hc0
    exact sub_eq_zero.mp hc0
  -- `ζ` vanishes on every `dx^I`, hence on every covector
  refine ContinuousLinearMap.ext fun α => ?_
  rw [zero_apply, hexp α, map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  split_ifs with hI
  · rw [map_smul, hζ I (θ I) hI (hθ I), smul_zero]
  · exact map_zero ζ
/-- **Directional difference estimate from the divergence bound** (steps 1–2 of the parent proof).
For `‖w‖ ≤ 1` the field `g(y) = a(y + v) • w` is admissible and `div g(y) = Da(y + v)(w)` (trace
of a rank-one map), so `|∫ h·Da(q + v)(w) dν| ≤ Λ`.  The fundamental theorem of calculus along
`s ↦ q x + s • z` and Fubini on `(0, 1] × X` (majorant `M‖z‖|h|`, `‖Da‖ ≤ M`) give
`∫ h·(a(q + z) − a(q)) dν = ∫₀¹ ∫ h·Da(q + s • z)(z) dν ds`, and `Da(p)(z) = ‖z‖·Da(p)(w)` with
`w = ‖z‖⁻¹ • z` bounds the inner integral by `Λ‖z‖`. -/
theorem Submission.cmr_tdn_directional_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, |a y| ≤ 1) → ∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖ := by
  intro n X _ ν q h Λ hν hq hh hdiv a ha hsupp hbd z
  -- Step 1: `a` is differentiable, `Da` is continuous with compact support, so `‖Da‖ ≤ M`
  have h0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ a := ha.differentiable h0
  have hcont : Continuous (fderiv ℝ a) := ha.continuous_fderiv h0
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support (hsupp.fderiv ℝ)
  -- Step 3: for `‖w‖ ≤ 1` the field `g(y) = a(y + v) • w` is admissible, with
  -- `div g(y) = Da(y + v)(w)`; this gives `(∗)`
  have key : ∀ v w : Euclid n, ‖w‖ ≤ 1 → |∫ x, h x * fderiv ℝ a (q x + v) w ∂ν| ≤ Λ := by
    intro v w hw
    set g : Euclid n → Euclid n := fun y => a (y + v) • w with hg_def
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
      (ha.comp (contDiff_id.add contDiff_const)).smul contDiff_const
    have hg_supp : HasCompactSupport g :=
      (hsupp.comp_homeomorph (Homeomorph.addRight v)).smul_right (f' := fun _ => w)
    have hg_bd : ∀ y, ‖g y‖ ≤ 1 := by
      intro y
      simp only [hg_def, norm_smul, Real.norm_eq_abs]
      calc |a (y + v)| * ‖w‖ ≤ 1 * 1 := mul_le_mul (hbd _) hw (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have htrace : ∀ y, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g y).toLinearMap
        = fderiv ℝ a (y + v) w := by
      intro y
      have h1 : HasFDerivAt (fun y => a (y + v)) (fderiv ℝ a (y + v)) y :=
        (hasFDerivAt_comp_add_right v).2 (hdiff (y + v)).hasFDerivAt
      rw [(h1.smul_const w).fderiv, ContinuousLinearMap.coe_smulRight,
        LinearMap.trace_smulRight]
      rfl
    simpa only [htrace] using hdiv g hg_smooth hg_supp hg_bd
  -- Step 4: fundamental theorem of calculus along `s ↦ q x + s • z`
  have hftc : ∀ x, ∫ s in (0 : ℝ)..1, h x * fderiv ℝ a (q x + s • z) z
      = h x * (a (q x + z) - a (q x)) := by
    intro x
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => a (q x + s • z)) (fderiv ℝ a (q x + s • z) z) s := by
      intro s _
      have hline : HasDerivAt (fun s : ℝ => q x + s • z) z s := by
        simpa using ((hasDerivAt_id s).smul_const z).const_add (q x)
      exact (hdiff (q x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
    have hcontS : Continuous (fun s : ℝ => fderiv ℝ a (q x + s • z) z) :=
      (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcontS.intervalIntegrable 0 1)]
    simp
  -- Step 5: Fubini on `Leb|(0, 1] ⊗ ν`, with integrable majorant `M‖z‖|h|`
  have hGint : Integrable (uncurry fun (s : ℝ) (x : X) => h x * fderiv ℝ a (q x + s • z) z)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) := by
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
      rw [uIoc_of_le zero_le_one]; infer_instance
    have hmaj : Integrable (fun p : ℝ × X => (M * ‖z‖) * |h p.2|)
        ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) :=
      (hh.abs.comp_snd _).const_mul _
    refine hmaj.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : ℝ × X => h p.2)
          ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) := hh.aestronglyMeasurable.comp_snd
      have h2 : Continuous (fun p : ℝ × Euclid n => fderiv ℝ a (p.2 + p.1 • z) z) :=
        (hcont.comp (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
          continuous_const
      have h3 : Measurable (fun p : ℝ × X => (p.1, q p.2)) :=
        measurable_fst.prodMk (hq.comp measurable_snd)
      exact h1.mul (h2.measurable.comp h3).aestronglyMeasurable
    · filter_upwards with p
      simp only [uncurry, Real.norm_eq_abs, abs_mul]
      have hp : |fderiv ℝ a (q p.2 + p.1 • z) z| ≤ M * ‖z‖ :=
        calc |fderiv ℝ a (q p.2 + p.1 • z) z| = ‖fderiv ℝ a (q p.2 + p.1 • z) z‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ a (q p.2 + p.1 • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖z‖ := by gcongr; exact hM _
      calc |h p.2| * |fderiv ℝ a (q p.2 + p.1 • z) z| ≤ |h p.2| * (M * ‖z‖) := by gcongr
        _ = M * ‖z‖ * |h p.2| := by ring
  have heq : ∫ x, h x * (a (q x + z) - a (q x)) ∂ν
      = ∫ s in (0 : ℝ)..1, ∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν := by
    rw [intervalIntegral_integral_swap hGint]
    exact integral_congr_ae (Eventually.of_forall fun x => (hftc x).symm)
  -- Step 6: with `w = ‖z‖⁻¹ • z` (so `‖w‖ ≤ 1`, `z = ‖z‖ • w`, also for `z = 0`),
  -- `(∗)` bounds the inner integral by `Λ‖z‖` for every `s`
  set w : Euclid n := ‖z‖⁻¹ • z with hw_def
  have hw : ‖w‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hw_def, hz]
    · rw [hw_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
  have hzw : z = ‖z‖ • w := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [hw_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz), one_smul]
  have hlin : ∀ p : Euclid n, fderiv ℝ a p z = ‖z‖ * fderiv ℝ a p w := by
    intro p
    conv_lhs => rw [hzw]
    rw [map_smul, smul_eq_mul]
  have hbound : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν‖ ≤ Λ * ‖z‖ := by
    intro s _
    have hrw : ∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν
        = ‖z‖ * ∫ x, h x * fderiv ℝ a (q x + s • z) w ∂ν := by
      rw [← integral_const_mul]
      congr 1
      ext x
      rw [hlin]
      ring
    rw [hrw, Real.norm_eq_abs, abs_mul, abs_norm, mul_comm Λ]
    exact mul_le_mul_of_nonneg_left (key (s • z) w hw) (norm_nonneg _)
  rw [heq]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound
/-- **Ball-averaging estimate** (step 3 of the parent proof).  With `B = B_r(0)` and
`V = λ(B) ∈ (0, ∞)`, Fubini on `ν ⊗ λ⌞B` gives
`V ∫ h(x) a(q x) dν = ∫∫ h(x) a(q x + z) − ∫∫ h(x) (a(q x + z) − a(q x))`.  The second double
integral is at most `V Λ r` by the directional bound (`‖z‖ < r` on `B`), and the first at most
`(∫ |h| dν) ∫ a` since `0 ≤ ∫_B a(q x + z) dz ≤ ∫ a` by translation invariance.  Divide by `V`. -/
theorem Submission.cmr_tdn_ball_average_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ) (a : Euclid n → ℝ) (r : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → 0 ≤ Λ → Continuous a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → (∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖) → 0 < r → |∫ x, h x * a (q x) ∂ν| ≤ r * Λ + (volume (ball (0 : Euclid n) r)).toReal⁻¹ * (∫ x, |h x| ∂ν) * ∫ y, a y := by
  intro n X mX ν q h Λ a r hν hq hh hΛ ha ha_supp ha0 ha1 hdir hr
  -- the ball `B = B_r(0)`: measurable, inside `‖z‖ ≤ r`, of measure `λ(B) ∈ (0, ∞)`
  have hBm : MeasurableSet (ball (0 : Euclid n) r) := measurableSet_ball
  have hBr : ∀ z ∈ ball (0 : Euclid n) r, ‖z‖ ≤ r := fun z hz => (mem_ball_zero_iff.1 hz).le
  have hBpos : 0 < volume (ball (0 : Euclid n) r) := measure_ball_pos volume 0 hr
  have hBfin : volume (ball (0 : Euclid n) r) < ∞ := measure_ball_lt_top
  generalize ball (0 : Euclid n) r = B at hBm hBr hBpos hBfin ⊢
  have hV : 0 < (volume B).toReal := ENNReal.toReal_pos hBpos.ne' hBfin.ne
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin.ne
  have hμB : (volume.restrict B).real univ = (volume B).toReal := by
    rw [measureReal_def, Measure.restrict_apply_univ]
  generalize (volume B).toReal = V at hV hμB ⊢
  -- `a` is integrable, and so are its translates
  have ha_int : Integrable a volume := ha.integrable_of_hasCompactSupport ha_supp
  -- the integrands on `ν ⊗ λ⌞B`, dominated by `|h x|`
  have hm₁ : Measurable fun p : X × Euclid n => a (q p.1 + p.2) :=
    ha.measurable.comp ((hq.comp measurable_fst).add measurable_snd)
  have hm₀ : Measurable fun p : X × Euclid n => a (q p.1) :=
    ha.measurable.comp (hq.comp measurable_fst)
  have hh₁ : AEStronglyMeasurable (fun p : X × Euclid n => h p.1) (ν.prod (volume.restrict B)) :=
    hh.aestronglyMeasurable.comp_fst
  have hdom : Integrable (fun p : X × Euclid n => |h p.1|) (ν.prod (volume.restrict B)) :=
    hh.abs.comp_fst _
  have hG₂ : Integrable (fun p : X × Euclid n => h p.1 * a (q p.1 + p.2))
      (ν.prod (volume.restrict B)) := by
    refine hdom.mono' (hh₁.mul hm₁.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (ha1 _)
  have hG₁ : Integrable (fun p : X × Euclid n => h p.1 * (a (q p.1 + p.2) - a (q p.1)))
      (ν.prod (volume.restrict B)) := by
    refine hdom.mono' (hh₁.mul (hm₁.sub hm₀).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) (abs_sub_le_iff.2 ⟨?_, ?_⟩)
    · linarith [ha0 (q p.1), ha1 (q p.1 + p.2)]
    · linarith [ha0 (q p.1 + p.2), ha1 (q p.1)]
  -- `V F = ∫∫ h(x) a(q x + z) - ∫∫ h(x) (a(q x + z) - a(q x))` over `ν ⊗ λ⌞B`
  have hsplit : V * ∫ x, h x * a (q x) ∂ν =
      (∫ p, h p.1 * a (q p.1 + p.2) ∂(ν.prod (volume.restrict B))) -
        ∫ p, h p.1 * (a (q p.1 + p.2) - a (q p.1)) ∂(ν.prod (volume.restrict B)) := by
    rw [← integral_sub hG₂ hG₁]
    have hfun : (fun p : X × Euclid n =>
        h p.1 * a (q p.1 + p.2) - h p.1 * (a (q p.1 + p.2) - a (q p.1))) =
        fun p => h p.1 * a (q p.1) := by
      funext p
      ring
    rw [hfun, integral_fun_fst (fun x => h x * a (q x)), hμB, smul_eq_mul]
  -- Fubini and the directional bound: `|∫∫ h(x) (a(q x + z) - a(q x))| ≤ V Λ r`
  have hJ : |∫ p, h p.1 * (a (q p.1 + p.2) - a (q p.1)) ∂(ν.prod (volume.restrict B))| ≤
      V * (Λ * r) := by
    rw [integral_prod_symm _ hG₁]
    have hb : ∀ᵐ z ∂(volume.restrict B), ‖∫ x, h x * (a (q x + z) - a (q x)) ∂ν‖ ≤ Λ * r := by
      filter_upwards [ae_restrict_mem hBm] with z hz
      rw [Real.norm_eq_abs]
      exact (hdir z).trans (mul_le_mul_of_nonneg_left (hBr z hz) hΛ)
    have := norm_integral_le_of_norm_le (integrable_const (Λ * r)) hb
    rw [integral_const, hμB, smul_eq_mul, Real.norm_eq_abs] at this
    exact this
  -- translation invariance: `|∫∫ h(x) a(q x + z)| ≤ (∫ |h|) ∫ a`
  have hM : |∫ p, h p.1 * a (q p.1 + p.2) ∂(ν.prod (volume.restrict B))| ≤
      (∫ x, |h x| ∂ν) * ∫ y, a y := by
    rw [integral_prod _ hG₂]
    have hb : ∀ x, ‖∫ z, h x * a (q x + z) ∂(volume.restrict B)‖ ≤ |h x| * ∫ y, a y := by
      intro x
      rw [integral_const_mul, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h0 : 0 ≤ ∫ z, a (q x + z) ∂(volume.restrict B) := integral_nonneg fun z => ha0 _
      rw [abs_of_nonneg h0]
      exact (setIntegral_le_integral (ha_int.comp_add_left (q x))
        (Eventually.of_forall fun z => ha0 _)).trans_eq (integral_add_left_eq_self a (q x))
    have := norm_integral_le_of_norm_le (hh.abs.mul_const (∫ y, a y)) (Eventually.of_forall hb)
    rw [integral_mul_const, Real.norm_eq_abs] at this
    exact this
  -- conclusion: `V |F| ≤ (∫ |h|) ∫ a + V Λ r`, then divide by `V > 0`
  have key : V * |∫ x, h x * a (q x) ∂ν| ≤ (∫ x, |h x| ∂ν) * (∫ y, a y) + V * (Λ * r) := by
    rw [← abs_of_pos hV, ← abs_mul, abs_of_pos hV, hsplit]
    exact (abs_sub _ _).trans (add_le_add hM hJ)
  generalize ∫ x, h x * a (q x) ∂ν = F at key ⊢
  generalize ∫ x, |h x| ∂ν = H at key ⊢
  generalize ∫ y, a y = A at key ⊢
  have hV0 : V ≠ 0 := hV.ne'
  calc |F| ≤ (H * A + V * (Λ * r)) / V := by
        rw [le_div_iff₀ hV]
        linarith
    _ = r * Λ + V⁻¹ * H * A := by
        field_simp
        ring
/-- **Smooth cut-offs of a compact Lebesgue-null set** (steps 4 and 5(ii) of the parent proof).
With `δₖ = 1/(k+1)`, take `aₖ` smooth with values in `[0, 1]`, support `thickening δₖ K`, and
`aₖ = 1` exactly on `K` (`exists_contDiff_support_eq_eq_one_iff`).  Then `aₖ` vanishes off the
compact `cthickening δₖ K`; a point `y ∉ K = ⋂_{δ>0} cthickening δ K` misses some
`cthickening δ K`, so `aₖ(y) = 0` once `δₖ < δ`; and `0 ≤ ∫ aₖ ≤ λ(cthickening δₖ K) → λ(K) = 0`. -/
theorem Submission.cmr_tdn_null_set_cutoffs : ∀ (n : ℕ) (K : Set (Euclid n)), IsCompact K → volume K = 0 → ∃ a : ℕ → Euclid n → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k, HasCompactSupport (a k)) ∧ (∀ k y, 0 ≤ a k y) ∧ (∀ k y, a k y ≤ 1) ∧ (∀ k, ∀ y ∈ K, a k y = 1) ∧ (∀ y, y ∉ K → ∀ᶠ k in atTop, a k y = 0) ∧ Tendsto (fun k => ∫ y, a k y) atTop (𝓝 0) := by
  intro n K hK hK0
  -- `aₖ`: smooth, `[0, 1]`-valued, with support `thickening δₖ K` and `aₖ = 1` exactly on `K`
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hex : ∀ k : ℕ, ∃ f : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
      support f = thickening (1 / ((k : ℝ) + 1)) K ∧ ∀ x, x ∈ K ↔ f x = 1 := fun k =>
    exists_contDiff_support_eq_eq_one_iff isOpen_thickening hK.isClosed
      (self_subset_thickening (hδ k) K)
  choose a ha_smooth ha_range ha_supp ha_one using hex
  have hnonneg : ∀ k y, 0 ≤ a k y := fun k y => (ha_range k (mem_range_self y)).1
  have hle : ∀ k y, a k y ≤ 1 := fun k y => (ha_range k (mem_range_self y)).2
  -- `aₖ` vanishes off the compact `cthickening δₖ K`
  have hzero : ∀ (k : ℕ) y, y ∉ cthickening (1 / ((k : ℝ) + 1)) K → a k y = 0 := by
    intro k y hy
    by_contra h
    have hy' : y ∈ support (a k) := h
    rw [ha_supp k] at hy'
    exact hy (thickening_subset_cthickening _ _ hy')
  refine ⟨a, ha_smooth, fun k => HasCompactSupport.intro hK.cthickening (hzero k), hnonneg, hle,
    fun k y hy => (ha_one k y).1 hy, ?_, ?_⟩
  · -- `y ∉ K = ⋂_{δ>0} cthickening δ K`, so `y ∉ cthickening δ K ⊇ cthickening δₖ K` for some
    -- `δ > 0` and all `k` with `δₖ < δ`
    intro y hy
    rw [← hK.isClosed.closure_eq, closure_eq_iInter_cthickening] at hy
    simp only [mem_iInter, not_forall] at hy
    obtain ⟨δ, hδpos, hyδ⟩ := hy
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hδpos
    filter_upwards [eventually_ge_atTop k₀] with k hk
    refine hzero k y fun hmem => hyδ (cthickening_mono ?_ K hmem)
    have hkk₀ : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    linarith
  · -- `0 ≤ ∫ aₖ ≤ λ(cthickening δₖ K)`, and `λ(cthickening δₖ K) → λ(K) = 0`
    have hmeas : Tendsto (fun k : ℕ => (volume (cthickening (1 / ((k : ℝ) + 1)) K)).toReal)
        atTop (𝓝 0) := by
      have h := (tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure (Euclid n)))
        hK).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rw [hK0] at h
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas
      (fun k => integral_nonneg (hnonneg k)) fun k => ?_
    set C := cthickening (1 / ((k : ℝ) + 1)) K
    have hCm : MeasurableSet C := isClosed_cthickening.measurableSet
    have hint : Integrable (C.indicator fun _ => (1 : ℝ)) volume :=
      (integrable_indicator_iff hCm).2 (integrableOn_const hK.cthickening.measure_lt_top.ne)
    have hind : ∀ y, a k y ≤ C.indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ C
      · rw [indicator_of_mem hy]
        exact hle k y
      · rw [indicator_of_notMem hy, hzero k y hy]
    calc ∫ y, a k y ≤ ∫ y, C.indicator (fun _ => (1 : ℝ)) y :=
          integral_mono_of_nonneg (Eventually.of_forall (hnonneg k)) hint
            (Eventually.of_forall hind)
      _ = (volume C).toReal := by
          rw [integral_indicator_const _ hCm]
          simp [measureReal_def]

/-- **Vanishing on compact null sets from an `ε + C ∫ a` bound** (steps 5(i) and 6 of the
top-dimensional null-set argument): let `q : X → ℝⁿ` be measurable and `h ∈ L¹(ν)` (`ν` need not
be finite), and suppose that for every `ε > 0` there is `C` with `|∫ h · a(q) dν| ≤ ε + C ∫ a`
for all smooth compactly supported `0 ≤ a ≤ 1`.  Then `∫_{q⁻¹K} h dν = 0` for every compact
Lebesgue-null `K ⊆ ℝⁿ`.  Along the cut-offs `a_k` of `K` given by
`Submission.cmr_tdn_null_set_cutoffs`, dominated convergence (majorant `|h|`) gives
`∫ h · a_k(q) dν → ∫_{q⁻¹K} h dν`, while `ε + C ∫ a_k → ε`; so `|∫_{q⁻¹K} h dν| ≤ ε` for every
`ε > 0`. -/
theorem Submission.cmr_tdn_null_of_average_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ), Measurable q → Integrable h ν → (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → |∫ x, h x * a (q x) ∂ν| ≤ ε + C * ∫ y, a y) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0 := by
  intro n X _ ν q h hq hh hbd K hK hK0
  -- smooth cut-offs `a k` of `K`: `a k = 1` on `K`, `a k → 0` pointwise off `K`, `∫ a k → 0`
  obtain ⟨a, ha, hac, ha0, ha1, haK, haoff, haint⟩ :=
    Submission.cmr_tdn_null_set_cutoffs n K hK hK0
  -- dominated convergence with majorant `|h|`: `∫ h (a k ∘ q) dν → ∫ 1_{q⁻¹K} h dν`
  have hE : MeasurableSet (q ⁻¹' K) := hq hK.isClosed.measurableSet
  have hlim : Tendsto (fun k => ∫ x, h x * a k (q x) ∂ν) atTop
      (𝓝 (∫ x in q ⁻¹' K, h x ∂ν)) := by
    rw [← integral_indicator hE]
    refine tendsto_integral_of_dominated_convergence (fun x => |h x|)
      (fun k => hh.aestronglyMeasurable.mul
        ((ha k).continuous.measurable.comp hq).aestronglyMeasurable)
      hh.abs (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k (q x))]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha1 k (q x))
    · by_cases hx : q x ∈ K
      · have h1 : ∀ k, a k (q x) = 1 := fun k => haK k (q x) hx
        simp only [indicator_of_mem (show x ∈ q ⁻¹' K from hx), h1, mul_one]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem (show x ∉ q ⁻¹' K from hx)]
        refine tendsto_nhds_of_eventually_eq ?_
        filter_upwards [haoff (q x) hx] with k hk
        rw [hk, mul_zero]
  -- for `ε > 0`: `|∫ h (a k ∘ q) dν| ≤ ε + C ∫ a k → ε`, so `|∫_{q⁻¹K} h dν| ≤ ε`
  refine abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨C, hC⟩ := hbd ε hε
  have hR : Tendsto (fun k => ε + C * ∫ y, a k y) atTop (𝓝 (ε + C * 0)) :=
    tendsto_const_nhds.add (haint.const_mul C)
  rw [mul_zero, add_zero] at hR
  rw [zero_add]
  exact le_of_tendsto_of_tendsto' hlim.abs hR fun k => hC (a k) (ha k) (hac k) (ha0 k) (ha1 k)

/-- **Lemma TD for `m = q_#(h ν)`** (top-dimensional step of the absolute continuity of normal
currents, Simon Ch. 6, 2.36): if `|∫ h · div g(q) dν| ≤ Λ` for all smooth compactly supported
fields `g` with `‖g‖ ≤ 1`, then `∫_{q⁻¹K} h dν = 0` for every compact Lebesgue-null `K ⊆ ℝⁿ`.
Testing with `g = 0` gives `Λ ≥ 0`, and `Submission.cmr_tdn_directional_bound` gives
`|∫ h (a(q + z) − a(q)) dν| ≤ Λ‖z‖` for smooth compactly supported `|a| ≤ 1`.  For `ε > 0`,
averaging over `B_r` with `rΛ ≤ ε` (`Submission.cmr_tdn_ball_average_bound`) gives
`|∫ h a(q) dν| ≤ ε + |B_r|⁻¹ ‖h‖₁ ∫ a` for smooth compactly supported `0 ≤ a ≤ 1`, and
`Submission.cmr_tdn_null_of_average_bound` turns these bounds into the claim. -/
theorem Submission.cmr_null_of_div_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0 := by
  intro n X _ ν q h Λ hν hq hh hdiv
  -- `Λ ≥ 0`: the field `g = 0` has divergence `0`
  have hΛ : 0 ≤ Λ := by
    simpa using hdiv (fun _ => 0) contDiff_const HasCompactSupport.zero fun _ => by simp
  -- the translation estimate `|∫ h (a(q + z) − a(q)) dν| ≤ Λ‖z‖`
  have hdir := Submission.cmr_tdn_directional_bound n X ν q h Λ hν hq hh hdiv
  refine Submission.cmr_tdn_null_of_average_bound n X ν q h hq hh fun ε hε => ?_
  -- average over `B_r` with `r = ε / (Λ + 1)`, so that `rΛ ≤ ε`
  obtain ⟨r, hr, hrΛ⟩ : ∃ r : ℝ, 0 < r ∧ r * Λ ≤ ε := by
    refine ⟨ε / (Λ + 1), div_pos hε (by linarith), ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨(volume (ball (0 : Euclid n) r)).toReal⁻¹ * ∫ x, |h x| ∂ν, fun a ha hac ha0 ha1 => ?_⟩
  have hB := Submission.cmr_tdn_ball_average_bound n X ν q h Λ a r hν hq hh hΛ ha.continuous hac
    ha0 ha1 (hdir a ha hac fun y => abs_le.2 ⟨by linarith [ha0 y], ha1 y⟩) hr
  linarith
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

/-- **Divergence form of `b · (div g) ∘ p_I` against `θ = dx^I`** (the projection step
`p_I^#((div g) dy) = d(p_I^#γ)` of the mass representation used for Simon 7.2.4).  Let
`p_I x = (x_{I k})_k`, `ι y = ∑ₖ y_k e_{I k}` and `G = ι ∘ g ∘ p_I`, so that
`(DG(x) v)_{I k} = (Dg(p_I x)(p_I v))_k`.  Put `η = b • θ.curryLeft ∘ G` and
`ζ = dη − (b · tr Dg ∘ p_I) • θ`.  The formula for `dη` (`cmr_df_extDeriv_smul_curryLeft`) and
Jacobi's trace identity in coordinates (`cmr_df_cons_sum_trace`) give
`ζ(x)(w) = ∑ᵢ (−1)ⁱ Db(x)(wᵢ) θ(G x, w without wᵢ)`.  Hence `‖η‖ ≤ sup|b| ‖θ‖ ‖ι‖` and
`‖ζ‖ ≤ (m + 1) sup‖Db‖ ‖θ‖ ‖ι‖`, both forms vanish off `tsupport b`, and part (iii) of
`rsd_mw_tfa_norm_props` turns these operator-norm bounds into a coefficient-norm bound `K`
that does not depend on `g`. -/
theorem Submission.cmr_coordinate_divergence_form : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ), StrictMono I → (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → ∃ K : ℝ, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → (∀ y, ‖g y‖ ≤ 1) → ∃ (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)), IsTestForm η ∧ IsTestForm ζ ∧ tsupport η ⊆ tsupport b ∧ tsupport ζ ⊆ tsupport b ∧ (∀ x, covectorEuclideanNorm (η x) ≤ K) ∧ (∀ x, covectorEuclideanNorm (ζ x) ≤ K) ∧ ∀ x, exteriorDerivative η x = (b x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ + ζ x := by
  intro P m I θ b hI hθ hb hbc
  -- the coordinate projection `p = p_I` and the coordinate embedding `ι`, `(ι y)_{I k} = y_k`
  let p : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun k => x (I k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : Euclid (m + 1) →L[ℝ] Euclid P := LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun j => ∑ k, if I k = j then y k else 0)
      map_add' := fun y z => by
        ext j
        simp only [PiLp.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      map_smul' := fun c y => by
        ext j
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp }
  have hι : ∀ y k, ι y (I k) = y k := by
    intro y k
    change (∑ k', if I k' = I k then y k' else 0) = y k
    simp [hI.injective.eq_iff]
  -- the constant `K`: (F1) from `rsd_mw_tfa_norm_props` (iii), `β₀ = sup |b|`, `β₁ = sup ‖Db‖`
  obtain ⟨Cm, hCm0, hCm⟩ := (Submission.rsd_mw_tfa_norm_props P m).2.2.1
  obtain ⟨Cn, hCn0, hCn⟩ := (Submission.rsd_mw_tfa_norm_props P (m + 1)).2.2.1
  obtain ⟨β₀, hβ₀⟩ := hb.continuous.bounded_above_of_compact_support hbc
  obtain ⟨β₁, hβ₁⟩ :=
    (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support (hbc.fderiv ℝ)
  have hβ₀0 : 0 ≤ β₀ := (norm_nonneg _).trans (hβ₀ 0)
  have hβ₁0 : 0 ≤ β₁ := (norm_nonneg _).trans (hβ₁ 0)
  refine ⟨Cm * (β₀ * (‖θ‖ * ‖ι‖)) + Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))), ?_⟩
  intro g hg hg1
  -- the vector field `G = ι ∘ g ∘ p`: smooth, `‖G‖ ≤ ‖ι‖`, `DG(x) = ι ∘ Dg(p x) ∘ p`
  obtain ⟨G, hG⟩ : ∃ G : Euclid P → Euclid P, G = fun x => ι (g (p x)) := ⟨_, rfl⟩
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := hG ▸ ι.contDiff.comp (hg.comp p.contDiff)
  have hGb : ∀ x, ‖G x‖ ≤ ‖ι‖ := by
    intro x
    rw [hG]
    calc ‖ι (g (p x))‖ ≤ ‖ι‖ * ‖g (p x)‖ := ι.le_opNorm _
      _ ≤ ‖ι‖ * 1 := mul_le_mul_of_nonneg_left (hg1 _) (norm_nonneg _)
      _ = ‖ι‖ := mul_one _
  have hDG : ∀ x v, fderiv ℝ G x v = ι (fderiv ℝ g (p x) (p v)) := by
    intro x v
    have hgd : DifferentiableAt ℝ g (p x) := hg.differentiable (by simp) _
    have h : HasFDerivAt G (ι.comp ((fderiv ℝ g (p x)).comp p)) x := by
      rw [hG]
      exact ι.hasFDerivAt.comp x (hgd.hasFDerivAt.comp x p.hasFDerivAt)
    rw [h.fderiv]
    rfl
  -- `(DG(x) v)_{I k} = (Dg(p x)(p v))_k`, the hypothesis of `cmr_df_cons_sum_trace`
  have hL : ∀ x (v : Euclid P) (k : Fin (m + 1)), fderiv ℝ G x v (I k) =
      (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap
        (WithLp.toLp 2 (fun k' => v (I k'))) k := by
    intro x v k
    rw [hDG, hι]
    rfl
  -- the forms `η = b • θ.curryLeft ∘ G` and `ζ = dη − (b · tr Dg ∘ p) • θ`
  obtain ⟨η, hη⟩ : ∃ η : DifferentialForm (Euclid P) m,
      η = fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : DifferentialForm (Euclid P) (m + 1),
      ζ = fun x => exteriorDerivative η x - (b x * LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ := ⟨_, rfl⟩
  -- Step 1: `η` is a test form with `tsupport η ⊆ tsupport b`
  have hηs : tsupport η ⊆ tsupport b := by
    rw [hη]
    exact tsupport_smul_subset_left b _
  have hηT : IsTestForm η := by
    refine ⟨?_, hbc.mono' ((subset_tsupport η).trans hηs)⟩
    rw [hη]
    exact hb.smul ((ContinuousAlternatingMap.curryLeft θ).contDiff.comp hGs)
  -- Steps 2-4: `dη(x)(w) = Z_x(w) + b(x) S_x(w)` and `S_x(w) = tr Dg(p x) · θ(w)`,
  -- so `ζ(x)(w) = Z_x(w) = ∑ᵢ (−1)ⁱ Db(x)(wᵢ) θ(G x, w without wᵢ)`
  have hζZ : ∀ x (w : Fin (m + 1) → Euclid P), ζ x w = ∑ i : Fin (m + 1),
      (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w))) := by
    intro x w
    have hbx : DifferentiableAt ℝ b x := hb.differentiable (by simp) x
    have hGx : DifferentiableAt ℝ G x := hGs.differentiable (by simp) x
    have h1 := Submission.cmr_df_extDeriv_smul_curryLeft P m θ b G x hbx hGx w
    have h2 := Submission.cmr_df_cons_sum_trace P m I θ
      (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap (fderiv ℝ G x) hθ (hL x) w
    have h3 : ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i))
          (i.removeNth w))) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w))) + b x * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
          θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hζ]
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [hη, h1, h3, h2]
    ring
  -- Step 4: `ζ` is a test form with `tsupport ζ ⊆ tsupport b`
  have hζsupp : support ζ ⊆ tsupport b := by
    intro x hx
    by_contra hxb
    have hbx : b x = 0 := image_eq_zero_of_notMem_tsupport hxb
    have hdη : exteriorDerivative η x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hxb (hηs (tsupport_exteriorDerivative_subset η h))
    exact hx (by rw [hζ]; simp [hbx, hdη])
  have hζs : tsupport ζ ⊆ tsupport b := closure_minimal hζsupp (isClosed_tsupport b)
  have hζT : IsTestForm ζ := by
    refine ⟨?_, hbc.mono' hζsupp⟩
    let tr : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid (m + 1)) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have htr : ContDiff ℝ (⊤ : ℕ∞) fun x : Euclid P => LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap :=
      tr.contDiff.comp ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp p.contDiff)
    rw [hζ]
    exact (exteriorDerivative_isTestForm hηT).1.sub ((hb.mul htr).smul contDiff_const)
  -- Step 5: operator-norm bounds, independent of `g`
  have hη_op : ∀ x, ‖η x‖ ≤ β₀ * (‖θ‖ * ‖ι‖) := by
    intro x
    rw [hη, norm_smul]
    refine mul_le_mul (hβ₀ x) ?_ (norm_nonneg _) hβ₀0
    calc ‖ContinuousAlternatingMap.curryLeft θ (G x)‖
        ≤ ‖ContinuousAlternatingMap.curryLeft θ‖ * ‖G x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖θ‖ * ‖ι‖ := by
        rw [ContinuousAlternatingMap.norm_curryLeft]
        exact mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _)
  have hζ_op : ∀ x, ‖ζ x‖ ≤ ((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖)) := by
    intro x
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [hζZ x w]
    have hterm : ∀ i : Fin (m + 1), ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w)))‖ ≤ β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ := by
      intro i
      have h1 : ‖fderiv ℝ b x (w i)‖ ≤ β₁ * ‖w i‖ :=
        ((fderiv ℝ b x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hβ₁ x) (norm_nonneg _))
      have h2 : ‖θ (Fin.cons (G x) (i.removeNth w))‖ ≤
          ‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖ := by
        calc ‖θ (Fin.cons (G x) (i.removeNth w))‖
            ≤ ‖θ‖ * ∏ j : Fin (m + 1),
                ‖(Fin.cons (G x) (i.removeNth w) : Fin (m + 1) → Euclid P) j‖ :=
              θ.le_opNorm _
          _ = ‖θ‖ * (‖G x‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by
              rw [Fin.prod_univ_succ]
              simp [Fin.removeNth_apply]
          _ ≤ ‖θ‖ * (‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by
              gcongr
              exact hGb x
          _ = ‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖ := by ring
      calc ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)))‖
          = ‖fderiv ℝ b x (w i)‖ * ‖θ (Fin.cons (G x) (i.removeNth w))‖ := by
            simp [norm_mul]
        _ ≤ (β₁ * ‖w i‖) * (‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = β₁ * (‖θ‖ * ‖ι‖) * (‖w i‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by ring
        _ = β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ := by
            rw [Fin.prod_univ_succAbove (fun j => ‖w j‖) i]
    calc ‖∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
          θ (Fin.cons (G x) (i.removeNth w)))‖
        ≤ ∑ i : Fin (m + 1), ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
          θ (Fin.cons (G x) (i.removeNth w)))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (m + 1), β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖)) * ∏ j, ‖w j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  -- Steps 5-6: coefficient-norm bounds by (F1), and the identity, by definition of `ζ`
  have hK1 : 0 ≤ Cm * (β₀ * (‖θ‖ * ‖ι‖)) := by positivity
  have hK2 : 0 ≤ Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))) := by positivity
  refine ⟨η, ζ, hηT, hζT, hηs, hζs, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · calc covectorEuclideanNorm (η x) ≤ Cm * ‖η x‖ := hCm _
      _ ≤ Cm * (β₀ * (‖θ‖ * ‖ι‖)) := mul_le_mul_of_nonneg_left (hη_op x) hCm0
      _ ≤ _ := le_add_of_nonneg_right hK2
  · calc covectorEuclideanNorm (ζ x) ≤ Cn * ‖ζ x‖ := hCn _
      _ ≤ Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))) := mul_le_mul_of_nonneg_left (hζ_op x) hCn0
      _ ≤ _ := le_add_of_nonneg_left hK1
  · rw [hζ]
    exact (add_sub_cancel _ _).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
