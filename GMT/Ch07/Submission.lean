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

/-- **Smooth affine homotopy on `ℝ × ℝᴺ` and its differential** (Simon 6.2.26, and the
differential used in the proof of 6.2.27).  For smooth `F, G : ℝᴺ → ℝ^{N'}` let
`tail y = (y₁, …, y_N)` and `π₀ y = y₀` on `ℝ^{N+1}`, both continuous linear, and
`H(y) = F(tail y) + π₀(y) (G(tail y) − F(tail y))`.  Then `H` is smooth and
`H(ι(t, x)) = F(x) + t (G(x) − F(x))` for `ι(t, x) = (t, x)`.  By the chain and product rules
`DH(y)h = DF(tail y)(tail h) + π₀(y) (DG(tail y) − DF(tail y))(tail h) + π₀(h) (G − F)(tail y)`;
with `tail e₀ = 0`, `π₀ e₀ = 1`, `tail (0, v) = v` and `π₀ (0, v) = 0` this gives
`DH(ι(t, x))e₀ = G(x) − F(x)` and `DH(ι(t, x))(0, v) = DF(x)v + t (DG(x)v − DF(x)v)`. -/
theorem Submission.cmcdt_lpo_she_affine_homotopy : ∀ (N N' : ℕ) (F G : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ∃ H : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) H ∧ (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = G x - F x) ∧ ∀ (t : ℝ) (x v : Euclid N), fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v + t • (fderiv ℝ G x v - fderiv ℝ F x v) := by
  intro N N' F G hF hG
  -- Step 1: the continuous linear coordinate maps `tail y = (y₁, …, y_N)` and `π₀ y = y₀`
  let tail : Euclid (N + 1) →L[ℝ] Euclid N := LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
      map_add' := fun y z => by ext i; simp [Fin.tail]
      map_smul' := fun c y => by ext i; simp [Fin.tail] }
  let π₀ : Euclid (N + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  -- Step 2: their values at `ι(t, x)` and at `e₀`
  have htail : ∀ (t : ℝ) (x : Euclid N), tail (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x :=
    fun t x => rfl
  have hπ : ∀ (t : ℝ) (x : Euclid N), π₀ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = t :=
    fun t x => rfl
  have htail₀ : tail (EuclideanSpace.single 0 1) = 0 := by
    ext i; simp [tail, Fin.tail, EuclideanSpace.single, Fin.succ_ne_zero]
  have hπ₀ : π₀ (EuclideanSpace.single 0 1) = 1 := by simp [π₀]
  -- Steps 3–4: `H y = F (tail y) + π₀ y • (G (tail y) - F (tail y))` is smooth
  have hFt : ContDiff ℝ (⊤ : ℕ∞) (fun y => F (tail y)) := hF.comp tail.contDiff
  have hGt : ContDiff ℝ (⊤ : ℕ∞) (fun y => G (tail y)) := hG.comp tail.contDiff
  -- Step 6: the chain and product rules give `DH(y)`
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hder : ∀ y, HasFDerivAt (fun y => F (tail y) + π₀ y • (G (tail y) - F (tail y)))
      ((fderiv ℝ F (tail y)).comp tail + (π₀ y • ((fderiv ℝ G (tail y)).comp tail -
        (fderiv ℝ F (tail y)).comp tail) + π₀.smulRight (G (tail y) - F (tail y)))) y := by
    intro y
    have h₁ : HasFDerivAt (fun y => F (tail y)) ((fderiv ℝ F (tail y)).comp tail) y :=
      (hFd (tail y)).hasFDerivAt.comp y tail.hasFDerivAt
    have h₂ : HasFDerivAt (fun y => G (tail y)) ((fderiv ℝ G (tail y)).comp tail) y :=
      (hGd (tail y)).hasFDerivAt.comp y tail.hasFDerivAt
    exact h₁.add (π₀.hasFDerivAt.fun_smul (h₂.sub h₁))
  refine ⟨fun y => F (tail y) + π₀ y • (G (tail y) - F (tail y)),
    hFt.add (π₀.contDiff.smul (hGt.sub hFt)), fun t x => ?_, fun t x => ?_, fun t x v => ?_⟩
  -- Step 5: formula (i)
  · simp only [htail, hπ]
  -- Step 7: formula (ii), from `tail e₀ = 0` and `π₀ e₀ = 1`
  · rw [(hder _).fderiv]
    simp [htail, hπ, htail₀, hπ₀]
  -- Step 8: formula (iii), from `tail (0, v) = v` and `π₀ (0, v) = 0`
  · rw [(hder _).fderiv]
    simp [htail, hπ]
/-- **Coefficient bounds for the cylinder `[[(0,1)]] × T`** (Simon 6.2.17, 6.2.25): with
`J v = ι(0, v)` the inclusion `ℝᴺ → ℝᴺ⁺¹`, `x ↦ (0, x)`, and `e₀ = EuclideanSpace.single 0 1`, the
`dt`-part `Φ γ (v₁, …, v_k) = γ(e₀, J v₁, …, J v_k)` and the spatial part
`Ψ γ (v₁, …, v_k) = γ(J v₁, …, J v_k)` of a covector `γ` on `ℝᴺ⁺¹` are continuous linear in `γ` and
do not increase the Euclidean coefficient norm.  Indeed `Φ γ = (ι_{e₀} γ) ∘ J` and `Ψ γ = γ ∘ J`, so
the pullback bound (L1) `|β ∘ A|_E ≤ ‖A‖ᵏ |β|_E` and the interior product bound (L2)
`|ι_v β|_E ≤ ‖v‖ |β|_E` apply, with `‖J‖ ≤ 1` (`J` preserves norms) and `‖e₀‖ = 1`. -/
theorem Submission.cmcdt_lpo_cyl_restriction_bounds : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ N k : ℕ, ∃ Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N), Φ γ v = γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∀ γ : Covector (Euclid (N + 1)) (k + 1), covectorEuclideanNorm (Φ γ) ≤ covectorEuclideanNorm γ) ∧ (∀ N k : ℕ, ∃ Ψ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) k) (v : Fin k → Euclid N), Ψ γ v = γ (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ γ : Covector (Euclid (N + 1)) k, covectorEuclideanNorm (Ψ γ) ≤ covectorEuclideanNorm γ) := by
  intro hL1 hL2
  -- `J v = ι(0, v)`: a continuous linear map `ℝᴺ → ℝᴺ⁺¹` with `‖J v‖ = ‖v‖`, so `‖J‖ ≤ 1`
  have hJ : ∀ N : ℕ, ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧ ‖J‖ ≤ 1 := by
    intro N
    let L : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun u v => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun a v => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    have hLv : ∀ v, LinearMap.toContinuousLinearMap L v =
        WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) := fun v => rfl
    refine ⟨LinearMap.toContinuousLinearMap L, hLv,
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_⟩
    rw [hLv, one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    simp
  refine ⟨fun N k => ?_, fun N k => ?_⟩
  · -- `Φ γ = (ι_{e₀} γ) ∘ J`, i.e. `Φ = J^* ∘ (evaluation at e₀) ∘ curryLeft`
    obtain ⟨J, hJv, hJ1⟩ := hJ N
    refine ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k)
          (EuclideanSpace.single 0 1)).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap), fun γ v => ?_, fun γ => ?_⟩
    · simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        ContinuousAlternatingMap.curryLeftLI_apply, ContinuousLinearMap.apply_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 1
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      simp [hJv]
    · -- (L1) with `A = J`, then (L2) with `v = e₀`, `‖e₀‖ = 1`
      have he : ‖(EuclideanSpace.single 0 1 : Euclid (N + 1))‖ = 1 := by simp
      calc _ = covectorEuclideanNorm
              ((γ.curryLeft (EuclideanSpace.single 0 1)).compContinuousLinearMap J) := rfl
        _ ≤ ‖J‖ ^ k * covectorEuclideanNorm (γ.curryLeft (EuclideanSpace.single 0 1)) :=
          hL1 N (N + 1) k J _
        _ ≤ covectorEuclideanNorm (γ.curryLeft (EuclideanSpace.single 0 1)) :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (pow_le_one₀ (norm_nonneg J) hJ1)
        _ ≤ ‖(EuclideanSpace.single 0 1 : Euclid (N + 1))‖ * covectorEuclideanNorm γ :=
          hL2 (N + 1) k _ γ
        _ = covectorEuclideanNorm γ := by rw [he, one_mul]
  · -- `Ψ γ = γ ∘ J`, the pullback by `J`
    obtain ⟨J, hJv, hJ1⟩ := hJ N
    refine ⟨ContinuousAlternatingMap.compContinuousLinearMapCLM J, fun γ v => ?_, fun γ => ?_⟩
    · simp only [ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      funext i
      exact hJv (v i)
    · calc _ = covectorEuclideanNorm (γ.compContinuousLinearMap J) := rfl
        _ ≤ ‖J‖ ^ k * covectorEuclideanNorm γ := hL1 N (N + 1) k J γ
        _ ≤ covectorEuclideanNorm γ :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg γ) (pow_le_one₀ (norm_nonneg J) hJ1)
/-- **The slice operator `S ω = ∫₀¹ ω(ι(t, ·))(e₀, J ·) dt`** (the operator behind the cylinder
`[[(0, 1)]] × X` of Simon Ch. 6, 2.18–2.21 and the homotopy formula 2.25, as used for the
Lipschitz push-forward in the deformation theorem).  Choose for every `ω` the slice `η ω` given by
(SA).  Since `t ↦ ω(ι(t, x))` is continuous, every evaluated integrand is interval integrable, and
a test form with the slice formula of `ω` equals `η ω` (`ContinuousAlternatingMap.ext`,
`Subtype.ext`); linearity of the interval integral then makes `S = η` additive and homogeneous.
(i) and (ii) are the chosen properties of `η ω`, and (iii) is (SE) for the continuous
`f t = Φ (ω (ι(t, x)))`, `Φ` from (R1), whose bound `|Φ γ| ≤ |γ|` gives `|f t| ≤ c`. -/
theorem Submission.cmcdt_lpo_cyl_slice_operator : (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) → (∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c) → (∀ N k : ℕ, ∃ Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N), Φ γ v = γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∀ γ : Covector (Euclid (N + 1)) (k + 1), covectorEuclideanNorm (Φ γ) ≤ covectorEuclideanNorm γ) → ∀ N k : ℕ, ∃ S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] TestFormOn (univ : Set (Euclid N)) k, (∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N) (v : Fin k → Euclid N), (S ω : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), tsupport (S ω : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S ω : DifferentialForm (Euclid N) k) x) ≤ c := by
  intro hSA hSE hR1 N k
  -- Step 2: choose a slice `η ω` for every `ω`, with the formula (i) and the support bound (ii)
  choose η hηf hηs using hSA N k
  -- Step 1: `t ↦ ω(ι(t, x))` is continuous, so every evaluated integrand is interval integrable
  have hcont : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N),
      Continuous fun t : ℝ => (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) := by
    intro ω x
    have hι : Continuous fun t : ℝ =>
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) := by
      fun_prop
    exact ω.property.1.1.continuous.comp hι
  have hint : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N)
      (w : Fin (k + 1) → Euclid (N + 1)),
      IntervalIntegrable (fun t : ℝ => (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) w) volume 0 1 :=
    fun ω x w => ((continuous_eval_const w).comp (hcont ω x)).intervalIntegrable 0 1
  -- Step 3: a test form satisfying the slice formula of `ω` is `η ω`
  have huniq : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
      (θ : TestFormOn (univ : Set (Euclid N)) k),
      (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v =
        ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
          (Fin.cons (EuclideanSpace.single 0 1)
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → θ = η ω := by
    intro ω θ hθ
    refine Subtype.ext (funext fun x => ContinuousAlternatingMap.ext fun v => ?_)
    rw [hθ, hηf]
  -- Step 4: `S ω := η ω` is additive and homogeneous
  have hadd : ∀ ω₁ ω₂ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1),
      η (ω₁ + ω₂) = η ω₁ + η ω₂ := by
    intro ω₁ ω₂
    refine (huniq (ω₁ + ω₂) (η ω₁ + η ω₂) fun x v => ?_).symm
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
    rw [hηf, hηf, ← intervalIntegral.integral_add (hint _ _ _) (hint _ _ _)]
  have hsmul : ∀ (a : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)),
      η (a • ω) = a • η ω := by
    intro a ω
    refine (huniq (a • ω) (a • η ω) fun x v => ?_).symm
    simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [hηf, ← intervalIntegral.integral_const_mul]
  refine ⟨{ toFun := η, map_add' := hadd, map_smul' := hsmul }, fun ω x v => hηf ω x v,
    fun ω => hηs ω, fun ω c hc x => ?_⟩
  -- Step 6: (iii) from (SE) applied to `f t = Φ (ω (ι(t, x)))`
  obtain ⟨Φ, hΦ, hΦb⟩ := hR1 N k
  refine hSE N k _ (fun t => Φ ((ω : DifferentialForm (Euclid (N + 1)) (k + 1))
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) c (Φ.continuous.comp (hcont ω x))
      (fun v => ?_) fun t _ => (hΦb _).trans (hc _)
  change (η ω : DifferentialForm (Euclid N) k) x v = _
  rw [hηf]
  simp only [hΦ]
/-- **Simon 6.2.17, 2.20** (the cylinder `[[(0, 1)]] × X` as `X ∘ S`): given the mass bound (MSB)
`|X(ψ)| ≤ c M(X)` for `|ψ| ≤ c` on `spt X` and the bounded-current constructor (BC), a linear
`S : 𝒟^{k+1}(ℝ^{N+1}) → 𝒟^k(ℝ^N)` with `|S ω| ≤ c` whenever `|ω| ≤ c` induces
`cyl : 𝒟_k(ℝ^N) → 𝒟_{k+1}(ℝ^{N+1})` with `cyl X = X ∘ S` and `M(cyl X) ≤ M(X)` if `M(X) < ∞`,
and `cyl (X − Y) = cyl X − cyl Y` if `M(X), M(Y) < ∞`.  (MSB) bounds `X ∘ S` by `M(X)` and (BC)
realizes it as a current; `M(X − Y) < ∞` by (MSB) with `c = 1`. -/
theorem Submission.cmcdt_lpo_cyl_current : (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) → (∀ (N k : ℕ) (T₀ : TestFormOn (univ : Set (Euclid N)) k →ₗ[ℝ] ℝ) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T₀ ω| ≤ C * c) → ∃ T : GeometricCurrentOn (univ : Set (Euclid N)) k, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal C) → ∀ (N k : ℕ) (S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] TestFormOn (univ : Set (Euclid N)) k), (∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S ω : DifferentialForm (Euclid N) k) x) ≤ c) → ∃ cyl : GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1), (∀ X : GeometricCurrentOn (univ : Set (Euclid N)) k, X.mass < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), cyl X ω = X (S ω)) ∧ (cyl X).mass ≤ X.mass) ∧ ∀ X Y : GeometricCurrentOn (univ : Set (Euclid N)) k, X.mass < ∞ → Y.mass < ∞ → cyl (X - Y) = cyl X - cyl Y := by
  intro hMSB hBC N k S hS
  -- `X ∘ S` is a current of mass `≤ M(X)` when `M(X) < ∞`
  have hT : ∀ X : GeometricCurrentOn (univ : Set (Euclid N)) k, X.mass < ∞ →
      ∃ T : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1),
        (∀ ω, T ω = X (S ω)) ∧ T.mass ≤ X.mass := by
    intro X hX
    obtain ⟨T, hTω, hTM⟩ := hBC (N + 1) (k + 1) (X.toCurrent ∘ₗ S) X.mass.toReal
      fun ω c hω => (hMSB N k X (S ω) c hX fun x _ => hS ω c hω x).trans_eq (mul_comm _ _)
    exact ⟨T, hTω, by rwa [ENNReal.ofReal_toReal hX.ne] at hTM⟩
  choose! cyl hcylω hcylM using hT
  refine ⟨cyl, fun X hX => ⟨hcylω X hX, hcylM X hX⟩, fun X Y hX hY => ?_⟩
  -- `M(X − Y) ≤ M(X) + M(Y) < ∞`, by (MSB) with `c = 1` on each admissible form
  have hXY : (X - Y).mass < ∞ := by
    refine lt_of_le_of_lt (sSup_le ?_) (ENNReal.ofReal_lt_top (r := X.mass.toReal + Y.mass.toReal))
    rintro _ ⟨ω, hω, rfl⟩
    have h1 := hMSB N k X ω 1 hX fun x _ => hω.2 x
    have h2 := hMSB N k Y ω 1 hY fun x _ => hω.2 x
    rw [one_mul] at h1 h2
    apply ENNReal.ofReal_le_ofReal
    show X ω - Y ω ≤ _
    linarith [le_abs_self (X ω), neg_abs_le (Y ω)]
  ext ω
  rw [hcylω _ hXY]
  show X (S ω) - Y (S ω) = cyl X ω - cyl Y ω
  rw [hcylω X hX, hcylω Y hY]
/-- The support of `Z = X ∘ S` lies in the cylinder `C = ι([0, 1] × spt X)`, `ι(t, x) = (t, x)`,
and is compact (step 7 of the cylinder construction, Simon 6.2.17–2.21).  `C` is the continuous
image of the compact `[0, 1] × spt X`, hence compact and closed.  For `y ∉ C` pick
`B(y, r) ⊆ Cᶜ`; it is open with compact closure, and if `tsupport ω ⊆ B(y, r)` then
`tsupport S(ω)` misses `spt X` (a point `x` of both gives `ι(t, x) ∈ tsupport ω ∩ C`), so (VO)
gives `Z(ω) = X(S(ω)) = 0`.  Hence `y` lies in the zero region of `Z`, i.e. `spt Z ⊆ C`, and
`spt Z = (zero region)ᶜ` is closed, so compact. -/
theorem Submission.cmcdt_lpo_cyl_support : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (Z : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) → TestFormOn (univ : Set (Euclid N)) k), IsCompact X.support → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), tsupport (S ω : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), Z ω = X (S ω)) → IsCompact Z.support ∧ Z.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
  intro hVO N k X Z S hXc hS hZ
  set C : Set (Euclid (N + 1)) := {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
    y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}
  -- `C = ι([0, 1] × spt X)` is compact
  have hCc : IsCompact C := by
    have hCι : C = (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
          (Icc (0 : ℝ) 1 ×ˢ X.support) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [hCι]
    exact (isCompact_Icc.prod hXc).image (by fun_prop)
  -- `spt Z ⊆ C`: a ball `B(y, r) ⊆ Cᶜ` lies in the zero region of `Z`
  have hsub : Z.support ⊆ C := by
    intro y hy
    by_contra hyC
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hCc.isClosed.isOpen_compl y hyC
    refine hy.2 (Set.mem_sUnion.mpr ⟨ball y r, ⟨isOpen_ball, ?_, subset_univ _, ?_⟩,
      mem_ball_self hr⟩)
    · exact (isCompact_closedBall y r).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · intro ω hω
      rw [hZ ω]
      refine hVO N k univ X (S ω) (Set.disjoint_left.mpr fun x hx hxX => ?_)
      obtain ⟨t, ht, hmem⟩ := hS ω hx
      exact hball (hω hmem) ⟨t, ht, x, hxX, rfl⟩
  -- `spt Z = (zero region)ᶜ` is closed, so compact
  exact ⟨hCc.of_isClosed_subset (isClosed_univ.sdiff Z.isOpen_zeroRegion) hsub, hsub⟩
/-- **Simon 6.2.21** (mass form): `Z = [[(0, 1)]] × X` acts by `Z(ω) = X(S_k ω)`, where
`S_m ω(x) = ∫₀¹ ω(t, x)(e₀, ·) dt` integrates out the first coordinate of `ℝ^{N+1} = ℝ × ℝᴺ`.
If `M(X) < ∞` and `M(∂X) < ∞` then `M(∂Z) < ∞`.  For admissible `ω`, `∂Z(ω) = X(S_k dω)`, and the
slice identities give `S_k dω = ρ₁ − ρ₀ − dθ`, where `ρ_s` is the slice of `ω` at height `s`
and `θ = S_{k−1} ω` (no `dθ` term for `k = 0`).  So `∂Z(ω) ≤ 2 M(X) + M(∂X)`. -/
theorem Submission.cmcdt_lpo_cyl_boundary_mass : (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) → (∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v) → (∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ N k : ℕ, ∃ Ψ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) k) (v : Fin k → Euclid N), Ψ γ v = γ (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ γ : Covector (Euclid (N + 1)) k, covectorEuclideanNorm (Ψ γ) ≤ covectorEuclideanNorm γ) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (Z : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (S : ∀ m : ℕ, TestFormOn (univ : Set (Euclid (N + 1))) (m + 1) → TestFormOn (univ : Set (Euclid N)) m), X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ (m : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (m + 1)) (x : Euclid N) (v : Fin m → Euclid N), (S m ω : DifferentialForm (Euclid N) m) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (m + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ (m : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (m + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (m + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S m ω : DifferentialForm (Euclid N) m) x) ≤ c) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), Z ω = X (S k ω)) → Z.boundary.mass < ∞ := by
  intro hMSB hSLB hSLC hSLD hR2 N k X Z S hXm hXb hS hSb hZ
  obtain ⟨Ψ, hΨ, hΨn⟩ := hR2 N k
  -- every admissible evaluation of `∂Z` is at most `2 M(X) + M(∂X)`
  have key : ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid (N + 1))) k univ,
      Z.boundary ω ≤ 2 * X.mass.toReal + (boundaryMassOn X univ).toReal := by
    intro ω hω
    -- the end slice `ρ_s(x) = Ψ(ω(s, x))` has norm `≤ 1`, so `|X(ρ_s)| ≤ M(X)`
    have hend : ∀ s : ℝ, ∃ ρ : TestFormOn (univ : Set (Euclid N)) k,
        (∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧
        |X ρ| ≤ X.mass.toReal := by
      intro s
      obtain ⟨ρ, hρ⟩ := hSLB N k s ω
      refine ⟨ρ, hρ, ?_⟩
      have h := hMSB N k X ρ 1 hXm fun x _ => by
        have hx : (ρ : DifferentialForm (Euclid N) k) x =
            Ψ ((ω : DifferentialForm (Euclid (N + 1)) k)
              (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) := by
          ext v
          rw [hρ, hΨ]
        rw [hx]
        exact (hΨn _).trans (hω.2 _)
      rwa [one_mul] at h
    obtain ⟨ρ₀, hρ₀, h₀⟩ := hend 0
    obtain ⟨ρ₁, hρ₁, h₁⟩ := hend 1
    rw [(GeometricCurrentOn.boundary_apply Z ω).trans (hZ _)]
    cases k with
    | zero =>
      -- `S₀(dω) = ρ₁ - ρ₀`
      have hSd : S 0 (exteriorDerivativeTestOn univ 0 ω) = ρ₁ - ρ₀ := by
        apply Subtype.ext
        funext x
        ext v
        rw [hS 0 _ x v]
        simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
        rw [hρ₁, hρ₀]
        exact hSLD N ω x v
      have hlin : X (ρ₁ - ρ₀) = X ρ₁ - X ρ₀ := map_sub X.toCurrent ρ₁ ρ₀
      have hb : 0 ≤ (boundaryMassOn X univ).toReal := ENNReal.toReal_nonneg
      rw [hSd, hlin]
      linarith [le_abs_self (X ρ₁), neg_abs_le (X ρ₀)]
    | succ k' =>
      -- `S_{k'+1}(dω) = ρ₁ - ρ₀ - dθ` with `θ = S_{k'}(ω)`
      have hSd : S (k' + 1) (exteriorDerivativeTestOn univ (k' + 1) ω) =
          ρ₁ - ρ₀ - exteriorDerivativeTestOn univ k' (S k' ω) := by
        apply Subtype.ext
        funext x
        ext v
        rw [hS (k' + 1) _ x v]
        simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
        rw [hρ₁, hρ₀]
        exact hSLC N k' ω (S k' ω) (hS k' ω) x v
      have hlin₁ : X (ρ₁ - ρ₀ - exteriorDerivativeTestOn univ k' (S k' ω)) =
          X (ρ₁ - ρ₀) - X.boundary (S k' ω) := map_sub X.toCurrent _ _
      have hlin₀ : X (ρ₁ - ρ₀) = X ρ₁ - X ρ₀ := map_sub X.toCurrent ρ₁ ρ₀
      -- `|θ| ≤ 1`, so `|∂X(θ)| ≤ M(∂X)`
      have hθ := hMSB N k' X.boundary (S k' ω) 1 hXb fun x _ => hSb k' ω 1 hω.2 x
      have hbm : (boundaryMassOn X univ).toReal = X.boundary.mass.toReal := rfl
      rw [hSd, hlin₁, hlin₀, hbm]
      linarith [le_abs_self (X ρ₁), neg_abs_le (X ρ₀), neg_abs_le (X.boundary (S k' ω))]
  -- hence `M(∂Z) ≤ 2 M(X) + M(∂X) < ∞`
  have hle : Z.boundary.mass ≤
      ENNReal.ofReal (2 * X.mass.toReal + (boundaryMassOn X univ).toReal) := by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal (key ω hω)
  exact hle.trans_lt ENNReal.ofReal_lt_top
/-- Coordinates for the products `[[(0,1)]] × T` and `{p} × T` (Simon 6.2.17, 6.2.21–2.22),
`ℝ × ℝᴺ ≅ ℝᴺ⁺¹`, `(t, x) ↦ (t, x₁, …, x_N)`: the composite of `id × ofLp`, `Fin.consLinearEquiv`
and `toLp` is a linear equivalence, continuous in finite dimension, with `L(1, 0) = e₀` and
`‖L(0, x)‖ = ‖x‖`. -/
theorem Submission.cmcdt_lpo_slice_coords : ∀ N : ℕ, ∃ L : (ℝ × Euclid N) ≃L[ℝ] Euclid (N + 1), (∀ (t : ℝ) (x : Euclid N), L (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∧ L (1, 0) = EuclideanSpace.single 0 1 ∧ ∀ x : Euclid N, ‖L (0, x)‖ = ‖x‖ := by
  intro N
  -- `(t, x) ↦ (t, ofLp x) ↦ Fin.cons t (ofLp x) ↦ toLp 2 (Fin.cons t (ofLp x))`
  let e : (ℝ × Euclid N) ≃ₗ[ℝ] Euclid (N + 1) :=
    ((LinearEquiv.refl ℝ ℝ).prodCongr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))).trans
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (N + 1) => ℝ)).trans
        (WithLp.linearEquiv 2 ℝ (Fin (N + 1) → ℝ)).symm)
  -- `e` is continuous in finite dimension; (i) holds by unfolding the three maps
  have hL : ∀ (t : ℝ) (x : Euclid N),
      e.toContinuousLinearEquiv (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) :=
    fun _ _ => rfl
  refine ⟨e.toContinuousLinearEquiv, hL, ?_, fun x => ?_⟩
  · -- (ii): compare coordinates, splitting the index into `0` and `j.succ`
    rw [hL]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  · -- (iii): `‖L (0, x)‖² = ‖0‖² + ∑ⱼ ‖xⱼ‖² = ‖x‖²`
    rw [hL, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq x, Fin.sum_univ_succ]
    simp
/-- Smoothness of parametric integrals over `[0, 1]`, used for the slice form of `[[0, 1]] × T`
(Simon 6.2.17–2.22).  If `h : ℝ × ℝᴺ → V` is `C^∞`, then `x ↦ ∫₀¹ h(t, x) dt` is `C^∞` and its
derivative at `x` is `∫₀¹ D[x' ↦ h(t, x')](x) dt`.  The derivative formula is differentiation under
the integral sign, with the partial derivative bounded on `[0, 1] × closedBall x 1`; `C^n` follows
by induction on `n` over all value spaces, the derivative being a parametric integral of the
`C^∞` map `(t, x) ↦ D[x' ↦ h(t, x')](x)` with values in `L(ℝᴺ, V)`. -/
theorem Submission.cmcdt_lpo_slice_param_integral : ∀ (N : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (h : ℝ × Euclid N → V), ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x)) ∧ ∀ x : Euclid N, HasFDerivAt (fun x' : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x')) (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x) x := by
  intro N
  -- Steps 1–2: `x' ↦ h (t, x')` has derivative `(fderiv ℝ h (t, x)).comp inr` at `x`, so the
  -- partial derivative `h₁ p = fderiv ℝ (fun x' => h (p.1, x')) p.2` is `C^∞` in `p`.
  have hsmooth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h →
        ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Euclid N => fderiv ℝ (fun x' : Euclid N => h (p.1, x')) p.2) := by
    intro V _ _ h hh
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ h) := (contDiff_infty_iff_fderiv.1 hh).2
    have hpart : (fun p : ℝ × Euclid N => fderiv ℝ (fun x' : Euclid N => h (p.1, x')) p.2) =
        fun p => (fderiv ℝ h p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)) := by
      funext p
      exact (((contDiff_infty_iff_fderiv.1 hh).1 p).hasFDerivAt.comp p.2
        (hasFDerivAt_prodMk_right p.1 p.2)).fderiv
    rw [hpart]
    exact hd.clm_comp contDiff_const
  -- Step 3: differentiation under the integral sign, with a uniform bound on the partial
  -- derivative over the compact set `[0, 1] × closedBall x₀ 1`.
  have hderiv : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h → ∀ x₀ : Euclid N,
        HasFDerivAt (fun x' : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x'))
          (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x₀) x₀ := by
    intro V _ _ h hh x₀
    have hdiff : Differentiable ℝ h := (contDiff_infty_iff_fderiv.1 hh).1
    have hc : Continuous h := hh.continuous
    have h₁c := (hsmooth V h hh).continuous
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      h₁c.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => h (t, x)) (F' := fun x t => fderiv ℝ (fun x' : Euclid N => h (t, x')) x)
      (bound := fun _ => B) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun x =>
        (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (h₁c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_uIoc).mono fun t ht x hx => ?_
      rw [uIoc_of_le zero_le_one] at ht
      exact hB (t, x) (Set.mk_mem_prod (Ioc_subset_Icc_self ht) (ball_subset_closedBall hx))
    · exact Eventually.of_forall fun t x _ =>
        ((hdiff (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).differentiableAt.hasFDerivAt
  -- Step 4: `C^n` for every `n`, by induction over all value spaces at once.
  have hind : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ n (fun x : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x)) := by
    intro n
    induction n with
    | zero =>
      intro V _ _ h hh
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x => (hderiv V h hh x).continuousAt
    | succ n ih =>
      intro V _ _ h hh
      rw [Nat.cast_add_one, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x,
        ih (Euclid N →L[ℝ] V) _ (hsmooth V h hh), hderiv V h hh⟩
  -- Step 5.
  intro V _ _ _ h hh
  exact ⟨contDiff_infty.2 fun n => hind n V h hh, hderiv V h hh⟩

/-- **Coordinate splitting of `dβ` along `ℝ × ℝᴺ`** (pointwise form of Simon 6.2.17–2.21,
`∂([[0,1]] × T) = {1} × T − {0} × T − [[0,1]] × ∂T`).  Write `ι(s, y) = (s, y)`, `Jy = ι(0, y)` and
`e₀ = ι(1, 0)`; by `cmcdt_lpo_slice_coords`, `ι = L` for a continuous linear equivalence `L`.
Expand `dβ(ι(t, x))(e₀, Jv₀, …, Jvₖ) = Σᵢ (−1)ⁱ D[y ↦ β(y)(Ŵᵢ)](ι(t, x))(Wᵢ)` by
`exteriorDerivative_apply`, where `W = (e₀, Jv₀, …, Jvₖ)` and `Ŵᵢ` omits `Wᵢ`, and split off
`i = 0`.  As `y ↦ β(y)(u)` has derivative `m ↦ Dβ(y)(m)(u)`, the chain rule along `s ↦ ι(s, x)`
(derivative `e₀`) turns the `0`-th term into `d/ds|_{s=t} β(ι(s, x))(Jv)`.  For `i = j + 1`,
`Ŵᵢ = (e₀, J(removeNth j v))` and `Wᵢ = Jvⱼ`, and the chain rule along `x' ↦ ι(t, x')` (derivative
`J`) together with `(−1)^{j+1} = −(−1)^j` turns the term into
`−(−1)^j D[x' ↦ β(ι(t, x'))(e₀, J(removeNth j v))](x)(vⱼ)`. -/
theorem Submission.cmcdt_lpo_slice_extDeriv_split : ∀ (N k : ℕ) (β : DifferentialForm (Euclid (N + 1)) (k + 1)), Differentiable ℝ β → ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N), exteriorDerivative β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = deriv (fun s : ℝ => β (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) t - ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) • fderiv ℝ (fun x' : Euclid N => β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) := by
  intro N k β hβ t x v
  -- Step 1: the coordinate map `ι(s, y)` is `L (s, y)`, and `e₀ = L (1, 0)` (sibling `coords`)
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  simp only [← hL, ← hL1]
  -- Step 2: `y ↦ β y u` has derivative `m ↦ Dβ(y)(m)(u)`
  have hβu : ∀ (u : Fin (k + 1) → Euclid (N + 1)) (y : Euclid (N + 1)),
      HasFDerivAt (fun z => β z u) (fderiv ℝ (fun z => β z u) y) y := fun u y =>
    ((hβ y).continuousAlternatingMap_apply_const u).hasFDerivAt
  -- Step 3: derivatives of the coordinate paths `s ↦ L (s, x)` and `x' ↦ L (t, x')`
  have hpath₁ : HasDerivAt (fun s : ℝ => L (s, x)) (L (1, 0)) t :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hpath₂ : HasFDerivAt (fun x' : Euclid N => L (t, x'))
      ((L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N))) x :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have hslice : ∀ (u : Fin (k + 1) → Euclid (N + 1)) (y : Euclid N),
      fderiv ℝ (fun x' : Euclid N => β (L (t, x')) u) x y =
        fderiv ℝ (fun z => β z u) (L (t, x)) (L (0, y)) := by
    intro u y
    have h := (hβu u (L (t, x))).comp x hpath₂
    simp only [Function.comp_def] at h
    rw [h.fderiv]
    rfl
  -- Step 4: expand `dβ` and split off the index `0`
  rw [exteriorDerivative_apply (hβ _), Fin.sum_univ_succ, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · -- Step 5: the `0`-th term is `deriv φ t`, `φ s = β (L (s, x)) (Jv)`
    have h := (hβu (fun i => L (0, v i)) (L (t, x))).comp_hasDerivAt t hpath₁
    simp only [Function.comp_def] at h
    rw [h.deriv, Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero, Fin.tail_cons,
      Fin.cons_zero]
  · -- Step 6: the `(j + 1)`-st term, with `Ŵ = (e₀, J(removeNth j v))` and sign `−(−1)^j`
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrem : Fin.removeNth j.succ
        (Fin.cons (L (1, 0)) (fun i => L (0, v i)) : Fin (k + 1 + 1) → Euclid (N + 1)) =
        Fin.cons (L (1, 0)) (fun i => L (0, Fin.removeNth j v i)) :=
      Fin.cons_comp_succ_succAbove (L (1, 0)) (fun i => L (0, v i)) j
    rw [hslice, hrem, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
/-- **Simon 6.2.17** (the slice form of `[[0, 1]] × T`): for `ω ∈ 𝒟^{k+1}(ℝ^{N+1})` the fibre
integral `η(x)(v) = ∫₀¹ ω(t, x)(e₀, (0, v₁), …, (0, vₖ)) dt` is a test `k`-form on `ℝᴺ` with
`spt η ⊆ {x : (t, x) ∈ spt ω for some t ∈ [0, 1]}`.  In the coordinates `L (t, x) = (t, x)`,
`η` integrates `g (t, x) = Φ (ω (L (t, x)))` for the contraction
`Φ γ = γ (L (1, 0), J ·, …, J ·)`, `J y = L (0, y)`; it is smooth by the parametric integral
lemma and vanishes off the compact set `snd '' (L⁻¹ (spt ω) ∩ [0, 1] × ℝᴺ)`. -/
theorem Submission.cmcdt_lpo_slice_fiber_form : ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))} := by
  intro N k ω
  set ω' : DifferentialForm (Euclid (N + 1)) (k + 1) :=
    (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω' := ω.property.1.1
  have hωc : HasCompactSupport ω' := ω.property.1.2
  -- coordinates `L (t, y) = (t, y)` with `L (1, 0) = e₀`, and `J y = L (0, y)`
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  let J : Euclid N →L[ℝ] Euclid (N + 1) :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N))
  -- the contraction `Φ γ = γ (L (1, 0), J ·, …, J ·)` is continuous linear
  let Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k) (L (1, 0))).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap)
  have hΦ : ∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N),
      Φ γ v = γ (Fin.cons (L (1, 0)) fun i => L (0, v i)) := fun _ _ => rfl
  -- `g (t, x) = Φ (ω (L (t, x)))` is smooth, hence so is `η x = ∫₀¹ g (t, x) dt`
  let g : ℝ × Euclid N → Covector (Euclid N) k := fun p => Φ (ω' (L p))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Φ.contDiff.comp (hωs.comp L.contDiff)
  let η : DifferentialForm (Euclid N) k := fun x => ∫ t in (0 : ℝ)..1, g (t, x)
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η :=
    (Submission.cmcdt_lpo_slice_param_integral N (Covector (Euclid N) k) g hg).1
  -- `η` vanishes off the compact set `snd '' (L⁻¹ (spt ω) ∩ [0, 1] × ℝᴺ)`
  have hS : IsCompact (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) :=
    (L.toHomeomorph.isCompact_preimage.2 hωc.isCompact).inter_right
      (isClosed_Icc.prod isClosed_univ)
  have hsupp : support η ⊆ Prod.snd '' (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) := by
    intro x hx
    by_contra hxS
    refine mem_support.1 hx ?_
    have h0 : EqOn (fun t => g (t, x)) (fun _ => 0) (uIcc 0 1) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hnot : L (t, x) ∉ tsupport ω' := fun hmem =>
        hxS ⟨(t, x), ⟨hmem, ht, mem_univ _⟩, rfl⟩
      show Φ (ω' (L (t, x))) = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, map_zero]
    exact (intervalIntegral.integral_congr h0).trans intervalIntegral.integral_zero
  have hηt : tsupport η ⊆ Prod.snd '' (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) :=
    closure_minimal hsupp (hS.image continuous_snd).isClosed
  refine ⟨⟨η, ⟨hηs, (hS.image continuous_snd).of_isClosed_subset (isClosed_tsupport η) hηt⟩,
    subset_univ _⟩, fun x v => ?_, hηt.trans ?_⟩
  · -- evaluation at `v` commutes with the integral
    have hint : IntervalIntegrable (fun t => g (t, x)) volume 0 1 :=
      (hg.continuous.comp (Continuous.prodMk_left x)).intervalIntegrable 0 1
    let ev : Covector (Euclid N) k →L[ℝ] ℝ := ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ v
    calc η x v = ev (∫ t in (0 : ℝ)..1, g (t, x)) := rfl
      _ = ∫ t in (0 : ℝ)..1, ev (g (t, x)) := (ev.intervalIntegral_comp_comm hint).symm
      _ = _ := intervalIntegral.integral_congr fun t _ => by
        change Φ (ω' (L (t, x))) v = _
        rw [hΦ, hL1]
        simp only [hL]
  · rintro _ ⟨⟨t, y⟩, ⟨hmem, ht, -⟩, rfl⟩
    rw [mem_preimage, hL] at hmem
    exact ⟨t, ht, hmem⟩

/-- **End slices of `[[0, 1]] × T`** (Simon Ch. 6, 2.22: `{p} × T(ω) = T(Σ_β ω_{0β}(p, ·) dy^β)`).
Write `ι(t, x) = (t, x₁, …, x_N)` and `Jv = ι(0, v)`.  For `ω ∈ 𝒟ᵏ(ℝ^{N+1})` and `s ∈ ℝ`, the
form `ρ(x)(v₁, …, vₖ) = ω(ι(s, x))(Jv₁, …, Jvₖ)` lies in `𝒟ᵏ(ℝ^N)`.  With the coordinates
`L(t, y) = ι(t, y)` of `cmcdt_lpo_slice_coords`, `ρ` is the pull-back of `ω` by the affine map
`x ↦ L(s, 0) + L(0, x)`, which is proper since `‖x‖ = ‖L(0, x)‖ ≤ ‖L(s, 0) + L(0, x)‖ + ‖L(s, 0)‖`.
-/
theorem Submission.cmcdt_lpo_slice_end_form : ∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
  intro N k s ω
  obtain ⟨L, hL, -, hLn⟩ := Submission.cmcdt_lpo_slice_coords N
  -- `J y = L(0, y)`, so that `L(s, 0) + J x = L(s, x)`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1), ∀ y, J y = L (0, y) :=
    ⟨(L : (ℝ × Euclid N) →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)),
      fun _ => rfl⟩
  have hsJ : ∀ x, L (s, 0) + J x = L (s, x) := fun x => by
    rw [hJ, ← map_add L, Prod.mk_add_mk, add_zero, zero_add]
  -- `x ↦ L(s, 0) + J x` is proper: `‖x‖ = ‖J x‖ ≤ ‖L(s, 0) + J x‖ + ‖L(s, 0)‖`
  have hcont : Continuous fun x => L (s, 0) + J x := continuous_const.add J.continuous
  have hproper : IsProperMap fun x => L (s, 0) + J x := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine isCompact_of_isClosed_isBounded (hK.isClosed.preimage hcont)
      ((isBounded_closedBall (x := (0 : Euclid N)) (r := R + ‖L (s, 0)‖)).subset fun x hx => ?_)
    have hxR : ‖L (s, 0) + J x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖L (s, 0) + J x - L (s, 0)‖ := by rw [add_sub_cancel_left, hJ, hLn]
      _ ≤ ‖L (s, 0) + J x‖ + ‖L (s, 0)‖ := norm_sub_le _ _
      _ ≤ R + ‖L (s, 0)‖ := by linarith
  -- `ρ` is the affine pull-back of `ω`, a test form on `ℝ^N` by properness
  refine ⟨⟨affinePullbackForm J (L (s, 0)) (ω : DifferentialForm (Euclid (N + 1)) k), ?_⟩,
    fun x v => ?_⟩
  · exact show IsTestForm _ ∧ _ from
      ⟨affinePullbackForm_isTestForm J (L (s, 0)) hproper ω.property.1, subset_univ _⟩
  · show affinePullbackForm J (L (s, 0)) (ω : DifferentialForm (Euclid (N + 1)) k) x v = _
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hsJ, hL]
    congr 1
    funext i
    rw [Function.comp_apply, hJ, hL]

/-- **Slice homotopy identity in degree `k + 1`** (Simon 6.2.19, 6.2.21 at the level of forms:
`S_{dβ} = i₁^#β − i₀^#β − dS_β`).  Write `ι(t, x) = (t, x)`, `Jv = ι(0, v)` and `e₀ = ι(1, 0)`.
If `θ(x)(u) = ∫₀¹ β(ι(t, x))(e₀, Ju) dt` for all `x` and `u`, then
`∫₀¹ dβ(ι(t, x))(e₀, Jv) dt = β(ι(1, x))(Jv) − β(ι(0, x))(Jv) − dθ(x)(v)`.

By `cmcdt_lpo_slice_extDeriv_split` the integrand is `∂ₜ[β(ι(t, x))(Jv)]` minus the alternating
sum of the `x`-derivatives of the slices `β(ι(t, ·))(e₀, J v̂ⱼ)`.  The first term integrates to
the boundary terms (fundamental theorem of calculus).  Differentiating the hypothesis under the
integral sign (`cmcdt_lpo_slice_param_integral`; smoothness via the linear coordinates of
`cmcdt_lpo_slice_coords`) and expanding `dθ` identifies the integral of the second term with
`dθ(x)(v)`. -/
theorem Submission.cmcdt_lpo_slice_homotopy_succ : ∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v := by
  intro N k β θ hθ x v
  set B := (β : DifferentialForm (Euclid (N + 1)) (k + 1))
  set Θ := (θ : DifferentialForm (Euclid N) k)
  have hBs : ContDiff ℝ (⊤ : ℕ∞) B := β.property.1.1
  have hΘd : Differentiable ℝ Θ := θ.property.1.1.differentiable (by simp)
  -- (1) `p ↦ B(ι p)(w)` is smooth for each fixed tuple `w`, as `ι` is the linear equivalence `L`
  obtain ⟨L, hL, -, -⟩ := Submission.cmcdt_lpo_slice_coords N
  have hG : ∀ w : Fin (k + 1) → Euclid (N + 1), ContDiff ℝ (⊤ : ℕ∞)
      fun p : ℝ × Euclid N => B (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))) w := by
    intro w
    have hfun : (fun p : ℝ × Euclid N => B (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))) w) =
        ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w ∘ B ∘ L := by
      funext p
      simp only [Function.comp_apply, ContinuousAlternatingMap.apply_apply, ← hL, Prod.mk.eta]
    rw [hfun]
    exact (ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w).contDiff.comp
      (hBs.comp L.contDiff)
  -- (2) the `x`-derivative of each slice is continuous in `t`
  have hD : ∀ w : Fin (k + 1) → Euclid (N + 1), Continuous fun t : ℝ =>
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) w) x :=
    fun w => Continuous.fderiv
      (f := fun (t : ℝ) (x' : Euclid N) => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) w)
      (hG w) continuous_const (by simp)
  -- (3) differentiate the hypothesis on `θ` under the integral sign
  have hΘD : ∀ u : Fin k → Euclid N, fderiv ℝ (fun x' : Euclid N => Θ x' u) x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t
        (WithLp.ofLp x'))) (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i)))))) x := by
    intro u
    rw [show (fun x' : Euclid N => Θ x' u) = _ from funext fun x' => hθ x' u]
    exact ((Submission.cmcdt_lpo_slice_param_integral N ℝ _ (hG _)).2 x).fderiv
  -- (4) split the integrand into a `t`-derivative and the alternating sum of `x`-derivatives
  simp only [Submission.cmcdt_lpo_slice_extDeriv_split N k B (hBs.differentiable (by simp))]
  -- (5) fundamental theorem of calculus for `φ(s) = B(ι(s, x))(Jv)`
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => B (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
      (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :=
    (hG _).comp (contDiff_id.prodMk contDiff_const)
  have hFTC := intervalIntegral.integral_deriv_eq_sub (fun s _ => hφ.differentiable (by simp) s)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
  -- (6) the integral of the alternating sum is `dΘ(x)(v)`
  have hcont : ∀ j : Fin (k + 1), Continuous fun t : ℝ => (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x')))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) :=
    fun j => ((hD _).clm_apply continuous_const).fun_const_smul ((-1 : ℤ) ^ (j : ℕ))
  have hsum : ∫ t in (0 : ℝ)..1, ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x')))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) =
      exteriorDerivative Θ x v := by
    rw [exteriorDerivative_apply (hΘd x) v,
      intervalIntegral.integral_finsetSum fun j _ => (hcont j).intervalIntegrable 0 1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΘD, ContinuousLinearMap.intervalIntegral_apply ((hD _).intervalIntegrable 0 1)]
    simp only [zsmul_eq_mul, intervalIntegral.integral_const_mul]
  -- (7) linearity of the integral
  rw [intervalIntegral.integral_sub ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
    ((continuous_finsetSum _ fun j _ => hcont j).intervalIntegrable 0 1), hFTC, hsum]

/-- **Slice homotopy identity in degree `0`** (Simon 6.2.21 without the `∂T` term).  For
`β ∈ 𝒟⁰(ℝ^{N+1})`, `x ∈ ℝ^N` and the empty tuple `w = J ∘ v`,
`∫₀¹ dβ(ι(t, x))(e₀) dt = β(ι(1, x))(w) − β(ι(0, x))(w)`, where `ι(t, x) = (t, x)`.
With the coordinates `L(t, x) = ι(t, x)`, `L(1, 0) = e₀` of `cmcdt_lpo_slice_coords`, the path
`φ(s) = β(L(s, x))(w)` is smooth with `φ′(s) = D[y ↦ β(y)(w)](L(s, x))(e₀)`, the single term
`i = 0` of `exteriorDerivative_apply` (as `removeNth 0 (e₀, w) = w`); the fundamental theorem of
calculus concludes. -/
theorem Submission.cmcdt_lpo_slice_homotopy_zero : ∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
  intro N β x v
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  set ω : DifferentialForm (Euclid (N + 1)) 0 := (β : DifferentialForm (Euclid (N + 1)) 0)
  set w : Fin 0 → Euclid (N + 1) := fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω := β.property.1.1
  -- `y ↦ ω y w` is `ω` followed by the continuous linear evaluation at `w`
  have hωw : ContDiff ℝ (⊤ : ℕ∞) (fun y => ω y w) :=
    (ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w).contDiff.comp hω
  -- chain rule along the path `s ↦ L (s, x)`, whose velocity is `L (1, 0)`
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => L (s, x)) (L (1, 0)) s := fun s =>
    L.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ω (L (s, x)) w)
      (fderiv ℝ (fun y => ω y w) (L (s, x)) (L (1, 0))) s := fun s =>
    ((hωw.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s (hpath s)
  -- in degree `0` the exterior derivative is the single term `i = 0`
  have hpt : ∀ s : ℝ, exteriorDerivative ω (L (s, x)) (Fin.cons (L (1, 0)) w) =
      fderiv ℝ (fun y => ω y w) (L (s, x)) (L (1, 0)) := by
    intro s
    rw [exteriorDerivative_apply ((hω.differentiable (by simp)) _)]
    simp only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Int.reduceNeg,
      Fin.val_eq_zero, pow_zero, one_smul, Finset.sum_singleton, Fin.removeNth_zero,
      Fin.tail_cons, Fin.cons_zero]
  have hderiv : deriv (fun s : ℝ => ω (L (s, x)) w) =
      fun s => exteriorDerivative ω (L (s, x)) (Fin.cons (L (1, 0)) w) := by
    funext s
    rw [(hφ s).deriv, hpt]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ω (L (s, x)) w) :=
    hωw.comp (L.contDiff.comp (contDiff_id.prodMk contDiff_const))
  -- fundamental theorem of calculus, then back to the coordinates of the statement
  have key := intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1) _ hderiv
    (fun s _ => (hφ s).differentiableAt)
    (hderiv ▸ (hsmooth.continuous_deriv (by simp)).continuousOn)
  rw [hL1] at key
  simpa only [hL] using key
/-- **Simon 6.1.15, 6.2.17** (Minkowski's integral inequality for the Euclidean coefficient norm
`|·|` of 6.1.15, used for the slice forms defining `[[(0, 1)]] × T`): if `α(v) = ∫₀¹ f(t)(v) dt`
for all `v` and `|f(t)| ≤ c` on `[0, 1]`, then `|α| ≤ c`.  The coefficient vector
`κ(γ) = (γ(e_I))_{I strictly increasing} ∈ ℓ²` has `‖κ(γ)‖ = |γ|`, is continuous, and commutes
with the integral coordinatewise; hence `|α| = ‖∫₀¹ κ(f t) dt‖ ≤ c`. -/
theorem Submission.cmcdt_lpo_slice_covector_bound : ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c := by
  intro N k α f c hf hα hc
  classical
  -- the coefficient vector `κ γ = (γ(e_I))_I`, with `γ(e_I)` replaced by `0` unless `I` is
  -- strictly increasing
  let e : Fin N → Euclid N := fun j => EuclideanSpace.basisFun (Fin N) ℝ j
  let κ : Covector (Euclid N) k → EuclideanSpace ℝ (Fin k → Fin N) := fun γ =>
    WithLp.toLp 2 fun I => if StrictMono I then γ (fun i => e (I i)) else 0
  have hκnorm : ∀ γ, ‖κ γ‖ = covectorEuclideanNorm γ := by
    intro γ
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [κ, e, hI]
  have hκcont : Continuous κ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun I => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ite_true]
      exact continuous_eval_const _
    · simp only [hI, ite_false]
      exact continuous_const
  have hint : IntervalIntegrable (fun t => κ (f t)) volume 0 1 :=
    (hκcont.comp hf).intervalIntegrable 0 1
  -- `κ α = ∫₀¹ κ (f t) dt`, coordinatewise
  have hκα : κ α = ∫ t in (0 : ℝ)..1, κ (f t) := by
    ext I
    refine Eq.trans ?_ ((EuclideanSpace.proj I :
      EuclideanSpace ℝ (Fin k → Fin N) →L[ℝ] ℝ).intervalIntegral_comp_comm hint)
    by_cases hI : StrictMono I
    · simp only [κ, EuclideanSpace.coe_proj, hI, ite_true]
      exact hα _
    · simp only [κ, EuclideanSpace.coe_proj, hI, ite_false, intervalIntegral.integral_zero]
  rw [← hκnorm, hκα]
  calc ‖∫ t in (0 : ℝ)..1, κ (f t)‖ ≤ c * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
          rw [hκnorm]
          exact hc t (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le zero_le_one] using ht))
    _ = c := by simp

/-- **Slices of forms on `[0, 1] × ℝᴺ`** (Simon Ch. 6, 2.17–2.22, and the homotopy formula
2.25–2.27).  Write `ι(t, x) = (t, x₁, …, x_N)`, `Jv = ι(0, v)` and `e₀ = EuclideanSpace.single 0 1`.
(a) `η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt` is a test form on `ℝᴺ`, supported in the set of `x`
with `ι(t, x) ∈ spt ω` for some `t ∈ [0, 1]` (`cmcdt_lpo_slice_fiber_form`); (b) the end slice
`ρ(x)(v) = ω(ι(s, x))(Jv)` is a test form (`cmcdt_lpo_slice_end_form`); (c) if `θ` is the
slice (a) of `β`, then `∫₀¹ dβ(ι(t, x))(e₀, Jv) dt = β(ι(1, x))(Jv) − β(ι(0, x))(Jv) − dθ(x)(v)`
(`cmcdt_lpo_slice_homotopy_succ`); (d) in degree `0` the same identity holds without `dθ`
(`cmcdt_lpo_slice_homotopy_zero`); (e) `|α| ≤ c` when `α = ∫₀¹ f(t) dt` for continuous `f` with
`|f(t)| ≤ c` on `[0, 1]` (`cmcdt_lpo_slice_covector_bound`).  The statement is the conjunction
of these five children. -/
theorem Submission.cmcdt_lpo_slice_forms : (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ (∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v) ∧ (∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c :=
  ⟨Submission.cmcdt_lpo_slice_fiber_form, Submission.cmcdt_lpo_slice_end_form,
    Submission.cmcdt_lpo_slice_homotopy_succ, Submission.cmcdt_lpo_slice_homotopy_zero,
    Submission.cmcdt_lpo_slice_covector_bound⟩

/-- **Slice bound for the homotopy integrand** (Simon 6.2.27, the pointwise estimate of the
integrand of the homotopy formula).  Write `ι(t, x) = (t, x₁, …, x_N)`,
`e₀ = EuclideanSpace.single 0 1`, `Jv = ι(0, v)` and `|·|` for the Euclidean coefficient norm.
Given (L1) `|β ∘ A| ≤ ‖A‖ᵏ |β|` and (L2) `|β ⌟ v| ≤ ‖v‖ |β|`, if `α(v) = ∫₀¹ σ(ι(t, x))(e₀, Jv) dt`
and for each `t ∈ [0, 1]` the integrand is `γ(u, Av)` with `‖A‖ ≤ Λ`, `‖u‖ ≤ δ` and `|γ| ≤ c`,
then `|α| ≤ Λᵐ δ c`.  The integrand is `f(t) = (σ(ι(t, x)) ⌟ e₀) ∘ J`, continuous in `t`; on
`[0, 1]` it equals `(γ ⌟ u) ∘ A`, so `|f(t)| ≤ ‖A‖ᵐ ‖u‖ |γ| ≤ Λᵐ δ c` by (L1) and (L2), and the
Minkowski bound (conjunct (e) of `cmcdt_lpo_slice_forms`) concludes. -/
theorem Submission.cmcdt_lpo_she_slice_bound : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' m : ℕ) (σ : DifferentialForm (Euclid (N + 1)) (m + 1)) (x : Euclid N) (α : Covector (Euclid N) m) (Λ δ c : ℝ), Continuous σ → (∀ v : Fin m → Euclid N, α v = ∫ t in (0 : ℝ)..1, σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ t ∈ Icc (0 : ℝ) 1, ∃ (γ : Covector (Euclid N') (m + 1)) (u : Euclid N') (A : Euclid N →L[ℝ] Euclid N'), ‖A‖ ≤ Λ ∧ ‖u‖ ≤ δ ∧ covectorEuclideanNorm γ ≤ c ∧ ∀ v : Fin m → Euclid N, σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = γ (Fin.cons u (fun i => A (v i)))) → covectorEuclideanNorm α ≤ Λ ^ m * δ * c := by
  intro hcomp hcurry N N' m σ x α Λ δ c hσ hα hγ
  -- (1) `Λ, δ ≥ 0`, from the hypothesis at `t = 0`
  obtain ⟨-, u₀, A₀, hA₀, hu₀, -, -⟩ := hγ 0 ⟨le_rfl, zero_le_one⟩
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hA₀
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hu₀
  -- (2) the embedding `J v = ι(0, v)` is continuous linear (finite dimension)
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun r v => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  -- (3) the integrand `f t = (σ(ι(t, x)) ⌟ e₀) ∘ J`, so `f t v = σ(ι(t, x))(e₀, Jv₁, …, Jvₘ)`
  let f : ℝ → Covector (Euclid N) m := fun t =>
    ((σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))).curryLeft
      (EuclideanSpace.single 0 1)).compContinuousLinearMap J
  have hfv : ∀ (t : ℝ) (v : Fin m → Euclid N), f t v =
      σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1)
        (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
    intro t v
    simp only [f, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    rfl
  -- (4) `f` is continuous
  have hι : Continuous fun t : ℝ =>
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) :=
    (PiLp.continuous_toLp 2 _).comp
      (Continuous.finCons (A := fun _ => ℝ) continuous_id continuous_const)
  have hf : Continuous f :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM J).continuous.comp
      ((ContinuousAlternatingMap.curryLeftLI.continuous.comp (hσ.comp hι)).clm_apply
        continuous_const)
  -- (5) `α v = ∫₀¹ f t v dt`, and (7) the Minkowski bound (conjunct (e) of `slice_forms`)
  refine Submission.cmcdt_lpo_slice_forms.2.2.2.2 N m α f (Λ ^ m * δ * c) hf
    (fun v => (hα v).trans (intervalIntegral.integral_congr fun t _ => (hfv t v).symm)) ?_
  -- (6) `f t = (γ ⌟ u) ∘ A`, so `|f t| ≤ ‖A‖ᵐ ‖u‖ |γ| ≤ Λᵐ δ c` on `[0, 1]`
  intro t ht
  obtain ⟨γ, u, A, hA, hu, hγc, hγv⟩ := hγ t ht
  have hft : f t = (γ.curryLeft u).compContinuousLinearMap A := by
    ext v
    rw [hfv, hγv]
    rfl
  rw [hft]
  calc covectorEuclideanNorm ((γ.curryLeft u).compContinuousLinearMap A)
      ≤ ‖A‖ ^ m * covectorEuclideanNorm (γ.curryLeft u) := hcomp N N' m A _
    _ ≤ ‖A‖ ^ m * (‖u‖ * covectorEuclideanNorm γ) :=
        mul_le_mul_of_nonneg_left (hcurry N' m u γ) (pow_nonneg (norm_nonneg A) m)
    _ ≤ Λ ^ m * (δ * c) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg A) hA m)
          (mul_le_mul hu hγc (covectorEuclideanNorm_nonneg γ) hδ)
          (mul_nonneg (norm_nonneg u) (covectorEuclideanNorm_nonneg γ)) (pow_nonneg hΛ m)
    _ = Λ ^ m * δ * c := (mul_assoc _ _ _).symm
/-- **Cylinder homotopy formula** (Simon 6.2.25 for `[[0, 1]] × X`, through
`∂([[0, 1]] × X) = {1} × X − {0} × X − [[0, 1]] × ∂X`, 6.2.21–2.22).  Write
`ι(t, x) = (t, x₁, …, x_N)`, `Jv = ι(0, v)` and `e₀ = EuclideanSpace.single 0 1`, and assume the
locality property (LOC) of currents.  If `η₁(x)(v) = β(ι(1, x))(Jv)` and `η₀(x)(v) = β(ι(0, x))(Jv)`
for `x` in an open `W ⊇ spt X`, then `X(η₁) − X(η₀) = X(η) + ∂X(θ)` for the slice forms
`η(x)(v) = ∫₀¹ dβ(ι(t, x))(e₀, Jv) dt` and `θ(x)(u) = ∫₀¹ β(ι(t, x))(e₀, Ju) dt`
(`cmcdt_lpo_slice_forms` (a)); in degree `0`, `X(η₁) − X(η₀) = X(η)`.  By the slice identities
(c), (d) of `cmcdt_lpo_slice_forms`, `η = η₁ − η₀ − dθ` (resp. `η₁ − η₀`) on `W`; (LOC), linearity
of `X` and `∂X(θ) = X(dθ)` conclude. -/
theorem Submission.cmcdt_lpo_she_cylinder_homotopy : (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η') → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1)) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, ∀ v : Fin (k + 1) → Euclid N, (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) ∧ (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∃ (η : TestFormOn (univ : Set (Euclid N)) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η : DifferentialForm (Euclid N) (k + 1)) x v = ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ (∀ (x : Euclid N) (u : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x u = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i)))))) ∧ X η₁ - X η₀ = X η + X.boundary θ) ∧ ∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, ∀ v : Fin 0 → Euclid N, (η₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) ∧ (η₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∃ η : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η : DifferentialForm (Euclid N) 0) x v = ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ X η₁ - X η₀ = X η := by
  intro hloc
  -- the slice forms (a) and the slice homotopy identities (c), (d) of `cmcdt_lpo_slice_forms`
  obtain ⟨hA, -, hC, hD, -⟩ := Submission.cmcdt_lpo_slice_forms
  refine ⟨fun N k X β η₀ η₁ W hW hXW hend => ?_, fun N X β η₀ η₁ W hW hXW hend => ?_⟩
  · -- (1), steps 1–2: `η = S_{dβ}` and `θ = S_β` by (a); the coercion of the test form
    -- `exteriorDerivativeTestOn univ (k + 1) β` is definitionally `exteriorDerivative β`
    obtain ⟨η, hη, -⟩ := hA N (k + 1) (exteriorDerivativeTestOn univ (k + 1) β)
    obtain ⟨θ, hθ, -⟩ := hA N k β
    refine ⟨η, θ, hη, hθ, ?_⟩
    -- steps 3–4: by (c) and the end-slice hypotheses, `η = η₁ − η₀ − dθ` on `W`, so (LOC) applies
    have hX : X η = X (η₁ - η₀ - exteriorDerivativeTestOn univ k θ) := by
      refine hloc N (k + 1) X _ _ W hW hXW fun x hx => ?_
      ext v
      rw [hη x v]
      refine (hC N k β θ hθ x v).trans ?_
      obtain ⟨h₁, h₀⟩ := hend x hx v
      rw [← h₁, ← h₀]
      rfl
    -- step 5: linearity of `X` and `∂X(θ) = X(dθ)`
    have hsub : X (η₁ - η₀ - exteriorDerivativeTestOn univ k θ) =
        X η₁ - X η₀ - X (exteriorDerivativeTestOn univ k θ) :=
      (X.toCurrent.map_sub (η₁ - η₀) _).trans (congrArg (· - _) (X.toCurrent.map_sub η₁ η₀))
    rw [GeometricCurrentOn.boundary_apply, hX, hsub]
    ring
  · -- (2), step 6: `η = S_{dβ}` by (a) in degree `0`
    obtain ⟨η, hη, -⟩ := hA N 0 (exteriorDerivativeTestOn univ 0 β)
    refine ⟨η, hη, ?_⟩
    -- step 7: by (d) and the end-slice hypotheses, `η = η₁ − η₀` on `W`, so (LOC) applies
    have hX : X η = X (η₁ - η₀) := by
      refine hloc N 0 X _ _ W hW hXW fun x hx => ?_
      ext v
      rw [hη x v]
      refine (hD N β x v).trans ?_
      obtain ⟨h₁, h₀⟩ := hend x hx v
      rw [← h₁, ← h₀]
      rfl
    -- step 8: linearity of `X`
    rw [hX]
    exact (X.toCurrent.map_sub η₁ η₀).symm
/-- The cut-off pull-back of Simon 6.2.23: for a `C^∞` map `F : ℝᴺ → ℝ^{N'}`, `ω ∈ 𝒟ᵏ(ℝ^{N'})` and
a compact `K ⊆ ℝᴺ`, some `η = ζ F^#ω ∈ 𝒟ᵏ(ℝᴺ)` agrees with `F^#ω` on an open `W ⊇ K`, and
`dη = F^#(dω)` on `W` (as used in 6.2.24(1)).  Here `ζ` is a smooth bump equal to `1` on a ball
`W ⊇ K`.  `F^#ω` is smooth: as a multilinear map, `F^#ω(x) = ω(F x) ∘ (DF(x), …, DF(x))` depends
smoothly on `x`, and `γ ↦ (γ(e_{I 1}, …, e_{I k}))_I` is linear and injective into a
finite-dimensional space, so it has a continuous linear left inverse.  On `W`, `η = F^#ω` near
each point, so `dη = d(F^#ω) = F^#(dω)` (`extDeriv_pullback`). -/
theorem Submission.cmcdt_lpo_cutoff_pullback : ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
  intro N N' k F ω K hF hK
  set ω₀ : DifferentialForm (Euclid N') k := (ω : DifferentialForm (Euclid N') k)
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω₀ := ω.2.1.1
  have hDF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right le_rfl
  -- the pull-back `P = F^#ω` is smooth
  set P : DifferentialForm (Euclid N) k :=
    fun x => (ω₀ (F x)).compContinuousLinearMap (fderiv ℝ F x)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := by
    let ι : Covector (Euclid N) k →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclid N) ℝ :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x => ι (P x) := by
      have h := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => Euclid N) (fun _ : Fin k => Euclid N') ℝ).contDiff.comp
          (contDiff_pi.2 fun _ => hDF)).clm_apply
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp (hω.comp hF))
      convert h using 1
      funext x
      ext v
      simp [ι, P, Function.comp_def]
    -- the values on basis tuples determine a covector
    let e := EuclideanSpace.basisFun (Fin N) ℝ
    let ev' : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclid N) ℝ →L[ℝ]
        ((Fin k → Fin N) → ℝ) :=
      ContinuousLinearMap.pi fun I =>
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclid N) ℝ fun i => e (I i)
    let ev : Covector (Euclid N) k →ₗ[ℝ] ((Fin k → Fin N) → ℝ) := (ev'.comp ι).toLinearMap
    have hev : LinearMap.ker ev = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro γ hγ
      have h' : γ.toAlternatingMap = (0 : Covector (Euclid N) k).toAlternatingMap := by
        refine e.toBasis.ext_alternating fun I _ => ?_
        have := congrFun hγ I
        simpa [ev, ev', ι, e] using this
      exact ContinuousAlternatingMap.toAlternatingMap_injective h'
    obtain ⟨ℓ, hℓ⟩ := ev.exists_leftInverse_of_injective hev
    have hPℓ : P = fun x => LinearMap.toContinuousLinearMap ℓ (ev' (ι (P x))) := by
      funext x
      exact (LinearMap.congr_fun hℓ (P x)).symm
    rw [hPℓ]
    exact (LinearMap.toContinuousLinearMap ℓ).contDiff.comp (ev'.contDiff.comp h1)
  -- a smooth bump `b`, equal to `1` on a ball `W ⊇ K`
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Euclid N)
  let b : ContDiffBump (0 : Euclid N) := ⟨R, R + 1, hR, by linarith⟩
  have hb1 : ∀ x ∈ ball (0 : Euclid N) R, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hη : (fun x => b x • P x) ∈ TestFormOn (univ : Set (Euclid N)) k :=
    ⟨⟨b.contDiff.smul hP, b.hasCompactSupport.smul_right⟩, subset_univ _⟩
  refine ⟨⟨fun x => b x • P x, hη⟩, ball 0 R, isOpen_ball, hKR, fun x hx => ?_, fun x hx => ?_⟩
  · show b x • P x = P x
    rw [hb1 x hx, one_smul]
  · have heq : (fun x => b x • P x) =ᶠ[𝓝 x] P := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [hb1 y hy, one_smul]
    show extDeriv (fun x => b x • P x) x = _
    rw [heq.extDeriv_eq]
    exact extDeriv_pullback ((hω.differentiable (by simp)).differentiableAt) hF.contDiffAt
      (by simp)
/-- The affine homotopy `h(t, x) = f(x) + t (g(x) − f(x))` from `f` to `g` (Simon 6.2.26, p. 140)
for smooth `f, g : ℝᴺ → ℝᴺ'`, with `(t, x) ∈ ℝ^{N+1}` written `ι(t, x)`, and the derivative facts
used for 2.27: `h` is `C^∞`, `dh_{ι(t,x)} e₀ = g(x) − f(x)`,
`dh_{ι(t,x)} ι(0, v) = df_x v + t (dg_x v − df_x v)` and
`‖dh_{ι(t,x)}‖ ≤ |g(x) − f(x)| + ‖df_x‖ + |t| (‖dg_x‖ + ‖df_x‖)`.  With `tl y = (y₁, …, y_N)` and
`hd y = y₀`, both continuous linear with `‖tl w‖, |hd w| ≤ ‖w‖`, `h = f ∘ tl + hd • (g ∘ tl − f ∘ tl)`
and the chain and product rules give
`dh_y w = df_{tl y} (tl w) + hd y (dg_{tl y} (tl w) − df_{tl y} (tl w)) + hd w (g(tl y) − f(tl y))`. -/
theorem Submission.cmcdt_lpoh_interp_calculus : ∀ (N N' : ℕ) (f g : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g → ∃ h : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ (t : ℝ) (x : Euclid N), h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = f x + t • (g x - f x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = g x - f x) ∧ (∀ (t : ℝ) (x v : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ f x v + t • (fderiv ℝ g x v - fderiv ℝ f x v)) ∧ ∀ (t : ℝ) (x : Euclid N), ‖fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖) := by
  intro N N' f g hf hg
  -- the coordinate maps `tl y = (y₁, …, y_N)` and `hd y = y₀`
  let tlL : Euclid (N + 1) →ₗ[ℝ] Euclid N :=
    { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
      map_add' := by intro y z; rfl
      map_smul' := by intro r y; rfl }
  let tl : Euclid (N + 1) →L[ℝ] Euclid N := LinearMap.toContinuousLinearMap tlL
  let hd : Euclid (N + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (N + 1))
  have htl : ∀ y, tl y = WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) := fun y => rfl
  have hhd : ∀ y : Euclid (N + 1), hd y = WithLp.ofLp y 0 := fun y => rfl
  have htlι : ∀ (t : ℝ) (x : Euclid N), tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x := by
    intro t x; rw [htl]; simp
  have hhdι : ∀ (t : ℝ) (x : Euclid N), hd (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = t := by
    intro t x; rw [hhd]; simp
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  set h : Euclid (N + 1) → Euclid N' := fun y => f (tl y) + hd y • (g (tl y) - f (tl y)) with hh
  -- `dh_y = df_{tl y} ∘ tl + hd y • (dg_{tl y} ∘ tl − df_{tl y} ∘ tl) + hd ⊗ (g(tl y) − f(tl y))`
  have hderiv : ∀ y, HasFDerivAt h ((fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y)))) y := by
    intro y
    have h1 : HasFDerivAt (fun y => f (tl y)) ((fderiv ℝ f (tl y)).comp tl) y :=
      (hfd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    have h2 : HasFDerivAt (fun y => g (tl y)) ((fderiv ℝ g (tl y)).comp tl) y :=
      (hgd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    exact h1.add (hd.hasFDerivAt.smul (h2.sub h1))
  have hfd' : ∀ y, fderiv ℝ h y = (fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y))) := fun y => (hderiv y).fderiv
  have htle : tl (EuclideanSpace.single 0 1) = 0 := by
    rw [htl]; ext i; simp [Fin.tail]
  have hhde : hd (EuclideanSpace.single 0 1 : Euclid (N + 1)) = 1 := by
    rw [hhd]; simp
  have htlJ : ∀ v : Euclid N, tl (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = v := fun v => htlι 0 v
  have hhdJ : ∀ v : Euclid N, hd (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = 0 := fun v => hhdι 0 v
  -- `‖tl w‖ ≤ ‖w‖` and `|hd w| ≤ ‖w‖`
  have htln : ∀ w : Euclid (N + 1), ‖tl w‖ ≤ ‖w‖ := by
    intro w
    rw [htl, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    rw [Fin.sum_univ_succ]
    simp only [Fin.tail]
    have : 0 ≤ ‖WithLp.ofLp w 0‖ ^ 2 := by positivity
    linarith
  have hhdn : ∀ w : Euclid (N + 1), |hd w| ≤ ‖w‖ := by
    intro w
    rw [hhd, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le w 0
  refine ⟨h, (hf.comp tl.contDiff).add (hd.contDiff.smul ((hg.comp tl.contDiff).sub (hf.comp tl.contDiff))),
    ?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [hh, htlι, hhdι]
  · intro t x
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htle, hhde, map_zero, sub_self, smul_zero, zero_add, one_smul,
      htlι]
  · intro t x v
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlJ, hhdJ, zero_smul, add_zero, htlι, hhdι]
  · intro t x
    rw [hfd']
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlι, hhdι]
    have e1 : ‖fderiv ℝ f x (tl w)‖ ≤ ‖fderiv ℝ f x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e2 : ‖fderiv ℝ g x (tl w)‖ ≤ ‖fderiv ℝ g x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e3 : ‖hd w • (g x - f x)‖ ≤ ‖g x - f x‖ * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      gcongr
      exact hhdn w
    calc ‖fderiv ℝ f x (tl w) + (t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w)) + hd w • (g x - f x))‖
        ≤ ‖fderiv ℝ f x (tl w)‖ + (‖t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w))‖ + ‖hd w • (g x - f x)‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ‖fderiv ℝ f x‖ * ‖w‖ + (|t| * (‖fderiv ℝ g x‖ * ‖w‖ + ‖fderiv ℝ f x‖ * ‖w‖) + ‖g x - f x‖ * ‖w‖) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add e2 e1)
      _ = (‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖)) * ‖w‖ := by ring
/-- **Mollification of Lipschitz maps**: a `Λ`-Lipschitz `F : ℝᴺ → ℝᴺ'` has `C^∞`,
`Λ`-Lipschitz approximants `Fⱼ` with `|Fⱼ − F| ≤ Λ/(j + 1)`.  For `σ > 0` normalize the bump `b`
of a `ContDiffBump` at `0` with `rOut = σ` to `ϕ = b/∫b` (`∫b > 0` as `volume (B_σ(0)) > 0`), so
`ϕ ≥ 0`, `∫ϕ = 1` and `support ϕ ⊆ B_σ(0)`, and put `G = ϕ ⋆ F`.  Then `G` is `C^∞`,
`G x − G y = ∫ ϕ(t)(F(x − t) − F(y − t)) dt` gives the constant `Λ`, and `|G − F| ≤ Λσ` since
`|F y − F x| ≤ Λσ` on `B_σ(x)`.  Take `σ = 1/(j + 1)`. -/
theorem Submission.cmcdt_lpo_mollify_lipschitz : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ ∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := by
  intro N N' Λ F hF
  -- For each `σ > 0`: a `C^∞`, `Λ`-Lipschitz `G` with `|G − F| ≤ Λσ`
  have key : ∀ σ : ℝ, 0 < σ → ∃ G : Euclid N → Euclid N', ContDiff ℝ (⊤ : ℕ∞) G ∧
      LipschitzWith Λ G ∧ ∀ x, dist (G x) (F x) ≤ (Λ : ℝ) * σ := by
    intro σ hσ
    -- Step 1: the bump `b`: `C^∞`, `b ≥ 0`, `support b = B_σ(0)`, compact support
    let b : ContDiffBump (0 : Euclid N) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
    have hbi : Integrable (b : Euclid N → ℝ) :=
      b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    -- Step 2: `∫ b > 0`, and the normalized bump `ϕ = (∫ b)⁻¹ b`
    have hIpos : 0 < ∫ t, b t := by
      rw [integral_pos_iff_support_of_nonneg (fun t => b.nonneg) hbi, b.support_eq]
      exact measure_ball_pos _ _ hσ
    set ϕ : Euclid N → ℝ := fun t => (∫ s, b s)⁻¹ * b t with hϕ
    have hϕd : ContDiff ℝ (⊤ : ℕ∞) ϕ := contDiff_const.mul b.contDiff
    have hϕs : HasCompactSupport ϕ := b.hasCompactSupport.mul_left
    have hϕn : ∀ t, 0 ≤ ϕ t := fun t => mul_nonneg (inv_nonneg.2 hIpos.le) b.nonneg
    have hϕ1 : ∫ t, ϕ t = 1 := by
      rw [hϕ, integral_const_mul]
      exact inv_mul_cancel₀ hIpos.ne'
    have hϕb : support ϕ ⊆ ball 0 σ := by
      intro t ht
      have : t ∈ support (b : Euclid N → ℝ) := Function.support_mul_subset_right _ _ ht
      rwa [b.support_eq] at this
    have hϕi : Integrable ϕ := hϕd.continuous.integrable_of_hasCompactSupport hϕs
    -- Step 3: `G = ϕ ⋆ F` is `C^∞`; its integrands `t ↦ ϕ t • F (x - t)` are integrable
    have hFc : Continuous F := hF.continuous
    have hex : ∀ x, Integrable (fun t => ϕ t • F (x - t)) := by
      intro x
      have := (hϕs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hϕd.continuous
        hFc.locallyIntegrable (μ := volume)) x
      simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using this
    refine ⟨convolution ϕ F (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_⟩
    · exact hϕs.contDiff_convolution_left _ hϕd hFc.locallyIntegrable
    -- Step 4: `‖G x − G y‖ ≤ ∫ ϕ(t) Λ‖x − y‖ dt = Λ‖x − y‖`
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
      rw [dist_eq_norm, ← integral_sub (hex x) (hex y)]
      calc ‖∫ t, (ϕ t • F (x - t) - ϕ t • F (y - t))‖
          ≤ ∫ t, ϕ t * ((Λ : ℝ) * dist x y) := by
            refine norm_integral_le_of_norm_le (hϕi.mul_const _) (Eventually.of_forall fun t => ?_)
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hϕn t), ← dist_eq_norm]
            refine mul_le_mul_of_nonneg_left ?_ (hϕn t)
            calc dist (F (x - t)) (F (y - t)) ≤ (Λ : ℝ) * dist (x - t) (y - t) :=
                  hF.dist_le_mul _ _
              _ = (Λ : ℝ) * dist x y := by rw [dist_sub_right]
        _ = (Λ : ℝ) * dist x y := by rw [integral_mul_const, hϕ1, one_mul]
    -- Step 5: `|F y − F x| ≤ Λσ` on `B_σ(x)`, so `|G x − F x| ≤ Λσ` (`ϕ ≥ 0`, `∫ϕ = 1`)
    · intro x
      refine dist_convolution_le (by positivity) hϕb hϕn hϕ1 hFc.aestronglyMeasurable
        fun y hy => ?_
      calc dist (F y) (F x) ≤ (Λ : ℝ) * dist y x := hF.dist_le_mul _ _
        _ ≤ (Λ : ℝ) * σ := mul_le_mul_of_nonneg_left (mem_ball.1 hy).le Λ.coe_nonneg
  -- Step 6: `σ = 1/(j + 1)`
  choose G hG using fun j : ℕ => key (1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨G, fun j => (hG j).1, fun j => (hG j).2.1, fun j x => ?_⟩
  calc dist (G j x) (F x) ≤ (Λ : ℝ) * (1 / ((j : ℝ) + 1)) := (hG j).2.2 x
    _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring

/-- **Smooth approximants of a Lipschitz map with cut-off pull-backs** (the data of Simon 6.2.29):
for a `Λ`-Lipschitz `F : ℝᴺ → ℝ^{N'}` and a compact `K ⊆ ℝᴺ`, the mollified maps `Fⱼ` of
`cmcdt_lpo_mollify_lipschitz` are `C^∞` and `Λ`-Lipschitz, hence `‖DFⱼ‖ ≤ Λ`, and
`|Fⱼ − F| ≤ Λ/(j + 1) → 0` gives `Fⱼ → F` uniformly.  For `ω ∈ 𝒟ᵏ(ℝ^{N'})`,
`cmcdt_lpo_cutoff_pullback` applied to each `Fⱼ` gives `ηⱼ ∈ 𝒟ᵏ(ℝᴺ)` and an open `W ⊇ K` with
`ηⱼ = Fⱼ^#ω` and `dηⱼ = Fⱼ^#(dω)` on `W`. -/
theorem Submission.cmcdt_lpo_pf_approx_data : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (K : Set (Euclid N)), LipschitzWith Λ F → IsCompact K → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ)) ∧ (∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) ∧ TendstoUniformly Fs F atTop ∧ ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid N')) k), ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ ∀ x ∈ W, exteriorDerivative (ηs j : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x) := by
  intro N N' Λ F K hF hK
  obtain ⟨Fs, hFs, hLip, hdist⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ F hF
  refine ⟨Fs, hFs, hLip, fun j x => norm_fderiv_le_of_lipschitz ℝ (hLip j), hdist, ?_, ?_⟩
  -- `Λ/(j + 1) → 0`, so `Fⱼ → F` uniformly
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h0 : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
      rw [mul_zero] at this
      exact this.congr (fun j => mul_one_div _ _)
    filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_comm]
    exact lt_of_le_of_lt (hdist j x) hj
  -- the cut-off pull-backs `ηⱼ`, chosen for each `j`
  · intro k ω
    choose ηs W hW using fun j =>
      Submission.cmcdt_lpo_cutoff_pullback N N' k (Fs j) ω K (hFs j) hK
    exact ⟨ηs, fun j => ⟨W j, hW j⟩⟩
/-- **Test forms and their exterior derivatives are bounded** in the Euclidean coefficient norm
`|α|` of Simon (6.1.15), as used for the Lipschitz push-forward (Simon Ch. 6, 2.28–2.29).  For a
test form `θ ∈ 𝒟ᵐ(ℝᴺ)`, `y ↦ |θ(y)|` is the square root of a finite sum of squares of the
continuous evaluations `y ↦ θ(y)(e_{I 1}, …, e_{I m})`, hence continuous, and has compact support
since `|0| = 0`; so it is bounded.  Apply this to `ω` and to `dω`, a test form by
`exteriorDerivative_isTestForm`. -/
theorem Submission.cmcdt_lpo_pf_form_bounds : ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid N)) k), (∃ a : ℝ, ∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) y) ≤ a) ∧ ∃ b : ℝ, ∀ y, covectorEuclideanNorm (exteriorDerivative (ω : DifferentialForm (Euclid N) k) y) ≤ b := by
  intro N k ω
  -- a test form has bounded Euclidean coefficient norm
  have hbd : ∀ (m : ℕ) (θ : DifferentialForm (Euclid N) m), IsTestForm θ →
      ∃ a : ℝ, ∀ y, covectorEuclideanNorm (θ y) ≤ a := by
    intro m θ hθ
    have hθc : Continuous θ := hθ.1.continuous
    have hcont : Continuous (covectorEuclideanNorm ∘ θ) := by
      show Continuous fun y => covectorEuclideanNorm (θ y)
      unfold covectorEuclideanNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => (hθc.eval_const _).pow 2) (fun _ => continuous_const)
    have hsupp : HasCompactSupport (covectorEuclideanNorm ∘ θ) :=
      HasCompactSupport.comp_left (g := covectorEuclideanNorm) hθ.2 (covectorEuclideanNorm_zero N m)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
    refine ⟨C, fun y => (le_abs_self _).trans ?_⟩
    have := hC y
    rwa [Real.norm_eq_abs] at this
  exact ⟨hbd k _ ω.property.1, hbd (k + 1) _ (exteriorDerivative_isTestForm ω.property.1)⟩
/-- Compactly supported normal currents in `ℝᴺ` are closed under differences and boundaries.
(a) If `X, Y ∈ 𝒟ₖ(ℝᴺ)` have compact support, finite mass and finite boundary mass, then
`spt(X − Y) ⊆ spt X ∪ spt Y` is compact and `X − Y` has finite mass and boundary mass.
(b) If `X ∈ 𝒟ₖ₊₁(ℝᴺ)` has compact support, then `spt ∂X ⊆ spt X` is compact and `M(∂∂X) = 0`.
Mass is subadditive on differences since `−ω` is admissible with `ω`; supports are closed;
`X − Y` vanishes where `X` and `Y` both vanish; `spt dω ⊆ spt ω`; and `∂∂ = 0`. -/
theorem Submission.cmcdt_lpo_pf_normal_closure : (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → (X - Y).support ⊆ X.support ∪ Y.support ∧ IsCompact (X - Y).support ∧ (X - Y).mass < ∞ ∧ boundaryMassOn (X - Y) univ < ∞) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.boundary.support ⊆ X.support ∧ IsCompact X.boundary.support ∧ boundaryMassOn X.boundary univ = 0 := by
  -- `M(A − B) ≤ M(A) + M(B)`: `(A − B)(ω) = A(ω) + B(−ω)` and `−ω` is admissible with `ω`
  have key : ∀ (N m : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid N)) m),
      (A - B).massOn univ ≤ A.massOn univ + B.massOn univ := by
    intro N m A B
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    have hneg : -ω ∈ massAdmissibleOn univ m univ :=
      ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
    have hval : (A - B) ω = A ω + B (-ω) := by
      show A ω - B ω = A ω + B (-ω)
      have h := B.toCurrent.map_neg ω
      linarith
    dsimp only
    rw [hval]
    exact ENNReal.ofReal_add_le.trans (add_le_add (A.le_massOn hω) (B.le_massOn hneg))
  -- supports in `ℝᴺ` are closed: `spt T` is the complement of the open zero region
  have hclosed : ∀ (N m : ℕ) (A : GeometricCurrentOn (univ : Set (Euclid N)) m),
      IsClosed A.support := by
    intro N m A
    rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
    exact A.isOpen_zeroRegion.isClosed_compl
  refine ⟨?_, ?_⟩
  · intro N k X Y hX1 hX2 hX3 hY1 hY2 hY3
    -- `X − Y` vanishes on `W₁ ∩ W₂` when `X` vanishes on `W₁` and `Y` on `W₂`
    have hsupp : (X - Y).support ⊆ X.support ∪ Y.support := by
      rintro x ⟨-, hx⟩
      by_contra hxy
      simp only [mem_union, not_or] at hxy
      obtain ⟨W₁, ⟨hW₁o, hW₁c, -, hW₁v⟩, hxW₁⟩ : x ∈ X.zeroRegion :=
        not_not.1 fun h => hxy.1 ⟨mem_univ x, h⟩
      obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hxW₂⟩ : x ∈ Y.zeroRegion :=
        not_not.1 fun h => hxy.2 ⟨mem_univ x, h⟩
      refine hx ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o, ?_, subset_univ _, fun ω hω => ?_⟩, hxW₁, hxW₂⟩
      · exact hW₁c.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
      · show X ω - Y ω = 0
        rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
    refine ⟨hsupp, (hX1.union hY1).of_isClosed_subset (hclosed N k _) hsupp,
      (key N k X Y).trans_lt (ENNReal.add_lt_top.2 ⟨hX2, hY2⟩), ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k' =>
      -- `∂(X − Y) = ∂X − ∂Y`
      have hb : (X - Y).boundary = X.boundary - Y.boundary := by
        ext ω
        rfl
      show (X - Y).boundary.massOn univ < ∞
      rw [hb]
      exact (key N k' _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hX3, hY3⟩)
  · intro N k X hX
    -- `∂X` vanishes wherever `X` does, since `spt dω ⊆ spt ω`
    have hsupp : X.boundary.support ⊆ X.support := by
      rintro x ⟨-, hx⟩
      refine ⟨mem_univ x, fun hxX => hx ?_⟩
      obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxX
      exact ⟨W, ⟨hWo, hWc, hWU, fun ω hω =>
        hWv _ ((tsupport_exteriorDerivative_subset _).trans hω)⟩, hxW⟩
    refine ⟨hsupp, hX.of_isClosed_subset (hclosed N k _) hsupp, ?_⟩
    cases k with
    | zero => rfl
    | succ k' =>
      -- `∂∂X = 0`, and the zero current has zero mass
      show X.boundary.boundary.massOn univ = 0
      rw [X.boundary_boundary]
      refine le_antisymm (sSup_le ?_) bot_le
      rintro r ⟨ω, -, rfl⟩
      simp
/-- **Simon Ch. 6, 2.7–2.8 with 2.12** (mass–support bound).  Let `X ∈ 𝒟ₖ(ℝᴺ)` have
`M(X) < ∞` and let `|ψ(x)| ≤ c` on `spt X`.  The representation `X(ω) = ∫ ⟨ω, ξ⟩ dμ` with
`M_W(X) = μ(W)` (`W` open) and `|ξ| ≤ 1` makes `μ` finite with `μ(ℝᴺ) = M(X)`.  `X` kills every
test form supported in the open zero region `ℝᴺ \ spt X`, so `μ` gives it measure zero; hence
`|ξ(x)(ψ(x))| ≤ c` for `μ`-a.e. `x`, and `|X(ψ)| ≤ c μ(ℝᴺ) = c M(X)`. -/
theorem Submission.cmcdt_lpo_tk_mass_support_bound : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal := by
  intro hVO hREP N k X ψ c hX hψ
  -- the representation of `X`: every local mass is at most `M(X) < ∞`
  obtain ⟨μ, ξ, -, -, hμ, -, hξ, hrep, -⟩ := hREP N k univ X isOpen_univ
    fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX
  -- `μ(ℝᴺ) = M(X)`, so `μ` is finite
  have hμuniv : μ univ = X.mass := (hμ univ isOpen_univ).symm
  have : IsFiniteMeasure μ := ⟨hμuniv ▸ hX⟩
  -- the zero region is `μ`-null: `X` kills every admissible form supported in it
  have hZ : μ X.zeroRegion = 0 := by
    rw [← hμ _ X.isOpen_zeroRegion]
    refine le_antisymm (sSup_le ?_) bot_le
    rintro r ⟨ω, hω, rfl⟩
    have hω0 : X ω = 0 := hVO N k univ X ω <| Set.disjoint_left.2 fun x hx hxS => hxS.2 (hω.1 hx)
    simp [hω0]
  -- hence `μ`-a.e. `x` lies in `spt X`, where `|ξ(x)(ψ(x))| ≤ |ψ(x)| ≤ c`
  have hbound : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
    have hae : ∀ᵐ x ∂μ, x ∈ X.support :=
      measure_mono_null (fun x hx => by_contra fun hxZ => hx ⟨mem_univ x, hxZ⟩) hZ
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    exact (hξ x _).trans (hψ x hx)
  rw [hrep ψ, ← Real.norm_eq_abs, ← hμuniv, ← measureReal_def]
  exact norm_integral_le_of_norm_le_const hbound
/-- **Simon 6.2.1, 6.2.4** (bounded functionals are currents): a linear functional `T₀` on
`𝒟ᵏ(ℝᴺ)` with `|T₀(ω)| ≤ C c` whenever `|ω(x)| ≤ c` for all `x` (Euclidean coefficient norm) is
a current `T ∈ 𝒟ₖ(ℝᴺ)` with `M(T) ≤ C`.  Each coefficient of a covector `α` is its value on unit
vectors, so `|α| ≤ √(Nᵏ) ‖α‖`; hence `ωⱼ → 0` uniformly (supports in a fixed compact set) forces
`T₀(ωⱼ) → 0`.  The zero form gives `C ≥ 0`, and admissible forms give `T(ω) ≤ C`. -/
theorem Submission.cmcdt_lpo_tk_bounded_current : ∀ (N k : ℕ) (T₀ : TestFormOn (univ : Set (Euclid N)) k →ₗ[ℝ] ℝ) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T₀ ω| ≤ C * c) → ∃ T : GeometricCurrentOn (univ : Set (Euclid N)) k, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal C := by
  intro N k T₀ C hT
  -- `|α| ≤ √(Nᵏ) ‖α‖`: each of the `Nᵏ` summands is at most `‖α‖²`
  have hA : 0 ≤ Real.sqrt (Fintype.card (Fin k → Fin N)) := Real.sqrt_nonneg _
  have hcoef : ∀ α : Covector (Euclid N) k,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin k → Fin N)) * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    calc _ ≤ Real.sqrt (∑ _I : Fin k → Fin N, ‖α‖ ^ 2) := by
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h2 := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin N) ℝ (I i))
            simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
              Real.norm_eq_abs] at h2
            exact sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
          · positivity
      _ = Real.sqrt (Fintype.card (Fin k → Fin N)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- the zero form gives `0 ≤ C`
  have hC : 0 ≤ C := by
    have h := hT 0 1 (fun x => by simp)
    simpa using h
  -- continuity: only the uniform convergence of the forms themselves (`m = 0`) is needed
  have hcont : ∀ (omegaSeq : ℕ → TestFormOn (univ : Set (Euclid N)) k),
      TestFormOnConverges omegaSeq 0 → Tendsto (fun j ↦ T₀ (omegaSeq j)) atTop (𝓝 0) := by
    intro omegaSeq hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
    have hsmall : ∀ δ > 0, ∀ᶠ j in atTop,
        ∀ x, ‖(omegaSeq j : DifferentialForm (Euclid N) k) x‖ ≤ δ := by
      intro δ hδ
      filter_upwards [h0 δ hδ] with j hj
      intro x
      by_cases hx : x ∈ K
      · have hz : iteratedFDeriv ℝ 0
            ((0 : TestFormOn (univ : Set (Euclid N)) k) : DifferentialForm (Euclid N) k) x = 0 := by
          rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
          simp
        have h1 := hj x hx
        rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h1
        exact h1.le
      · rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsupp j hx')), norm_zero]
        exact hδ.le
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCA : 0 ≤ C * Real.sqrt (Fintype.card (Fin k → Fin N)) := mul_nonneg hC hA
    have hδ : 0 < ε / (C * Real.sqrt (Fintype.card (Fin k → Fin N)) + 1) :=
      div_pos hε (by linarith)
    filter_upwards [hsmall _ hδ] with j hj
    have hb := hT (omegaSeq j) _
      (fun x => (hcoef _).trans (mul_le_mul_of_nonneg_left (hj x) hA))
    rw [Real.dist_eq, sub_zero]
    refine hb.trans_lt ?_
    rw [← mul_assoc, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  -- the current, and its mass bound from admissible forms
  refine ⟨⟨T₀, hcont⟩, fun ω => rfl, ?_⟩
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  have h := hT ω 1 hω.2
  rw [mul_one] at h
  exact (le_abs_self _).trans h
/-- **Simon 6.2.3 and 6.2.11**: `spt ∂X ⊆ spt X` for `X ∈ 𝒟_{k+1}(ℝᴺ)`.  If `x ∉ spt X`, then
`x` lies in an open `W` with compact closure on which `X` vanishes.  For a test `k`-form `ω` with
`spt ω ⊆ W`, `∂X(ω) = X(dω) = 0`, as `spt dω ⊆ spt ω ⊆ W`.  So `W` is also a zero region of `∂X`,
and `x ∉ spt ∂X`. -/
theorem Submission.cmcdt_lpo_tk_boundary_support_subset : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), X.boundary.support ⊆ X.support := by
  intro N k X x hx
  -- `x ∈ spt ∂X = univ \ (∂X).zeroRegion`; it remains to show `x ∉ X.zeroRegion`
  refine ⟨hx.1, ?_⟩
  -- step 1: otherwise `x` lies in a zero region `W` of `X`
  rintro ⟨W, ⟨hWo, hWc, hWU, hXW⟩, hxW⟩
  -- steps 2–3: `W` is a zero region of `∂X` as well, so `x ∈ (∂X).zeroRegion`
  refine hx.2 ⟨W, ⟨hWo, hWc, hWU, fun ω hω => ?_⟩, hxW⟩
  -- `∂X(ω) = X(dω)` and `spt dω ⊆ spt ω ⊆ W`
  rw [GeometricCurrentOn.boundary_apply]
  exact hXW (exteriorDerivativeTestOn univ k ω)
    ((tsupport_exteriorDerivative_subset (ω : DifferentialForm (Euclid N) k)).trans hω)
/-- **Locality of a current** (Simon 6.2.11, chapter-06.txt lines 296–303): if every current
`S ∈ 𝒟ₙ(U)` kills the test forms whose support misses `spt S`, then `X ∈ 𝒟ₖ(ℝᴺ)` takes the same
value on test forms `η`, `η'` that agree on an open set `W ⊇ spt X`.  The difference
`ψ = η − η'` vanishes on `W`, so `tsupport ψ` lies in the closed set `Wᶜ`, which misses
`spt X ⊆ W`; hence `X(η) − X(η') = X(ψ) = 0`. -/
theorem Submission.cmcdt_lpo_tk_locality : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η' := by
  intro hVO N k X η η' W hW hXW hηη'
  -- Step 1: `ψ = η − η'` vanishes on `W`, so `tsupport ψ` lies in the closed set `Wᶜ`.
  have hψ : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
      DifferentialForm (Euclid N) k) ⊆ Wᶜ := by
    refine closure_minimal (fun x hx hxW => hx ?_) hW.isClosed_compl
    rw [Submodule.coe_sub, Pi.sub_apply, hηη' x hxW, sub_self]
  -- Step 2: `tsupport ψ ⊆ Wᶜ` misses `spt X ⊆ W`, so `X(ψ) = 0` by the vanishing hypothesis.
  have h0 : X (η - η') = 0 := hVO N k univ X (η - η') (disjoint_compl_left.mono hψ hXW)
  -- Step 3: `X(ψ) = X(η) − X(η')` by linearity of `X`.
  rw [map_sub X.toCurrent] at h0
  exact sub_eq_zero.mp h0
/-- **Smooth approximation of a Lipschitz straight-line homotopy**: for `Λ`-Lipschitz
`F, G : ℝᴺ → ℝᴺ'` and `H(t, x) = F x + t(G x − F x)` on `[0, 1] × K` (`K` compact), take the
mollifications `Fⱼ, Gⱼ` of `F, G` (`|Fⱼ − F|, |Gⱼ − G| ≤ Λ/(j + 1)`, so `|DFⱼ|, |DGⱼ| ≤ Λ`) and
let `Hⱼ` be the `C^∞` interpolation `Hⱼ(t, x) = Fⱼ x + t(Gⱼ x − Fⱼ x)`.  Then
`|∂ₜHⱼ| = |Gⱼ − Fⱼ| ≤ |F − G| + 2Λ/(j + 1)`, `DHⱼ(Jv) = (1 − t) DFⱼ v + t DGⱼ v` for
`t ∈ [0, 1]`, `|DHⱼ| ≤ sup_K |F − G| + 5Λ` on `[0, 1] × K`, and `Hⱼ → H` uniformly on
`[0, 1] × K` as `H − Hⱼ = (1 − t)(F − Fⱼ) + t(G − Gⱼ)` there. -/
theorem Submission.cmcdt_lpoh_smooth_approx : ∀ (N N' : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (Fs Gs : ℕ → Euclid N → Euclid N') (Hs : ℕ → Euclid (N + 1) → Euclid N') (Λ' : ℝ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Gs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Hs j)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ)) ∧ TendstoUniformly Fs F atTop ∧ TendstoUniformly Gs G atTop ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) = Gs j x) ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) = Fs j x) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Gs j) x v) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Fs j) x v) ∧ (∀ (j : ℕ) (t : ℝ) (x : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ (x v : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ Λ') ∧ TendstoUniformlyOn Hs H atTop {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
  intro N N' Λ F G H K hF hG hK hHK
  -- Step 1: mollify `F, G`; for each `j` interpolate `Fⱼ, Gⱼ` by the `C^∞` map `Hⱼ`
  obtain ⟨Fs, hFs, hFL, hFd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ F hF
  obtain ⟨Gs, hGs, hGL, hGd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ G hG
  choose Hs hHs hHι hHe hHJ hHn using
    fun j => Submission.cmcdt_lpoh_interp_calculus N N' (Fs j) (Gs j) (hFs j) (hGs j)
  -- `M` bounds `|F − G|` on the compact `K`
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ K, dist (F x) (G x) ≤ M := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      ((hF.continuous.dist hG.continuous).continuousOn)
    exact ⟨M, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x hx)⟩
  -- Step 2: `Λ`-Lipschitz maps have `|DFⱼ|, |DGⱼ| ≤ Λ`
  have hDF : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hFL j)
  have hDG : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hGL j)
  -- Step 3: `Λ/(j + 1) → 0`, so a uniform error `Λ/(j + 1)` gives uniform convergence
  have hsmall : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Λ : ℝ)
    rw [mul_zero] at h
    refine h.congr (fun j => ?_)
    rw [mul_one_div]
  have hunif : ∀ (Es : ℕ → Euclid N → Euclid N') (E : Euclid N → Euclid N'),
      (∀ (j : ℕ) (x : Euclid N), dist (Es j x) (E x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) →
      TendstoUniformly Es E atTop := by
    intro Es E hE
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_comm]
    exact (hE j x).trans_lt hj
  -- Step 6: `|Gⱼ − Fⱼ| ≤ |F − G| + 2Λ/(j + 1)`
  have hGF : ∀ (j : ℕ) (x : Euclid N),
      ‖Gs j x - Fs j x‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by
    intro j x
    rw [← dist_eq_norm]
    calc dist (Gs j x) (Fs j x) ≤ dist (Gs j x) (G x) + dist (G x) (F x) + dist (F x) (Fs j x) :=
          dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) / ((j : ℝ) + 1) + dist (F x) (G x) + (Λ : ℝ) / ((j : ℝ) + 1) := by
          gcongr
          · exact hGd j x
          · rw [dist_comm]
          · rw [dist_comm]; exact hFd j x
      _ = dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by ring
  refine ⟨Fs, Gs, Hs, M + 5 * (Λ : ℝ), hFs, hGs, hHs, hDF, hDG, hunif Fs F hFd, hunif Gs G hGd,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Steps 4, 5: end values and end derivatives at `t = 1, 0`
  · intro j x; rw [hHι]; simp
  · intro j x; rw [hHι]; simp
  · intro j x v; rw [hHJ]; simp
  · intro j x v; rw [hHJ]; simp
  -- Step 7: `DHⱼ e₀ = Gⱼ − Fⱼ`
  · intro j t x; rw [hHe]; exact hGF j x
  -- Step 8: `DHⱼ(Jv) = (1 − t) DFⱼ v + t DGⱼ v` has norm `≤ Λ|v|` for `t ∈ [0, 1]`
  · intro j t ht x v
    rw [hHJ]
    have h1 : fderiv ℝ (Fs j) x v + t • (fderiv ℝ (Gs j) x v - fderiv ℝ (Fs j) x v) =
        (1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have hF' : ‖fderiv ℝ (Fs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDF j x)
    have hG' : ‖fderiv ℝ (Gs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDG j x)
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v‖
        ≤ ‖(1 - t) • fderiv ℝ (Fs j) x v‖ + ‖t • fderiv ℝ (Gs j) x v‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ (Fs j) x v‖ + t * ‖fderiv ℝ (Gs j) x v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) * ‖v‖) + t * ((Λ : ℝ) * ‖v‖) := by gcongr
      _ = (Λ : ℝ) * ‖v‖ := by ring
  -- Step 9: `|DHⱼ| ≤ (M + 2Λ) + Λ + 1 · (Λ + Λ) = M + 5Λ` on `[0, 1] × K`
  · intro j t ht x hx
    refine (hHn j t x).trans ?_
    have h2 : 2 * (Λ : ℝ) / ((j : ℝ) + 1) ≤ 2 * (Λ : ℝ) :=
      div_le_self (by positivity) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    have habs : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc ‖Gs j x - Fs j x‖ + ‖fderiv ℝ (Fs j) x‖ + |t| * (‖fderiv ℝ (Gs j) x‖ + ‖fderiv ℝ (Fs j) x‖)
        ≤ (M + 2 * (Λ : ℝ)) + (Λ : ℝ) + 1 * ((Λ : ℝ) + (Λ : ℝ)) := by
          gcongr
          · exact (hGF j x).trans (by linarith [hM x hx])
          · exact hDF j x
          · exact hDG j x
          · exact hDF j x
      _ = M + 5 * (Λ : ℝ) := by ring
  -- Step 10: `H − Hⱼ = (1 − t)(F − Fⱼ) + t(G − Gⱼ)` has norm `≤ Λ/(j + 1)` on `[0, 1] × K`
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj y hy
    obtain ⟨t, ht, x, hx, rfl⟩ := hy
    rw [hHK x hx t ht, hHι, dist_eq_norm]
    have h1 : F x + t • (G x - F x) - (Fs j x + t • (Gs j x - Fs j x)) =
        (1 - t) • (F x - Fs j x) + t • (G x - Gs j x) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • (F x - Fs j x) + t • (G x - Gs j x)‖
        ≤ ‖(1 - t) • (F x - Fs j x)‖ + ‖t • (G x - Gs j x)‖ := norm_add_le _ _
      _ = (1 - t) * ‖F x - Fs j x‖ + t * ‖G x - Gs j x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) / ((j : ℝ) + 1)) + t * ((Λ : ℝ) / ((j : ℝ) + 1)) := by
          gcongr
          · rw [← dist_eq_norm, dist_comm]; exact hFd j x
          · rw [← dist_eq_norm, dist_comm]; exact hGd j x
      _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring
      _ < ε := hj
/-- **Covector bound for the `e₀`-slice of a pulled-back covector.**  Given the bounds
(L1) `|β ∘ A| ≤ ‖A‖ᵏ |β|` and (L2) `|β(v, ·)| ≤ ‖v‖ |β|` for the Euclidean coefficient norm
`|·| = covectorEuclideanNorm`, let `φ(v₁, …, v_k) = (D^#γ)(e₀, Jv₁, …, Jv_k)` with
`J v = (0, v)`, `‖D e₀‖ ≤ a` and `‖D (J v)‖ ≤ b ‖v‖`.  Then `φ = γ(D e₀, ·) ∘ (D ∘ J)`, so
`|φ| ≤ ‖D ∘ J‖ᵏ ‖D e₀‖ |γ| ≤ bᵏ a |γ|`. -/
theorem Submission.cmcdt_lpoh_phi_bound : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (γ : Covector (Euclid N') (k + 1)) (D : Euclid (N + 1) →L[ℝ] Euclid N') (φ : Covector (Euclid N) k) (a b : ℝ), 0 ≤ b → ‖D (EuclideanSpace.single 0 1)‖ ≤ a → (∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ b * ‖v‖) → (∀ v : Fin k → Euclid N, φ v = (γ.compContinuousLinearMap D) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → covectorEuclideanNorm φ ≤ b ^ k * a * covectorEuclideanNorm γ := by
  intro hL1 hL2 N N' k γ D φ a b hb hDe hDJ hφ
  /- Step 1: `J v = (0, v)` is linear (check coordinatewise), hence continuous linear. -/
  let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro r v
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jl
  /- Step 2: `φ = γ(D e₀, ·) ∘ (D ∘ J)`, since `D ∘ (e₀, Jv) = (D e₀, D (J v))`. -/
  have hφeq : φ = (γ.curryLeft (D (EuclideanSpace.single 0 1))).compContinuousLinearMap
      (D.comp J) := by
    ext v
    rw [hφ v]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousLinearMap.coe_comp]
    congr 1
    rw [Fin.comp_cons]
    rfl
  /- Step 3: `‖D ∘ J‖ ≤ b`. -/
  have hA : ‖D.comp J‖ ≤ b := ContinuousLinearMap.opNorm_le_bound _ hb hDJ
  /- Step 4: (L1) for `D ∘ J`, then (L2) for `D e₀`. -/
  rw [hφeq]
  calc covectorEuclideanNorm ((γ.curryLeft (D (EuclideanSpace.single 0 1))).compContinuousLinearMap
        (D.comp J))
      ≤ ‖D.comp J‖ ^ k * covectorEuclideanNorm (γ.curryLeft (D (EuclideanSpace.single 0 1))) :=
        hL1 N N' k (D.comp J) _
    _ ≤ b ^ k * (‖D (EuclideanSpace.single 0 1)‖ * covectorEuclideanNorm γ) := by
        gcongr
        · exact covectorEuclideanNorm_nonneg _
        · exact hL2 N' k _ γ
    _ ≤ b ^ k * (a * covectorEuclideanNorm γ) := by
        gcongr
        exact covectorEuclideanNorm_nonneg γ
    _ = b ^ k * a * covectorEuclideanNorm γ := by ring
/-- **Current toolkit** (Simon 6.2.1–2.12), for currents in `ℝᴺ`.  Assume (VO): a current
kills every test form supported off its support; and (REP): a current of locally finite mass
is integration against a measure `μ` with `M_W(T) = μ(W)` and a pointwise bounded `ξ`.  Then:
(MSB) `|X(ψ)| ≤ c M(X)` if `M(X) < ∞` and `|ψ| ≤ c` on `spt X`; (BC) a linear `T₀` with
`|T₀(ω)| ≤ C c` whenever `|ω| ≤ c` is a current of mass `≤ C`; (SB) `spt ∂X ⊆ spt X`;
(LOC) `X(η) = X(η')` if `η = η'` on an open set containing `spt X`.  The four parts are
independent: (MSB) uses (VO) and (REP), (LOC) uses only (VO), and (BC), (SB) use neither. -/
theorem Submission.cmcdt_lpo_current_toolkit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) ∧ (∀ (N k : ℕ) (T₀ : TestFormOn (univ : Set (Euclid N)) k →ₗ[ℝ] ℝ) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T₀ ω| ≤ C * c) → ∃ T : GeometricCurrentOn (univ : Set (Euclid N)) k, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal C) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), X.boundary.support ⊆ X.support) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η' :=
  fun hVO hREP => ⟨Submission.cmcdt_lpo_tk_mass_support_bound hVO hREP,
    Submission.cmcdt_lpo_tk_bounded_current, Submission.cmcdt_lpo_tk_boundary_support_subset,
    Submission.cmcdt_lpo_tk_locality hVO⟩

/-- Simon 6.2.25–6.2.27 for smooth maps (the estimate in the proof of 6.2.28): if `F, G` are
`C^∞`, `‖DF‖, ‖DG‖ ≤ Λ` and `|F − G| ≤ δ` on `spt X`, then
`|X(G^#ω) − X(F^#ω)| ≤ δ (Λᵏ M(X) sup |dω| + Λ^{k−1} M(∂X) sup |ω|)`.  The affine homotopy
`H(t, x) = F(x) + t (G(x) − F(x))` is cut off near `[0, 1] × spt X`, giving `β = H^#ω` there.  The
cylinder homotopy formula gives `X(η_G) − X(η_F) = X(S_{dβ}) + ∂X(S_β)`, and over `spt X` the
slice integrands are `dω(H)(G − F, A_t ·)` and `ω(H)(G − F, A_t ·)`, `A_t = DF + t (DG − DF)`,
`‖A_t‖ ≤ Λ`. -/
theorem Submission.cmcdt_lpo_smooth_homotopy_estimate : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (N N' k : ℕ) (Λ δ a b : ℝ) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηF ηG : TestFormOn (univ : Set (Euclid N)) k), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ‖fderiv ℝ F x‖ ≤ Λ ∧ ‖fderiv ℝ G x‖ ≤ Λ) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) y) ≤ a) → (∀ y, covectorEuclideanNorm (exteriorDerivative (ω : DifferentialForm (Euclid N') k) y) ≤ b) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → |X ηG - X ηF| ≤ δ * (Λ ^ k * X.mass.toReal * b + Λ ^ (k - 1) * (boundaryMassOn X univ).toReal * a) := by
  intro hVO hREP hLB N N' k Λ δ a b F G X ω ηF ηG hF hG hXc hXm hXbm hD hFG ha hb hηF hηG
  obtain ⟨hMSB, -, hSB, hLOC⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  obtain ⟨hL1, hL2, -⟩ := hLB
  obtain ⟨WF, hWFo, hXWF, hWF⟩ := hηF
  obtain ⟨WG, hWGo, hXWG, hWG⟩ := hηG
  obtain ⟨H, hH, hHval, hHe, hHJ⟩ := Submission.cmcdt_lpo_she_affine_homotopy N N' F G hF hG
  -- cut off `H^#ω` near the compact set `ι([0, 1] × spt X)`, `ι(t, x) = (t, x)`
  have hι : Continuous fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1)) := by
    fun_prop
  obtain ⟨β, W', hW'o, hKW', hβ, hdβ⟩ := Submission.cmcdt_lpo_cutoff_pullback (N + 1) N' k H ω
    ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
      (Icc (0 : ℝ) 1 ×ˢ X.support)) hH ((isCompact_Icc.prod hXc).image hι)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support,
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ W' :=
    fun t ht x hx => hKW' ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  -- `DH(ι(t, x))` maps `e₀` to `G x − F x` and `ι(0, v)` to `A_t v`, `A_t = DF + t (DG − DF)`
  have hDH : ∀ (m : ℕ) (t : ℝ) (x : Euclid N) (v : Fin m → Euclid N),
      ⇑(fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) ∘
          (Fin.cons (EuclideanSpace.single 0 1)
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :
            Fin (m + 1) → Euclid (N + 1)) =
        Fin.cons (G x - F x) fun i => (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) (v i) := by
    intro m t x v
    rw [Fin.comp_cons, hHe]
    congr 1
    funext i
    simp only [Function.comp_apply, hHJ, add_apply, smul_apply, sub_apply]
  have hA : ∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ ≤ Λ := by
    intro x hx t ht
    obtain ⟨hDF, hDG⟩ := hD x hx
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht.2
    calc ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖
        = ‖(1 - t) • fderiv ℝ F x + t • fderiv ℝ G x‖ := by congr 1; module
      _ ≤ ‖(1 - t) • fderiv ℝ F x‖ + ‖t • fderiv ℝ G x‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ F x‖ + t * ‖fderiv ℝ G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t, Real.norm_of_nonneg ht.1]
      _ ≤ (1 - t) * Λ + t * Λ :=
        add_le_add (mul_le_mul_of_nonneg_left hDF h1t) (mul_le_mul_of_nonneg_left hDG ht.1)
      _ = Λ := by ring
  -- over `x ∈ spt X`, the slice of a form `σ = H^#γ` (near `ι([0, 1] × spt X)`) has norm
  -- `≤ Λᵐ δ sup |γ|` (Simon 6.2.27)
  have hslice : ∀ (m : ℕ) (σ : DifferentialForm (Euclid (N + 1)) (m + 1))
      (γ : DifferentialForm (Euclid N') (m + 1)) (c : ℝ) (α : DifferentialForm (Euclid N) m),
      Continuous σ → (∀ y ∈ W', σ y = (γ (H y)).compContinuousLinearMap (fderiv ℝ H y)) →
      (∀ y, covectorEuclideanNorm (γ y) ≤ c) →
      (∀ (x : Euclid N) (v : Fin m → Euclid N), α x v = ∫ t in (0 : ℝ)..1,
        σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
          (Fin.cons (EuclideanSpace.single 0 1)
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) →
      ∀ x ∈ X.support, covectorEuclideanNorm (α x) ≤ Λ ^ m * δ * c := by
    intro m σ γ c α hσ hσW hγ hα x hx
    refine Submission.cmcdt_lpo_she_slice_bound hL1 hL2 N N' m σ x (α x) Λ δ c hσ (hα x)
      fun t ht => ⟨γ (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))), G x - F x,
        fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x), hA x hx t ht, ?_, hγ _, fun v => ?_⟩
    · rw [← dist_eq_norm, dist_comm]
      exact hFG x hx
    · rw [hσW _ (hmem t ht x hx), ContinuousAlternatingMap.compContinuousLinearMap_apply, hDH]
  -- the end slices of `β` are `G^#ω = η_G` and `F^#ω = η_F` near `spt X`
  obtain ⟨V, hVo, hXV, hV⟩ : ∃ V : Set (Euclid N), IsOpen V ∧ X.support ⊆ V ∧
      ∀ x ∈ V, ∀ v : Fin k → Euclid N,
        (ηG : DifferentialForm (Euclid N) k) x v = (β : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) ∧
          (ηF : DifferentialForm (Euclid N) k) x v = (β : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
    have hs : ∀ s : ℝ, Continuous fun x : Euclid N =>
        (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)) := fun s => by fun_prop
    refine ⟨{x | (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)) : Euclid (N + 1)) ∈ W'} ∩
        {x | (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x)) : Euclid (N + 1)) ∈ W'} ∩ WF ∩ WG,
      (((hW'o.preimage (hs 0)).inter (hW'o.preimage (hs 1))).inter hWFo).inter hWGo,
      fun x hx => ⟨⟨⟨hmem 0 ⟨le_rfl, zero_le_one⟩ x hx, hmem 1 ⟨zero_le_one, le_rfl⟩ x hx⟩,
        hXWF hx⟩, hXWG hx⟩, ?_⟩
    rintro x ⟨⟨⟨h0, h1⟩, hxF⟩, hxG⟩ v
    constructor
    · rw [hWG x hxG, hβ _ h1]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hHval,
        one_smul, add_sub_cancel, hHJ]
    · rw [hWF x hxF, hβ _ h0]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hHval,
        zero_smul, add_zero, hHJ]
  cases k with
  | zero =>
    obtain ⟨η, hηf, hid⟩ :=
      (Submission.cmcdt_lpo_she_cylinder_homotopy hLOC).2 N X β ηF ηG V hVo hXV hV
    have hη : |X η| ≤ Λ ^ 0 * δ * b * X.mass.toReal :=
      hMSB N 0 X η _ hXm (hslice 0 (exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0))
        (exteriorDerivative (ω : DifferentialForm (Euclid N') 0)) b
        (η : DifferentialForm (Euclid N) 0)
        (ContDiff.continuous (exteriorDerivative_isTestForm β.2.1).1) hdβ hb hηf)
    have hbm : boundaryMassOn X univ = 0 := rfl
    rw [hid, hbm, ENNReal.toReal_zero]
    calc |X η| ≤ Λ ^ 0 * δ * b * X.mass.toReal := hη
      _ = δ * (Λ ^ 0 * X.mass.toReal * b + Λ ^ (0 - 1) * 0 * a) := by ring
  | succ k =>
    obtain ⟨η, θ, hηf, hθf, hid⟩ :=
      (Submission.cmcdt_lpo_she_cylinder_homotopy hLOC).1 N k X β ηF ηG V hVo hXV hV
    have hη : |X η| ≤ Λ ^ (k + 1) * δ * b * X.mass.toReal :=
      hMSB N (k + 1) X η _ hXm
        (hslice (k + 1) (exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)))
          (exteriorDerivative (ω : DifferentialForm (Euclid N') (k + 1))) b
          (η : DifferentialForm (Euclid N) (k + 1))
          (ContDiff.continuous (exteriorDerivative_isTestForm β.2.1).1) hdβ hb hηf)
    -- `spt ∂X ⊆ spt X`, and `M(∂X) = boundaryMassOn X univ`
    have hbm : boundaryMassOn X univ = X.boundary.mass := rfl
    have hθ : |X.boundary θ| ≤ Λ ^ k * δ * a * X.boundary.mass.toReal :=
      hMSB N k X.boundary θ _ (hbm ▸ hXbm) fun x hx =>
        hslice k (β : DifferentialForm (Euclid (N + 1)) (k + 1))
          (ω : DifferentialForm (Euclid N') (k + 1)) a (θ : DifferentialForm (Euclid N) k)
          (ContDiff.continuous β.2.1.1) hβ ha hθf x (hSB N k X hx)
    rw [hid, hbm, Nat.add_sub_cancel]
    calc |X η + X.boundary θ| ≤ |X η| + |X.boundary θ| := abs_add_le _ _
      _ ≤ Λ ^ (k + 1) * δ * b * X.mass.toReal + Λ ^ k * δ * a * X.boundary.mass.toReal :=
        add_le_add hη hθ
      _ = δ * (Λ ^ (k + 1) * X.mass.toReal * b + Λ ^ k * X.boundary.mass.toReal * a) := by ring

/-- Simon 6.2.29, existence of the limit: for `X ∈ 𝒟ₖ(ℝᴺ)` with `spt X` compact and
`M(X), M(∂X) < ∞`, a Lipschitz `F : ℝᴺ → ℝᴺ'` and `ω ∈ 𝒟ᵏ(ℝᴺ')`, the evaluations `X(Fⱼ^#ω)`
converge to one limit `L` for every sequence of `C^∞` maps `Fⱼ → F` (uniformly on `spt X`, with
`|DFⱼ|` bounded there).  By the homotopy estimate 2.27, the evaluations on the mollified
approximants `Gᵢ` are Cauchy; comparing any admissible `Fⱼ` with `Gᵢ` gives the same limit. -/
theorem Submission.cmcdt_lpo_pf_pointwise_limit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ L : ℝ, ∀ (Λ' : ℝ) (Fs : ℕ → Euclid N → Euclid N') (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 L) := by
  intro hVO hREP hLB N N' k Λ F X ω hF hX1 hX2 hX3
  have hE := Submission.cmcdt_lpo_smooth_homotopy_estimate hVO hREP hLB
  -- step 1: bounds `a`, `b` for `|ω|`, `|dω|`; step 2: mollified `Gᵢ` and `θᵢ = Gᵢ^#ω` near `spt X`
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Submission.cmcdt_lpo_pf_form_bounds N' k ω
  obtain ⟨G, hG, -, hDG, hdistG, -, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨θ, hθs⟩ := hηG k ω
  have hθ : ∀ i, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ i : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G i x)).compContinuousLinearMap
          (fderiv ℝ (G i) x) := fun i => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs i
    exact ⟨W, hW, hKW, h1⟩
  let Cf : ℝ → ℝ := fun μ =>
    μ ^ k * X.mass.toReal * b + μ ^ (k - 1) * (boundaryMassOn X univ).toReal * a
  have ha0 : 0 ≤ a := (covectorEuclideanNorm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (covectorEuclideanNorm_nonneg _).trans (hb 0)
  have hC0 : ∀ μ : ℝ, 0 ≤ μ → 0 ≤ Cf μ := fun μ hμ => by
    simp only [Cf]
    positivity
  have hΛ0 : (0 : ℝ) ≤ Λ := Λ.2
  have hrate : Tendsto (fun i : ℕ => (Λ : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
    rw [mul_zero] at this
    exact this.congr (fun j => mul_one_div _ _)
  -- step 3: the homotopy estimate makes `X(θᵢ)` Cauchy; `L` is its limit
  have hcauchy : CauchySeq (fun i => X (θ i)) := by
    refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => 2 * ((Λ : ℝ) / ((n : ℝ) + 1)) * Cf Λ) ?_ ?_
    · intro n m M hn hm
      rw [Real.dist_eq, abs_sub_comm]
      have hest := hE N N' k Λ ((Λ : ℝ) / ((n : ℝ) + 1) + (Λ : ℝ) / ((m : ℝ) + 1)) a b (G n) (G m)
        X ω (θ n) (θ m) (hG n) (hG m) hX1 hX2 hX3 (fun x _ => ⟨hDG n x, hDG m x⟩)
        (fun x _ => (dist_triangle _ (F x) _).trans
          (add_le_add (hdistG n x) (by rw [dist_comm]; exact hdistG m x))) ha hb (hθ n) (hθ m)
      refine hest.trans (mul_le_mul_of_nonneg_right ?_ (hC0 _ hΛ0))
      have h1 : (Λ : ℝ) / ((n : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΛ0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have h2 : (Λ : ℝ) / ((m : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΛ0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
      linarith
    · have := (hrate.const_mul 2).mul_const (Cf Λ)
      simpa using this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- step 4: any admissible `Fⱼ`, `ηⱼ` give `|X(ηⱼ) − L| ≤ ε'·C(Λ'') < ε` for large `j`
  refine ⟨L, fun Λ' Fs ηs hFs hD hU hη => ?_⟩
  set Λ'' : ℝ := max (Λ : ℝ) Λ'
  have hΛ'' : 0 ≤ Λ'' := le_trans hΛ0 (le_max_left _ _)
  have hC'' := hC0 Λ'' hΛ''
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (Cf Λ'' + 1) with hε'eq
  have hε'pos : 0 < ε' := div_pos hε (by linarith)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hU ε' hε'pos)
  refine ⟨j₀, fun j hj => ?_⟩
  have hbound : ∀ i : ℕ, |X (ηs j) - X (θ i)| ≤ ((Λ : ℝ) / ((i : ℝ) + 1) + ε') * Cf Λ'' := by
    intro i
    exact hE N N' k Λ'' _ a b (G i) (Fs j) X ω (θ i) (ηs j) (hG i) (hFs j) hX1 hX2 hX3
      (fun x hx => ⟨(hDG i x).trans (le_max_left _ _), (hD j x hx).trans (le_max_right _ _)⟩)
      (fun x hx => (dist_triangle _ (F x) _).trans (add_le_add (hdistG i x) (hj₀ j hj x hx).le))
      ha hb (hθ i) (hη j)
  have hlim : |X (ηs j) - L| ≤ ε' * Cf Λ'' := by
    have h1 : Tendsto (fun i => |X (ηs j) - X (θ i)|) atTop (𝓝 |X (ηs j) - L|) :=
      (tendsto_const_nhds.sub hL).abs
    have h2 : Tendsto (fun i : ℕ => ((Λ : ℝ) / ((i : ℝ) + 1) + ε') * Cf Λ'') atTop
        (𝓝 ((0 + ε') * Cf Λ'')) := (hrate.add_const ε').mul_const _
    rw [zero_add] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 hbound
  rw [Real.dist_eq]
  calc |X (ηs j) - L| ≤ ε' * Cf Λ'' := hlim
    _ < ε := by
      rw [hε'eq, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- The Lipschitz push-forward of a normal current is a current (Simon 6.2.28–2.29).  For every
`ω`, `L ω` is the common limit of `X(ηⱼ)` over admissible data for `ω`
(`cmcdt_lpo_pf_pointwise_limit`).  The common approximants `Gⱼ` and forms `θⱼ^ω = Gⱼ^#ω` near
`spt X` of `cmcdt_lpo_pf_approx_data` are admissible for every `ω`; sums and scalar multiples of
them are admissible for `ω₁ + ω₂` and `c • ω`, so `L` is linear by uniqueness of limits.  By (L1)
and the mass–support bound, `|L ω| ≤ Λᵏ M(X) c` whenever `|ω| ≤ c`, so `L` is a current `T`
(`cmcdt_lpo_current_toolkit`), and `X(ηⱼ) → T(ω)` for all admissible data. -/
theorem Submission.cmcdt_lpo_pf_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ T : GeometricCurrentOn (univ : Set (Euclid N')) k, ∀ (Λ' : ℝ) (Fs : ℕ → Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (T ω)) := by
  intro hVO hREP hLB N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨hMSB, hBC, -, -⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  have hL1 := hLB.1
  -- the common limit `L ω` of `X(ηⱼ)` over all admissible data for `ω`
  choose L hL using fun ω =>
    Submission.cmcdt_lpo_pf_pointwise_limit hVO hREP hLB N N' k Λ F X ω hF hX1 hX2 hX3
  -- common approximants `Gⱼ` and pulled-back forms `θⱼ^ω`, admissible for every `ω`
  obtain ⟨G, hG, -, hDG, -, hUG, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  choose θ hθs using hηG k
  have hθ : ∀ ω j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ ω j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G j x)).compContinuousLinearMap
          (fderiv ℝ (G j) x) := fun ω j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs ω j
    exact ⟨W, hW, hKW, h1⟩
  have hconv : ∀ ω, Tendsto (fun j => X (θ ω j)) atTop (𝓝 (L ω)) := fun ω =>
    hL ω Λ G (θ ω) hG (fun j x _ => hDG j x) hUG.tendstoUniformlyOn (hθ ω)
  -- additivity: `θⱼ^{ω₁} + θⱼ^{ω₂}` is admissible for `ω₁ + ω₂`
  have hadd : ∀ ω₁ ω₂, L (ω₁ + ω₂) = L ω₁ + L ω₂ := by
    intro ω₁ ω₂
    have hdata : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        ((θ ω₁ j + θ ω₂ j : TestFormOn (univ : Set (Euclid N)) k) :
          DifferentialForm (Euclid N) k) x =
        (((ω₁ + ω₂ : TestFormOn (univ : Set (Euclid N')) k) : DifferentialForm (Euclid N') k)
          (G j x)).compContinuousLinearMap (fderiv ℝ (G j) x) := by
      intro j
      obtain ⟨W₁, hW₁, hK₁, h₁⟩ := hθ ω₁ j
      obtain ⟨W₂, hW₂, hK₂, h₂⟩ := hθ ω₂ j
      refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, subset_inter hK₁ hK₂, fun x hx => ?_⟩
      rw [Submodule.coe_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, h₁ x hx.1, h₂ x hx.2]
      ext v
      simp
    have h1 := hL (ω₁ + ω₂) Λ G (fun j => θ ω₁ j + θ ω₂ j) hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn hdata
    have h2 : Tendsto (fun j => X (θ ω₁ j + θ ω₂ j)) atTop (𝓝 (L ω₁ + L ω₂)) := by
      have := (hconv ω₁).add (hconv ω₂)
      refine this.congr (fun j => ?_)
      exact (X.toCurrent.map_add _ _).symm
    exact tendsto_nhds_unique h1 h2
  -- homogeneity: `c • θⱼ^ω` is admissible for `c • ω`
  have hsmul : ∀ (c : ℝ) ω, L (c • ω) = c * L ω := by
    intro c ω
    have hdata : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        ((c • θ ω j : TestFormOn (univ : Set (Euclid N)) k) :
          DifferentialForm (Euclid N) k) x =
        (((c • ω : TestFormOn (univ : Set (Euclid N')) k) : DifferentialForm (Euclid N') k)
          (G j x)).compContinuousLinearMap (fderiv ℝ (G j) x) := by
      intro j
      obtain ⟨W, hW, hK, h⟩ := hθ ω j
      refine ⟨W, hW, hK, fun x hx => ?_⟩
      rw [Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, h x hx]
      ext v
      simp
    have h1 := hL (c • ω) Λ G (fun j => c • θ ω j) hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn hdata
    have h2 : Tendsto (fun j => X (c • θ ω j)) atTop (𝓝 (c * L ω)) := by
      have := (hconv ω).const_mul c
      refine this.congr (fun j => ?_)
      exact (X.toCurrent.map_smul c _).symm
    exact tendsto_nhds_unique h1 h2
  let T₀ : TestFormOn (univ : Set (Euclid N')) k →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := hadd
      map_smul' := hsmul }
  -- `|T₀ ω| ≤ Λᵏ M(X) c` whenever `|ω| ≤ c`, by (L1) and the mass–support bound
  have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid N')) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) x) ≤ c) →
        |T₀ ω| ≤ ((Λ : ℝ) ^ k * X.mass.toReal) * c := by
    intro ω c hc
    have hj : ∀ j, |X (θ ω j)| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal := by
      intro j
      apply hMSB N k X (θ ω j) ((Λ : ℝ) ^ k * c) hX2
      intro x hx
      obtain ⟨W, -, hKW, h⟩ := hθ ω j
      rw [h x (hKW hx)]
      refine (hL1 N N' k (fderiv ℝ (G j) x) _).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDG j x) k) (hc _)
        (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.2 k)
    have hlim : |L ω| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal :=
      le_of_tendsto' (hconv ω).abs hj
    show |L ω| ≤ _
    linarith
  -- the bounded linear functional `T₀` is a current `T`, with `T ω = L ω`
  obtain ⟨T, hT, -⟩ := hBC N' k T₀ ((Λ : ℝ) ^ k * X.mass.toReal) hbound
  refine ⟨T, fun Λ' Fs ω ηs hFs hD hU hη => ?_⟩
  rw [hT ω]
  exact hL ω Λ' Fs ηs hFs hD hU hη
/-- **Mass bound and support of the Lipschitz push-forward** (Simon 6.2.29).  Assume (VO), (REP)
and the covector bounds, and let `lpush` be any family satisfying the approximation property (PA):
`X(G_j^# ω) → lpush(F, X)(ω)` along smooth `G_j → F` uniformly on `spt X` with bounded derivatives.
Then `M(lpush(F, X)) ≤ Λᵏ M(X)` and `spt lpush(F, X) ⊆ F(spt X)` for `Λ`-Lipschitz `F` and
compactly supported `X` with `M(X) + M(∂X) < ∞`.  The approximations come from
`cmcdt_lpo_pf_approx_data`; locality (LOC) and the support mass bound (MSB) are derived from (VO)
and (REP) as in Simon 6.2.7–2.12. -/
theorem Submission.cmcdt_lpo_pf_mass_support : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support := by
  intro hVO hREP hLB lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  -- (LOC), Simon 6.2.11 with (VO): `X(η) = X(η')` if `η = η'` on an open set containing `spt X`.
  have hLOC : ∀ (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W →
      X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x =
        (η' : DifferentialForm (Euclid N) k) x) → X η = X η' := by
    intro η η' W hW hXW hηη'
    have hsub : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
        DifferentialForm (Euclid N) k) ⊆ Wᶜ := by
      refine closure_minimal (fun x hx hxW => hx ?_) hW.isClosed_compl
      simp [hηη' x hxW]
    have h0 := hVO N k univ X (η - η') (Disjoint.mono hsub hXW disjoint_compl_left)
    rw [show X (η - η') = X η - X η' from map_sub X.toCurrent η η'] at h0
    linarith
  -- (MSB), Simon 6.2.7–2.12 with (VO), (REP): `|X(ψ)| ≤ c M(X)` if `|ψ| ≤ c` on `spt X`.
  have hMSB : ∀ (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ),
      (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) →
        |X ψ| ≤ c * X.mass.toReal := by
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hXμ, -⟩ := hREP N k univ X isOpen_univ
      (fun W _ _ => lt_of_le_of_lt (X.massOn_mono (subset_univ W)) hX2)
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨hμ ▸ hX2⟩
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, hω, rfl⟩
      dsimp only
      rw [hVO N k univ X ω (disjoint_left.2 fun x hx hxs => hxs.2 (hω.1 hx)),
        ENNReal.ofReal_zero]
    intro ψ c hψ
    have hae : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hZ
      by_contra hxZ
      exact hx ((Real.norm_eq_abs _).le.trans
        ((hξ x _).trans (hψ x (mem_sdiff_of_mem (mem_univ x) hxZ))))
    have h := norm_integral_le_of_norm_le_const hae
    rwa [Real.norm_eq_abs, ← hXμ ψ, measureReal_def, hμ] at h
  have hL1 := hLB.1
  obtain ⟨G, hG, -, hDG, hdistG, hUG, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  choose θ hθs using hηG k
  have hθ : ∀ ω j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ ω j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G j x)).compContinuousLinearMap
          (fderiv ℝ (G j) x) := fun ω j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs ω j
    exact ⟨W, hW, hKW, h1⟩
  have hconv : ∀ ω, Tendsto (fun j => X (θ ω j)) atTop (𝓝 (lpush N N' k F X ω)) := fun ω =>
    hPA N N' k Λ Λ F G X ω (θ ω) hF hX1 hX2 hX3 hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn (hθ ω)
  have hrate : Tendsto (fun i : ℕ => (Λ : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
    rw [mul_zero] at this
    exact this.congr (fun j => mul_one_div _ _)
  refine ⟨?_, ?_⟩
  · apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    have hj : ∀ j, |X (θ ω j)| ≤ (Λ : ℝ) ^ k * 1 * X.mass.toReal := by
      intro j
      apply hMSB (θ ω j) ((Λ : ℝ) ^ k * 1)
      intro x hx
      obtain ⟨W, -, hKW, h⟩ := hθ ω j
      rw [h x (hKW hx)]
      refine (hL1 N N' k (fderiv ℝ (G j) x) _).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDG j x) k) (hω.2 _)
        (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.2 k)
    have hlim : lpush N N' k F X ω ≤ (Λ : ℝ) ^ k * 1 * X.mass.toReal :=
      (le_abs_self _).trans (le_of_tendsto' (hconv ω).abs hj)
    dsimp only
    calc ENNReal.ofReal (lpush N N' k F X ω)
        ≤ ENNReal.ofReal ((Λ : ℝ) ^ k * 1 * X.mass.toReal) := ENNReal.ofReal_le_ofReal hlim
      _ = ENNReal.ofReal (((Λ ^ k : NNReal) : ℝ) * X.mass.toReal) := by
        rw [NNReal.coe_pow, mul_one]
      _ = ((Λ ^ k : NNReal) : ℝ≥0∞) * X.mass := by
        rw [ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_toReal hX2.ne]
      _ = (Λ : ℝ≥0∞) ^ k * X.mass := by
        rw [ENNReal.coe_pow]
  · rintro y ⟨-, hy⟩
    by_contra hyF
    apply hy
    by_cases hXe : X.support = ∅
    · have hX0 : ∀ η : TestFormOn (univ : Set (Euclid N)) k, X η = 0 := by
        intro η
        rw [hLOC η 0 ∅ isOpen_empty (by rw [hXe]) (fun x hx => hx.elim), map_zero]
      have hT0 : ∀ ω, lpush N N' k F X ω = 0 := by
        intro ω
        have h := hconv ω
        simp only [hX0] at h
        exact tendsto_nhds_unique h tendsto_const_nhds
      refine ⟨ball y 1, ⟨isOpen_ball, ?_, subset_univ _, fun ω _ => hT0 ω⟩, mem_ball_self one_pos⟩
      exact (isCompact_closedBall y 1).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · have hne : (F '' X.support).Nonempty := (nonempty_iff_ne_empty.2 hXe).image F
      have hcpt : IsCompact (F '' X.support) := hX1.image hF.continuous
      have hr : 0 < infDist y (F '' X.support) :=
        (hcpt.isClosed.notMem_iff_infDist_pos hne).1 hyF
      set r := infDist y (F '' X.support) with hrdef
      refine ⟨ball y (r / 3), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self (by linarith)⟩
      · exact (isCompact_closedBall y (r / 3)).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
      · intro ω hω
        have hev : ∀ᶠ j in atTop, X (θ ω j) = 0 := by
          filter_upwards [hrate.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 3))]
            with j hj
          obtain ⟨W, hW, hKW, h⟩ := hθ ω j
          have hO : IsOpen {x | r / 3 < dist (G j x) y} :=
            isOpen_lt continuous_const ((hG j).continuous.dist continuous_const)
          have hKO : X.support ⊆ {x | r / 3 < dist (G j x) y} := by
            intro x hx
            have h1 : r ≤ dist (F x) y := by
              rw [dist_comm]
              exact infDist_le_dist_of_mem (mem_image_of_mem F hx)
            have h2 : dist (G j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := hdistG j x
            have h3 := dist_triangle (F x) (G j x) y
            rw [dist_comm (F x) (G j x)] at h3
            show r / 3 < dist (G j x) y
            linarith
          have hzero : ∀ x ∈ {x | r / 3 < dist (G j x) y} ∩ W,
              (θ ω j : DifferentialForm (Euclid N) k) x =
                ((0 : TestFormOn (univ : Set (Euclid N)) k) : DifferentialForm (Euclid N) k) x := by
            intro x hx
            rw [h x hx.2]
            have h0 : (ω : DifferentialForm (Euclid N') k) (G j x) = 0 := by
              apply image_eq_zero_of_notMem_tsupport
              intro hmem
              have hb := hω hmem
              rw [mem_ball] at hb
              exact absurd hb (not_lt.2 hx.1.le)
            rw [h0]
            ext v
            simp
          rw [hLOC (θ ω j) 0 _ (hO.inter hW) (subset_inter hKO hKW) hzero, map_zero]
        have h0 : Tendsto (fun j => X (θ ω j)) atTop (𝓝 0) :=
          tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm)
        exact tendsto_nhds_unique (hconv ω) h0
/-- **Simon 6.2.29** (Lipschitz push-forward, normalization): push-forward by the identity is the
identity.  Let `lpush` satisfy the approximation property (PA): if `F` is Lipschitz, the `Fⱼ` are
`C^∞` with `‖DFⱼ‖ ≤ Λ'` on `spt X`, `Fⱼ → F` uniformly on `spt X`, and `ηⱼ = Fⱼ^# ω` on an open
`W ⊇ spt X`, then `X(ηⱼ) → lpush(F, X)(ω)`.  For `X` with compact support, `M(X) < ∞` and
`M(∂X) < ∞`, take `F = Fⱼ = id`, `Λ = Λ' = 1` and `ηⱼ = ω` (`id^# ω = ω`): the constant sequence
`X(ω)` tends to `lpush(id, X)(ω)`, so the two agree for every `ω`. -/
theorem Submission.cmcdt_lpo_pf_identity : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X := by
  intro lpush hPA N k X hX1 hX2 hX3
  ext ω
  -- the constant sequence `Fⱼ = id` converges uniformly to `id`
  have hU : TendstoUniformlyOn (fun (_ : ℕ) (x : Euclid N) => x) (fun x => x) atTop X.support := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun j x _ => by simpa using hε
  -- (PA) with `F = Fⱼ = id`, `Λ = Λ' = 1`, `ηⱼ = ω`, since `id^# ω = ω` on `W = ℝᴺ`
  have hT := hPA N N k 1 1 (fun x => x) (fun _ => fun x => x) X ω (fun _ => ω) LipschitzWith.id
    hX1 hX2 hX3 (fun _ => contDiff_id)
    (fun j x _ => by rw [fderiv_fun_id]; exact ContinuousLinearMap.norm_id_le) hU
    (fun j => ⟨univ, isOpen_univ, subset_univ _, fun x _ => by
      rw [fderiv_fun_id]
      ext v
      simp⟩)
  -- the constant sequence `X(ω)` tends to `lpush(id, X)(ω)` and to `X(ω)`
  exact tendsto_nhds_unique hT tendsto_const_nhds

/-- **Simon 6.2.29: the Lipschitz push-forward is additive** on currents `X` with `spt X` compact
and `M(X), M(∂X) < ∞`.  Suppose `lpush` has the approximation property (PA): `X(ηⱼ) → f#X(ω)`
whenever smooth `Fⱼ → F` uniformly on `spt X`, `‖DFⱼ‖ ≤ Λ'` there, and `ηⱼ = Fⱼ^#ω` on an open
`W ⊇ spt X`.  Then `f#(X − Y) = f#X − f#Y`.  `X − Y` is again such a current, with
`spt(X − Y) ⊆ spt X ∪ spt Y` (`cmcdt_lpo_pf_normal_closure`).  So one approximating sequence
`Fⱼ`, `ηⱼ` for `K = spt X ∪ spt Y` (`cmcdt_lpo_pf_approx_data`, `Λ' = Λ`) serves `X`, `Y` and
`X − Y`, and `(X − Y)(ηⱼ) = X(ηⱼ) − Y(ηⱼ)`.  Apply (PA) three times; limits are unique. -/
theorem Submission.cmcdt_lpo_pf_sub : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y := by
  intro lpush hPA N N' k Λ F X Y hF hX1 hX2 hX3 hY1 hY2 hY3
  -- `X − Y` is normal, with `spt(X − Y) ⊆ spt X ∪ spt Y`
  obtain ⟨hsupp, hZ1, hZ2, hZ3⟩ :=
    Submission.cmcdt_lpo_pf_normal_closure.1 N k X Y hX1 hX2 hX3 hY1 hY2 hY3
  ext ω
  -- one approximation `Fⱼ → F`, `ηⱼ = Fⱼ^#ω` near `K = spt X ∪ spt Y`
  obtain ⟨Fs, hFs, -, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F (X.support ∪ Y.support) hF (hX1.union hY1)
  obtain ⟨ηs, hηs⟩ := hη k ω
  have hη' : ∀ (S : Set (Euclid N)), S ⊆ X.support ∪ Y.support → ∀ j, ∃ W : Set (Euclid N),
      IsOpen W ∧ S ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun S hS j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hS.trans hKW, h1⟩
  -- (PA) for `X`, `Y` and `X − Y`, all with `Λ' = Λ`
  have hX := hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (hη' _ subset_union_left)
  have hY := hPA N N' k Λ Λ F Fs Y ω ηs hF hY1 hY2 hY3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (hη' _ subset_union_right)
  have hZ := hPA N N' k Λ Λ F Fs (X - Y) ω ηs hF hZ1 hZ2 hZ3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (hη' _ hsupp)
  -- `(X − Y)(ηⱼ) = X(ηⱼ) − Y(ηⱼ)` by definition of the difference
  have hXY : Tendsto (fun j => (X - Y) (ηs j)) atTop
      (𝓝 (lpush N N' k F X ω - lpush N N' k F Y ω)) := hX.sub hY
  exact tendsto_nhds_unique hZ hXY

/-- **The Lipschitz push-forward depends only on `F|spt X`** (Simon Ch. 6, 2.28–2.29).  Suppose
`lpush` has the approximation property (PA): whenever `F` is `Λ`-Lipschitz, the `Fⱼ` are `C^∞`
with `‖DFⱼ‖ ≤ Λ'` on `spt X`, `Fⱼ → F` uniformly on `spt X`, and `ηⱼ = Fⱼ^#ω` on an open set
containing `spt X`, then `X(ηⱼ) → lpush(F, X)(ω)` (`spt X` compact, `M(X), M(∂X) < ∞`).  If the
`Λ`-Lipschitz maps `F`, `G` agree on `spt X`, then `lpush(F, X) = lpush(G, X)`.

Fix `ω ∈ 𝒟ᵏ(ℝ^{N'})`.  The approximation data for `F` on `K = spt X` give `C^∞` maps `Fⱼ` with
`‖DFⱼ‖ ≤ Λ` and `Fⱼ → F` uniformly, and test forms `ηⱼ` equal to `Fⱼ^#ω` on open `Wⱼ ⊇ spt X`.
As `F = G` on `spt X`, also `Fⱼ → G` uniformly on `spt X`.  So (PA) for `F` and for `G`, with the
same `Fⱼ` and `ηⱼ`, gives `X(ηⱼ) → lpush(F, X)(ω)` and `X(ηⱼ) → lpush(G, X)(ω)`, and limits in
`ℝ` are unique.  This is 2.28 (`f#T = g#T` for `C¹` maps with `f = g` on `spt T`) for the
Lipschitz push-forward of 2.29, the limit of push-forwards by smooth approximations of `f`. -/
theorem Submission.cmcdt_lpo_pf_congr : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X := by
  intro lpush hPA N N' k Λ F G X hF hG hX1 hX2 hX3 hFG
  -- currents are determined by their values on test forms: fix `ω ∈ 𝒟ᵏ(ℝ^{N'})`
  ext ω
  -- `C^∞` maps `Fⱼ → F` with `‖DFⱼ‖ ≤ Λ`, and forms `ηⱼ = Fⱼ^#ω` on open `Wⱼ ⊇ spt X`
  obtain ⟨Fs, hFs, -, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨ηs, hηs⟩ := hη k ω
  have hη' : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hKW, h1⟩
  -- `Fⱼ → F` uniformly on `spt X`, hence `Fⱼ → G` there, as `F = G` on `spt X`
  have hUF : TendstoUniformlyOn Fs F atTop X.support := hU.tendstoUniformlyOn
  have hUG : TendstoUniformlyOn Fs G atTop X.support := hUF.congr_right hFG
  -- (PA) for `F` and for `G` with the same data (`Λ' = Λ`); limits in `ℝ` are unique
  have h1 := hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x) hUF hη'
  have h2 := hPA N N' k Λ Λ G Fs X ω ηs hG hX1 hX2 hX3 hFs (fun j x _ => hD j x) hUG hη'
  exact tendsto_nhds_unique h1 h2

/-- **Simon 6.2.24(1) and 6.2.29: the Lipschitz push-forward commutes with the boundary** on
currents `X` with `spt X` compact and `M(X), M(∂X) < ∞`.  Suppose `lpush` has the approximation
property (PA): `X(ηⱼ) → f#X(ω)` whenever smooth `Fⱼ → F` uniformly on `spt X`, `‖DFⱼ‖ ≤ Λ'`
there, and `ηⱼ = Fⱼ^#ω` on an open `W ⊇ spt X`.  Then `∂f#X = f#∂X`.  `∂X` is again such a
current, with `spt ∂X ⊆ spt X` (`cmcdt_lpo_pf_normal_closure`).  One approximating sequence
`Fⱼ`, `ηⱼ` for `K = spt X` (`cmcdt_lpo_pf_approx_data`, `Λ' = Λ`) also has `dηⱼ = Fⱼ^#(dω)` near
`spt X`.  So (PA) for `∂X` with `ω` and for `X` with `dω` concern the same sequence
`∂X(ηⱼ) = X(dηⱼ)`; its limits `f#∂X(ω)` and `f#X(dω) = ∂f#X(ω)` agree. -/
theorem Submission.cmcdt_lpo_pf_boundary : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary := by
  intro lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  -- `∂X` is normal, with `spt ∂X ⊆ spt X`; `boundaryMassOn X univ` is `M(∂X)`
  obtain ⟨hbsupp, hbX1, hbX3⟩ := Submission.cmcdt_lpo_pf_normal_closure.2 N k X hX1
  have hX3' : boundaryMassOn X univ < ∞ := hX3
  have hbX3' : boundaryMassOn X.boundary univ < ∞ := by
    rw [hbX3]
    exact ENNReal.zero_lt_top
  ext ω
  -- one approximation `Fⱼ → F` with `ηⱼ = Fⱼ^#ω` and `dηⱼ = Fⱼ^#(dω)` near `K = spt X`
  obtain ⟨Fs, hFs, -, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨ηs, hηs⟩ := hη k ω
  -- (PA) for `∂X` with `ω`, `ηⱼ` and for `X` with `dω`, `dηⱼ`, both with `Λ' = Λ`
  have h1 := hPA N N' k Λ Λ F Fs X.boundary ω ηs hF hbX1 hX3 hbX3' hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (fun j => by
      obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
      exact ⟨W, hW, hbsupp.trans hKW, h1⟩)
  have h2 := hPA N N' (k + 1) Λ Λ F Fs X (exteriorDerivativeTestOn univ k ω)
    (fun j => exteriorDerivativeTestOn univ k (ηs j)) hF hX1 hX2 hX3' hFs
    (fun j x _ => hD j x) hU.tendstoUniformlyOn (fun j => by
      obtain ⟨W, hW, hKW, -, h2⟩ := hηs j
      exact ⟨W, hW, hKW, h2⟩)
  -- `∂X(ηⱼ) = X(dηⱼ)` and `∂(f#X)(ω) = f#X(dω)` by definition; limits are unique
  exact tendsto_nhds_unique h2 h1

/-- **Push-forward as a limit of smooth push-forwards** (Simon 6.2.28–2.29).  Suppose `lpush`
has the approximation property (PA): `X(ηⱼ) → lpush(F, X)(ω)` whenever the `Fⱼ` are `C^∞` with
`‖DFⱼ‖ ≤ Λ'` on `spt X`, `Fⱼ → F` uniformly on `spt X` and `ηⱼ = Fⱼ^#ω` on an open set
containing `spt X`.  Then a single sequence of `C^∞`, `Λ`-Lipschitz `Fⱼ → F` (uniformly on `ℝᴺ`)
serves every `ω ∈ 𝒟ᵏ(ℝ^{N'})`: take the approximants and cut-off pull-backs of
`cmcdt_lpo_pf_approx_data` for `K = spt X` (so `‖DFⱼ‖ ≤ Λ` everywhere), drop the `dηⱼ` clause
and apply (PA) with `Λ' = Λ`. -/
theorem Submission.cmcdt_lpo_pf_smooth_approx : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω)) := by
  intro lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨Fs, hFs, hLip, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  refine ⟨Fs, hFs, hLip, hU, fun ω => ?_⟩
  obtain ⟨ηs, hηs⟩ := hη k ω
  -- `ηⱼ = Fⱼ^#ω` on an open `W ⊇ spt X` (the `dηⱼ` clause is not needed)
  have hη' : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hKW, h1⟩
  -- (PA) with `Λ' = Λ`, and uniform convergence on `ℝᴺ` restricted to `spt X`
  exact ⟨ηs, hη', hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn hη'⟩

/-- **The Lipschitz push-forward** (Simon 6.2.28–2.29).  For `F` Lipschitz and `X` with compact
support, `M(X) < ∞` and `M(∂X) < ∞`, `lpush F X` is the current `T` of `cmcdt_lpo_pf_current`:
`T(ω) = lim X(ηⱼ)` whenever `Fⱼ` are `C^∞`, `Fⱼ → F` uniformly on `spt X` with `‖DFⱼ‖` bounded
there, and `ηⱼ = Fⱼ^#ω` near `spt X`; otherwise `lpush F X = 0`.  This limit property (PA) does not
mention the Lipschitz constant used to build `T`, so it holds for every `Λ`.  Conjuncts (1)–(6) are
derived from (PA) for an arbitrary family `lpush` (the mass bound also uses (VO), (REP), (LB)). -/
theorem Submission.cmcdt_lpo_lipschitz_pushforward : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) ∧ ∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω)) := by
  intro hVO hREP hLB
  classical
  choose T hT using Submission.cmcdt_lpo_pf_current hVO hREP hLB
  -- `lpush F X = T` if `F` is Lipschitz and `X` is normal with compact support, `0` otherwise
  obtain ⟨lpush, hlpush⟩ : ∃ lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') →
      GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k,
      ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k)
        (h : (∃ Λ : NNReal, LipschitzWith Λ F) ∧ IsCompact X.support ∧ X.mass < ∞ ∧
          boundaryMassOn X univ < ∞),
        lpush N N' k F X = T N N' k h.1.choose F X h.1.choose_spec h.2.1 h.2.2.1 h.2.2.2 :=
    ⟨fun N N' k F X => if h : (∃ Λ : NNReal, LipschitzWith Λ F) ∧ IsCompact X.support ∧
        X.mass < ∞ ∧ boundaryMassOn X univ < ∞ then
        T N N' k h.1.choose F X h.1.choose_spec h.2.1 h.2.2.1 h.2.2.2 else 0,
      fun N N' k F X h => dite_eq_left h⟩
  -- (PA): the limit property of `T` holds for any Lipschitz constant of `F`
  have hPA : ∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N')
      (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k)
      (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k),
      LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') →
      TendstoUniformlyOn Fs F atTop X.support →
      (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        (ηs j : DifferentialForm (Euclid N) k) x =
          ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x)) →
      Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω)) := by
    intro N N' k Λ Λ' F Fs X ω ηs hF hXc hXm hXb hFs hDF hU hη
    rw [hlpush N N' k F X ⟨⟨Λ, hF⟩, hXc, hXm, hXb⟩]
    exact hT _ _ _ _ _ _ _ _ _ _ Λ' Fs ω ηs hFs hDF hU hη
  -- conjuncts (1)–(6) from (PA)
  exact ⟨lpush, Submission.cmcdt_lpo_pf_identity lpush hPA,
    Submission.cmcdt_lpo_pf_sub lpush hPA, Submission.cmcdt_lpo_pf_congr lpush hPA,
    Submission.cmcdt_lpo_pf_mass_support hVO hREP hLB lpush hPA,
    Submission.cmcdt_lpo_pf_boundary lpush hPA, Submission.cmcdt_lpo_pf_smooth_approx lpush hPA,
    hPA⟩
/-- **The cylinder `[[0, 1]] × X`** (Simon 6.2.17–2.21): conjuncts (7)–(9) of the operator
package.  With `ι(t, x) = (t, x)`, `J v = ι(0, v)` and `e₀` the first unit vector,
`cyl X (ω) = X(S ω)` for the slice `S ω (x)(v) = ∫₀¹ ω(ι(t, x))(e₀, J v) dt`.  The covector maps
`γ ↦ γ(e₀, J ·)` and `γ ↦ γ(J ·)` do not increase the Euclidean norm, so `S` is linear,
support-controlled and bounded in the sup of the covector norm; the bounded-current constructor
gives `cyl X` with `M(cyl X) ≤ M(X)`, additive in `X`.  Its support lies in the compact set
`ι([0, 1] × spt X)`, and the homotopy identities
`S(dω) = ω(ι(1, ·))(J ·) − ω(ι(0, ·))(J ·) − d(S ω)` (Simon 6.2.21) make `M(∂ cyl X)` finite. -/
theorem Submission.cmcdt_lpo_cylinder : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∃ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η := by
  intro hVO hREP hLB
  obtain ⟨hL1, hL2, -⟩ := hLB
  -- slices (a)–(e) of test forms, and the bounds (MSB), (BC) of the current toolkit
  obtain ⟨hSA, hSB, hSC, hSD, hSE⟩ := Submission.cmcdt_lpo_slice_forms
  obtain ⟨hMSB, hBC, -, -⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  -- step 1: `γ ↦ γ(e₀, J ·)` and `γ ↦ γ(J ·)` do not increase the covector norm
  obtain ⟨hR1, hR2⟩ := Submission.cmcdt_lpo_cyl_restriction_bounds hL1 hL2
  -- step 2: the linear slice operators `S N k : 𝒟^{k+1}(ℝ^{N+1}) → 𝒟^k(ℝ^N)`
  choose S hSf hSs hSb using Submission.cmcdt_lpo_cyl_slice_operator hSA hSE hR1
  -- step 3: `cyl X (ω) = X(S ω)` with `M(cyl X) ≤ M(X)`, additive on finite-mass currents
  choose cyl hcyl hsub using fun N k : ℕ =>
    Submission.cmcdt_lpo_cyl_current hMSB hBC N k (S N k) (hSb N k)
  refine ⟨cyl, fun N k X hXc hXm hXb => ?_,
    fun N k X Y _ hXm _ _ hYm _ => hsub N k X Y hXm hYm,
    fun N k X _ hXm _ ω => ⟨S N k ω, hSf N k ω, (hcyl N k X hXm).1 ω⟩⟩
  -- conjunct (7): compact support in `ι([0, 1] × spt X)`, finite mass and boundary mass
  obtain ⟨happ, hmass⟩ := hcyl N k X hXm
  obtain ⟨hcpt, hspt⟩ :=
    Submission.cmcdt_lpo_cyl_support hVO N k X (cyl N k X) (S N k) hXc (hSs N k) happ
  exact ⟨hcpt, hmass.trans_lt hXm,
    Submission.cmcdt_lpo_cyl_boundary_mass hMSB hSB hSC hSD hR2 N k X (cyl N k X)
      (fun m => S N m) hXm hXb (fun m => hSf N m) (fun m => hSb N m) happ, hspt⟩

/-- **Cut-off pull-backs along the smoothed homotopy and their limits** (Simon Ch. 6, §2: the
homotopy formula for Lipschitz maps via smooth approximation).  Write `ι(t, x) = (t, x₁, …, x_N)`,
`Jv = ι(0, v)` and `C = {ι(t, x) : t ∈ [0, 1], x ∈ K}` (compact).  With the smooth approximations
`F_j, G_j, H_j` of `cmcdt_lpoh_smooth_approx`, `β_j` is the cut-off pull-back of
`cmcdt_lpo_cutoff_pullback`, equal to `H_j^#ω` (and `dβ_j` to `H_j^#(dω)`) on an open `W_j ⊇ C`,
and `ρ_{s,j}(x) = β_j(ι(s, x)) ∘ J` is the affine pull-back of `β_j` by the isometric embedding
`ι(s, ·)`, a test form since `ι(s, ·)` is proper.  As `H_j ∘ ι(1, ·) = G_j` and
`H_j ∘ ι(0, ·) = F_j` with matching derivatives along `J`, `ρ_{1,j} = G_j^#ω` and
`ρ_{0,j} = F_j^#ω` near `K`, so (PA) gives the limits; the pointwise description of `β_j` on `C`
carries the derivative bounds of `cmcdt_lpoh_smooth_approx`. -/
theorem Submission.cmcdt_lpoh_pullback_limits : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' m : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)) (ω : TestFormOn (univ : Set (Euclid N')) m), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (β : ℕ → TestFormOn (univ : Set (Euclid (N + 1))) m) (ρ₁ ρ₀ : ℕ → TestFormOn (univ : Set (Euclid N)) m), (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₁ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₀ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid N)) m, IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → X.support ⊆ K → Tendsto (fun j => X (ρ₁ j)) atTop (𝓝 (lpush N N' m G X ω)) ∧ Tendsto (fun j => X (ρ₀ j)) atTop (𝓝 (lpush N N' m F X ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) m, IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (β j)) atTop (𝓝 (lpush (N + 1) N' m H Y ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (m + 1), IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j))) atTop (𝓝 (lpush (N + 1) N' (m + 1) H Y (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)))) ∧ ∀ (j : ℕ), ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∃ (p : Euclid N') (D : Euclid (N + 1) →L[ℝ] Euclid N'), (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((ω : DifferentialForm (Euclid N') m) p).compContinuousLinearMap D ∧ ‖D (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) ∧ ∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖ := by
  intro lpush hPA N N' m Λ L F G H K ω hF hG hH hK hHK
  obtain ⟨Fs, Gs, Hs, Λ', hFs, hGs, hHs, hDF, hDG, hFu, hGu, hH1, hH0, hDH1, hDH0, hDe, hDJ, hDHb,
    hHu⟩ := Submission.cmcdt_lpoh_smooth_approx N N' Λ F G H K hF hG hK hHK
  -- `C = {ι(t, x) : t ∈ [0, 1], x ∈ K}` is compact
  set C : Set (Euclid (N + 1)) := {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
    y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}
  have hιc : ∀ s : ℝ, Continuous
      (fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) :=
    fun s => (PiLp.continuous_toLp 2 _).comp (continuous_const.finCons (PiLp.continuous_ofLp 2 _))
  have hCc : IsCompact C := by
    have : C = (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
          (Icc (0 : ℝ) 1 ×ˢ K) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [this]
    exact (isCompact_Icc.prod hK).image (by fun_prop)
  -- cut-off pull-backs `β_j = H_j^#ω` and `dβ_j = H_j^#(dω)` on an open `W_j ⊇ C`
  have hCP := fun j => Submission.cmcdt_lpo_cutoff_pullback (N + 1) N' m (Hs j) ω C (hHs j) hCc
  choose β W hWo hCW hβW hdβW using hCP
  -- end slices `ρ(x)(v) = β(ι(s, x))(Jv)`: the affine pull-back by the isometry `ι(s, ·)`
  have hslice : ∀ (s : ℝ) (β' : TestFormOn (univ : Set (Euclid (N + 1))) m),
      ∃ ρ : TestFormOn (univ : Set (Euclid N)) m, ∀ (x : Euclid N) (v : Fin m → Euclid N),
        (ρ : DifferentialForm (Euclid N) m) x v =
          (β' : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
    intro s β'
    let Jₗ : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun v w => by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp
        map_smul' := fun c v => by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp }
    let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jₗ
    have hJ : ∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) := fun _ => rfl
    set b : Euclid (N + 1) := WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (0 : Euclid N))) with hb
    have hbJ : ∀ x, b + J x = WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) := by
      intro x
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [hb, hJ]
    have hproper : IsProperMap fun x => b + J x := by
      refine (Isometry.isClosedEmbedding (Isometry.of_dist_eq fun x y => ?_)).isProperMap
      rw [hbJ, hbJ, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succ]
      simp
    refine ⟨⟨affinePullbackForm J b (β' : DifferentialForm (Euclid (N + 1)) m),
      affinePullbackForm_isTestForm J b hproper β'.property.1, subset_univ _⟩, fun x v => ?_⟩
    show affinePullbackForm J b (β' : DifferentialForm (Euclid (N + 1)) m) x v = _
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hbJ]
    rfl
  choose ρ hρ using fun (s : ℝ) (j : ℕ) => hslice s (β j)
  refine ⟨β, ρ 1, ρ 0, fun j x v => hρ 1 j x v, fun j x v => hρ 0 j x v, ?_, ?_, ?_, ?_⟩
  · -- (ii): near `K`, `ρ_{1,j} = G_j^#ω` and `ρ_{0,j} = F_j^#ω`
    intro X hXc hXm hXb hXK
    have hend : ∀ (s : ℝ) (Es : ℕ → Euclid N → Euclid N'),
        (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) = Es j x) →
        (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
          (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Es j) x v) →
        s ∈ Icc (0 : ℝ) 1 → ∀ j, ∃ W' : Set (Euclid N), IsOpen W' ∧ X.support ⊆ W' ∧ ∀ x ∈ W',
          (ρ s j : DifferentialForm (Euclid N) m) x =
            ((ω : DifferentialForm (Euclid N') m) (Es j x)).compContinuousLinearMap
              (fderiv ℝ (Es j) x) := by
      intro s Es hE hDE hs j
      refine ⟨(fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)))
        ⁻¹' W j, (hWo j).preimage (hιc s), fun x hx => hCW j ⟨s, hs, x, hXK hx, rfl⟩,
        fun x hx => ?_⟩
      ext v
      rw [hρ s j x v, hβW j _ hx]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hE]
      congr 1
      funext i
      exact hDE j x (v i)
    constructor
    · exact hPA N N' m Λ Λ G Gs X ω (ρ 1) hG hXc hXm hXb hGs (fun j x _ => hDG j x)
        hGu.tendstoUniformlyOn (hend 1 Gs hH1 hDH1 ⟨zero_le_one, le_rfl⟩)
    · exact hPA N N' m Λ Λ F Fs X ω (ρ 0) hF hXc hXm hXb hFs (fun j x _ => hDF j x)
        hFu.tendstoUniformlyOn (hend 0 Fs hH0 hDH0 ⟨le_rfl, zero_le_one⟩)
  · -- (iii): (PA) for `H` with the approximations `H_j`
    intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' m L Λ' H Hs Y ω β hH hYc hYm hYb hHs ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hβW j⟩
  · -- (iv): the same in degree `m + 1` for `dβ_j` and `dω`
    intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' (m + 1) L Λ' H Hs Y
      (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)
      (fun j => exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j)) hH hYc hYm hYb hHs
      ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hdβW j⟩
  · -- (v): on `C`, `β_j = H_j^#ω` with the derivative bounds of the smoothed homotopy
    intro j x hx t ht
    exact ⟨Hs j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      hβW j _ (hCW j ⟨t, ht, x, hx, rfl⟩), hDe j t x, hDJ j t ht x⟩

/-- **Homotopy identity for a cylinder operator** (Simon Ch. 6, 2.17–2.22, and the homotopy
formula 2.25–2.27).  Let `cyl` take `X ∈ 𝒟ₖ(ℝᴺ)` to `cyl X ∈ 𝒟ₖ₊₁(ℝᴺ⁺¹)` with the slice property
(9): for `X` with compact support, `M(X) < ∞` and `M(∂X) < ∞`, and `ω ∈ 𝒟ᵏ⁺¹(ℝᴺ⁺¹)`,
`cyl X (ω) = X(η)` with `η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt`.  (a) In degree `0`, where
`boundaryMassOn X univ = 0`, (9) for `dβ` and the slice identity (d) of `cmcdt_lpo_slice_forms`
give `η = ρ₁ − ρ₀`, so `cyl X (dβ) = X(ρ₁) − X(ρ₀)`.  (b) In degree `k + 1`, (9) for `X` and `dβ`
gives `η`, (9) for `∂X` and `β` gives `θ` with `cyl ∂X (β) = ∂X(θ) = X(dθ)`, and the slice
identity (c) gives `η = ρ₁ − ρ₀ − dθ`; by linearity of `X`,
`cyl X (dβ) = X(ρ₁) − X(ρ₀) − cyl ∂X (β)`. -/
theorem Submission.cmcdt_lpoh_cyl_identity : ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (ρ₁ ρ₀ : TestFormOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (ρ₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (ρ₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 β) = X ρ₁ - X ρ₀) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (ρ₁ ρ₀ : TestFormOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → IsCompact X.boundary.support → boundaryMassOn X.boundary univ < ∞ → (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (ρ₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (ρ₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → cyl N (k + 1) X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) β) = X ρ₁ - X ρ₀ - cyl N k X.boundary β := by
  intro cyl h9
  -- the slice identities (c) and (d) of `cmcdt_lpo_slice_forms`
  obtain ⟨-, -, hc, hd, -⟩ := Submission.cmcdt_lpo_slice_forms
  refine ⟨?_, ?_⟩
  · intro N X β ρ₁ ρ₀ hXc hXm hρ₁ hρ₀
    -- Step 1: `boundaryMassOn X univ = 0` in degree `0`, so `X` is normal
    have hXb : boundaryMassOn X univ < ∞ := by
      show (0 : ℝ≥0∞) < ∞
      exact ENNReal.zero_lt_top
    -- Step 2: (9) for `X` and `dβ`
    obtain ⟨η, hη, hcyl⟩ := h9 N 0 X hXc hXm hXb
      (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 β)
    -- Step 3: `η = ρ₁ − ρ₀` by the slice identity (d); then linearity of `X`
    have hηeq : η = ρ₁ - ρ₀ := by
      apply Subtype.ext
      funext x
      ext v
      rw [hη x v]
      have := hd N β x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hρ₁, hρ₀]
      exact this
    rw [hcyl, hηeq]
    exact map_sub X.toCurrent ρ₁ ρ₀
  · intro N k X β ρ₁ ρ₀ hXc hXm hXbm hbc hbb hρ₁ hρ₀
    -- Steps 4–5: `boundaryMassOn X univ = M(∂X)`; (9) for `X` and `dβ`, and for `∂X` and `β`
    obtain ⟨η, hη, hcyl⟩ := h9 N (k + 1) X hXc hXm hXbm
      (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) β)
    obtain ⟨θ, hθ, hcylb⟩ := h9 N k X.boundary hbc hXbm hbb β
    -- Step 6: `η = ρ₁ − ρ₀ − dθ` by the slice identity (c)
    have hηeq : η = ρ₁ - ρ₀ - exteriorDerivativeTestOn (univ : Set (Euclid N)) k θ := by
      apply Subtype.ext
      funext x
      ext v
      rw [hη x v]
      have := hc N k β θ hθ x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hρ₁, hρ₀]
      exact this
    -- Step 7: `cyl ∂X (β) = ∂X(θ) = X(dθ)`, and linearity of `X`
    rw [hcyl, hcylb, hηeq]
    exact (map_sub X.toCurrent _ _).trans (by rw [map_sub X.toCurrent ρ₁ ρ₀]; rfl)
/-- **Evaluation bound for the cylinder on a pulled-back test form** (parent proof step 7).  By (9),
`cyl(X)(β) = X(θ)` with `θ(x)(v) = ∫₀¹ β(ι(t, x))(e₀, Jv) dt`, so by the mass-support bound it is
enough that `|θ(x)| ≤ bᵏ·a·c` on `spt X`.  For fixed `x` the integrand is the continuous
`f(t) = (β(ι(t, x)) ⌟ e₀) ∘ J`, and `|f(t)| ≤ bᵏ·a·|γ| ≤ bᵏ·a·c` for `t ∈ [0, 1]` by
`cmcdt_lpoh_phi_bound`; the Minkowski bound for coefficient norms gives `|θ(x)| ≤ bᵏ·a·c`. -/
theorem Submission.cmcdt_lpoh_cyl_eval_bound : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → ∀ (N N' k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (a b c : ℝ), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → 0 ≤ b → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, ∃ (γ : Covector (Euclid N') (k + 1)) (D : Euclid (N + 1) →L[ℝ] Euclid N'), (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = γ.compContinuousLinearMap D ∧ covectorEuclideanNorm γ ≤ c ∧ ‖D (EuclideanSpace.single 0 1)‖ ≤ a ∧ ∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ b * ‖v‖) → |cyl N k X β| ≤ b ^ k * a * c * X.mass.toReal := by
  intro hVO hREP hL1 hL2 cyl h9 N N' k X β a b c hXc hXm hXb hb hβ
  -- Mass-support bound: `|X(ψ)| ≤ c'·M(X)` when `|ψ(x)| ≤ c'` on `spt X`.  By (REP) on `univ`,
  -- `X(ψ) = ∫ ξ(x)(ψ(x)) dμ` with `μ(univ) = M(X)`, and the zero region of `X` is `μ`-null by (VO).
  have hMSB : ∀ (ψ : TestFormOn (univ : Set (Euclid N)) k) (c' : ℝ),
      (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c') →
        |X ψ| ≤ c' * X.mass.toReal := by
    intro ψ c' hψ
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hXμ, -⟩ := hREP N k univ X isOpen_univ
      fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hXm
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨by rw [hμ]; exact hXm⟩
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, hω, rfl⟩
      simp only [hVO N k univ X ω (disjoint_sdiff_right.mono_left hω.1), ENNReal.ofReal_zero,
        le_refl]
    have hae : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c' := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with x hx
      rw [Real.norm_eq_abs]
      exact (hξ x _).trans (hψ x ⟨mem_univ x, hx⟩)
    rw [hXμ ψ, ← hμ, ← Real.norm_eq_abs, ← measureReal_def]
    exact norm_integral_le_of_norm_le_const hae
  -- Minkowski bound for the coefficient norm: if `α(v) = ∫₀¹ f(t)(v) dt` with `f` continuous and
  -- `|f(t)| ≤ C` on `[0, 1]`, Cauchy–Schwarz gives `|α|² = ∫₀¹ ⟨α, f(t)⟩ dt ≤ |α|·C`, so `|α| ≤ C`.
  have hMink : ∀ (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (C : ℝ),
      Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) →
        (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ C) → covectorEuclideanNorm α ≤ C := by
    intro α f C hf hα hfC
    let s : Finset (Fin k → Fin N) := Finset.univ.filter fun I => StrictMono I
    let e : (Fin k → Fin N) → Fin k → Euclid N := fun I i => EuclideanSpace.basisFun (Fin N) ℝ (I i)
    have hnorm : ∀ γ : Covector (Euclid N) k,
        covectorEuclideanNorm γ = Real.sqrt (∑ I ∈ s, γ (e I) ^ 2) := by
      intro γ
      rw [covectorEuclideanNorm, Finset.sum_filter]
    have hcont : ∀ v : Fin k → Euclid N, Continuous fun t => f t v :=
      fun v => (continuous_eval_const v).comp hf
    have hC : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hfC 0 ⟨le_rfl, zero_le_one⟩)
    have hcont' : ∀ I, Continuous fun t => α (e I) * f t (e I) :=
      fun I => continuous_const.mul (hcont (e I))
    have hsq : covectorEuclideanNorm α ^ 2 = ∫ t in (0 : ℝ)..1, ∑ I ∈ s, α (e I) * f t (e I) := by
      rw [intervalIntegral.integral_finsetSum fun I _ => (hcont' I).intervalIntegrable 0 1, hnorm,
        Real.sq_sqrt (Finset.sum_nonneg fun I _ => sq_nonneg _)]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [intervalIntegral.integral_const_mul, ← hα, sq]
    have hle : covectorEuclideanNorm α ^ 2 ≤ covectorEuclideanNorm α * C := by
      rw [hsq]
      calc ∫ t in (0 : ℝ)..1, ∑ I ∈ s, α (e I) * f t (e I)
          ≤ ∫ t in (0 : ℝ)..1, covectorEuclideanNorm α * C := by
            refine intervalIntegral.integral_mono_on zero_le_one
              ((continuous_finsetSum _ fun I _ => hcont' I).intervalIntegrable 0 1)
              intervalIntegrable_const fun t ht => ?_
            calc ∑ I ∈ s, α (e I) * f t (e I)
                ≤ Real.sqrt (∑ I ∈ s, α (e I) ^ 2) * Real.sqrt (∑ I ∈ s, f t (e I) ^ 2) :=
                  Real.sum_mul_le_sqrt_mul_sqrt s _ _
              _ = covectorEuclideanNorm α * covectorEuclideanNorm (f t) := by rw [hnorm, hnorm]
              _ ≤ covectorEuclideanNorm α * C :=
                  mul_le_mul_of_nonneg_left (hfC t ht) (covectorEuclideanNorm_nonneg _)
        _ = covectorEuclideanNorm α * C := by simp
    rcases (covectorEuclideanNorm_nonneg α).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact hC
    · exact le_of_mul_le_mul_left (by rwa [sq] at hle) hpos
  -- Step 1: the slice `θ` with `cyl(X)(β) = X(θ)`; step 2: reduce to `|θ(x)| ≤ bᵏ·a·c` on `spt X`
  obtain ⟨θ, hθ, hcyl⟩ := h9 N k X hXc hXm hXb β
  rw [hcyl]
  refine hMSB θ (b ^ k * a * c) fun x hx => ?_
  -- Step 3: the continuous integrand `f(t) = (β(ι(t, x)) ⌟ e₀) ∘ J`
  let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro r v
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jl
  let f : ℝ → Covector (Euclid N) k := fun t =>
    (((β : DifferentialForm (Euclid (N + 1)) (k + 1))
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))).curryLeft
        (EuclideanSpace.single 0 1)).compContinuousLinearMap J
  have hf : Continuous f := by
    have hι : Continuous fun t : ℝ =>
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) := by
      fun_prop
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM J).continuous.comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single 0 1 : Euclid (N + 1))).continuous.comp
        ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid (N + 1)) (F := ℝ)
          (n := k)).continuous.comp (β.property.1.1.continuous.comp hι)))
  have hfv : ∀ (t : ℝ) (v : Fin k → Euclid N), f t v =
      (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) :=
    fun _ _ => rfl
  -- Steps 4–5: `|f(t)| ≤ bᵏ·a·c` on `[0, 1]` by `cmcdt_lpoh_phi_bound`, then the Minkowski bound
  refine hMink ((θ : DifferentialForm (Euclid N) k) x) f (b ^ k * a * c) hf
    (fun v => by rw [hθ x v]; simp only [hfv]) fun t ht => ?_
  obtain ⟨γ, D, hβeq, hγ, hDe, hDJ⟩ := hβ x hx t ht
  have ha : 0 ≤ a := (norm_nonneg _).trans hDe
  calc covectorEuclideanNorm (f t) ≤ b ^ k * a * covectorEuclideanNorm γ :=
        Submission.cmcdt_lpoh_phi_bound hL1 hL2 N N' k γ D (f t) a b hb hDe hDJ
          fun v => by rw [hfv, hβeq]
    _ ≤ b ^ k * a * c := mul_le_mul_of_nonneg_left hγ (mul_nonneg (pow_nonneg hb k) ha)
/-- **Lipschitz homotopy formula** (Simon 6.2.25 for the affine homotopy 6.2.26, with the
Lipschitz push-forward of 6.2.29), conjuncts (10) and (11): for `Λ`-Lipschitz `F, G` and an
`L`-Lipschitz `H` with `H(t, x) = F(x) + t(G(x) − F(x))` on `[0, 1] × spt X`,
`G_#X − F_#X = ∂H_#(cyl X)` in degree `0`, and `G_#X − F_#X − H_#(cyl ∂X) = ∂H_#(cyl X)` in
positive degree.  For a test form `ω`, `Submission.cmcdt_lpoh_pullback_limits` (with
`K = spt X`) gives forms `β_j` whose end slices `ρ_{1,j}, ρ_{0,j}` give `X(ρ_{1,j}) → G_#X(ω)`,
`X(ρ_{0,j}) → F_#X(ω)`, while `cyl(X)(dβ_j) → H_#(cyl X)(dω)` and
`cyl(∂X)(β_j) → H_#(cyl ∂X)(ω)`; `Submission.cmcdt_lpoh_cyl_identity` gives
`cyl(X)(dβ_j) = X(ρ_{1,j}) − X(ρ_{0,j}) [− cyl(∂X)(β_j)]`, and limits are unique.  `∂X` is
normal: `spt ∂X ⊆ spt X` because `d` does not enlarge supports, and `∂∂X = 0`. -/
theorem Submission.cmcdt_lpoh_homotopy_formula : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) := by
  intro _hVO _hREP lpush cyl hPA h7 h9
  have hID := Submission.cmcdt_lpoh_cyl_identity cyl h9
  refine ⟨?_, ?_⟩
  · intro N N' Λ L F G H X hF hG hH hXc hXm hHX
    -- in degree `0`, `M(∂X) = 0` by convention
    have hXb : boundaryMassOn X univ < ∞ := by
      show (0 : ℝ≥0∞) < ∞
      exact ENNReal.zero_lt_top
    obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N 0 X hXc hXm hXb
    apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨β, ρ₁, ρ₀, hρ₁, hρ₀, hlimX, -, hlimY', -⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' 0 Λ L F G H X.support ω hF hG hH hXc
        hHX
    have h1 := hlimY' (cyl N 0 X) hc1 hc2 hc3 hc4
    obtain ⟨h2, h3⟩ := hlimX X hXc hXm hXb subset_rfl
    have h4 : Tendsto
        (fun j => cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 (β j)))
        atTop (𝓝 (lpush N N' 0 G X ω - lpush N N' 0 F X ω)) :=
      (h2.sub h3).congr fun j => (hID.1 N X (β j) (ρ₁ j) (ρ₀ j) hXc hXm (hρ₁ j) (hρ₀ j)).symm
    exact tendsto_nhds_unique h4 h1
  · intro N N' k Λ L F G H X hF hG hH hXc hXm hXbm hHX
    have hXb : boundaryMassOn X univ < ∞ := hXbm
    -- `spt ∂X ⊆ spt X`: `d` does not enlarge supports
    have hSBX : X.boundary.support ⊆ X.support := by
      intro x hx
      simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_univ, true_and] at hx ⊢
      intro hxz
      apply hx
      obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxz
      exact ⟨W, ⟨hWo, hWc, hWU, fun ω hω => hWv (exteriorDerivativeTestOn univ k ω)
        ((tsupport_exteriorDerivative_subset _).trans hω)⟩, hxW⟩
    have hbc : IsCompact X.boundary.support :=
      hXc.of_isClosed_subset (isClosed_univ.sdiff X.boundary.isOpen_zeroRegion) hSBX
    -- `M(∂∂X) = 0`
    have hbb : boundaryMassOn X.boundary univ < ∞ := by
      cases k with
      | zero =>
        show (0 : ℝ≥0∞) < ∞
        exact ENNReal.zero_lt_top
      | succ k' =>
        show X.boundary.boundary.massOn univ < ∞
        rw [GeometricCurrentOn.boundary_boundary]
        refine lt_of_le_of_lt ?_ ENNReal.zero_lt_top
        apply sSup_le
        rintro _ ⟨ω', -, rfl⟩
        simp
    obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N (k + 1) X hXc hXm hXb
    obtain ⟨hd1, hd2, hd3, hd4⟩ := h7 N k X.boundary hbc hXbm hbb
    have hd4' : (cyl N k X.boundary).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1,
        ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      intro y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hd4 hy
      exact ⟨t, ht, x, hSBX hx, rfl⟩
    apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨β, ρ₁, ρ₀, hρ₁, hρ₀, hlimX, hlimY, hlimY', -⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' (k + 1) Λ L F G H X.support ω hF hG hH
        hXc hHX
    have h1 := hlimY' (cyl N (k + 1) X) hc1 hc2 hc3 hc4
    have h5 := hlimY (cyl N k X.boundary) hd1 hd2 hd3 hd4'
    obtain ⟨h2, h3⟩ := hlimX X hXc hXm hXb subset_rfl
    have h4 : Tendsto (fun j => cyl N (k + 1) X
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) (β j)))
        atTop (𝓝 (lpush N N' (k + 1) G X ω - lpush N N' (k + 1) F X ω -
          lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) ω)) :=
      ((h2.sub h3).sub h5).congr fun j => (hID.2 N k X (β j) (ρ₁ j) (ρ₀ j) hXc hXm hXbm hbc hbb
        (hρ₁ j) (hρ₀ j)).symm
    exact tendsto_nhds_unique h4 h1

/-- Mass bound for the Lipschitz homotopy, conjunct (12): `M(lpush(H, cyl X)) ≤ δ (2Λ)ᵏ M(X)`.
For an admissible `ω`, `cmcdt_lpoh_pullback_limits` (with `K = spt X`) gives forms `βⱼ` with
`cyl(X)(βⱼ) → lpush(H, cyl X)(ω)` and `βⱼ(ι(t, x)) = ω(p) ∘ D`, `‖De₀‖ ≤ δ + 2Λ/(j + 1)`,
`‖D(Jv)‖ ≤ Λ‖v‖`; so `cmcdt_lpoh_cyl_eval_bound` gives `|cyl(X)(βⱼ)| ≤ Λᵏ (δ + 2Λ/(j + 1)) M(X)`.
Letting `j → ∞`, `|lpush(H, cyl X)(ω)| ≤ Λᵏ δ M(X)`; taking the supremum over admissible `ω`
(using `Λᵏ ≤ (2Λ)ᵏ`, and `ofReal δ = 0` if `δ < 0`) gives the claim. -/
theorem Submission.cmcdt_lpoh_mass_bound : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP hLB lpush cyl hPA h7 h9 N N' k Λ L F G H X δ hF hG hH hXc hXm hXb hHX hδ
  -- `cyl X` has compact support in `[0, 1] × spt X`, finite mass and finite boundary mass.
  obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N k X hXc hXm hXb
  -- Key estimate: `|lpush(H, cyl X)(ω)| ≤ Λᵏ δ M(X)` for every admissible `ω`.
  have key : ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) ≤ 1) →
      |lpush (N + 1) N' (k + 1) H (cyl N k X) ω| ≤ (Λ : ℝ) ^ k * δ * X.mass.toReal := by
    intro ω hω
    obtain ⟨β, -, -, -, -, -, hlimY, -, hβ⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' (k + 1) Λ L F G H X.support ω hF hG hH
        hXc hHX
    have hlim := hlimY (cyl N k X) hc1 hc2 hc3 hc4
    have hbound : ∀ j : ℕ, |cyl N k X (β j)| ≤
        (Λ : ℝ) ^ k * (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * 1 * X.mass.toReal := by
      intro j
      refine Submission.cmcdt_lpoh_cyl_eval_bound hVO hREP hLB.1 hLB.2.1 cyl h9 N N' k X (β j)
        (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) Λ 1 hXc hXm hXb Λ.coe_nonneg ?_
      intro x hx t ht
      obtain ⟨p, D, hpD, hDe, hDJ⟩ := hβ j x hx t ht
      exact ⟨(ω : DifferentialForm (Euclid N') (k + 1)) p, D, hpD, hω p,
        hDe.trans (by linarith [hδ x hx]), hDJ⟩
    have hl1 : Tendsto (fun j => |cyl N k X (β j)|) atTop
        (𝓝 |lpush (N + 1) N' (k + 1) H (cyl N k X) ω|) := hlim.abs
    have hsmall : Tendsto (fun j : ℕ => 2 * (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (Λ : ℝ))
      rw [mul_zero] at h
      refine h.congr fun j => ?_
      rw [mul_one_div]
    have hl2 : Tendsto
        (fun j : ℕ => (Λ : ℝ) ^ k * (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * 1 * X.mass.toReal)
        atTop (𝓝 ((Λ : ℝ) ^ k * (δ + 0) * 1 * X.mass.toReal)) :=
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add hsmall)).mul tendsto_const_nhds).mul
        tendsto_const_nhds
    simpa using le_of_tendsto_of_tendsto' hl1 hl2 hbound
  -- Supremum over the admissible forms `ω` defining `M(lpush(H, cyl X))`.
  apply sSup_le
  rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
  dsimp only
  have h := key ω hω
  have hM : X.mass ≠ ∞ := hXm.ne
  set T := lpush (N + 1) N' (k + 1) H (cyl N k X)
  rcases le_or_gt 0 δ with hδ0 | hδ0
  · calc ENNReal.ofReal (T ω) ≤ ENNReal.ofReal (δ * (2 * (Λ : ℝ)) ^ k * X.mass.toReal) := by
          apply ENNReal.ofReal_le_ofReal
          have hΛ : (Λ : ℝ) ^ k ≤ (2 * (Λ : ℝ)) ^ k :=
            pow_le_pow_left₀ Λ.coe_nonneg (by linarith [Λ.coe_nonneg]) k
          calc T ω ≤ |T ω| := le_abs_self _
            _ ≤ (Λ : ℝ) ^ k * δ * X.mass.toReal := h
            _ ≤ (2 * (Λ : ℝ)) ^ k * δ * X.mass.toReal := by gcongr
            _ = δ * (2 * (Λ : ℝ)) ^ k * X.mass.toReal := by ring
      _ = ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hδ0, ENNReal.ofReal_toReal hM,
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp
  · -- `δ < 0`: then `T ω ≤ 0`, so `ofReal (T ω) = 0`.
    have hle : T ω ≤ 0 := by
      have h0 : (Λ : ℝ) ^ k * δ * X.mass.toReal ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ0.le) ENNReal.toReal_nonneg
      linarith [le_abs_self (T ω)]
    rw [ENNReal.ofReal_of_nonpos hle]
    exact bot_le

/-- **Homotopy formula for Lipschitz maps** (Simon 6.2.25–6.2.27, with 6.2.29): for `lpush`, `cyl`
with (PA), (7) and (9), `Λ`-Lipschitz `F`, `G` and an `L`-Lipschitz `H` with
`H(t, x) = F x + t (G x − F x)` on `[0, 1] × spt X`, we have
`G_# X − F_# X − H_#([[0, 1]] × ∂X) = ∂ H_#([[0, 1]] × X)` (no middle term in degree `0`), and
`M(H_#([[0, 1]] × X)) ≤ δ (2Λ)^k M(X)` if `|F − G| ≤ δ` on `spt X`.  The two identities are
`Submission.cmcdt_lpoh_homotopy_formula` and the mass bound is `Submission.cmcdt_lpoh_mass_bound`;
both pass to the limit along the smooth affine homotopies `H_j` between mollifications of `F`, `G`. -/
theorem Submission.cmcdt_lpo_lipschitz_homotopy : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP hLB lpush cyl hPA h7 h9
  obtain ⟨h10, h11⟩ := Submission.cmcdt_lpoh_homotopy_formula hVO hREP lpush cyl hPA h7 h9
  exact ⟨h10, h11, Submission.cmcdt_lpoh_mass_bound hVO hREP hLB lpush cyl hPA h7 h9⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
