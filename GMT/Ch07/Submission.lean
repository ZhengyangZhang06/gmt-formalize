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

/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion
/-- **Simon Ch. 6, 2.4–2.5 and 3.2(1)**, algebra of integer multiplicity currents.  (a) The zero
current is integer multiplicity (empty carrier).  (b) If `A = pB + qC` with `p, q ∈ ℤ`, then
`M_W(A) ≤ |p| M_W(B) + |q| M_W(C)`: `−ω` is admissible with `ω`, so `|X(ω)| ≤ M_W(X)`.  (c) If
differences of integer multiplicity currents in an open `U` are integer multiplicity, then every
finite integer combination `Y = Σᵢ mᵢSᵢ` of integer multiplicity currents is integer multiplicity
(`A + B = A − (0 − B)`), and `M_W(Y) ≤ Σᵢ |mᵢ| M_W(Sᵢ)`. -/
theorem Submission.cbr_cc_current_algebra : (∀ (P n : ℕ) (U : Set (Euclid P)), IsIntegerMultiplicity (0 : GeometricCurrentOn U n)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B C : GeometricCurrentOn U n) (p q : ℤ), (∀ ω : TestFormOn U n, A ω = (p : ℝ) * B ω + (q : ℝ) * C ω) → ∀ W : Set (Euclid P), A.massOn W ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W) ∧ ((∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (ι : Type) (F : Finset ι) (S : ι → GeometricCurrentOn U n) (m : ι → ℤ), IsOpen U → (∀ i ∈ F, IsIntegerMultiplicity (S i)) → ∃ Y : GeometricCurrentOn U n, IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U n, Y ω = ∑ i ∈ F, (m i : ℝ) * S i ω) ∧ ∀ W : Set (Euclid P), Y.massOn W ≤ ∑ i ∈ F, ((m i).natAbs : ℝ≥0∞) * (S i).massOn W) := by
  -- (a): the representation with empty carrier, zero multiplicity and zero orientation
  have hzero : ∀ (P n : ℕ) (U : Set (Euclid P)),
      IsIntegerMultiplicity (0 : GeometricCurrentOn U n) := by
    intro P n U
    refine ⟨{ carrier := ∅
              mult := fun _ => 0
              orient := fun _ => 0
              measurableSet_carrier := MeasurableSet.empty
              carrier_subset := empty_subset U
              rectifiable :=
                Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
              measurable_mult := measurable_const
              mult_pos := fun x hx => by simp at hx
              locallyIntegrable_mult := fun K _ _ => by simp
              aestronglyMeasurable_orient := aestronglyMeasurable_const
              orients := by simp }, ?_⟩
    intro ω
    simp [IMRep.action]
  -- `|X(ω)| ≤ M_W(X)` for admissible `ω`, since `−ω` is admissible as well
  have habs : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n)
      (W : Set (Euclid P)) (ω : TestFormOn U n), ω ∈ massAdmissibleOn U n W →
      ENNReal.ofReal |X ω| ≤ X.massOn W := by
    intro P n U X W ω hω
    rcases le_total 0 (X ω) with h | h
    · rw [abs_of_nonneg h]
      exact X.le_massOn hω
    · have hneg : -ω ∈ massAdmissibleOn U n W := by
        refine ⟨?_, fun x => ?_⟩
        · rw [Submodule.coe_neg, tsupport_neg]
          exact hω.1
        · rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
          exact hω.2 x
      rw [abs_of_nonpos h, ← map_neg X.toCurrent ω]
      exact X.le_massOn hneg
  -- one term `|k| |X(ω)| ≤ |k| M_W(X)` of an integer combination
  have hterm : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n) (k : ℤ)
      (W : Set (Euclid P)) (ω : TestFormOn U n), ω ∈ massAdmissibleOn U n W →
      ENNReal.ofReal (|(k : ℝ)| * |X ω|) ≤ (k.natAbs : ℝ≥0∞) * X.massOn W := by
    intro P n U X k W ω hω
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Int.cast_abs, ← Nat.cast_natAbs,
      ENNReal.ofReal_natCast]
    exact mul_le_mul' le_rfl (habs P n U X W ω hω)
  -- (b)
  have hmass : ∀ (P n : ℕ) (U : Set (Euclid P)) (A B C : GeometricCurrentOn U n) (p q : ℤ),
      (∀ ω : TestFormOn U n, A ω = (p : ℝ) * B ω + (q : ℝ) * C ω) → ∀ W : Set (Euclid P),
      A.massOn W ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W := by
    intro P n U A B C p q hA W
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    calc ENNReal.ofReal (A ω)
        ≤ ENNReal.ofReal (|(p : ℝ)| * |B ω| + |(q : ℝ)| * |C ω|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hA ω, ← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
      _ = ENNReal.ofReal (|(p : ℝ)| * |B ω|) + ENNReal.ofReal (|(q : ℝ)| * |C ω|) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ (p.natAbs : ℝ≥0∞) * B.massOn W + (q.natAbs : ℝ≥0∞) * C.massOn W :=
          add_le_add (hterm P n U B p W ω hω) (hterm P n U C q W ω hω)
  refine ⟨hzero, hmass, ?_⟩
  -- (c)
  intro hsub P n U ι F S m hU hS
  classical
  have hsubapp : ∀ (A B : GeometricCurrentOn U n) (ω : TestFormOn U n),
      (A - B) ω = A ω - B ω := fun A B ω => rfl
  -- `A − (0 − B)` is integer multiplicity, with values `A(ω) + B(ω)`
  have hadd : ∀ A B : GeometricCurrentOn U n, IsIntegerMultiplicity A →
      IsIntegerMultiplicity B →
      IsIntegerMultiplicity (A - (0 - B)) ∧ ∀ ω, (A - (0 - B)) ω = A ω + B ω := by
    intro A B hA hB
    refine ⟨hsub P n U A (0 - B) hU hA (hsub P n U 0 B hU (hzero P n U) hB), fun ω => ?_⟩
    rw [hsubapp, hsubapp, GeometricCurrentOn.zero_apply]
    ring
  -- natural multiples `k X = X + ⋯ + X`
  have hnat : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X → ∀ k : ℕ,
      ∃ V : GeometricCurrentOn U n, IsIntegerMultiplicity V ∧ ∀ ω, V ω = (k : ℝ) * X ω := by
    intro X hX k
    induction k with
    | zero => exact ⟨0, hzero P n U, fun ω => by simp⟩
    | succ k ih =>
      obtain ⟨V, hV, hVω⟩ := ih
      obtain ⟨hV', hV'ω⟩ := hadd V X hV hX
      refine ⟨V - (0 - X), hV', fun ω => ?_⟩
      rw [hV'ω, hVω]
      push_cast
      ring
  -- integer multiples, `(−k) X = 0 − k X`
  have hint : ∀ X : GeometricCurrentOn U n, IsIntegerMultiplicity X → ∀ k : ℤ,
      ∃ V : GeometricCurrentOn U n, IsIntegerMultiplicity V ∧ ∀ ω, V ω = (k : ℝ) * X ω := by
    intro X hX k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · obtain ⟨V, hV, hVω⟩ := hnat X hX j
      exact ⟨V, hV, fun ω => by rw [hVω, Int.cast_natCast]⟩
    · obtain ⟨V, hV, hVω⟩ := hnat X hX j
      refine ⟨0 - V, hsub P n U 0 V hU (hzero P n U) hV, fun ω => ?_⟩
      rw [hsubapp, GeometricCurrentOn.zero_apply, hVω, Int.cast_neg, Int.cast_natCast]
      ring
  -- finite integer combinations, by induction on the index set
  have hsum : ∀ G : Finset ι, (∀ i ∈ G, IsIntegerMultiplicity (S i)) →
      ∃ Y : GeometricCurrentOn U n, IsIntegerMultiplicity Y ∧
        ∀ ω, Y ω = ∑ i ∈ G, (m i : ℝ) * S i ω := by
    intro G
    induction G using Finset.induction_on with
    | empty => exact fun _ => ⟨0, hzero P n U, fun ω => by simp⟩
    | insert j G hj ih =>
      intro hG
      obtain ⟨Y, hY, hYω⟩ := ih fun i hi => hG i (Finset.mem_insert_of_mem hi)
      obtain ⟨V, hV, hVω⟩ := hint (S j) (hG j (Finset.mem_insert_self j G)) (m j)
      obtain ⟨hY', hY'ω⟩ := hadd Y V hY hV
      refine ⟨Y - (0 - V), hY', fun ω => ?_⟩
      rw [hY'ω, hYω, hVω, Finset.sum_insert hj]
      ring
  obtain ⟨Y, hY, hYω⟩ := hsum F hS
  refine ⟨Y, hY, hYω, fun W => ?_⟩
  -- the mass bound, from `Y(ω) ≤ Σᵢ |mᵢ| |Sᵢ(ω)|` for admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (Y ω)
      ≤ ENNReal.ofReal (∑ i ∈ F, |(m i : ℝ)| * |S i ω|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hYω]
        exact Finset.sum_le_sum fun i _ => by rw [← abs_mul]; exact le_abs_self _
    _ = ∑ i ∈ F, ENNReal.ofReal (|(m i : ℝ)| * |S i ω|) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity
    _ ≤ ∑ i ∈ F, ((m i).natAbs : ℝ≥0∞) * (S i).massOn W :=
        Finset.sum_le_sum fun i _ => hterm P n U (S i) (m i) W ω hω
/-- **`H¹` on a line** (Simon Ch. 6, 2.2 and 2.4).  For a unit vector `τ`, `φ(u) = a + uτ` is an
isometry `ℝ → ℝᴾ` (`|φ(u) − φ(v)| = |u − v| |τ|`), hence a closed and so measurable embedding, and
`φ(A)` is Borel for Borel `A`.  On `ℝ`, `μHE[1]` is Lebesgue measure, and `μHE[1]` is preserved by
isometries: `H¹(φ(A)) = H¹(A) = L¹(A)`, and `φ_#L¹ = H¹⌞range φ` gives `H¹⌞φ(A) = φ_#(L¹⌞A)`, so
`∫_{φ(A)} h dH¹ = ∫_A h(a + uτ) du` for every `h` (change of variables along an embedding). -/
theorem Submission.cbr_cc_seg_line_hausdorff : ∀ (P : ℕ) (a τ : Euclid P), ‖τ‖ = 1 → ∀ A : Set ℝ, MeasurableSet A → MeasurableSet ((fun u : ℝ => a + u • τ) '' A) ∧ μHE[1] ((fun u : ℝ => a + u • τ) '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in (fun u : ℝ => a + u • τ) '' A, h x ∂μHE[1] = ∫ u in A, h (a + u • τ) := by
  intro P a τ hτ A hA
  set φ : ℝ → Euclid P := fun u => a + u • τ with hφ
  -- Step 1: `φ` is an isometry, `|φ(u) − φ(v)| = |(u − v)τ| = |u − v|`
  have hiso : Isometry φ := by
    refine Isometry.of_dist_eq fun u v => ?_
    rw [hφ, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hτ,
      mul_one]
  -- Step 2: hence a closed, so measurable, embedding, and `φ(A)` is Borel
  have hemb : MeasurableEmbedding φ := hiso.isClosedEmbedding.measurableEmbedding
  have hmeas : MeasurableSet (φ '' A) := hemb.measurableSet_image.mpr hA
  -- Step 3: on `ℝ`, `μHE[1]` is Lebesgue measure
  have hvol : (μHE[1] : Measure ℝ) = volume := by
    simpa only [Module.finrank_self] using
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  refine ⟨hmeas, ?_, fun h => ?_⟩
  -- Step 4: isometry invariance, `H¹(φ(A)) = H¹(A) = L¹(A)`
  · rw [hiso.euclideanHausdorffMeasure_image, hvol]
  -- Step 5: `H¹⌞φ(A) = (H¹⌞range φ)⌞φ(A) = (φ_#H¹)⌞φ(A) = φ_#(H¹⌞A) = φ_#(L¹⌞A)`
  · have hrestr : (μHE[1] : Measure (Euclid P)).restrict (φ '' A) = (volume.restrict A).map φ :=
      calc (μHE[1] : Measure (Euclid P)).restrict (φ '' A)
          = ((μHE[1] : Measure (Euclid P)).restrict (range φ)).restrict (φ '' A) := by
            rw [Measure.restrict_restrict hmeas, inter_eq_left.mpr (image_subset_range φ A)]
        _ = ((μHE[1] : Measure ℝ).map φ).restrict (φ '' A) := by
            rw [hiso.map_euclideanHausdorffMeasure]
        _ = (volume.restrict A).map φ := by
            rw [hemb.restrict_map, hemb.injective.preimage_image, hvol]
    -- Step 6: change of variables along the measurable embedding `φ`, for every `h`
    rw [hrestr, hemb.integral_map]

/-- **Approximate tangent line of an open segment** (Simon Ch. 3, 1.4).  If `|τ| = 1`, the open
segment `I = {a + uτ : 0 < u < ℓ}` has approximate tangent space `span{τ}` at every point
`x = a + s₀τ` of `I`.  Let `f ∈ C_c` vanish outside `B̄_ρ(0)` and `0 < r < min(s₀, ℓ − s₀)/ρ`.
Then `η_{x,r}(I) ⊆ span{τ}`, and every `y = cτ` with `f(y) ≠ 0` equals `η_{x,r}(a + (s₀ + rc)τ)`
with `s₀ + rc ∈ (0, ℓ)`.  So `∫_{η_{x,r}(I)} f dH¹ = ∫_{span{τ}} f dH¹` for all small `r > 0`. -/
theorem Submission.cbr_cc_seg_open_segment_tangent : ∀ (P : ℕ) (a τ : Euclid P) (ℓ : ℝ), ‖τ‖ = 1 → ∀ x ∈ (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ, HasApproximateTangentSpaceAt 1 ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) x (Submodule.span ℝ {τ}) := by
  intro P a τ ℓ hτ x hx
  -- Step 1: `x = a + s₀τ` with `0 < s₀ < ℓ`, and `dim span{τ} = 1` since `τ ≠ 0`
  obtain ⟨s₀, ⟨hs₀, hs₀ℓ⟩, rfl⟩ := hx
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  refine ⟨finrank_span_singleton hτ0, fun f => ?_⟩
  -- Step 2: `f y ≠ 0` implies `|y| ≤ ρ`
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
    f.hasCompactSupport.isCompact.isBounded
  set ρ := max R₀ 1
  have hρpos : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfρ : ∀ y, f y ≠ 0 → ‖y‖ ≤ ρ := by
    intro y hy
    have h := hR₀ (subset_tsupport f hy)
    rw [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  -- Step 3: `δ = min(s₀, ℓ - s₀)` and `0 < r < δ/ρ`
  set δ := min s₀ (ℓ - s₀)
  have hδpos : 0 < δ := lt_min hs₀ (sub_pos.mpr hs₀ℓ)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδpos hρpos)] with r hr
  obtain ⟨hr0, hrδ⟩ := hr
  have hrρ : r * ρ < δ := by rwa [lt_div_iff₀ hρpos] at hrδ
  -- Step 4: `η_r(a + uτ) = (r⁻¹(u - s₀))τ`, so `η_r(I) ⊆ span{τ}`
  have hη : ∀ u : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (a + s₀ • τ) r (a + u • τ) =
      (r⁻¹ * (u - s₀)) • τ := by
    intro u
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, mul_smul, sub_smul, add_sub_add_left_eq_sub]
  have hsub : Poincare.SimonGMT.Chapter03.blowUpMap (a + s₀ • τ) r ''
      ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) ⊆ (Submodule.span ℝ {τ} : Set (Euclid P)) := by
    rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨_, (hη u).symm⟩
  -- Step 6: `span{τ}` is closed, so the two integrals agree once `f = 0` on `span{τ} \ η_r(I)`
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (Submodule.closed_of_finiteDimensional _).measurableSet.nullMeasurableSet hsub
    (Eventually.of_forall fun y hy => ?_)
  -- Step 5: if `y = cτ` and `f y ≠ 0`, then `y = η_r(a + (s₀ + rc)τ)` with `s₀ + rc ∈ (0, ℓ)`
  by_contra hfy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy.1
  have hc : |c| ≤ ρ := by
    have h := hfρ _ hfy
    rwa [norm_smul, hτ, mul_one, Real.norm_eq_abs] at h
  have hrc : |r * c| < δ := by
    rw [abs_mul, abs_of_pos hr0]
    exact (mul_le_mul_of_nonneg_left hc hr0.le).trans_lt hrρ
  have hδs₀ : δ ≤ s₀ := min_le_left _ _
  have hδℓ : δ ≤ ℓ - s₀ := min_le_right _ _
  obtain ⟨hrc₁, hrc₂⟩ := abs_lt.mp hrc
  refine hy.2 ⟨a + (s₀ + r * c) • τ, ⟨s₀ + r * c, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
  rw [hη, add_sub_cancel_left, inv_mul_cancel_left₀ hr0.ne']

/-- **Fundamental theorem of calculus for a `0`-form along a segment** (Simon Ch. 6, 2.3: Stokes'
theorem `∂T(ω) = T(dω)` in dimension one).  For a smooth `0`-form `g` on `ℝᴾ`, `a, v ∈ ℝᴾ` and
`ℓ ≥ 0`, `∫_{(0,ℓ)} dg(a + uv)(v) du = g(a + ℓv)⟨⟩ − g(a)⟨⟩`.  The function `ĝ = g(·)⟨⟩` is
smooth, and `dg(y)(v) = Dĝ(y)v` since `removeNth 0` of a `1`-tuple is the empty tuple `⟨⟩`.  By
the chain rule `u ↦ ĝ(a + uv)` has the continuous derivative `Dĝ(a + uv)v`, and the FTC on
`[0, ℓ]` concludes (`(0, ℓ)` and `(0, ℓ]` differ by a null set). -/
theorem Submission.cbr_cc_seg_zero_form_ftc : ∀ (P : ℕ) (g : DifferentialForm (Euclid P) 0), IsSmoothForm g → ∀ (a v : Euclid P) (ℓ : ℝ), 0 ≤ ℓ → ∫ u in Ioo 0 ℓ, exteriorDerivative g (a + u • v) (fun _ => v) = g (a + ℓ • v) (fun i => i.elim0) - g a (fun i => i.elim0) := by
  intro P g hg a v ℓ hℓ
  set e : Fin 0 → Euclid P := fun i => i.elim0
  -- (1) `ĝ = g(·)⟨⟩ = ev_⟨⟩ ∘ g` is smooth
  have hĝ := (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ e).contDiff.comp hg
  have hĝd : Differentiable ℝ (fun y => g y e) := hĝ.differentiable (by simp)
  -- (2) `dg(y)(v) = Dĝ(y)v`: `removeNth 0` of a `1`-tuple is the empty tuple
  have hd : ∀ y, exteriorDerivative g y (fun _ => v) = fderiv ℝ (fun z => g z e) y v := by
    intro y
    rw [exteriorDerivative_apply ((hg.differentiable (by simp)) y), Fin.sum_univ_one]
    have hrm : (Fin.removeNth (0 : Fin 1) fun _ : Fin 1 => v) = e := Subsingleton.elim _ _
    simp [hrm]
  -- (3) chain rule: `d/du ĝ(a + uv) = Dĝ(a + uv)v`
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u => g (a + u • v) e)
      (fderiv ℝ (fun z => g z e) (a + u • v) v) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => a + u • v) v u := by
      simpa using ((hasDerivAt_id u).smul_const v).const_add a
    exact (hĝd (a + u • v)).hasFDerivAt.comp_hasDerivAt u h1
  -- (4) the derivative is continuous in `u`, hence interval integrable
  have hcont : Continuous (fun u : ℝ => fderiv ℝ (fun z => g z e) (a + u • v) v) :=
    ((hĝ.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  -- (5) `∫_{(0,ℓ)} = ∫_0^ℓ` for `ℓ ≥ 0`, then the FTC
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hℓ]
  simp only [hd]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 ℓ), zero_smul, add_zero]
/-- **The oriented open segment as an integer multiplicity triple** (Simon 6.2.2, 6.3.1).  For a
unit vector `τ` and `ℓ > 0`, the triple `R = (I, 1, ζ₀)` with `I = φ((0, ℓ))`, `φ(u) = a + uτ`, and
`ζ₀ = τ` (`⟨α, ζ₀⟩ = α(τ)`) is an `IMRep` of degree `1` in `ℝᴾ`.  `I` is Borel with `H¹(I) = ℓ`
and `∫_I h dH¹ = ∫₀^ℓ h(a + uτ) du` (`line_hausdorff`); it lies in the range of the `1`-Lipschitz
map `w ↦ a + w₀τ`, so it is countably `1`-rectifiable; `ζ₀` orients `span{τ}`, the approximate
tangent space of `I` at each of its points (`open_segment_tangent`).  Hence `I ⊆ [a, a + ℓτ]`,
`μ_R(ℝᴾ) = H¹(I) < ∞`, and `R(ω) = ∫_I ω(x)(τ) dH¹(x) = ∫₀^ℓ ω(a + uτ)(τ) du`. -/
theorem Submission.cbr_cc_seg_segment_imrep : ∀ (P : ℕ) (a τ : Euclid P) (ℓ : ℝ), ‖τ‖ = 1 → 0 < ℓ → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.carrier ⊆ segment ℝ a (a + ℓ • τ) ∧ R.measure univ < ∞ ∧ ∀ ω : DifferentialForm (Euclid P) 1, R.action ω = ∫ u in Ioo 0 ℓ, ω (a + u • τ) (fun _ => τ) := by
  intro P a τ ℓ hτ hℓ
  -- Step 1: `I = φ((0, ℓ))` is Borel, `H¹(I) = ℓ < ∞`, and `∫_I h dH¹ = ∫₀^ℓ h ∘ φ`
  obtain ⟨hImeas, hIvol, hIint⟩ :=
    Submission.cbr_cc_seg_line_hausdorff P a τ hτ (Ioo 0 ℓ) measurableSet_Ioo
  have hIfin : μHE[1] ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) < ∞ := by
    rw [hIvol, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  -- Step 2: `ζ₀ = (α ↦ α(τ))` is a unit orientation of `span{τ}`
  let ζ₀ : MultiVector P 1 := ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => τ)
  have hζ₀ : IsUnitOrientationOf ζ₀ (Submodule.span ℝ {τ}) := by
    refine ⟨fun _ => τ, ?_, by rw [range_const], Or.inl fun α => rfl⟩
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, ite_eq_left rfl, real_inner_self_eq_norm_sq, hτ, one_pow]
  -- Step 3: `I` lies in the range of the `1`-Lipschitz map `w ↦ a + w₀τ`
  have hrect : CountablyRectifiable 1 ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ) := by
    let F : EuclideanSpace ℝ (Fin 1) → Euclid P := fun w => a + w 0 • τ
    have hF : LipschitzWith 1 F := by
      refine LipschitzWith.of_dist_le_mul fun w w' => ?_
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
      calc ‖F w - F w'‖ = ‖(w - w') 0‖ := by
            simp only [F, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hτ, mul_one,
              PiLp.sub_apply]
        _ ≤ ‖w - w'‖ := PiLp.norm_apply_le _ _
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hF).mono ?_
    rintro _ ⟨u, -, rfl⟩
    exact ⟨EuclideanSpace.single 0 u, by simp [F]⟩
  -- Step 4: the triple `R = (I, 1, ζ₀)`
  let R : IMRep (univ : Set (Euclid P)) 1 :=
    { carrier := (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ
      mult := fun _ => 1
      orient := fun _ => ζ₀
      measurableSet_carrier := hImeas
      carrier_subset := subset_univ _
      rectifiable := hrect
      measurable_mult := measurable_const
      mult_pos := fun _ _ => Nat.one_pos
      locallyIntegrable_mult := fun K _ _ => by
        rw [Nat.cast_one, setLIntegral_one]
        exact (lt_of_le_of_lt (measure_mono inter_subset_left) hIfin).ne
      aestronglyMeasurable_orient := aestronglyMeasurable_const
      orients := ae_restrict_of_forall_mem hImeas fun x hx =>
        ⟨_, Submission.cbr_cc_seg_open_segment_tangent P a τ ℓ hτ x hx, hζ₀⟩ }
  refine ⟨R, ?_, ?_, ?_⟩
  -- Step 5: `I ⊆ [a, a + ℓτ]`, via `φ(u) = a + (u/ℓ)((a + ℓτ) − a)` with `u/ℓ ∈ [0, 1]`
  · rintro _ ⟨u, ⟨hu0, huℓ⟩, rfl⟩
    rw [segment_eq_image']
    refine ⟨u / ℓ, ⟨div_nonneg hu0.le hℓ.le, (div_le_one hℓ).mpr huℓ.le⟩, ?_⟩
    simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ u hℓ.ne']
  -- Step 6: `μ_R(ℝᴾ) = H¹(I) < ∞`
  · show ((μHE[1].restrict ((fun u : ℝ => a + u • τ) '' Ioo 0 ℓ)).withDensity
      fun _ => ((1 : ℕ) : ℝ≥0∞)) univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Nat.cast_one,
      setLIntegral_one]
    exact hIfin
  -- Step 7: `R(ω) = ∫_I ω(x)(τ) dH¹(x) = ∫₀^ℓ ω(a + uτ)(τ) du`
  · intro ω
    show ∫ x in (fun u : ℝ => a + u • τ) '' Ioo 0 ℓ, ((1 : ℕ) : ℝ) * ζ₀ (ω x) ∂μHE[1] = _
    rw [Nat.cast_one]
    simp only [one_mul, ζ₀, ContinuousAlternatingMap.apply_apply]
    exact hIint fun x => ω x fun _ => τ

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
