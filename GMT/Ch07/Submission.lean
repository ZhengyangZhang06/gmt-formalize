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

/-- Integration by parts for a Lipschitz `u` against `C¹` fields `Φᵢ` with compact support in
`B = B_R(0)`: `∫_B Σᵢ Du(x)eᵢ Φᵢ(x) dx = −∫_B u(x) Σᵢ DΦᵢ(x)eᵢ dx`.  Each `Φᵢ` is Lipschitz, so
Lipschitz integration by parts in direction `eᵢ` (`LipschitzWith.integral_lineDeriv_mul_eq`) applies
on `ℝⁿ`; by Rademacher, `lineDeriv u x eᵢ = Du(x)eᵢ` for a.e. `x`.  Both integrands are integrable
(`Du` is bounded by the Lipschitz constant) and vanish off `B`, so summing over `i` concludes. -/
theorem Submission.dorag_ha_lsc_ibp_lipschitz : ∀ (n : ℕ) (R : ℝ) (u : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∃ L : NNReal, LipschitzWith L u) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R u Φ ⟨L, hu⟩ hΦ hΦc hΦs
  set e : Fin n → Euclid n := fun i => EuclideanSpace.single i (1 : ℝ)
  have hΦL : ∀ i, ∃ C, LipschitzWith C (Φ i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hΦc i) (hΦ i) one_ne_zero
  choose C hC using hΦL
  -- integrability of the two families of integrands
  have hint1 : ∀ i, Integrable (fun x => fderiv ℝ u x (e i) * Φ i x) := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hΦ i).continuous.integrable_of_hasCompactSupport (hΦc i))
      (measurable_fderiv_apply_const ℝ u (e i)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    exact ((fderiv ℝ u x).le_opNorm (e i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))
  have hcontd : ∀ i, Continuous fun x => fderiv ℝ (Φ i) x (e i) := fun i =>
    ((hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint2 : ∀ i, Integrable (fun x => u x * fderiv ℝ (Φ i) x (e i)) := by
    intro i
    refine (hu.continuous.mul (hcontd i)).integrable_of_hasCompactSupport ?_
    exact ((hΦc i).fderiv_apply (𝕜 := ℝ) (e i)).mul_left
  -- per-coordinate identity on the whole space
  have key : ∀ i, ∫ x, fderiv ℝ u x (e i) * Φ i x = -∫ x, u x * fderiv ℝ (Φ i) x (e i) := by
    intro i
    have h1 :=
      hu.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid n))) (hC i) (hΦc i) (e i)
    have h2 : (fun x => lineDeriv ℝ u x (e i) * Φ i x) =ᵐ[volume]
        fun x => fderiv ℝ u x (e i) * Φ i x := by
      filter_upwards [hu.ae_differentiableAt] with x hx
      rw [hx.lineDeriv_eq_fderiv]
    have h3 : (fun x => lineDeriv ℝ (Φ i) x (-e i) * u x) =
        fun x => -(u x * fderiv ℝ (Φ i) x (e i)) := by
      funext x
      rw [(((hΦ i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
      ring
    rw [integral_congr_ae h2, h3, integral_neg] at h1
    exact h1
  -- integrands vanish off the ball
  have hzero1 : ∀ x, x ∉ ball (0 : Euclid n) R →
      ∑ i : Fin n, fderiv ℝ u x (e i) * Φ i x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  have hzero2 : ∀ x, x ∉ ball (0 : Euclid n) R →
      u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (e i) = 0 := by
    intro x hx
    rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => key i

namespace Submission

/-- Integration by parts on `B = B_R(0)` for `h` that is only `C¹` on `B`, against `C¹` fields
`Φᵢ` with compact support in `B`: `∫_B Σᵢ Dᵢh Φᵢ = -∫_B h Σᵢ DᵢΦᵢ`.  The supports of the `Φᵢ` lie
in some `B_{r₁}(0)`, `r₁ < R`.  A bump `χ` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ ⊆ B` makes
`h̃ = χh` a compactly supported `C¹`, hence Lipschitz, function, so `dorag_ha_lsc_ibp_lipschitz`
applies to `h̃`; both integrands only see `B_{r₁}(0)`, where `h̃ = h`. -/
theorem dorag_ha_lsc_ibp_c1_ball : ∀ (n : ℕ) (R : ℝ) (h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R h Φ hh hΦ hΦc hΦs
  -- `R ≤ 0`: the ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR]; simp
  -- The supports of the `Φᵢ` lie in a smaller ball `B_{r₁}(0)`, `0 < r₁ < R`.
  set K := ⋃ i, tsupport (Φ i)
  have hKc : IsClosed K := isClosed_iUnion_of_finite fun i => isClosed_tsupport _
  have hKB : K ⊆ ball 0 R := iUnion_subset hΦs
  obtain ⟨r₁, ⟨hr₁0, hr₁R⟩, hK₁⟩ := exists_pos_lt_subset_ball hR hKc hKB
  -- `h̃ = χh` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ = B̄_{(r₁+R)/2}(0) ⊆ B` is `C¹_c`.
  let χ : ContDiffBump (0 : Euclid n) := ⟨r₁, (r₁ + R) / 2, hr₁0, by linarith⟩
  set ht : Euclid n → ℝ := fun x => χ x * h x
  have hχsupp : tsupport χ ⊆ ball 0 R := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (show (r₁ + R) / 2 < R by linarith)
  have htC : ContDiff ℝ 1 ht := by
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · exact ((χ.contDiff.contDiffOn).mul hh).contDiffAt (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : ht =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [ht, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have htc : HasCompactSupport ht := χ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport htc htC one_ne_zero
  have key := Submission.dorag_ha_lsc_ibp_lipschitz n R ht Φ ⟨C, hC⟩ hΦ hΦc hΦs
  -- On `B_{r₁}(0)`, `h̃ = h` near each point; off it, every `Φᵢ` and `DΦᵢ` vanishes.
  have hone : ∀ y ∈ ball (0 : Euclid n) r₁, ht y = h y := by
    intro y hy
    simp [ht, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hEq : ∀ x ∈ ball (0 : Euclid n) r₁, ht =ᶠ[𝓝 x] h := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using hone y hy
  have hout : ∀ x, x ∉ ball (0 : Euclid n) r₁ → ∀ i, x ∉ tsupport (Φ i) :=
    fun x hx i h' => hx (hK₁ (mem_iUnion.2 ⟨i, h'⟩))
  have h1 : ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x =
      ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ ht x (EuclideanSpace.single i (1 : ℝ)) * Φ i x := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [(hEq x hx).fderiv_eq]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [image_eq_zero_of_notMem_tsupport (hout x hx i)]
  have h2 : ∫ x in ball (0 : Euclid n) R,
        h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ x in ball (0 : Euclid n) R,
        ht x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [hone x hx]
    · have : ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [fderiv_of_notMem_tsupport ℝ (hout x hx i)]; rfl
      simp only [this, mul_zero]
  rw [h1, h2, key]

/-- Duality bound for the variation of a smooth `g` (Simon Ch. 2, 2.5 (4)): if `∫ g div ψ ≤ c`
for every `C^∞` field `ψ` with compact support in `B = B_r(0)` and `|ψ| ≤ 1`, then
`∫_B |Dg| ≤ c`.  Applied to the coordinates `ψᵢ`, `dorag_ha_lsc_ibp_c1_ball` gives
`∫ g div ψ = -∫_B Σᵢ Dg(eᵢ) ψᵢ`.  With the gradient `G = ∇g`, `θₖ = 1/(k+1)` and bumps `χₖ`
with `χₖ = 1` on `B̄_{r(1-θₖ/2)}(0)` and `spt χₖ ⊆ B`, the fields
`ψₖ = -χₖ G/√(|G|² + θₖ²)` are admissible, so `∫_B χₖ |G|²/√(|G|² + θₖ²) ≤ c`.  The integrands
tend to `|G| = |Dg|` on `B`, and Fatou's lemma concludes. -/
theorem codim1_zsl_pc_smooth_grad_bound : ∀ (m : ℕ) (g : Euclid m → ℝ) (r c : ℝ), ContDiff ℝ (⊤ : ℕ∞) g → (∀ ψ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap ≤ c) → ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ g v‖ₑ ≤ ENNReal.ofReal c := by
  intro m g r c hg hψ
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]; simp
  set B := ball (0 : Euclid m) r with hB
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  -- Step 1: integration by parts in trace form, from `dorag_ha_lsc_ibp_c1_ball`.
  have ibp : ∀ ψ : Euclid m → Euclid m, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
      ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = -∫ v in B, ∑ i : Fin m, fderiv ℝ g v (EuclideanSpace.single i (1:ℝ)) * ψ v i := by
    intro ψ hψ1 hψc hψB
    have key := Submission.dorag_ha_lsc_ibp_c1_ball m r g (fun i x => ψ x i)
      (hg.of_le h1).contDiffOn (fun i => (contDiff_piLp 2).1 hψ1 i)
      (fun i => hψc.comp_left (g := fun w : Euclid m => w i) (by simp))
      (fun i => (tsupport_comp_subset (g := fun w : Euclid m => w i) (by simp) ψ).trans hψB)
    have hd : ∀ v (i : Fin m), fderiv ℝ (fun x => ψ x i) v
        = (PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp (fderiv ℝ ψ v) := fun v i => by
      have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (ψ v) i).comp v
        ((hψ1.differentiable one_ne_zero) v).hasFDerivAt
      exact h.fderiv
    have htr : ∀ v, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = ∑ i : Fin m, fderiv ℝ (fun x => ψ x i) v (EuclideanSpace.single i 1) := by
      intro v
      rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin m) ℝ)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd]
      simp [EuclideanSpace.inner_single_left]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) ?_]
    · simp_rw [htr]
      simp only [] at key
      rw [key, neg_neg]
    · intro v hv
      have : fderiv ℝ ψ v = 0 := by
        by_contra hne
        exact hv (hψB (support_fderiv_subset ℝ hne))
      simp [this]
  -- Step 2: the gradient field `G = ∇g`.
  set L := fderiv ℝ g with hLdef
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := (contDiff_infty_iff_fderiv.1 hg).2
  set G : Euclid m → Euclid m := fun v => (InnerProductSpace.toDual ℝ (Euclid m)).symm (L v)
    with hGdef
  have hGi : ∀ v (i : Fin m), G v i = L v (EuclideanSpace.single i 1) := by
    intro v i
    have := EuclideanSpace.inner_single_left i (1:ℝ) (G v)
    rw [real_inner_comm, hGdef, InnerProductSpace.toDual_symm_apply] at this
    simpa using this.symm
  have hGn : ∀ v, ‖G v‖ = ‖L v‖ := fun v => LinearIsometryEquiv.norm_map _ _
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_piLp 2]
    intro i
    have : (fun x => G x i) = fun x => L x (EuclideanSpace.single i 1) := funext fun x => hGi x i
    rw [this]
    exact hL.clm_apply contDiff_const
  have hsum : ∀ v, ∑ i : Fin m, L v (EuclideanSpace.single i 1) * G v i = ‖G v‖ ^ 2 := by
    intro v
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hGi, Real.norm_eq_abs, sq_abs, sq]
  -- Step 3: parameters `θₖ`, bump cut-offs `χₖ` and test fields `ψₖ`.
  set θ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hθdef
  have hθpos : ∀ k, 0 < θ k := fun k => by positivity
  have hθle : ∀ k, θ k ≤ 1 := fun k => by
    rw [hθdef, div_le_one (by positivity)]
    have := (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith
  have hθlim : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set ri : ℕ → ℝ := fun k => r * (1 - θ k / 2) with hridef
  set ro : ℕ → ℝ := fun k => r * (1 - θ k / 4) with hrodef
  have hri : ∀ k, 0 < ri k := fun k => mul_pos hr (by linarith [hθle k])
  have hrio : ∀ k, ri k < ro k := fun k => mul_lt_mul_of_pos_left (by linarith [hθpos k]) hr
  have hro : ∀ k, ro k < r := fun k => mul_lt_of_lt_one_right hr (by linarith [hθpos k])
  let χ : ℕ → ContDiffBump (0 : Euclid m) := fun k => ⟨ri k, ro k, hri k, hrio k⟩
  have hχ1 : ∀ v ∈ B, ∀ᶠ k in atTop, χ k v = 1 := by
    intro v hv
    have hlim : Tendsto ri atTop (𝓝 r) := by
      have := (tendsto_const_nhds (x := r)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).sub (hθlim.div_const 2))
      simpa using this
    have hv' : ‖v‖ < r := by simpa [hB] using hv
    filter_upwards [hlim.eventually_const_lt hv'] with k hk
    exact (χ k).one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hk.le)
  set s : ℕ → Euclid m → ℝ := fun k v => √(‖G v‖ ^ 2 + θ k ^ 2) with hsdef
  have hspos : ∀ k v, 0 < s k v := fun k v => Real.sqrt_pos.2 (by have := hθpos k; positivity)
  have hGs : ∀ k v, ‖G v‖ ≤ s k v := fun k v =>
    Real.le_sqrt_of_sq_le (by have := hθpos k; nlinarith)
  have hsc : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (s k) := fun k =>
    ((hG.norm_sq ℝ).add contDiff_const).sqrt (fun v => by have := hθpos k; positivity)
  set ψ : ℕ → Euclid m → Euclid m := fun k v => (-(χ k v / s k v)) • G v with hψdef
  set f : ℕ → Euclid m → ℝ := fun k v => χ k v * (‖G v‖ ^ 2 / s k v) with hfdef
  have hψs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) := fun k =>
    (((χ k).contDiff.div (hsc k) (fun v => (hspos k v).ne')).neg).smul hG
  have hψsupp : ∀ k, tsupport (ψ k) ⊆ closedBall 0 (ro k) := by
    intro k
    rw [← (χ k).tsupport_eq]
    apply closure_mono
    intro v hv
    rw [Function.mem_support] at hv ⊢
    intro h0
    apply hv
    simp [hψdef, h0]
  have hψB : ∀ k, tsupport (ψ k) ⊆ B := fun k => (hψsupp k).trans (closedBall_subset_ball (hro k))
  have hψc : ∀ k, HasCompactSupport (ψ k) := fun k =>
    (isCompact_closedBall 0 (ro k)).of_isClosed_subset (isClosed_tsupport _) (hψsupp k)
  have hψn : ∀ k v, ‖ψ k v‖ ≤ 1 := by
    intro k v
    have hχ0 := (χ k).nonneg (x := v)
    have hχ1' := (χ k).le_one (x := v)
    simp only [hψdef, norm_smul, norm_neg, norm_div, Real.norm_eq_abs, abs_of_nonneg hχ0,
      abs_of_pos (hspos k v)]
    rw [div_mul_eq_mul_div, div_le_one (hspos k v)]
    calc χ k v * ‖G v‖ ≤ 1 * s k v := mul_le_mul hχ1' (hGs k v) (norm_nonneg _) zero_le_one
      _ = s k v := one_mul _
  -- Step 4: `∫ g div ψₖ = ∫_B fₖ ≤ c`.
  have hint_eq : ∀ k, ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ (ψ k) v).toLinearMap
      = ∫ v in B, f k v := by
    intro k
    rw [ibp (ψ k) ((hψs k).of_le h1) (hψc k) (hψB k), ← integral_neg]
    congr 1
    funext v
    have : ∀ i : Fin m, L v (EuclideanSpace.single i 1) * (ψ k v) i
        = -(χ k v / s k v) * (L v (EuclideanSpace.single i 1) * G v i) := fun i => by
      simp only [hψdef, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [this, ← Finset.mul_sum, hsum, hfdef]
    ring
  have hle : ∀ k, ∫ v in B, f k v ≤ c := fun k =>
    (hint_eq k) ▸ hψ (ψ k) (hψs k) (hψc k) (hψB k) (hψn k)
  have hfc : ∀ k, Continuous (f k) := fun k =>
    (χ k).continuous.mul (((continuous_norm.comp hG.continuous).pow 2).div (hsc k).continuous
      (fun v => (hspos k v).ne'))
  have hfnn : ∀ k v, 0 ≤ f k v := fun k v =>
    mul_nonneg (χ k).nonneg (div_nonneg (sq_nonneg _) (hspos k v).le)
  have hfi : ∀ k, IntegrableOn (f k) B := fun k =>
    ((hfc k).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euclid m) r)).mono_set
      ball_subset_closedBall
  have hbound : ∀ k, ∫⁻ v in B, ENNReal.ofReal (f k v) ≤ ENNReal.ofReal c := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (ae_of_all _ (hfnn k))]
    exact ENNReal.ofReal_le_ofReal (hle k)
  -- Step 5: `fₖ → ‖Dg‖` on `B`, and Fatou's lemma.
  have htend : ∀ v ∈ B, Tendsto (fun k => ENNReal.ofReal (f k v)) atTop
      (𝓝 (ENNReal.ofReal ‖G v‖)) := by
    intro v hv
    apply ENNReal.tendsto_ofReal
    have hχt : Tendsto (fun k => χ k v) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (by filter_upwards [hχ1 v hv] with k hk; exact hk.symm)
    have hq : Tendsto (fun k => ‖G v‖ ^ 2 / s k v) atTop (𝓝 ‖G v‖) := by
      rcases eq_or_ne ‖G v‖ 0 with h0 | h0
      · simp [h0]
      · have hs : Tendsto (fun k => s k v) atTop (𝓝 (√(‖G v‖ ^ 2 + 0 ^ 2))) :=
          (tendsto_const_nhds.add (hθlim.pow 2)).sqrt
        have hne : √(‖G v‖ ^ 2 + 0 ^ 2) ≠ 0 := by
          rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]; exact h0
        have := (tendsto_const_nhds (x := ‖G v‖ ^ 2)).div hs hne
        convert this using 2
        rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _), sq, mul_self_div_self]
    have := hχt.mul hq
    rw [one_mul] at this
    exact this
  calc ∫⁻ v in B, ‖L v‖ₑ = ∫⁻ v in B, liminf (fun k => ENNReal.ofReal (f k v)) atTop := by
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        rw [(htend v hv).liminf_eq, hGn, ofReal_norm]
    _ ≤ liminf (fun k => ∫⁻ v in B, ENNReal.ofReal (f k v)) atTop :=
        lintegral_liminf_le (fun k => (hfc k).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end Submission
/-- Mollifying a test field (Simon Ch. 2, 2.5): with the reflected kernel `ρ̌(z) = ρ(-z)`, the
field `ψ' = ρ̌ ⋆ ψ` is `C^∞`, has compact support in `B_{r+ε}(0)` (`spt ψ ⊆ B_{r₁}(0)`, `r₁ < r`,
and `spt ρ̌ ⊆ B̄_ε(0)`) and satisfies `|ψ'| ≤ ∫ρ̌ = 1`.  Differentiating under the convolution and
commuting the trace with the integral gives `div ψ'(w) = ∫ ρ(z) div ψ(w + z) dz`; Fubini and the
measure-preserving shear `(v, z) ↦ (v + z, z)` then turn `∫ (ρ ⋆ 1_F) div ψ` into `∫_F div ψ'`. -/
theorem Submission.codim1_zsl_pc_mollify_test_field : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (ψ : Euclid m → Euclid m) (r ε : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∃ ψ' : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ HasCompactSupport ψ' ∧ tsupport ψ' ⊆ ball (0 : Euclid m) (r + ε) ∧ (∀ v, ‖ψ' v‖ ≤ 1) ∧ ∫ v, (∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap = ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap := by
  intro m F ρ ψ r ε hF hρ hρ0 hρε hρ1 hψ hψcs hψr hψ1
  -- basic facts about `ρ` and its reflection `ρ'`
  have hρc : Continuous ρ := hρ.continuous
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε z (by simpa using hz))
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  set ρ' : Euclid m → ℝ := fun z => ρ (-z) with hρ'_def
  have hρ'c : Continuous ρ' := hρc.comp continuous_neg
  have hρ'cs : HasCompactSupport ρ' :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε (-z) (by simpa using hz))
  have hρ'smooth : ContDiff ℝ (⊤ : ℕ∞) ρ' := hρ.comp contDiff_neg
  have hρ'i : Integrable ρ' := hρ'c.integrable_of_hasCompactSupport hρ'cs
  have hρ'1 : ∫ z, ρ' z = 1 := by
    rw [show (∫ z, ρ' z) = ∫ z, ρ (-z) from rfl, integral_neg_eq_self ρ volume]
    exact hρ1
  -- the trace as a continuous linear map
  obtain ⟨Tr, hTr⟩ : ∃ Tr : (Euclid m →L[ℝ] Euclid m) →L[ℝ] ℝ, ∀ A : Euclid m →L[ℝ] Euclid m,
      Tr A = LinearMap.trace ℝ (Euclid m) A.toLinearMap :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid m)) ∘ₗ (ContinuousLinearMap.coeLM ℝ)), fun A => rfl⟩
  -- the mollified field `ψ' = ρ' ⋆ ψ`
  set L : ℝ →L[ℝ] Euclid m →L[ℝ] Euclid m := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set ψ' : Euclid m → Euclid m := convolution ρ' ψ L volume with hψ'_def
  have hψ'apply : ∀ w, ψ' w = ∫ t, ρ' t • ψ (w - t) := by
    intro w
    rw [hψ'_def, convolution_def]
    simp [L]
  -- support
  obtain ⟨r₁, hr₁r, hr₁⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψr
  have hsupp : support ψ' ⊆ closedBall 0 (r₁ + ε) := by
    intro w hw
    rw [Function.mem_support, hψ'apply] at hw
    by_contra hcon
    apply hw
    have hzero : ∀ t, ρ' t • ψ (w - t) = 0 := by
      intro t
      by_cases h1 : ρ' t = 0
      · simp [h1]
      by_cases h2 : ψ (w - t) = 0
      · simp [h2]
      exfalso
      apply hcon
      have ht : ‖t‖ ≤ ε := by
        by_contra h
        push Not at h
        exact h1 (hρε (-t) (by rwa [norm_neg]))
      have hwt : w - t ∈ ball (0 : Euclid m) r₁ := hr₁ (subset_tsupport ψ h2)
      rw [mem_ball_zero_iff] at hwt
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ = ‖(w - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - t‖ + ‖t‖ := norm_add_le _ _
        _ ≤ r₁ + ε := by linarith
    simp [hzero]
  have htsupp : tsupport ψ' ⊆ closedBall 0 (r₁ + ε) := closure_minimal hsupp isClosed_closedBall
  -- derivative of `ψ'` and its trace
  have hderiv : ∀ w, fderiv ℝ ψ' w =
      convolution ρ' (fderiv ℝ ψ) (ContinuousLinearMap.precompR (Euclid m) L) volume w := fun w =>
    (hψcs.hasFDerivAt_convolution_right L hρ'i.locallyIntegrable
      (hψ.of_le (by exact_mod_cast le_top)) w).fderiv
  have hG' : ∀ w, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
      ∫ z, ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap := by
    intro w
    have hint : Integrable (fun t => ρ' t • fderiv ℝ ψ (w - t)) :=
      (hψcs.fderiv (𝕜 := ℝ)).convolutionExists_right (ContinuousLinearMap.precompR (Euclid m) L)
        hρ'i.locallyIntegrable (hψ.continuous_fderiv (by simp)) w
    have h1 : fderiv ℝ ψ' w = ∫ t, ρ' t • fderiv ℝ ψ (w - t) := by
      rw [hderiv w, convolution_def]
      congr 1
    rw [← hTr, h1, ← ContinuousLinearMap.integral_comp_comm Tr hint,
      ← integral_neg_eq_self
        (fun z => ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap) volume]
    congr 1
    funext t
    rw [map_smul, smul_eq_mul, hTr, ← sub_eq_add_neg]
  refine ⟨ψ', ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ'cs.contDiff_convolution_left L hρ'smooth hψ.continuous.locallyIntegrable
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsupp
  · exact htsupp.trans (closedBall_subset_ball (by linarith))
  · intro v
    rw [hψ'apply]
    refine (norm_integral_le_of_norm_le hρ'i (ae_of_all _ fun t => ?_)).trans hρ'1.le
    rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_of_le_one_right (hρ0 _) (hψ1 _)
  · -- Fubini
    set u : Euclid m → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
    set G : Euclid m → ℝ :=
      fun v => LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap with hG
    have hGeq : G = Tr ∘ fderiv ℝ ψ := by
      funext v
      simp only [G, Function.comp_apply, hTr]
    have hGc : Continuous G := by
      rw [hGeq]; exact Tr.continuous.comp (hψ.continuous_fderiv (by simp))
    have hGcs : HasCompactSupport G := by
      rw [hGeq]; exact (hψcs.fderiv (𝕜 := ℝ)).comp_left (map_zero Tr)
    have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGcs
    have hum : Measurable u := measurable_const.indicator hF
    have hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := fun x => by
      by_cases hx : x ∈ F <;> simp [u, hx]
    set g : Euclid m × Euclid m → ℝ := fun p => ρ p.2 * u (p.1 - p.2) * G p.1 with hg
    have hgm : Measurable g :=
      ((hρc.measurable.comp measurable_snd).mul
        (hum.comp (measurable_fst.sub measurable_snd))).mul (hGc.measurable.comp measurable_fst)
    have hgi : Integrable g (volume.prod volume) := by
      refine Integrable.mono' (hGi.norm.mul_prod hρi) hgm.aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      have h1 := hu01 (p.1 - p.2)
      have h2 := hρ0 p.2
      simp only [g, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1.1]
      nlinarith [mul_nonneg (mul_nonneg h2 (abs_nonneg (G p.1))) (sub_nonneg.mpr h1.2)]
    have hT : MeasurePreserving (fun p : Euclid m × Euclid m => (p.1 + p.2, p.2))
        (volume.prod volume) (volume.prod volume) := measurePreserving_add_prod volume volume
    have hgTi : Integrable (fun p : Euclid m × Euclid m => g (p.1 + p.2, p.2))
        (volume.prod volume) :=
      (hT.integrable_comp hgm.aestronglyMeasurable).mpr hgi
    have hgT : ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) =
        ∫ p, g p ∂(volume.prod volume) := by
      have := integral_map (μ := volume.prod volume) hT.measurable.aemeasurable
        (f := g) (by rw [hT.map_eq]; exact hgm.aestronglyMeasurable)
      rw [hT.map_eq] at this
      exact this.symm
    have hLHS : ∫ v, (∫ z, ρ z * u (v - z)) * G v = ∫ p, g p ∂(volume.prod volume) := by
      rw [integral_prod g hgi]
      congr 1
      funext v
      rw [← integral_mul_const]
    have hRHS : ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
        ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) := by
      rw [integral_prod _ hgTi, ← integral_indicator hF]
      congr 1
      funext w
      have h1 : ∀ z, g (w + z, z) = u w * (ρ z * G (w + z)) := fun z => by
        simp only [g, add_sub_cancel_right]
        ring
      dsimp only
      simp only [h1]
      rw [integral_const_mul, ← hG' w]
      by_cases hw : w ∈ F <;> simp [u, hw]
    exact hLHS.trans (hgT.symm.trans hRHS.symm)

/-- Gradient bound for a mollified indicator (Simon Ch. 2, 2.5; step 3 of the perimeter
compactness used for the zero-scale limit planes of 7.5).  Let `ρ ≥ 0` be `C^∞` with `∫ ρ = 1` and
`ρ = 0` off `B̄_ε(0)`, and let `∫_F div φ ≤ c` for every `C^∞` field `φ` with compact support in
`B_{r+ε}(0)` and `|φ| ≤ 1`.  Then `f = ρ ⋆ 1_F` is `C^∞` and `∫_{B_r(0)} |Df| ≤ c`.  As `ρ` has
compact support and `1_F` is locally integrable, `f` is `C^∞`
(`HasCompactSupport.contDiff_convolution_left`).  For a test field `ψ` in `B_r(0)` with
`|ψ| ≤ 1`, `codim1_zsl_pc_mollify_test_field` gives a test field `ψ'` in `B_{r+ε}(0)` with
`|ψ'| ≤ 1` and `∫ f div ψ = ∫_F div ψ' ≤ c`, and `codim1_zsl_pc_smooth_grad_bound` turns these
bounds into `∫_{B_r(0)} |Df| ≤ c`. -/
theorem Submission.codim1_zsl_pc_mollify_grad_bound : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (r ε c : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (r + ε) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) ∧ ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) v‖ₑ ≤ ENNReal.ofReal c := by
  intro m F ρ r ε c hF hρ hρ0 hρs hρ1 hP
  -- `f = ρ ⋆ 1_F` is `C^∞`: `ρ` is `C^∞` with support in `B̄_ε(0)`, `1_F` is locally integrable
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε) fun z hz => hρs z ?_
    simpa [mem_closedBall, dist_zero_right, not_le] using hz
  have hli : LocallyIntegrable (F.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hF
  have hconv : (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z))
      = convolution ρ (F.indicator (fun _ => (1 : ℝ))) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext v
    simp [convolution_def, smul_eq_mul]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) := by
    rw [hconv]
    exact hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hli
  refine ⟨hsmooth, Submission.codim1_zsl_pc_smooth_grad_bound m _ r c hsmooth ?_⟩
  -- a test field `ψ` in `B_r(0)` against `f` is a test field `ψ'` in `B_{r+ε}(0)` against `1_F`
  intro ψ hψ hψc hψs hψ1
  obtain ⟨ψ', hψ', hψ'c, hψ's, hψ'1, heq⟩ :=
    Submission.codim1_zsl_pc_mollify_test_field m F ρ ψ r ε hF hρ hρ0 hρs hρ1 hψ hψc hψs hψ1
  rw [heq]
  exact hP ψ' hψ' hψ'c hψ's hψ'1

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
