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

/-- **Integrating factor for the monotonicity identity** (Simon Ch. 4, 3.16–3.17).  If `I` is
continuous on `(0, r]`, has derivative `I'` on `(0, r)` and `n I(s) − s I'(s) ≤ κ s I(s)` there,
then `s ↦ e^{κs} s⁻ⁿ I(s)` is nondecreasing on `(0, r]`.  On `(0, r]` this function equals
`G(s) = exp(κs − n log s) I(s)`, and `G'(s) = exp(κs − n log s) s⁻¹ (κ s I(s) − (n I(s) − s I'(s)))
≥ 0` on `(0, r)`, so the mean value theorem applies. -/
theorem Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq : ∀ (n : ℕ) (κ r : ℝ) (I I' : ℝ → ℝ), ContinuousOn I (Ioc 0 r) → (∀ s ∈ Ioo 0 r, HasDerivAt I (I' s) s) → (∀ s ∈ Ioo 0 r, (n : ℝ) * I s - s * I' s ≤ κ * s * I s) → MonotoneOn (fun s => Real.exp (κ * s) / s ^ n * I s) (Ioc 0 r) := by
  intro n κ r I I' hIc hId hineq
  -- on `(0, r]`, `e^{κs}/sⁿ · I(s) = G(s) := exp(κs − n log s) · I(s)`
  refine MonotoneOn.congr (f₁ := fun s => Real.exp (κ * s - n * Real.log s) * I s) ?_ ?_
  swap
  · intro s hs
    simp only [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hs.1]
  -- `G` is continuous on `(0, r]`
  have hGc : ContinuousOn (fun s => Real.exp (κ * s - n * Real.log s) * I s) (Ioc 0 r) := by
    refine ContinuousOn.mul (Real.continuous_exp.comp_continuousOn ?_) hIc
    exact (continuousOn_const.mul continuousOn_id).sub
      (continuousOn_const.mul (Real.continuousOn_log.mono fun s hs => hs.1.ne'))
  -- `G' = exp(κs − n log s) · ((κ − n/s) I + I') ≥ 0` on `(0, r)`; mean value theorem
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 r) hGc
    (f' := fun s => Real.exp (κ * s - n * Real.log s) * ((κ - n * s⁻¹) * I s + I' s)) ?_ ?_
  · intro s hs
    rw [interior_Ioc] at hs
    have h1 : HasDerivAt (fun s => κ * s - n * Real.log s) (κ * 1 - n * s⁻¹) s :=
      ((hasDerivAt_id' s).const_mul κ).sub ((Real.hasDerivAt_log hs.1.ne').const_mul (n : ℝ))
    exact ((h1.exp.mul (hId s hs)).congr_deriv (by ring)).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    have key : (κ - n * s⁻¹) * I s + I' s = s⁻¹ * (κ * s * I s - (n * I s - s * I' s)) := by
      linear_combination (-(κ * I s + I' s)) * mul_inv_cancel₀ hs.1.ne'
    rw [key]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (inv_nonneg.mpr hs.1.le) (sub_nonneg.mpr (hineq s hs)))
/-- **Differentiation of radial cutoff integrals** (Simon Ch. 4, 3.3–3.4, where
`I(ρ) = ∫ φ(r/ρ) dμ` is differentiated in `ρ`; here the cutoff is written in the squared ratio
`|x - z|²/t²`).  If `μ(B_r(z)) < ∞` and `η` is `C¹` with `η = 0` on `[1, ∞)`, then
`I(t) = ∫ η(|x - z|²/t²) dμ` is continuous on `(0, r]` and, for `0 < s < r`,
`I'(s) = -(∫ 2 (|x - z|²/s²) η'(|x - z|²/s²) dμ)/s` (dominated convergence and differentiation
under the integral sign). -/
theorem Submission.dsmc_em_cutoff_integral_hasDerivAt : ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), μ (ball z r) < ∞ → ContDiff ℝ 1 η → (∀ u, 1 ≤ u → η u = 0) → ContinuousOn (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (Ioc 0 r) ∧ ∀ s ∈ Ioo 0 r, HasDerivAt (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (-(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s) s := by
  intro P μ z r η hμ hη hη1
  have hηc : Continuous η := hη.continuous
  have hη'c : Continuous (deriv η) := hη.continuous_deriv le_rfl
  -- `η' = deriv η` vanishes on `(1, ∞)` (where `η` is locally zero), hence on `[1, ∞)`.
  have hη'1 : ∀ u, 1 ≤ u → deriv η u = 0 := by
    have hIoi : Ioi (1 : ℝ) ⊆ {u | deriv η u = 0} := fun u hu => by
      have hloc : η =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact hη1 v (le_of_lt hv)
      show deriv η u = 0
      rw [hloc.deriv_eq, deriv_const]
    have hIci : Ici (1 : ℝ) ⊆ {u | deriv η u = 0} := by
      rw [← closure_Ioi]
      exact closure_minimal hIoi (isClosed_eq hη'c continuous_const)
    exact fun u hu => hIci hu
  -- Bounds on `[0, 1]` for `η` and for `u ↦ 2 u η'(u)`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hηc.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (f := fun u : ℝ => 2 * u * deriv η u) (by fun_prop)
  have hg1 : ∀ u, 1 ≤ u → 2 * u * deriv η u = 0 := fun u hu => by
    rw [hη'1 u hu, mul_zero]
  -- For `0 < t ≤ r`, `g(|x - z|²/t²)` vanishes off `B_t(z) ⊆ B_r(z)` and is dominated there.
  have hdom : ∀ (g : ℝ → ℝ) (B : ℝ), (∀ u, 1 ≤ u → g u = 0) → (∀ u ∈ Icc (0 : ℝ) 1, ‖g u‖ ≤ B) →
      ∀ t, 0 < t → t ≤ r → ∀ x : Euclid P,
        ‖g (‖x - z‖ ^ 2 / t ^ 2)‖ ≤ (ball z r).indicator (fun _ => B) x := by
    intro g B hg0 hgB t ht htr x
    have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0 ⟨le_rfl, zero_le_one⟩)
    by_cases hx : ‖x - z‖ < t
    · have hxr : x ∈ ball z r := by
        rw [mem_ball, dist_eq_norm]
        exact hx.trans_le htr
      rw [indicator_of_mem hxr]
      apply hgB
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx.le 2
    · rw [not_lt] at hx
      rw [hg0 _ ?_, norm_zero]
      · exact indicator_nonneg (fun _ _ => hB) x
      · rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ ht.le hx 2
  have hint : ∀ c : ℝ, Integrable ((ball z r).indicator (fun _ => c)) μ := fun c =>
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
  have hcont : ∀ t : ℝ, Continuous fun x : Euclid P => η (‖x - z‖ ^ 2 / t ^ 2) := fun t => by
    fun_prop
  -- Pointwise derivative in `t ≠ 0`.
  have hderiv : ∀ x : Euclid P, ∀ t : ℝ, t ≠ 0 →
      HasDerivAt (fun t => η (‖x - z‖ ^ 2 / t ^ 2))
        (-(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t) t := by
    intro x t ht
    have h1 := (hasDerivAt_const t (‖x - z‖ ^ 2)).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht)
    have h2 := (hη.differentiable one_ne_zero (‖x - z‖ ^ 2 / t ^ 2)).hasDerivAt.comp t h1
    refine h2.congr_deriv ?_
    field_simp
    ring
  refine ⟨?_, fun s hs => ?_⟩
  · -- (i) continuity on `(0, r]` by dominated convergence
    refine continuousOn_of_dominated (F := fun t x => η (‖x - z‖ ^ 2 / t ^ 2))
      (bound := (ball z r).indicator (fun _ => C)) (fun t _ => (hcont t).aestronglyMeasurable)
      (fun t ht => Eventually.of_forall (hdom η C hη1 hC t ht.1 ht.2)) (hint C)
      (Eventually.of_forall fun x t ht => (hderiv x t ht.1.ne').continuousAt.continuousWithinAt)
  · -- (ii) differentiation under the integral sign on `(s/2, r)`
    have hs0 : 0 < s := hs.1
    have hb : ∀ x : Euclid P, ∀ t ∈ Ioo (s / 2) r,
        ‖-(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t‖ ≤
          (ball z r).indicator (fun _ => K) x / (s / 2) := by
      intro x t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have h1 : ‖2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)‖ ≤
          (ball z r).indicator (fun _ => K) x :=
        hdom (fun u => 2 * u * deriv η u) K hg1 hK t ht0 ht.2.le x
      have h2 : 0 ≤ (ball z r).indicator (fun _ => K) x := (norm_nonneg _).trans h1
      rw [norm_div, norm_neg, Real.norm_of_nonneg ht0.le]
      calc ‖2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)‖ / t
          ≤ (ball z r).indicator (fun _ => K) x / t := by gcongr
        _ ≤ (ball z r).indicator (fun _ => K) x / (s / 2) := by
          gcongr
          exact ht.1.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
      (F := fun t x => η (‖x - z‖ ^ 2 / t ^ 2))
      (F' := fun t x => -(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t)
      (bound := fun x => (ball z r).indicator (fun _ => K) x / (s / 2))
      (Ioo_mem_nhds (by linarith) hs.2)
      (Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
      ((hint C).mono' (hcont s).aestronglyMeasurable
        (Eventually.of_forall (hdom η C hη1 hC s hs0 hs.2.le)))
      (by fun_prop : Continuous fun x : Euclid P =>
        -(2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) / s).aestronglyMeasurable
      (Eventually.of_forall hb) ((hint K).div_const (s / 2))
      (Eventually.of_forall fun x t ht => hderiv x t (by linarith [ht.1] : 0 < t).ne')
    have hval : ∫ x, -(2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) / s ∂μ =
        -(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s := by
      rw [integral_div, integral_neg]
    rw [← hval]
    exact key.2
/-- **Radial first-variation inequality** (Simon Ch. 4, 3.2–3.3 with the bounded generalized mean
curvature of 3.14–3.16).  Test the first variation of `v(M, θ)` with the radial field
`X(x) = η(u(x)) (x - z)`, `u(x) = ‖x - z‖² / s²`, where `η ≥ 0` is `C¹`, nonincreasing and vanishes
on `[1, ∞)`.  Then `μ`-a.e. `n η(u) + 2 u η'(u) ≤ div_M X ≤ n η(u)`, and
`|X · H| ≤ κ s η(u)`, so `n ∫ η(u) dμ + ∫ 2 u η'(u) dμ ≤ ∫ div_M X dμ = -∫ X · H dμ ≤ κ s ∫ η(u) dμ`. -/
theorem Submission.dsmc_em_cutoff_first_variation_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ContDiff ℝ 1 η → (∀ u, 0 ≤ η u) → (∀ u, deriv η u ≤ 0) → (∀ u, 1 ≤ u → η u = 0) → ∀ s : ℝ, 0 < s → s < r → (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure + ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure := by
  intro P n U R H κ z r η hzU hPm hHκ hfv hη hη0 hη'0 hη1 s hs hsr
  classical
  set μ : Measure (Euclid P) := R.measure with hμ
  /- Step 0.  `κ ≥ 0`; `μ(B̄_s(z)) < ∞`; `η' = deriv η` is continuous and vanishes on `(1, ∞)`;
  `η` and `η'` are bounded on `[0, 1]`. -/
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hBc : IsCompact (closedBall z s) := isCompact_closedBall z s
  have hBm : MeasurableSet (closedBall z s) := measurableSet_closedBall
  have hBU : closedBall z s ⊆ U := (closedBall_subset_closedBall hsr.le).trans hzU
  have hBr : closedBall z s ⊆ ball z r := closedBall_subset_ball hsr
  have hμB : μ (closedBall z s) < ∞ := by
    rw [hμ, IMRep.measure, withDensity_apply _ hBm, Measure.restrict_restrict hBm, inter_comm]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult _ hBc hBU)
  have hind : ∀ c : ℝ, Integrable ((closedBall z s).indicator fun _ => c) μ := fun c =>
    (integrable_indicator_iff hBm).mpr (integrableOn_const hμB.ne)
  have hηd : ∀ u, HasDerivAt η (deriv η u) u := fun u =>
    ((hη.differentiable (by norm_num)) u).hasDerivAt
  have hηc : Continuous η := hη.continuous
  have hη'c : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have hη'1 : ∀ u, 1 < u → deriv η u = 0 := by
    intro u hu
    have : η =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact hη1 v hv.le
    rw [this.deriv_eq]
    simp
  obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Icc (0 : ℝ) 1, ‖η u‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hηc.continuousOn
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ Icc (0 : ℝ) 1, ‖deriv η u‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hη'c.continuousOn
  -- the radius ratio `u(x) = ‖x - z‖² / s²`
  have hucont : Continuous fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2 := by fun_prop
  have hu0 : ∀ x : Euclid P, 0 ≤ ‖x - z‖ ^ 2 / s ^ 2 := fun x => by positivity
  have hu_le : ∀ x ∈ closedBall z s, ‖x - z‖ ^ 2 / s ^ 2 ≤ 1 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [div_le_one (pow_pos hs 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hu_gt : ∀ x, x ∉ closedBall z s → 1 < ‖x - z‖ ^ 2 / s ^ 2 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [one_lt_div (pow_pos hs 2)]
    exact pow_lt_pow_left₀ hx hs.le two_ne_zero
  -- the two integrands vanish off `B̄_s(z)` and are bounded on it
  have hFint : Integrable (fun x => η (‖x - z‖ ^ 2 / s ^ 2)) μ := by
    refine Integrable.mono' (hind C) (hηc.comp hucont).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall z s
    · rw [indicator_of_mem hx]
      exact hC _ ⟨hu0 x, hu_le x hx⟩
    · rw [indicator_of_notMem hx, hη1 _ (hu_gt x hx).le, norm_zero]
  have hGint : Integrable
      (fun x => 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) μ := by
    refine Integrable.mono' (hind (2 * M))
      ((continuous_const.mul hucont).mul (hη'c.comp hucont)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall z s
    · have h1 := hu_le x hx
      have h2 := hM _ ⟨hu0 x, h1⟩
      rw [Real.norm_eq_abs] at h2
      rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_mul, abs_two,
        abs_of_nonneg (hu0 x)]
      calc 2 * (‖x - z‖ ^ 2 / s ^ 2) * |deriv η (‖x - z‖ ^ 2 / s ^ 2)| ≤ 2 * 1 * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) h2 (abs_nonneg _)
              (by norm_num)
        _ = 2 * M := by ring
    · rw [indicator_of_notMem hx, hη'1 _ (hu_gt x hx), mul_zero, norm_zero]
  /- Step 1.  The radial field `X(x) = η(u(x)) (x - z)` is `C¹`, with
  `DX(x) v = η(u) v + η'(u) (2/s²) ⟪x - z, v⟫ (x - z)` and `tsupport X ⊆ B̄_s(z) ⊆ B_r(z)`. -/
  let X : Euclid P → Euclid P := fun x => η (‖x - z‖ ^ 2 / s ^ 2) • (x - z)
  have hXd : ∀ x, HasFDerivAt X
      (η (‖x - z‖ ^ 2 / s ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
        ((deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2)) • innerSL ℝ (x - z)).smulRight
          (x - z)) x := by
    intro x
    have h1 : HasFDerivAt (fun x : Euclid P => x - z) (ContinuousLinearMap.id ℝ _) x :=
      (hasFDerivAt_id x).sub_const z
    have h3 : HasFDerivAt (fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2)
        ((s ^ 2)⁻¹ • (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ (Euclid P)))) x := by
      simpa only [div_eq_mul_inv] using HasFDerivAt.mul_const h1.norm_sq (s ^ 2)⁻¹
    have h5 := ((hηd (‖x - z‖ ^ 2 / s ^ 2)).comp_hasFDerivAt x h3).smul h1
    refine HasFDerivAt.congr_fderiv (f := X) h5 (ContinuousLinearMap.ext fun v => ?_)
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      ContinuousLinearMap.comp_apply, Function.comp_apply, smul_eq_mul]
    congr 2
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hXcd : ContDiff ℝ 1 X := by
    have h1 : ContDiff ℝ 1 (fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2) :=
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _
    exact (hη.comp h1).smul (contDiff_id.sub contDiff_const)
  have hXzero : ∀ x, x ∉ closedBall z s → X x = 0 := by
    intro x hx
    show η (‖x - z‖ ^ 2 / s ^ 2) • (x - z) = 0
    rw [hη1 _ (hu_gt x hx).le, zero_smul]
  have hXts : tsupport X ⊆ closedBall z s := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra h
    exact hx (hXzero x h)
  have hXcs : HasCompactSupport X := HasCompactSupport.intro hBc hXzero
  /- Step 2.  `μ`-a.e. the tangent projection is `∑ᵢ τᵢ ⟪τᵢ, ·⟫` for an orthonormal family `τ`
  of size `n` (`R.orients` and uniqueness of approximate tangent spaces). -/
  have hproj : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      (Submodule.span ℝ (range τ)).starProjection =
        ∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) := by
    intro τ hτ
    let b0 := Module.Basis.span hτ.linearIndependent
    have hb0 : ∀ i, (b0 i : Euclid P) = τ i := fun i =>
      congrArg Subtype.val (Module.Basis.span_apply hτ.linearIndependent i)
    have hb0o : Orthonormal ℝ b0 := by
      have e : (Submodule.span ℝ (range τ)).subtypeₗᵢ ∘ b0 = τ := funext hb0
      rw [← (Submodule.span ℝ (range τ)).subtypeₗᵢ.orthonormal_comp_iff, e]
      exact hτ
    rw [OrthonormalBasis.starProjection_eq_sum_rankOne (b0.toOrthonormalBasis hb0o),
      Module.Basis.coe_toOrthonormalBasis]
    simp only [hb0]
  have hμac : μ ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hPae : ∀ᵐ x ∂μ, ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧
      (approxTangentPlane n R.carrier x).starProjection =
        ∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) := by
    refine hμac.ae_le ?_
    filter_upwards [R.orients] with x ⟨Q, hQ, τ, hτ, hspan, _⟩
    have hex : ∃ Q', HasApproximateTangentSpaceAt n R.carrier x Q' := ⟨Q, hQ⟩
    have happrox : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    exact ⟨τ, hτ, by rw [happrox, ← hspan, hproj τ hτ]⟩
  /- Step 3.  `div_M X = n η(u) + η'(u) (2/s²) ∑ᵢ ⟪τᵢ, x - z⟫²`, and by Bessel's inequality and
  `η' ≤ 0`, `n η(u) + 2 u η'(u) ≤ div_M X ≤ n η(u)` `μ`-a.e. -/
  let d : Euclid P → ℝ := fun x => tangentialDivergence n R.carrier X x
  -- `trace ((∑ τᵢ ⊗ τᵢ) ∘ L) = ∑ ⟪τᵢ, L τᵢ⟫`
  have htr : ∀ (τ : Fin n → Euclid P) (L : Euclid P →L[ℝ] Euclid P),
      LinearMap.trace ℝ (Euclid P) ((∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) :
        Euclid P →L[ℝ] Euclid P).toLinearMap ∘ₗ L.toLinearMap) =
        ∑ i, inner ℝ (τ i) (L (τ i)) := by
    intro τ L
    rw [← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.finsetSum_comp,
      ContinuousLinearMap.toLinearMap_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.comp_rankOne,
      InnerProductSpace.trace_rankOne]
  -- Bessel's inequality
  have hbessel : ∀ (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∀ v : Euclid P,
      ∑ i, inner ℝ (τ i) v ^ 2 ≤ ‖v‖ ^ 2 := by
    intro τ hτ v
    have := hτ.sum_inner_products_le (s := Finset.univ) (x := v)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hdae : ∀ᵐ x ∂μ,
      n * η (‖x - z‖ ^ 2 / s ^ 2) + 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ≤
        d x ∧ d x ≤ n * η (‖x - z‖ ^ 2 / s ^ 2) := by
    filter_upwards [hPae] with x ⟨τ, hτ, hPx⟩
    have h1 : ∀ i, inner ℝ (τ i) (τ i) = (1 : ℝ) := fun i => by
      rw [real_inner_self_eq_norm_sq, hτ.1 i, one_pow]
    have e : d x = n * η (‖x - z‖ ^ 2 / s ^ 2) + deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) *
        ∑ i, inner ℝ (τ i) (x - z) ^ 2 := by
      show tangentialDivergence n R.carrier X x = _
      unfold tangentialDivergence
      rw [hPx, (hXd x).fderiv, htr]
      simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, inner_add_right,
        inner_smul_right, h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (x - z) (τ i)]
      ring
    have hb := hbessel τ hτ (x - z)
    have hS0 : 0 ≤ ∑ i, inner ℝ (τ i) (x - z) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hk : deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hη'0 _) (div_nonneg zero_le_two (sq_nonneg s))
    have h2 := mul_le_mul_of_nonpos_left hb hk
    have h3 := mul_nonpos_of_nonpos_of_nonneg hk hS0
    have e2 : deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) * ‖x - z‖ ^ 2 =
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) := by ring
    rw [e]
    exact ⟨e2 ▸ add_le_add le_rfl h2, add_le_of_nonpos_right h3⟩
  /- Step 4.  `div_M X` is `μ`-integrable: it is `AEStronglyMeasurable` (the tangent projection
  is `μ`-measurable, `DX` is continuous, `(A, B) ↦ trace (A ∘ B)` is continuous) and
  `|div_M X| ≤ n η(u) + |2 u η'(u)|` `μ`-a.e. -/
  have hTc : Continuous fun p : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
      LinearMap.trace ℝ (Euclid P) (p.1.toLinearMap ∘ₗ p.2.toLinearMap) := by
    have h1 : Continuous fun A : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) A.toLinearMap :=
      ((LinearMap.trace ℝ (Euclid P)).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact h1.comp (continuous_fst.clm_comp continuous_snd)
  have hPmeas : AEStronglyMeasurable
      (fun x => (approxTangentPlane n R.carrier x).starProjection) μ := hPm.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable d μ := by
    have h3 := hTc.comp_aestronglyMeasurable
      (hPmeas.prodMk (hXcd.continuous_fderiv one_ne_zero).aestronglyMeasurable)
    show AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) μ
    unfold tangentialDivergence
    exact h3
  have hdint : Integrable d μ := by
    refine Integrable.mono' ((hFint.const_mul n).add hGint.abs) hdmeas ?_
    filter_upwards [hdae] with x hx
    have h0 : 0 ≤ (n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) := mul_nonneg (Nat.cast_nonneg n) (hη0 _)
    have hG1 := neg_abs_le (2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2))
    have hG2 := abs_nonneg (2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2))
    show ‖d x‖ ≤ n * η (‖x - z‖ ^ 2 / s ^ 2) +
      |2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)|
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  /- Step 5.  `∫ f dμ = ∫_M θ f dHⁿ`, so `∫ div_M X dμ = R.firstVariation X`. -/
  have hμint : ∀ f : Euclid P → ℝ,
      ∫ x, f x ∂μ = ∫ x in R.carrier, (R.mult x : ℝ) * f x ∂μHE[n] := by
    intro f
    have hθ : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    have hθm : Measurable fun x => (R.mult x : NNReal) :=
      measurable_from_top.comp R.measurable_mult
    rw [hμ, IMRep.measure, hθ, integral_withDensity_eq_integral_smul hθm]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [NNReal.smul_def]
  /- Step 6.  Integrate: `n ∫ η(u) + ∫ 2 u η'(u) ≤ ∫ div_M X = -∫ X · H ≤ κ s ∫ η(u)`, using
  `|X · H| ≤ ‖X‖ κ ≤ κ s η(u)` (`X = 0` off `B̄_s(z)`). -/
  have e1 : (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ +
      ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ =
      ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) +
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) ∂μ := by
    rw [integral_add (hFint.const_mul _) hGint, integral_const_mul]
  have e3 : ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) +
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) ∂μ ≤ ∫ x, d x ∂μ := by
    refine integral_mono_ae ((hFint.const_mul _).add hGint) hdint ?_
    filter_upwards [hdae] with x hx
    exact hx.1
  have e4 : ∫ x, d x ∂μ = -∫ x, inner ℝ (X x) (H x) ∂μ := by
    rw [hμint]
    exact hfv X hXcd hXcs (hXts.trans hBr)
  have e5 : -∫ x, inner ℝ (X x) (H x) ∂μ ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ := by
    have h1 : -∫ x, inner ℝ (X x) (H x) ∂μ ≤ ∫ x, ‖inner ℝ (X x) (H x)‖ ∂μ := by
      refine (neg_le_abs _).trans ?_
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ x, ‖inner ℝ (X x) (H x)‖ ∂μ ≤ ∫ x, κ * s * η (‖x - z‖ ^ 2 / s ^ 2) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hFint.const_mul _)
        (ae_of_all _ fun x => ?_)
      show ‖inner ℝ (X x) (H x)‖ ≤ κ * s * η (‖x - z‖ ^ 2 / s ^ 2)
      by_cases hx : x ∈ closedBall z s
      · have hXn : ‖X x‖ ≤ η (‖x - z‖ ^ 2 / s ^ 2) * s := by
          show ‖η (‖x - z‖ ^ 2 / s ^ 2) • (x - z)‖ ≤ η (‖x - z‖ ^ 2 / s ^ 2) * s
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 _)]
          exact mul_le_mul_of_nonneg_left (by rwa [mem_closedBall, dist_eq_norm] at hx) (hη0 _)
        calc ‖inner ℝ (X x) (H x)‖ ≤ ‖X x‖ * ‖H x‖ := norm_inner_le_norm _ _
          _ ≤ (η (‖x - z‖ ^ 2 / s ^ 2) * s) * κ :=
            mul_le_mul hXn (hHκ x) (norm_nonneg _) (mul_nonneg (hη0 _) hs.le)
          _ = κ * s * η (‖x - z‖ ^ 2 / s ^ 2) := by ring
      · rw [hXzero x hx, inner_zero_left, norm_zero]
        exact mul_nonneg (mul_nonneg hκ0 hs.le) (hη0 _)
    rw [integral_const_mul] at h2
    exact h1.trans h2
  calc (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ +
        ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ = _ := e1
    _ ≤ _ := e3
    _ = _ := e4
    _ ≤ _ := e5
/-- **Radial cutoffs for the monotonicity formula** (Simon Ch. 4, 3.1–3.4).  With
`g = Real.smoothTransition` and `ηⱼ(u) = g((j + 2)(1 − u))`, every `ηⱼ` is `C¹`, nonnegative and
nonincreasing, vanishes for `u ≥ 1`, and `ηⱼ(|x − z|²/s²)` increases to the indicator of the
open ball `B_s(z)`; by dominated convergence `∫ ηⱼ(|x − z|²/s²) dμ → μ(B_s(z))` whenever
`μ(B_s(z)) < ∞`. -/
theorem Submission.dsmc_em_cutoff_tendsto_ball : ∃ η : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (η j)) ∧ (∀ j u, 0 ≤ η j u) ∧ (∀ j u, deriv (η j) u ≤ 0) ∧ (∀ j u, 1 ≤ u → η j u = 0) ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (s : ℝ), 0 < s → μ (ball z s) < ∞ → Tendsto (fun j => ∫ x, η j (‖x - z‖ ^ 2 / s ^ 2) ∂μ) atTop (𝓝 (μ.real (ball z s))) := by
  -- Steps 1–5: `ηⱼ(u) = g((j + 2)(1 − u))` is `C¹`, `≥ 0`, antitone, and `0` for `u ≥ 1`.
  have hanti : ∀ j : ℕ, Antitone fun u : ℝ => Real.smoothTransition (((j : ℝ) + 2) * (1 - u)) := by
    intro j a b hab
    apply Real.smoothTransition.monotone
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    nlinarith
  have hzero : ∀ (j : ℕ) (u : ℝ), 1 ≤ u →
      Real.smoothTransition (((j : ℝ) + 2) * (1 - u)) = 0 := by
    intro j u hu
    apply Real.smoothTransition.zero_of_nonpos
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    nlinarith
  refine ⟨fun j u => Real.smoothTransition (((j : ℝ) + 2) * (1 - u)), fun j => ?_,
    fun j u => Real.smoothTransition.nonneg _, fun j u => (hanti j).deriv_nonpos, hzero, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
  -- Step 6: dominated convergence with the bound `1_{B_s(z)}`.
  intro P μ z s hs hμ
  have hs2 : 0 < s ^ 2 := by positivity
  -- `|x − z|²/s² < 1` exactly on the open ball
  have hlt : ∀ x : Euclid P, x ∈ ball z s → ‖x - z‖ ^ 2 / s ^ 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [div_lt_one hs2]
    exact pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero
  have hge : ∀ x : Euclid P, x ∉ ball z s → 1 ≤ ‖x - z‖ ^ 2 / s ^ 2 := by
    intro x hx
    rw [mem_ball, dist_eq_norm, not_lt] at hx
    rw [one_le_div hs2]
    exact pow_le_pow_left₀ hs.le hx 2
  have hint : Integrable ((ball z s).indicator (1 : Euclid P → ℝ)) μ :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
  rw [← integral_indicator_one measurableSet_ball]
  refine tendsto_integral_of_dominated_convergence ((ball z s).indicator 1)
    (F := fun (j : ℕ) (x : Euclid P) =>
      Real.smoothTransition (((j : ℝ) + 2) * (1 - ‖x - z‖ ^ 2 / s ^ 2)))
    (fun j => ?_) hint (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · -- (a) each integrand is continuous
    exact (Real.smoothTransition.continuous.comp (by fun_prop)).aestronglyMeasurable
  · -- (a) `|ηⱼ(u(x))| ≤ 1_{B_s(z)}(x)`
    by_cases hx : x ∈ ball z s
    · rw [indicator_of_mem hx, Pi.one_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rw [indicator_of_notMem hx, hzero j _ (hge x hx), norm_zero]
  · -- (b) pointwise convergence to `1_{B_s(z)}(x)`
    by_cases hx : x ∈ ball z s
    · rw [indicator_of_mem hx, Pi.one_apply]
      have hpos : 0 < 1 - ‖x - z‖ ^ 2 / s ^ 2 := sub_pos.2 (hlt x hx)
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / (1 - ‖x - z‖ ^ 2 / s ^ 2))
      rw [div_le_iff₀ hpos] at hN
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun j hj => ?_⟩)
      have hj : (N : ℝ) ≤ j := by exact_mod_cast hj
      refine (Real.smoothTransition.one_of_one_le ?_).symm
      nlinarith
    · rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun j => (hzero j _ (hge x hx)).symm

/-- **Monotonicity of `e^{κρ} ρ⁻ⁿ μ_R(B_ρ(z))` under bounded generalized mean curvature**
(Simon Ch. 4, 3.14–3.17).  If `δV(X) = -∫ X · H dμ_R` for `C¹` fields `X` supported in `B_r(z)`,
`B̄_r(z) ⊆ U` and `|H| ≤ κ`, then `e^{κs} s⁻ⁿ μ_R(B_s(z))` is nondecreasing on `(0, r]`.  For each
radial cutoff `ηⱼ`, `I(s) = ∫ ηⱼ(|x - z|²/s²) dμ_R` satisfies `n I - s I' ≤ κ s I` on `(0, r)`, so
`e^{κs} s⁻ⁿ I(s)` is nondecreasing; letting `j → ∞` gives `I(s) → μ_R(B_s(z))`. -/
theorem Submission.dsmc_exp_ball_mass_monotone : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ r → ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (ball z σ) ≤ ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n) * R.measure (ball z ρ) := by
  intro P n U R H κ z r hzU hPm _ hHκ hfv σ ρ hσ hσρ hρr
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- (a) `μ(B̄_r(z)) < ∞` (`R.locallyIntegrable_mult`), so `μ(B_t(z)) < ∞` for `t ≤ r`
  have hμB : R.measure (closedBall z r) < ∞ := by
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult _ (isCompact_closedBall z r) hzU)
  have hμt : ∀ t, t ≤ r → R.measure (ball z t) < ∞ := fun t ht =>
    (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall ht))).trans_lt hμB
  -- (b) for each cutoff `ηⱼ`, `e^{κs} s⁻ⁿ ∫ ηⱼ(|x - z|²/s²) dμ` is nondecreasing on `(0, r]`
  obtain ⟨η, hηC, hη0, hη'0, hη1, hlim⟩ := Submission.dsmc_em_cutoff_tendsto_ball
  have hj : ∀ j, Real.exp (κ * σ) / σ ^ n * ∫ x, η j (‖x - z‖ ^ 2 / σ ^ 2) ∂R.measure ≤
      Real.exp (κ * ρ) / ρ ^ n * ∫ x, η j (‖x - z‖ ^ 2 / ρ ^ 2) ∂R.measure := by
    intro j
    obtain ⟨hcont, hderiv⟩ := Submission.dsmc_em_cutoff_integral_hasDerivAt P R.measure z r (η j)
      (hμt r le_rfl) (hηC j) (hη1 j)
    refine Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq n κ r _ _ hcont hderiv (fun s hs => ?_)
      ⟨hσ, hσρ.trans hρr⟩ ⟨hρ, hρr⟩ hσρ
    -- `n I(s) - s I'(s) = n I(s) + ∫ 2 u η'(u) dμ ≤ κ s I(s)`
    have h := Submission.dsmc_em_cutoff_first_variation_le P n U R H κ z r (η j) hzU hPm hHκ hfv
      (hηC j) (hη0 j) (hη'0 j) (hη1 j) s hs.1 hs.2
    rw [mul_div_cancel₀ _ hs.1.ne', sub_neg_eq_add]
    exact h
  -- (c) let `j → ∞`: the integrals tend to `μ(B_σ(z))` and `μ(B_ρ(z))`
  have hreal : Real.exp (κ * σ) / σ ^ n * R.measure.real (ball z σ) ≤
      Real.exp (κ * ρ) / ρ ^ n * R.measure.real (ball z ρ) :=
    le_of_tendsto_of_tendsto'
      ((hlim P R.measure z σ hσ (hμt σ (hσρ.trans hρr))).const_mul _)
      ((hlim P R.measure z ρ hρ (hμt ρ hρr)).const_mul _) hj
  -- (d) transfer to `[0, ∞]`
  rw [← ofReal_measureReal (hμt σ (hσρ.trans hρr)).ne, ← ofReal_measureReal (hμt ρ hρr).ne,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
