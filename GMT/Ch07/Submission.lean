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

/-- `spt(S − T) ⊆ spt S ∪ spt T`.  A point `y ∈ U` outside `spt S ∪ spt T` lies in zero-region
sets `W₁` of `S` and `W₂` of `T`; then `W₁ ∩ W₂` is open, contains `y`, has compact closure in `U`
(a closed subset of `closure W₁`), and `S − T` vanishes on it, so `y ∉ spt(S − T)`. -/
theorem Submission.cbrld_ns_support_sub_subset : ∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n), (S - T).support ⊆ S.support ∪ T.support := by
  intro P n U S T y hy
  obtain ⟨hyU, hyZ⟩ := hy
  by_contra hST
  -- `y ∈ Z(S)` and `y ∈ Z(T)`, since `y ∈ U` lies in neither support
  have hS : y ∈ S.zeroRegion := not_not.mp fun h => hST (Or.inl ⟨hyU, h⟩)
  have hT : y ∈ T.zeroRegion := not_not.mp fun h => hST (Or.inr ⟨hyU, h⟩)
  obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hyW₁⟩ := mem_sUnion.mp hS
  obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hyW₂⟩ := mem_sUnion.mp hT
  -- `W₁ ∩ W₂` belongs to the family whose union is `Z(S − T)`
  have hcl : closure (W₁ ∩ W₂) ⊆ closure W₁ := closure_mono inter_subset_left
  refine hyZ (mem_sUnion.mpr ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o,
    hW₁c.of_isClosed_subset isClosed_closure hcl, hcl.trans hW₁U, ?_⟩, hyW₁, hyW₂⟩)
  -- `(S − T)(ω) = S(ω) − T(ω) = 0 − 0`
  intro ω hω
  change S ω - T ω = 0
  rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
/-- `M_W(S − T) ≤ M_W(S) + M_W(T)`.  For every `W`-admissible `ω`, `−ω` is `W`-admissible as well
(`tsupport (−ω) = tsupport ω`, `|−ω(x)| = |ω(x)|`) and `(S − T)(ω) = S(ω) + T(−ω)`, so
`ofReal((S − T)(ω)) ≤ ofReal(S(ω)) + ofReal(T(−ω)) ≤ M_W(S) + M_W(T)`; take the supremum
over `ω`. -/
theorem Submission.cbrld_ns_massOn_sub_le : ∀ (P n : ℕ) (U W : Set (Euclid P)) (S T : GeometricCurrentOn U n), (S - T).massOn W ≤ S.massOn W + T.massOn W := by
  intro P n U W S T
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- `−ω` is `W`-admissible
  have hneg : -ω ∈ massAdmissibleOn U n W := by
    refine ⟨?_, fun x => ?_⟩
    · show tsupport (-(ω : DifferentialForm (Euclid P) n)) ⊆ W
      rw [tsupport_neg]
      exact hω.1
    · show covectorEuclideanNorm (-(ω : DifferentialForm (Euclid P) n) x) ≤ 1
      rw [covectorEuclideanNorm_neg]
      exact hω.2 x
  -- `(S − T)(ω) = S(ω) + T(−ω)`
  have heq : (S - T) ω = S ω + T (-ω) := by
    rw [show T (-ω) = -T ω from map_neg T.toCurrent ω]
    exact sub_eq_add_neg (S ω) (T ω)
  calc ENNReal.ofReal ((S - T) ω) = ENNReal.ofReal (S ω + T (-ω)) := by rw [heq]
    _ ≤ ENNReal.ofReal (S ω) + ENNReal.ofReal (T (-ω)) := ENNReal.ofReal_add_le
    _ ≤ S.massOn W + T.massOn W := add_le_add (S.le_massOn hω) (T.le_massOn hneg)
/-- **Mass of a current integrating over a ball** (first half of fact 1(e) in the null-set step
of the lower density bound used for Simon 7.2.4): if `|⟨α, ξ(y)⟩| ≤ |α|` for `μ`-a.e. `y` and
`A(ω) = ∫_{B_ρ(x)} ⟨ω(y), ξ(y)⟩ dμ(y)` for all `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `M(A) ≤ μ(B_ρ(x))`.  The bound
is trivial if `μ(B_ρ(x)) = ∞`; otherwise each admissible `ω` (`|ω| ≤ 1`) has
`A(ω) ≤ |∫_{B_ρ(x)} ⟨ω, ξ⟩ dμ| ≤ μ(B_ρ(x))`, and `M(A)` is the supremum of these values. -/
theorem Submission.cbrld_ns_ball_current_mass_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (A : GeometricCurrentOn (univ : Set (Euclid P)) n) (x : Euclid P) (ρ : ℝ), (∀ᵐ y ∂μ, ∀ α : Covector (Euclid P) n, |ξ y α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, A ω = ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ) → A.mass ≤ μ (ball x ρ) := by
  intro P n μ ξ A x ρ hξ hA
  -- the bound is trivial if `μ(B_ρ(x)) = ∞`
  rcases eq_top_or_lt_top (μ (ball x ρ)) with htop | hfin
  · exact htop ▸ le_top
  -- `M(A)` is the supremum of `A(ω)` over admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- `|⟨ω(y), ξ(y)⟩| ≤ |ω(y)| ≤ 1` for `μ⌞B_ρ(x)`-a.e. `y`
  have hbound : ∀ᵐ y ∂μ.restrict (ball x ρ),
      ‖ξ y ((ω : DifferentialForm (Euclid P) n) y)‖ ≤ 1 :=
    ae_restrict_of_ae (hξ.mono fun y hy => (Real.norm_eq_abs _).trans_le ((hy _).trans (hω.2 y)))
  have hle : A ω ≤ (μ (ball x ρ)).toReal := by
    rw [hA ω]
    calc ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ
        ≤ ‖∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ‖ := Real.le_norm_self _
      _ ≤ 1 * μ.real (ball x ρ) := norm_setIntegral_le_of_norm_le_const_ae hfin hbound
      _ = (μ (ball x ρ)).toReal := by rw [one_mul, measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).2 hle
/-- `spt A ⊆ B̄_ρ(x)` when `A(ω) = ∫_{B_ρ(x)} ⟨ω(y), ξ(y)⟩ dμ(y)` for every test form `ω`.  If
`|y − x| > ρ`, then `W = B_r(y)`, `r = (|y − x| − ρ)/2 > 0`, is open with compact closure and
misses `B_ρ(x)`, so every test form supported in `W` vanishes on `B_ρ(x)` and `A` vanishes on `W`;
hence `y` lies in the zero region of `A` (Simon 6.2.11). -/
theorem Submission.cbrld_ns_ball_current_support_subset : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (A : GeometricCurrentOn (univ : Set (Euclid P)) n) (x : Euclid P) (ρ : ℝ), (∀ ω : TestFormOn (univ : Set (Euclid P)) n, A ω = ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ) → A.support ⊆ closedBall x ρ := by
  intro P n μ ξ A x ρ hA y hy
  by_contra hyx
  rw [mem_closedBall, not_le] at hyx
  -- `A` vanishes on `B_r(y)`, `r = (|y − x| − ρ)/2 > 0`, so `y` lies in the zero region of `A`
  have hr : 0 < (dist y x - ρ) / 2 := by linarith
  refine hy.2 (mem_sUnion_of_mem (mem_ball_self hr) ⟨isOpen_ball, ?_, subset_univ _, ?_⟩)
  · -- `closure B_r(y) ⊆ B̄_r(y)`, which is compact in the proper space `ℝᴾ`
    exact (isCompact_closedBall y _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  · -- a test form supported in `B_r(y)` vanishes at every `z ∈ B_ρ(x)`, since `|z − y| > r`
    intro ω hω
    rw [hA ω]
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hzω : z ∉ tsupport (ω : DifferentialForm (Euclid P) n) := by
      intro hz'
      have hzy := hω hz'
      rw [mem_ball] at hz hzy
      linarith [dist_triangle y z x, dist_comm z y]
    rw [image_eq_zero_of_notMem_tsupport hzω, map_zero]
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

/-- **Test forms are Lipschitz in the Euclidean coefficient norm** (the constant `c` of the cone
inequality, Simon Ch. 6, 2.27/2.30 as used in 8.2(4)–(6)).  `ω` is `C^∞` with compact support, so
`Dω` is continuous with compact support and `‖Dω(z)‖ ≤ L₀` for some `L₀ ≥ 0`; the mean value
inequality on the convex set `ℝᴾ` gives `‖ω(x) - ω(y)‖ ≤ L₀ ‖x - y‖`.  With the bound
`covectorEuclideanNorm β ≤ C ‖β‖` of `Submission.rsd_mw_tfa_norm_props`, `c = C L₀` works. -/
theorem Submission.cbrld_cone_testForm_coeff_lipschitz : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : Euclid P, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y) ≤ c * dist x y := by
  intro P k U ω
  -- Step 1: the coefficient norm is dominated by the operator norm, `|β| ≤ C ‖β‖`
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P k).2.2.1
  -- Step 2: `ω` is smooth with compact support, so `Dω` is continuous with compact support
  have hsm : IsSmoothForm (ω : DifferentialForm (Euclid P) k) := ω.property.1.1
  have hcs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.property.1.2
  have hcont : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) :=
    hsm.continuous_fderiv (by simp)
  have hcs' : HasCompactSupport (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) := hcs.fderiv ℝ
  -- Step 3: `Dω` is bounded, `‖Dω(z)‖ ≤ L ≤ max L 0`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ z, ‖fderiv ℝ (ω : DifferentialForm (Euclid P) k) z‖ ≤ L :=
    Continuous.bounded_above_of_compact_support
      (f := fderiv ℝ (ω : DifferentialForm (Euclid P) k)) hcont hcs'
  -- Step 4: the mean value inequality on the convex set `ℝᴾ`
  have hdiff : Differentiable ℝ (ω : DifferentialForm (Euclid P) k) :=
    hsm.differentiable (by simp)
  have hmv : ∀ x y : Euclid P, ‖(ω : DifferentialForm (Euclid P) k) x -
      (ω : DifferentialForm (Euclid P) k) y‖ ≤ max L 0 * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => (hL z).trans (le_max_left _ _)) (mem_univ y) (mem_univ x)
  -- Step 5: `c = C · max L 0`
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right _ _), fun x y => ?_⟩
  have h1 := hC ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y)
  have h2 := mul_le_mul_of_nonneg_left (hmv x y) hC0
  rw [dist_eq_norm]
  calc covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x -
        (ω : DifferentialForm (Euclid P) k) y)
      ≤ C * ‖(ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y‖ := h1
    _ ≤ C * (max L 0 * ‖x - y‖) := h2
    _ = C * max L 0 * ‖x - y‖ := by ring
/-- **Simon 6.2.25, 6.2.30** (homotopy formula for a constant form): the affine contraction
`ψ(y) = (n + 1)⁻¹ • α.curryLeft (y - x₀)`, i.e. `ψ(y)(v₁, …, vₙ) = (n + 1)⁻¹ α(y - x₀, v₁, …, vₙ)`,
is a primitive of the constant `(n + 1)`-covector `α`.  Its derivative is the constant map
`(n + 1)⁻¹ • α.curryLeft`, and alternatizing `α.curryLeft` gives `(n + 1) • α`. -/
theorem Submission.cbrld_cone_extDeriv_affine_contraction : ∀ (P n : ℕ) (α : Covector (Euclid P) (n + 1)) (x₀ x : Euclid P), extDeriv (fun y : Euclid P => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀)) x = α := by
  intro P n α x₀ x
  -- `y ↦ α.curryLeft (y - x₀)` is affine with linear part `α.curryLeft`
  have h1 : HasFDerivAt (fun y : Euclid P => α.curryLeft (y - x₀)) α.curryLeft x := by
    have h := (α.curryLeft.hasFDerivAt (x := x - x₀)).comp x ((hasFDerivAt_id x).sub_const x₀)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hd : HasFDerivAt (fun y : Euclid P => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀))
      (((n : ℝ) + 1)⁻¹ • α.curryLeft) x := h1.const_smul (((n : ℝ) + 1)⁻¹)
  -- `extDeriv ψ x = (n + 1)⁻¹ • alternatizeUncurryFin α.curryLeft = (n + 1)⁻¹ • (n + 1) • α`
  rw [extDeriv, hd.fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_smul,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [inv_mul_cancel₀ hn, one_smul]
/-- **Localization to a neighbourhood of `spt X`** (Simon 6.2.11): assuming (VO), i.e. that a
current kills every test form whose support misses its support, a current `X` takes the same
value on test forms `φ₁`, `φ₂` that agree on an open set `G ⊇ spt X`.  The difference `φ₁ - φ₂`
vanishes on `G`, so its topological support lies in the closed set `Gᶜ`, which misses `spt X`;
(VO) and linearity give `X(φ₁) - X(φ₂) = X(φ₁ - φ₂) = 0`. -/
theorem Submission.cbrld_cone_eval_eq_of_eqOn_open : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P k : ℕ) (U G : Set (Euclid P)) (X : GeometricCurrentOn U k) (φ₁ φ₂ : TestFormOn U k), IsOpen G → X.support ⊆ G → EqOn (φ₁ : DifferentialForm (Euclid P) k) (φ₂ : DifferentialForm (Euclid P) k) G → X φ₁ = X φ₂ := by
  intro VO P k U G X φ₁ φ₂ hG hspt heq
  -- `φ₁ - φ₂` vanishes on the open set `G`, so its topological support lies in `Gᶜ`
  have hsub : tsupport ((φ₁ - φ₂ : TestFormOn U k) : DifferentialForm (Euclid P) k) ⊆ Gᶜ := by
    apply closure_minimal _ hG.isClosed_compl
    intro x hx hxG
    apply hx
    change (φ₁ : DifferentialForm (Euclid P) k) x - (φ₂ : DifferentialForm (Euclid P) k) x = 0
    rw [heq hxG, sub_self]
  -- hence it misses `spt X ⊆ G`, and (VO) kills it
  have hdisj : Disjoint (tsupport ((φ₁ - φ₂ : TestFormOn U k) : DifferentialForm (Euclid P) k))
      X.support :=
    Disjoint.mono hsub hspt disjoint_compl_left
  have h := VO P k U X (φ₁ - φ₂) hdisj
  -- linearity of `X`
  have h2 := X.toCurrent.map_sub φ₁ φ₂
  change X (φ₁ - φ₂) = X φ₁ - X φ₂ at h2
  linarith
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2

/-- **Constant forms are boundaries near the support of a cycle** (steps 5 and 7 of the cone
inequality used in Simon Ch. 6, 8.2(4)–(6), via the homotopy formula 2.25 and the cone 2.30).
Assume (VO), the vanishing of a current on test forms supported off its support.  If
`X ∈ 𝒟_{n+1}(ℝᴾ)` has `∂X = 0` and `spt X ⊆ B_r(x₀)`, and the test form `φ` equals the constant
covector `α` on `B_r(x₀)`, then `X(φ) = 0`.  With the bump `ζ` (`ζ = 1` on `B̄_r(x₀)`) and the
primitive `ψ(y) = (n + 1)⁻¹ ι_{y−x₀} α` of `α` (`cbrld_cone_extDeriv_affine_contraction`), the
test form `η = ζψ` has `dη = dψ = α = φ` on `B_r(x₀)`, so `cbrld_cone_eval_eq_of_eqOn_open` gives
`X(φ) = X(dη) = ∂X(η) = 0`. -/
theorem Submission.cbrld_cone_cycle_eval_eq_zero_of_const_on_ball : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)) (x₀ : Euclid P) (r : ℝ) (α : Covector (Euclid P) (n + 1)) (φ : TestFormOn (univ : Set (Euclid P)) (n + 1)), 0 < r → X.boundary = 0 → X.support ⊆ ball x₀ r → (∀ x ∈ ball x₀ r, (φ : DifferentialForm (Euclid P) (n + 1)) x = α) → X φ = 0 := by
  intro VO P n X x₀ r α φ hr hbd hspt hφ
  -- Step 1: the cut-off `ζ`, equal to `1` on `B̄_r(x₀)`
  let ζ : ContDiffBump x₀ := ⟨r, r + 1, hr, by linarith⟩
  -- Step 2: the affine primitive `ψ` of `α`
  let ψ : DifferentialForm (Euclid P) n := fun y => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀)
  have hψ : IsSmoothForm ψ :=
    (α.curryLeft.contDiff.comp (contDiff_id.sub contDiff_const)).const_smul _
  -- Step 3: the compactly supported primitive `η = ζψ`
  let g : DifferentialForm (Euclid P) n := fun y => ζ y • ψ y
  have hg : IsSmoothForm g := ζ.contDiff.smul hψ
  have hgc : HasCompactSupport g := ζ.hasCompactSupport.smul_right
  let η : TestFormOn (univ : Set (Euclid P)) n := ⟨g, ⟨hg, hgc⟩, subset_univ _⟩
  -- Step 4: `X(dη) = ∂X(η) = 0`
  have h0 : X (exteriorDerivativeTestOn univ n η) = 0 := by
    have h := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) n => T η) hbd
    simpa using h
  -- Step 5: `φ = dη` on `B_r(x₀)`, since `η = ψ` near each point of the ball
  have heq : EqOn (φ : DifferentialForm (Euclid P) (n + 1))
      ((exteriorDerivativeTestOn univ n η : TestFormOn (univ : Set (Euclid P)) (n + 1)) :
        DifferentialForm (Euclid P) (n + 1)) (ball x₀ r) := by
    intro y hy
    rw [hφ y hy]
    change α = extDeriv g y
    have hev : g =ᶠ[𝓝 y] ψ := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      simp [g, ζ.one_of_mem_closedBall (ball_subset_closedBall hz)]
    rw [hev.extDeriv_eq, Submission.cbrld_cone_extDeriv_affine_contraction P n α x₀ y]
  -- Step 6: localization to the open ball containing `spt X`
  rw [Submission.cbrld_cone_eval_eq_of_eqOn_open VO P (n + 1) univ (ball x₀ r) X φ _ isOpen_ball
    hspt heq, h0]
/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem)**, from the scaled deformation theorem 5.3 in the
frozen form (DT), with constant `c ≥ 1` for `(P, m)`.  Let `Z ∈ 𝒟_{m+1}(ℝᴾ)` be integer
multiplicity with `spt Z` compact, `∂Z = 0` and `z = M(Z) < ∞`.  Apply (DT) to `T = Z` with
`K = spt Z`, `Λ = z` and `ρ = (2cz)^{1/(m+1)}` (`ρ = 1` if `z = 0`).  A current of zero mass is
zero (test `±sω` with `s‖ω‖_∞ ≤ 1`), so `M(S) ≤ cρ M(∂Z) = 0` gives `S = 0`, and
`M(Q) ≤ cz < ρ^{m+1}` excludes the second alternative, so `Q = 0` and `Z = ∂R`.  Then `Y = R` has
the mass and support bounds of (DT); if `z = 0`, also `M(R) = 0`, so `spt R = ∅`. -/
theorem Submission.cbr_isoperimetric_filling : (∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → ∀ (P m : ℕ), ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support := by
  intro hDT P m
  obtain ⟨c, hc1, hDT⟩ := hDT P m
  refine ⟨(c : ℝ), by exact_mod_cast hc1, ?_⟩
  intro Z hZ hZc hZb hZm
  -- `M(0) = 0` and `spt 0 = ∅`
  have hmass0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).mass = 0 := by
    intro k
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  have hsupp0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).support = ∅ := by
    intro k
    refine eq_empty_of_forall_notMem fun x hx => hx.2 ?_
    exact ⟨ball x 1, ⟨isOpen_ball, isBounded_ball.isCompact_closure, subset_univ _,
      fun ω _ => rfl⟩, mem_ball_self one_pos⟩
  -- the Euclidean coefficient norm is absolutely homogeneous
  have hhom : ∀ (k : ℕ) (t : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro k t α
    simp only [covectorEuclideanNorm]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- a current of zero mass is zero: test `±sω` with `s‖ω‖_∞ ≤ 1`
  have hzero : ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), X.mass = 0 →
      X = 0 := by
    intro k X hX
    ext ω
    have hω : Continuous (ω : DifferentialForm (Euclid P) k) := ω.property.1.1.continuous
    have hfc : Continuous (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) := by
      simp only [Function.comp_def, covectorEuclideanNorm]
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => ((continuous_eval_const _).comp hω).pow 2)
        fun _ => continuous_const
    have hcs : HasCompactSupport (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) :=
      ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k)
    obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hcs
    obtain ⟨s, hs, hsC⟩ : ∃ s : ℝ, 0 < s ∧ s * (|C| + 1) = 1 :=
      ⟨(|C| + 1)⁻¹, by positivity, inv_mul_cancel₀ (by positivity)⟩
    have hadm : ∀ t : ℝ, |t| ≤ s → t • ω ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      intro t ht
      refine ⟨subset_univ _, fun x => ?_⟩
      show covectorEuclideanNorm (t • (ω : DifferentialForm (Euclid P) k) x) ≤ 1
      rw [hhom]
      have h0 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
      have h1 : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ |C| + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg h0] at this
        linarith [le_abs_self C]
      calc |t| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x)
          ≤ s * (|C| + 1) := mul_le_mul ht h1 h0 hs.le
        _ = 1 := hsC
    have hX' : X.massOn univ = 0 := hX
    have h1 := X.le_massOn (hadm s (abs_of_pos hs).le)
    have h2 := X.le_massOn (hadm (-s) (by rw [abs_neg, abs_of_pos hs]))
    rw [hX', nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1 h2
    have e1 : X (s • ω) = s * X ω := map_smul X.toCurrent s ω
    have e2 : X ((-s) • ω) = -(s * X ω) := by
      rw [show X ((-s) • ω) = -s * X ω from map_smul X.toCurrent (-s) ω]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have h3 : s * X ω = 0 := by linarith
    rw [GeometricCurrentOn.zero_apply]
    exact (mul_eq_zero.1 h3).resolve_left hs.ne'
  -- the scale `ρ`
  set z : ℝ := Z.mass.toReal
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  have hZmz : Z.mass = ENNReal.ofReal z := (ENNReal.ofReal_toReal hZm.ne).symm
  have hc0 : (0 : ℝ) ≤ c := c.coe_nonneg
  have hc0' : (0 : ℝ) < c := by exact_mod_cast zero_lt_one.trans_le hc1
  have hcz0 : 0 ≤ (c : ℝ) * z := mul_nonneg hc0 hz0
  obtain ⟨ρ, hρ0, hρlt, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ (c : ℝ) * z < ρ ^ (m + 1) ∧
      (z = 0 ∨ ρ = (2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) := by
    rcases hz0.eq_or_lt with h | h
    · exact ⟨1, one_pos, by rw [← h]; simp, Or.inl h.symm⟩
    · have hcz : 0 < 2 * (c : ℝ) * z := mul_pos (mul_pos two_pos hc0') h
      refine ⟨_, Real.rpow_pos_of_pos hcz _, ?_, Or.inr rfl⟩
      have hpow : ((2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = 2 * (c : ℝ) * z := by
        rw [one_div, ← Nat.cast_succ]
        exact Real.rpow_inv_natCast_pow hcz.le (Nat.succ_ne_zero m)
      rw [hpow]
      have : 0 < (c : ℝ) * z := mul_pos hc0' h
      linarith
  have hcρ : 0 ≤ (c : ℝ) * ρ := mul_nonneg hc0 hρ0.le
  -- apply (DT) to `T = Z`
  obtain ⟨𝒬, -, hDT⟩ := hDT ρ Z.support Z.mass.toNNReal hρ0 hZc
  obtain ⟨Q, -, R, S, -, -, hR, hZQS, hQ, hQm, -, hRm, hSm, hQR, -⟩ :=
    hDT Z hZ subset_rfl (ENNReal.coe_toNNReal hZm.ne).ge
      (by rw [hZb, hmass0]; exact ENNReal.zero_lt_top)
  -- `M(S) ≤ cρ M(∂Z) = 0`, so `S = 0`
  rw [hZb, hmass0, mul_zero, nonpos_iff_eq_zero] at hSm
  obtain rfl : S = 0 := hzero _ S hSm
  -- `M(Q) ≤ cz < ρ^{m+1}`, so `Q = 0`
  obtain rfl : Q = 0 := by
    refine hQ.resolve_right fun h => ?_
    have h' := h.trans hQm
    rw [hZmz, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_le_ofReal_iff hcz0] at h'
    linarith
  -- hence `Z = ∂R`
  have hRZ : R.boundary = Z := by
    rw [← hZQS]
    ext ω
    show Z ω - 0 - 0 = Z ω
    ring
  rcases hρ with h | rfl
  · -- `z = 0`: `M(R) ≤ cρ · 0 = 0`, so `R = 0`
    rw [hZmz, h, ENNReal.ofReal_zero, mul_zero, nonpos_iff_eq_zero] at hRm
    refine ⟨R, hR, hRZ, hRm.trans_le zero_le, ?_⟩
    rw [hzero _ R hRm, hsupp0]
    exact empty_subset _
  · refine ⟨R, hR, hRZ, hRm.trans (le_of_eq ?_), subset_union_right.trans hQR⟩
    rw [ENNReal.ofReal_mul hcρ, ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal, hZmz]

/-- **Cone inequality for small cycles** (Simon Ch. 6, 2.27/2.30, as used in 8.2(4)–(6)).  Assume
(VO) and let `c ≥ 0` be a Lipschitz constant of `ω` in the Euclidean coefficient norm.  If
`∂X = 0`, `M(X) < ∞` and `spt X ⊆ B̄_ϱ(x₀)`, fix `ε > 0`, a bump `ζ` with `ζ = 1` on
`B̄_{ϱ+ε/2}(x₀)` and `ζ = 0` off `B_{ϱ+ε}(x₀)`, `α := ω(x₀)` and `φ := ζ (ω - α)`.  Then
`ω - φ = α` on `B_{ϱ+ε/2}(x₀) ⊇ spt X`, so `X(ω - φ) = 0` (a constant form is exact near `spt X`
and `∂X = 0`), while `|φ(x)| = ζ(x) |ω(x) - ω(x₀)| ≤ c (ϱ + ε)`.  Hence
`|X(ω)| = |X(φ)| ≤ c (ϱ + ε) M(X)`, and `ε ↓ 0` gives the claim. -/
theorem Submission.cbrld_cycle_eval_le_radius_mul_mass : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (n + 1)), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)) (x₀ : Euclid P) (ϱ : ℝ), 0 < ϱ → X.boundary = 0 → X.mass < ∞ → X.support ⊆ closedBall x₀ ϱ → |X ω| ≤ c * ϱ * X.mass.toReal := by
  intro VO P n ω
  -- the constant depends only on `ω`: a Lipschitz constant in the coefficient norm
  obtain ⟨c, hc0, hc⟩ := Submission.cbrld_cone_testForm_coeff_lipschitz P (n + 1) univ ω
  refine ⟨c, hc0, fun X x₀ ϱ hϱ hbd hM hspt => ?_⟩
  have hsmul := (Submission.rsd_mw_tfa_norm_props P (n + 1)).2.1
  let α : Covector (Euclid P) (n + 1) := (ω : DifferentialForm (Euclid P) (n + 1)) x₀
  -- `|X(ω)| ≤ c (ϱ + ε) M(X)` for every `ε > 0`
  have hbound : ∀ ε : ℝ, 0 < ε → |X ω| ≤ c * (ϱ + ε) * X.mass.toReal := by
    intro ε hε
    -- the cut-off: `ζ = 1` on `B̄_{ϱ+ε/2}(x₀)` and `ζ = 0` off `B_{ϱ+ε}(x₀)`
    let ζ : ContDiffBump x₀ := ⟨ϱ + ε / 2, ϱ + ε, by linarith, by linarith⟩
    -- the test form `φ = ζ (ω - α)`
    let φ : TestFormOn (univ : Set (Euclid P)) (n + 1) :=
      ⟨fun x => ζ x • ((ω : DifferentialForm (Euclid P) (n + 1)) x - α),
        ⟨ζ.contDiff.smul (ContDiff.sub ω.property.1.1 contDiff_const),
          ζ.hasCompactSupport.smul_right⟩, subset_univ _⟩
    -- `ω - φ = α` on `B_{ϱ+ε/2}(x₀) ⊇ spt X`, so the cycle `X` kills `ω - φ`
    have hconst : ∀ x ∈ ball x₀ (ϱ + ε / 2),
        ((ω - φ : TestFormOn (univ : Set (Euclid P)) (n + 1)) :
          DifferentialForm (Euclid P) (n + 1)) x = α := by
      intro x hx
      change (ω : DifferentialForm (Euclid P) (n + 1)) x -
        ζ x • ((ω : DifferentialForm (Euclid P) (n + 1)) x - α) = α
      rw [ζ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul, sub_sub_cancel]
    have h0 : X (ω - φ) = 0 :=
      Submission.cbrld_cone_cycle_eval_eq_zero_of_const_on_ball VO P n X x₀ (ϱ + ε / 2) α
        (ω - φ) (by linarith) hbd (hspt.trans (closedBall_subset_ball (by linarith))) hconst
    have hXφ : X ω = X φ := by
      have h := map_sub X.toCurrent ω φ
      change X (ω - φ) = X ω - X φ at h
      linarith
    -- `|φ(x)| = ζ(x) |ω(x) - ω(x₀)| ≤ c (ϱ + ε)`
    have hφ : ∀ x, covectorEuclideanNorm ((φ : DifferentialForm (Euclid P) (n + 1)) x) ≤
        c * (ϱ + ε) := by
      intro x
      change covectorEuclideanNorm (ζ x • ((ω : DifferentialForm (Euclid P) (n + 1)) x - α)) ≤
        c * (ϱ + ε)
      rw [hsmul, abs_of_nonneg (ζ.nonneg' x)]
      by_cases hx : dist x x₀ < ϱ + ε
      · calc ζ x * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (n + 1)) x - α)
            ≤ 1 * (c * (ϱ + ε)) :=
              mul_le_mul ζ.le_one ((hc x x₀).trans (mul_le_mul_of_nonneg_left hx.le hc0))
                (covectorEuclideanNorm_nonneg _) zero_le_one
          _ = c * (ϱ + ε) := one_mul _
      · rw [ζ.zero_of_le_dist (not_lt.1 hx), zero_mul]
        exact mul_nonneg hc0 (by linarith)
    rw [hXφ]
    exact Submission.cmr_abs_apply_le_massOn P (n + 1) univ univ X φ (c * (ϱ + ε)) hM.ne
      (subset_univ _) hφ
  -- let `ε ↓ 0`
  have hlim : Tendsto (fun ε : ℝ => c * (ϱ + ε) * X.mass.toReal) (𝓝[>] 0)
      (𝓝 (c * ϱ * X.mass.toReal)) := by
    have h := (show Continuous fun ε : ℝ => c * (ϱ + ε) * X.mass.toReal by fun_prop).tendsto 0
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
/-- **Simon Ch. 1, Remark 3.11(3)** (via the Besicovitch Covering Lemma 3.12), with the balls
chosen inside an open set as in the proof of Theorem 3.13: let `μ` be finite on compact subsets of
`ℝᴾ`, `W` open and `E ⊆ W` (not necessarily measurable).  If every `x ∈ E` admits arbitrarily small
radii `ρ > 0` with `Q x ρ`, then countably many pairwise disjoint closed balls
`B̄_{r(x)}(x) ⊆ W`, `x ∈ t ⊆ E`, with `Q x (r x)`, cover `μ`-almost all of `E`.  Apply the
measurable Besicovitch covering theorem to the admissible radii `{ρ | B̄_ρ(x) ⊆ W ∧ Q x ρ}`. -/
theorem Submission.cbrldvc_exists_disjoint_closedBall_cover : ∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Euclid P → ℝ → Prop) (E W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → IsOpen W → E ⊆ W → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q x ρ) → ∃ (t : Set (Euclid P)) (r : Euclid P → ℝ), t.Countable ∧ t ⊆ E ∧ (∀ x ∈ t, 0 < r x ∧ closedBall x (r x) ⊆ W ∧ Q x (r x)) ∧ t.PairwiseDisjoint (fun x => closedBall x (r x)) ∧ μ (E \ ⋃ x ∈ t, closedBall x (r x)) = 0 := by
  intro P μ Q E W hK hW hEW hQ
  -- finite on compacts, hence s-finite on the proper space `ℝᴾ`
  have : IsFiniteMeasureOnCompacts μ := ⟨hK⟩
  -- admissible radii: shrink below the radius `R` of an open ball `B_R(x) ⊆ W`
  have hf : ∀ x ∈ E, ∀ δ > 0, ({ρ | closedBall x ρ ⊆ W ∧ Q x ρ} ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW x (hEW hx)
    obtain ⟨ρ, hρ, hρδ, hQρ⟩ := hQ x hx (min δ R) (lt_min hδ hR)
    exact ⟨ρ, ⟨(closedBall_subset_ball (hρδ.trans_le (min_le_right _ _))).trans hRW, hQρ⟩, hρ,
      hρδ.trans_le (min_le_left _ _)⟩
  obtain ⟨t, r, ht, htE, hr, hμ, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae μ
    (fun x => {ρ | closedBall x ρ ⊆ W ∧ Q x ρ}) E hf (fun _ => 1) fun _ _ => zero_lt_one
  exact ⟨t, r, ht, htE, fun x hx => ⟨(hr x hx).2.1, (hr x hx).1.1, (hr x hx).1.2⟩, hdisj, hμ⟩
/-- **Summation over disjoint sets** (step 5 of the lower density bound used for Simon 7.2.4):
if `B(x)`, `x ∈ t`, are countably many disjoint measurable sets with `V = ⋃_{x ∈ t} B(x)` of finite
measure, `g` is integrable on `V` and `∫_{B(x)} g dμ ≤ θ μ(B(x))` for every `x ∈ t`, then
`∫_V g dμ ≤ θ μ(V)`.  Reindex by the countable subtype `↥t`; countable additivity gives
`∑ᵢ ∫_{B(i)} g dμ = ∫_V g dμ` and `∑ᵢ μ(B(i)) = μ(V) < ∞`, so the real series `∑ᵢ θ μ(B(i))`
converges to `θ μ(V)`, and the two series compare term by term (no sign condition on `θ`). -/
theorem Submission.cbrldvc_setIntegral_biUnion_le_mul_measure : ∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (t : Set (Euclid P)) (B : Euclid P → Set (Euclid P)), t.Countable → (∀ x ∈ t, MeasurableSet (B x)) → t.PairwiseDisjoint B → μ (⋃ x ∈ t, B x) < ∞ → IntegrableOn g (⋃ x ∈ t, B x) μ → (∀ x ∈ t, ∫ y in B x, g y ∂μ ≤ θ * (μ (B x)).toReal) → ∫ y in ⋃ x ∈ t, B x, g y ∂μ ≤ θ * (μ (⋃ x ∈ t, B x)).toReal := by
  intro P μ g θ t B ht hB hd hfin hg hle
  -- reindex `⋃ x ∈ t, B x` as `⋃ i : t, B i` over the countable subtype
  have : Countable t := ht.to_subtype
  have hBi : ∀ i : t, MeasurableSet (B i) := fun i => hB i i.2
  have hdi : Pairwise (Disjoint on fun i : t => B i) :=
    fun i j hij => hd i.2 j.2 (Subtype.coe_injective.ne hij)
  rw [biUnion_eq_iUnion] at hfin hg ⊢
  -- countable additivity of the integral
  have hint : HasSum (fun i : t => ∫ y in B i, g y ∂μ) (∫ y in ⋃ i : t, B i, g y ∂μ) :=
    hasSum_integral_iUnion hBi hdi hg
  -- countable additivity of the measure, read in `ℝ`
  have hμ : μ (⋃ i : t, B i) = ∑' i : t, μ (B i) := measure_iUnion hdi hBi
  have hfin' : ∑' i : t, μ (B i) ≠ ∞ := hμ ▸ hfin.ne
  have hmeas : HasSum (fun i : t => (μ (B i)).toReal) (μ (⋃ i : t, B i)).toReal := by
    rw [hμ, ENNReal.tsum_toReal_eq fun i => ENNReal.ne_top_of_tsum_ne_top hfin' i]
    exact ENNReal.hasSum_toReal hfin'
  -- compare the two series term by term
  exact hasSum_le (fun i : t => hle i i.2) hint (hmeas.mul_left θ)
/-- Complement bound in the covering step of the lower density estimate (cf. Simon Ch. 6, 8.2): if
`|g| ≤ 1` `μ`-a.e., `V ⊆ W` with `V` measurable, `μ W < ∞` and `∫_V g dμ ≤ θ μ(V)`, then
`∫_W g dμ = ∫_{W∖V} g dμ + ∫_V g dμ ≤ (μ(W) − μ(V)) + θ μ(V) = μ(W) − (1 − θ) μ(V)`. -/
theorem Submission.cbrldvc_setIntegral_le_sub_of_subset : ∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (V W : Set (Euclid P)), AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, |g x| ≤ 1) → MeasurableSet V → V ⊆ W → μ W < ∞ → ∫ y in V, g y ∂μ ≤ θ * (μ V).toReal → ∫ y in W, g y ∂μ ≤ (μ W).toReal - (1 - θ) * (μ V).toReal := by
  intro P μ g θ V W hg hbd hV hVW hW hθ
  -- `μ V ≤ μ W < ∞` and `μ (W \ V) ≤ μ W < ∞`
  have hVW_le : μ V ≤ μ W := measure_mono hVW
  have hVfin : μ V ≠ ∞ := (hVW_le.trans_lt hW).ne
  have hWVfin : μ (W \ V) ≠ ∞ := ((measure_mono sdiff_subset).trans_lt hW).ne
  -- `|g| ≤ 1` a.e. makes `g` integrable on every set of finite measure
  have hgS : ∀ S : Set (Euclid P), μ S ≠ ∞ → IntegrableOn g S μ := fun S hS =>
    Measure.integrableOn_of_bounded (M := 1) hS hg
      (by filter_upwards [ae_restrict_of_ae hbd] with x hx; rwa [Real.norm_eq_abs])
  have hgV : IntegrableOn g V μ := hgS V hVfin
  have hgWV : IntegrableOn g (W \ V) μ := hgS (W \ V) hWVfin
  -- `∫_W g = ∫_{W∖V} g + ∫_V g`
  have hsplit : ∫ y in W, g y ∂μ = ∫ y in W \ V, g y ∂μ + ∫ y in V, g y ∂μ := by
    conv_lhs => rw [← sdiff_union_of_subset hVW]
    exact setIntegral_union disjoint_sdiff_left hV hgWV hgV
  -- `∫_{W∖V} g ≤ ∫_{W∖V} 1 = μ(W ∖ V)`
  have hcomp : ∫ y in W \ V, g y ∂μ ≤ (μ (W \ V)).toReal := by
    calc ∫ y in W \ V, g y ∂μ ≤ ∫ _ in W \ V, (1 : ℝ) ∂μ :=
          integral_mono_ae hgWV (integrableOn_const hWVfin)
            (by filter_upwards [ae_restrict_of_ae hbd] with x hx; exact (le_abs_self _).trans hx)
      _ = (μ (W \ V)).toReal := by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  -- `μ(W ∖ V) = μ(W) − μ(V)`
  have hdiff : (μ (W \ V)).toReal = (μ W).toReal - (μ V).toReal := by
    rw [measure_sdiff hVW hV.nullMeasurableSet hVfin, ENNReal.toReal_sub_of_le hVW_le hW.ne]
  rw [hsplit]
  linarith

/-- **Covering inequality for the set integral of a bounded density** (the covering in the proof
of Simon Ch. 6, 8.2 after (4): pairwise disjoint closed balls covering almost all of the low
density set, with total measure at most `μ(W)`).  Let `μ` be finite on compact subsets of `ℝᴾ`,
`|g| ≤ 1` `μ`-a.e., `θ ≤ 1`, `W` open with `μ(W) < ∞`, and let every point of `E ⊆ W` be the
centre of arbitrarily small closed balls `B̄_ρ(x)` with `∫_{B̄_ρ(x)} g dμ ≤ θ μ(B̄_ρ(x))`.
Besicovitch gives countably many such balls, pairwise disjoint and contained in `W`, whose
union `V` covers `μ`-almost all of `E`.  By countable additivity `∫_V g dμ ≤ θ μ(V)`, and `g ≤ 1`
on `W \ V`, so `∫_W g dμ ≤ μ(W) − (1 − θ) μ(V) ≤ μ(W) − (1 − θ) μ(E)`. -/
theorem Submission.cbrld_vitali_setIntegral_le : ∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (E W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, |g x| ≤ 1) → θ ≤ 1 → IsOpen W → E ⊆ W → μ W < ∞ → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ ∫ y in closedBall x ρ, g y ∂μ ≤ θ * (μ (closedBall x ρ)).toReal) → ∫ y in W, g y ∂μ ≤ (μ W).toReal - (1 - θ) * (μ E).toReal := by
  intro P μ g θ E W hK hg hg1 hθ hW hEW hWfin hsmall
  -- steps 1–3: countably many pairwise disjoint admissible balls `B̄_{r(x)}(x) ⊆ W`, `x ∈ t`,
  -- covering `μ`-almost all of `E`
  obtain ⟨t, r, htc, -, hr, hdisj, hnull⟩ :=
    Submission.cbrldvc_exists_disjoint_closedBall_cover P μ
      (fun x ρ => ∫ y in closedBall x ρ, g y ∂μ ≤ θ * (μ (closedBall x ρ)).toReal) E W hK hW hEW
      hsmall
  -- step 4: their union `V` is measurable, `V ⊆ W`, `μ(V) < ∞` and `μ(E) ≤ μ(V)`
  have hVmeas : MeasurableSet (⋃ x ∈ t, closedBall x (r x)) :=
    MeasurableSet.biUnion htc fun _ _ => measurableSet_closedBall
  have hVW : ⋃ x ∈ t, closedBall x (r x) ⊆ W := iUnion₂_subset fun x hx => (hr x hx).2.1
  have hVfin : μ (⋃ x ∈ t, closedBall x (r x)) < ∞ := (measure_mono hVW).trans_lt hWfin
  have hEV : μ E ≤ μ (⋃ x ∈ t, closedBall x (r x)) := measure_mono_ae (ae_le_set.2 hnull)
  -- step 5: `∫_V g dμ ≤ θ μ(V)`, summing over the disjoint balls
  have hgV : IntegrableOn g (⋃ x ∈ t, closedBall x (r x)) μ :=
    Measure.integrableOn_of_bounded hVfin.ne hg (M := 1)
      (ae_restrict_of_ae (hg1.mono fun x hx => by rwa [Real.norm_eq_abs]))
  have hV : ∫ y in ⋃ x ∈ t, closedBall x (r x), g y ∂μ ≤
      θ * (μ (⋃ x ∈ t, closedBall x (r x))).toReal :=
    Submission.cbrldvc_setIntegral_biUnion_le_mul_measure P μ g θ t (fun x => closedBall x (r x))
      htc (fun _ _ => measurableSet_closedBall) hdisj hVfin hgV fun x hx => (hr x hx).2.2
  -- steps 6–7: `g ≤ 1` on `W \ V`; then `μ(E) ≤ μ(V)` and `1 − θ ≥ 0`
  calc ∫ y in W, g y ∂μ
      ≤ (μ W).toReal - (1 - θ) * (μ (⋃ x ∈ t, closedBall x (r x))).toReal :=
        Submission.cbrldvc_setIntegral_le_sub_of_subset P μ g θ _ W hg hg1 hVmeas hVW hWfin hV
    _ ≤ (μ W).toReal - (1 - θ) * (μ E).toReal :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hVfin.ne hEV)
          (sub_nonneg.2 hθ)) _

/-- **Comparison with a small filling** (Simon Ch. 6, proof of Theorem 8.2, (4)–(6), pp. 177–178,
for a single test form).  Suppose `∂S = ∂A` in `ℝᴾ`, `M(A) ≤ m < ∞`, `M(S) ≤ κm`,
`spt A, spt S ⊆ B̄_R(x)`, `|ω| ≤ 1`, and `ω` satisfies the cone inequality `|X(ω)| ≤ cϱM(X)` for
every cycle `X` of finite mass supported in a closed ball of radius `ϱ`.  Then `X = S − A` is such
a cycle, with `M(X) ≤ M(S) + M(A) ≤ (1 + κ)m` and `spt X ⊆ spt S ∪ spt A ⊆ B̄_R(x)`, so
`|X(ω)| ≤ cR(1 + κ)m`; and `S(ω) ≤ M(S) ≤ κm` because `ω` is admissible.  Hence
`A(ω) = S(ω) − X(ω) ≤ (κ + cR(1 + κ))m`. -/
theorem Submission.cbrld_ns_eval_le_of_small_filling : ∀ (P d : ℕ) (A S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)) (m : ℝ≥0∞) (x : Euclid P) (c κ R : ℝ), 0 ≤ c → 0 ≤ κ → 0 < R → m < ∞ → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (d + 1)) y) ≤ 1) → (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (x₀ : Euclid P) (ϱ : ℝ), 0 < ϱ → X.boundary = 0 → X.mass < ∞ → X.support ⊆ closedBall x₀ ϱ → |X ω| ≤ c * ϱ * X.mass.toReal) → S.boundary = A.boundary → A.mass ≤ m → S.mass ≤ ENNReal.ofReal κ * m → A.support ⊆ closedBall x R → S.support ⊆ closedBall x R → A ω ≤ (κ + c * R * (1 + κ)) * m.toReal := by
  intro P d A S ω m x c κ R hc hκ hR hm hω hcone hbd hA hS hsptA hsptS
  -- Step 1: the comparison current `X = S − A`, with `X(η) = S(η) − A(η)`.
  set X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1) := S - A
  have hXapp : ∀ η, X η = S η - A η := fun _ => rfl
  -- Step 2: `∂X(η) = S(dη) − A(dη) = ∂S(η) − ∂A(η) = 0`.
  have hXbd : X.boundary = 0 := by
    ext η
    rw [GeometricCurrentOn.boundary_apply, hXapp, ← GeometricCurrentOn.boundary_apply,
      ← GeometricCurrentOn.boundary_apply, hbd, sub_self, GeometricCurrentOn.zero_apply]
  -- Step 3: `M(X) ≤ M(S) + M(A) ≤ κm + m < ∞`, hence `M(X) ≤ (1 + κ)m` as real numbers.
  have hκm : ENNReal.ofReal κ * m < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm
  have hsum : ENNReal.ofReal κ * m + m < ∞ := ENNReal.add_lt_top.2 ⟨hκm, hm⟩
  have hXmass : X.mass ≤ ENNReal.ofReal κ * m + m :=
    (Submission.cbrld_ns_massOn_sub_le P (d + 1) univ univ S A).trans (add_le_add hS hA)
  have hXfin : X.mass < ∞ := hXmass.trans_lt hsum
  have hXreal : X.mass.toReal ≤ (1 + κ) * m.toReal := by
    have h := ENNReal.toReal_mono hsum.ne hXmass
    rw [ENNReal.toReal_add hκm.ne hm.ne, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] at h
    linarith
  -- Step 4: `spt X ⊆ spt S ∪ spt A ⊆ B̄_R(x)`.
  have hXspt : X.support ⊆ closedBall x R :=
    (Submission.cbrld_ns_support_sub_subset P (d + 1) univ S A).trans (union_subset hsptS hsptA)
  -- Step 5: the cone inequality at `(x, R)`: `|X(ω)| ≤ cR·M(X) ≤ cR(1 + κ)m`.
  have hXω : |X ω| ≤ c * R * ((1 + κ) * m.toReal) :=
    (hcone X x R hR hXbd hXfin hXspt).trans
      (mul_le_mul_of_nonneg_left hXreal (mul_nonneg hc hR.le))
  -- Step 6: `ω` is `ℝᴾ`-admissible, so `S(ω) ≤ M(S) ≤ κm`.
  have hSω : S ω ≤ κ * m.toReal := by
    have hadm : ω ∈ massAdmissibleOn (univ : Set (Euclid P)) (d + 1) univ :=
      ⟨subset_univ _, hω⟩
    have h := (ENNReal.ofReal_le_iff_le_toReal hκm.ne).1 ((S.le_massOn hadm).trans hS)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] at h
  -- Step 7: `A(ω) = S(ω) − X(ω) ≤ S(ω) + |X(ω)| ≤ κm + cR(1 + κ)m`.
  have hAω : A ω = S ω - X ω := by rw [hXapp]; ring
  rw [hAω]
  linarith [neg_le_abs (X ω)]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
