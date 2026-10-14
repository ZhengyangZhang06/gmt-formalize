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

/-- **Cut-off affine homotopies on `ℝ^{P+1}`** (Simon 6.2.26–6.2.29).  For `y ∈ ℝ^{P+1}` write
`pr y = (y₁, …, y_P)` and `y₀`, and put
`H_{Φ,Ψ}(y) = Φ(pr y) + (a(y₀) χ(pr y)) • (Ψ(pr y) - Φ(pr y))`, where `a` is bounded and
Lipschitz and `χ` is Lipschitz with compact support `K`.  (A) `H_{F,G}` is Lipschitz: `φ = χ •
(G - F)` is bounded by `sup |χ| · sup_K ‖G - F‖` and Lipschitz (by cases on `K`), and
`H_{F,G}(y) = F(pr y) + a(y₀) • φ(pr y)`.  (B) For `C¹`, `Λ`-Lipschitz `Fⱼ → F`, `Gⱼ → G`
uniformly, every `H_{Fⱼ,Gⱼ}` is `C¹`, all are Lipschitz with the constant of (A) for the bound
`supⱼ sup_K ‖Gⱼ - Fⱼ‖ < ∞`, and `H_{Fⱼ,Gⱼ} → H_{F,G}` uniformly.  (C) Near `(t, x)` with
`x ∈ W` and `t ∈ (-1, 2)`, `H_{F',G'}(y) = F'(pr y) + y₀ • (G'(pr y) - F'(pr y))`, so
`DH(t,x) ê₀ = G'x - F'x` and `DH(t,x) ∘ J = DF'(x) + t (DG'(x) - DF'(x))` for `J v = (0, v)`;
`curryLeft_compContinuousLinearMap` turns `(H^#ω)(t,x)(ê₀, J ·)` into the integrand of 6.2.27. -/
theorem Submission.dor_lmb_fcdp_homotopy_maps : ∀ (P : ℕ) (Λ La Lχ : NNReal) (A : ℝ) (a : ℝ → ℝ) (χ : Euclid P → ℝ) (F G : Euclid P → Euclid P), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith La a → (∀ t, |a t| ≤ A) → LipschitzWith Lχ χ → HasCompactSupport χ → (∃ L : NNReal, LipschitzWith L (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ (ContDiff ℝ 1 a → ContDiff ℝ 1 χ → ∀ Fs Gs : ℕ → Euclid P → Euclid P, (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ContDiff ℝ 1 (fun y : Euclid (P + 1) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ (∃ L : NNReal, ∀ j, LipschitzWith L (fun y : Euclid (P + 1) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ TendstoUniformly (fun j (y : Euclid (P + 1)) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) atTop) ∧ ∀ (F' G' : Euclid P → Euclid P) (W : Set (Euclid P)) (k : ℕ) (ω : DifferentialForm (Euclid P) (k + 1)) (t : ℝ) (x : Euclid P), ContDiff ℝ 1 a → ContDiff ℝ 1 χ → ContDiff ℝ 1 F' → ContDiff ℝ 1 G' → IsOpen W → (∀ z ∈ W, χ z = 1) → (∀ s ∈ Ioo (-1 : ℝ) 2, a s = s) → x ∈ W → t ∈ Ioo (-1 : ℝ) 2 → (((ω ((fun y : Euclid (P + 1) => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)))).compContinuousLinearMap (fderiv ℝ (fun y : Euclid (P + 1) => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)))).curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap (fderiv ℝ (fun x' : Euclid P => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x) = ((ω (F' x + t • (G' x - F' x))).curryLeft (G' x - F' x)).compContinuousLinearMap (fderiv ℝ F' x + t • (fderiv ℝ G' x - fderiv ℝ F' x)) := by
  intro P Λ La Lχ A a χ F G hF hG ha haA hχ hχc
  -- the coordinate maps `pr y = (y₁, …, y_P)` and `y ↦ y₀` are continuous linear
  let prL : Euclid (P + 1) →L[ℝ] Euclid P :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let e0 : Euclid (P + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  -- both are `1`-Lipschitz
  have hpr : ∀ y y' : Euclid (P + 1), dist (prL y) (prL y') ≤ dist y y' := by
    intro y y'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succ]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have he0 : ∀ y y' : Euclid (P + 1), dist (e0 y) (e0 y') ≤ dist y y' :=
    fun y y' => PiLp.dist_apply_le y y' 0
  -- `0 ≤ A` and `|χ| ≤ B`
  have hA : 0 ≤ A := (abs_nonneg _).trans (haA 0)
  obtain ⟨B, hB⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  -- `H_{Φ,Ψ}` is Lipschitz, with a constant depending only on a bound `D` for `‖Ψ - Φ‖` on
  -- `K = spt χ`
  have key : ∀ (Φ Ψ : Euclid P → Euclid P), LipschitzWith Λ Φ → LipschitzWith Λ Ψ → ∀ D : ℝ,
      0 ≤ D → (∀ x ∈ tsupport χ, ‖Ψ x - Φ x‖ ≤ D) →
      LipschitzWith (Real.toNNReal (Λ + La * B * D + A * (Lχ * D + B * (2 * Λ))))
        (fun y : Euclid (P + 1) => Φ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) +
          (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) •
            (Ψ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) -
              Φ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) := by
    intro Φ Ψ hΦ hΨ D hD0 hD
    -- `φ = χ • (Ψ - Φ)` is bounded by `B * D` ...
    have hφb : ∀ x, ‖χ x • (Ψ x - Φ x)‖ ≤ B * D := by
      intro x
      by_cases hx : x ∈ tsupport χ
      · rw [norm_smul]
        exact mul_le_mul (hB x) (hD x hx) (norm_nonneg _) hB0
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero]
        exact mul_nonneg hB0 hD0
    -- ... and `(Lχ D + 2BΛ)`-Lipschitz, by cases on `spt χ`
    have hV : ∀ x x', ‖(Ψ x - Φ x) - (Ψ x' - Φ x')‖ ≤ 2 * Λ * dist x x' := by
      intro x x'
      have h1 := hΨ.dist_le_mul x x'
      have h2 := hΦ.dist_le_mul x x'
      rw [dist_eq_norm] at h1 h2
      calc ‖(Ψ x - Φ x) - (Ψ x' - Φ x')‖ = ‖(Ψ x - Ψ x') - (Φ x - Φ x')‖ := by congr 1; abel
        _ ≤ ‖Ψ x - Ψ x'‖ + ‖Φ x - Φ x'‖ := norm_sub_le _ _
        _ ≤ Λ * dist x x' + Λ * dist x x' := add_le_add h1 h2
        _ = 2 * Λ * dist x x' := by ring
    have hφL' : ∀ x x', x' ∈ tsupport χ →
        ‖χ x • (Ψ x - Φ x) - χ x' • (Ψ x' - Φ x')‖ ≤ (Lχ * D + B * (2 * Λ)) * dist x x' := by
      intro x x' hx'
      have h1 : ‖χ x - χ x'‖ ≤ Lχ * dist x x' := by
        rw [← dist_eq_norm]; exact hχ.dist_le_mul x x'
      calc ‖χ x • (Ψ x - Φ x) - χ x' • (Ψ x' - Φ x')‖
          = ‖(χ x - χ x') • (Ψ x' - Φ x') + χ x • ((Ψ x - Φ x) - (Ψ x' - Φ x'))‖ := by
            congr 1; simp only [sub_smul, smul_sub]; abel
        _ ≤ ‖χ x - χ x'‖ * ‖Ψ x' - Φ x'‖ + ‖χ x‖ * ‖(Ψ x - Φ x) - (Ψ x' - Φ x')‖ := by
            rw [← norm_smul, ← norm_smul]; exact norm_add_le _ _
        _ ≤ (Lχ * dist x x') * D + B * (2 * Λ * dist x x') :=
            add_le_add (mul_le_mul h1 (hD x' hx') (norm_nonneg _) (by positivity))
              (mul_le_mul (hB x) (hV x x') (norm_nonneg _) hB0)
        _ = (Lχ * D + B * (2 * Λ)) * dist x x' := by ring
    have hφL : ∀ x x',
        ‖χ x • (Ψ x - Φ x) - χ x' • (Ψ x' - Φ x')‖ ≤ (Lχ * D + B * (2 * Λ)) * dist x x' := by
      intro x x'
      by_cases hx' : x' ∈ tsupport χ
      · exact hφL' x x' hx'
      by_cases hx : x ∈ tsupport χ
      · rw [norm_sub_rev, dist_comm]; exact hφL' x' x hx
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx', zero_smul,
          zero_smul, sub_zero, norm_zero]
        positivity
    -- `H_{Φ,Ψ}(y) = Φ(p) + a(s) • φ(p)` with `p = pr y`, `s = y₀`
    refine LipschitzWith.of_dist_le' fun y y' => ?_
    change dist (Φ (prL y) + (a (e0 y) * χ (prL y)) • (Ψ (prL y) - Φ (prL y)))
      (Φ (prL y') + (a (e0 y') * χ (prL y')) • (Ψ (prL y') - Φ (prL y'))) ≤ _
    have hp := hpr y y'
    have hs := he0 y y'
    generalize prL y = p at hp ⊢
    generalize prL y' = p' at hp ⊢
    generalize e0 y = s at hs ⊢
    generalize e0 y' = s' at hs ⊢
    have hΦp : ‖Φ p - Φ p'‖ ≤ Λ * dist y y' := by
      rw [← dist_eq_norm]; exact (hΦ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hp Λ.2)
    have has : ‖a s - a s'‖ ≤ La * dist y y' := by
      rw [← dist_eq_norm]; exact (ha.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hs La.2)
    have has' : ‖a s'‖ ≤ A := by rw [Real.norm_eq_abs]; exact haA _
    have hφp := (hφL p p').trans (mul_le_mul_of_nonneg_left hp (by positivity))
    rw [dist_eq_norm]
    calc ‖(Φ p + (a s * χ p) • (Ψ p - Φ p)) - (Φ p' + (a s' * χ p') • (Ψ p' - Φ p'))‖
        = ‖(Φ p - Φ p') + ((a s - a s') • (χ p • (Ψ p - Φ p)) +
            a s' • (χ p • (Ψ p - Φ p) - χ p' • (Ψ p' - Φ p')))‖ := by
          congr 1; simp only [mul_smul, sub_smul, smul_sub]; abel
      _ ≤ ‖Φ p - Φ p'‖ + (‖a s - a s'‖ * ‖χ p • (Ψ p - Φ p)‖ +
            ‖a s'‖ * ‖χ p • (Ψ p - Φ p) - χ p' • (Ψ p' - Φ p')‖) := by
          rw [← norm_smul, ← norm_smul]
          exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ Λ * dist y y' + (La * dist y y' * (B * D) + A * ((Lχ * D + B * (2 * Λ)) * dist y y')) :=
          add_le_add hΦp (add_le_add (mul_le_mul has (hφb _) (norm_nonneg _) (by positivity))
            (mul_le_mul has' hφp (norm_nonneg _) hA))
      _ = (Λ + La * B * D + A * (Lχ * D + B * (2 * Λ))) * dist y y' := by ring
  -- (A): `D = sup_K ‖G - F‖`
  obtain ⟨D, hD⟩ := hχc.isCompact.exists_bound_of_continuousOn
    (hG.continuous.sub hF.continuous).continuousOn
  refine ⟨⟨_, key F G hF hG (max D 0) (le_max_right _ _) fun x hx =>
    (hD x hx).trans (le_max_left _ _)⟩, ?_, ?_⟩
  -- (B)
  · intro ha1 hχ1 Fs Gs hFs1 hGs1 hFsL hGsL hFsU hGsU
    refine ⟨fun j => ?_, ?_, ?_⟩
    · -- `H_j` is `C¹`
      exact ((hFs1 j).comp prL.contDiff).add (((ha1.comp e0.contDiff).mul
        (hχ1.comp prL.contDiff)).smul (((hGs1 j).comp prL.contDiff).sub
          ((hFs1 j).comp prL.contDiff)))
    · -- `D₂ = sup_j sup_K ‖Gs j - Fs j‖ < ∞`: `≤ D + 2` for `j ≥ N`, and finitely many `j < N`
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        ((Metric.tendstoUniformly_iff.mp hFsU 1 one_pos).and
          (Metric.tendstoUniformly_iff.mp hGsU 1 one_pos))
      have hC : ∀ j, ∃ C, ∀ x ∈ tsupport χ, ‖Gs j x - Fs j x‖ ≤ C := fun j =>
        hχc.isCompact.exists_bound_of_continuousOn
          ((hGsL j).continuous.sub (hFsL j).continuous).continuousOn
      choose C hC using hC
      have hsum : 0 ≤ ∑ i ∈ Finset.range N, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      have hD₂ : ∀ j, ∀ x ∈ tsupport χ,
          ‖Gs j x - Fs j x‖ ≤ max D 0 + 2 + ∑ i ∈ Finset.range N, |C i| := by
        intro j x hx
        rcases le_or_gt N j with hj | hj
        · obtain ⟨h1, h2⟩ := hN j hj
          have e1 := h1 x
          have e2 := h2 x
          rw [dist_eq_norm] at e1 e2
          calc ‖Gs j x - Fs j x‖ = ‖(G x - F x) - (G x - Gs j x) + (F x - Fs j x)‖ := by
                congr 1; abel
            _ ≤ ‖G x - F x‖ + ‖G x - Gs j x‖ + ‖F x - Fs j x‖ :=
                (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
            _ ≤ max D 0 + 1 + 1 :=
                add_le_add (add_le_add ((hD x hx).trans (le_max_left _ _)) e2.le) e1.le
            _ ≤ max D 0 + 2 + ∑ i ∈ Finset.range N, |C i| := by linarith
        · calc ‖Gs j x - Fs j x‖ ≤ |C j| := (hC j x hx).trans (le_abs_self _)
            _ ≤ ∑ i ∈ Finset.range N, |C i| :=
                Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
                  (Finset.mem_range.mpr hj)
            _ ≤ max D 0 + 2 + ∑ i ∈ Finset.range N, |C i| := by linarith [le_max_right D 0]
      exact ⟨_, fun j => key (Fs j) (Gs j) (hFsL j) (hGsL j) _ (by positivity) (hD₂ j)⟩
    · -- `H_j → H` uniformly: `‖H_j - H‖ ≤ ‖Fs j - F‖ + A B (‖Gs j - G‖ + ‖Fs j - F‖)`
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hden : 0 < 1 + 2 * (A * B) := by positivity
      set δ := ε / (1 + 2 * (A * B))
      have hδ : 0 < δ := div_pos hε hden
      have hδε : δ + A * B * (δ + δ) = ε :=
        calc δ + A * B * (δ + δ) = δ * (1 + 2 * (A * B)) := by ring
          _ = ε := div_mul_cancel₀ ε hden.ne'
      filter_upwards [Metric.tendstoUniformly_iff.mp hFsU _ hδ,
        Metric.tendstoUniformly_iff.mp hGsU _ hδ] with j hFj hGj y
      change dist (F (prL y) + (a (e0 y) * χ (prL y)) • (G (prL y) - F (prL y)))
        (Fs j (prL y) + (a (e0 y) * χ (prL y)) • (Gs j (prL y) - Fs j (prL y))) < ε
      have hc : ‖a (e0 y) * χ (prL y)‖ ≤ A * B := by
        rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul (haA _) (hB _) (norm_nonneg _) hA
      have e1 := hFj (prL y)
      have e2 := hGj (prL y)
      generalize a (e0 y) * χ (prL y) = c at hc ⊢
      generalize prL y = p at e1 e2 ⊢
      rw [dist_eq_norm] at e1 e2 ⊢
      calc ‖(F p + c • (G p - F p)) - (Fs j p + c • (Gs j p - Fs j p))‖
          = ‖(F p - Fs j p) + c • ((G p - Gs j p) - (F p - Fs j p))‖ := by
            congr 1; simp only [smul_sub]; abel
        _ ≤ ‖F p - Fs j p‖ + ‖c‖ * (‖G p - Gs j p‖ + ‖F p - Fs j p‖) := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
        _ ≤ ‖F p - Fs j p‖ + A * B * (δ + δ) :=
            add_le_add le_rfl (mul_le_mul hc (add_le_add e2.le e1.le) (by positivity)
              (by positivity))
        _ < δ + A * B * (δ + δ) := by linarith
        _ = ε := hδε
  -- (C)
  · intro F' G' W k ω t x ha1 hχ1 hF'1 hG'1 hW hχW haI hxW ht
    -- `J v = (0, v)`
    let J : Euclid P →L[ℝ] Euclid (P + 1) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun v => WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ)
          map_add' := fun v w => by ext i; cases i using Fin.cases <;> simp
          map_smul' := fun c v => by ext i; cases i using Fin.cases <;> simp }
    set z : Euclid (P + 1) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)
    set H' : Euclid (P + 1) → Euclid P := fun y => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) +
      (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) •
        (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) -
          F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))
    set ι : Euclid P → Euclid (P + 1) := fun x' : Euclid P =>
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))
    have hprz : prL z = x := rfl
    have he0z : e0 z = t := rfl
    -- `ι(x') = ι(0) + J x'`, so `Dι(x) = J`
    have hι : fderiv ℝ ι x = J := by
      have : ι = fun x' => WithLp.toLp 2 (Fin.cons t 0 : Fin (P + 1) → ℝ) + J x' := by
        funext x'
        ext i
        cases i using Fin.cases <;> simp [ι, J]
      rw [this]
      exact (J.hasFDerivAt.const_add _).fderiv
    -- near `z`, `χ(pr y) = 1` and `a(y₀) = y₀`
    have hloc : H' =ᶠ[𝓝 z] fun y => F' (prL y) + e0 y • (G' (prL y) - F' (prL y)) := by
      have hO : IsOpen (prL ⁻¹' W ∩ e0 ⁻¹' Ioo (-1) 2) :=
        (hW.preimage prL.continuous).inter (isOpen_Ioo.preimage e0.continuous)
      have hzO : z ∈ prL ⁻¹' W ∩ e0 ⁻¹' Ioo (-1) 2 := by
        rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, hprz, he0z]
        exact ⟨hxW, ht⟩
      filter_upwards [hO.mem_nhds hzO] with y hy
      have h1 : χ (prL y) = 1 := hχW _ hy.1
      have h2 : a (e0 y) = e0 y := haI _ hy.2
      change F' (prL y) + (a (e0 y) * χ (prL y)) • (G' (prL y) - F' (prL y)) = _
      rw [h1, h2, mul_one]
    -- the derivative of `F'(pr y) + y₀ • (G'(pr y) - F'(pr y))` at `z`
    have hF'd : HasFDerivAt F' (fderiv ℝ F' x) (prL z) := by
      rw [hprz]; exact (hF'1.differentiable one_ne_zero x).hasFDerivAt
    have hG'd : HasFDerivAt G' (fderiv ℝ G' x) (prL z) := by
      rw [hprz]; exact (hG'1.differentiable one_ne_zero x).hasFDerivAt
    have hd := (hF'd.comp z prL.hasFDerivAt).fun_add (e0.hasFDerivAt.fun_smul
      ((hG'd.comp z prL.hasFDerivAt).fun_sub (hF'd.comp z prL.hasFDerivAt)))
    have hfd : fderiv ℝ H' z = (fderiv ℝ F' x).comp prL +
        (e0 z • ((fderiv ℝ G' x).comp prL - (fderiv ℝ F' x).comp prL) +
          e0.smulRight (G' (prL z) - F' (prL z))) := by
      rw [hloc.fderiv_eq]; exact hd.fderiv
    -- `DH'(z) ê₀ = G'x - F'x` and `DH'(z) ∘ J = DF'(x) + t (DG'(x) - DF'(x))`
    have hDe : fderiv ℝ H' z (EuclideanSpace.single 0 1) = G' x - F' x := by
      have h0 : prL (EuclideanSpace.single 0 1) = 0 := by
        change (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
          (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)))) : Euclid P) = 0
        ext i
        simp [Fin.tail, Fin.succ_ne_zero]
      have h1 : e0 (EuclideanSpace.single 0 1) = 1 := by simp [e0]
      rw [hfd]
      simp [h0, h1, hprz]
    have hDJ : (fderiv ℝ H' z).comp J = fderiv ℝ F' x + t • (fderiv ℝ G' x - fderiv ℝ F' x) := by
      rw [hfd]
      ext1 v
      have h0 : prL (J v) = v := rfl
      have h1 : e0 (J v) = 0 := rfl
      simp [h0, h1, he0z]
    have hHz : H' z = F' x + t • (G' x - F' x) := by
      change F' (prL z) + (a (e0 z) * χ (prL z)) • (G' (prL z) - F' (prL z)) = _
      rw [hprz, he0z, hχW x hxW, haI t ht, mul_one]
    -- `((ω ∘ DH') ⌞ ê₀) ∘ J = (ω ⌞ DH' ê₀) ∘ (DH' ∘ J)`
    rw [hHz, hι, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDe, ← hDJ]
    rfl

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
