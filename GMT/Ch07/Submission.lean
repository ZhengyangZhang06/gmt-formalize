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

set_option maxHeartbeats 1000000 in
/-- Tangential `C¹` deformations (Simon Ch. 2, before 5.8; Ch. 4, 2.5–2.6; step 3 of the proof
of 7.1.2).  `X = X₀ + Σᵢ χᵢX` by a partition of unity, where `X₀` vanishes on `N` and `χᵢX` is
supported in the range of a straightening chart `Ψ(a, w) = ψ(vₚ + a) + Jw` of `N` (`J` an isometry
onto `(range Dψ(vₚ))ᗮ`; inverse function theorem).  `X₀` is deformed by `id + tX₀`; `Y = χᵢX` by
`Ψ ∘ (b ↦ b + tZ(b)) ∘ Ψ⁻¹`, `Z = DΨ⁻¹ Y ∘ Ψ`, which keeps `N` because `Z` is horizontal along
`ℝᵈ × {0}` (`TₓN = range Dψ`), and has `Dφ_t = I + tDY + o(t)` uniformly (mean value inequality
and symmetry of `D²Ψ`).  The composition has `Dφ_t = I + tDX + o(t)` uniformly, so for small `t`
it is a bijection with injective derivative (`‖Dφ_t - I‖ ≤ 1/2`); `φ_t = id` for large `|t|`. -/
theorem Submission.tangential_c1_deformation_exists : ∀ (P d : ℕ) (U N : Set (Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → ∃ φ : ℝ → Euclid P → Euclid P, (∀ t, ContDiff ℝ 1 (φ t) ∧ Bijective (φ t) ∧ (∀ x, Injective (fderiv ℝ (φ t) x)) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) (N ∩ U) (N ∩ U)) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t| := by
  have hchart := Submission.chart_tangentSpace_eq_range_fderiv
  -- Step 5: a family with the uniform expansion is, for small `t`, a bijection with injective
  -- derivative (`‖Dφ_t - I‖ ≤ 1/2`); it is replaced by `id` for large `|t|`
  have gfinal (P : ℕ) (U N : Set (Euclid P)) (X : Euclid P → Euclid P)
      (hU : IsOpen U) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) (hXU : tsupport X ⊆ U)
      (hgood : ∃ φ : ℝ → Euclid P → Euclid P, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ,
        (∀ t : ℝ, |t| < δ₀ → ContDiff ℝ 1 (φ t) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧
          MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x,
          ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t|) :
      ∃ φ : ℝ → Euclid P → Euclid P, (∀ t, ContDiff ℝ 1 (φ t) ∧ Bijective (φ t) ∧
        (∀ x, Injective (fderiv ℝ (φ t) x)) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧
        MapsTo (φ t) (N ∩ U) (N ∩ U)) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
        ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤
          ε * |t| := by
    obtain ⟨φ, δ₀, hδ₀, C, hφ, hexp⟩ := hgood
    obtain ⟨MX, hMX⟩ := (hXc.fderiv ℝ).exists_bound_of_continuous (hX.continuous_fderiv one_ne_zero)
    obtain ⟨δ₁, hδ₁, h1⟩ := hexp 1 one_pos
    obtain ⟨η, hη, hηU⟩ := hXc.isCompact.exists_cthickening_subset_open hU hXU
    have hMX0 : 0 ≤ |MX| := abs_nonneg MX
    set t₁ : ℝ := min (min δ₀ δ₁) (min (1 / (2 * (|MX| + 1))) (η / (|C| + 1))) with ht₁
    have ht₁pos : 0 < t₁ := by
      refine lt_min (lt_min hδ₀ hδ₁) (lt_min (by positivity) (by positivity))
    refine ⟨fun t => if |t| < t₁ then φ t else id, fun t => ?_, fun ε hε => ?_⟩
    · by_cases ht : |t| < t₁
      · simp only [ht, ↓reduceIte]
        have htδ₀ : |t| < δ₀ := lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_left _ _))
        have htδ₁ : |t| < δ₁ := lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_right _ _))
        have htM : |t| < 1 / (2 * (|MX| + 1)) :=
          lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
        have htη : |t| < η / (|C| + 1) :=
          lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
        obtain ⟨hC1, hid, hmaps, hdisp⟩ := hφ t htδ₀
        have hdiff : Differentiable ℝ (φ t) := hC1.differentiable one_ne_zero
        have hD : ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P)‖ ≤ 1 / 2 := by
          intro x
          have hx1 := h1 t htδ₁ x
          have hx2 : ‖t • fderiv ℝ X x‖ ≤ |t| * |MX| := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left ((hMX x).trans (le_abs_self MX)) (abs_nonneg t)
          have hkey : |t| * (|MX| + 1) ≤ 1 / 2 := by
            have h2 : 0 < 2 * (|MX| + 1) := by positivity
            rw [lt_div_iff₀ h2] at htM
            nlinarith
          calc ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P)‖
              = ‖(fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x) +
                  t • fderiv ℝ X x‖ := by congr 1; abel
            _ ≤ ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ +
                  ‖t • fderiv ℝ X x‖ := norm_add_le _ _
            _ ≤ 1 * |t| + |t| * |MX| := add_le_add hx1 hx2
            _ = |t| * (|MX| + 1) := by ring
            _ ≤ 1 / 2 := hkey
        have happrox : ApproximatesLinearOn (φ t)
            ((ContinuousLinearEquiv.refl ℝ (Euclid P) : Euclid P →L[ℝ] Euclid P)) univ
            (1 / 2 : NNReal) := by
          intro x _ y _
          have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := φ t)
            (f' := fun z => fderiv ℝ (φ t) z) (φ := ContinuousLinearMap.id ℝ (Euclid P)) (s := univ)
            (fun z _ => (hdiff z).hasFDerivAt.hasFDerivWithinAt) (fun z _ => hD z) convex_univ
            (mem_univ y) (mem_univ x)
          simpa using this
        have hinj : Injective (φ t) := by
          intro x y hxy
          have := happrox x (mem_univ x) y (mem_univ y)
          rw [hxy, sub_self, zero_sub, norm_neg] at this
          have h' : ‖x - y‖ ≤ 1 / 2 * ‖x - y‖ := by simpa using this
          have : ‖x - y‖ = 0 := by linarith [norm_nonneg (x - y)]
          exact sub_eq_zero.1 (norm_eq_zero.1 this)
        have hsurj : Surjective (φ t) := by
          refine happrox.surjective ?_
          rcases subsingleton_or_nontrivial (Euclid P) with h | h
          · exact Or.inl h
          · right
            simp
            norm_num
        refine ⟨hC1, ⟨hinj, hsurj⟩, ?_, hid, ?_⟩
        · intro x v w hvw
          have h0 : fderiv ℝ (φ t) x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
          have hle : ‖v - w‖ ≤ 1 / 2 * ‖v - w‖ := by
            calc ‖v - w‖ = ‖(fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P)) (v - w)‖ := by
                  rw [sub_apply, h0, ContinuousLinearMap.id_apply, zero_sub,
                    norm_neg]
              _ ≤ ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P)‖ * ‖v - w‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 / 2 * ‖v - w‖ := by gcongr; exact hD x
          have : ‖v - w‖ = 0 := by linarith [norm_nonneg (v - w)]
          exact sub_eq_zero.1 (norm_eq_zero.1 this)
        · rintro x ⟨hxN, hxU⟩
          refine ⟨hmaps hxN, ?_⟩
          by_cases hxK : x ∈ tsupport X
          · apply hηU
            apply Metric.mem_cthickening_of_dist_le _ x _ _ hxK
            rw [dist_eq_norm]
            have hC0 : 0 < |C| + 1 := by positivity
            rw [lt_div_iff₀ hC0] at htη
            calc ‖φ t x - x‖ ≤ C * |t| := hdisp x
              _ ≤ |C| * |t| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg t)
              _ ≤ η := by nlinarith [abs_nonneg t, abs_nonneg C]
          · rw [hid x hxK]; exact hxU
      · simp only [ht, ↓reduceIte]
        refine ⟨contDiff_id, bijective_id, fun x => ?_, fun x _ => rfl, fun x hx => hx⟩
        rw [fderiv_id]
        exact injective_id
    · obtain ⟨δ₂, hδ₂, h2⟩ := hexp ε hε
      refine ⟨min δ₂ t₁, lt_min hδ₂ ht₁pos, fun t ht x => ?_⟩
      have ht1 : |t| < t₁ := lt_of_lt_of_le ht (min_le_right _ _)
      simp only [ht1, ↓reduceIte]
      exact h2 t (lt_of_lt_of_le ht (min_le_left _ _)) x
  -- Step 4: a field vanishing on `N` is deformed by `id + tA`
  have gnormal (P : ℕ) (N S : Set (Euclid P)) (A : Euclid P → Euclid P)
      (hA : ContDiff ℝ 1 A) (hAc : HasCompactSupport A) (hAS : tsupport A ⊆ S)
      (hAN : ∀ z ∈ N, A z = 0) :
      ∃ φ : ℝ → Euclid P → Euclid P, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ,
        (∀ t : ℝ, |t| < δ₀ → ContDiff ℝ 1 (φ t) ∧ (∀ x, x ∉ S → φ t x = x) ∧
          MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x,
          ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤
            ε * |t| := by
    obtain ⟨M, hM⟩ := hAc.exists_bound_of_continuous hA.continuous
    refine ⟨fun t x => x + t • A x, 1, one_pos, M, fun t _ => ⟨?_, ?_, ?_, ?_⟩,
      fun ε hε => ⟨1, one_pos, fun t _ x => ?_⟩⟩
    · exact contDiff_id.add (hA.const_smul t)
    · intro x hx
      simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hAS h))]
    · intro z hz
      simpa [hAN z hz] using hz
    · intro x
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg t)
    · have hd : HasFDerivAt (fun x => x + t • A x)
          (ContinuousLinearMap.id ℝ (Euclid P) + t • fderiv ℝ A x) x :=
        (hasFDerivAt_id x).add ((hA.differentiable one_ne_zero x).hasFDerivAt.const_smul t)
      rw [hd.fderiv]
      simp only [add_sub_cancel_left, sub_self, norm_zero]
      positivity
  -- Step 5(d): deformations for `A` and `B` compose to one for `A + B`, as `DA` is uniformly
  -- continuous and the displacement is `O(t)`
  have gadd (P : ℕ) (N S : Set (Euclid P)) (Good : (Euclid P → Euclid P) → Prop)
      (hGood : ∀ A, Good A ↔ ∃ φ : ℝ → Euclid P → Euclid P, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ,
        (∀ t : ℝ, |t| < δ₀ → ContDiff ℝ 1 (φ t) ∧ (∀ x, x ∉ S → φ t x = x) ∧
          MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x,
          ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤ ε * |t|) :
      ∀ A B : Euclid P → Euclid P, ContDiff ℝ 1 A → HasCompactSupport A → ContDiff ℝ 1 B →
        HasCompactSupport B → Good A → Good B → Good (A + B) := by
    intro A B hA hAc hB hBc hGA hGB
    obtain ⟨φ, δ₁, hδ₁, C₁, hφ, eφ⟩ := (hGood A).1 hGA
    obtain ⟨ψ, δ₂, hδ₂, C₂, hψ, eψ⟩ := (hGood B).1 hGB
    refine (hGood (A + B)).2 ⟨fun t => φ t ∘ ψ t, min δ₁ δ₂, lt_min hδ₁ hδ₂, C₁ + C₂,
      fun t ht => ?_, fun ε hε => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hφ t (lt_of_lt_of_le ht (min_le_left _ _))
      obtain ⟨g1, g2, g3, g4⟩ := hψ t (lt_of_lt_of_le ht (min_le_right _ _))
      refine ⟨h1.comp g1, fun x hx => ?_, h3.comp g3, fun x => ?_⟩
      · simp only [Function.comp_apply, g2 x hx, h2 x hx]
      · calc ‖(φ t ∘ ψ t) x - x‖ = ‖(φ t (ψ t x) - ψ t x) + (ψ t x - x)‖ := by
              simp only [Function.comp_apply]; congr 1; abel
          _ ≤ ‖φ t (ψ t x) - ψ t x‖ + ‖ψ t x - x‖ := norm_add_le _ _
          _ ≤ C₁ * |t| + C₂ * |t| := add_le_add (h4 _) (g4 _)
          _ = (C₁ + C₂) * |t| := by ring
    · obtain ⟨MA, hMA⟩ :=
        (hAc.fderiv ℝ).exists_bound_of_continuous (hA.continuous_fderiv one_ne_zero)
      obtain ⟨MB, hMB⟩ :=
        (hBc.fderiv ℝ).exists_bound_of_continuous (hB.continuous_fderiv one_ne_zero)
      have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
      have hMB0 : 0 ≤ MB := (norm_nonneg _).trans (hMB 0)
      obtain ⟨η, hη, hUCη⟩ := Metric.uniformContinuous_iff.1
        ((hAc.fderiv ℝ).uniformContinuous_of_continuous (hA.continuous_fderiv one_ne_zero))
        (ε / 4) (by positivity)
      obtain ⟨d₁, hd₁, e1⟩ := eφ (ε / 8) (by positivity)
      obtain ⟨d₂, hd₂, e2⟩ := eψ (ε / 4) (by positivity)
      have hm : 0 < min 1 (ε / (4 * (MA + 1))) := lt_min one_pos (by positivity)
      set τ : ℝ := min 1 (ε / (4 * (MA + 1))) / (ε / 4 + MB + 1) with hτ
      have hτpos : 0 < τ := div_pos hm (by positivity)
      refine ⟨min (min (min δ₁ δ₂) (min d₁ d₂)) (min τ (η / (|C₂| + 1))),
        lt_min (lt_min (lt_min hδ₁ hδ₂) (lt_min hd₁ hd₂)) (lt_min hτpos (by positivity)),
        fun t ht x => ?_⟩
      simp only [lt_min_iff] at ht
      obtain ⟨⟨⟨htδ₁, htδ₂⟩, ⟨htd₁, htd₂⟩⟩, ⟨htτ, htη⟩⟩ := ht
      obtain ⟨h1, -, -, -⟩ := hφ t htδ₁
      obtain ⟨g1, -, -, g4⟩ := hψ t htδ₂
      have hcomp : fderiv ℝ (φ t ∘ ψ t) x = (fderiv ℝ (φ t) (ψ t x)).comp (fderiv ℝ (ψ t) x) :=
        fderiv_comp x ((h1.differentiable one_ne_zero) _) ((g1.differentiable one_ne_zero) _)
      have hsum : fderiv ℝ (A + B) x = fderiv ℝ A x + fderiv ℝ B x :=
        ((hA.differentiable one_ne_zero x).hasFDerivAt.add
          (hB.differentiable one_ne_zero x).hasFDerivAt).fderiv
      rw [hcomp, hsum]
      set y := ψ t x with hy
      set Pm := fderiv ℝ (φ t) y with hPm
      set Q := fderiv ℝ (ψ t) x with hQ
      set a := fderiv ℝ A x with ha
      set a' := fderiv ℝ A y with ha'
      set b := fderiv ℝ B x with hb
      set I := ContinuousLinearMap.id ℝ (Euclid P) with hI
      have eP : ‖Pm - I - t • a'‖ ≤ ε / 8 * |t| := e1 t htd₁ y
      have eQ : ‖Q - I - t • b‖ ≤ ε / 4 * |t| := e2 t htd₂ x
      have htb : ‖t • b‖ ≤ |t| * MB := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMB x) (abs_nonneg t)
      have hQid : ‖Q - I‖ ≤ |t| * (ε / 4 + MB) := by
        calc ‖Q - I‖ = ‖(Q - I - t • b) + t • b‖ := by congr 1; abel
          _ ≤ ‖Q - I - t • b‖ + ‖t • b‖ := norm_add_le _ _
          _ ≤ ε / 4 * |t| + |t| * MB := add_le_add eQ htb
          _ = |t| * (ε / 4 + MB) := by ring
      have hτ' : |t| * (ε / 4 + MB) ≤ min 1 (ε / (4 * (MA + 1))) := by
        have h3 : 0 < ε / 4 + MB + 1 := by positivity
        have h4 : |t| * (ε / 4 + MB + 1) < min 1 (ε / (4 * (MA + 1))) := by
          rw [hτ, lt_div_iff₀ h3] at htτ; exact htτ
        nlinarith [abs_nonneg t]
      have hQ1 : ‖Q - I‖ ≤ 1 := hQid.trans (hτ'.trans (min_le_left _ _))
      have hQ2 : ‖Q - I‖ ≤ ε / (4 * (MA + 1)) := hQid.trans (hτ'.trans (min_le_right _ _))
      have hQn : ‖Q‖ ≤ 2 := by
        calc ‖Q‖ = ‖(Q - I) + I‖ := by congr 1; abel
          _ ≤ ‖Q - I‖ + ‖I‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add hQ1 ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      have hdist : dist y x < η := by
        rw [dist_eq_norm]
        have hC0 : 0 < |C₂| + 1 := by positivity
        rw [lt_div_iff₀ hC0] at htη
        calc ‖y - x‖ ≤ C₂ * |t| := g4 x
          _ ≤ |C₂| * |t| := mul_le_mul_of_nonneg_right (le_abs_self C₂) (abs_nonneg t)
          _ < η := by nlinarith [abs_nonneg t, abs_nonneg C₂]
      have haa : ‖a' - a‖ ≤ ε / 4 := by
        have := hUCη hdist
        rw [dist_eq_norm] at this
        exact this.le
      have hMAε : MA * (ε / (4 * (MA + 1))) ≤ ε / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have hident : Pm.comp Q - I - t • (a + b) =
          (Pm - I - t • a').comp Q + (Q - I - t • b) + t • (a'.comp (Q - I)) + t • (a' - a) := by
        ext v
        simp only [sub_apply, add_apply,
          ContinuousLinearMap.comp_apply, smul_apply, hI,
          ContinuousLinearMap.id_apply, map_sub, smul_sub, smul_add]
        abel_nf
      rw [hident]
      have t1 : ‖(Pm - I - t • a').comp Q‖ ≤ ε / 4 * |t| := by
        calc ‖(Pm - I - t • a').comp Q‖ ≤ ‖Pm - I - t • a'‖ * ‖Q‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ε / 8 * |t| * 2 := mul_le_mul eP hQn (norm_nonneg _) (by positivity)
          _ = ε / 4 * |t| := by ring
      have t3 : ‖t • (a'.comp (Q - I))‖ ≤ ε / 4 * |t| := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖a'.comp (Q - I)‖ ≤ |t| * (MA * (ε / (4 * (MA + 1)))) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
              exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
                (mul_le_mul (hMA y) hQ2 (norm_nonneg _) hMA0)
          _ ≤ |t| * (ε / 4) := mul_le_mul_of_nonneg_left hMAε (abs_nonneg t)
          _ = ε / 4 * |t| := by ring
      have t4 : ‖t • (a' - a)‖ ≤ ε / 4 * |t| := by
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right haa (abs_nonneg t)
      calc ‖(Pm - I - t • a').comp Q + (Q - I - t • b) + t • (a'.comp (Q - I)) + t • (a' - a)‖
          ≤ ‖(Pm - I - t • a').comp Q‖ + ‖Q - I - t • b‖ + ‖t • (a'.comp (Q - I))‖ +
              ‖t • (a' - a)‖ := norm_add₄_le
        _ ≤ ε / 4 * |t| + ε / 4 * |t| + ε / 4 * |t| + ε / 4 * |t| := by gcongr
        _ = ε * |t| := by ring
  have gsum (P : ℕ) (N S : Set (Euclid P)) (Good : (Euclid P → Euclid P) → Prop)
      (hGood : ∀ A, Good A ↔ ∃ φ : ℝ → Euclid P → Euclid P, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ,
        (∀ t : ℝ, |t| < δ₀ → ContDiff ℝ 1 (φ t) ∧ (∀ x, x ∉ S → φ t x = x) ∧
          MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x,
          ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤ ε * |t|)
      (gadd : ∀ A B : Euclid P → Euclid P, ContDiff ℝ 1 A → HasCompactSupport A → ContDiff ℝ 1 B →
        HasCompactSupport B → Good A → Good B → Good (A + B)) :
      ∀ (ι : Type) (s : Finset ι) (A : ι → Euclid P → Euclid P),
        (∀ i ∈ s, ContDiff ℝ 1 (A i) ∧ HasCompactSupport (A i) ∧ Good (A i)) →
        ContDiff ℝ 1 (∑ i ∈ s, A i) ∧ HasCompactSupport (∑ i ∈ s, A i) ∧ Good (∑ i ∈ s, A i) := by
    intro ι s A hA
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      refine ⟨contDiff_const, HasCompactSupport.zero, (hGood 0).2 ⟨fun _ => id, 1, one_pos, 0,
        fun t _ => ⟨contDiff_id, fun x _ => rfl, mapsTo_id N, fun x => by simp⟩,
        fun ε hε => ⟨1, one_pos, fun t _ x => ?_⟩⟩⟩
      simp only [fderiv_id, sub_self, zero_sub]
      have : fderiv ℝ (0 : Euclid P → Euclid P) x = 0 := fderiv_const_apply (0 : Euclid P)
      rw [this, norm_neg, norm_smul, norm_zero, mul_zero]
      positivity
    | insert a s has ih =>
      rw [Finset.sum_insert has]
      obtain ⟨hC, hc, hG⟩ := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      obtain ⟨hCa, hca, hGa⟩ := hA a (Finset.mem_insert_self a s)
      exact ⟨hCa.add hC, hca.add hc, gadd _ _ hCa hca hC hc hGa hG⟩
  -- Steps 2-3: near `p ∈ N`, straighten `N` by `Ψ(a, w) = ψ(vp + a) + Jw` and conjugate
  -- `b ↦ b + tZ(b)`; a field tangent to `N` is horizontal along the slice `ℝᵈ × {0}`
  have glocal (P d : ℕ) (N S : Set (Euclid P)) (hN : IsEmbeddedSubmanifold 2 d N)
      (Good : (Euclid P → Euclid P) → Prop)
      (hGood : ∀ A, Good A ↔ ∃ φ : ℝ → Euclid P → Euclid P, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ,
        (∀ t : ℝ, |t| < δ₀ → ContDiff ℝ 1 (φ t) ∧ (∀ x, x ∉ S → φ t x = x) ∧
          MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x,
          ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤ ε * |t|)
      (p : Euclid P) (hp : p ∈ N) :
      ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∀ Y : Euclid P → Euclid P, ContDiff ℝ 1 Y →
        HasCompactSupport Y → tsupport Y ⊆ O → tsupport Y ⊆ S →
        (∀ z ∈ N ∩ O, Y z ∈ tangentSpace N z) → Good Y := by
    classical
    obtain ⟨V, W, ψ, hV, hW, hpW, hψ, hψinj, hψim, hψprop, hψD⟩ := hN p hp
    obtain ⟨vp, hvpV, hvp⟩ : p ∈ ψ '' V := by rw [hψim]; exact ⟨hpW, hp⟩
    have hψ2 : ContDiffOn ℝ 2 ψ V := by simpa using hψ
    -- the straightening map `Ψ(a, w) = ψ(vp + a) + w`, `w ∈ (range Dψ(vp))ᗮ`
    set A : Euclid d →L[ℝ] Euclid P := fderiv ℝ ψ vp with hAdef
    have hAinj : Injective A := hψD vp hvpV
    -- a complement of `range A`: `J : ℝᵏ → ℝᴾ` injective with range `(range A)ᗮ`
    obtain ⟨k, J, hJinj, hJrange⟩ : ∃ (k : ℕ) (J : Euclid k →L[ℝ] Euclid P), Injective J ∧
        LinearMap.range (J : Euclid k →ₗ[ℝ] Euclid P) =
          (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P))ᗮ := by
      set K := (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P))ᗮ with hK
      let bK := stdOrthonormalBasis ℝ K
      refine ⟨Module.finrank ℝ K, K.subtypeL.comp
        (bK.repr.symm.toContinuousLinearEquiv : Euclid (Module.finrank ℝ K) →L[ℝ] K),
        fun x y hxy => bK.repr.symm.injective (Subtype.ext hxy), ?_⟩
      ext v
      constructor
      · rintro ⟨w, rfl⟩
        exact (bK.repr.symm w).2
      · intro hv
        exact ⟨bK.repr ⟨v, hv⟩, by simp⟩
    obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Euclid d × Euclid k → Euclid P, ∀ b, Ψ b = ψ (vp + b.1) + J b.2 :=
      ⟨_, fun _ => rfl⟩
    have hΨfun : Ψ = fun b => ψ (vp + b.1) + J b.2 := funext hΨdef
    set Ω : Set (Euclid d × Euclid k) := {b | vp + b.1 ∈ V} with hΩdef
    have hΩ : IsOpen Ω := hV.preimage (continuous_const.add continuous_fst)
    have h0Ω : (0 : Euclid d × Euclid k) ∈ Ω := by simp [hΩdef, hvpV]
    have hΨC : ∀ b ∈ Ω, ContDiffAt ℝ 2 Ψ b := by
      intro b hb
      have h1 : ContDiffAt ℝ 2 ψ (vp + b.1) := hψ2.contDiffAt (hV.mem_nhds hb)
      rw [hΨfun]
      exact (h1.comp b (contDiffAt_const.add contDiffAt_fst)).add
        ((J.contDiff.comp contDiff_snd).contDiffAt)
    have hΨD : ∀ b ∈ Ω, HasFDerivAt Ψ ((fderiv ℝ ψ (vp + b.1)).comp
        (ContinuousLinearMap.fst ℝ (Euclid d) (Euclid k)) +
        J.comp (ContinuousLinearMap.snd ℝ (Euclid d) (Euclid k))) b := by
      intro b hb
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (vp + b.1)) (vp + b.1) :=
        ((hψ2.contDiffAt (hV.mem_nhds hb)).differentiableAt (by norm_num)).hasFDerivAt
      have h2 : HasFDerivAt (fun b : Euclid d × Euclid k => vp + b.1)
          (ContinuousLinearMap.fst ℝ (Euclid d) (Euclid k)) b := (hasFDerivAt_fst).const_add vp
      have h3 : HasFDerivAt (fun b : Euclid d × Euclid k => J b.2)
          (J.comp (ContinuousLinearMap.snd ℝ (Euclid d) (Euclid k))) b :=
        J.hasFDerivAt.comp b hasFDerivAt_snd
      rw [hΨfun]
      exact (h1.comp b h2).add h3
    -- `DΨ(0)(h, w) = Ah + Jw` is a linear isomorphism
    set L₀ : Euclid d × Euclid k →L[ℝ] Euclid P :=
      A.comp (ContinuousLinearMap.fst ℝ (Euclid d) (Euclid k)) +
        J.comp (ContinuousLinearMap.snd ℝ (Euclid d) (Euclid k)) with hL₀
    have hL₀inj : Injective L₀ := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨h, w⟩ hhw
      have hhw' : A h + J w = 0 := by simpa [hL₀] using hhw
      have hk : J w ∈ (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P))ᗮ := by
        rw [← hJrange]; exact LinearMap.mem_range_self _ w
      have h0 : inner ℝ (A h) (J w) = 0 :=
        (Submodule.mem_orthogonal _ _).1 hk _ (LinearMap.mem_range_self _ h)
      have hk' : J w = -A h := eq_neg_of_add_eq_zero_right hhw'
      have hAh0 : A h = 0 := by
        rw [hk', inner_neg_right, neg_eq_zero, real_inner_self_eq_norm_sq] at h0
        exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
      have hw0 : w = 0 := hJinj (by rw [hk', hAh0, neg_zero, map_zero])
      have hh0 : h = 0 := hAinj (by rw [hAh0, map_zero])
      rw [hh0, hw0]
      rfl
    have hdim : Module.finrank ℝ (Euclid d × Euclid k) = Module.finrank ℝ (Euclid P) := by
      rw [Module.finrank_prod,
        ← Submodule.finrank_add_finrank_orthogonal (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)),
        ← hJrange, LinearMap.finrank_range_of_inj (f := (A : Euclid d →ₗ[ℝ] Euclid P)) hAinj,
        LinearMap.finrank_range_of_inj (f := (J : Euclid k →ₗ[ℝ] Euclid P)) hJinj]
    obtain ⟨e₀, he₀⟩ : ∃ e₀ : (Euclid d × Euclid k) ≃L[ℝ] Euclid P,
        (e₀ : Euclid d × Euclid k →L[ℝ] Euclid P) = L₀ :=
      ⟨(LinearMap.linearEquivOfInjective (L₀ : Euclid d × Euclid k →ₗ[ℝ] Euclid P) hL₀inj
        hdim).toContinuousLinearEquiv, ContinuousLinearMap.ext fun b => rfl⟩
    have hΨD0 : HasFDerivAt Ψ (e₀ : Euclid d × Euclid k →L[ℝ] Euclid P) 0 := by
      have := hΨD 0 h0Ω
      simp only [Prod.fst_zero, add_zero] at this
      rw [he₀]
      exact this
    have hstrict : HasStrictFDerivAt Ψ (e₀ : Euclid d × Euclid k →L[ℝ] Euclid P) 0 := by
      have := (hΨC 0 h0Ω).hasStrictFDerivAt (by norm_num)
      rwa [hΨD0.fderiv] at this
    -- inverse function theorem
    obtain ⟨H, hHcoe, h0H⟩ : ∃ H : OpenPartialHomeomorph (Euclid d × Euclid k) (Euclid P),
        (H : Euclid d × Euclid k → Euclid P) = Ψ ∧ (0 : Euclid d × Euclid k) ∈ H.source :=
      ⟨hstrict.toOpenPartialHomeomorph Ψ, hstrict.toOpenPartialHomeomorph_coe,
        hstrict.mem_toOpenPartialHomeomorph_source⟩
    have hΨCon : ContDiffOn ℝ 2 Ψ Ω := fun b hb => (hΨC b hb).contDiffWithinAt
    have hDΨcont : ContinuousOn (fderiv ℝ Ψ) Ω :=
      hΨCon.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
    set B : Set (Euclid d × Euclid k) := H.source ∩ (Ω ∩ fderiv ℝ Ψ ⁻¹'
      range (ContinuousLinearEquiv.toContinuousLinearMap :
        ((Euclid d × Euclid k) ≃L[ℝ] Euclid P) → (Euclid d × Euclid k →L[ℝ] Euclid P))) with hBdef
    have hBopen : IsOpen B :=
      H.open_source.inter (hDΨcont.isOpen_inter_preimage hΩ ContinuousLinearEquiv.isOpen)
    have h0B : (0 : Euclid d × Euclid k) ∈ B := ⟨h0H, h0Ω, e₀, hΨD0.fderiv.symm⟩
    have hBΩ : ∀ b ∈ B, b ∈ Ω := fun b hb => hb.2.1
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Euclid P → Euclid d × Euclid k, Φ = H.symm := ⟨_, rfl⟩
    set O' : Set (Euclid P) := H.target ∩ Φ ⁻¹' B with hO'def
    have hO'open : IsOpen O' := by rw [hO'def, hΦdef]; exact H.isOpen_inter_preimage_symm hBopen
    have hΦB : ∀ y ∈ O', Φ y ∈ B := fun y hy => hy.2
    have hΨΦ : ∀ y ∈ O', Ψ (Φ y) = y := fun y hy => by
      rw [← hHcoe, hΦdef]; exact H.right_inv hy.1
    have hΦΨ : ∀ b ∈ B, Φ (Ψ b) = b := fun b hb => by
      rw [← hHcoe, hΦdef]; exact H.left_inv hb.1
    have hBO' : ∀ b ∈ B, Ψ b ∈ O' := fun b hb => by
      refine ⟨?_, ?_⟩
      · rw [← hHcoe]; exact H.map_source hb.1
      · show Φ (Ψ b) ∈ B
        rw [hΦΨ b hb]; exact hb
    have hΦeq : ∀ y ∈ O', ∃ e : (Euclid d × Euclid k) ≃L[ℝ] Euclid P, fderiv ℝ Ψ (Φ y) = e ∧
        HasFDerivAt Φ (e.symm : Euclid P →L[ℝ] Euclid d × Euclid k) y ∧ ContDiffAt ℝ 2 Φ y := by
      intro y hy
      obtain ⟨-, hbΩ, e, he⟩ := hΦB y hy
      have hD : HasFDerivAt H (e : Euclid d × Euclid k →L[ℝ] Euclid P) (H.symm y) := by
        rw [hHcoe, ← hΦdef, he]
        exact ((hΨC _ hbΩ).differentiableAt (by norm_num)).hasFDerivAt
      have hC : ContDiffAt ℝ 2 H (H.symm y) := by
        rw [hHcoe, ← hΦdef]
        exact hΨC _ hbΩ
      refine ⟨e, he.symm, ?_, ?_⟩
      · rw [hΦdef]; exact H.hasFDerivAt_symm hy.1 hD
      · rw [hΦdef]; exact H.contDiffAt_symm hy.1 hD hC
    have hΦC2 : ∀ y ∈ O', ContDiffAt ℝ 2 Φ y := fun y hy => (hΦeq y hy).choose_spec.2.2
    have hΨΦD : ∀ y ∈ O', ∀ v, fderiv ℝ Ψ (Φ y) (fderiv ℝ Φ y v) = v := by
      intro y hy v
      obtain ⟨e, he, hΦd, -⟩ := hΦeq y hy
      rw [he, hΦd.fderiv]
      exact e.apply_symm_apply v
    have hΦΨD : ∀ y ∈ O', ∀ u, fderiv ℝ Φ y (fderiv ℝ Ψ (Φ y) u) = u := by
      intro y hy u
      obtain ⟨e, he, hΦd, -⟩ := hΦeq y hy
      rw [he, hΦd.fderiv]
      exact e.symm_apply_apply u
    -- the slice `ℝᵈ × {0}` near `0`
    obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 hBopen 0 h0B
    have hslB : ∀ a : Euclid d, ‖a‖ < r → ((a, 0) : Euclid d × Euclid k) ∈ B := by
      intro a ha
      apply hrB
      rw [mem_ball_zero_iff, Prod.norm_def]
      simp only [norm_zero]
      exact max_lt ha hr
    -- `N` near `p` is the image of `ball vp r`
    obtain ⟨rW, hrW, hrWW⟩ : ∃ rW > 0, closedBall p rW ⊆ W :=
      Metric.nhds_basis_closedBall.mem_iff.1 (hW.mem_nhds hpW)
    have hC' : IsCompact ((V ∩ ψ ⁻¹' closedBall p rW) \ ball vp r) :=
      (hψprop _ hrWW (isCompact_closedBall p rW)).diff isOpen_ball
    have hψC' : IsCompact (ψ '' ((V ∩ ψ ⁻¹' closedBall p rW) \ ball vp r)) :=
      hC'.image_of_continuousOn (hψ2.continuousOn.mono (fun x hx => hx.1.1))
    have hpnot : p ∉ ψ '' ((V ∩ ψ ⁻¹' closedBall p rW) \ ball vp r) := by
      rintro ⟨c, ⟨⟨hcV, _⟩, hcball⟩, hc⟩
      have : c = vp := hψinj hcV hvpV (hc.trans hvp.symm)
      exact hcball (this ▸ mem_ball_self hr)
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.isOpen_iff.1 hψC'.isClosed.isOpen_compl p hpnot
    set ρ : ℝ := min ρ₀ rW with hρdef
    have hρ : 0 < ρ := lt_min hρ₀ hrW
    have hslice : ∀ z ∈ N, dist z p < ρ → ∃ a : Euclid d, ‖a‖ < r ∧ ψ (vp + a) = z := by
      intro z hzN hzp
      have hzW : z ∈ W := hrWW (mem_closedBall.2 (le_of_lt (lt_of_lt_of_le hzp (min_le_right _ _))))
      obtain ⟨c, hcV, hcz⟩ : z ∈ ψ '' V := by rw [hψim]; exact ⟨hzW, hzN⟩
      have hcball : c ∈ ball vp r := by
        by_contra hcb
        have hzin : z ∈ ψ '' ((V ∩ ψ ⁻¹' closedBall p rW) \ ball vp r) := by
          refine ⟨c, ⟨⟨hcV, ?_⟩, hcb⟩, hcz⟩
          rw [mem_preimage, hcz]
          exact mem_closedBall.2 (le_of_lt (lt_of_lt_of_le hzp (min_le_right _ _)))
        exact hρ₀sub (mem_ball.2 (lt_of_lt_of_le hzp (min_le_left _ _))) hzin
      refine ⟨c - vp, ?_, by rw [add_sub_cancel, hcz]⟩
      rwa [mem_ball, dist_eq_norm] at hcball
    have hsl : ∀ z ∈ N, z ∈ O' ∩ ball p ρ →
        ∃ a : Euclid d, ‖a‖ < r ∧ ψ (vp + a) = z ∧ Φ z = ((a, 0) : Euclid d × Euclid k) := by
      intro z hzN hz
      obtain ⟨a, ha, hψa⟩ := hslice z hzN (mem_ball.1 hz.2)
      refine ⟨a, ha, hψa, ?_⟩
      have hΨa : Ψ ((a, 0) : Euclid d × Euclid k) = z := by
        rw [hΨdef]; simp [hψa]
      rw [← hΨa]
      exact hΦΨ _ (hslB a ha)
    refine ⟨O' ∩ ball p ρ, hO'open.inter isOpen_ball, ⟨?_, mem_ball_self hρ⟩, ?_⟩
    · have : Ψ 0 = p := by rw [hΨdef]; simp [hvp]
      rw [← this]
      exact hBO' 0 h0B
    -- the local deformation of a tangent field `Y` supported in `O' ∩ ball p ρ`
    intro Y hY hYc hYO hYS hYT
    have hKY : IsCompact (tsupport Y) := hYc
    have hKYO' : tsupport Y ⊆ O' := fun y hy => (hYO hy).1
    obtain ⟨Vf, hVfdef⟩ : ∃ Vf : Euclid P → Euclid d × Euclid k, ∀ y, Vf y = fderiv ℝ Φ y (Y y) :=
      ⟨_, fun _ => rfl⟩
    have hVffun : Vf = fun y => fderiv ℝ Φ y (Y y) := funext hVfdef
    have hΦCon : ContDiffOn ℝ 2 Φ O' := fun y hy => (hΦC2 y hy).contDiffWithinAt
    have hDΦC1 : ContDiffOn ℝ 1 (fderiv ℝ Φ) O' := hΦCon.fderiv_of_isOpen hO'open (by norm_num)
    have hVfC1 : ContDiffOn ℝ 1 Vf O' := by
      rw [hVffun]; exact hDΦC1.clm_apply hY.contDiffOn
    have hVf0 : ∀ y, y ∉ tsupport Y → Vf y = 0 := by
      intro y hy
      rw [hVfdef, image_eq_zero_of_notMem_tsupport hy, map_zero]
    -- tangency: in the chart, `Vf` is horizontal along the slice
    have hV2 : ∀ z ∈ N, z ∈ tsupport Y → (Vf z).2 = 0 := by
      intro z hzN hzK
      obtain ⟨a, ha, hψa, hΦz⟩ := hsl z hzN (hYO hzK)
      have hvaV : vp + a ∈ V := hBΩ _ (hslB a ha)
      have hT : tangentSpace N z = Set.range (fderiv ℝ ψ (vp + a)) := by
        rw [← hψa]
        exact hchart P d 2 N W V ψ (vp + a) (by norm_num) hV hW hψ hψinj hψim hψprop hψD hvaV
      have hYz : Y z ∈ Set.range (fderiv ℝ ψ (vp + a)) := hT ▸ hYT z ⟨hzN, hYO hzK⟩
      obtain ⟨h, hh⟩ := hYz
      have hDΨa :
          fderiv ℝ Ψ ((a, 0) : Euclid d × Euclid k) ((h, 0) : Euclid d × Euclid k) = Y z := by
        rw [(hΨD _ (hBΩ _ (hslB a ha))).fderiv]
        simp [hh]
      have hzO' : z ∈ O' := hKYO' hzK
      have key := hΦΨD z hzO' ((h, 0) : Euclid d × Euclid k)
      rw [hΦz, hDΨa] at key
      rw [hVfdef, key]
    -- deformations
    obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ → Euclid P → Euclid P,
        ∀ t y, φ t y = if y ∈ O' then Ψ (Φ y + t • Vf y) else y := ⟨_, fun _ _ => rfl⟩
    have hid : ∀ t y, y ∉ tsupport Y → φ t y = y := by
      intro t y hy
      rw [hφdef]
      split_ifs with h
      · rw [hVf0 y hy, smul_zero, add_zero, hΨΦ y h]
      · rfl
    -- bounds
    obtain ⟨MΦ, hMΦ0, hMΦ⟩ : ∃ M, 0 ≤ M ∧ ∀ y ∈ tsupport Y, ‖fderiv ℝ Φ y‖ ≤ M := by
      obtain ⟨M, hM⟩ := hKY.exists_bound_of_continuousOn (hDΦC1.continuousOn.mono hKYO')
      exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩
    obtain ⟨MV, hMV0, hMV⟩ : ∃ M, 0 ≤ M ∧ ∀ y ∈ tsupport Y, ‖Vf y‖ ≤ M := by
      obtain ⟨M, hM⟩ := hKY.exists_bound_of_continuousOn (hVfC1.continuousOn.mono hKYO')
      exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩
    obtain ⟨MDV, hMDV0, hMDV⟩ : ∃ M, 0 ≤ M ∧ ∀ y ∈ tsupport Y, ‖fderiv ℝ Vf y‖ ≤ M := by
      obtain ⟨M, hM⟩ := hKY.exists_bound_of_continuousOn
        ((hVfC1.continuousOn_fderiv_of_isOpen hO'open le_rfl).mono hKYO')
      exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩
    have hKB : IsCompact (Φ '' tsupport Y) :=
      hKY.image_of_continuousOn (hΦdef ▸ H.continuousOn_symm.mono (fun y hy => (hKYO' hy).1))
    have hKBB : Φ '' tsupport Y ⊆ B := by
      rintro _ ⟨y, hy, rfl⟩; exact hΦB y (hKYO' hy)
    obtain ⟨η, hη, hηB⟩ := hKB.exists_cthickening_subset_open hBopen hKBB
    have hKc : IsCompact (cthickening η (Φ '' tsupport Y)) := hKB.cthickening
    have hKcΩ : cthickening η (Φ '' tsupport Y) ⊆ Ω := fun b hb => hBΩ b (hηB hb)
    have hDΨC1 : ContDiffOn ℝ 1 (fderiv ℝ Ψ) Ω := hΨCon.fderiv_of_isOpen hΩ (by norm_num)
    have hD2cont := hDΨC1.continuousOn_fderiv_of_isOpen hΩ le_rfl
    obtain ⟨M1, hM10, hM1⟩ : ∃ M, 0 ≤ M ∧
        ∀ c ∈ cthickening η (Φ '' tsupport Y), ‖fderiv ℝ Ψ c‖ ≤ M := by
      obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hDΨcont.mono hKcΩ)
      exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩
    obtain ⟨M2, hM20, hM2⟩ : ∃ M, 0 ≤ M ∧
        ∀ c ∈ cthickening η (Φ '' tsupport Y), ‖fderiv ℝ (fderiv ℝ Ψ) c‖ ≤ M := by
      have hb : ∃ M, ∀ c ∈ cthickening η (Φ '' tsupport Y), ‖fderiv ℝ (fderiv ℝ Ψ) c‖ ≤ M := by
        exact hKc.exists_bound_of_continuousOn (hD2cont.mono hKcΩ)
      obtain ⟨M, hM⟩ := hb
      exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩
    have hUC0 : ∀ ε' > 0, ∃ δ > 0, ∀ x ∈ cthickening η (Φ '' tsupport Y),
        ∀ y ∈ cthickening η (Φ '' tsupport Y), dist x y < δ →
          ‖fderiv ℝ (fderiv ℝ Ψ) x - fderiv ℝ (fderiv ℝ Ψ) y‖ < ε' := by
      intro ε' hε'
      obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
        (hKc.uniformContinuousOn_of_continuous (hD2cont.mono hKcΩ)) ε' hε'
      refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
      calc ‖fderiv ℝ (fderiv ℝ Ψ) x - fderiv ℝ (fderiv ℝ Ψ) y‖
          = dist (fderiv ℝ (fderiv ℝ Ψ) x) (fderiv ℝ (fderiv ℝ Ψ) y) :=
            (dist_eq_norm (fderiv ℝ (fderiv ℝ Ψ) x) (fderiv ℝ (fderiv ℝ Ψ) y)).symm
        _ < ε' := h x hx y hy hxy
    set δ₀ : ℝ := η / (MV + 1) with hδ₀
    have hδ₀pos : 0 < δ₀ := by positivity
    have hseg : ∀ t : ℝ, |t| < δ₀ → ∀ y ∈ tsupport Y, ∀ c ∈ segment ℝ (Φ y) (Φ y + t • Vf y),
        c ∈ cthickening η (Φ '' tsupport Y) ∧ dist c (Φ y) ≤ |t| * MV := by
      intro t ht y hy c hc
      rw [segment_eq_image'] at hc
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hc
      have hd : dist (Φ y + θ • (Φ y + t • Vf y - Φ y)) (Φ y) ≤ |t| * MV := by
        rw [dist_eq_norm, add_sub_cancel_left, add_sub_cancel_left, norm_smul, norm_smul,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hθ0]
        calc θ * (|t| * ‖Vf y‖) ≤ 1 * (|t| * MV) := by
              gcongr
              exact hMV y hy
          _ = |t| * MV := one_mul _
      refine ⟨Metric.mem_cthickening_of_dist_le _ (Φ y) _ _ (mem_image_of_mem Φ hy) ?_, hd⟩
      refine hd.trans ?_
      have h2 : |t| * (MV + 1) < η := by
        rw [hδ₀, lt_div_iff₀ (by positivity)] at ht; exact ht
      exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg t)).trans
        h2.le
    have hC1 : ∀ t, |t| < δ₀ → ContDiff ℝ 1 (φ t) := by
      intro t ht
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hyK : y ∈ tsupport Y
      · have hyO' := hKYO' hyK
        have hev : φ t =ᶠ[𝓝 y] fun y => Ψ (Φ y + t • Vf y) := by
          filter_upwards [hO'open.mem_nhds hyO'] with y' hy'
          rw [hφdef, ite_eq_left hy']
        refine ContDiffAt.congr_of_eventuallyEq ?_ hev
        have hin : Φ y + t • Vf y ∈ Ω :=
          hKcΩ (hseg t ht y hyK _ (right_mem_segment ℝ _ _)).1
        exact ((hΨC _ hin).of_le (by norm_num)).comp y
          (((hΦC2 y hyO').of_le (by norm_num)).add
            ((hVfC1.contDiffAt (hO'open.mem_nhds hyO')).const_smul t))
      · have hev : φ t =ᶠ[𝓝 y] id := by
          filter_upwards [(isClosed_tsupport Y).isOpen_compl.mem_nhds hyK] with y' hy'
          exact hid t y' hy'
        exact contDiffAt_id.congr_of_eventuallyEq hev
    have hmaps : ∀ t, |t| < δ₀ → MapsTo (φ t) N N := by
      intro t ht z hz
      by_cases hzK : z ∈ tsupport Y
      · obtain ⟨a, ha, hψa, hΦz⟩ := hsl z hz (hYO hzK)
        have hw2 := hV2 z hz hzK
        have hzO' := hKYO' hzK
        have hin : Φ z + t • Vf z ∈ Ω :=
          hKcΩ (hseg t ht z hzK _ (right_mem_segment ℝ _ _)).1
        have h2 : (Φ z + t • Vf z).2 = 0 := by
          rw [Prod.snd_add, Prod.smul_snd, hΦz, hw2, smul_zero, add_zero]
        rw [hφdef, ite_eq_left hzO', hΨdef, h2, map_zero, add_zero]
        have hmem : ψ (vp + (Φ z + t • Vf z).1) ∈ ψ '' V := mem_image_of_mem ψ hin
        rw [hψim] at hmem
        exact hmem.2
      · rw [hid t z hzK]; exact hz
    have hdisp : ∀ t, |t| < δ₀ → ∀ y, ‖φ t y - y‖ ≤ M1 * MV * |t| := by
      intro t ht y
      by_cases hyK : y ∈ tsupport Y
      · have hyO' := hKYO' hyK
        rw [hφdef, ite_eq_left hyO']
        have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := Ψ) (f' := fderiv ℝ Ψ)
          (s := segment ℝ (Φ y) (Φ y + t • Vf y))
          (fun c hc => ((hΨC c (hKcΩ (hseg t ht y hyK c hc).1)).differentiableAt
            (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
          (fun c hc => hM1 c (hseg t ht y hyK c hc).1) (convex_segment _ _)
          (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        rw [hΨΦ y hyO', add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
        calc ‖Ψ (Φ y + t • Vf y) - y‖ ≤ M1 * (|t| * ‖Vf y‖) := h
          _ ≤ M1 * (|t| * MV) := by gcongr; exact hMV y hyK
          _ = M1 * MV * |t| := by ring
      · rw [hid t y hyK, sub_self, norm_zero]; positivity
    refine (hGood Y).2 ⟨φ, δ₀, hδ₀pos, M1 * MV, fun t ht => ⟨hC1 t ht,
      fun x hx => hid t x (fun h => hx (hYS h)), hmaps t ht, hdisp t ht⟩, fun ε hε => ?_⟩
    -- the expansion `Dφ_t = I + t DY + o(t)`
    obtain ⟨η₂, hη₂, hUC⟩ := hUC0 (ε / (2 * (MV * MΦ + 1))) (by positivity)
    refine ⟨min δ₀ (min (η₂ / (MV + 1)) (ε / (2 * (M2 * MV * MDV + 1)))),
      lt_min hδ₀pos (lt_min (by positivity) (by positivity)), fun t ht y => ?_⟩
    simp only [lt_min_iff] at ht
    obtain ⟨htδ₀, htη₂, htε⟩ := ht
    by_cases hyK : y ∈ tsupport Y
    · have hyO' := hKYO' hyK
      have hbΩ : Φ y ∈ Ω := hKcΩ (hseg t htδ₀ y hyK _ (left_mem_segment ℝ _ _)).1
      have hbtw : Φ y + t • Vf y ∈ Ω := hKcΩ (hseg t htδ₀ y hyK _ (right_mem_segment ℝ _ _)).1
      have hΦd : HasFDerivAt Φ (fderiv ℝ Φ y) y :=
        ((hΦC2 y hyO').differentiableAt (by norm_num)).hasFDerivAt
      have hVd : HasFDerivAt Vf (fderiv ℝ Vf y) y :=
        ((hVfC1.contDiffAt (hO'open.mem_nhds hyO')).differentiableAt one_ne_zero).hasFDerivAt
      have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ (Φ y + t • Vf y)) (Φ y + t • Vf y) :=
        ((hΨC _ hbtw).differentiableAt (by norm_num)).hasFDerivAt
      have hcompd : HasFDerivAt (fun y => Ψ (Φ y + t • Vf y))
          ((fderiv ℝ Ψ (Φ y + t • Vf y)).comp (fderiv ℝ Φ y + t • fderiv ℝ Vf y)) y :=
        hΨd.comp y (hΦd.add (hVd.const_smul t))
      have hev : φ t =ᶠ[𝓝 y] fun y => Ψ (Φ y + t • Vf y) := by
        filter_upwards [hO'open.mem_nhds hyO'] with y' hy'
        rw [hφdef, ite_eq_left hy']
      have hDφ : fderiv ℝ (φ t) y =
          (fderiv ℝ Ψ (Φ y + t • Vf y)).comp (fderiv ℝ Φ y + t • fderiv ℝ Vf y) :=
        (hcompd.congr_of_eventuallyEq hev).fderiv
      have hDΨd : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) (Φ y)) (Φ y) :=
        ((hDΨC1.contDiffAt (hΩ.mem_nhds hbΩ)).differentiableAt one_ne_zero).hasFDerivAt
      have hYd : HasFDerivAt (fun y => fderiv ℝ Ψ (Φ y) (Vf y))
          ((fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y) +
            ((fderiv ℝ (fderiv ℝ Ψ) (Φ y)).comp (fderiv ℝ Φ y)).flip (Vf y)) y :=
        (hDΨd.comp y hΦd).clm_apply hVd
      have hevY : Y =ᶠ[𝓝 y] fun y => fderiv ℝ Ψ (Φ y) (Vf y) := by
        filter_upwards [hO'open.mem_nhds hyO'] with y' hy'
        rw [hVfdef, hΨΦD y' hy' (Y y')]
      have hDY : fderiv ℝ Y y = (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y) +
          ((fderiv ℝ (fderiv ℝ Ψ) (Φ y)).comp (fderiv ℝ Φ y)).flip (Vf y) :=
        (hYd.congr_of_eventuallyEq hevY).fderiv
      have hI : ContinuousLinearMap.id ℝ (Euclid P) = (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Φ y) := by
        refine ContinuousLinearMap.ext fun v => ?_
        rw [ContinuousLinearMap.comp_apply, hΨΦD y hyO' v, ContinuousLinearMap.id_apply]
      have hsymm : ∀ u v, fderiv ℝ (fderiv ℝ Ψ) (Φ y) u v = fderiv ℝ (fderiv ℝ Ψ) (Φ y) v u :=
        (hΨC _ hbΩ).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      rw [hDφ, hDY, hI]
      set L1 := fderiv ℝ Ψ (Φ y + t • Vf y) with hL1
      set L0 := fderiv ℝ Ψ (Φ y) with hL0
      set D2 := fderiv ℝ (fderiv ℝ Ψ) (Φ y) with hD2
      set G := fderiv ℝ Φ y with hG
      set DV := fderiv ℝ Vf y with hDV
      set w := Vf y with hw
      have hident : L1.comp (G + t • DV) - L0.comp G - t • (L0.comp DV + (D2.comp G).flip w) =
          (L1 - L0 - t • D2 w).comp G + t • ((L1 - L0).comp DV) := by
        refine ContinuousLinearMap.ext fun v => ?_
        simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
          ContinuousLinearMap.flip_apply, map_add, map_smul, smul_sub, smul_add]
        rw [hsymm (G v) w]
        abel_nf
      rw [hident]
      -- mean value estimates on the segment `[Φ y, Φ y + t w]`
      have hsegy := hseg t htδ₀ y hyK
      have hderivs : ∀ c ∈ segment ℝ (Φ y) (Φ y + t • w),
          HasFDerivWithinAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) c)
            (segment ℝ (Φ y) (Φ y + t • w)) c := fun c hc =>
        ((hDΨC1.contDiffAt (hΩ.mem_nhds (hKcΩ (hsegy c hc).1))).differentiableAt
          one_ne_zero).hasFDerivAt.hasFDerivWithinAt
      have hη₂' : |t| * MV < η₂ := by
        rw [lt_div_iff₀ (by positivity)] at htη₂
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg t)) htη₂
      have hb : Φ y ∈ cthickening η (Φ '' tsupport Y) := (hsegy _ (left_mem_segment ℝ _ _)).1
      have hm1 : ‖L1 - L0 - t • D2 w‖ ≤ ε / (2 * (MV * MΦ + 1)) * ‖t • w‖ := by
        have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fderiv ℝ Ψ)
          (f' := fderiv ℝ (fderiv ℝ Ψ)) (φ := D2) hderivs
          (fun c hc => by
            have h1 := hsegy c hc
            exact (hUC c h1.1 (Φ y) hb (lt_of_le_of_lt h1.2 hη₂')).le)
          (convex_segment _ _) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        rw [add_sub_cancel_left, map_smul] at h
        exact h
      have hm2 : ‖L1 - L0‖ ≤ M2 * ‖t • w‖ := by
        have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fderiv ℝ Ψ)
          (f' := fderiv ℝ (fderiv ℝ Ψ)) hderivs (fun c hc => hM2 c (hsegy c hc).1)
          (convex_segment _ _) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        rw [add_sub_cancel_left] at h
        exact h
      have htw : ‖t • w‖ ≤ |t| * MV := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hMV y hyK) (abs_nonneg t)
      have hGb : ‖G‖ ≤ MΦ := hMΦ y hyK
      have hDVb : ‖DV‖ ≤ MDV := hMDV y hyK
      have ht2 : |t| * (M2 * MV * MDV) ≤ ε / 2 := by
        have h0 : 0 < 2 * (M2 * MV * MDV + 1) := by positivity
        rw [lt_div_iff₀ h0] at htε
        linarith only [htε, abs_nonneg t]
      have hε1 : ε / (2 * (MV * MΦ + 1)) * (MV * MΦ) ≤ ε / 2 := by
        have hX : 0 ≤ MV * MΦ := mul_nonneg hMV0 hMΦ0
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith only [hε]
      have hA1 : ‖L1 - L0 - t • D2 w‖ ≤ ε / (2 * (MV * MΦ + 1)) * (|t| * MV) :=
        hm1.trans (mul_le_mul_of_nonneg_left htw (by positivity))
      have hA2 : ‖L1 - L0‖ ≤ M2 * (|t| * MV) := hm2.trans (mul_le_mul_of_nonneg_left htw hM20)
      calc ‖(L1 - L0 - t • D2 w).comp G + t • ((L1 - L0).comp DV)‖
          ≤ ‖(L1 - L0 - t • D2 w).comp G‖ + ‖t • ((L1 - L0).comp DV)‖ := norm_add_le _ _
        _ ≤ ‖L1 - L0 - t • D2 w‖ * ‖G‖ + |t| * (‖L1 - L0‖ * ‖DV‖) := by
            rw [norm_smul, Real.norm_eq_abs]
            exact add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (abs_nonneg t))
        _ ≤ (ε / (2 * (MV * MΦ + 1)) * (|t| * MV)) * MΦ + |t| * ((M2 * (|t| * MV)) * MDV) := by
            gcongr
        _ = |t| * (ε / (2 * (MV * MΦ + 1)) * (MV * MΦ)) + |t| * (|t| * (M2 * MV * MDV)) := by
            ring
        _ ≤ |t| * (ε / 2) + |t| * (ε / 2) := by gcongr
        _ = ε * |t| := by ring
    · have hev : φ t =ᶠ[𝓝 y] id := by
        filter_upwards [(isClosed_tsupport Y).isOpen_compl.mem_nhds hyK] with y' hy'
        exact hid t y' hy'
      rw [hev.fderiv_eq, fderiv_id]
      have hDY0 : fderiv ℝ Y y = 0 := by
        by_contra h
        exact hyK (support_fderiv_subset ℝ (mem_support.2 h))
      rw [hDY0, sub_self, zero_sub, norm_neg, norm_smul, norm_zero, mul_zero]
      positivity
  -- assembly: partition of unity subordinate to straightening charts and `U \ N̄`
  intro P d U N X hU hN hNU hX hXc hXU hXT
  obtain ⟨Good, hGood⟩ : ∃ Good : (Euclid P → Euclid P) → Prop, ∀ A, Good A ↔
      ∃ φ : ℝ → Euclid P → Euclid P, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ,
        (∀ t : ℝ, |t| < δ₀ → ContDiff ℝ 1 (φ t) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧
          MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x,
          ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤ ε * |t| :=
    ⟨_, fun _ => Iff.rfl⟩
  have hsum := gsum P N (tsupport X) Good hGood (gadd P N (tsupport X) Good hGood)
  have hTsub : ∀ z ∈ N, ∃ T : Submodule ℝ (Euclid P), tangentSpace N z = T := by
    intro z hz
    obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hψinj, hψim, hψprop, hψD⟩ := hN z hz
    obtain ⟨v, hv, rfl⟩ : z ∈ ψ '' V := by rw [hψim]; exact ⟨hzW, hz⟩
    refine ⟨LinearMap.range (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P), ?_⟩
    rw [hchart P d 2 N W V ψ v (by norm_num) hV hW hψ hψinj hψim hψprop hψD hv]
    ext u
    simp
  have hNK : IsCompact (N ∩ tsupport X) := by
    have h : N ∩ tsupport X = closure N ∩ tsupport X := by
      ext x
      refine ⟨fun h => ⟨subset_closure h.1, h.2⟩, fun h => ⟨?_, h.2⟩⟩
      by_contra hxN
      have hx : x ∈ (closure N \ N) ∩ U := ⟨⟨h.1, hxN⟩, hXU h.2⟩
      rw [hNU] at hx
      exact hx
    rw [h]
    exact hXc.isCompact.inter_left isClosed_closure
  have hloc : ∀ p : ↥(N ∩ tsupport X), ∃ O : Set (Euclid P), IsOpen O ∧ (p : Euclid P) ∈ O ∧
      ∀ Y : Euclid P → Euclid P, ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ O →
        tsupport Y ⊆ tsupport X → (∀ z ∈ N ∩ O, Y z ∈ tangentSpace N z) → Good Y :=
    fun p => glocal P d N (tsupport X) hN Good hGood p.1 p.2.1
  choose O hOopen hpO hOgood using hloc
  obtain ⟨s, hs⟩ := hNK.elim_finite_subcover O hOopen
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩)
  obtain ⟨G, hGdef⟩ : ∃ G : Option ↥s → Set (Euclid P),
      ∀ j, G j = Option.elim j (U \ closure N) (fun i => O i.1) := ⟨_, fun _ => rfl⟩
  have hGopen : ∀ j, IsOpen (G j) := by
    rintro (_ | i)
    · rw [hGdef]; exact hU.sdiff isClosed_closure
    · rw [hGdef]; exact hOopen _
  have hGcover : tsupport X ⊆ ⋃ j, G j := by
    intro x hx
    by_cases hxN : x ∈ N
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hs ⟨hxN, hx⟩)
      exact mem_iUnion.2 ⟨some ⟨i, hi⟩, by rw [hGdef]; exact hxi⟩
    · refine mem_iUnion.2 ⟨none, ?_⟩
      rw [hGdef]
      refine ⟨hXU hx, fun hxc => ?_⟩
      have hx' : x ∈ (closure N \ N) ∩ U := ⟨⟨hxc, hxN⟩, hXU hx⟩
      rw [hNU] at hx'
      exact hx'
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) (isClosed_tsupport X) G hGopen hGcover
  have hfC : ∀ j, ContDiff ℝ 1 (f j) := fun j =>
    (contMDiff_iff_contDiff.1 (f j).contMDiff).of_le (by exact_mod_cast le_top)
  have hsum1 : ∀ x ∈ tsupport X, ∑ j, f j x = 1 := fun x hx => by
    rw [← finsum_eq_sum_of_fintype]; exact f.sum_eq_one hx
  have hdecomp : X = ∑ j, fun x => f j x • X x := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ tsupport X
    · rw [← Finset.sum_smul, hsum1 x hx, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hpieces : ∀ j ∈ (Finset.univ : Finset (Option ↥s)), ContDiff ℝ 1 (fun x => f j x • X x) ∧
      HasCompactSupport (fun x => f j x • X x) ∧ Good (fun x => f j x • X x) := by
    intro j _
    have hC : ContDiff ℝ 1 (fun x => f j x • X x) := (hfC j).smul hX
    have hc : HasCompactSupport (fun x => f j x • X x) :=
      hXc.mono (support_smul_subset_right (f j) X)
    have hsX : tsupport (fun x => f j x • X x) ⊆ tsupport X := tsupport_smul_subset_right _ _
    have hsG : tsupport (fun x => f j x • X x) ⊆ G j :=
      (tsupport_smul_subset_left _ _).trans (hf j)
    refine ⟨hC, hc, ?_⟩
    rcases j with _ | i
    · refine (hGood _).2 (gnormal P N (tsupport X) _ hC hc hsX (fun z hz => ?_))
      have hz0 : f none z = 0 := by
        by_contra h0
        have hzG : z ∈ G none := hf none (subset_tsupport _ (mem_support.2 h0))
        have hzG' : z ∈ U \ closure N := by rw [hGdef] at hzG; exact hzG
        exact hzG'.2 (subset_closure hz)
      simp [hz0]
    · have hsG' : tsupport (fun x => f (some i) x • X x) ⊆ O i.1 := by
        rw [hGdef] at hsG; exact hsG
      refine hOgood i.1 _ hC hc hsG' hsX (fun z hz => ?_)
      obtain ⟨T, hT⟩ := hTsub z hz.1
      rw [hT]
      by_cases hXz : X z = 0
      · simp only [hXz, smul_zero]; exact T.zero_mem
      · have hzU : z ∈ U := hXU (subset_tsupport _ (mem_support.2 hXz))
        have hXzT := hXT z ⟨hz.1, hzU⟩
        rw [hT] at hXzT
        exact T.smul_mem _ hXzT
  obtain ⟨-, -, hGX⟩ := hsum (Option ↥s) Finset.univ (fun j x => f j x • X x) hpieces
  rw [show (∑ i ∈ Finset.univ, (fun j x => f j x • X x) i) = X from hdecomp.symm] at hGX
  exact gfinal P U N X hU hX hXc hXU ((hGood X).1 hGX)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
