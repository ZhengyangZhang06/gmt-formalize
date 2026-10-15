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

/-- **One-sided limits at `0⁺` from subsequences of positive null sequences.**  If every
sequence `λⱼ > 0`, `λⱼ → 0` has a subsequence along which `f(λ_{φ(j)}) → L`, then `f(t) → L` as
`t ↓ 0`.  `𝓝[>] 0` is countably generated, so by the subsequence criterion it suffices to treat a
sequence `ns → 0⁺`.  It is positive from some `N` on and tends to `0`, so `λⱼ = ns (j + N)` is a
positive null sequence; the hypothesis gives `φ` with `f(λ_{φ(j)}) → L`, and `ms j = φ j + N` is
the required subsequence of `ns`. -/
theorem Submission.idtp_cse_bml_tendsto_nhdsGT_of_subseq : ∀ (f : ℝ → ℝ≥0∞) (L : ℝ≥0∞), (∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun j => f (lams (φ j))) atTop (𝓝 L)) → Tendsto f (𝓝[>] 0) (𝓝 L) := by
  intro f L h
  -- `𝓝[>] 0` is countably generated: it suffices to treat sequences `ns → 0⁺`
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- `0 < ns n` for `n ≥ N` and `ns → 0`, so `λⱼ = ns (j + N)` is a positive null sequence
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hns.eventually_mem self_mem_nhdsWithin)
  obtain ⟨φ, -, hφ⟩ := h (fun j => ns (j + N)) (fun j => hN (j + N) (Nat.le_add_left N j))
    ((tendsto_nhdsWithin_iff.1 hns).1.comp (tendsto_add_atTop_nat N))
  -- `ms j = φ j + N` gives `ns (ms j) = λ_{φ(j)}`
  exact ⟨fun j => φ j + N, hφ⟩
/-- **Cubic bound `|arctan z − z| ≤ |z|³`** (step 1(e) of the box inclusions in the proof of
Simon 7.3.3).  `g(t) = arctan t − t` has `g(0) = 0` and
`g'(t) = 1/(1 + t²) − 1 = −t²/(1 + t²)`, so `|g'(t)| ≤ t²`.  The mean value theorem on
`[min 0 z, max 0 z]` gives `arctan z − z = g'(ξ) z` for some `ξ` strictly between `0` and `z`,
hence `|arctan z − z| ≤ ξ² |z| ≤ |z|³`. -/
theorem Submission.idtp_cse_bml_rbi_abs_arctan_sub_self_le : ∀ z : ℝ, |Real.arctan z - z| ≤ |z| ^ 3 := by
  intro z
  -- step 1: both sides vanish at `z = 0`
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  -- step 2: `g(t) = arctan t − t` is differentiable with `g'(t) = 1/(1 + t²) − 1`
  have hg : ∀ t : ℝ, HasDerivAt (fun t => Real.arctan t - t) (1 / (1 + t ^ 2) - 1) t :=
    fun t => (Real.hasDerivAt_arctan t).sub (hasDerivAt_id t)
  -- step 3: `|g'(ξ)| = ξ²/(1 + ξ²) ≤ ξ²`
  have hg' : ∀ ξ : ℝ, |1 / (1 + ξ ^ 2) - 1| ≤ ξ ^ 2 := by
    intro ξ
    have hpos : 0 < 1 + ξ ^ 2 := by positivity
    rw [show 1 / (1 + ξ ^ 2) - 1 = -(ξ ^ 2 / (1 + ξ ^ 2)) by field_simp; ring, abs_neg,
      abs_of_nonneg (by positivity)]
    exact div_le_self (sq_nonneg ξ) (le_add_of_nonneg_right (sq_nonneg ξ))
  -- step 4: the mean value theorem on `[min 0 z, max 0 z]` gives `arctan z − z = g'(ξ) z`
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => Real.arctan t - t)
    (fun t => 1 / (1 + t ^ 2) - 1) (min_lt_max.2 hz.symm)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hval : Real.arctan z - z = (1 / (1 + ξ ^ 2) - 1) * z := by
    rw [hslope]
    rcases hz.lt_or_gt with h | h
    · rw [min_eq_right h.le, max_eq_left h.le, Real.arctan_zero]
      field_simp
      ring
    · rw [min_eq_left h.le, max_eq_right h.le, Real.arctan_zero]
      field_simp
      ring
  -- step 5: `ξ` lies strictly between `0` and `z`, so `ξ² ≤ |z|²`
  have hξz : ξ ^ 2 ≤ |z| ^ 2 := by
    have h := Set.abs_sub_left_of_mem_uIcc (Set.Ioo_subset_Icc_self hξ)
    rw [sub_zero, sub_zero] at h
    rw [← sq_abs ξ]
    exact pow_le_pow_left₀ (abs_nonneg ξ) h 2
  -- step 6: `|arctan z − z| = |g'(ξ)| |z| ≤ ξ² |z| ≤ |z|³`
  calc |Real.arctan z - z| = |1 / (1 + ξ ^ 2) - 1| * |z| := by rw [hval, abs_mul]
    _ ≤ ξ ^ 2 * |z| := mul_le_mul_of_nonneg_right (hg' ξ) (abs_nonneg z)
    _ ≤ |z| ^ 2 * |z| := mul_le_mul_of_nonneg_right hξz (abs_nonneg z)
    _ = |z| ^ 3 := by ring

/-- Arctangent of a perturbed quotient: if `0 < s'`, `20s' < 1` and `|p|, |q| ≤ 3s'`, then
`|arctan(q/(1 + p)) − q| ≤ 30s'²`.  Here `1 + p > 17/20`, so `z = q/(1 + p)` has `|z| ≤ 4s'` and
`|z − q| = |q||p|/(1 + p) ≤ 11s'²`, while the cubic bound `|arctan z − z| ≤ |z|³` gives
`|arctan z − z| ≤ 64s'³ ≤ 4s'²`. -/
theorem Submission.idtp_cse_bml_rbi_arctan_quotient_estimate : ∀ (p q s' : ℝ), 0 < s' → 20 * s' < 1 → |p| ≤ 3 * s' → |q| ≤ 3 * s' → |Real.arctan (q / (1 + p)) - q| ≤ 30 * s' ^ 2 := by
  intro p q s' hs h20 hp hq
  -- `1 + p ≥ 1 − 3s' > 17/20`, so `z = q/(1 + p)` is a genuine quotient
  have hd : 17 / 20 < 1 + p := by linarith [neg_abs_le p]
  have hd0 : 0 < 1 + p := by linarith
  set z := q / (1 + p) with hz
  -- `|z| = |q|/(1 + p) ≤ 60s'/17 ≤ 4s'`
  have hz4 : |z| ≤ 4 * s' := by
    rw [hz, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    nlinarith [mul_lt_mul_of_pos_left hd hs]
  -- `z − q = −qp/(1 + p)`, so `|z − q| = |q||p|/(1 + p) ≤ 180s'²/17 ≤ 11s'²`
  have hzq : |z - q| ≤ 11 * s' ^ 2 := by
    have hqp : |q| * |p| ≤ 3 * s' * (3 * s') := mul_le_mul hq hp (abs_nonneg p) (by linarith)
    rw [show z - q = -(q * p) / (1 + p) by rw [hz]; field_simp; ring, abs_div, abs_neg, abs_mul,
      abs_of_pos hd0, div_le_iff₀ hd0]
    nlinarith [mul_lt_mul_of_pos_left hd (by positivity : (0 : ℝ) < 11 * s' ^ 2), sq_nonneg s']
  -- the cubic bound: `|arctan z − z| ≤ |z|³ ≤ 64s'³ ≤ 4s'²`, as `s' < 1/20`
  have hat : |Real.arctan z - z| ≤ 4 * s' ^ 2 := by
    refine (Submission.idtp_cse_bml_rbi_abs_arctan_sub_self_le z).trans ?_
    have h3 : |z| ^ 3 ≤ (4 * s') ^ 3 := pow_le_pow_left₀ (abs_nonneg z) hz4 3
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 16 * s' ≤ 1) (sq_nonneg s')]
  -- triangle inequality: `|arctan z − q| ≤ 4s'² + 11s'² ≤ 30s'²`
  calc |Real.arctan z - q| ≤ |Real.arctan z - z| + |z - q| := abs_sub_le _ _ _
    _ ≤ 4 * s' ^ 2 + 11 * s' ^ 2 := add_le_add hat hzq
    _ ≤ 30 * s' ^ 2 := by nlinarith [sq_nonneg s']
/-- **Second-order expansion of `|a + s'w|` at a unit vector `a`** (steps 1(a), 1(d) of the
box-inclusion estimate in the proof of Simon 7.3.3).  With `t = |a + s'w|`, `p = s'⟨w, a⟩` and
`y = 2p + s'²|w|²` one has `t² = 1 + y`, `|y| ≤ 7s'`, hence `(t − 1)² ≤ y² ≤ 49s'²` (as
`(t + 1)² ≥ 1`), and `t − 1 − p = (s'²|w|² − (t − 1)²) / 2` lies in `[−49s'²/2, 9s'²/2]`. -/
theorem Submission.idtp_cse_bml_rbi_norm_expansion : ∀ (P : ℕ) (a w : Euclid P) (s' : ℝ), ‖a‖ = 1 → ‖w‖ ≤ 3 → 0 < s' → 20 * s' < 1 → |‖a + s' • w‖ - 1 - s' * inner ℝ w a| ≤ 30 * s' ^ 2 := by
  intro P a w s' ha hw hs hs20
  -- Step 1: `|⟨w, a⟩| ≤ |w| |a| = |w| ≤ 3` (Cauchy–Schwarz), so `|p| ≤ 3s'`
  have hinner : |inner ℝ w a| ≤ 3 := by
    calc |inner ℝ w a| ≤ ‖w‖ * ‖a‖ := abs_real_inner_le_norm w a
      _ = ‖w‖ := by rw [ha, mul_one]
      _ ≤ 3 := hw
  have hp : |s' * inner ℝ w a| ≤ 3 * s' := by
    rw [abs_mul, abs_of_pos hs, mul_comm]
    exact mul_le_mul_of_nonneg_right hinner hs.le
  -- Step 2: `t² = 1 + y`, `y = 2p + s'²|w|²`
  have hsq : ‖a + s' • w‖ ^ 2 = 1 + (2 * (s' * inner ℝ w a) + s' ^ 2 * ‖w‖ ^ 2) := by
    rw [norm_add_sq_real, ha, real_inner_smul_right, real_inner_comm w a, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs]
    ring
  set t := ‖a + s' • w‖
  set p := s' * inner ℝ w a
  have ht0 : 0 ≤ t := norm_nonneg _
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  -- Step 3: `0 ≤ s'²|w|² ≤ 9s'² ≤ s'`, hence `|y| ≤ 6s' + s' = 7s'`
  have hW : s' ^ 2 * ‖w‖ ^ 2 ≤ 9 * s' ^ 2 := by
    have : ‖w‖ ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ hw0 hw 2
    nlinarith [sq_nonneg s']
  have hW0 : 0 ≤ s' ^ 2 * ‖w‖ ^ 2 := by positivity
  have h9 : 9 * s' ^ 2 ≤ s' := by nlinarith
  have hy : |2 * p + s' ^ 2 * ‖w‖ ^ 2| ≤ 7 * s' := by
    rw [abs_le] at hp ⊢
    constructor <;> linarith [hp.1, hp.2]
  -- Step 4: `(t − 1)(t + 1) = y` and `(t + 1)² ≥ 1`, so `(t − 1)² ≤ y² ≤ 49s'²`
  have hty : (t - 1) * (t + 1) = 2 * p + s' ^ 2 * ‖w‖ ^ 2 := by linear_combination hsq
  have htsq : (t - 1) ^ 2 ≤ 49 * s' ^ 2 := by
    have h1 : (t - 1) ^ 2 ≤ ((t - 1) * (t + 1)) ^ 2 := by
      rw [mul_pow]
      have : 1 ≤ (t + 1) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (t - 1)]
    have h2 : (2 * p + s' ^ 2 * ‖w‖ ^ 2) ^ 2 ≤ (7 * s') ^ 2 :=
      sq_le_sq' (abs_le.1 hy).1 (abs_le.1 hy).2
    rw [hty] at h1
    nlinarith
  -- Steps 5–7: `t − 1 − p = (s'²|w|² − (t − 1)²) / 2 ∈ [−49s'²/2, 9s'²/2]`
  have hkey : t - 1 - p = (s' ^ 2 * ‖w‖ ^ 2 - (t - 1) ^ 2) / 2 := by
    linear_combination hsq / 2
  rw [hkey, abs_le]
  constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg s']
/-- Projection residual of `a + s'w` for `a ∈ Q`, `s' ≥ 0`: with `π = Q.starProjection`, `πa = a`
and linearity give `(a + s'w) − π(a + s'w) = s'(w − πw)`; since `w − πw = π_{Qᗮ}w`, Pythagoras
`‖w‖² = ‖πw‖² + ‖w − πw‖²` gives `‖w − πw‖ ≤ ‖w‖`, so the residual has norm at most `s'‖w‖`. -/
theorem Submission.idtp_cse_bml_rbi_projection_residual_le : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a w : Euclid P) (s' : ℝ), a ∈ Q → 0 ≤ s' → ‖(a + s' • w) - Q.starProjection (a + s' • w)‖ ≤ s' * ‖w‖ := by
  intro P Q a w s' ha hs'
  -- `πa = a`, since `a ∈ Q`
  have hπa : Q.starProjection a = a := Submodule.starProjection_eq_self_iff.mpr ha
  -- by linearity the residual is `s' • (w − πw)`
  have hres : (a + s' • w) - Q.starProjection (a + s' • w) = s' • (w - Q.starProjection w) := by
    rw [map_add, map_smul, hπa, smul_sub, add_sub_add_left_eq_sub]
  -- `w − πw = π_{Qᗮ}w`, so Pythagoras gives `‖w‖² = ‖πw‖² + ‖w − πw‖²`
  have hpyth : ‖w‖ ^ 2 = ‖Q.starProjection w‖ ^ 2 + ‖w - Q.starProjection w‖ ^ 2 := by
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection w Q
  have hle : ‖w - Q.starProjection w‖ ≤ ‖w‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [hpyth]
    exact le_add_of_nonneg_left (sq_nonneg _)
  -- `‖s' • (w − πw)‖ = s'‖w − πw‖ ≤ s'‖w‖`, as `s' ≥ 0`
  rw [hres, norm_smul, Real.norm_of_nonneg hs']
  exact mul_le_mul_of_nonneg_left hle hs'

/-- **Rescaled box inclusions** (box-mass limits in the proof of Simon 7.3.3).  With the open box
`U = {w : ‖w‖ < 3, |⟨w, a⟩| < 1 − η, |⟨w, e⟩| < 1 − η}`, the closed box
`K = {w : ‖w‖ ≤ 3, |⟨w, a⟩| ≤ 1 + η, |⟨w, e⟩| ≤ 1 + η}` and the sector
`Z(s, s') = {x : ⟨x, a⟩ > 0, |‖x‖ − 1| < s', |arctan(⟨x, e⟩/⟨x, a⟩)| < s', ‖x − πx‖ < s‖x‖}`,
`η_{a,s'}⁻¹(U) ⊆ Z(s, s')` and `Z(s, s') ∩ B_{3s'}(a) ⊆ η_{a,s'}⁻¹(K)`.  Write `x = a + s'w` with
`w = η_{a,s'}(x) = s'⁻¹(x − a)`; then `⟨x, a⟩ = 1 + p`, `⟨x, e⟩ = q` for `p = s'⟨w, a⟩`,
`q = s'⟨w, e⟩`, and for `‖w‖ ≤ 3`: `|‖x‖ − 1 − p| ≤ 30s'²`, `|arctan(q/(1 + p)) − q| ≤ 30s'²` and
`‖x − πx‖ ≤ s'‖w‖`.  If `w ∈ U` then `|p|, |q| < s'(1 − η)`, so `x ∈ Z(s, s')` as `30s' < η` and
`6s' < s`; if `x ∈ Z(s, s')` and `|x − a| < 3s'` then `‖w‖ < 3` and
`|p|, |q| < s' + 30s'² < s'(1 + η)`. -/
theorem Submission.idtp_cse_bml_rescaled_box_inclusions : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s η s' : ℝ), a ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < η → 0 < s' → 20 * s' < 1 → 30 * s' < η → 6 * s' < s → dilation a s' ⁻¹' {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < 1 - η ∧ |inner ℝ w e| < 1 - η} ⊆ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∧ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} ∩ ball a (3 * s') ⊆ dilation a s' ⁻¹' {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ 1 + η ∧ |inner ℝ w e| ≤ 1 + η} := by
  intro P Q a e s η s' haQ ha he hae hη hs h20 h30 h6
  -- `η_{a,s'}(y) = −s'⁻¹a + s'⁻¹y`, so `η_{a,s'}(a + s'w) = w` and `x = a + s'η_{a,s'}(x)`
  have hdil : ∀ w : Euclid P, dilation a s' (a + s' • w) = w := by
    intro w
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_add,
      smul_smul, inv_mul_cancel₀ hs.ne', one_smul, neg_add_cancel_left]
  have hrep : ∀ x : Euclid P, ∃ w : Euclid P, x = a + s' • w := by
    intro x
    refine ⟨dilation a s' x, ?_⟩
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_add,
      smul_neg, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_neg_cancel_left]
  -- `⟨x, a⟩ = 1 + p` and `⟨x, e⟩ = q`, as `‖a‖ = 1` and `⟨a, e⟩ = 0`
  have hxa : ∀ w : Euclid P, inner ℝ (a + s' • w) a = 1 + s' * inner ℝ w a := by
    intro w
    rw [inner_add_left, real_inner_self_eq_norm_sq, ha, one_pow, real_inner_smul_left]
  have hxe : ∀ w : Euclid P, inner ℝ (a + s' • w) e = s' * inner ℝ w e := by
    intro w
    rw [inner_add_left, hae, real_inner_smul_left, zero_add]
  -- `|s't| ≤ 3s'` whenever `|t| ≤ 3`
  have h3 : ∀ t : ℝ, |t| ≤ 3 → |s' * t| ≤ 3 * s' := by
    intro t ht
    rw [abs_mul, abs_of_pos hs, mul_comm]
    exact mul_le_mul_of_nonneg_right ht hs.le
  -- the error `30s'²` is less than `s'η`
  have hsη : 30 * s' ^ 2 < s' * η := by nlinarith
  constructor
  · -- step 2: `η_{a,s'}⁻¹(U) ⊆ Z(s, s')`
    intro x hx
    obtain ⟨w, rfl⟩ := hrep x
    rw [Set.mem_preimage, hdil] at hx
    obtain ⟨hw3, hwa, hwe⟩ := hx
    -- `|p|, |q| < s'(1 − η) < s'`
    have hp : |s' * inner ℝ w a| < s' * (1 - η) := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_lt_mul_of_pos_left hwa hs
    have hq : |s' * inner ℝ w e| < s' * (1 - η) := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_lt_mul_of_pos_left hwe hs
    have hp3 : |s' * inner ℝ w a| ≤ 3 * s' := h3 _ (by linarith)
    have hq3 : |s' * inner ℝ w e| ≤ 3 * s' := h3 _ (by linarith)
    have hN := Submission.idtp_cse_bml_rbi_norm_expansion P a w s' ha hw3.le hs h20
    have hA := Submission.idtp_cse_bml_rbi_arctan_quotient_estimate _ _ s' hs h20 hp3 hq3
    have hR := Submission.idtp_cse_bml_rbi_projection_residual_le P Q a w s' haQ hs.le
    -- `|‖x‖ − 1| ≤ |p| + 30s'² < s'(1 − η) + s'η = s'`
    have hnorm : |‖a + s' • w‖ - 1| < s' := by
      rw [abs_le] at hN
      rw [abs_lt] at hp ⊢
      constructor <;> linarith
    simp only [Set.mem_ofPred_eq]
    rw [hxa, hxe]
    refine ⟨?_, hnorm, ?_, ?_⟩
    · -- `⟨x, a⟩ = 1 + p > 1 − s' > 0`
      have := (abs_lt.1 hp).1
      nlinarith
    · -- `|arctan(q/(1 + p))| ≤ |q| + 30s'² < s'(1 − η) + s'η = s'`
      rw [abs_le] at hA
      rw [abs_lt] at hq ⊢
      constructor <;> linarith
    · -- `‖x − πx‖ ≤ s'‖w‖ < 3s' < s‖x‖`, as `‖x‖ > 1 − s' > 1/2` and `s > 6s'`
      have hx1 := (abs_lt.1 hnorm).1
      have hxpos : 0 < ‖a + s' • w‖ := by linarith
      calc ‖a + s' • w - Q.starProjection (a + s' • w)‖ ≤ s' * ‖w‖ := hR
        _ < 3 * s' := by nlinarith
        _ < s * ‖a + s' • w‖ := by nlinarith [mul_pos (sub_pos.2 h6) hxpos]
  · -- step 3: `Z(s, s') ∩ B_{3s'}(a) ⊆ η_{a,s'}⁻¹(K)`
    rintro x ⟨hx, hxB⟩
    obtain ⟨w, rfl⟩ := hrep x
    simp only [Set.mem_ofPred_eq] at hx
    rw [hxa, hxe] at hx
    obtain ⟨-, hx1, hxat, -⟩ := hx
    rw [Set.mem_preimage, hdil]
    -- `s'‖w‖ = ‖x − a‖ < 3s'`, so `‖w‖ < 3`
    have hw3 : ‖w‖ < 3 := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs] at hxB
      nlinarith
    -- Cauchy–Schwarz: `|p|, |q| ≤ s'‖w‖ ≤ 3s'`
    have hp3 : |s' * inner ℝ w a| ≤ 3 * s' :=
      h3 _ ((abs_real_inner_le_norm w a).trans (by rw [ha, mul_one]; exact hw3.le))
    have hq3 : |s' * inner ℝ w e| ≤ 3 * s' :=
      h3 _ ((abs_real_inner_le_norm w e).trans (by rw [he, mul_one]; exact hw3.le))
    have hN := Submission.idtp_cse_bml_rbi_norm_expansion P a w s' ha hw3.le hs h20
    have hA := Submission.idtp_cse_bml_rbi_arctan_quotient_estimate _ _ s' hs h20 hp3 hq3
    rw [abs_le] at hN hA
    rw [abs_lt] at hx1 hxat
    refine ⟨hw3.le, ?_, ?_⟩
    · -- `|p| ≤ |‖x‖ − 1| + 30s'² < s' + s'η`, so `|⟨w, a⟩| < 1 + η`
      have hu : s' * inner ℝ w a < s' * (1 + η) := by linarith
      have hl : s' * -(1 + η) < s' * inner ℝ w a := by linarith
      exact abs_le.2 ⟨(lt_of_mul_lt_mul_left hl hs.le).le, (lt_of_mul_lt_mul_left hu hs.le).le⟩
    · -- `|q| ≤ |arctan(q/(1 + p))| + 30s'² < s' + s'η`, so `|⟨w, e⟩| < 1 + η`
      have hu : s' * inner ℝ w e < s' * (1 + η) := by linarith
      have hl : s' * -(1 + η) < s' * inner ℝ w e := by linarith
      exact abs_le.2 ⟨(lt_of_mul_lt_mul_left hl hs.le).le, (lt_of_mul_lt_mul_left hu hs.le).le⟩
/-- **`Hⁿ⌞Q = ι_#(Lⁿ)` for the plane of an orthonormal frame** (step 3 of the planar constancy
argument, Simon Ch. 6, 2.34, in the proof of Simon 7.3.3).  For `τ` orthonormal in `ℝᴾ`,
`ι(s) = Σᵢ sᵢτᵢ` is linear with `|ι(s)|² = Σᵢ sᵢ² = |s|²`, so it is an isometry `ℝⁿ → ℝᴾ` with
range `Q = span{τ₁, …, τₙ}`; `Hⁿ` is preserved by isometries (`ι_#(Hⁿ) = Hⁿ⌞range ι`) and
`Hⁿ = Lⁿ` on `ℝⁿ`. -/
theorem Submission.idtp_pc_plane_hausdorff_eq_map : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → (μHE[n] : Measure (Euclid P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) = Measure.map (fun s : Euclid n => ∑ i, s i • τ i) volume := by
  intro P n τ hτ
  -- `ι(s) = Σᵢ sᵢτᵢ` is linear
  let L : Euclid n →ₗ[ℝ] Euclid P :=
    { toFun := fun s => ∑ i, s i • τ i
      map_add' := fun s t => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.smul_sum, smul_smul] }
  have hLapp : ∀ s, L s = ∑ i, s i • τ i := fun s => rfl
  -- `|ι(s)|² = ⟨ι(s), ι(s)⟩ = Σᵢ sᵢ² = |s|²`, so `ι` is an isometry
  have hnorm : ∀ s, ‖L s‖ = ‖s‖ := by
    intro s
    have h1 : ‖L s‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [hLapp, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hiso : Isometry L := AddMonoidHomClass.isometry_of_norm L hnorm
  -- `range ι = Q`: `ι(s) ∈ Q`, and each `y ∈ Q` is `Σᵢ cᵢτᵢ = ι(c)`
  have hrange : Set.range L = (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      rw [hLapp]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (SetLike.mem_coe.mp hy)
      exact ⟨(WithLp.equiv 2 (Fin n → ℝ)).symm c, by rw [hLapp]; rfl⟩
  -- `ι_#(Hⁿ) = Hⁿ⌞range ι = Hⁿ⌞Q`, and `Hⁿ = Lⁿ` on `ℝⁿ`
  have h := hiso.map_euclideanHausdorffMeasure (d := n)
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hrange] at h
  exact h.symm
/-- **Lebesgue measure of the squares `(−r, r)²` and `[−r, r]²` in `ℝ²`** (for the box masses at
the edge of a planar sector, in the proof of Simon 7.3.3).  `WithLp.ofLp : ℝ² → (Fin 2 → ℝ)`
preserves volume, the open square is the preimage of the box `∏ᵢ (−r, r)` and the closed square
that of `∏ᵢ [−r, r]`, and both boxes have volume `(2r)·(2r) = 4r²` for `r ≥ 0`. -/
theorem Submission.idtp_cse_bml_sqm_coord_square_volume : ∀ r : ℝ, 0 ≤ r → volume {v : Euclid 2 | |v 0| < r ∧ |v 1| < r} = ENNReal.ofReal (4 * r ^ 2) ∧ volume {v : Euclid 2 | |v 0| ≤ r ∧ |v 1| ≤ r} = ENNReal.ofReal (4 * r ^ 2) := by
  intro r hr
  -- `WithLp.ofLp : ℝ² → (Fin 2 → ℝ)` is measure preserving
  have hmp := PiLp.volume_preserving_ofLp (Fin 2)
  -- both boxes have volume `ofReal (2r) · ofReal (2r) = ofReal (4r²)`, using `r ≥ 0`
  have h4 : (∏ _i : Fin 2, ENNReal.ofReal (r - -r)) = ENNReal.ofReal (4 * r ^ 2) := by
    rw [Fin.prod_univ_two, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  constructor
  · -- the open square is the preimage of `∏ᵢ (−r, r)` (`|t| < r ↔ −r < t < r`)
    have hset : {v : Euclid 2 | |v 0| < r ∧ |v 1| < r} =
        WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin 2 => Ioo (-r) r) := by
      ext v
      simp [abs_lt, Fin.forall_fin_two]
    rw [hset, hmp.measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, h4]
  · -- the closed square is the preimage of `∏ᵢ [−r, r]` (`|t| ≤ r ↔ −r ≤ t ≤ r`)
    have hset : {v : Euclid 2 | |v 0| ≤ r ∧ |v 1| ≤ r} =
        WithLp.ofLp ⁻¹' (Set.Icc (fun _ : Fin 2 => -r) (fun _ => r)) := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two,
        abs_le]
      tauto
    rw [hset, hmp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, h4]

/-- **`H²` of the squares in a `2`-plane, and local finiteness of `H²⌞Q`** (for the box masses at
the edge of a planar sector, in the proof of Simon 7.3.3).  `H²⌞Q` is regular
(`regular_euclideanHausdorffMeasure_restrict_submodule`), hence finite on compacts.  The orthonormal
pair `(a, e)` spans `Q` (`dim Q = 2`), so `H²⌞Q = ι_#(L²)` for `ι(s) = s₀a + s₁e`; since
`⟨ι s, a⟩ = s₀`, `⟨ι s, e⟩ = s₁` and `|ι s|² = s₀² + s₁² ≤ 2r² ≤ 8 < 9`, the preimages of the two
sets are the squares `(−r, r)²` and `[−r, r]²`, both of area `4r²`. -/
theorem Submission.idtp_cse_bml_plane_square_measure : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → IsFiniteMeasureOnCompacts (μHE[2].restrict (Q : Set (Euclid P))) ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 2 → μHE[2].restrict (Q : Set (Euclid P)) {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < r ∧ |inner ℝ w e| < r} = ENNReal.ofReal (4 * r ^ 2) ∧ μHE[2].restrict (Q : Set (Euclid P)) {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ r ∧ |inner ℝ w e| ≤ r} = ENNReal.ofReal (4 * r ^ 2) := by
  intro P Q a e hQ haQ heQ ha he hae
  refine ⟨(Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    hQ).toIsFiniteMeasureOnCompacts, ?_⟩
  intro r hr0 hr2
  -- `τ = (a, e)` is an orthonormal frame
  let τ : Fin 2 → Euclid P := ![a, e]
  have hτ : Orthonormal ℝ τ := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [τ, ha, he, hae, real_inner_comm a e]
  -- its span is `Q`
  have hspan : Submodule.span ℝ (Set.range τ) = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact haQ
      · exact heQ
    · rw [finrank_span_eq_card hτ.linearIndependent, hQ]
      simp
  have hmap := Submission.idtp_pc_plane_hausdorff_eq_map P 2 τ hτ
  rw [hspan] at hmap
  -- `ι(s) = s₀a + s₁e`, with `⟨ι s, a⟩ = s₀`, `⟨ι s, e⟩ = s₁` and `|ι s|² = s₀² + s₁²`
  set ι : Euclid 2 → Euclid P := fun s => ∑ i, s i • τ i
  have hιc : Continuous ι := by fun_prop
  have hf : ∀ s : Euclid 2, ι s = s 0 • a + s 1 • e := by
    intro s
    simp [ι, τ, Fin.sum_univ_two]
  have hia : ∀ s : Euclid 2, inner ℝ (ι s) a = s 0 := by
    intro s
    rw [hf, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      ha, real_inner_comm a e, hae]
    ring
  have hie : ∀ s : Euclid 2, inner ℝ (ι s) e = s 1 := by
    intro s
    rw [hf, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      he, hae]
    ring
  have hn : ∀ s : Euclid 2, ‖ι s‖ ^ 2 = s 0 ^ 2 + s 1 ^ 2 := by
    intro s
    rw [← real_inner_self_eq_norm_sq]
    calc inner ℝ (ι s) (ι s) = inner ℝ (ι s) (s 0 • a + s 1 • e) := by rw [← hf]
      _ = s 0 * inner ℝ (ι s) a + s 1 * inner ℝ (ι s) e := by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      _ = s 0 ^ 2 + s 1 ^ 2 := by rw [hia, hie]; ring
  -- both sets are Borel
  have hSo : MeasurableSet {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < r ∧ |inner ℝ w e| < r} :=
    IsOpen.measurableSet <| (isOpen_lt continuous_norm continuous_const).inter
      ((isOpen_lt (f := fun w : Euclid P => |inner ℝ w a|) (by fun_prop) continuous_const).inter
        (isOpen_lt (f := fun w : Euclid P => |inner ℝ w e|) (by fun_prop) continuous_const))
  have hSc : MeasurableSet {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ r ∧ |inner ℝ w e| ≤ r} :=
    IsClosed.measurableSet <| (isClosed_le continuous_norm continuous_const).inter
      ((isClosed_le (f := fun w : Euclid P => |inner ℝ w a|) (by fun_prop) continuous_const).inter
        (isClosed_le (f := fun w : Euclid P => |inner ℝ w e|) (by fun_prop) continuous_const))
  have hsq := Submission.idtp_cse_bml_sqm_coord_square_volume r hr0
  constructor
  · -- `ι⁻¹(S) = (−r, r)²`: the ball constraint is redundant, `|ι s|² < 2r² ≤ 8 < 9`
    rw [hmap, Measure.map_apply hιc.measurable hSo]
    convert hsq.1 using 2
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hia, hie]
    constructor
    · rintro ⟨-, h0, h1⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨?_, h0, h1⟩
      have h2 := hn s
      nlinarith [sq_abs (s 0), sq_abs (s 1), abs_nonneg (s 0), abs_nonneg (s 1), norm_nonneg (ι s)]
  · -- `ι⁻¹(K) = [−r, r]²`: `|ι s|² ≤ 2r² ≤ 8 < 9`
    rw [hmap, Measure.map_apply hιc.measurable hSc]
    convert hsq.2 using 2
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hia, hie]
    constructor
    · rintro ⟨-, h0, h1⟩
      exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨?_, h0, h1⟩
      have h2 := hn s
      nlinarith [sq_abs (s 0), sq_abs (s 1), abs_nonneg (s 0), abs_nonneg (s 1), norm_nonneg (ι s)]
/-- **Portmanteau inequalities for vague convergence on an open set** (Evans–Gariepy §1.9).
Simon does not state this separately: it is the converse of the "standard approximation
argument" ending the proof of 7.2.4, and its compact-set half is the `ε`-neighbourhood argument
giving (13) there (chapter-07.txt lines 264–288).  Let `U` be open and `νⱼ`, `μ` finite on compact
subsets of `U`.  If `∫ f dνⱼ → ∫ f dμ` for every continuous `f` with compact support in `U`, then
`limsup νⱼ(K) ≤ μ(K)` for compact `K ⊆ U` and `μ(G) ≤ liminf νⱼ(G)` for open `G ⊆ U`.  Urysohn
cut-offs `1_K ≤ h ≤ 1_{thickening r K}` give `limsup νⱼ(K) ≤ μ(cthickening r K) → μ(K)` as
`r ↓ 0`; cut-offs `1_C ≤ h` with `tsupport h ⊆ G` give `μ(C) ≤ liminf νⱼ(G)` for compact
`C ⊆ G`, and `G` is exhausted by increasing compact sets. -/
theorem Submission.cbr_vague_portmanteau : ∀ (P : ℕ) (U : Set (Euclid P)) (νs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), IsOpen U → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → νs j K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (∫ x, f x ∂μ))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => νs j K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => νs j G) atTop) := by
  intro P U νs μ hU hνs hμ hconv
  -- Step 1: cut-off functions.  For compact `C` and `r > 0`, Urysohn's lemma gives a continuous
  -- `h` with compact support, `0 ≤ h ≤ 1`, `h = 1` on `C` and `h = 0` off `thickening r C`;
  -- hence `tsupport h ⊆ cthickening r C`
  have hcut : ∀ (C : Set (Euclid P)) (r : ℝ), IsCompact C → 0 < r →
      ∃ h : Euclid P → ℝ, Continuous h ∧ HasCompactSupport h ∧ (∀ x, 0 ≤ h x) ∧
        (∀ x ∈ C, h x = 1) ∧ (∀ x, h x ≤ 1) ∧ (∀ x, x ∉ thickening r C → h x = 0) ∧
        tsupport h ⊆ cthickening r C := by
    intro C r hC hr
    obtain ⟨h, h1, h0, hcs, h01⟩ := exists_continuous_one_zero_of_isCompact hC
      isOpen_thickening.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (self_subset_thickening hr C))
    refine ⟨h, h.continuous, hcs, fun x => (h01 x).1, fun x hx => h1 hx, fun x => (h01 x).2,
      fun x hx => h0 hx, (closure_mono fun x hx => ?_).trans
        (closure_thickening_subset_cthickening r C)⟩
    by_contra hxr
    exact hx (h0 hxr)
  -- Step 0: such an `h` is `ρ`-integrable whenever `ρ(tsupport h) < ∞`; then
  -- `ρ(B) ≤ ofReal (∫ h dρ)` if `h = 1` on `B` (`Integrable.measure_le_integral`), and in any
  -- case `ofReal (∫ h dρ) ≤ ρ(V)` if `h ≤ 1` and `h = 0` off `V` (`integral_le_measure`)
  have hint : ∀ (ρ : Measure (Euclid P)) (h : Euclid P → ℝ), Continuous h → HasCompactSupport h →
      ρ (tsupport h) < ∞ → Integrable h ρ := fun ρ h hc hcs hρ =>
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport h)).mp
      (hc.continuousOn.integrableOn_of_subset_isCompact hcs (isClosed_tsupport h).measurableSet
        subset_rfl hρ.ne)
  -- Step 2: compact sets.  Choose `δ > 0` with `cthickening δ K ⊆ U`; for `0 < r ≤ δ`,
  -- `limsup νⱼ(K) ≤ lim ofReal (∫ h dνⱼ) = ofReal (∫ h dμ) ≤ μ(cthickening r K)`, and
  -- `μ(cthickening r K) → μ(K)` as `r → 0` because `μ(cthickening δ K) < ∞`
  have hK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      limsup (fun j => νs j K) atTop ≤ μ K := by
    intro K hKc hKU
    obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
    have hr : ∀ r, 0 < r → r ≤ δ → limsup (fun j => νs j K) atTop ≤ μ (cthickening r K) := by
      intro r hr hrδ
      obtain ⟨h, hc, hcs, h0, h1, hle1, hout, hts⟩ := hcut K r hKc hr
      have htsU : tsupport h ⊆ U := hts.trans ((cthickening_mono hrδ K).trans hδU)
      calc limsup (fun j => νs j K) atTop
          ≤ limsup (fun j => ENNReal.ofReal (∫ x, h x ∂(νs j))) atTop :=
            limsup_le_limsup (Eventually.of_forall fun j =>
              (hint (νs j) h hc hcs (hνs j _ hcs htsU)).measure_le_integral
                (Eventually.of_forall h0) fun x hx => (h1 x hx).ge)
        _ = ENNReal.ofReal (∫ x, h x ∂μ) :=
            ((ENNReal.continuous_ofReal.tendsto _).comp (hconv h hc hcs htsU)).limsup_eq
        _ ≤ μ (cthickening r K) := integral_le_measure (fun x _ => hle1 x)
            fun x hx => (hout x fun hx' => hx (thickening_subset_cthickening r K hx')).le
    have hlim := tendsto_measure_cthickening_of_isClosed
      ⟨δ, hδ, (hμ _ hKc.cthickening hδU).ne⟩ hKc.isClosed
    refine ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)) ?_
    filter_upwards [Ioc_mem_nhdsGT hδ] with r hr' using hr r hr'.1 hr'.2
  -- Step 3: compact subsets `C` of open `G ⊆ U`.  With `h = 1` on `C` and `tsupport h ⊆ G`,
  -- `μ(C) ≤ ofReal (∫ h dμ) = lim ofReal (∫ h dνⱼ) ≤ liminf νⱼ(G)`
  have hCG : ∀ G : Set (Euclid P), IsOpen G → G ⊆ U → ∀ C : Set (Euclid P), IsCompact C →
      C ⊆ G → μ C ≤ liminf (fun j => νs j G) atTop := by
    intro G hG hGU C hCc hCG
    obtain ⟨δ, hδ, hδG⟩ := hCc.exists_cthickening_subset_open hG hCG
    obtain ⟨h, hc, hcs, h0, h1, hle1, -, hts⟩ := hcut C δ hCc hδ
    have htsG : tsupport h ⊆ G := hts.trans hδG
    calc μ C ≤ ENNReal.ofReal (∫ x, h x ∂μ) :=
          (hint μ h hc hcs (hμ _ hcs (htsG.trans hGU))).measure_le_integral
            (Eventually.of_forall h0) fun x hx => (h1 x hx).ge
      _ = liminf (fun j => ENNReal.ofReal (∫ x, h x ∂(νs j))) atTop :=
          (((ENNReal.continuous_ofReal.tendsto _).comp
            (hconv h hc hcs (htsG.trans hGU))).liminf_eq).symm
      _ ≤ liminf (fun j => νs j G) atTop :=
          liminf_le_liminf (Eventually.of_forall fun j => integral_le_measure (fun x _ => hle1 x)
            fun x hx => (image_eq_zero_of_notMem_tsupport fun hx' => hx (htsG hx')).le)
  -- Step 4: open sets.  `G = ⋃ₙ Fₙ` with `Fₙ` closed and increasing, so `G` is exhausted by the
  -- increasing compact sets `Fₙ ∩ closedBall 0 n ⊆ G`; continuity from below and Step 3
  refine ⟨hK, fun G hG hGU => ?_⟩
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hCm : Monotone fun n : ℕ => F n ∩ closedBall (0 : Euclid P) n := fun m n hmn =>
    inter_subset_inter (hFm hmn) (closedBall_subset_closedBall (Nat.cast_le.mpr hmn))
  calc μ G ≤ μ (⋃ n : ℕ, F n ∩ closedBall (0 : Euclid P) n) := measure_mono fun x hx => by
        rw [← hFU] at hx
        obtain ⟨m, hm⟩ := mem_iUnion.mp hx
        obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
        exact mem_iUnion.mpr ⟨max m k, hFm (le_max_left m k) hm,
          mem_closedBall_zero_iff.mpr (hk.trans (Nat.cast_le.mpr (le_max_right m k)))⟩
    _ = ⨆ n : ℕ, μ (F n ∩ closedBall (0 : Euclid P) n) := hCm.measure_iUnion
    _ ≤ liminf (fun j => νs j G) atTop := iSup_le fun n =>
        hCG G hG hGU _ ((isCompact_closedBall 0 n).inter_left (hFc n))
          (inter_subset_left.trans (hFG n))
/-- **Rescaled push-forward under a dilation** (Simon 7.3, the scaling `μ_{η_{a,λ#}T}` of blow-ups).
For `λ > 0`, `η = η_{a,λ}` is the homeomorphism `y ↦ −λ⁻¹a + λ⁻¹y`.  Hence `ν = η_#(λ⁻²μ)` is
finite on compact sets when `μ` is (preimages of compact sets are compact), `ν(S) = λ⁻²μ(η⁻¹S)`
for measurable `S`, and `∫ g dν = λ⁻² ∫ g ∘ η dμ` for continuous `g` (change of variables). -/
theorem Submission.idtp_cse_bml_rpm_dilation_map : ∀ (P : ℕ) (μ : Measure (Euclid P)) (a : Euclid P) (lam : ℝ), IsFiniteMeasureOnCompacts μ → 0 < lam → (∀ K : Set (Euclid P), IsCompact K → Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ) K < ∞) ∧ (∀ S : Set (Euclid P), MeasurableSet S → Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ) S = ENNReal.ofReal (lam⁻¹ ^ 2) * μ (dilation a lam ⁻¹' S)) ∧ ∀ g : Euclid P → ℝ, Continuous g → ∫ x, g x ∂(Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ)) = lam⁻¹ ^ 2 * ∫ x, g (dilation a lam x) ∂μ := by
  intro P μ a lam hμ hlam
  -- Step 1: `η_{a,λ}` is the homeomorphism `y ↦ −λ⁻¹a + λ⁻¹y`, so it is measurable and
  -- preimages of compact sets are compact
  let e : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
    (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have he : ⇑e = dilation a lam := by
    funext y
    simp [e, dilation, dilationCLM]
  have hη : Measurable (dilation a lam) := he ▸ e.continuous.measurable
  -- Step 2: `ν(S) = (λ⁻²μ)(η⁻¹S) = λ⁻²μ(η⁻¹S)` for measurable `S`
  have hset : ∀ S : Set (Euclid P), MeasurableSet S →
      Measure.map (dilation a lam) (ENNReal.ofReal (lam⁻¹ ^ 2) • μ) S =
        ENNReal.ofReal (lam⁻¹ ^ 2) * μ (dilation a lam ⁻¹' S) := fun S hS => by
    rw [Measure.map_apply hη hS, Measure.smul_apply, smul_eq_mul]
  refine ⟨fun K hK => ?_, hset, fun g hg => ?_⟩
  · -- Step 3: a compact `K` is closed, hence measurable, and `μ(η⁻¹K) < ∞` as `η⁻¹K` is compact
    have hK' : IsCompact (dilation a lam ⁻¹' K) := by
      rw [← he]
      exact e.isCompact_preimage.mpr hK
    rw [hset K hK.isClosed.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top
  · -- Step 4: change of variables, then `∫ f d(cμ) = c.toReal ∫ f dμ` with `c.toReal = λ⁻²`
    rw [integral_map hη.aemeasurable hg.aestronglyMeasurable, integral_smul_measure,
      ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

/-- **Portmanteau bounds for the rescaled measures `λⱼ⁻²(η_{a,λⱼ})_#μ`** (Simon 7.3, the blow-up
measures `μ_{η_{a,λⱼ#}T}`; the compact-set half is (13) in the proof of 7.2.4).  Let `μ`, `ν` be
finite on compact sets, `λⱼ > 0` and `ηⱼ = η_{a,λⱼ}`.  If `λⱼ⁻² ∫ g ∘ ηⱼ dμ → ∫ g dν` for every
continuous `g` with compact support, then `limsup λⱼ⁻²μ(ηⱼ⁻¹K) ≤ ν(K)` for compact `K` and
`ν(U) ≤ liminf λⱼ⁻²μ(ηⱼ⁻¹U)` for open `U`: the measures `νⱼ = ηⱼ#(λⱼ⁻²μ)` are finite on compact
sets with `∫ g dνⱼ = λⱼ⁻² ∫ g ∘ ηⱼ dμ`, so vague portmanteau on `ℝᴾ` applies to `νⱼ → ν`, and
`νⱼ(S) = λⱼ⁻²μ(ηⱼ⁻¹S)` for the (Borel) sets `S = K, U`. -/
theorem Submission.idtp_cse_bml_rescaled_portmanteau : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (a : Euclid P) (lams : ℕ → ℝ), IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → (∀ j, 0 < lams j) → (∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams j)⁻¹ ^ 2 * ∫ x, g (dilation a (lams j) x) ∂μ) atTop (𝓝 (∫ x, g x ∂ν))) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun j => ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' K)) atTop ≤ ν K) ∧ ∀ U : Set (Euclid P), IsOpen U → ν U ≤ liminf (fun j => ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' U)) atTop := by
  intro P μ ν a lams hμ hν hlams hconv
  -- Step 1: `νⱼ = ηⱼ#(λⱼ⁻²μ)` is finite on compact sets, `νⱼ(S) = λⱼ⁻²μ(ηⱼ⁻¹S)` for measurable
  -- `S` and `∫ g dνⱼ = λⱼ⁻² ∫ g ∘ ηⱼ dμ` for continuous `g`
  have hmap := fun j => Submission.idtp_cse_bml_rpm_dilation_map P μ a (lams j) hμ (hlams j)
  have hset : ∀ (j : ℕ) (S : Set (Euclid P)), MeasurableSet S →
      Measure.map (dilation a (lams j)) (ENNReal.ofReal ((lams j)⁻¹ ^ 2) • μ) S =
        ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' S) :=
    fun j => (hmap j).2.1
  -- Step 2: vague portmanteau on `U = ℝᴾ` for `νⱼ → ν`
  obtain ⟨hK, hU⟩ := Submission.cbr_vague_portmanteau P univ
    (fun j => Measure.map (dilation a (lams j)) (ENNReal.ofReal ((lams j)⁻¹ ^ 2) • μ)) ν
    isOpen_univ (fun j K hK _ => (hmap j).1 K hK) (fun K hK _ => hK.measure_lt_top)
    fun g hg hgs _ => (hconv g hg hgs).congr fun j => ((hmap j).2.2 g hg).symm
  -- Step 3: compact and open sets are measurable, so `νⱼ(S) = λⱼ⁻²μ(ηⱼ⁻¹S)` for them
  refine ⟨fun K hKc => ?_, fun U hUo => ?_⟩
  · have hS : ∀ j, Measure.map (dilation a (lams j)) (ENNReal.ofReal ((lams j)⁻¹ ^ 2) • μ) K =
        ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' K) := fun j =>
      hset j K hKc.measurableSet
    simpa only [hS] using hK K hKc (subset_univ K)
  · have hS : ∀ j, Measure.map (dilation a (lams j)) (ENNReal.ofReal ((lams j)⁻¹ ^ 2) • μ) U =
        ENNReal.ofReal ((lams j)⁻¹ ^ 2) * μ (dilation a (lams j) ⁻¹' U) := fun j =>
      hset j U hUo.measurableSet
    simpa only [hS] using hU U hUo (subset_univ U)

/-- **Box mass limit** at the edge point of a planar sector of a 2-dimensional minimizing cone
(the rigidity behind the classification of 2-dimensional minimizing cones used in Simon 7.3.3(1),
case `n − d = 2`, chapter-07.txt lines 497–510; the book cites [Whi82] and gives no proof).
Let `μ` be finite on compact sets, `Q` a `2`-plane with orthonormal `a, e ∈ Q`, and
`Z(s, s') = {⟨x, a⟩ > 0, ||x| − 1| < s', |arctan(⟨x, e⟩/⟨x, a⟩)| < s', |x − πx| < s|x|}`.
Suppose (L) `μ(Z(s, s') \ B_{3s'}(a)) = 0` for `0 < s' ≤ s`, and (V) every null sequence
`λⱼ > 0` has a subsequence along which `λ⁻² ∫ g ∘ dilation a λ dμ → m ∫_Q g dH²` for continuous
compactly supported `g`.  Then `μ(Z(s, s')) / s'² → 4m` as `s' ↓ 0`.
By the subsequence criterion it suffices to treat a subsequence `tⱼ` given by (V).  For
`0 < η < 1/2` the open square `U_η` (`‖w‖ < 3`, `|⟨w, a⟩|, |⟨w, e⟩| < 1 − η`) and the compact
square `K_η` (`≤ 3`, `≤ 1 + η`) satisfy `(dilation a tⱼ)⁻¹ U_η ⊆ Z(s, tⱼ)` and
`Z(s, tⱼ) ∩ B_{3tⱼ}(a) ⊆ (dilation a tⱼ)⁻¹ K_η` for large `j`; with (L) and the portmanteau
inequalities for `ν = m H²⌞Q` this gives `4m(1 − η)² ≤ liminf ≤ limsup ≤ 4m(1 + η)²`.
Let `η ↓ 0`. -/
theorem Submission.idtp_cse_bml_box_mass_limit : ∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (m : ℕ) (s : ℝ), IsFiniteMeasureOnCompacts μ → Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → (∀ s' : ℝ, 0 < s' → s' ≤ s → μ ({x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} \ ball a (3 * s')) = 0) → (∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams (φ j))⁻¹ ^ 2 * ∫ x, g (dilation a (lams (φ j)) x) ∂μ) atTop (𝓝 ((m : ℝ) * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) → Tendsto (fun s' : ℝ => μ {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} / ENNReal.ofReal (s' ^ 2)) (𝓝[>] 0) (𝓝 (4 * (m : ℝ≥0∞))) := by
  intro P μ Q a e m s hμ hQ haQ heQ ha he hae hs hL hV
  set Z : ℝ → Set (Euclid P) := fun s' => {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s' ∧
    |Real.arctan (inner ℝ x e / inner ℝ x a)| < s' ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}
  -- Steps 2–8, along a null sequence `tⱼ > 0` for which (V) holds
  have key : ∀ t : ℕ → ℝ, (∀ j, 0 < t j) → Tendsto t atTop (𝓝 0) →
      (∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g →
        Tendsto (fun j => (t j)⁻¹ ^ 2 * ∫ x, g (dilation a (t j) x) ∂μ) atTop
          (𝓝 ((m : ℝ) * ∫ x in (Q : Set (Euclid P)), g x ∂μHE[2]))) →
      Tendsto (fun j => μ (Z (t j)) / ENNReal.ofReal (t j ^ 2)) atTop (𝓝 (4 * (m : ℝ≥0∞))) := by
    intro t ht0 ht hVt
    -- Step 3: `ν = m H²⌞Q` is finite on compact sets, and `∫ g dν = m ∫_Q g dH²`
    obtain ⟨hQfin, hsq⟩ :=
      Submission.idtp_cse_bml_plane_square_measure P Q a e hQ haQ heQ ha he hae
    set ν : Measure (Euclid P) := (m : ℝ≥0∞) • μHE[2].restrict (Q : Set (Euclid P)) with hν
    have hνfin : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
      rw [hν, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top m) (hQfin.lt_top_of_isCompact hK)⟩
    have hconv : ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g →
        Tendsto (fun j => (t j)⁻¹ ^ 2 * ∫ x, g (dilation a (t j) x) ∂μ) atTop
          (𝓝 (∫ x, g x ∂ν)) := by
      intro g hg hgc
      rw [hν, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]
      exact hVt g hg hgc
    -- Step 4: limsup on compact sets and liminf on open sets of the rescaled masses
    -- `ofReal (tⱼ⁻²) μ((dilation a tⱼ)⁻¹ ·)`
    obtain ⟨hC, hO⟩ :=
      Submission.idtp_cse_bml_rescaled_portmanteau P μ ν a t hμ hνfin ht0 hconv
    -- Step 5: `c / ofReal (tⱼ²) = ofReal (tⱼ⁻²) c`
    have hdiv : ∀ j (c : ℝ≥0∞),
        c / ENNReal.ofReal (t j ^ 2) = ENNReal.ofReal ((t j)⁻¹ ^ 2) * c := by
      intro j c
      rw [ENNReal.div_eq_inv_mul, inv_pow, ENNReal.ofReal_inv_of_pos (pow_pos (ht0 j) 2)]
    -- Steps 6–7: for `0 < η < 1/2`, `4m(1 − η)² ≤ liminf` and `limsup ≤ 4m(1 + η)²`
    have hη : ∀ η : ℝ, 0 < η → η < 1 / 2 →
        (m : ℝ≥0∞) * ENNReal.ofReal (4 * (1 - η) ^ 2) ≤
            liminf (fun j => μ (Z (t j)) / ENNReal.ofReal (t j ^ 2)) atTop ∧
          limsup (fun j => μ (Z (t j)) / ENNReal.ofReal (t j ^ 2)) atTop ≤
            (m : ℝ≥0∞) * ENNReal.ofReal (4 * (1 + η) ^ 2) := by
      intro η hη0 hη1
      -- the open square `U_η` and the compact square `K_η`, and their `ν`-measures
      have hUo : IsOpen {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < 1 - η ∧ |inner ℝ w e| < 1 - η} :=
        (isOpen_lt (by fun_prop) (by fun_prop)).and
          ((isOpen_lt (by fun_prop) (by fun_prop)).and (isOpen_lt (by fun_prop) (by fun_prop)))
      have hKc : IsCompact
          {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ 1 + η ∧ |inner ℝ w e| ≤ 1 + η} := by
        refine (isCompact_closedBall (0 : Euclid P) 3).of_isClosed_subset ?_
          fun w hw => mem_closedBall_zero_iff.mpr hw.1
        exact (isClosed_le (by fun_prop) (by fun_prop)).and
          ((isClosed_le (by fun_prop) (by fun_prop)).and (isClosed_le (by fun_prop) (by fun_prop)))
      have hνU : ν {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < 1 - η ∧ |inner ℝ w e| < 1 - η} =
          (m : ℝ≥0∞) * ENNReal.ofReal (4 * (1 - η) ^ 2) := by
        rw [hν, Measure.smul_apply, smul_eq_mul, (hsq (1 - η) (by linarith) (by linarith)).1]
      have hνK : ν {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ 1 + η ∧ |inner ℝ w e| ≤ 1 + η} =
          (m : ℝ≥0∞) * ENNReal.ofReal (4 * (1 + η) ^ 2) := by
        rw [hν, Measure.smul_apply, smul_eq_mul, (hsq (1 + η) (by linarith) (by linarith)).2]
      -- Step 6: once `20 tⱼ < 1`, `30 tⱼ < η` and `6 tⱼ < s`, the box inclusions and (L)
      -- sandwich `μ(Z(s, tⱼ)) / ofReal (tⱼ²)` between the rescaled masses of `U_η` and `K_η`
      have hsand : ∀ᶠ j in atTop,
          ENNReal.ofReal ((t j)⁻¹ ^ 2) * μ (dilation a (t j) ⁻¹'
              {w : Euclid P | ‖w‖ < 3 ∧ |inner ℝ w a| < 1 - η ∧ |inner ℝ w e| < 1 - η}) ≤
            μ (Z (t j)) / ENNReal.ofReal (t j ^ 2) ∧
          μ (Z (t j)) / ENNReal.ofReal (t j ^ 2) ≤
            ENNReal.ofReal ((t j)⁻¹ ^ 2) * μ (dilation a (t j) ⁻¹'
              {w : Euclid P | ‖w‖ ≤ 3 ∧ |inner ℝ w a| ≤ 1 + η ∧ |inner ℝ w e| ≤ 1 + η}) := by
        filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20)),
          ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 30)),
          ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < s / 6))] with j hj1 hj2 hj3
        obtain ⟨hin, hout⟩ := Submission.idtp_cse_bml_rescaled_box_inclusions P Q a e s η (t j)
          haQ ha he hae hη0 (ht0 j) (by linarith) (by linarith) (by linarith)
        have hnull : μ (Z (t j) \ ball a (3 * t j)) = 0 := hL (t j) (ht0 j) (by linarith)
        rw [hdiv]
        refine ⟨mul_le_mul_right (measure_mono hin) _, mul_le_mul_right ?_ _⟩
        calc μ (Z (t j)) ≤ μ (Z (t j) ∩ ball a (3 * t j)) + μ (Z (t j) \ ball a (3 * t j)) :=
              measure_le_inter_add_sdiff μ _ _
          _ = μ (Z (t j) ∩ ball a (3 * t j)) := by rw [hnull, add_zero]
          _ ≤ _ := measure_mono hout
      -- Step 7
      constructor
      · rw [← hνU]
        exact (hO _ hUo).trans (liminf_le_liminf (hsand.mono fun j hj => hj.1))
      · rw [← hνK]
        exact (limsup_le_limsup (hsand.mono fun j hj => hj.2)).trans (hC _ hKc)
    -- Step 8: `m ofReal (4(1 ∓ η)²) → 4m` as `η ↓ 0`
    have hlim : ∀ c : ℝ, Tendsto (fun η : ℝ => (m : ℝ≥0∞) * ENNReal.ofReal (4 * (1 + c * η) ^ 2))
        (𝓝[>] 0) (𝓝 (4 * (m : ℝ≥0∞))) := by
      intro c
      have h : Tendsto (fun η : ℝ => ENNReal.ofReal (4 * (1 + c * η) ^ 2)) (𝓝 0)
          (𝓝 (ENNReal.ofReal (4 * (1 + c * 0) ^ 2))) :=
        (ENNReal.continuous_ofReal.comp (by fun_prop)).tendsto 0
      convert (ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.natCast_ne_top m))).mono_left
        nhdsWithin_le_nhds using 2
      simp [mul_comm]
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · refine le_of_tendsto (hlim (-1)) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with η hη'
      simpa [← sub_eq_add_neg] using (hη η hη'.1 hη'.2).1
    · refine ge_of_tendsto (hlim 1) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with η hη'
      simpa using (hη η hη'.1 hη'.2).2
  -- Step 1: the subsequence criterion, the subsequence being supplied by (V)
  refine Submission.idtp_cse_bml_tendsto_nhdsGT_of_subseq _ _ fun lams hl0 hl => ?_
  obtain ⟨φ, hφ, hVφ⟩ := hV lams hl0 hl
  exact ⟨φ, hφ, key (fun j => lams (φ j)) (fun j => hl0 (φ j)) (hl.comp hφ.tendsto_atTop) hVφ⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
