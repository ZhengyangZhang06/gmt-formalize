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

/-- **`Hⁿ` under the blow-up map `η_{x,r}(y) = r⁻¹(y − x)`, `r > 0`**: `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)`
for every `S ⊆ ℝᴾ`, the scaling used in the proof of Simon Ch. 3, Theorem 1.6 "⇒".  `η_{x,r}` is
the translation `y ↦ y + (−x)`, an isometry, followed by the dilation `z ↦ r⁻¹z`, and
`Hⁿ(cT) = |c|ⁿ Hⁿ(T)` for `c ≠ 0`. -/
theorem Submission.rsd_cmr_ir_blowUp_image_measure : ∀ (P n : ℕ) (x : Euclid P) (r : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] S := by
  intro P n x r S hr
  -- `η_{x,r}(S) = r⁻¹ • (S + (−x))`: `η_{x,r}(y) = r⁻¹ • (y − x)` and `y − x = y + (−x)`.
  have hS : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
      (fun z => r⁻¹ • z) '' ((fun y => y + -x) '' S) := by
    rw [Set.image_image]
    rfl
  -- `Hⁿ(r⁻¹ • T) = ‖r⁻¹‖₊ⁿ • Hⁿ(T)`, translation invariance, and `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n` for `r > 0`.
  rw [hS, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
    (isometry_add_right (-x)).euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul,
    ← ENNReal.ofReal_coe_nnreal]
  congr 2
  simp [abs_of_pos hr]

/-- Deleting from the Borel set `M` a set that is `Hⁿ`-null near `x` keeps the approximate
tangent space of `M` at `x` (Simon Ch. 3, 1.4): if `M' ⊆ M` and `Hⁿ((M ∖ M') ∩ B_δ(x)) = 0`, then
`TₓM = Q` gives `TₓM' = Q`.  Choose `R₀ > 0` with `spt f ⊆ B̄_{R₀}(0)`.  For
`0 < λ < δ/(R₀ + 1)`, a point `z = η_{x,λ}(y)` of `η_{x,λ}(M) ∖ η_{x,λ}(M')` with `f(z) ≠ 0` has
`y ∈ M ∖ M'` and `|y − x| = λ|z| ≤ λR₀ < δ`, so it lies in `η_{x,λ}((M ∖ M') ∩ B_δ(x))`, which is
`Hⁿ`-null by `rsd_cmr_ir_blowUp_image_measure`.  Hence `f = 0` a.e. on
`η_{x,λ}(M) ∖ η_{x,λ}(M')`, and the Borel set `η_{x,λ}(M)` and its subset `η_{x,λ}(M')` carry the
same integral of `f` for all small `λ` (as in the proof of 1.6 "⇒"). -/
theorem Submission.rsd_cmr_ir_approxTangent_of_local_null : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P) (δ : ℝ) (Q : Submodule ℝ (Euclid P)), MeasurableSet M → M' ⊆ M → 0 < δ → μHE[n] ((M \ M') ∩ ball x δ) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x δ Q hM hM'M hδ hnull hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `spt f ⊆ B̄_{R₀}(0)` with `R₀ > 0`
  obtain ⟨R₀, hR₀, hfR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  have hR₀' : (0 : ℝ) < R₀ + 1 := by linarith
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR₀')] with r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  -- `Z_λ = η_{x,λ}((M ∖ M') ∩ B_δ(x))` is `Hⁿ`-null
  have hZ : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' ((M \ M') ∩ ball x δ)) = 0 := by
    rw [Submission.rsd_cmr_ir_blowUp_image_measure P n x r _ hr.1, hnull, mul_zero]
  -- `η_{x,λ}(y) = λ⁻¹ • (y − x)`
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη] at hZ ⊢
  -- `η_{x,λ}(M)` is Borel: it is the preimage of `M` under `z ↦ x + λ • z`
  have hmeas : MeasurableSet ((fun y => r⁻¹ • (y - x)) '' M) := by
    have himg : (fun y => r⁻¹ • (y - x)) '' M = (fun z => x + r • z) ⁻¹' M := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [smul_smul, mul_inv_cancel₀ hr0] using hy
      · intro hz
        exact ⟨x + r • z, hz, by simp [smul_smul, inv_mul_cancel₀ hr0]⟩
    rw [himg]
    exact hM.preimage (by fun_prop)
  -- `f` vanishes on `η_{x,λ}(M) ∖ η_{x,λ}(M')` off `Z_λ`, hence a.e. there
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hmeas.nullMeasurableSet
    (image_mono hM'M) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ] with z hzZ hz
  obtain ⟨⟨y, hyM, rfl⟩, hyM'⟩ := hz
  apply image_eq_zero_of_notMem_tsupport
  intro hyf
  apply hzZ
  refine ⟨y, ⟨⟨hyM, fun h => hyM' ⟨y, h, rfl⟩⟩, ?_⟩, rfl⟩
  -- `|y − x| = λ|η_{x,λ}(y)| ≤ λR₀ < λ(R₀ + 1) < δ`
  have h1 : ‖r⁻¹ • (y - x)‖ ≤ R₀ := mem_closedBall_zero_iff.mp (hfR₀ hyf)
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.1.le, inv_mul_le_iff₀ hr.1] at h1
  have h2 := (lt_div_iff₀ hR₀').mp hr.2
  rw [mem_ball, dist_eq_norm]
  linarith [hr.1]

/-- **Restricting an integer multiplicity triple to a locally full-measure subset.**  If
`R = (M, θ, ξ)` is an integer multiplicity triple in `U` and `A` is Borel, then `(M ∩ A, θ', ξ)` is
one in `U'` provided `M ∩ A ⊆ U'`, `θ'` is measurable, positive on `M ∩ A` and locally integrable
on `M ∩ A` in `U'`, and `Hⁿ`-a.e. `x ∈ M ∩ A` has a ball `B_δ(x)` with `Hⁿ((M \ A) ∩ B_δ(x)) = 0`.
This is used for `(M ∩ B, 1, ξ)`, `B` open, and for `(M_X ∩ K, θ_X, ξ_X)` in the constant
multiplicity reduction behind Simon 7.4.2 (via Ch. 5, Corollary 7.3).  All fields but the
orientation pass from `R` to the subset `M ∩ A ⊆ M`; at such `x`, `T_x(M ∩ A) = T_xM`
(Simon Ch. 3, Definition 1.4, chapter-03.txt lines 77–84) by
`Submission.rsd_cmr_ir_approxTangent_of_local_null`, since `M \ (M ∩ A) = M \ A`. -/
theorem Submission.rsd_cmr_imrep_restrict : ∀ (P n : ℕ) (U U' A : Set (Euclid P)) (R : IMRep U n) (θ : Euclid P → ℕ), MeasurableSet A → R.carrier ∩ A ⊆ U' → Measurable θ → (∀ x ∈ R.carrier ∩ A, 0 < θ x) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U' → ∫⁻ x in R.carrier ∩ A ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ A)), ∃ δ : ℝ, 0 < δ ∧ μHE[n] ((R.carrier \ A) ∩ ball x δ) = 0) → ∃ R' : IMRep U' n, R'.carrier = R.carrier ∩ A ∧ R'.mult = θ ∧ R'.orient = R.orient := by
  intro P n U U' A R θ hA hsub hθ hθpos hθint hlocal
  refine ⟨{ carrier := R.carrier ∩ A
            mult := θ
            orient := R.orient
            measurableSet_carrier := R.measurableSet_carrier.inter hA
            carrier_subset := hsub
            rectifiable := R.rectifiable.mono inter_subset_left
            measurable_mult := hθ
            mult_pos := hθpos
            locallyIntegrable_mult := hθint
            aestronglyMeasurable_orient :=
              R.aestronglyMeasurable_orient.mono_set inter_subset_left
            orients := ?_ }, rfl, rfl, rfl⟩
  -- `Hⁿ⌞(M ∩ A)`-a.e. `x` has `T_xM = Q` oriented by `ξ(x)` (from `Hⁿ⌞M`-a.e., `M ∩ A ⊆ M`) and
  -- a ball `B_δ(x)` on which `M \ (M ∩ A) = M \ A` is `Hⁿ`-null, so `T_x(M ∩ A) = Q`.
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients, hlocal]
    with x ⟨Q, hQ, hξ⟩ ⟨δ, hδ, hnull⟩
  refine ⟨Q, Submission.rsd_cmr_ir_approxTangent_of_local_null P n R.carrier (R.carrier ∩ A) x δ Q
    R.measurableSet_carrier inter_subset_left hδ ?_ hQ, hξ⟩
  rwa [Set.sdiff_self_inter]
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]

/-- **Simon Ch. 6, 3.1 (‡)**: the integrand `θ ⟨ω, ξ⟩` of `τ(M, θ, ξ)(ω)` is `Hⁿ⌞M`-integrable.
`ω` is continuous with compact support `K = spt ω ⊆ U`, so `‖ω‖ ≤ C` and `ω = 0` off `K`, and
`‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e.; hence `|θ ⟨ω, ξ⟩| ≤ C θ 1_K`, integrable as `∫_{M ∩ K} θ dHⁿ < ∞`. -/
theorem Submission.rsd_cmr_ic_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
  obtain ⟨⟨hsmooth, hcpt⟩, hsupp⟩ := hω
  have hcont : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  -- `‖ω‖ ≤ C`, and `K = spt ω` is closed
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hcont
  have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
    (isClosed_tsupport _).measurableSet
  have hθ : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- `1_K θ` is `Hⁿ⌞M`-integrable: `∫_{M ∩ K} θ dHⁿ < ∞`
  have hh : Integrable ((tsupport (ω : DifferentialForm (Euclid P) n)).indicator
      fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
    refine ⟨hθ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
    exact (R.locallyIntegrable_mult _ hcpt.isCompact hsupp).lt_top
  -- `θ ⟨ω, ξ⟩` is a.e. strongly measurable and dominated by `C θ 1_K`
  refine (hh.const_mul C).mono' (hθ.aestronglyMeasurable.mul
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable))) ?_
  filter_upwards [R.orients] with x hx
  obtain ⟨Q, -, hQ⟩ := hx
  have hξ := (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  by_cases hK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
  · rw [indicator_of_mem hK, norm_mul, Real.norm_natCast, mul_comm C]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖
        ≤ ‖R.orient x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (R.orient x).le_opNorm _
      _ ≤ 1 * C := mul_le_mul hξ (hC x) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  · simp [indicator_of_notMem hK, image_eq_zero_of_notMem_tsupport hK]
/-- **Simon Ch. 6, 3.1 (‡)**: if `spt ω ⊆ K` for a compact `K ⊆ U` and `‖ω(x)‖ ≤ ε` for all `x`,
then `|τ(M, θ, ξ)(ω)| ≤ ε ∫_{M ∩ K} θ dHⁿ`.  `Hⁿ`-a.e. on `M`, `ξ(x)` is a unit orientation, so
`‖ξ(x)‖ ≤ 1` and `|θ(x) ⟨ω(x), ξ(x)⟩| ≤ ε θ(x) 1_K(x)`; the bound `θ 1_K` is `Hⁿ⌞M`-integrable
with integral `∫_{M ∩ K} θ dHⁿ < ∞`, `θ` being locally `Hⁿ`-integrable in `U`. -/
theorem Submission.rsd_cmr_ic_action_abs_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)) (ω : TestFormOn U n) (ε : ℝ), IsCompact K → K ⊆ U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ ε) → |R.action (ω : DifferentialForm (Euclid P) n)| ≤ ε * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
  intro P n U R K ω ε hK hKU hsupp hbound
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hθ0 : ∀ x, (0 : ℝ) ≤ R.mult x := fun x => Nat.cast_nonneg _
  -- `(Hⁿ⌞M)⌞K = Hⁿ⌞(M ∩ K)`, and `ofReal θ = θ` since `θ` is `ℕ`-valued
  have hrestr : (μHE[n].restrict R.carrier).restrict K = μHE[n].restrict (R.carrier ∩ K) := by
    rw [Measure.restrict_restrict hKm, inter_comm]
  have hlint : ∫⁻ x, ENNReal.ofReal (R.mult x : ℝ) ∂(μHE[n].restrict (R.carrier ∩ K)) =
      ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    simp_rw [ENNReal.ofReal_natCast]
  -- `θ 1_K` is `Hⁿ⌞M`-integrable with integral `∫_{M ∩ K} θ dHⁿ`
  have hint : Integrable (K.indicator fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    rw [integrable_indicator_iff hKm, IntegrableOn, hrestr]
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hθ0), hlint]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hval : ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂(μHE[n].restrict R.carrier) =
      (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    rw [integral_indicator hKm, hrestr,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hθ0) hθm.aestronglyMeasurable, hlint]
  -- `‖ξ(x)‖ ≤ 1` for `Hⁿ`-a.e. `x ∈ M`, `ξ(x)` being a unit orientation there
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `|θ ⟨ω, ξ⟩| ≤ θ ‖ξ‖ ‖ω‖ ≤ ε θ` on `K`, and `ω = 0` off `K ⊇ spt ω`
  have hpt : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ ≤
        ε * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_of_nonneg (hθ0 x), mul_comm ε]
      refine mul_le_mul_of_nonneg_left ?_ (hθ0 x)
      calc ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖
          ≤ ‖R.orient x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (R.orient x).le_opNorm _
        _ ≤ 1 * ε := mul_le_mul hx (hbound x) (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
    · have hωx : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp h)
      rw [indicator_of_notMem hxK, hωx, map_zero, mul_zero, norm_zero, mul_zero]
  -- `|τ(M, θ, ξ)(ω)| ≤ ∫ ε θ 1_K d(Hⁿ⌞M) = ε ∫_{M ∩ K} θ dHⁿ`
  have h := norm_integral_le_of_norm_le (hint.const_mul ε) hpt
  rwa [integral_const_mul, hval, Real.norm_eq_abs] at h

/-- **Simon Ch. 6, 3.1 (‡)**: an integer multiplicity triple `(M, θ, ξ)` in `U` defines a current
`τ(M, θ, ξ) ∈ 𝒟ₙ(U)`, `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)`.  The integrand is
`Hⁿ⌞M`-integrable, so `ω ↦ τ(M, θ, ξ)(ω)` is linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)`, then
`spt ωⱼ ⊆ K` for one compact `K ⊆ U` and `ωⱼ → 0` uniformly on `K`; for `ε > 0` and `j` large,
`‖ωⱼ‖ ≤ δ = ε / (I + 1)`, `I = ∫_{M ∩ K} θ dHⁿ`, so `|τ(M, θ, ξ)(ωⱼ)| ≤ δ I < ε`. -/
theorem Submission.rsd_cmr_imrep_represents_exists : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  refine ⟨{ toCurrent :=
              { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
                map_add' := fun ω η => ?_
                map_smul' := fun c ω => ?_ }
            continuous' := fun ωs hωs => ?_ }, fun ω => rfl⟩
  · -- `θ ⟨ω + η, ξ⟩ = θ ⟨ω, ξ⟩ + θ ⟨η, ξ⟩`, both integrable
    simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
    exact integral_add (Submission.rsd_cmr_ic_action_integrable P n U R ω)
      (Submission.rsd_cmr_ic_action_integrable P n U R η)
  · -- `θ ⟨c ω, ξ⟩ = c θ ⟨ω, ξ⟩`
    simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
      RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · -- `spt ωⱼ ⊆ K` for a compact `K ⊆ U`, and the `0`-th derivatives `ωⱼ → 0` uniformly on `K`
    obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hωs
    change Tendsto (fun j => R.action (ωs j : DifferentialForm (Euclid P) n)) atTop (𝓝 0)
    set I := (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal
    have hI : 0 ≤ I := ENNReal.toReal_nonneg
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (hconv 0) _ hδ)
    refine ⟨N, fun j hj => ?_⟩
    -- `‖ωⱼ(x)‖ ≤ δ` everywhere: on `K` by uniform convergence, off `K` since `ωⱼ = 0` there
    have hbound : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε / (I + 1) := fun x => by
      by_cases hx : x ∈ K
      · have h := hN j hj x hx
        rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply,
          LinearIsometryEquiv.dist_map, Submodule.coe_zero, Pi.zero_apply, dist_zero_left] at h
        exact h.le
      · rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h), norm_zero]
        exact hδ.le
    -- `|τ(M, θ, ξ)(ωⱼ)| ≤ δ I < ε`
    have h := Submission.rsd_cmr_ic_action_abs_le P n U R K (ωs j) _ hK hKU (hsupp j) hbound
    rw [Real.dist_eq, sub_zero]
    calc |R.action (ωs j : DifferentialForm (Euclid P) n)| ≤ ε / (I + 1) * I := h
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Extension by zero** (Simon 6.2.16, 6.3.1; step 6(b)–(c) of the proof of 7.4.2).  Let
`B ⊆ U` with `B` open, `K ⊆ B` compact, and `X = τ(M, θ, ξ) ∈ 𝒟ₙ(B)` with `μ_X = θ Hⁿ⌞M`
vanishing near each point of `B \ K`.  By second countability `μ_X(B \ K) = 0`, so
`Hⁿ(M \ K) = 0` as `θ ≥ 1` on `M ⊆ B`.  Then `E = τ(M ∩ K, θ, ξ) ∈ 𝒟ₙ(U)` is integer
multiplicity, extends `X` (`M ∩ K = M` up to the `Hⁿ`-null set `M \ K`) and vanishes on forms
whose support misses `K`. -/
theorem Submission.rsd_cmr_zero_extension : ∀ (P n : ℕ) (U B K : Set (Euclid P)) (hBU : B ⊆ U) (X : GeometricCurrentOn B n) (R : IMRep B n), IsOpen B → IsCompact K → K ⊆ B → R.Represents X → (∀ y ∈ B, y ∉ K → ∃ ρ : ℝ, 0 < ρ ∧ R.measure (ball y ρ) = 0) → ∃ E : GeometricCurrentOn U n, IsIntegerMultiplicity E ∧ (∀ ω : TestFormOn B n, E (testFormOnInclusion hBU n ω) = X ω) ∧ ∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → E ω = 0 := by
  intro P n U B K hBU X R hB hK hKB hX hloc
  -- `μ_X(B \ K) = 0`: each point of `B \ K` has a `μ_X`-null ball, and `ℝᴾ` is second countable.
  have hnull : R.measure (B \ K) = 0 :=
    measure_null_of_locally_null _ fun y hy => by
      obtain ⟨ρ, hρ, hball⟩ := hloc y hy.1 hy.2
      exact ⟨ball y ρ, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hρ), hball⟩
  -- `Hⁿ(M \ K) ≤ ∫_{M ∩ (B \ K)} θ dHⁿ = μ_X(B \ K) = 0`, since `θ ≥ 1` on `M ⊆ B`.
  have hBK : MeasurableSet (B \ K) := hB.measurableSet.diff hK.measurableSet
  have hMK : μHE[n] (R.carrier \ K) = 0 := by
    refine nonpos_iff_eq_zero.1 (le_of_le_of_eq ?_ hnull)
    calc μHE[n] (R.carrier \ K) ≤ μHE[n] ((B \ K) ∩ R.carrier) :=
          measure_mono fun x hx => ⟨⟨R.carrier_subset hx.1, hx.2⟩, hx.1⟩
      _ = ∫⁻ _ in (B \ K) ∩ R.carrier, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in (B \ K) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' (hBK.inter R.measurableSet_carrier) fun x hx =>
            Nat.one_le_cast.2 (R.mult_pos x hx.2)
      _ = R.measure (B \ K) := by
          rw [IMRep.measure, withDensity_apply _ hBK, Measure.restrict_restrict hBK]
  -- `(M ∩ K, θ, ξ)` is a triple in `U`: `θ` is integrable on the compact `K ⊆ B`, and the
  -- discarded part `M \ K` is `Hⁿ`-null.
  obtain ⟨R', hR'c, hR'm, hR'o⟩ := Submission.rsd_cmr_imrep_restrict P n B U K R R.mult
    hK.measurableSet (fun x hx => hBU (hKB hx.2)) R.measurable_mult
    (fun x hx => R.mult_pos x hx.1)
    (fun _ _ _ => ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKB)
      (lintegral_mono_set inter_subset_left))
    (Eventually.of_forall fun _ => ⟨1, one_pos, measure_mono_null inter_subset_left hMK⟩)
  -- `E = τ(M ∩ K, θ, ξ) ∈ 𝒟ₙ(U)`.
  obtain ⟨E, hE⟩ := Submission.rsd_cmr_imrep_represents_exists P n U R'
  refine ⟨E, ⟨R', hE⟩, fun ω => ?_, fun ω hω => ?_⟩
  · -- `E` extends `X`: `M ∩ K` and `M` differ by the `Hⁿ`-null set `M \ K`.
    rw [hE (testFormOnInclusion hBU n ω), hX ω]
    simp only [IMRep.action, testFormOnInclusion_coe]
    rw [hR'c, hR'm, hR'o]
    refine setIntegral_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [Set.sdiff_eq_empty.2 inter_subset_left, measure_empty]
    · rwa [Set.sdiff_self_inter]
  · -- `E(ω) = 0` when `spt ω ∩ K = ∅`: `ω` vanishes on `M ∩ K ⊆ K`.
    rw [hE ω]
    simp only [IMRep.action]
    rw [hR'c]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport (Set.disjoint_right.1 hω hx.2), map_zero, mul_zero]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
