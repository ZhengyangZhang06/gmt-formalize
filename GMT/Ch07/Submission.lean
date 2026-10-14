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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Mollification by an even `C¹` kernel `η` with compact support commutes with `D` and is
self-adjoint: `∫ D(η * u)(x)(s x) dx = −∫ u div(η * s)` for integrable `u`, `s` (Simon Ch. 2,
Lemma 2.5).  Both derivatives are convolutions with the odd, bounded `Dη`, and Fubini applies to
`Dη(x − z)(s x) u(z)`, which is dominated by `C ‖s x‖ |u z|`. -/
theorem codim1_rdo_dg_sp_mollifier_adjoint : ∀ (P : ℕ) (η u : Euclid P → ℝ) (s : Euclid P → Euclid P), ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, η (-z) = η z) → Integrable u → Integrable s → ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z : Euclid P →ₗ[ℝ] Euclid P) := by
  intro P η u s hη hηc heven hu hs
  -- Step 0: `Dη` is continuous with compact support, hence bounded by some `C`.
  have hDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDcs : HasCompactSupport (fderiv ℝ η) := hηc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 1: `η` is even, so `Dη` is odd (chain rule for `η = η ∘ (−id)`).
  have hodd : ∀ y, fderiv ℝ η (-y) = -fderiv ℝ η y := by
    intro y
    have h1 : HasFDerivAt (η ∘ fun z => -z)
        ((fderiv ℝ η (-y)).comp (-ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hη.differentiable one_ne_zero) (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
    rw [show (η ∘ fun z => -z) = η from funext heven] at h1
    ext v
    rw [h1.fderiv]
    simp
  -- Step 2: `D(η * u)(x) = (Dη * u)(x)`, so `D(η * u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz`.
  have hLHS : ∀ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) =
      ∫ z, fderiv ℝ η (x - z) (s x) * u z := by
    intro x
    rw [(hηc.hasFDerivAt_convolution_left _ hη hu.locallyIntegrable x).fderiv, convolution_eq_swap,
      ContinuousLinearMap.integral_apply
        ((hDcs.convolutionExists_left _ hDc hu.locallyIntegrable x).integrable_swap)]
    simp
  -- Step 3: `div(η * s)(z) = trace D(η * s)(z) = ∫ Dη(z − x)(s x) dx`: the trace `T` is a
  -- continuous linear functional, and the trace of the rank-one map `v ↦ a(v) w` is `a(w)`.
  have hRHS : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
        Euclid P →ₗ[ℝ] Euclid P) = ∫ x, fderiv ℝ η (z - x) (s x) := by
    let T : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid P) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have hTA : ∀ A : Euclid P →L[ℝ] Euclid P,
        T A = LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) := fun A => rfl
    have hrk : ∀ (a : Euclid P →L[ℝ] ℝ) (w : Euclid P), T (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w) = a w := by
      intro a w
      have h : ((ContinuousLinearMap.precompL (Euclid P)
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w :
            Euclid P →L[ℝ] Euclid P) : Euclid P →ₗ[ℝ] Euclid P) =
          (a : Euclid P →ₗ[ℝ] ℝ).smulRight w := by
        ext v
        simp
      rw [hTA, h, LinearMap.trace_smulRight]
      rfl
    intro z
    rw [(hηc.hasFDerivAt_convolution_left _ hη hs.locallyIntegrable z).fderiv, convolution_eq_swap]
    have hT := ContinuousLinearMap.integral_comp_comm T
      ((hDcs.convolutionExists_left (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P)) hDc
          hs.locallyIntegrable z).integrable_swap)
    simp_rw [hrk] at hT
    exact hT.symm
  -- Step 4: Fubini for `H(x, z) = Dη(x − z)(s x) u(z)`, dominated by `C ‖s x‖ |u z|`.
  have hint : Integrable (uncurry fun x z => fderiv ℝ η (x - z) (s x) * u z)
      ((volume : Measure (Euclid P)).prod volume) := by
    refine Integrable.mono' ((hs.norm.mul_prod hu.norm).const_mul C) ?_ (Eventually.of_forall ?_)
    · exact ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
        hs.aestronglyMeasurable.comp_fst
        (hDc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hu.aestronglyMeasurable.comp_snd
    · rintro ⟨x, z⟩
      simp only [uncurry_apply_pair, norm_mul]
      calc ‖fderiv ℝ η (x - z) (s x)‖ * ‖u z‖ ≤ (C * ‖s x‖) * ‖u z‖ := by
            gcongr
            exact ((fderiv ℝ η (x - z)).le_opNorm (s x)).trans (by gcongr; exact hC _)
        _ = C * (‖s x‖ * ‖u z‖) := by ring
  -- Step 5: combine, using `Dη(z − x) = −Dη(x − z)` to identify the swapped integral.
  calc ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x)
      = ∫ x, ∫ z, fderiv ℝ η (x - z) (s x) * u z := by simp_rw [hLHS]
    _ = ∫ z, ∫ x, fderiv ℝ η (x - z) (s x) * u z := integral_integral_swap hint
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P)
          (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
            Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_neg]
      congr 1
      funext z
      rw [hRHS z, ← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      rw [← neg_sub x z, hodd, neg_apply]
      ring
/-- Mollification does not increase the variation (Simon Ch. 2, Lemma 2.5, formula (4)): if
`|∫ u div g| ≤ M` for every `g ∈ C¹_c(ℝᴾ; ℝᴾ)` with `|g| ≤ 1`, then `∫ |D(η * u)| ≤ M` for an even
mollifier `η ≥ 0` with `∫ η = 1`.  With `w = η * u`, the field `s = 1_{spt w} |∇w|⁻¹ ∇w`
(`0⁻¹ = 0`) is Borel, bounded by `1`, compactly supported and has `Dw(s) = |Dw|`;
`codim1_rdo_dg_sp_mollifier_adjoint` moves `η` onto `s`, and `g = η * s` is admissible. -/
theorem codim1_rdo_dg_sp_mollify_variation : ∀ (P : ℕ) (u : Euclid P → ℝ) (M : ℝ), Integrable u → HasCompactSupport u → (∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ M) → ∀ η : Euclid P → ℝ, ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, 0 ≤ η z) → (∀ z, η (-z) = η z) → ∫ z, η z = 1 → ∫ z, ‖fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) z‖ ≤ M := by
  intro P u M hu huc hM η hη hηc hη0 heven hη1
  -- Step 1: `w = η * u` is `C¹` with compact support `S = spt w`.
  set w := convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwc : HasCompactSupport w := hηc.convolution _ huc
  have hDw : Continuous (fderiv ℝ w) :=
    (hηc.contDiff_convolution_left _ hη hu.locallyIntegrable).continuous_fderiv one_ne_zero
  set S := tsupport w
  have hSm : MeasurableSet S := (isClosed_tsupport w).measurableSet
  -- Step 2: the gradient `∇w = (toDual)⁻¹ Dw` is continuous, `|∇w| = |Dw|`, `Dw(∇w) = |∇w|²`.
  set grad : Euclid P → Euclid P :=
    fun x => (InnerProductSpace.toDual ℝ (Euclid P)).symm (fderiv ℝ w x)
  have hgc : Continuous grad := (InnerProductSpace.toDual ℝ (Euclid P)).symm.continuous.comp hDw
  have hgn : ∀ x, ‖grad x‖ = ‖fderiv ℝ w x‖ := fun x => LinearIsometryEquiv.norm_map _ _
  have hgg : ∀ x, fderiv ℝ w x (grad x) = ‖grad x‖ ^ 2 := by
    intro x
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := grad x) (y := fderiv ℝ w x)]
    exact real_inner_self_eq_norm_sq _
  -- Step 3: the unit field `f = |∇w|⁻¹ ∇w` (`0⁻¹ = 0`) and `s = 1_S f`.
  set f : Euclid P → Euclid P := fun x => ‖grad x‖⁻¹ • grad x with hf
  have hfm : Measurable f := hgc.norm.measurable.inv.smul hgc.measurable
  have hf1 : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    simp only [hf, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖grad x‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  set s : Euclid P → Euclid P := S.indicator f with hs
  have hs1 : ∀ x, ‖s x‖ ≤ 1 := fun x => (norm_indicator_le_norm_self f x).trans (hf1 x)
  have hsc : HasCompactSupport s :=
    HasCompactSupport.intro hwc.isCompact fun x hx => indicator_of_notMem hx f
  have hsi : Integrable s := by
    rw [hs, integrable_indicator_iff hSm]
    exact Measure.integrableOn_of_bounded hwc.isCompact.measure_lt_top.ne
      hfm.aestronglyMeasurable (Eventually.of_forall hf1)
  -- Step 4: `Dw(x)(s x) = |Dw(x)|` for all `x`.
  have hDs : ∀ x, fderiv ℝ w x (s x) = ‖fderiv ℝ w x‖ := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hs, indicator_of_mem hx, hf, map_smul, hgg, smul_eq_mul, ← hgn]
      rcases eq_or_ne ‖grad x‖ 0 with h | h
      · simp [h]
      · field_simp
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  -- Step 5: `g = η * s` is admissible: `C¹`, compact support, `|g| ≤ ∫ η = 1`.
  set g := convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume with hg
  have hgC1 : ContDiff ℝ 1 g := hηc.contDiff_convolution_left _ hη hsi.locallyIntegrable
  have hgcs : HasCompactSupport g := hηc.convolution _ hsc
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  have hg1 : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    rw [hg, convolution_def]
    refine (norm_integral_le_of_norm_le hηi (Eventually.of_forall fun t => ?_)).trans hη1.le
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hη0 t)]
    exact mul_le_of_le_one_right (hη0 t) (hs1 _)
  -- Steps 6–7: the adjoint identity, then the hypothesis for `g`.
  calc ∫ z, ‖fderiv ℝ w z‖ = ∫ z, fderiv ℝ w z (s z) :=
        integral_congr_ae (Eventually.of_forall fun z => (hDs z).symm)
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) :=
        Submission.codim1_rdo_dg_sp_mollifier_adjoint P η u s hη hηc heven hu hsi
    _ ≤ |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| :=
        neg_le_abs _
    _ ≤ M := hM g hgC1 hgcs hg1

/-- **Integer density, layers and truncation bounds** (Simon Ch. 6, first step and (3)–(7) of the
proof of 3.14; Remarks 2.35, 3.15; Ch. 2, Lemma 2.5).  An integer multiplicity `R ∈ 𝒟_{n+1}(ℝ^{n+1})`
with compact support is `R(ω) = ∫ θ ω(e)` for an integrable integer density `θ` vanishing off
`spt R`: an orientation of an `(n+1)`-plane in `ℝ^{n+1}` is `±e₀ ∧ ⋯ ∧ eₙ`, and `θ = 0` a.e. off
`spt R` by `dtc_vanish_off_support`.  The layers `Uⱼ = {θ ≥ j}` give `Xⱼ = [[Uⱼ]]` with
`Σⱼ ∂Xⱼ = ∂R` (dominated convergence, `∫ dη(e) = 0`).  For the mass bounds, `∂R` tested with `⋆g`
bounds `∫ θ div g` for smooth fields `|g| ≤ 1`; for an admissible `η`, integration by parts and
`codim1_rdo_dg_sp_mollifier_adjoint` give `∫ Ψ(ρₖ * θ) dη(e) ≤ M(∂R)` for Simon's smoothed
truncations `Ψ` (`|Ψ'| ≤ 1`, `Ψ = (1 - 4δ) Σⱼ 1_{[j,∞)}` on `ℤ`); letting `k → ∞` (Lebesgue
differentiation) and `δ → 0` bounds `M(Σ_{j=a}^b ∂Xⱼ)`. -/
theorem dtc_bc_lc_fd_bim_layers : ∀ (n : ℕ) (R : GeometricCurrentOn (univ : Set (Euclid (n + 1))) (n + 1)), IsIntegerMultiplicity R → IsCompact R.support → ∃ (U : ℤ → Set (Euclid (n + 1))) (X : ℤ → GeometricCurrentOn (univ : Set (Euclid (n + 1))) (n + 1)), (∀ j, MeasurableSet (U j)) ∧ (∀ j, U (j + 1) ⊆ U j) ∧ (∀ (j : ℤ) (ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1)), X j ω = ∫ x in U j, (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) ∧ (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n, HasSum (fun j => (X j).boundary η) (R.boundary η)) ∧ (∀ j, (X j).boundary.mass ≤ R.boundary.mass) ∧ ∀ (N : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid (n + 1))) n), (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n, Y η = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, (X j).boundary η) → Y.mass ≤ R.boundary.mass := by
  intro n R hIM hcpt
  classical
  -- Step 1. The determinant covector `D` of the standard basis `e`: `α = α(e) D` for every
  -- `(n+1)`-covector `α`, and `D(τ) = ±1` for orthonormal `τ`.
  obtain ⟨D, hD, hDe, hαD⟩ : ∃ D : Covector (Euclid (n + 1)) (n + 1),
      (∀ v, D v = (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det v) ∧
      D (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 ∧
      (∀ (α : Covector (Euclid (n + 1)) (n + 1)) (v : Fin (n + 1) → Euclid (n + 1)),
        α v = α (fun i => EuclideanSpace.single i (1 : ℝ)) * D v) := by
    have hcont : Continuous fun v : Fin (n + 1) → Euclid (n + 1) =>
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det v := by
      simp only [Module.Basis.det_apply]
      refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
      simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_repr]
      exact (EuclideanSpace.proj i).continuous.comp (continuous_apply j)
    have hbe : ⇑(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis =
        fun i => EuclideanSpace.single i (1 : ℝ) := by
      funext i; simp
    refine ⟨⟨⟨(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det.toMultilinearMap, hcont⟩,
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det.map_eq_zero_of_eq'⟩, fun v => rfl, ?_, ?_⟩
    · change (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det _ = 1
      rw [← hbe, Module.Basis.det_self]
    · intro α v
      have h := AlternatingMap.eq_smul_basis_det (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
        α.toAlternatingMap
      rw [hbe] at h
      exact congrArg (fun f : Euclid (n + 1) [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ => f v) h
  have hDτ : ∀ τ : Fin (n + 1) → Euclid (n + 1), Orthonormal ℝ τ → D τ = 1 ∨ D τ = -1 := by
    intro τ hτ
    have hsp := hτ.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [finrank_euclideanSpace, Fintype.card_fin])
    have h := OrthonormalBasis.det_to_matrix_orthonormalBasis_real
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) (OrthonormalBasis.mk hτ hsp.ge)
    rwa [OrthonormalBasis.coe_mk, ← hD] at h
  -- Step 2. `R` is given by an integrable integer density `θ` vanishing off `spt R`.
  obtain ⟨θ, hθm, hθ0, hθi, hRθ⟩ : ∃ θ : Euclid (n + 1) → ℤ, Measurable θ ∧
      (∀ x ∉ R.support, θ x = 0) ∧ Integrable (fun x => (θ x : ℝ)) ∧
      ∀ ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1),
        R ω = ∫ x, (θ x : ℝ) * (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    obtain ⟨Rep, hRep⟩ := hIM
    have hμ : (μHE[n + 1] : Measure (Euclid (n + 1))) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume (n + 1)
    have hVm : MeasurableSet Rep.carrier := Rep.measurableSet_carrier
    -- `ξ(x)(α) = α(e) s(x)` with `s(x) = ξ(x)(D)`
    have horient : ∀ x (α : Covector (Euclid (n + 1)) (n + 1)), Rep.orient x α =
        α (fun i => EuclideanSpace.single i (1 : ℝ)) * Rep.orient x D := by
      intro x α
      have hα : α = α (fun i => EuclideanSpace.single i (1 : ℝ)) • D := by
        ext v
        rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        exact hαD α v
      conv_lhs => rw [hα]
      rw [map_smul, smul_eq_mul]
    have hsm : AEStronglyMeasurable (fun x => Rep.orient x D) (volume.restrict Rep.carrier) :=
      hμ ▸ (continuous_eval_const D).comp_aestronglyMeasurable Rep.aestronglyMeasurable_orient
    have hs1 : ∀ᵐ x ∂(volume.restrict Rep.carrier), Rep.orient x D = 1 ∨ Rep.orient x D = -1 := by
      rw [← hμ]
      filter_upwards [Rep.orients] with x hx
      obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
      rcases hξ with h | h <;> rw [h D] <;> rcases hDτ τ hτ with h' | h' <;> rw [h']
      exacts [Or.inl rfl, Or.inr rfl, Or.inr rfl, Or.inl (neg_neg 1)]
    -- the integer density `θ₁ = ±θ₀` on `V`
    obtain ⟨s', hs'm, hss'⟩ : ∃ s' : Euclid (n + 1) → ℝ, Measurable s' ∧
        (fun x => Rep.orient x D) =ᵐ[volume.restrict Rep.carrier] s' :=
      ⟨_, hsm.stronglyMeasurable_mk.measurable, hsm.ae_eq_mk⟩
    obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : Euclid (n + 1) → ℤ, ∀ x, θ₁ x = if x ∈ Rep.carrier then
        (if 0 < s' x then (Rep.mult x : ℤ) else -(Rep.mult x : ℤ)) else 0 := ⟨_, fun x => rfl⟩
    have hθ₁m : Measurable θ₁ := (funext hθ₁ : θ₁ = _) ▸
      Measurable.ite hVm (Measurable.ite (measurableSet_lt measurable_const hs'm)
        (measurable_from_nat.comp Rep.measurable_mult)
        ((measurable_from_nat (f := fun m : ℕ => -(m : ℤ))).comp Rep.measurable_mult))
        measurable_const
    have hθ₁m' : Measurable fun x => (θ₁ x : ℝ) := measurable_from_top.comp hθ₁m
    have hθ₁ae : ∀ᵐ x ∂(volume.restrict Rep.carrier), ∀ α : Covector (Euclid (n + 1)) (n + 1),
        (Rep.mult x : ℝ) * Rep.orient x α = (θ₁ x : ℝ) * α (fun i => EuclideanSpace.single i (1 : ℝ)) := by
      filter_upwards [hs1, hss', ae_restrict_mem hVm] with x hx hxs hxV α
      rw [horient x α, hθ₁ x, ite_eq_left hxV, ← hxs]
      rcases hx with h | h <;> rw [h]
      · rw [ite_eq_left one_pos, mul_one, Int.cast_natCast]
      · rw [ite_eq_right (lt_asymm neg_one_lt_zero), mul_neg_one, Int.cast_neg, Int.cast_natCast,
          neg_mul, mul_neg]
    -- `R(ω) = ∫ θ₁ ω(e)`
    have hRθ₁ : ∀ ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1),
        R ω = ∫ x, (θ₁ x : ℝ) * (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) := by
      intro ω
      rw [hRep ω, IMRep.action, hμ, setIntegral_congr_ae hVm (by
          filter_upwards [ae_restrict_iff' hVm |>.1 hθ₁ae] with x hx hxV using hx hxV _)]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      rw [hθ₁ x, ite_eq_right hx, Int.cast_zero, zero_mul]
    -- local integrability of `θ₁`
    have hθ₁loc : LocallyIntegrable (fun x => (θ₁ x : ℝ)) volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      refine ⟨hθ₁m'.aestronglyMeasurable, ?_⟩
      have hnorm : ∀ x, ‖(θ₁ x : ℝ)‖ₑ = Rep.carrier.indicator (fun x => (Rep.mult x : ℝ≥0∞)) x := by
        intro x
        rw [hθ₁ x]
        by_cases hx : x ∈ Rep.carrier
        · rw [ite_eq_left hx, indicator_of_mem hx]
          split_ifs
          · rw [Int.cast_natCast, Real.enorm_natCast]
          · rw [Int.cast_neg, Int.cast_natCast, enorm_neg, Real.enorm_natCast]
        · rw [ite_eq_right hx, indicator_of_notMem hx, Int.cast_zero, enorm_zero]
      rw [HasFiniteIntegral, lintegral_congr hnorm, lintegral_indicator hVm,
        Measure.restrict_restrict hVm, ← hμ]
      exact (Rep.locallyIntegrable_mult K hK (subset_univ K)).lt_top
    -- `θ₁ = 0` a.e. off `spt R`
    have hZ : ∀ᵐ x ∂volume, x ∈ R.zeroRegion → (θ₁ x : ℝ) = 0 := by
      refine R.isOpen_zeroRegion.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hθ₁loc.locallyIntegrableOn _) fun g hg hgc hgZ => ?_
      have h0 := Submission.dtc_vanish_off_support (n + 1) (n + 1) univ R
        ⟨fun x => g x • D, ⟨⟨hg.smul_const D, hgc.smul_right⟩, subset_univ _⟩⟩
        (Set.disjoint_left.2 fun x hx hxR => hxR.2 (hgZ (tsupport_smul_subset_left _ _ hx)))
      rw [hRθ₁] at h0
      rw [← h0]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change g x • (θ₁ x : ℝ) = (θ₁ x : ℝ) * (g x • D) (fun i => EuclideanSpace.single i (1 : ℝ))
      rw [ContinuousAlternatingMap.smul_apply, hDe, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    -- `θ = θ₁ 1_{spt R}`
    have hSm : MeasurableSet R.support := MeasurableSet.univ.diff R.isOpen_zeroRegion.measurableSet
    refine ⟨fun x => if x ∈ R.support then θ₁ x else 0, Measurable.ite hSm hθ₁m measurable_const,
      fun x hx => ite_eq_right hx, ?_, fun ω => ?_⟩
    · refine ((integrable_indicator_iff hSm).2 (hθ₁loc.integrableOn_isCompact hcpt)).congr
        (Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ R.support
      · rw [indicator_of_mem hx, ite_eq_left hx]
      · rw [indicator_of_notMem hx, ite_eq_right hx, Int.cast_zero]
    · rw [hRθ₁ ω]
      refine integral_congr_ae ?_
      filter_upwards [hZ] with x hx
      by_cases hxs : x ∈ R.support
      · rw [ite_eq_left hxs]
      · rw [ite_eq_right hxs, hx (by_contra fun h => hxs ⟨mem_univ x, h⟩), Int.cast_zero]
  have hθc : HasCompactSupport fun x => (θ x : ℝ) :=
    HasCompactSupport.intro hcpt fun x hx => by rw [hθ0 x hx, Int.cast_zero]
  -- Step 3. The currents `[[S]](ω) = ∫_S ω(e)`.
  have hcur : ∀ S : Set (Euclid (n + 1)), ∃ T : GeometricCurrentOn (univ : Set (Euclid (n + 1))) (n + 1),
      ∀ ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1), T ω = ∫ x in S,
        (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    intro S
    have hint : ∀ ω : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1),
        Integrable (fun x => (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))) := fun ω =>
      ((continuous_eval_const _).comp ω.property.1.1.continuous).integrable_of_hasCompactSupport
        (ω.property.1.2.comp_left rfl)
    refine ⟨⟨{ toFun := (fun ω => ∫ x in S, (ω : DifferentialForm (Euclid (n + 1)) (n + 1)) x
                  (fun i => EuclideanSpace.single i (1 : ℝ))),
                map_add' := fun ω₁ ω₂ => integral_add (hint ω₁).integrableOn (hint ω₂).integrableOn,
                map_smul' := fun c ω => integral_const_mul c _ }, fun ωs hωs => ?_⟩, fun ω => rfl⟩
    obtain ⟨K, hK, -, hsupp, -, hconv⟩ := hωs
    have h0 := Metric.tendstoUniformlyOn_iff.1 (hconv 0)
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hC : 0 ≤ volume.real K := measureReal_nonneg
    filter_upwards [h0 (ε / (volume.real K + 1)) (by positivity)] with j hj
    have hbd : ∀ x, ‖(ωs j : DifferentialForm (Euclid (n + 1)) (n + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ))‖ ≤ K.indicator (fun _ => ε / (volume.real K + 1)) x := by
      intro x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        refine (((ωs j : DifferentialForm (Euclid (n + 1)) (n + 1)) x).le_opNorm _).trans ?_
        have h1 := hj x hx
        have hz : iteratedFDeriv ℝ 0 ((0 : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1)) :
            DifferentialForm (Euclid (n + 1)) (n + 1)) x = 0 := by
          ext m; rw [iteratedFDeriv_zero_apply]; rfl
        rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h1
        simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one]
        exact h1.le
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h))]
        simp
    rw [dist_zero_right]
    calc ‖∫ x in S, (ωs j : DifferentialForm (Euclid (n + 1)) (n + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ))‖
        ≤ ∫ x in S, K.indicator (fun _ => ε / (volume.real K + 1)) x :=
          norm_integral_le_of_norm_le ((integrable_indicator_iff hK.measurableSet).2
            (integrableOn_const hK.measure_lt_top.ne)).integrableOn (Eventually.of_forall hbd)
      _ ≤ ∫ x, K.indicator (fun _ => ε / (volume.real K + 1)) x :=
          setIntegral_le_integral ((integrable_indicator_iff hK.measurableSet).2
            (integrableOn_const hK.measure_lt_top.ne)) (Eventually.of_forall fun x =>
              indicator_nonneg (fun _ _ => by positivity) x)
      _ = volume.real K * (ε / (volume.real K + 1)) := by
          rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul]
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  choose X hX using fun j : ℤ => hcur {x | j ≤ θ x}
  -- Step 4. `∫ ∂ᵥh = 0` for `C¹` compactly supported `h` (translation invariance).
  have hS5 : ∀ (h : Euclid (n + 1) → ℝ) (h' : Euclid (n + 1) → Euclid (n + 1) →L[ℝ] ℝ),
      (∀ x, HasFDerivAt h (h' x) x) → Continuous h' → HasCompactSupport h →
        ∀ v, Integrable (fun x => h' x v) ∧ ∫ x, h' x v = 0 := by
    intro h h' hd hc hcs v
    have hcont : Continuous h := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
    have hcs' : HasCompactSupport h' := HasCompactSupport.intro hcs fun x hx =>
      (hd x).unique ((hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hx))
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs'
    have hK : IsCompact (cthickening ‖v‖ (tsupport h')) := hcs'.isCompact.cthickening
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun (t : ℝ) x => h (x + t • v)) (x₀ := 0)
      (bound := (cthickening ‖v‖ (tsupport h')).indicator fun _ => C * ‖v‖)
      (Metric.ball_mem_nhds 0 one_pos)
      (Eventually.of_forall fun t =>
        (hcont.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (by simp only [zero_smul, add_zero]; exact hcont.integrable_of_hasCompactSupport hcs)
      (F' := fun t x => h' (x + t • v) v)
      ((hc.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun a t ht => by
        by_cases hmem : a + t • v ∈ tsupport h'
        · have haK : a ∈ cthickening ‖v‖ (tsupport h') := by
            refine mem_cthickening_of_dist_le a (a + t • v) ‖v‖ (tsupport h') hmem ?_
            rw [dist_self_add_right, norm_smul]
            rw [mem_ball_zero_iff] at ht
            exact mul_le_of_le_one_left (norm_nonneg v) ht.le
          rw [indicator_of_mem haK]
          exact ((h' _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
        · rw [image_eq_zero_of_notMem_tsupport hmem, zero_apply, norm_zero]
          exact indicator_nonneg (fun _ _ => (norm_nonneg _).trans ((h' 0).le_opNorm v |>.trans
            (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))) a)
      ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
      (Eventually.of_forall fun a t _ => by
        have := (hd (a + t • v)).comp_hasDerivAt t (((hasDerivAt_id t).smul_const v).const_add a)
        rwa [one_smul] at this)
    have h1 := key.1
    have h2 := key.2
    rw [show (fun t : ℝ => ∫ x, h (x + t • v)) = fun _ => ∫ x, h x from
      funext fun t => integral_add_right_eq_self h (t • v)] at h2
    have h3 := h2.unique (hasDerivAt_const 0 _)
    simp only [zero_smul, add_zero] at h1 h3
    exact ⟨h1, h3⟩
  -- the vector field `φ_α = Σᵢ (-1)ⁱ α(e_î) eᵢ` of an `n`-covector `α`
  let Φ : Covector (Euclid (n + 1)) n →L[ℝ] Euclid (n + 1) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin (n + 1) => ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => ((-1 : ℝ) ^ (i : ℕ)) • ContinuousAlternatingMap.apply ℝ
        (Euclid (n + 1)) ℝ (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)))
  have hΦi : ∀ (α : Covector (Euclid (n + 1)) n) (i : Fin (n + 1)),
      Φ α i = (-1 : ℝ) ^ (i : ℕ) * α (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) :=
    fun α i => rfl
  have hΦ : ∀ (α : Covector (Euclid (n + 1)) n) (A : Euclid (n + 1) →L[ℝ] ℝ), A (Φ α) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * α (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) *
        A (EuclideanSpace.single i (1 : ℝ)) := by
    intro α A
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr (Φ α)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, hΦi]
  -- integration by parts for forms: `∫ f dη(e) = -∫ f'(φ_η)`
  have hIBPf : ∀ (f : Euclid (n + 1) → ℝ) (f' : Euclid (n + 1) → Euclid (n + 1) →L[ℝ] ℝ),
      (∀ x, HasFDerivAt f (f' x) x) → Continuous f' → ∀ η : Euclid (n + 1) → Covector (Euclid (n + 1)) n,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → HasCompactSupport η →
        Integrable (fun x => f x * extDeriv η x (fun i => EuclideanSpace.single i (1 : ℝ))) ∧
        ∫ x, f x * extDeriv η x (fun i => EuclideanSpace.single i (1 : ℝ)) = -∫ x, f' x (Φ (η x)) := by
    intro f f' hfd hf'c η hηs hηc
    have hf : Continuous f := continuous_iff_continuousAt.2 fun x => (hfd x).continuousAt
    have hηis : ∀ i : Fin (n + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y =>
        η y (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) :=
      fun i => (ContinuousAlternatingMap.apply ℝ (Euclid (n + 1)) ℝ
        (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ))).contDiff.comp hηs
    -- integration by parts in the `i`-th coordinate direction
    have hS := fun i : Fin (n + 1) => hS5
      (fun x => f x * η x
        (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)))
      (fun x => f x • fderiv ℝ (fun y => η y
        (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ))) x +
        η x (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) •
          f' x)
      (fun x => (hfd x).mul ((hηis i).differentiable (by simp) x).hasFDerivAt)
      ((hf.smul ((hηis i).continuous_fderiv (by simp))).add ((hηis i).continuous.smul hf'c))
      (hηc.comp_left (g := fun α : Covector (Euclid (n + 1)) n =>
        α (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ))) rfl).mul_left
      (EuclideanSpace.single i (1 : ℝ))
    -- `f dη(e) + f'(φ_η) = Σᵢ (-1)ⁱ ∂ᵢ(f ηᵢ)`
    have hpt : ∀ x, f x * extDeriv η x
        (fun i => EuclideanSpace.single i (1 : ℝ)) + f' x (Φ (η x)) =
        ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * (f x • fderiv ℝ (fun y => η y
          (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ))) x +
          η x (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) •
            f' x) (EuclideanSpace.single i (1 : ℝ)) := by
      intro x
      rw [extDeriv_apply (hηs.differentiable (by simp) x), hΦ, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zsmul_eq_mul, add_apply, smul_apply,
        smul_apply, smul_eq_mul, smul_eq_mul]
      push_cast
      ring
    have hsum : Integrable fun x => ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * (f x • fderiv ℝ
        (fun y => η y
          (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ))) x +
          η x (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) •
            f' x) (EuclideanSpace.single i (1 : ℝ)) :=
      integrable_finsetSum _ fun i _ => (hS i).1.const_mul _
    have hI2 : Integrable fun x => f' x (Φ (η x)) :=
      (hf'c.clm_apply (Φ.continuous.comp hηs.continuous)).integrable_of_hasCompactSupport
        ((hηc.comp_left (g := fun α => Φ α) Φ.map_zero).mono' fun x hx =>
          subset_tsupport _ fun h0 => hx (show f' x (Φ (η x)) = 0 by
            rw [show Φ (η x) = 0 from h0]; exact (f' x).map_zero))
    have hI1 : Integrable fun x => f x * extDeriv η x
        (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      (hsum.sub hI2).congr (Eventually.of_forall fun x => by
        simp only [Pi.sub_apply]; rw [← hpt x, add_sub_cancel_right])
    refine ⟨hI1, ?_⟩
    have h0 : ∫ x, (f x * extDeriv η x
        (fun i => EuclideanSpace.single i (1 : ℝ)) + f' x (Φ (η x))) = 0 := by
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun i _ => (hS i).1.const_mul _]
      exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, (hS i).2, mul_zero]
    rw [integral_add hI1 hI2] at h0
    linarith
  have hG0 : ∀ η : Euclid (n + 1) → Covector (Euclid (n + 1)) n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → HasCompactSupport η →
      Integrable (fun x => extDeriv η x (fun i => EuclideanSpace.single i (1 : ℝ))) ∧
      ∫ x, extDeriv η x (fun i => EuclideanSpace.single i (1 : ℝ)) = 0 := fun η hηs hηc => by
    have h := hIBPf (fun _ => 1) (fun _ => 0) (fun x => hasFDerivAt_const 1 x) continuous_const η hηs hηc
    simp only [one_mul, zero_apply, integral_zero, neg_zero] at h
    exact h
  -- Step 5. The layers `{θ ≥ j}` sum to `θ`, so `Σⱼ ∂Xⱼ = ∂R` (dominated convergence).
  have hHS : ∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n,
      HasSum (fun j => (X j).boundary η) (R.boundary η) := by
    intro η
    obtain ⟨G, hG⟩ : ∃ G : Euclid (n + 1) → ℝ, G = fun x =>
        extDeriv (η : DifferentialForm (Euclid (n + 1)) n) x (fun i => EuclideanSpace.single i (1 : ℝ)) :=
      ⟨_, rfl⟩
    have hGc : Continuous G := hG ▸ (continuous_eval_const _).comp
      (exteriorDerivative_isTestForm η.property.1).1.continuous
    have hGcs : HasCompactSupport G := hG ▸ (exteriorDerivative_isTestForm η.property.1).2.comp_left
      (g := fun α : Covector (Euclid (n + 1)) (n + 1) => α fun i => EuclideanSpace.single i (1 : ℝ)) rfl
    have hG0 : ∫ x, G x = 0 := hG ▸ (hG0 _ η.property.1.1 η.property.1.2).2
    rw [show (fun j => (X j).boundary η) = fun j => ∫ x in {x | j ≤ θ x}, G x from
      funext fun j => (hX j _).trans (by rw [hG]; rfl), show R.boundary η = ∫ x, (θ x : ℝ) * G x from
        (hRθ _).trans (by rw [hG]; rfl)]
    have hcount : ∀ t : ℤ, HasSum (fun j : ℤ => (if j ≤ t then (1 : ℝ) else 0) -
        (if j ≤ 0 then 1 else 0)) (t : ℝ) := by
      intro t
      induction t using Int.induction_on with
      | zero => simp
      | succ i ih =>
        have h := ih.add (hasSum_ite_eq ((i : ℤ) + 1) (1 : ℝ))
        push_cast at h ⊢
        refine h.congr_fun fun j => ?_
        rcases lt_trichotomy j ((i : ℤ) + 1) with hj | hj | hj
        · rw [ite_eq_right (ne_of_lt hj), ite_eq_left (show j ≤ (i : ℤ) by omega),
            ite_eq_left hj.le, add_zero]
        · rw [hj, ite_eq_left rfl, ite_eq_right (show ¬ (i : ℤ) + 1 ≤ i by omega),
            ite_eq_left le_rfl]
          ring
        · rw [ite_eq_right (ne_of_gt hj), ite_eq_right (show ¬ j ≤ (i : ℤ) by omega),
            ite_eq_right (show ¬ j ≤ (i : ℤ) + 1 by omega), add_zero]
      | pred i ih =>
        have h := ih.sub (hasSum_ite_eq (-(i : ℤ)) (1 : ℝ))
        push_cast at h ⊢
        refine h.congr_fun fun j => ?_
        rcases lt_trichotomy j (-(i : ℤ)) with hj | hj | hj
        · rw [ite_eq_right (ne_of_lt hj), ite_eq_left (show j ≤ -(i : ℤ) by omega),
            ite_eq_left (show j ≤ -(i : ℤ) - 1 by omega), sub_zero]
        · rw [hj, ite_eq_left rfl, ite_eq_right (show ¬ -(i : ℤ) ≤ -(i : ℤ) - 1 by omega),
            ite_eq_left le_rfl]
          ring
        · rw [ite_eq_right (ne_of_gt hj), ite_eq_right (show ¬ j ≤ -(i : ℤ) by omega),
            ite_eq_right (show ¬ j ≤ -(i : ℤ) - 1 by omega), sub_zero]
    have hcountabs : ∀ t : ℤ, HasSum (fun j : ℤ => |(if j ≤ t then (1 : ℝ) else 0) -
        (if j ≤ 0 then 1 else 0)|) |(t : ℝ)| := by
      intro t
      rcases le_or_gt 0 t with ht | ht
      · rw [abs_of_nonneg (by exact_mod_cast ht : (0 : ℝ) ≤ t)]
        refine (hcount t).congr_fun fun j => abs_of_nonneg ?_
        by_cases h1 : j ≤ t
        · rw [ite_eq_left h1, sub_nonneg]; split_ifs <;> norm_num
        · rw [ite_eq_right h1, ite_eq_right (show ¬ j ≤ 0 by omega), sub_zero]
      · rw [abs_of_neg (by exact_mod_cast ht : (t : ℝ) < 0)]
        refine (hcount t).neg.congr_fun fun j => abs_of_nonpos ?_
        by_cases h1 : j ≤ 0
        · rw [ite_eq_left h1, sub_nonpos]; split_ifs <;> norm_num
        · rw [ite_eq_right h1, ite_eq_right (show ¬ j ≤ t by omega), sub_zero]
    have hθm' : ∀ j : ℤ, Measurable fun x => (if j ≤ θ x then (1 : ℝ) else 0) - (if j ≤ 0 then 1 else 0) :=
      fun j => (measurable_from_top (f := fun t : ℤ => (if j ≤ t then (1 : ℝ) else 0) -
        (if j ≤ 0 then 1 else 0))).comp hθm
    have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGcs
    obtain ⟨C, hC⟩ := hGc.bounded_above_of_compact_support hGcs
    have key := hasSum_integral_of_dominated_convergence (μ := volume)
      (F := fun (j : ℤ) x => ((if j ≤ θ x then (1 : ℝ) else 0) - (if j ≤ 0 then 1 else 0)) * G x)
      (f := fun x => (θ x : ℝ) * G x)
      (fun j x => |(if j ≤ θ x then (1 : ℝ) else 0) - (if j ≤ 0 then 1 else 0)| * |G x|)
      (fun j => ((hθm' j).mul hGc.measurable).aestronglyMeasurable)
      (fun j => Eventually.of_forall fun x => by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs])
      (Eventually.of_forall fun x => ((hcountabs (θ x)).mul_right _).summable)
      (by
        simp_rw [tsum_mul_right, (hcountabs _).tsum_eq]
        exact hθi.abs.mul_bdd hGc.abs.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hC x))
      (Eventually.of_forall fun x => (hcount (θ x)).mul_right (G x))
    refine key.congr_fun fun j => ?_
    have h1 : (fun x => ((if j ≤ θ x then (1 : ℝ) else 0) - (if j ≤ 0 then 1 else 0)) * G x) =
        fun x => {x | j ≤ θ x}.indicator G x - (if j ≤ 0 then (1 : ℝ) else 0) * G x := by
      funext x
      rw [sub_mul, indicator_apply, ite_mul, one_mul, zero_mul]
      rfl
    rw [h1, integral_sub ((integrable_indicator_iff (measurableSet_le measurable_const hθm)).2
        hGi.integrableOn) (hGi.const_mul _), integral_const_mul, hG0, mul_zero, sub_zero,
      integral_indicator (measurableSet_le measurable_const hθm)]
  -- Step 6. The Hodge star `⋆c = D(c, ·)`: `(⋆c)(e_î) = (-1)ⁱ cᵢ`, `|⋆c| = |c|`,
  -- `d(⋆g)(e) = div g`; and `|α|² = Σᵢ α(e_î)²` for `n`-covectors `α`.
  have hstarval : ∀ (c : Euclid (n + 1)) (i : Fin (n + 1)),
      D.curryLeft c (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)) =
        (-1) ^ (i : ℕ) * c i := by
    intro c i
    rw [ContinuousAlternatingMap.curryLeft_apply_apply, hD, Module.Basis.det_apply,
      Matrix.det_succ_column_zero, Finset.sum_eq_single i]
    · have h1 : ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.toMatrix
          (Matrix.vecCons c (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)))).submatrix
            i.succAbove Fin.succ = 1 := by
        ext r q
        simp [Module.Basis.toMatrix_apply, Fin.removeNth, Matrix.one_apply, PiLp.single_apply]
      rw [h1, Matrix.det_one, mul_one]
      simp [Module.Basis.toMatrix_apply]
    · intro p _ hpi
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hpi)
      rw [Matrix.det_eq_zero_of_row_eq_zero r, mul_zero]
      intro q
      simp [Module.Basis.toMatrix_apply, Fin.removeNth, hr]
    · simp
  have hcovnorm : ∀ α : Covector (Euclid (n + 1)) n, covectorEuclideanNorm α = Real.sqrt
      (∑ p : Fin (n + 1), (α (Fin.removeNth p fun i => EuclideanSpace.single i (1 : ℝ))) ^ 2) := by
    have hclass : ∀ F : (Fin n → Fin (n + 1)) → ℝ,
        (∑ I : Fin n → Fin (n + 1), if StrictMono I then F I else 0) =
          ∑ p : Fin (n + 1), F p.succAbove := by
      intro F
      rw [← Finset.sum_filter]
      have himage : Finset.univ.filter (fun I : Fin n → Fin (n + 1) => StrictMono I) =
          Finset.univ.image (fun p : Fin (n + 1) => (p.succAbove : Fin n → Fin (n + 1))) := by
        ext I
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        refine ⟨fun hI => ?_, ?_⟩
        · obtain ⟨p, hp⟩ : ∃ p, ∀ x, I x ≠ p := by
            by_contra h
            push Not at h
            have := Fintype.card_le_of_surjective I h
            simp at this
          have hcard : (Finset.univ.erase p).card = n := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin,
              Nat.add_sub_cancel]
          refine ⟨p, ?_⟩
          rw [Finset.orderEmbOfFin_unique hcard (f := p.succAbove)
              (fun x => Finset.mem_erase.2 ⟨Fin.succAbove_ne p x, Finset.mem_univ _⟩)
              (Fin.strictMono_succAbove p),
            Finset.orderEmbOfFin_unique hcard (f := I)
              (fun x => Finset.mem_erase.2 ⟨hp x, Finset.mem_univ _⟩) hI]
        · rintro ⟨p, rfl⟩
          exact Fin.strictMono_succAbove p
      rw [himage, Finset.sum_image fun p _ q _ h => Fin.succAbove_left_injective h]
    intro α
    rw [covectorEuclideanNorm, hclass fun I =>
      (α fun i => EuclideanSpace.basisFun (Fin (n + 1)) ℝ (I i)) ^ 2]
    simp only [EuclideanSpace.basisFun_apply]
    rfl
  have hstarnorm : ∀ c : Euclid (n + 1), covectorEuclideanNorm (D.curryLeft c) = ‖c‖ := by
    intro c
    rw [hcovnorm, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hstarval, mul_pow, ← pow_mul, mul_comm (p : ℕ) 2, pow_mul, neg_one_sq, one_pow, one_mul,
      Real.norm_eq_abs, sq_abs]
  -- `div g = trace Dg = Σᵢ ∂ᵢgⁱ`
  have htrace : ∀ A : Euclid (n + 1) →L[ℝ] Euclid (n + 1),
      LinearMap.trace ℝ (Euclid (n + 1)) (A : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) =
        ∑ i, (A (EuclideanSpace.single i (1 : ℝ))) i := by
    intro A
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis,
      Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    rfl
  -- `d(⋆g)(e) = div g`
  -- `d(⋆g)(e) = div g`
  have hdstar : ∀ (g : Euclid (n + 1) → Euclid (n + 1)), Differentiable ℝ g → ∀ x,
      extDeriv (fun y => D.curryLeft (g y)) x (fun i => EuclideanSpace.single i (1 : ℝ)) =
        LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ g x : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) := by
    have hsign : ∀ (k : ℕ) (a : ℝ), (-1 : ℤ) ^ k • ((-1 : ℝ) ^ k * a) = a := fun k a => by
      rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← mul_assoc, ← mul_pow, neg_one_mul,
        neg_neg, one_pow, one_mul]
    intro g hg x
    rw [extDeriv_apply (show DifferentiableAt ℝ (fun y => D.curryLeft (g y)) x from
      (D.curryLeft).differentiableAt.comp x (hg x)), htrace]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hd : HasFDerivAt (fun y => D.curryLeft (g y) (Fin.removeNth i fun i => EuclideanSpace.single i (1 : ℝ)))
        ((-1 : ℝ) ^ (i : ℕ) • ((EuclideanSpace.proj i : Euclid (n + 1) →L[ℝ] ℝ).comp (fderiv ℝ g x))) x := by
      have h := ((EuclideanSpace.proj i : Euclid (n + 1) →L[ℝ] ℝ).hasFDerivAt.comp x
        (hg x).hasFDerivAt).const_mul ((-1 : ℝ) ^ (i : ℕ))
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun y => hstarval (g y) i)
    rw [hd.fderiv]
    exact hsign i _
  -- Step 7. Mollifiers `ρₖ` (normalized bumps) with `ρₖ * θ → θ` a.e. (Lebesgue differentiation).
  obtain ⟨ρ, hρs, hρc, hρ0, hρe, hρ1, hρae⟩ : ∃ ρ : ℕ → Euclid (n + 1) → ℝ,
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ k)) ∧ (∀ k, HasCompactSupport (ρ k)) ∧
      (∀ k x, 0 ≤ ρ k x) ∧ (∀ k x, ρ k (-x) = ρ k x) ∧ (∀ k, ∫ x, ρ k x = 1) ∧
      ∀ᵐ x₀ ∂volume, Tendsto (fun k => convolution (ρ k) (fun x => (θ x : ℝ))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀) atTop (𝓝 (θ x₀ : ℝ)) := by
    let φ : ℕ → ContDiffBump (0 : Euclid (n + 1)) := fun k =>
      ⟨1 / ((k : ℝ) + 1), 2 * (1 / ((k : ℝ) + 1)), by positivity,
        lt_two_mul_self (by positivity)⟩
    have hBpos : ∀ k : ℕ, 0 < volume.real (closedBall (0 : Euclid (n + 1)) (1 / ((k : ℝ) + 1))) :=
      fun k => ENNReal.toReal_pos (measure_closedBall_pos _ _ (by positivity)).ne'
        measure_closedBall_lt_top.ne
    have hI : ∀ k : ℕ, volume.real (closedBall (0 : Euclid (n + 1)) (1 / ((k : ℝ) + 1))) ≤ ∫ x, φ k x := by
      intro k
      calc volume.real (closedBall (0 : Euclid (n + 1)) (1 / ((k : ℝ) + 1)))
          = ∫ x in closedBall (0 : Euclid (n + 1)) (1 / ((k : ℝ) + 1)), (1 : ℝ) := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
        _ = ∫ x in closedBall (0 : Euclid (n + 1)) (1 / ((k : ℝ) + 1)), φ k x :=
            setIntegral_congr_fun measurableSet_closedBall fun x hx =>
              ((φ k).one_of_mem_closedBall hx).symm
        _ ≤ ∫ x, φ k x := setIntegral_le_integral
            ((φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport)
            (Eventually.of_forall fun x => (φ k).nonneg)
    have hIpos : ∀ k : ℕ, 0 < ∫ x, φ k x := fun k => (hBpos k).trans_le (hI k)
    refine ⟨fun k x => (∫ y, φ k y)⁻¹ * φ k x, fun k => contDiff_const.mul (φ k).contDiff,
      fun k => (φ k).hasCompactSupport.comp_left (mul_zero _),
      fun k x => mul_nonneg (inv_nonneg.2 (hIpos k).le) (φ k).nonneg,
      fun k x => by dsimp only; rw [(φ k).neg], fun k => by rw [integral_const_mul, inv_mul_cancel₀ (hIpos k).ne'], ?_⟩
    filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Euclid (n + 1)))).ae_tendsto_average_norm_sub
      hθi.locallyIntegrable] with x₀ h₀
    simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    have hr : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    refine tendsto_integral_smul_of_tendsto_average_norm_sub (2 ^ (n + 1))
      ((h₀.comp (Besicovitch.tendsto_filterAt volume x₀)).comp hr)
      (Eventually.of_forall fun k => hθi.integrableOn) ?_ ?_ ?_
    · refine tendsto_const_nhds.congr fun k => ?_
      rw [integral_sub_left_eq_self (fun x => (∫ y, φ k y)⁻¹ * φ k x) volume x₀, integral_const_mul,
        inv_mul_cancel₀ (hIpos k).ne']
    · refine Eventually.of_forall fun k y hy => ?_
      have h1 : x₀ - y ∈ ball (0 : Euclid (n + 1)) (φ k).rOut :=
        (φ k).support_eq ▸ (right_ne_zero_of_mul hy : φ k (x₀ - y) ≠ 0)
      rw [mem_ball_zero_iff] at h1
      dsimp only
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h1.le
    · refine Eventually.of_forall fun k y => ?_
      have h2 : volume.real (closedBall x₀ (2 * (1 / ((k : ℝ) + 1)))) =
          2 ^ (n + 1) * volume.real (closedBall (0 : Euclid (n + 1)) (1 / ((k : ℝ) + 1))) := by
        rw [measureReal_def, Measure.addHaar_closedBall_mul_of_pos volume x₀ two_pos,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace,
          Fintype.card_fin, ← measureReal_def]
      dsimp only
      rw [h2, div_mul_cancel_left₀ (by positivity : (2 : ℝ) ^ (n + 1) ≠ 0), abs_of_nonneg
        (mul_nonneg (inv_nonneg.2 (hIpos k).le) (φ k).nonneg)]
      calc (∫ y, φ k y)⁻¹ * φ k (x₀ - y) ≤ (∫ y, φ k y)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ k).le_one (inv_nonneg.2 (hIpos k).le)
        _ ≤ _ := by rw [mul_one]; exact inv_anti₀ (hBpos k) (hI k)
  -- Step 8. Smoothed truncations `Ψ` (Simon's `ψ`): `C¹`, `|Ψ'| ≤ 1/(1-4δ)`, `Ψ(m) = #{j ∈ [a,b] : j ≤ m}`.
  have hΨ : ∀ (δ : ℝ), 0 < δ → δ < 1 / 8 → ∀ (a b : ℤ), ∃ (Ψ Ψ' : ℝ → ℝ),
      (∀ t, HasDerivAt Ψ (Ψ' t) t) ∧ Continuous Ψ' ∧ (∀ t, |Ψ' t| ≤ 1) ∧
      (∀ m : ℤ, Ψ m = (1 - 4 * δ) * ∑ j ∈ Finset.Icc a b, if j ≤ m then (1 : ℝ) else 0) ∧
      ∀ t, |Ψ t| ≤ ((Finset.Icc a b).card : ℝ) := by
    intro δ hδ hδ8 a b
    let β : ContDiffBump (-1 / 2 : ℝ) := ⟨1 / 2 - 2 * δ, 1 / 2 - δ, by linarith, by linarith⟩
    have hβc : Continuous β := β.continuous
    have hβ0 : ∀ s : ℝ, (s ≤ -1 + δ ∨ -δ ≤ s) → β s = 0 := fun s hs =>
      β.zero_of_le_dist (show 1 / 2 - δ ≤ dist s (-1 / 2) by
        rw [Real.dist_eq, le_abs]
        rcases hs with hs | hs
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith))
    have hint : ∀ u v : ℝ, IntervalIntegrable β volume u v := fun u v => hβc.intervalIntegrable u v
    obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ t, F t = ∫ s in (-1 : ℝ)..t, β s := ⟨_, fun t => rfl⟩
    have hFd : ∀ t, HasDerivAt F (β t) t := fun t =>
      (funext hF : F = _) ▸ (hβc.integral_hasStrictDerivAt (-1) t).hasDerivAt
    have hF0 : ∀ t ≤ (-1 : ℝ), F t = 0 := by
      intro t ht
      rw [hF, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => hβ0 s (Or.inl ?_),
        intervalIntegral.integral_zero]
      rw [uIcc_of_ge ht] at hs
      linarith [hs.2]
    have hFI : ∀ t ≥ (0 : ℝ), F t = F 0 := by
      intro t ht
      rw [hF, hF, ← intervalIntegral.integral_add_adjacent_intervals (hint (-1) 0) (hint 0 t),
        intervalIntegral.integral_congr (a := 0) (b := t) (g := fun _ => (0 : ℝ))
          fun s hs => hβ0 s (Or.inr ?_), intervalIntegral.integral_zero, add_zero]
      rw [uIcc_of_le ht] at hs
      linarith [hs.1]
    have hI : 1 - 4 * δ ≤ F 0 := by
      have h1 := intervalIntegral.integral_nonneg (μ := volume) (by linarith : (-1 : ℝ) ≤ -1 + 2 * δ)
        fun s _ => β.nonneg (x := s)
      have h2 := intervalIntegral.integral_nonneg (μ := volume) (by linarith : (-2 * δ : ℝ) ≤ 0)
        fun s _ => β.nonneg (x := s)
      have h3 : ∫ s in (-1 + 2 * δ)..(-2 * δ), β s = ∫ s in (-1 + 2 * δ)..(-2 * δ), (1 : ℝ) :=
        intervalIntegral.integral_congr fun s hs => β.one_of_mem_closedBall (by
          rw [uIcc_of_le (by linarith)] at hs
          show dist s (-1 / 2) ≤ 1 / 2 - 2 * δ
          rw [Real.dist_eq, abs_le]
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h3
      rw [hF, ← intervalIntegral.integral_add_adjacent_intervals (hint (-1) (-1 + 2 * δ)) (hint _ 0),
        ← intervalIntegral.integral_add_adjacent_intervals (hint (-1 + 2 * δ) (-2 * δ)) (hint _ 0), h3]
      linarith
    have hIpos : 0 < F 0 := by linarith
    have hFle : ∀ t, |F t| ≤ F 0 := by
      intro t
      rcases le_or_gt t (-1) with ht | ht
      · rw [hF0 t ht, abs_zero]; exact hIpos.le
      rcases le_or_gt 0 t with ht' | ht'
      · rw [hFI t ht', abs_of_pos hIpos]
      have h1 : 0 ≤ F t := (hF t).symm ▸ intervalIntegral.integral_nonneg (μ := volume) ht.le
        fun s _ => β.nonneg (x := s)
      have h2 : 0 ≤ ∫ s in t..0, β s :=
        intervalIntegral.integral_nonneg (μ := volume) ht'.le fun s _ => β.nonneg (x := s)
      have h3 : F t + ∫ s in t..0, β s = F 0 := by
        rw [hF, hF]; exact intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
      rw [abs_of_nonneg h1]
      linarith
    have hk0 : 0 ≤ (1 - 4 * δ) / F 0 := div_nonneg (by linarith) hIpos.le
    have hk1 : (1 - 4 * δ) / F 0 ≤ 1 := (div_le_one hIpos).2 hI
    refine ⟨fun t => ∑ j ∈ Finset.Icc a b, F (t - j) * ((1 - 4 * δ) / F 0),
      fun t => ∑ j ∈ Finset.Icc a b, β (t - j) * ((1 - 4 * δ) / F 0), fun t => ?_, ?_, fun t => ?_,
      fun m => ?_, fun t => ?_⟩
    · refine HasDerivAt.fun_sum fun j _ => ?_
      have := ((hFd (t - j)).comp t ((hasDerivAt_id t).sub_const (j : ℝ))).mul_const ((1 - 4 * δ) / F 0)
      rwa [mul_one] at this
    · exact continuous_finsetSum _ fun j _ => (hβc.comp (continuous_sub_right _)).mul continuous_const
    · dsimp only
      have hsum : ∑ j ∈ Finset.Icc a b, β (t - j) ≤ 1 := by
        have hz : ∀ j ∈ Finset.Icc a b, β (t - j) = if ⌈t⌉ = j then β (t - j) else 0 := by
          intro j _
          split_ifs with hj
          · rfl
          · refine hβ0 _ (or_iff_not_imp_left.2 fun h1 => ?_)
            by_contra h2
            exact hj (Int.ceil_eq_iff.2 ⟨by linarith [not_le.1 h1], by linarith [not_le.1 h2]⟩)
        rw [Finset.sum_congr rfl hz, Finset.sum_ite_eq]
        split_ifs
        · exact β.le_one
        · exact zero_le_one
      rw [← Finset.sum_mul, abs_mul, abs_of_nonneg hk0,
        abs_of_nonneg (Finset.sum_nonneg fun j _ => β.nonneg)]
      exact (mul_le_mul hsum hk1 hk0 zero_le_one).trans_eq (one_mul 1)
    · dsimp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rw [hFI _ (sub_nonneg.2 (by exact_mod_cast hj)), mul_div_cancel₀ _ hIpos.ne', mul_one]
      · rw [hF0 _ (by have : (m : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : m + 1 ≤ j)
                      linarith), zero_mul, mul_zero]
    · dsimp only
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_one (Finset.Icc a b).card, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg hk0]
        calc |F (t - j)| * ((1 - 4 * δ) / F 0) ≤ F 0 * ((1 - 4 * δ) / F 0) :=
              mul_le_mul_of_nonneg_right (hFle _) hk0
          _ ≤ 1 := by rw [mul_div_cancel₀ _ hIpos.ne']; linarith
  -- Step 9. Mass bounds: `M(Σ_{j=a}^b ∂Xⱼ) ≤ M(∂R)` (Simon 3.14 (5)–(7)).
  have hmassY : ∀ (a b : ℤ) (Y : GeometricCurrentOn (univ : Set (Euclid (n + 1))) n),
      (∀ η : TestFormOn (univ : Set (Euclid (n + 1))) n,
        Y η = ∑ j ∈ Finset.Icc a b, (X j).boundary η) → Y.mass ≤ R.boundary.mass := by
    intro a b Y hY
    rcases eq_or_ne R.boundary.mass ⊤ with htop | hfin
    · rw [htop]; exact le_top
    obtain ⟨L, hL0, hLmass⟩ : ∃ L : ℝ, 0 ≤ L ∧ R.boundary.mass = ENNReal.ofReal L :=
      ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hfin).symm⟩
    -- smooth fields `g` with `|g| ≤ 1`: `∫ θ div g ≤ M(∂R)`, testing `∂R` with `⋆g`
    have hfield : ∀ g : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
        HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → ∫ z, (θ z : ℝ) * LinearMap.trace ℝ (Euclid (n + 1))
          (fderiv ℝ g z : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) ≤ L := by
      intro g hg hgc hg1
      let η : TestFormOn (univ : Set (Euclid (n + 1))) n :=
        ⟨fun y => D.curryLeft (g y), ⟨⟨(D.curryLeft).contDiff.comp hg,
          hgc.comp_left (g := fun c => D.curryLeft c) (D.curryLeft).map_zero⟩,
          subset_univ _⟩⟩
      have h1 := R.boundary.le_massOn (W := univ) (omega := η)
        ⟨subset_univ _, fun x => (hstarnorm (g x)).le.trans (hg1 x)⟩
      rw [GeometricCurrentOn.boundary_apply, hRθ] at h1
      have h2 : ∀ x, ((exteriorDerivativeTestOn univ n η : TestFormOn (univ : Set (Euclid (n + 1))) (n + 1)) :
          DifferentialForm (Euclid (n + 1)) (n + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) =
            LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ g x : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) :=
        hdstar g (hg.differentiable (by simp))
      simp only [h2] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hL0).1 (h1.trans_eq hLmass)
    -- the smoothed truncations of the mollified density, tested against admissible `η`
    have hperk : ∀ (ρ : Euclid (n + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
        HasCompactSupport ρ → (∀ x, 0 ≤ ρ x) → (∀ x, ρ (-x) = ρ x) → ∫ x, ρ x = 1 →
        ∀ (Ψ Ψ' : ℝ → ℝ), (∀ t, HasDerivAt Ψ (Ψ' t) t) → Continuous Ψ' →
        (∀ t, |Ψ' t| ≤ 1) → ∀ η : Euclid (n + 1) → Covector (Euclid (n + 1)) n,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → HasCompactSupport η →
        (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∀ G : Euclid (n + 1) → ℝ,
        G = (fun x => extDeriv η x (fun i => EuclideanSpace.single i (1 : ℝ))) →
        ∫ x, Ψ (convolution ρ (fun x => (θ x : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * G x ≤
          L := by
      intro ρ hρs hρc hρ0 hρe hρ1 Ψ Ψ' hΨd hΨ'c hΨ'b η hηs hηc hη G hG
      subst hG
      -- the mollified density `w = ρ * θ` is `C¹`
      have hw1 : ContDiff ℝ 1 (convolution ρ (fun x => (θ x : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
        hρc.contDiff_convolution_left _ (hρs.of_le (by norm_cast)) hθi.locallyIntegrable
      obtain ⟨w, hw⟩ : ∃ w, w = convolution ρ (fun x => (θ x : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        ⟨_, rfl⟩
      rw [← hw] at hw1 ⊢
      have hwd : Differentiable ℝ w := hw1.differentiable one_ne_zero
      have hwdc : Continuous (fderiv ℝ w) := hw1.continuous_fderiv one_ne_zero
      -- integration by parts: `∫ Ψ(w) dη(e) = -∫ Ψ'(w) Dw(φ_η)`
      rw [(hIBPf (fun x => Ψ (w x)) (fun x => Ψ' (w x) • fderiv ℝ w x)
        (fun x => (hΨd (w x)).comp_hasFDerivAt x (hwd x).hasFDerivAt)
        ((hΨ'c.comp hw1.continuous).smul hwdc) η hηs hηc).2]
      -- the field `s = c⁻¹ Ψ'(w) φ_η`, with `|s| ≤ 1`
      have hφn : ∀ x, ‖Φ (η x)‖ ≤ 1 := by
        intro x
        refine le_of_eq_of_le ?_ (hη x)
        rw [EuclideanSpace.norm_eq, hcovnorm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hΦi, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, mul_comm (i : ℕ) 2, pow_mul, neg_one_sq,
          one_pow, one_mul]
      obtain ⟨s, hs⟩ : ∃ s : Euclid (n + 1) → Euclid (n + 1), s = fun x => Ψ' (w x) • Φ (η x) :=
        ⟨_, rfl⟩
      have hsn : ∀ x, ‖s x‖ ≤ 1 := fun x => by
        rw [hs, norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul (hΨ'b _) (hφn x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      have hsc : Continuous s := hs ▸ (hΨ'c.comp hw1.continuous).smul (Φ.continuous.comp hηs.continuous)
      have hscs : HasCompactSupport s := hs ▸
        (hηc.comp_left (g := fun α => Φ α) Φ.map_zero).smul_left (f := fun x => Ψ' (w x))
      have hsi : Integrable s := hsc.integrable_of_hasCompactSupport hscs
      have hsx : ∀ x, (Ψ' (w x) • fderiv ℝ w x) (Φ (η x)) = fderiv ℝ w x (s x) := fun x => by
        rw [hs]; exact ((fderiv ℝ w x).map_smul (Ψ' (w x)) (Φ (η x))).symm
      rw [integral_congr_ae (Eventually.of_forall hsx), hw,
        Submission.codim1_rdo_dg_sp_mollifier_adjoint (n + 1) ρ (fun x => (θ x : ℝ)) s
          (hρs.of_le (by norm_cast)) hρc hρe hθi hsi, neg_neg]
      -- the smooth field `ρ * s` is admissible
      refine hfield _ (hρc.contDiff_convolution_left _ hρs hsi.locallyIntegrable)
        (hρc.convolution _ hscs) fun z => ?_
      rw [convolution_def]
      refine (norm_integral_le_of_norm_le (hρs.continuous.integrable_of_hasCompactSupport hρc)
        (Eventually.of_forall fun t => ?_)).trans hρ1.le
      rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
      exact mul_le_of_le_one_right (hρ0 t) (hsn _)
    rw [hLmass]
    refine sSup_le ?_
    rintro _ ⟨η, hη, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    -- the admissible form as a plain function `ω`; `G = dω(e)`, `T = Σ_{j=a}^b 1_{θ ≥ j}`
    obtain ⟨ω, hω⟩ : ∃ ω : Euclid (n + 1) → Covector (Euclid (n + 1)) n,
        ω = (η : DifferentialForm (Euclid (n + 1)) n) := ⟨_, rfl⟩
    have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := hω ▸ η.property.1.1
    have hωc : HasCompactSupport ω := hω ▸ η.property.1.2
    obtain ⟨G, hG⟩ : ∃ G : Euclid (n + 1) → ℝ,
        G = fun x => extDeriv ω x (fun i => EuclideanSpace.single i (1 : ℝ)) := ⟨_, rfl⟩
    have hGi : Integrable G := hG ▸ (hG0 ω hωs hωc).1
    have hGcont : Continuous G := hG ▸ (continuous_eval_const _).comp
      (exteriorDerivative_isTestForm ⟨hωs, hωc⟩).1.continuous
    obtain ⟨T, hT⟩ : ∃ T : Euclid (n + 1) → ℝ,
        T = fun x => ∑ j ∈ Finset.Icc a b, if j ≤ θ x then (1 : ℝ) else 0 := ⟨_, rfl⟩
    -- `Σ_{j=a}^b ∂Xⱼ(η) = ∫ T dη(e)`
    have hsumT : ∑ j ∈ Finset.Icc a b, (X j).boundary η = ∫ x, T x * G x := by
      calc ∑ j ∈ Finset.Icc a b, (X j).boundary η
          = ∑ j ∈ Finset.Icc a b, ∫ x, {x | j ≤ θ x}.indicator G x :=
            Finset.sum_congr rfl fun j _ => (hX j _).trans (by
              rw [hG, hω, integral_indicator (measurableSet_le measurable_const hθm)]; rfl)
        _ = ∫ x, ∑ j ∈ Finset.Icc a b, {x | j ≤ θ x}.indicator G x :=
            (integral_finsetSum _ fun j _ =>
              hGi.indicator (measurableSet_le measurable_const hθm)).symm
        _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
            simp only [hT, Finset.sum_mul, indicator_apply, mem_ofPred_eq, ite_mul, one_mul, zero_mul])
    rw [hY η, hsumT]
    -- for every `δ ∈ (0, 1/8)` the bound holds up to the factor `1 - 4δ`
    have hδ : ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → (1 - 4 * δ) * ∫ x, T x * G x ≤ L := by
      intro δ hδ0 hδ8
      obtain ⟨Ψ, Ψ', hΨd, hΨ'c, hΨ'b, hΨint, hΨbd⟩ := hΨ δ hδ0 hδ8 a b
      have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun t => (hΨd t).continuousAt
      have hlim : Tendsto (fun k => ∫ x, Ψ (convolution (ρ k) (fun x => (θ x : ℝ))
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x) * G x) atTop (𝓝 (∫ x, Ψ (θ x) * G x)) := by
        refine tendsto_integral_of_dominated_convergence
          (fun x => ((Finset.Icc a b).card : ℝ) * |G x|) (fun k => ?_) (hGi.abs.const_mul _)
          (fun k => Eventually.of_forall fun x => ?_) ?_
        · exact ((hΨc.comp ((hρc k).continuous_convolution_left _ (hρs k).continuous
            hθi.locallyIntegrable)).mul hGcont).aestronglyMeasurable
        · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hΨbd _) (abs_nonneg _)
        · filter_upwards [hρae] with x hx
          exact ((hΨc.tendsto _).comp hx).mul_const _
      have hrw : (1 - 4 * δ) * ∫ x, T x * G x = ∫ x, Ψ (θ x) * G x := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun x => by
          rw [hT]; dsimp only; rw [hΨint (θ x), mul_assoc])
      rw [hrw]
      exact le_of_tendsto' hlim fun k => hperk (ρ k) (hρs k) (hρc k) (hρ0 k) (hρe k) (hρ1 k) Ψ Ψ'
        hΨd hΨ'c hΨ'b ω hωs hωc (hω ▸ hη.2) G hG
    -- letting `δ → 0`
    refine le_of_tendsto (x := 𝓝[>] (0 : ℝ)) ?_
      (eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 8)) fun δ hδ' => hδ δ hδ'.1 hδ'.2)
    have h4 : Tendsto (fun δ : ℝ => (1 - 4 * δ) * ∫ x, T x * G x) (𝓝 0)
        (𝓝 ((1 - 4 * 0) * ∫ x, T x * G x)) :=
      ((continuous_const.sub (continuous_const.mul continuous_id)).mul continuous_const).tendsto 0
    rw [mul_zero, sub_zero, one_mul] at h4
    exact h4.mono_left nhdsWithin_le_nhds
  refine ⟨fun j => {x | j ≤ θ x}, X, fun j => measurableSet_le measurable_const hθm,
    fun j x hx => le_trans (le_of_lt (lt_add_one j)) hx, hX, hHS,
    fun j => hmassY j j _ fun η => by rw [Finset.Icc_self, Finset.sum_singleton],
    fun N Y hY => hmassY _ _ Y hY⟩

end Submission

end GMT.Ch07
