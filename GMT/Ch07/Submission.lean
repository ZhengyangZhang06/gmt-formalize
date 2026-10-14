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

/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Total variation of a smooth function by duality with smooth test fields** (parent step 5:
`∫_W |Dw|` is bounded by the supremum of `∫ Dw · g` over `C^∞` fields `g` with compact support in
`W` and `|g| ≤ 1`).  Let `F = (Dw(·) eᵢ)ᵢ` be the gradient field of `w`, so `⟪F, h⟫ = Dw · h` and
`|F| = ‖Dw‖`; `F` is `C^∞`, and bounded by `M` on the compact set `closure W`.  Given `ε > 0`, the
smooth cut-off `rsd_mw_tfa_smooth_cutoff` (for `vol⌞W`) gives `χ ∈ C_c^∞(W)` with `0 ≤ χ ≤ 1` and
`vol (W ∩ {χ ≠ 1}) < ε`.  The field `g = χ F / √(|F|² + ε²)` is admissible, and
`Dw · g = ψ := χ |F|² / √(|F|² + ε²)`, which vanishes off `W`, so `∫_W ψ ≤ V`.  On `W`,
`|F| ≤ ψ + |M| 1_{χ ≠ 1} + ε` (if `χ = 1`, use `a ≤ a² / √(a² + ε²) + ε`; otherwise `|F| ≤ M`).
Integrating, `∫_W |F| ≤ V + (|M| + vol W) ε`, and `ε → 0` gives the claim. -/
theorem Submission.dor_lmb_fcd_cp_smooth_duality : ∀ (P : ℕ) (w : Euclid P → ℝ) (W : Set (Euclid P)) (V : ℝ), IsOpen W → Bornology.IsBounded W → ContDiff ℝ (⊤ : ℕ∞) w → (∀ g : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ W → (∀ y, ‖g y‖ ≤ 1) → ∫ y, fderiv ℝ w y (g y) ≤ V) → ∫ y in W, ‖fderiv ℝ w y‖ ≤ V := by
  intro P w W V hWo hWb hw hV
  -- Step 1: the gradient field `F y = (Dw(y) eᵢ)ᵢ`, with `⟪F y, h⟫ = Dw(y) h` and `‖F y‖ = ‖Dw(y)‖`
  set F : Euclid P → Euclid P :=
    fun y => WithLp.toLp 2 (fun i => fderiv ℝ w y (EuclideanSpace.single i 1))
  have hinner : ∀ y h, inner ℝ (F y) h = fderiv ℝ w y h := by
    intro y h
    have hh : h = ∑ i, h i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hh]
    simp [F, PiLp.inner_apply, map_sum, map_smul]
  have hFc : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ w y) :=
      hw.fderiv_right (by exact_mod_cast le_top)
    have : ContDiff ℝ (⊤ : ℕ∞) (fun y => (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)).symm
        (fun i => fderiv ℝ w y (EuclideanSpace.single i 1))) := by
      apply (LinearEquiv.toContinuousLinearEquiv
        (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)).symm).contDiff.comp
      exact contDiff_pi.2 fun i => hD.clm_apply contDiff_const
    simpa [F] using this
  have hFn : ∀ y, ‖F y‖ = ‖fderiv ℝ w y‖ := by
    intro y
    have hdual : InnerProductSpace.toDual ℝ (Euclid P) (F y) = fderiv ℝ w y := by
      ext h
      simp [InnerProductSpace.toDual_apply_apply, hinner]
    rw [← hdual, LinearIsometryEquiv.norm_map]
  simp_rw [← hFn]
  -- Step 2: `vol W < ∞`, `closure W` is compact, `‖F‖ ≤ M` on `closure W`, `‖F‖` integrable on `W`
  have hWm : volume W < ∞ := hWb.measure_lt_top
  have hWc : IsCompact (closure W) := hWb.isCompact_closure
  obtain ⟨M, hM⟩ := hWc.exists_bound_of_continuousOn hFc.continuous.continuousOn
  have hFi : IntegrableOn (fun y => ‖F y‖) W :=
    (hFc.continuous.norm.continuousOn.integrableOn_compact hWc).mono_set subset_closure
  -- the scalar inequality `a ≤ a² / S + ε` for `a ≤ S ≤ a + ε`
  have alg : ∀ ε a S : ℝ, 0 < S → a ≤ S → S ≤ a + ε → a ≤ S⁻¹ * a ^ 2 + ε := by
    intro ε a S hS haS hSa
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hS]
    nlinarith [sq_nonneg (S - a), mul_nonneg hS.le (sub_nonneg.2 hSa)]
  -- Step 3: for every `ε > 0`, `∫_W ‖F‖ ≤ V + (|M| + vol W) ε`
  have key : ∀ ε : ℝ, 0 < ε → ∫ y in W, ‖F y‖ ≤ V + (|M| + volume.real W) * ε := by
    intro ε hε
    -- the smooth cut-off `χ` with compact support in `W` and `vol (W ∩ {χ ≠ 1}) < ε`
    have hfin : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWm.ne
    obtain ⟨χ, hχ, hχc, hχW, hχ01, hχm⟩ :=
      Submission.rsd_mw_tfa_smooth_cutoff P (volume.restrict W) W hfin hWo
        (by rw [Measure.restrict_apply' hWo.measurableSet, compl_inter_self, measure_empty]) ε hε
    -- the regularised length `s = √(‖F‖² + ε²)` and the test field `g = χ s⁻¹ F`
    set s : Euclid P → ℝ := fun y => √(‖F y‖ ^ 2 + ε ^ 2)
    have hspos : ∀ y, 0 < s y := by
      intro y
      show 0 < √(‖F y‖ ^ 2 + ε ^ 2)
      positivity
    have hsc : ContDiff ℝ (⊤ : ℕ∞) s :=
      ((hFc.norm_sq ℝ).add contDiff_const).sqrt fun y =>
        (by positivity : (0 : ℝ) < ‖F y‖ ^ 2 + ε ^ 2).ne'
    have hFs : ∀ y, ‖F y‖ ≤ s y := by
      intro y
      show ‖F y‖ ≤ √(‖F y‖ ^ 2 + ε ^ 2)
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg ε))
    have hsF : ∀ y, s y ≤ ‖F y‖ + ε := by
      intro y
      show √(‖F y‖ ^ 2 + ε ^ 2) ≤ ‖F y‖ + ε
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_nonneg (norm_nonneg (F y)) hε.le]
    have hgc : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y • ((s y)⁻¹ • F y)) :=
      hχ.smul ((hsc.inv fun y => (hspos y).ne').smul hFc)
    have hgcs : HasCompactSupport (fun y => χ y • ((s y)⁻¹ • F y)) :=
      hχc.smul_right (f' := fun y => (s y)⁻¹ • F y)
    have hgt : tsupport (fun y => χ y • ((s y)⁻¹ • F y)) ⊆ W :=
      (tsupport_smul_subset_left χ fun y => (s y)⁻¹ • F y).trans hχW
    have hg1 : ∀ y, ‖χ y • ((s y)⁻¹ • F y)‖ ≤ 1 := by
      intro y
      have hc0 : 0 ≤ (s y)⁻¹ * ‖F y‖ := mul_nonneg (inv_nonneg.2 (hspos y).le) (norm_nonneg _)
      have hc1 : (s y)⁻¹ * ‖F y‖ ≤ 1 := by
        rw [inv_mul_le_iff₀ (hspos y), mul_one]
        exact hFs y
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hχ01 y).1,
        Real.norm_of_nonneg (inv_nonneg.2 (hspos y).le)]
      exact (mul_le_of_le_one_left hc0 (hχ01 y).2).trans hc1
    -- `Dw(y) (g y) = ψ y := χ y s(y)⁻¹ ‖F y‖²`; `ψ` vanishes off `W`, so `∫_W ψ ≤ V`
    set ψ : Euclid P → ℝ := fun y => χ y * ((s y)⁻¹ * ‖F y‖ ^ 2)
    have hDg : ∀ y, fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) = ψ y := by
      intro y
      show fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) = χ y * ((s y)⁻¹ * ‖F y‖ ^ 2)
      rw [← hinner, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hψ0W : ∀ y ∉ W, ψ y = 0 := by
      intro y hy
      have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hχW h)
      show χ y * ((s y)⁻¹ * ‖F y‖ ^ 2) = 0
      rw [h0, zero_mul]
    have hψV : ∫ y in W, ψ y ≤ V := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hψ0W]
      calc ∫ y, ψ y = ∫ y, fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) := by simp_rw [hDg]
        _ ≤ V := hV (fun y => χ y • ((s y)⁻¹ • F y)) hgc hgcs hgt hg1
    -- pointwise on `W`: `‖F‖ ≤ ψ + |M| 1_{χ ≠ 1} + ε`
    have hEm : MeasurableSet {x | χ x ≠ 1} :=
      (isOpen_ne_fun hχ.continuous continuous_const).measurableSet
    have hpt : ∀ y ∈ W,
        ‖F y‖ ≤ ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y + ε := by
      intro y hy
      by_cases hy1 : χ y = 1
      · have hyE : y ∉ {x | χ x ≠ 1} := fun h => h hy1
        rw [indicator_of_notMem hyE, add_zero]
        show ‖F y‖ ≤ χ y * ((s y)⁻¹ * ‖F y‖ ^ 2) + ε
        rw [hy1, one_mul]
        exact alg ε _ _ (hspos y) (hFs y) (hsF y)
      · have hyE : y ∈ {x | χ x ≠ 1} := hy1
        rw [indicator_of_mem hyE]
        have hψ0 : 0 ≤ ψ y :=
          mul_nonneg (hχ01 y).1 (mul_nonneg (inv_nonneg.2 (hspos y).le) (sq_nonneg _))
        have h1 := hM y (subset_closure hy)
        have h2 := le_abs_self M
        show ‖F y‖ ≤ ψ y + |M| + ε
        linarith
    -- integrate over `W`
    have hψc : Continuous ψ :=
      hχ.continuous.mul ((hsc.continuous.inv₀ fun y => (hspos y).ne').mul
        (hFc.continuous.norm.pow 2))
    have hψi : IntegrableOn ψ W :=
      (hψc.continuousOn.integrableOn_compact hWc).mono_set subset_closure
    have hEi : IntegrableOn (Set.indicator {x | χ x ≠ 1} fun _ => |M|) W :=
      (integrableOn_const hWm.ne).indicator hEm
    have hψEi : IntegrableOn (fun y => ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y) W :=
      hψi.add hEi
    have hεi : IntegrableOn (fun _ => ε) W := integrableOn_const hWm.ne
    have hEε : (volume.restrict W).real {x | χ x ≠ 1} ≤ ε :=
      (ENNReal.toReal_lt_of_lt_ofReal hχm).le
    calc ∫ y in W, ‖F y‖
        ≤ ∫ y in W, (ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y + ε) :=
          setIntegral_mono_on hFi (hψEi.add hεi) hWo.measurableSet hpt
      _ = (∫ y in W, ψ y) + (∫ y in W, Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y) +
            ∫ y in W, ε := by
          rw [integral_add hψEi hεi, integral_add hψi hEi]
      _ = (∫ y in W, ψ y) + (volume.restrict W).real {x | χ x ≠ 1} * |M| +
            volume.real W * ε := by
          rw [integral_indicator_const _ hEm, setIntegral_const, smul_eq_mul, smul_eq_mul]
      _ ≤ V + (|M| + volume.real W) * ε := by
          nlinarith [mul_le_mul_of_nonneg_right hEε (abs_nonneg M)]
  -- Step 4: let `ε → 0`
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hL : 0 ≤ volume.real W := measureReal_nonneg
  have hpos : 0 < |M| + volume.real W + 1 := by positivity
  have h1 := key (η / (|M| + volume.real W + 1)) (div_pos hη hpos)
  have h2 : (|M| + volume.real W) * (η / (|M| + volume.real W + 1)) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith
  linarith

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

/-- Simon Ch. 2, Lemma 2.5 on the cube `Q₁ = (0, 1)^{m+1}`: if `∫_{Q₁} u div g ≤ V` for every
smooth `g` with compact support in `Q₁` and `|g| ≤ 1`, then `u_η = η * 1_{Q₁} u` is smooth and
`∫_{Q_δ} |Du_η| ≤ V` whenever `spt η ⊆ B_δ(0)`.  For `g` with compact support in `Q_δ`, the
mollified field `G = η * g` is admissible, and `∫ Du_η · g = −∫_{Q₁} u div G = ∫_{Q₁} u div(−G)`. -/
theorem dor_lmb_fcd_cp_mollified_variation : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → (∀ z, 0 ≤ η z) → (∀ z, η (-z) = η z) → ∫ z, η z = 1 → support η ⊆ ball (0 : Euclid (m + 1)) δ → ContDiff ℝ (⊤ : ℕ∞) (convolution η (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ (convolution η (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ V := by
  intro m u V δ η hu hH hδ hη hηc hη0 heven hη1 hηs
  -- Step 0: `{y : a < yᵢ < b for all i}` is open, a finite intersection of open slabs.
  have hopen : ∀ a b : ℝ, IsOpen {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hQ₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    (hopen 0 1).measurableSet
  have hũ : Integrable ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) :=
    hu.integrable_indicator hQ₁
  -- Step 1: `1_{Q₁} u` is integrable, so `u_η` is smooth.
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (convolution η
      ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_left _ hη hũ.locallyIntegrable
  -- Step 2: `Q_δ` is open and bounded: it lies in the closed ball of radius `√(m + 1)`.
  have hbdd : Bornology.IsBounded {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} := by
    refine (isBounded_closedBall (x := (0 : Euclid (m + 1))) (r := √((m : ℝ) + 1))).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h0 : 0 < y i := by linarith [(hy i).1]
          have h1 : y i < 1 := by linarith [(hy i).2]
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = (m : ℝ) + 1 := by simp
  -- Step 3: by `smooth_duality` it suffices to bound `∫ Du_η · g` for admissible `g` in `Q_δ`.
  refine ⟨hsmooth, Submission.dor_lmb_fcd_cp_smooth_duality (m + 1) _ _ V (hopen δ (1 - δ)) hbdd
    hsmooth fun g hg hgc hgs hg1 => ?_⟩
  -- Step 4: `G = η * g` is smooth, compactly supported in `Q₁`, and `|G| ≤ 1`.
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_left _ hη hg.continuous.locallyIntegrable
  have hGc : HasCompactSupport (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.convolution _ hgc
  have hGs : tsupport (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    -- `spt G ⊆ spt η + spt g ⊆ B̄_δ(0) + Q_δ ⊆ Q₁`, the middle set being compact.
    refine (closure_minimal ((support_convolution_subset (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1))).trans
      (add_subset_add (subset_tsupport η) (subset_tsupport g)))
      (hηc.isCompact.add hgc.isCompact).isClosed).trans ?_
    rintro _ ⟨z, hz, q, hq, rfl⟩ i
    have hz' : ‖z‖ ≤ δ :=
      mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall (closure_mono hηs hz))
    have hzi : |z i| ≤ δ := by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le z i).trans hz'
    have hqi := hgs hq i
    rw [PiLp.add_apply]
    constructor <;> linarith [(abs_le.mp hzi).1, (abs_le.mp hzi).2, hqi.1, hqi.2]
  have hG1 : ∀ x, ‖convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ ≤ 1 := by
    intro x
    rw [convolution_def]
    calc ‖∫ t, ContinuousLinearMap.lsmul ℝ ℝ (η t) (g (x - t))‖ ≤ ∫ t, η t :=
          norm_integral_le_of_norm_le (hη.continuous.integrable_of_hasCompactSupport hηc)
            (Eventually.of_forall fun t => by
              rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (hη0 t)]
              exact mul_le_of_le_one_right (hη0 t) (hg1 _))
      _ = 1 := hη1
  -- Step 5: `mollifier_adjoint` gives `∫ Du_η · g = −∫ 1_{Q₁} u div G`.
  have hadj := codim1_rdo_dg_sp_mollifier_adjoint (m + 1) η
    ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) g
    (hη.of_le (by exact_mod_cast le_top)) hηc heven hũ
    (hg.continuous.integrable_of_hasCompactSupport hgc)
  -- Step 6: (H) for `−G` reads `−∫_{Q₁} u div G ≤ V`, since `div(−G) = −div G`.
  have hneg := hH (-convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) hGsmooth.neg hGc.neg
    (by rwa [tsupport_neg]) fun y => by rw [Pi.neg_apply, norm_neg]; exact hG1 y
  simp only [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg, mul_neg,
    integral_neg] at hneg
  rw [← integral_indicator hQ₁] at hneg
  simp_rw [indicator_mul_left] at hneg
  rw [hadj]
  exact hneg

end Submission

end GMT.Ch07
