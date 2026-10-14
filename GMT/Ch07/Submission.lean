import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.AreaLipschitz
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

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

/-- **Lipschitz order statistic** (proof of Simon Ch. 6, Lemma 5.4, the retraction of the
deformation theorem): for `m + 1 < P` the `ℓ`-th largest entry
`κ u = max_{|I| = ℓ} min_{i ∈ I} u i`, `ℓ = P − (m + 1)`, of `u : Fin P → ℝ` is `≤` at least `ℓ`
entries of `u`, `≥` at least `m + 2` entries, and is `1`-Lipschitz for the sup norm.  A maximizing
`I` gives the first property; if at most `m + 1` entries were `≤ κ u`, then `ℓ` entries `> κ u`
would form an `I` with `min_I u > κ u`; and each `min_I` is `1`-Lipschitz for the sup norm, hence
so is their maximum. -/
theorem Submission.dor_lmb_fcdr_order_stat : ∀ (P m : ℕ), m + 1 < P → ∃ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) ∧ (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, u i ≤ κ u) ∧ ∀ u v : Fin P → ℝ, ∀ t : ℝ, (∀ i, |u i - v i| ≤ t) → |κ u - κ v| ≤ t := by
  intro P m hmP
  classical
  -- `𝓕` = the `ℓ`-element index sets, `ℓ = P − (m + 1) ≥ 1`; `𝓕` and its members are nonempty
  let F : Finset (Finset (Fin P)) := Finset.powersetCard (P - (m + 1)) Finset.univ
  have hF : F.Nonempty := Finset.powersetCard_nonempty.2 (by rw [Finset.card_fin]; omega)
  have hFI : ∀ I ∈ F, I.Nonempty ∧ I.card = P - (m + 1) := fun I hI => by
    have hc := (Finset.mem_powersetCard.1 hI).2
    exact ⟨Finset.card_pos.1 (by omega), hc⟩
  -- `g u I = min_{i ∈ I} u i` (the empty set, not in `𝓕`, gets `0`); `κ u = max_{I ∈ 𝓕} g u I`
  let g : (Fin P → ℝ) → Finset (Fin P) → ℝ := fun u I => if h : I.Nonempty then I.inf' h u else 0
  have hg : ∀ u I (hI : I ∈ F), g u I = I.inf' (hFI I hI).1 u := fun u I hI =>
    dite_eq_left (hFI I hI).1
  refine ⟨fun u => F.sup' hF (g u), fun u => ?_, fun u => ?_, fun u v t huv => ?_⟩
  · -- (1): a maximizing `I` has `ℓ` indices with `κ u ≤ u i`
    obtain ⟨I, hI, hIu⟩ := Finset.exists_mem_eq_sup' hF (g u)
    refine ⟨I, by have := (hFI I hI).2; omega, fun i hi => ?_⟩
    show F.sup' hF (g u) ≤ u i
    rw [hIu, hg u I hI]
    exact Finset.inf'_le u hi
  · -- (2): otherwise `ℓ` entries `> κ u` would form `I ∈ 𝓕` with `g u I > κ u`
    refine ⟨Finset.univ.filter (fun i => u i ≤ F.sup' hF (g u)), ?_,
      fun i hi => (Finset.mem_filter.1 hi).2⟩
    by_contra hlt
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => u i ≤ F.sup' hF (g u))
    rw [Finset.card_fin] at hsum
    obtain ⟨I, hIB, hIc⟩ := Finset.exists_subset_card_eq
      (s := Finset.univ.filter (fun i => ¬ u i ≤ F.sup' hF (g u))) (n := P - (m + 1)) (by omega)
    have hI : I ∈ F := Finset.mem_powersetCard.2 ⟨Finset.subset_univ I, hIc⟩
    have h1 : g u I ≤ F.sup' hF (g u) := Finset.le_sup' (g u) hI
    have h2 : F.sup' hF (g u) < g u I := by
      rw [hg u I hI, Finset.lt_inf'_iff]
      exact fun i hi => lt_of_not_ge (Finset.mem_filter.1 (hIB hi)).2
    exact absurd h1 (not_le.2 h2)
  · -- (3): each `g · I`, hence `κ`, is `1`-Lipschitz for the sup norm
    have key : ∀ u v : Fin P → ℝ, (∀ i, |u i - v i| ≤ t) →
        F.sup' hF (g u) ≤ F.sup' hF (g v) + t := by
      intro u v huv
      refine Finset.sup'_le hF (g u) fun I hI => ?_
      obtain ⟨i₀, hi₀, hv⟩ := Finset.exists_mem_eq_inf' (hFI I hI).1 v
      have h1 : g u I ≤ u i₀ := by rw [hg u I hI]; exact Finset.inf'_le u hi₀
      have h2 : g v I = v i₀ := by rw [hg v I hI]; exact hv
      have h3 : g v I ≤ F.sup' hF (g v) := Finset.le_sup' (g v) hI
      have h4 := (abs_le.1 (huv i₀)).2
      linarith
    have hvu : ∀ i, |v i - u i| ≤ t := fun i => by rw [abs_sub_comm]; exact huv i
    show |F.sup' hF (g u) - F.sup' hF (g v)| ≤ t
    rw [abs_sub_le_iff]
    constructor <;> linarith [key u v huv, key v u hvu]
/-- **Distance to `L*(a)` from an integer translate** (Simon Ch. 6, 5.4, closed-form retraction,
Claim C).  Let `|aᵢ - 1/2| < 1/4` for all `i`, and let `κ(u) ≥ uᵢ` for at least `m + 2` indices `i`
(every `u`).  If `x - y ∈ ℤᴾ` then `dist(x, L*(a)) ≤ √(m + 2) κ(r(y))`, where
`r_j(y) = max((y_j - a_j)/(1 - a_j), (a_j - y_j)/a_j)` and `L*(a)` is the set of points with at least
`m + 2` coordinates in `aᵢ + ℤ`.  As `0 < a_j, 1 - a_j ≤ 1`, `|y_j - a_j| ≤ r_j(y)`.  On a set `J`
of `m + 2` indices with `r_i(y) ≤ κ(r(y))` put `x*_i = x_i - y_i + a_i` (`i ∈ J`), `x*_i = x_i`
(`i ∉ J`); then `x* ∈ L*(a)` and `|x - x*|² = Σ_{i ∈ J} (y_i - a_i)² ≤ (m + 2) κ(r(y))²`. -/
theorem Submission.dor_lmb_fcdr_dual_dist : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, u i ≤ κ u) → ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) → infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} ≤ Real.sqrt (m + 2) * κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) := by
  intro P m a ha κ hκ x y hxy
  set u : Fin P → ℝ := fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j) with hu_def
  -- Steps 1–2: `1/4 < a_j < 3/4`, so `|y_j - a_j| ≤ r_j(y) = u j`
  have hbound : ∀ j, |y j - a j| ≤ u j := by
    intro j
    obtain ⟨h1l, h1r⟩ := abs_lt.mp (ha j)
    have ha0 : 0 < a j := by linarith
    have ha1 : 0 < 1 - a j := by linarith
    rcases le_total (a j) (y j) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have hle : y j - a j ≤ (y j - a j) / (1 - a j) := by
        rw [le_div_iff₀ ha1]
        nlinarith
      exact hle.trans (le_max_left _ _)
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
      have hle : a j - y j ≤ (a j - y j) / a j := by
        rw [le_div_iff₀ ha0]
        nlinarith
      exact hle.trans (le_max_right _ _)
  -- Step 3: a set `J` of exactly `m + 2` indices with `|y_i - a_i| ≤ u i ≤ κ u`, so `κ u ≥ 0`
  obtain ⟨s, hs_card, hs⟩ := hκ u
  obtain ⟨J, hJs, hJcard⟩ := Finset.exists_subset_card_eq hs_card
  choose k hk using hxy
  have hJbound : ∀ i ∈ J, |y i - a i| ≤ κ u := fun i hi =>
    (hbound i).trans (hs i (hJs hi))
  have hκ_nonneg : 0 ≤ κ u := by
    have hJne : J.Nonempty := by
      rw [← Finset.card_pos, hJcard]; omega
    obtain ⟨i, hi⟩ := hJne
    exact (abs_nonneg _).trans (hJbound i hi)
  -- Step 4: the shifted point `x*` lies in `L*(a)`
  let xs : Euclid P := WithLp.toLp 2 (fun i => if i ∈ J then x i - y i + a i else x i)
  have hxs_mem : xs ∈ {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} := by
    refine ⟨J, hJcard.ge, fun i hi => ⟨k i, ?_⟩⟩
    show (if i ∈ J then x i - y i + a i else x i) - a i = k i
    rw [ite_eq_left hi, ← hk i]
    ring
  -- Step 5: `dist(x, L*(a)) ≤ |x - x*| = (Σ_{i ∈ J} (y_i - a_i)²)^{1/2} ≤ √(m + 2) κ u`
  refine (infDist_le_dist_of_mem hxs_mem).trans ?_
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (xs i) ^ 2 ≤ ((m : ℝ) + 2) * (κ u) ^ 2 := by
    have h1 : ∑ i, dist (x i) (xs i) ^ 2 = ∑ i ∈ J, dist (x i) (xs i) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ J)
      intro i _ hi
      show dist (x i) (if i ∈ J then x i - y i + a i else x i) ^ 2 = 0
      rw [ite_eq_right hi, dist_self]
      ring
    rw [h1]
    have h2 : ∑ i ∈ J, dist (x i) (xs i) ^ 2 ≤ J.card • (κ u ^ 2) := by
      apply Finset.sum_le_card_nsmul
      intro i hi
      show dist (x i) (if i ∈ J then x i - y i + a i else x i) ^ 2 ≤ κ u ^ 2
      rw [ite_eq_left hi, Real.dist_eq]
      have hxy' : x i - (x i - y i + a i) = y i - a i := by ring
      rw [hxy']
      exact pow_le_pow_left₀ (abs_nonneg _) (hJbound i hi) 2
    rw [hJcard, nsmul_eq_mul] at h2
    push_cast at h2
    exact h2
  calc Real.sqrt (∑ i, dist (x i) (xs i) ^ 2)
      ≤ Real.sqrt (((m : ℝ) + 2) * (κ u) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((m : ℝ) + 2) * κ u := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hκ_nonneg]
/-- **Simon Ch. 6, Lemma 5.4** (step 4(i) of the closed-form retraction): with
`r_j(y) = max((y_j − a_j)/(1 − a_j), (a_j − y_j)/a_j)` and `κ(r(y)) > 0`, the point
`Φ(y)_i = a_i + (y_i − a_i)/max(r_i(y), κ(r(y)))` lies in the cube `[0, 1]ᴾ`, and `Φ(y)_i ∈ {0, 1}`
on an index set `s` with `P ≤ m + 1 + |s|`.  As `1/4 < a_i < 3/4`, `μ_i = max(r_i(y), κ(r(y)))` is
positive and dominates `(y_i − a_i)/(1 − a_i)` and `(a_i − y_i)/a_i`, so
`−a_i ≤ (y_i − a_i)/μ_i ≤ 1 − a_i`.  On the indices with `κ(r(y)) ≤ r_i(y)` given by the hypothesis
on `κ`, `μ_i = r_i(y)` and the quotient is exactly `1 − a_i` (`y_i ≥ a_i`) or `−a_i` (`y_i < a_i`). -/
theorem Submission.dor_lmb_fcdr_cube_skeleton : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y : Euclid P, 0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) → (∀ i, 0 ≤ Φ y i ∧ Φ y i ≤ 1) ∧ ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, Φ y i = 0 ∨ Φ y i = 1 := by
  intro P m a ha κ hκ Φ hΦ y hy
  -- `|a_i − 1/2| < 1/4` gives `0 < a_i < 1`
  have ha' : ∀ i, 0 < a i ∧ a i < 1 := fun i => by
    obtain ⟨h1, h2⟩ := abs_lt.mp (ha i)
    constructor <;> linarith
  -- if `μ > 0` dominates `(z − b)/(1 − b)` and `(b − z)/b`, then `0 ≤ b + (z − b)/μ ≤ 1`
  have bounds : ∀ b z μ : ℝ, 0 < b → b < 1 → 0 < μ → (z - b) / (1 - b) ≤ μ → (b - z) / b ≤ μ →
      0 ≤ b + (z - b) / μ ∧ b + (z - b) / μ ≤ 1 := by
    intro b z μ hb0 hb1 hμ h1 h2
    rw [div_le_iff₀ (by linarith)] at h1
    rw [div_le_iff₀ hb0] at h2
    constructor
    · have : -b ≤ (z - b) / μ := by
        rw [le_div_iff₀ hμ]
        linarith
      linarith
    · have : (z - b) / μ ≤ 1 - b := by
        rw [div_le_iff₀ hμ]
        linarith
      linarith
  -- if moreover `0 < k ≤ r = max((z − b)/(1 − b), (b − z)/b)`, then `max(r, k) = r` and the
  -- coordinate is `b + (1 − b) = 1` (`z ≥ b`) or `b − b = 0` (`z < b`)
  have skel : ∀ b z k : ℝ, 0 < b → b < 1 → 0 < k → k ≤ max ((z - b) / (1 - b)) ((b - z) / b) →
      b + (z - b) / max (max ((z - b) / (1 - b)) ((b - z) / b)) k = 0 ∨
        b + (z - b) / max (max ((z - b) / (1 - b)) ((b - z) / b)) k = 1 := by
    intro b z k hb0 hb1 hk hkr
    have h1b : 0 < 1 - b := by linarith
    rw [max_eq_left hkr]
    rcases le_or_gt b z with h | h
    · right
      have e1 : (b - z) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hb0.le
      have e2 : 0 ≤ (z - b) / (1 - b) := div_nonneg (by linarith) h1b.le
      rw [max_eq_left (e1.trans e2)] at hkr ⊢
      have hzb : z - b ≠ 0 := by
        intro h0
        rw [h0, zero_div] at hkr
        linarith
      rw [div_div_cancel₀ hzb]
      ring
    · left
      have e1 : (z - b) / (1 - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h1b.le
      have e2 : 0 ≤ (b - z) / b := div_nonneg (by linarith) hb0.le
      rw [max_eq_right (e1.trans e2), ← neg_sub b z, neg_div, div_div_cancel₀ (sub_pos.mpr h).ne']
      ring
  -- `μ_i = max(r_i(y), κ(r(y))) ≥ κ(r(y)) > 0` dominates both quotients in `r_i(y)`
  refine ⟨fun i => ?_, ?_⟩
  · rw [hΦ y i]
    exact bounds (a i) (y i) _ (ha' i).1 (ha' i).2 (hy.trans_le (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
  · -- the indices with `κ(r(y)) ≤ r_i(y)` land on a face: `Φ(y)_i ∈ {0, 1}`
    obtain ⟨s, hs, hsκ⟩ := hκ fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)
    refine ⟨s, hs, fun i hi => ?_⟩
    rw [hΦ y i]
    exact skel (a i) (y i) _ (ha' i).1 (ha' i).2 hy (hsκ i hi)
/-- **Simon Ch. 6, Lemma 5.4** (retraction onto the `n`-skeleton), integer-translation
compatibility of the cube map `Φ(y)ᵢ = aᵢ + (yᵢ − aᵢ)/max(rᵢ(y), κ(r(y)))`, where
`rⱼ(y) = max((yⱼ − aⱼ)/(1 − aⱼ), (aⱼ − yⱼ)/aⱼ)`: if `y, y' ∈ [0, 1]ᴾ` and `y' − y ∈ ℤᴾ`, then
`Φ(y') = Φ(y) + (y' − y)`.  Each coordinate has `y'ⱼ = yⱼ` or `{yⱼ, y'ⱼ} = {0, 1}`, where
`rⱼ = 1`; so `r(y') = r(y)`, `κ(r(y)) ≤ rᵢ₀(y) ≤ 1` for some `i₀` (as `m + 1 < P`), and `Φ` is the
identity on the moved coordinates. -/
theorem Submission.dor_lmb_fcdr_cube_periodic : ∀ (P m : ℕ), m + 1 < P → ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y y' : Euclid P, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → (∀ i, ∃ k : ℤ, y' i - y i = k) → ∀ i, Φ y' i = Φ y i + (y' i - y i) := by
  intro P m hmP a ha κ hκ Φ hΦ y y' hy hy' hint i
  -- `0 < aⱼ < 1`
  have ha0 : ∀ j, 0 < a j := fun j => by linarith [(abs_lt.mp (ha j)).1]
  have ha1 : ∀ j, 0 < 1 - a j := fun j => by linarith [(abs_lt.mp (ha j)).2]
  -- `ρⱼ(t) = max((t − aⱼ)/(1 − aⱼ), (aⱼ − t)/aⱼ)` has `ρⱼ(0) = ρⱼ(1) = 1` and `ρⱼ ≤ 1` on `[0, 1]`
  have hρ0 : ∀ j, max ((0 - a j) / (1 - a j)) ((a j - 0) / a j) = 1 := fun j => by
    rw [sub_zero, div_self (ha0 j).ne']
    exact max_eq_right ((div_le_one (ha1 j)).mpr (by linarith))
  have hρ1 : ∀ j, max ((1 - a j) / (1 - a j)) ((a j - 1) / a j) = 1 := fun j => by
    rw [div_self (ha1 j).ne']
    exact max_eq_left ((div_le_one (ha0 j)).mpr (by linarith))
  have hρle : ∀ j, max ((y j - a j) / (1 - a j)) ((a j - y j) / a j) ≤ 1 := fun j =>
    max_le ((div_le_one (ha1 j)).mpr (by linarith [(hy j).2]))
      ((div_le_one (ha0 j)).mpr (by linarith [(hy j).1]))
  -- `y'ⱼ − yⱼ ∈ ℤ ∩ [−1, 1]`, so `y'ⱼ = yⱼ` or `{yⱼ, y'ⱼ} = {0, 1}`
  have hcase : ∀ j, y' j = y j ∨ (y j = 0 ∧ y' j = 1) ∨ (y j = 1 ∧ y' j = 0) := by
    intro j
    obtain ⟨k, hk⟩ := hint j
    obtain ⟨h₀, h₁⟩ := hy j
    obtain ⟨h₀', h₁'⟩ := hy' j
    have hk1 : k ≤ 1 := by
      have : (k : ℝ) ≤ 1 := by linarith
      exact_mod_cast this
    have hk2 : -1 ≤ k := by
      have : (-1 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl <;> push_cast at hk
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  -- hence `r(y') = r(y)` and `κ(r(y')) = κ(r(y))`
  have hr : ∀ j, max ((y' j - a j) / (1 - a j)) ((a j - y' j) / a j)
      = max ((y j - a j) / (1 - a j)) ((a j - y j) / a j) := by
    intro j
    rcases hcase j with h | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h]
    · rw [h0, h1, hρ0 j, hρ1 j]
    · rw [h0, h1, hρ0 j, hρ1 j]
  have hκeq : κ (fun j => max ((y' j - a j) / (1 - a j)) ((a j - y' j) / a j))
      = κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) :=
    congrArg κ (funext hr)
  -- `κ(r(y)) ≤ 1`: `s` is nonempty as `P ≤ m + 1 + |s|` and `m + 1 < P`
  have hκle : κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) ≤ 1 := by
    obtain ⟨s, hs, hsκ⟩ := hκ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hne
    exact (hsκ i₀ hi₀).trans (hρle i₀)
  -- coordinates with `y'ᵢ = yᵢ` agree; on `{yᵢ, y'ᵢ} = {0, 1}`, `max(rᵢ, κ) = 1` and `Φ` fixes `yᵢ`
  rw [hΦ y' i, hΦ y i, hκeq, hr i]
  rcases hcase i with h | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h]
    ring
  · rw [h0, h1, hρ0 i, max_eq_left hκle]
    ring
  · rw [h0, h1, hρ1 i, max_eq_left hκle]
    ring
/-- **Claim B** (Simon Ch. 6, Lemma 5.4, step 6 of the corrected closed-form proof: Lipschitz bound
for the cube retraction `Φ`).  Let `|aᵢ − 1/2| < 1/4`, let `κ` be `1`-Lipschitz for the sup norm,
`rⱼ(y) = max((yⱼ − aⱼ)/(1 − aⱼ), (aⱼ − yⱼ)/aⱼ)` and `Φ(y)ᵢ = aᵢ + (yᵢ − aᵢ)/max(rᵢ(y), κ(r(y)))`.
If `κ(r(y)) > 0` then `|Φ(y) − Φ(y')| ≤ 4√P |y − y'| / κ(r(y))`: each `rⱼ` is `4`-Lipschitz, so the
denominators `μ = max(rᵢ(y), κ(r(y)))` and `μ'` differ by at most `4|y − y'|`; `|y'ᵢ − aᵢ| ≤ (3/4)μ'`,
and `u/μ − u'/μ' = (u − u')/μ + (u'/μ')(μ' − μ)/μ` bounds each coordinate by
`4|y − y'|/κ(r(y))`. -/
theorem Submission.dor_lmb_fcdr_cube_lipschitz : ∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u v : Fin P → ℝ, ∀ t : ℝ, (∀ i, |u i - v i| ≤ t) → |κ u - κ v| ≤ t) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y y' : Euclid P, 0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) → dist (Φ y) (Φ y') ≤ 4 * Real.sqrt P / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) * dist y y' := by
  intro P a ha κ hκ Φ hΦ y y' hk
  -- Step 1: `1/4 < aᵢ < 3/4`, and `|yⱼ − y'ⱼ| ≤ dist y y'`
  have a_bounds : ∀ c : ℝ, |c - 1 / 2| < 1 / 4 → 1 / 4 < c ∧ c < 3 / 4 := fun c hc => by
    rcases abs_lt.mp hc with ⟨h1, h2⟩
    constructor <;> linarith
  have hcoord : ∀ j, |y j - y' j| ≤ dist y y' := fun j => by
    have := PiLp.dist_apply_le y y' j
    rwa [Real.dist_eq] at this
  -- Step 2: `rⱼ` is `4`-Lipschitz in `yⱼ`, so `|κ(r(y)) − κ(r(y'))| ≤ 4 dist y y'`
  have div_lip : ∀ s x x' δ : ℝ, 1 / 4 < s → |x - x'| ≤ δ → |x / s - x' / s| ≤ 4 * δ := by
    intro s x x' δ hs h
    have hs0 : (0 : ℝ) < s := by linarith
    have hδ : 0 ≤ δ := le_trans (abs_nonneg _) h
    rw [← sub_div, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    nlinarith [mul_nonneg hδ (by linarith : (0 : ℝ) ≤ 4 * s - 1)]
  have r_lip : ∀ c b b' δ : ℝ, |c - 1 / 2| < 1 / 4 → |b - b'| ≤ δ →
      |max ((b - c) / (1 - c)) ((c - b) / c) - max ((b' - c) / (1 - c)) ((c - b') / c)|
        ≤ 4 * δ := by
    intro c b b' δ hc h
    obtain ⟨hc1, hc2⟩ := a_bounds c hc
    refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le ?_ ?_)
    · apply div_lip _ _ _ _ (by linarith)
      rwa [sub_sub_sub_cancel_right]
    · apply div_lip _ _ _ _ hc1
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact h
  have hkk : |κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))
      - κ (fun j => max ((y' j - a j) / (1 - a j)) ((a j - y' j) / a j))| ≤ 4 * dist y y' :=
    hκ _ _ _ (fun j => r_lip _ _ _ _ (ha j) (hcoord j))
  -- Step 3: `|b − c| ≤ (3/4) r(b)`; in particular `r(b) ≥ 0`, and `r(b) = 0` forces `b = c`
  have abs_le_r : ∀ c b : ℝ, |c - 1 / 2| < 1 / 4 →
      |b - c| ≤ 3 / 4 * max ((b - c) / (1 - c)) ((c - b) / c) := by
    intro c b hc
    obtain ⟨hc1, hc2⟩ := a_bounds c hc
    have h1c : (0 : ℝ) < 1 - c := by linarith
    have hc0 : (0 : ℝ) < c := by linarith
    rcases le_total c b with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have hq : 0 ≤ (b - c) / (1 - c) := div_nonneg (sub_nonneg.mpr h) h1c.le
      have he : (b - c) / (1 - c) * (1 - c) = b - c := div_mul_cancel₀ _ h1c.ne'
      have hm := le_max_left ((b - c) / (1 - c)) ((c - b) / c)
      nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ c - 1 / 4)]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      have hq : 0 ≤ (c - b) / c := div_nonneg (sub_nonneg.mpr h) hc0.le
      have he : (c - b) / c * c = c - b := div_mul_cancel₀ _ hc0.ne'
      have hm := le_max_right ((b - c) / (1 - c)) ((c - b) / c)
      nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ 3 / 4 - c)]
  -- Step 4: `|u/μ − u'/μ'| ≤ 4δ/μ`
  have key : ∀ u u' μ μ' δ : ℝ, 0 < μ → 0 ≤ μ' → |u'| ≤ 3 / 4 * μ' → |u - u'| ≤ δ →
      |μ - μ'| ≤ 4 * δ → |u / μ - u' / μ'| ≤ 4 * δ / μ := by
    intro u u' μ μ' δ hμ hμ'0 hu' huu hμμ
    have hX : u / μ * μ = u := div_mul_cancel₀ u hμ.ne'
    have hX' : u' / μ' * μ' = u' ∧ |u' / μ'| ≤ 3 / 4 := by
      rcases hμ'0.eq_or_lt with h | h
      · -- (b) `μ' = 0` forces `u' = 0`
        subst h
        have hu0 : u' = 0 := abs_nonpos_iff.mp (by linarith)
        subst hu0
        norm_num
      · -- (a) `μ' > 0` gives `|u'|/μ' ≤ 3/4`
        refine ⟨div_mul_cancel₀ u' h.ne', ?_⟩
        rw [abs_div, abs_of_pos h, div_le_iff₀ h]
        exact hu'
    rw [le_div_iff₀ hμ]
    have hsplit : (u / μ - u' / μ') * μ = (u - u') - u' / μ' * (μ - μ') := by
      linear_combination hX - hX'.1
    have habs : |u / μ - u' / μ'| * μ = |(u / μ - u' / μ') * μ| := by
      rw [abs_mul, abs_of_pos hμ]
    rw [habs, hsplit]
    have h1 : |u' / μ' * (μ - μ')| ≤ 3 / 4 * (4 * δ) := by
      rw [abs_mul]
      exact mul_le_mul hX'.2 hμμ (abs_nonneg _) (by norm_num)
    have h2 := abs_le.mp h1
    have h3 := abs_le.mp huu
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  -- Steps 3–5 for one coordinate: `|Φ(y)ᵢ − Φ(y')ᵢ| ≤ 4δ/κ(r(y))`
  have coord_bound : ∀ c b b' k k' δ : ℝ, |c - 1 / 2| < 1 / 4 → 0 < k → |b - b'| ≤ δ →
      |k - k'| ≤ 4 * δ →
      |(c + (b - c) / max (max ((b - c) / (1 - c)) ((c - b) / c)) k) -
        (c + (b' - c) / max (max ((b' - c) / (1 - c)) ((c - b') / c)) k')| ≤ 4 * δ / k := by
    intro c b b' k k' δ hc hk hbb hkk
    have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hbb
    have hr' : |b' - c| ≤ 3 / 4 * max ((b' - c) / (1 - c)) ((c - b') / c) := abs_le_r c b' hc
    have hr'0 : 0 ≤ max ((b' - c) / (1 - c)) ((c - b') / c) := by
      have := abs_nonneg (b' - c)
      linarith
    have hμk : k ≤ max (max ((b - c) / (1 - c)) ((c - b) / c)) k := le_max_right _ _
    have hμ : 0 < max (max ((b - c) / (1 - c)) ((c - b) / c)) k := lt_of_lt_of_le hk hμk
    have hμ' : max ((b' - c) / (1 - c)) ((c - b') / c)
        ≤ max (max ((b' - c) / (1 - c)) ((c - b') / c)) k' := le_max_left _ _
    have huu : |(b - c) - (b' - c)| ≤ δ := by
      rw [sub_sub_sub_cancel_right]
      exact hbb
    have hμμ : |max (max ((b - c) / (1 - c)) ((c - b) / c)) k
        - max (max ((b' - c) / (1 - c)) ((c - b') / c)) k'| ≤ 4 * δ :=
      le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le (r_lip c b b' δ hc hbb) hkk)
    have hu' : |b' - c| ≤ 3 / 4 * max (max ((b' - c) / (1 - c)) ((c - b') / c)) k' := by
      linarith
    rw [add_sub_add_left_eq_sub]
    exact le_trans (key _ _ _ _ _ hμ (le_trans hr'0 hμ') hu' huu hμμ)
      (div_le_div_of_nonneg_left (by linarith) hk hμk)
  have hi : ∀ i, |Φ y i - Φ y' i|
      ≤ 4 * dist y y' / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) := by
    intro i
    rw [hΦ y i, hΦ y' i]
    exact coord_bound _ _ _ _ _ _ (ha i) hk (hcoord i) hkk
  -- Step 5: sum the squares over the `P` coordinates
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (Φ y i) (Φ y' i) ^ 2)
      ≤ Real.sqrt (∑ _i : Fin P,
          (4 * dist y y' / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (hi i) 2
    _ = 4 * Real.sqrt P / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))
          * dist y y' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _),
          Real.sqrt_sq (div_nonneg (by positivity) hk.le)]
        ring
/-- **Lipschitz on every closed unit grid cube implies Lipschitz along segments** (Simon Ch. 6,
5.4, closed-form retraction, step 7(i)).  If `|f x − f y| ≤ K |x − y|` whenever `x, y ∈ S` lie in
a common closed cube `z + [0, 1]ᴾ` (`z ∈ ℤᴾ`), then `|f x − f y| ≤ K |x − y|` whenever
`[x, y] ⊆ S`.  With `γ(t) = x + t (y − x)`, the parameters `t ∈ [0, 1]` at which a non-constant
coordinate `γᵢ(t)` is an integer, together with `0` and `1`, are finitely many,
`0 = t₀ < ⋯ < t_N = 1`.  Between consecutive breakpoints no coordinate crosses an integer, so
`γ(t_k)` and `γ(t_{k+1})` lie in the cube `⌊γ(s)⌋ + [0, 1]ᴾ`, `s = (t_k + t_{k+1})/2`; the cube
estimates `K (t_{k+1} − t_k) |x − y|` telescope along the triangle inequality to `K |x − y|`. -/
theorem Submission.dor_lmb_fcdr_grid_segment : ∀ (P : ℕ) (f : Euclid P → Euclid P) (S : Set (Euclid P)) (K : ℝ), 0 ≤ K → (∀ (z : Fin P → ℤ) (x y : Euclid P), x ∈ S → y ∈ S → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) → dist (f x) (f y) ≤ K * dist x y) → ∀ x y : Euclid P, segment ℝ x y ⊆ S → dist (f x) (f y) ≤ K * dist x y := by
  intro P f S K hK hcube x y hseg
  -- Step 1: `γ t = x + t (y − x)`, `t ∈ [0, 1]`, parametrises `[x, y] ⊆ S`, and
  -- `|γ a − γ b| = |a − b| |x − y|`
  let γ : ℝ → Euclid P := fun t => x + t • (y - x)
  have hγi : ∀ t i, γ t i = x i + t * (y i - x i) := fun t i => by simp [γ]
  have hγS : ∀ t, 0 ≤ t → t ≤ 1 → γ t ∈ S := fun t h0 h1 =>
    hseg (by rw [segment_eq_image']; exact ⟨t, ⟨h0, h1⟩, rfl⟩)
  have hγdist : ∀ a b, dist (γ a) (γ b) = |a - b| * dist x y := by
    intro a b
    have h : γ a - γ b = (a - b) • (y - x) := by
      simp only [γ]; rw [add_sub_add_left_eq_sub, sub_smul]
    rw [dist_eq_norm (γ a) (γ b), h, norm_smul, Real.norm_eq_abs, ← dist_eq_norm y x,
      dist_comm y x]
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ 1 = y := by simp [γ]
  -- Step 2: the breakpoints `T ⊆ [0, 1]`: `0`, `1` and every `t` with `γᵢ(t) = m ∈ ℤ`,
  -- `xᵢ ≠ yᵢ`, i.e. `t = (m − xᵢ)/(yᵢ − xᵢ)` with `m ∈ [⌊min(xᵢ, yᵢ)⌋, ⌈max(xᵢ, yᵢ)⌉]` (for
  -- `xᵢ = yᵢ` this quotient is `0 ∈ T`) ...
  let B : Finset ℝ := Finset.univ.biUnion fun i : Fin P =>
    (Finset.Icc ⌊min (x i) (y i)⌋ ⌈max (x i) (y i)⌉).image fun m : ℤ =>
      ((m : ℝ) - x i) / (y i - x i)
  let T : Finset ℝ := (insert 0 (insert 1 B)).filter fun t => 0 ≤ t ∧ t ≤ 1
  have hmemT : ∀ u, u ∈ T ↔ (u = 0 ∨ u = 1 ∨ u ∈ B) ∧ 0 ≤ u ∧ u ≤ 1 := fun u =>
    Finset.mem_filter.trans <|
      and_congr_left' (Finset.mem_insert.trans (or_congr_right Finset.mem_insert))
  have hmemB : ∀ (i : Fin P) (m : ℤ), min (x i) (y i) < m → (m : ℝ) < max (x i) (y i) →
      ((m : ℝ) - x i) / (y i - x i) ∈ B := fun i m h1 h2 =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2 ⟨m,
      Finset.mem_Icc.2 ⟨Int.floor_le_iff.2 (by linarith), Int.le_ceil_iff.2 (by linarith)⟩, rfl⟩⟩
  have hT : ∀ u ∈ T, 0 ≤ u ∧ u ≤ 1 := fun u hu => ((hmemT u).1 hu).2
  have h0T : (0 : ℝ) ∈ T := (hmemT 0).2 ⟨Or.inl rfl, le_rfl, zero_le_one⟩
  have h1T : (1 : ℝ) ∈ T := (hmemT 1).2 ⟨Or.inr (Or.inl rfl), zero_le_one, le_rfl⟩
  -- ... listed increasingly as `0 = t 0 < t 1 < ⋯ < t N = 1`, `N = card T − 1`
  have hcard : 2 ≤ T.card := by
    have h := Finset.card_le_card (show ({0, 1} : Finset ℝ) ⊆ T by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact h0T
      · rw [Finset.mem_singleton.1 hu]; exact h1T)
    rwa [Finset.card_pair zero_ne_one] at h
  let e := T.orderEmbOfFin rfl
  let t : ℕ → ℝ := fun k => if h : k < T.card then e ⟨k, h⟩ else 1
  let N := T.card - 1
  have h0 : 0 < T.card := lt_of_lt_of_le two_pos hcard
  have hNlt : N < T.card := Nat.sub_lt h0 one_pos
  have ht0 : t 0 = 0 := by
    have : t 0 = e ⟨0, h0⟩ := dite_eq_left h0
    rw [this, Finset.orderEmbOfFin_zero rfl h0]
    exact le_antisymm (Finset.min'_le T 0 h0T) (Finset.le_min' T _ 0 fun u hu => (hT u hu).1)
  have htN : t N = 1 := by
    have : t N = e ⟨T.card - 1, hNlt⟩ := dite_eq_left hNlt
    rw [this, Finset.orderEmbOfFin_last rfl h0]
    exact le_antisymm (Finset.max'_le T _ 1 fun u hu => (hT u hu).2) (Finset.le_max' T 1 h1T)
  -- `t k < t (k + 1)` are consecutive breakpoints
  have hstep : ∀ k < N, t k ∈ T ∧ t (k + 1) ∈ T ∧ t k < t (k + 1) ∧
      ∀ u ∈ T, ¬(t k < u ∧ u < t (k + 1)) := by
    intro k hk
    have hk1 : k < T.card := hk.trans hNlt
    have hk2 : k + 1 < T.card := Nat.add_lt_of_lt_sub hk
    have htk : t k = e ⟨k, hk1⟩ := dite_eq_left hk1
    have htk' : t (k + 1) = e ⟨k + 1, hk2⟩ := dite_eq_left hk2
    rw [htk, htk']
    refine ⟨T.orderEmbOfFin_mem rfl _, T.orderEmbOfFin_mem rfl _,
      e.strictMono (Fin.mk_lt_mk.2 k.lt_succ_self), ?_⟩
    rintro u hu ⟨h1, h2⟩
    have hu' : u ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hu
    obtain ⟨j, rfl⟩ := hu'
    have h1' : k < j.val := Fin.lt_def.1 (e.lt_iff_lt.1 h1)
    have h2' : j.val < k + 1 := Fin.lt_def.1 (e.lt_iff_lt.1 h2)
    exact absurd h1' (not_lt.2 (Nat.lt_add_one_iff.1 h2'))
  -- Step 3: if no breakpoint lies strictly between `a < b`, no coordinate of `γ` passes strictly
  -- across an integer `m` on `[a, b]`: otherwise `(m − xᵢ)/(yᵢ − xᵢ)` would be such a breakpoint
  have hcross : ∀ a b, 0 ≤ a → b ≤ 1 → a < b → (∀ u ∈ T, ¬(a < u ∧ u < b)) →
      ∀ (i : Fin P) (m : ℤ), ¬(γ a i < m ∧ (m : ℝ) < γ b i) ∧ ¬(γ b i < m ∧ (m : ℝ) < γ a i) := by
    intro a b ha hb hab hgap i m
    have hbreak : a < ((m : ℝ) - x i) / (y i - x i) → ((m : ℝ) - x i) / (y i - x i) < b →
        min (x i) (y i) < m → (m : ℝ) < max (x i) (y i) → False := fun h1 h2 h3 h4 =>
      hgap _ ((hmemT _).2 ⟨Or.inr (Or.inr (hmemB i m h3 h4)), by linarith, by linarith⟩) ⟨h1, h2⟩
    simp only [hγi]
    constructor
    · rintro ⟨h1, h2⟩
      have hd : 0 < y i - x i := not_le.1 fun hd =>
        by linarith [mul_le_mul_of_nonpos_right hab.le hd]
      exact hbreak ((lt_div_iff₀ hd).2 (by linarith)) ((div_lt_iff₀ hd).2 (by linarith))
        (by linarith [min_le_left (x i) (y i), mul_nonneg ha hd.le])
        (by linarith [le_max_right (x i) (y i), mul_le_of_le_one_left hd.le hb])
    · rintro ⟨h1, h2⟩
      have hd : y i - x i < 0 := not_le.1 fun hd =>
        by linarith [mul_le_mul_of_nonneg_right hab.le hd]
      exact hbreak ((lt_div_iff_of_neg hd).2 (by linarith)) ((div_lt_iff_of_neg hd).2 (by linarith))
        (by linarith [min_le_right (x i) (y i), mul_nonneg (sub_nonneg.2 hb) (neg_nonneg.2 hd.le)])
        (by linarith [le_max_left (x i) (y i), mul_nonneg ha (neg_nonneg.2 hd.le)])
  -- Steps 3–4: each piece `γ(t k), γ(t (k + 1))` lies in the closed cube `z + [0, 1]ᴾ`,
  -- `z = ⌊γ(midpoint)⌋`, so the cube estimate bounds it by `K (t (k + 1) − t k) |x − y|`
  have key : ∀ k < N,
      dist (f (γ (t k))) (f (γ (t (k + 1)))) ≤ K * dist x y * (t (k + 1) - t k) := by
    intro k hk
    obtain ⟨haT, hbT, hab, hgap⟩ := hstep k hk
    set a := t k
    set b := t (k + 1)
    obtain ⟨ha0, ha1⟩ := hT a haT
    obtain ⟨hb0, hb1⟩ := hT b hbT
    let z : Fin P → ℤ := fun i => ⌊γ ((a + b) / 2) i⌋
    have hz : ∀ i, ((z i : ℝ) ≤ γ a i ∧ γ a i ≤ z i + 1) ∧
        ((z i : ℝ) ≤ γ b i ∧ γ b i ≤ z i + 1) := by
      intro i
      have hmid : γ ((a + b) / 2) i = (γ a i + γ b i) / 2 := by rw [hγi, hγi, hγi]; ring
      have hz1 : (z i : ℝ) ≤ (γ a i + γ b i) / 2 := hmid ▸ Int.floor_le _
      have hz2 : (γ a i + γ b i) / 2 < z i + 1 := hmid ▸ Int.lt_floor_add_one _
      obtain ⟨hc1, hc2⟩ := hcross a b ha0 hb1 hab hgap i (z i)
      obtain ⟨hd1, hd2⟩ := hcross a b ha0 hb1 hab hgap i (z i + 1)
      rw [Int.cast_add, Int.cast_one] at hd1 hd2
      exact ⟨⟨not_lt.1 fun h => hc1 ⟨h, by linarith⟩, not_lt.1 fun h => hd2 ⟨by linarith, h⟩⟩,
        not_lt.1 fun h => hc2 ⟨h, by linarith⟩, not_lt.1 fun h => hd1 ⟨by linarith, h⟩⟩
    calc dist (f (γ a)) (f (γ b)) ≤ K * dist (γ a) (γ b) :=
          hcube z (γ a) (γ b) (hγS a ha0 ha1) (hγS b hb0 hb1) (fun i => (hz i).1) fun i => (hz i).2
      _ = K * dist x y * (b - a) := by
          rw [hγdist, abs_sub_comm, abs_of_pos (sub_pos.2 hab)]; ring
  -- Step 5: triangle inequality along `γ(t 0), …, γ(t N)`, then telescoping
  calc dist (f x) (f y) = dist (f (γ (t 0))) (f (γ (t N))) := by rw [ht0, htN, hγ0, hγ1]
    _ ≤ ∑ k ∈ Finset.range N, dist (f (γ (t k))) (f (γ (t (k + 1)))) :=
        dist_le_range_sum_dist (fun k => f (γ (t k))) N
    _ ≤ ∑ k ∈ Finset.range N, K * dist x y * (t (k + 1) - t k) :=
        Finset.sum_le_sum fun k hk => key k (Finset.mem_range.1 hk)
    _ = K * dist x y * (t N - t 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ = K * dist x y := by rw [ht0, htN]; ring
/-- **Simon Ch. 6, Lemma 5.4** (retraction onto the `n`-skeleton, `n = m + 1 < P`; the printed
construction, with the derivative bound proved directly).  Let `|aᵢ − 1/2| < 1/4`, `L*(a)` the set
of points with at least `m + 2` coordinates in `aᵢ + ℤ`, `rⱼ(y) = max((yⱼ − aⱼ)/(1 − aⱼ),
(aⱼ − yⱼ)/aⱼ)`, `κ` the `ℓ`-th largest entry (`ℓ = P − (m + 1)`),
`Φ(y)ᵢ = aᵢ + (yᵢ − aᵢ)/max(rᵢ(y), κ(r(y)))` the closed form of the composed radial retractions of
`[0, 1]ᴾ`, and `ψ(x) = ⌊x⌋ + Φ(x − ⌊x⌋)`.  Off `L*(a)`, `κ(r(x − ⌊x⌋)) > 0` (Claim C), so `ψ(x)`
has `ℓ` integer coordinates and `|ψ(x) − x| ≤ √P`.  On a grid cube `z + [0, 1]ᴾ`,
`ψ = z + Φ(· − z)` by periodicity, and Claims B and C bound its Lipschitz constant on
`{dist(·, L*(a)) ≥ r/2}` by `4√P/κ ≤ 2c₁/r`, `c₁ = 4√P √(m + 2)`.  If `|x − y| < r`, the segment
`[x, y]` stays in `{dist(·, L*(a)) ≥ r/2}` and cutting it at the grid gives `(2c₁/r)|x − y|`; if
`|x − y| ≥ r`, then `|ψ(x) − ψ(y)| ≤ |x − y| + 2√P ≤ ((1/4 + 2√P)/r)|x − y|`.  So
`c = 2c₁ + 2√P + 1/4` works. -/
theorem Submission.dor_lmb_fcd_retraction : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y := by
  intro P m hmP
  -- Step 2: `κ`, the `ℓ`-th largest entry, `ℓ = P − (m + 1)`
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := Submission.dor_lmb_fcdr_order_stat P m hmP
  -- `c = 2c₁ + 2√P + 1/4 ≥ max(2c₁, 1/4 + 2√P)`, `c₁ = 4√P √(m + 2)`
  refine ⟨8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4, by positivity,
    fun a ha => ?_⟩
  set L : Set (Euclid P) := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
    ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  have hsP := Real.sqrt_nonneg (P : ℝ)
  have hsm := Real.sqrt_nonneg ((m : ℝ) + 2)
  -- Step 3: the closed-form cube map `Φ`
  let Φ : Euclid P → Euclid P := fun y => WithLp.toLp 2 fun i => a i + (y i - a i) /
    max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i))
      (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))
  have hΦ : ∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) /
      max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i))
        (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))) := fun _ _ => rfl
  -- integer points `z ∈ ℤᴾ` of `ℝᴾ`, and Step 5: `ψ(x) = ⌊x⌋ + Φ(x − ⌊x⌋)`
  let zv : (Fin P → ℤ) → Euclid P := fun z => WithLp.toLp 2 fun i => (z i : ℝ)
  let ψ : Euclid P → Euclid P := fun x => zv (fun j => ⌊x j⌋) + Φ (x - zv (fun j => ⌊x j⌋))
  have hψ : ∀ x i, ψ x i = ⌊x i⌋ + Φ (x - zv (fun j => ⌊x j⌋)) i := fun _ _ => rfl
  have hint : ∀ (z : Fin P → ℤ) (x : Euclid P) (i : Fin P), ∃ k : ℤ, x i - (x - zv z) i = k :=
    fun z x i => ⟨z i, show x i - (x i - z i) = z i by ring⟩
  -- Claim C: `dist(x, L*(a)) ≤ √(m + 2) κ(r(y))` if `x − y ∈ ℤᴾ`; so `κ(r(y)) > 0` off `L*(a)`
  have hdual : ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) →
      infDist x L ≤ Real.sqrt (m + 2) *
        κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) :=
    Submission.dor_lmb_fcdr_dual_dist P m a ha κ hκ2
  have hκpos : ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) → 0 < infDist x L →
      0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) := by
    intro x y hxy hx
    by_contra hneg
    have h := mul_nonpos_of_nonneg_of_nonpos hsm (not_lt.1 hneg)
    linarith [hdual x y hxy]
  -- Step 5: on a grid cube `z + [0, 1]ᴾ`, `ψ = z + Φ(· − z)` (periodicity of `Φ`)
  have hψcube : ∀ (z : Fin P → ℤ) (x : Euclid P), (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) →
      ψ x = zv z + Φ (x - zv z) := by
    intro z x hx
    have hper := Submission.dor_lmb_fcdr_cube_periodic P m hmP a ha κ hκ1 Φ hΦ
      (x - zv (fun j => ⌊x j⌋)) (x - zv z)
      (fun j => show 0 ≤ x j - ⌊x j⌋ ∧ x j - ⌊x j⌋ ≤ 1 from
        ⟨by linarith [Int.floor_le (x j)], by linarith [Int.lt_floor_add_one (x j)]⟩)
      (fun j => show 0 ≤ x j - z j ∧ x j - z j ≤ 1 from
        ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩)
      (fun j => ⟨⌊x j⌋ - z j, show (x j - z j) - (x j - ⌊x j⌋) = ((⌊x j⌋ - z j : ℤ) : ℝ) by
        push_cast; ring⟩)
    ext i
    show (⌊x i⌋ : ℝ) + Φ (x - zv (fun j => ⌊x j⌋)) i = z i + Φ (x - zv z) i
    rw [hper i]
    show (⌊x i⌋ : ℝ) + Φ (x - zv (fun j => ⌊x j⌋)) i
      = z i + (Φ (x - zv (fun j => ⌊x j⌋)) i + ((x i - z i) - (x i - ⌊x i⌋)))
    ring
  -- Step 5: the first conclusion
  have hfirst : ∀ x : Euclid P, 0 < infDist x L →
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧
        dist (ψ x) x ≤ Real.sqrt P := by
    intro x hx
    obtain ⟨h01, s, hs, hs01⟩ := Submission.dor_lmb_fcdr_cube_skeleton P m a ha κ hκ1 Φ hΦ
      (x - zv (fun j => ⌊x j⌋)) (hκpos x _ (hint _ x) hx)
    refine ⟨⟨s, hs, fun i hi => ?_⟩, ?_⟩
    · -- `Φ(x − ⌊x⌋)ᵢ ∈ {0, 1}` on `s`
      rcases hs01 i hi with h | h
      · exact ⟨⌊x i⌋, by rw [hψ, h, add_zero]⟩
      · exact ⟨⌊x i⌋ + 1, by rw [hψ, h]; push_cast; ring⟩
    · -- `|ψ(x)ᵢ − xᵢ| = |Φ(x − ⌊x⌋)ᵢ − (xᵢ − ⌊xᵢ⌋)| ≤ 1`
      rw [EuclideanSpace.dist_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, dist (ψ x i) (x i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := h01 i
            have h2 := Int.floor_le (x i)
            have h3 := Int.lt_floor_add_one (x i)
            have h5 : |ψ x i - x i| ≤ 1 := by
              rw [hψ, abs_le]
              constructor <;> linarith [h1.1, h1.2]
            rw [Real.dist_eq]
            calc |ψ x i - x i| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
              _ = 1 := one_pow 2
        _ = P := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Claims B and C on a grid cube: `|ψ(p) − ψ(q)| ≤ (4√P/κ) |p − q| ≤ (c/r) |p − q|` when
  -- `dist(p, L*(a)) ≥ r/2`
  have hcubeLip : ∀ r : ℝ, 0 < r → ∀ (z : Fin P → ℤ) (p q : Euclid P), r / 2 ≤ infDist p L →
      (∀ i, (z i : ℝ) ≤ p i ∧ p i ≤ z i + 1) → (∀ i, (z i : ℝ) ≤ q i ∧ q i ≤ z i + 1) →
      dist (ψ p) (ψ q) ≤
        (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r * dist p q := by
    intro r hr z p q hp hpz hqz
    have hk := hκpos p (p - zv z) (hint z p) (by linarith)
    have hd := hdual p (p - zv z) (hint z p)
    have hB := Submission.dor_lmb_fcdr_cube_lipschitz P a ha κ hκ3 Φ hΦ (p - zv z) (q - zv z) hk
    rw [dist_sub_right p q (zv z)] at hB
    rw [hψcube z p hpz, hψcube z q hqz, dist_add_left]
    refine hB.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    -- `4√P/κ ≤ 8√P√(m + 2)/r ≤ c/r`, as `r ≤ 2√(m + 2) κ`
    have key : ∀ k : ℝ, 0 < k → r / 2 ≤ Real.sqrt (m + 2) * k →
        4 * Real.sqrt P / k ≤
          (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r := by
      intro k hk hrk
      rw [div_le_div_iff₀ hk hr]
      nlinarith [mul_nonneg hsP (by linarith : (0 : ℝ) ≤ 2 * (Real.sqrt (m + 2) * k) - r),
        mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt P + 1 / 4) hk.le]
    exact key _ hk (hp.trans hd)
  -- `[x, y] ⊆ ℝᴾ`: `|x − p| + |y − p| ≤ |x − y|` for `p ∈ [x, y]`
  have hseg : ∀ x y p : Euclid P, p ∈ segment ℝ x y → dist x p + dist y p ≤ dist x y := by
    intro x y p hp
    rw [segment_eq_image'] at hp
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := hp
    have hθ' : x + θ • (y - x) = p := hθ
    have e1 : x - p = (-θ) • (y - x) := by rw [← hθ', neg_smul]; abel
    have e2 : y - p = (1 - θ) • (y - x) := by rw [← hθ', sub_smul, one_smul]; abel
    rw [dist_eq_norm x p, dist_eq_norm y p, e1, e2, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg hθ0, abs_of_nonneg (sub_nonneg.2 hθ1),
      dist_comm, dist_eq_norm]
    linarith
  refine ⟨ψ, hfirst, fun r hr hr4 x y hx hy => ?_⟩
  have hc0 : 0 ≤ (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r := by
    positivity
  rcases lt_or_ge (dist x y) r with hxy | hxy
  · -- Step 7(i): `|x − y| < r`, so `dist(·, L*(a)) ≥ r/2` on `[x, y]`; cut `[x, y]` at the grid
    refine Submission.dor_lmb_fcdr_grid_segment P ψ {p | r / 2 ≤ infDist p L} _ hc0
      (fun z p q hp _ hpz hqz => hcubeLip r hr z p q hp hpz hqz) x y fun p hp => ?_
    show r / 2 ≤ infDist p L
    have h1 : infDist x L ≤ infDist p L + dist x p := infDist_le_infDist_add_dist
    have h2 : infDist y L ≤ infDist p L + dist y p := infDist_le_infDist_add_dist
    linarith [hseg x y p hp]
  · -- Step 7(ii): `|x − y| ≥ r`, so `|ψ(x) − ψ(y)| ≤ |x − y| + 2√P ≤ (c/r)|x − y|`
    have h1 := (hfirst x (by linarith)).2
    have h2 := (hfirst y (by linarith)).2
    have h3 := dist_triangle4 (ψ x) x y (ψ y)
    rw [dist_comm y (ψ y)] at h3
    have hd : 0 ≤ dist x y := dist_nonneg
    calc dist (ψ x) (ψ y) ≤ dist x y + 2 * Real.sqrt P := by linarith
      _ ≤ (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        nlinarith [mul_nonneg hsP (sub_nonneg.2 hxy),
          mul_nonneg hd (by linarith : (0 : ℝ) ≤ 1 / 4 - r), mul_nonneg (mul_nonneg hsP hsm) hd]
/-- **Tube about the shifted dual skeleton** (Simon Ch. 6, proof of 5.1, the identity before
display (6), inclusion `⊆`).  Let `L*(a)` be the set of `w` with `w_i − a_i ∈ ℤ` for at least
`m + 2` indices `i`.  It contains `a`, so `infDist x L*(a) < r` gives `w ∈ L*(a)` with
`|x − w| < r`.  Enumerate `m + 2` of the indices of `w` by `e`, and put
`z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`.  Then
`Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k (x_{e(k)} − w_{e(k)})² ≤ |x − w|² < r²`. -/
theorem Submission.dor_lmb_fcd_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
  classical
  intro P m hPm a x r hx
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- Steps 1–2: `a ∈ L*(a)` (all `P ≥ m + 2` indices), so some `w ∈ L*(a)` has `|x − w| < r`
  have hne : L.Nonempty := ⟨a, Finset.univ, by simp; omega, fun i _ => ⟨0, by simp⟩⟩
  obtain ⟨w, ⟨s, hs, hsz⟩, hxw⟩ := (infDist_lt_iff hne).1 hx
  -- Step 3: `m + 2` of the indices in `s`, enumerated injectively by `e`
  obtain ⟨J, hJs, hJ⟩ := Finset.exists_subset_card_eq hs
  let e : Fin (m + 2) → Fin P := fun k => J.orderEmbOfFin hJ k
  have he : Function.Injective e := (J.orderEmbOfFin hJ).injective
  have hes : ∀ k, e k ∈ s := fun k => hJs (J.orderEmbOfFin_mem hJ k)
  -- Step 4: `z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`
  choose z hz using fun k => hsz (e k) (hes k)
  refine ⟨e, he, z, ?_⟩
  have hterm : ∀ k, x (e k) - a (e k) - z k = x (e k) - w (e k) := fun k => by
    rw [← hz k]; ring
  -- Step 5: the `m + 2` selected squares are among the `P` nonnegative squares
  have hsub : ∑ k, (x (e k) - w (e k)) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    have := Finset.sum_map Finset.univ ⟨e, he⟩ (fun i => (x i - w i) ^ 2)
    simp only [Function.Embedding.coeFn_mk] at this
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  -- Step 6: `Σ_i (x_i − w_i)² = |x − w|²`
  have hdist : ∑ i, (x i - w i) ^ 2 = dist x w ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.dist_eq, sq_abs]
  have h0 : 0 ≤ dist x w := dist_nonneg
  -- Step 7
  calc ∑ k, (x (e k) - a (e k) - z k) ^ 2 = ∑ k, (x (e k) - w (e k)) ^ 2 := by
        simp_rw [hterm]
    _ ≤ ∑ i, (x i - w i) ^ 2 := hsub
    _ = dist x w ^ 2 := hdist
    _ < r ^ 2 := by nlinarith
/-- **Simon, Ch. 6, proof of 5.1** ((1)–(4) and the summation after them: the bad set of centres
is small).  Let `ρ` be a finite measure on `ℝᵈ` and `β > 0`.  Call a centre `g` of the open cube
`(1/4, 3/4)ᵈ` bad if `β rᵈ ρ(ℝᵈ) < ρ(O_r(g))` for some `r ∈ (0, 1/4]`, where
`O_r(g) = {y : |y − g − z| < r for some z ∈ ℤᵈ}` is the open `r`-neighbourhood of `g + ℤᵈ`.  Then
the bad set has Lebesgue measure at most `10ᵈ/β`.  Vitali's covering lemma gives bad centres `b`
with pairwise disjoint sup-metric balls `B(b, r_b)` such that the balls `B(b, 3r_b)` cover the bad
set.  The sets `O_{r_b}(b)` are then pairwise disjoint as well, so `Σ_b β r_bᵈ ≤ 1`, and the
bad set has measure at most `Σ_b (6r_b)ᵈ ≤ 6ᵈ/β`. -/
theorem Submission.dor_lmb_fcd_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)}
  -- step 1: the periodic sets `O_r(g)` are open
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- step 2: if `ρ(ℝᵈ) = 0` the bad set is empty
  by_cases h0 : ρ univ = 0
  · have : Bad = ∅ := by
      ext g
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨-, r, -, -, hr⟩
      rw [h0, mul_zero, measure_mono_null (subset_univ _) h0] at hr
      exact lt_irrefl _ hr
    rw [this, measure_empty]
    exact bot_le
  have hfin : ρ univ ≠ ∞ := measure_ne_top ρ univ
  -- step 3: a radius `r_g` for every bad centre `g`
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- step 4: Vitali's covering lemma for the balls `B(g, r_g)`, with `τ = 2`
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- step 5: `u` is countable
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- step 6: the balls `B(b, 3 r_b)`, `b ∈ u`, cover the bad set
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- step 7: the periodic sets `O_{r_b}(b)`, `b ∈ u`, are pairwise disjoint
  have hcoord : ∀ (y g : Fin d → ℝ) (r : ℝ) (z : Fin d → ℤ),
      ∑ k, (y k - g k - z k) ^ 2 < r ^ 2 → 0 < r → ∀ k, |y k - g k - z k| < r := by
    intro y g r z h hr k
    have hk : (y k - g k - z k) ^ 2 < r ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (y i - g i - z i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)) h
    exact abs_lt_of_sq_lt_sq hk hr.le
  have hOdisj : u.PairwiseDisjoint fun b => O b (rad b) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨z', hz'⟩
    have hb0 := hrad0 b (huBad hb)
    have hb'0 := hrad0 b' (huBad hb')
    have h1 := hcoord y b (rad b) z hz hb0
    have h2 := hcoord y b' (rad b') z' hz' hb'0
    have hr1 := hrad1 b (huBad hb)
    have hr2 := hrad1 b' (huBad hb')
    -- the centres lie in `(1/4, 3/4)ᵈ` and the radii are `≤ 1/4`, so the integer shifts agree
    have hzz : z = z' := by
      funext k
      have a1 := abs_lt.1 (h1 k)
      have a2 := abs_lt.1 (h2 k)
      have a3 := abs_lt.1 ((huBad hb).1 k)
      have a4 := abs_lt.1 ((huBad hb').1 k)
      have c1 : (z k : ℝ) < z' k + 1 := by linarith
      have c2 : (z' k : ℝ) < z k + 1 := by linarith
      have c1' : z k < z' k + 1 := by exact_mod_cast c1
      have c2' : z' k < z k + 1 := by exact_mod_cast c2
      omega
    subst hzz
    -- then `y − z` lies in both balls `B(b, r_b)` and `B(b', r_{b'})`
    have hv : (fun k => y k - z k) ∈ ball b (rad b) ∩ ball b' (rad b') := by
      constructor
      · rw [mem_ball, dist_pi_lt_iff hb0]
        intro k
        rw [Real.dist_eq]
        have := h1 k
        rwa [show y k - z k - b k = y k - b k - z k by ring]
      · rw [mem_ball, dist_pi_lt_iff hb'0]
        intro k
        rw [Real.dist_eq]
        have := h2 k
        rwa [show y k - z k - b' k = y k - b' k - z k by ring]
    exact (Set.disjoint_left.1 (hudisj hb hb' hne)) hv.1 hv.2
  -- step 8: `S = Σ_{b ∈ u} β r_bᵈ ≤ 1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d)
  have hSle : S ≤ 1 := by
    have hsum : S * ρ univ ≤ 1 * ρ univ := by
      calc S * ρ univ = ∑' b : u, ENNReal.ofReal (β * rad b ^ d) * ρ univ :=
            (ENNReal.tsum_mul_right).symm
        _ ≤ ∑' b : u, ρ (O b (rad b)) :=
            ENNReal.tsum_le_tsum fun b => (hradlt b (huBad b.2)).le
        _ = ρ (⋃ b ∈ u, O b (rad b)) :=
            (measure_biUnion hucount hOdisj fun b _ => (hOopen _ _).measurableSet).symm
        _ ≤ ρ univ := measure_mono (subset_univ _)
        _ = 1 * ρ univ := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left h0 hfin).1 hsum
  -- step 9: the volume estimate
  calc volume Bad ≤ volume (⋃ b ∈ u, ball b (3 * rad b)) := measure_mono hBadsub
    _ ≤ ∑' b : u, volume (ball (b : Fin d → ℝ) (3 * rad b)) := measure_biUnion_le _ hucount _
    _ = ∑' b : u, ENNReal.ofReal (6 ^ d / β) * ENNReal.ofReal (β * rad b ^ d) := by
        refine tsum_congr fun b => ?_
        have hb0 := hrad0 b (huBad b.2)
        rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (6 ^ d / β) * S := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (6 ^ d / β) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (10 ^ d / β) := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        norm_num
/-- **Simon, Ch. 6, proof of 5.1** ((5) and the choice of `a`, cube version).  If sets
`E_e ⊆ ℝ^d`, one for each map `e : Fin d → Fin P`, have total Lebesgue outer measure
`< (1/2)^P`, then some `a` in the open cube `(1/4, 3/4)^P` has `(a_{e(k)})_k ∉ E_e` for every
injective `e`.  By Fubini over the coordinates in `range e` and the rest, the centres in the cube
whose `e`-projection lies in `E_e` have volume `≤ L^d(E_e)`; the cube has volume `(1/2)^P`, so the
union bound leaves a good centre. -/
theorem Submission.dor_lmb_fcd_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
  classical
  intro P d E hsum
  -- Step 2 (Fubini): for injective `e`, the points of the cube whose `e`-projection lies in `F`
  -- have volume at most `volume F`
  have fubini : ∀ e : Fin d → Fin P, Function.Injective e → ∀ F : Set (Fin d → ℝ),
      volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ≤
        volume F := by
    intro e he F
    let p : Fin P → Prop := fun i => i ∈ range e
    let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    have hΦ : MeasurePreserving Φ := by
      convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    let σ : Fin d ≃ {i // p i} := Equiv.ofInjective e he
    let ψ := (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm
    have hψ : MeasurePreserving ψ :=
      (volume_measurePreserving_piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm _
    have hψapp : ∀ u k, ψ u k = u (σ k) := by
      intro u k
      simp [ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    let G : Set ({i // p i} → ℝ) := ψ ⁻¹' F
    let H : Set ({i // ¬ p i} → ℝ) := Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)
    have hsub : {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ⊆
        Φ ⁻¹' (G ×ˢ H) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, fun i _ => hx1 i⟩
      show ψ (fun i => x i) ∈ F
      have : ψ (fun i : {i // p i} => x i) = fun k => x (e k) := by
        funext k; rw [hψapp]; rfl
      rw [this]; exact hx2
    have hG : volume G = volume F := hψ.measure_preimage_equiv F
    have hH : volume H ≤ 1 := by
      rw [Real.volume_pi_Ioo]
      refine Finset.prod_le_one fun i _ => ?_
      rw [ENNReal.ofReal_le_one]; norm_num
    calc volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F}
        ≤ volume (Φ ⁻¹' (G ×ˢ H)) := measure_mono hsub
      _ = volume (G ×ˢ H) := hΦ.measure_preimage_equiv _
      _ = volume G * volume H := by
          rw [Measure.volume_eq_prod]; exact Measure.prod_prod G H
      _ ≤ volume G * 1 := by gcongr
      _ = volume F := by rw [mul_one, hG]
  have hI : ∀ t : ℝ, |t - 1 / 2| < 1 / 4 ↔ t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro t
    rw [abs_sub_lt_iff, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- Step 1: the open cube `Q` in `Euclid P` has volume `(1/2)^P`
  let Q : Set (Euclid P) := {a | ∀ i, a i ∈ Ioo (1 / 4 : ℝ) (3 / 4)}
  have hofLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin P)
  have hQ : volume Q = ENNReal.ofReal ((1 / 2) ^ P) := by
    have : Q = (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
        (Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext a; simp [Q, Set.mem_pi]
    rw [this, hofLp.measure_preimage_equiv, Real.volume_pi_Ioo, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  -- Step 3: the sets of centres with a bad projection
  let A : (Fin d → Fin P) → Set (Euclid P) := fun e =>
    {a | Function.Injective e ∧ a ∈ Q ∧ (fun k => a (e k)) ∈ E e}
  have hA : ∀ e, volume (A e) ≤ volume (E e) := by
    intro e
    by_cases he : Function.Injective e
    · have hsub : A e ⊆ (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
          {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ E e} := by
        rintro a ⟨-, haQ, haE⟩
        exact ⟨haQ, haE⟩
      calc volume (A e) ≤ _ := measure_mono hsub
        _ = _ := hofLp.measure_preimage_equiv _
        _ ≤ volume (E e) := fubini e he (E e)
    · have : A e = ∅ := by
        ext a; simp only [mem_empty_iff_false, iff_false]; exact fun h => he h.1
      rw [this, measure_empty]; exact bot_le
  -- Steps 4–5: union bound and choice of `a`
  by_contra hcon
  push Not at hcon
  have hcov : Q ⊆ ⋃ e, A e := by
    intro a haQ
    obtain ⟨e, he, haE⟩ := hcon a fun i => (hI _).2 (haQ i)
    exact mem_iUnion.2 ⟨e, he, haQ, haE⟩
  have : volume Q < volume Q :=
    calc volume Q ≤ volume (⋃ e, A e) := measure_mono hcov
      _ ≤ ∑ e, volume (A e) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ e, volume (E e) := Finset.sum_le_sum fun e _ => hA e
      _ < ENNReal.ofReal ((1 / 2) ^ P) := hsum
      _ = volume Q := hQ.symm
  exact lt_irrefl _ this
/-- **Simon, Ch. 6, proof of 5.1** (choice of the centre `a`, (5)–(7)).  Put `d = m + 2`,
`K = #(Fin d → Fin P)`, `β = 2K·10ᵈ·2ᴾ + 1` and `C = Kβ`.  For each `e : Fin d → Fin P` let
`E_e` be the union of the bad sets of centres of the image measures of `μ` and `μ'` under
`x ↦ (x_{e(k)})_k`.  Each bad set has volume `≤ 10ᵈ/β`, so `Σ_e |E_e| < (1/2)ᴾ` and the cube
selection gives `a` with `(a_{e(k)})_k ∉ E_e` for every injective `e`.  The `r`-tube about
`L*(a)` lies in the union over injective `e` of the preimages of the periodic
`r`-neighbourhoods of `(a_{e(k)})_k`, each of `ν`-measure `≤ β rᵈ ν(ℝᴾ)` for `ν = μ, μ'`; hence
`ν(tube) ≤ Kβ rᵈ ν(ℝᴾ)`. -/
theorem Submission.dor_lmb_fcd_good_center : ∀ (P m : ℕ), m + 1 < P → ∃ C : NNReal, ∀ μ μ' : Measure (Euclid P), IsFiniteMeasure μ → IsFiniteMeasure μ' → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ univ ∧ μ' {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ' univ := by
  have c1 := Submission.dor_lmb_fcd_gc_tube_cover
  have c2 := Submission.dor_lmb_fcd_gc_bad_set_volume
  have c3 := Submission.dor_lmb_fcd_gc_cube_selection
  classical
  intro P m hPm
  -- Step 4: the constants `β` and `C = Kβ`, depending only on `P` and `m`
  set K : ℕ := Fintype.card (Fin (m + 2) → Fin P) with hK
  set β : ℝ := 2 * K * 10 ^ (m + 2) * 2 ^ P + 1 with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨Real.toNNReal (K * β), ?_⟩
  intro μ μ' hμ hμ'
  -- the coordinate projections `x ↦ (x_{e(k)})_k`
  let prj : (Fin (m + 2) → Fin P) → Euclid P → (Fin (m + 2) → ℝ) := fun e x k => x (e k)
  have hprj : ∀ e, Measurable (prj e) := fun e =>
    (continuous_pi fun k => PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (e k)).measurable
  -- the bad sets of centres of the projected measures (steps 2–3)
  let Bad : Measure (Fin (m + 2) → ℝ) → Set (Fin (m + 2) → ℝ) := fun ρ =>
    {g | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ (m + 2)) * ρ univ <
        ρ {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}}
  let E : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
    Bad (μ.map (prj e)) ∪ Bad (μ'.map (prj e))
  have hE : ∀ e, volume (E e) ≤ 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := by
    intro e
    calc volume (E e) ≤ volume (Bad (μ.map (prj e))) + volume (Bad (μ'.map (prj e))) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (10 ^ (m + 2) / β) + ENNReal.ofReal (10 ^ (m + 2) / β) :=
          add_le_add (c2 (m + 2) _ inferInstance β hβpos) (c2 (m + 2) _ inferInstance β hβpos)
      _ = 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := (two_mul _).symm
  -- the exceptional sets do not exhaust the cube
  have hsum : ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) := by
    calc ∑ e, volume (E e) ≤ ∑ _e : Fin (m + 2) → Fin P, 2 * ENNReal.ofReal (10 ^ (m + 2) / β) :=
          Finset.sum_le_sum fun e _ => hE e
      _ = ENNReal.ofReal (2 * K * 10 ^ (m + 2) / β) := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal ((1 / 2) ^ P) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), div_lt_iff₀ hβpos, hβ]
          have h2 : ((1 : ℝ) / 2) ^ P * 2 ^ P = 1 := by
            rw [← mul_pow]; norm_num
          have h3 : (0 : ℝ) < (1 / 2) ^ P := by positivity
          have h4 : ((1 : ℝ) / 2) ^ P * (2 * K * 10 ^ (m + 2) * 2 ^ P + 1) =
              2 * K * 10 ^ (m + 2) * ((1 / 2) ^ P * 2 ^ P) + (1 / 2) ^ P := by ring
          rw [h4, h2]
          linarith
  -- choice of a good centre `a` for both measures
  obtain ⟨a, ha, hgood⟩ := c3 P (m + 2) E hsum
  refine ⟨a, ha, ?_⟩
  intro r hr0 hr1
  -- Step 5: the estimate for any finite `ν` for which `a` is good
  have key : ∀ ν : Measure (Euclid P), IsFiniteMeasure ν →
      (∀ e : Fin (m + 2) → Fin P, Function.Injective e → prj e a ∉ Bad (ν.map (prj e))) →
      ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤
        (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
    intro ν hν hνgood
    let O : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
      {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - prj e a k - z k) ^ 2 < r ^ 2}
    let T : (Fin (m + 2) → Fin P) → Set (Euclid P) := fun e =>
      {x | Function.Injective e ∧ prj e x ∈ O e}
    -- step 1: the `r`-tube about `L*(a)` lies in the periodic coordinate cylinders
    have hcover : {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ⊆ ⋃ e, T e := by
      intro x hx
      obtain ⟨e, he, z, hz⟩ := c1 P m hPm a x r hx
      exact mem_iUnion.2 ⟨e, he, z, hz⟩
    -- each cylinder family has `ν`-measure `≤ β rᵈ ν(ℝᴾ)`, since `a` is good
    have hT : ∀ e, ν (T e) ≤ ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
      intro e
      by_cases he : Function.Injective e
      · have hsub : T e ⊆ prj e ⁻¹' O e := fun x hx => hx.2
        have hcube : ∀ k, |prj e a k - 1 / 2| < 1 / 4 := fun k => ha (e k)
        have hnot := hνgood e he
        have hle : (ν.map (prj e)) (O e) ≤
            ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := by
          by_contra hlt
          exact hnot ⟨hcube, r, hr0, hr1, not_le.1 hlt⟩
        calc ν (T e) ≤ ν (prj e ⁻¹' O e) := measure_mono hsub
          _ ≤ (ν.map (prj e)) (O e) := Measure.le_map_apply (hprj e).aemeasurable _
          _ ≤ ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := hle
          _ = ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
              rw [Measure.map_apply (hprj e) MeasurableSet.univ, preimage_univ]
      · have : T e = ∅ := by
          ext x
          simp only [mem_empty_iff_false, iff_false]
          exact fun hx => he hx.1
        rw [this, measure_empty]
        exact bot_le
    -- subadditivity over the `K` maps `e`
    calc ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
          ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ ν (⋃ e, T e) := measure_mono hcover
      _ ≤ ∑ e, ν (T e) := measure_iUnion_fintype_le ν T
      _ ≤ ∑ _e : Fin (m + 2) → Fin P, ENNReal.ofReal (β * r ^ (m + 2)) * ν univ :=
          Finset.sum_le_sum fun e _ => hT e
      _ = (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            show ((Real.toNNReal (K * β) : ℝ≥0∞)) = ENNReal.ofReal (K * β) from rfl,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact ⟨key μ hμ fun e he h => hgood e he (Or.inl h),
    key μ' hμ' fun e he h => hgood e he (Or.inr h)⟩
/-- **Simon Ch. 3, Lemma 1.2 and Remark 1.3**, with bi-Lipschitz Borel pieces in place of `C¹`
submanifolds: a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null set, the disjoint
union of Borel sets `Fᵢ(Bᵢ) ⊆ M`, where `Fᵢ : ℝⁿ → ℝᴾ` is Lipschitz, `Bᵢ` is Borel,
`mᵢ|a − a'| ≤ |Fᵢ(a) − Fᵢ(a')|` on `Bᵢ` for some `mᵢ > 0`, and `DFᵢ` exists and is injective on
`Bᵢ`.  Each Lipschitz `Fⱼ` of the cover maps its non-differentiability points (Rademacher) and
its critical points (the image of `{JFⱼ = 0}`) to `Hⁿ`-null sets.  Mathlib's partition lemma cuts
the regular points into pieces on which `Fⱼ` is close to an injective linear map, hence
bi-Lipschitz; the images of the pieces are Borel (Lusin–Souslin) and are made disjoint as in
Remark 1.3. -/
theorem Submission.dpf_rectifiable_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → ∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0 := by
  intro P n M hM hrect
  have hvol : (μHE[n] : Measure (Euclid n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- Step 1: the rectifiable cover `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)`
  obtain ⟨M₀, hM₀, F₀, hF₀, hcover⟩ := hrect
  choose K hK using hF₀
  -- Step 2: the regular sets `Gⱼ` are Borel and `Hⁿ(Fⱼ(ℝⁿ ∖ Gⱼ)) = 0`
  have hGmeas : ∀ f : Euclid n → Euclid P,
      MeasurableSet {a | DifferentiableAt ℝ f a ∧ Injective (fderiv ℝ f a)} := fun f =>
    (measurableSet_of_differentiableAt ℝ f).inter
      (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet)
  -- Step 2(a): nondifferentiability points have null image (Rademacher)
  have hrad : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | ¬ DifferentiableAt ℝ f a}) = 0 := by
    intro f L hf
    have hz : volume {a : Euclid n | ¬ DifferentiableAt ℝ f a} = 0 :=
      ae_iff.mp (hf.ae_differentiableAt (μ := volume))
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hf.lipschitzOnWith (s := {a | ¬ DifferentiableAt ℝ f a}))
    rw [hvol, hz, mul_zero] at hle
    exact le_antisymm hle bot_le
  -- Step 2(b): critical points have null image.  On a piece where `f` is `ε`-close to a
  -- rank-deficient `A` (`Av = 0`, `‖v‖ = 1`), `|f a - f a'| ≤ (L + 1)|D a - D a'|` for
  -- `D = id - (1 - ε) v ⊗ v`, and `det D = ε`.
  have hsard : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}) = 0 := by
    intro f L hf
    set S := {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}
    have hSmeas : MeasurableSet S :=
      (measurableSet_of_differentiableAt ℝ f).inter
        (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet).compl
    have hR : ∀ R : ℕ, μHE[n] (f '' (S ∩ ball (0 : Euclid n) R)) = 0 := by
      intro R
      set s := S ∩ ball (0 : Euclid n) R
      have hsmeas : MeasurableSet s := hSmeas.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (f '' s) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
        intro ε hε hε1
        rcases s.eq_empty_or_nonempty with hse | hsne
        · rw [hse, image_empty, measure_empty]; exact bot_le
        obtain ⟨t, A, htdisj, htmeas, hst, hA, hAy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
            (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => ε) (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (f '' (s ∩ t k)) ≤
            ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
          intro k
          obtain ⟨y, hy, hAk⟩ := hAy hsne k
          have hAnorm : ‖A k‖ ≤ L := hAk ▸ norm_fderiv_le_of_lipschitz ℝ hf
          have hAni : ¬ Injective (A k) := hAk ▸ hy.1.2
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ A k v = 0 := by
            simp only [Injective, not_forall] at hAni
            obtain ⟨a, b, hab, hne⟩ := hAni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c : ℝ := 1 - (ε : ℝ) with hc
          have hc0 : 0 ≤ c := by
            rw [hc]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hAD : ∀ h, A k (D h) = A k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc]; ring
          have hfD : ∀ a ∈ s ∩ t k, ∀ a' ∈ s ∩ t k,
              ‖f a - f a'‖ ≤ ((L : ℝ) + 1) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hA k a ha a' ha'
            have h2 : ‖A k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hAD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (f a - f a') (A k (a - a'))
            linarith
          have himg : μHE[n] (f '' (s ∩ t k)) ≤
              ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := by
            set X := s ∩ t k
            set g := Function.invFunOn D X
            have hg : ∀ y ∈ D '' X, g y ∈ X ∧ D (g y) = y :=
              fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
            have hLip : LipschitzOnWith (L + 1) (f ∘ g) (D '' X) := by
              refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
              obtain ⟨hgy, hDy⟩ := hg y hy
              obtain ⟨hgy', hDy'⟩ := hg y' hy'
              simp only [comp_apply, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
              calc ‖f (g y) - f (g y')‖ ≤ ((L : ℝ) + 1) * ‖D (g y) - D (g y')‖ :=
                    hfD _ hgy _ hgy'
                _ = _ := by rw [hDy, hDy']
            have hsub : f '' X ⊆ (f ∘ g) '' (D '' X) := by
              rintro _ ⟨a, ha, rfl⟩
              refine ⟨D a, mem_image_of_mem D ha, ?_⟩
              obtain ⟨hga, hDa⟩ := hg (D a) (mem_image_of_mem D ha)
              have := hfD _ hga _ ha
              rw [hDa, sub_self, norm_zero, mul_zero] at this
              exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
            exact (measure_mono hsub).trans
              (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c * v i) = 1 - c * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc]; ring
          calc μHE[n] (f '' (s ∩ t k)) ≤
                ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := himg
            _ = ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
              rw [hvol, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
                NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
              push_cast
              ring
        calc μHE[n] (f '' s) ≤ μHE[n] (⋃ k, f '' (s ∩ t k)) := by
              apply measure_mono
              rintro _ ⟨a, ha, rfl⟩
              obtain ⟨k, hk⟩ := mem_iUnion.mp (hst ha)
              exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
          _ ≤ ∑' k, μHE[n] (f '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := ENNReal.tsum_le_tsum hpiece
          _ = ((L : ℝ≥0∞) + 1) ^ n * volume (⋃ k, s ∩ t k) * ε := by
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right
              · exact fun k => hsmeas.inter (htmeas k)
          _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left.trans inter_subset_right
      have hfin : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have htend : Tendsto (fun ε : NNReal =>
          ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * (ε : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.coe_zero]
          exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hfin)
      refine le_antisymm (ge_of_tendsto htend ?_) bot_le
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
      exact hbound ε hε.1 hε.2
    refine measure_mono_null ?_ (measure_iUnion_null hR)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
  set G : ℕ → Set (Euclid n) := fun j =>
    {a | DifferentiableAt ℝ (F₀ j) a ∧ Injective (fderiv ℝ (F₀ j) a)}
  have hGnull : ∀ j, μHE[n] (F₀ j '' (G j)ᶜ) = 0 := by
    intro j
    refine measure_mono_null ?_ (measure_union_null (hrad _ _ (hK j)) (hsard _ _ (hK j)))
    rintro _ ⟨a, ha, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F₀ j) a
    · exact Or.inr ⟨a, ⟨hd, fun hi => ha ⟨hd, hi⟩⟩, rfl⟩
    · exact Or.inl ⟨a, hd, rfl⟩
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Step 4: Mathlib's partition of `Gⱼ` into pieces on which `Fⱼ` is close to linear
  have hpart : ∀ j, ∃ (t : ℕ → Set (Euclid n)) (A : ℕ → Euclid n →L[ℝ] Euclid P),
      Pairwise (Disjoint on t) ∧ (∀ k, MeasurableSet (t k)) ∧ G j ⊆ ⋃ k, t k ∧
      (∀ k, ApproximatesLinearOn (F₀ j) (A k) (G j ∩ t k) (c (A k) / 2)) ∧
      ((G j).Nonempty → ∀ k, ∃ y ∈ G j, A k = fderiv ℝ (F₀ j) y) := fun j =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F₀ j) (G j) (fderiv ℝ (F₀ j))
      (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) (fun A => c A / 2)
      (fun A => (div_pos (hcpos A) two_pos).ne')
  choose t A htdisj htmeas hGt hAapprox hAy using hpart
  -- Step 5: `Fⱼ` is bi-Lipschitz on `Gⱼ ∩ tⱼₖ` with lower constant `c(Aⱼₖ)/2`
  have hlow : ∀ j k, ∀ a ∈ G j ∩ t j k, ∀ a' ∈ G j ∩ t j k,
      ((c (A j k) / 2 : NNReal) : ℝ) * ‖a - a'‖ ≤ ‖F₀ j a - F₀ j a'‖ := by
    intro j k a ha a' ha'
    obtain ⟨y, hy, hAk⟩ := hAy j ⟨a, ha.1⟩ k
    have hinj : Injective (A j k) := hAk ▸ hy.2
    have h1 := hc (A j k) hinj (a - a')
    have h2 := hAapprox j k a ha a' ha'
    have h3 := norm_sub_norm_le (A j k (a - a')) (F₀ j a - F₀ j a')
    rw [norm_sub_rev (A j k (a - a'))] at h3
    push_cast at h2 ⊢
    linarith
  -- Step 6: enumerate the pieces by `i ↦ (unpair i)`; their images are Borel (Lusin–Souslin)
  set Fi : ℕ → Euclid n → Euclid P := fun i => F₀ (Nat.unpair i).1 with hFi
  set Di : ℕ → Set (Euclid n) := fun i =>
    G (Nat.unpair i).1 ∩ t (Nat.unpair i).1 (Nat.unpair i).2 with hDi
  set mi : ℕ → ℝ := fun i =>
    ((c (A (Nat.unpair i).1 (Nat.unpair i).2) / 2 : NNReal) : ℝ) with hmi
  have hDmeas : ∀ i, MeasurableSet (Di i) := fun i =>
    (hGmeas _).inter (htmeas _ _)
  have hmipos : ∀ i, 0 < mi i := fun i => by
    simp only [hmi, NNReal.coe_div, NNReal.coe_ofNat]
    exact div_pos (hcpos _) two_pos
  have hlowi : ∀ i, ∀ a ∈ Di i, ∀ a' ∈ Di i, mi i * ‖a - a'‖ ≤ ‖Fi i a - Fi i a'‖ :=
    fun i => hlow _ _
  have hNmeas : ∀ i, MeasurableSet (Fi i '' Di i) := by
    intro i
    refine (hDmeas i).image_of_continuousOn_injOn (hK _).continuous.continuousOn ?_
    intro a ha a' ha' h
    have := hlowi i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmipos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 7: disjointify the images inside `M`
  set Ñ : ℕ → Set (Euclid P) := fun i => Fi i '' Di i ∩ M
  have hÑmeas : ∀ i, MeasurableSet (Ñ i) := fun i => (hNmeas i).inter hM
  set B : ℕ → Set (Euclid n) := fun i => Di i ∩ Fi i ⁻¹' disjointed Ñ i with hB
  have himg : ∀ i, Fi i '' B i = disjointed Ñ i := by
    intro i
    rw [hB, image_inter_preimage]
    exact inter_eq_right.mpr ((disjointed_subset Ñ i).trans inter_subset_left)
  refine ⟨Fi, B, mi, fun i => ⟨K _, hK _⟩,
    fun i => (hDmeas i).inter ((hK _).continuous.measurable (MeasurableSet.disjointed hÑmeas i)),
    hmipos, fun i a ha a' ha' => hlowi i a ha.1 a' ha'.1, fun i a ha => ha.1.1,
    fun i => himg i ▸ MeasurableSet.disjointed hÑmeas i,
    fun i => himg i ▸ ((disjointed_subset Ñ i).trans inter_subset_right), ?_, ?_⟩
  · intro i j hij
    rw [himg i, himg j]
    exact disjoint_disjointed Ñ hij
  -- Step 8: the remainder lies in `M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ ∖ Gⱼ)`
  · have hU : (⋃ i, Fi i '' B i) = ⋃ i, Ñ i := by
      simp_rw [himg]
      exact iUnion_disjointed
    rw [hU]
    refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hGnull))
    rintro x ⟨hxM, hxN⟩
    rcases hcover hxM with hx0 | hx
    · exact Or.inl hx0
    · obtain ⟨j, a, rfl⟩ := mem_iUnion.mp hx
      by_cases ha : a ∈ G j
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hGt j ha)
        apply hxN
        refine mem_iUnion.mpr ⟨Nat.pair j k, ⟨a, ?_, ?_⟩, hxM⟩
        · simp only [hDi, Nat.unpair_pair]
          exact ⟨ha, hk⟩
        · simp only [hFi, Nat.unpair_pair]
      · exact Or.inr (mem_iUnion.mpr ⟨j, a, ha, rfl⟩)
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.ptd_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]
/-- Localized Besicovitch density (Simon Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6, with
Simon Ch. 1, Theorem 3.16 = Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be
open, `A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e.
`x` and every `ε > 0`, `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`; the
exceptional set does not depend on `ε`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `a/β`, where
  `a = Hⁿ(A ∩ B̄_ρ(x))` and `β = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `a/β > 1 − ε`, which forces `0 < β < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = β − a ≤ εβ`. -/
theorem Submission.ptd_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many open balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2–3: Besicovitch density for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`, off one
  -- `Hⁿ⌞A`-null set for all `y ∈ D` at once
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  -- Step 4: `x ∈ B(y, r y)` for some `y ∈ D`, so `B̄_ρ(x) ⊆ B̄(y, r y)` for `ρ < δ`
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- (i)–(ii): for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  -- (iii): `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄(y, r y)) < ∞` for `ρ < δ`
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- (iv): `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 5: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- (a) `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- (b) `ε < 1`: eventually `a / β > 1 − ε`, with `β ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set β := μHE[n] (B ∩ closedBall x ρ)
    set a := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hβtop : β ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + a = β := hsplit ρ
    -- `β ≠ 0`, since otherwise `a / β = 0 / 0 = 0 ≤ 1 − ε`
    have hβ0 : β ≠ 0 := by
      intro h0
      have ha0 : a = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : a / β = 0 := by rw [ha0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * β < a :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hβ0) (Or.inl hβtop)).1 hρq
    -- `e + (1 − ε)β ≤ e + a = β = εβ + (1 − ε)β`, and `(1 − ε)β ≠ ∞`
    have h1 : e + (1 - ε) * β ≤ ε * β + (1 - ε) * β := by
      calc e + (1 - ε) * β ≤ e + a := by gcongr
        _ = β := hsplitρ
        _ = (ε + (1 - ε)) * β := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * β + (1 - ε) * β := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hβtop) h1

/-- **Simon Ch. 3, Remark 1.5(3)** (the upper bound, with `ε = 1`): if `D` has approximate
tangent space `Q` at `x` and `Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all
small `ρ > 0`.

* Test Definition 1.4 with `φ = max(0, min(1, 2 − |w|)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`:
  `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`, so for `0 < ρ < r₁` it is `< C := |Λ| + 1`, and
  `2ρ < r₀`.
* By the blow-up scaling, `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, so `φ` is
  integrable on `η_{x,ρ}(D)` and `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} φ dHⁿ < C`.
* Scaling back, `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ Cρⁿ`. -/
theorem Submission.ptd_tl_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1: the cutoff `φ = max(0, min(1, 2 − ‖w‖)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`
  have hout : ∀ w : Euclid P, w ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖w‖)) = 0 := by
    intro w hw
    rw [mem_closedBall_zero_iff, not_le] at hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let φ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun w => max 0 (min 1 (2 - ‖w‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hφ0 : ∀ w, 0 ≤ φ w := fun w => le_max_left _ _
  have hφ1 : ∀ w, φ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hφB : ∀ w ∈ closedBall (0 : Euclid P) 1, φ w = 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    show max 0 (min 1 (2 - ‖w‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 2: `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`; choose `r₁` such that
  -- `∫_{η_{x,ρ}(D)} φ dHⁿ < |Λ| + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set Λ := ∫ w in (Q : Set (Euclid P)), φ w ∂μHE[n]
  have hC : (0 : ℝ) ≤ |Λ| + 1 := by positivity
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, φ w ∂μHE[n]) < |Λ| + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 φ).eventually_lt_const ((le_abs_self Λ).trans_lt (lt_add_one _))).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨|Λ| + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hI, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.2 hρ).ne'
  -- the blow-up scaling with `R = 2` and `R = 1`
  have h2 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 2 D hρ
  have h1 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 1 D hρ
  rw [mul_one ρ] at h1
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  -- Step 3: `Hⁿ(T ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, as `2ρ < r₀`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    rw [h2]
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hρ0)) ?_
    refine ne_top_of_le_ne_top hfin (measure_mono (Set.inter_subset_inter_right _ ?_))
    exact closedBall_subset_closedBall (by linarith)
  -- Step 4: `|φ| ≤ 1_{B̄₂(0)}`, which is integrable for `Hⁿ⌞T`; hence so is `φ`
  have hint : Integrable (fun w => φ w) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      φ.continuous.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hw : w ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hw, Real.norm_of_nonneg (hφ0 w)]
        exact hφ1 w
      · rw [Set.indicator_of_notMem hw, norm_le_zero_iff]
        exact hout w hw
  -- Step 5: `Hⁿ(T ∩ B̄₁(0)) = ∫⁻ 1_{B̄₁(0)} d(Hⁿ⌞T) ≤ ∫⁻ φ d(Hⁿ⌞T) = ∫_T φ dHⁿ < |Λ| + 1`
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (|Λ| + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ w, (closedBall (0 : Euclid P) 1).indicator 1 w ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ w, ENNReal.ofReal (φ w) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hw, Pi.one_apply, hφB w hw, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hw]
            exact zero_le
      _ = ENNReal.ofReal (∫ w, φ w ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hφ0)).symm
      _ ≤ ENNReal.ofReal (|Λ| + 1) := ENNReal.ofReal_le_ofReal hI.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(T ∩ B̄₁(0)) ≤ (|Λ| + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      = ENNReal.ofReal ρ ^ n * ((ENNReal.ofReal ρ)⁻¹ ^ n * μHE[n] (D ∩ closedBall x ρ)) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hρ0 ENNReal.ofReal_ne_top, one_pow,
          one_mul]
    _ = ENNReal.ofReal ρ ^ n * μHE[n] (T ∩ closedBall 0 1) := by rw [h1]
    _ ≤ ENNReal.ofReal ρ ^ n * ENNReal.ofReal (|Λ| + 1) := by gcongr
    _ = ENNReal.ofReal ((|Λ| + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hρ.le, mul_comm (ENNReal.ofReal ρ ^ n)]
/-- Zero `n`-density of the excess `B ∖ A` (step 6 of the tangent-locality argument for a piece):
if `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0` as
`ρ ↓ 0`.  With `ε = 1/2`, subadditivity and cancellation of the finite half give
`Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ`; then `ε = δ/(2C + 1)` gives
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.ptd_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hG hE
  -- Step 1: for `ρ > 0`, `ofReal (Cρⁿ) = ofReal C · (ofReal ρ)ⁿ`
  have hA : ∀ ρ : ℝ, 0 < ρ → ρ < r₁ →
      μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal C * ENNReal.ofReal ρ ^ n := by
    intro ρ hρ hρ₁
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul' (pow_nonneg hρ.le n)]
    exact hG ρ hρ hρ₁
  -- Step 2: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ κ (ofReal ρ)ⁿ` with `κ = 2 ofReal C`
  set κ : ℝ≥0∞ := 2 * ENNReal.ofReal C with hκ
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ κ * ENNReal.ofReal ρ ^ n := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hE 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := hρ.2.le.trans (min_le_left _ _)
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hβ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hρ₀)))
    -- `B ∩ B̄_ρ(x) ⊆ (A ∩ B̄_ρ(x)) ∪ ((B ∖ A) ∩ B̄_ρ(x))`, so subadditivity applies
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- `β/2 + β/2 = β ≤ a + e ≤ a + β/2`; cancelling the finite `β/2` gives `β/2 ≤ a`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hβ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add le_rfl he)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * (ENNReal.ofReal C * ENNReal.ofReal ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = κ * ENNReal.ofReal ρ ^ n := by rw [hκ, mul_assoc]
  -- Step 3: for `δ > 0`, `ε = δ/(κ + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δ (ofReal ρ)ⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hκ₁ : κ + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hκ₀ : κ + 1 ≠ 0 := by positivity
  filter_upwards [hB, hE (δ / (κ + 1)) (ENNReal.div_pos hδ.ne' hκ₁)] with ρ hρB hρe
  -- Step 4: hence `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / (ofReal ρ)ⁿ ≤ δ`
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ)
      ≤ δ / (κ + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (κ + 1) * ((κ + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hκ₀ hκ₁]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value
(by `Submission.ptd_tl_blowUp_measure_scaling`), and this tends to `0`. -/
theorem Submission.ptd_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)` is Borel
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Step 2: for every `f ∈ C_c`, `Δ_f(ρ) = ∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- (a): `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- (b): `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- (c)–(e) give `|Δ_f(ρ)| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for `0 < ρ < r₀/R`; (f) sends the
    -- bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- (c): for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- (d): `Δ_f(ρ) = ∫_{η_{x,ρ}(B ∖ A)} f`, as `η_{x,ρ}(B ∖ A) = η_{x,ρ}(B) ∖ η_{x,ρ}(A)`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- (e): `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- (f): `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Steps 3–4: transfer the limits of Definition 1.4 in both directions; `finrank Q = n` is shared
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _

/-- **Simon Ch. 3, Remarks 1.5(2)–(3) and the proof of Theorem 1.6 "⇒"**: let `U` be open,
`A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x`,
simultaneously for every subspace `Q`, `B` has approximate tangent space `Q` at `x` iff `A` does.

* Off one `Hⁿ⌞A`-null set, independent of `Q`, `x ∈ A` and for every `ε > 0`,
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0` (Besicovitch).
* `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U` is compact, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`.
* A tangent plane of `B` or of `A` at `x` gives `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for small `ρ` (via
  `A ⊆ B` in the first case), hence `Hⁿ((B \ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals
  of `B` and `A` have the same limits. -/
theorem Submission.ptd_ae_approxTangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 2–4: off one `Hⁿ⌞A`-null set, chosen before `Q`, `x ∈ A` and the excess of `B` over
  -- `A` near `x` is eventually small relative to `Hⁿ(B ∩ B̄_ρ(x))`
  filter_upwards [Submission.ptd_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB_le : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 6–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` makes the excess `o(ρⁿ)`, which forces
  -- the same approximate tangent spaces
  have hiff : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.ptd_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.ptd_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth
          hexc) Q
  -- Step 8: step 5 turns the assumed tangent plane into the growth bound
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (hiff C r₁ hr₁ fun ρ hρ hρr₁ => (hAB_le ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB_le (s / 2))) hTA
    exact (hiff C r₁ hr₁ hgrowth).2 hTA
/-- Borel image and null-set pullback along a bi-Lipschitz piece: if `F : ℝⁿ → ℝᴾ` is Lipschitz,
`B ⊆ ℝⁿ` is Borel and `m‖a − a'‖ ≤ ‖F a − F a'‖` on `B` (`m > 0`), then `F(B)` is Borel
(Lusin–Souslin), and a property holding `Hⁿ⌞F(B)`-a.e. holds at `F b` for Lebesgue-a.e. `b ∈ B`:
`invFunOn F B` is `m⁻¹`-Lipschitz on `F(B)` (Simon Ch. 2, 1.8(i)) and maps the `Hⁿ`-null bad
image set onto a superset of the bad parameters, and `Hⁿ` is Lebesgue measure on `ℝⁿ`. -/
theorem Submission.ptd_piece_image_measurable_ae_pullback : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → MeasurableSet (F '' B) ∧ ∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ b ∂(volume.restrict B), p (F b) := by
  intro P n F B L m hF hB hm hlow
  -- Step 1: the lower bound makes `F` injective on `B`
  have hinj : InjOn F B := fun a ha a' ha' h => by
    have hle := hlow a ha a' ha'
    rw [h, sub_self, norm_zero] at hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle hm))
  -- Step 2: Lusin–Souslin
  have hFB : MeasurableSet (F '' B) := hB.image_of_continuousOn_injOn hF.continuous.continuousOn hinj
  refine ⟨hFB, fun p hp => ?_⟩
  -- Step 3: `G = invFunOn F B` is `m⁻¹`-Lipschitz on `F '' B`
  have hG : LipschitzOnWith (Real.toNNReal m⁻¹) (invFunOn F B) (F '' B) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [hinj.leftInvOn_invFunOn ha, hinj.leftInvOn_invFunOn ha', dist_eq_norm, dist_eq_norm,
      inv_mul_eq_div, le_div_iff₀' hm]
    exact hlow a ha a' ha'
  -- Step 4: the bad parameters lie in the `G`-image of the `Hⁿ`-null bad image set
  rw [ae_restrict_iff' hFB, ae_iff] at hp
  rw [ae_restrict_iff' hB, ae_iff, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hnull : μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)}) = 0 := by
    refine le_zero_iff.1 ?_
    calc μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)})
        ≤ (Real.toNNReal m⁻¹ : ℝ≥0∞) ^ n * μHE[n] {y | ¬(y ∈ F '' B → p y)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hG.mono fun y hy => (not_imp.1 hy).1)
      _ = 0 := by rw [hp, mul_zero]
  refine measure_mono_null (fun b hb => ?_) hnull
  obtain ⟨hbB, hpb⟩ := not_imp.1 (show ¬(b ∈ B → p (F b)) from hb)
  exact ⟨F b, show ¬(F b ∈ F '' B → p (F b)) from not_imp.2 ⟨mem_image_of_mem F hbB, hpb⟩,
    hinj.leftInvOn_invFunOn hbB⟩
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.pit_setIntegral_blowUpMap_image : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
  intro P n M x r hr f
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
      ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
    ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
  -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
  have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
    intro S
    have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
      rw [image_image, he]
      rfl
    rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
  have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
      Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
      e.image_preimage]
  -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
  rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]

/-- **Rescaled area formula** (Jacobian kept abstract): if `F` is continuous, `B` and `J ≥ 0` are
Borel and `∫⁻_{F(B)} g dHⁿ = ∫⁻_B J(x) g(F(x)) dλ(x)` for every `g ≥ 0`, then for `r > 0` and
continuous `f`,
`∫_{η_{F(b),r}(F(B))} f dHⁿ = ∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dλ(c)`.
The area hypothesis says `Hⁿ⌞F(B) = F_#ν` with `ν = J λ⌞B`, which transports every integral;
the substitution `a = b + rc` produces the factor `rⁿ` that cancels the `r⁻ⁿ` of the blow-up. -/
theorem Submission.pit_blowUp_image_setIntegral_eq_rescaled : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (b : Euclid n) (r : ℝ) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume) → 0 < r → Continuous f → ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (F b) r '' (F '' B), f z ∂μHE[n] = ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume := by
  intro P n F B J b r f hF hB hJ hJ0 harea hr hf
  -- blow-up scaling: `∫_{η(F(B))} f dHⁿ = r⁻ⁿ ∫_{F(B)} f ∘ η dHⁿ`, `η = η_{F(b),r}`
  rw [Submission.pit_setIntegral_blowUpMap_image P n (F '' B) (F b) r hr f]
  -- `Hⁿ⌞F(B) = F_#ν`: the area hypothesis with `g = 1_T` for every Borel `T`
  have hmeas : μHE[n].restrict (F '' B) =
      Measure.map F ((volume.restrict B).withDensity fun x => ENNReal.ofReal (J x)) := by
    ext T hT
    have h := harea (T.indicator 1)
    rw [lintegral_indicator_one hT] at h
    rw [h, Measure.map_apply hF.measurable hT, withDensity_apply _ (hT.preimage hF.measurable),
      ← lintegral_indicator (hT.preimage hF.measurable)]
    congr 1
    funext x
    by_cases hx : F x ∈ T <;> simp [hx]
  -- `∫_{F(B)} f ∘ η dHⁿ = ∫ 1_B J (f ∘ η ∘ F) dλ`, with no integrability needed
  have hη : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r z) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hpull : ∫ y in F '' B, f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r y) ∂μHE[n] =
      ∫ x, B.indicator J x * f (r⁻¹ • (F x - F b)) ∂volume := by
    rw [hmeas, integral_map hF.aemeasurable hη.aestronglyMeasurable]
    have h := integral_withDensity_eq_integral_smul (μ := volume.restrict B) hJ.real_toNNReal
      (fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r (F x)))
    simp only [ENNReal.ofReal]
    rw [h, ← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B
    · simp [hx, NNReal.smul_def, hJ0 x, Poincare.SimonGMT.Chapter03.blowUpMap]
    · simp [hx]
  rw [hpull]
  -- substitution `a = b + rc`: `∫ G(b + rc) dλ(c) = r⁻ⁿ ∫ G dλ`
  set G : Euclid n → ℝ := fun x => B.indicator J x * f (r⁻¹ • (F x - F b))
  have hsubst : ∫ c, G (b + r • c) ∂volume = r⁻¹ ^ n * ∫ a, G a ∂volume := by
    rw [Measure.integral_comp_smul volume (fun x => G (b + x)) r,
      integral_add_left_eq_self (fun x => G x) b, finrank_euclideanSpace_fin, smul_eq_mul,
      ← inv_pow, abs_of_pos (pow_pos (inv_pos.2 hr) n)]
  exact hsubst.symm
/-- Co-Lipschitz bounds pass to the derivative at density points: if `m > 0`,
`m‖a − b‖ ≤ ‖F(a) − F(b)‖` for every `a ∈ B` (`B` arbitrary), `F` is differentiable at `b` and
`λ(B ∩ B̄_ρ(b)) / λ(B̄_ρ(b)) → 1` as `ρ ↓ 0`, then `m‖c‖ ≤ ‖DF(b)c‖` for every `c`.
For small `r > 0` the ball `B_{rδ}(b + rc)`, a fixed fraction `(δ / (‖c‖ + δ))ⁿ` of
`B̄_{r(‖c‖+δ)}(b)`, must meet `B`; the bound at such a point and differentiability give
`m‖c‖ ≤ ‖DF(b)c‖ + δ(m + ‖DF(b)‖ + ‖c‖ + δ)`, and `δ ↓ 0`. -/
theorem Submission.pit_fderiv_lower_bound_of_density : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (m : ℝ) (b : Euclid n), 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → ∀ c : Euclid n, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ := by
  intro P n F B m b hm hB hF hdens c
  set L := fderiv ℝ F b with hL
  have hFL : HasFDerivAt F L b := hF.hasFDerivAt
  -- main estimate: for every `δ > 0`, `m‖c‖ ≤ ‖Lc‖ + δ (m + ‖L‖ + ‖c‖ + δ)`
  have key : ∀ δ : ℝ, 0 < δ → m * ‖c‖ ≤ ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ) := by
    intro δ hδ
    have hK : 0 < ‖c‖ + δ := by positivity
    -- differentiability: `‖F a - F b - L (a - b)‖ ≤ δ ‖a - b‖` near `b`
    obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.1 (hFL.isLittleO.bound hδ)
    -- density: the ratio exceeds `1 - q`, `q = (δ / (‖c‖ + δ)) ^ n`, on some `(0, ρ₀)`
    obtain ⟨q, hq_def⟩ : ∃ q : ℝ≥0∞, q = ENNReal.ofReal ((δ / (‖c‖ + δ)) ^ n) := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq_def, Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hlt : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.1 (hdens.eventually_const_lt hlt)
    have hρ₀' : 0 < ρ₀ := hρ₀
    -- the radius `ρ = r (‖c‖ + δ)`
    obtain ⟨ρ, hρ, hρε, hρρ₀⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ρ < ρ₀ :=
      ⟨min ε ρ₀ / 2, by positivity, by linarith [min_le_left ε ρ₀, lt_min hε hρ₀'],
        by linarith [min_le_right ε ρ₀, lt_min hε hρ₀']⟩
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / (‖c‖ + δ) := ⟨_, rfl⟩
    have hr : 0 < r := by rw [hr_def]; positivity
    have hrK : r * (‖c‖ + δ) = ρ := by rw [hr_def]; field_simp
    -- some point of `B` lies in `B_{rδ}(b + r c)`, else the ratio at `ρ` is `≤ 1 - q`
    obtain ⟨a, haB, ha⟩ : ∃ a ∈ B, ‖a - (b + r • c)‖ < r * δ := by
      by_contra! hcon
      have hsub : ball (b + r • c) (r * δ) ⊆ closedBall b ρ := by
        intro x hx
        rw [mem_ball, dist_eq_norm] at hx
        rw [mem_closedBall, dist_eq_norm]
        calc ‖x - b‖ = ‖(x - (b + r • c)) + r • c‖ := by congr 1; abel
          _ ≤ ‖x - (b + r • c)‖ + ‖r • c‖ := norm_add_le _ _
          _ = ‖x - (b + r • c)‖ + r * ‖c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
          _ ≤ ρ := by rw [← hrK]; linarith
      have hBsub : B ∩ closedBall b ρ ⊆ closedBall b ρ \ ball (b + r • c) (r * δ) := by
        rintro x ⟨hxB, hx⟩
        refine ⟨hx, fun hxW => ?_⟩
        rw [mem_ball, dist_eq_norm] at hxW
        exact (hcon x hxB).not_gt hxW
      have hVfin : volume (closedBall b ρ) ≠ ∞ := measure_closedBall_lt_top.ne
      have hball : volume (ball (b + r • c) (r * δ)) = q * volume (closedBall b ρ) := by
        rw [Measure.addHaar_ball_of_pos volume _ (mul_pos hr hδ),
          Measure.addHaar_closedBall volume _ hρ.le, finrank_euclideanSpace_fin, ← mul_assoc,
          hq_def, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (δ / (‖c‖ + δ)) ^ n), ← mul_pow,
          ← hrK]
        congr 3
        field_simp
      have hle : volume (B ∩ closedBall b ρ) ≤ (1 - q) * volume (closedBall b ρ) := by
        calc volume (B ∩ closedBall b ρ)
            ≤ volume (closedBall b ρ \ ball (b + r • c) (r * δ)) := measure_mono hBsub
          _ = volume (closedBall b ρ) - volume (ball (b + r • c) (r * δ)) :=
            measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
          _ = (1 - q) * volume (closedBall b ρ) := by
            rw [hball, ENNReal.sub_mul (fun _ _ => hVfin), one_mul]
      have hgt : 1 - q < volume (B ∩ closedBall b ρ) / volume (closedBall b ρ) :=
        hρ₀sub ⟨hρ, hρρ₀⟩
      exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
    -- the estimate at `a`, with `a - b = r c + e`, `‖e‖ < r δ`
    obtain ⟨e, he_def⟩ : ∃ e : Euclid n, e = a - (b + r • c) := ⟨_, rfl⟩
    rw [← he_def] at ha
    have hab : a - b = r • c + e := by rw [he_def]; abel
    have hab_le : ‖a - b‖ ≤ r * ‖c‖ + ‖e‖ := by
      rw [hab]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
    have hab_lt : ‖a - b‖ < r * (‖c‖ + δ) := by rw [mul_add]; linarith
    have hdist : dist a b < ε := by rw [dist_eq_norm]; linarith
    have h1 : m * ‖a - b‖ ≤ ‖F a - F b‖ := hB a haB
    have h2 : ‖F a - F b‖ ≤ ‖L (a - b)‖ + δ * ‖a - b‖ := by
      have h := hεF hdist
      have h' := norm_sub_norm_le (F a - F b) (L (a - b))
      linarith
    have h3 : ‖L (a - b)‖ ≤ r * ‖L c‖ + ‖L‖ * ‖e‖ := by
      rw [hab, map_add, map_smul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      linarith [L.le_opNorm e]
    have h4 : r * ‖c‖ ≤ ‖a - b‖ + ‖e‖ := by
      have : r • c = (a - b) - e := by rw [hab]; abel
      calc r * ‖c‖ = ‖r • c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ = ‖(a - b) - e‖ := by rw [this]
        _ ≤ ‖a - b‖ + ‖e‖ := norm_sub_le _ _
    have h5 : ‖L‖ * ‖e‖ ≤ ‖L‖ * (r * δ) := mul_le_mul_of_nonneg_left ha.le (norm_nonneg _)
    have h6 : m * ‖e‖ ≤ m * (r * δ) := mul_le_mul_of_nonneg_left ha.le hm.le
    have h7 : δ * ‖a - b‖ ≤ δ * (r * (‖c‖ + δ)) := mul_le_mul_of_nonneg_left hab_lt.le hδ.le
    have h8 : m * (r * ‖c‖) ≤ m * (‖a - b‖ + ‖e‖) := mul_le_mul_of_nonneg_left h4 hm.le
    have hfin : r * (m * ‖c‖) ≤ r * (‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by
      linarith
    exact le_of_mul_le_mul_left hfin hr
  -- let `δ → 0⁺`
  have hlim : Tendsto (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) (𝓝[>] 0) (𝓝 ‖L c‖) := by
    have hcont : Continuous (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
/-- If `F` has derivative `L` at `b` and `f` is continuous with compact support, then
`∫_{B̄_R(0)} |f(r⁻¹(F(b + rc) − F(b))) − f(Lc)| dc → 0` as `r ↓ 0` (the error term `T₃` in the
limit of rescaled integrals over the image of a `C¹` piece; cf. the tangent-plane limit in Simon
Ch. 3, proof of 1.6 "⇒").  With `V = |B̄_R(0)|` and `S = |R| + 1`, take `η` from the uniform
continuity of `f` for `ε / (V + 1)`, then `δ₀` with `‖F(b + k) − F(b) − Lk‖ ≤ (η / 2S)‖k‖` for
`‖k‖ < δ₀`; for `0 < r < δ₀ / S` the integrand is `≤ ε / (V + 1)` on the ball. -/
theorem Submission.pit_ril_diffQuot_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (b : Euclid n) (f : Euclid P → ℝ) (R : ℝ), HasFDerivAt F L b → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro P n F L b f R hF hfc hfs
  -- `D = B̄_R(0)` has finite measure `V`, and `‖c‖ < S = |R| + 1` on `D`
  have hDfin : (volume : Measure (Euclid n)) (closedBall 0 R) < ∞ := measure_closedBall_lt_top
  set V : ℝ := (volume : Measure (Euclid n)).real (closedBall 0 R)
  have hV : 0 ≤ V := measureReal_nonneg
  set S : ℝ := |R| + 1
  have hS : 0 < S := by positivity
  have hcS : ∀ c ∈ closedBall (0 : Euclid n) R, ‖c‖ < S := fun c hc =>
    ((mem_closedBall_zero_iff.1 hc).trans (le_abs_self R)).trans_lt (lt_add_one _)
  -- uniform continuity of `f` and the little-o form of `HasFDerivAt`
  have huc := Metric.uniformContinuous_iff.1 (hfs.uniformContinuous_of_continuous hfc)
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hV1 : 0 < V + 1 := by linarith
  set ε₁ : ℝ := ε / (V + 1) with hε₁_def
  have hε₁ : 0 < ε₁ := div_pos hε hV1
  obtain ⟨η, hη, hηf⟩ := huc ε₁ hε₁
  set θ : ℝ := η / (2 * S) with hθ_def
  have hθ : 0 < θ := div_pos hη (by linarith)
  obtain ⟨δ₀, hδ₀, hδ₀F⟩ := Metric.eventually_nhds_iff.1 (hlo.bound hθ)
  refine ⟨δ₀ / S, div_pos hδ₀ hS, fun r hr hrδ => ?_⟩
  rw [mem_Ioi] at hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hrδ
  have hrS : r * S < δ₀ := (lt_div_iff₀ hS).1 hrδ
  -- pointwise bound on the integrand
  have hpt : ∀ c ∈ closedBall (0 : Euclid n) R,
      ‖‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖ ≤ ε₁ := by
    intro c hc
    have hc' := hcS c hc
    have hnorm : ‖r • c‖ = r * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hrc : dist (r • c) 0 < δ₀ := by
      rw [dist_zero_right, hnorm]
      calc r * ‖c‖ ≤ r * S := mul_le_mul_of_nonneg_left hc'.le hr.le
        _ < δ₀ := hrS
    have hbound := hδ₀F hrc
    have heq : r⁻¹ • (F (b + r • c) - F b) - L c
        = r⁻¹ • (F (b + r • c) - F b - L (r • c)) := by
      rw [map_smul, smul_sub _ (F (b + r • c) - F b), inv_smul_smul₀ hr.ne']
    have hclose : dist (r⁻¹ • (F (b + r • c) - F b)) (L c) < η := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      calc r⁻¹ * ‖F (b + r • c) - F b - L (r • c)‖
          ≤ r⁻¹ * (θ * ‖r • c‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr.le)
        _ = θ * ‖c‖ := by rw [hnorm]; field_simp
        _ ≤ θ * S := mul_le_mul_of_nonneg_left hc'.le hθ.le
        _ = η / 2 := by rw [hθ_def]; field_simp
        _ < η := half_lt_self hη
    have := hηf hclose
    rw [Real.dist_eq] at this
    rw [norm_norm, Real.norm_eq_abs]
    exact this.le
  -- integral bound
  have hint := norm_setIntegral_le_of_norm_le_const hDfin hpt
  rw [dist_zero_right]
  calc ‖∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖
      ≤ ε₁ * V := hint
    _ < ε := by
      rw [hε₁_def, div_mul_eq_mul_div, div_lt_iff₀ hV1]
      nlinarith
/-- At a point `b` of Lebesgue density one of the Borel set `B` (`λ(B ∩ B̄_ρ(b))/λ(B̄_ρ(b)) → 1`
as `ρ ↓ 0`, the quotient taken in `[0, ∞]`), the averages `⨍_{B̄_s(b)} 1_{ℝⁿ∖B} dλ` tend to `0`
as `s ↓ 0`.  For `s > 0`, `0 < λ(B̄_s(b)) < ∞` and, by additivity, the average equals
`1 − (λ(B ∩ B̄_s(b))/λ(B̄_s(b))).toReal`; `toReal` is continuous at `1`. -/
theorem Submission.pit_ril_compl_average_tendsto : ∀ (n : ℕ) (B : Set (Euclid n)) (b : Euclid n), MeasurableSet B → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, Bᶜ.indicator (fun _ => (1 : ℝ)) a ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n B b hB hlim
  -- `q(ρ).toReal → 1` (`toReal` is continuous at `1 ≠ ∞`), so `1 - q(ρ).toReal → 0`
  have h1 : Tendsto (fun ρ : ℝ =>
      1 - (volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).sub
      ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim)
    rwa [ENNReal.toReal_one, sub_self] at h
  refine h1.congr' ?_
  -- for `s > 0`, `0 < λ(C_s) < ∞` and the average equals `1 - q(s).toReal`
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hfin : volume (closedBall b s) ≠ ∞ := measure_closedBall_lt_top.ne
  have hC : volume.real (closedBall b s) ≠ 0 :=
    (ENNReal.toReal_pos (measure_closedBall_pos volume b hs).ne' hfin).ne'
  -- `λ_ℝ(C_s ∩ B) + λ_ℝ(C_s \ B) = λ_ℝ(C_s)`
  have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := closedBall b s) hB hfin
  rw [setAverage_eq, setIntegral_indicator hB.compl, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, inter_comm B,
    ← Set.sdiff_eq, ← hsplit]
  rw [← hsplit] at hC
  field_simp
  ring
/-- Localised three-term estimate for the rescaled area integrals (one fixed `r > 0`).  With
`Φ_r(c) = r⁻¹(F(b + rc) − F(b))` and `D = B̄_{R/m}(0)`, the integrands
`X(c) = 1_B(b + rc) J(b + rc) f(Φ_r(c))` and `Y(c) = J(b) f(Lc)` vanish off `D` (by the lower
bounds for `F` on `B` and for `L`, as `f = 0` off the open `R`-ball), and pointwise
`|X − Y| ≤ KM·1_{Bᶜ}(b + rc) + M|J(b + rc) − J(b)| + J(b)|f(Φ_r(c)) − f(Lc)|`, by cases on
`b + rc ∈ B`; all are bounded Borel functions, so integrate over `D`. -/
theorem Submission.pit_ril_three_term_bound : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ) (R M r : ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → (∀ c, m * ‖c‖ ≤ ‖L c‖) → Continuous f → (∀ w, R ≤ ‖w‖ → f w = 0) → (∀ w, ‖f w‖ ≤ M) → 0 < r → ‖(∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) - J b * (∫ c, f (L c) ∂volume)‖ ≤ K * M * (∫ c in closedBall (0 : Euclid n) (R / m), Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) ∂volume) + M * (∫ c in closedBall (0 : Euclid n) (R / m), ‖J (b + r • c) - J b‖ ∂volume) + J b * (∫ c in closedBall (0 : Euclid n) (R / m), ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) := by
  intro P n F L B J K m b f R M r hF hB hJ hJK hm hFB hL hf hfR hfM hr
  -- constants: `0 ≤ M`, `0 ≤ J b ≤ K`, `0 ≤ K`, and `λ(D) < ∞` for `D = B̄_{R/m}(0)`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfM 0)
  have hJb0 : 0 ≤ J b := (hJK b).1
  have hJbK : J b ≤ K := (hJK b).2
  have hK0 : 0 ≤ K := hJb0.trans hJbK
  have hDfin : volume (closedBall (0 : Euclid n) (R / m)) ≠ ∞ := measure_closedBall_lt_top.ne
  -- measurability of the integrands
  have hshift : Continuous fun c : Euclid n => b + r • c :=
    continuous_const.add (continuous_id.const_smul r)
  have hΦ : Continuous fun c : Euclid n => f (r⁻¹ • (F (b + r • c) - F b)) :=
    hf.comp (((hF.comp hshift).sub continuous_const).const_smul r⁻¹)
  have hfL : Continuous fun c : Euclid n => f (L c) := hf.comp L.continuous
  have hIJ : Measurable fun c : Euclid n => B.indicator J (b + r • c) :=
    (hJ.indicator hB).comp hshift.measurable
  have hg₁ : Measurable fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) :=
    (measurable_const.indicator hB.compl).comp hshift.measurable
  have hg₂ : Measurable fun c : Euclid n => ‖J (b + r • c) - J b‖ :=
    ((hJ.comp hshift.measurable).sub measurable_const).norm
  have hg₃ : Continuous fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
    (hΦ.sub hfL).norm
  -- bounded measurable functions are integrable on `D`
  have hIJb : ∀ c : Euclid n, ‖B.indicator J (b + r • c)‖ ≤ K := by
    intro c
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (hJK _).1]
      exact (hJK _).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact hK0
  have hXint : IntegrableOn
      (fun c : Euclid n => B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (hIJ.mul hΦ.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul]
    exact mul_le_mul (hIJb c) (hfM _) (norm_nonneg _) hK0
  have hYint : IntegrableOn (fun c : Euclid n => J b * f (L c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (measurable_const.mul hfL.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul, Real.norm_of_nonneg hJb0]
    exact mul_le_mul hJbK (hfM _) (norm_nonneg _) hK0
  have hg₁int : IntegrableOn (fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := 1) hDfin hg₁.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    by_cases h : b + r • c ∈ Bᶜ
    · rw [Set.indicator_of_mem h, norm_one]
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact zero_le_one
  have hg₂int : IntegrableOn (fun c : Euclid n => ‖J (b + r • c) - J b‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K) hDfin hg₂.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm, Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hJK (b + r • c), hJK b]
  have hg₃int : IntegrableOn
      (fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := M + M) hDfin hg₃.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hfM _) (hfM _))
  -- localisation: both integrands vanish off `D`
  have hloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → R < m * ‖c‖ := by
    intro c hc
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hc
    rwa [mul_comm] at hc
  have hXloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) →
      B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) = 0 := by
    intro c hc
    by_cases h : b + r • c ∈ B
    · have h1 := hFB _ h
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h2 : R ≤ ‖r⁻¹ • (F (b + r • c) - F b)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc R ≤ m * ‖c‖ := (hloc c hc).le
          _ = r⁻¹ * (m * (r * ‖c‖)) := by rw [mul_left_comm m r, inv_mul_cancel_left₀ hr.ne']
          _ ≤ r⁻¹ * ‖F (b + r • c) - F b‖ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hr.le)
      rw [hfR _ h2, mul_zero]
    · rw [Set.indicator_of_notMem h, zero_mul]
  have hYloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → J b * f (L c) = 0 := by
    intro c hc
    rw [hfR _ ((hloc c hc).le.trans (hL c)), mul_zero]
  -- pointwise three-term estimate, by cases on `b + r • c ∈ B`
  have hpt : ∀ c : Euclid n,
      ‖B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖ ≤
        K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) + M * ‖J (b + r • c) - J b‖ +
          J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
    intro c
    have hu := hfM (r⁻¹ • (F (b + r • c) - F b))
    have hv := hfM (L c)
    have hA : 0 ≤ M * ‖J (b + r • c) - J b‖ := mul_nonneg hM0 (norm_nonneg _)
    have hB' : 0 ≤ J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
      mul_nonneg hJb0 (norm_nonneg _)
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h), mul_zero,
        zero_add]
      have hJu := mul_le_mul_of_nonneg_left hu (norm_nonneg (J (b + r • c) - J b))
      calc ‖J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖
          = ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b)) +
              J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := by
            congr 1
            ring
        _ ≤ ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b))‖ +
              ‖J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := norm_add_le _ _
        _ = ‖J (b + r • c) - J b‖ * ‖f (r⁻¹ • (F (b + r • c) - F b))‖ +
              J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg hJb0]
        _ ≤ M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            linarith [mul_comm M ‖J (b + r • c) - J b‖]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), zero_mul, zero_sub,
        norm_neg, norm_mul, Real.norm_of_nonneg hJb0, mul_one]
      have hJv : J b * ‖f (L c)‖ ≤ K * M := mul_le_mul hJbK hv (norm_nonneg _) hK0
      linarith
  -- integrate the pointwise estimate over `D`
  have h1 : (∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m),
        B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hXloc).symm
  have h2 : J b * (∫ c, f (L c) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m), J b * f (L c) ∂volume := by
    rw [← integral_const_mul]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hYloc).symm
  have hG₁₂ : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖) (closedBall (0 : Euclid n) (R / m)) volume :=
    (hg₁int.const_mul _).add (hg₂int.const_mul _)
  have hG : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume :=
    hG₁₂.add (hg₃int.const_mul _)
  rw [h1, h2, ← integral_sub hXint hYint]
  refine (norm_integral_le_of_norm_le hG (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add hG₁₂ (hg₃int.const_mul _), integral_add (hg₁int.const_mul _) (hg₂int.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
/-- **Rescaled integrals at a point of vanishing ball averages**: for `R > 0`, if
`⨍_{B̄_s(b)} h → 0` as `s → 0⁺`, then `∫_{B̄_R(0)} h(b + rc) dc → 0` as `r → 0⁺`.
For `r > 0`, dilation by `r` and translation by `b` give
`∫_{B̄_R(0)} h(b + rc) dc = r⁻ⁿ ∫_{B̄_{rR}(b)} h = ω Rⁿ ⨍_{B̄_{rR}(b)} h`, `ω = λ(B̄₁(0))`. -/
theorem Submission.pit_integral_closedBall_rescale_tendsto : ∀ (n : ℕ) (h : Euclid n → ℝ) (b : Euclid n) (R : ℝ), 0 < R → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, h a ∂volume) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n h b R hR hlim
  -- `ω = λ(B̄₁(0)) ∈ (0, ∞)` and `λ(B̄_s(z)) = sⁿ ω` for `s ≥ 0`
  set ω : ℝ := volume.real (closedBall (0 : Euclid n) 1) with hω_def
  have hω : 0 < ω := by
    rw [hω_def, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  have hvol : ∀ (z : Euclid n) {s : ℝ}, 0 ≤ s → volume.real (closedBall z s) = s ^ n * ω := by
    intro z s hs
    rw [Measure.addHaar_real_closedBall' volume z hs, finrank_euclideanSpace_fin]
  -- for `r > 0`: `∫_{B̄_R(0)} h(b + rc) dc = Rⁿ ω ⨍_{B̄_{rR}(b)} h`
  have key : ∀ r : ℝ, 0 < r → ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
      R ^ n * ω * ⨍ a in closedBall b (r * R), h a ∂volume := by
    intro r hr
    set H : Euclid n → ℝ := (closedBall b (r * R)).indicator h with hH
    have hmem : ∀ c : Euclid n, b + r • c ∈ closedBall b (r * R) ↔ c ∈ closedBall (0 : Euclid n) R := by
      intro c
      rw [mem_closedBall, mem_closedBall, dist_self_add_left, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, mul_le_mul_iff_of_pos_left hr]
    -- `1_{B̄_R(0)}(c) h(b + rc) = H(b + rc)`
    have h1 : ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
        ∫ c, H (b + r • c) ∂volume := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      ext c
      by_cases hc : c ∈ closedBall (0 : Euclid n) R
      · rw [indicator_of_mem hc, hH, indicator_of_mem ((hmem c).2 hc)]
      · rw [indicator_of_notMem hc, hH, indicator_of_notMem (mt (hmem c).1 hc)]
    -- dilation by `r` and translation by `b`
    have h2 : ∫ c, H (b + r • c) ∂volume = (r ^ n)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [Measure.integral_comp_smul volume (fun x => H (b + x)) r, integral_add_left_eq_self H b,
        hH, integral_indicator measurableSet_closedBall, finrank_euclideanSpace_fin, smul_eq_mul,
        abs_of_pos (inv_pos.2 (pow_pos hr n))]
    have h3 : ⨍ a in closedBall b (r * R), h a ∂volume =
        ((r * R) ^ n * ω)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [setAverage_eq, hvol b (mul_pos hr hR).le, smul_eq_mul]
    rw [h1, h2, h3, mul_pow]
    field_simp
  -- `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have hlim' := (hlim.comp hmap).const_mul (R ^ n * ω)
  rw [mul_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (key r hr).symm

/-- **Rescaled integrals at a density point of `B` and a Lebesgue point of `J`**: let
`m|a − b| ≤ |F(a) − F(b)|` on `B`, `m|c| ≤ |Lc|` for `L = DF(b)`, `0 ≤ J ≤ K`, let `B` have
density `1` at `b` and `⨍_{B̄_ρ(b)} |J − J(b)| → 0`.  Then for `f ∈ C_c(ℝᴾ)`,
`∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dc → J(b) ∫ f(Lc) dc` as `r → 0⁺`.
With `f = 0` off `B_R(0)` and `|f| ≤ M`, the error is at most `K M T₁ + M T₂ + J(b) T₃`, where
`T₁, T₂, T₃` integrate `1_{Bᶜ}(b + rc)`, `|J(b + rc) − J(b)|` and
`|f(r⁻¹(F(b + rc) − F(b))) − f(Lc)|` over `B̄_{R/m}(0)`; each tends to `0`. -/
theorem Submission.pit_rescaled_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → (∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖) → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) (𝓝[>] 0) (𝓝 (J b * ∫ c, f (fderiv ℝ F b c) ∂volume)) := by
  intro P n F B J K m b f hF hB hJ hJK hm hFB hdiff hL hdens hLeb hf hfc
  -- `f = 0` off `B_R(0)` and `|f| ≤ M`; the integrals live on `B̄_{R/m}(0)`
  obtain ⟨R, hR, hRf⟩ := hfc.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hRm : 0 < R / m := div_pos hR hm
  -- `T₁ → 0`: `B` has density `1` at `b`
  have hT₁ := Submission.pit_integral_closedBall_rescale_tendsto n
    (Bᶜ.indicator fun _ => (1 : ℝ)) b (R / m) hRm
    (Submission.pit_ril_compl_average_tendsto n B b hB hdens)
  -- `T₂ → 0`: `b` is a Lebesgue point of `J`
  have hT₂ := Submission.pit_integral_closedBall_rescale_tendsto n (fun a => ‖J a - J b‖) b
    (R / m) hRm hLeb
  -- `T₃ → 0`: `r⁻¹(F(b + rc) − F(b)) → Lc` uniformly on `B̄_{R/m}(0)`
  have hT₃ := Submission.pit_ril_diffQuot_integral_tendsto P n F (fderiv ℝ F b) b f (R / m)
    hdiff.hasFDerivAt hf hfc
  have hlim := ((hT₁.const_mul (K * M)).add (hT₂.const_mul M)).add (hT₃.const_mul (J b))
  simp only [mul_zero, add_zero] at hlim
  -- squeeze `|I(r) − J(b) ∫ f(Lc) dc| ≤ K M T₁(r) + M T₂(r) + J(b) T₃(r)` for `r > 0`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Submission.pit_ril_three_term_bound P n F (fderiv ℝ F b) B J K m b f R M r hF hB hJ hJK
    hm hFB hL hf hRf hM hr
/-- Integral over the range of a linear map with constant Jacobian: if `T : ℝⁿ → ℝᴾ` is linear
and `Hⁿ(T(S)) = j λ(S)` for every `S ⊆ ℝⁿ` (`j ≥ 0`, `λ` Lebesgue measure), then for continuous
`f`, `∫_{T(ℝⁿ)} f dHⁿ = j ∫ f(T(c)) dλ(c)`.  On Borel `A`, `A ∩ T(ℝⁿ) = T(T⁻¹(A))`, so
`Hⁿ⌞T(ℝⁿ) = j T_#λ`. -/
theorem Submission.pit_setIntegral_range_linear : ∀ (P n : ℕ) (T : Euclid n →L[ℝ] Euclid P) (j : ℝ) (f : Euclid P → ℝ), 0 ≤ j → (∀ S : Set (Euclid n), μHE[n] (T '' S) = ENNReal.ofReal j * volume S) → Continuous f → ∫ y in (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = j * ∫ c, f (T c) ∂volume := by
  intro P n T j f hj hT hf
  -- the carrier of the submodule `range T` is the set `T(ℝⁿ)`
  have hrange : (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) = range T := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  -- `Hⁿ⌞T(ℝⁿ) = ofReal(j) • T_#λ`, checked on Borel sets
  have hmeas : μHE[n].restrict (range T) = ENNReal.ofReal j • volume.map T := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply T.measurable hA,
      ← image_preimage_eq_inter_range, hT, smul_eq_mul]
  -- change of variables, with `(ofReal j).toReal = j` since `j ≥ 0`
  rw [hrange, hmeas, integral_smul_measure,
    integral_map T.measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hj, smul_eq_mul]
/-- **Simon Ch. 3, 1.4** (approximate tangent spaces of a bi-Lipschitz piece): let `F : ℝⁿ → ℝᴾ`
be `L`-Lipschitz, `B ⊆ ℝⁿ` Borel and `m > 0` with `m|a − a'| ≤ |F a − F a'|` on `B`, and let `F`
be differentiable at every point of `B` with injective derivative.  Then for a.e. `b ∈ B`,
`F(B)` has approximate tangent space `range DF(b)` at `F b`.
With `J := normDet DF` (Borel, `0 ≤ J ≤ Lⁿ`) the injective area formula holds on `B`.  A.e.
`b ∈ B` is a density point of `B` and a Lebesgue point of `J`; there
`∫_{η_{F b,r}(F(B))} f dHⁿ = ∫ 1_B J(b + rc) f(r⁻¹(F(b + rc) − F b)) dc` tends to
`J(b) ∫ f(DF(b)c) dc = ∫_{range DF(b)} f dHⁿ` as `r ↓ 0`. -/
theorem Submission.ptd_piece_image_approxTangent_ae : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n (F '' B) (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F B L m hF hB hm hcolip hreg
  have hfin : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  -- the area Jacobian `J = normDet DF`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid n → ℝ, J = Poincare.SimonGMT.Chapter02.areaJacobianAt F :=
    ⟨_, rfl⟩
  have hJmeas : Measurable J := hJ ▸ Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
  have hJnonneg : ∀ a, 0 ≤ J a := hJ ▸ Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
  -- `Hⁿ(T(S)) = normDet T · λ(S)` for every linear `T`
  have hlin : ∀ (T : Euclid n →L[ℝ] Euclid P) (S : Set (Euclid n)),
      μHE[n] (T '' S) = ENNReal.ofReal (T : Euclid n →ₗ[ℝ] Euclid P).normDet * volume S := by
    intro T S
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (T : Euclid n →ₗ[ℝ] Euclid P) S
    rw [hfin] at h
    simpa using h
  have hJlin : ∀ a (S : Set (Euclid n)),
      μHE[n] (fderiv ℝ F a '' S) = ENNReal.ofReal (J a) * volume S := by
    intro a S
    rw [hlin, hJ, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
  -- `J ≤ Lⁿ`: compare `Hⁿ(DF(a)(B̄₁(0)))` with the Lipschitz bound `‖DF(a)‖ ≤ L`
  have hJle : ∀ a, J a ≤ (L : ℝ) ^ n := by
    intro a
    have hTL : ‖fderiv ℝ F a‖₊ ≤ L := by
      have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := a) hF
      exact_mod_cast h
    have hpos : volume (closedBall (0 : Euclid n) 1) ≠ 0 :=
      (measure_closedBall_pos volume (0 : Euclid n) one_pos).ne'
    have hfin' : volume (closedBall (0 : Euclid n) 1) ≠ ∞ := measure_closedBall_lt_top.ne
    have hle : ENNReal.ofReal (J a) * volume (closedBall (0 : Euclid n) 1) ≤
        (L : ℝ≥0∞) ^ n * volume (closedBall (0 : Euclid n) 1) := by
      rw [← hJlin a, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
      calc μHE[n] (fderiv ℝ F a '' closedBall 0 1)
          ≤ (‖fderiv ℝ F a‖₊ : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (fderiv ℝ F a).lipschitzWith.lipschitzOnWith
        _ ≤ (L : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) := by gcongr
    have h2 : ENNReal.ofReal (J a) ≤ (L : ℝ≥0∞) ^ n :=
      (ENNReal.mul_le_mul_iff_left hpos hfin').1 hle
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_pow L.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    exact h2
  -- `F` is injective on `B`, so the area formula holds on `B` with weight `J`
  have hinjOn : InjOn F B := by
    intro a ha a' ha' hFa
    have h := hcolip a ha a' ha'
    rw [hFa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hm
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have harea : ∀ g : Euclid P → ℝ≥0∞,
      ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume := by
    intro g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hB hinjOn g
    rw [hfin] at h
    rw [h, hJ]
  -- `J` is bounded and Borel, hence locally integrable
  have hJloc : LocallyIntegrable J volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne hJmeas.aestronglyMeasurable
      (M := (L : ℝ) ^ n) (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hJnonneg a)]
    exact hJle a
  -- a.e. `b ∈ B` is a density point of `B` and a Lebesgue point of `J`
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Euclid n))
    hJloc 1
  filter_upwards [ae_restrict_mem hB, Besicovitch.ae_tendsto_measure_inter_div volume B,
    ae_restrict_of_ae hleb] with b hbB hα hβ
  have hβ' : Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) :=
    hβ (fun _ => b) id tendsto_id (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) =>
      mem_closedBall_self (by simpa using hρ.le))
  obtain ⟨hdb, hinj⟩ := hreg b hbB
  have hcolb : ∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖ := fun a ha => hcolip a ha b hbB
  have hγ : ∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ :=
    Submission.pit_fderiv_lower_bound_of_density P n F B m b hm hcolb hdb hα
  refine ⟨?_, fun f => ?_⟩
  · rw [LinearMap.finrank_range_of_inj (by simpa using hinj), hfin]
  · rw [Submission.pit_setIntegral_range_linear P n (fderiv ℝ F b) (J b) f (hJnonneg b)
      (hJlin b) f.continuous]
    refine (Submission.pit_rescaled_integral_tendsto P n F B J ((L : ℝ) ^ n) m b f hF.continuous
      hB hJmeas (fun a => ⟨hJnonneg a, hJle a⟩) hm hcolb hdb hγ hα hβ' f.continuous
      f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (Submission.pit_blowUp_image_setIntegral_eq_rescaled P n F B J b r f hF.continuous hB
      hJmeas hJnonneg harea hr f.continuous).symm

/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"**, for a bi-Lipschitz piece: let `U` be open,
`Y ⊆ U` Borel with `Hⁿ(Y ∩ C) < ∞` for compact `C ⊆ U`, `F` Lipschitz, `B` Borel with
`m|a − a'| ≤ |F(a) − F(a')|` on `B`, `DF(a)` injective for `a ∈ B`, and `F(B) ⊆ Y`.  Then for
a.e. `b ∈ B`, `Y` has approximate tangent space `range DF(b)` at `F(b)`.  The image `F(B)` itself
has this tangent space at `F(b)` for a.e. `b`; `Y` and its Borel subset `F(B)` have the same
approximate tangent spaces `Hⁿ`-a.e. on `F(B)`; and `Hⁿ⌞F(B)`-null sets pull back along `F` to
Lebesgue-null subsets of `B`. -/
theorem Submission.dpf_approxTangent_ae_bilipschitz_piece : ∀ (P n : ℕ) (U Y : Set (Euclid P)) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → MeasurableSet Y → Y ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (Y ∩ C) ≠ ∞) → LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → F '' B ⊆ Y → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n Y (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n U Y F B L m hU hY hYU hfin hF hB hm hbi hdiff hFBY
  -- Step 0(a)–(b): `F(B)` is Borel; `Hⁿ⌞F(B)`-a.e. properties hold at `F(b)` for a.e. `b ∈ B`
  obtain ⟨hA, hpull⟩ := Submission.ptd_piece_image_measurable_ae_pullback P n F B L m hF hB hm hbi
  -- Steps 1–3 and 6: `Hⁿ`-a.e. on `F(B)`, `Y` and `F(B)` have the same approximate tangent spaces
  have hloc := Submission.ptd_ae_approxTangent_iff_of_subset P n U (F '' B) Y hU hA hY hFBY hYU hfin
  -- Steps 4, 5 and 7: `F(B)` has approximate tangent space `range DF(b)` at `F(b)` for a.e. `b ∈ B`
  filter_upwards [hpull _ hloc,
    Submission.ptd_piece_image_approxTangent_ae P n F B L m hF hB hm hbi hdiff] with b hYA hA'
  exact (hYA _).2 hA'
/-- **Markov selection of a good parameter** (Simon, Ch. 6, proof of 5.1, (10): a slicing radius
in `(σ/2, σ)`).  If `g : ℝ → [0, ∞]` is a.e.-measurable, `p` holds for a.e. `t`, `a < b` and
`∫_{(a,b)} g ≤ I`, then some `t ∈ (a, b)` has `p t` and `(b − a) g(t) ≤ 2I`.  Otherwise
`2I < (b − a) g` a.e. on `(a, b)`, which is impossible for `I = ∞` as `(a, b)` is not null; for
`I < ∞` integration gives `2I(b − a) ≤ (b − a)I`, so `I = 0`, whence `g = 0` a.e. on `(a, b)`,
contradicting `0 < (b − a) g` a.e. there. -/
theorem Submission.dor_lmb_fcd_sd_markov_point : ∀ (g : ℝ → ℝ≥0∞) (p : ℝ → Prop) (a b : ℝ) (I : ℝ≥0∞), a < b → AEMeasurable g → (∀ᵐ t, p t) → ∫⁻ t in Ioo a b, g t ≤ I → ∃ t ∈ Ioo a b, p t ∧ ENNReal.ofReal (b - a) * g t ≤ 2 * I := by
  intro g p a b I hab hg hp hI
  set c : ℝ≥0∞ := ENNReal.ofReal (b - a) with hc
  have hc0 : c ≠ 0 := by simpa [hc] using hab
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hvol : volume (Ioo a b) = c := Real.volume_Ioo
  -- Step 1: otherwise `2I < c g(t)` for every `t ∈ (a, b)` with `p t`
  by_contra hcon
  have hbad : ∀ t ∈ Ioo a b, p t → 2 * I < c * g t := fun t ht hpt =>
    not_le.1 fun hle => hcon ⟨t, ht, hpt, hle⟩
  -- Step 2: `2I < c g` almost everywhere on `(a, b)`
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), 2 * I < c * g t := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hp] with t ht htI
    exact hbad t htI ht
  -- Step 3: `(a, b)` is not null
  have hnull : ¬ ∀ᵐ _t ∂(volume.restrict (Ioo a b)), False := by
    intro h
    have h0 : volume.restrict (Ioo a b) = 0 := ae_eq_bot.1 (eventually_false_iff_eq_bot.1 h)
    rw [Measure.restrict_eq_zero, hvol] at h0
    exact hc0 h0
  rcases eq_or_ne I ∞ with hItop | hItop
  · -- Step 4: `I = ∞`
    apply hnull
    filter_upwards [hae] with t ht
    rw [hItop] at ht
    simp at ht
  · -- Step 5: `I < ∞` forces `I = 0`
    have h1 : ∫⁻ _t in Ioo a b, 2 * I ≤ ∫⁻ t in Ioo a b, c * g t :=
      lintegral_mono_ae (hae.mono fun t ht => ht.le)
    rw [setLIntegral_const, lintegral_const_mul'' _ hg.restrict, hvol] at h1
    have h2 : 2 * I * c ≤ I * c :=
      calc 2 * I * c ≤ c * ∫⁻ t in Ioo a b, g t := h1
        _ ≤ c * I := by gcongr
        _ = I * c := mul_comm c I
    have h3 : 2 * I ≤ I := (ENNReal.mul_le_mul_iff_left hc0 hctop).1 h2
    have hI0 : I = 0 := by
      have h4 : I + I ≤ 0 + I := by rw [zero_add, ← two_mul]; exact h3
      exact nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_right hItop h4)
    -- Step 6: `g = 0` a.e. on `(a, b)` contradicts `0 < c g` a.e.
    have hg0 : ∀ᵐ t ∂(volume.restrict (Ioo a b)), g t = 0 :=
      (lintegral_eq_zero_iff' hg.restrict).1 (nonpos_iff_eq_zero.1 (hI.trans hI0.le))
    apply hnull
    filter_upwards [hae, hg0] with t ht ht0
    rw [hI0, ht0] at ht
    simp at ht
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0

/-- **Simon Ch. 6, 3.2(3) and 2.11–2.12**: if `T = τ(M, θ, ξ)` in the open set `U`, then
(i) `M_W(T) = μ_R(W)` for every open `W`, where `μ_R = θ Hⁿ⌞M`, and (ii) `spt T = U ∩ spt μ_R`.
`M_W(T) ≤ μ_R(W)` because admissible forms pair with `ξ` to at most `1`; `μ_R(W) ≤ M_W(T)` by
smoothing the dual covector field of `ξ` (Lusin); (ii) follows from (i) alone. -/
theorem Submission.dor_imrep_massOn_eq_measure_and_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support := by
  intro P n U T R hU hR
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  exact ⟨hmass, Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass⟩
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]
/-- Steps 3–5 of the orientation push-forward (Simon 6.3.4–3.5, with the orthonormal basis of
`span v` chosen by Gram–Schmidt): a linearly independent family `v` in `ℝᴾ` has an orthonormal
frame `σ` with the same span such that `A = (⟨σᵢ, vⱼ⟩)` satisfies `det(⟨vᵢ, vⱼ⟩) = (det A)²`,
`det A ≠ 0` and `|det A| ≤ ∏ᵢ |vᵢ|`.  Gram–Schmidt in `W = span v` makes `A` the upper-triangular
matrix of `v` in an orthonormal basis of `W`, and Parseval gives `(⟨vᵢ, vⱼ⟩) = AᵀA`. -/
theorem Submission.dpf_exists_orthonormal_frame_det_gram : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Submodule.span ℝ (Set.range v) ∧ Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ^ 2 ∧ Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ≠ 0 ∧ |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| ≤ ∏ i, ‖v i‖ := by
  intro P n v hv
  set W := Submodule.span ℝ (Set.range v)
  -- `v` regarded in `W` is a linearly independent spanning family `w`
  let w : Fin n → W := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp W.subtype hv
  have hspan_w : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  -- the Gram–Schmidt orthonormal basis `b` of `W`, and `σ = b` regarded in `ℝᴾ`
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  -- `A` is the (upper-triangular) matrix of `w` in the basis `b`
  have hA : (Matrix.of fun i j => inner ℝ (σ i) (v j)) = b.toBasis.toMatrix w := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, Submodule.coe_inner]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) =
      ∏ i, inner ℝ (σ i) (v i) := by
    rw [hA, ← Module.Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    rfl
  refine ⟨σ, b.orthonormal.comp_linearIsometry W.subtypeₗᵢ, ?_, ?_, ?_, ?_⟩
  · -- `span σ = W`
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
    have hσ : Set.range σ = W.subtype '' Set.range b := Set.range_comp _ _
    rw [hσ, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
  · -- Parseval: `(⟨vᵢ, vⱼ⟩) = AᵀA`
    have hG : (Matrix.of fun i j => inner ℝ (v i) (v j)) =
        Matrix.transpose (Matrix.of fun i j => inner ℝ (σ i) (v j)) *
          Matrix.of fun i j => inner ℝ (σ i) (v j) := by
      ext i j
      have hp := b.sum_inner_mul_inner (w i) (w j)
      simp only [Submodule.coe_inner] at hp
      rw [Matrix.mul_apply, Matrix.of_apply, ← hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, real_inner_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  · -- `det A = det_b w` is a unit
    rw [hA, ← Module.Basis.det_apply]
    exact ((Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩).ne_zero
  · -- Cauchy–Schwarz on the diagonal entries
    rw [hdet, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |inner ℝ (σ i) (v i)| ≤ ‖σ i‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖v i‖ := by rw [show ‖σ i‖ = 1 from b.norm_eq_one i, one_mul]

/-- **Simon Ch. 6, 2.27–2.29 and 3.9** (analytic toolkit, and the Lipschitz push-forward of
integer multiplicity currents vanishing off a compact set).  (i) If `X = τ(M, θ, ξ)` in `ℝᴾ`
vanishes off the compact `E`, then `μ_R(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(X) = 0`, so `Hᵏ(M ∖ E) = 0` (`θ ≥ 1`
on `M`), `M(X) = μ_R(ℝᴾ) = μ_R(E) < ∞`, and `R.action γ` depends only on `γ|_E`.  (ii) Hadamard:
`|α(v)| ≤ |α| ∏ᵢ |vᵢ|`, from `|α(v)| ≤ |α| det(⟨vᵢ, vⱼ⟩)^{1/2}` and a Gram–Schmidt frame with
`det(⟨vᵢ, vⱼ⟩) = (det A)²`, `|det A| ≤ ∏ᵢ |vᵢ|`.  (iii) `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` a.e. with `τ`
orthonormal, so `|θ ξ(γ)| ≤ c θ` and `|R.action γ| ≤ c μ_R(ℝᴾ)`.  (iv) `F_j = ψ_j ⋆ F` with
normalized `C^∞` bumps `ψ_j` supported in `B_{1/(j+1)}(0)` are `Λ`-Lipschitz and
`|F_j - F| ≤ Λ/(j+1)`.  (v) A smooth Urysohn function for `cthickening 1 E ⊆ thickening 2 E`.
(vi) Given (IPF), `push k F X = Y_X(F)` for `Y_X` from (IPF) for a chosen finite-mass
representation of `X`: it is integer multiplicity, depends only on `F|_E`, is the limit of
`X(η_j) = R.action(F_j^#ω)`, has `M ≤ Λᵏ M(X)` (Hadamard with `‖DF_j‖ ≤ Λ`, then (iii)), and
vanishes off `F(E)` (for large `j`, `F_j(E)` avoids `spt ω`). -/
theorem Submission.dor_lmb_fcdp_toolkit_push : ((∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ') ∧ (∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal) ∧ (∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop) ∧ ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1) ∧ ((∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (Λ : NNReal) (F : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ (∀ F' : Euclid P → Euclid P, LipschitzWith Λ F' → EqOn F F' E → push k F X = push k F' X) ∧ (∀ (Fs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (push k F X ω))) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0) := by
  -- (i) compactly vanishing integer multiplicity representations
  have hi : ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ' := by
    intro P k X R E hR hE hXE
    have hmass :=
      (Submission.dor_imrep_massOn_eq_measure_and_support P k univ X R isOpen_univ hR).1
    have hEm : MeasurableSet E := hE.isClosed.measurableSet
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
    -- `μ_R(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(X) = 0`: admissible forms supported off `E` are killed by `X`
    have hμEc : R.measure Eᶜ = 0 := by
      rw [← hmass Eᶜ hE.isClosed.isOpen_compl]
      refine le_antisymm (sSup_le ?_) bot_le
      rintro _ ⟨ω, ⟨hωE, -⟩, rfl⟩
      dsimp only
      rw [hXE ω (subset_compl_iff_disjoint_right.mp hωE), ENNReal.ofReal_zero]
    -- `Hᵏ(M ∖ E) = 0`, since `θ ≥ 1` on `M`
    have hnull : μHE[k] (R.carrier \ E) = 0 := by
      rw [IMRep.measure, withDensity_apply_eq_zero' hθ.aemeasurable,
        Measure.restrict_apply' R.measurableSet_carrier] at hμEc
      refine measure_mono_null ?_ hμEc
      intro x hx
      exact ⟨⟨Nat.cast_ne_zero.mpr (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
    -- `Hᵏ⌞M`-a.e. point lies in `E`
    have hae : ∀ᵐ x ∂(μHE[k].restrict R.carrier), x ∈ E := by
      rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
      refine measure_mono_null ?_ hnull
      intro x hx
      exact ⟨hx.2, hx.1⟩
    -- `μ_R(ℝᴾ) = μ_R(E) = ∫_{M ∩ E} θ dHᵏ < ∞`
    have hfin : R.measure univ ≠ ∞ := by
      rw [← measure_add_measure_compl hEm, hμEc, add_zero, IMRep.measure, withDensity_apply _ hEm,
        Measure.restrict_restrict hEm, inter_comm]
      exact R.locallyIntegrable_mult E hE (subset_univ E)
    refine ⟨hnull, hmass univ isOpen_univ, hfin, fun γ γ' hγ => ?_⟩
    -- the integrands agree on `E`, hence `Hᵏ⌞M`-a.e.
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hγ hx]
  -- (ii) Hadamard's inequality for the Euclidean coefficient norm
  have hii : ∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ := by
    intro N m α v
    by_cases hv : LinearIndependent ℝ v
    · obtain ⟨σ, -, -, hG, -, hA⟩ := Submission.dpf_exists_orthonormal_frame_det_gram N m v hv
      calc |α v| ≤ covectorEuclideanNorm α *
            Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j))) :=
            (Submission.covectorEuclideanNorm_gram_bounds N m).1 α v
        _ = covectorEuclideanNorm α * |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| := by
            rw [hG, Real.sqrt_sq_eq_abs]
        _ ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ :=
            mul_le_mul_of_nonneg_left hA (covectorEuclideanNorm_nonneg α)
    · -- a linearly dependent family is killed by every alternating map
      rw [show α v = 0 from α.toAlternatingMap.map_linearDependent v hv, abs_zero]
      exact mul_nonneg (covectorEuclideanNorm_nonneg α)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
  -- (iii) the action is bounded by `c μ_R(ℝᴾ)` when `γ` is bounded by `c` on orthonormal frames
  have hiii : ∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal := by
    intro P k U R γ c hfin hc hγ
    have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
    -- `∫⁻ θ d(Hᵏ⌞M) = μ_R(ℝᴾ)`, so `θ` is `Hᵏ⌞M`-integrable with `∫ θ d(Hᵏ⌞M) = μ_R(ℝᴾ)`
    have hlint : ∫⁻ x, ENNReal.ofReal (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) =
        R.measure univ := by
      rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_congr fun x => ENNReal.ofReal_natCast _
    have hθ0 : 0 ≤ᵐ[μHE[k].restrict R.carrier] fun x => (R.mult x : ℝ) :=
      ae_of_all _ fun x => Nat.cast_nonneg _
    have hθint : Integrable (fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) :=
      ⟨hθm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hθ0).mpr (hlint ▸ hfin.lt_top)⟩
    have hθI : ∫ x, (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) = (R.measure univ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hθ0 hθm.aestronglyMeasurable, hlint]
    rw [← Real.norm_eq_abs, IMRep.action]
    calc ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (γ x) ∂μHE[k]‖
        ≤ ∫ x, c * (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) := by
          refine norm_integral_le_of_norm_le (hθint.const_mul c) ?_
          -- a.e. `ξ(x)(β) = ±β(τ)` with `τ` orthonormal, so `|ξ(x)(γ x)| = |γ(x)(τ)| ≤ c`
          filter_upwards [hγ, R.orients] with x hx hor
          obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hor
          rw [norm_mul, Real.norm_natCast, mul_comm c]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rcases hξ with h | h
          · rw [h, Real.norm_eq_abs]
            exact hx τ hτ
          · rw [h, norm_neg, Real.norm_eq_abs]
            exact hx τ hτ
      _ = c * (R.measure univ).toReal := by rw [integral_const_mul, hθI]
  -- (iv) `C^∞` `Λ`-Lipschitz approximations by mollification
  have hiv : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop := by
    intro N N' Λ F hF
    -- normalized `C^∞` bumps `ψ = φ / ∫ φ` supported in `B_r(0)`
    have hker : ∀ r : ℝ, 0 < r → ∃ ψ : Euclid N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧ support ψ ⊆ ball 0 r := by
      intro r hr
      let φ : ContDiffBump (0 : Euclid N) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hr
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    choose ψ hψ hψc hψ0 hψ1 hψs using fun j : ℕ =>
      hker (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hFi : LocallyIntegrable F volume := hF.continuous.locallyIntegrable
    refine ⟨fun j => convolution (ψ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      fun j => (hψc j).contDiff_convolution_left _ (hψ j) hFi, fun j => ?_, ?_⟩
    · -- `ψ_j ⋆ F` is `Λ`-Lipschitz: it averages the differences `F(x - t) - F(x' - t)`
      have hconv : ∀ x, Integrable (fun t => ψ j t • F (x - t)) volume := fun x =>
        ((hψc j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hψ j).continuous hFi
          x).integrable
      refine LipschitzWith.of_dist_le_mul fun x x' => ?_
      dsimp only
      rw [dist_eq_norm, convolution_def, convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
      rw [← integral_sub (hconv x) (hconv x')]
      calc ‖∫ t, (ψ j t • F (x - t) - ψ j t • F (x' - t))‖ ≤ ∫ t, ψ j t * (Λ * dist x x') := by
            refine norm_integral_le_of_norm_le
              (((hψ j).continuous.integrable_of_hasCompactSupport (hψc j)).mul_const _)
              (ae_of_all _ fun t => ?_)
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hψ0 j t)]
            refine mul_le_mul_of_nonneg_left ?_ (hψ0 j t)
            rw [← dist_eq_norm]
            calc dist (F (x - t)) (F (x' - t)) ≤ Λ * dist (x - t) (x' - t) := hF.dist_le_mul _ _
              _ = Λ * dist x x' := by rw [dist_sub_right]
        _ = Λ * dist x x' := by rw [integral_mul_const, hψ1 j, one_mul]
    · -- `dist((ψ_j ⋆ F)(x), F(x)) ≤ Λ/(j+1)`, as `F` moves by `≤ Λ/(j+1)` on `B_{1/(j+1)}(x)`
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hlim : Tendsto (fun j : ℕ => (Λ : ℝ) * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ : ℝ)
        rwa [mul_zero] at this
      filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj x
      rw [dist_comm]
      refine (dist_convolution_le (by positivity) (hψs j) (hψ0 j) (hψ1 j)
        hF.continuous.aestronglyMeasurable fun y hy => ?_).trans_lt hj
      calc dist (F y) (F x) ≤ Λ * dist y x := hF.dist_le_mul y x
        _ ≤ Λ * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left (mem_ball.mp hy).le Λ.coe_nonneg
  -- (v) smooth cut-off functions
  have hv : ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1 := by
    intro P E hE
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := 2) (E := E)) (isClosed_cthickening (δ := 1) (E := E))
      (cthickening_subset_thickening' two_pos one_lt_two E)
    refine ⟨χ, thickening 1 E, hχ, ?_, fun x => hχr ⟨x, rfl⟩, isOpen_thickening,
      self_subset_thickening one_pos E,
      fun x hx => (hχ1 x).mp (thickening_subset_cthickening 1 E hx)⟩
    exact HasCompactSupport.of_support_subset_isCompact (hE.cthickening (r := 2))
      (hχs ▸ thickening_subset_cthickening 2 E)
  refine ⟨⟨hi, hii, hiii, hiv, hv⟩, ?_⟩
  -- (vi) the push-forward operator, assuming (IPF)
  intro hIPF P
  -- for `X` with a finite-mass IM representation `R`, choose `Y_X` from (IPF) for `R`
  obtain ⟨Ych, hYch⟩ : ∃ Ych : ∀ k : ℕ, GeometricCurrentOn (univ : Set (Euclid P)) k →
      (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k,
      ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k),
        (∃ R : IMRep (univ : Set (Euclid P)) k, R.Represents X ∧ R.measure univ ≠ ∞) →
        ∃ (R : IMRep (univ : Set (Euclid P)) k) (hR : R.measure univ ≠ ∞),
          R.Represents X ∧ Ych k X = Classical.choose (hIPF P P k R hR) := by
    classical
    exact ⟨fun k X => if h : ∃ R : IMRep (univ : Set (Euclid P)) k, R.Represents X ∧
      R.measure univ ≠ ∞ then Classical.choose (hIPF P P k h.choose h.choose_spec.2)
      else fun _ => X, fun k X h => ⟨h.choose, h.choose_spec.2, h.choose_spec.1, dite_eq_left h⟩⟩
  refine ⟨fun k F X => Ych k X F, ?_⟩
  rintro k Λ F E X hF hE ⟨R', hR'⟩ hXE
  dsimp only
  -- by (i) every representation of `X` has finite mass
  obtain ⟨R, hRfin, hRX, hY⟩ := hYch k X ⟨R', hR', (hi P k X R' E hR' hE hXE).2.2.1⟩
  obtain ⟨hYa, hYb⟩ := Classical.choose_spec (hIPF P P k R hRfin)
  rw [← hY] at hYa hYb
  obtain ⟨hnull, hmass, -, hloc⟩ := hi P k X R E hRX hE hXE
  have hae : ∀ᵐ x ∂(μHE[k].restrict R.carrier), x ∈ E := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null ?_ hnull
    intro x hx
    exact ⟨hx.2, hx.1⟩
  -- `C^∞` `Λ`-Lipschitz `F_j → F` by (iv); `push k F X (ω) = lim R.action(F_j^#ω)`
  obtain ⟨Fs, hFs, hFsL, hFsU⟩ := hiv P P Λ F hF
  have hFs1 : ∀ j, ContDiff ℝ 1 (Fs j) := fun j => (hFs j).of_le (by exact_mod_cast le_top)
  have hlim := (hYa F Λ hF).2 Fs hFs1 hFsL hFsU
  refine ⟨(hYa F Λ hF).1, fun F' hF' hFF' => hYb F F' Λ hF hF' ?_,
    fun Fs' ω ηs hFs' hFsL' hFsU' hη => ?_, ?_, fun ω hω => ?_⟩
  · -- (P2): `F = F'` on `E`, hence `Hᵏ⌞M`-a.e.
    filter_upwards [hae] with x hx using hFF' hx
  · -- (P3): `X(η_j) = R.action(η_j) = R.action(F_j^#ω) → push k F X (ω)`
    refine ((hYa F Λ hF).2 Fs' hFs' hFsL' hFsU' ω).congr fun j => ?_
    rw [hRX (ηs j)]
    exact hloc _ _ fun x hx => (hη j x hx).symm
  · -- (P4): for admissible `ω`, `|R.action(F_j^#ω)| ≤ Λᵏ μ_R(ℝᴾ)` by (ii) and (iii)
    rw [hmass, GeometricCurrentOn.mass, GeometricCurrentOn.massOn]
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨-, hω1⟩, rfl⟩
    dsimp only
    have hbd : ∀ j, |R.action (fun x => ((ω : DifferentialForm (Euclid P) k)
        (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))| ≤
        (Λ : ℝ) ^ k * (R.measure univ).toReal := by
      intro j
      refine hiii P k univ R _ _ hRfin (by positivity) (ae_of_all _ fun x τ hτ => ?_)
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      calc |(ω : DifferentialForm (Euclid P) k) (Fs j x) (fderiv ℝ (Fs j) x ∘ τ)|
          ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) (Fs j x)) *
            ∏ i, ‖(fderiv ℝ (Fs j) x ∘ τ) i‖ := hii P k _ _
        _ ≤ 1 * ∏ _i : Fin k, (Λ : ℝ) := by
          refine mul_le_mul (hω1 _)
            (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
            (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
          -- `‖DF_j(x) τᵢ‖ ≤ ‖DF_j(x)‖ ≤ Λ`
          calc ‖(fderiv ℝ (Fs j) x ∘ τ) i‖ ≤ ‖fderiv ℝ (Fs j) x‖ * ‖τ i‖ :=
                (fderiv ℝ (Fs j) x).le_opNorm _
            _ ≤ Λ := by
                rw [hτ.1 i, mul_one]
                exact norm_fderiv_le_of_lipschitz ℝ (hFsL j)
        _ = (Λ : ℝ) ^ k := by rw [one_mul, Fin.prod_const]
    have hle : Ych k X F ω ≤ (Λ : ℝ) ^ k * (R.measure univ).toReal :=
      le_of_tendsto' (hlim ω) fun j => (le_abs_self _).trans (hbd j)
    calc ENNReal.ofReal (Ych k X F ω)
        ≤ ENNReal.ofReal ((Λ : ℝ) ^ k * (R.measure univ).toReal) := ENNReal.ofReal_le_ofReal hle
      _ = (Λ : ℝ≥0∞) ^ k * R.measure univ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hRfin,
          ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
  · -- (P5): for large `j`, `F_j(E)` avoids `spt ω`, so `F_j^#ω = 0` on `E`
    obtain ⟨δ, hδ, hδK⟩ := (hE.image hF.continuous).exists_cthickening_subset_open
      (isClosed_tsupport _).isOpen_compl (subset_compl_iff_disjoint_left.mpr hω)
    have hev : ∀ᶠ j in atTop, R.action (fun x => ((ω : DifferentialForm (Euclid P) k)
        (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) = 0 := by
      filter_upwards [Metric.tendstoUniformly_iff.mp hFsU δ hδ] with j hj
      refine (hloc _ 0 fun x hx => ?_).trans ?_
      · have hmem : Fs j x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
          hδK (thickening_subset_cthickening δ _
            (mem_thickening_iff.mpr ⟨F x, mem_image_of_mem F hx, by rw [dist_comm]; exact hj x⟩))
        rw [image_eq_zero_of_notMem_tsupport hmem]
        ext v
        simp
      · simp [IMRep.action]
    exact tendsto_nhds_unique (hlim ω) (tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm))
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

/-- Step 4(d) of the local unit representation of `∂[[E]]` (Simon 7.5; Gram–Schmidt as in the
graph chart): if `a₁, …, aₙ` are linearly independent in `ℝᴾ`, the Gram determinant
`Γ = det(⟨aᵢ, aⱼ⟩)` is positive and `ξ = Γ^{-1/2} a₁ ∧ ⋯ ∧ aₙ`, i.e.
`⟨α, ξ⟩ = Γ^{-1/2} α(a₁, …, aₙ)`, is a unit orientation of `span a`.  For an orthonormal frame
`σ` of `span a` and `R = (⟨σᵢ, aⱼ⟩)`, `Γ = (det R)²` and `α(a) = det R · α(σ)`, so
`ξ = sign(det R) σ₁ ∧ ⋯ ∧ σₙ`. -/
theorem Submission.codim1_lur_normalized_wedge_orientation : ∀ (P n : ℕ) (a : Fin n → Euclid P), LinearIndependent ℝ a → 0 < Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i) (a j)) ∧ ∀ ξ : MultiVector P n, (∀ α : Covector (Euclid P) n, ξ α = (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i) (a j))))⁻¹ * α a) → IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range a)) := by
  intro P n a ha
  -- an orthonormal frame `σ` of `span a` with `Γ = (det R)²`, `R = (⟨σᵢ, aⱼ⟩)` invertible
  obtain ⟨σ, hσ, hspan, hgram, hdet, -⟩ :=
    Submission.dpf_exists_orthonormal_frame_det_gram P n a ha
  set d := Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (a j))
  refine ⟨hgram ▸ sq_pos_of_ne_zero hdet, fun ξ hξ => ⟨σ, hσ, hspan, ?_⟩⟩
  -- `α(a) = det R · α(σ)`, hence `⟨α, ξ⟩ = |det R|⁻¹ det R · α(σ)`
  have hξ' : ∀ α : Covector (Euclid P) n, ξ α = |d|⁻¹ * d * α σ := fun α => by
    rw [hξ, hgram, Real.sqrt_sq_eq_abs, mul_assoc,
      Submission.dgoj_covector_eq_det_mul_of_mem_span P n σ a hσ
        (fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩) α]
  rcases hdet.lt_or_gt with hneg | hpos
  · exact Or.inr fun α => by
      rw [hξ', abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hdet, neg_one_mul]
  · exact Or.inl fun α => by
      rw [hξ', abs_of_pos hpos, inv_mul_cancel₀ hdet, one_mul]
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound

/-- A mass-summable series of integer multiplicity densities converges `Hⁿ`-a.e. and integrates
termwise against test forms (the `L¹` convergence of the densities `θ_q ξ_q` in the proof of
Simon Ch. 6, Lemma 3.13).  With `g_r = 1_{M_r} θ_r`, `∫ g_r dHⁿ = μ_{R_r}(M_r) ≤ μ_{R_r}(U)`, so
`Σ_r g_r < ∞` `Hⁿ`-a.e.; as `‖ξ_r‖ ≤ 1` `Hⁿ`-a.e. on `M_r`, the densities `D_r = 1_{M_r} θ_r ξ_r`
satisfy `‖D_r‖ ≤ g_r`, so `η = Σ_r D_r` converges absolutely `Hⁿ`-a.e., and dominated convergence
for series with the bounds `(sup ‖ω‖) g_r` gives `Σ_r τ(M_r, θ_r, ξ_r)(ω) = ∫ ⟨ω, η⟩ dHⁿ`. -/
theorem Submission.dor_lmb_fc_ims_density_series : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), ∑' r, (R r).measure U ≠ ∞ → ∃ η : Euclid P → MultiVector P n, (∀ᵐ x ∂μHE[n], HasSum (fun r => (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x) (η x)) ∧ ∀ ω : TestFormOn U n, HasSum (fun r => (R r).action (ω : DifferentialForm (Euclid P) n)) (∫ x, η x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) := by
  have hnorm := Submission.unit_orientation_norm_le_one
  intro P n U R hfin
  set D : ℕ → Euclid P → MultiVector P n := fun r x =>
    (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x
  set g : ℕ → Euclid P → ℝ := fun r x =>
    (R r).carrier.indicator (fun y => ((R r).mult y : ℝ)) x
  have hg_nonneg : ∀ r x, 0 ≤ g r x := fun r x =>
    Set.indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  have hmult_meas : ∀ r, Measurable (fun y => ((R r).mult y : ℝ)) := fun r =>
    measurable_from_nat.comp (R r).measurable_mult
  have hg_meas : ∀ r, Measurable (g r) := fun r =>
    (hmult_meas r).indicator (R r).measurableSet_carrier
  -- ∫⁻ g_r dHⁿ = μ_{R_r}(M_r) ≤ μ_{R_r}(U)
  have hg_lint : ∀ r, ∫⁻ x, ENNReal.ofReal (g r x) ∂μHE[n] ≤ (R r).measure U := by
    intro r
    have hM := (R r).measurableSet_carrier
    have h1 : (fun x => ENNReal.ofReal (g r x)) =
        (R r).carrier.indicator (fun y => ((R r).mult y : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ (R r).carrier <;> simp [g, hx]
    calc ∫⁻ x, ENNReal.ofReal (g r x) ∂μHE[n]
        = ∫⁻ x in (R r).carrier, ((R r).mult x : ℝ≥0∞) ∂μHE[n] := by
          rw [h1, lintegral_indicator hM]
      _ = (R r).measure (R r).carrier := by
          rw [IMRep.measure, withDensity_apply _ hM, Measure.restrict_restrict hM, inter_self]
      _ ≤ (R r).measure U := measure_mono (R r).carrier_subset
  have hsum_lint : ∫⁻ x, ∑' r, ENNReal.ofReal (g r x) ∂μHE[n] ≠ ∞ := by
    rw [lintegral_tsum (fun r => (hg_meas r).ennreal_ofReal.aemeasurable)]
    exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hg_lint)
  have hfinite : ∀ᵐ x ∂μHE[n], ∑' r, ENNReal.ofReal (g r x) < ∞ :=
    ae_lt_top (Measurable.tsum fun r => (hg_meas r).ennreal_ofReal) hsum_lint
  have hg_summ : ∀ᵐ x ∂μHE[n], Summable (fun r => g r x) := by
    filter_upwards [hfinite] with x hx
    have := ENNReal.summable_toReal hx.ne
    simpa [ENNReal.toReal_ofReal (hg_nonneg _ x)] using this
  -- ‖D_r(x)‖ ≤ g_r(x) a.e., from ‖ξ‖ ≤ 1 for unit orientations
  have hD_bound : ∀ r, ∀ᵐ x ∂μHE[n], ‖D r x‖ ≤ g r x := by
    intro r
    have h := (R r).orients
    rw [ae_restrict_iff' (R r).measurableSet_carrier] at h
    filter_upwards [h] with x hx
    by_cases hxM : x ∈ (R r).carrier
    · obtain ⟨Q, -, hQ⟩ := hx hxM
      have h1 := hnorm P n Q _ hQ
      simp only [D, g, Set.indicator_of_mem hxM]
      calc ‖((R r).mult x : ℝ) • (R r).orient x‖
          ≤ ‖((R r).mult x : ℝ)‖ * ‖(R r).orient x‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ ‖((R r).mult x : ℝ)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ((R r).mult x : ℝ) := by rw [mul_one, Real.norm_natCast]
    · simp only [D, g, Set.indicator_of_notMem hxM]
      exact ContinuousLinearMap.opNorm_zero.le
  have hD_bound' : ∀ᵐ x ∂μHE[n], ∀ r, ‖D r x‖ ≤ g r x := ae_all_iff.2 hD_bound
  have hD_summ : ∀ᵐ x ∂μHE[n], Summable (fun r => D r x) := by
    filter_upwards [hD_bound', hg_summ] with x h1 h2
    exact Summable.of_norm_bounded (E := MultiVector P n) h2 h1
  refine ⟨fun x => ∑' r, D r x, ?_, ?_⟩
  · filter_upwards [hD_summ] with x hx
    exact hx.hasSum
  · intro ω
    set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
    have hw_cont : Continuous w := ContDiff.continuous ω.property.1.1
    obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖w x‖ ≤ B :=
      hw_cont.bounded_above_of_compact_support ω.property.1.2
    have hDr_meas : ∀ r, AEStronglyMeasurable (D r) μHE[n] := by
      intro r
      refine (aestronglyMeasurable_indicator_iff (R r).measurableSet_carrier).2 ?_
      exact (hmult_meas r).aestronglyMeasurable.smul (R r).aestronglyMeasurable_orient
    have hF_meas : ∀ r, AEStronglyMeasurable (fun x => D r x (w x)) μHE[n] := fun r =>
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hDr_meas r).prodMk hw_cont.aestronglyMeasurable)
    have h_bound : ∀ r, ∀ᵐ x ∂μHE[n], ‖D r x (w x)‖ ≤ B * g r x := by
      intro r
      filter_upwards [hD_bound r] with x hx
      calc ‖D r x (w x)‖ ≤ ‖D r x‖ * ‖w x‖ := (D r x).le_opNorm _
        _ ≤ g r x * B := mul_le_mul hx (hB x) (norm_nonneg _) (hg_nonneg r x)
        _ = B * g r x := mul_comm _ _
    have h_summ : ∀ᵐ x ∂μHE[n], Summable (fun r => B * g r x) :=
      hg_summ.mono fun x hx => hx.mul_left B
    have h_int : Integrable (fun x => ∑' r, B * g r x) μHE[n] := by
      have hG : Integrable (fun x => (∑' r, ENNReal.ofReal (g r x)).toReal) μHE[n] :=
        integrable_toReal_of_lintegral_ne_top
          (Measurable.tsum fun r => (hg_meas r).ennreal_ofReal).aemeasurable hsum_lint
      refine (hG.const_mul B).congr ?_
      filter_upwards [hg_summ] with x hx
      rw [tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun r => hg_nonneg r x) hx,
        ENNReal.toReal_ofReal (tsum_nonneg fun r => hg_nonneg r x)]
    have hlim : ∀ᵐ x ∂μHE[n], HasSum (fun r => D r x (w x)) ((∑' r, D r x) (w x)) := by
      filter_upwards [hD_summ] with x hx
      exact hx.hasSum.mapL (ContinuousLinearMap.apply ℝ ℝ (w x))
    have hHS := hasSum_integral_of_dominated_convergence (fun r x => B * g r x) hF_meas
      h_bound h_summ h_int hlim
    convert hHS using 1
    funext r
    have hM := (R r).measurableSet_carrier
    have h1 : (fun x => D r x (w x)) =
        (R r).carrier.indicator (fun x => ((R r).mult x : ℝ) * (R r).orient x (w x)) := by
      funext x
      by_cases hx : x ∈ (R r).carrier <;> simp [D, hx]
    rw [h1, integral_indicator hM]
    rfl
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA
/-- **The cylinder over a rectifiable set** (the carrier of `[[(0,1)]] × T`, Simon Ch. 6, 2.17–2.21
and the proof of 2.27): let `M ⊆ ℝᴾ` be Borel and countably `k`-rectifiable with `Hᵏ(M) < ∞`, and
let `ι(t, x) = (t, x₁, …, x_P)`.  There is a Borel `C ⊆ ι((0,1) × M)` which is countably
`(k+1)`-rectifiable, satisfies `Hᵏ⁺¹⌞C = ι_#(L¹⌞(0,1) ⊗ Hᵏ⌞M)`, and for `Hᵏ⁺¹`-a.e. `y ∈ C`, if `M`
has approximate tangent space `Q` at `(y₁, …, y_P)` then `C` has approximate tangent space
`ℝe₀ ⊕ Q` at `y`.  Cut `M` into bi-Lipschitz pieces `F i (B i)` up to an `Hᵏ`-null set and take
`C = ι((0,1) × ⋃ F i (B i))`, parametrized by `G i(b) = ι(b₀, F i(b₁, …, b_k))` on
`π⁻¹((0,1) × B i)`, `π(b) = (b₀, (b₁, …, b_k))`.  The Gram matrix of `DG i(b)` is
`diag(1, Gram DF i)`, so `JG i = JF i ∘ π₂`; the area formula for `G i` and for `F i`, the measure
preserving `π` and Tonelli give the measure identity.  The tangent planes come from the piece lemma
for `F i` on `M` and for `G i` on `C`, with `range DG i(b) = ℝe₀ ⊕ range DF i(π₂ b)`. -/
theorem Submission.dor_lmb_fcdp_cylinder : ∀ (P k : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable k M → μHE[k] M ≠ ∞ → ∃ C : Set (Euclid (P + 1)), MeasurableSet C ∧ C ⊆ (fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M) ∧ CountablyRectifiable (k + 1) C ∧ μHE[k + 1].restrict C = ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict M)).map (fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) ∧ ∀ᵐ y ∂(μHE[k + 1].restrict C), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k M (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P) Q → HasApproximateTangentSpaceAt (k + 1) C y (Submodule.span ℝ (insert (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) ((fun v : Euclid P => (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Q : Set (Euclid P))))) := by
  intro P k M hM hrect hfin
  -- `ι_n(t, x) = (t, x₁, …, x_n)` and `π_n(y) = (y₀, (y₁, …, y_n))`, mutually inverse linear maps
  have hι : ∀ n : ℕ, ∃ L : ℝ × Euclid n →L[ℝ] Euclid (n + 1), ∀ p, L p =
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ) : Euclid (n + 1)) := by
    intro n
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun p =>
          (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ) : Euclid (n + 1))
        map_add' := ?_
        map_smul' := ?_ }, fun p => rfl⟩
    · intro p q
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · intro c p
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hπ : ∀ n : ℕ, ∃ L : Euclid (n + 1) →L[ℝ] ℝ × Euclid n, ∀ y,
      L y = (WithLp.ofLp y 0, (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid n)) := by
    intro n
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun y => (WithLp.ofLp y 0, (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid n))
        map_add' := ?_
        map_smul' := ?_ }, fun p => rfl⟩
    · intro p q
      ext <;> simp [Fin.tail]
    · intro c p
      ext <;> simp [Fin.tail]
  choose ιL hιL using hι
  choose πL hπL using hπ
  have hπι : ∀ n p, πL n (ιL n p) = p := by
    intro n p
    rw [hιL, hπL]
    simp
  have hιπ : ∀ n y, ιL n (πL n y) = y := by
    intro n y
    rw [hπL, hιL]
    simp
  have hinner : ∀ n p q, inner ℝ (ιL n p) (ιL n q) = p.1 * q.1 + inner ℝ p.2 q.2 := by
    intro n p q
    rw [hιL, hιL, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  have hnorm : ∀ n p, ‖ιL n p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
    intro n p
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner, sq]
  have hιinj : ∀ n, Injective (ιL n) := fun n => LeftInverse.injective (hπι n)
  -- A1: `π_n` maps Lebesgue measure on `ℝⁿ⁺¹` to Lebesgue measure on `ℝ × ℝⁿ`
  have hπmp : ∀ n, MeasurePreserving (πL n) volume volume := by
    intro n
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin n))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin (n + 1))))
    convert h using 1
    funext y
    rw [hπL]
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  have hπe0 : ∀ n, πL n (EuclideanSpace.single 0 1) = (1, 0) := by
    intro n
    rw [hπL]
    ext
    · simp
    · simp [Fin.tail]
  have hπes : ∀ n (j : Fin n),
      πL n (EuclideanSpace.single j.succ 1) = (0, EuclideanSpace.single j 1) := by
    intro n j
    rw [hπL]
    ext l
    · simp
    · simp [Fin.tail, PiLp.single_apply]
  -- the statement's `ι`, `J`, `ê₀` and `pr` in terms of `ι_P` and `π_P`
  have hιfun : (fun p : ℝ × Euclid P =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
      ιL P := funext fun p => (hιL P p).symm
  have hJfun : (fun v : Euclid P =>
      (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
      fun v => ιL P (0, v) := funext fun v => (hιL P (0, v)).symm
  have he0 : (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) = ιL P (1, 0) := by
    rw [← hπe0, hιπ]
  have hpr : ∀ y : Euclid (P + 1),
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P) = (πL P y).2 := fun y => by rw [hπL]
  rw [hιfun, hJfun, he0]
  simp only [hpr]
  -- B1: the bi-Lipschitz pieces `F i (B i)` of `M` (accepted `dpf_rectifiable_bilipschitz_pieces`)
  obtain ⟨F, B, m, hFL, hB, hm, hbi, hdiff, hFBm, hFBM, hdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P k M hM hrect
  choose L hL using hFL
  have hFinj : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have h1 := hbi i a ha a' ha'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖a - a'‖ ≤ 0 := by nlinarith [norm_nonneg (a - a'), hm i]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- `A i = F i (B i)`, `C i = ι((0,1) × A i)`, `G i = ι ∘ (id × F i) ∘ π` on
  -- `Bh i = π⁻¹((0,1) × B i)`
  set A : ℕ → Set (Euclid P) := fun i => F i '' B i
  set C : ℕ → Set (Euclid (P + 1)) := fun i => ιL P '' (Ioo (0 : ℝ) 1 ×ˢ A i)
  set G : ℕ → Euclid (k + 1) → Euclid (P + 1) := fun i b => ιL P ((πL k b).1, F i (πL k b).2)
  set Bh : ℕ → Set (Euclid (k + 1)) := fun i => πL k ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ B i)
  have hmeas_img : ∀ T : Set (ℝ × Euclid P), MeasurableSet T → MeasurableSet (ιL P '' T) :=
    fun T hT => hT.image_of_continuousOn_injOn (ιL P).continuous.continuousOn (hιinj P).injOn
  have hCm : ∀ i, MeasurableSet (C i) := fun i => hmeas_img _ (measurableSet_Ioo.prod (hFBm i))
  have hCU : ιL P '' (Ioo (0 : ℝ) 1 ×ˢ ⋃ i, A i) = ⋃ i, C i := by
    rw [prod_iUnion, image_iUnion]
  have hCdisj : Pairwise (Disjoint on C) := fun i j hij =>
    (disjoint_image_iff (hιinj P)).mpr (disjoint_prod.mpr (Or.inr (hdisj hij)))
  have hBhm : ∀ i, MeasurableSet (Bh i) := fun i =>
    (measurableSet_Ioo.prod (hB i)).preimage (πL k).continuous.measurable
  have hGC : ∀ i, G i '' Bh i = C i := by
    intro i
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨((πL k b).1, F i (πL k b).2), ⟨hb.1, mem_image_of_mem _ hb.2⟩, rfl⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, u, hu, rfl⟩, rfl⟩
      refine ⟨ιL k (t, u), ?_, ?_⟩
      · show πL k (ιL k (t, u)) ∈ Ioo (0 : ℝ) 1 ×ˢ B i
        rw [hπι]
        exact ⟨ht, hu⟩
      · show ιL P ((πL k (ιL k (t, u))).1, F i (πL k (ιL k (t, u))).2) = ιL P (t, F i u)
        rw [hπι]
  -- A2: `G i` is Lipschitz
  have hGlip : ∀ i, ∃ K, LipschitzWith K (G i) := fun i =>
    ⟨_, (ιL P).lipschitzWith.comp ((LipschitzWith.prod_fst.comp (πL k).lipschitzWith).prodMk
      ((hL i).comp (LipschitzWith.prod_snd.comp (πL k).lipschitzWith)))⟩
  -- A3: `DG i(b) c = ι(c₀, DF i(π₂ b)(π₂ c))`, which is injective
  have hGd : ∀ i, ∀ b ∈ Bh i, HasFDerivAt (G i) ((ιL P).comp
      (((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ (F i) (πL k b).2)).comp (πL k))) b := by
    intro i b hb
    have h1 : HasFDerivAt (Prod.map (id : ℝ → ℝ) (F i))
        ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ (F i) (πL k b).2)) (πL k b) :=
      HasFDerivAt.prodMap (πL k b) (hasFDerivAt_id _) (hdiff i _ hb.2).1.hasFDerivAt
    exact (ιL P).hasFDerivAt.comp b (h1.comp b (πL k).hasFDerivAt)
  have hDap : ∀ i b c, ((ιL P).comp (((ContinuousLinearMap.id ℝ ℝ).prodMap
      (fderiv ℝ (F i) (πL k b).2)).comp (πL k))) c =
      ιL P ((πL k c).1, fderiv ℝ (F i) (πL k b).2 (πL k c).2) := fun _ _ _ => rfl
  have hGdinj : ∀ i, ∀ b ∈ Bh i, Injective (fderiv ℝ (G i) b) := by
    intro i b hb c c' h
    rw [(hGd i b hb).fderiv, hDap, hDap] at h
    obtain ⟨h3, h4⟩ := Prod.mk.inj (hιinj P h)
    rw [← hιπ k c, ← hιπ k c']
    exact congrArg (ιL k) (Prod.ext h3 ((hdiff i _ hb.2).2 h4))
  -- A4: the Gram matrix of `DG i(b)` is `diag(1, Gram DF i(π₂ b))`, so `JG i(b) = JF i(π₂ b)`
  have hGJ : ∀ i, ∀ b ∈ Bh i, Real.sqrt (Matrix.det (Matrix.of fun a c : Fin (k + 1) =>
      inner ℝ (fderiv ℝ (G i) b (EuclideanSpace.single a 1))
        (fderiv ℝ (G i) b (EuclideanSpace.single c 1)))) =
      Real.sqrt (Matrix.det (Matrix.of fun a c : Fin k =>
        inner ℝ (fderiv ℝ (F i) (πL k b).2 (EuclideanSpace.single a 1))
          (fderiv ℝ (F i) (πL k b).2 (EuclideanSpace.single c 1)))) := by
    intro i b hb
    rw [(hGd i b hb).fderiv, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, hDap, hπe0, hπes, hinner, map_zero, inner_zero_left,
      inner_zero_right, Fin.succAbove_zero, mul_zero, zero_mul, add_zero, mul_one, Fin.val_zero,
      pow_zero, one_mul, Finset.sum_const_zero]
    congr 2
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hπes, zero_mul, zero_add]
  -- B5(d): `range DG i(b) = span{ê₀} ⊔ J(range DF i(π₂ b))`
  have hGrange : ∀ i, ∀ b ∈ Bh i,
      LinearMap.range (fderiv ℝ (G i) b : Euclid (k + 1) →ₗ[ℝ] Euclid (P + 1)) =
      Submodule.span ℝ (insert (ιL P (1, 0)) ((fun v => ιL P (0, v)) ''
        (LinearMap.range (fderiv ℝ (F i) (πL k b).2 : Euclid k →ₗ[ℝ] Euclid P) :
          Set (Euclid P)))) := by
    intro i b hb
    rw [(hGd i b hb).fderiv]
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hsplit : ιL P ((πL k c).1, fderiv ℝ (F i) (πL k b).2 (πL k c).2) =
          (πL k c).1 • ιL P (1, 0) + ιL P (0, fderiv ℝ (F i) (πL k b).2 (πL k c).2) := by
        rw [← map_smul, ← map_add]
        congr 1
        ext <;> simp
      show ((ιL P).comp (((ContinuousLinearMap.id ℝ ℝ).prodMap
        (fderiv ℝ (F i) (πL k b).2)).comp (πL k))) c ∈ _
      rw [hDap, hsplit]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert _ _)))
        (Submodule.subset_span (mem_insert_of_mem _ ⟨_, ⟨_, rfl⟩, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ (rfl | ⟨_, ⟨w, rfl⟩, rfl⟩)
      · exact ⟨EuclideanSpace.single 0 1,
          by simp only [ContinuousLinearMap.coe_coe, hDap, hπe0, map_zero]⟩
      · exact ⟨ιL k (0, w), by simp only [ContinuousLinearMap.coe_coe, hDap, hπι]⟩
  -- B5(b): `min(1, m i) |b − b'| ≤ |G i b − G i b'|` on `Bh i`
  have hGlow : ∀ i, ∀ b ∈ Bh i, ∀ b' ∈ Bh i, min 1 (m i) * ‖b - b'‖ ≤ ‖G i b - G i b'‖ := by
    intro i b hb b' hb'
    have h1 : G i b - G i b' =
        ιL P ((πL k b).1 - (πL k b').1, F i (πL k b).2 - F i (πL k b').2) := by
      rw [← map_sub]
      rfl
    have h2 : b - b' = ιL k ((πL k b).1 - (πL k b').1, (πL k b).2 - (πL k b').2) := by
      rw [show ((πL k b).1 - (πL k b').1, (πL k b).2 - (πL k b').2) = πL k (b - b') by
        rw [map_sub]; rfl, hιπ]
    have hX : ‖b - b'‖ ^ 2 =
        ((πL k b).1 - (πL k b').1) ^ 2 + ‖(πL k b).2 - (πL k b').2‖ ^ 2 := by
      rw [h2, hnorm]
    have hY : ‖G i b - G i b'‖ ^ 2 =
        ((πL k b).1 - (πL k b').1) ^ 2 + ‖F i (πL k b).2 - F i (πL k b').2‖ ^ 2 := by
      rw [h1, hnorm]
    have hμ0 : 0 < min 1 (m i) := lt_min one_pos (hm i)
    have hμT : min 1 (m i) * ‖(πL k b).2 - (πL k b').2‖ ≤ ‖F i (πL k b).2 - F i (πL k b').2‖ :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans (hbi i _ hb.2 _ hb'.2)
    have e1 : min 1 (m i) ^ 2 * ((πL k b).1 - (πL k b').1) ^ 2 ≤ ((πL k b).1 - (πL k b').1) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hμ0.le (min_le_left _ _))
    have e2 : (min 1 (m i) * ‖(πL k b).2 - (πL k b').2‖) ^ 2 ≤
        ‖F i (πL k b).2 - F i (πL k b').2‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hμ0.le (norm_nonneg _)) hμT 2
    refine (pow_le_pow_iff_left₀ (mul_nonneg hμ0.le (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).mp ?_
    rw [mul_pow, hX, hY, mul_add, ← mul_pow (min 1 (m i)) ‖(πL k b).2 - (πL k b').2‖]
    exact add_le_add e1 e2
  have hGinj : ∀ i, InjOn (G i) (Bh i) := by
    intro i b hb b' hb' h
    have h1 := hGlow i b hb b' hb'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖b - b'‖ ≤ 0 := by nlinarith [norm_nonneg (b - b'), lt_min one_pos (hm i)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  have hfinA : ∀ i, IsFiniteMeasure (μHE[k].restrict (A i)) := fun i =>
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top hfin (measure_mono (hFBM i)))
  -- A5–A6: `Hᵏ⁺¹⌞C i = ι_#(L¹⌞(0,1) ⊗ Hᵏ⌞A i)`, by the area formula (accepted
  -- `codim1_lura_gram_area_formula`) for `G i` and for `F i`, the measure preserving `π`
  -- and Tonelli
  have hpiece : ∀ i, μHE[k + 1].restrict (C i) =
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict (A i))).map (ιL P) := by
    intro i
    have := hfinA i
    obtain ⟨hJm, hGA⟩ := Submission.codim1_lura_gram_area_formula k P (F i)
    have hGAh := (Submission.codim1_lura_gram_area_formula (k + 1) (P + 1) (G i)).2 (Bh i)
      (hBhm i) (fun b hb => (hGd i b hb).differentiableAt) (hGdinj i) (hGinj i)
    ext S hS
    have hιS : MeasurableSet (ιL P ⁻¹' S) := (ιL P).continuous.measurable hS
    have hhm : Measurable fun p : ℝ × Euclid k => ENNReal.ofReal (Real.sqrt (Matrix.det
        (Matrix.of fun a c : Fin k => inner ℝ (fderiv ℝ (F i) p.2 (EuclideanSpace.single a 1))
          (fderiv ℝ (F i) p.2 (EuclideanSpace.single c 1))))) *
        S.indicator 1 (ιL P (p.1, F i p.2)) :=
      (ENNReal.measurable_ofReal.comp (hJm.comp measurable_snd)).mul
        ((measurable_one.indicator hS).comp ((ιL P).continuous.comp
          (continuous_fst.prodMk ((hL i).continuous.comp continuous_snd))).measurable)
    rw [← lintegral_indicator_one (μ := μHE[k + 1].restrict (C i)) hS, ← hGC i, hGAh,
      Measure.map_apply (ιL P).continuous.measurable hS, Measure.prod_apply hιS,
      setLIntegral_congr_fun (hBhm i) (fun b hb => by rw [hGJ i b hb])]
    rw [(hπmp k).setLIntegral_comp_preimage (measurableSet_Ioo.prod (hB i)) hhm,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hhm.aemeasurable]
    refine lintegral_congr fun t => ?_
    rw [← lintegral_indicator_one (measurable_prodMk_left hιS)]
    exact (hGA (B i) (hB i) (fun a ha => (hdiff i a ha).1) (fun a ha => (hdiff i a ha).2)
      (hFinj i) (fun x => S.indicator 1 (ιL P (t, x)))).symm
  -- B4: sum over the pieces, using `Hᵏ(M ∖ ⋃ A i) = 0`
  have hMA : μHE[k].restrict M = Measure.sum fun i => μHE[k].restrict (A i) := by
    rw [← Measure.restrict_iUnion hdisj hFBm]
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨hnull, ?_⟩)
    rw [sdiff_eq_empty.mpr (iUnion_subset hFBM), measure_empty]
  have hmeasure : μHE[k + 1].restrict (ιL P '' (Ioo (0 : ℝ) 1 ×ˢ ⋃ i, A i)) =
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict M)).map (ιL P) := by
    rw [hCU, Measure.restrict_iUnion hCdisj hCm, hMA, Measure.prod_sum_right,
      Measure.map_sum (ιL P).continuous.measurable.aemeasurable]
    exact congrArg Measure.sum (funext hpiece)
  -- B2: the cylinder `C = ι((0,1) × ⋃ A i) = ⋃ C i` is Borel with `Hᵏ⁺¹(C) = Hᵏ(M) < ∞`
  set Ctot := ιL P '' (Ioo (0 : ℝ) 1 ×ˢ ⋃ i, A i)
  have hCtotm : MeasurableSet Ctot :=
    hmeas_img _ (measurableSet_Ioo.prod (MeasurableSet.iUnion hFBm))
  have hCfin : μHE[k + 1] Ctot ≠ ∞ := by
    have : IsFiniteMeasure (μHE[k].restrict M) := isFiniteMeasure_restrict.mpr hfin
    have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
    rw [← Measure.restrict_apply_univ, hmeasure]
    exact measure_ne_top _ _
  -- B5: the tangent planes, piece by piece (accepted `dpf_approxTangent_ae_bilipschitz_piece`)
  have htan : ∀ i, ∀ᵐ y ∂(μHE[k + 1].restrict (C i)), ∀ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k M (πL P y).2 Q → HasApproximateTangentSpaceAt (k + 1) Ctot y
        (Submodule.span ℝ (insert (ιL P (1, 0))
          ((fun v => ιL P (0, v)) '' (Q : Set (Euclid P))))) := by
    intro i
    obtain ⟨K, hK⟩ := hGlip i
    -- (a) `M` has approximate tangent space `range DF i(u)` at `F i u` for a.e. `u ∈ B i`
    have hTM := Submission.dpf_approxTangent_ae_bilipschitz_piece P k univ M (F i) (B i) (L i)
      (m i) isOpen_univ hM (subset_univ _)
      (fun K' _ _ => ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))
      (hL i) (hB i) (hm i) (hbi i) (hdiff i) (hFBM i)
    -- (b) `C` has approximate tangent space `range DG i(b)` at `G i b` for a.e. `b ∈ Bh i`
    have hTC := Submission.dpf_approxTangent_ae_bilipschitz_piece (P + 1) (k + 1) univ Ctot (G i)
      (Bh i) K (min 1 (m i)) isOpen_univ hCtotm (subset_univ _)
      (fun K' _ _ => ne_top_of_le_ne_top hCfin (measure_mono inter_subset_left)) hK (hBhm i)
      (lt_min one_pos (hm i)) (hGlow i)
      (fun b hb => ⟨(hGd i b hb).differentiableAt, hGdinj i b hb⟩)
      (by rw [hGC i, hCU]; exact subset_iUnion C i)
    -- (c) (a) holds at `π₂ b` for a.e. `b ∈ Bh i`, since `π` is measure preserving
    have hTM' : ∀ᵐ b ∂(volume.restrict (Bh i)), HasApproximateTangentSpaceAt k M (F i (πL k b).2)
        (LinearMap.range (fderiv ℝ (F i) (πL k b).2 : Euclid k →ₗ[ℝ] Euclid P)) := by
      refine ((hπmp k).restrict_preimage
        (measurableSet_Ioo.prod (hB i))).quasiMeasurePreserving.ae
        (p := fun p : ℝ × Euclid k => HasApproximateTangentSpaceAt k M (F i p.2)
          (LinearMap.range (fderiv ℝ (F i) p.2 : Euclid k →ₗ[ℝ] Euclid P))) ?_
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact Measure.quasiMeasurePreserving_snd.ae hTM
    -- (d) there, uniqueness of approximate tangent spaces and `range DG i(b) = ℝe₀ ⊕ J(range DF i)`
    have hcomb : ∀ᵐ b ∂(volume.restrict (Bh i)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt k M (πL P (G i b)).2 Q →
        HasApproximateTangentSpaceAt (k + 1) Ctot (G i b)
          (Submodule.span ℝ (insert (ιL P (1, 0))
            ((fun v => ιL P (0, v)) '' (Q : Set (Euclid P))))) := by
      filter_upwards [hTC, hTM', ae_restrict_mem (hBhm i)] with b hbC hbM hb Q hQ
      have hprG : (πL P (G i b)).2 = F i (πL k b).2 := by
        show (πL P (ιL P ((πL k b).1, F i (πL k b).2))).2 = _
        rw [hπι]
      rw [hprG] at hQ
      rw [hQ.unique hbM, ← hGrange i b hb]
      exact hbC
    -- (e) the exceptional set is the image of a Lebesgue-null set under the Lipschitz `G i`
    rw [← hGC i, ae_iff, Measure.restrict_apply' ((hGC i).symm ▸ hCm i)]
    rw [ae_iff, Measure.restrict_apply' (hBhm i)] at hcomb
    refine measure_mono_null (t := G i '' ({b | ¬∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt k M (πL P (G i b)).2 Q →
        HasApproximateTangentSpaceAt (k + 1) Ctot (G i b) (Submodule.span ℝ (insert (ιL P (1, 0))
          ((fun v => ιL P (0, v)) '' (Q : Set (Euclid P)))))} ∩ Bh i)) ?_ ?_
    · rintro _ ⟨hy, b, hb, rfl⟩
      exact ⟨b, ⟨hy, hb⟩, rfl⟩
    · refine le_antisymm (le_trans
        (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (k + 1)
          hK.lipschitzOnWith) ?_) bot_le
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hcomb, mul_zero]
  refine ⟨Ctot, hCtotm, image_mono (prod_mono subset_rfl (iUnion_subset hFBM)), ?_, hmeasure, ?_⟩
  -- B3: `C ⊆ ⋃ range (G i)`, every `G i` being Lipschitz
  · refine ⟨∅, measure_empty, G, hGlip, ?_⟩
    rw [empty_union, hCU]
    exact iUnion_mono fun i => hGC i ▸ image_subset_range _ _
  · have hCC : μHE[k + 1].restrict Ctot = μHE[k + 1].restrict (⋃ i, C i) := by rw [hCU]
    rw [hCC, ae_restrict_iUnion_iff]
    exact htan

/-- **Smooth pull-backs and the homotopy formula on forms** (Simon 6.2.23–6.2.26, dual form).
(a) The pull-back `Φ^#α(x) = α(Φ x) ∘ DΦ(x)` of a smooth form by a `C^∞` map is smooth.
(b) Let `F, G` be `C^∞`, `h(t, x) = F x + t(G x - F x)` the affine homotopy (6.2.26) and `ω` a
smooth `(k+1)`-form.  Then `Kω(x) = ∫₀¹ (ι_{G x - F x} ω(h(t, x))) ∘ D_x h(t, x) dt` is smooth and
`G^#ω - F^#ω = d(Kω) + K(dω)`, the homotopy formula 6.2.25 tested on `ω`.  The precomposition
`L ↦ (γ ↦ γ ∘ L)` is analytic, which gives (a).  For (b) we work on a proper normed space `E`:
with `H = h` on `ℝ × E`, `Θ = H^#ω` and `e = (1, 0)`, `dΘ = H^#(dω)` and Cartan's formula
`d(ι_e Θ) + ι_e dΘ = DΘ[e]` hold; pulling back by `y ↦ (t, y)` turns `ι_e Θ` and `ι_e dΘ` into the
integrands of `Kω` and `K(dω)` and `DΘ[e]` into `∂_t (h_t^#ω)`.  Integrating over `t ∈ [0, 1]`
and differentiating under the integral sign gives the formula. -/
theorem Submission.dor_lmb_fcdp_smooth_homotopy : (∀ (N N' m : ℕ) (Φ : Euclid N → Euclid N') (α : DifferentialForm (Euclid N') m), ContDiff ℝ (⊤ : ℕ∞) Φ → IsSmoothForm α → IsSmoothForm (fun x => (α (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x))) ∧ ∀ (P k : ℕ) (F G : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1, ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧ ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) - (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) = exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1, ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x + ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
  -- the pull-back `x ↦ α(x) ∘ L(x)` is `C^∞` when `α` and `L` are, as `L ↦ (γ ↦ γ ∘ L)` is analytic
  have hpb : ∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
      [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
      (m : ℕ) (α : E₁ → E₂ [⋀^Fin m]→L[ℝ] ℝ) (L : E₁ → E₃ →L[ℝ] E₂),
      ContDiff ℝ (⊤ : ℕ∞) α → ContDiff ℝ (⊤ : ℕ∞) L →
        ContDiff ℝ (⊤ : ℕ∞) (fun x => (α x).compContinuousLinearMap (L x)) := by
    intro E₁ E₂ E₃ _ _ _ _ _ _ m α L hα hL
    have hΨ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E₃ →L[ℝ] E₂) → (E₂ [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] (E₃ [⋀^Fin m]→L[ℝ] ℝ)) :=
      (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
    exact (hΨ.comp hL).clm_apply hα
  -- (a) `Φ^#α(x) = α(Φ x) ∘ DΦ(x)`
  refine ⟨fun N N' m Φ α hΦ hα => hpb (Euclid N) (Euclid N') (Euclid N) m (fun x => α (Φ x))
    (fderiv ℝ Φ) (hα.comp hΦ) (contDiff_infty_iff_fderiv.mp hΦ).2, ?_⟩
  -- (b) on an abstract proper normed space `E`, then for `E = ℝᴾ`
  suffices key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (k : ℕ)
      (F G : E → E) (ω : DifferentialForm E (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1,
        ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧
      ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) -
        (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) =
        exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1,
          ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap
            (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x +
        ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft
          (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) by
    intro P k F G ω hF hG hω
    exact key (Euclid P) k F G ω hF hG hω
  intro E _ _ _ k F G ω hF hG hω
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω := hω
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hr : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hF1 : Differentiable ℝ F := hF.differentiable hne
  have hG1 : Differentiable ℝ G := hG.differentiable hne
  have hω1 : Differentiable ℝ ω := hωs.differentiable hne
  -- `γ ↦ γ.curryLeft` is a linear isometry, hence `C^∞`
  have hcl : ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] (m : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) (fun γ : E₁ [⋀^Fin (m + 1)]→L[ℝ] ℝ => γ.curryLeft) := by
    intro E₁ _ _ m
    have h := LinearIsometry.contDiff (𝕜 := ℝ) (E := E₁ [⋀^Fin (m + 1)]→L[ℝ] ℝ)
      (F := E₁ →L[ℝ] E₁ [⋀^Fin m]→L[ℝ] ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      ContinuousAlternatingMap.curryLeftLI
    exact h
  -- differentiation under the integral sign: `D_x ∫₀¹ f(t, x) dt = ∫₀¹ Df(t, x) ∘ J dt`, `J = inr`,
  -- with the bound `sup ‖Df ∘ J‖` over the compact set `[0, 1] × B̄(x₀, 1)`
  have hpar : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (f : ℝ × E → Y), ContDiff ℝ (⊤ : ℕ∞) f → ∀ x₀ : E,
      HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, f (t, x))
        (∫ t in (0 : ℝ)..1, (fderiv ℝ f (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x₀ := by
    intro Y _ _ _ f hf x₀
    have : SecondCountableTopologyEither ℝ (E →L[ℝ] Y) := ⟨Or.inl inferInstance⟩
    have hf1 : Differentiable ℝ f := hf.differentiable hne
    have hDf : Continuous (fun p : ℝ × E => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
      (hf.continuous_fderiv hne).clm_comp continuous_const
    have hjt : ∀ x : E, Continuous (fun t : ℝ => ((t, x) : ℝ × E)) :=
      fun x => continuous_id.prodMk continuous_const
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
      (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn hDf.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => f (t, x))
      (F' := fun x t => (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (bound := fun _ => C) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x => (hf.continuous.comp (hjt x)).aestronglyMeasurable)
      ((hf.continuous.comp (hjt x₀)).intervalIntegrable 0 1)
      (hDf.comp (hjt x₀)).aestronglyMeasurable ?_ intervalIntegrable_const ?_
    · rw [ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun t ht x hx => hC (t, x) ⟨?_, ?_⟩
      · rw [uIoc_of_le zero_le_one] at ht
        exact Ioc_subset_Icc_self ht
      · exact ball_subset_closedBall hx
    · exact Eventually.of_forall fun t x _ =>
        (hf1 (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- `x ↦ ∫₀¹ f(t, x) dt` is `C^n` for every `n`, by induction (for all `Y` at once)
  have hsm : ∀ (n : ℕ) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (f : ℝ × E → Y), ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, f (t, x)) := by
    intro n
    induction n with
    | zero =>
      intro Y _ _ _ f hf
      rw [Nat.cast_zero, contDiff_zero]
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => f (t, x)) (hf.continuous.comp continuous_swap) 0 1
    | succ n ih =>
      intro Y _ _ _ f hf
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ t in (0 : ℝ)..1, (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E),
        ih (E →L[ℝ] Y) (fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E))
          ((contDiff_infty_iff_fderiv.mp hf).2.clm_comp contDiff_const), hpar Y f hf⟩
  have hcc : ∀ (m : ℕ) (g : Covector E m) (L : ℝ × E →L[ℝ] E) (L' : E →L[ℝ] ℝ × E),
      (g.compContinuousLinearMap L).compContinuousLinearMap L' =
        g.compContinuousLinearMap (L.comp L') := fun _ _ _ _ => rfl
  -- the homotopy `H(t, y) = F y + t • (G y - F y)` on `ℝ × E`: `DH(t, y) e = G y - F y` for
  -- `e = (1, 0)`, and `DH(t, y) ∘ J = DF y + t • (DG y - DF y)`
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × E → E, H = fun p => F p.2 + p.1 • (G p.2 - F p.2) := ⟨_, rfl⟩
  have hHapp : ∀ (t : ℝ) (y : E), H (t, y) = F y + t • (G y - F y) := fun t y => by rw [hHdef]
  have hHs : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [hHdef]
    exact (hF.comp contDiff_snd).add
      (contDiff_fst.smul ((hG.comp contDiff_snd).sub (hF.comp contDiff_snd)))
  have hH1 : Differentiable ℝ H := hHs.differentiable hne
  have hDHe : ∀ (t : ℝ) (y : E), fderiv ℝ H (t, y) (1, 0) = G y - F y := by
    intro t y
    have h1 : HasDerivAt (fun s : ℝ => H (s, y)) (fderiv ℝ H (t, y) (1, 0)) t :=
      (hH1 (t, y)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    have h2 := ((hasDerivAt_id' t).smul_const (G y - F y)).const_add (F y)
    rw [one_smul] at h2
    simp only [← hHapp] at h2
    exact h1.unique h2
  have hDHJ : ∀ (t : ℝ) (y : E), (fderiv ℝ H (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      fderiv ℝ F y + t • (fderiv ℝ G y - fderiv ℝ F y) := by
    intro t y
    have h1 : HasFDerivAt (fun y' : E => H (t, y'))
        ((fderiv ℝ H (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
      (hH1 (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
    have h2 : HasFDerivAt (fun y' : E => F y' + t • (G y' - F y'))
        (fderiv ℝ F y + t • (fderiv ℝ G y - fderiv ℝ F y)) y :=
      (hF1 y).hasFDerivAt.add (((hG1 y).hasFDerivAt.sub (hF1 y).hasFDerivAt).const_smul t)
    simp only [← hHapp] at h2
    exact h1.unique h2
  -- `Θ = H^#ω` is `C^∞` with `dΘ = H^#(dω)`, and `ι_e Θ` is `C^∞`
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : DifferentialForm (ℝ × E) (k + 1),
      Θ = fun p => (ω (H p)).compContinuousLinearMap (fderiv ℝ H p) := ⟨_, rfl⟩
  have hΘs : ContDiff ℝ (⊤ : ℕ∞) Θ := by
    rw [hΘdef]
    exact hpb (ℝ × E) E (ℝ × E) (k + 1) (fun p => ω (H p)) (fderiv ℝ H) (hωs.comp hHs)
      (contDiff_infty_iff_fderiv.mp hHs).2
  have hΘ1 : Differentiable ℝ Θ := hΘs.differentiable hne
  have hdΘ : ∀ p, extDeriv Θ p = (extDeriv ω (H p)).compContinuousLinearMap (fderiv ℝ H p) := by
    intro p
    rw [hΘdef]
    exact extDeriv_pullback (hω1 (H p)) hHs.contDiffAt hr
  obtain ⟨ιΘ, hιΘdef⟩ : ∃ ιΘ : DifferentialForm (ℝ × E) k,
      ιΘ = fun p => (Θ p).curryLeft (1, 0) := ⟨_, rfl⟩
  have hιΘs : ContDiff ℝ (⊤ : ℕ∞) ιΘ := by
    rw [hιΘdef]
    exact ((hcl (ℝ × E) k).comp hΘs).clm_apply contDiff_const
  have hιΘ1 : Differentiable ℝ ιΘ := hιΘs.differentiable hne
  -- the integrands `κ` of `Kω` and `κd` of `K(dω)` are `ι_e Θ ∘ J` and `ι_e dΘ ∘ J`
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ × E → Covector E k, κ = fun p =>
      ((ω (F p.2 + p.1 • (G p.2 - F p.2))).curryLeft (G p.2 - F p.2)).compContinuousLinearMap
        (fderiv ℝ F p.2 + p.1 • (fderiv ℝ G p.2 - fderiv ℝ F p.2)) := ⟨_, rfl⟩
  have hκapp : ∀ (t : ℝ) (x : E), κ (t, x) =
      ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := fun t x => by rw [hκdef]
  obtain ⟨κd, hκddef⟩ : ∃ κd : ℝ × E → Covector E (k + 1), κd = fun p =>
      ((extDeriv ω (F p.2 + p.1 • (G p.2 - F p.2))).curryLeft
        (G p.2 - F p.2)).compContinuousLinearMap
        (fderiv ℝ F p.2 + p.1 • (fderiv ℝ G p.2 - fderiv ℝ F p.2)) := ⟨_, rfl⟩
  have hκdapp : ∀ (t : ℝ) (x : E), κd (t, x) =
      ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft
        (G x - F x)).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := fun t x => by rw [hκddef]
  have hκeq : ∀ (t : ℝ) (y : E),
      (ιΘ (t, y)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) = κ (t, y) := by
    intro t y
    rw [hκapp, hιΘdef, hΘdef]
    simp only [ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDHe, hcc, hDHJ, hHapp]
  have hκdeq : ∀ (t : ℝ) (y : E), ((extDeriv Θ (t, y)).curryLeft (1, 0)).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E) = κd (t, y) := by
    intro t y
    rw [hκddef, hdΘ]
    simp only [ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDHe, hcc, hDHJ, hHapp]
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := by
    have hκfun : κ = fun p => (ιΘ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) :=
      funext fun p => (hκeq p.1 p.2).symm
    rw [hκfun]
    exact hpb (ℝ × E) (ℝ × E) E k ιΘ (fun _ => ContinuousLinearMap.inr ℝ ℝ E) hιΘs contDiff_const
  -- `Kω` is `C^∞`
  simp only [← hκapp, ← hκdapp]
  refine ⟨contDiff_infty.mpr fun n => hsm n _ κ hκs, fun x => ?_⟩
  -- Cartan's formula for the constant field `e`: `d(ι_e Θ) + ι_e dΘ = DΘ[e]`
  have hcartan : ∀ p, extDeriv ιΘ p + (extDeriv Θ p).curryLeft (1, 0) = fderiv ℝ Θ p (1, 0) := by
    intro p
    ext v
    have h0 : Fin.removeNth 0 (Matrix.vecCons ((1 : ℝ), (0 : E)) v) = v := by simp
    have hs : ∀ i : Fin (k + 1), Fin.removeNth i.succ (Matrix.vecCons ((1 : ℝ), (0 : E)) v) =
        Matrix.vecCons ((1 : ℝ), (0 : E)) (Fin.removeNth i v) :=
      fun i => Fin.cons_comp_succ_succAbove _ v i
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      extDeriv_apply (hιΘ1 p), extDeriv_apply (hΘ1 p), Fin.sum_univ_succ (n := k + 1)]
    simp only [hιΘdef, ContinuousAlternatingMap.curryLeft_apply_apply, h0, hs, Fin.val_zero,
      pow_zero, one_smul, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_succ]
    rw [fderiv_continuousAlternatingMap_apply_const_apply (hΘ1 p), add_left_comm,
      ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
    intro i _
    rw [pow_succ, mul_neg_one, neg_smul, add_neg_cancel]
  -- pulling back by `y ↦ (t, y)`: `d(κ(t, ·))(x) = d(ι_e Θ)(t, x) ∘ J`
  have hj : ∀ (t : ℝ) (y : E),
      fderiv ℝ (fun y' : E => ((t, y') : ℝ × E)) y = ContinuousLinearMap.inr ℝ ℝ E :=
    fun t y => (hasFDerivAt_prodMk_right t y).fderiv
  have hpull : ∀ t : ℝ, extDeriv (fun x' => κ (t, x')) x =
      (extDeriv ιΘ (t, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro t
    have h := extDeriv_pullback (ω := ιΘ) (f := fun y' : E => ((t, y') : ℝ × E)) (x := x)
      (hιΘ1 (t, x)) (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
        (fun y' : E => ((t, y') : ℝ × E))).contDiffAt hr
    simp only [hj, hκeq] at h
    exact h
  -- `Θ ∘ J` is `C^∞` with `D(Θ ∘ J)[e] = DΘ[e] ∘ J = d(κ(t, ·))(x) + κd(t, x)` at `(t, x)`
  have hΘ's : ContDiff ℝ (⊤ : ℕ∞)
      (fun p => (Θ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E)) :=
    hpb (ℝ × E) (ℝ × E) E (k + 1) Θ (fun _ => ContinuousLinearMap.inr ℝ ℝ E) hΘs contDiff_const
  have hΘ'1 : Differentiable ℝ
      (fun p => (Θ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E)) :=
    hΘ's.differentiable hne
  have hΘ'e : ∀ p, fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) p (1, 0) =
      (fderiv ℝ Θ p (1, 0)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro p
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ← fderiv_continuousAlternatingMap_apply_const_apply (hΘ'1 p),
      ← fderiv_continuousAlternatingMap_apply_const_apply (hΘ1 p)]
    rfl
  have hpt : ∀ t : ℝ, fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0) =
      extDeriv (fun x' => κ (t, x')) x + κd (t, x) := by
    intro t
    rw [hΘ'e, ← hcartan, hpull, ← hκdeq]
    ext v
    rfl
  -- the fundamental theorem of calculus for `t ↦ Θ(t, x) ∘ J`
  have hjt : Continuous (fun t : ℝ => ((t, x) : ℝ × E)) := continuous_id.prodMk continuous_const
  have hc1 : Continuous (fun t : ℝ => fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0)) :=
    ((hΘ's.continuous_fderiv hne).comp hjt).clm_apply continuous_const
  have hβd : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (Θ (s, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E))
      (fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
        (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0)) t := by
    intro t
    have h := (hΘ'1 (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hβd t)
    (hc1.intervalIntegrable 0 1)
  -- `d(Kω)(x) = ∫₀¹ d(κ(t, ·))(x) dt`, as `d = alternatizeUncurryFin ∘ D` with a CLM
  have hκ1 : Differentiable ℝ κ := hκs.differentiable hne
  have hκt : ∀ t : ℝ, fderiv ℝ (fun x' => κ (t, x')) x =
      (fderiv ℝ κ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    fun t => ((hκ1 (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hc3 : Continuous (fun t : ℝ => (fderiv ℝ κ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
    ((hκs.continuous_fderiv hne).comp hjt).clm_comp continuous_const
  have hi3 := Continuous.intervalIntegrable (E := E →L[ℝ] Covector E k) (μ := volume) hc3 0 1
  have hc4 : Continuous (fun t : ℝ => extDeriv (fun x' => κ (t, x')) x) := by
    simp only [extDeriv, hκt]
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).continuous.comp hc3
  have hc2 : Continuous (fun t : ℝ => κd (t, x)) := by
    refine (hc1.sub hc4).congr fun t => ?_
    simp only [Pi.sub_apply]
    rw [hpt t, add_sub_cancel_left]
  have hdK : extDeriv (fun x' => ∫ t in (0 : ℝ)..1, κ (t, x')) x =
      ∫ t in (0 : ℝ)..1, extDeriv (fun x' => κ (t, x')) x := by
    simp only [extDeriv, hκt]
    rw [(hpar _ κ hκs x).fderiv]
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
      (E := E →L[ℝ] Covector E k) (F := Covector E (k + 1))
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) hi3
    exact hcomm.symm
  -- `Θ(1, x) ∘ J = G^#ω(x)` and `Θ(0, x) ∘ J = F^#ω(x)`
  have hβ : ∀ t : ℝ, (Θ (t, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (F x + t • (G x - F x))).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
    intro t
    rw [hΘdef]
    simp only [hcc, hDHJ, hHapp]
  have hβ1 : (Θ (1, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) := by
    rw [hβ, one_smul, one_smul, add_sub_cancel, add_sub_cancel]
  have hβ0 : (Θ (0, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
    rw [hβ, zero_smul ℝ (G x - F x), zero_smul ℝ (fderiv ℝ G x - fderiv ℝ F x), add_zero,
      add_zero]
  -- `G^#ω - F^#ω = ∫₀¹ (d(κ(t, ·))(x) + κd(t, x)) dt = d(Kω)(x) + K(dω)(x)`
  show (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) -
      (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) =
    extDeriv (fun x' => ∫ t in (0 : ℝ)..1, κ (t, x')) x + ∫ t in (0 : ℝ)..1, κd (t, x)
  rw [← hβ1, ← hβ0, ← hftc, hdK, ← intervalIntegral.integral_add (hc4.intervalIntegrable 0 1)
    (hc2.intervalIntegrable 0 1)]
  exact intervalIntegral.integral_congr fun t _ => hpt t
/-- **The product `[[(0,1)]] × τ(M, θ, ξ)` as an integer multiplicity current** (Simon 6.2.17,
6.2.21).  For an `IMRep` `R = (M, θ, ξ)` of degree `k` in `ℝᴾ` with `μ_R(ℝᴾ) < ∞`, take the
cylinder `C ⊆ ι((0,1) × M)` of `dor_lmb_fcdp_cylinder`, with `Hᵏ⁺¹⌞C = ι_*(L¹⌞(0,1) ⊗ Hᵏ⌞M)`,
and put `R' = (C, θ ∘ pr, (ξ ∘ pr) ∘ c)`, `c(β) = (β ⌟ ê₀) ∘ J`, `J v = ι(0, v)`.  The measure
identity gives `μ_{R'}(ℝᴾ⁺¹) = μ_R(ℝᴾ)` and carries `Hᵏ⌞M`-null sets to `Hᵏ⁺¹⌞C`-null sets of
the form `pr⁻¹(N)`; `ê₀` followed by `J` of an orthonormal basis of `TₓM` is an orthonormal basis
of `ℝê₀ ⊕ J(TₓM)` realizing `ξ(x) ∘ c`; Fubini gives the action formula. -/
theorem Submission.dor_lmb_fcdp_product_imrep : ∀ (P k : ℕ) (R : IMRep (univ : Set (Euclid P)) k), R.measure univ ≠ ∞ → ∃ R' : IMRep (univ : Set (Euclid (P + 1))) (k + 1), R'.measure univ ≠ ∞ ∧ (∀ S : Set (Euclid P), MeasurableSet S → μHE[k] (R.carrier \ S) = 0 → μHE[k + 1] (R'.carrier \ ((fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Icc (0 : ℝ) 1 ×ˢ S))) = 0) ∧ ∀ β : DifferentialForm (Euclid (P + 1)) (k + 1), Continuous β → (∃ C : ℝ, ∀ y, ‖β y‖ ≤ C) → R'.action β = R.action (fun x => ∫ t in (0 : ℝ)..1, ((β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ) : Euclid (P + 1))).curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap (fderiv ℝ (fun x' : Euclid P => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x)) := by
  intro P k R hR
  -- `μ_R(ℝᴾ) = ∫_M θ dHᵏ ≥ Hᵏ(M)`, as `θ ≥ 1` on `M`
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hRmeas : R.measure univ = ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k] := by
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hMfin : μHE[k] R.carrier ≠ ∞ := by
    refine ne_top_of_le_ne_top hR ?_
    rw [hRmeas, ← setLIntegral_one]
    exact setLIntegral_mono hθm fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx)
  -- the cylinder `C ⊆ ι((0,1) × M)` with `Hᵏ⁺¹⌞C = ι_*(L¹⌞(0,1) ⊗ Hᵏ⌞M)`
  obtain ⟨C, hCm, hCsub, hCrect, hCmeas, hCtan⟩ :=
    Submission.dor_lmb_fcdp_cylinder P k R.carrier R.measurableSet_carrier R.rectifiable hMfin
  have : IsFiniteMeasure (μHE[k].restrict R.carrier) := isFiniteMeasure_restrict.2 hMfin
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  -- `ι(t, x) = (t, x)` is a measurable embedding, with left inverse `y ↦ (y₀, pr y)`
  have hιc : Continuous (fun p : ℝ × Euclid P =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) := by
    fun_prop
  have hprc : Continuous (fun y : Euclid (P + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P)) := by
    fun_prop
  have hιme : MeasurableEmbedding (fun p : ℝ × Euclid P =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun y : Euclid (P + 1) =>
        (WithLp.ofLp y 0, (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P)))
      hιc.measurable ?_ (Continuous.measurable (by fun_prop)) fun p => rfl
    have hsurj : range (fun p : ℝ × Euclid P =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
        univ :=
      range_eq_univ.2 fun y : Euclid (P + 1) =>
        ⟨(WithLp.ofLp y 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))), by simp [Fin.cons_self_tail]⟩
    rw [hsurj]
    exact MeasurableSet.univ
  -- `J v = ι(0, v)` is linear isometric and is the `x`-derivative of `ι(t, x)`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid P →L[ℝ] Euclid (P + 1), ∀ v,
      J v = (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1)) :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun v =>
          (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))
        map_add' := fun u v => by
          ext i
          induction i using Fin.cases <;> simp
        map_smul' := fun r v => by
          ext i
          induction i using Fin.cases <;> simp }, fun v => rfl⟩
  have hJinner : ∀ u v : Euclid P, inner ℝ (J u) (J v) = inner ℝ u v := by
    intro u v
    rw [hJ, hJ, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp
  have hfd : ∀ (t : ℝ) (x : Euclid P), fderiv ℝ (fun x' : Euclid P =>
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x = J := by
    intro t x
    have h : (fun x' : Euclid P =>
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
        fun x' => (WithLp.toLp 2 (Fin.cons t 0 : Fin (P + 1) → ℝ) : Euclid (P + 1)) + J x' := by
      funext x'
      rw [hJ]
      ext i
      induction i using Fin.cases <;> simp
    rw [h]
    exact (J.hasFDerivAt.const_add _).fderiv
  -- `c(γ) = (γ ⌟ ê₀) ∘ J`
  obtain ⟨c, hc⟩ : ∃ c : Covector (Euclid (P + 1)) (k + 1) →L[ℝ] Covector (Euclid P) k, ∀ γ,
      c γ = (γ.curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap
        J :=
    ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap), fun γ => rfl⟩
  -- `Hᵏ⌞M`-a.e. properties hold at `pr y` for `Hᵏ⁺¹⌞C`-a.e. `y`; `∫_C θ ∘ pr = ∫_M θ`
  have htr : ∀ {p : Euclid P → Prop}, (∀ᵐ x ∂μHE[k].restrict R.carrier, p x) →
      ∀ᵐ y ∂μHE[k + 1].restrict C, p (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) := by
    intro p hp
    rw [hCmeas, hιme.ae_map_iff]
    exact Measure.quasiMeasurePreserving_snd.ae hp
  have hlin : ∫⁻ y in C, (R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) : ℝ≥0∞) ∂μHE[k + 1] =
      ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k] := by
    rw [hCmeas, hιme.lintegral_map]
    change ∫⁻ q, (R.mult q.2 : ℝ≥0∞)
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) = _
    rw [lintegral_prod (fun q : ℝ × Euclid P => (R.mult q.2 : ℝ≥0∞))
      (hθm.comp measurable_snd).aemeasurable]
    simp [Real.volume_Ioo]
  -- the fields of `R' = (C, θ ∘ pr, (ξ ∘ pr) ∘ c)`
  have hpos : ∀ y ∈ C, 0 < R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) := by
    intro y hy
    obtain ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩ := hCsub hy
    exact R.mult_pos x hx
  have hloc : ∀ K : Set (Euclid (P + 1)), IsCompact K → K ⊆ univ → ∫⁻ y in C ∩ K,
      (R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) : ℝ≥0∞) ∂μHE[k + 1] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_set inter_subset_left)
    rw [hlin, ← hRmeas]
    exact hR
  have hξm : AEStronglyMeasurable (fun y : Euclid (P + 1) =>
      (R.orient (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))).comp c) (μHE[k + 1].restrict C) := by
    rw [hCmeas, hιme.aestronglyMeasurable_map_iff]
    have hcomp : Continuous fun ζ : MultiVector P k => ζ.comp c :=
      continuous_id.clm_comp continuous_const
    exact hcomp.comp_aestronglyMeasurable R.aestronglyMeasurable_orient.comp_snd
  -- `(ê₀, Jτ₁, …, Jτₖ)` is an orthonormal basis of `ℝê₀ ⊕ J(Q)` realizing `ξ(pr y) ∘ c`
  have hor : ∀ᵐ y ∂(μHE[k + 1].restrict C), ∃ Q : Submodule ℝ (Euclid (P + 1)),
      HasApproximateTangentSpaceAt (k + 1) C y Q ∧
        IsUnitOrientationOf ((R.orient (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))).comp c) Q := by
    filter_upwards [htr R.orients, hCtan] with y ⟨Q, hQ, τ, hτ, hspan, hsign⟩ hy
    refine ⟨_, hy Q hQ,
      Fin.cons (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) (J ∘ τ), ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite] at hτ ⊢
      intro i j
      induction i using Fin.cases <;> induction j using Fin.cases
      · simp
      · simp [EuclideanSpace.inner_single_left, hJ]
        exact (Fin.succ_ne_zero _).symm
      · simp [EuclideanSpace.inner_single_right, hJ]
      · simp [hJinner, hτ]
    · apply le_antisymm
      · rw [Fin.range_cons]
        refine Submodule.span_mono (insert_subset_insert ?_)
        rintro _ ⟨i, rfl⟩
        refine ⟨τ i, ?_, (hJ (τ i)).symm⟩
        rw [← hspan]
        exact Submodule.subset_span (mem_range_self i)
      · rw [Fin.range_cons, Submodule.span_le]
        rintro _ (rfl | ⟨v, hv, rfl⟩)
        · exact Submodule.subset_span (mem_insert _ _)
        · rw [← hspan] at hv
          dsimp only
          rw [← hJ]
          have h :=
            Submodule.apply_mem_span_image_of_mem_span (J : Euclid P →ₗ[ℝ] Euclid (P + 1)) hv
          rw [← range_comp] at h
          exact Submodule.span_mono (subset_insert _ _) h
    · rcases hsign with h | h
      · left
        intro γ
        rw [ContinuousLinearMap.comp_apply, h, hc]
        rfl
      · right
        intro γ
        rw [ContinuousLinearMap.comp_apply, h, hc]
        rfl
  refine ⟨⟨C, fun y => R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))),
    fun y => (R.orient (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))).comp c, hCm, subset_univ C,
    hCrect, R.measurable_mult.comp hprc.measurable, hpos, hloc, hξm, hor⟩, ?_, ?_, ?_⟩
  · -- (1) `μ_{R'}(ℝᴾ⁺¹) = μ_R(ℝᴾ)`
    show ((μHE[k + 1].restrict C).withDensity
      fun y => (R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) : ℝ≥0∞)) univ ≠ ∞
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlin, ← hRmeas]
    exact hR
  · -- (2) `C \ ι([0,1] × S) ⊆ C ∩ pr⁻¹(ℝᴾ \ S)`, which is `Hᵏ⁺¹`-null
    intro S hS hMS
    have hae : ∀ᵐ x ∂μHE[k].restrict R.carrier, x ∈ S :=
      (ae_restrict_iff' R.measurableSet_carrier).2
        (ae_iff.2 (measure_mono_null (fun x hx => not_imp.1 hx) hMS))
    have hnull := ae_iff.1 (htr hae)
    rw [Measure.restrict_apply' hCm] at hnull
    refine measure_mono_null ?_ hnull
    rintro y ⟨hyC, hyS⟩
    refine ⟨fun h => hyS ?_, hyC⟩
    obtain ⟨⟨t, x⟩, ⟨ht, -⟩, rfl⟩ := hCsub hyC
    exact ⟨(t, x), ⟨Ioo_subset_Icc_self ht, h⟩, rfl⟩
  · -- (3) Fubini, with the integrable bound `θ(x)‖c‖C_β` from `‖ξ‖ ≤ 1` a.e.
    rintro β hβc ⟨Cβ, hCβ⟩
    have hξbd : ∀ᵐ x ∂μHE[k].restrict R.carrier, ∀ α : Covector (Euclid P) k,
        ‖R.orient x α‖ ≤ ‖α‖ := by
      filter_upwards [R.orients] with x ⟨Q, _, τ, hτ, _, hsign⟩ α
      have h1 : ‖α τ‖ ≤ ‖α‖ := by
        simpa [hτ.1] using α.le_opNorm τ
      rcases hsign with h | h <;> rw [h α]
      · exact h1
      · rwa [norm_neg]
    have hθint : Integrable (fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) := by
      have h := integrable_toReal_of_lintegral_ne_top hθm.aemeasurable (hRmeas ▸ hR)
      simpa using h
    have : SecondCountableTopologyEither (ℝ × Euclid P) (Covector (Euclid P) k) :=
      secondCountableTopologyEither_of_left _ _
    have : SecondCountableTopologyEither ℝ (Covector (Euclid P) k) :=
      secondCountableTopologyEither_of_left _ _
    have hcb : ∀ y, ‖c (β y)‖ ≤ ‖c‖ * Cβ := fun y =>
      (c.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hCβ y) (norm_nonneg _))
    have hint : Integrable (fun q : ℝ × Euclid P => (R.mult q.2 : ℝ) *
        R.orient q.2 (c (β (WithLp.toLp 2 (Fin.cons q.1 (WithLp.ofLp q.2) : Fin (P + 1) → ℝ)))))
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) := by
      refine Integrable.mono' ((hθint.comp_snd _).mul_const (‖c‖ * Cβ)) ?_ ?_
      · refine ((measurable_from_nat.comp R.measurable_mult).comp
          measurable_snd).aestronglyMeasurable.mul ?_
        have h1 : AEStronglyMeasurable (fun q : ℝ × Euclid P => R.orient q.2)
            ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) :=
          R.aestronglyMeasurable_orient.comp_snd
        have h2 : Continuous (fun q : ℝ × Euclid P =>
            c (β (WithLp.toLp 2 (Fin.cons q.1 (WithLp.ofLp q.2) : Fin (P + 1) → ℝ)))) :=
          c.continuous.comp (hβc.comp hιc)
        exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (h1.prodMk h2.aestronglyMeasurable)
      · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hξbd] with q hq
        rw [norm_mul, Real.norm_natCast]
        exact mul_le_mul_of_nonneg_left ((hq _).trans (hcb _)) (Nat.cast_nonneg _)
    have hintt : ∀ x : Euclid P, Integrable (fun t : ℝ =>
        c (β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ))))
        (volume.restrict (Ioo (0 : ℝ) 1)) := fun x =>
      Integrable.of_bound ((c.continuous.comp (hβc.comp
          (hιc.comp (continuous_id.prodMk continuous_const)))).aestronglyMeasurable)
        (‖c‖ * Cβ) (ae_of_all _ fun t => hcb _)
    -- the inner integral is `∫_{(0,1)} c(β(ι(t, x))) dt`
    have hω : (fun x : Euclid P => ∫ t in (0 : ℝ)..1, ((β
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ) : Euclid (P + 1))).curryLeft
          (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap
          (fderiv ℝ (fun x' : Euclid P =>
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x)) =
        fun x => ∫ t in Ioo (0 : ℝ) 1,
          c (β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ))) := by
      funext x
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      simp only [hfd, ← hc]
    rw [hω]
    simp only [IMRep.action]
    rw [hCmeas, hιme.integral_map]
    change ∫ q, (R.mult q.2 : ℝ) *
      R.orient q.2 (c (β (WithLp.toLp 2 (Fin.cons q.1 (WithLp.ofLp q.2) : Fin (P + 1) → ℝ))))
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) = _
    rw [integral_prod_symm _ hint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [integral_const_mul, ContinuousLinearMap.integral_comp_comm _ (hintt x)]
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

/-- **The affine homotopy operator** `h_#([[(0,1)]] × X)` (Simon 6.2.25–6.2.27).  Assume the
Lipschitz push-forward (IPF) of finite-mass integer multiplicity representations.  Fix an integer
multiplicity `X` vanishing off a compact `E₀`, represented by `R₀`, and let `R'` be the product
representation of `[[(0,1)]] × X` (`dor_lmb_fcdp_product_imrep`) and `Y'` its push-forward.  With
a smooth cut-off `χ = 1` near `E₀` and a smooth bounded `s` with `s(t) = t` on `(-1,2)`, put
`Ĥ(y) = F(pr y) + s(y₀)χ(pr y)(G − F)(pr y)` and `homot k F G X := Y'(Ĥ)`.  The cut-offs of the
definition are already smooth, so no separate a.e. comparison with a smooth `Ĥ*` is needed.  `Ĥ` is
Lipschitz and the smooth `Ĥⱼ` built from `Fⱼ, Gⱼ` converge to it (`dor_lmb_fcdp_homotopy_maps`), so
`homot` is integer multiplicity and local, and the product action formula with the pulled-back
integrand identity gives `R₀.action(Kⱼω) → homot(ω)`; locality of `R₀` on `E` gives (H3).  For (H4)
the segments `hⱼ(t,x)` eventually avoid `spt ω`, and for (H5) Hadamard's inequality gives
`|Kⱼω(x)(τ)| ≤ (δ + ε)Λᵏ` on `E` (`dor_lmb_fcdp_toolkit_push`). -/
theorem Submission.dor_lmb_fcdp_homot_operator : (∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), ∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (homot k F G X) ∧ (∀ F' G' : Euclid P → Euclid P, LipschitzWith Λ F' → LipschitzWith Λ G' → EqOn F F' E → EqOn G G' E → homot k F G X = homot k F' G' X) ∧ (∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (homot k F G X ω))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → homot k F G X ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hIPF P
  obtain ⟨hT1, hT2, hT3, hT4, hT5⟩ := Submission.dor_lmb_fcdp_toolkit_push.1
  have h1top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  -- a.e. membership in `S` on a carrier `C` with `Hᵈ(C \ S) = 0`
  have hgen : ∀ (N d : ℕ) (C S : Set (Euclid N)), MeasurableSet C → μHE[d] (C \ S) = 0 →
      ∀ᵐ y ∂(μHE[d].restrict C), y ∈ S := by
    intro N d C S hC hS
    refine (ae_restrict_iff' hC).2 (ae_iff.2 (measure_mono_null (fun y hy => ?_) hS))
    exact not_imp.1 hy
  -- step 1: a `C¹` bounded Lipschitz `s : ℝ → ℝ` with `s t = t` on `(-1, 2)`, `s(t) = tφ(t)`
  obtain ⟨s, hs1, ⟨Ls, hsL⟩, ⟨As, hsA⟩, hsid⟩ : ∃ s : ℝ → ℝ, ContDiff ℝ 1 s ∧
      (∃ L : NNReal, LipschitzWith L s) ∧ (∃ A : ℝ, ∀ t, |s t| ≤ A) ∧
      ∀ t ∈ Ioo (-1 : ℝ) 2, s t = t := by
    let φ : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 5 / 2, by norm_num, by norm_num⟩
    have hc : ContDiff ℝ 1 (fun t : ℝ => t * φ t) := contDiff_id.mul (φ.contDiff (n := 1))
    have hcs : HasCompactSupport (fun t : ℝ => t * φ t) := φ.hasCompactSupport.mul_left (f := id)
    obtain ⟨A, hA⟩ := hc.continuous.bounded_above_of_compact_support hcs
    refine ⟨fun t => t * φ t, hc, ContDiff.lipschitzWith_of_hasCompactSupport hcs hc one_ne_zero,
      ⟨A, fun t => by simpa [Real.norm_eq_abs] using hA t⟩, fun t ht => ?_⟩
    have hmem : t ∈ closedBall (1 / 2 : ℝ) (3 / 2) := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hφ : φ t = 1 := φ.one_of_mem_closedBall hmem
    simp only [hφ, mul_one]
  -- step 2: for each current `X` choose the homotopy operator `F, G ↦ Y'(Ĥ_{F,G})`
  have key : ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), ∃ H : (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (H F G) ∧ (∀ F' G' : Euclid P → Euclid P, LipschitzWith Λ F' → LipschitzWith Λ G' → EqOn F F' E → EqOn G G' E → H F G = H F' G') ∧ (∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (H F G ω))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → H F G ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (H F G).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
    intro k X
    by_cases hX : ∃ E₀ : Set (Euclid P), IsCompact E₀ ∧ IsIntegerMultiplicity X ∧
        ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
          Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E₀ → X ω = 0
    swap
    · exact ⟨fun _ _ => 0, fun Λ F G E _ _ hE hXI hXE => absurd ⟨E, hE, hXI, hXE⟩ hX⟩
    -- `X = τ(R₀)` vanishes off the compact `E₀`; `R'` is the product representation of
    -- `[[(0,1)]] × X`, `Y'` its push-forward, `χ = 1` on an open `W ⊇ E₀`
    obtain ⟨E₀, hE₀, ⟨R₀, hR₀⟩, hXE₀⟩ := hX
    obtain ⟨-, hmass, hR₀fin, hlocE₀⟩ := hT1 P k X R₀ E₀ hR₀ hE₀ hXE₀
    obtain ⟨R', hR'fin, hR'ae, hR'act⟩ := Submission.dor_lmb_fcdp_product_imrep P k R₀ hR₀fin
    obtain ⟨Y, hYa, hYb⟩ := hIPF (P + 1) P (k + 1) R' hR'fin
    obtain ⟨χ, W, hχs, hχc, -, hWo, hE₀W, hχW⟩ := hT5 P E₀ hE₀
    have hχ1 : ContDiff ℝ 1 χ := hχs.of_le h1top
    obtain ⟨Lχ, hχL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ1 one_ne_zero
    -- pull-backs of test forms by `C¹` Lipschitz maps are continuous and bounded
    have hpull : ∀ (Φ : Euclid (P + 1) → Euclid P) (LΦ : NNReal), ContDiff ℝ 1 Φ →
        LipschitzWith LΦ Φ → ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1),
        Continuous (fun y => ((ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)).compContinuousLinearMap
          (fderiv ℝ Φ y)) ∧
        ∃ C : ℝ, ∀ y, ‖((ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)).compContinuousLinearMap
          (fderiv ℝ Φ y)‖ ≤ C := by
      intro Φ LΦ hΦ hΦL ω
      have hωc : Continuous (ω : DifferentialForm (Euclid P) (k + 1)) := ω.property.1.1.continuous
      obtain ⟨Cω, hCω⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
      have hcomp : Continuous (ContinuousAlternatingMap.compContinuousLinearMapCLM :
          (Euclid (P + 1) →L[ℝ] Euclid P) →
            (Euclid P [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (Euclid (P + 1) [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :=
        continuousOn_univ.1
          (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).continuousOn
      refine ⟨(hcomp.comp (hΦ.continuous_fderiv one_ne_zero)).clm_apply (hωc.comp hΦ.continuous),
        Cω * (LΦ : ℝ) ^ (k + 1), fun y => ?_⟩
      calc ‖((ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)).compContinuousLinearMap
            (fderiv ℝ Φ y)‖
          ≤ ‖(ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)‖ *
              ‖fderiv ℝ Φ y‖ ^ Fintype.card (Fin (k + 1)) :=
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
        _ ≤ Cω * (LΦ : ℝ) ^ (k + 1) := by
            rw [Fintype.card_fin]
            exact mul_le_mul (hCω _)
              (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hΦL) _)
              (by positivity) ((norm_nonneg _).trans (hCω 0))
    refine ⟨fun F G => Y (fun y => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))), ?_⟩
    intro Λ F G E hF hG hE _ hXE
    -- step 3: `Hᵏ(M \ E) = 0`, `M(X) = μ_{R₀}(ℝᴾ) < ∞` and `R₀` is local on `E`
    obtain ⟨hR₀E, -, -, hlocE⟩ := hT1 P k X R₀ E hR₀ hE hXE
    have hHM := Submission.dor_lmb_fcdp_homotopy_maps P Λ Ls Lχ As s χ F G hF hG hsL hsA hχL hχc
    -- step 4: `Ĥ` is Lipschitz
    obtain ⟨L₀, hL₀⟩ := hHM.1
    -- step 7: `R₀.action(Kⱼω) → homot k F G X (ω)`
    have hchar : ∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → Tendsto (fun j => R₀.action (fun x => ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)))) atTop (𝓝 (Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω)) := by
      intro Fs Gs ω hFs hGs hFsL hGsL hFsu hGsu
      -- the smooth `Ĥⱼ` are `C¹`, uniformly Lipschitz and converge uniformly to `Ĥ`
      obtain ⟨hHj1, ⟨L, hHjL⟩, hHju⟩ := hHM.2.1 hs1 hχ1 Fs Gs hFs hGs hFsL hGsL hFsu hGsu
      have hlim := (hYa _ (max L₀ L) (hL₀.weaken (le_max_left _ _))).2 _ hHj1
        (fun j => (hHjL j).weaken (le_max_right _ _)) hHju ω
      refine Tendsto.congr (fun j => ?_) hlim
      -- product action formula, then the pulled-back integrand identity on `W ⊇ E₀`
      obtain ⟨hβc, hβb⟩ := hpull _ _ (hHj1 j) (hHjL j) ω
      refine (hR'act _ hβc hβb).trans
        (hlocE₀ _ _ (fun x hx => intervalIntegral.integral_congr (fun t ht => ?_)))
      rw [uIcc_of_le zero_le_one] at ht
      exact hHM.2.2 (Fs j) (Gs j) W k (ω : DifferentialForm (Euclid P) (k + 1)) t x hs1 hχ1
        (hFs j) (hGs j) hWo hχW hsid (hE₀W hx) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- step 9: smooth Lipschitz approximations of `F` and `G`
    obtain ⟨Fa, hFa, hFaL, hFau⟩ := hT4 P P Λ F hF
    obtain ⟨Ga, hGa, hGaL, hGau⟩ := hT4 P P Λ G hG
    have hFa1 : ∀ j, ContDiff ℝ 1 (Fa j) := fun j => (hFa j).of_le h1top
    have hGa1 : ∀ j, ContDiff ℝ 1 (Ga j) := fun j => (hGa j).of_le h1top
    -- step 10 (H4): the segments `hⱼ(t,x)` eventually avoid `spt ω`
    have hH4 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω = 0 := by
      intro ω hω
      -- the trace `Σ` is compact
      have hTr : IsCompact {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} := by
        have hTreq : {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} =
            (fun p : ℝ × Euclid P => F p.2 + p.1 • (G p.2 - F p.2)) '' (Icc 0 1 ×ˢ E) := by
          ext y
          constructor
          · rintro ⟨x, hx, t, ht, rfl⟩
            exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
          · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
            exact ⟨x, hx, t, ht, rfl⟩
        rw [hTreq]
        exact (isCompact_Icc.prod hE).image ((hF.continuous.comp continuous_snd).add
          (continuous_fst.smul ((hG.continuous.comp continuous_snd).sub
            (hF.continuous.comp continuous_snd))))
      obtain ⟨d, hd, hdisj⟩ := Disjoint.exists_thickenings hω.symm hTr (isClosed_tsupport _)
      refine tendsto_nhds_unique (hchar Fa Ga ω hFa1 hGa1 hFaL hGaL hFau hGau)
        (tendsto_const_nhds.congr' ?_)
      filter_upwards [Metric.tendstoUniformly_iff.1 hFau d hd,
        Metric.tendstoUniformly_iff.1 hGau d hd] with j hjF hjG
      have h0 : R₀.action (0 : DifferentialForm (Euclid P) k) = 0 := by simp [IMRep.action]
      refine ((hlocE _ 0 (fun x hx => ?_)).trans h0).symm
      simp only [Pi.zero_apply]
      refine (intervalIntegral.integral_congr (g := fun _ => 0) (fun t ht => ?_)).trans
        intervalIntegral.integral_zero
      rw [uIcc_of_le zero_le_one] at ht
      -- `hⱼ(t,x)` lies within `d` of `F x + t(G x − F x) ∈ Σ`
      have hnot : Fa j x + t • (Ga j x - Fa j x) ∉
          tsupport (ω : DifferentialForm (Euclid P) (k + 1)) := by
        intro hmem
        refine Set.disjoint_left.1 hdisj ?_ (Metric.self_subset_thickening hd _ hmem)
        rw [Metric.mem_thickening_iff]
        refine ⟨F x + t • (G x - F x), ⟨x, hx, t, ht, rfl⟩, ?_⟩
        have e : Fa j x + t • (Ga j x - Fa j x) - (F x + t • (G x - F x)) =
            (1 - t) • (Fa j x - F x) + t • (Ga j x - G x) := by
          simp only [smul_sub, sub_smul, one_smul]
          abel
        have ha : ‖Fa j x - F x‖ < d := by rw [← dist_eq_norm, dist_comm]; exact hjF x
        have hb : ‖Ga j x - G x‖ < d := by rw [← dist_eq_norm, dist_comm]; exact hjG x
        rw [dist_eq_norm, e]
        calc ‖(1 - t) • (Fa j x - F x) + t • (Ga j x - G x)‖
            ≤ ‖(1 - t) • (Fa j x - F x)‖ + ‖t • (Ga j x - G x)‖ := norm_add_le _ _
          _ = (1 - t) * ‖Fa j x - F x‖ + t * ‖Ga j x - G x‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
                Real.norm_of_nonneg ht.1]
          _ ≤ (1 - t) * max ‖Fa j x - F x‖ ‖Ga j x - G x‖ +
                t * max ‖Fa j x - F x‖ ‖Ga j x - G x‖ :=
              add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [ht.2]))
                (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
          _ = max ‖Fa j x - F x‖ ‖Ga j x - G x‖ := by ring
          _ < d := max_lt ha hb
      have hz : (ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x)) = 0 :=
        image_eq_zero_of_notMem_tsupport hnot
      simp only [hz]
      ext v
      simp
    refine ⟨(hYa _ L₀ hL₀).1, ?_, ?_, hH4, ?_⟩
    -- step 6 (H2): `Ĥ_{F,G} = Ĥ_{F',G'}` on `ι([0,1] × E)`, which carries `R'` a.e.
    · intro F' G' hF' hG' hFF' hGG'
      obtain ⟨L₁, hL₁⟩ :=
        (Submission.dor_lmb_fcdp_homotopy_maps P Λ Ls Lχ As s χ F' G' hF' hG' hsL hsA hχL hχc).1
      refine hYb _ _ (max L₀ L₁) (hL₀.weaken (le_max_left _ _)) (hL₁.weaken (le_max_right _ _)) ?_
      filter_upwards [hgen (P + 1) (k + 1) R'.carrier _ R'.measurableSet_carrier
        (hR'ae E hE.isClosed.measurableSet hR₀E)] with y hy
      obtain ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩ := hy
      have hx' : x ∈ E := hx
      simp only [Fin.tail_cons, WithLp.toLp_ofLp, hFF' hx', hGG' hx']
    -- step 8 (H3): `X(ηⱼ) = R₀.action(ηⱼ) = R₀.action(Kⱼω)` by locality on `E`
    · intro Fs Gs ω ηs hFs hGs hFsL hGsL hFsu hGsu hη
      refine Tendsto.congr (fun j => ?_) (hchar Fs Gs ω hFs hGs hFsL hGsL hFsu hGsu)
      exact (hlocE _ _ (fun x hx => (hη j x hx).symm)).trans (hR₀ (ηs j)).symm
    -- step 11 (H5): `|R₀.action(Kⱼω)| ≤ (δ + ε)Λᵏ M(X)` eventually, by Hadamard's inequality
    · intro δ hδ
      rcases E.eq_empty_or_nonempty with hE0 | ⟨x₀, hx₀⟩
      · refine le_trans (sSup_le ?_) zero_le
        rintro _ ⟨ω, -, rfl⟩
        simp only [hH4 ω (by simp [hE0]), ENNReal.ofReal_zero, le_refl]
      have hδ0 : 0 ≤ δ := dist_nonneg.trans (hδ x₀ hx₀)
      refine sSup_le ?_
      rintro _ ⟨ω, hωadm, rfl⟩
      have hωb : ∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (k + 1)) y) ≤ 1 :=
        hωadm.2
      have hε : ∀ ε : ℝ, 0 < ε → Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω ≤ (δ + ε) * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal) := by
        intro ε hε
        refine le_of_tendsto (hchar Fa Ga ω hFa1 hGa1 hFaL hGaL hFau hGau) ?_
        filter_upwards [Metric.tendstoUniformly_iff.1 hFau (ε / 2) (half_pos hε),
          Metric.tendstoUniformly_iff.1 hGau (ε / 2) (half_pos hε)] with j hjF hjG
        refine (le_abs_self _).trans ((hT3 P k univ R₀ _ ((δ + ε) * (Λ : ℝ) ^ k) hR₀fin
          (mul_nonneg (by linarith) (by positivity)) ?_).trans (le_of_eq (mul_assoc _ _ _)))
        filter_upwards [hgen P k R₀.carrier E R₀.measurableSet_carrier hR₀E] with x hx τ hτ
        beta_reduce
        rw [← Real.norm_eq_abs]
        refine (ContinuousAlternatingMap.le_opNorm _ _).trans ?_
        rw [Finset.prod_eq_one (fun i _ => hτ.1 i), mul_one]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const
          (C := (δ + ε) * (Λ : ℝ) ^ k) (fun t ht => ?_)).trans (le_of_eq (by simp))
        rw [uIoc_of_le zero_le_one] at ht
        -- `|ω(hⱼ)| ≤ 1`, `‖Gⱼx − Fⱼx‖ ≤ δ + ε` and `‖DFⱼ(x) + t(DGⱼ(x) − DFⱼ(x))‖ ≤ Λ`
        have hωh : ‖(ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x))‖ ≤ 1 := by
          refine ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
          rw [Real.norm_eq_abs, one_mul]
          exact (hT2 P (k + 1) _ v).trans (mul_le_of_le_one_left
            (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (hωb _))
        have hV : ‖Ga j x - Fa j x‖ ≤ δ + ε := by
          have e : Ga j x - Fa j x = (Ga j x - G x) + (G x - F x) + (F x - Fa j x) := by abel
          have h1 : ‖Ga j x - G x‖ < ε / 2 := by rw [← dist_eq_norm, dist_comm]; exact hjG x
          have h2 : ‖G x - F x‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact hδ x hx
          have h3 : ‖F x - Fa j x‖ < ε / 2 := by rw [← dist_eq_norm]; exact hjF x
          rw [e]
          calc ‖(Ga j x - G x) + (G x - F x) + (F x - Fa j x)‖
              ≤ ‖(Ga j x - G x) + (G x - F x)‖ + ‖F x - Fa j x‖ := norm_add_le _ _
            _ ≤ ‖Ga j x - G x‖ + ‖G x - F x‖ + ‖F x - Fa j x‖ :=
                add_le_add (norm_add_le _ _) le_rfl
            _ ≤ δ + ε := by linarith
        have hA : ‖fderiv ℝ (Fa j) x + t • (fderiv ℝ (Ga j) x - fderiv ℝ (Fa j) x)‖ ≤ Λ :=
          mem_closedBall_zero_iff.1 ((convex_closedBall (0 : Euclid P →L[ℝ] Euclid P) Λ).add_smul_sub_mem
            (mem_closedBall_zero_iff.2 (norm_fderiv_le_of_lipschitz ℝ (hFaL j)))
            (mem_closedBall_zero_iff.2 (norm_fderiv_le_of_lipschitz ℝ (hGaL j))) ⟨ht.1.le, ht.2⟩)
        calc ‖(((ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x))).curryLeft
              (Ga j x - Fa j x)).compContinuousLinearMap
              (fderiv ℝ (Fa j) x + t • (fderiv ℝ (Ga j) x - fderiv ℝ (Fa j) x))‖
            ≤ ‖((ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x))).curryLeft
                (Ga j x - Fa j x)‖ *
              ‖fderiv ℝ (Fa j) x + t • (fderiv ℝ (Ga j) x - fderiv ℝ (Fa j) x)‖ ^
                Fintype.card (Fin k) :=
              ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
          _ ≤ (1 * (δ + ε)) * (Λ : ℝ) ^ k := by
              rw [Fintype.card_fin]
              refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) hA k) (by positivity)
                (by linarith)
              refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
              rw [ContinuousAlternatingMap.norm_curryLeft]
              exact mul_le_mul hωh hV (norm_nonneg _) zero_le_one
          _ = (δ + ε) * (Λ : ℝ) ^ k := by ring
      -- let `ε → 0`
      have hY : Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω ≤ δ * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal) := by
        have hc : Tendsto (fun ε : ℝ => (δ + ε) * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal))
            (𝓝[>] 0) (𝓝 (δ * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal))) := by
          have h := ((tendsto_const_nhds (x := δ)).add (tendsto_id (x := 𝓝 (0 : ℝ)))).mul
            (tendsto_const_nhds (x := (Λ : ℝ) ^ k * (R₀.measure univ).toReal))
          rw [add_zero] at h
          exact h.mono_left nhdsWithin_le_nhds
        exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall (fun ε hε' => hε ε hε'))
      calc ENNReal.ofReal (Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω)
          ≤ ENNReal.ofReal (δ * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal)) :=
            ENNReal.ofReal_le_ofReal hY
        _ = ENNReal.ofReal δ * (Λ : ℝ≥0∞) ^ k * X.mass := by
            rw [ENNReal.ofReal_mul hδ0, ENNReal.ofReal_mul (pow_nonneg (NNReal.coe_nonneg Λ) k),
              ENNReal.ofReal_pow (NNReal.coe_nonneg Λ), ENNReal.ofReal_coe_nnreal,
              ENNReal.ofReal_toReal hR₀fin, hmass, mul_assoc]
        _ ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
            gcongr
            exact le_mul_of_one_le_left zero_le one_le_two
  choose H hH using key
  exact ⟨fun k F G X => H k X F G, fun k Λ F G E X hF hG hE hXI hXE => hH k X Λ F G E hF hG hE hXI hXE⟩
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
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

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
/-- **Simon Ch. 6, 3.6–3.9 and 2.29 for `n = 0`**: the Lipschitz push-forward of a finite-mass
`0`-dimensional integer multiplicity current.  `H⁰ = μHE[0]` is counting measure, so
`H⁰(M) ≤ μ_R(ℝᴺ) < ∞` makes the carrier `M` finite and `H⁰⌞M`-a.e. statements hold on all of `M`;
there each `ξ(x)` is `ε(x) ev` with `ε(x) = ±1`.  `Y(F)(ω) = ∑_{x ∈ M} θ(x) ε(x) ω(F(x))(∅)` is a
current, `R.action(F_j^# ω)` is the same finite sum with `F_j` in place of `F` (so it converges to
`Y(F)(ω)`), and `Y(F)` depends only on `F` on `M`.  Regrouping by the fibres of `F`,
`Y(F) = τ(M', |c|, sign(c) ev)` with `c(y) = ∑_{F(x) = y} θ(x) ε(x)` and `M' = {c ≠ 0}` finite
(a finite set has approximate tangent space `{0}` at each of its points). -/
theorem Submission.dor_lmb_fcd_imp_degree_zero : ∀ (N N' : ℕ) (R : IMRep (univ : Set (Euclid N)) 0), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) 0, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) 0, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') 0) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[0].restrict R.carrier), F x = F' x) → Y F = Y F' := by
  intro N N' R hR
  classical
  -- `μHE[0]` is the counting measure
  have hsing : ∀ {P : ℕ} (x : Euclid P), (μHE[0] : Measure (Euclid P)) {x} = 1 := by
    intro P x
    rw [Measure.euclideanHausdorffMeasure_zero]
    exact Measure.hausdorffMeasure_zero_singleton x
  -- the carrier is finite, since `H⁰(M) ≤ R.measure univ < ∞`
  have hfin : R.carrier.Finite := by
    by_contra hinf
    have hle : (μHE[0] : Measure (Euclid N)) R.carrier ≤ R.measure univ := by
      rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← setLIntegral_one]
      exact setLIntegral_mono' R.measurableSet_carrier fun x hx => by
        exact_mod_cast R.mult_pos x hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_le_ne_top hR hle)
    obtain ⟨t, hts, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have : ((t.card : ℕ) : ℝ≥0∞) ≤ (μHE[0] : Measure (Euclid N)) R.carrier := by
      calc ((t.card : ℕ) : ℝ≥0∞) = ∑ x ∈ t, (μHE[0] : Measure (Euclid N)) {x} := by
            simp
        _ = (μHE[0] : Measure (Euclid N)) t := sum_measure_singleton
        _ ≤ _ := measure_mono hts
    exact absurd hn (not_lt.mpr this)
  set S := hfin.toFinset
  have hS : (S : Set (Euclid N)) = R.carrier := hfin.coe_toFinset
  -- `H⁰⌞M`-a.e. statements hold at every point of `M`
  have hpt : ∀ {p : Euclid N → Prop},
      (∀ᵐ x ∂((μHE[0] : Measure (Euclid N)).restrict R.carrier), p x) → ∀ x ∈ R.carrier, p x := by
    intro p hp x hx
    by_contra hpx
    have h0 := ae_iff.mp hp
    have hsub : ({x} : Set (Euclid N)) ⊆ {y | ¬ p y} ∩ R.carrier := by
      rintro y rfl
      exact ⟨hpx, hx⟩
    have h1 : (μHE[0] : Measure (Euclid N)) {x} ≤
        ((μHE[0] : Measure (Euclid N)).restrict R.carrier) {y | ¬ p y} :=
      (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
    rw [hsing, h0] at h1
    exact absurd h1 (by norm_num)
  -- the unit `0`-covector and the empty tuple; a `0`-covector is `α(∅)` times the unit
  let K₁ : ∀ {P : ℕ}, Covector (Euclid P) 0 := fun {P} =>
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ)
  let v₀ : ∀ {P : ℕ}, Fin 0 → Euclid P := fun {P} => fun i => i.elim0
  have hcov : ∀ {P : ℕ} (α : Covector (Euclid P) 0), α = α v₀ • K₁ := by
    intro P α
    ext v
    simp [K₁, Subsingleton.elim v v₀]
  have horient : ∀ x (α : Covector (Euclid N) 0), R.orient x α = α v₀ * R.orient x K₁ := by
    intro x α
    conv_lhs => rw [hcov α]
    rw [map_smul, smul_eq_mul]
  -- signs: on `M`, `ξ(x) = ε(x) · ev` with `ε(x) = ±1`
  have hsign : ∀ x ∈ R.carrier, R.orient x K₁ = 1 ∨ R.orient x K₁ = -1 := by
    intro x hx
    obtain ⟨Q, -, τ, -, -, hτ⟩ := hpt R.orients x hx
    rcases hτ with hτ | hτ
    · left; rw [hτ]; simp [K₁]
    · right; rw [hτ]; simp [K₁]
  let σ : Euclid N → ℤ := fun x => if R.orient x K₁ = 1 then 1 else -1
  have hσ : ∀ x ∈ R.carrier, R.orient x K₁ = (σ x : ℝ) := by
    intro x hx
    rcases hsign x hx with h | h
    · simp [σ, h]
    · simp [σ, h]
  let wZ : Euclid N → ℤ := fun x => (R.mult x : ℤ) * σ x
  -- `R.action β = ∑_{x ∈ M} θ(x) ε(x) β(x)(∅)`
  have haction : ∀ β : DifferentialForm (Euclid N) 0,
      R.action β = ∑ x ∈ S, (wZ x : ℝ) * β x v₀ := by
    intro β
    have hint : IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (β x)) (S : Set (Euclid N))
        (μHE[0] : Measure (Euclid N)) := by
      rw [← (S : Set (Euclid N)).biUnion_of_singleton, integrableOn_finite_biUnion S.finite_toSet]
      intro x _
      exact integrableOn_singleton (hx := by rw [hsing]; exact ENNReal.one_lt_top)
    rw [IMRep.action, ← hS, setIntegral_finset S hint]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxM : x ∈ R.carrier := hS ▸ hx
    rw [measureReal_def, hsing, ENNReal.toReal_one, one_smul, horient, hσ x hxM]
    simp only [wZ]
    push_cast
    ring
  -- the currents `Y(F)(ω) = ∑_{x ∈ M} θ(x) ε(x) ω(F(x))(∅)`
  let L : (Euclid N → Euclid N') → CurrentOn (univ : Set (Euclid N')) 0 := fun F =>
    { toFun := fun ω => ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring }
  have hL : ∀ F ω, L F ω = ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀ :=
    fun F ω => rfl
  have hcont : ∀ F (ωs : ℕ → TestFormOn (univ : Set (Euclid N')) 0), TestFormOnConverges ωs 0 →
      Tendsto (fun j => L F (ωs j)) atTop (𝓝 0) := by
    intro F ωs hωs
    obtain ⟨K, -, -, hsupp, -, hconv⟩ := hωs
    have hpt0 : ∀ y,
        Tendsto (fun j => (ωs j : DifferentialForm (Euclid N') 0) y v₀) atTop (𝓝 0) := by
      intro y
      by_cases hy : y ∈ K
      · have hΦ : Continuous (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Euclid N')
            (Covector (Euclid N') 0) => g v₀ v₀) :=
          (continuous_eval_const v₀).comp (continuous_eval_const v₀)
        have h0 := (hΦ.tendsto _).comp ((hconv 0).tendsto_at hy)
        simpa [Function.comp_def, iteratedFDeriv_zero_apply] using h0
      · have hz : ∀ j, (ωs j : DifferentialForm (Euclid N') 0) y = 0 := fun j =>
          image_eq_zero_of_notMem_tsupport fun h => hy (hsupp j h)
        simp [hz]
    have := tendsto_finsetSum S fun x _ => (hpt0 (F x)).const_mul (wZ x : ℝ)
    simpa [hL] using this
  let Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) 0 := fun F =>
    ⟨L F, hcont F⟩
  have hY : ∀ F ω, Y F ω = ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀ :=
    fun F ω => rfl
  refine ⟨Y, fun F Λ hF => ⟨?_, ?_⟩, ?_⟩
  · -- integrality: regroup the finite sum by the fibres of `F`
    let c : Euclid N' → ℤ := fun y => ∑ x ∈ S.filter (fun x => F x = y), wZ x
    have hc_supp : ∀ y, c y ≠ 0 → y ∈ S.image F := by
      intro y hy
      by_contra hy'
      apply hy
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_filter] at hx
      exact absurd (Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩) hy'
    let T' : Finset (Euclid N') := (S.image F).filter (fun y => c y ≠ 0)
    have hT' : ∀ y, y ∈ T' ↔ c y ≠ 0 := by
      intro y
      simp only [T', Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hc_supp y h, h⟩⟩
    have hT'meas : MeasurableSet (T' : Set (Euclid N')) := T'.finite_toSet.measurableSet
    let ev : MultiVector N' 0 := ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ v₀
    let orient' : Euclid N' → MultiVector N' 0 := fun y => if c y < 0 then -ev else ev
    refine ⟨{ carrier := T'
              mult := fun y => (c y).natAbs
              orient := orient'
              measurableSet_carrier := hT'meas
              carrier_subset := subset_univ _
              rectifiable := ?_
              measurable_mult := ?_
              mult_pos := ?_
              locallyIntegrable_mult := ?_
              aestronglyMeasurable_orient := ?_
              orients := ?_ }, ?_⟩
    · -- a finite set is countably `0`-rectifiable
      obtain ⟨g, hg⟩ := Set.countable_iff_exists_subset_range.mp T'.countable_toSet
      refine ⟨∅, measure_empty, fun j _ => g j, fun j => ⟨0, LipschitzWith.const _⟩, ?_⟩
      intro y hy
      obtain ⟨j, rfl⟩ := hg hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, 0, rfl⟩)
    · -- measurability of the multiplicity
      refine measurable_to_countable' fun k => ?_
      by_cases hk : k = 0
      · have : (fun y => (c y).natAbs) ⁻¹' {k} = (T' : Set (Euclid N'))ᶜ := by
          ext y
          simp [hk, hT']
        rw [this]
        exact hT'meas.compl
      · refine (T'.finite_toSet.subset fun y hy => ?_).measurableSet
        have hy' : (c y).natAbs = k := hy
        rw [Finset.mem_coe, hT']
        intro h0
        rw [h0] at hy'
        exact hk hy'.symm
    · intro y hy
      exact Int.natAbs_pos.mpr ((hT' y).mp hy)
    · intro K _ _
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_set Set.inter_subset_left)
      rw [lintegral_finset]
      exact ENNReal.sum_ne_top.mpr fun y _ => by simp
    · refine (StronglyMeasurable.ite ?_ stronglyMeasurable_const
        stronglyMeasurable_const).aestronglyMeasurable
      exact (T'.finite_toSet.subset fun y hy => (hT' y).mpr (ne_of_lt hy)).measurableSet
    · refine ae_restrict_of_forall_mem hT'meas fun y hy => ⟨⊥, ⟨by simp, fun f => ?_⟩, ?_⟩
      · -- the approximate tangent space of a finite set is `{0}`
        obtain ⟨ρ, hρ⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Euclid N')
        have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ ∀ z ∈ T', z ≠ y → ρ < r⁻¹ * ‖z - y‖ := by
          refine eventually_mem_nhdsWithin.and ((Filter.eventually_all_finset T').2 fun z _ => ?_)
          by_cases hzy : z = y
          · exact Eventually.of_forall fun _ h => absurd hzy h
          · have hd : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
            exact ((tendsto_inv_nhdsGT_zero.atTop_mul_const hd).eventually_gt_atTop ρ).mono
              fun r hr _ => hr
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with r hr
        obtain ⟨hr0, hfar⟩ := hr
        symm
        rw [Submodule.bot_coe]
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (T'.finite_toSet.image _).measurableSet ?_ ?_
        · rintro _ rfl
          exact ⟨y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap]⟩
        · rintro _ ⟨⟨z, hz, rfl⟩, hz0⟩
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have hzy : z ≠ y := by
            rintro rfl
            exact hz0 (by simp [Poincare.SimonGMT.Chapter03.blowUpMap])
          have h1 := hρ hmem
          have h2 := hfar z hz hzy
          rw [mem_closedBall_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
            Real.norm_of_nonneg hr0.le] at h1
          linarith
      · -- `±ev` orients `⊥`
        refine ⟨v₀, ⟨fun i => i.elim0, by intro i; exact i.elim0⟩, by simp, ?_⟩
        by_cases hneg : c y < 0
        · right; intro α; simp [orient', hneg, ev]
        · left; intro α; simp [orient', hneg, ev]
    · -- `R'` represents `Y(F)`
      intro ω
      have hint : IntegrableOn
          (fun y => ((c y).natAbs : ℝ) * orient' y ((ω : DifferentialForm (Euclid N') 0) y))
          (T' : Set (Euclid N')) (μHE[0] : Measure (Euclid N')) := by
        rw [← (T' : Set (Euclid N')).biUnion_of_singleton,
          integrableOn_finite_biUnion T'.finite_toSet]
        intro y _
        exact integrableOn_singleton (hx := by rw [hsing]; exact ENNReal.one_lt_top)
      show ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀ =
        ∫ y in (T' : Set (Euclid N')),
          ((c y).natAbs : ℝ) * orient' y ((ω : DifferentialForm (Euclid N') 0) y)
            ∂(μHE[0] : Measure (Euclid N'))
      rw [setIntegral_finset T' hint]
      have hterm : ∀ y ∈ T', (μHE[0] : Measure (Euclid N')).real {y} •
          (((c y).natAbs : ℝ) * orient' y ((ω : DifferentialForm (Euclid N') 0) y)) =
          (c y : ℝ) * (ω : DifferentialForm (Euclid N') 0) y v₀ := by
        intro y _
        rw [measureReal_def, hsing, ENNReal.toReal_one, one_smul, Nat.cast_natAbs, Int.cast_abs]
        by_cases hneg : c y < 0
        · have habs : |(c y : ℝ)| = -(c y : ℝ) := abs_of_neg (by exact_mod_cast hneg)
          simp only [orient', ite_eq_left hneg, ev, habs, neg_apply,
            ContinuousAlternatingMap.apply_apply]
          ring
        · have habs : |(c y : ℝ)| = (c y : ℝ) := abs_of_nonneg (by exact_mod_cast not_lt.mp hneg)
          simp only [orient', ite_eq_right hneg, ev, habs, ContinuousAlternatingMap.apply_apply]
      rw [Finset.sum_congr rfl hterm]
      show _ = ∑ y ∈ (S.image F).filter (fun y => c y ≠ 0),
        (c y : ℝ) * (ω : DifferentialForm (Euclid N') 0) y v₀
      rw [Finset.sum_filter_of_ne]
      · simp only [c, Int.cast_sum, Finset.sum_mul]
        rw [← Finset.sum_fiberwise_of_maps_to (g := F) (t := S.image F)
          fun x hx => Finset.mem_image_of_mem F hx]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
        rw [(Finset.mem_filter.mp hx).2]
      · intro y _ h h0
        apply h
        rw [h0, Int.cast_zero, zero_mul]
  · -- `R.action(F_j^# ω) → Y(F)(ω)`
    intro Fs _ _ hFs ω
    simp only [haction, hY]
    refine tendsto_finsetSum S fun x _ => Tendsto.const_mul _ ?_
    have hω : Continuous (ω : DifferentialForm (Euclid N') 0) := ContDiff.continuous ω.property.1.1
    have h1 := (((continuous_eval_const v₀).comp hω).tendsto (F x)).comp (hFs.tendsto_at x)
    refine h1.congr fun j => ?_
    simp only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  · -- locality
    intro F F' Λ _ _ hFF'
    have hEq : ∀ x ∈ R.carrier, F x = F' x := hpt hFF'
    ext ω
    simp only [hY]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hEq x (hS ▸ hx)]

/-- **Simon Ch. 6, 3.4–3.5** (orientation along a bi-Lipschitz parametrised piece): let
`(M, θ, ξ)` be an integer multiplicity triple of degree `k` in `ℝᴺ` with `Hᵏ(M) < ∞`, `G : ℝᵏ → ℝᴺ`
Lipschitz, `B` Borel with `κ|a − a'| ≤ |G(a) − G(a')|` on `B`, `DG(a)` injective for `a ∈ B`, and
`G(B) ⊆ M`.  Then there is a Borel sign `s = ±1` with
`J_G(u) ξ(G u) = s(u) DG(u)e₁ ∧ ⋯ ∧ DG(u)eₖ` for a.e. `u ∈ B`, `J_G = det(⟨DG eₐ, DG e_b⟩)^{1/2}`.
For a.e. `u ∈ B`, `T_{G(u)}M = range DG(u)` and `ξ(G u)` orients it; so does
`ζ = J_G⁻¹ DG(u)e₁ ∧ ⋯ ∧ DG(u)eₖ`, hence `ξ(G u) = ±ζ`.  The sign is read off by comparing the
distances from `J_G ξ̃(G u)` to `±DG(u)e₁ ∧ ⋯ ∧ DG(u)eₖ`, `ξ̃` a Borel version of `ξ`. -/
theorem Submission.dor_lmb_fcd_imp_piece_orientation_sign : ∀ (N k : ℕ) (R : IMRep (univ : Set (Euclid N)) k) (G : Euclid k → Euclid N) (B : Set (Euclid k)) (L : NNReal) (κ : ℝ), μHE[k] R.carrier ≠ ∞ → LipschitzWith L G → MeasurableSet B → 0 < κ → (∀ a ∈ B, ∀ a' ∈ B, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ B, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' B ⊆ R.carrier → ∃ s : Euclid k → ℝ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧ ∀ᵐ u ∂(volume.restrict B), ∀ α : Covector (Euclid N) k, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ G u (EuclideanSpace.single b (1 : ℝ))))) * R.orient (G u) α = s u * α (fun a => fderiv ℝ G u (EuclideanSpace.single a (1 : ℝ))) := by
  intro N k R G B L κ hfin hG hB hκ hbi hdiff hGBM
  -- `e` is the standard basis of `ℝᵏ`; `J T = det(⟨T eₐ, T e_b⟩)^{1/2}` and `Ev T = (α ↦ α(T e))`
  let e : Fin k → Euclid k := fun a => EuclideanSpace.single a (1 : ℝ)
  let J : (Euclid k →L[ℝ] Euclid N) → ℝ := fun T =>
    Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (T (e a)) (T (e b))))
  let Ev : (Euclid k →L[ℝ] Euclid N) → MultiVector N k := fun T =>
    (ContinuousAlternatingMap.apply ℝ (Euclid k) ℝ e).comp
      (ContinuousAlternatingMap.compContinuousLinearMapCLM T)
  have hev : ∀ v : Euclid k, Continuous fun T : Euclid k →L[ℝ] Euclid N => T v :=
    fun v => continuous_eval_const v
  have hJc : Continuous J := Real.continuous_sqrt.comp (Continuous.matrix_det
    (continuous_matrix fun a b => (hev (e a)).inner (hev (e b))))
  have hEvc : Continuous Ev :=
    continuous_const.clm_comp ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM
  -- Step 1: `Hᵏ⌞M`-a.e. properties hold at `G u` for a.e. `u ∈ B`
  obtain ⟨-, hpull⟩ := Submission.ptd_piece_image_measurable_ae_pullback N k G B L κ hG hB hκ hbi
  have hpullM : ∀ p : Euclid N → Prop, (∀ᵐ y ∂(μHE[k].restrict R.carrier), p y) →
      ∀ᵐ u ∂(volume.restrict B), p (G u) :=
    fun p hp => hpull p (ae_restrict_of_ae_restrict_of_subset hGBM hp)
  -- a strongly measurable version `g` of the orientation `ξ`
  let g := R.aestronglyMeasurable_orient.mk R.orient
  have hg : StronglyMeasurable g := R.aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hgeq : ∀ᵐ u ∂(volume.restrict B), R.orient (G u) = g (G u) :=
    hpullM (fun y => R.orient y = g y) R.aestronglyMeasurable_orient.ae_eq_mk
  -- the sign `s u = ±1` compares the distances from `J g(G u)` to `±Ev(DG u)`
  let X : Euclid k → MultiVector N k := fun u => J (fderiv ℝ G u) • g (G u)
  let E : Euclid k → MultiVector N k := fun u => Ev (fderiv ℝ G u)
  let s : Euclid k → ℝ := fun u =>
    if dist (X u) (E u) ≤ dist (X u) ((-1 : ℝ) • E u) then 1 else -1
  have hX : StronglyMeasurable X :=
    (hJc.measurable.comp (measurable_fderiv ℝ G)).stronglyMeasurable.smul
      (hg.comp_measurable hG.continuous.measurable)
  have hE : StronglyMeasurable E :=
    hEvc.comp_stronglyMeasurable (measurable_fderiv ℝ G).stronglyMeasurable
  have hs : Measurable s :=
    Measurable.ite (measurableSet_le
      ((continuous_dist (α := MultiVector N k)).comp_stronglyMeasurable (hX.prodMk hE)).measurable
      ((continuous_dist (α := MultiVector N k)).comp_stronglyMeasurable
        (hX.prodMk (hE.const_smul (-1 : ℝ)))).measurable)
      measurable_const measurable_const
  refine ⟨s, hs, fun u => ?_, ?_⟩
  · simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- Steps 2–5: for a.e. `u ∈ B`, `J ξ(G u) = ± Ev(DG u)`
  have hkey : ∀ᵐ u ∂(volume.restrict B), X u = E u ∨ X u = (-1 : ℝ) • E u := by
    filter_upwards [ae_restrict_mem hB, hgeq, hpullM _ R.orients,
      Submission.dpf_approxTangent_ae_bilipschitz_piece N k univ R.carrier G B L κ isOpen_univ
        R.measurableSet_carrier (subset_univ _)
        (fun C _ _ => ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)) hG hB hκ hbi
        hdiff hGBM] with u huB hgu hQ hT
    obtain ⟨Q, hQ, hξQ⟩ := hQ
    obtain ⟨-, hinj⟩ := hdiff u huB
    -- the approximate tangent space at `G u` is `range DG(u)`
    have hQeq : Q = LinearMap.range (fderiv ℝ G u : Euclid k →ₗ[ℝ] Euclid N) := hQ.unique hT
    -- `v = DG(u) e` is linearly independent and spans `range DG(u)`
    have hli : LinearIndependent ℝ (fun a => fderiv ℝ G u (e a)) := by
      have h := ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis.linearIndependent).map'
        (fderiv ℝ G u : Euclid k →ₗ[ℝ] Euclid N) (LinearMap.ker_eq_bot.2 hinj)
      convert h using 1
      funext a
      simp [e]
    have hspan : Submodule.span ℝ (range fun a => fderiv ℝ G u (e a)) =
        LinearMap.range (fderiv ℝ G u : Euclid k →ₗ[ℝ] Euclid N) := by
      rw [LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.span_eq,
        Submodule.map_span, ← range_comp]
      congr 2
      funext a
      simp [e]
    -- `ζ = J⁻¹ Ev(DG u)` is a unit orientation of `range DG(u)`, and `J > 0`
    obtain ⟨hpos, hwedge⟩ :=
      Submission.codim1_lur_normalized_wedge_orientation N k (fun a => fderiv ℝ G u (e a)) hli
    have hJpos : 0 < J (fderiv ℝ G u) := Real.sqrt_pos.2 hpos
    have hζ : IsUnitOrientationOf ((J (fderiv ℝ G u))⁻¹ • E u) Q := by
      rw [hQeq, ← hspan]
      exact hwedge _ fun α => rfl
    -- `ξ(G u) = ±ζ`
    rcases Submission.rsdic_unitOrientation_eq_or_eq_neg N k _ _ Q hζ hξQ with h | h
    · left
      ext α
      show J (fderiv ℝ G u) * g (G u) α = E u α
      rw [← hgu, h]
      show J (fderiv ℝ G u) * ((J (fderiv ℝ G u))⁻¹ * E u α) = E u α
      rw [← mul_assoc, mul_inv_cancel₀ hJpos.ne', one_mul]
    · right
      ext α
      show J (fderiv ℝ G u) * g (G u) α = -1 * E u α
      rw [← hgu, h]
      show J (fderiv ℝ G u) * -((J (fderiv ℝ G u))⁻¹ * E u α) = -1 * E u α
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hJpos.ne', one_mul, neg_one_mul]
  -- Steps 5–7: the distance comparison selects the sign
  filter_upwards [hkey, hgeq] with u hu hgu α
  rw [hgu]
  show X u α = s u * E u α
  simp only [s]
  split_ifs with hle
  · rcases hu with h | h
    · rw [h, one_mul]
    · rw [h, dist_self] at hle
      have h0 : (-1 : ℝ) • E u = E u := dist_le_zero.1 hle
      rw [h, h0, one_mul]
  · rcases hu with h | h
    · exact absurd (by rw [h, dist_self]; exact dist_nonneg) hle
    · rw [h]
      rfl

/-- **Parametric representation of an integer multiplicity triple of finite mass** (Simon Ch. 6,
3.1 and 3.3–3.6, with Ch. 3, 1.1–1.3).  Let `R = (M, θ, ξ)` be an `IMRep` in `ℝᴺ` with
`μ_R(ℝᴺ) = ∫_M θ dHᵏ < ∞`, and write `J_G = √det(⟨DG eₐ, DG e_b⟩)`.  Then `M` is, up to an
`Hᵏ`-null set, the disjoint union of Borel pieces `Pᵢ = Gᵢ(Bᵢ) ⊆ M` with `Gᵢ` Lipschitz,
`mᵢ|a − a'| ≤ |Gᵢ(a) − Gᵢ(a')|` on `Bᵢ` and `DGᵢ` injective on `Bᵢ`
(`dpf_rectifiable_bilipschitz_pieces`); on each piece `J_{Gᵢ} ξ(Gᵢ) = sᵢ DGᵢ e` a.e. with
`sᵢ = ±1` (`dor_lmb_fcd_imp_piece_orientation_sign`), and the integer weights are
`wᵢ = (θ ∘ Gᵢ) sᵢ`.  The inverse of `Gᵢ|Bᵢ` is `mᵢ⁻¹`-Lipschitz, so `Gᵢ#(Lᵏ⌞Bᵢ) ≤ mᵢ^{-k} Hᵏ⌞Pᵢ`:
this gives `∫_{Bᵢ} |wᵢ| < ∞` and pulls `Hᵏ`-a.e. statements on `M` back to `Lᵏ`-a.e. statements on
`Bᵢ`.  The area formula `Hᵏ⌞Pᵢ = Gᵢ#((J_{Gᵢ} Lᵏ)⌞Bᵢ)` (`codim1_lura_gram_area_formula`) gives
`Σᵢ ∫_{Bᵢ} |wᵢ| J_{Gᵢ} = ∫_{⋃ Pᵢ} θ dHᵏ ≤ μ_R(ℝᴺ)` and, for bounded continuous `γ`,
`τ(M, θ, ξ)(γ) = Σᵢ ∫_{Pᵢ} θ ξ(γ) dHᵏ = Σᵢ ∫_{Bᵢ} wᵢ γ(Gᵢ)(DGᵢ e)` by countable additivity. -/
theorem Submission.dor_lmb_fcd_imp_parametric_rep : ∀ (N k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ (G : ℕ → Euclid k → Euclid N) (B : ℕ → Set (Euclid k)) (w : ℕ → Euclid k → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, ∀ u ∈ B i, DifferentiableAt ℝ (G i) u) ∧ (∀ i, Measurable (w i)) ∧ (∀ i u, ∃ z : ℤ, w i u = z) ∧ (∀ i, ∀ u ∈ B i, w i u ≠ 0) ∧ (∀ i, IntegrableOn (w i) (B i)) ∧ ∑' i, ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ)))))) ≤ R.measure univ ∧ (∀ γ : Euclid N → Covector (Euclid N) k, Continuous γ → (∃ C : ℝ, ∀ x, ‖γ x‖ ≤ C) → HasSum (fun i => ∫ u in B i, w i u * γ (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))) (R.action γ)) ∧ ∀ p : Euclid N → Prop, (∀ᵐ x ∂(μHE[k].restrict R.carrier), p x) → ∀ i, ∀ᵐ u ∂(volume.restrict (B i)), p (G i u) := by
  intro N k R hfin
  -- `θ` as a Borel function with values in `ℝ≥0∞` and in `ℝ`
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    (measurable_from_nat (f := fun j : ℕ => (j : ℝ≥0∞))).comp R.measurable_mult
  have hθmR : Measurable fun x => (R.mult x : ℝ) :=
    (measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp R.measurable_mult
  -- Step 1: `μ_R(ℝᴺ) = ∫_M θ dHᵏ`, and `Hᵏ(M) ≤ μ_R(ℝᴺ) < ∞` since `θ ≥ 1` on `M`
  have hmass : R.measure univ = ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k] := by
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hMfin : μHE[k] R.carrier ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [hmass]
    calc μHE[k] R.carrier = ∫⁻ _ in R.carrier, (1 : ℝ≥0∞) ∂μHE[k] := by rw [setLIntegral_one]
      _ ≤ ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k] := by
        refine setLIntegral_mono hθm fun x hx => ?_
        exact_mod_cast R.mult_pos x hx
  -- Step 2: disjoint Borel bi-Lipschitz pieces `Pᵢ = Gᵢ(Bᵢ) ⊆ M` covering `M` up to a null set
  obtain ⟨G, B, m, hLip, hBm, hm, hbi, hdiff, hPm, hPM, hdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces N k R.carrier R.measurableSet_carrier
      R.rectifiable
  choose L hL using hLip
  have hGm : ∀ i, Measurable (G i) := fun i => (hL i).continuous.measurable
  have hinj : ∀ i, InjOn (G i) (B i) := by
    intro i a ha a' ha' h
    have h1 := hbi i a ha a' ha'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖a - a'‖ ≤ 0 := by
      by_contra hc
      exact absurd h1 (not_le.mpr (mul_pos (hm i) (not_le.mp hc)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- the Gram-determinant Jacobian `J_{Gᵢ}`
  obtain ⟨J, hJ⟩ : ∃ J : ℕ → Euclid k → ℝ, ∀ i u, J i u = Real.sqrt (Matrix.det
      (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))
        (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ))))) :=
    ⟨_, fun _ _ => rfl⟩
  have hJm : ∀ i, Measurable (J i) := by
    intro i
    have h := (Submission.codim1_lura_gram_area_formula k N (G i)).1
    simp only [← hJ] at h
    exact h
  -- Step 3: the signs `sᵢ = ±1` with `J_{Gᵢ}(u) ξ(Gᵢ u) = sᵢ(u) DGᵢ(u)e` a.e. on `Bᵢ`
  choose s hsm hspm hsae using fun i =>
    Submission.dor_lmb_fcd_imp_piece_orientation_sign N k R (G i) (B i) (L i) (m i) hMfin (hL i)
      (hBm i) (hm i) (hbi i) (hdiff i) (hPM i)
  -- Step 4: the weights `wᵢ = (θ ∘ Gᵢ) sᵢ`
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Euclid k → ℝ, ∀ i u, w i u = (R.mult (G i u) : ℝ) * s i u :=
    ⟨_, fun _ _ => rfl⟩
  have hwm : ∀ i, Measurable (w i) := by
    intro i
    have h : w i = fun u => (R.mult (G i u) : ℝ) * s i u := funext (hw i)
    rw [h]
    exact (hθmR.comp (hGm i)).mul (hsm i)
  have hwz : ∀ i u, ∃ z : ℤ, w i u = z := by
    intro i u
    rcases hspm i u with h | h
    · exact ⟨(R.mult (G i u) : ℤ), by rw [hw, h]; push_cast; ring⟩
    · exact ⟨-(R.mult (G i u) : ℤ), by rw [hw, h]; push_cast; ring⟩
  have hw0 : ∀ i, ∀ u ∈ B i, w i u ≠ 0 := by
    intro i u hu
    have hpos : 0 < R.mult (G i u) := R.mult_pos _ (hPM i (mem_image_of_mem _ hu))
    rw [hw]
    refine mul_ne_zero (by exact_mod_cast hpos.ne') ?_
    rcases hspm i u with h | h <;> rw [h] <;> norm_num
  have hwe : ∀ i u, ‖w i u‖ₑ = (R.mult (G i u) : ℝ≥0∞) := by
    intro i u
    rcases hspm i u with h | h <;> simp [hw, h]
  -- Step 5: `Lᵏ(Bᵢ ∩ Gᵢ⁻¹ Z) ≤ mᵢ^{-k} Hᵏ(Z ∩ Pᵢ)`, the inverse of `Gᵢ|Bᵢ` being `mᵢ⁻¹`-Lipschitz
  have hpull : ∀ i (Z : Set (Euclid N)), volume (G i ⁻¹' Z ∩ B i) ≤
      ((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k * μHE[k] (Z ∩ G i '' B i) := by
    intro i Z
    have hψ : LipschitzOnWith (Real.toNNReal (m i)⁻¹) (Function.invFunOn (G i) (B i))
        (G i '' B i) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨a', ha', rfl⟩ := hy'
      rw [(hinj i).leftInvOn_invFunOn ha, (hinj i).leftInvOn_invFunOn ha',
        Real.coe_toNNReal _ (inv_nonneg.mpr (hm i).le), dist_eq_norm, dist_eq_norm,
        inv_mul_eq_div, le_div_iff₀ (hm i)]
      linarith [hbi i a ha a' ha']
    have hsub : G i ⁻¹' Z ∩ B i ⊆ Function.invFunOn (G i) (B i) '' (Z ∩ G i '' B i) :=
      fun u hu => ⟨G i u, ⟨hu.1, mem_image_of_mem _ hu.2⟩, (hinj i).leftInvOn_invFunOn hu.2⟩
    calc volume (G i ⁻¹' Z ∩ B i)
        ≤ volume (Function.invFunOn (G i) (B i) '' (Z ∩ G i '' B i)) := measure_mono hsub
      _ = μHE[k] (Function.invFunOn (G i) (B i) '' (Z ∩ G i '' B i)) := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      _ ≤ _ := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
          (hψ.mono inter_subset_right)
  have hmaple : ∀ i, Measure.map (G i) (volume.restrict (B i)) ≤
      ((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k • μHE[k].restrict (G i '' B i) := by
    intro i
    rw [Measure.le_iff]
    intro Z hZ
    rw [Measure.map_apply (hGm i) hZ, Measure.restrict_apply (hGm i hZ), Measure.smul_apply,
      Measure.restrict_apply hZ, smul_eq_mul]
    exact hpull i Z
  -- Step 5(a): `Hᵏ`-a.e. statements on `M` pull back to `Lᵏ`-a.e. statements on `Bᵢ`
  have hae : ∀ p : Euclid N → Prop, (∀ᵐ x ∂(μHE[k].restrict R.carrier), p x) →
      ∀ i, ∀ᵐ u ∂(volume.restrict (B i)), p (G i u) := by
    intro p hp i
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier] at hp
    rw [ae_iff, Measure.restrict_apply' (hBm i)]
    refine nonpos_iff_eq_zero.mp ?_
    calc volume ({u | ¬p (G i u)} ∩ B i)
        ≤ ((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k * μHE[k] ({x | ¬p x} ∩ G i '' B i) :=
          hpull i {x | ¬p x}
      _ ≤ ((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k * μHE[k] ({x | ¬p x} ∩ R.carrier) := by
          gcongr
          exact hPM i
      _ = 0 := by rw [hp, mul_zero]
  -- Step 6: `∫_{Bᵢ} |wᵢ| = ∫_{Bᵢ} θ ∘ Gᵢ ≤ mᵢ^{-k} ∫_{Pᵢ} θ dHᵏ ≤ mᵢ^{-k} μ_R(ℝᴺ) < ∞`
  have hwint : ∀ i, IntegrableOn (w i) (B i) := by
    intro i
    refine ⟨(hwm i).aestronglyMeasurable, ?_⟩
    show ∫⁻ u in B i, ‖w i u‖ₑ < ∞
    simp only [hwe]
    calc ∫⁻ u in B i, (R.mult (G i u) : ℝ≥0∞)
        = ∫⁻ y, (R.mult y : ℝ≥0∞) ∂(Measure.map (G i) (volume.restrict (B i))) :=
          (lintegral_map hθm (hGm i)).symm
      _ ≤ ∫⁻ y, (R.mult y : ℝ≥0∞) ∂(((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k •
            μHE[k].restrict (G i '' B i)) := lintegral_mono' (hmaple i) le_rfl
      _ = ((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k *
            ∫⁻ y in G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[k] := lintegral_smul_measure _ _
      _ ≤ ((Real.toNNReal (m i)⁻¹ : NNReal) : ℝ≥0∞) ^ k *
            ∫⁻ y in R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[k] := by
          gcongr
          exact hPM i
      _ < ∞ := by
          rw [← hmass]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfin.lt_top
  -- Step 7: the area formula on `Pᵢ`, and `Hᵏ⌞Pᵢ = Gᵢ#((J_{Gᵢ} Lᵏ)⌞Bᵢ)`
  have harea' : ∀ i (g : Euclid N → ℝ≥0∞), ∫⁻ y in G i '' B i, g y ∂μHE[k] =
      ∫⁻ u in B i, ENNReal.ofReal (J i u) * g (G i u) := by
    intro i g
    rw [(Submission.codim1_lura_gram_area_formula k N (G i)).2 (B i) (hBm i)
      (fun u hu => (hdiff i u hu).1) (fun u hu => (hdiff i u hu).2) (hinj i) g]
    simp only [hJ]
  have hμeq : ∀ i, μHE[k].restrict (G i '' B i) = Measure.map (G i)
      ((volume.restrict (B i)).withDensity fun u => ((J i u).toNNReal : ℝ≥0∞)) := by
    intro i
    ext Z hZ
    rw [Measure.map_apply (hGm i) hZ, withDensity_apply _ (hGm i hZ),
      ← lintegral_indicator_one hZ, harea' i, ← lintegral_indicator (hGm i hZ)]
    refine lintegral_congr fun u => ?_
    by_cases hu : G i u ∈ Z
    · simp [hu, indicator_of_mem, ENNReal.ofReal]
    · simp [hu]
  have htr : ∀ i (h : Euclid N → ℝ), AEStronglyMeasurable h (μHE[k].restrict R.carrier) →
      ∫ y in G i '' B i, h y ∂μHE[k] = ∫ u in B i, J i u * h (G i u) := by
    intro i h hh
    have hh' : AEStronglyMeasurable h (Measure.map (G i)
        ((volume.restrict (B i)).withDensity fun u => ((J i u).toNNReal : ℝ≥0∞))) := by
      rw [← hμeq i]
      exact hh.mono_measure (Measure.restrict_mono (hPM i) le_rfl)
    rw [hμeq i, integral_map (hGm i).aemeasurable hh',
      integral_withDensity_eq_integral_smul (hJm i).real_toNNReal]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _), hJ]
  -- Step 8: `Σᵢ ∫_{Bᵢ} |wᵢ| J_{Gᵢ} = Σᵢ ∫_{Pᵢ} θ dHᵏ = ∫_{⋃ Pᵢ} θ dHᵏ ≤ μ_R(ℝᴺ)`
  have hmassle : ∑' i, ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (J i u) ≤ R.measure univ := by
    calc ∑' i, ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (J i u)
        = ∑' i, ∫⁻ y in G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[k] := by
          refine tsum_congr fun i => ?_
          rw [harea' i]
          refine lintegral_congr fun u => ?_
          rw [hwe, mul_comm]
      _ = ∫⁻ y in ⋃ i, G i '' B i, (R.mult y : ℝ≥0∞) ∂μHE[k] := (lintegral_iUnion hPm hdisj _).symm
      _ ≤ ∫⁻ y in R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[k] := lintegral_mono_set (iUnion_subset hPM)
      _ = R.measure univ := hmass.symm
  -- Step 9: for bounded continuous `γ`, `τ(γ) = Σᵢ ∫_{Pᵢ} θ ξ(γ) dHᵏ = Σᵢ ∫_{Bᵢ} wᵢ γ(Gᵢ)(DGᵢ e)`
  have hsum : ∀ γ : Euclid N → Covector (Euclid N) k, Continuous γ → (∃ C : ℝ, ∀ x, ‖γ x‖ ≤ C) →
      HasSum (fun i => ∫ u in B i, w i u * γ (G i u)
        (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))) (R.action γ) := by
    rintro γ hγ ⟨C, hC⟩
    -- (a) `|ξ(x)(α)| ≤ ‖α‖` a.e. on `M`, `ξ(x)` being a unit orientation; hence `θ ξ(γ)` is
    -- `Hᵏ`-integrable on `M`, being dominated by `C θ`
    have hbound : ∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ α : Covector (Euclid N) k,
        |R.orient x α| ≤ ‖α‖ := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
      intro α
      have hτn : ∀ j, ‖τ j‖ = 1 := fun j => hτ.1 j
      have hατ : |α τ| ≤ ‖α‖ := by
        have h := α.le_opNorm τ
        simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
        exact h
      rcases hξ with h | h
      · rw [h]; exact hατ
      · rw [h, abs_neg]; exact hατ
    have hθi : Integrable (fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) := by
      refine ⟨hθmR.aestronglyMeasurable, ?_⟩
      show ∫⁻ x in R.carrier, ‖(R.mult x : ℝ)‖ₑ ∂μHE[k] < ∞
      simp only [Real.enorm_natCast]
      rw [← hmass]
      exact hfin.lt_top
    have hhm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (γ x))
        (μHE[k].restrict R.carrier) := by
      have h2 : AEStronglyMeasurable (fun x => R.orient x (γ x)) (μHE[k].restrict R.carrier) :=
        Continuous.comp_aestronglyMeasurable₂
          (g := fun (L : MultiVector N k) (α : Covector (Euclid N) k) => L α)
          (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid N) k) (F := ℝ)).continuous
          R.aestronglyMeasurable_orient hγ.aestronglyMeasurable
      exact hθmR.aestronglyMeasurable.mul h2
    have hhi : IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (γ x)) R.carrier μHE[k] := by
      refine Integrable.mono' (hθi.const_mul C) hhm ?_
      filter_upwards [hbound] with x hx
      rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x (γ x)| ≤ (R.mult x : ℝ) * ‖γ x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    -- (b) `τ(γ) = ∫_{⋃ Pᵢ} θ ξ(γ) dHᵏ = Σᵢ ∫_{Pᵢ} θ ξ(γ) dHᵏ`
    have haction : R.action γ =
        ∫ y in ⋃ i, G i '' B i, (R.mult y : ℝ) * R.orient y (γ y) ∂μHE[k] := by
      rw [IMRep.action]
      refine setIntegral_congr_set ?_
      rw [ae_eq_set]
      refine ⟨hnull, ?_⟩
      rw [sdiff_eq_empty.mpr (iUnion_subset hPM), measure_empty]
    have hU := hasSum_integral_iUnion hPm hdisj (hhi.mono_set (iUnion_subset hPM))
    -- (c) `∫_{Pᵢ} θ ξ(γ) dHᵏ = ∫_{Bᵢ} J_{Gᵢ} θ(Gᵢ) ξ(Gᵢ)(γ(Gᵢ)) = ∫_{Bᵢ} wᵢ γ(Gᵢ)(DGᵢ e)`
    have hterm : ∀ i, ∫ y in G i '' B i, (R.mult y : ℝ) * R.orient y (γ y) ∂μHE[k] =
        ∫ u in B i, w i u * γ (G i u)
          (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) := by
      intro i
      rw [htr i _ hhm]
      refine integral_congr_ae ?_
      filter_upwards [hsae i] with u hu
      have h := hu (γ (G i u))
      rw [← hJ] at h
      rw [hw]
      calc J i u * ((R.mult (G i u) : ℝ) * R.orient (G i u) (γ (G i u)))
          = (R.mult (G i u) : ℝ) * (J i u * R.orient (G i u) (γ (G i u))) := by ring
        _ = (R.mult (G i u) : ℝ) * (s i u * γ (G i u)
              (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))) := by rw [h]
        _ = (R.mult (G i u) : ℝ) * s i u * γ (G i u)
              (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) := by ring
    rw [haction, ← funext hterm]
    exact hU
  -- Step 10: assemble
  refine ⟨G, B, w, fun i => ⟨L i, hL i⟩, hBm, fun i u hu => (hdiff i u hu).1, hwm, hwz, hw0,
    hwint, ?_, hsum, hae⟩
  simpa only [hJ] using hmassle
/-- **Simon Ch. 3, 1.2–1.3** (bi-Lipschitz partition of the regular set): for any
`H : ℝᵏ → ℝ^{N'}` and Borel `B ⊆ ℝᵏ`, the set `S` of `u ∈ B` at which `H` is differentiable with
injective derivative is the disjoint union of countably many Borel pieces `Aₗ` with
`κₗ|a − a'| ≤ |H(a) − H(a')|` on `Aₗ`, `κₗ > 0`.  `S` is Borel (`measurableSet_of_differentiableAt`,
`measurable_fderiv`, `ContinuousLinearMap.isOpen_injective`).  For injective `L` take `K > 0` with
`|x| ≤ K|Lx|` (`LinearMap.exists_antilipschitzWith`) and `r(L) = K⁻¹/2`; otherwise `r(L) = 1`.
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` gives Borel `Aₗ = S ∩ tₗ` on which
`H` is `r(Tₗ)`-close to `Tₗ = DH(yₗ)`, `yₗ ∈ S`, so
`|H(a) − H(a')| ≥ |Tₗ(a − a')| − r(Tₗ)|a − a'| ≥ r(Tₗ)|a − a'|` and `κₗ = r(Tₗ)`. -/
theorem Submission.dor_lmb_fcd_imp_regular_partition : ∀ (k N' : ℕ) (H : Euclid k → Euclid N') (B : Set (Euclid k)), MeasurableSet B → ∃ (A : ℕ → Set (Euclid k)) (κ : ℕ → ℝ), (∀ l, MeasurableSet (A l)) ∧ (∀ l, A l ⊆ B) ∧ Pairwise (fun l l' => Disjoint (A l) (A l')) ∧ (∀ l, 0 < κ l) ∧ (∀ l, ∀ a ∈ A l, ∀ a' ∈ A l, κ l * ‖a - a'‖ ≤ ‖H a - H a'‖) ∧ (∀ l, ∀ a ∈ A l, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) ∧ ∀ u ∈ B, DifferentiableAt ℝ H u → Injective (fderiv ℝ H u) → ∃ l, u ∈ A l := by
  intro k N' H B hB
  -- the regular set `S = B ∩ {H differentiable, DH injective}` is Borel
  set S : Set (Euclid k) := B ∩ {u | DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u)}
  have hS : MeasurableSet S :=
    hB.inter ((measurableSet_of_differentiableAt ℝ H).inter
      (measurable_fderiv ℝ H ContinuousLinearMap.isOpen_injective.measurableSet))
  -- coercivity radius: `r(L) ≠ 0`, and `2 r(L) |x| ≤ |Lx|` for injective `L`
  have hcoer : ∀ L : Euclid k →L[ℝ] Euclid N', ∃ c : NNReal, c ≠ 0 ∧
      (Injective L → ∀ x, 2 * ((c : ℝ) * ‖x‖) ≤ ‖L x‖) := by
    intro L
    by_cases hL : Injective L
    · obtain ⟨K, hK, hKL⟩ := LinearMap.exists_antilipschitzWith (L : Euclid k →ₗ[ℝ] Euclid N')
        (LinearMap.ker_eq_bot.mpr hL)
      refine ⟨K⁻¹ / 2, div_ne_zero (inv_ne_zero hK.ne') two_ne_zero, fun _ x => ?_⟩
      have hb : ‖x‖ ≤ K * ‖L x‖ := ZeroHomClass.bound_of_antilipschitz L hKL x
      have hK' : (0 : ℝ) < K := hK
      calc 2 * (((K⁻¹ / 2 : NNReal) : ℝ) * ‖x‖) = (K : ℝ)⁻¹ * ‖x‖ := by push_cast; ring
        _ ≤ (K : ℝ)⁻¹ * (K * ‖L x‖) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hK'.le)
        _ = ‖L x‖ := inv_mul_cancel_left₀ hK'.ne' _
    · exact ⟨1, one_ne_zero, fun h => absurd h hL⟩
  choose r rpos hr using hcoer
  -- partition of `S` into Borel pieces on which `H` is `r(Tₗ)`-close to `Tₗ = DH(yₗ)`
  obtain ⟨t, T, htd, htm, hSt, happrox, hrep⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H S (fderiv ℝ H)
      (fun x hx => hx.2.1.hasFDerivAt.hasFDerivWithinAt) r rpos
  refine ⟨fun l => S ∩ t l, fun l => (r (T l) : ℝ), fun l => hS.inter (htm l),
    fun l x hx => hx.1.1, fun l l' hll' => (htd hll').mono inter_subset_right inter_subset_right,
    fun l => NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (rpos (T l))), ?_, fun l x hx => hx.1.2, ?_⟩
  · -- `|H(a) − H(a')| ≥ |Tₗ(a − a')| − r(Tₗ)|a − a'| ≥ r(Tₗ)|a − a'|`, `Tₗ = DH(yₗ)` injective
    intro l a ha a' ha'
    obtain ⟨y, hyS, hy⟩ := hrep ⟨a, ha.1⟩ l
    have hinj : Injective (T l) := by rw [hy]; exact hyS.2.2
    have h2 : ‖H a - H a' - T l (a - a')‖ ≤ r (T l) * ‖a - a'‖ := happrox l a ha a' ha'
    have h3 := hr (T l) hinj (a - a')
    have h4 : ‖T l (a - a')‖ ≤ ‖H a - H a'‖ + ‖H a - H a' - T l (a - a')‖ :=
      calc ‖T l (a - a')‖ = ‖(H a - H a') - (H a - H a' - T l (a - a'))‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    show (r (T l) : ℝ) * ‖a - a'‖ ≤ ‖H a - H a'‖
    linarith
  · -- every regular point of `H` in `B` lies in `S ⊆ ⋃ₗ tₗ`
    intro u hu hdiff hinj
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hSt ⟨hu, hdiff, hinj⟩)
    exact ⟨l, ⟨hu, hdiff, hinj⟩, hl⟩
/-- **Simon Ch. 6, 3.5–3.9 on one bi-Lipschitz piece** (step 7 of the integer multiplicity
push-forward).  Assume (IMC): (a) approximate tangent spaces are local, (b) restricting an
`IMRep` to a Borel set represents a current, (c) differences of integer multiplicity currents are
integer multiplicity, (d) `|⟨α, ξ(x)⟩| ≤ |α|` a.e. on the carrier.  Let `H : ℝᵏ → ℝ^{N'}` be
Lipschitz, `A ⊆ ℝᵏ` Borel with `κ|a − a'| ≤ |H(a) − H(a')|` on `A` (`κ > 0`) and `DH(a)`
injective on `A`, and `g` Borel, integer-valued, nonzero on `A`, with `∫_A |g| J < ∞`, where
`J = √det(⟨DH eₐ, DH e_b⟩)`.  Then `Φ(ω) = ∫_A g ω(H)(DH e₁, …, DH eₖ)` is an integer
multiplicity current with `M(Φ) ≤ ∫_A |g| J`.  With `ψ` a Borel inverse of `H` on `A` and
`η = J⁻¹ DH e₁ ∧ ⋯ ∧ DH eₖ`, `Φ = τ(H(A), |g ∘ ψ|, sign(g ∘ ψ) η ∘ ψ)` by (IMC)(b); the area
formula gives `Hᵏ⌞H(A) = H_#(J Lᵏ⌞A)`, which yields the action, and (IMC)(d) the mass bound. -/
theorem Submission.dor_lmb_fcd_imp_piece_current : ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (k N' : ℕ) (H : Euclid k → Euclid N') (A : Set (Euclid k)) (L : NNReal) (κ : ℝ) (g : Euclid k → ℝ), LipschitzWith L H → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ A, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → (∀ u, ∃ z : ℤ, g u = z) → (∀ u ∈ A, g u ≠ 0) → ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ H u (EuclideanSpace.single b (1 : ℝ)))))) ≠ ∞ → ∃ Φ : GeometricCurrentOn (univ : Set (Euclid N')) k, IsIntegerMultiplicity Φ ∧ Φ.mass ≤ ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ H u (EuclideanSpace.single b (1 : ℝ)))))) ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Φ ω = ∫ u in A, g u * (ω : DifferentialForm (Euclid N') k) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) := by
  intro hIMC k N' H A L κ g hH hA hκ hbi hdiff hg hgZ hg0 hfin
  obtain ⟨-, hIMCb, -, hIMCd⟩ := hIMC
  -- Step 1: `H` is injective on `A`, `N = H(A)` is Borel, and the area formula on `A`
  have hinj : InjOn H A := fun a ha a' ha' h => by
    have hle := hbi a ha a' ha'
    rw [h, sub_self, norm_zero] at hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle hκ))
  have hN : MeasurableSet (H '' A) :=
    hA.image_of_continuousOn_injOn hH.continuous.continuousOn hinj
  have hHm : Measurable H := hH.continuous.measurable
  set J : Euclid k → ℝ := fun u => Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k =>
    inner ℝ (fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ)))
      (fderiv ℝ H u (EuclideanSpace.single b (1 : ℝ)))))
  obtain ⟨hJm, harea⟩ := Submission.codim1_lura_gram_area_formula k N' H
  have hJm' : Measurable J := hJm
  have hareaA : ∀ φ : Euclid N' → ℝ≥0∞,
      ∫⁻ y in H '' A, φ y ∂μHE[k] = ∫⁻ u in A, ENNReal.ofReal (J u) * φ (H u) :=
    harea A hA (fun u hu => (hdiff u hu).1) (fun u hu => (hdiff u hu).2) hinj
  -- Step 2: a Borel left inverse `ψ` of `H` on `A`
  obtain ⟨ψ, hψm, hψ⟩ := (ContinuousOn.measurableEmbedding hA hH.continuous.continuousOn
    hinj).exists_measurable_extend measurable_subtype_coe fun _ => ⟨0⟩
  have hψH : ∀ a ∈ A, ψ (H a) = a := fun a ha => congr_fun hψ ⟨a, ha⟩
  -- Step 3: `η(u) = J(u)⁻¹ DH(u)e₁ ∧ ⋯ ∧ DH(u)eₖ`
  let Ev : (Euclid k →L[ℝ] Euclid N') → MultiVector N' k := fun T =>
    (ContinuousAlternatingMap.apply ℝ (Euclid k) ℝ
      (fun a : Fin k => EuclideanSpace.single a (1 : ℝ))).comp
      (ContinuousAlternatingMap.compContinuousLinearMapCLM T)
  have hEvc : Continuous Ev :=
    continuous_const.clm_comp ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM
  let η : Euclid k → MultiVector N' k := fun u => (J u)⁻¹ • Ev (fderiv ℝ H u)
  have hη : ∀ u α, η u α = (J u)⁻¹ * α (fun a => fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) :=
    fun u α => rfl
  have hηm : StronglyMeasurable η :=
    hJm'.inv.stronglyMeasurable.smul
      (hEvc.comp_stronglyMeasurable (measurable_fderiv ℝ H).stronglyMeasurable)
  -- the frame `DH(a)e` is linearly independent and spans `range DH(a)` for `a ∈ A`
  have hli : ∀ a ∈ A, LinearIndependent ℝ
      (fun i : Fin k => fderiv ℝ H a (EuclideanSpace.single i (1 : ℝ))) := by
    intro a ha
    have := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.linearIndependent.map'
      (fderiv ℝ H a : Euclid k →ₗ[ℝ] Euclid N') (LinearMap.ker_eq_bot.mpr (hdiff a ha).2)
    simpa [Function.comp_def] using this
  have hspan : ∀ a, Submodule.span ℝ
      (Set.range (fun i : Fin k => fderiv ℝ H a (EuclideanSpace.single i (1 : ℝ)))) =
      LinearMap.range (fderiv ℝ H a : Euclid k →ₗ[ℝ] Euclid N') := by
    intro a
    have : (fun i : Fin k => fderiv ℝ H a (EuclideanSpace.single i (1 : ℝ))) =
        (fderiv ℝ H a : Euclid k →ₗ[ℝ] Euclid N') ∘
          (EuclideanSpace.basisFun (Fin k) ℝ).toBasis := by
      funext i; simp
    rw [this, Set.range_comp, Submodule.span_image,
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.span_eq, Submodule.map_top]
  have hJpos : ∀ a ∈ A, 0 < J a := fun a ha =>
    Real.sqrt_pos.2 (Submission.codim1_lur_normalized_wedge_orientation N' k _ (hli a ha)).1
  have hηor : ∀ a ∈ A, IsUnitOrientationOf (η a)
      (LinearMap.range (fderiv ℝ H a : Euclid k →ₗ[ℝ] Euclid N')) := by
    intro a ha
    rw [← hspan a]
    exact (Submission.codim1_lur_normalized_wedge_orientation N' k _ (hli a ha)).2 (η a)
      (fun α => hη a α)
  have hJnn : ∀ u, 0 ≤ J u := fun u => Real.sqrt_nonneg _
  have hfin' : ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (J u) ≠ ∞ := hfin
  -- Step 4: the multiplicity `θ = ⌊|g ∘ ψ|⌋₊`, equal to `|g|` on `A` via `ψ ∘ H = id`
  have hfloor : Measurable (Nat.floor : ℝ → ℕ) :=
    measurable_to_countable fun r => by
      rcases eq_or_ne ⌊r⌋₊ 0 with h | h <;>
        simp [h, Nat.preimage_floor_of_ne_zero, -Nat.floor_eq_zero]
  let mult : Euclid N' → ℕ := fun y => ⌊|g (ψ y)|⌋₊
  have hmultm : Measurable mult := hfloor.comp (continuous_abs.measurable.comp (hg.comp hψm))
  have hmultA : ∀ a ∈ A, ∃ z : ℤ, g a = z ∧ mult (H a) = z.natAbs ∧ |g a| = (z.natAbs : ℝ) := by
    intro a ha
    obtain ⟨z, hz⟩ := hgZ a
    have habs : |g a| = (z.natAbs : ℝ) := by rw [hz, Nat.cast_natAbs, Int.cast_abs]
    refine ⟨z, hz, ?_, habs⟩
    show ⌊|g (ψ (H a))|⌋₊ = z.natAbs
    rw [hψH a ha, habs, Nat.floor_natCast]
  have hmultR : ∀ a ∈ A, ((mult (H a) : ℕ) : ℝ) = |g a| := by
    intro a ha
    obtain ⟨z, -, hm, habs⟩ := hmultA a ha
    rw [habs, hm]
  have hmultE : ∀ a ∈ A, ((mult (H a) : ℕ) : ℝ≥0∞) = ‖g a‖ₑ := by
    intro a ha
    obtain ⟨z, -, hm, habs⟩ := hmultA a ha
    rw [Real.enorm_eq_ofReal_abs, habs, ENNReal.ofReal_natCast, hm]
  have hmultpos : ∀ a ∈ A, 0 < mult (H a) := by
    intro a ha
    obtain ⟨z, hz, hm, -⟩ := hmultA a ha
    rw [hm]
    exact Int.natAbs_pos.2 (by rintro rfl; exact hg0 a ha (by simpa using hz))
  -- `∫_{H(A)} θ dHᵏ = ∫_A |g| J`, and `Hᵏ(H(A)) = ∫_A J ≤ ∫_A |g| J < ∞`
  have hmultint : ∫⁻ y in H '' A, (mult y : ℝ≥0∞) ∂μHE[k] =
      ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (J u) := by
    rw [hareaA]
    refine setLIntegral_congr_fun hA (fun u hu => ?_)
    rw [hmultE u hu, mul_comm]
  have hNfin : μHE[k] (H '' A) ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin' ?_
    rw [← setLIntegral_one, hareaA]
    refine setLIntegral_mono' hA (fun u hu => ?_)
    rw [mul_one]
    calc ENNReal.ofReal (J u) = 1 * ENNReal.ofReal (J u) := (one_mul _).symm
      _ ≤ ‖g u‖ₑ * ENNReal.ofReal (J u) := by
        gcongr
        rw [← hmultE u hu]
        exact_mod_cast hmultpos u hu
  -- Step 5: the orientation `ξ = ±η ∘ ψ` (sign of `g ∘ ψ`)
  let orient : Euclid N' → MultiVector N' k := fun y =>
    (if 0 ≤ g (ψ y) then (1 : ℝ) else -1) • η (ψ y)
  have hsgn : Measurable fun y => if 0 ≤ g (ψ y) then (1 : ℝ) else -1 :=
    Measurable.ite (measurableSet_le measurable_const (hg.comp hψm)) measurable_const
      measurable_const
  have horm : StronglyMeasurable orient :=
    hsgn.stronglyMeasurable.smul (hηm.comp_measurable hψm)
  have horA : ∀ a ∈ A, IsUnitOrientationOf (orient (H a))
      (LinearMap.range (fderiv ℝ H a : Euclid k →ₗ[ℝ] Euclid N')) := by
    intro a ha
    obtain ⟨τ, hτ, hτspan, hτor⟩ := hηor a ha
    show IsUnitOrientationOf ((if 0 ≤ g (ψ (H a)) then (1 : ℝ) else -1) • η (ψ (H a))) _
    rw [hψH a ha]
    split_ifs
    · rw [one_smul]
      exact ⟨τ, hτ, hτspan, hτor⟩
    · refine ⟨τ, hτ, hτspan, hτor.symm.imp (fun h' α => ?_) (fun h' α => ?_)⟩
      · simp [h' α]
      · simp [h' α]
  -- `orients`: `H(A)` has approximate tangent space `range DH(a)` at `H(a)` for a.e. `a ∈ A`,
  -- and `Hᵏ`-null sets of parameters have `Hᵏ`-null images
  have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece N' k univ (H '' A) H A L κ
    isOpen_univ hN (subset_univ _)
    (fun C _ _ => ne_top_of_le_ne_top hNfin (measure_mono inter_subset_left))
    hH hA hκ hbi hdiff subset_rfl
  have hgood : ∀ᵐ b ∂(volume.restrict A), ∃ Q : Submodule ℝ (Euclid N'),
      HasApproximateTangentSpaceAt k (H '' A) (H b) Q ∧ IsUnitOrientationOf (orient (H b)) Q := by
    filter_upwards [htan, ae_restrict_mem hA] with b hb hbA
    exact ⟨_, hb, horA b hbA⟩
  have horients : ∀ᵐ y ∂(μHE[k].restrict (H '' A)), ∃ Q : Submodule ℝ (Euclid N'),
      HasApproximateTangentSpaceAt k (H '' A) y Q ∧ IsUnitOrientationOf (orient y) Q := by
    rw [ae_restrict_iff' hA, ae_iff] at hgood
    rw [ae_restrict_iff' hN, ae_iff]
    refine measure_mono_null (fun y hy => ?_) (le_zero_iff.1
      ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
        hH.lipschitzOnWith).trans
        (by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hgood, mul_zero])))
    obtain ⟨⟨b, hb, rfl⟩, hPy⟩ := not_imp.1 hy
    exact ⟨b, not_imp.2 ⟨hb, hPy⟩, rfl⟩
  -- Step 6: the triple `(H(A), θ, ξ)` is an integer multiplicity representation in `ℝ^{N'}`
  let R : IMRep (univ : Set (Euclid N')) k :=
    { carrier := H '' A
      mult := mult
      orient := orient
      measurableSet_carrier := hN
      carrier_subset := subset_univ _
      rectifiable := ⟨∅, measure_empty, fun _ => H, fun _ => ⟨L, hH⟩,
        fun y hy => Or.inr (mem_iUnion.2 ⟨0, image_subset_range H A hy⟩)⟩
      measurable_mult := hmultm
      mult_pos := by
        rintro _ ⟨a, ha, rfl⟩
        exact hmultpos a ha
      locallyIntegrable_mult := fun K _ _ =>
        ne_top_of_le_ne_top (hmultint ▸ hfin') (lintegral_mono_set inter_subset_left)
      aestronglyMeasurable_orient := horm.aestronglyMeasurable
      orients := horients }
  obtain ⟨Φ, R', hRep, hcar, hmul, hori⟩ :=
    hIMCb N' k univ R univ isOpen_univ MeasurableSet.univ
  have hcar' : R'.carrier = H '' A := by rw [hcar, inter_univ]
  have hΦ : ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Φ ω =
      ∫ y in H '' A, (mult y : ℝ) * orient y ((ω : DifferentialForm (Euclid N') k) y) ∂μHE[k] := by
    intro ω
    rw [hRep ω, IMRep.action, hcar', hmul, hori]
  -- Step 7: `Hᵏ⌞H(A) = H_#(J Lᵏ⌞A)`, hence `∫_{H(A)} h dHᵏ = ∫_A J (h ∘ H)`
  have hmeasEq : μHE[k].restrict (H '' A) =
      Measure.map H ((volume.restrict A).withDensity fun u => ENNReal.ofReal (J u)) := by
    ext S hS
    calc (μHE[k].restrict (H '' A)) S = ∫⁻ y in H '' A, S.indicator 1 y ∂μHE[k] :=
          (lintegral_indicator_one hS).symm
      _ = ∫⁻ u in A, ENNReal.ofReal (J u) * S.indicator 1 (H u) := hareaA _
      _ = ∫⁻ u in A, (H ⁻¹' S).indicator (fun u => ENNReal.ofReal (J u)) u := by
          refine lintegral_congr fun u => ?_
          by_cases hu : H u ∈ S <;> simp [hu]
      _ = _ := by
          rw [lintegral_indicator (hHm hS), Measure.map_apply hHm hS, withDensity_apply _ (hHm hS)]
  have hint : ∀ h : Euclid N' → ℝ, AEStronglyMeasurable h (μHE[k].restrict (H '' A)) →
      ∫ y in H '' A, h y ∂μHE[k] = ∫ u in A, J u * h (H u) := by
    intro h hh
    rw [hmeasEq] at hh ⊢
    rw [integral_map hHm.aemeasurable hh, integral_withDensity_eq_integral_toReal_smul
      hJm'.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hJnn u)]
  -- Step 8: the action `Φ(ω) = ∫_A g ω(H)(DH e)`
  have hval : ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Φ ω = ∫ u in A, g u *
      (ω : DifferentialForm (Euclid N') k) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a (1 : ℝ))) := by
    intro ω
    have hωt : IsTestForm (ω : DifferentialForm (Euclid N') k) := ω.2.1
    have hωc : Continuous (ω : DifferentialForm (Euclid N') k) := ContDiff.continuous hωt.1
    have hcont : Continuous (uncurry fun (ξ : MultiVector N' k) (α : Covector (Euclid N') k) =>
        ξ α) := isBoundedBilinearMap_apply.continuous
    have hm : AEStronglyMeasurable
        (fun y => (mult y : ℝ) * orient y ((ω : DifferentialForm (Euclid N') k) y))
        (μHE[k].restrict (H '' A)) :=
      (measurable_from_nat.comp hmultm).aestronglyMeasurable.mul
        (hcont.comp_aestronglyMeasurable₂ horm.aestronglyMeasurable hωc.aestronglyMeasurable)
    rw [hΦ ω, hint _ hm]
    refine setIntegral_congr_fun hA (fun u hu => ?_)
    have hJu : J u ≠ 0 := (hJpos u hu).ne'
    rw [hmultR u hu]
    show J u * (|g u| * ((if 0 ≤ g (ψ (H u)) then (1 : ℝ) else -1) *
      η (ψ (H u)) ((ω : DifferentialForm (Euclid N') k) (H u)))) = _
    rw [hψH u hu, hη]
    split_ifs with hgu
    · rw [abs_of_nonneg hgu]
      field_simp
    · rw [abs_of_neg (not_le.1 hgu)]
      field_simp
  -- Step 9: the mass bound, from `|ξ(α)| ≤ |α|` a.e. (IMC (d))
  have hbound : ∀ᵐ y ∂(μHE[k].restrict (H '' A)), ∀ α : Covector (Euclid N') k,
      |orient y α| ≤ covectorEuclideanNorm α := by
    have h := hIMCd N' k univ R'
    rw [hcar', hori] at h
    exact h
  have hmass : Φ.mass ≤ ∫⁻ u in A, ‖g u‖ₑ * ENNReal.ofReal (J u) := by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (Φ ω) ≤ _
    rw [hΦ ω, ← hmultint]
    calc ENNReal.ofReal (∫ y in H '' A, (mult y : ℝ) *
          orient y ((ω : DifferentialForm (Euclid N') k) y) ∂μHE[k])
        ≤ ‖∫ y in H '' A, (mult y : ℝ) *
          orient y ((ω : DifferentialForm (Euclid N') k) y) ∂μHE[k]‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ y in H '' A, ‖(mult y : ℝ) *
          orient y ((ω : DifferentialForm (Euclid N') k) y)‖ₑ ∂μHE[k] :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y in H '' A, (mult y : ℝ≥0∞) ∂μHE[k] := by
          refine lintegral_mono_ae (hbound.mono fun y hy => ?_)
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_natCast]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_of_le_one_right (Nat.cast_nonneg _) ((hy _).trans (hω.2 y))
  exact ⟨Φ, ⟨R', hRep⟩, hmass, hval⟩
/-- **First-order calculus of Lipschitz maps on parameter domains** (Simon Ch. 7, deformation step;
Ch. 6, 2.29; Ch. 2, 3.3–3.5).  Write `J_H(u) = √det(⟨DH(u)eₐ, DH(u)e_b⟩)`.
(i) If `F` is `Λ`-Lipschitz and `G` is differentiable at `u`, then `J_{F∘G}(u) ≤ Λᵏ J_G(u)`:
`|D(F∘G)(u)v| ≤ Λ|DG(u)v|` by difference quotients; a non-injective `D(F∘G)(u)` has singular Gram
matrix, and otherwise the area formula for the linear maps `L = D(F∘G)(u)`, `M = DG(u)` on the unit
ball `S` gives `Hᵏ(L S) = J(L)|S|`, `Hᵏ(M S) = J(M)|S|`, while `L = A ∘ M` with `A` `Λ`-Lipschitz on
`M S`, so `Hᵏ(L S) ≤ Λᵏ Hᵏ(M S)`.
(ii) If `H, H'` are Lipschitz and agree a.e. on a Borel set `B`, then `DH = DH'` a.e. on `B`: at a
point `u` of `E = {H = H'}` where `E` has density `1` along the balls `B(y, |y - u|/(n+1))`,
`y → u` (Lebesgue density theorem for the doubling measure `Lᵏ`), every `y` near `u` is within
`|y - u|/(n+1)` of `E`, so `H - H'` has derivative `0` at `u`. -/
theorem Submission.dor_lmb_fcd_imp_lipschitz_jacobian_locality : (∀ (k N N' : ℕ) (F : Euclid N → Euclid N') (G : Euclid k → Euclid N) (Λ : NNReal) (u : Euclid k), LipschitzWith Λ F → DifferentiableAt ℝ G u → Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ (F ∘ G) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (F ∘ G) u (EuclideanSpace.single b (1 : ℝ))))) ≤ (Λ : ℝ) ^ k * Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ G u (EuclideanSpace.single b (1 : ℝ)))))) ∧ ∀ (k N' : ℕ) (H H' : Euclid k → Euclid N') (B : Set (Euclid k)) (L L' : NNReal), LipschitzWith L H → LipschitzWith L' H' → MeasurableSet B → (∀ᵐ u ∂(volume.restrict B), H u = H' u) → ∀ᵐ u ∂(volume.restrict B), fderiv ℝ H u = fderiv ℝ H' u := by
  refine ⟨fun k N N' F G Λ u hF hG => ?_, fun k N' H H' B L L' hH hH' hB hae => ?_⟩
  · -- (i)  `Lm = D(F∘G)(u)`, `Mm = DG(u)`
    set Lm := fderiv ℝ (F ∘ G) u with hLm
    set Mm := fderiv ℝ G u with hMm
    -- `|Lm v| ≤ Λ |Mm v|`, from the difference quotients along `u + v/n`
    have hLM : ∀ v : Euclid k, ‖Lm v‖ ≤ (Λ : ℝ) * ‖Mm v‖ := by
      intro v
      by_cases hFG : DifferentiableAt ℝ (F ∘ G) u
      · have hc : Tendsto (fun n : ℕ => ‖(n : ℝ)‖) atTop atTop := by
          simpa only [Real.norm_natCast] using tendsto_natCast_atTop_atTop
        have h1 := (hFG.hasFDerivAt.lim v hc).norm
        have h2 := ((hG.hasFDerivAt.lim v hc).norm).const_mul (Λ : ℝ)
        refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
        rw [norm_smul, norm_smul, mul_left_comm]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hF.dist_le_mul _ _
      · rw [hLm, fderiv_zero_of_not_differentiableAt hFG, zero_apply, norm_zero]
        positivity
    by_cases hLinj : Injective Lm
    · have hMinj : Injective Mm := by
        intro v w hvw
        apply hLinj
        have h := hLM (v - w)
        simp only [map_sub, hvw, sub_self, norm_zero, mul_zero] at h
        exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
      -- area formula for an injective linear map on the closed unit ball
      have harea : ∀ {P : ℕ} (T : Euclid k →L[ℝ] Euclid P), Injective T →
          μHE[k] (T '' closedBall 0 1) = ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k =>
            inner ℝ (T (EuclideanSpace.single a (1 : ℝ))) (T (EuclideanSpace.single b (1 : ℝ)))))) *
            volume (closedBall (0 : Euclid k) 1) := by
        intro P T hT
        have h := (Submission.codim1_lura_gram_area_formula k P T).2 (closedBall 0 1)
          measurableSet_closedBall (fun x _ => T.differentiableAt)
          (fun x _ => by rw [T.fderiv]; exact hT) hT.injOn (fun _ => 1)
        simpa only [ContinuousLinearMap.fderiv, mul_one, setLIntegral_one, setLIntegral_const] using h
      -- `Lm = A ∘ Mm` with `A = Lm ∘ Linv` `Λ`-Lipschitz on the range of `Mm`
      obtain ⟨Linv, hLinv⟩ := LinearMap.exists_leftInverse_of_injective (Mm : Euclid k →ₗ[ℝ] Euclid N)
        (LinearMap.ker_eq_bot.mpr hMinj)
      have hLx : ∀ x, Linv (Mm x) = x := fun x => by
        simpa using LinearMap.congr_fun hLinv x
      have hA : LipschitzOnWith Λ (fun y => Lm (Linv y)) (Mm '' closedBall 0 1) := by
        refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
        obtain ⟨x, -, rfl⟩ := hy
        obtain ⟨x', -, rfl⟩ := hy'
        simp only [hLx, dist_eq_norm, ← map_sub]
        exact hLM (x - x')
      have himg : (fun y => Lm (Linv y)) '' (Mm '' closedBall 0 1) = Lm '' closedBall 0 1 := by
        rw [image_image]
        simp only [hLx]
      have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hA
      rw [himg, harea Lm hLinj, harea Mm hMinj] at hle
      have hS0 : volume (closedBall (0 : Euclid k) 1) ≠ 0 := (measure_closedBall_pos volume 0 one_pos).ne'
      have hSt : volume (closedBall (0 : Euclid k) 1) ≠ ∞ := measure_closedBall_lt_top.ne
      rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hS0 hSt, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_pow Λ.coe_nonneg, ← ENNReal.ofReal_mul (p := (Λ : ℝ) ^ k) (by positivity)] at hle
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    · -- a non-injective `Lm` has singular Gram matrix
      obtain ⟨v, w, hvw, hne⟩ : ∃ v w, Lm v = Lm w ∧ v ≠ w := by
        simpa [Injective] using hLinj
      have hdet : Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (Lm (EuclideanSpace.single a (1 : ℝ)))
          (Lm (EuclideanSpace.single b (1 : ℝ)))) = 0 := by
        have hx : ∑ b, (v - w).ofLp b • EuclideanSpace.single b (1 : ℝ) = v - w := by
          ext i
          simp [Pi.single_apply]
        rw [← Matrix.exists_mulVec_eq_zero_iff]
        refine ⟨(v - w).ofLp, fun h0 => hne (sub_eq_zero.mp ?_), ?_⟩
        · rw [← hx, h0]
          simp
        · funext a
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
          calc ∑ b, inner ℝ (Lm (EuclideanSpace.single a (1 : ℝ))) (Lm (EuclideanSpace.single b (1 : ℝ))) *
                (v - w).ofLp b
              = inner ℝ (Lm (EuclideanSpace.single a (1 : ℝ)))
                  (Lm (∑ b, (v - w).ofLp b • EuclideanSpace.single b (1 : ℝ))) := by
                rw [map_sum, inner_sum]
                refine Finset.sum_congr rfl fun b _ => ?_
                rw [map_smul, inner_smul_right, mul_comm]
            _ = 0 := by rw [hx, map_sub, hvw, sub_self, inner_zero_right]
      rw [hdet, Real.sqrt_zero]
      positivity
  · -- (ii)  `E = {H = H'}` is closed and contains almost all of `B`
    set E : Set (Euclid k) := {x | H x = H' x} with hE
    have hBE : B ≤ᵐ[volume] E := by
      filter_upwards [(ae_restrict_iff' hB).mp hae] with x hx
      exact fun hxB => hx hxB
    -- density of `E` along the balls `B(y, |y - x|/(n+1))`, `y → x`
    have hdens : ∀ᵐ x ∂(volume.restrict E), ∀ n : ℕ,
        Tendsto (fun y => volume (E ∩ closedBall y (dist y x / ((n : ℝ) + 1))) /
          volume (closedBall y (dist y x / ((n : ℝ) + 1)))) (𝓝[≠] x) (𝓝 1) := by
      rw [ae_all_iff]
      intro n
      filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
        (volume : Measure (Euclid k)) E ((n : ℝ) + 1)] with x hx
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      refine hx id (fun y => dist y x / ((n : ℝ) + 1)) ?_ ?_
      · rw [tendsto_nhdsWithin_iff]
        constructor
        · have h0 : Tendsto (fun y => dist y x / ((n : ℝ) + 1)) (𝓝 x) (𝓝 (dist x x / ((n : ℝ) + 1))) :=
            ((continuous_id.dist continuous_const).div_const _).tendsto x
          rw [dist_self, zero_div] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with y hy
          exact div_pos (dist_pos.mpr (mem_compl_singleton_iff.mp hy)) hn
      · refine Eventually.of_forall fun y => ?_
        rw [mem_closedBall, id, mul_div_cancel₀ _ hn.ne', dist_comm]
    filter_upwards [hae, ae_mono (Measure.restrict_mono_ae hBE) hdens] with u hu hdu
    -- `H - H'` has derivative `0` at `u`
    have hD : HasFDerivAt (fun x => H x - H' x) (0 : Euclid k →L[ℝ] Euclid N') u := by
      refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.mpr fun c hc => ?_)
      obtain ⟨n, hn⟩ := exists_nat_gt (((L : ℝ) + L') / c)
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hev : ∀ᶠ y in 𝓝[≠] u, (E ∩ closedBall y (dist y u / ((n : ℝ) + 1))).Nonempty := by
        filter_upwards [(hdu n).eventually_ne one_ne_zero] with y hy
        refine nonempty_of_measure_ne_zero (μ := volume) fun h0 => hy ?_
        rw [h0, ENNReal.zero_div]
      rw [eventually_nhdsWithin_iff] at hev
      filter_upwards [hev] with y hy
      simp only [hu, sub_self, sub_zero, zero_apply]
      by_cases hyu : y = u
      · subst hyu
        simp [hu]
      obtain ⟨z, hzE, hz⟩ := hy (mem_compl_singleton_iff.mpr hyu)
      rw [mem_closedBall, dist_comm] at hz
      have hzE' : H z = H' z := hzE
      have hcoef : ((L : ℝ) + L') / ((n : ℝ) + 1) ≤ c := by
        rw [div_le_iff₀ hn1]
        rw [div_lt_iff₀ hc] at hn
        nlinarith
      calc ‖H y - H' y‖ = ‖(H y - H z) - (H' y - H' z)‖ := by rw [hzE']; congr 1; abel
        _ ≤ ‖H y - H z‖ + ‖H' y - H' z‖ := norm_sub_le _ _
        _ ≤ L * dist y z + L' * dist y z := by
            rw [← dist_eq_norm, ← dist_eq_norm]
            exact add_le_add (hH.dist_le_mul _ _) (hH'.dist_le_mul _ _)
        _ = (L + L') * dist y z := by ring
        _ ≤ (L + L') * (dist y u / ((n : ℝ) + 1)) := by gcongr
        _ = ((L + L') / ((n : ℝ) + 1)) * dist y u := by ring
        _ ≤ c * ‖y - u‖ := by
            rw [← dist_eq_norm]
            exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
    by_cases hd : DifferentiableAt ℝ H u
    · have h1 := hd.hasFDerivAt.sub hD
      rw [show (H - fun x => H x - H' x) = H' from funext fun x => sub_sub_cancel (H x) (H' x)] at h1
      rw [h1.fderiv, sub_zero]
    · have hd' : ¬DifferentiableAt ℝ H' u := fun hd' => hd (by
        have h1 := hd'.hasFDerivAt.add hD
        rw [show (H' + fun x => H x - H' x) = H from funext fun x => add_sub_cancel (H' x) (H x)] at h1
        exact h1.differentiableAt)
      rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

/-- **Integrality of the parametric image series** (Simon Ch. 6, 3.6–3.9: `f#τ(M, θ, ξ)` is an
integer multiplicity current; step 7 of the selected proof, with the bounds of step 6).  Write
`d = k + 1`, `Hᵢ = F ∘ Gᵢ`, `J_H = √det(⟨DH eₐ, DH e_b⟩)`,
`Tᵢ(ω) = ∫_{Bᵢ} wᵢ ω(Hᵢ)(DHᵢ e₀, …, DHᵢ eₖ)` and `mᵢ = ∫⁻_{Bᵢ} |wᵢ| J_{Gᵢ}`.
* `J_{Hᵢ} ≤ Λᵈ J_{Gᵢ}` on `Bᵢ` (`dor_lmb_fcd_imp_lipschitz_jacobian_locality`), so
  `∫⁻_{Bᵢ} |wᵢ| J_{Hᵢ} ≤ Λᵈ mᵢ < ∞`.
* `dor_lmb_fcd_imp_regular_partition` gives disjoint Borel `Aᵢₗ ⊆ Bᵢ` on which `Hᵢ` is
  bi-Lipschitz below with injective derivative, covering every `u ∈ Bᵢ` where `DHᵢ(u)` exists and
  is injective; `dor_lmb_fcd_imp_piece_current` gives integer multiplicity `Φᵢₗ` with
  `Φᵢₗ(ω) = ∫_{Aᵢₗ} wᵢ ω(Hᵢ)(DHᵢ e)` and `M(Φᵢₗ) ≤ ∫⁻_{Aᵢₗ} |wᵢ| J_{Hᵢ}`.
* On `Bᵢ \ ⋃ₗ Aᵢₗ` either `DHᵢ = 0` or the columns `DHᵢ eₐ` are linearly dependent, so the
  integrand vanishes there; it is integrable on `Bᵢ` (`|ω| ≤ C`, `‖DHᵢ‖ ≤ ΛLᵢ`).  Countable
  additivity gives `∑ₗ Φᵢₗ(ω) = Tᵢ(ω)` and `∑ₗ M(Φᵢₗ) ≤ ∫⁻_{Bᵢ} |wᵢ| J_{Hᵢ} ≤ Λᵈ mᵢ`.
* Enumerating the pairs `(i, l)` by `ℕ`, (IMS) gives an integer multiplicity `Y` with
  `∑ᵢₗ Φᵢₗ(ω) = Y(ω)`; summing fibrewise, `∑ᵢ Tᵢ(ω) = Y(ω)`.
* If `|ω(x)| ≤ c`, then `±c⁻¹ω` is admissible for the mass, so `|Φᵢₗ(ω)| ≤ c M(Φᵢₗ)` and
  `|Tᵢ(ω)| ≤ c ∑ₗ M(Φᵢₗ) ≤ c Λᵈ mᵢ`. -/
theorem Submission.dor_lmb_fcd_imp_image_series_im : (∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (N N' k : ℕ) (G : ℕ → Euclid (k + 1) → Euclid N) (B : ℕ → Set (Euclid (k + 1))) (w : ℕ → Euclid (k + 1) → ℝ) (F : Euclid N → Euclid N') (Λ : NNReal), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) → (∀ i, MeasurableSet (B i)) → (∀ i, ∀ u ∈ B i, DifferentiableAt ℝ (G i) u) → (∀ i, Measurable (w i)) → (∀ i u, ∃ z : ℤ, w i u = z) → (∀ i, ∀ u ∈ B i, w i u ≠ 0) → (∀ i, IntegrableOn (w i) (B i)) → ∑' i, ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ)))))) ≠ ∞ → LipschitzWith Λ F → ∃ Y : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), HasSum (fun i => ∫ u in B i, w i u * (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))) (Y ω)) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)) (c : ℝ), 0 < c → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) x) ≤ c) → ∀ i, |∫ u in B i, w i u * (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))| ≤ c * (Λ : ℝ) ^ (k + 1) * (∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ))))))).toReal := by
  intro hIMS hIMC N N' k G B w F Λ hGlip hBm hGd hwm hwZ hw0 hwi hsum hF
  -- Lipschitz constants `Lᵢ` of `Gᵢ`; `Hᵢ = F ∘ Gᵢ` is `ΛLᵢ`-Lipschitz
  choose L hL using hGlip
  have hHlip : ∀ i, LipschitzWith (Λ * L i) (F ∘ G i) := fun i => hF.comp (hL i)
  have hΛ : (Λ : ℝ≥0∞) ^ (k + 1) ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  -- `mᵢ = ∫⁻_{Bᵢ} |wᵢ| J_{Gᵢ} < ∞`
  have hm : ∀ i, (∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det
      (Matrix.of fun a b : Fin (k + 1) =>
        inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))
          (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ))))))) ≠ ∞ :=
    fun i => ENNReal.ne_top_of_tsum_ne_top hsum i
  -- (1) Jacobian comparison `J_{Hᵢ} ≤ Λᵈ J_{Gᵢ}` on `Bᵢ`: `∫⁻_{Bᵢ} |wᵢ| J_{Hᵢ} ≤ Λᵈ mᵢ`
  have hJ : ∀ i, (∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det
      (Matrix.of fun a b : Fin (k + 1) =>
        inner ℝ (fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))
          (fderiv ℝ (F ∘ G i) u (EuclideanSpace.single b (1 : ℝ))))))) ≤
      (Λ : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det
        (Matrix.of fun a b : Fin (k + 1) =>
          inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ)))))) := by
    intro i
    rw [← lintegral_const_mul' _ _ hΛ]
    refine setLIntegral_mono' (hBm i) fun u hu => ?_
    have h := ENNReal.ofReal_le_ofReal
      ((Submission.dor_lmb_fcd_imp_lipschitz_jacobian_locality).1 (k + 1) N N' F (G i) Λ u hF
        (hGd i u hu))
    rw [ENNReal.ofReal_mul (p := (Λ : ℝ) ^ (k + 1)) (by positivity),
      ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal] at h
    exact (mul_le_mul_of_nonneg_left h zero_le).trans_eq (mul_left_comm _ _ _)
  -- (3) disjoint Borel pieces `Aᵢₗ ⊆ Bᵢ` covering the points of `Bᵢ` where `DHᵢ` is injective
  choose A κ hAm hAB hAd hκ hAbl hAreg hAcov using fun i =>
    Submission.dor_lmb_fcd_imp_regular_partition (k + 1) N' (F ∘ G i) (B i) (hBm i)
  -- (4) the integer multiplicity piece currents `Φᵢₗ`
  choose Φ hΦIM hΦM hΦω using fun i l =>
    Submission.dor_lmb_fcd_imp_piece_current hIMC (k + 1) N' (F ∘ G i) (A i l) (Λ * L i) (κ i l)
      (w i) (hHlip i) (hAm i l) (hκ i l) (hAbl i l) (hAreg i l) (hwm i) (hwZ i)
      (fun u hu => hw0 i u (hAB i l hu))
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top hΛ (hm i))
        ((lintegral_mono_set (hAB i l)).trans (hJ i)))
  -- (7) `∑ₗ M(Φᵢₗ) ≤ ∫⁻_{⋃ₗ Aᵢₗ} |wᵢ| J_{Hᵢ} ≤ Λᵈ mᵢ`
  have hmass : ∀ i, ∑' l, (Φ i l).mass ≤
      (Λ : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det
        (Matrix.of fun a b : Fin (k + 1) =>
          inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ)))))) := by
    intro i
    refine (ENNReal.tsum_le_tsum fun l => hΦM i l).trans ?_
    rw [← lintegral_iUnion (hAm i) (hAd i)]
    exact (lintegral_mono_set (iUnion_subset (hAB i))).trans (hJ i)
  -- linearly independent columns `T e₀, …, T eₖ` force `T` to be injective
  have hcols : ∀ T : Euclid (k + 1) →L[ℝ] Euclid N',
      LinearIndependent ℝ (fun a => T (EuclideanSpace.single a (1 : ℝ))) → Injective T := by
    intro T hli
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hzs : ∑ a, z.ofLp a • EuclideanSpace.single a (1 : ℝ) = z := by
      have h := (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).sum_repr z
      simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at h
      exact h
    have hc : ∀ a, z.ofLp a = 0 := by
      refine Fintype.linearIndependent_iff.mp hli _ ?_
      calc ∑ a, z.ofLp a • T (EuclideanSpace.single a (1 : ℝ))
          = T (∑ a, z.ofLp a • EuclideanSpace.single a (1 : ℝ)) := by
            rw [map_sum]; simp only [map_smul]
        _ = 0 := by rw [hzs, hz]
    rw [← hzs]
    exact Finset.sum_eq_zero fun a _ => by rw [hc a, zero_smul]
  -- (2), (5), (6): `∑ₗ Φᵢₗ(ω) = Tᵢ(ω)`
  have hfib : ∀ i (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)),
      HasSum (fun l => Φ i l ω) (∫ u in B i, w i u * (ω : DifferentialForm (Euclid N') (k + 1))
        ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))) := by
    intro i ω
    have hωc : Continuous (ω : DifferentialForm (Euclid N') (k + 1)) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    -- (2) the integrand is Borel and bounded by `C (ΛLᵢ)ᵈ |wᵢ|`, hence integrable on `Bᵢ`
    have hcont : Continuous fun p : Euclid N' × (Euclid (k + 1) →L[ℝ] Euclid N') =>
        (ω : DifferentialForm (Euclid N') (k + 1)) p.1
          (fun a => p.2 (EuclideanSpace.single a (1 : ℝ))) :=
      (hωc.comp continuous_fst).eval
        (continuous_pi fun a => continuous_snd.clm_apply continuous_const)
    have hmeas : AEStronglyMeasurable (fun u => (ω : DifferentialForm (Euclid N') (k + 1))
        ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))))
        (volume.restrict (B i)) :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (y : Euclid N') (T : Euclid (k + 1) →L[ℝ] Euclid N') =>
          (ω : DifferentialForm (Euclid N') (k + 1)) y
            (fun a => T (EuclideanSpace.single a (1 : ℝ))))
        hcont (hHlip i).continuous.aestronglyMeasurable
        (measurable_fderiv ℝ (F ∘ G i)).aestronglyMeasurable
    have hbd : ∀ u, ‖(ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)
        (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))‖ ≤
        C * ((Λ * L i : NNReal) : ℝ) ^ (k + 1) := by
      intro u
      have hcol : ∀ a : Fin (k + 1),
          ‖fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))‖ ≤ ((Λ * L i : NNReal) : ℝ) := by
        intro a
        calc ‖fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))‖
            ≤ ‖fderiv ℝ (F ∘ G i) u‖ * ‖EuclideanSpace.single a (1 : ℝ)‖ :=
              (fderiv ℝ (F ∘ G i) u).le_opNorm _
          _ = ‖fderiv ℝ (F ∘ G i) u‖ := by simp
          _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ (hHlip i)
      have hprod : ∏ a : Fin (k + 1), ‖fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))‖ ≤
          ((Λ * L i : NNReal) : ℝ) ^ (k + 1) := by
        calc ∏ a : Fin (k + 1), ‖fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))‖
            ≤ ∏ _a : Fin (k + 1), ((Λ * L i : NNReal) : ℝ) :=
              Finset.prod_le_prod₀ (fun a _ => norm_nonneg _) fun a _ => hcol a
          _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (((ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)).le_opNorm _).trans
        (mul_le_mul (hC _) hprod (Finset.prod_nonneg fun a _ => norm_nonneg _)
          ((norm_nonneg _).trans (hC 0)))
    have hint : IntegrableOn (fun u => w i u * (ω : DifferentialForm (Euclid N') (k + 1))
        ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))) (B i) := by
      refine Integrable.mono' ((hwi i).norm.mul_const (C * ((Λ * L i : NNReal) : ℝ) ^ (k + 1)))
        ((hwm i).aestronglyMeasurable.mul hmeas) (ae_of_all _ fun u => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd u) (norm_nonneg _)
    -- (5) the integrand vanishes on `Bᵢ \ ⋃ₗ Aᵢₗ`, where `DHᵢ = 0` or `DHᵢ` is not injective
    have hvan : ∀ u ∈ B i \ ⋃ l, A i l, w i u * (ω : DifferentialForm (Euclid N') (k + 1))
        ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))) = 0 := by
      rintro u ⟨huB, huA⟩
      rw [mem_iUnion, not_exists] at huA
      suffices h : (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)
          (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))) = 0 by
        rw [h, mul_zero]
      by_cases hd : DifferentiableAt ℝ (F ∘ G i) u
      · by_cases hinj : Injective (fderiv ℝ (F ∘ G i) u)
        · obtain ⟨l, hl⟩ := hAcov i u huB hd hinj
          exact absurd hl (huA l)
        · -- the columns `DHᵢ(u) eₐ` are linearly dependent
          exact ((ω : DifferentialForm (Euclid N') (k + 1))
            ((F ∘ G i) u)).toAlternatingMap.map_linearDependent _ fun hli => hinj (hcols _ hli)
      · rw [fderiv_zero_of_not_differentiableAt hd]
        exact ((ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)).map_zero
    -- (6) `Tᵢ(ω) = ∫_{⋃ₗ Aᵢₗ} = ∑ₗ ∫_{Aᵢₗ} = ∑ₗ Φᵢₗ(ω)`
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hBm i) (iUnion_subset (hAB i)) hvan]
    have hfun : (fun l => Φ i l ω) = fun l => ∫ u in A i l, w i u *
        (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)
          (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ))) :=
      funext fun l => hΦω i l ω
    rw [hfun]
    exact hasSum_integral_iUnion (hAm i) (hAd i) (hint.mono_set (iUnion_subset (hAB i)))
  -- (8) enumerate the pieces by `ℕ`: `Xᵣ = Φ_{π(r)}`; (IMS) gives the integer multiplicity `Y`
  let π : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let X : ℕ → GeometricCurrentOn (univ : Set (Euclid N')) (k + 1) := fun r => Φ (π r).1 (π r).2
  have hXmass : ∑' r, (X r).mass ≠ ∞ := by
    have h : ∑' r, (X r).mass = ∑' i, ∑' l, (Φ i l).mass :=
      (Equiv.tsum_eq π fun p : ℕ × ℕ => (Φ p.1 p.2).mass).trans
        (ENNReal.tsum_prod (f := fun i l => (Φ i l).mass))
    rw [h]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hΛ hsum) ?_
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hmass
  obtain ⟨Y, hYIM, hYsum, -⟩ :=
    hIMS N' k univ X isOpen_univ (fun r => hΦIM (π r).1 (π r).2) hXmass
  refine ⟨Y, hYIM, fun ω => ?_, fun ω c hc hωc i => ?_⟩
  · -- (9) `HasSum ((i, l) ↦ Φᵢₗ(ω)) (Y ω)`, summed fibrewise over `l`
    have h : HasSum ((fun p : ℕ × ℕ => Φ p.1 p.2 ω) ∘ π) (Y ω) := hYsum ω
    exact ((Equiv.hasSum_iff π).mp h).prod_fiberwise fun i => hfib i ω
  · -- (10) `±Tᵢ(ω) = ∑ₗ ±Φᵢₗ(ω) ≤ c ∑ₗ M(Φᵢₗ) ≤ c Λᵈ mᵢ`
    have hc0 : c ≠ 0 := hc.ne'
    have hsmul : ∀ (s : ℝ) (α : Covector (Euclid N') (k + 1)),
        covectorEuclideanNorm (s • α) = |s| * covectorEuclideanNorm α := by
      intro s α
      unfold covectorEuclideanNorm
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg s), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    -- `|Z(ω)| ≤ c M(Z)`: `±c⁻¹ω` is admissible for `M(Z) = M_{ℝ^{N'}}(Z)`
    have hZω : ∀ Z : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1), Z.mass ≠ ∞ →
        |Z ω| ≤ c * Z.mass.toReal := by
      intro Z hZ
      have hadm : ∀ s : ℝ, |s| = c⁻¹ → s * Z ω ≤ Z.mass.toReal := by
        intro s hs
        have hmem : s • ω ∈ massAdmissibleOn (univ : Set (Euclid N')) (k + 1) univ := by
          rw [massAdmissibleOn, mem_ofPred_eq]
          refine ⟨subset_univ _, fun x => ?_⟩
          rw [Submodule.coe_smul, Pi.smul_apply, hsmul, hs]
          calc c⁻¹ * covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) x)
              ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (hωc x) (inv_nonneg.mpr hc.le)
            _ = 1 := inv_mul_cancel₀ hc0
        have h := Z.le_massOn hmem
        rw [map_smul, smul_eq_mul] at h
        exact (ENNReal.ofReal_le_iff_le_toReal hZ).mp h
      have h1 := mul_le_mul_of_nonneg_left (hadm c⁻¹ (abs_of_pos (inv_pos.mpr hc))) hc.le
      have h2 := mul_le_mul_of_nonneg_left
        (hadm (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc)])) hc.le
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h1
      rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h2
      rw [abs_le]
      constructor <;> linarith
    have hfinsum : ∑' l, (Φ i l).mass ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top hΛ (hm i)) (hmass i)
    have hfin : ∀ l, (Φ i l).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hfinsum
    have hS : HasSum (fun l => c * ((Φ i l).mass).toReal) (c * (∑' l, (Φ i l).mass).toReal) := by
      rw [ENNReal.tsum_toReal_eq hfin]
      exact (ENNReal.summable_toReal hfinsum).hasSum.mul_left c
    have hup := hasSum_le (fun l => (le_abs_self _).trans (hZω _ (hfin l))) (hfib i ω) hS
    have hlo := hasSum_le (fun l => (neg_le_abs _).trans (hZω _ (hfin l))) (hfib i ω).neg hS
    have hfinal := mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (ENNReal.mul_ne_top hΛ (hm i)) (hmass i)) hc.le
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← mul_assoc] at hfinal
    rw [abs_le]
    constructor <;> linarith
/-- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
`n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
formula, and the Leibniz formula with `|x(l)| ≤ ‖x‖` gives `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`, so
`θ⁰` is continuous. -/
theorem Submission.cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
  intro P n I
  -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => x (I k)
      map_add' := fun x y => by
        funext k
        simp
      map_smul' := fun c x => by
        funext k
        simp }
  -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
  let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
  have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  -- Step 4: the Leibniz formula, `|sign σ| = 1` and `|x(l)| ≤ ‖x‖` give
  -- `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`
  have hbound : ∀ v : Fin n → Euclid P, ‖θ₀ v‖ ≤ (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
    intro v
    rw [hθ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, ‖v j‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| =
              ∏ j, |v j (I (σ j))| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [hσ]
          gcongr with j
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (v j) (I (σ j))
      _ = (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  -- Step 5: `θ = θ⁰.mkContinuous n!` is an `n`-covector with the same values as `θ⁰`
  exact ⟨θ₀.mkContinuous (n.factorial : ℝ) hbound, hθ₀⟩
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]
/-- **Coordinate expansion of a `k`-covector** (the pointwise identity behind
`H^#ω(u)(e) = Σ_I ω_I(H(u)) det D(H^I)(u)`): for `f ∈ Λᵏ(ℝ^{N'})` and `u ∈ (ℝ^{N'})ᵏ`,
`k! f(u) = Σ_I f(e'_{I 0}, …, e'_{I (k-1)}) det (u_b (I c))_{c,b}`, the sum over all maps
`I : Fin k → Fin N'`.  Expand each `u_b = Σ_i u_b(i) e'_i` and use multilinearity; for each
permutation `σ` reindex `J = I ∘ σ` and use `f (v ∘ σ) = sign σ • f v`; average over the `k!`
permutations and recognize the Leibniz formula for the determinant. -/
theorem Submission.dor_lmb_fcd_jwc_covector_det_expansion : ∀ (N' k : ℕ) (f : Covector (Euclid N') k) (u : Fin k → Euclid N'), (k.factorial : ℝ) * f u = ∑ I : Fin k → Fin N', f (fun c => EuclideanSpace.single (I c) (1 : ℝ)) * Matrix.det (Matrix.of fun c b => u b (I c)) := by
  intro N' k f u
  set e : Fin N' → Euclid N' := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- step 1: multilinear expansion in the standard basis
  have h1 : f u = ∑ J : Fin k → Fin N', (∏ b, u b (J b)) * f (fun b => e (J b)) := by
    have hu : u = fun b => ∑ i, u b i • e i := by
      funext b
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N') ℝ).sum_repr (u b)]
      simp [he]
    conv_lhs => rw [hu]
    rw [show f (fun b => ∑ i, u b i • e i) = f.toMultilinearMap (fun b => ∑ i, u b i • e i) from rfl,
      MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp [smul_eq_mul]
  -- step 2: reindex by a permutation `σ`, using alternation
  have h2 : ∀ σ : Equiv.Perm (Fin k), f u = ∑ I : Fin k → Fin N',
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) := by
    intro σ
    rw [h1]
    rw [← Equiv.sum_comp ((σ.symm).arrowCongr (Equiv.refl (Fin N')))]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hperm : f (fun b => e (I (σ b))) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * f (fun c => e (I c)) := by
      have := f.toAlternatingMap.map_perm (fun c => e (I c)) σ
      simp only [Function.comp_def] at this
      rw [show f (fun b => e (I (σ b))) = f.toAlternatingMap (fun b => e (I (σ b))) from rfl, this,
        Units.smul_def, zsmul_eq_mul]
      rfl
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm, Function.comp_apply]
    rw [hperm]
    ring
  -- step 3: average over `σ` and recognize the Leibniz formula
  have h3 : (k.factorial : ℝ) * f u = ∑ σ : Equiv.Perm (Fin k), f u := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [h3]
  calc ∑ σ : Equiv.Perm (Fin k), f u
      = ∑ σ : Equiv.Perm (Fin k), ∑ I : Fin k → Fin N',
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_congr rfl fun σ _ => h2 σ
    _ = ∑ I : Fin k → Fin N', ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_comm
    _ = _ := ?_
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp only [Matrix.of_apply, he]
  ring
/-- **Jacobian minors of Lipschitz maps are measurable and bounded** (the integrands in the weak
continuity of Jacobian minors): if `g₀, …, g_{r-1}` are `L`-Lipschitz on `ℝᵏ` and
`V₀, …, V_{r-1} ∈ ℝᵏ`, then `D(x) = det (Dg_c(x) V_b)_{c,b}` is measurable and
`|D(x)| ≤ r! (L ∑_b ‖V_b‖)ʳ` for every `x`, where `Dg(x) = fderiv ℝ g x` (`0` where `g` is not
differentiable).  Each entry `x ↦ Dg_c(x) V_b` is measurable (`measurable_fderiv_apply_const`)
and bounded by `‖Dg_c(x)‖ ‖V_b‖ ≤ L ‖V_b‖ ≤ L ∑_b ‖V_b‖` (`norm_fderiv_le_of_lipschitz`); by the
Leibniz formula `D` is a signed sum of `r!` products of `r` entries, which gives both claims.
(`Matrix.det_le` is outside the import closure, so the bound is done by hand.) -/
theorem Submission.dor_lmb_fcd_jwc_minor_measurable_bound : ∀ (k r : ℕ) (L : NNReal) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k), (∀ c, LipschitzWith L (g c)) → Measurable (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))) ∧ ∀ x, |Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))| ≤ (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r := by
  intro k r L g V hg
  -- Leibniz formula: `D(x) = ∑_σ sign σ ∏_b Dg_{σ b}(x) V_b`
  have hdet : ∀ x, Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b) :=
    fun x => Matrix.det_apply' _
  refine ⟨?_, fun x => ?_⟩
  · -- steps 1–2: the entries are measurable, hence so is the signed sum of their products
    have hm : Measurable fun x => ∑ σ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b) :=
      Finset.measurable_sum _ fun σ _ => measurable_const.mul
        (Finset.measurable_prod _ fun b _ => measurable_fderiv_apply_const ℝ (g (σ b)) (V b))
    simpa only [hdet] using hm
  · -- step 3: every entry is bounded by `s = L ∑_b ‖V_b‖`
    have hent : ∀ c b, |fderiv ℝ (g c) x (V b)| ≤ (L : ℝ) * ∑ b, ‖V b‖ := by
      intro c b
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (g c) x (V b)‖ ≤ ‖fderiv ℝ (g c) x‖ * ‖V b‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖V b‖ :=
            mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hg c)) (norm_nonneg _)
        _ ≤ L * ∑ b, ‖V b‖ := by
            gcongr
            exact Finset.single_le_sum (f := fun b => ‖V b‖) (fun b _ => norm_nonneg _)
              (Finset.mem_univ b)
    -- step 4: the triangle inequality and `|sign σ| = 1` give `|D(x)| ≤ ∑_σ sʳ = r! sʳ`
    rw [hdet]
    calc |∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b)|
        ≤ ∑ σ : Equiv.Perm (Fin r),
            |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm (Fin r), ∏ b, |fderiv ℝ (g (σ b)) x (V b)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [abs_mul, Finset.abs_prod]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), ∏ _b : Fin r, (L : ℝ) * ∑ b, ‖V b‖ := by
          gcongr with σ _ b _
          exact hent (σ b) b
      _ = (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r := by
          rw [Finset.sum_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- **Derivative of the mollification of a Lipschitz function**: for an `L`-Lipschitz `f` and a
`C¹` kernel `ρ` with compact support, `D(ρ ⋆ f)(x) v = ∫ ρ(t) Df(x − t) v dt`.  Differentiating
under the integral (`HasCompactSupport.hasFDerivAt_convolution_left`) gives
`D(ρ ⋆ f)(x) v = ∫ Dρ(t) v · f(x − t) dt`.  With `t = x − s` and the reflected kernel
`h(s) = ρ(x − s)` (`C¹` with compact support, hence Lipschitz, and `∂_{−v} h(s) = Dρ(x − s) v`)
the two sides become `∫ ∂_{−v} h · f` and `∫ h · Df(·) v`; they agree by integration by parts for
Lipschitz functions (`LipschitzWith.integral_lineDeriv_mul_eq`: `∫ ∂_v f · h = ∫ ∂_{−v} h · f`)
and Rademacher (`∂_v f = Df · v` a.e.). -/
theorem Submission.dor_lmb_fcd_jwc_mollify_fderiv_eq : ∀ (k : ℕ) (L : NNReal) (f ρ : Euclid k → ℝ), LipschitzWith L f → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x v : Euclid k, fderiv ℝ (fun y => ∫ t, ρ t * f (y - t)) x v = ∫ t, ρ t * fderiv ℝ f (x - t) v := by
  intro k L f ρ hf hρ hρs x v
  have hconv : (fun y => ∫ t, ρ t * f (y - t)) =
      convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y; simp [convolution_def]
  have hD := hρs.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    hf.continuous.locallyIntegrable x
  have hint := (hρs.fderiv (𝕜 := ℝ)).convolutionExists_left (μ := (volume : Measure (Euclid k)))
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euclid k)) (hρ.continuous_fderiv (by norm_num))
    (hf.continuous.locallyIntegrable (μ := (volume : Measure (Euclid k)))) x
  rw [hconv, hD.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- change of variables `t ↦ x - t` on both sides
  rw [← integral_sub_left_eq_self (fun t => fderiv ℝ ρ t v * f (x - t)) (μ := volume) x,
    ← integral_sub_left_eq_self (fun t => ρ t * fderiv ℝ f (x - t) v) (μ := volume) x]
  simp only [sub_sub_cancel]
  -- integration by parts against `h(s) = ρ(x - s)`
  set h : Euclid k → ℝ := fun s => ρ (x - s) with hh
  have hhC1 : ContDiff ℝ 1 h := hρ.comp (contDiff_const.sub contDiff_id)
  have hhs : HasCompactSupport h := hρs.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hhL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hhs hhC1 (by norm_num)
  have hibp := hf.integral_lineDeriv_mul_eq (μ := volume) hhL hhs v
  have hlh : ∀ s, lineDeriv ℝ h s (-v) = fderiv ℝ ρ (x - s) v := by
    intro s
    rw [(hhC1.differentiable (by norm_num) s).lineDeriv_eq_fderiv]
    have h1 : HasFDerivAt h (-(fderiv ℝ ρ (x - s))) s := by
      have := (hρ.differentiable (by norm_num) (x - s)).hasFDerivAt.comp s
        ((hasFDerivAt_const x s).sub (hasFDerivAt_id s))
      simpa [hh, Function.comp_def] using this
    rw [h1.fderiv]
    simp
  -- Rademacher: `∂_v f = Df · v` almost everywhere
  have hlf : ∀ᵐ s ∂(volume : Measure (Euclid k)), lineDeriv ℝ f s v = fderiv ℝ f s v := by
    filter_upwards [hf.ae_differentiableAt] with s hs
    exact hs.lineDeriv_eq_fderiv
  simp only [hlh] at hibp
  rw [← hibp]
  refine integral_congr_ae ?_
  filter_upwards [hlf] with s hs
  rw [hs, hh]
  ring
/-- **Smooth approximation of a Lipschitz function** (step 4 of the weak continuity of Jacobians):
an `L`-Lipschitz `f : ℝᵏ → ℝ` is the uniform limit of `C^∞`, `L`-Lipschitz functions `f_n` with
`Df_n(x) → Df(x)` in operator norm for a.e. `x`.  Take `f_n = ρ_n ⋆ f`, where `ρ_n = φ_n / ∫ φ_n`
normalizes a bump `φ_n` equal to `1` on `B(0, 1/(n+2))` and supported in `B(0, 2/(n+2))`.  Then
`f_n` is smooth, `L`-Lipschitz (`cmcs_ls_mollify_lipschitz`) and `|f_n - f| ≤ 2L/(n+2)`.  By
`dor_lmb_fcd_jwc_mollify_fderiv_eq`, `Df_n(x) eᵢ = (ρ_n ⋆ Df(·) eᵢ)(x)`; as `∫ φ_n ≥ |B(0, 1/(n+2))|`
gives `0 ≤ ρ_n ≤ 2ᵈ / |B(0, 2/(n+2))|`, this tends to `Df(x) eᵢ` at every Lebesgue point of the
bounded function `Df(·) eᵢ`, and `‖T‖ ≤ ∑ᵢ |T eᵢ|` gives convergence in operator norm. -/
theorem Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  intro k L f hf
  -- step 1: bumps `φ n` with `rIn = 1/(n+2)`, `rOut = 2/(n+2)`, normalized to `ρ n = φ n / ∫ φ n`
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : Euclid k) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by have := hpos n; positivity,
      div_lt_div_of_pos_right (by norm_num) (hpos n)⟩
  have hrOut : ∀ n, (φ n).rOut = 2 * (φ n).rIn := fun n => by
    show 2 / ((n : ℝ) + 2) = 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div]
  -- `|B(x, r)| = r ^ d * c` with `c = |B(0, 1)| > 0`
  set d := Module.finrank ℝ (Euclid k)
  set c := (volume : Measure (Euclid k)).real (closedBall 0 1)
  have hcpos : 0 < c := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
    measure_closedBall_lt_top.ne
  have hvol : ∀ (x : Euclid k) (r : ℝ), 0 ≤ r →
      (volume : Measure (Euclid k)).real (closedBall x r) = r ^ d * c :=
    fun x r hr => Measure.addHaar_real_closedBall' _ x hr
  -- `φ n = 1` on `B(0, rIn)` and `φ n ≥ 0`, so `∫ φ n ≥ |B(0, rIn)| = rIn ^ d * c > 0`
  have hφint : ∀ n, Integrable (φ n) (volume : Measure (Euclid k)) := fun n =>
    (φ n).continuous.integrable_of_hasCompactSupport (φ n).hasCompactSupport
  have hIge : ∀ n, (φ n).rIn ^ d * c ≤ ∫ x, φ n x := by
    intro n
    rw [← hvol 0 _ (φ n).rIn_pos.le]
    calc (volume : Measure (Euclid k)).real (closedBall 0 (φ n).rIn)
        = ∫ x in closedBall (0 : Euclid k) (φ n).rIn, φ n x := by
          rw [setIntegral_congr_fun measurableSet_closedBall
            (fun x hx => (φ n).one_of_mem_closedBall hx), setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ ∫ x, φ n x :=
          setIntegral_le_integral (hφint n) (Eventually.of_forall fun x => (φ n).nonneg)
  have hIpos : ∀ n, 0 < ∫ x, φ n x := fun n =>
    (mul_pos (pow_pos (φ n).rIn_pos d) hcpos).trans_le (hIge n)
  set ρ : ℕ → Euclid k → ℝ := fun n x => φ n x / ∫ y, φ n y with hρ
  have hρc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρc1 : ∀ n, ContDiff ℝ 1 (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (φ n).continuous.div_const _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    (φ n).hasCompactSupport.comp_left (g := fun t : ℝ => t / ∫ y, φ n y) (zero_div _)
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n x => div_nonneg (φ n).nonneg (hIpos n).le
  have hρint : ∀ n, ∫ x, ρ n x = 1 := fun n => by
    show ∫ x, φ n x / ∫ y, φ n y = 1
    rw [integral_div, div_self (hIpos n).ne']
  have hρsupp : ∀ n, support (ρ n) ⊆ ball 0 (φ n).rOut := fun n x hx => by
    rw [← (φ n).support_eq, mem_support]
    intro h0
    exact (mem_support.1 hx) (by simp [hρ, h0])
  have hρle : ∀ n x, ρ n x ≤ 1 / ((φ n).rIn ^ d * c) := fun n x =>
    calc ρ n x = φ n x / ∫ y, φ n y := rfl
      _ ≤ 1 / ∫ y, φ n y := div_le_div_of_nonneg_right (φ n).le_one (hIpos n).le
      _ ≤ 1 / ((φ n).rIn ^ d * c) :=
          one_div_le_one_div_of_le (mul_pos (pow_pos (φ n).rIn_pos d) hcpos) (hIge n)
  -- `f_n = ρ n ⋆ f`
  set fs : ℕ → Euclid k → ℝ := fun n x => ∫ t, ρ n t * f (x - t) with hfs
  have hconv : ∀ n, fs n = convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro n; funext x; simp [hfs, convolution_def]
  have hrOut0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [φ] using this
  refine ⟨fs, fun n => ?_, fun n => ?_, ?_, ?_⟩
  · -- step 2: `ρ n ⋆ f` is smooth
    rw [hconv]
    exact (hρs n).contDiff_convolution_left _ (hρc n) hf.continuous.locallyIntegrable
  · -- step 3: `ρ n ⋆ f` is `L`-Lipschitz
    exact Submission.cmcs_ls_mollify_lipschitz k (ρ n) f L (hρcont n) (hρs n) (hρ0 n) (hρint n) hf
  · -- step 4: `|f_n x - f x| ≤ L * rOut` for all `x`, and `rOut → 0`
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(hrOut0.const_mul (L : ℝ)).eventually (gt_mem_nhds (by simpa using hε))]
      with n hn x
    have hdist := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := f x) (g := f)
      (by positivity : (0 : ℝ) ≤ L * (φ n).rOut) (hρsupp n) (hρ0 n) (hρint n)
      hf.continuous.aestronglyMeasurable (fun y hy => by
        calc dist (f y) (f x) ≤ L * dist y x := hf.dist_le_mul y x
          _ ≤ L * (φ n).rOut := by gcongr; exact (mem_ball.1 hy).le)
    rw [← hconv] at hdist
    rw [dist_comm]
    exact lt_of_le_of_lt hdist hn
  · -- step 5: `Df_n(x) v = ∫ ρ n t * Df(x - t) v dt`
    have hB1 : ∀ n x v, fderiv ℝ (fs n) x v = ∫ t, ρ n t * fderiv ℝ f (x - t) v := fun n x v =>
      Submission.dor_lmb_fcd_jwc_mollify_fderiv_eq k L f (ρ n) hf (hρc1 n) (hρs n) x v
    have hδ : Tendsto (fun n => (φ n).rOut) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hrOut0, Eventually.of_forall fun n => (φ n).rOut_pos⟩
    -- steps 6-7: for each basis vector `e_i`, `Df_n(x) e_i → Df(x) e_i` for a.e. `x`
    have hDi : ∀ i : Fin k, ∀ᵐ x ∂(volume : Measure (Euclid k)),
        Tendsto (fun n => fderiv ℝ (fs n) x (EuclideanSpace.single i (1 : ℝ))) atTop
          (𝓝 (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) := by
      intro i
      set g : Euclid k → ℝ := fun s => fderiv ℝ f s (EuclideanSpace.single i (1 : ℝ)) with hg
      have hloc : LocallyIntegrable g (volume : Measure (Euclid k)) := by
        refine (locallyIntegrable_const ((L : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)).mono
          ((measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs (_ * _), abs_of_nonneg (by positivity)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      -- Lebesgue differentiation: `⨍_{B(x, r)} |g - g x| → 0` as `r → 0`, for a.e. `x`
      filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1]
        with x hx
      have havg := hx (fun _ => x) (fun n => (φ n).rOut) hδ
        (Eventually.of_forall fun n => mem_closedBall_self (by simpa using (φ n).rOut_pos.le))
      -- `0 ≤ ρ n (x - ·) ≤ 2 ^ d / |B(x, rOut)|`, supported in `B(x, rOut)`, with integral `1`
      have key := tendsto_integral_smul_of_tendsto_average_norm_sub ((2 : ℝ) ^ d) havg
        (g := fun n y => ρ n (x - y))
        (Eventually.of_forall fun n => hloc.integrableOn_isCompact (isCompact_closedBall _ _))
        (tendsto_const_nhds.congr fun n => by
          rw [integral_sub_left_eq_self (ρ n) volume x, hρint n])
        (Eventually.of_forall fun n y hy => by
          have hy' : x - y ∈ ball (0 : Euclid k) (φ n).rOut := hρsupp n hy
          rw [mem_ball, dist_zero_right] at hy'
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact hy'.le)
        (Eventually.of_forall fun n y => by
          rw [abs_of_nonneg (hρ0 n _), hvol x _ (φ n).rOut_pos.le, hrOut n]
          calc ρ n (x - y) ≤ 1 / ((φ n).rIn ^ d * c) := hρle n _
            _ = 2 ^ d / ((2 * (φ n).rIn) ^ d * c) := by
              rw [mul_pow]
              field_simp)
      refine key.congr fun n => ?_
      rw [hB1, ← integral_sub_left_eq_self (fun y => ρ n (x - y) • g y) volume x]
      simp only [sub_sub_cancel, smul_eq_mul, hg]
    filter_upwards [ae_all_iff.2 hDi] with x hx
    -- step 8: `‖T‖ ≤ ∑ᵢ |T eᵢ|`, so convergence on the basis gives convergence in norm
    have hbound : ∀ T : Euclid k →L[ℝ] ℝ, ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound T (Finset.sum_nonneg fun i _ => norm_nonneg _)
        fun w => ?_
      have hw : w = ∑ i, w i • EuclideanSpace.single i (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w]
        simp
      calc ‖T w‖ = ‖∑ i, w i • T (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hw]
            simp [map_sum, map_smul]
        _ ≤ ∑ i, ‖w i • T (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
        _ = ∑ i, ‖w i‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by simp
        _ ≤ ∑ i, ‖w‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
            gcongr with i
            exact PiLp.norm_apply_le w i
        _ = (∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖) * ‖w‖ := by
            rw [Finset.sum_mul]; simp [mul_comm]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hbound _) ?_
    have : Tendsto (fun n => ∑ i : Fin k, ‖(fderiv ℝ (fs n) x - fderiv ℝ f x)
        (EuclideanSpace.single i (1 : ℝ))‖) atTop (𝓝 (∑ i : Fin k, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hx i)
      simpa using this
    simpa using this
/-- **The Piola identity** (the Jacobian minors are null Lagrangians): for `C²` functions
`g₀, …, g_{r-1}` on `ℝᵏ` and directions `V₀, …, V_r`, the minors
`M_b(y) = det (Dg_c(y) V_{s_b(b')})_{c,b'}` (`s_b = Fin.succAbove b`, so `V_b` is deleted) satisfy
`∑_b (-1)^b DM_b(x) V_b = 0`.  With `G = (g₀, …, g_{r-1})` and the constant determinant form
`θ = dy⁰ ∧ ⋯ ∧ dy^{r-1}` one has `M_b(y) = (G^*θ)(y)(V ∘ s_b)`, so the left side is
`d(G^*θ)(x)(V)`, and `d(G^*θ) = G^*(dθ) = 0` by the naturality of `d` (which is where the symmetry
of `D²G` enters). -/
theorem Submission.dor_lmb_fcd_jwc_piola_identity : ∀ (k r : ℕ) (g : Fin r → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (x : Euclid k), (∀ c, ContDiff ℝ 2 (g c)) → ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c) y (V (b.succAbove b')))) x (V b) = 0 := by
  intro k r g V x hg
  -- Step 1: the map `G = (g₀, …, g_{r-1}) : ℝᵏ → ℝʳ` is `C²`, and `(DG(y) w)_c = Dg_c(y) w`
  set e : (Fin r → ℝ) ≃L[ℝ] Euclid r := (EuclideanSpace.equiv (Fin r) ℝ).symm with he
  set G : Euclid k → Euclid r := fun y => e (fun c => g c y) with hG
  have hGc : ContDiff ℝ 2 G := e.contDiff.comp (contDiff_pi.2 hg)
  have hGd : ∀ y w (c : Fin r), fderiv ℝ G y w c = fderiv ℝ (g c) y w := by
    intro y w c
    have hpi : HasFDerivAt (fun y => fun c => g c y)
        (ContinuousLinearMap.pi fun c => fderiv ℝ (g c) y) y :=
      hasFDerivAt_pi.2 fun c => ((hg c).differentiable (by norm_num) y).hasFDerivAt
    have h := e.hasFDerivAt.comp y hpi
    rw [show G = e ∘ (fun y => fun c => g c y) from rfl, h.fderiv]
    simp [he]
  -- Step 2: the constant determinant form `Θ ≡ θ`, `θ(w) = det (w_b(c))_{c,b}`
  obtain ⟨θ, hθ⟩ := Submission.cmr_cc_det_covector_exists r r id
  set Θ : Euclid r → Covector (Euclid r) r := fun _ => θ with hΘ
  -- Step 3: `dΘ = 0`, since `DΘ = 0` and the alternatization is linear
  have hdΘ : extDeriv Θ (G x) = 0 := by
    simp [extDeriv, hΘ, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  -- Step 4: naturality of `d` gives `d(G^*Θ)(x) = (dΘ)(G x) ∘ DG(x) = 0`
  have hpull := extDeriv_pullback (ω := Θ) (f := G) (x := x) (r := 2) (differentiableAt_const θ)
    hGc.contDiffAt (by simp)
  rw [hdΘ] at hpull
  -- Step 5: the coordinate formula `d(G^*Θ)(x)(V) = ∑_b (-1)^b D[(G^*Θ)(·)(V ∘ s_b)](x) V_b`
  have hβd : DifferentiableAt ℝ (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)) x :=
    (differentiableAt_const θ).continuousAlternatingMapCompContinuousLinearMap
      ((hGc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  have happ := extDeriv_apply hβd V
  rw [hpull] at happ
  -- Step 6: `(G^*Θ)(y)(V ∘ s_b) = M_b(y)` by Steps 1 and 2
  have hβ : ∀ i : Fin (r + 1), (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)
      (i.removeNth V)) = fun y => Matrix.det (Matrix.of fun (c b' : Fin r) =>
        fderiv ℝ (g c) y (V (i.succAbove b'))) := by
    intro i
    funext y
    simp only [hΘ, ContinuousAlternatingMap.compContinuousLinearMap_apply, hθ]
    congr 1
    ext c b'
    simp [Matrix.of_apply, Fin.removeNth, hGd]
  -- Step 7: hence `0 = d(G^*Θ)(x)(V) = ∑_b (-1)^b DM_b(x) V_b`
  simp only [hβ] at happ
  rw [eq_comm] at happ
  simpa [zsmul_eq_mul] using happ

/-- **Integration by parts for Jacobian minors** (formula (∗) of the weak continuity of Jacobian
minors, for `C²` maps): for `C²` functions `g₀, …, g_r` on `ℝᵏ`, directions `V₀, …, V_r` and a
compactly supported `C¹` function `ψ`, with `A = (Dg_c V_b)_{c,b}` and `M_b` the minor of `A`
without row `0` and column `b`, `∫ ψ det A = −Σ_b (−1)^b ∫ (Dψ V_b) g₀ M_b`.  Laplace expansion
along row `0`, the product rule for `F_b = ψ g₀ M_b` and the Piola identity
`Σ_b (−1)^b ∂_{V_b} M_b = 0` give `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
pointwise, and `∫ ∂_W F = 0` for every compactly supported `C¹` function `F` (integration by
parts of the Lipschitz functions `1` and `F`). -/
theorem Submission.dor_lmb_fcd_jwc_smooth_minor_ibp : ∀ (k r : ℕ) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, ContDiff ℝ 2 (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r g V ψ hg hψ hψs
  -- Step 2: the entries `Dg_c(·)W` are `C¹` (`g_c` is `C²`), hence so is every determinant of
  -- such entries (Leibniz formula), in particular every minor `M_b`
  have hdetC1 : ∀ {m : ℕ} (A : Euclid k → Fin m → Fin m → ℝ),
      (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) →
      ContDiff ℝ 1 (fun x => Matrix.det (Matrix.of (A x))) := by
    intro m A hA
    have hLeib : (fun x => Matrix.det (Matrix.of (A x))) =
        fun x => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A x (σ i) i := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      simp [Matrix.of_apply]
    rw [hLeib]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA _ _)
  have hentry : ∀ c (W : Euclid k), ContDiff ℝ 1 (fun x => fderiv ℝ (g c) x W) := fun c W =>
    ((hg c).fderiv_right (by norm_num)).clm_apply contDiff_const
  set M : Fin (r + 1) → Euclid k → ℝ := fun b x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
    fderiv ℝ (g c.succ) x (V (b.succAbove b')))
  have hMC1 : ∀ b, ContDiff ℝ 1 (M b) := fun b =>
    hdetC1 (fun x c b' => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) fun c b' => hentry _ _
  -- `F_b = ψ g₀ M_b` is `C¹` with compact support
  have hFC1 : ∀ b, ContDiff ℝ 1 (fun y => ψ y * g 0 y * M b y) := fun b =>
    (hψ.mul ((hg 0).of_le (by norm_num))).mul (hMC1 b)
  have hFs : ∀ b, HasCompactSupport (fun y => ψ y * g 0 y * M b y) := fun b =>
    hψs.mul_right.mul_right
  -- Step 3: product rule for `∂_{V_b} F_b`
  have hdiff : ∀ b x, fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) =
      fderiv ℝ ψ x (V b) * g 0 x * M b x + ψ x * fderiv ℝ (g 0) x (V b) * M b x +
        ψ x * g 0 x * fderiv ℝ (M b) x (V b) := by
    intro b x
    have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
    have hgd : DifferentiableAt ℝ (g 0) x := (hg 0).differentiable (by norm_num) x
    have hMd : DifferentiableAt ℝ (M b) x := (hMC1 b).differentiable (by norm_num) x
    have h : HasFDerivAt (fun y => ψ y * g 0 y * M b y) _ x :=
      (hψd.hasFDerivAt.mul hgd.hasFDerivAt).mul hMd.hasFDerivAt
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  -- Steps 1, 4, 5: Laplace expansion along row `0` and the Piola identity give, pointwise,
  -- `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
  have hpt : ∀ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) := by
    intro x
    have hp : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) = 0 :=
      Submission.dor_lmb_fcd_jwc_piola_identity k r (fun c => g c.succ) V x fun c => hg c.succ
    simp_rw [hdiff]
    have halg : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x +
          ψ x * fderiv ℝ (g 0) x (V b) * M b x + ψ x * g 0 x * fderiv ℝ (M b) x (V b)) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) =
        ψ x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (g 0) x (V b) * M b x +
          ψ x * g 0 x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [halg, hp, mul_zero, add_zero, Matrix.det_succ_row_zero]
    rfl
  -- Step 6: `∫ ∂_W F = 0` for `C¹` compactly supported `F` (integration by parts of the
  -- Lipschitz functions `1` and `F`)
  have hIBP0 : ∀ F : Euclid k → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ∀ W,
      ∫ x, fderiv ℝ F x W = 0 := by
    intro F hF hFs W
    obtain ⟨C, hFL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hFs hF (by norm_num)
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid k)))
      (LipschitzWith.const (1 : ℝ)) hFL hFs (-W)
    have h0 : ∀ x : Euclid k, lineDeriv ℝ (fun _ : Euclid k => (1 : ℝ)) x (-W) = 0 := by
      intro x
      rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
      simp
    have h1 : ∀ x, lineDeriv ℝ F x W = fderiv ℝ F x W := fun x =>
      (hF.differentiable (by norm_num) x).lineDeriv_eq_fderiv
    simp only [h0, zero_mul, integral_zero, neg_neg, mul_one, h1] at h
    exact h.symm
  -- Step 7: every term is continuous with compact support, hence integrable; integrate
  have hi1 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b)) := fun b =>
    ((((hFC1 b).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hFs b).fderiv_apply ℝ (V b))).const_mul _
  have hi2 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      (fderiv ℝ ψ x (V b) * g 0 x * M b x)) := fun b =>
    (((((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hg 0).continuous).mul (hMC1 b).continuous).integrable_of_hasCompactSupport
      ((hψs.fderiv_apply ℝ (V b)).mul_right.mul_right)).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_sub (integrable_finsetSum _ fun b _ => hi1 b)
      (integrable_finsetSum _ fun b _ => hi2 b),
    integral_finsetSum _ fun b _ => hi1 b, integral_finsetSum _ fun b _ => hi2 b]
  have hz : ∑ b : Fin (r + 1), ∫ x, (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [integral_const_mul, hIBP0 _ (hFC1 b) (hFs b) _, mul_zero]
  rw [hz, zero_sub]
  simp only [integral_const_mul]
  rfl

/-- **Integration by parts for Jacobian minors of Lipschitz maps** (the step "`(∗)` holds for
Lipschitz `v`" in the weak continuity of Jacobian minors): for `L`-Lipschitz `g₀, …, g_r` on `ℝᵏ`,
vectors `V₀, …, V_r` and `ψ ∈ C¹_c(ℝᵏ)`,
`∫ ψ det A = −Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, where `A = (Dg_c V_b)_{c,b}` and `M_b` is the minor
`det (Dg_{c+1} V_{s_b(b')})_{c,b'}`, `s_b = b.succAbove`.  Mollify every `g_c`: `C^∞`, `L`-Lipschitz
`g^n_c → g_c` uniformly with `Dg^n_c → Dg_c` a.e.  The identity holds for every `n` (smooth case);
the determinants converge a.e. and are bounded by `(r+1)! (L Σ_b ‖V_b‖)^(r+1)`, resp.
`r! (L Σ_b' ‖V_{s_b(b')}‖)^r`, so both sides converge by dominated convergence (on the right with
`|g^n_0| ≤ |g_0| + 1` for large `n`), and the limits agree. -/
theorem Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp : ∀ (k r : ℕ) (L : NNReal) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, LipschitzWith L (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r L g V ψ hg hψ hψs
  -- step 1: smooth `L`-Lipschitz approximants `fs c n` of every component `g c`
  choose fs hfs_smooth hfs_lip hfs_unif hfs_ae using
    fun c => Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx k L (g c) (hg c)
  -- step 2: the identity for the smooth maps `fs · n`
  have hid := fun n => Submission.dor_lmb_fcd_jwc_smooth_minor_ibp k r (fun c => fs c n) V ψ
    (fun c => (hfs_smooth c n).of_le (by simp)) hψ hψs
  -- step 3: off a null set all derivatives converge, hence so do the entries and determinants
  have hae : ∀ᵐ x ∂(volume : Measure (Euclid k)), ∀ c,
      Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x)) := ae_all_iff.2 hfs_ae
  have hdet_lim : ∀ {m : ℕ} (σ : Fin m → Fin (r + 1)) (W : Fin m → Euclid k) (x : Euclid k),
      (∀ c, Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x))) →
      Tendsto (fun n => Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b)))) := by
    intro m σ W x hx
    have hM : Tendsto (fun n => (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b))) := by
      refine tendsto_pi_nhds.2 fun c => tendsto_pi_nhds.2 fun b => ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (W b)).continuous.tendsto _).comp (hx (σ c))
    exact ((continuous_id.matrix_det).tendsto _).comp hM
  -- step 4: the bound `B` of the full determinants and the integrability of `ψ`
  set B : ℝ := ((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1)
  have hψc : Continuous ψ := hψ.continuous
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  -- step 5: the left side converges, dominated by `B |ψ|`
  have hL : Tendsto
      (fun n => ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (fs c n) x (V b)))
      atTop (𝓝 (∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => B * ‖ψ x‖) (fun n => ?_)
      (hψi.norm.const_mul B) (fun n => Eventually.of_forall fun x => ?_) ?_
    · exact hψc.aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
          (fun c => hfs_lip c n)).1.aestronglyMeasurable
    · have h := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
        (fun c => hfs_lip c n)).2 x
      rw [norm_mul, Real.norm_eq_abs (Matrix.det _), mul_comm]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · filter_upwards [hae] with x hx
      exact tendsto_const_nhds.mul (hdet_lim id V x hx)
  -- step 6: each term of the right side converges, dominated by `Br |∂_{V_b}ψ| (|g 0| + 1)`
  have hR : ∀ b : Fin (r + 1), Tendsto (fun n => ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x *
      Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) := by
    intro b
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) := hψs.fderiv_apply (𝕜 := ℝ) (V b)
    have hwi : Integrable (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1))) := by
      refine Integrable.const_mul ?_ _
      exact Continuous.integrable_of_hasCompactSupport
        (hdψc.norm.mul ((hg 0).continuous.norm.add continuous_const)) hdψs.norm.mul_right
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)))
      (Eventually.of_forall fun n => ?_) ?_ hwi ?_
    · exact (hdψc.mul (hfs_smooth 0 n).continuous).aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
          (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).1.aestronglyMeasurable
    · -- `|fs 0 n| ≤ |g 0| + 1` once `fs 0 n` is uniformly `1`-close to `g 0`
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hfs_unif 0) 1 one_pos).exists_forall_of_atTop
      refine eventually_atTop.2 ⟨N, fun n hn => Eventually.of_forall fun x => ?_⟩
      have h1 : ‖fs 0 n x‖ ≤ ‖g 0 x‖ + 1 := by
        have := hN n hn x
        rw [dist_comm, dist_eq_norm] at this
        have := norm_le_insert' (fs 0 n x) (g 0 x)
        linarith
      have h2 := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
        (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).2 x
      rw [norm_mul, norm_mul, Real.norm_eq_abs (Matrix.det _)]
      calc ‖fderiv ℝ ψ x (V b)‖ * ‖fs 0 n x‖ * |Matrix.det _|
          ≤ ‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1) * Br := by gcongr
        _ = Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)) := by ring
    · filter_upwards [hae] with x hx
      refine (tendsto_const_nhds.mul ((hfs_unif 0).tendsto_at x)).mul ?_
      exact hdet_lim Fin.succ (fun b' => V (b.succAbove b')) x hx
  have hRall : Tendsto (fun n => -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) *
      ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (-∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x *
        Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) :=
    Tendsto.neg (tendsto_finsetSum _ fun b _ => (hR b).const_mul _)
  -- step 7: both sides of step 2 agree for every `n`, so their limits agree
  exact tendsto_nhds_unique hL (hRall.congr fun n => (hid n).symm)
/-- **Weak-* convergence against `L¹` test functions** (density step of the weak continuity of
Jacobian minors): if `|F_j|, |F| ≤ C` and `∫ ψ F_j → ∫ ψ F` for every `C^∞` compactly supported
`ψ`, then `∫ φ F_j → ∫ φ F` for every integrable `φ`.  `C_c^∞` is dense in `L¹`: by
`MemLp.induction_dense` it suffices to approximate `c 1_s` with `μ(s) < ∞`; regularity gives
`K ⊆ s ⊆ U`, `K` compact, `U` open, `μ(U \ K)` small, and `c χ` works for a smooth Urysohn
function `χ` (`χ = 1` exactly on `K`, `support χ = U ∩ B_R(0)`).  (Mathlib's
`MemLp.exist_eLpNorm_sub_le` is outside the import closure.)  For `ε > 0` take such `ψ` with
`∫ |φ − ψ| ≤ η = ε/(4C + 1)`; then `|∫ φ F_j − ∫ φ F| ≤ 2Cη + |∫ ψ F_j − ∫ ψ F| < ε` for large
`j`. -/
theorem Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade : ∀ (k : ℕ) (C : ℝ) (Fs : ℕ → Euclid k → ℝ) (F : Euclid k → ℝ), (∀ j, AEStronglyMeasurable (Fs j) (volume : Measure (Euclid k))) → AEStronglyMeasurable F (volume : Measure (Euclid k)) → (∀ j x, |Fs j x| ≤ C) → (∀ x, |F x| ≤ C) → (∀ ψ : Euclid k → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → Tendsto (fun j => ∫ x, ψ x * Fs j x) atTop (𝓝 (∫ x, ψ x * F x))) → ∀ φ : Euclid k → ℝ, Integrable φ → Tendsto (fun j => ∫ x, φ x * Fs j x) atTop (𝓝 (∫ x, φ x * F x)) := by
  intro k C Fs F hFs hF hFsb hFb hconv φ hφ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
  -- step 1: `C_c^∞` is dense in `L¹`; by `MemLp.induction_dense` only `c 1_s` needs approximating
  have hdense : ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ ψ : Euclid k → ℝ,
      eLpNorm (φ - ψ) 1 (volume : Measure (Euclid k)) ≤ ε ∧
        (ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ) := by
    intro ε hε
    refine MemLp.induction_dense ENNReal.one_ne_top
      (fun g => ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) ?_ ?_
      (memLp_one_iff_integrable.2 hφ) hε
    · intro c s hs hμs ε' hε'
      -- `K ⊆ s ⊆ U` with `μ(U \ s), μ(s \ K) < δ/2`, `δ = ε'/‖c‖`
      set δ : ℝ≥0∞ := ε' / ‖c‖ₑ with hδ
      have hδ0 : δ ≠ 0 := by
        rw [hδ, Ne, ENNReal.div_eq_zero_iff, not_or]
        exact ⟨hε', enorm_ne_top⟩
      have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ0).ne'
      obtain ⟨K, hKs, hKc, hK⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hδ2
      obtain ⟨U, hsU, hUo, -, hU⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hδ2
      -- smooth Urysohn function `χ`: `χ = 1` on `K`, `support χ = U ∩ B_R(0)`, `0 ≤ χ ≤ 1`
      obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball (0 : Euclid k)
      obtain ⟨χ, hχd, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
        (hUo.inter isOpen_ball) hKc.isClosed (subset_inter (hKs.trans hsU) hR)
      have hχc : HasCompactSupport χ := by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid k) R) (fun x hx => ?_)
        rw [← notMem_support, hχs]
        exact fun h => hx (ball_subset_closedBall h.2)
      refine ⟨fun x => c * χ x, ?_, contDiff_const.mul hχd, hχc.mul_left⟩
      -- `|c χ − c 1_s| ≤ |c| 1_{U \ K}`, so `‖c χ − c 1_s‖₁ ≤ ‖c‖ μ(U \ K) ≤ ‖c‖ δ ≤ ε'`
      have hle : ∀ x, ‖((fun x => c * χ x) - s.indicator fun _ => c) x‖ ≤
          ‖(U \ K).indicator (fun _ => c) x‖ := by
        intro x
        obtain ⟨h0, h1⟩ := hχr (mem_range_self x)
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        by_cases hxK : x ∈ K
        · rw [(hχ1 x).1 hxK, indicator_of_mem (hKs hxK)]
          simp
        by_cases hxU : x ∈ U
        · rw [indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
          by_cases hxs : x ∈ s
          · rw [indicator_of_mem hxs, show c * χ x - c = c * (χ x - 1) by ring, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg c) (by rw [abs_le]; constructor <;> linarith)
          · rw [indicator_of_notMem hxs, sub_zero, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg c) (by rw [abs_le]; constructor <;> linarith)
        · have hχ0 : χ x = 0 := by
            rw [← notMem_support, hχs]
            exact fun h => hxU h.1
          rw [hχ0, indicator_of_notMem (fun h => hxU (hsU h))]
          simp
      calc eLpNorm ((fun x => c * χ x) - s.indicator fun _ => c) 1 volume
          ≤ eLpNorm ((U \ K).indicator fun _ => c) 1 volume :=
            eLpNorm_mono (((contDiff_const.mul hχd).continuous.aestronglyMeasurable).sub
              (aestronglyMeasurable_const.indicator hs)) hle
        _ = ‖c‖ₑ * volume (U \ K) := by
          rw [eLpNorm_indicator_const (hUo.measurableSet.diff hKc.isClosed.measurableSet).nullMeasurableSet
            one_ne_zero ENNReal.one_ne_top]
          simp
        _ ≤ ‖c‖ₑ * δ := by
          gcongr
          calc volume (U \ K) ≤ volume ((U \ s) ∪ (s \ K)) := by
                refine measure_mono fun x hx => ?_
                by_cases hxs : x ∈ s
                · exact Or.inr ⟨hxs, hx.2⟩
                · exact Or.inl ⟨hx.1, hxs⟩
            _ ≤ volume (U \ s) + volume (s \ K) := measure_union_le _ _
            _ ≤ δ / 2 + δ / 2 := add_le_add hU.le hK.le
            _ = δ := ENNReal.add_halves δ
        _ ≤ ε' := ENNReal.mul_div_le
    · rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
      exact ⟨hf1.add hg1, hf2.add hg2⟩
  -- step 2: `|∫ θ G| ≤ C ∫ |θ|` for integrable `θ` and `|G| ≤ C`
  have hint : ∀ θ : Euclid k → ℝ, Integrable θ → ∀ G : Euclid k → ℝ,
      AEStronglyMeasurable G (volume : Measure (Euclid k)) → (∀ x, |G x| ≤ C) →
      Integrable (fun x => θ x * G x) ∧ |∫ x, θ x * G x| ≤ C * ∫ x, ‖θ x‖ := by
    intro θ hθ G hG hGb
    refine ⟨hθ.mul_bdd hG (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x), ?_⟩
    calc |∫ x, θ x * G x| = ‖∫ x, θ x * G x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, C * ‖θ x‖ := by
          refine norm_integral_le_of_norm_le (hθ.norm.const_mul C) (Eventually.of_forall fun x => ?_)
          rw [norm_mul, Real.norm_eq_abs (G x), mul_comm]
          exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _)
      _ = C * ∫ x, ‖θ x‖ := integral_const_mul _ _
  -- step 3: `ψ ∈ C_c^∞` with `∫ |φ − ψ| ≤ η = ε/(4C + 1)`, and `N` from the convergence on `ψ`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * C + 1) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ, hψε, hψs, hψc⟩ := hdense (ENNReal.ofReal_pos.2 hηpos).ne'
  have hψi : Integrable ψ := hψs.continuous.integrable_of_hasCompactSupport hψc
  have hdiff : ∫ x, ‖(φ - ψ) x‖ ≤ η := by
    have h1 := integral_norm_eq_lintegral_enorm (μ := (volume : Measure (Euclid k)))
      (hφ.sub hψi).aestronglyMeasurable
    rw [h1, ← eLpNorm_one_eq_lintegral_enorm]
    · exact ENNReal.toReal_le_of_le_ofReal hηpos.le hψε
    · exact (hφ.sub hψi).aestronglyMeasurable
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv ψ hψs hψc) (ε / 2) (by positivity)
  -- step 4: three-term estimate `|∫ φ F_j − ∫ φ F| ≤ 2Cη + |∫ ψ F_j − ∫ ψ F| < ε` for `j ≥ N`
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hint (φ - ψ) (hφ.sub hψi) (Fs j) (hFs j) (hFsb j)
  have h2 := hint (φ - ψ) (hφ.sub hψi) F hF hFb
  have h3 := hint ψ hψi (Fs j) (hFs j) (hFsb j)
  have h4 := hint ψ hψi F hF hFb
  have e1 : ∫ x, φ x * Fs j x = (∫ x, (φ - ψ) x * Fs j x) + ∫ x, ψ x * Fs j x := by
    rw [← integral_add h1.1 h3.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have e2 : ∫ x, φ x * F x = (∫ x, (φ - ψ) x * F x) + ∫ x, ψ x * F x := by
    rw [← integral_add h2.1 h4.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have hNj := hN j hj
  rw [Real.dist_eq] at hNj ⊢
  rw [e1, e2]
  have hCη : C * η < ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hA := h1.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have hB := h2.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have key : ∀ a1 b1 a2 b2 : ℝ, |(a1 + b1) - (a2 + b2)| ≤ |a1| + |a2| + |b1 - b2| := by
    intro a1 b1 a2 b2
    calc |(a1 + b1) - (a2 + b2)| = |(a1 - a2) + (b1 - b2)| := by ring_nf
      _ ≤ |a1 - a2| + |b1 - b2| := abs_add_le _ _
      _ ≤ |a1| + |a2| + |b1 - b2| := by
          have := abs_sub a1 a2
          linarith
  have := key (∫ x, (φ - ψ) x * Fs j x) (∫ x, ψ x * Fs j x) (∫ x, (φ - ψ) x * F x) (∫ x, ψ x * F x)
  linarith

/-- **Weak continuity of Jacobian minors** (null Lagrangians; Reshetnyak 1967, Ball 1977): if the
`L`-Lipschitz `gʲ_c` converge uniformly to the `L`-Lipschitz `g_c` on `ℝᵏ` (`c < r`), then
`∫ φ det(Dgʲ_c V_b) → ∫ φ det(Dg_c V_b)` for every `φ ∈ L¹`.  Induction on `r`; for `r = 0` both
determinants are `1`.  For `r + 1` the minors are measurable and bounded by
`(r+1)! (L Σ_b ‖V_b‖)^{r+1}`, so by the weak-* to `L¹` upgrade it suffices to take `φ = ψ ∈ C^∞_c`.
Integration by parts in the first row writes `∫ ψ det(Dg_c V_b)` as
`−Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, `M_b` the minor of the rows `c ≥ 1` and the columns `≠ b`.
Split `gʲ₀ = (gʲ₀ − g₀) + g₀`: the first part is at most
`r! (L Σ_{b'} ‖V_{b'}‖)^r sup |gʲ₀ − g₀| ∫ |∂_{V_b}ψ| → 0`, and the second converges by the
induction hypothesis with the continuous compactly supported weight `∂_{V_b}ψ · g₀`. -/
theorem Submission.dor_lmb_fcd_jwc_minor_weak_continuity : ∀ (k r : ℕ) (L : NNReal) (gs : ℕ → Fin r → Euclid k → ℝ) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k) (φ : Euclid k → ℝ), Integrable φ → (∀ j c, LipschitzWith L (gs j c)) → (∀ c, LipschitzWith L (g c)) → (∀ c, TendstoUniformly (fun j => gs j c) (g c) atTop) → Tendsto (fun j => ∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b))) atTop (𝓝 (∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
  intro k r
  induction r with
  | zero =>
    -- the empty determinant is `1`
    intro L gs g V φ hφ hgs hg hU
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro L gs g V φ hφ hgs hg hU
    -- Step 2: the minors are bounded, so it suffices to test against `ψ ∈ C^∞_c`
    have hb := fun (G : Fin (r + 1) → Euclid k → ℝ) (hG : ∀ c, LipschitzWith L (G c)) =>
      Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L G V hG
    refine Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade k
      (((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1))
      (fun j x => Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b)))
      (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))
      (fun j => (hb (gs j) (hgs j)).1.aestronglyMeasurable) (hb g hg).1.aestronglyMeasurable
      (fun j => (hb (gs j) (hgs j)).2) (hb g hg).2 ?_ φ hφ
    intro ψ hψ hψs
    -- Step 3: integrate by parts in the first row
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hIBPj := fun j =>
      Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L (gs j) V ψ (hgs j) hψ1 hψs
    have hIBP := Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L g V ψ hg hψ1 hψs
    simp only [hIBPj, hIBP]
    refine Tendsto.neg (tendsto_finsetSum _ fun b _ => Tendsto.const_mul _ ?_)
    -- the minors `Mʲ_b`, `M_b` and their bound
    set Mj : ℕ → Euclid k → ℝ := fun j x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
      fderiv ℝ (gs j c.succ) x (V (b.succAbove b'))) with hMj
    set M : Euclid k → ℝ := fun x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
      fderiv ℝ (g c.succ) x (V (b.succAbove b'))) with hM
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r with hBr
    have hbr := fun j => Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L
      (fun c => gs j c.succ) (fun b' => V (b.succAbove b')) (fun c => hgs j c.succ)
    -- Step 4: the weight `θ_b = ∂_{V_b}ψ · g₀` is continuous with compact support
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) :=
      (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Euclid k →L[ℝ] ℝ => T (V b)) (by simp)
    have hdψi : Integrable (fun x => fderiv ℝ ψ x (V b)) :=
      hdψc.integrable_of_hasCompactSupport hdψs
    have hθi : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x) :=
      (hdψc.mul (hg 0).continuous).integrable_of_hasCompactSupport hdψs.mul_right
    -- Step 6: the induction hypothesis with the weight `θ_b`
    have hih := ih L (fun j c => gs j c.succ) (fun c => g c.succ) (fun b' => V (b.succAbove b'))
      (fun x => fderiv ℝ ψ x (V b) * g 0 x) hθi (fun j c => hgs j c.succ) (fun c => hg c.succ)
      (fun c => hU c.succ)
    -- Step 5: `|∫ ∂_{V_b}ψ (gʲ₀ − g₀) Mʲ_b| ≤ Br sup |gʲ₀ − g₀| ∫ |∂_{V_b}ψ| → 0`
    have herr : Tendsto (fun j => ∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x) atTop
        (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set K : ℝ := Br * (∫ x, ‖fderiv ℝ ψ x (V b)‖) + 1 with hK
      have hBr0 : 0 ≤ Br := by positivity
      have hK0 : 0 < K := by
        have : 0 ≤ ∫ x, ‖fderiv ℝ ψ x (V b)‖ := integral_nonneg fun _ => norm_nonneg _
        positivity
      have hδ : 0 < ε / (2 * K) := by positivity
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hU 0) (ε / (2 * K)) hδ).exists_forall_of_atTop
      refine ⟨N, fun j hj => ?_⟩
      rw [Real.dist_eq, sub_zero]
      have hbd : ∀ x, ‖fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x‖ ≤
          (ε / (2 * K) * Br) * ‖fderiv ℝ ψ x (V b)‖ := by
        intro x
        have h1 : |gs j 0 x - g 0 x| ≤ ε / (2 * K) := by
          have := hN j hj x
          rw [dist_comm, Real.dist_eq] at this
          exact this.le
        have h2 : |Mj j x| ≤ Br := (hbr j).2 x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        calc |fderiv ℝ ψ x (V b)| * |gs j 0 x - g 0 x| * |Mj j x|
            ≤ |fderiv ℝ ψ x (V b)| * (ε / (2 * K)) * Br := by gcongr
          _ = (ε / (2 * K) * Br) * |fderiv ℝ ψ x (V b)| := by ring
      calc |∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x|
          = ‖∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, (ε / (2 * K) * Br) * ‖fderiv ℝ ψ x (V b)‖ :=
            norm_integral_le_of_norm_le (hdψi.norm.const_mul _) (Eventually.of_forall hbd)
        _ = (ε / (2 * K)) * (Br * ∫ x, ‖fderiv ℝ ψ x (V b)‖) := by
            rw [integral_const_mul]; ring
        _ ≤ (ε / (2 * K)) * K := by gcongr; linarith
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    -- Step 7: `∫ ∂_{V_b}ψ gʲ₀ Mʲ_b = ∫ ∂_{V_b}ψ (gʲ₀ − g₀) Mʲ_b + ∫ θ_b Mʲ_b → 0 + ∫ θ_b M_b`
    have hsum := herr.add hih
    rw [zero_add] at hsum
    refine hsum.congr' (Eventually.of_forall fun j => ?_)
    have i2 : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x * Mj j x) := by
      have h1 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * g 0 x)) :=
        Integrable.bdd_mul (c := Br) hθi (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      exact h1.congr (Eventually.of_forall fun x => by simp only; ring)
    have i1 : Integrable (fun x => fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x) := by
      have hgj : Integrable (fun x => fderiv ℝ ψ x (V b) * gs j 0 x) :=
        (hdψc.mul (hgs j 0).continuous).integrable_of_hasCompactSupport hdψs.mul_right
      have h1 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * gs j 0 x)) :=
        Integrable.bdd_mul (c := Br) hgj (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      have h2 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * g 0 x)) :=
        Integrable.bdd_mul (c := Br) hθi (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      exact (h1.sub h2).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    simp only
    rw [← integral_add i1 i2]
    congr 1
    funext x
    ring

/-- **Weak continuity of pulled-back `k`-forms** (the identification of Simon 2.29 with 3.6): if
the `L`-Lipschitz `H_j : ℝᵏ → ℝ^{N'}` converge uniformly to the `L`-Lipschitz `H`, `w ∈ L¹(A)` and
`ω ∈ 𝒟ᵏ(ℝ^{N'})`, then `∫_A w H_j^#ω(e) → ∫_A w H^#ω(e)`, where
`H^#ω(u)(e) = ω(H(u))(DH(u)e₁, …, DH(u)e_k)`.  Where `G` is differentiable (a.e., by Rademacher)
`D(G^i)(u) v = (DG(u) v) i`, so the covector expansion gives `k! G^#ω(e) = Σ_I ω_I(G) D_I(G)` a.e.,
with coefficients `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (k-1)})` continuous with compact support and
minors `D_I(G) = det (D(G^{I c}) e_b)_{c,b}` measurable and bounded by `Cb = k! (L Σ_b ‖e_b‖)ᵏ`.
For each `I` split `ω_I(H_j) = (ω_I(H_j) − ω_I(H)) + ω_I(H)`: the first part contributes at most
`Cb sup |ω_I(H_j) − ω_I(H)| ∫_A |w| → 0` (`ω_I` is uniformly continuous), and
`∫_A w ω_I(H) D_I(H_j) → ∫_A w ω_I(H) D_I(H)` is the weak continuity of Jacobian minors with the
weight `1_A w ω_I(H) ∈ L¹`.  Summing over `I` and dividing by `k!` concludes. -/
theorem Submission.dor_lmb_fcd_jacobian_weak_continuity : ∀ (k N' : ℕ) (A : Set (Euclid k)) (w : Euclid k → ℝ) (L : NNReal) (Hs : ℕ → Euclid k → Euclid N') (H : Euclid k → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k), MeasurableSet A → IntegrableOn w A → (∀ j, LipschitzWith L (Hs j)) → LipschitzWith L H → TendstoUniformly Hs H atTop → Tendsto (fun j => ∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (Hs j u) (fun i => fderiv ℝ (Hs j) u (EuclideanSpace.single i (1 : ℝ)))) atTop (𝓝 (∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (H u) (fun i => fderiv ℝ H u (EuclideanSpace.single i (1 : ℝ))))) := by
  intro k N' A w L Hs H ω hA hw hHs hH hU
  have hw' : Integrable w (volume.restrict A) := hw
  -- step 1: `ω` is continuous with compact support, hence so are its coefficients
  -- `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (k-1)})`, which are therefore bounded
  obtain ⟨⟨hωsm, hωs⟩, -⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid N') k) := ContDiff.continuous hωsm
  obtain ⟨ωI, hωI⟩ : ∃ f : (Fin k → Fin N') → Euclid N' → ℝ, ∀ I y,
      f I y = (ω : DifferentialForm (Euclid N') k) y
        (fun c => EuclideanSpace.single (I c) (1 : ℝ)) :=
    ⟨fun I y => (ω : DifferentialForm (Euclid N') k) y
      (fun c => EuclideanSpace.single (I c) (1 : ℝ)), fun _ _ => rfl⟩
  have hωIc : ∀ I, Continuous (ωI I) := by
    intro I
    have h : ωI I = fun y => ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ
        (fun c => EuclideanSpace.single (I c) (1 : ℝ)) ((ω : DifferentialForm (Euclid N') k) y) := by
      funext y; rw [hωI]; rfl
    rw [h]
    exact (ContinuousLinearMap.continuous _).comp hωc
  have hωIs : ∀ I, HasCompactSupport (ωI I) := by
    intro I
    have h : ωI I = (fun f : Covector (Euclid N') k =>
        f (fun c => EuclideanSpace.single (I c) (1 : ℝ))) ∘ (ω : DifferentialForm (Euclid N') k) := by
      funext y; rw [hωI]; rfl
    rw [h]
    exact hωs.comp_left (by simp)
  have hωIG : ∀ I (G : Euclid k → Euclid N'), Continuous G →
      Continuous (fun u => ωI I (G u)) ∧ ∃ M, ∀ u, ‖ωI I (G u)‖ ≤ M := fun I G hG =>
    ⟨(hωIc I).comp hG, ((hωIc I).bounded_above_of_compact_support (hωIs I)).imp
      fun _ hM u => hM (G u)⟩
  -- step 2: coordinates of `L`-Lipschitz maps are `L`-Lipschitz, and the minors
  -- `D_I(G) = det (D(G^{I c}) e_b)_{c,b}` are measurable and bounded by `Cb`
  have hcoordL : ∀ G : Euclid k → Euclid N', LipschitzWith L G → ∀ i,
      LipschitzWith L (fun y => G y i) :=
    fun G hG i => LipschitzWith.of_dist_le_mul fun x y =>
      (PiLp.dist_apply_le (G x) (G y) i).trans (hG.dist_le_mul x y)
  obtain ⟨D, hD⟩ : ∃ D : (Euclid k → Euclid N') → (Fin k → Fin N') → Euclid k → ℝ, ∀ G I x,
      D G I x = Matrix.det (Matrix.of fun c b =>
        fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))) :=
    ⟨fun G I x => Matrix.det (Matrix.of fun c b =>
      fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))), fun _ _ _ => rfl⟩
  set Cb : ℝ := (k.factorial : ℝ) *
    ((L : ℝ) * ∑ b : Fin k, ‖EuclideanSpace.single b (1 : ℝ)‖) ^ k
  have hDmb : ∀ G : Euclid k → Euclid N', LipschitzWith L G → ∀ I,
      Measurable (D G I) ∧ ∀ x, |D G I x| ≤ Cb := by
    intro G hG I
    have h := Submission.dor_lmb_fcd_jwc_minor_measurable_bound k k L (fun c y => G y (I c))
      (fun b => EuclideanSpace.single b (1 : ℝ)) (fun c => hcoordL G hG (I c))
    have hDe : D G I = fun x => Matrix.det (Matrix.of fun c b =>
        fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))) := funext (hD G I)
    rw [hDe]
    exact h
  -- `w F D_I(G)` is integrable on `A` for continuous bounded `F`
  have hint : ∀ F : Euclid k → ℝ, Continuous F → (∃ M, ∀ u, ‖F u‖ ≤ M) →
      ∀ G : Euclid k → Euclid N', LipschitzWith L G → ∀ I,
      Integrable (fun u => w u * F u * D G I u) (volume.restrict A) := by
    rintro F hF ⟨M, hM⟩ G hG I
    refine (hw'.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hM)).mul_bdd (c := Cb)
      (hDmb G hG I).1.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]
    exact (hDmb G hG I).2 u
  -- step 3: where `G` is differentiable, `D(G^i)(u) v = (DG(u) v) i`, so the covector expansion
  -- gives `k! G^#ω(e) = Σ_I ω_I(G) D_I(G)`
  have hpt : ∀ (G : Euclid k → Euclid N') (u : Euclid k), DifferentiableAt ℝ G u →
      (k.factorial : ℝ) * (ω : DifferentialForm (Euclid N') k) (G u)
          (fun i => fderiv ℝ G u (EuclideanSpace.single i (1 : ℝ))) =
        ∑ I, ωI I (G u) * D G I u := by
    intro G u hGu
    rw [Submission.dor_lmb_fcd_jwc_covector_det_expansion]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hωI, hD]
    congr 2
    ext c b
    simp only [Matrix.of_apply]
    have h : HasFDerivAt (PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c) ∘ G)
        ((PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c)).comp (fderiv ℝ G u)) u :=
      (PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c)).hasFDerivAt.comp u hGu.hasFDerivAt
    have h' : HasFDerivAt (fun y => G y (I c))
        ((PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c)).comp (fderiv ℝ G u)) u := h
    rw [h'.fderiv]
    rfl
  -- Rademacher: the expansion holds a.e., so `∫_A w G^#ω(e) = (k!)⁻¹ Σ_I ∫_A w ω_I(G) D_I(G)`
  have hexp : ∀ G : Euclid k → Euclid N', LipschitzWith L G →
      ∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (G u)
          (fun i => fderiv ℝ G u (EuclideanSpace.single i (1 : ℝ))) =
        (k.factorial : ℝ)⁻¹ * ∑ I, ∫ u in A, w u * ωI I (G u) * D G I u := by
    intro G hG
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [← integral_finsetSum (f := fun I u => w u * ωI I (G u) * D G I u) Finset.univ
      fun I _ => hint _ (hωIG I G hG.continuous).1 (hωIG I G hG.continuous).2 G hG I,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hG.ae_differentiableAt (μ := volume))] with u hu
    have h2 : ∑ I, w u * ωI I (G u) * D G I u = w u * ∑ I, ωI I (G u) * D G I u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun I _ => mul_assoc _ _ _
    rw [h2, ← hpt G u hu, mul_left_comm, inv_mul_cancel_left₀ hk]
  -- step 4: the coordinates `H_j^i` converge uniformly to `H^i`
  have hcoordU : ∀ i, TendstoUniformly (fun j y => Hs j y i) (fun y => H y i) atTop := by
    intro i
    have hl : LipschitzWith 1 (fun x : Euclid N' => x i) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [NNReal.coe_one, one_mul]
        exact PiLp.dist_apply_le x y i
    exact hl.uniformContinuous.comp_tendstoUniformly hU
  -- step 5: for each `I`, `∫_A w ω_I(H_j) D_I(H_j) → ∫_A w ω_I(H) D_I(H)`
  have hconvI : ∀ I, Tendsto (fun j => ∫ u in A, w u * ωI I (Hs j u) * D (Hs j) I u) atTop
      (𝓝 (∫ u in A, w u * ωI I (H u) * D H I u)) := by
    intro I
    obtain ⟨hωHc, M, hM⟩ := hωIG I H hH.continuous
    -- weak continuity of Jacobian minors, with the fixed weight `φ = 1_A w ω_I(H) ∈ L¹`
    have hφ : Integrable (A.indicator fun u => w u * ωI I (H u)) := by
      rw [integrable_indicator_iff hA]
      exact hw'.mul_bdd hωHc.aestronglyMeasurable (Eventually.of_forall hM)
    have hmain := Submission.dor_lmb_fcd_jwc_minor_weak_continuity k k L
      (fun j c y => Hs j y (I c)) (fun c y => H y (I c)) (fun b => EuclideanSpace.single b (1 : ℝ))
      _ hφ (fun j c => hcoordL (Hs j) (hHs j) (I c)) (fun c => hcoordL H hH (I c))
      (fun c => hcoordU (I c))
    have hind : ∀ G : Euclid k → Euclid N',
        ∫ x, A.indicator (fun u => w u * ωI I (H u)) x * Matrix.det (Matrix.of fun c b =>
          fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))) =
        ∫ u in A, w u * ωI I (H u) * D G I u := by
      intro G
      rw [← integral_indicator hA]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Set.indicator_mul_left A (fun u => w u * ωI I (H u)) (D G I), hD]
    have hmain' : Tendsto (fun j => ∫ u in A, w u * ωI I (H u) * D (Hs j) I u) atTop
        (𝓝 (∫ u in A, w u * ωI I (H u) * D H I u)) := by
      rw [← hind H]
      exact hmain.congr fun j => hind (Hs j)
    -- the error `|∫_A w (ω_I(H_j) − ω_I(H)) D_I(H_j)| ≤ Cb sup |ω_I(H_j) − ω_I(H)| ∫_A |w| → 0`
    have hωU : TendstoUniformly (fun j u => ωI I (Hs j u)) (fun u => ωI I (H u)) atTop :=
      ((hωIs I).uniformContinuous_of_continuous (hωIc I)).comp_tendstoUniformly hU
    have herr : Tendsto (fun j => ∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u)
        atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set K : ℝ := Cb * (∫ u in A, ‖w u‖) + 1
      have hCb0 : 0 ≤ Cb := by positivity
      have hK0 : 0 < K := by
        have : 0 ≤ ∫ u in A, ‖w u‖ := integral_nonneg fun _ => norm_nonneg _
        positivity
      have hδ : 0 < ε / (2 * K) := by positivity
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 hωU (ε / (2 * K)) hδ).exists_forall_of_atTop
      refine ⟨N, fun j hj => ?_⟩
      rw [Real.dist_eq, sub_zero]
      have hbd : ∀ u, ‖w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u‖ ≤
          (ε / (2 * K) * Cb) * ‖w u‖ := by
        intro u
        have h1 : |ωI I (Hs j u) - ωI I (H u)| ≤ ε / (2 * K) := by
          have := hN j hj u
          rw [dist_comm, Real.dist_eq] at this
          exact this.le
        have h2 : |D (Hs j) I u| ≤ Cb := (hDmb (Hs j) (hHs j) I).2 u
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        calc |w u| * |ωI I (Hs j u) - ωI I (H u)| * |D (Hs j) I u|
            ≤ |w u| * (ε / (2 * K)) * Cb := by gcongr
          _ = (ε / (2 * K) * Cb) * |w u| := by ring
      calc |∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u|
          = ‖∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ u in A, (ε / (2 * K) * Cb) * ‖w u‖ :=
            norm_integral_le_of_norm_le (hw'.norm.const_mul _) (Eventually.of_forall hbd)
        _ = (ε / (2 * K)) * (Cb * ∫ u in A, ‖w u‖) := by
            rw [integral_const_mul]; ring
        _ ≤ (ε / (2 * K)) * K := by gcongr; linarith
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    -- `∫_A w ω_I(H_j) D_I(H_j) = (error) + ∫_A w ω_I(H) D_I(H_j)`
    have heq : ∀ j, (∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u) +
        ∫ u in A, w u * ωI I (H u) * D (Hs j) I u =
        ∫ u in A, w u * ωI I (Hs j u) * D (Hs j) I u := by
      intro j
      have i1 := hint _ (hωIG I (Hs j) (hHs j).continuous).1 (hωIG I (Hs j) (hHs j).continuous).2
        (Hs j) (hHs j) I
      have i2 := hint _ hωHc ⟨M, hM⟩ (Hs j) (hHs j) I
      have i3 : Integrable (fun u => w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u)
          (volume.restrict A) :=
        (i1.sub i2).congr (Eventually.of_forall fun u => by simp only [Pi.sub_apply]; ring)
      rw [← integral_add i3 i2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      ring
    have hsum := herr.add hmain'
    rw [zero_add] at hsum
    exact hsum.congr heq
  -- step 6: sum over `I` and divide by `k!`
  have hlim := (tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin N'))
    fun I _ => hconvI I).const_mul ((k.factorial : ℝ)⁻¹)
  rw [hexp H hH]
  exact hlim.congr fun j => (hexp (Hs j) (hHs j)).symm

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
/-- **A unit covector attaining `1` on an orthonormal frame** (Simon (6.1.1); step 1(b) of the
mass formula, Remark 6.3.2(3)): every orthonormal `τ₁, …, τₙ` in `ℝᴾ` admits an `n`-covector `β`
with `|β|_E = 1` and `β(τ) = 1`.  Take the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors
`⟨τᵢ, ·⟩`, so `β(τ) = det 1 = 1`.  Extend `τ` to an orthonormal basis `f` of `ℝᴾ` with
`f ∘ ι = τ`, `ι = Fin.castLE`.  Then `β(f ∘ j) = sgn π` if `j = ι ∘ π` for a permutation `π`,
and `β(f ∘ j) = 0` otherwise (a zero column, or a repeated vector), so `Σ_j β(f ∘ j)² = n!`;
`regcomp_covector_sq_sum_orthonormalBasis` turns this into `n! = n! |β|_E²`. -/
theorem Submission.regcomp_exists_covector_eval_orthonormal_eq_one : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β = 1 ∧ β τ = 1 := by
  intro P n τ hτ
  classical
  -- Step 1: the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors `⟨τᵢ, ·⟩` (Simon (6.1.1))
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) n, ∀ v : Fin n → Euclid P,
      β v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun i => (innerSL ℝ (τ i) : Euclid P →L[ℝ] ℝ).toLinearMap
    let g : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hg : ∀ v, g v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      intro v
      rw [← Matrix.det_transpose]
      show Matrix.det (Matrix.of fun a b => L (v a) b) = _
      congr 1
    have hcont : Continuous fun v : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i k
      exact Continuous.inner (f := fun _ => τ i) (g := fun v : Fin n → Euclid P => v k)
        continuous_const (continuous_apply k)
    refine ⟨{ g with cont := ?_ }, hg⟩
    have : (g : (Fin n → Euclid P) → ℝ) =
        fun v => Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := funext hg
    simpa [this] using hcont
  -- Step 2: by orthonormality `(⟨τᵢ, τ_k⟩) = 1`, so `β(τ) = det 1 = 1`
  have hβτ : β τ = 1 := by
    have hone : (Matrix.of fun i k => inner ℝ (τ i) (τ k) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext i k
      rw [Matrix.of_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.mp hτ i k
    rw [hβ, hone, Matrix.det_one]
  -- Step 3: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 4: `β(f ∘ j)² = 1` if `j = ι ∘ π` for a permutation `π`, and `0` otherwise
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), β (fun k => f (Φ π k)) ^ 2 = 1 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : β (τ ∘ π) = Equiv.Perm.sign π • β τ := β.toAlternatingMap.map_perm τ π
    rw [h1, h2, hβτ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hzero : ∀ j : Fin n → Fin P, j ∉ Finset.univ.image Φ → β (fun k => f (j k)) ^ 2 = 0 := by
    intro j hj
    have hj' : ∀ π, Φ π ≠ j := fun π hπ => hj (Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ⟩)
    rw [sq_eq_zero_iff]
    by_cases hr : ∀ k, j k ∈ range ι
    · -- `j = ι ∘ ρ` with `ρ` not a permutation, hence not injective: `f ∘ j` repeats a vector
      choose ρ hρ using hr
      have hρ' : ¬ Injective ρ := fun hinj =>
        hj' (Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hinj)) (funext hρ)
      refine β.map_eq_zero_of_not_injective _ fun hinj => hρ' fun a b hab => hinj ?_
      exact congrArg f ((hρ a).symm.trans ((congrArg ι hab).trans (hρ b)))
    · -- some `j k₀ ∉ range ι`: column `k₀` of `(⟨τᵢ, f (j k)⟩)` vanishes
      obtain ⟨k₀, hk₀⟩ := not_forall.mp hr
      rw [hβ]
      refine Matrix.det_eq_zero_of_column_eq_zero k₀ fun i => ?_
      rw [Matrix.of_apply, ← hfι i, f.inner_eq_ite, ite_eq_right fun h => hk₀ ⟨i, h⟩]
  have hsum : ∑ j : Fin n → Fin P, β (fun k => f (j k)) ^ 2 = n.factorial := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) fun j _ hj => hzero j hj,
      Finset.sum_image fun π _ π' _ h => hΦ h]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- Step 5: `n! = n! |β|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`, so `|β|_E = 1`
  have hsq := Submission.regcomp_covector_sq_sum_orthonormalBasis P n β f
  rw [hsum] at hsq
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine ⟨β, (pow_eq_one_iff_of_nonneg (covectorEuclideanNorm_nonneg β) two_ne_zero).mp ?_, hβτ⟩
  exact mul_left_cancel₀ hfac (by rw [← hsq, mul_one])
/-- **Simon Ch. 6, 1.7 and 1.15**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has dual Euclidean coefficient norm exactly one: `|ξ(α)| = |α(τ)| ≤ |α|_E` for every
`n`-covector `α`, and `ξ(±β₀) = 1` for a covector `β₀` with `|β₀|_E = 1` and `β₀(τ) = 1`
(`+β₀` for the sign `+`, `−β₀` for the sign `−`, using `|−β₀|_E = |β₀|_E`). -/
theorem Submission.regcomp_unit_orientation_pairing : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ β = 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  obtain ⟨β₀, hβ₀, hβ₀τ⟩ := Submission.regcomp_exists_covector_eval_orthonormal_eq_one P n τ hτ
  rcases hξ with h | h
  · -- `ξ(α) = α(τ)`: take `β = β₀`
    refine ⟨fun α => ?_, β₀, hβ₀.le, ?_⟩
    · rw [h α]
      exact Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    · rw [h β₀, hβ₀τ]
  · -- `ξ(α) = −α(τ)`: `|ξ(α)| = |α(τ)|`, and take `β = −β₀`
    refine ⟨fun α => ?_, -β₀, ?_, ?_⟩
    · rw [h α, abs_neg]
      exact Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    · rw [covectorEuclideanNorm_neg]
      exact hβ₀.le
    · rw [h (-β₀), ContinuousAlternatingMap.neg_apply, hβ₀τ, neg_neg]

/-- **Mass bound for an integer combination** (Simon Ch. 6, Remark 3.2(1)): if
`1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e. for integer multiplicity triples
`R = (M, θ, ξ)`, `R₁ = (M₁, θ₁, ξ₁)`, `R₂ = (M₂, θ₂, ξ₂)`, then `μ_R ≤ |p₁| μ_{R₁} + |p₂| μ_{R₂}`.
At a.e. `x ∈ M`, `regcomp_unit_orientation_pairing` gives `β` with `|β|_E ≤ 1` and
`ξ(x)(β) = 1`, and `|ξᵢ(x)(β)| ≤ |β|_E ≤ 1` at a.e. `x ∈ Mᵢ`; evaluating the identity at `β`
gives `1_M θ ≤ |p₁| 1_{M₁} θ₁ + |p₂| 1_{M₂} θ₂` a.e.  Since `μ_{R'}` has density `1_{M'} θ'` with
respect to `Hⁿ`, this bound integrates to the claim. -/
theorem Submission.dor_lmb_ic_measure_le_of_weighted_orient_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → R.measure ≤ (p₁.natAbs : ℝ≥0∞) • R₁.measure + (p₂.natAbs : ℝ≥0∞) • R₂.measure := by
  intro P n U R₁ R₂ R p₁ p₂ h
  -- Step 1: `Hⁿ`-a.e., `x ∈ M'` implies that `ξ'(x)` is a unit orientation
  have hor : ∀ R' : IMRep U n, ∀ᵐ x ∂μHE[n], x ∈ R'.carrier →
      ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (R'.orient x) Q := by
    intro R'
    filter_upwards [(ae_restrict_iff' R'.measurableSet_carrier).mp R'.orients] with x hx hxM
    obtain ⟨Q, -, hQ⟩ := hx hxM
    exact ⟨Q, hQ⟩
  -- Step 2: at such `x`, `|(1_{M'} θ' ξ')(x)(β)| ≤ 1_{M'} θ'(x)` whenever `|β|_E ≤ 1`
  have hone : ∀ (R' : IMRep U n) (x : Euclid P),
      (x ∈ R'.carrier → ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (R'.orient x) Q) →
      ∀ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 →
        |R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x β| ≤
          ((R'.carrier.indicator R'.mult x : ℕ) : ℝ) := by
    intro R' x hx β hβ
    by_cases hxM : x ∈ R'.carrier
    · obtain ⟨Q, hQ⟩ := hx hxM
      have hle :=
        ((Submission.regcomp_unit_orientation_pairing P n (R'.orient x) Q hQ).1 β).trans hβ
      rw [Set.indicator_of_mem hxM, Set.indicator_of_mem hxM, smul_apply, smul_eq_mul, abs_mul,
        Nat.abs_cast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hle
    · rw [Set.indicator_of_notMem hxM, Set.indicator_of_notMem hxM]
      simp
  -- Step 3: `μ_{R'}` has the measurable density `1_{M'} θ'` with respect to `Hⁿ`
  have hM : ∀ R' : IMRep U n,
      R'.measure = μHE[n].withDensity (R'.carrier.indicator fun x => (R'.mult x : ℝ≥0∞)) := by
    intro R'
    rw [IMRep.measure, withDensity_indicator R'.measurableSet_carrier]
  have hmeas : ∀ R' : IMRep U n, Measurable (R'.carrier.indicator fun x => (R'.mult x : ℝ≥0∞)) :=
    fun R' => (measurable_from_nat.comp R'.measurable_mult).indicator R'.measurableSet_carrier
  have hind : ∀ (R' : IMRep U n) (x : Euclid P), R'.carrier.indicator
      (fun y => (R'.mult y : ℝ≥0∞)) x = ((R'.carrier.indicator R'.mult x : ℕ) : ℝ≥0∞) := by
    intro R' x
    by_cases hxM : x ∈ R'.carrier
    · rw [Set.indicator_of_mem hxM, Set.indicator_of_mem hxM]
    · rw [Set.indicator_of_notMem hxM, Set.indicator_of_notMem hxM, Nat.cast_zero]
  -- Step 4: `|p₁| μ_{R₁} + |p₂| μ_{R₂}` has density `|p₁| 1_{M₁} θ₁ + |p₂| 1_{M₂} θ₂`, so it
  -- suffices to compare the densities `Hⁿ`-a.e.
  rw [hM R, hM R₁, hM R₂, ← withDensity_smul _ (hmeas R₁), ← withDensity_smul _ (hmeas R₂),
    ← withDensity_add_left ((hmeas R₁).const_smul _)]
  refine withDensity_mono ?_
  -- Step 5: `1_M θ ≤ |p₁| 1_{M₁} θ₁ + |p₂| 1_{M₂} θ₂` wherever the identity and Step 1 hold
  filter_upwards [h, hor R, hor R₁, hor R₂] with x hx h0 h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hind]
  by_cases hxM : x ∈ R.carrier
  swap
  · rw [Set.indicator_of_notMem hxM, Nat.cast_zero]
    exact zero_le
  -- evaluate the identity at a `β` with `|β|_E ≤ 1` and `ξ(x)(β) = 1`
  obtain ⟨Q, hQ⟩ := h0 hxM
  obtain ⟨-, β, hβ, hξβ⟩ := Submission.regcomp_unit_orientation_pairing P n (R.orient x) Q hQ
  have hev := congrArg (fun F : MultiVector P n => F β) hx
  simp only [Set.indicator_of_mem hxM, add_apply, smul_apply, smul_eq_mul, hξβ, mul_one] at hev
  have hreal : (R.mult x : ℝ) ≤ (p₁.natAbs : ℝ) * ((R₁.carrier.indicator R₁.mult x : ℕ) : ℝ) +
      (p₂.natAbs : ℝ) * ((R₂.carrier.indicator R₂.mult x : ℕ) : ℝ) := by
    rw [hev, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    calc (p₁ : ℝ) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x β +
          (p₂ : ℝ) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x β
        ≤ |(p₁ : ℝ)| * |R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x β| +
          |(p₂ : ℝ)| * |R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x β| := by
          rw [← abs_mul, ← abs_mul]
          exact add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ _ := by
          gcongr
          · exact hone R₁ x h1 β hβ
          · exact hone R₂ x h2 β hβ
  -- a real inequality between natural numbers
  have hnat : R.mult x ≤ p₁.natAbs * R₁.carrier.indicator R₁.mult x +
      p₂.natAbs * R₂.carrier.indicator R₂.mult x := by
    exact_mod_cast hreal
  rw [Set.indicator_of_mem hxM]
  exact_mod_cast hnat

/-- **Representations of the partial sums** (Simon Ch. 6, Lemma 3.13, steps 3–4): for integer
multiplicity triples `R r = (M_r, θ_r, ξ_r)` in an open `U` and every `q`, there is a triple
`R' = (M', θ', ξ')` with `1_{M'} θ' ξ' = ∑_{r<q} 1_{M_r} θ_r ξ_r` `Hⁿ`-a.e. and
`μ_{R'} ≤ ∑_{r<q} μ_{R r}`.  Induction on `q`: for `q = 0` take the empty triple `(∅, 0, 0)`; for
`q → q + 1`, `rsdic_exists_imrep_int_combination` with `p₁ = p₂ = 1` combines `R'` and `R q`, and
`dor_lmb_ic_measure_le_of_weighted_orient_eq` bounds the weight of the combination by
`μ_{R'} + μ_{R q}`. -/
theorem Submission.dor_lmb_fc_ims_partial_sum_reps : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → ∀ q : ℕ, ∃ R' : IMRep U n, (∀ᵐ x ∂μHE[n], R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x = ∑ r ∈ Finset.range q, (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x) ∧ R'.measure ≤ ∑ r ∈ Finset.range q, (R r).measure := by
  intro P n U R hU q
  induction q with
  | zero =>
    -- the empty triple `(∅, 0, 0)` has density `0` and weight `0`
    let R₀ : IMRep U n :=
      { carrier := ∅
        mult := fun _ => 0
        orient := fun _ => 0
        measurableSet_carrier := MeasurableSet.empty
        carrier_subset := empty_subset U
        rectifiable :=
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
        measurable_mult := measurable_const
        mult_pos := fun x hx => absurd hx (notMem_empty x)
        locallyIntegrable_mult := fun K _ _ => by simp
        aestronglyMeasurable_orient := aestronglyMeasurable_const
        orients := by simp }
    refine ⟨R₀, Eventually.of_forall fun x => by simp [R₀], ?_⟩
    simp [R₀, IMRep.measure]
  | succ q ih =>
    obtain ⟨R', hR', hR'μ⟩ := ih
    -- `R''` represents `1 • (density of R') + 1 • (density of R q)`
    obtain ⟨R'', hR''⟩ := Submission.rsdic_exists_imrep_int_combination P n U R' (R q) 1 1 hU
    refine ⟨R'', ?_, ?_⟩
    · filter_upwards [hR'', hR'] with x h₁ h₂
      rw [h₁, h₂, Finset.sum_range_succ]
      simp
    · have h := Submission.dor_lmb_ic_measure_le_of_weighted_orient_eq P n U R' (R q) R'' 1 1 hR''
      simp only [Int.natAbs_one, Nat.cast_one, one_smul] at h
      rw [Finset.sum_range_succ]
      exact h.trans (add_le_add hR'μ le_rfl)
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ

/-- **Lipschitz extension into `ℝᴾ` with a `√P` loss** (Simon Ch. 2, 1.2, applied to each
coordinate; used for the deformation theorem, Ch. 6, 5.1).  Each coordinate `x ↦ ψ(x)ᵢ` is
`K`-Lipschitz on `S` since `|vᵢ| ≤ |v|`; McShane's extension gives `K`-Lipschitz `gᵢ : ℝᴾ → ℝ`
with `gᵢ = ψ(·)ᵢ` on `S`, and `φ = (gᵢ)ᵢ` agrees with `ψ` on `S` and satisfies
`|φ(x) − φ(y)|² = Σᵢ |gᵢ(x) − gᵢ(y)|² ≤ P K² |x − y|²`. -/
theorem Submission.dor_lmb_fcd_sd_lipschitz_extend : ∀ (P : ℕ) (S : Set (Euclid P)) (ψ : Euclid P → Euclid P) (K : NNReal), LipschitzOnWith K ψ S → ∃ φ : Euclid P → Euclid P, LipschitzWith (NNReal.sqrt P * K) φ ∧ EqOn φ ψ S := by
  intro P S ψ K hψ
  -- each coordinate of `ψ` is `K`-Lipschitz on `S`, as `|v i| ≤ ‖v‖`
  have hcoord : ∀ i : Fin P, LipschitzOnWith K (fun x => ψ x i) S := fun i =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
      (PiLp.dist_apply_le (ψ x) (ψ y) i).trans (hψ.dist_le_mul x hx y hy)
  -- McShane extension of every coordinate
  choose g hg hgS using fun i => (hcoord i).extend_real
  refine ⟨fun x => WithLp.toLp 2 fun i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_,
    fun x hx => ?_⟩
  · -- `dist (φ x) (φ y) = √(Σᵢ dist (gᵢ x) (gᵢ y) ^ 2) ≤ √(P (K dist x y) ^ 2)`
    rw [EuclideanSpace.dist_eq]
    calc _ ≤ √(∑ _i : Fin P, ((K : ℝ) * dist x y) ^ 2) := by
          gcongr with i
          exact (hg i).dist_le_mul x y
      _ = ↑(NNReal.sqrt P * K) * dist x y := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity), NNReal.coe_mul,
            Real.coe_sqrt, NNReal.coe_natCast, mul_assoc]
  · -- agreement on `S`, coordinatewise
    ext i
    exact (hgS i hx).symm
/-- **Simon Ch. 6, 2.11 and 3.2(3)**: if `X = τ(M, θ, ξ)` in `ℝᴾ` and `X(ω) = 0` whenever
`spt ω` misses the closed set `F`, then `μ_R(ℝᴾ \ F) = 0` and `M(X) ≤ M_W(X)` for every open
`W ⊇ F`.  Admissible forms for `M_{ℝᴾ \ F}(X)` have support disjoint from `F`, so
`μ_R(ℝᴾ \ F) = M_{ℝᴾ \ F}(X) = 0`; then `M(X) = μ_R(ℝᴾ) ≤ μ_R(W) + μ_R(ℝᴾ \ W) = μ_R(W) = M_W(X)`. -/
theorem Submission.dor_lmb_fcd_sd_im_concentrated : ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (F : Set (Euclid P)), R.Represents X → IsClosed F → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F) → X ω = 0) → R.measure Fᶜ = 0 ∧ ∀ W : Set (Euclid P), IsOpen W → F ⊆ W → X.mass ≤ X.massOn W := by
  intro P k X R F hR hF hX
  -- `M_W(X) = μ_R(W)` for every open `W`
  have hmass := (Submission.dor_imrep_massOn_eq_measure_and_support P k univ X R isOpen_univ hR).1
  -- every admissible `ω` for `M_{Fᶜ}(X)` has `spt ω` disjoint from `F`, so `X(ω) = 0`
  have h0 : X.massOn Fᶜ = 0 := by
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (X ω) ≤ 0
    rw [hX ω (Set.subset_compl_iff_disjoint_right.mp hω.1), ENNReal.ofReal_zero]
  have hFc : R.measure Fᶜ = 0 := by
    rw [← hmass Fᶜ hF.isOpen_compl, h0]
  refine ⟨hFc, fun W hW hFW => ?_⟩
  -- `M(X) = μ_R(W ∪ Wᶜ) ≤ μ_R(W) + μ_R(Wᶜ)`, and `μ_R(Wᶜ) ≤ μ_R(Fᶜ) = 0`
  calc X.mass = R.measure (W ∪ Wᶜ) := by
        rw [Set.union_compl_self]
        exact hmass univ isOpen_univ
    _ ≤ R.measure W + R.measure Wᶜ := measure_union_le W Wᶜ
    _ = X.massOn W := by
        rw [measure_mono_null (Set.compl_subset_compl.mpr hFW) hFc, add_zero, hmass W hW]

/-- **A good slice in a prescribed interval of levels** (Simon Ch. 6, 4.10 and display (10) of the
proof of 5.1: Markov choice of the slicing level).  Let `T = τ(M, θ, ξ)` in `ℝᴾ`, `f` continuous,
and let `Pₜ` satisfy (H1) `∫ M_W(Pₜ) dt ≤ L M_W(T)` for open `W` and (H2) for a.e. `t`: `Pₜ` is
integer multiplicity, vanishes off `f⁻¹{t}` and is given by the slice formula.  Then some
`t ∈ (a, b)` satisfies (H2) and `(b - a) M(Pₜ) ≤ 2 L μ_T{a < f < b}`.
* `W = {a < f < b}` is open and `M_W(T) = μ_T(W)` by (C1), so (H1) gives
  `∫_{(a, b)} M_W(Pₜ) dt ≤ L μ_T(W)`.
* `dor_lmb_fcd_sd_markov_point` gives `t ∈ (a, b)` in the a.e. set of (H2) with
  `(b - a) M_W(Pₜ) ≤ 2 L μ_T(W)`.
* `Pₜ` is integer multiplicity and vanishes off the closed level set `f⁻¹{t} ⊆ W`, so
  `M(Pₜ) ≤ M_W(Pₜ)` by `dor_lmb_fcd_sd_im_concentrated`. -/
theorem Submission.dor_lmb_fcd_sd_good_slice : ∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (RT : IMRep (univ : Set (Euclid P)) (m + 1)) (RB : IMRep (univ : Set (Euclid P)) m) (f : Euclid P → ℝ) (L : NNReal) (Ps : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) m) (a b : ℝ), RT.Represents T → Continuous f → a < b → (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) → (∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ t ∈ Ioo a b, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) ∧ ENNReal.ofReal (b - a) * (Ps t).mass ≤ 2 * ((L : ℝ≥0∞) * RT.measure {x | a < f x ∧ f x < b}) := by
  intro P m T RT RB f L Ps a b hRT hf hab hH1 hH2
  -- Step 1: the strip `W = {a < f < b}` is open
  have hW : IsOpen {x : Euclid P | a < f x ∧ f x < b} :=
    (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  -- Step 2: (H1) and (C1) give `∫_{(a, b)} M_W(Pₜ) dt ≤ ∫ M_W(Pₜ) dt ≤ L μ_T(W)`
  obtain ⟨hgm, hgI⟩ := hH1 _ hW
  rw [(Submission.dor_imrep_massOn_eq_measure_and_support P (m + 1) univ T RT isOpen_univ
    hRT).1 _ hW] at hgI
  -- Step 3: Markov choice of `t ∈ (a, b)` in the a.e. set of (H2)
  obtain ⟨t, ht, ⟨⟨Rt, hRt⟩, hvan, hform⟩, hle⟩ := Submission.dor_lmb_fcd_sd_markov_point _ _ a b
    _ hab hgm hH2 ((setLIntegral_le_lintegral _ _).trans hgI)
  -- Step 4: `Pₜ` vanishes off the closed level set `f⁻¹{t} ⊆ W`, so `M(Pₜ) ≤ M_W(Pₜ)`
  have hmass := (Submission.dor_lmb_fcd_sd_im_concentrated P m (Ps t) Rt (f ⁻¹' {t}) hRt
    (isClosed_singleton.preimage hf) hvan).2 _ hW fun x (hx : f x = t) => ⟨hx ▸ ht.1, hx ▸ ht.2⟩
  -- Step 5: `(b - a) M(Pₜ) ≤ (b - a) M_W(Pₜ) ≤ 2 L μ_T(W)`
  exact ⟨t, ht, ⟨Rt, hRt⟩, hvan, hform, (mul_le_mul_right hmass _).trans hle⟩
/-- **Restriction of an integer multiplicity current to a Borel set** (Simon Ch. 6, 2.9, 3.1 and
3.2(3)), for `R = (M, θ, ξ)` in `ℝᴾ`.
(A) For a test form `β`, `x ↦ θ(x) ξ(x)(β(x))` is `Hᵏ`-integrable on `M`: `Hᵏ`-a.e. on `M`,
`|ξ(x)(α)| ≤ |α|`, so the integrand is bounded by `s θ 1_{spt β}` with `s = sup |β|`, and
`∫_{M ∩ spt β} θ dHᵏ < ∞`.
(B) If `X = τ(M, θ, ξ)` vanishes off the closed `F` and `B` is Borel, then `Y = τ(M ∩ B, θ, ξ)`
is integer multiplicity with `M(Y) = ∫_{M ∩ B} θ dHᵏ = μ_R(B)`, and `Y(ω) = 0` whenever `spt ω`
misses `F ∩ B`: `μ_R(Fᶜ) = 0` and `θ ≥ 1` on `M` give `Hᵏ(M ∖ F) = 0`, while the integrand
vanishes on `M ∩ B ∩ F`. -/
theorem Submission.dor_lmb_fcd_sd_im_restrict : ∀ (P k : ℕ) (R : IMRep (univ : Set (Euclid P)) k), (∀ β : DifferentialForm (Euclid P) k, IsTestForm β → IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (β x)) R.carrier μHE[k]) ∧ ∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (F B : Set (Euclid P)), R.Represents X → IsClosed F → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F) → X ω = 0) → MeasurableSet B → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) k, IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y ω = ∫ x in R.carrier ∩ B, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ Y.mass = R.measure B ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F ∩ B) → Y ω = 0 := by
  intro P k R
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  refine ⟨fun β hβ => ?_, fun X F B hX hF hXF hB => ?_⟩
  · -- (A), step 1: `x ↦ |β(x)|` is continuous with compact support, hence `|β| ≤ s`
    obtain ⟨hsmooth, hcpt⟩ := hβ
    have hSm : MeasurableSet (tsupport β) := (isClosed_tsupport β).measurableSet
    have hcont : Continuous fun α : Covector (Euclid P) k => covectorEuclideanNorm α := by
      unfold covectorEuclideanNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
      split_ifs
      · exact (continuous_eval_const _).pow 2
      · exact continuous_const
    obtain ⟨s, hs⟩ := (hcont.comp hsmooth.continuous).bddAbove_range_of_hasCompactSupport
      (hcpt.comp_left (covectorEuclideanNorm_zero P k))
    -- step 4: `x ↦ θ(x) ξ(x)(β(x))` is `Hᵏ⌞M`-a.e. strongly measurable
    have hev : Continuous fun p : MultiVector P k × Covector (Euclid P) k => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (β x))
        (μHE[k].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul
        (hev.comp_aestronglyMeasurable
          (R.aestronglyMeasurable_orient.prodMk hsmooth.continuous.aestronglyMeasurable))
    -- step 3: `s θ 1_{spt β}` is integrable on `M`, as `∫_{M ∩ spt β} θ dHᵏ < ∞`
    have hint : Integrable (fun x => s * (tsupport β).indicator (fun x => (R.mult x : ℝ)) x)
        (μHE[k].restrict R.carrier) := by
      refine Integrable.const_mul ?_ s
      rw [integrable_indicator_iff hSm, IntegrableOn, Measure.restrict_restrict hSm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[k].restrict (tsupport β ∩ R.carrier)) (f := fun x => (R.mult x : ℝ≥0∞))
        hθm.aemeasurable
        (by rw [inter_comm]; exact R.locallyIntegrable_mult _ hcpt (subset_univ _))
      simpa using h
    -- step 2: `|θ ξ(β)| ≤ θ |β| ≤ s θ 1_{spt β}` `Hᵏ⌞M`-a.e., by (IMC)(d)
    refine hint.mono' hmeas ?_
    filter_upwards [Submission.cmc_imRep_locality_restrict_sub.2.2.2 P k univ R] with x hx
    by_cases hxS : x ∈ tsupport β
    · rw [indicator_of_mem hxS, norm_mul, Real.norm_natCast, Real.norm_eq_abs, mul_comm s]
      exact mul_le_mul_of_nonneg_left ((hx (β x)).trans (hs (mem_range_self x)))
        (Nat.cast_nonneg _)
    · simp [indicator_of_notMem hxS, image_eq_zero_of_notMem_tsupport hxS]
  · -- (B), step 5: `θ Hᵏ⌞M` does not charge `Fᶜ`, so `Hᵏ(M ∖ F) = 0` as `θ ≥ 1` on `M`
    have hnull : μHE[k] (R.carrier ∩ Fᶜ) = 0 := by
      have h0 := (Submission.dor_lmb_fcd_sd_im_concentrated P k X R F hX hF hXF).1
      rw [IMRep.measure, withDensity_apply_eq_zero' hθm.aemeasurable,
        Measure.restrict_apply' R.measurableSet_carrier] at h0
      refine measure_mono_null ?_ h0
      intro x hx
      exact ⟨⟨by simpa using (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
    -- step 6: `Y = τ(M ∩ B, θ, ξ)` by (IMC)(b)
    obtain ⟨Y, R', hY, hcar, hmult, horient⟩ :=
      Submission.cmc_imRep_locality_restrict_sub.2.1 P k univ R B isOpen_univ hB
    have hrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y ω = ∫ x in R.carrier ∩ B,
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] := by
      intro ω
      rw [hY ω, IMRep.action, hcar, hmult, horient]
    refine ⟨Y, ⟨R', hY⟩, hrep, ?_, fun ω hω => ?_⟩
    · -- step 7: `M(Y) = μ_{R'}(ℝᴾ) = ∫_{M ∩ B} θ dHᵏ = μ_R(B)` by (C1)
      rw [GeometricCurrentOn.mass, (Submission.dor_imrep_massOn_eq_measure_and_support P k univ
        Y R' isOpen_univ hY).1 univ isOpen_univ]
      simp only [IMRep.measure, hcar, hmult]
      rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ hB, Measure.restrict_univ,
        Measure.restrict_restrict hB, inter_comm]
    · -- step 8: the integrand vanishes on `M ∩ B ∩ F`, and `(M ∩ B) ∖ F` is `Hᵏ`-null
      rw [hrep ω]
      refine integral_eq_zero_of_ae ?_
      rw [EventuallyEq, ae_restrict_iff' (R.measurableSet_carrier.inter hB)]
      refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hnull)
      obtain ⟨⟨hxM, hxB⟩, hne⟩ := Classical.not_imp.1 hx
      refine ⟨hxM, fun hxF => hne ?_⟩
      rw [image_eq_zero_of_notMem_tsupport (disjoint_right.1 hω ⟨hxF, hxB⟩), map_zero, mul_zero,
        Pi.zero_apply]
/-- **Simon Ch. 6, Lemma 3.13 (steps 5–7 of the proof)**: an `Hⁿ`-a.e. limit `η` of integer
multiplicity densities `D_q = 1_{N_q} ϑ_q ζ_q` of `IMRep`s `R_q = (N_q, ϑ_q, ζ_q)` in the open `U`,
whose weights `μ_{R_q}(K)` are bounded uniformly in `q` on each compact `K ⊆ U`, is itself the
density of an `IMRep` `R'`, and `R'` acts by `ω ↦ ∫ ⟨ω, η⟩ dHⁿ`.
* `N(ζ) = √|ζ(Lζ)|`, with `L` from `dor_ims_unitOrientation_dual`, is continuous with
  `N(cζ) = c` for unit orientations `ζ` and `c ≥ 0`; so `N(D_q) = 1_{N_q} ϑ_q ∈ ℕ` a.e., and these
  integers are eventually equal to `θ = ⌊N(η̃)⌋` (`η̃` a Borel version of `η`) off a Borel null set.
* `M = (⋃_q N_q) ∩ {θ ≥ 1}` and `ξ = η̃ / θ` on `M`; Fatou bounds `∫_{M ∩ K} θ dHⁿ` by the
  weight bound.
* On `M`, eventually `x ∈ N_q` with `TₓN_q = TₓM` (tangent locality), so `ζ_q(x) = ±e` orients
  `TₓM` and `ζ_q(x) = D_q(x) / θ(x) → ξ(x)`; hence `ξ(x) = ±e` orients `TₓM`.
* `D_{R'} = η` a.e., so the actions agree. -/
theorem Submission.dor_lmb_fc_ims_ae_limit_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n) (η : Euclid P → MultiVector P n), IsOpen U → (∀ᵐ x ∂μHE[n], Tendsto (fun q => (R q).carrier.indicator (fun y => ((R q).mult y : ℝ) • (R q).orient y) x) atTop (𝓝 (η x))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ q, (R q).measure K ≤ C) → ∃ R' : IMRep U n, (∀ᵐ x ∂μHE[n], R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x = η x) ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x, η x (ω x) ∂μHE[n] := by
  have hIMC := Submission.cmc_imRep_locality_restrict_sub
  have hUOD := Submission.dor_ims_unitOrientation_dual
  have hsign := Submission.rsdic_unitOrientation_eq_or_eq_neg
  intro P n U R η hU hconv hbound
  obtain ⟨L, hL⟩ := hUOD P n
  -- Step 0: the multiplicity functional N(ζ) = √|ζ(Lζ)|
  set N : MultiVector P n → ℝ := fun ζ => Real.sqrt |ζ (L ζ)| with hN
  have hN_cont : Continuous N := by
    have h1 : Continuous fun ζ : MultiVector P n => ζ (L ζ) :=
      isBoundedBilinearMap_apply.continuous.comp (continuous_id.prodMk L.continuous)
    exact Real.continuous_sqrt.comp (continuous_abs.comp h1)
  have hN_smul : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (c : ℝ),
      IsUnitOrientationOf ζ Q → 0 ≤ c → N (c • ζ) = c := by
    intro ζ Q c hζ hc
    have h1 := (hL ζ Q hζ).2.2
    have h2 : (c • ζ) (L (c • ζ)) = c * c := by
      rw [map_smul, smul_apply, map_smul, h1, smul_eq_mul, smul_eq_mul, mul_one]
    simp only [hN, h2]
    rw [abs_of_nonneg (mul_nonneg hc hc), Real.sqrt_mul_self hc]
  have hN_zero : N 0 = 0 := by simp [hN]
  -- densities and integer multiplicities
  set D : ℕ → Euclid P → MultiVector P n := fun q x =>
    (R q).carrier.indicator (fun y => ((R q).mult y : ℝ) • (R q).orient y) x with hD
  set b : ℕ → Euclid P → ℕ := fun q x => (R q).carrier.indicator (R q).mult x with hb
  have hb_meas : ∀ q, Measurable (b q) := fun q =>
    (R q).measurable_mult.indicator (R q).measurableSet_carrier
  have hor : ∀ q, ∀ᵐ x ∂μHE[n], x ∈ (R q).carrier → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R q).carrier x Q ∧ IsUnitOrientationOf ((R q).orient x) Q :=
    fun q => (ae_restrict_iff' (R q).measurableSet_carrier).1 (R q).orients
  -- Step 1: N(D_q(x)) = b_q(x) a.e.
  have hND : ∀ q, ∀ᵐ x ∂μHE[n], N (D q x) = (b q x : ℝ) := by
    intro q
    filter_upwards [hor q] with x hx
    by_cases hxM : x ∈ (R q).carrier
    · obtain ⟨Q, -, hQ⟩ := hx hxM
      simp only [hD, hb, Set.indicator_of_mem hxM]
      exact hN_smul _ Q _ hQ (Nat.cast_nonneg _)
    · simp only [hD, hb, Set.indicator_of_notMem hxM, Nat.cast_zero]
      exact hN_zero
  -- Step 2: a Borel version of η
  have hmult_meas : ∀ q, Measurable (fun y => ((R q).mult y : ℝ)) := fun q =>
    measurable_from_nat.comp (R q).measurable_mult
  have hD_meas : ∀ q, AEStronglyMeasurable (D q) μHE[n] := fun q =>
    (aestronglyMeasurable_indicator_iff (R q).measurableSet_carrier).2
      ((hmult_meas q).aestronglyMeasurable.smul (R q).aestronglyMeasurable_orient)
  have hmetr : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  have hη_meas : AEStronglyMeasurable η μHE[n] :=
    aestronglyMeasurable_of_tendsto_ae atTop hD_meas hconv
  set ηt := hη_meas.mk η with hηt
  have hηt_sm : StronglyMeasurable ηt := hη_meas.stronglyMeasurable_mk
  have hηt_ae : η =ᵐ[μHE[n]] ηt := hη_meas.ae_eq_mk
  -- Step 3: the good set and a Borel null set Z₀ containing its complement
  set G : Set (Euclid P) := {x | η x = ηt x ∧ Tendsto (fun q => D q x) atTop (𝓝 (η x)) ∧
    ∀ q, N (D q x) = (b q x : ℝ) ∧ (x ∈ (R q).carrier → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R q).carrier x Q ∧
        IsUnitOrientationOf ((R q).orient x) Q)} with hG
  have hG_ae : ∀ᵐ x ∂μHE[n], x ∈ G := by
    have h3 := ae_all_iff.2 fun q => (hND q).and (hor q)
    filter_upwards [hηt_ae, hconv, h3] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set Z₀ := toMeasurable μHE[n] Gᶜ with hZ₀
  have hZ₀_meas : MeasurableSet Z₀ := measurableSet_toMeasurable _ _
  have hZ₀_null : μHE[n] Z₀ = 0 := by
    rw [hZ₀, measure_toMeasurable]
    exact hG_ae
  have hgood : ∀ x, x ∉ Z₀ → x ∈ G := fun x hx => by
    by_contra h
    exact hx (subset_toMeasurable _ _ h)
  -- Step 4: integer limits
  have nat_stab : ∀ (c : ℕ → ℕ) (a : ℝ), Tendsto (fun q => (c q : ℝ)) atTop (𝓝 a) →
      ∃ q₀, (∀ q ≥ q₀, c q = c q₀) ∧ a = c q₀ := by
    intro c a h
    obtain ⟨q₀, hq₀⟩ := (Metric.tendsto_atTop.1 h) (1 / 2) (by norm_num)
    have hconst : ∀ q ≥ q₀, c q = c q₀ := by
      intro q hq
      have h1 := hq₀ q hq
      have h2 := hq₀ q₀ le_rfl
      rw [Real.dist_eq] at h1 h2
      have h3 : |(c q : ℝ) - (c q₀ : ℝ)| < 1 := by
        calc |(c q : ℝ) - (c q₀ : ℝ)| = |((c q : ℝ) - a) - ((c q₀ : ℝ) - a)| := by ring_nf
          _ ≤ |(c q : ℝ) - a| + |(c q₀ : ℝ) - a| := abs_sub _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
          _ = 1 := by norm_num
      have h4 : |((c q : ℤ) - (c q₀ : ℤ))| < 1 := by
        have : (((c q : ℤ) - (c q₀ : ℤ) : ℤ) : ℝ) = (c q : ℝ) - (c q₀ : ℝ) := by push_cast; ring
        rw [← Int.cast_lt (R := ℝ), Int.cast_abs, this]
        simpa using h3
      have h5 := Int.abs_lt_one_iff.1 h4
      omega
    refine ⟨q₀, hconst, ?_⟩
    have h5 : Tendsto (fun q => (c q : ℝ)) atTop (𝓝 (c q₀ : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop q₀] with q hq
      rw [hconst q hq]
    exact tendsto_nhds_unique h h5
  have hstab : ∀ x ∈ G, ∃ q₀, (∀ q ≥ q₀, b q x = b q₀ x) ∧ N (η x) = (b q₀ x : ℝ) := by
    intro x hx
    have h1 : Tendsto (fun q => N (D q x)) atTop (𝓝 (N (η x))) :=
      (hN_cont.tendsto _).comp hx.2.1
    have h2 : Tendsto (fun q => (b q x : ℝ)) atTop (𝓝 (N (η x))) :=
      h1.congr fun q => (hx.2.2 q).1
    exact nat_stab (fun q => b q x) _ h2
  -- the multiplicity θ, the carrier M₊ and the orientation ξ
  set θ : Euclid P → ℕ := Z₀ᶜ.indicator (fun y => ⌊N (ηt y)⌋₊) with hθ
  have hθ_meas : Measurable θ :=
    (Measurable.comp (show Measurable (Nat.floor : ℝ → ℕ) from Nat.floor_mono.measurable)
      (hN_cont.measurable.comp hηt_sm.measurable)).indicator hZ₀_meas.compl
  have hθ_good : ∀ x, x ∉ Z₀ → ∃ q₀, (∀ q ≥ q₀, b q x = θ x) := by
    intro x hx
    obtain ⟨q₀, hq₀, hNη⟩ := hstab x (hgood x hx)
    refine ⟨q₀, fun q hq => ?_⟩
    have h1 : θ x = b q₀ x := by
      simp only [hθ, Set.indicator_of_mem (show x ∈ Z₀ᶜ from hx)]
      rw [← (hgood x hx).1, hNη, Nat.floor_natCast]
    rw [h1, hq₀ q hq]
  set M : Set (Euclid P) := (⋃ q, (R q).carrier) ∩ Z₀ᶜ ∩ {x | 1 ≤ θ x} with hM
  have hM_meas : MeasurableSet M :=
    ((MeasurableSet.iUnion fun q => (R q).measurableSet_carrier).inter hZ₀_meas.compl).inter
      (hθ_meas (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ k})))
  have hMU : M ⊆ U := fun x hx => by
    obtain ⟨q, hq⟩ := mem_iUnion.1 hx.1.1
    exact (R q).carrier_subset hq
  set ξ : Euclid P → MultiVector P n := M.indicator (fun x => ((θ x : ℝ))⁻¹ • ηt x) with hξ
  have hθr_meas : Measurable (fun x => ((θ x : ℝ))⁻¹) :=
    (measurable_from_nat.comp hθ_meas : Measurable (fun x => (θ x : ℝ))).inv
  have hξ_sm : StronglyMeasurable ξ :=
    (hθr_meas.stronglyMeasurable.smul hηt_sm).indicator hM_meas
  -- Step 6: Fatou and local finiteness
  have hmeasK : ∀ q (K : Set (Euclid P)), MeasurableSet K →
      (R q).measure K = ∫⁻ x, K.indicator (fun y => (b q y : ℝ≥0∞)) x ∂μHE[n] := by
    intro q K hKm
    have hNm := (R q).measurableSet_carrier
    have h1 : K.indicator (fun y => (b q y : ℝ≥0∞)) =
        (K ∩ (R q).carrier).indicator (fun y => ((R q).mult y : ℝ≥0∞)) := by
      funext y
      by_cases hyK : y ∈ K <;> by_cases hyN : y ∈ (R q).carrier <;> simp [hb, hyK, hyN]
    rw [h1, lintegral_indicator (hKm.inter hNm), IMRep.measure, withDensity_apply _ hKm,
      Measure.restrict_restrict hKm]
  have hM_lint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    obtain ⟨C, hC, hCq⟩ := hbound K hK hKU
    have hKm := hK.measurableSet
    have hpt : ∀ x, (M ∩ K).indicator (fun y => (θ y : ℝ≥0∞)) x ≤
        liminf (fun q => K.indicator (fun y => (b q y : ℝ≥0∞)) x) atTop := by
      intro x
      by_cases hx : x ∈ M ∩ K
      · rw [Set.indicator_of_mem hx]
        obtain ⟨q₀, hq₀⟩ := hθ_good x hx.1.1.2
        have hev : (fun q => K.indicator (fun y => (b q y : ℝ≥0∞)) x) =ᶠ[atTop]
            fun _ => (θ x : ℝ≥0∞) := by
          filter_upwards [eventually_ge_atTop q₀] with q hq
          rw [Set.indicator_of_mem hx.2, hq₀ q hq]
        rw [(tendsto_const_nhds.congr' hev.symm).liminf_eq]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    have hlt : ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≤ C := by
      calc ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n]
          = ∫⁻ x, (M ∩ K).indicator (fun y => (θ y : ℝ≥0∞)) x ∂μHE[n] :=
            (lintegral_indicator (hM_meas.inter hKm) _).symm
        _ ≤ ∫⁻ x, liminf (fun q => K.indicator (fun y => (b q y : ℝ≥0∞)) x) atTop ∂μHE[n] :=
            lintegral_mono hpt
        _ ≤ liminf (fun q => ∫⁻ x, K.indicator (fun y => (b q y : ℝ≥0∞)) x ∂μHE[n]) atTop :=
            lintegral_liminf_le fun q =>
              ((measurable_from_nat.comp (hb_meas q) : Measurable (fun y => (b q y : ℝ≥0∞)))).indicator hKm
        _ = liminf (fun q => (R q).measure K) atTop := by
            congr 1
            funext q
            exact (hmeasK q K hKm).symm
        _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hCq)
    exact ne_top_of_le_ne_top hC hlt
  have hNq_fin : ∀ q (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] ((R q).carrier ∩ K) ≠ ∞ := by
    intro q K hK hKU
    refine ne_top_of_le_ne_top ((R q).locallyIntegrable_mult K hK hKU) ?_
    calc μHE[n] ((R q).carrier ∩ K) = ∫⁻ _ in (R q).carrier ∩ K, 1 ∂μHE[n] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in (R q).carrier ∩ K, ((R q).mult x : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_mono' ((R q).measurableSet_carrier.inter hK.measurableSet)
          intro x hx
          exact_mod_cast (R q).mult_pos x hx.1
  have hM_fin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hM_lint K hK hKU) ?_
    calc μHE[n] (M ∩ K) = ∫⁻ _ in M ∩ K, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in M ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_mono' (hM_meas.inter hK.measurableSet)
          intro x hx
          exact_mod_cast hx.1.2
  -- Step 7: orientation
  have htan : ∀ q, ∀ᵐ x ∂μHE[n], x ∈ M ∩ (R q).carrier → ∀ Q : Submodule ℝ (Euclid P),
      (HasApproximateTangentSpaceAt n (M ∩ (R q).carrier) x Q ↔
        HasApproximateTangentSpaceAt n (R q).carrier x Q) ∧
      (HasApproximateTangentSpaceAt n (M ∩ (R q).carrier) x Q ↔
        HasApproximateTangentSpaceAt n M x Q) := by
    intro q
    have hMq := hM_meas.inter (R q).measurableSet_carrier
    have h1 := hIMC.1 P n U (M ∩ (R q).carrier) (R q).carrier hU hMq
      (R q).measurableSet_carrier inter_subset_right (R q).carrier_subset (hNq_fin q)
    have h2 := hIMC.1 P n U (M ∩ (R q).carrier) M hU hMq hM_meas inter_subset_left hMU hM_fin
    rw [ae_restrict_iff' hMq] at h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 hx Q
    exact ⟨hx1 hx Q, hx2 hx Q⟩
  have htan' := ae_all_iff.2 htan
  have horients : ∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ξ x) Q := by
    rw [ae_restrict_iff' hM_meas]
    filter_upwards [htan'] with x hx hxM
    have hxZ : x ∉ Z₀ := hxM.1.2
    have hxG := hgood x hxZ
    obtain ⟨q₀, hq₀⟩ := hθ_good x hxZ
    have hθpos : 1 ≤ θ x := hxM.2
    have hmem : ∀ q ≥ q₀, x ∈ (R q).carrier ∧ (R q).mult x = θ x := by
      intro q hq
      have h1 := hq₀ q hq
      by_cases hxq : x ∈ (R q).carrier
      · refine ⟨hxq, ?_⟩
        simpa [hb, hxq] using h1
      · exfalso
        simp only [hb, Set.indicator_of_notMem hxq] at h1
        omega
    have hTq : ∀ q ≥ q₀, ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf ((R q).orient x) Q := by
      intro q hq
      have hxq := (hmem q hq).1
      obtain ⟨Q, hQT, hQu⟩ := (hxG.2.2 q).2 hxq
      refine ⟨Q, ?_, hQu⟩
      have h := hx q ⟨hxM, hxq⟩ Q
      exact h.2.1 (h.1.2 hQT)
    obtain ⟨Q, hQT, hQu⟩ := hTq q₀ le_rfl
    set e := (R q₀).orient x with he
    have hpm : ∀ q ≥ q₀, (R q).orient x ∈ ({e, -e} : Set (MultiVector P n)) := by
      intro q hq
      obtain ⟨Q', hQ'T, hQ'u⟩ := hTq q hq
      have hQQ' : Q' = Q := hQ'T.unique hQT
      rw [hQQ'] at hQ'u
      rcases hsign P n e ((R q).orient x) Q hQu hQ'u with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hθx0 : (θ x : ℝ) ≠ 0 := by
      have : θ x ≠ 0 := by omega
      exact_mod_cast this
    have hlim : Tendsto (fun q => (R q).orient x) atTop (𝓝 (ξ x)) := by
      have h1 : Tendsto (fun q => ((θ x : ℝ))⁻¹ • D q x) atTop (𝓝 (((θ x : ℝ))⁻¹ • η x)) :=
        hxG.2.1.const_smul _
      have h2 : ξ x = ((θ x : ℝ))⁻¹ • η x := by
        simp only [hξ, Set.indicator_of_mem hxM, hxG.1]
      rw [h2]
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop q₀] with q hq
      obtain ⟨hxq, hmq⟩ := hmem q hq
      simp only [hD, Set.indicator_of_mem hxq, hmq, smul_smul, inv_mul_cancel₀ hθx0, one_smul]
    have hclosed : IsClosed ({e, -e} : Set (MultiVector P n)) :=
      (Set.toFinite _).isClosed
    have hξmem : ξ x ∈ ({e, -e} : Set (MultiVector P n)) :=
      hclosed.mem_of_tendsto hlim (eventually_atTop.2 ⟨q₀, hpm⟩)
    refine ⟨Q, hQT, ?_⟩
    rcases hξmem with h | h
    · rw [h]
      exact hQu
    · rw [Set.mem_singleton_iff.1 h]
      obtain ⟨τ, hτ, hspan, hs⟩ := hQu
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hs with hs | hs
      · right
        intro α
        rw [neg_apply, hs α]
      · left
        intro α
        rw [neg_apply, hs α, neg_neg]
  -- Step 8: the IMRep
  let R' : IMRep U n :=
    { carrier := M
      mult := θ
      orient := ξ
      measurableSet_carrier := hM_meas
      carrier_subset := hMU
      rectifiable := (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _
        fun q => (R q).rectifiable).mono fun x hx => hx.1.1
      measurable_mult := hθ_meas
      mult_pos := fun x hx => hx.2
      locallyIntegrable_mult := hM_lint
      aestronglyMeasurable_orient := hξ_sm.aestronglyMeasurable
      orients := horients }
  -- Step 9: the density of R' is η a.e., and the action formula
  have hdens : ∀ᵐ x ∂μHE[n], M.indicator (fun y => (θ y : ℝ) • ξ y) x = η x := by
    have hZ := measure_eq_zero_iff_ae_notMem.1 hZ₀_null
    filter_upwards [hZ] with x hxZ
    have hxG := hgood x hxZ
    by_cases hxM : x ∈ M
    · have hθ1 : 1 ≤ θ x := hxM.2
      have hθx0 : (θ x : ℝ) ≠ 0 := by
        have : θ x ≠ 0 := by omega
        exact_mod_cast this
      simp only [Set.indicator_of_mem hxM, hξ, smul_smul, mul_inv_cancel₀ hθx0, one_smul]
      exact hxG.1.symm
    · rw [Set.indicator_of_notMem hxM]
      obtain ⟨q₀, hq₀⟩ := hθ_good x hxZ
      have hzero : ∀ q ≥ q₀, D q x = 0 := by
        intro q hq
        by_cases hxq : x ∈ (R q).carrier
        · exfalso
          apply hxM
          refine ⟨⟨mem_iUnion.2 ⟨q, hxq⟩, hxZ⟩, ?_⟩
          show 1 ≤ θ x
          rw [← hq₀ q hq]
          simp only [hb, Set.indicator_of_mem hxq]
          exact (R q).mult_pos x hxq
        · simp only [hD, Set.indicator_of_notMem hxq]
      have h5 : Tendsto (fun q => D q x) atTop (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop q₀] with q hq
        rw [hzero q hq]
      exact tendsto_nhds_unique h5 hxG.2.1
  refine ⟨R', hdens, fun ω => ?_⟩
  show ∫ x in M, (θ x : ℝ) * ξ x (ω x) ∂μHE[n] = ∫ x, η x (ω x) ∂μHE[n]
  rw [← integral_indicator hM_meas]
  apply integral_congr_ae
  filter_upwards [hdens] with x hx
  rw [← hx]
  by_cases hxM : x ∈ M
  · simp only [Set.indicator_of_mem hxM, smul_apply, smul_eq_mul]
  · simp only [Set.indicator_of_notMem hxM, zero_apply]

/-- **Simon Ch. 6, Lemma 3.13 (p. 149), for the partial sums of a mass-summable series.**  If
`X_r ∈ 𝒟ₙ(U)` (`n = m + 1`, `U` open) are integer multiplicity with `Σ_r M(X_r) < ∞`, then
`Y(ω) = Σ_r X_r(ω)` is an integer multiplicity current with `M(Y) ≤ Σ_r M(X_r)`.
Write `X_r = τ(M_r, θ_r, ξ_r)`; by 3.2(3), `M(X_r) = μ_{X_r}(U)`, so the densities
`η_r = 1_{M_r} θ_r ξ_r` sum `Hⁿ`-a.e. to some `η` with `Σ_r X_r(ω) = ∫ ⟨ω, η⟩ dHⁿ`.  The partial
sums `Σ_{r<q} η_r` are `Hⁿ`-a.e. the densities of triples `R'_q` with `μ_{R'_q} ≤ Σ_{r<q} μ_{X_r}`;
they converge to `η` with locally bounded masses, so `η` is the density of a triple `(M₊, θ, ξ)`
and `Y = τ(M₊, θ, ξ)`.  An admissible `ω` has `Y(ω) = Σ_r X_r(ω) ≤ Σ_r M(X_r)`. -/
theorem Submission.dor_lmb_fc_im_series : ∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass := by
  intro P m U X hU hX hfin
  -- Step 2: triples `R_r = (M_r, θ_r, ξ_r)` with `X_r = τ(R_r)`; `M(X_r) = μ_{R_r}(U)` (3.2(3))
  have hX' : ∀ r, ∃ R : IMRep U (m + 1), R.Represents (X r) := hX
  choose R hR using hX'
  have hmass : ∀ r, (X r).mass = (R r).measure U := fun r =>
    (Submission.dor_imrep_massOn_eq_measure_and_support P (m + 1) U (X r) (R r) hU (hR r)).1 U hU
  have hfin' : ∑' r, (R r).measure U ≠ ∞ := by simpa only [hmass] using hfin
  -- `η = Σ_r 1_{M_r} θ_r ξ_r` converges `Hⁿ`-a.e., and `Σ_r X_r(ω) = ∫ ⟨ω, η⟩ dHⁿ`
  obtain ⟨η, hη, hηω⟩ := Submission.dor_lmb_fc_ims_density_series P (m + 1) U R hfin'
  -- Steps 3–4: the partial sums `Y_q = Σ_{r<q} X_r` are represented by triples `R'_q` with
  -- density `Σ_{r<q} 1_{M_r} θ_r ξ_r` `Hⁿ`-a.e. and `μ_{R'_q} ≤ Σ_{r<q} μ_{R_r}`
  choose R' hR'η hR'μ using Submission.dor_lmb_fc_ims_partial_sum_reps P (m + 1) U R hU
  -- the densities of the `R'_q` converge to `η` `Hⁿ`-a.e.
  have hconv : ∀ᵐ x ∂μHE[m + 1], Tendsto (fun q => (R' q).carrier.indicator
      (fun y => ((R' q).mult y : ℝ) • (R' q).orient y) x) atTop (𝓝 (η x)) := by
    filter_upwards [hη, ae_all_iff.2 hR'η] with x hx hx'
    exact hx.tendsto_sum_nat.congr fun q => (hx' q).symm
  -- `μ_{R'_q}(K) ≤ Σ_{r<q} μ_{R_r}(U) ≤ Σ_r μ_{R_r}(U) < ∞` for compact `K ⊆ U`
  have hbound : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ q, (R' q).measure K ≤ C := by
    intro K _ hKU
    refine ⟨∑' r, (R r).measure U, hfin', fun q => ?_⟩
    calc (R' q).measure K ≤ (∑ r ∈ Finset.range q, (R r).measure) K :=
          Measure.le_iff'.1 (hR'μ q) K
      _ = ∑ r ∈ Finset.range q, (R r).measure K := Measure.finsetSum_apply _ _ _
      _ ≤ ∑ r ∈ Finset.range q, (R r).measure U :=
          Finset.sum_le_sum fun r _ => measure_mono hKU
      _ ≤ ∑' r, (R r).measure U := ENNReal.sum_le_tsum _
  -- Steps 5–7: a triple `R★ = (M₊, θ, ξ)` with density `η`, so `τ(R★)(ω) = ∫ ⟨ω, η⟩ dHⁿ`
  obtain ⟨Rs, -, hRs⟩ :=
    Submission.dor_lmb_fc_ims_ae_limit_imrep P (m + 1) U R' η hU hconv hbound
  -- `Y = τ(R★)`: the restriction of `R★` to `E = ℝᴾ` represents a current `Y`
  obtain ⟨Y, R₀, hY, hcar, hmult, hor⟩ :=
    Submission.cmc_imRep_locality_restrict_sub.2.1 P (m + 1) U Rs univ hU MeasurableSet.univ
  have hYω : ∀ ω : TestFormOn U (m + 1),
      Y ω = ∫ x, η x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] := by
    intro ω
    rw [hY ω, ← hRs (ω : DifferentialForm (Euclid P) (m + 1))]
    simp only [IMRep.action, hcar, hmult, hor, inter_univ]
  -- Step 1: `Σ_r X_r(ω) = Σ_r τ(R_r)(ω)` converges to `∫ ⟨ω, η⟩ dHⁿ = Y(ω)`
  have hsum : ∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω) := by
    intro ω
    have hXR : (fun r => X r ω) =
        fun r => (R r).action (ω : DifferentialForm (Euclid P) (m + 1)) := funext fun r => hR r ω
    rw [hXR, hYω ω]
    exact hηω ω
  refine ⟨Y, ⟨R₀, hY⟩, hsum, ?_⟩
  -- Step 1: for admissible `ω`, `X_r(ω) ≤ M(X_r) < ∞`, so `Y(ω) = Σ_r X_r(ω) ≤ Σ_r M(X_r)`
  have hne : ∀ r, (X r).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hfin
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (Y ω) ≤ ∑' r, (X r).mass
  rw [ENNReal.ofReal_le_iff_le_toReal hfin, ENNReal.tsum_toReal_eq hne]
  exact hasSum_le (fun r => (ENNReal.ofReal_le_iff_le_toReal (hne r)).1 ((X r).le_massOn hω))
    (hsum ω) (ENNReal.summable_toReal hfin).hasSum

/-- **Lipschitz push-forward of a finite-mass integer multiplicity triple** (Simon Ch. 6,
3.3–3.9 with Remark 2.24 and Lemma 2.29).  For `R = (M, θ, ξ)` with `μ_R(ℝᴺ) < ∞` there is
`F ↦ Y(F)` with `Y(F)` integer multiplicity for Lipschitz `F`, `R(Fⱼ^#ω) → Y(F)(ω)` for
`C¹` maps `Fⱼ → F` uniformly with a common Lipschitz constant, and `Y(F) = Y(F')` when
`F = F'` `Hᵏ`-a.e. on `M`.
* `k = 0`: `dor_lmb_fcd_imp_degree_zero`.
* `k = d ≥ 1`: `dor_lmb_fcd_imp_parametric_rep` gives `Gᵢ`, `Bᵢ`, integer `wᵢ` with
  `R(γ) = ∑ᵢ ∫_{Bᵢ} wᵢ γ(Gᵢ)(DGᵢ e)` for bounded continuous `γ` and
  `∑ᵢ mᵢ ≤ μ_R(ℝᴺ)`, `mᵢ = ∫⁻_{Bᵢ} |wᵢ| J_{Gᵢ}`.  For Lipschitz `F`, (IMS) and (IMC) give the
  integer multiplicity `Y(F)` of `dor_lmb_fcd_imp_image_series_im` with
  `Y(F)(ω) = ∑ᵢ Tᵢ(F)(ω)`, `Tᵢ(F)(ω) = ∫_{Bᵢ} wᵢ ω(F ∘ Gᵢ)(D(F ∘ Gᵢ) e)`; `Y(F) = 0` otherwise.
* Limit: `Fⱼ^#ω` is continuous and bounded by `sup |ω| Λᵈ`, and the chain rule on `Bᵢ` gives
  `R(Fⱼ^#ω) = ∑ᵢ Tᵢ(Fⱼ)(ω)`; `Tᵢ(Fⱼ)(ω) → Tᵢ(F)(ω)` by the weak continuity of pulled-back forms
  (`dor_lmb_fcd_jacobian_weak_continuity`), and `|Tᵢ(Fⱼ)(ω)| ≤ c Λᵈ mᵢ` is summable, so dominated
  convergence for series (the counting measure) gives `R(Fⱼ^#ω) → Y(F)(ω)`.
* Locality: `F ∘ Gᵢ = F' ∘ Gᵢ` a.e. on `Bᵢ` (pull-back of `Hᵏ⌞M`-null sets), hence
  `D(F ∘ Gᵢ) = D(F' ∘ Gᵢ)` a.e. on `Bᵢ` (`dor_lmb_fcd_imp_lipschitz_jacobian_locality`), so
  `Tᵢ(F) = Tᵢ(F')` and `Y(F) = Y(F')`. -/
theorem Submission.dor_lmb_fcd_im_pushforward : (∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F' := by
  intro hIMS N N' k R hR
  obtain _ | k := k
  · exact Submission.dor_lmb_fcd_imp_degree_zero N N' R hR
  -- the parametric representation `R(γ) = ∑ᵢ ∫_{Bᵢ} wᵢ γ(Gᵢ)(DGᵢ e)`, `∑ᵢ mᵢ ≤ μ_R(ℝᴺ) < ∞`
  obtain ⟨G, B, w, hGlip, hBm, hGd, hwm, hwZ, hw0, hwi, hsum, hact, hpull⟩ :=
    Submission.dor_lmb_fcd_imp_parametric_rep N (k + 1) R hR
  choose L hL using hGlip
  have hfin := ne_top_of_le_ne_top hR hsum
  -- `Y(F)`: the integer multiplicity sum `∑ᵢ Tᵢ(F)` for Lipschitz `F`, and `0` otherwise
  have hex : ∀ F : Euclid N → Euclid N', ∃ Y : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1),
      ∀ Λ : NNReal, LipschitzWith Λ F → IsIntegerMultiplicity Y ∧
        ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), HasSum (fun i => ∫ u in B i, w i u *
          (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)
            (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))) (Y ω) := by
    intro F
    by_cases hF : ∃ Λ : NNReal, LipschitzWith Λ F
    · obtain ⟨Λ, hΛ⟩ := hF
      obtain ⟨Y, hYIM, hYω, -⟩ := Submission.dor_lmb_fcd_imp_image_series_im hIMS
        Submission.cmc_imRep_locality_restrict_sub N N' k G B w F Λ (fun i => ⟨L i, hL i⟩) hBm
        hGd hwm hwZ hw0 hwi hfin hΛ
      exact ⟨Y, fun _ _ => ⟨hYIM, hYω⟩⟩
    · exact ⟨0, fun Λ hΛ => absurd ⟨Λ, hΛ⟩ hF⟩
  choose Y hY using hex
  refine ⟨Y, fun F Λ hF => ⟨(hY F Λ hF).1, ?_⟩, ?_⟩
  · intro Fs hFs hFsL hFsU ω
    have hωc : Continuous (ω : DifferentialForm (Euclid N') (k + 1)) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    -- `Tᵢ(Fⱼ)(ω)`, `Tᵢ(F)(ω)` and `mᵢ`
    let f : ℕ → ℕ → ℝ := fun j i => ∫ u in B i, w i u *
      (ω : DifferentialForm (Euclid N') (k + 1)) ((Fs j ∘ G i) u)
        (fun a => fderiv ℝ (Fs j ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))
    let g : ℕ → ℝ := fun i => ∫ u in B i, w i u *
      (ω : DifferentialForm (Euclid N') (k + 1)) ((F ∘ G i) u)
        (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a (1 : ℝ)))
    let m : ℕ → ℝ := fun i => (∫⁻ u in B i, ‖w i u‖ₑ * ENNReal.ofReal (Real.sqrt (Matrix.det
      (Matrix.of fun a b : Fin (k + 1) =>
        inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a (1 : ℝ)))
          (fderiv ℝ (G i) u (EuclideanSpace.single b (1 : ℝ))))))).toReal
    -- (a) `R(Fⱼ^#ω) = ∑ᵢ Tᵢ(Fⱼ)(ω)`: `Fⱼ^#ω` is continuous and bounded, and on `Bᵢ`
    -- `(Fⱼ^#ω)(Gᵢ)(DGᵢ e) = ω(Fⱼ ∘ Gᵢ)(D(Fⱼ ∘ Gᵢ) e)` by the chain rule
    have htr : ∀ j, HasSum (f j) (R.action (fun x =>
        ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x))) := by
      intro j
      have hγc : Continuous (fun x =>
          ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x)) :=
        (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
          ((hFs j).continuous_fderiv one_ne_zero)).clm_apply (hωc.comp (hFs j).continuous)
      have hγb : ∃ C' : ℝ, ∀ x,
          ‖((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x)‖ ≤ C' := by
        refine ⟨C * (Λ : ℝ) ^ (k + 1), fun x => ?_⟩
        refine (ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Fintype.card_fin]
        exact mul_le_mul (hC _)
          (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ (hFsL j)) _)
          (by positivity) ((norm_nonneg _).trans (hC 0))
      convert hact _ hγc hγb using 1
      funext i
      refine setIntegral_congr_fun (hBm i) fun u hu => ?_
      rw [fderiv_comp u ((hFs j).differentiable one_ne_zero (G i u)) (hGd i u hu)]
      rfl
    -- (b) `Tᵢ(Fⱼ)(ω) → Tᵢ(F)(ω)`: weak continuity of pulled-back forms
    have hterm : ∀ i, Tendsto (fun j => f j i) atTop (𝓝 (g i)) := fun i =>
      Submission.dor_lmb_fcd_jacobian_weak_continuity (k + 1) N' (B i) (w i) (Λ * L i)
        (fun j => Fs j ∘ G i) (F ∘ G i) ω (hBm i) (hwi i) (fun j => (hFsL j).comp (hL i))
        (hF.comp (hL i)) (hFsU.comp (G i))
    -- (c) `|Tᵢ(Fⱼ)(ω)| ≤ c Λᵈ mᵢ` with `c > sup |ω|`
    have hcont : Continuous fun α : Covector (Euclid N') (k + 1) => covectorEuclideanNorm α := by
      unfold covectorEuclideanNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
      split_ifs
      · exact (continuous_eval_const _).pow 2
      · exact continuous_const
    obtain ⟨c, hc⟩ := (hcont.comp hωc).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero N' (k + 1)))
    have hc' : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) x) ≤
        max c 0 + 1 := by
      intro x
      have := hc x
      rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
      linarith [le_max_left c 0]
    have hbd : ∀ j i, ‖f j i‖ ≤ (max c 0 + 1) * (Λ : ℝ) ^ (k + 1) * m i := by
      intro j
      obtain ⟨-, -, -, hb⟩ := Submission.dor_lmb_fcd_imp_image_series_im hIMS
        Submission.cmc_imRep_locality_restrict_sub N N' k G B w (Fs j) Λ (fun i => ⟨L i, hL i⟩)
        hBm hGd hwm hwZ hw0 hwi hfin (hFsL j)
      intro i
      rw [Real.norm_eq_abs]
      exact hb ω _ (by positivity) hc' i
    have hbs : Summable fun i => (max c 0 + 1) * (Λ : ℝ) ^ (k + 1) * m i :=
      (ENNReal.summable_toReal hfin).mul_left _
    -- (d) dominated convergence for series, via the counting measure on `ℕ`
    have hbi : Integrable (fun i => (max c 0 + 1) * (Λ : ℝ) ^ (k + 1) * m i) Measure.count := by
      rw [integrable_count_iff]
      refine hbs.congr fun i => ?_
      exact (Real.norm_of_nonneg ((norm_nonneg _).trans (hbd 0 i))).symm
    have hfi : ∀ j, Integrable (f j) Measure.count := fun j =>
      hbi.mono' (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ (hbd j))
    have hgi : Integrable g Measure.count :=
      hbi.mono' (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun i =>
        le_of_tendsto (tendsto_norm.comp (hterm i)) (Eventually.of_forall fun j => hbd j i))
    have hlim := tendsto_integral_of_dominated_convergence _
      (fun j => (hfi j).aestronglyMeasurable) hbi (fun j => ae_of_all _ (hbd j))
      (ae_of_all _ hterm)
    have e1 : ∀ j, ∫ i, f j i ∂Measure.count = R.action (fun x =>
        ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x)) := by
      intro j
      rw [integral_countable (hfi j)]
      simp only [count_real_singleton, one_smul]
      exact (htr j).tsum_eq
    have e2 : ∫ i, g i ∂Measure.count = Y F ω := by
      rw [integral_countable hgi]
      simp only [count_real_singleton, one_smul]
      exact ((hY F Λ hF).2 ω).tsum_eq
    rw [e2] at hlim
    exact hlim.congr e1
  · -- locality: `F ∘ Gᵢ = F' ∘ Gᵢ` and `D(F ∘ Gᵢ) = D(F' ∘ Gᵢ)` a.e. on `Bᵢ`
    intro F F' Λ hF hF' hae
    ext ω
    refine ((hY F Λ hF).2 ω).unique ?_
    convert (hY F' Λ hF').2 ω using 1
    funext i
    have h1 : ∀ᵐ u ∂(volume.restrict (B i)), (F ∘ G i) u = (F' ∘ G i) u :=
      hpull (fun x => F x = F' x) hae i
    have h2 := (Submission.dor_lmb_fcd_imp_lipschitz_jacobian_locality).2 (k + 1) N' (F ∘ G i)
      (F' ∘ G i) (B i) (Λ * L i) (Λ * L i) (hF.comp (hL i)) (hF'.comp (hL i)) (hBm i) h1
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with u hu1 hu2
    rw [hu1, hu2]

/-- **Shells along the level sets of `f`** (Simon Ch. 6, proof of the Deformation Theorem 5.1:
the shells `T_ρ − T_{ρ/2}` of (8)–(13), here cut along the level sets of `f`).  Let
`T = τ(M, θ, ξ)` vanish off the closed set `K`, `∂T = τ(M', θ', ξ')`, and let
`Zⱼ = ∂(T⌞{f < rⱼ}) − (∂T)⌞{f < rⱼ}` (the slice `⟨T, f, rⱼ−⟩` of 4.6), i.e.
`Zⱼ(ω) = ∫_{M ∩ {f < rⱼ}} θ⟨dω, ξ⟩ dHᵐ⁺¹ − ∫_{M' ∩ {f < rⱼ}} θ'⟨ω, ξ'⟩ dHᵐ`.  The shells
`Wⱼ = T⌞Sⱼ`, `Dⱼ = (∂T)⌞Sⱼ` (`S₀ = {f ≥ r₀}`, `Sⱼ₊₁ = {rⱼ₊₁ ≤ f < rⱼ}`) and `A_N = T⌞{f < r_N}`
are integer multiplicity with masses `μ_T(Sⱼ)`, `μ_{∂T}(Sⱼ)` and `μ_T({f < r_N})`.  Splitting the
integrals over `M` and `M'` along `{f < rⱼ}` gives `∂W₀ = D₀ − Z₀`, `∂Wⱼ₊₁ = Dⱼ₊₁ + Zⱼ − Zⱼ₊₁`
and `Σ_{j ≤ N} Wⱼ = T − A_N`.  `Wⱼ`, `Dⱼ` and (by induction on `j`, as `Eⱼ ⊆ Eⱼ₊₁` for antitone
`r`) `Zⱼ` vanish off `Eⱼ = K ∩ {f ≥ rⱼ}`. -/
theorem Submission.dor_lmb_fcd_sd_shells : ∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (RT : IMRep (univ : Set (Euclid P)) (m + 1)) (RB : IMRep (univ : Set (Euclid P)) m) (K : Set (Euclid P)) (f : Euclid P → ℝ) (r : ℕ → ℝ) (Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), RT.Represents T → RB.Represents T.boundary → IsClosed K → Continuous f → Antitone r → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (K) → T ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Z j ω = (∫ x in RT.carrier ∩ {x | f x < r j}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1]) - ∫ x in RB.carrier ∩ {x | f x < r j}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ (W A : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ j, IsIntegerMultiplicity (W j)) ∧ (∀ j, IsIntegerMultiplicity (D j)) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (K ∩ {x | r j ≤ f x}) → W j ω = 0) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (K ∩ {x | r j ≤ f x}) → D j ω = 0) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (K ∩ {x | r j ≤ f x}) → Z j ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) m, (W 0).boundary ω = D 0 ω - Z 0 ω) ∧ (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), (W (j + 1)).boundary ω = D (j + 1) ω + Z j ω - Z (j + 1) ω) ∧ (∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), ∑ j ∈ Finset.range (N + 1), W j ω = T ω - A N ω) ∧ (W 0).mass = RT.measure {x | r 0 ≤ f x} ∧ (∀ j, (W (j + 1)).mass = RT.measure {x | r (j + 1) ≤ f x ∧ f x < r j}) ∧ (D 0).mass = RB.measure {x | r 0 ≤ f x} ∧ (∀ j, (D (j + 1)).mass = RB.measure {x | r (j + 1) ≤ f x ∧ f x < r j}) ∧ ∀ N, (A N).mass = RT.measure {x | f x < r N} := by
  intro P m T RT RB K f r Z hRT hRB hK hf hr hTK hZ
  -- Step 1: `∂T` vanishes off `K`, because `spt dω ⊆ spt ω`
  have hbK : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) K → T.boundary ω = 0 := by
    intro ω hω
    rw [GeometricCurrentOn.boundary_apply]
    exact hTK _
      (hω.mono_left (tsupport_exteriorDerivative_subset (ω : DifferentialForm (Euclid P) m)))
  -- Step 2 (im_restrict (A)): `g_ω = θ⟨dω, ξ⟩` and `k_η = θ⟨η, ξ⟩` are integrable on `M`,
  -- `h_ω = θ'⟨ω, ξ'⟩` on `M'`
  obtain ⟨hintT, hresT⟩ := Submission.dor_lmb_fcd_sd_im_restrict P (m + 1) RT
  obtain ⟨hintB, hresB⟩ := Submission.dor_lmb_fcd_sd_im_restrict P m RB
  have hg : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, IntegrableOn (fun x => (RT.mult x : ℝ) *
      RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x)) RT.carrier
        μHE[m + 1] :=
    fun ω => hintT _ (exteriorDerivative_isTestForm ω.property.1)
  have hh : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, IntegrableOn (fun x => (RB.mult x : ℝ) *
      RB.orient x ((ω : DifferentialForm (Euclid P) m) x)) RB.carrier μHE[m] :=
    fun ω => hintB _ ω.property.1
  have hk : ∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), IntegrableOn (fun x =>
      (RT.mult x : ℝ) * RT.orient x ((η : DifferentialForm (Euclid P) (m + 1)) x)) RT.carrier
        μHE[m + 1] :=
    fun η => hintT _ η.property.1
  -- Step 3: `T(η) = ∫_M k_η` and `∂T(ω) = T(dω) = ∫_M g_ω = ∫_{M'} h_ω`
  have hTη : ∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), T η = ∫ x in RT.carrier,
      (RT.mult x : ℝ) * RT.orient x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
    hRT
  have hbT : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, T.boundary ω = ∫ x in RT.carrier,
      (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x)
        ∂μHE[m + 1] :=
    fun ω => hRT (exteriorDerivativeTestOn univ m ω)
  have hbB : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, T.boundary ω = ∫ x in RB.carrier,
      (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] :=
    hRB
  -- Step 4: splitting integrals along the (Borel) level sets of the continuous `f`
  have hle : ∀ a : ℝ, MeasurableSet {x | a ≤ f x} := fun a =>
    measurableSet_le measurable_const hf.measurable
  have hlt : ∀ a : ℝ, MeasurableSet {x | f x < a} := fun a =>
    measurableSet_lt hf.measurable measurable_const
  have hband : ∀ a b : ℝ, MeasurableSet {x | a ≤ f x ∧ f x < b} := fun a b =>
    (hle a).inter (hlt b)
  -- (i) `∫_{G ∩ {a ≤ f}} u = ∫_G u − ∫_{G ∩ {f < a}} u`
  have split₁ : ∀ (μ : Measure (Euclid P)) (G : Set (Euclid P)) (u : Euclid P → ℝ) (a : ℝ),
      IntegrableOn u G μ → ∫ x in G ∩ {x | a ≤ f x}, u x ∂μ =
        (∫ x in G, u x ∂μ) - ∫ x in G ∩ {x | f x < a}, u x ∂μ := by
    intro μ G u a hu
    have h := integral_inter_add_sdiff (hle a) hu
    have hd : G \ {x | a ≤ f x} = G ∩ {x | f x < a} := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_le]
    rw [hd] at h
    linarith
  -- (ii) for `b ≤ a`, `∫_{G ∩ {b ≤ f < a}} u = ∫_{G ∩ {f < a}} u − ∫_{G ∩ {f < b}} u`
  have split₂ : ∀ (μ : Measure (Euclid P)) (G : Set (Euclid P)) (u : Euclid P → ℝ) (a b : ℝ),
      b ≤ a → IntegrableOn u G μ → ∫ x in G ∩ {x | b ≤ f x ∧ f x < a}, u x ∂μ =
        (∫ x in G ∩ {x | f x < a}, u x ∂μ) - ∫ x in G ∩ {x | f x < b}, u x ∂μ := by
    intro μ G u a b hba hu
    have h := integral_inter_add_sdiff (hlt b)
      (hu.mono_set inter_subset_left : IntegrableOn u (G ∩ {x | f x < a}) μ)
    have h₁ : G ∩ {x | f x < a} ∩ {x | f x < b} = G ∩ {x | f x < b} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hx.2.trans_le hba⟩, hx.2⟩⟩
    have h₂ : (G ∩ {x | f x < a}) \ {x | f x < b} = G ∩ {x | b ≤ f x ∧ f x < a} := by
      ext x
      simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_lt]
      exact ⟨fun hx => ⟨hx.1.1, hx.2, hx.1.2⟩, fun hx => ⟨⟨hx.1, hx.2.2⟩, hx.2.1⟩⟩
    rw [h₁, h₂] at h
    linarith
  -- Step 5 (im_restrict (B)): the restrictions `T⌞B` and `(∂T)⌞B` to Borel sets `B`, which are
  -- integer multiplicity, have mass `μ_T(B)`, `μ_{∂T}(B)` and vanish off `K ∩ B`
  choose YT hYT_im hYT_eq hYT_mass hYT_van using
    fun (B : Set (Euclid P)) (hB : MeasurableSet B) => hresT T K B hRT hK hTK hB
  choose YB hYB_im hYB_eq hYB_mass hYB_van using
    fun (B : Set (Euclid P)) (hB : MeasurableSet B) => hresB T.boundary K B hRB hK hbK hB
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      W 0 = YT {x | r 0 ≤ f x} (hle (r 0)) ∧
        ∀ j, W (j + 1) = YT {x | r (j + 1) ≤ f x ∧ f x < r j} (hband _ _) :=
    ⟨fun j => Nat.casesOn j (YT {x | r 0 ≤ f x} (hle (r 0)))
      fun i => YT {x | r (i + 1) ≤ f x ∧ f x < r i} (hband _ _), rfl, fun _ => rfl⟩
  obtain ⟨D, hD0, hDs⟩ : ∃ D : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m,
      D 0 = YB {x | r 0 ≤ f x} (hle (r 0)) ∧
        ∀ j, D (j + 1) = YB {x | r (j + 1) ≤ f x ∧ f x < r j} (hband _ _) :=
    ⟨fun j => Nat.casesOn j (YB {x | r 0 ≤ f x} (hle (r 0)))
      fun i => YB {x | r (i + 1) ≤ f x ∧ f x < r i} (hband _ _), rfl, fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      ∀ N, A N = YT {x | f x < r N} (hlt (r N)) :=
    ⟨fun N => YT {x | f x < r N} (hlt (r N)), fun _ => rfl⟩
  -- Step 6: `Wⱼ` and `Dⱼ` vanish off `Eⱼ = K ∩ {rⱼ ≤ f}`, which contains `K ∩ Sⱼ`
  have hWv : ∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (K ∩ {x | r j ≤ f x}) →
        W j ω = 0 := by
    rintro (_ | j) ω hω
    · rw [hW0]
      exact hYT_van _ _ ω hω
    · rw [hWs]
      exact hYT_van _ _ ω (hω.mono_right (inter_subset_inter_right K fun x hx => hx.1))
  have hDv : ∀ j (ω : TestFormOn (univ : Set (Euclid P)) m),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (K ∩ {x | r j ≤ f x}) →
        D j ω = 0 := by
    rintro (_ | j) ω hω
    · rw [hD0]
      exact hYB_van _ _ ω hω
    · rw [hDs]
      exact hYB_van _ _ ω (hω.mono_right (inter_subset_inter_right K fun x hx => hx.1))
  -- Step 7: `∂W₀(ω) = ∫_M g_ω − ∫_{M ∩ {f < r₀}} g_ω = D₀(ω) − Z₀(ω)`
  have hbW0 : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, (W 0).boundary ω = D 0 ω - Z 0 ω := by
    intro ω
    have e₁ : (W 0).boundary ω = ∫ x in RT.carrier ∩ {x | r 0 ≤ f x}, (RT.mult x : ℝ) *
        RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x) ∂μHE[m + 1] := by
      rw [GeometricCurrentOn.boundary_apply, hW0, hYT_eq]
      rfl
    have e₂ : D 0 ω = ∫ x in RB.carrier ∩ {x | r 0 ≤ f x}, (RB.mult x : ℝ) *
        RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] := by
      rw [hD0, hYB_eq]
    rw [e₁, e₂, hZ 0 ω, split₁ _ _ _ (r 0) (hg ω), split₁ _ _ _ (r 0) (hh ω)]
    linarith [hbT ω, hbB ω]
  -- Step 8: `∂Wⱼ₊₁(ω) = ∫_{M ∩ {f < rⱼ}} g_ω − ∫_{M ∩ {f < rⱼ₊₁}} g_ω = Dⱼ₊₁(ω) + Zⱼ(ω) − Zⱼ₊₁(ω)`
  have hbWs : ∀ j (ω : TestFormOn (univ : Set (Euclid P)) m),
      (W (j + 1)).boundary ω = D (j + 1) ω + Z j ω - Z (j + 1) ω := by
    intro j ω
    have hrj : r (j + 1) ≤ r j := hr (Nat.le_succ j)
    have e₁ : (W (j + 1)).boundary ω = ∫ x in RT.carrier ∩ {x | r (j + 1) ≤ f x ∧ f x < r j},
        (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) m) x)
          ∂μHE[m + 1] := by
      rw [GeometricCurrentOn.boundary_apply, hWs, hYT_eq]
      rfl
    have e₂ : D (j + 1) ω = ∫ x in RB.carrier ∩ {x | r (j + 1) ≤ f x ∧ f x < r j},
        (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] := by
      rw [hDs, hYB_eq]
    rw [e₁, e₂, hZ j ω, hZ (j + 1) ω, split₂ _ _ _ (r j) (r (j + 1)) hrj (hg ω),
      split₂ _ _ _ (r j) (r (j + 1)) hrj (hh ω)]
    ring
  -- Step 9: `Σ_{j ≤ N} Wⱼ = T − A_N`, by induction on `N`
  have hsum : ∀ N (η : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      ∑ j ∈ Finset.range (N + 1), W j η = T η - A N η := by
    intro N η
    induction N with
    | zero =>
      rw [Finset.sum_range_one, hW0, hA, hYT_eq, hYT_eq, hTη, split₁ _ _ _ (r 0) (hk η)]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hWs, hA, hA, hYT_eq, hYT_eq, hYT_eq,
        split₂ _ _ _ (r N) (r (N + 1)) (hr (Nat.le_succ N)) (hk η)]
      ring
  -- Step 10: `Zⱼ` vanishes off `Eⱼ`, by induction on `j` (`Eⱼ ⊆ Eⱼ₊₁` as `r` is antitone)
  have hZv : ∀ j (ω : TestFormOn (univ : Set (Euclid P)) m),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (K ∩ {x | r j ≤ f x}) →
        Z j ω = 0 := by
    intro j
    induction j with
    | zero =>
      intro ω hω
      have h₁ : (W 0).boundary ω = 0 := by
        rw [GeometricCurrentOn.boundary_apply]
        exact hWv 0 _ (hω.mono_left
          (tsupport_exteriorDerivative_subset (ω : DifferentialForm (Euclid P) m)))
      linarith [hbW0 ω, hDv 0 ω hω]
    | succ j ih =>
      intro ω hω
      have h₁ : (W (j + 1)).boundary ω = 0 := by
        rw [GeometricCurrentOn.boundary_apply]
        exact hWv (j + 1) _ (hω.mono_left
          (tsupport_exteriorDerivative_subset (ω : DifferentialForm (Euclid P) m)))
      have h₂ : Z j ω = 0 := ih ω (hω.mono_right (inter_subset_inter_right K
        fun x hx => (hr (Nat.le_succ j)).trans hx))
      linarith [hbWs j ω, hDv (j + 1) ω hω]
  -- Step 11: integrality and masses of the shells (im_restrict (B))
  refine ⟨W, A, D, ?_, ?_, hWv, hDv, hZv, hbW0, hbWs, hsum, ?_, fun j => ?_, ?_, fun j => ?_,
    fun N => ?_⟩
  · rintro (_ | j)
    · rw [hW0]
      exact hYT_im _ _
    · rw [hWs]
      exact hYT_im _ _
  · rintro (_ | j)
    · rw [hD0]
      exact hYB_im _ _
    · rw [hDs]
      exact hYB_im _ _
  · rw [hW0]
    exact hYT_mass _ _
  · rw [hWs]
    exact hYT_mass _ _
  · rw [hD0]
    exact hYB_mass _ _
  · rw [hDs]
    exact hYB_mass _ _
  · rw [hA]
    exact hYT_mass _ _
/-- **Zero and negated currents** (Simon Ch. 6, 2.4–2.5 and 3.1).
(a) The empty triple `(∅, 0, 0)` in `U` represents `0`, so `0` is integer multiplicity.
(b) If `X` is integer multiplicity, so is `0 − X` (integer multiplicity calculus (c)).
(c) `(0 − X)(ω) = X(−ω)`, and `ω ↦ −ω` permutes the admissible forms for `M_G`
(`tsupport (−ω) = tsupport ω`, `|−ω(x)| = |ω(x)|`), so `M_G(0 − X) = M_G(X)`.
(d) If `s > 0`, `M(X) < ∞` and `|ω(x)| ≤ s`, then `±s⁻¹ω` are admissible for `M(X) = M_U(X)`
(the coefficient norm is absolutely homogeneous), so `|X(ω)| = s |X(s⁻¹ω)| ≤ s M(X)`. -/
theorem Submission.dor_lmb_fcd_sd_zero_neg : ∀ (P k : ℕ) (U : Set (Euclid P)), IsOpen U → IsIntegerMultiplicity (0 : GeometricCurrentOn U k) ∧ (∀ X : GeometricCurrentOn U k, IsIntegerMultiplicity X → IsIntegerMultiplicity (0 - X)) ∧ (∀ (X : GeometricCurrentOn U k) (G : Set (Euclid P)), (0 - X).massOn G = X.massOn G) ∧ ∀ (X : GeometricCurrentOn U k) (ω : TestFormOn U k) (s : ℝ), 0 < s → X.mass ≠ ∞ → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ s) → |X ω| ≤ s * X.mass.toReal := by
  intro P k U hU
  -- (a) the empty triple `(∅, 0, 0)` in `U` represents the zero current
  have h0 : IsIntegerMultiplicity (0 : GeometricCurrentOn U k) := by
    refine ⟨{ carrier := ∅
              mult := fun _ => 0
              orient := fun _ => 0
              measurableSet_carrier := MeasurableSet.empty
              carrier_subset := empty_subset U
              rectifiable :=
                Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
              measurable_mult := measurable_const
              mult_pos := fun x hx => absurd hx (notMem_empty x)
              locallyIntegrable_mult := fun K _ _ => by simp
              aestronglyMeasurable_orient := aestronglyMeasurable_const
              orients := by simp }, fun ω => ?_⟩
    simp [IMRep.action]
  -- `(0 − X)(ω) = −X(ω) = X(−ω)`
  have hsub : ∀ (X : GeometricCurrentOn U k) (ω : TestFormOn U k), (0 - X) ω = X (-ω) := by
    intro X ω
    show (0 : GeometricCurrentOn U k) ω - X ω = X (-ω)
    rw [GeometricCurrentOn.zero_apply, zero_sub]
    exact (map_neg X.toCurrent ω).symm
  -- `ω ↦ −ω` preserves admissibility: `tsupport (−ω) = tsupport ω`, `|−ω(x)| = |ω(x)|`
  have hadm : ∀ (G : Set (Euclid P)) (ω : TestFormOn U k), ω ∈ massAdmissibleOn U k G →
      -ω ∈ massAdmissibleOn U k G := by
    intro G ω hω
    refine ⟨?_, fun x => ?_⟩
    · simpa using hω.1
    · simpa using hω.2 x
  -- (b) `0 − X` is integer multiplicity, by (IMC)(c)
  refine ⟨h0, fun X hX => Submission.cmc_imRep_locality_restrict_sub.2.2.1 P k U 0 X hU h0 hX,
    fun X G => ?_, ?_⟩
  · -- (c) `M_G(0 − X) = M_G(X)`
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨ω, hω, rfl⟩
      show ENNReal.ofReal ((0 - X) ω) ≤ X.massOn G
      rw [hsub]
      exact X.le_massOn (hadm G ω hω)
    · apply sSup_le
      rintro r ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (X ω) ≤ (0 - X).massOn G
      have h := (0 - X).le_massOn (hadm G ω hω)
      rwa [hsub, show -(-ω) = ω from neg_neg ω] at h
  · -- (d) `|X(ω)| ≤ s M(X)` when `|ω(x)| ≤ s`
    intro X ω s hs hX hω
    -- homogeneity of the coefficient norm
    have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) k),
        covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
      intro c α
      simp only [covectorEuclideanNorm, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs <;> ring
    -- `s⁻¹ω` is admissible for `M(X) = M_U(X)`
    have hω' : s⁻¹ • ω ∈ massAdmissibleOn U k U := by
      refine ⟨(s⁻¹ • ω).property.2, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hsmul, abs_of_pos (inv_pos.2 hs)]
      calc s⁻¹ * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ s⁻¹ * s :=
            mul_le_mul_of_nonneg_left (hω x) (inv_nonneg.2 hs.le)
        _ = 1 := inv_mul_cancel₀ hs.ne'
    have h1 : X (s⁻¹ • ω) ≤ X.mass.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hX).1 (X.le_massOn hω')
    have h2 : X (-(s⁻¹ • ω)) ≤ X.mass.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hX).1 (X.le_massOn (hadm U _ hω'))
    have hlin : X (s⁻¹ • ω) = s⁻¹ * X ω := map_smul X.toCurrent s⁻¹ ω
    have hneg : X (-(s⁻¹ • ω)) = -X (s⁻¹ • ω) := map_neg X.toCurrent _
    have habs : |X (s⁻¹ • ω)| ≤ X.mass.toReal := abs_le.2 ⟨by linarith, h1⟩
    calc |X ω| = |s * X (s⁻¹ • ω)| := by rw [hlin, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      _ = s * |X (s⁻¹ • ω)| := by rw [abs_mul, abs_of_pos hs]
      _ ≤ s * X.mass.toReal := mul_le_mul_of_nonneg_left habs hs.le

/-- **Shell-wise push-forwards and homotopies telescope** (Simon Ch. 6, proof of 5.1, with the
homotopy formula 2.25).  Let `push`, `homot` satisfy, on integer multiplicity currents vanishing
off a compact set, PF(1) `push(id, X) = X`, PF(2) linearity, PF(3) locality and PF(5)
`∂push(F, X) = push(F, ∂X)`, `push(G, X) − push(F, X) − homot(F, G, ∂X) = ∂homot(F, G, X)`.
For shells `Wⱼ` with `∂W₀ = D₀ − Z₀`, `∂Wⱼ₊₁ = Dⱼ₊₁ + Zⱼ − Zⱼ₊₁` and maps with `φⱼ₊₁ = φⱼ` on
`Eⱼ`, writing `hⱼ = homot(id, φⱼ, ·)`:
(S1) `Σ_{j≤N} (push(φⱼ, Wⱼ) − Wⱼ − ∂hⱼ(Wⱼ)) = Σ_{j≤N} hⱼ(Dⱼ) − h_N(Z_N)`;
(S2) `Σ_{j≤N} ∂push(φⱼ, Wⱼ) = Σ_{j≤N} push(φⱼ, Dⱼ) − push(φ_N, Z_N)`.

On a shell, `∂X = (D′ − (0 − Z′)) − Z″` is integer multiplicity (zero_neg, (IMC)(c)), so PF(5),
PF(1) and three applications of PF(2) give the shell identities; PF(3) identifies the
`Zⱼ`-terms of consecutive shells, and the sums telescope by induction on `N`. -/
theorem Submission.dor_lmb_fcd_sd_telescoping : ∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), (∀ (k : ℕ) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → push k (fun x => x) X = X) → (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → Y ω = 0) → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) → (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → EqOn F F' E → EqOn G G' E → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) → (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity X.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) (E) → X ω = 0) → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary) → ∀ (E : ℕ → Set (Euclid P)) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ j, IsCompact (E j)) → (∀ j, E j ⊆ E (j + 1)) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, EqOn (φ (j + 1)) (φ j) (E j)) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsIntegerMultiplicity (D j)) → (∀ j, IsIntegerMultiplicity (Z j)) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (E j) → W j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → D j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → Z j ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, (W 0).boundary ω = D 0 ω - Z 0 ω) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), (W (j + 1)).boundary ω = D (j + 1) ω + Z j ω - Z (j + 1) ω) → (∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), ∑ j ∈ Finset.range (N + 1), push (m + 1) (φ j) (W j) ω - ∑ j ∈ Finset.range (N + 1), W j ω - ∑ j ∈ Finset.range (N + 1), (homot (m + 1) (fun x => x) (φ j) (W j)).boundary ω = ∑ j ∈ Finset.range (N + 1), homot m (fun x => x) (φ j) (D j) ω - homot m (fun x => x) (φ N) (Z N) ω) ∧ ∀ N (ω : TestFormOn (univ : Set (Euclid P)) m), ∑ j ∈ Finset.range (N + 1), (push (m + 1) (φ j) (W j)).boundary ω = ∑ j ∈ Finset.range (N + 1), push m (φ j) (D j) ω - push m (φ N) (Z N) ω := by
  intro P m push homot hid hlin hloc hhom E φ Λ W D Z hEc hEs hφ hΛ1 hΛs hφE hW hD hZ hWE hDE
    hZE hW0 hWs
  -- values of a difference: `(A − B)(ω) = A(ω) − B(ω)`
  have hsub : ∀ {k : ℕ} (A B : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (ω : TestFormOn (univ : Set (Euclid P)) k), (A - B) ω = A ω - B ω := fun _ _ _ => rfl
  -- Step 1: `id` is `Λⱼ`-Lipschitz and `φⱼ` is `Λⱼ₊₁`-Lipschitz
  have hidL : ∀ j, LipschitzWith (Λ j) (fun x : Euclid P => x) := fun j =>
    LipschitzWith.id.weaken (hΛ1 j)
  have hφL : ∀ j, LipschitzWith (Λ (j + 1)) (φ j) := fun j => (hφ j).weaken (hΛs j)
  -- `0` and `0 − X` are integer multiplicity (zero_neg), and so is `A − B` ((IMC)(c))
  have hz := Submission.dor_lmb_fcd_sd_zero_neg P m univ isOpen_univ
  have hIM : ∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) m, IsIntegerMultiplicity A →
      IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B) := fun A B hA hB =>
    Submission.cmc_imRep_locality_restrict_sub.2.2.1 P m univ A B isOpen_univ hA hB
  -- Step 2: `push(F, 0)` and `homot(F, G, 0)` vanish (PF(2) with `X = Y = 0`, `E = ∅`)
  have hzero : ∀ (L : NNReal) (F G : Euclid P → Euclid P), LipschitzWith L F →
      LipschitzWith L G → (∀ ω, push m F 0 ω = 0) ∧ ∀ η, homot m F G 0 η = 0 := by
    intro L F G hF hG
    have h00 : (0 : GeometricCurrentOn (univ : Set (Euclid P)) m) - 0 = 0 :=
      GeometricCurrentOn.ext fun ω => by rw [hsub, GeometricCurrentOn.zero_apply, sub_self]
    obtain ⟨hp, hh⟩ := hlin m L F G ∅ 0 0 hF hG isCompact_empty hz.1 hz.1 (fun _ _ => rfl)
      (fun _ _ => rfl)
    rw [h00] at hp hh
    refine ⟨fun ω => ?_, fun η => ?_⟩
    · have h := congrArg (fun T => T ω) hp
      simp only [hsub] at h
      linarith
    · have h := congrArg (fun T => T η) hh
      simp only [hsub] at h
      linarith
  -- Step 3: the one-shell identities (i) and (ii)
  have shell : ∀ (j : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1))
      (D' Z' Z'' : GeometricCurrentOn (univ : Set (Euclid P)) m),
      IsIntegerMultiplicity X → IsIntegerMultiplicity D' → IsIntegerMultiplicity Z' →
      IsIntegerMultiplicity Z'' →
      (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (E j) → X ω = 0) →
      (∀ ω : TestFormOn (univ : Set (Euclid P)) m,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → D' ω = 0) →
      (∀ ω : TestFormOn (univ : Set (Euclid P)) m,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → Z' ω = 0) →
      (∀ ω : TestFormOn (univ : Set (Euclid P)) m,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → Z'' ω = 0) →
      (∀ ω, X.boundary ω = D' ω + Z' ω - Z'' ω) →
      (∀ η, push (m + 1) (φ j) X η - X η - (homot (m + 1) (fun x => x) (φ j) X).boundary η =
        homot m (fun x => x) (φ j) D' η + homot m (fun x => x) (φ j) Z' η -
          homot m (fun x => x) (φ j) Z'' η) ∧
      ∀ ω, (push (m + 1) (φ j) X).boundary ω =
        push m (φ j) D' ω + push m (φ j) Z' ω - push m (φ j) Z'' ω := by
    intro j X D' Z' Z'' hX hD' hZ' hZ'' hXE hD'E hZ'E hZ''E hbd
    -- `0 − Z′` and `D′ − (0 − Z′)` are integer multiplicity and vanish off `Eⱼ`
    have hnZ := hz.2.1 Z' hZ'
    have hDnZ := hIM D' (0 - Z') hD' hnZ
    have hnZE : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → (0 - Z') ω = 0 :=
      fun ω hω => by rw [hsub, hZ'E ω hω, GeometricCurrentOn.zero_apply, sub_zero]
    have hDnZE : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) →
          (D' - (0 - Z')) ω = 0 :=
      fun ω hω => by rw [hsub, hD'E ω hω, hnZE ω hω, sub_zero]
    -- `∂X = (D′ − (0 − Z′)) − Z″` is integer multiplicity
    have hbdX : X.boundary = (D' - (0 - Z')) - Z'' := GeometricCurrentOn.ext fun ω => by
      simp only [hbd, hsub, GeometricCurrentOn.zero_apply]
      ring
    have hbdIM : IsIntegerMultiplicity X.boundary := by
      rw [hbdX]
      exact hIM _ _ hDnZ hZ''
    -- PF(2) for `(D′ − (0 − Z′), Z″)`, `(D′, 0 − Z′)`, `(0, Z′)` expands `push(F, ∂X)` and
    -- `homot(F, G, ∂X)`
    have hexp : ∀ F G : Euclid P → Euclid P, LipschitzWith (Λ j) F → LipschitzWith (Λ j) G →
        (∀ ω, push m F X.boundary ω = push m F D' ω + push m F Z' ω - push m F Z'' ω) ∧
        ∀ η, homot m F G X.boundary η =
          homot m F G D' η + homot m F G Z' η - homot m F G Z'' η := by
      intro F G hF hG
      obtain ⟨p₁, k₁⟩ := hlin m (Λ j) F G (E j) (D' - (0 - Z')) Z'' hF hG (hEc j) hDnZ hZ''
        hDnZE hZ''E
      obtain ⟨p₂, k₂⟩ := hlin m (Λ j) F G (E j) D' (0 - Z') hF hG (hEc j) hD' hnZ hD'E hnZE
      obtain ⟨p₃, k₃⟩ := hlin m (Λ j) F G (E j) 0 Z' hF hG (hEc j) hz.1 hZ' (fun _ _ => rfl)
        hZ'E
      obtain ⟨p₀, k₀⟩ := hzero (Λ j) F G hF hG
      rw [hbdX]
      refine ⟨fun ω => ?_, fun η => ?_⟩
      · rw [p₁, hsub, p₂, hsub, p₃, hsub, p₀]
        ring
      · rw [k₁, hsub, k₂, hsub, k₃, hsub, k₀]
        ring
    -- (i): PF(5) with `(F, G) = (id, φⱼ)` and PF(1); (ii): PF(5) with `(F, G) = (φⱼ, φⱼ)`
    obtain ⟨-, h₅⟩ := hhom m (Λ j) (fun x => x) (φ j) (E j) X (hidL j) (hφ j) (hEc j) hX hbdIM
      hXE
    obtain ⟨h₅', -⟩ := hhom m (Λ j) (φ j) (φ j) (E j) X (hφ j) (hφ j) (hEc j) hX hbdIM hXE
    rw [hid (m + 1) (E j) X (hEc j) hX hXE] at h₅
    refine ⟨fun η => ?_, fun ω => ?_⟩
    · have h := congrArg (fun T => T η) h₅
      simp only [hsub] at h
      have e := (hexp (fun x => x) (φ j) (hidL j) (hφ j)).2 η
      linarith
    · rw [h₅']
      exact (hexp (φ j) (φ j) (hφ j) (hφ j)).1 ω
  -- Steps 5 and 6: the shells `0` (with `Z′ = 0`) and `j + 1` (`Zⱼ` vanishes off `Eⱼ ⊆ Eⱼ₊₁`)
  have s₀ := shell 0 (W 0) (D 0) 0 (Z 0) (hW 0) (hD 0) hz.1 (hZ 0) (hWE 0) (hDE 0)
    (fun _ _ => rfl) (hZE 0) (fun ω => by rw [hW0 ω, GeometricCurrentOn.zero_apply, add_zero])
  have s := fun j : ℕ => shell (j + 1) (W (j + 1)) (D (j + 1)) (Z j) (Z (j + 1)) (hW _) (hD _)
    (hZ j) (hZ _) (hWE _) (hDE _) (fun ω hω => hZE j ω (hω.mono_right (hEs j))) (hZE _) (hWs j)
  -- Step 7: PF(3) on `Eⱼ`, where `φⱼ₊₁ = φⱼ`, identifies the `Zⱼ`-terms of consecutive shells
  have hZZ : ∀ j, (∀ η, homot m (fun x => x) (φ (j + 1)) (Z j) η =
      homot m (fun x => x) (φ j) (Z j) η) ∧
      ∀ ω, push m (φ (j + 1)) (Z j) ω = push m (φ j) (Z j) ω := by
    intro j
    have k := (hloc m (Λ (j + 1)) (fun x => x) (φ (j + 1)) (fun x => x) (φ j) (E j) (Z j)
      (hidL (j + 1)) (hφ (j + 1)) (hidL (j + 1)) (hφL j) (hEc j) (hZ j) (hZE j)
      (eqOn_refl _ _) (hφE j)).2
    have p := (hloc m (Λ (j + 1)) (φ (j + 1)) (fun x => x) (φ j) (fun x => x) (E j) (Z j)
      (hφ (j + 1)) (hidL (j + 1)) (hφL j) (hidL (j + 1)) (hEc j) (hZ j) (hZE j) (hφE j)
      (eqOn_refl _ _)).1
    exact ⟨fun η => by rw [k], fun ω => by rw [p]⟩
  -- Step 8: telescoping by induction on `N`
  refine ⟨fun N => ?_, fun N => ?_⟩
  · induction N with
    | zero =>
      intro η
      simp only [zero_add, Finset.sum_range_one]
      have h₁ := s₀.1 η
      have h₂ := (hzero (Λ 0) (fun x => x) (φ 0) (hidL 0) (hφ 0)).2 η
      linarith
    | succ N ih =>
      intro η
      rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1),
        Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1)]
      have h₁ := (s N).1 η
      have h₂ := (hZZ N).1 η
      have h₃ := ih η
      linarith
  · induction N with
    | zero =>
      intro ω
      simp only [zero_add, Finset.sum_range_one]
      have h₁ := s₀.2 ω
      have h₂ := (hzero (Λ 0) (φ 0) (φ 0) (hφ 0) (hφ 0)).1 ω
      linarith
    | succ N ih =>
      intro ω
      rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1)]
      have h₁ := (s N).2 ω
      have h₂ := (hZZ N).2 ω
      have h₃ := ih ω
      linarith
/-- **Limits of the deformation series** (Simon Ch. 6, proof of the Deformation Theorem 5.1,
(19)–(21), (24), (25); used for the flat convergence in the proof of 7.5.1).  By (IMS) the series
`Q = ∑ⱼ Vⱼ`, `R₁ = ∑ⱼ (0 − Hⱼ)` and `S₁ = ∑ⱼ (0 − E′ⱼ)` converge on every test form to integer
multiplicity currents with `M(Q) ≤ ∑ⱼ M(Vⱼ)`, `M(R₁) ≤ ∑ⱼ M(Hⱼ)` and `M(S₁) ≤ ∑ⱼ M(E′ⱼ)`.  A
current of small mass is small on each test form, `|X(ω)| ≤ s M(X)` when `|ω| ≤ s`; so `A_N(ω)` and
`K_N(ω)` tend to `0`, and letting `N → ∞` in (h1) gives `T − Q = ∂R₁ + S₁`.  For an admissible
`ω`, `∂Q(ω) = lim_N ∑_{j≤N} ∂Vⱼ(ω) = lim_N (∑_{j≤N} Yⱼ(ω) − L_N(ω))` by (h2), and the latter is
at most `c M(∂T) + M(L_N) → c M(∂T)`; hence `M(∂Q) ≤ c M(∂T)`.  Sums of currents vanishing off
`F₁` (or `F₂`) vanish off the same set. -/
theorem Submission.dor_lmb_fcd_sd_series_limit : (∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ (P m : ℕ) (c : ℝ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (V E' A Kc : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (H : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (Y L : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (F₁ F₂ : Set (Euclid P)), T.mass ≠ ∞ → T.boundary.mass ≠ ∞ → (∀ j, IsIntegerMultiplicity (V j)) → (∀ j, IsIntegerMultiplicity (H j)) → (∀ j, IsIntegerMultiplicity (E' j)) → (∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), ∑ j ∈ Finset.range (N + 1), V j ω - T ω + A N ω - ∑ j ∈ Finset.range (N + 1), (H j).boundary ω = ∑ j ∈ Finset.range (N + 1), E' j ω - Kc N ω) → (∀ N (ω : TestFormOn (univ : Set (Euclid P)) m), ∑ j ∈ Finset.range (N + 1), (V j).boundary ω = ∑ j ∈ Finset.range (N + 1), Y j ω - L N ω) → Tendsto (fun N => (A N).mass) atTop (𝓝 0) → Tendsto (fun N => (Kc N).mass) atTop (𝓝 0) → Tendsto (fun N => (L N).mass) atTop (𝓝 0) → ∑' j, (V j).mass ≤ ENNReal.ofReal c * T.mass → ∑' j, (H j).mass ≤ ENNReal.ofReal c * T.mass → ∑' j, (E' j).mass ≤ ENNReal.ofReal c * T.boundary.mass → ∑' j, (Y j).mass ≤ ENNReal.ofReal c * T.boundary.mass → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₁) → V j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 2)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (F₂) → H j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₂) → E' j ω = 0) → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity R₁ ∧ IsIntegerMultiplicity S₁ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Q ω = R₁.boundary ω + S₁ ω) ∧ Q.mass ≤ ENNReal.ofReal c * T.mass ∧ Q.boundary.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ R₁.mass ≤ ENNReal.ofReal c * T.mass ∧ S₁.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₁) → Q ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (F₂) → R₁ ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₂) → S₁ ω = 0 := by
  intro IMS P m c T V E' A Kc H Y L F₁ F₂ hT hbT hV hH hE' h1 h2 hA hK hL hVm hHm hE'm hYm hVF hHF
    hE'F
  -- `0 − X` acts as `−X` on test forms
  have hneg_apply : ∀ {k : ℕ} (X : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (ω : TestFormOn (univ : Set (Euclid P)) k), (0 - X) ω = -X ω :=
    fun X ω => zero_sub (X ω)
  -- zero_neg in the degrees `m`, `m + 1` and `m + 2`
  obtain ⟨-, -, hnegm₀, -⟩ := Submission.dor_lmb_fcd_sd_zero_neg P m univ isOpen_univ
  obtain ⟨-, hneg₁, hnegm₁, hsmall₁⟩ :=
    Submission.dor_lmb_fcd_sd_zero_neg P (m + 1) univ isOpen_univ
  obtain ⟨-, hneg₂, hnegm₂, -⟩ := Submission.dor_lmb_fcd_sd_zero_neg P (m + 1 + 1) univ isOpen_univ
  -- Step 1: the bounds `c M(T)` and `c M(∂T)` are finite
  have hcT : ENNReal.ofReal c * T.mass ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT
  have hcbT : ENNReal.ofReal c * T.boundary.mass ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbT
  -- Step 2: `Q = ∑ⱼ Vⱼ`
  obtain ⟨Q, hQ, hQsum, hQm⟩ := IMS P m univ V isOpen_univ hV (ne_top_of_le_ne_top hcT hVm)
  -- Step 3: `R₁ = ∑ⱼ (0 − Hⱼ)`, with `M(0 − Hⱼ) = M(Hⱼ)`
  have eH : ∑' j, (0 - H j : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1 + 1)).mass =
      ∑' j, (H j).mass := tsum_congr fun j => hnegm₂ (H j) univ
  obtain ⟨R₁, hR₁, hR₁sum, hR₁m⟩ := IMS P (m + 1) univ (fun j => 0 - H j) isOpen_univ
    (fun j => hneg₂ (H j) (hH j)) (ne_top_of_le_ne_top hcT (eH.le.trans hHm))
  -- Step 4: `S₁ = ∑ⱼ (0 − E′ⱼ)`, with `M(0 − E′ⱼ) = M(E′ⱼ)`
  have eE : ∑' j, (0 - E' j).mass = ∑' j, (E' j).mass := tsum_congr fun j => hnegm₁ (E' j) univ
  obtain ⟨S₁, hS₁, hS₁sum, hS₁m⟩ := IMS P m univ (fun j => 0 - E' j) isOpen_univ
    (fun j => hneg₁ (E' j) (hE' j)) (ne_top_of_le_ne_top hcbT (eE.le.trans hE'm))
  -- Step 5: if `M(X_N) → 0` then `X_N(ω) → 0`, since `|X_N(ω)| ≤ s M(X_N)` for a bound `s` of `|ω|`
  have hweak : ∀ X : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      Tendsto (fun N => (X N).mass) atTop (𝓝 0) →
      ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Tendsto (fun N => X N ω) atTop (𝓝 0) := by
    intro X hX ω
    -- `x ↦ |ω(x)| = √(∑_I ω(x)(e_I)²)` is continuous, since each coefficient `ω(x)(e_I)` is
    have hcont : Continuous fun x =>
        covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (m + 1)) x) := by
      have hω : Continuous (ω : DifferentialForm (Euclid P) (m + 1)) := ω.property.1.1.continuous
      unfold covectorEuclideanNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
      split_ifs
      · exact ((continuous_eval_const _).comp hω).pow 2
      · exact continuous_const
    have hcs : HasCompactSupport fun x =>
        covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (m + 1)) x) := by
      refine ω.property.1.2.mono' fun x hx => subset_tsupport _ fun h0 => hx ?_
      simp only [h0, covectorEuclideanNorm_zero]
    obtain ⟨s₀, hs₀⟩ := hcont.bddAbove_range_of_hasCompactSupport hcs
    have hs : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (m + 1)) x) ≤
        max s₀ 1 := fun x => (hs₀ (mem_range_self x)).trans (le_max_left _ _)
    have hlim : Tendsto (fun N => max s₀ 1 * (X N).mass.toReal) atTop (𝓝 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hX).const_mul (max s₀ 1)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hX.eventually (gt_mem_nhds zero_lt_one)] with N hN
    rw [Real.norm_eq_abs]
    exact hsmall₁ (X N) ω (max s₀ 1) (lt_max_of_lt_right one_pos) (ne_top_of_lt hN) hs
  -- Step 6: letting `N → ∞` in (h1) gives `T − Q = ∂R₁ + S₁`
  have hid : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      T ω - Q ω = R₁.boundary ω + S₁ ω := by
    intro ω
    have sH : HasSum (fun j => (H j).boundary ω) (-R₁.boundary ω) := by
      have e : (fun j => (H j).boundary ω) =
          fun j => -(0 - H j) (exteriorDerivativeTestOn univ (m + 1) ω) := by
        funext j
        rw [hneg_apply, neg_neg]
        rfl
      rw [e]
      exact (hR₁sum _).neg
    have sE : HasSum (fun j => E' j ω) (-S₁ ω) := by
      have e : (fun j => E' j ω) = fun j => -(0 - E' j) ω := by
        funext j
        rw [hneg_apply, neg_neg]
      rw [e]
      exact (hS₁sum ω).neg
    have tV : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), V j ω) atTop (𝓝 (Q ω)) :=
      (hQsum ω).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have tH : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), (H j).boundary ω) atTop
        (𝓝 (-R₁.boundary ω)) := sH.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have tE : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), E' j ω) atTop (𝓝 (-S₁ ω)) :=
      sE.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have tl : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), V j ω - T ω + A N ω -
        ∑ j ∈ Finset.range (N + 1), (H j).boundary ω) atTop
        (𝓝 (Q ω - T ω + 0 - -R₁.boundary ω)) :=
      ((tV.sub tendsto_const_nhds).add (hweak A hA ω)).sub tH
    have tr : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), V j ω - T ω + A N ω -
        ∑ j ∈ Finset.range (N + 1), (H j).boundary ω) atTop (𝓝 (-S₁ ω - 0)) :=
      (tE.sub (hweak Kc hK ω)).congr fun N => (h1 N ω).symm
    have := tendsto_nhds_unique tl tr
    linarith
  -- Step 7: `M(∂Q) ≤ c M(∂T)`, tested on each admissible `ω`
  have hbQ : Q.boundary.mass ≤ ENNReal.ofReal c * T.boundary.mass := by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have t1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), Y j ω - L N ω) atTop
        (𝓝 (Q.boundary ω)) :=
      ((hQsum (exteriorDerivativeTestOn univ m ω)).tendsto_sum_nat.comp
        (tendsto_add_atTop_nat 1)).congr fun N => h2 N ω
    have t2 : Tendsto (fun N => ENNReal.ofReal c * T.boundary.mass + (L N).mass) atTop
        (𝓝 (ENNReal.ofReal c * T.boundary.mass)) := by
      simpa using (tendsto_const_nhds (x := ENNReal.ofReal c * T.boundary.mass)).add hL
    refine le_of_tendsto_of_tendsto' (ENNReal.tendsto_ofReal t1) t2 fun N => ?_
    calc ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), Y j ω - L N ω)
        = ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), Y j ω + (0 - L N) ω) := by
          rw [hneg_apply, ← sub_eq_add_neg]
      _ ≤ ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), Y j ω) + ENNReal.ofReal ((0 - L N) ω) :=
          ENNReal.ofReal_add_le
      _ ≤ ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (Y j ω) + (0 - L N).massOn univ :=
          add_le_add (Finset.le_sum_of_subadditive ENNReal.ofReal ENNReal.ofReal_zero.le
            (fun _ _ => ENNReal.ofReal_add_le) _ _) ((0 - L N).le_massOn hω)
      _ ≤ ∑ j ∈ Finset.range (N + 1), (Y j).mass + (L N).mass :=
          add_le_add (Finset.sum_le_sum fun j _ => (Y j).le_massOn hω) (hnegm₀ (L N) univ).le
      _ ≤ ENNReal.ofReal c * T.boundary.mass + (L N).mass :=
          add_le_add ((ENNReal.sum_le_tsum _).trans hYm) le_rfl
  -- Steps 8–9: the vanishing sets, and all conclusions
  refine ⟨Q, R₁, S₁, hQ, hR₁, hS₁, hid, hQm.trans hVm, hbQ, hR₁m.trans (eH.le.trans hHm),
    hS₁m.trans (eE.le.trans hE'm), fun ω hω => ?_, fun ω hω => ?_, fun ω hω => ?_⟩
  · have hz : ∀ j, V j ω = 0 := fun j => hVF j ω hω
    rw [← (hQsum ω).tsum_eq]
    simp [hz]
  · have hz : ∀ j, (0 - H j : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1 + 1)) ω = 0 :=
      fun j => by rw [hneg_apply, hHF j ω hω, neg_zero]
    rw [← (hR₁sum ω).tsum_eq]
    simp [hz]
  · have hz : ∀ j, (0 - E' j) ω = 0 := fun j => by rw [hneg_apply, hE'F j ω hω, neg_zero]
    rw [← (hS₁sum ω).tsum_eq]
    simp [hz]

/-- **Deformation of the shells onto the skeleton: assembly** (Simon Ch. 6, 5.1, displays (11)–(18)
and the end of the proof of the deformation theorem).  With `Vⱼ = φⱼ#Wⱼ`, `Hⱼ = h#(id, φⱼ)Wⱼ`,
`Yⱼ = φⱼ#Dⱼ`, `E′ⱼ = h#(id, φⱼ)Dⱼ`, `L_N = φ_N#Z_N` and `K_N = h#(id, φ_N)Z_N`, the telescoping
identities and `Σ_{j≤N} Wⱼ = T − A_N` give `Σ_{j≤N} Vⱼ − T + A_N − ∂Σ_{j≤N} Hⱼ = Σ_{j≤N} E′ⱼ − K_N`
and `∂Σ_{j≤N} Vⱼ = Σ_{j≤N} Yⱼ − L_N`.  As `Λⱼ ≤ c₄2ʲ` and `|φⱼ − id| = |ψ − id| ≤ √P` on `Eⱼ`,
the mass bounds `M(φ#X) ≤ Λᵏ M(X)`, `M(h#X) ≤ √P (2Λ)ᵏ M(X)` and the dyadic decay of `M(Wⱼ)`,
`M(Dⱼ)`, `M(Zⱼ)` give `Σ M(Vⱼ), Σ M(Hⱼ) ≤ c M(T)`, `Σ M(Yⱼ), Σ M(E′ⱼ) ≤ c M(∂T)` and
`M(L_N), M(K_N) → 0`; `Vⱼ` lives on `ψ(Eⱼ) ⊆ F₁` and `Hⱼ`, `E′ⱼ` on the segments from `x` to
`ψ(x)`, inside `F₂`.  The series limit then yields `Q`, `R₁`, `S₁`. -/
theorem Submission.dor_lmb_fcd_sd_core : (∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), (∀ (k : ℕ) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → push k (fun x => x) X = X) → (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → Y ω = 0) → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) → (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → EqOn F F' E → EqOn G G' E → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) → (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ IsIntegerMultiplicity (homot k F G X) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) ({y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) → homot k F G X ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) → (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity X.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) (E) → X ω = 0) → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary) → ∀ (c c₄ C : ℝ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ψ : Euclid P → Euclid P) (E : ℕ → Set (Euclid P)) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (W A : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (F₁ F₂ : Set (Euclid P)), 0 ≤ c₄ → 0 ≤ C → c₄ ^ (m + 1) * (1 + 2 * C) ≤ c → Real.sqrt P * (2 * c₄) ^ (m + 1) * (1 + 2 * C) ≤ c → c₄ ^ m * (1 + 2 * C) ≤ c → Real.sqrt P * (2 * c₄) ^ m * (1 + 2 * C) ≤ c → T.mass ≠ ∞ → T.boundary.mass ≠ ∞ → (∀ j, IsCompact (E j)) → (∀ j, E j ⊆ E (j + 1)) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, (Λ j : ℝ) ≤ c₄ * 2 ^ j) → (∀ j, EqOn (φ j) ψ (E j)) → (∀ j, ∀ x ∈ E j, dist (ψ x) x ≤ Real.sqrt P) → (∀ j, ψ '' E j ⊆ F₁) → (∀ j, ∀ x ∈ E j, ∀ t ∈ Icc (0 : ℝ) 1, x + t • (ψ x - x) ∈ F₂) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsIntegerMultiplicity (D j)) → (∀ j, IsIntegerMultiplicity (Z j)) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (E j) → W j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → D j ω = 0) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) (E j) → Z j ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, (W 0).boundary ω = D 0 ω - Z 0 ω) → (∀ j (ω : TestFormOn (univ : Set (Euclid P)) m), (W (j + 1)).boundary ω = D (j + 1) ω + Z j ω - Z (j + 1) ω) → (∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), ∑ j ∈ Finset.range (N + 1), W j ω = T ω - A N ω) → (W 0).mass ≤ T.mass → (∀ j, (W (j + 1)).mass ≤ ENNReal.ofReal (C * (1 / 2) ^ ((j + 2) * (m + 2))) * T.mass) → (D 0).mass ≤ T.boundary.mass → (∀ j, (D (j + 1)).mass ≤ ENNReal.ofReal (C * (1 / 2) ^ ((j + 2) * (m + 2))) * T.boundary.mass) → (∀ j, (Z j).mass ≤ ENNReal.ofReal (4 * C * (1 / 2) ^ ((j + 2) * (m + 1))) * T.mass) → Tendsto (fun N => (A N).mass) atTop (𝓝 0) → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity R₁ ∧ IsIntegerMultiplicity S₁ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Q ω = R₁.boundary ω + S₁ ω) ∧ Q.mass ≤ ENNReal.ofReal c * T.mass ∧ Q.boundary.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ R₁.mass ≤ ENNReal.ofReal c * T.mass ∧ S₁.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₁) → Q ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (F₂) → R₁ ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (F₂) → S₁ ω = 0 := by
  intro hIMS P m push homot hPF1 hPF2 hPF3 hPF4 hPF5 c c₄ C T ψ E φ Λ W A D Z F₁ F₂ hc₄ hC hcV hcH
    hcY hcE hT hbT hEc hEsub hφL hΛ1 hΛmono hΛc hφψ hψdist hψF₁ hψF₂ hWim hDim hZim hWv hDv hZv
    hbW0 hbW hWsum hW0 hW hD0 hD hZ hA
  -- Step 1: `id` is `Λⱼ`-Lipschitz, as `1 ≤ Λⱼ`
  have hid : ∀ j, LipschitzWith (Λ j) (fun x : Euclid P => x) :=
    fun j => LipschitzWith.id.weaken (hΛ1 j)
  -- Step 2: `φ_{j+1} = ψ = φⱼ` on `Eⱼ ⊆ E_{j+1}`
  have hφstep : ∀ j, EqOn (φ (j + 1)) (φ j) (E j) :=
    fun j x hx => (hφψ (j + 1) (hEsub j hx)).trans (hφψ j hx).symm
  -- Step 3: the telescoping identities (S1), (S2)
  obtain ⟨hS1, hS2⟩ := Submission.dor_lmb_fcd_sd_telescoping P m push homot hPF1 hPF2 hPF3 hPF5
    E φ Λ W D Z hEc hEsub hφL hΛ1 hΛmono hφstep hWim hDim hZim hWv hDv hZv hbW0 hbW
  -- (h1): add `Σ_{j≤N} Wⱼ = T − A_N` to (S1)
  have h1 : ∀ N (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      ∑ j ∈ Finset.range (N + 1), push (m + 1) (φ j) (W j) ω - T ω + A N ω -
          ∑ j ∈ Finset.range (N + 1), (homot (m + 1) (fun x => x) (φ j) (W j)).boundary ω =
        ∑ j ∈ Finset.range (N + 1), homot m (fun x => x) (φ j) (D j) ω -
          homot m (fun x => x) (φ N) (Z N) ω := fun N ω => by
    have hS := hS1 N ω
    have hT' := hWsum N ω
    linarith
  -- Step 4: PF(4) for `push_k(φⱼ, ·)` and `homot_k(id, φⱼ, ·)` on `Wⱼ`, `Dⱼ`, `Zⱼ`
  have hpW := fun j : ℕ => hPF4 (m + 1) (Λ j) (φ j) (φ j) (E j) (W j) (hφL j) (hφL j) (hEc j)
    (hWim j) (hWv j)
  have hhW := fun j : ℕ => hPF4 (m + 1) (Λ j) (fun x => x) (φ j) (E j) (W j) (hid j) (hφL j)
    (hEc j) (hWim j) (hWv j)
  have hpD := fun j : ℕ => hPF4 m (Λ j) (φ j) (φ j) (E j) (D j) (hφL j) (hφL j) (hEc j)
    (hDim j) (hDv j)
  have hhD := fun j : ℕ => hPF4 m (Λ j) (fun x => x) (φ j) (E j) (D j) (hid j) (hφL j) (hEc j)
    (hDim j) (hDv j)
  have hpZ := fun j : ℕ => hPF4 m (Λ j) (φ j) (φ j) (E j) (Z j) (hφL j) (hφL j) (hEc j)
    (hZim j) (hZv j)
  have hhZ := fun j : ℕ => hPF4 m (Λ j) (fun x => x) (φ j) (E j) (Z j) (hid j) (hφL j) (hEc j)
    (hZim j) (hZv j)
  -- `|x − φⱼ(x)| = |ψ(x) − x| ≤ √P` on `Eⱼ`
  have hδ : ∀ j, ∀ x ∈ E j, dist x (φ j x) ≤ Real.sqrt P := fun j x hx => by
    rw [hφψ j hx, dist_comm]
    exact hψdist j x hx
  -- Step 5(a), (b): `Λᵏ M(X) ≤ c₄ᵏ y (1/2)ᵉ M₀` from `Λ ≤ c₄2ʲ`, `M(X) ≤ y (1/2)ᵇ M₀`, `jk + e ≤ b`
  have key : ∀ (a κ y r : ℝ) (L : ℝ≥0∞) (j k b e : ℕ) (M M₀ : ℝ≥0∞),
      0 ≤ a → 0 ≤ κ → 0 ≤ y → L ≤ ENNReal.ofReal (κ * 2 ^ j) → j * k + e ≤ b →
      a * κ ^ k * y * (1 / 2) ^ e ≤ r → M ≤ ENNReal.ofReal (y * (1 / 2) ^ b) * M₀ →
      ENNReal.ofReal a * L ^ k * M ≤ ENNReal.ofReal r * M₀ := by
    intro a κ y r L j k b e M M₀ ha hκ hy hL hb hr hM
    have hκ2 : 0 ≤ κ * 2 ^ j := by positivity
    have hak : 0 ≤ a * (κ * 2 ^ j) ^ k := by positivity
    have hreal : a * (κ * 2 ^ j) ^ k * (y * (1 / 2) ^ b) ≤ r := by
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hb
      have h2 : (2 : ℝ) ^ (j * k) * (1 / 2) ^ (j * k) = 1 := by rw [← mul_pow]; norm_num
      calc a * (κ * 2 ^ j) ^ k * (y * (1 / 2) ^ (j * k + e + l))
          = a * κ ^ k * y * (1 / 2) ^ e * ((2 : ℝ) ^ (j * k) * (1 / 2) ^ (j * k)) *
              (1 / 2) ^ l := by
            rw [mul_pow, ← pow_mul, pow_add, pow_add]; ring
        _ ≤ a * κ ^ k * y * (1 / 2) ^ e := by
            rw [h2, mul_one]
            exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
        _ ≤ r := hr
    calc ENNReal.ofReal a * L ^ k * M
        ≤ ENNReal.ofReal a * ENNReal.ofReal (κ * 2 ^ j) ^ k *
            (ENNReal.ofReal (y * (1 / 2) ^ b) * M₀) := by gcongr
      _ = ENNReal.ofReal (a * (κ * 2 ^ j) ^ k * (y * (1 / 2) ^ b)) * M₀ := by
          rw [← ENNReal.ofReal_pow hκ2, ← ENNReal.ofReal_mul ha, ← mul_assoc,
            ← ENNReal.ofReal_mul hak]
      _ ≤ ENNReal.ofReal r * M₀ := by gcongr
  have keyP : ∀ (κ y r : ℝ) (L : ℝ≥0∞) (j k b e : ℕ) (M M₀ : ℝ≥0∞),
      0 ≤ κ → 0 ≤ y → L ≤ ENNReal.ofReal (κ * 2 ^ j) → j * k + e ≤ b →
      κ ^ k * y * (1 / 2) ^ e ≤ r → M ≤ ENNReal.ofReal (y * (1 / 2) ^ b) * M₀ →
      L ^ k * M ≤ ENNReal.ofReal r * M₀ := by
    intro κ y r L j k b e M M₀ hκ hy hL hb hr hM
    have h := key 1 κ y r L j k b e M M₀ zero_le_one hκ hy hL hb (by rw [one_mul]; exact hr) hM
    rwa [ENNReal.ofReal_one, one_mul] at h
  -- Step 5(c): `Σⱼ aⱼ ≤ (A₀ + 2B) M₀` if `a₀ ≤ A₀ M₀` and `a_{j+1} ≤ B (1/2)ʲ M₀`
  have hgeom : ∀ b : ℝ, 0 ≤ b →
      ∑' j : ℕ, ENNReal.ofReal (b * (1 / 2) ^ j) = ENNReal.ofReal (2 * b) := by
    intro b hb
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hb (pow_nonneg (by norm_num) j))
      (summable_geometric_two.mul_left b), tsum_mul_left, tsum_geometric_two, mul_comm]
  have hsum : ∀ (f : ℕ → ℝ≥0∞) (M₀ : ℝ≥0∞) (a₀ b r : ℝ), 0 ≤ a₀ → 0 ≤ b → a₀ + 2 * b ≤ r →
      f 0 ≤ ENNReal.ofReal a₀ * M₀ → (∀ j, f (j + 1) ≤ ENNReal.ofReal (b * (1 / 2) ^ j) * M₀) →
      ∑' j, f j ≤ ENNReal.ofReal r * M₀ := by
    intro f M₀ a₀ b r ha₀ hb hr h0 hs
    have h2b : 0 ≤ 2 * b := by positivity
    calc ∑' j, f j = f 0 + ∑' j, f (j + 1) := tsum_eq_zero_add' ENNReal.summable
      _ ≤ ENNReal.ofReal a₀ * M₀ + ∑' j, ENNReal.ofReal (b * (1 / 2) ^ j) * M₀ :=
          add_le_add h0 (ENNReal.tsum_le_tsum hs)
      _ = ENNReal.ofReal (a₀ + 2 * b) * M₀ := by
          rw [ENNReal.tsum_mul_right, hgeom b hb, ENNReal.ofReal_add ha₀ h2b, add_mul]
      _ ≤ ENNReal.ofReal r * M₀ := by gcongr
  -- `g_N ≤ K (1/2)ᴺ M(T)` and `M(T) < ∞` give `g_N → 0`
  have htend : ∀ (g : ℕ → ℝ≥0∞) (K : ℝ),
      (∀ N, g N ≤ ENNReal.ofReal (K * (1 / 2) ^ N) * T.mass) → Tendsto g atTop (𝓝 0) := by
    intro g K hg
    have h1 : Tendsto (fun N : ℕ => K * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul K
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hT)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun N => zero_le) hg
  -- `Λⱼ ≤ c₄2ʲ` and `2Λⱼ ≤ (2c₄)2ʲ` in `[0, ∞]`
  have hΛe : ∀ j, (Λ j : ℝ≥0∞) ≤ ENNReal.ofReal (c₄ * 2 ^ j) := fun j =>
    ENNReal.ofReal_coe_nnreal.symm.le.trans (ENNReal.ofReal_le_ofReal (hΛc j))
  have hΛe2 : ∀ j, 2 * (Λ j : ℝ≥0∞) ≤ ENNReal.ofReal (2 * c₄ * 2 ^ j) := fun j => by
    rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    gcongr
    exact hΛe j
  have hsP : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have h2c₄ : 0 ≤ 2 * c₄ := by positivity
  -- Step 6: the masses of `Vⱼ`, `Hⱼ`, `Yⱼ`, `E′ⱼ`, `L_N`, `K_N`
  have hV0 : (push (m + 1) (φ 0) (W 0)).mass ≤ ENNReal.ofReal (c₄ ^ (m + 1)) * T.mass :=
    (hpW 0).2.2.1.trans (keyP c₄ 1 _ _ 0 (m + 1) 0 0 _ _ hc₄ zero_le_one (hΛe 0) (by simp)
      (by simp) (by simpa using hW0))
  have hV : ∀ j, (push (m + 1) (φ (j + 1)) (W (j + 1))).mass ≤
      ENNReal.ofReal (c₄ ^ (m + 1) * C * (1 / 2) ^ j) * T.mass := fun j =>
    (hpW (j + 1)).2.2.1.trans (keyP c₄ C _ _ (j + 1) (m + 1) ((j + 2) * (m + 2)) j _ _ hc₄ hC
      (hΛe (j + 1)) (by nlinarith) le_rfl (hW j))
  have hH0 : (homot (m + 1) (fun x => x) (φ 0) (W 0)).mass ≤
      ENNReal.ofReal (Real.sqrt P * (2 * c₄) ^ (m + 1)) * T.mass :=
    ((hhW 0).2.2.2.2.2 (Real.sqrt P) (hδ 0)).trans (key (Real.sqrt P) (2 * c₄) 1 _ _ 0 (m + 1) 0 0
      _ _ hsP h2c₄ zero_le_one (hΛe2 0) (by simp) (by simp) (by simpa using hW0))
  have hH : ∀ j, (homot (m + 1) (fun x => x) (φ (j + 1)) (W (j + 1))).mass ≤
      ENNReal.ofReal (Real.sqrt P * (2 * c₄) ^ (m + 1) * C * (1 / 2) ^ j) * T.mass := fun j =>
    ((hhW (j + 1)).2.2.2.2.2 (Real.sqrt P) (hδ (j + 1))).trans (key (Real.sqrt P) (2 * c₄) C _ _
      (j + 1) (m + 1) ((j + 2) * (m + 2)) j _ _ hsP h2c₄ hC (hΛe2 (j + 1)) (by nlinarith) le_rfl
      (hW j))
  have hY0 : (push m (φ 0) (D 0)).mass ≤ ENNReal.ofReal (c₄ ^ m) * T.boundary.mass :=
    (hpD 0).2.2.1.trans (keyP c₄ 1 _ _ 0 m 0 0 _ _ hc₄ zero_le_one (hΛe 0) (by simp) (by simp)
      (by simpa using hD0))
  have hY : ∀ j, (push m (φ (j + 1)) (D (j + 1))).mass ≤
      ENNReal.ofReal (c₄ ^ m * C * (1 / 2) ^ j) * T.boundary.mass := fun j =>
    (hpD (j + 1)).2.2.1.trans (keyP c₄ C _ _ (j + 1) m ((j + 2) * (m + 2)) j _ _ hc₄ hC
      (hΛe (j + 1)) (by nlinarith) le_rfl (hD j))
  have hE0 : (homot m (fun x => x) (φ 0) (D 0)).mass ≤
      ENNReal.ofReal (Real.sqrt P * (2 * c₄) ^ m) * T.boundary.mass :=
    ((hhD 0).2.2.2.2.2 (Real.sqrt P) (hδ 0)).trans (key (Real.sqrt P) (2 * c₄) 1 _ _ 0 m 0 0 _ _
      hsP h2c₄ zero_le_one (hΛe2 0) (by simp) (by simp) (by simpa using hD0))
  have hE : ∀ j, (homot m (fun x => x) (φ (j + 1)) (D (j + 1))).mass ≤
      ENNReal.ofReal (Real.sqrt P * (2 * c₄) ^ m * C * (1 / 2) ^ j) * T.boundary.mass := fun j =>
    ((hhD (j + 1)).2.2.2.2.2 (Real.sqrt P) (hδ (j + 1))).trans (key (Real.sqrt P) (2 * c₄) C _ _
      (j + 1) m ((j + 2) * (m + 2)) j _ _ hsP h2c₄ hC (hΛe2 (j + 1)) (by nlinarith) le_rfl (hD j))
  have hL : ∀ N, (push m (φ N) (Z N)).mass ≤
      ENNReal.ofReal (c₄ ^ m * (4 * C) * (1 / 2) ^ N) * T.mass := fun N =>
    (hpZ N).2.2.1.trans (keyP c₄ (4 * C) _ _ N m ((N + 2) * (m + 1)) N _ _ hc₄ (by positivity)
      (hΛe N) (by nlinarith) le_rfl (hZ N))
  have hK : ∀ N, (homot m (fun x => x) (φ N) (Z N)).mass ≤
      ENNReal.ofReal (Real.sqrt P * (2 * c₄) ^ m * (4 * C) * (1 / 2) ^ N) * T.mass := fun N =>
    ((hhZ N).2.2.2.2.2 (Real.sqrt P) (hδ N)).trans (key (Real.sqrt P) (2 * c₄) (4 * C) _ _ N m
      ((N + 2) * (m + 1)) N _ _ hsP h2c₄ (by positivity) (hΛe2 N) (by nlinarith) le_rfl (hZ N))
  -- the four mass sums, with `c₄^{m+1}(1 + 2C) ≤ c` etc.
  have hVsum : ∑' j, (push (m + 1) (φ j) (W j)).mass ≤ ENNReal.ofReal c * T.mass :=
    hsum (fun j => (push (m + 1) (φ j) (W j)).mass) T.mass _ _ c (by positivity) (by positivity)
      (by linarith) hV0 hV
  have hHsum : ∑' j, (homot (m + 1) (fun x => x) (φ j) (W j)).mass ≤ ENNReal.ofReal c * T.mass :=
    hsum (fun j => (homot (m + 1) (fun x => x) (φ j) (W j)).mass) T.mass _ _ c (by positivity)
      (by positivity) (by linarith) hH0 hH
  have hYsum : ∑' j, (push m (φ j) (D j)).mass ≤ ENNReal.ofReal c * T.boundary.mass :=
    hsum (fun j => (push m (φ j) (D j)).mass) T.boundary.mass _ _ c (by positivity)
      (by positivity) (by linarith) hY0 hY
  have hEsum : ∑' j, (homot m (fun x => x) (φ j) (D j)).mass ≤
      ENNReal.ofReal c * T.boundary.mass :=
    hsum (fun j => (homot m (fun x => x) (φ j) (D j)).mass) T.boundary.mass _ _ c (by positivity)
      (by positivity) (by linarith) hE0 hE
  -- Step 7: `Vⱼ` vanishes off `φⱼ(Eⱼ) = ψ(Eⱼ) ⊆ F₁`; `Hⱼ`, `E′ⱼ` vanish off the segments `⊆ F₂`
  have hseg :
      ∀ j, {y : Euclid P | ∃ x ∈ E j, ∃ t ∈ Icc (0 : ℝ) 1, y = x + t • (φ j x - x)} ⊆ F₂ := by
    rintro j y ⟨x, hx, t, ht, rfl⟩
    rw [hφψ j hx]
    exact hψF₂ j x hx t ht
  -- Step 8: the series limit
  exact Submission.dor_lmb_fcd_sd_series_limit hIMS P m c T (fun j => push (m + 1) (φ j) (W j))
    (fun j => homot m (fun x => x) (φ j) (D j)) A (fun N => homot m (fun x => x) (φ N) (Z N))
    (fun j => homot (m + 1) (fun x => x) (φ j) (W j)) (fun j => push m (φ j) (D j))
    (fun N => push m (φ N) (Z N)) F₁ F₂ hT hbT (fun j => (hpW j).1) (fun j => (hhW j).2.1)
    (fun j => (hhD j).2.1) h1 hS2 hA (htend _ _ hK) (htend _ _ hL) hVsum hHsum hEsum hYsum
    (fun j ω hω => (hpW j).2.2.2.1 ω (hω.mono_right ((hφψ j).image_eq.trans_subset (hψF₁ j))))
    (fun j ω hω => (hhW j).2.2.2.2.1 ω (hω.mono_right (hseg j)))
    (fun j ω hω => (hhD j).2.2.2.2.1 ω (hω.mono_right (hseg j)))
/-- **Lipschitz push-forward and the affine homotopy formula** (Simon Ch. 6, 2.17–2.29 with
3.2(2) and 3.9).  Given the integer multiplicity series lemma (IMS), for every `P` there are
operations `push k F X = F_# X` and `homot k F G X = h_#([[(0,1)]] × X)`, where
`h(t, x) = F(x) + t(G(x) − F(x))`, on `k`-currents in `ℝᴾ`.  For `Λ`-Lipschitz maps and integer
multiplicity currents vanishing off a compact `E` they satisfy:
(1) `id_# X = X`; (2) both operations are additive; (3) both depend only on the maps on `E`;
(4) both are integer multiplicity, `M(F_# X) ≤ Λᵏ M(X)`, `F_# X` vanishes off `F(E)`, and
`h_#([[(0,1)]] × X)` vanishes off `h([0,1] × E)` and has mass at most `δ (2Λ)ᵏ M(X)` when
`|F − G| ≤ δ` on `E`; (5) `∂F_# X = F_# ∂X`, and the homotopy formula
`G_# X − F_# X − h_#([[(0,1)]] × ∂X) = ∂h_#([[(0,1)]] × X)` (2.25) holds when `∂X` is integer
multiplicity.

Both operations come from the integer multiplicity push-forward (IPF, which follows from (IMS)):
`push` from the push-forward toolkit and `homot` from the homotopy operator.  Each is
characterized as the limit of `X(η_j)` for test forms `η_j` that equal `F_j^# ω` (resp. the
homotopy form `K_j ω`) on `E`, along `C¹` `Λ`-Lipschitz maps `F_j → F`, `G_j → G`.  Take smooth
mollifications `F_j, G_j` and a cut-off `ζ` equal to `1` near `E`.  Then `ζ F_j^# ω` and
`ζ K_j ω` are test forms.  (1) is the case `F_j = id`, `η_j = ω`.  (2) uses linearity of `X`,
uniqueness of limits, and that `X − Y` is integer multiplicity.  (3) and (4) are properties of
the two operators.  (5) uses `d(F_j^# ω) = F_j^#(dω)` and Cartan's formula
`G_j^# ω − F_j^# ω = d(K_j ω) + K_j(dω)`, together with `d(ζ γ) = d γ` where `ζ = 1`. -/
theorem Submission.dor_lmb_fcd_pushforward_homotopy : (∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ P : ℕ, ∃ (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), (∀ (k : ℕ) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → Y ω = 0) → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → EqOn F F' E → EqOn G G' E → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ IsIntegerMultiplicity (homot k F G X) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) ({y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) → homot k F G X ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ ∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity X.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) (E) → X ω = 0) → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary := by
  intro hIMS P
  -- (IPF) from (IMS); the push-forward toolkit (mollifications, cut-offs and `push`), the
  -- homotopy operator `homot`, smoothness of pull-backs and Cartan's formula
  have hIPF := Submission.dor_lmb_fcd_im_pushforward hIMS
  obtain ⟨⟨-, -, -, hmoll, hcut⟩, hpushEx⟩ := Submission.dor_lmb_fcdp_toolkit_push
  obtain ⟨push, hpush⟩ := hpushEx hIPF P
  obtain ⟨homot, hhomot⟩ := Submission.dor_lmb_fcdp_homot_operator hIPF P
  obtain ⟨hpb, hcartan⟩ := Submission.dor_lmb_fcdp_smooth_homotopy
  -- `ζ • γ` is a test form for a smooth form `γ` and a smooth compactly supported `ζ`
  have cutTest : ∀ (j : ℕ) (ζ : Euclid P → ℝ) (γ : DifferentialForm (Euclid P) j),
      ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → IsSmoothForm γ →
        (fun x => ζ x • γ x) ∈ testFormOnSubmodule (univ : Set (Euclid P)) j := by
    intro j ζ γ hζ hζc hγ
    exact ⟨⟨hζ.smul hγ, hζc.smul_right⟩, subset_univ _⟩
  -- `d(ζ • γ) = dγ` on an open set where `ζ = 1`
  have dcut : ∀ (j : ℕ) (ζ : Euclid P → ℝ) (W : Set (Euclid P))
      (γ : DifferentialForm (Euclid P) j) (x : Euclid P), IsOpen W → (∀ y ∈ W, ζ y = 1) →
        x ∈ W → exteriorDerivative (fun y => ζ y • γ y) x = exteriorDerivative γ x := by
    intro j ζ W γ x hW hζW hx
    apply Filter.EventuallyEq.extDeriv_eq
    filter_upwards [hW.mem_nhds hx] with y hy
    rw [hζW y hy, one_smul]
  -- `C^∞` maps are `C¹`
  have hC1 : ∀ Φ : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Φ → ContDiff ℝ 1 Φ :=
    fun Φ hΦ => hΦ.of_le (by exact_mod_cast le_top)
  refine ⟨push, homot, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `id_# X = X`: take `F_j = id` and `η_j = ω`
    intro k E X hE hX hXE
    obtain ⟨-, -, hP3, -, -⟩ := hpush k 1 (fun x => x) E X LipschitzWith.id hE hX hXE
    refine GeometricCurrentOn.ext fun ω => ?_
    have hlim := hP3 (fun _ x => x) ω (fun _ => ω) (fun _ => contDiff_id)
      (fun _ => LipschitzWith.id)
      (fun u hu => Filter.Eventually.of_forall fun _ _ => refl_mem_uniformity hu)
      (fun _ x _ => by ext v; simp)
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- (2) additivity: `X − Y` is integer multiplicity and vanishes off `E`; compare limits
    intro k Λ F G E X Y hF hG hE hX hY hXE hYE
    have hXY : IsIntegerMultiplicity (X - Y) :=
      Submission.cmc_imRep_locality_restrict_sub.2.2.1 P k univ X Y isOpen_univ hX hY
    have hXYE : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → (X - Y) ω = 0 := by
      intro ω hω
      show X ω - Y ω = 0
      rw [hXE ω hω, hYE ω hω, sub_self]
    obtain ⟨Fs, hFs, hFsL, hFsU⟩ := hmoll P P Λ F hF
    obtain ⟨Gs, hGs, hGsL, hGsU⟩ := hmoll P P Λ G hG
    obtain ⟨ζ, W, hζ, hζc, -, -, hEW, hζW⟩ := hcut P E hE
    refine ⟨GeometricCurrentOn.ext fun ω => ?_, GeometricCurrentOn.ext fun ω => ?_⟩
    · -- `η_j = ζ F_j^# ω`
      let ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k := fun j =>
        ⟨fun x => ζ x • ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x),
          cutTest k ζ _ hζ hζc (hpb P P k (Fs j) _ (hFs j) ω.property.1.1)⟩
      have hη : ∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x =
          ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x) := by
        intro j x hx
        show ζ x • _ = _
        rw [hζW x (hEW hx), one_smul]
      have h1 := (hpush k Λ F E (X - Y) hF hE hXY hXYE).2.2.1 Fs ω ηs
        (fun j => hC1 _ (hFs j)) hFsL hFsU hη
      have h2 := (hpush k Λ F E X hF hE hX hXE).2.2.1 Fs ω ηs
        (fun j => hC1 _ (hFs j)) hFsL hFsU hη
      have h3 := (hpush k Λ F E Y hF hE hY hYE).2.2.1 Fs ω ηs
        (fun j => hC1 _ (hFs j)) hFsL hFsU hη
      exact tendsto_nhds_unique h1 (h2.sub h3)
    · -- `η_j = ζ K_j ω`
      let ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k := fun j =>
        ⟨fun x => ζ x • ∫ t in (0 : ℝ)..1,
          (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft
            (Gs j x - Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)),
          cutTest k ζ _ hζ hζc (hcartan P k (Fs j) (Gs j) _ (hFs j) (hGs j) ω.property.1.1).1⟩
      have hη : ∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1,
          (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft
            (Gs j x - Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)) := by
        intro j x hx
        show ζ x • _ = _
        rw [hζW x (hEW hx), one_smul]
      have h1 := (hhomot k Λ F G E (X - Y) hF hG hE hXY hXYE).2.2.1 Fs Gs ω ηs
        (fun j => hC1 _ (hFs j)) (fun j => hC1 _ (hGs j)) hFsL hGsL hFsU hGsU hη
      have h2 := (hhomot k Λ F G E X hF hG hE hX hXE).2.2.1 Fs Gs ω ηs
        (fun j => hC1 _ (hFs j)) (fun j => hC1 _ (hGs j)) hFsL hGsL hFsU hGsU hη
      have h3 := (hhomot k Λ F G E Y hF hG hE hY hYE).2.2.1 Fs Gs ω ηs
        (fun j => hC1 _ (hFs j)) (fun j => hC1 _ (hGs j)) hFsL hGsL hFsU hGsU hη
      exact tendsto_nhds_unique h1 (h2.sub h3)
  · -- (3) locality
    intro k Λ F G F' G' E X hF hG hF' hG' hE hX hXE hFF' hGG'
    exact ⟨(hpush k Λ F E X hF hE hX hXE).2.1 F' hF' hFF',
      (hhomot k Λ F G E X hF hG hE hX hXE).2.1 F' G' hF' hG' hFF' hGG'⟩
  · -- (4) integrality, mass bounds and supports
    intro k Λ F G E X hF hG hE hX hXE
    obtain ⟨hP1, -, -, hP4, hP5⟩ := hpush k Λ F E X hF hE hX hXE
    obtain ⟨hH1, -, -, hH4, hH5⟩ := hhomot k Λ F G E X hF hG hE hX hXE
    exact ⟨hP1, hH1, hP4, hP5, hH4, hH5⟩
  · -- (5) boundary commutation and the homotopy formula
    intro k Λ F G E X hF hG hE hX hbX hXE
    -- `∂X` vanishes off `E`, as `tsupport dω ⊆ tsupport ω`
    have hbXE : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
        Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X.boundary ω = 0 :=
      fun ω hω => hXE (exteriorDerivativeTestOn univ k ω)
        (Disjoint.mono_left (tsupport_exteriorDerivative_subset (ω : DifferentialForm (Euclid P) k))
          hω)
    obtain ⟨Fs, hFs, hFsL, hFsU⟩ := hmoll P P Λ F hF
    obtain ⟨Gs, hGs, hGsL, hGsU⟩ := hmoll P P Λ G hG
    obtain ⟨ζ, W, hζ, hζc, -, hW, hEW, hζW⟩ := hcut P E hE
    refine ⟨GeometricCurrentOn.ext fun ω => ?_, GeometricCurrentOn.ext fun ω => ?_⟩
    · -- `∂X(ζ F_j^# ω) = X(d(ζ F_j^# ω))`, and `d(ζ F_j^# ω) = F_j^#(dω)` on `E`
      let ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k := fun j =>
        ⟨fun x => ζ x • ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x),
          cutTest k ζ _ hζ hζc (hpb P P k (Fs j) _ (hFs j) ω.property.1.1)⟩
      have hη : ∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x =
          ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x) := by
        intro j x hx
        show ζ x • _ = _
        rw [hζW x (hEW hx), one_smul]
      have hdη : ∀ j, ∀ x ∈ E,
          (exteriorDerivativeTestOn univ k (ηs j) : DifferentialForm (Euclid P) (k + 1)) x =
            ((exteriorDerivativeTestOn univ k ω : DifferentialForm (Euclid P) (k + 1))
              (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x) := by
        intro j x hx
        show exteriorDerivative (fun y => ζ y • _) x = _
        rw [dcut k ζ W _ x hW hζW (hEW hx)]
        exact extDeriv_pullback (ω.property.1.1.differentiable (by simp)).differentiableAt
          (hFs j).contDiffAt (by simp)
      have h1 := (hpush k Λ F E X.boundary hF hE hbX hbXE).2.2.1 Fs ω ηs
        (fun j => hC1 _ (hFs j)) hFsL hFsU hη
      have h2 := (hpush (k + 1) Λ F E X hF hE hX hXE).2.2.1 Fs
        (exteriorDerivativeTestOn univ k ω) (fun j => exteriorDerivativeTestOn univ k (ηs j))
        (fun j => hC1 _ (hFs j)) hFsL hFsU hdη
      exact tendsto_nhds_unique h2 h1
    · -- Cartan: `ζ G_j^# ω − ζ F_j^# ω − d(ζ K_j ω) = K_j(dω)` on `E`
      have hcart := fun j => hcartan P k (Fs j) (Gs j) (ω : DifferentialForm (Euclid P) (k + 1))
        (hFs j) (hGs j) ω.property.1.1
      let a : ℕ → TestFormOn (univ : Set (Euclid P)) (k + 1) := fun j =>
        ⟨fun x => ζ x •
          ((ω : DifferentialForm (Euclid P) (k + 1)) (Gs j x)).compContinuousLinearMap
            (fderiv ℝ (Gs j) x),
          cutTest (k + 1) ζ _ hζ hζc (hpb P P (k + 1) (Gs j) _ (hGs j) ω.property.1.1)⟩
      let b : ℕ → TestFormOn (univ : Set (Euclid P)) (k + 1) := fun j =>
        ⟨fun x => ζ x •
          ((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x),
          cutTest (k + 1) ζ _ hζ hζc (hpb P P (k + 1) (Fs j) _ (hFs j) ω.property.1.1)⟩
      let c : ℕ → TestFormOn (univ : Set (Euclid P)) k := fun j =>
        ⟨fun x => ζ x • ∫ t in (0 : ℝ)..1,
          (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft
            (Gs j x - Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)),
          cutTest k ζ _ hζ hζc (hcart j).1⟩
      have ha : ∀ j, ∀ x ∈ E, (a j : DifferentialForm (Euclid P) (k + 1)) x =
          ((ω : DifferentialForm (Euclid P) (k + 1)) (Gs j x)).compContinuousLinearMap
            (fderiv ℝ (Gs j) x) := by
        intro j x hx
        show ζ x • _ = _
        rw [hζW x (hEW hx), one_smul]
      have hb : ∀ j, ∀ x ∈ E, (b j : DifferentialForm (Euclid P) (k + 1)) x =
          ((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x) := by
        intro j x hx
        show ζ x • _ = _
        rw [hζW x (hEW hx), one_smul]
      have hc : ∀ j, ∀ x ∈ E, (c j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1,
          (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft
            (Gs j x - Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)) := by
        intro j x hx
        show ζ x • _ = _
        rw [hζW x (hEW hx), one_smul]
      have he : ∀ j, ∀ x ∈ E,
          ((a j - b j - exteriorDerivativeTestOn univ k (c j) :
            TestFormOn (univ : Set (Euclid P)) (k + 1)) :
              DifferentialForm (Euclid P) (k + 1)) x = ∫ t in (0 : ℝ)..1,
          (((exteriorDerivativeTestOn univ (k + 1) ω : DifferentialForm (Euclid P) (k + 1 + 1))
            (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)) := by
        intro j x hx
        have hxW := hEW hx
        simp only [Submodule.coe_sub, Pi.sub_apply]
        show ζ x • _ - ζ x • _ - exteriorDerivative (fun y => ζ y • _) x = _
        rw [hζW x hxW, one_smul, one_smul, dcut k ζ W _ x hW hζW hxW, (hcart j).2 x]
        exact add_sub_cancel_left _ _
      have h1 := (hpush (k + 1) Λ G E X hG hE hX hXE).2.2.1 Gs ω a
        (fun j => hC1 _ (hGs j)) hGsL hGsU ha
      have h2 := (hpush (k + 1) Λ F E X hF hE hX hXE).2.2.1 Fs ω b
        (fun j => hC1 _ (hFs j)) hFsL hFsU hb
      have h3 := (hhomot k Λ F G E X.boundary hF hG hE hbX hbXE).2.2.1 Fs Gs ω c
        (fun j => hC1 _ (hFs j)) (fun j => hC1 _ (hGs j)) hFsL hGsL hFsU hGsU hc
      have h4 := (hhomot (k + 1) Λ F G E X hF hG hE hX hXE).2.2.1 Fs Gs
        (exteriorDerivativeTestOn univ (k + 1) ω)
        (fun j => a j - b j - exteriorDerivativeTestOn univ k (c j))
        (fun j => hC1 _ (hFs j)) (fun j => hC1 _ (hGs j)) hFsL hGsL hFsU hGsU he
      -- `X(a_j − b_j − d c_j) = X(a_j) − X(b_j) − ∂X(c_j)`
      have h5 : Tendsto (fun j => X (a j - b j - exteriorDerivativeTestOn univ k (c j))) atTop
          (𝓝 (push (k + 1) G X ω - push (k + 1) F X ω - homot k F G X.boundary ω)) := by
        refine ((h1.sub h2).sub h3).congr fun j => ?_
        have e1 : X (a j - b j - exteriorDerivativeTestOn univ k (c j)) =
            X (a j - b j) - X (exteriorDerivativeTestOn univ k (c j)) :=
          X.toCurrent.map_sub (a j - b j) (exteriorDerivativeTestOn univ k (c j))
        have e2 : X (a j - b j) = X (a j) - X (b j) := X.toCurrent.map_sub (a j) (b j)
        show X (a j) - X (b j) - X (exteriorDerivativeTestOn univ k (c j)) = _
        rw [e1, e2]
      exact tendsto_nhds_unique h5 h4

/-- **Simon Ch. 6, Deformation Theorem 5.1, displays (6)–(25)** (deformation onto the
`n`-skeleton, `n = m + 1 < P`), with the slicing theorem (SL) and the series theorem (IMS) as
antecedents.  Let `T` be integer multiplicity with `∂T` integer multiplicity, vanishing off the
compact `K`, with `M(T), M(∂T) < ∞`; `μ_T`, `μ_∂T` are the measures of representations of `T`,
`∂T` (`M_W = μ(W)` for open `W`).
* The good centre `a` (`dor_lmb_fcd_good_center`) gives `μ({d < r}) ≤ C r^{n+1} μ(ℝᴾ)` for
  `d = dist(·, L*(a))` and `r ≤ 1/4`; the retraction `ψ` (`dor_lmb_fcd_retraction`) sends
  `{d > 0}` into `Lₙ`, moves points by at most `√P`, and is `c_R/r`-Lipschitz on `{d ≥ r}`.
* Slicing `T` by the `1`-Lipschitz `d` (SL) and a Markov choice (`dor_lmb_fcd_sd_good_slice`)
  give radii `r_j ∈ (2^{-j-3}, 2^{-j-2})` with `M(P_{r_j}) ≤ 4C 2^{-(j+2)(m+1)} M(T)`.
* The shells of `T`, `∂T` between consecutive radii (`dor_lmb_fcd_sd_shells`) vanish off
  `E_j = K ∩ {d ≥ r_j}`, where `ψ` agrees with its `√P c_R/r_j`-Lipschitz extension `φ_j`
  (`dor_lmb_fcd_sd_lipschitz_extend`); `Λ_j = max(1, √P c_R/r_j) ≤ c₄ 2^j`, `c₄ = 8(1 + √P c_R)`.
* `dor_lmb_fcd_sd_core` deforms the shells and sums them with (IMS), with the constant
  `c = max(c₄^{n}(1 + 2C), √P(2c₄)^{n}(1 + 2C), c₄^{n-1}(1 + 2C), √P(2c₄)^{n-1}(1 + 2C))`. -/
theorem Submission.dor_lmb_fcd_skeleton_deformation : ((∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Ps : ℝ → GeometricCurrentOn U n, (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) ∧ ∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn U n, Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 ≤ c ∧ ∀ (K : Set (Euclid P)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (K) → T ω = 0) → T.mass ≠ ∞ → T.boundary.mass ≠ ∞ → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity R₁ ∧ IsIntegerMultiplicity S₁ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω - Q ω = R₁.boundary ω + S₁ ω) ∧ Q.mass ≤ ENNReal.ofReal c * T.mass ∧ Q.boundary.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ R₁.mass ≤ ENNReal.ofReal c * T.mass ∧ S₁.mass ≤ ENNReal.ofReal c * T.boundary.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) ({x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ∩ cthickening (Real.sqrt P) K) → Q ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 2))) (cthickening (Real.sqrt P) K) → R₁ ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (cthickening (Real.sqrt P) K) → S₁ ω = 0 := by
  intro hSL hIMS P m hmP
  have hSL' := hSL Submission.dor_imrep_massOn_eq_measure_and_support
  -- constants: retraction `c_R`, good-centre `C`, `c₄ = 8(1 + √P c_R)` and `c`
  obtain ⟨cR, hcR, hRET⟩ := Submission.dor_lmb_fcd_retraction P m hmP
  obtain ⟨CG, hGC⟩ := Submission.dor_lmb_fcd_good_center P m hmP
  obtain ⟨push, homot, hPF1, hPF2, hPF3, hPF4, hPF5⟩ :=
    Submission.dor_lmb_fcd_pushforward_homotopy hIMS P
  have hsP : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hC0 : (0 : ℝ) ≤ CG := NNReal.coe_nonneg CG
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : ℝ, c₄ = 8 * (1 + Real.sqrt P * cR) := ⟨_, rfl⟩
  have hc₄0 : 0 ≤ c₄ := by
    rw [hc₄]
    have := mul_nonneg hsP hcR.le
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max (max (c₄ ^ (m + 1) * (1 + 2 * (CG : ℝ)))
      (Real.sqrt P * (2 * c₄) ^ (m + 1) * (1 + 2 * (CG : ℝ))))
      (max (c₄ ^ m * (1 + 2 * (CG : ℝ))) (Real.sqrt P * (2 * c₄) ^ m * (1 + 2 * (CG : ℝ)))) :=
    ⟨_, rfl⟩
  have hc1 : c₄ ^ (m + 1) * (1 + 2 * (CG : ℝ)) ≤ c := by
    rw [hc]; exact le_max_of_le_left (le_max_left _ _)
  have hc2 : Real.sqrt P * (2 * c₄) ^ (m + 1) * (1 + 2 * (CG : ℝ)) ≤ c := by
    rw [hc]; exact le_max_of_le_left (le_max_right _ _)
  have hc3 : c₄ ^ m * (1 + 2 * (CG : ℝ)) ≤ c := by
    rw [hc]; exact le_max_of_le_right (le_max_left _ _)
  have hc4 : Real.sqrt P * (2 * c₄) ^ m * (1 + 2 * (CG : ℝ)) ≤ c := by
    rw [hc]; exact le_max_of_le_right (le_max_right _ _)
  refine ⟨c, le_trans (mul_nonneg (pow_nonneg hc₄0 _) (by positivity)) hc1, ?_⟩
  intro K T hK hTIM hBIM hTK hTmass hBmass
  -- the measures `μ_T`, `μ_∂T` of representations; `μ(ℝᴾ)` is the mass
  obtain ⟨RT, hRT⟩ := hTIM
  obtain ⟨RB, hRB⟩ := hBIM
  have hTuniv : RT.measure univ = T.mass :=
    ((Submission.dor_imrep_massOn_eq_measure_and_support P (m + 1) univ T RT isOpen_univ
      hRT).1 univ isOpen_univ).symm
  have hBuniv : RB.measure univ = T.boundary.mass :=
    ((Submission.dor_imrep_massOn_eq_measure_and_support P m univ T.boundary RB isOpen_univ
      hRB).1 univ isOpen_univ).symm
  have hTfin : IsFiniteMeasure RT.measure := ⟨by rw [hTuniv]; exact lt_top_iff_ne_top.2 hTmass⟩
  have hBfin : IsFiniteMeasure RB.measure := ⟨by rw [hBuniv]; exact lt_top_iff_ne_top.2 hBmass⟩
  -- good centre `a`, dual skeleton `L*(a)`, retraction `ψ`
  obtain ⟨a, ha, hGCa⟩ := hGC RT.measure RB.measure hTfin hBfin
  obtain ⟨ψ, hψ, hψLip⟩ := hRET a ha
  set Lstar : Set (Euclid P) :=
    {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  have hdcont : Continuous fun x => infDist x Lstar := continuous_infDist_pt Lstar
  -- slices of `T` by `d = dist(·, L*(a))` and good radii `r_j ∈ (2^{-j-3}, 2^{-j-2})`
  obtain ⟨Ps, hPs1, hPs2⟩ := hSL' P m univ T RT RB (fun x => infDist x Lstar) 1 isOpen_univ hRT
    hRB (lipschitz_infDist_pt Lstar)
  have hab : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 3) < (1 / 2) ^ (j + 2) := fun j =>
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hquarter : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 2) ≤ 1 / 4 := fun j =>
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 2 ≤ j + 2)).trans
      (by norm_num)
  choose r hr hrIM hrvan hrform hrmass using fun j : ℕ =>
    Submission.dor_lmb_fcd_sd_good_slice P m T RT RB (fun x => infDist x Lstar) 1 Ps
      ((1 / 2 : ℝ) ^ (j + 3)) ((1 / 2 : ℝ) ^ (j + 2)) hRT hdcont (hab j) hPs1 hPs2
  have hr0 : ∀ j, 0 < r j := fun j => (pow_pos (by norm_num) _).trans (hr j).1
  have hr14 : ∀ j, r j ≤ 1 / 4 := fun j => (hr j).2.le.trans (hquarter j)
  have hrsucc : ∀ j, r (j + 1) < r j := by
    intro j
    have h1 := (hr (j + 1)).2
    rw [show j + 1 + 2 = j + 3 by omega] at h1
    exact h1.trans (hr j).1
  have hranti : Antitone r := antitone_nat_of_succ_le fun j => (hrsucc j).le
  -- shells of `T` and `∂T` between consecutive good radii
  obtain ⟨W, A, D, hWIM, hDIM, hWvan, hDvan, hZvan, hW0bd, hWbd, hWsum, hW0mass, hWmass,
      hD0mass, hDmass, hAmass⟩ :=
    Submission.dor_lmb_fcd_sd_shells P m T RT RB K (fun x => infDist x Lstar) r
      (fun j => Ps (r j)) hRT hRB hK.isClosed hdcont hranti hTK hrform
  -- mass estimates (Simon (6), (7), (10))
  have hGCT : ∀ j : ℕ, RT.measure {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)} ≤
      ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.mass := by
    intro j
    calc RT.measure {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)}
        ≤ (CG : ℝ≥0∞) * ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) * RT.measure univ :=
          (hGCa _ (by positivity) (hquarter j)).1
      _ = ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.mass := by
          rw [hTuniv, ← pow_mul, ENNReal.ofReal_mul hC0, ENNReal.ofReal_coe_nnreal]
  have hGCB : ∀ j : ℕ, RB.measure {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)} ≤
      ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.boundary.mass := by
    intro j
    calc RB.measure {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)}
        ≤ (CG : ℝ≥0∞) * ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) * RB.measure univ :=
          (hGCa _ (by positivity) (hquarter j)).2
      _ = ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.boundary.mass := by
          rw [hBuniv, ← pow_mul, ENNReal.ofReal_mul hC0, ENNReal.ofReal_coe_nnreal]
  have hW0le : (W 0).mass ≤ T.mass := by
    rw [hW0mass, ← hTuniv]; exact measure_mono (subset_univ _)
  have hD0le : (D 0).mass ≤ T.boundary.mass := by
    rw [hD0mass, ← hBuniv]; exact measure_mono (subset_univ _)
  have hWle : ∀ j, (W (j + 1)).mass ≤
      ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.mass := by
    intro j
    rw [hWmass j]
    have hsub : {x | r (j + 1) ≤ infDist x Lstar ∧ infDist x Lstar < r j} ⊆
        {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)} := fun x hx => hx.2.trans (hr j).2
    exact (measure_mono (μ := RT.measure) hsub).trans (hGCT j)
  have hDle : ∀ j, (D (j + 1)).mass ≤
      ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.boundary.mass := by
    intro j
    rw [hDmass j]
    have hsub : {x | r (j + 1) ≤ infDist x Lstar ∧ infDist x Lstar < r j} ⊆
        {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)} := fun x hx => hx.2.trans (hr j).2
    exact (measure_mono (μ := RB.measure) hsub).trans (hGCB j)
  have hZle : ∀ j, (Ps (r j)).mass ≤
      ENNReal.ofReal (4 * (CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 1))) * T.mass := by
    intro j
    have hδpos : (0 : ℝ) < (1 / 2) ^ (j + 3) := by positivity
    have hsub : {x | (1 / 2 : ℝ) ^ (j + 3) < infDist x Lstar ∧
        infDist x Lstar < (1 / 2) ^ (j + 2)} ⊆ {x | infDist x Lstar < (1 / 2 : ℝ) ^ (j + 2)} :=
      fun x hx => hx.2
    have hstrip := (measure_mono (μ := RT.measure) hsub).trans (hGCT j)
    have hreal : (1 / 2 : ℝ) ^ (j + 3) * (4 * (CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 1))) =
        2 * ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) := by
      rw [show (j + 2) * (m + 2) = (j + 2) * (m + 1) + (j + 2) by ring, pow_add]
      ring
    have hR : ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 3)) *
        (ENNReal.ofReal (4 * (CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 1))) * T.mass) =
        2 * (ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ ((j + 2) * (m + 2))) * T.mass) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hδpos.le, hreal,
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
    have h1 := hrmass j
    rw [show (1 / 2 : ℝ) ^ (j + 2) - (1 / 2) ^ (j + 3) = (1 / 2) ^ (j + 3) by ring,
      ENNReal.coe_one, one_mul] at h1
    rw [← ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hδpos).ne' ENNReal.ofReal_ne_top,
      hR]
    exact h1.trans (mul_le_mul' le_rfl hstrip)
  have hAtendsto : Tendsto (fun N => (A N).mass) atTop (𝓝 0) := by
    have hAle : ∀ N, (A N).mass ≤ ENNReal.ofReal ((CG : ℝ) * (1 / 2) ^ N) * T.mass := by
      intro N
      rw [hAmass N]
      have hsub : {x | infDist x Lstar < r N} ⊆ {x | infDist x Lstar < (1 / 2 : ℝ) ^ (N + 2)} :=
        fun x hx => lt_trans hx (hr N).2
      have hpow : (1 / 2 : ℝ) ^ ((N + 2) * (m + 2)) ≤ (1 / 2) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)
      exact (measure_mono (μ := RT.measure) hsub).trans ((hGCT N).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hC0)) le_rfl))
    have h1 : Tendsto (fun N : ℕ => (CG : ℝ) * (1 / 2) ^ N) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (CG : ℝ)
      rwa [mul_zero] at this
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hTmass)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
      hAle
  -- globally Lipschitz pieces `φ_j = ψ` on `{d ≥ r_j}` with constants `Λ_j ≤ c₄ 2^j`
  have hψLipOn : ∀ j, LipschitzOnWith (Real.toNNReal (cR / r j)) ψ {x | r j ≤ infDist x Lstar} :=
    fun j => LipschitzOnWith.of_dist_le' fun x hx y hy => hψLip (r j) (hr0 j) (hr14 j) x y hx hy
  choose φ hφLip hφEq using fun j => Submission.dor_lmb_fcd_sd_lipschitz_extend P
    {x | r j ≤ infDist x Lstar} ψ (Real.toNNReal (cR / r j)) (hψLipOn j)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℕ → NNReal,
      ∀ j, Λ j = max 1 (NNReal.sqrt P * Real.toNNReal (cR / r j)) := ⟨_, fun j => rfl⟩
  have hφΛ : ∀ j, LipschitzWith (Λ j) (φ j) := fun j => by
    rw [hΛ]; exact (hφLip j).weaken (le_max_right _ _)
  have hΛ1 : ∀ j, 1 ≤ Λ j := fun j => by rw [hΛ]; exact le_max_left _ _
  have hΛmono : ∀ j, Λ j ≤ Λ (j + 1) := fun j => by
    rw [hΛ, hΛ]
    exact max_le_max le_rfl (mul_le_mul' le_rfl (Real.toNNReal_le_toNNReal
      (div_le_div_of_nonneg_left hcR.le (hr0 (j + 1)) (hranti (Nat.le_succ j)))))
  have hΛc₄ : ∀ j, (Λ j : ℝ) ≤ c₄ * 2 ^ j := fun j => by
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hkey : cR / r j ≤ 8 * cR * 2 ^ j := by
      rw [div_le_iff₀ (hr0 j)]
      have h1 := mul_lt_mul_of_pos_left (hr j).1 (by positivity : (0 : ℝ) < 2 ^ j)
      have h2 : (2 : ℝ) ^ j * (1 / 2) ^ (j + 3) = 1 / 8 := by
        rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num
      rw [h2] at h1
      nlinarith [mul_lt_mul_of_pos_left h1 hcR]
    rw [hΛ, NNReal.coe_max, NNReal.coe_one, NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_natCast,
      Real.coe_toNNReal _ (div_nonneg hcR.le (hr0 j).le), hc₄]
    have h3 : 0 ≤ Real.sqrt P * cR * 2 ^ j :=
      mul_nonneg (mul_nonneg hsP hcR.le) (by positivity)
    refine max_le (by nlinarith) ?_
    nlinarith [mul_le_mul_of_nonneg_left hkey hsP]
  -- the compact sets `E_j = K ∩ {d ≥ r_j}` and the vanishing sets `F₁ = Lₙ ∩ K_√P`, `F₂ = K_√P`
  have hEcpt : ∀ j, IsCompact (K ∩ {x | r j ≤ infDist x Lstar}) := fun j =>
    hK.inter_right (isClosed_le continuous_const hdcont)
  have hEmono : ∀ j, K ∩ {x | r j ≤ infDist x Lstar} ⊆ K ∩ {x | r (j + 1) ≤ infDist x Lstar} :=
    fun j x hx => ⟨hx.1, (hranti (Nat.le_succ j)).trans hx.2⟩
  have hφψ : ∀ j, EqOn (φ j) ψ (K ∩ {x | r j ≤ infDist x Lstar}) := fun j x hx => hφEq j hx.2
  have hψdist : ∀ j, ∀ x ∈ K ∩ {x | r j ≤ infDist x Lstar}, dist (ψ x) x ≤ Real.sqrt P :=
    fun j x hx => (hψ x ((hr0 j).trans_le hx.2)).2
  have hψF₁ : ∀ j, ψ '' (K ∩ {x | r j ≤ infDist x Lstar}) ⊆
      {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ∩
        cthickening (Real.sqrt P) K := by
    rintro j _ ⟨x, hx, rfl⟩
    exact ⟨(hψ x ((hr0 j).trans_le hx.2)).1,
      mem_cthickening_of_dist_le _ x _ K hx.1 (hψdist j x hx)⟩
  have hψF₂ : ∀ j, ∀ x ∈ K ∩ {x | r j ≤ infDist x Lstar}, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (ψ x - x) ∈ cthickening (Real.sqrt P) K := by
    intro j x hx t ht
    refine mem_cthickening_of_dist_le _ x _ K hx.1 ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
      ← dist_eq_norm]
    calc t * dist (ψ x) x ≤ 1 * Real.sqrt P :=
          mul_le_mul ht.2 (hψdist j x hx) dist_nonneg zero_le_one
      _ = Real.sqrt P := one_mul _
  -- deform the shells and sum them (Simon (11)–(25))
  exact Submission.dor_lmb_fcd_sd_core hIMS P m push homot hPF1 hPF2 hPF3 hPF4 hPF5 c c₄ CG T
    ψ (fun j => K ∩ {x | r j ≤ infDist x Lstar}) φ Λ W A D (fun j => Ps (r j))
    ({x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ∩
      cthickening (Real.sqrt P) K) (cthickening (Real.sqrt P) K)
    hc₄0 hC0 hc1 hc2 hc3 hc4 hTmass hBmass hEcpt hEmono hφΛ hΛ1 hΛmono hΛc₄ hφψ hψdist hψF₁
    hψF₂ hWIM hDIM hrIM hWvan hDvan hZvan hW0bd hWbd hWsum hW0le hWle hD0le hDle hZle hAtendsto

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

/-- Integer median of an integer-valued function on the open unit cube `Q₁ ⊆ ℝ^{m+1}` (Simon
Ch. 6, 5.1, (31) and (35)): some `β ∈ ℤ` has `Lⁿ(Q₁ ∩ {β ≤ u}) ≥ 1/2`, `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`
and `|β| ≤ 2 ∫_{Q₁} |u|`.  `β` is the least integer with `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`; integrality
makes `{β ≤ u}` the complement of `{u ≤ β - 1}`, and Chebyshev's inequality for `|u|` gives both
the existence of `β` and the bound. -/
theorem dor_lmb_fcd_cp_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | (β : ℝ) ≤ u y}) ∧ 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | u y ≤ (β : ℝ)}) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hZ hu
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ
  -- Step 0: `Q₁` is the preimage of the box `(0, 1)ⁿ` under the measure-preserving coordinate map,
  -- so it is measurable with `Lⁿ(Q₁) = 1`.
  have hbox : MeasurableSet (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQeq : Q = WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hQm : MeasurableSet Q := by
    rw [hQeq]
    exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable hbox
  have hQ1 : volume Q = 1 := by
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage hbox.nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp
  -- Work with the probability measure `μ = Lⁿ⌞Q₁`; `Lⁿ(Q₁ ∩ s) = μ(s)` for every set `s`.
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q with hμQ
  have hμ : ∀ s, volume (Q ∩ s) = μ s := fun s => by
    rw [hμQ, Measure.restrict_apply' hQm, inter_comm]
  have hμuniv : μ univ = 1 := by rw [← hμ, inter_univ, hQ1]
  have : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.one_lt_top⟩
  simp only [hμ]
  set I := ∫ y, |u y| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  -- Chebyshev: `ε μ({ε ≤ |u|}) ≤ ∫ |u| dμ`; no measurability of `u` is needed.
  have hmarkov : ∀ ε : ℝ, ε * μ.real {y | ε ≤ |u y|} ≤ I := fun ε =>
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
      (Integrable.abs (μ := μ) hu) ε
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
  -- Tails: for `N > 2 ∫ |u|`, `μ({N ≤ |u|}) < 1/2`.
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * I)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by linarith) hN
  have htail : μ {y | (N : ℝ) ≤ |u y|} < 1 / 2 := by
    have h1 := hmarkov N
    have h2 : μ.real {y | (N : ℝ) ≤ |u y|} < 1 / 2 := not_le.1 fun h => by nlinarith
    rw [← hhalf, measureReal_def] at h2
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by norm_num)).1 h2
  -- `μ(A) + μ(B) ≥ 1` and `μ(B) < 1/2` force `μ(A) ≥ 1/2`.
  have hcompl : ∀ a b : ℝ≥0∞, 1 ≤ a + b → b < 1 / 2 → 1 / 2 ≤ a := by
    intro a b hab hb
    refine not_lt.1 fun h => ?_
    have h' := ENNReal.add_lt_add h hb
    rw [ENNReal.add_halves] at h'
    exact absurd hab (not_le.2 h')
  -- Steps 1–2: the least integer `β` with `μ({u ≤ β}) ≥ 1/2` (Simon (31)).  It exists since
  -- `μ({u ≤ N}) ≥ 1/2` while `μ({u ≤ z}) < 1/2` for `z < -N`.
  have hS : ∃ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} := by
    refine ⟨N, hcompl _ (μ {y | u y ≤ ((N : ℤ) : ℝ)}ᶜ) (hμuniv ▸ measure_univ_le_add_compl _)
      (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail)⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, Int.cast_natCast] at hy ⊢
    exact hy.le.trans (le_abs_self _)
  have hSb : ∃ b : ℤ, ∀ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} → b ≤ z := by
    refine ⟨-N, fun z hz => not_lt.1 fun hlt => ?_⟩
    have hz' : (z : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hlt.le
    refine absurd hz (not_le.2 (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail))
    simp only [mem_ofPred_eq] at hy ⊢
    linarith [neg_abs_le (u y)]
  obtain ⟨β, hβ, hβmin⟩ := Int.exists_least_of_bdd hSb hS
  have hβ1 : μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 :=
    not_le.1 fun h => by have := hβmin (β - 1) h; omega
  -- Step 3: by integrality `{β ≤ u}ᶜ = {u ≤ β - 1}`, so `μ({β ≤ u}) ≥ 1 - μ({u ≤ β - 1}) ≥ 1/2`.
  have hup : 1 / 2 ≤ μ {y | (β : ℝ) ≤ u y} := by
    refine hcompl _ _ ?_ hβ1
    calc (1 : ℝ≥0∞) = μ univ := hμuniv.symm
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | (β : ℝ) ≤ u y}ᶜ := measure_univ_le_add_compl _
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} := by
        gcongr
        intro y hy
        simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hy ⊢
        obtain ⟨k, hk⟩ := hZ y
        rw [hk] at hy ⊢
        have hk' : k < β := by exact_mod_cast hy
        have hk'' : k ≤ β - 1 := by omega
        exact_mod_cast hk''
  refine ⟨β, hup, hβ, ?_⟩
  -- Step 4 (Simon (35)): `{|β| ≤ |u|}` contains `{β ≤ u}` (`β ≥ 0`) or `{u ≤ β}` (`β ≤ 0`), so it
  -- has measure `≥ 1/2`, and Chebyshev gives `|β| / 2 ≤ ∫ |u|`.
  have hbig : 1 / 2 ≤ μ {y | |(β : ℝ)| ≤ |u y|} := by
    rcases le_total 0 β with h0 | h0
    · refine hup.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (0 : ℝ) ≤ β := by exact_mod_cast h0
      rw [abs_of_nonneg h0']
      exact hy.trans (le_abs_self _)
    · refine hβ.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (β : ℝ) ≤ 0 := by exact_mod_cast h0
      rw [abs_of_nonpos h0']
      exact (neg_le_neg hy).trans (neg_le_abs _)
  have hbig' : 1 / 2 ≤ μ.real {y | |(β : ℝ)| ≤ |u y|} := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) hbig
    rwa [hhalf, ← measureReal_def] at h
  have h4 := hmarkov |(β : ℝ)|
  nlinarith [abs_nonneg (β : ℝ)]
/-- Deviation from a `θ`-median `β` is controlled by the double-integral oscillation (Simon Ch. 2,
Lemma 2.7, proof): `∫_W |v − β| ≤ (1 + θ⁻¹) |W|⁻¹ ∫_W ∫_W |v(x) − v(y)|`.  With the mean
`v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`; Markov's inequality on the half
`{β ≤ v}` or `{v ≤ β}` on the far side of `β` from `v̄` gives `|W| |v̄ − β| ≤ θ⁻¹ ∫_W |v − v̄|`. -/
theorem dor_lmb_fcd_cp_median_deviation : ∀ (P : ℕ) (W : Set (Euclid P)) (v : Euclid P → ℝ) (β θ : ℝ), MeasurableSet W → volume W ≠ ∞ → IntegrableOn v W → 0 < θ → θ * (volume W).toReal ≤ (volume (W ∩ {y | β ≤ v y})).toReal → θ * (volume W).toReal ≤ (volume (W ∩ {y | v y ≤ β})).toReal → ∫ y in W, |v y - β| ≤ (1 + θ⁻¹) * ((volume W).toReal)⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
  intro P W v β θ hW hWfin hv hθ hge hle
  -- `volume⌞W` is a finite measure; write `m = |W|`
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hWfin
  set m := (volume W).toReal
  -- Step 0: if `|W| = 0`, then `volume⌞W = 0` and both sides vanish
  rcases (ENNReal.toReal_nonneg : 0 ≤ m).eq_or_lt with hm | hm
  · have hW0 : volume W = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hm.symm).resolve_right hWfin
    simp [Measure.restrict_eq_zero.mpr hW0]
  -- Step 1: integrability; the partial integral is integrable by Fubini
  have hvi : Integrable v (volume.restrict W) := hv
  have hint : ∀ c : ℝ, Integrable (fun x => |v x - c|) (volume.restrict W) := fun c =>
    (hvi.sub (integrable_const c)).abs
  have hprod : Integrable (fun p : Euclid P × Euclid P => |v p.1 - v p.2|)
      ((volume.restrict W).prod (volume.restrict W)) :=
    ((hvi.comp_fst _).sub (hvi.comp_snd _)).abs
  have hG : Integrable (fun x => ∫ y in W, |v x - v y|) (volume.restrict W) :=
    hprod.integral_prod_left
  -- Step 2: with the mean `v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`
  set vbar := m⁻¹ * ∫ y in W, v y with hvbar
  have hpt : ∀ x, |v x - vbar| ≤ m⁻¹ * ∫ y in W, |v x - v y| := by
    intro x
    have h1 : ∫ y in W, (v x - v y) = m * v x - ∫ y in W, v y := by
      rw [integral_sub (integrable_const _) hvi, integral_const, measureReal_restrict_apply_univ,
        smul_eq_mul]
      rfl
    have h2 : v x - vbar = m⁻¹ * ∫ y in W, (v x - v y) := by
      rw [h1, hvbar, mul_sub, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
    rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hm)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hm.le)
  have hJ : ∫ x in W, |v x - vbar| ≤ m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
    rw [← integral_const_mul]
    exact integral_mono (hint vbar) (hG.const_mul _) hpt
  -- Step 3: `|v − v̄| ≥ |β − v̄|` on the half on the far side of `β`, which has measure `≥ θ|W|`
  set I := ∫ x in W, |v x - vbar| with hI
  have hmeas : θ * m ≤ (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} := by
    rcases le_total vbar β with hb | hb
    · refine hge.trans ?_
      rw [show (volume (W ∩ {y | β ≤ v y})).toReal = (volume.restrict W).real {y | β ≤ v y} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : β ≤ v x) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (by linarith)]
      linarith
    · refine hle.trans ?_
      rw [show (volume (W ∩ {y | v y ≤ β})).toReal = (volume.restrict W).real {y | v y ≤ β} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : v x ≤ β) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonpos (sub_nonpos.mpr hb), abs_of_nonpos (by linarith)]
      linarith
  -- Markov's inequality for `|v − v̄|` at level `|β − v̄|`
  have hM : |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} ≤ I :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hint vbar) _
  have hmed : m * |vbar - β| ≤ θ⁻¹ * I := by
    rw [abs_sub_comm, le_inv_mul_iff₀ hθ]
    calc θ * (m * |β - vbar|) = |β - vbar| * (θ * m) := by ring
      _ ≤ |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} :=
        mul_le_mul_of_nonneg_left hmeas (abs_nonneg _)
      _ ≤ I := hM
  -- Step 4: triangle inequality `|v − β| ≤ |v − v̄| + |v̄ − β|`
  have htri : ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := by
    have h3 : ∫ y in W, (|v y - vbar| + |vbar - β|) = I + m * |vbar - β| := by
      rw [integral_add (hint vbar) (integrable_const _), integral_const,
        measureReal_restrict_apply_univ, smul_eq_mul]
      rfl
    rw [← h3]
    exact integral_mono (hint β) ((hint vbar).add (integrable_const _))
      fun y => abs_sub_le (v y) vbar β
  calc ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := htri
    _ ≤ I + θ⁻¹ * I := by linarith
    _ = (1 + θ⁻¹) * I := by ring
    _ ≤ (1 + θ⁻¹) * (m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y|) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (1 + θ⁻¹) * m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by ring
/-- Fubini identity for mixed points on the cube `Q_δ = {y | ∀ i, δ < y i < 1 - δ}`: if `a_k(x, y)`
takes the coordinates `j < k` from `y` and the others from `x`, then
`∫_{Q_δ} ∫_{Q_δ} h(a_k(x, y)) dy dx = vol(Q_δ) ∫_{Q_δ} h`.  The swap `σ` exchanging `x_j` and `y_j`
for `j < k` is an involution preserving `vol ⊗ vol` (a factorwise product of swaps and identities)
and `Q_δ × Q_δ`, so Fubini on the finite measure space `Q_δ × Q_δ` turns the left side into
`∫_{Q_δ × Q_δ} h(x)`. -/
theorem dor_lmb_fcd_cp_mixed_point_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) = (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- the coordinate swap on `(Fin (m+1) → ℝ)²`
  have hτ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      ((fun j => if j < k then p.2 j else p.1 j), (fun j => if j < k then p.1 j else p.2 j)))
      (volume.prod volume) (volume.prod volume) := by
    set A := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1))
    have hA : MeasurePreserving A (Measure.pi fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
        ((volume : Measure (Fin (m + 1) → ℝ)).prod volume) :=
      measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1)) (fun _ => volume) (fun _ => volume)
    let f : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ := fun j => if j < k then Prod.swap else id
    have hf : ∀ j, MeasurePreserving (f j) ((volume : Measure ℝ).prod volume)
        ((volume : Measure ℝ).prod volume) := by
      intro j
      by_cases hj : j < k
      · simp only [f, hj, ite_true]
        exact Measure.measurePreserving_swap
      · simp only [f, hj, ite_false]
        exact MeasurePreserving.id _
    have hP := measurePreserving_pi (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
      (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume) hf
    have hcomp := (hA.comp hP).comp hA.symm
    convert hcomp using 1
    funext p
    ext j
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  -- the same swap on `Euclid (m+1) × Euclid (m+1)`
  set σ : Euclid (m + 1) × Euclid (m + 1) → Euclid (m + 1) × Euclid (m + 1) := fun p =>
    (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j),
      WithLp.toLp 2 (fun j => if j < k then p.1 j else p.2 j)) with hσdef
  have hσ : MeasurePreserving σ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (PiLp.volume_preserving_ofLp (Fin (m + 1)))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (PiLp.volume_preserving_toLp (Fin (m + 1)))
    have := (h2.comp hτ).comp h1
    convert this using 1
    funext p
    rfl
  have hσσ : ∀ p, σ (σ p) = p := by
    intro p
    ext j
    · by_cases hj : j < k <;> simp [hσdef, hj]
    · by_cases hj : j < k <;> simp [hσdef, hj]
  let σe : (Euclid (m + 1) × Euclid (m + 1)) ≃ᵐ (Euclid (m + 1) × Euclid (m + 1)) :=
    { toFun := σ
      invFun := σ
      left_inv := hσσ
      right_inv := hσσ
      measurable_toFun := hσ.measurable
      measurable_invFun := hσ.measurable }
  have hemb : MeasurableEmbedding σ := σe.measurableEmbedding
  have hpre : σ ⁻¹' (Q ×ˢ Q) = Q ×ˢ Q := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hσdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
  have hQm : MeasurableSet Q := by
    have : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y; simp [hQ]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (by fun_prop)).inter (measurableSet_lt (by fun_prop) measurable_const)
  have hσQ : MeasurePreserving σ ((volume.prod volume).restrict (Q ×ˢ Q))
      ((volume.prod volume).restrict (Q ×ˢ Q)) := by
    have := hσ.restrict_preimage_emb hemb (Q ×ˢ Q)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict Q) =
      ((volume : Measure (Euclid (m + 1))).prod volume).restrict (Q ×ˢ Q) :=
    Measure.prod_restrict Q Q
  have hQfin : volume Q ≠ ∞ := by
    have hb : Bornology.IsBounded Q := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))]
      refine ⟨Real.sqrt (((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2), fun y hy => ?_⟩
      rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (|δ| + |1 - δ|) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := hy i
            rw [Real.norm_eq_abs]
            have h1 : |y i| ≤ |δ| + |1 - δ| := by
              rw [abs_le]
              constructor <;> cases abs_cases δ <;> cases abs_cases (1 - δ) <;> linarith [this.1, this.2]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = ((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2 := by simp
    exact hb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2 hQfin
  -- integrability of `p ↦ h p.1` on `Q × Q`
  have hint1 : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => h p.1)
      ((volume.restrict Q).prod (volume.restrict Q)) := hh.comp_fst (volume.restrict Q)
  have hint2 : Integrable (fun p => h (σ p).1) ((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr] at hint1 ⊢
    exact (hσQ.integrable_comp_emb hemb).2 hint1
  -- compute
  have e1 : ∫ x in Q, ∫ y in Q, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) =
      ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr]
    exact hσQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      (volume Q).toReal * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    rw [integral_const_mul]
  rw [e1, e2, e3]
/-- Fubini along the `k`-th coordinate of the cube `Q_δ = (δ, 1 − δ)^{m+1}` (Simon Ch. 2,
proof of Lemma 2.7): for `h` integrable on `Q_δ`,
`∫_{Q_δ} ∫_δ^{1−δ} h(x[k ↦ t]) dt dx = (1 − 2δ) ∫_{Q_δ} h`.  The slice swap
`ρ(x, t) = (x[k ↦ t], x_k)` is a measure-preserving involution of `Euclid (m + 1) × ℝ` that maps
`Q_δ × (δ, 1 − δ)` onto itself. -/
theorem dor_lmb_fcd_cp_slice_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ t in Ioo δ (1 - δ), h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) = (1 - 2 * δ) * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- Step 0: if `δ ≥ 1/2` the cube is empty and both sides vanish.
  rcases le_or_gt (1 / 2) δ with hδ | hδ
  · have hQe : Q = ∅ := by
      ext y
      simp only [hQ, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, fun h0 => by linarith [h0.1, h0.2]⟩
    simp [hQe]
  -- Step 2: the slice swap on `(Fin (m + 1) → ℝ) × ℝ` preserves volume.  Under
  -- `piFinSuccAbove` it is `((a, b), c) ↦ ((c, b), a)`, a composition of swaps and
  -- reassociations.
  have hρ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × ℝ => (Function.update p.1 k p.2, p.1 k))
      (volume.prod volume) (volume.prod volume) := by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    have he : MeasurePreserving e (volume : Measure (Fin (m + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    set T : (ℝ × (Fin m → ℝ)) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ := fun q => ((q.2, q.1.2), q.1.1) with hTdef
    have hT : MeasurePreserving T (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) := by
      have s1 : MeasurePreserving (Prod.map Prod.swap id : (ℝ × (Fin m → ℝ)) × ℝ → ((Fin m → ℝ) × ℝ) × ℝ)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have s2 := measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)
      have s3 : MeasurePreserving (Prod.map id Prod.swap : (Fin m → ℝ) × (ℝ × ℝ) → (Fin m → ℝ) × (ℝ × ℝ))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume)) :=
        (MeasurePreserving.id _).prod Measure.measurePreserving_swap
      have s4 := (measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)).symm
      have s5 : MeasurePreserving (Prod.map Prod.swap id : ((Fin m → ℝ) × ℝ) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have := s5.comp (s4.comp (s3.comp (s2.comp s1)))
      convert this using 1
      funext q
      rfl
    have hE2 : MeasurePreserving (e.prodCongr (MeasurableEquiv.refl ℝ))
        ((volume : Measure (Fin (m + 1) → ℝ)).prod (volume : Measure ℝ))
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
      he.prod (MeasurePreserving.id _)
    have hfull := (hE2.symm.comp hT).comp hE2
    convert hfull using 1
    funext p
    ext j
    · simp only [Function.comp, e, T]
      simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
    · simp [e, T, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
  -- Steps 1–2: the same map `ρ` on `Euclid (m + 1) × ℝ` (via `ofLp`/`toLp`) is a
  -- measure-preserving involution, hence a measurable embedding.
  set ρ : Euclid (m + 1) × ℝ → Euclid (m + 1) × ℝ := fun p =>
    (WithLp.toLp 2 (Function.update (WithLp.ofLp p.1) k p.2), p.1 k) with hρdef
  have hρE : MeasurePreserving ρ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have := (h2.comp hρ).comp h1
    convert this using 1
    funext p
    rfl
  have hρρ : ∀ p, ρ (ρ p) = p := by
    intro p
    ext j
    · by_cases hj : j = k
      · subst hj; simp [hρdef]
      · simp [hρdef]
    · simp [hρdef]
  let ρe : (Euclid (m + 1) × ℝ) ≃ᵐ (Euclid (m + 1) × ℝ) :=
    { toFun := ρ
      invFun := ρ
      left_inv := hρρ
      right_inv := hρρ
      measurable_toFun := hρE.measurable
      measurable_invFun := hρE.measurable }
  have hemb : MeasurableEmbedding ρ := ρe.measurableEmbedding
  -- Step 3: `ρ⁻¹(Q × I) = Q × I`, so `ρ` preserves `(vol⌞Q) ⊗ (vol⌞I)`.
  set I : Set ℝ := Ioo δ (1 - δ) with hI
  have hpre : ρ ⁻¹' (Q ×ˢ I) = Q ×ˢ I := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hρdef, hI, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · simpa using h1 k
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · exact h1 k
  have hρQ : MeasurePreserving ρ ((volume.prod volume).restrict (Q ×ˢ I))
      ((volume.prod volume).restrict (Q ×ˢ I)) := by
    have := hρE.restrict_preimage_emb hemb (Q ×ˢ I)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict I) =
      ((volume : Measure (Euclid (m + 1))).prod (volume : Measure ℝ)).restrict (Q ×ˢ I) :=
    Measure.prod_restrict Q I
  -- Step 4: `(x, t) ↦ h x` and `(x, t) ↦ h (x[k ↦ t])` are integrable on `Q × I`.
  have hfinI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.2 (by simp [hI])
  have hint1 : Integrable (fun p : Euclid (m + 1) × ℝ => h p.1)
      ((volume.restrict Q).prod (volume.restrict I)) := hh.comp_fst (volume.restrict I)
  have hint2 : Integrable (fun p => h (ρ p).1) ((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr] at hint1 ⊢
    exact (hρQ.integrable_comp_emb hemb).2 hint1
  -- Step 5: Fubini, the change of variables `ρ`, and `vol(I) = 1 − 2δ`.
  have e1 : ∫ x in Q, ∫ t in I, h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) =
      ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr]
    exact hρQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      (1 - 2 * δ) * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hI, Real.volume_Ioo]
    rw [integral_const_mul, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [e1, e2, e3]
/-- One coordinate step of the Poincaré inequality on the cube `Q_δ`: the points
`a_k(x, y)`, `b_k(x, y)` differ only in the `k`-th coordinate, so by the fundamental theorem of
calculus `|v(a_k) − v(b_k)| ≤ Φ(a_k) := ∫_{(δ, 1−δ)} |∂_k v(a_k[t])| dt`.  Integrating, the
mixed-point identity gives `∫∫ Φ(a_k) = |Q_δ| ∫_{Q_δ} Φ` and the slice identity gives
`∫_{Q_δ} Φ = (1 − 2δ) ∫_{Q_δ} |∂_k v|`. -/
theorem dor_lmb_fcd_cp_coordinate_step : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ) (k : Fin (m + 1)), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) - v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤ (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |fderiv ℝ v x (EuclideanSpace.single k 1)| := by
  intro m v δ k hv _ _
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- `Q` is open, and contained in the compact cube `K = [δ, 1 − δ]^{m+1}`.
  have hQo : IsOpen Q := by
    have hQi : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y
      simp [hQ]
    rw [hQi]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  set K : Set (Euclid (m + 1)) := WithLp.toLp 2 '' Set.pi univ fun _ => Icc δ (1 - δ)
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hQK : Q ⊆ K := fun y hy => ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
  -- `∂_k v` is continuous.
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hgc : Continuous fun p : Euclid (m + 1) => |fderiv ℝ v p (EuclideanSpace.single k 1)| :=
    (hfd.clm_apply continuous_const).abs
  -- `p[t]`, the point `p` with `k`-th coordinate `t`, is `p + (t − p_k) e_k`.
  have hupd : ∀ (p : Euclid (m + 1)) (t : ℝ),
      WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t) =
        p + (t - p k) • EuclideanSpace.single k (1 : ℝ) := by
    intro p t
    ext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  -- `Φ(p) = ∫_{(δ, 1−δ)} |∂_k v(p[t])| dt` is continuous.
  set Φ : Euclid (m + 1) → ℝ := fun p => ∫ t in Ioo δ (1 - δ),
    |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t)) (EuclideanSpace.single k 1)|
    with hΦ
  have hΦc : Continuous Φ := by
    have hGc : Continuous fun z : Euclid (m + 1) × ℝ =>
        |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp z.1) k z.2))
          (EuclideanSpace.single k 1)| := by
      simp_rw [hupd]
      exact hgc.comp (by fun_prop)
    have hΦ' : Φ = fun p => ∫ t in Icc δ (1 - δ),
        |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t))
          (EuclideanSpace.single k 1)| := by
      funext p
      exact integral_Icc_eq_integral_Ioo.symm
    rw [hΦ']
    exact continuous_parametric_integral_of_continuous
      (f := fun p t => |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t))
        (EuclideanSpace.single k 1)|) hGc isCompact_Icc
  -- `(x, y) ↦ Φ(a_k(x, y))` is continuous.
  have hac : Continuous fun z : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j) : Euclid (m + 1)) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => by fun_prop) (fun _ => by fun_prop)
  have hFc : Continuous fun z : Euclid (m + 1) × Euclid (m + 1) =>
      Φ (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j)) := hΦc.comp hac
  -- Integrability: continuous functions are integrable on the compact `K ⊇ Q`.
  have hI1 : IntegrableOn (fun p => |fderiv ℝ v p (EuclideanSpace.single k 1)|) Q :=
    (hgc.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hI2 : IntegrableOn Φ Q := (hΦc.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hI3 : ∀ x : Euclid (m + 1), IntegrableOn
      (fun y : Euclid (m + 1) => Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j))) Q :=
    fun x => ((hFc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      hKc).mono_set hQK
  have hI4 : IntegrableOn (fun x : Euclid (m + 1) =>
      ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j))) Q := by
    have hprod : Integrable (fun z : Euclid (m + 1) × Euclid (m + 1) =>
        Φ (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j)))
        ((volume.restrict Q).prod (volume.restrict Q)) := by
      rw [Measure.prod_restrict]
      exact (hFc.continuousOn.integrableOn_compact (hKc.prod hKc)).mono_set (prod_mono hQK hQK)
    exact hprod.integral_prod_left
  -- Step 1: the fundamental theorem of calculus along `t ↦ a_k[t]`.
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q,
      |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤
        Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := by
    intro x hx y hy
    set a : Euclid (m + 1) := WithLp.toLp 2 (fun j => if j < k then y j else x j) with ha
    set ℓ : ℝ → Euclid (m + 1) := fun t => a + (t - a k) • EuclideanSpace.single k (1 : ℝ)
      with hℓ
    have hak : a k = x k := by simp [ha]
    have hℓx : ℓ (x k) = a := by simp [hℓ, hak]
    have hℓy : ℓ (y k) = WithLp.toLp 2 (fun j => if j ≤ k then y j else x j) := by
      ext j
      rcases lt_trichotomy j k with h | h | h
      · simp [hℓ, ha, h, le_of_lt h, ne_of_lt h]
      · subst h
        simp [hℓ, ha]
      · simp [hℓ, ha, not_lt.2 (le_of_lt h), not_le.2 h, (ne_of_lt h).symm]
    have hℓd : ∀ t, HasDerivAt ℓ (EuclideanSpace.single k (1 : ℝ)) t := by
      intro t
      have := (((hasDerivAt_id' t).sub_const (a k)).smul_const
        (EuclideanSpace.single k (1 : ℝ))).const_add a
      rw [one_smul] at this
      exact this
    have hderiv : ∀ t, HasDerivAt (fun t => v (ℓ t))
        (fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)) t := fun t =>
      ((hv.differentiable one_ne_zero (ℓ t)).hasFDerivAt).comp_hasDerivAt t (hℓd t)
    have hcont : Continuous fun t => fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1) :=
      (hfd.comp (by fun_prop)).clm_apply continuous_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable (x k) (y k))
    simp only [hℓx, hℓy] at hftc
    have hsub : Set.uIoc (x k) (y k) ⊆ Ioo δ (1 - δ) := by
      intro t ht
      rcases Set.mem_uIoc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [(hx k).1], by linarith [(hy k).2]⟩
      · exact ⟨by linarith [(hy k).1], by linarith [(hx k).2]⟩
    rw [abs_sub_comm, ← hftc]
    calc |∫ t in x k..y k, fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)|
        = ‖∫ t in x k..y k, fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ (t : ℝ) in Set.uIoc (x k) (y k), ‖fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ (t : ℝ) in Ioo δ (1 - δ), ‖fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          setIntegral_mono_set
            (hcont.norm.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
            (Eventually.of_forall fun t => norm_nonneg _) hsub.eventuallyLE
      _ = Φ a := by
          simp only [hΦ, hℓ, ← hupd, Real.norm_eq_abs]
  -- Step 3: integrate the pointwise bound.
  have hstep : ∫ x in Q, ∫ y in Q, |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤
      ∫ x in Q, ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun x => integral_nonneg fun y => abs_nonneg _) hI4 ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hI3 x) ?_
    filter_upwards [ae_restrict_mem hQm] with y hy
    exact hpt x hx y hy
  -- Steps 4–6: the mixed-point and slice identities.
  calc _ ≤ ∫ x in Q, ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := hstep
    _ = (volume Q).toReal * ∫ x in Q, Φ x :=
        Submission.dor_lmb_fcd_cp_mixed_point_integral m δ k Φ hI2
    _ = (volume Q).toReal *
        ((1 - 2 * δ) * ∫ x in Q, |fderiv ℝ v x (EuclideanSpace.single k 1)|) := by
        congr 1
        exact Submission.dor_lmb_fcd_cp_slice_integral m δ k
          (fun p => |fderiv ℝ v p (EuclideanSpace.single k 1)|) hI1
    _ = _ := by ring
/-- **Poincaré inequality on the cube `Q_δ = (δ, 1 − δ)^{m+1}` for `C¹` functions** (the "usual
Poincaré inequality for smooth functions" invoked in Simon Ch. 2, proof of Lemma 2.7, here on a
cube of side `1 − 2δ`):
`∫_Q ∫_Q |v(x) − v(y)| dy dx ≤ (m + 1)(1 − 2δ) Lⁿ(Q) ∫_Q ‖Dv‖`.  Along the coordinate path from
`x` to `y`, `v x − v y` telescopes into the `m + 1` coordinate steps bounded by
`dor_lmb_fcd_cp_coordinate_step`; every integrand is continuous on the compact cube
`[δ, 1 − δ]^{m+1} ⊇ Q`, hence integrable, and `|Dv(x) eₖ| ≤ ‖Dv(x)‖`. -/
theorem dor_lmb_fcd_cp_smooth_poincare : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v x - v y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v δ hv hδ0 hδ
  -- Step 1: telescoping along the coordinate path `W₀ = x, …, W_{m+1} = y`
  have htel : ∀ x y : Euclid (m + 1), v x - v y = ∑ k : Fin (m + 1),
      (v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))) := by
    intro x y
    set W : ℕ → Euclid (m + 1) :=
      fun n => WithLp.toLp 2 (fun j => if (j : ℕ) < n then y j else x j) with hW
    have h0 : W 0 = x := by
      simp [hW]
    have hN : W (m + 1) = y := by
      have hlt : ∀ j : Fin (m + 1), (j : ℕ) < m + 1 := fun j => j.is_lt
      simp only [hW, hlt, ite_true]
    have hk : ∀ k : Fin (m + 1),
        v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
          v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j)) = v (W k) - v (W (k + 1)) := by
      intro k
      have e1 : (fun j : Fin (m + 1) => if j < k then y j else x j) =
          (fun j : Fin (m + 1) => if (j : ℕ) < (k : ℕ) then y j else x j) := by
        funext j
        simp only [Fin.lt_def]
      have e2 : (fun j : Fin (m + 1) => if j ≤ k then y j else x j) =
          (fun j : Fin (m + 1) => if (j : ℕ) < (k : ℕ) + 1 then y j else x j) := by
        funext j
        simp only [Fin.le_iff_val_le_val, Nat.lt_succ_iff]
      rw [e1, e2]
    rw [Finset.sum_congr rfl (fun k _ => hk k),
      Fin.sum_univ_eq_sum_range (fun n => v (W n) - v (W (n + 1))) (m + 1),
      Finset.sum_range_sub', h0, hN]
  have habs : ∀ x y : Euclid (m + 1), |v x - v y| ≤ ∑ k : Fin (m + 1),
      |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| := by
    intro x y
    rw [htel x y]
    exact Finset.abs_sum_le_sum_abs _ _
  -- Step 2: integrability; `Q_δ` lies in the compact cube `K = [δ, 1 − δ]^{m+1}`
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  set K : Set (Euclid (m + 1)) := {y | ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ}
  have hQK : Q ⊆ K := fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hKc : IsCompact K := by
    have hKeq : K = WithLp.toLp 2 '' Set.pi univ (fun _ : Fin (m + 1) => Icc δ (1 - δ)) := by
      ext y
      constructor
      · intro hy
        exact ⟨WithLp.ofLp y, fun i _ => hy i, rfl⟩
      · rintro ⟨z, hz, rfl⟩ i
        exact hz i (mem_univ i)
    rw [hKeq]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hint : ∀ g : Euclid (m + 1) → ℝ, Continuous g → IntegrableOn g Q :=
    fun g hg => (hg.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hint2 : ∀ F : Euclid (m + 1) × Euclid (m + 1) → ℝ, Continuous F →
      Integrable F ((volume.restrict Q).prod (volume.restrict Q)) := by
    intro F hF
    rw [Measure.prod_restrict]
    exact (hF.continuousOn.integrableOn_compact (hKc.prod hKc)).mono_set (prod_mono hQK hQK)
  -- the coordinate points depend continuously on `(x, y)`
  have hlt : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j) : Euclid (m + 1)) := by
    intro k
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_snd)
      fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have hle : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j ≤ k then p.2 j else p.1 j) : Euclid (m + 1)) := by
    intro k
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_snd)
      fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have hF0 : Continuous fun p : Euclid (m + 1) × Euclid (m + 1) => |v p.1 - v p.2| :=
    ((hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)).abs
  have hFk : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      |v (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then p.2 j else p.1 j))| :=
    fun k => ((hv.continuous.comp (hlt k)).sub (hv.continuous.comp (hle k))).abs
  have hfac : 0 ≤ (1 - 2 * δ) * (volume Q).toReal :=
    mul_nonneg (by linarith) ENNReal.toReal_nonneg
  -- Steps 3–4: integrate the telescoping bound, apply `coordinate_step`, and `|Dv eₖ| ≤ ‖Dv‖`
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      ≤ ∫ x in Q, ∑ k : Fin (m + 1), ∫ y in Q,
          |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
            v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| := by
        refine integral_mono (hint2 _ hF0).integral_prod_left
          (integrable_finsetSum _ fun k _ => (hint2 _ (hFk k)).integral_prod_left) fun x => ?_
        have hx : ∀ k : Fin (m + 1), IntegrableOn (fun y : Euclid (m + 1) =>
            |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
              v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))|) Q :=
          fun k => hint _ ((hFk k).comp (Continuous.prodMk_right x))
        exact (integral_mono (hint _ (hF0.comp (Continuous.prodMk_right x)))
          (integrable_finsetSum _ fun k _ => hx k) (habs x)).trans_eq
          (integral_finsetSum _ fun k _ => hx k)
    _ = ∑ k : Fin (m + 1), ∫ x in Q, ∫ y in Q,
          |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
            v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| :=
        integral_finsetSum _ fun k _ => (hint2 _ (hFk k)).integral_prod_left
    _ ≤ ∑ k : Fin (m + 1), (1 - 2 * δ) * (volume Q).toReal *
          ∫ x in Q, |fderiv ℝ v x (EuclideanSpace.single k 1)| :=
        Finset.sum_le_sum fun k _ => Submission.dor_lmb_fcd_cp_coordinate_step m v δ k hv hδ0 hδ
    _ ≤ ∑ _k : Fin (m + 1), (1 - 2 * δ) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ hfac
        have hDv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
        refine integral_mono (hint _ (hDv.clm_apply continuous_const).abs) (hint _ hDv.norm)
          fun x => ?_
        calc |fderiv ℝ v x (EuclideanSpace.single k 1)|
            = ‖fderiv ℝ v x (EuclideanSpace.single k 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ v x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ := (fderiv ℝ v x).le_opNorm _
          _ = ‖fderiv ℝ v x‖ := by simp
    _ = ((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
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
/-- BV Poincaré inequality on the cube `Q_δ = (δ, 1 − δ)^{m+1}` in double-integral form (cf. the
proof of Simon Ch. 2, Lemma 2.7): if `∫_{Q₁} u div g ≤ V` for all smooth `g` with compact support
in `Q₁ = (0, 1)^{m+1}` and `|g| ≤ 1`, then `∫_{Q_δ} ∫_{Q_δ} |u(x) − u(y)| ≤ (m + 1)(1 − 2δ)|Q_δ| V`.
The mollifications `v_k = η_k ∗ 1_{Q₁}u` satisfy this bound by the smooth inequality, and
`v_k → u` a.e. on `Q_δ`, so Fatou's lemma on `Q_δ × Q_δ` passes it to `u`. -/
theorem dor_lmb_fcd_cp_bv_poincare : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : ℕ → Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → δ < 1 / 2 → (∀ k, ContDiff ℝ (⊤ : ℕ∞) (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ k, support (η k) ⊆ ball (0 : Euclid (m + 1)) δ) → (∀ᵐ x ∂volume, Tendsto (fun k => (convolution (η k) (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) atTop (𝓝 ((Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) x))) → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |u x - u y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * V := by
  intro m u V δ η hu hH hδ hδ2 hη hηc hη0 hηe hη1 hηs hlim
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  set C : ℝ := ((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal
  set v : ℕ → Euclid (m + 1) → ℝ := fun k =>
    convolution (η k) (Q₁.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- Step 1: each `v k` is smooth with `∫_Q ‖D v_k‖ ≤ V` (sibling `mollified_variation`).
  have hmv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ ∫ x in Q, ‖fderiv ℝ (v k) x‖ ≤ V := fun k =>
    Submission.dor_lmb_fcd_cp_mollified_variation m u V δ (η k) hu hH hδ (hη k) (hηc k)
      (hη0 k) (hηe k) (hη1 k) (hηs k)
  have hV : 0 ≤ V := (integral_nonneg fun x => norm_nonneg _).trans (hmv 0).2
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 1 - 2 * δ := by linarith
    positivity
  -- Step 2: the smooth Poincaré inequality for `v k` (sibling `smooth_poincare`).
  have hD : ∀ k, ∫ x in Q, ∫ y in Q, |v k x - v k y| ≤ C * V := fun k =>
    (Submission.dor_lmb_fcd_cp_smooth_poincare m (v k) δ
      ((hmv k).1.of_le (by exact_mod_cast le_top)) hδ.le hδ2).trans
      (mul_le_mul_of_nonneg_left (hmv k).2 hC0)
  -- `Q` is a measurable subset of `Q₁` contained in a compact ball.
  have hQQ₁ : Q ⊆ Q₁ := fun y hy i => ⟨hδ.trans (hy i).1, (hy i).2.trans (by linarith)⟩
  have hQm : MeasurableSet Q := by
    have hc : ∀ i : Fin (m + 1), Measurable fun y : Euclid (m + 1) => y i := fun i => by fun_prop
    have hQi : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y
      rw [mem_iInter]
      exact Iff.rfl
    rw [hQi]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hc i)).inter (measurableSet_lt (hc i) measurable_const)
  have hQK : Q ⊆ closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1)) := by
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have h1 := (hy i).1
          have h2 := (hy i).2
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = m + 1 := by simp
  have hK : IsCompact (closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1))) :=
    isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.2 ((measure_mono hQK).trans_lt hK.measure_lt_top).ne
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q
  -- Integrability on `Q × Q`.
  have huQ : Integrable u μ := hu.mono_set hQQ₁
  have hF : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|) (μ.prod μ) :=
    ((huQ.comp_fst μ).sub (huQ.comp_snd μ)).abs
  have hFk : ∀ k, Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => |v k p.1 - v k p.2|)
      (μ.prod μ) := fun k => by
    have hvk : Integrable (v k) μ :=
      (((hmv k).1.continuous.continuousOn).integrableOn_compact hK).mono_set hQK
    exact ((hvk.comp_fst μ).sub (hvk.comp_snd μ)).abs
  -- Step 3: `v k → u` a.e. on `Q`, hence `|v k x - v k y| → |u x - u y|` a.e. on `Q × Q`.
  have hlimQ : ∀ᵐ x ∂μ, Tendsto (fun k => v k x) atTop (𝓝 (u x)) := by
    filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem hQm] with x hx hxQ
    rwa [indicator_of_mem (hQQ₁ hxQ)] at hx
  have hlimP : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun k => ENNReal.ofReal |v k p.1 - v k p.2|) atTop
      (𝓝 (ENNReal.ofReal |u p.1 - u p.2|)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlimQ,
      Measure.quasiMeasurePreserving_snd.ae hlimQ] with p h1 h2
    exact ENNReal.tendsto_ofReal (h1.sub h2).abs
  -- Steps 4–5: Fatou's lemma on `Q × Q` and Fubini.
  have hFatou : ∫⁻ p, ENNReal.ofReal |u p.1 - u p.2| ∂(μ.prod μ) ≤ ENNReal.ofReal (C * V) :=
    calc ∫⁻ p, ENNReal.ofReal |u p.1 - u p.2| ∂(μ.prod μ)
        = ∫⁻ p, liminf (fun k => ENNReal.ofReal |v k p.1 - v k p.2|) atTop ∂(μ.prod μ) :=
          lintegral_congr_ae (hlimP.mono fun p hp => hp.liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ p, ENNReal.ofReal |v k p.1 - v k p.2| ∂(μ.prod μ)) atTop :=
          lintegral_liminf_le' fun k => (hFk k).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (C * V) := liminf_le_of_frequently_le' (Frequently.of_forall fun k => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hFk k) (ae_of_all _ fun p => abs_nonneg _),
            integral_prod _ (hFk k)]
          exact ENNReal.ofReal_le_ofReal (hD k))
  have hfin : ENNReal.ofReal (∫ x in Q, ∫ y in Q, |u x - u y|) ≤ ENNReal.ofReal (C * V) := by
    rw [← integral_prod (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|) hF,
      ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun p => abs_nonneg _)]
    exact hFatou
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 hV)).1 hfin
/-- Shrinking the unit cube `Q₁ = (0, 1)ᵐ⁺¹` to `Q_δ = (δ, 1 − δ)ᵐ⁺¹` while keeping half of the
`L¹` norm of `f` (Simon Ch. 2, proof of Lemma 2.7).  The cubes `Q_{1/(j+4)}` are open and
increase to `Q₁`, so continuity of the measure from above and of the integral along increasing
unions give one `j` for both the layer bound and the integral bound. -/
theorem dor_lmb_fcd_cp_shrinking : ∀ (m : ℕ) (f : Euclid (m + 1) → ℝ), IntegrableOn f {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} ≤ 1 ∧ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \ {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}) ≤ 1 / 4 ∧ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |f y| := by
  intro m f hf
  -- Step 1: `Q_t` is open, `Q_t ⊆ Q₁` for `t ≥ 0`, and `volume Q₁ = 1`.
  have hopen : ∀ t : ℝ, IsOpen {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} := by
    intro t
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hmeas : ∀ t : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} :=
    fun t => (hopen t).measurableSet
  have hmeas₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    simpa using hmeas 0
  have hsub : ∀ t : ℝ, 0 ≤ t → {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun t ht y hy i =>
    ⟨ht.trans_lt (hy i).1, (hy i).2.trans_le (by linarith)⟩
  have hvol₁ : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
    have hpre : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
        WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Set.mem_pi]
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  -- Step 2: `δ_j = 1/(j+4)` decreases to `0`, and the cubes `Q_{δ_j}` increase to `Q₁`.
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun j : ℕ => 1 / ((j : ℝ) + 4) := ⟨_, rfl⟩
  have hδpos : ∀ j, 0 < δ j := fun j => by rw [hδdef]; positivity
  have hδle : ∀ j, δ j ≤ 1 / 4 := fun j => by
    simp only [hδdef]
    gcongr
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hδanti : Antitone δ := fun j k hjk => by
    simp only [hδdef]
    gcongr
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    rw [hδdef]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hmono : Monotone fun j => {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j} :=
    fun j k hjk y hy i =>
      ⟨(hδanti hjk).trans_lt (hy i).1, (hy i).2.trans_le (by linarith [hδanti hjk])⟩
  have hunion : ⋃ j, {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j} =
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    refine Subset.antisymm (iUnion_subset fun j => hsub _ (hδpos j).le) fun y hy => ?_
    have hev : ∀ᶠ j in atTop, ∀ i, δ j < y i ∧ y i < 1 - δ j := by
      rw [eventually_all]
      intro i
      filter_upwards [(tendsto_order.1 hδlim).2 _ (hy i).1,
        (tendsto_order.1 hδlim).2 _ (sub_pos.2 (hy i).2)] with j hj₁ hj₂
      exact ⟨hj₁, by linarith⟩
    obtain ⟨j, hj⟩ := hev.exists
    exact mem_iUnion.2 ⟨j, hj⟩
  -- Step 3: continuity from above, `volume (Q₁ \ Q_{δ_j}) → 0`.
  have hlayer : Tendsto (fun j => volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
      {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j})) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := volume)
      (s := fun j => {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
        {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j})
      (fun j => (hmeas₁.diff (hmeas _)).nullMeasurableSet)
      (fun j k hjk => Set.sdiff_subset_sdiff_right (hmono hjk))
      ⟨0, ((measure_mono Set.sdiff_subset).trans_lt (by rw [hvol₁]; exact ENNReal.one_lt_top)).ne⟩
    rw [← Set.sdiff_iUnion, hunion, Set.sdiff_self, measure_empty] at h
    exact h
  have hev₁ : ∀ᶠ j in atTop, volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
      {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}) < 1 / 4 :=
    (tendsto_order.1 hlayer).2 _ (by norm_num)
  -- Step 4: continuity of the integral, `∫_{Q_{δ_j}} |f| → ∫_{Q₁} |f|`.
  have hint : Tendsto (fun j => ∫ y in {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}, |f y|)
      atTop (𝓝 (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y|)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume) (f := fun y => |f y|)
      (fun j => hmeas (δ j)) hmono (by rw [hunion]; exact hf.abs)
    rw [hunion] at h
    exact h
  have hev₂ : ∀ᶠ j in atTop, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤
      2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}, |f y| := by
    rcases (integral_nonneg fun y => abs_nonneg (f y) :
        0 ≤ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y|).eq_or_lt with h₀ | hpos
    · exact Eventually.of_forall fun j => by
        rw [← h₀]
        exact mul_nonneg zero_le_two (integral_nonneg fun y => abs_nonneg (f y))
    · filter_upwards [(tendsto_order.1 hint).1 _ (half_lt_self hpos)] with j hj
      linarith
  -- Step 5: one `j` works for both bounds.
  obtain ⟨j, hj₁, hj₂⟩ := (hev₁.and hev₂).exists
  exact ⟨δ j, hδpos j, hδle j, (measure_mono (hsub _ (hδpos j).le)).trans hvol₁.le, hj₁.le, hj₂⟩

/-- **Poincaré inequality with an integer median on the unit cube** (Simon Ch. 2, Lemma 2.7 with
`θ = 1/4`, and the choice (31), (35) of `β_F` in the proof of the Deformation Theorem, Ch. 6, 5.1):
there is `c = c(m) > 0` such that every integer-valued `u` integrable on `Q₁ = (0, 1)^{m+1}` with
`∫_{Q₁} u div g ≤ V` for all smooth `g` with compact support in `Q₁` and `|g| ≤ 1` has an integer
`β` with `∫_{Q₁} |u − β| ≤ c V` and `|β| ≤ 2 ∫_{Q₁} |u|`.  Take the integer median `β`
(`dor_lmb_fcd_cp_integer_median`) and shrink `Q₁` to `Q_δ = (δ, 1 − δ)^{m+1}`, keeping half of
`∫ |u − β|` with `Lⁿ(Q₁ \ Q_δ) ≤ 1/4` (`dor_lmb_fcd_cp_shrinking`), so `β` is a `¼`-median of `u`
on `Q_δ`.  Normalized bumps of radius `δ/(k + 2)` give the BV Poincaré inequality on `Q_δ`
(`dor_lmb_fcd_cp_bv_poincare`), and `dor_lmb_fcd_cp_median_deviation` gives
`∫_{Q₁} |u − β| ≤ 2 ∫_{Q_δ} |u − β| ≤ 2 · 5 (m + 1)(1 − 2δ) V ≤ 10 (m + 1) V`. -/
theorem dor_lmb_fcd_cube_poincare : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m
  refine ⟨10 * ((m : ℝ) + 1), by positivity, ?_⟩
  intro u V hZ hu hH
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  -- Step 0: `V ≥ 0` (test `g = 0`); `{a < yᵢ < b}` is the preimage of the box `(a, b)ⁿ`, so it is
  -- measurable, and `Lⁿ(Q₁) = 1`
  have hV : 0 ≤ V := by
    have h0 := hH (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa using h0
  have hpre : ∀ a b : ℝ, {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} =
      WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo a b) := fun a b => by
    ext y
    simp [Set.mem_pi]
  have hmeas : ∀ a b : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} :=
    fun a b => by
      rw [hpre]
      exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hvol₁ : volume Q₁ = 1 := by
    rw [hQ₁, hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  -- Step 1: the integer median `β` of `u` on `Q₁` (Simon (31), (35))
  obtain ⟨β, hβge, hβle, hβbd⟩ := dor_lmb_fcd_cp_integer_median m u hZ hu
  refine ⟨β, ?_, hβbd⟩
  -- Step 2: shrink `Q₁` to `Q = Q_δ`, keeping half of `∫_{Q₁} |u − β|`
  have hf : IntegrableOn (fun y => u y - β) Q₁ :=
    hu.sub (integrableOn_const (by rw [hvol₁]; exact ENNReal.one_ne_top))
  obtain ⟨δ, hδ0, hδ4, hQ1, hlayer, hhalf⟩ := dor_lmb_fcd_cp_shrinking m (fun y => u y - β) hf
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  have hQQ₁ : Q ⊆ Q₁ := fun y hy i => ⟨hδ0.trans (hy i).1, (hy i).2.trans (by linarith)⟩
  have hQfin : volume Q ≠ ∞ := (hQ1.trans_lt ENNReal.one_lt_top).ne
  -- Step 3: median transfer, `Lⁿ(Q ∩ A) ≥ Lⁿ(Q₁ ∩ A) − Lⁿ(Q₁ \ Q) ≥ 1/4 ≥ ¼ Lⁿ(Q)` for
  -- `A = {β ≤ u}` and `A = {u ≤ β}`; in particular `Lⁿ(Q) > 0`
  have hq1 : (volume Q).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hQ1
    rwa [ENNReal.toReal_one] at h
  have htransfer : ∀ A : Set (Euclid (m + 1)), 1 / 2 ≤ volume (Q₁ ∩ A) →
      1 / 4 ≤ (volume (Q ∩ A)).toReal := by
    intro A hA
    have hsub : Q₁ ∩ A ⊆ (Q ∩ A) ∪ (Q₁ \ Q) := fun y hy => by
      by_cases hyQ : y ∈ Q
      · exact Or.inl ⟨hyQ, hy.2⟩
      · exact Or.inr ⟨hy.1, hyQ⟩
    have h1 : 1 / 2 ≤ volume (Q ∩ A) + 1 / 4 :=
      hA.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hlayer)))
    have hfinA : volume (Q ∩ A) ≠ ∞ :=
      ((measure_mono inter_subset_left).trans_lt (hQ1.trans_lt ENNReal.one_lt_top)).ne
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinA, by norm_num⟩) h1
    rw [ENNReal.toReal_add hfinA (by norm_num)] at h2
    have h3 : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
    have h4 : ((1 : ℝ≥0∞) / 4).toReal = 1 / 4 := by norm_num
    rw [h3, h4] at h2
    linarith
  have hge : 1 / 4 * (volume Q).toReal ≤ (volume (Q ∩ {y | (β : ℝ) ≤ u y})).toReal := by
    linarith [htransfer _ hβge]
  have hle : 1 / 4 * (volume Q).toReal ≤ (volume (Q ∩ {y | u y ≤ (β : ℝ)})).toReal := by
    linarith [htransfer _ hβle]
  have hqpos : 0 < (volume Q).toReal := by
    have h : (volume (Q ∩ {y | (β : ℝ) ≤ u y})).toReal ≤ (volume Q).toReal :=
      ENNReal.toReal_mono hQfin (measure_mono inter_subset_left)
    linarith [htransfer _ hβge]
  -- Step 4: deviation from the `¼`-median `β` on `Q` (Simon 2.7)
  have hdev := dor_lmb_fcd_cp_median_deviation (m + 1) Q u β (1 / 4) (hmeas δ (1 - δ)) hQfin
    (hu.mono_set hQQ₁) (by norm_num) hge hle
  -- Step 5: normalized bumps `η_k` of radius `δ/(k + 2)`; their mollifications of `1_{Q₁} u`
  -- converge a.e. (Lebesgue differentiation), so the BV Poincaré inequality holds on `Q`
  let φ : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    { rIn := δ / ((k : ℝ) + 2) / 2
      rOut := δ / ((k : ℝ) + 2)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : 0 < δ / ((k : ℝ) + 2) := by positivity
        linarith }
  have hφ0 : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hφK : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn :=
    Eventually.of_forall fun k => by
      change δ / ((k : ℝ) + 2) ≤ 2 * (δ / ((k : ℝ) + 2) / 2)
      linarith
  have hφs : ∀ k, support ((φ k).normed volume) ⊆ ball (0 : Euclid (m + 1)) δ := fun k => by
    rw [(φ k).support_normed_eq]
    exact ball_subset_ball (div_le_self hδ0.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hφ0 hφK (hu.integrable_indicator (hmeas 0 1)).locallyIntegrable
  have hbv := dor_lmb_fcd_cp_bv_poincare m u V δ (fun k => (φ k).normed volume) hu hH hδ0
    (by linarith) (fun k => (φ k).contDiff_normed) (fun k => (φ k).hasCompactSupport_normed)
    (fun k => (φ k).nonneg_normed) (fun k => (φ k).normed_neg) (fun k => (φ k).integral_normed)
    hφs hae
  -- Step 6: `∫_{Q₁} |u − β| ≤ 2 ∫_Q |u − β| ≤ 2 · 5 (m + 1)(1 − 2δ) V ≤ 10 (m + 1) V`
  have hQbd : ∫ y in Q, |u y - β| ≤ 5 * ((m : ℝ) + 1) * V := by
    have hmδV : 0 ≤ ((m : ℝ) + 1) * δ * V := by positivity
    calc ∫ y in Q, |u y - β|
        ≤ (1 + (1 / 4 : ℝ)⁻¹) * ((volume Q).toReal)⁻¹ * ∫ x in Q, ∫ y in Q, |u x - u y| := hdev
      _ ≤ (1 + (1 / 4 : ℝ)⁻¹) * ((volume Q).toReal)⁻¹ *
            (((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal * V) :=
          mul_le_mul_of_nonneg_left hbv (by positivity)
      _ = 5 * ((m : ℝ) + 1) * (1 - 2 * δ) * V * (((volume Q).toReal)⁻¹ * (volume Q).toReal) := by
          ring
      _ = 5 * ((m : ℝ) + 1) * (1 - 2 * δ) * V := by rw [inv_mul_cancel₀ hqpos.ne', mul_one]
      _ ≤ 5 * ((m : ℝ) + 1) * V := by linarith
  calc ∫ y in Q₁, |u y - β| ≤ 2 * ∫ y in Q, |u y - β| := hhalf
    _ ≤ 2 * (5 * ((m : ℝ) + 1) * V) := by gcongr
    _ = 10 * ((m : ℝ) + 1) * V := by ring

end Submission

end GMT.Ch07
