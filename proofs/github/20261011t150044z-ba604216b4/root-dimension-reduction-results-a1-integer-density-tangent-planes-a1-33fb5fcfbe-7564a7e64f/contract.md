<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.tangent_cones-a1.blowup_compactness-a1 -->

## Theorem `Submission.idtp_fons_blowUp_compactness`

Let ℓ ≤ k, n ≥ 1, U ⊆ ℝ^{n+k} open, N ⊆ ℝ^{n+k} an embedded C² (n+ℓ)-dimensional submanifold (IsEmbeddedSubmanifold 2 (n+ℓ) N) with (N̄ ∖ N) ∩ U = ∅, T ∈ 𝒟_n(U) minimizing in U ∩ N with spt T ⊆ U ∩ N, x ∈ spt T ∖ spt ∂T, and θ ∈ ℝ with HasMassDensity T x θ. Then for every sequence λ_j > 0 with λ_j → 0 there are a strictly increasing φ : ℕ → ℕ and C ∈ 𝒟_n(ℝ^{n+k}) such that S_j := η_{x,λ_{φ(j)}#}T (blowUp) satisfy S_j ⇀ C in ℝ^{n+k} (ConvergesWeakly), μ_{S_j} → μ_C as Radon measures for all integer multiplicity representations (MassMeasuresConverge), C is integer multiplicity and minimizing in ℝ^{n+k} (IsMinimizingIn C univ), and ∂C = 0 (BoundaryVanishes C).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.tangent_cones-a1.blowup_compactness-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5836

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/808, https://github.com/ZhengyangZhang06/gmt-formalize/issues/813, https://github.com/ZhengyangZhang06/gmt-formalize/issues/818

Decomposition children: None

## Lean problem

Declaration: `Submission.idtp_fons_blowUp_compactness`

```lean
∀ (n k ℓ : ℕ), ℓ ≤ k → 0 < n → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n) (x : Euclid (n + k)) (θ : ℝ), IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → x ∈ T.support \ boundarySupport T → HasMassDensity T x θ → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.tangent_cones-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.tangent_cones-a1.blowup_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Registration note (context, not part of the numbered proof). This child is a fresh registration, under the new Lean name idtp_fons_blowUp_compactness, of a frozen type byte-identical to that of DAG node root.density_and_tangent_cones-a1.blowup_compactness-a1 (Submission.dtc_blowUp_compactness, status speculative-ready), which is not comparator-accepted and is owned by another parent, so the runtime forbids sharing its name here. The numbered proof below is that node's parent-supplied natural proof, accepted in the decomposition audit of root.density_and_tangent_cones-a1, reproduced unchanged. Its 'parent proof' is step 4 (Lemma BC) of the proof of the selected node root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.tangent_cones-a1, which coincides with step 4 of the proof of root.density_and_tangent_cones-a1; its siblings vanish_off_support (V), mass_eq_measure (M), im_sub (G) and blowup_scaling (BU) are the identically keyed, comparator-accepted siblings of this split (Submission.dtc_vanish_off_support, Submission.dtc_mass_eq_measure, Submission.dtc_isIntegerMultiplicity_sub, Submission.dtc_blowUp_scaling). The comparator-accepted lemmas of the audited split of the identically typed node (Submission.dtc_bc_measure_restrict_eq_of_eqOn, Submission.dtc_bc_tendsto_integral_of_limsup_liminf, Submission.dtc_bc_local_retraction, Submission.dtc_bc_minimizing_of_local_comparison) may be reused by exact type; the numbered proof below is complete without them.

Source: step 4 of the parent proof (Lemma BC, Remark 7.2.5(2) for N_j = η_{x_j,λ_j}(N), whose proof Simon "leaves to the reader"), specialized to x_j = x, which is all that the parent uses in step 5; it re-runs the proof of Simon 7.2.4 (chapter-07.txt lines 177–270, equations (1)–(14)) and replaces footnote 2 of 7.3.1 (competitors are arbitrary in ℝ^{n+k}, pushed into η(N) by retractions, so no projection onto T_xN is needed). Cited results: Simon Ch. 6, 2.14 (lower semicontinuity of mass; SimonGMT WeaklyConvergesOn.massOn_le_liminf), 2.24 and 2.29 (push-forward and its boundary and mass), 2.34 (Constancy Theorem), 3.3–3.9 and the remark after 3.9 (push-forward of integer multiplicity currents), 3.11 (Federer–Fleming compactness), 4.5 (slicing), 7.2 (weak = flat convergence), and the tubular neighbourhood theorem for C² submanifolds (the nearest-point projection is C¹; cf. Simon 7.5, chapter-07.txt lines 783–786). Siblings used: vanish_off_support (V), mass_eq_measure (M), im_sub (G), blowup_scaling (BU). Write η_j := η_{x,λ_j} and S_j := η_{j#}T; the output subsequence is chosen in step 2.3.
0. Preliminaries.
 0.1 x ∈ spt T ⊆ U ∩ N and x ∉ spt ∂T; spt ∂T is relatively closed in U, so there is r > 0 with closedBall(x, 2r) ⊆ U and ball(x, 2r) ∩ spt ∂T = ∅.
 0.2 By BU, each S_j is integer multiplicity and minimizing in η_j(U ∩ N), and M_{η_j(W)}(S_j) = λ_j^{−n}M_W(T); in particular M_{B_R(0)}(S_j) = λ_j^{−n}M_{B_{λ_jR}(x)}(T), since η_j(B_{λ_jR}(x)) = B_R(0). As η_j(U) ⊇ η_j(B_{2r}(x)) = B_{2r/λ_j}(0), every compact subset of ℝ^{n+k} lies in η_j(U) for large j.
 0.3 Mass bound. As M_{B_s(x)}(T)/(ω_n sⁿ) → θ for s ↓ 0, there is s₀ ∈ (0, r) with M_{B_s(x)}(T) ≤ ω_n(θ + 1)sⁿ for 0 < s < s₀. Hence for every R > 0 and every j with λ_jR < s₀: M_{B_R(0)}(S_j) ≤ cRⁿ, c := ω_n(θ + 1).
 0.4 Boundary. ∂S_j = η_{j#}∂T (SimonGMT boundary_affinePushforward). For ω ∈ 𝒟^{n−1}(η_j(U)) with tsupport ω ⊆ B_{2r/λ_j}(0), tsupport(η_j^#ω) = η_j⁻¹(tsupport ω) ⊆ B_{2r}(x) is disjoint from spt ∂T, so ∂S_j(ω) = ∂T(η_j^#ω) = 0 by V. Thus ∂S_j = 0 in B_{2r/λ_j}(0), and 2r/λ_j → ∞.
 0.5 Measures. If Y is integer multiplicity in an open V and R₁, R₂ represent Y, then μ_{R₁} = μ_{R₂}: by M both equal M_W(Y) on every open W ⊆ V, both vanish outside V and are finite on compact subsets of V; the open subsets of V form a π-system generating the Borel sets of V, and V is a countable union of open sets of finite measure, so the measures agree on all Borel sets. Write μ_Y for this measure; μ_Y(W) = M_W(Y) for open W ⊆ V. Consequences: (i) μ_Y(V ∖ spt Y) = 0, since V ∖ spt Y is open and every admissible form supported there is annihilated by Y (V), so M_{V∖spt Y}(Y) = 0. (ii) If Y (in V) and Y' (in an open V') are integer multiplicity and agree on an open W₀ ⊆ V ∩ V' (same values on forms supported in W₀), then μ_Y and μ_{Y'} agree on Borel subsets of W₀ (apply the first assertion to the restrictions to W₀, which are represented by the representations with carriers intersected with W₀). (iii) For integer multiplicity A, B in V (so A ± B integer multiplicity by G) and Borel E ⊆ V: μ_{A±B}(E) ≤ μ_A(E) + μ_B(E) — for open E because M_E(A ± B) ≤ M_E(A) + M_E(B) directly from the definition of M_E as a supremum, and for Borel E by outer regularity of these measures (finite on compact subsets of V). (iv) For open W₀ ⊆ V, A⌞W₀ (represented by the representation of A with carrier intersected with W₀) is integer multiplicity and μ_{A⌞W₀} = μ_A⌞W₀.
 0.6 spt S_j ⊆ η_j(spt T) ⊆ η_j(N): if ω ∈ 𝒟ⁿ(η_j(U)) has tsupport disjoint from the relatively closed set η_j(spt T), then tsupport(η_j^#ω) is disjoint from spt T, so S_j(ω) = T(η_j^#ω) = 0 by V. With 0.5(i), μ_{S_j} is carried by η_j(N).
1. The case k = 0. Then ℓ = 0, ℝ^{n+k} = ℝⁿ, and T has ∂T = 0 in the connected open set B_{2r}(x) (0.1). By the Constancy Theorem (Ch. 6, 2.34) T = c[[B_{2r}(x)]] in B_{2r}(x) (standard orientation e₁∧…∧eₙ) for a constant c. Writing T = τ(M, θ, ξ) with ξ = ±e₁∧…∧eₙ a.e., the uniqueness of densities (the signed measures θξ(e¹∧…∧eⁿ)Hⁿ⌞M and cLⁿ agree on C_c^∞(B_{2r}(x))) gives θξ(e¹∧…∧eⁿ)1_M = c a.e. on B_{2r}(x), so c ∈ ℤ, and c ≠ 0 because x ∈ spt T. Then S_j = c[[ℝⁿ]] in B_{2r/λ_j}(0) (η_j preserves the orientation and Lebesgue measure transforms by λ_j^{−n}), and C := c[[ℝⁿ]] works with φ := id: C is integer multiplicity with ∂C = 0; ConvergesWeakly holds since each ω ∈ 𝒟ⁿ(ℝⁿ) is eventually supported in B_{2r/λ_j}(0) where S_j = C; for f ∈ C_c(ℝⁿ), ∫f dμ_{S_j} = ∫ f |c| dLⁿ = ∫ f dμ_C for large j (0.5(ii)), so MassMeasuresConverge holds for all representations (0.5); and C is minimizing in ℝⁿ: if S is integer multiplicity with ∂S = ∂C = 0 and spt(S − C) compact, the Constancy Theorem on the connected ℝⁿ gives S − C = c'[[ℝⁿ]] with compact support, so c' = 0, S = C and M_W(C) = M_W(S). Assume k ≥ 1 from now on (so all cited results of Ch. 6 §3 are used in their stated range).
2. Truncation and compactness.
 2.1 Put ρ_j := min(j + 1, r/λ_j) > 0, so ρ_j → ∞. By slicing (Ch. 6, 4.5(1)–(2)) applied to the integer multiplicity current S_j in the open ball B_{2r/λ_j}(0), where ∂S_j = 0, with the 1-Lipschitz function |·|: for a.e. t ∈ (0, 2r/λ_j) the slice ⟨S_j, |·|, t⟩ is integer multiplicity, ⟨S_j, |·|, t⟩ = ∂(S_j⌞B_t(0)) in B_{2r/λ_j}(0), and ∫_0^{ρ_j} M(⟨S_j, |·|, t⟩) dt ≤ M_{B_{ρ_j}(0)}(S_j) < ∞ (finite because closedBall(0, ρ_j) ⊆ η_j(closedBall(x, r)) is a compact subset of η_j(U) and S_j has locally finite mass by M). Choose ρ'_j ∈ (ρ_j/2, ρ_j) with M(⟨S_j, |·|, ρ'_j⟩) < ∞ and the slice identity.
 2.2 Let (M_j, θ_j, ξ_j) represent S_j and let Ŝ_j ∈ 𝒟_n(ℝ^{n+k}) be the current represented by (M_j ∩ B_{ρ'_j}(0), θ_j, ξ_j) (an IMRep in ℝ^{n+k}: the carrier lies in the compact closedBall(0, ρ'_j) ⊆ η_j(U), so it has finite θ_j-weighted measure; at points of the open ball the approximate tangent spaces are those of M_j). Ŝ_j = S_j in B_{ρ'_j}(0); ∂Ŝ_j is the slice ⟨S_j, |·|, ρ'_j⟩ (for ω ∈ 𝒟^{n−1}(ℝ^{n+k}) take ω₁ := χω with χ ∈ C_c^∞(B_{2r/λ_j}(0)), χ = 1 near closedBall(0, ρ'_j); then Ŝ_j(dω) = Ŝ_j(dω₁) = ⟨S_j, |·|, ρ'_j⟩(ω₁)), supported on ∂B_{ρ'_j}(0) with finite mass. Consequently, for every bounded open W ⊆ B_R(0): M_W(Ŝ_j) ≤ cRⁿ when λ_jR < s₀, and M_W(Ŝ_j) ≤ M(Ŝ_j) < ∞ for the finitely many other j; M_W(∂Ŝ_j) = 0 when W ⊆ B_{ρ'_j}(0) (all large j) and ≤ M(⟨S_j, |·|, ρ'_j⟩) < ∞ otherwise. Thus sup_j (M_W(Ŝ_j) + M_W(∂Ŝ_j)) < ∞ for every W ⊂⊂ ℝ^{n+k}.
 2.3 By the Federer–Fleming compactness theorem (Ch. 6, 3.11) in U = ℝ^{n+k} there are a strictly increasing φ : ℕ → ℕ and an integer multiplicity C ∈ 𝒟_n(ℝ^{n+k}) with Ŝ_{φ(j)} ⇀ C. Relabel so that S_j, Ŝ_j, λ_j, ρ'_j denote the φ-subsequence (all properties above persist).
 2.4 ConvergesWeakly: for ω ∈ 𝒟ⁿ(ℝ^{n+k}), tsupport ω ⊆ B_{ρ'_j}(0) ⊆ η_j(U) for all large j, so currentEval(S_j, ω) = S_j(ω) = Ŝ_j(ω) → C(ω).
 2.5 ∂C = 0: for ω ∈ 𝒟^{n−1}, ∂C(ω) = C(dω) = lim Ŝ_j(dω) = lim ∂Ŝ_j(ω) = 0, since tsupport ω ⊆ B_{ρ'_j}(0) for large j. So BoundaryVanishes C.
 2.6 M_{B_R(0)}(C) ≤ liminf_j M_{B_R(0)}(Ŝ_j) ≤ cRⁿ for every R (Ch. 6, 2.14).
3. Retractions onto η_j(N).
 3.1 Since x ∈ N, N is an embedded C² submanifold, and N ∩ U is relatively closed in U ((N̄ ∖ N) ∩ U = ∅), the tubular neighbourhood theorem gives δ ∈ (0, r) and a C¹ map π : B_{2δ}(x) → N (the nearest-point projection onto N) with π(y) = y for y ∈ N ∩ B_{2δ}(x), |π(y) − y| = dist(y, N), and Dπ(y) = p_{T_yN} for y ∈ N ∩ B_{2δ}(x); in particular ‖Dπ(x)‖ = 1. Put ω_π(s) := sup_{B_s(x)} ‖Dπ − Dπ(x)‖ for 0 < s ≤ δ; ω_π(s) → 0 as s ↓ 0 (continuity of Dπ), and since B_s(x) is convex, Lip(π|_{B_s(x)}) ≤ 1 + ω_π(s).
 3.2 For large j define π_j := η_j ∘ π ∘ η_j⁻¹ on B_{2δ/λ_j}(0): a C¹ map into η_j(N) with π_j = Id on η_j(N) ∩ B_{2δ/λ_j}(0). For each fixed G > 0 and j with λ_jG ≤ δ, |π_j(z) − π_j(z')| = λ_j⁻¹|π(x + λ_jz) − π(x + λ_jz')| ≤ L_j|z − z'| on B_G(0), with L_j := 1 + ω_π(λ_jG) ≥ 1 and L_j → 1. Moreover |π_j(z) − z| = λ_j⁻¹dist(x + λ_jz, N) ≤ |z| (as x ∈ N), so |π_j(z)| ≤ 2|z|.
4. Comparison (proof of 7.2.4, adapted).
 4.1 Fix a compact K ⊆ ℝ^{n+k} and ε ∈ (0, 1). Choose smooth ψ : ℝ^{n+k} → [0,1] with ψ = 1 on a neighbourhood of K and spt ψ ⊆ {dist(·, K) < ε}, and set W_s := {ψ > s} (0 ≤ s < 1), so K ⊆ W_s ⊂⊂ ℝ^{n+k}. Fix G > 0 with spt ψ ⊆ B_{G/3}(0), and j₀ such that for j ≥ j₀: λ_jG < min(s₀, δ/2), B_G(0) ⊂⊂ η_j(U), and closedBall(0, G) ⊆ B_{ρ'_j}(0); then π_j(spt ψ) ⊆ B_{2G/3}(0) for j ≥ j₀.
 4.2 By Ch. 6, 7.2 (applicable by 2.2–2.3), d_{W₀}(Ŝ_j, C) → 0: C − Ŝ_j = ∂R_j + S'_j with R_j ∈ 𝒟_{n+1}(ℝ^{n+k}), S'_j ∈ 𝒟_n(ℝ^{n+k}) integer multiplicity and M_{W₀}(R_j) + M_{W₀}(S'_j) → 0; ∂R_j = C − Ŝ_j − S'_j has locally finite mass.
 4.3 Slicing R_j by ψ (Ch. 6, 4.5; book (3)–(5)): there are α ∈ (0, 1) and a further subsequence (used only inside steps 4–6) with ∂(R_j⌞W_α) = (∂R_j)⌞W_α + P_j, P_j integer multiplicity, spt P_j ⊆ ∂W_α, M(P_j) → 0, and μ_{Ŝ_j}(∂W_α) = 0 for all j, μ_C(∂W_α) = 0 (only countably many levels carry mass). Then (book (6)–(7)) C⌞W_α = Ŝ_j⌞W_α + ∂R̃_j + S̃_j with R̃_j := R_j⌞W_α and S̃_j := S'_j⌞W_α − P_j integer multiplicity (0.5(iv), G) and M(R̃_j) + M(S̃_j) → 0. For j ≥ j₀, W̄_α ⊆ B_G(0) ⊆ B_{ρ'_j}(0), so Ŝ_j may be replaced by S_j in all statements localized to B_G(0); in particular μ_{S_j}(∂W_α) = 0.
 4.4 Let X ∈ 𝒟_n(ℝ^{n+k}) be integer multiplicity with ∂X = 0 and spt X ⊆ K. Put Y_j := X + ∂R̃_j; ∂R̃_j = (C − Ŝ_j)⌞W_α − S̃_j is integer multiplicity (0.5(iv), G), so Y_j is integer multiplicity with spt Y_j ⊆ W̄_α, M(Y_j) < ∞ and ∂Y_j = 0. Regard Y_j as a current in B_{δ/λ_j}(0) ⊇ W̄_α (j ≥ j₀). π_j is Lipschitz there and proper on the compact spt Y_j, so by Ch. 6, 2.29 the push-forward π_{j#}Y_j := lim_{σ↓0} (π_j^{(σ)})_#Y_j (π_j^{(σ)} the mollified maps) exists, with ∂π_{j#}Y_j = lim_{σ↓0}(π_j^{(σ)})_#∂Y_j = 0 (2.24(1) for the smooth maps π_j^{(σ)}), spt π_{j#}Y_j ⊆ π_j(spt Y_j) ⊆ η_j(N) ∩ B_{2G/3}(0), and M(π_{j#}Y_j) ≤ L_jⁿM(Y_j); for the C¹ map π_j it agrees with the formula of 2.24(2)/3.3, and by 3.9 it is integer multiplicity. Regard π_{j#}Y_j as a current in η_j(U) (its support is a compact subset of B_G(0) ⊂⊂ η_j(U)) and let Z_j := S_j + π_{j#}Y_j, integer multiplicity by G (Z_j = S_j − (0 − π_{j#}Y_j)). Then spt(Z_j − S_j) is a compact subset of η_j(U ∩ N) ∩ B_G(0) and ∂Z_j = ∂S_j, so minimality of S_j in η_j(U ∩ N) (0.2) with W := B_G(0) gives μ_{S_j}(B_G(0)) ≤ μ_{Z_j}(B_G(0)).
 4.5 π_{j#}(S_j⌞B_G(0)) = S_j⌞B_G(0): by 0.6 and 0.5(i), Hⁿ(M_j ∖ η_j(N)) = 0, so at Hⁿ-a.e. y ∈ M_j ∩ B_G(0) the approximate tangent plane T_yM_j equals that of M_j ∩ η_j(N); for a set A contained in the embedded C¹ submanifold N' := η_j(N) ∩ B_{2δ/λ_j}(0) and a point y ∈ A where T_yA exists, T_yA ⊆ T_yN' (the blow-ups η_{y,s}(N') converge locally in Hausdorff distance to T_yN', so ∫_{T_yA} f dHⁿ = lim ∫_{η_{y,s}(A)} f dHⁿ = 0 for every f ≥ 0 in C_c supported away from T_yN'), and dπ_j(y) = p_{T_yN'} is the identity on T_yN'. The push-forward formula (Ch. 6, 2.24(2), 3.3–3.9: f_#Q(ω) = ∫⟨ω(f(y)), d^Mf_{y#}ξ(y)⟩θ dHⁿ) therefore gives π_{j#}(S_j⌞B_G(0)) = S_j⌞B_G(0) (π_j(y) = y and d^Mπ_{j#}ξ(y) = ξ(y) a.e.). Hence Z_j⌞B_G(0) = π_{j#}((S_j + Y_j)⌞B_G(0)) and μ_{Z_j}(B_G(0)) ≤ L_jⁿ·μ_{S_j+Y_j}(B_G(0)) (mass bound of 2.29 with Lip ≤ L_j on B_G(0)).
 4.6 Comparison off W_α (book (9)–(11)). Since spt Y_j ⊆ W̄_α ⊆ B_G(0), μ_{S_j}(∂W_α) = 0, and 0.5(ii)–(iv): μ_{S_j}(B_G) = μ_{S_j}(W_α) + μ_{S_j}(B_G ∖ W̄_α); μ_{S_j+Y_j}(B_G) ≤ μ_{S_j+Y_j}(W_α) + μ_{Y_j}(∂W_α) + μ_{S_j}(B_G ∖ W̄_α); μ_{Y_j}(∂W_α) ≤ μ_X(∂W_α) + μ_{(∂R_j)⌞W_α}(∂W_α) + μ_{P_j}(∂W_α) = M(P_j) (spt X ⊆ K ⊆ W_α, and (∂R_j)⌞W_α is carried by the open set W_α); and, because S_j + Y_j = C + X − S̃_j in W_α, μ_{S_j+Y_j}(W_α) ≤ μ_{C+X}(W_α) + M(S̃_j). Combining with 4.4–4.5 and subtracting the finite μ_{S_j}(B_G ∖ W̄_α) (L_j ≥ 1): μ_{S_j}(W_α) ≤ μ_{C+X}(W_α) + M(S̃_j) + M(P_j) + (L_jⁿ − 1)Λ_G for j ≥ j₀, where Λ_G := sup_{j≥j₀}[μ_{C+X}(W_α) + M(S̃_j) + M(P_j) + μ_{S_j}(B_G)] ≤ 2cGⁿ + M(X) + sup_{j≥j₀}(M(S̃_j) + M(P_j)) < ∞ (0.3, 2.6). So μ_{S_j}(W_α) ≤ μ_{C+X}(W_α) + ε_j with ε_j → 0.
 4.7 By 2.14, μ_C(W_α) = M_{W_α}(C) ≤ liminf_j M_{W_α}(Ŝ_j) = liminf_j μ_{S_j}(W_α) ≤ μ_{C+X}(W_α) (book (8)).
5. Minimality of C. C is integer multiplicity (2.3). Let W be open with compact closure, S ∈ 𝒟_n(ℝ^{n+k}) integer multiplicity with ∂S = ∂C and spt(S − C) compact ⊆ W. X := S − C is integer multiplicity (G) with ∂X = 0 and K := spt X ⊆ W. Run step 4 with this K and ε < dist(K, ℝ^{n+k} ∖ W), so K ⊆ W_α ⊆ W, and get μ_C(W_α) ≤ μ_S(W_α). As S = C on the open set W ∖ K, μ_S and μ_C agree on Borel subsets of W ∖ K (0.5(ii)), in particular on W ∖ W_α. Hence M_W(C) = μ_C(W_α) + μ_C(W ∖ W_α) ≤ μ_S(W_α) + μ_S(W ∖ W_α) = M_W(S) (M). So IsMinimizingIn C univ.
6. Mass convergence.
 6.1 With X = 0, 4.6 gives μ_{S_j}(K) ≤ μ_{S_j}(W_α) ≤ μ_C(W_α) + ε_j ≤ μ_C({dist(·, K) < ε}) + ε_j along the further subsequence of 4.3. Since steps 4.1–4.6 apply to any subsequence of (S_j), every subsequence has a further subsequence along which lim sup μ_{S_j}(K) ≤ μ_C({dist(·, K) < ε}); hence this holds for the whole sequence, and letting ε ↓ 0, lim sup_j μ_{S_j}(K) ≤ μ_C(K) for every compact K (book (13)).
 6.2 For bounded open W, μ_C(W) = M_W(C) ≤ liminf M_W(Ŝ_j) = liminf μ_{S_j}(W) (2.14; Ŝ_j = S_j on W for large j) (book (14)).
 6.3 For f ∈ C_c(ℝ^{n+k}), f ≥ 0, with spt f ⊆ B_R(0): ∫f dμ = ∫_0^{max f} μ({f > t}) dt = ∫_0^{max f} μ({f ≥ t}) dt for μ = μ_C and μ = μ_{S_j} (layer cake; the two integrands differ only at the countably many t with μ({f = t}) > 0). Fatou with 6.2 for the bounded open sets {f > t} gives liminf ∫f dμ_{S_j} ≥ ∫f dμ_C; reverse Fatou (μ_{S_j}({f ≥ t}) ≤ μ_{S_j}(B_R(0)) ≤ cRⁿ for large j) with 6.1 for the compact sets {f ≥ t} gives lim sup ∫f dμ_{S_j} ≤ ∫f dμ_C. Splitting f = f⁺ − f⁻ gives ∫f dμ_{S_j} → ∫f dμ_C for every f ∈ C_c(ℝ^{n+k}).
 6.4 By 0.5, for arbitrary representations R_j of S_j and R of C, μ_{R_j} = μ_{S_j} and μ_R = μ_C; so MassMeasuresConverge holds.
7. Output: the strictly increasing φ of step 2.3, the current C, ConvergesWeakly (2.4), MassMeasuresConverge (6.4), IsMinimizingIn C univ (5) and BoundaryVanishes C (2.5) (for k = 0: step 1). The further subsequences of 4.3 are used only inside the proofs of 5 and 6.1.

## Key steps

1. Blow-ups are integer multiplicity, minimizing in η_j(U ∩ N), boundaryless on B_{2r/λ_j}(0), with M_{B_R(0)} ≤ cRⁿ from the density bound at x.
2. Truncate at good slicing radii and apply Federer–Fleming compactness in ℝ^{n+k} to get C, integer multiplicity, ∂C = 0, with weak convergence of the blow-ups.
3. Proof of 7.2.4 with retractions π_j onto η_j(N) (Lip → 1): flat decomposition, slicing, competitor S_j + π_{j#}(X + ∂R̃_j), giving μ_C(W_α) ≤ μ_{C+X}(W_α).
4. Conclude minimality of C in ℝ^{n+k}, limsup/liminf mass bounds, and convergence of the mass measures for all representations.

## Reference use

### local-project

Queries:
- `python3 -I -c 'json.load(open("local-references/123e8435b4a2469b/manifest.json"))'`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git log -1 --format=%H`
- `rg -n 'DensityAndTangentCones|IsConeCurrent|def blowUp|def HasMassDensity|def MassMeasuresConverge|def ConvergesWeakly' local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n -i 'federer|fleming|compactness|monotonicity|constancy|slic|tangent cone|blowUp|blow-up' local-references/123e8435b4a2469b/project/GMT -t lean`
- `rg -n 'theorem upperSemicontinuousOn_const|theorem Ioo_mem_nhdsGT|theorem fderiv_id |theorem notMem_empty' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'massOn_le_liminf|theorem GeometricCurrentOn.boundary_affinePushforward|def GeometricCurrentOn.restrictDomain' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `python3 scan of dag.json (updated_at 2026-10-13T19:27:35Z): status, lean_name, lean_statement, depends_on, children, candidate_commit of root.density_and_tangent_cones-a1, its ten children, the eight children of root.density_and_tangent_cones-a1.blowup_compactness-a1, root.minimizing_implies_stationary-a1, and the twelve children of root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1`
- `python3 extraction of subproblem fields from nodes/root-density-and-tangent-cones-a1-{mass-eq-measure,vanish-off-support,im-sub,blowup-scaling,dim-zero,localize,density-usc,blowup-compactness,blowup-density,cone}-a1/parent-child-handoff.json and of the verdicts in nodes/root-density-and-tangent-cones-a1/decomposition-audit-v1.json`
- `isolated-comparator-result.json and tail of comparator-v1.log for the nine accepted dtc_ nodes; permitted_axioms in cluster-state/verification/results/hoa63/20261013T050058Z-ch07-root.density_and_tangent_cones-a1.cone-a1-mfeckvv8/comparator-config.json`
- `git show a78eb69b43d2cb80577081e099cb2b15d96cabbe -- GMT/Ch07/Submission.lean`
- `grep -n '_existing_lean_name_problem|def _accepted_checkpoint|def _overlay_accepted_children|def _dependency_problem|def _install_parent_supplied_child_handoff|def _solve_children' /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py; sed -n 251,290p /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/store.py`
- `grep -c idtp_fons_blowUp_compactness dag.json; grep -rl 'idtp_fons_blowUp_compactness\|idtp_fons_blowup_compactness' nodes GMT .lake/packages/simongmt; xargs grep -l over ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (1534 files)`
- `lake env lean /tmp/tc_split_check/Types.lean; lake env lean /tmp/tc_split_check/AssemblyAx.lean`
- `python3 replay of Runtime._dependency_problem, Runtime._topological and Runtime._existing_lean_name_problem on the ten proposed subproblems against dag.json`
- `sed -n 160,180p and sed -n 300,366p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Semicontinuity/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c115a9274a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-density-usc-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-density-usc-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/verification/results/hoa63/20261013T050058Z-ch07-root.density_and_tangent_cones-a1.cone-a1-mfeckvv8/comparator-config.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/store.py`
- `/tmp/tc_split_check/Types.lean`
- `/tmp/tc_split_check/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`

Pins match. The manifest records project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, which is the workspace HEAD, and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace Contract.lean, which equals Submission.lean. In the snapshot, Ch04 (StationaryMonotonicity, BoundedCurvatureMonotonicity) and Ch06 (FedererFlemingCompactness, SlicingTheorem, ConstancyTheorem) are unproved specifications (main_theorem := by sorry) over a different ambient type, Eucl P; no library declaration proves Simon 7.3.1, Lemma BC or 7.2.4 for the contract's currents. SimonGMT supplies only WeaklyConvergesOn.massOn_le_liminf (Mass.lean:100), GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188) and restrictDomain (CurrentLocalEquality.lean:40). The snapshot Mathlib has upperSemicontinuousOn_const (Topology/Semicontinuity/Defs.lean:508), fderiv_id (Analysis/Calculus/FDeriv/Basic.lean:715) and Set.notMem_empty (Data/Set/Basic.lean:324), which the assembly uses. The identically typed node root.density_and_tangent_cones-a1 has an audited ten-child split (decomposition-audit-v1: all acceptable). Nine of those children are accepted with candidate commits, passed the isolated comparator with the Lean kernel (permitted axioms propext, Quot.sound, Classical.choice), and have DAG types identical to their handoffs: dtc_mass_eq_measure bff81d31, dtc_vanish_off_support 44ef61f7, dtc_isIntegerMultiplicity_sub 77fcc7d4, dtc_blowUp_scaling a94d596c, dtc_dim_zero_eq_zero 7f446789, dtc_localize 3b14aa45, dtc_density_usc 4cc9fd94, dtc_blowUp_density 13c3e6ac and dtc_cone_of_constant_density 47d40434. dtc_blowUp_compactness is speculative-ready under another parent. Its accepted grandchildren are dtc_bc_measure_restrict_eq_of_eqOn, dtc_bc_tendsto_integral_of_limsup_liminf, dtc_bc_local_retraction and dtc_bc_minimizing_of_local_comparison. The runtime (_existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff) permits reusing accepted names with identical types and requires a fresh name otherwise. idtp_fons_blowUp_compactness does not occur in dag.json, nodes, GMT, simongmt or any of the 1534 worktree Submission.lean files. Lean v4.35.0-rc3: all ten child types elaborate after import GMT.Ch07.Submission in the contract's namespace and opens. The adapted speculative assembly (a78eb69b) compiles, and #print axioms lists exactly dtc_blowUp_density, dtc_cone_of_constant_density, dtc_density_usc, dtc_dim_zero_eq_zero, dtc_localize, idtp_fons_blowUp_compactness and idtp_fons_minimizing_stationary, plus propext, Classical.choice and Quot.sound. A replay of the runtime's key, name, dependency and topological checks reports no problems. The book's 7.3.1 proof (chapter-07.txt lines 326–360) and Remark 2.5(2) (lines 166–174) match the children's roles.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
