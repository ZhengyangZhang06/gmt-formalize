<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1 -->

## Theorem `Submission.dimred_integer_density_and_tangent_planes`

IntegerDensityAndTangentPlanes of the frozen contract (Simon 7.3.3, with README erratum 4: E ⊆ F). For all n, k, ℓ ∈ ℕ with ℓ ≤ k, all sets U, N ⊆ ℝ^{n+k} and every T ∈ 𝒟_n(U): if U is open, N is an embedded C² (n+ℓ)-dimensional submanifold (IsEmbeddedSubmanifold 2 (n + ℓ) N), (closure N ∖ N) ∩ U = ∅, T is minimizing in U ∩ N, spt T ⊆ U ∩ N and ∂T = 0 in U (BoundaryVanishes T), then there exist sets E ⊆ F ⊆ ℝ^{n+k} such that μH[n − 3 + α](E) = 0 for every real α > 0; for every x ∈ U ∖ E there is an integer m with HasMassDensity T x m; μH[n − 2 + α](F) = 0 for every real α > 0; and HasTangentPlaneAt T x for every x ∈ spt T ∖ F.

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/374

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1016, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1017, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1018, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1024, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1026, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1030

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4777, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4780, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4782, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4789, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4800, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4821, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4833, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4838, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4842, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4857

## Lean problem

Declaration: `Submission.dimred_integer_density_and_tangent_planes`

```lean
IntegerDensityAndTangentPlanes
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

- Parent DAG node: `root.dimension_reduction_results-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 0, A1–A5 (Simon 7.3.3, Remark 3.4, Lemma 3.5 and the proofs of 3.3(1), 3.3(2), chapter-07.txt lines 367–583), with the errata of the parent: E ⊆ F (README 4); in R_β (line 524) the bound is sup|q(y − x)| < βρ; in 3.3(2)(12),(13) the union ∪_j R_{β_j} must read the intersection ∩_j R_{β_j}; departures [D1] (scalar density functions, flatness map whose domain is recovered from the total mass and barycenter) and [D2] (flatness and exceptional sets per rescaled ball, F their countable union); the classification of 2-dimensional minimizing cones [Whi82] is used as cited by the book (lines 501–504; see also S. X. Chang, J. Amer. Math. Soc. 1 (1988), Appendix A, pp. 761–762). P := n + k; for an integer multiplicity A, μ_A is the measure of any representation (all representations have the same measure), M_W(A) = μ_A(W) for open W and spt A = spt μ_A (sibling child im_mass_measure (c), (a), (b)); Θ_A := Θ^n(μ_A, ·); ω_n := unitBallVolume n; η_{y,λ}(w) := λ^{−1}(w − y); H^n := μHE[n] = c_nμH[n], c_n ∈ (0, ∞).
0. (n = 0.) By the sibling child zero_dim_vanishing (A := U ∩ N; T is minimizing in U ∩ N and spt T ⊆ U ∩ N), T = 0. Take E = F := ∅: μH[s](∅) = 0 for every s; for x ∈ U, HasMassDensity 0 x 0 (all masses of the zero current vanish), with m := 0 ∈ ℤ; and spt 0 = ∅, so the tangent-plane condition is vacuous. From now on n ≥ 1.
1. (A1: densities.) Since n ≥ 1 and ∂T = 0, boundarySupport T = spt 0 = ∅. By the sibling child monotonicity (d := n + ℓ), there is Θ : ℝ^P → ℝ with HasMassDensity T x (Θ(x)) for x ∈ U, Θ upper semicontinuous on U, Θ ≥ 0, and Θ ≥ 1 on spt T; for each compact K ⊆ U there is Λ_K ≥ 0 such that e^{Λ_Kρ}ρ^{−n}μ_T(B_ρ(y)) is nondecreasing on (0, R) whenever closedBall y R ⊆ K. Put E := {x ∈ U : Θ(x) ∉ ℤ}. For x ∈ U ∖ E, m := Θ(x) ∈ ℤ satisfies HasMassDensity T x m.
2. (Uniform density bounds; parent T10.) Let K ⊆ U be compact with Θ < θ₁ on K, let θ₂ > θ₁, and let K'' ⊆ U be a compact set containing a 2σ₀-neighbourhood of K (σ₀ > 0). Then there is ρ₀ > 0 with μ_T(B_ρ(y)) ≤ θ₂ω_nρ^n for y ∈ K and ρ < ρ₀. Proof: for y ∈ K choose ρ_y ∈ (0, σ₀) with e^{Λρ_y}μ_T(B_{ρ_y}(y))/(ω_nρ_y^n) < θ₁ (Λ := Λ_{K''}; possible because the ratio tends to Θ(y) < θ₁ and e^{Λρ} → 1), and τ_y ∈ (0, ρ_y) with θ₁(ρ_y/(ρ_y − τ_y))^n ≤ θ₂. For |y' − y| < τ_y and ρ < ρ_y − τ_y, monotonicity at y' (closedBall y' ρ_y ⊆ K'') and B_{ρ_y−τ_y}(y') ⊆ B_{ρ_y}(y) give e^{Λρ}μ_T(B_ρ(y'))/(ω_nρ^n) ≤ e^{Λρ_y}μ_T(B_{ρ_y}(y))/(ω_n(ρ_y − τ_y)^n) < θ₁(ρ_y/(ρ_y − τ_y))^n ≤ θ₂. Cover K by finitely many B_{τ_y}(y) and let ρ₀ be the least ρ_y − τ_y.
3. (Densities of admissible zero-scale limits.) Let z ∈ ℝ^P, r > 0, θ₂ > 0 and ρ₀ > 0 be such that μ_T(B_ρ(y)) ≤ θ₂ω_nρ^n for y ∈ B_{3r/2}(z) and ρ < ρ₀. Let x_i ∈ B_r(z), λ_i → 0⁺ and S ∈ 𝒟_n(ℝ^P) with blowUp T x_i λ_i ⇀ S (ConvergesWeakly), S minimizing in ℝ^P with ∂S = 0. Then Θ_S ≤ θ₂ everywhere and Θ_S ∈ ℤ_{≥1} μ_S-a.e. Proof: for w ∈ ℝ^P and ρ > 0, for large i, x_i + λ_iw ∈ B_{3r/2}(z) and λ_iρ < ρ₀; the blow-up masses scale as M_{B_ρ(w)}(blowUp T x_i λ_i) = λ_i^{−n}M_{B_{λ_iρ}(x_i+λ_iw)}(T) ≤ θ₂ω_nρ^n. For every admissible ω for M_{B_ρ(w)}(S), S(ω) = lim currentEval(blowUp T x_i λ_i, ω) ≤ liminf M_{B_ρ(w)}(blowUp T x_i λ_i), so M_{B_ρ(w)}(S) ≤ θ₂ω_nρ^n and Θ_S(w) ≤ θ₂ (Θ_S exists everywhere by the sibling child monotonicity with U = N = ℝ^P). Θ_S equals the multiplicity of S μ_S-a.e. (Simon Ch. 3, Theorem 1.9; Ch. 4, Remark 1.8(2)), a positive integer.
4. (A2: μH[n−3+α](E) = 0, and E = ∅ if n ≤ 2.) For m ∈ ℕ, m ≥ 1, and β ∈ ℚ ∩ (0, 1/2) let U_{m,β} := {x ∈ U : Θ(x) < m − β} (open, by upper semicontinuity) and E_{m,β} := {x ∈ U_{m,β} : Θ(x) ≥ m − 1 + β}. Every x ∈ E has Θ(x) ∈ (m − 1, m) for some integer m ≥ 1 (Θ ≥ 0), and then x ∈ E_{m,β} for every rational β < min(1/2, Θ(x) − m + 1, m − Θ(x)); so E = ∪_{m,β}E_{m,β}, a countable union. Fix (m, β) and x₀ ∈ U_{m,β}; choose σ > 0 with closedBall x₀ (4σ) ⊆ U_{m,β}. By step 2 (K := closedBall x₀ (3σ/2), K'' := closedBall x₀ (4σ), θ₁ := m − β, θ₂ := m − β/2) there is ρ₀ > 0 with μ_T(B_ρ(y)) ≤ (m − β/2)ω_nρ^n for y ∈ B_{3σ/2}(x₀), ρ < ρ₀. Apply the sibling child threshold_reduction with z := x₀, r := σ (closedBall x₀ (2σ) ⊆ U), c := m − 1 + β > 0 and d₀ := n − 2 (natural subtraction). Hypothesis (H1): let S be an admissible zero-scale limit (centres x_i ∈ B_σ(x₀), scales → 0, minimizing, ∂S = 0) with Θ_S = c'·1_Q, Q an n-dimensional subspace, c' ≥ c. By step 3, Θ_S ≤ m − β/2 and Θ_S ∈ ℤ_{≥1} μ_S-a.e. As Θ_S = c' > 0 on Q, Q ⊆ spt S, so μ_S ≠ 0 and there is y with Θ_S(y) ∈ ℤ_{≥1}; then y ∈ Q and c' = Θ_S(y) ∈ ℤ. But m − 1 < m − 1 + β ≤ c' ≤ m − β/2 < m: no integer, a contradiction. Hypothesis (H2): let S be an admissible zero-scale limit and L a subspace with d₀ ≤ d := dim L < n, with L-invariant density function and {Θ_S ≥ c} = L. By step 3, Θ_S ≤ m − β/2; as 0 ∈ L, Θ_S(0) ≥ m − 1 + β. Since n − 2 ≤ d (if n ≥ 2; if n = 1 then d = 0 = n − 1), n − d ∈ {1, 2}. By the sibling child cone_splitting (dim L < n, S minimizing with ∂S = 0, density invariance), there is S₀ ∈ 𝒟_{n−d}(ℝ^P), minimizing in ℝ^P, ∂S₀ = 0, a cone, with Θ_S(0) = Θ_{S₀}(0) (t = 0, y = 0). If n − d = 1, the sibling child one_dim_cones (applied to S₀, transported to degree 1) gives e and m' ∈ ℕ with HasMassDensity S₀ y m' for y ∈ span{e} ∋ 0, so Θ_S(0) = m' ∈ ℤ. If n − d = 2, S₀ is a 2-dimensional integer multiplicity area-minimizing cone with ∂S₀ = 0; by the classification of such cones [Whi82] (as cited in Simon, lines 501–504), spt S₀ ⊆ P_1 ∪ ⋯ ∪ P_q with 2-planes P_i, P_i ∩ P_j = {0} (i ≠ j), and by the constancy theorem (Ch. 6, 2.34) on the connected sets P_i ∖ {0} (and μ_{S₀}({0}) = 0) S₀ = Σ_i m_i[[P_i]] with m_i ∈ ℤ, so μ_{S₀} = Σ_i|m_i|H^2⌞P_i and Θ_{S₀}(0) = Σ_i|m_i| ∈ ℤ. Either way Θ_S(0) ∈ ℤ ∩ [m − 1 + β, m − β/2] = ∅: a contradiction. Hence threshold_reduction gives: if n ≥ 3 (d₀ = n − 2 ≥ 1), μH[n − 3 + α](Z) = 0 for α > 0, and if n ≤ 2 (d₀ = 0), Z = ∅, where Z := {x ∈ B_σ(x₀) : Θ(x) ≥ m − 1 + β} ⊇ E_{m,β} ∩ B_σ(x₀). By Lindelöf, countably many such balls B_σ(x₀) cover U_{m,β}. Hence, by countable subadditivity, μH[n − 3 + α](E) = 0 for all α > 0 if n ≥ 3, and E = ∅ if n ≤ 2 (so μH[n − 3 + α](E) = 0 for every real exponent).
5. (A3: the flatness class for one ball.) Let 𝒞 := {(z, r) : z ∈ ℚ^P, r ∈ ℚ_{>0}, closedBall z (2r) ⊆ U}; the balls B_r(z), (z, r) ∈ 𝒞, cover U. Fix (z, r) ∈ 𝒞 and let T' be the restriction of blowUp T z r to B_2(0): T' is integer multiplicity, minimizing in B_2(0) ∩ η_{z,r}(N), spt T' ⊆ η_{z,r}(N), ∂T' = 0 in B_2(0), Θ_{T'}(w) = Θ(z + rw), m₀ := μ_{T'}(B_2(0)) < ∞, and with Λ₀ := rΛ_{closedBall z (2r)}, e^{Λ₀ρ}ρ^{−n}μ_{T'}(B_ρ(y)) is nondecreasing on (0, R) whenever closedBall y R ⊆ closedBall 0 2. If T' = 0 put F'_{z,r} := ∅. Otherwise let b₀ be the barycenter of μ_{T'} and let 𝒯 be the class of pairs (S, U_S) arising as follows: x_i ∈ ℝ^P, λ_i ∈ (0, 1), |x_i| < 1 − λ_i, x_i → x, λ_i → λ ∈ [0, 1], U_S := η_{x,λ}(B_2(0)) if λ > 0 and U_S := ℝ^P if λ = 0, S ∈ 𝒟_n(U_S), and (η_{x_i,λ_i#}T')(ω) → S(ω) for every ω ∈ 𝒟^n(U_S) (with tsupport ω eventually inside η_{x_i,λ_i}(B_2(0))). These members have the following properties (parent T4, T5). (a) If λ > 0, then S = η_{x,λ#}T' (for ω ∈ 𝒟^n(U_S), η_{x_i,λ_i}^#ω → η_{x,λ}^#ω in 𝒟^n(B_2(0))), U_S ⊇ B_2(0) (as |x| ≤ 1 − λ), μ_S(ℝ^P) = λ^{−n}m₀ ∈ (0, ∞), spt μ_S ⊆ closedBall (−x/λ) (2/λ), the barycenter of μ_S is (b₀ − x)/λ, Θ_S(w) = Θ(z + r(x + λw)) ≥ 1 for w ∈ spt S, and e^{Λ₀ρ}ρ^{−n}μ_S(B_ρ(y)) is nondecreasing on (0, R) whenever closedBall y R ⊆ closure(U_S) (because η_{x,λ}^{−1}(closedBall y R) = closedBall (x + λy) (λR) ⊆ closedBall 0 2 and λΛ₀ ≤ Λ₀); (T', B_2(0)) ∈ 𝒯 (x_i = 0, λ_i = 1 − 1/(i + 2)). (b) If λ = 0, then, since η_{x_i,λ_i}∘η_{z,r} = η_{z+rx_i,rλ_i} and the domains η_{x_i,λ_i}(B_2(0)) eventually contain every compact set, S is the ConvergesWeakly-limit of blowUp T (z + rx_i) (rλ_i); by the sibling child moving_blowups (centre z + rx ∈ closedBall z r ⊆ U) and uniqueness of weak limits, S is integer multiplicity, minimizing in ℝ^P, ∂S = 0, and μ_{η_{x_i,λ_i#}T'} → μ_S vaguely (every subsequence has a further subsequence with measure convergence); by the sibling child monotonicity (U = N = ℝ^P, d := P), ρ^{−n}μ_S(B_ρ(w)) is nondecreasing on (0, ∞), Θ_S exists everywhere and is upper semicontinuous, Θ_S ≥ 1 on spt S, so μ_S(B_ρ(w)) ≥ ω_nρ^n for w ∈ spt S and μ_S(ℝ^P) ∈ {0, ∞}. (c) For a member with parameters (x, λ), 0 < λ' < 1 and |y| ≤ 1 − λ', (η_{y,λ'#}S, η_{y,λ'}(U_S)) ∈ 𝒯 with parameters (x + λy, λλ'), because η_{y,λ'}∘η_{x_i,λ_i} = η_{x_i+λ_iy,λ_iλ'} and |x_i + λ_iy| < 1 − λ_iλ'. (d) (Uniform bounds; countable-test convergence criterion.) c₁ := e^{Λ₀}(4/3)^nm₀ bounds e^{Λ₀ρ}ρ^{−n}μ_{T'}(B_ρ(y)) for |y| ≤ 1 and 0 < ρ ≤ 3/4 (monotonicity on (0, 1) at y, as closedBall y 1 ⊆ closedBall 0 2, compared with ρ = 3/4). Put c₂ := max(c₁, 2^nm₀). Then μ_A(B_R(0)) ≤ c₂R^n for every R > 0 whenever A = η_{x',λ'#}T' with |x'| ≤ 1 and λ' ∈ (0, 1] (μ_A extended by 0 off the domain of A: μ_A(B_R(0)) = λ'^{−n}μ_{T'}(B_{λ'R}(x')), which is ≤ c₁R^n if λ'R ≤ 1/2 and ≤ λ'^{−n}m₀ < (2R)^nm₀ otherwise); in particular for every member with λ > 0 (A = η_{x,λ#}T', |x| ≤ 1 − λ, λ ≤ 1) and for every blow-up η_{x_i,λ_i#}T' occurring in the definition of 𝒯; for members with λ = 0 the bound follows by lower semicontinuity of mass under the defining convergence (for ω admissible for M_{B_R(0)}(S), S(ω) = lim_i (η_{x_i,λ_i#}T')(ω) ≤ liminf_i M_{B_R(0)}(η_{x_i,λ_i#}T') ≤ c₂R^n); and M_{B_R(0)}(A) = μ_A(B_R(0)) whenever B_R(0) lies in the domain of A (sibling child im_mass_measure (a)). (Countable-test criterion for limits on ℝ^P approximated by currents whose domains exhaust ℝ^P.) Fix a countable family {ω_m} ⊆ 𝒟^n(ℝ^P) such that for every R ∈ ℕ, every ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ B_R(0) and every ε > 0 there is m with tsupport ω_m ⊆ B_{R+1}(0) and sup_w |ω(w) − ω_m(w)| < ε (|·| the Euclidean coefficient norm); for instance the forms χ_R·Σ_I p_I dx^I (R ∈ ℕ, I increasing multi-indices) with a fixed χ_R ∈ C^∞_c(B_{R+1}(0); [0, 1]) equal to 1 on closedBall 0 R and polynomials p_I with rational coefficients: approximate the coefficients of ω uniformly on closedBall 0 (R + 1) by such p_I (Weierstrass); since ω = 0 off B_R(0) and χ_R = 1 on closedBall 0 R, sup|ω − χ_R·p| ≤ sup_{closedBall 0 (R+1)}|ω − p|. Criterion (C): let V_k ⊆ ℝ^P be open, A_k ∈ 𝒟_n(V_k) and A ∈ 𝒟_n(ℝ^P), and suppose that for every R ∈ ℕ there are k_R ∈ ℕ and Γ_R < ∞ with B_{R+1}(0) ⊆ V_k and M_{B_{R+1}(0)}(A_k) ≤ Γ_R for all k ≥ k_R, and M_{B_{R+1}(0)}(A) ≤ Γ_R. If A_k(ω_m) → A(ω_m) for every m (for k ≥ k_R these values are defined when tsupport ω_m ⊆ B_{R+1}(0)), then currentEval(A_k, ω) → A(ω) for every ω ∈ 𝒟^n(ℝ^P), i.e. A_k ⇀ A in ℝ^P (ConvergesWeakly). Proof: let tsupport ω ⊆ B_R(0) and ε > 0, and choose ω_m as above. For k ≥ k_R, tsupport ω ⊆ V_k, so currentEval(A_k, ω) = A_k(ω); a test form β with tsupport β ⊆ W (W open) and sup|β| ≤ s satisfies |A'(β)| ≤ s·M_W(A') for every current A' (if s > 0, ±β/s is admissible for M_W(A')), so |A_k(ω) − A_k(ω_m)| ≤ Γ_Rε and |A(ω) − A(ω_m)| ≤ Γ_Rε; hence limsup_k |currentEval(A_k, ω) − A(ω)| ≤ 2Γ_Rε for every ε > 0. (The criterion is used only for limits on all of ℝ^P approximated by currents whose domains exhaust ℝ^P, and no metric for weak convergence on varying bounded domains is used: for a limit on a bounded domain, currentEval vanishes at the limit on a form whose support meets the boundary of the limit domain, although it need not vanish along the approximants. For example, in ℝ (n = P = 1) let λ_i ↑ 1, A_i := [[(−2/λ_i, 2/λ_i)]] ∈ 𝒟_1((−2/λ_i, 2/λ_i)) and A := [[(−2, 2)]] ∈ 𝒟_1((−2, 2)): A_i ⇀ A in (−2, 2) and μ_{A_i} → μ_A vaguely there, but for ω = g dx with spt g = [−2, 2] and ∫g > 0, currentEval(A_i, ω) = ∫g > 0 for every i while currentEval(A, ω) = 0.) (e) (Tangent cones of members.) Let (S, U_S) ∈ 𝒯 have parameters (x, λ), |y| < 1 and λ_k ↓ 0. Case λ > 0. Since η_{y,λ_k}∘η_{x,λ} = η_{x+λy,λλ_k}, η_{y,λ_k#}S = η_{x+λy,λλ_k#}T'; these are the restrictions to η_{x+λy,λλ_k}(B_2(0)) of the blow-ups blowUp T (z + r(x + λy)) (rλλ_k) of T at z + r(x + λy) ∈ B_r(z) (|x + λy| < 1 − λ + λ = 1) with scales rλλ_k → 0, and their domains η_{x+λy,λλ_k}(B_2(0)) ⊇ B_{(2−|x+λy|)/(λλ_k)}(0) exhaust ℝ^P. If z + r(x + λy) ∈ spt T, the sibling density_and_tangent_cones (2) (boundarySupport T = ∅) gives a strictly increasing subsequence along which these blow-ups converge weakly in ℝ^P (ConvergesWeakly), with convergence of the mass measures (MassMeasuresConverge), to a minimizing cone C; otherwise T vanishes on a ball around z + r(x + λy), the blow-ups vanish on every ball B_R(0) for large k, and C := 0. Because every compact set eventually lies in η_{x+λy,λλ_k}(B_2(0)), on which η_{y,λ_k#}S agrees with the blow-up of T, η_{y,λ_k#}S ⇀ C in ℝ^P and μ_{η_{y,λ_k#}S} → μ_C vaguely on ℝ^P along the subsequence; and C is a member with parameters (x + λy, 0) via the sequence x'_k := x + λy, λ'_k := λλ_k (k so large that λλ_k < 1 − |x + λy|): for every ω ∈ 𝒟^n(ℝ^P), tsupport ω ⊆ η_{x'_k,λ'_k}(B_2(0)) for large k and (η_{x'_k,λ'_k#}T')(ω) = currentEval(blowUp T (z + r(x + λy)) (rλλ_k), ω) → C(ω). Case λ = 0. By (b), S is integer multiplicity and minimizing in ℝ^P with ∂S = 0. If y ∈ spt S, the sibling density_and_tangent_cones (2) (U = N = ℝ^P, ℓ := k, the codimension P − n) gives a strictly increasing subsequence along which η_{y,λ_k#}S ⇀ C in ℝ^P and μ_{η_{y,λ_k#}S} → μ_C vaguely, C a minimizing cone; if y ∉ spt S, η_{y,λ_k#}S vanishes on every B_R(0) for large k and C := 0. Diagonal selection: pass to that subsequence, discard the k with λ_k ≥ 1 − |y|, and let (x_i, s_i) be a defining sequence of S (x_i → x, s_i ∈ (0, 1), s_i → 0, |x_i| < 1 − s_i, and η_{x_i,s_i#}T' → S in the sense of the definition of 𝒯; the letter s_i is used to distinguish these scales from the tangent scales λ_k). For each k and i put A_{k,i} := η_{x_i+s_iy,s_iλ_k#}T', a current on η_{x_i+s_iy,s_iλ_k}(B_2(0)). As η_{y,λ_k}∘η_{x_i,s_i} = η_{x_i+s_iy,s_iλ_k}, A_{k,i}(ω) = (η_{x_i,s_i#}T')(η_{y,λ_k}^#ω) whenever tsupport ω lies in the domain of A_{k,i}; since η_{y,λ_k}^#ω ∈ 𝒟^n(ℝ^P), the defining property of S gives, for fixed k and ω ∈ 𝒟^n(ℝ^P): tsupport ω lies in the domain of A_{k,i} for all large i, and A_{k,i}(ω) → S(η_{y,λ_k}^#ω) = (η_{y,λ_k#}S)(ω) as i → ∞. Choose i(1) < i(2) < ⋯ with s_{i(k)} < 1/k, |x_{i(k)} − x| < 1/k, and, for all m ≤ k, tsupport ω_m inside the domain of A_{k,i(k)} and |A_{k,i(k)}(ω_m) − (η_{y,λ_k#}S)(ω_m)| < 1/k (finitely many conditions, each holding for all large i). Put D_k := A_{k,i(k)}, x'_k := x_{i(k)} + s_{i(k)}y and λ'_k := s_{i(k)}λ_k. Then λ'_k ∈ (0, 1), λ'_k → 0, x'_k → x, and |x'_k| < 1 − s_{i(k)} + s_{i(k)}|y| ≤ 1 − s_{i(k)}λ_k = 1 − λ'_k (as |y| ≤ 1 − λ_k). Eventual support containment: the domain of D_k is η_{x'_k,λ'_k}(B_2(0)) = B_{2/λ'_k}(−x'_k/λ'_k) ⊇ B_{1/λ'_k}(0) because |x'_k| < 1, so every compact subset of ℝ^P lies in the domain of D_k for all large k. Mass bounds: by (d), M_{B_{R+1}(0)}(D_k) ≤ c₂(R + 1)^n as soon as B_{R+1}(0) lies in the domain of D_k, and M_{B_{R+1}(0)}(C) ≤ liminf_k M_{B_{R+1}(0)}(η_{y,λ_k#}S) ≤ c₂(R + 1)^n by lower semicontinuity of mass, η_{y,λ_k#}S being a member by (c) (0 < λ_k < 1, |y| ≤ 1 − λ_k). Tests: for each m and all k ≥ m, |D_k(ω_m) − C(ω_m)| < 1/k + |(η_{y,λ_k#}S)(ω_m) − C(ω_m)| → 0. By criterion (C) of (d), D_k ⇀ C in ℝ^P, i.e. for every ω ∈ 𝒟^n(ℝ^P), tsupport ω ⊆ η_{x'_k,λ'_k}(B_2(0)) for large k and (η_{x'_k,λ'_k#}T')(ω) → C(ω): C is a member with parameters (x, 0) = (x + λy, 0). In both cases, along the chosen strictly increasing subsequence, μ_{η_{y,λ_k#}S} → μ_C vaguely on ℝ^P and C is a cone. (f) A member with μ_S ≠ 0 and μ_S(λA) = λ^nμ_S(A) for all λ > 0, or with μ_S(ℝ^P) = ∞, has parameter 0 (members with λ > 0 have finite positive total mass, which a nonzero n-homogeneous measure cannot have). Density functions (parent T5). Let e₁ be the unit vector of Euclid 1, H^n := μHE[n], and c_n := addHaarScalarFactor(volume, μH[n]) ∈ ℝ≥0 (the scalar in Mathlib's definition μHE[n] = c_n·μH[n]); c_n ≠ 0 (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so c_n ∈ (0, ∞) and H^n = c_n·μH[n]. Consider integer multiplicity currents A on open sets V_A ⊆ ℝ^P whose mass measure μ_A, extended by 0 outside V_A, is locally finite on ℝ^P; these include all members (finite total mass if λ > 0, μ_S(B_R(0)) ≤ c₂R^n if λ = 0, by (d)), all their rescalings η_{y,λ#}S, and the cones C of (e). For such A put ϑ_A(w) := limsup_{ρ↓0} μ_A(B_ρ(w))/(ω_nρ^n) when finite and 0 otherwise, and φ_A(w) := ϑ_A(w)·e₁; write ϑ_S, φ_S for members. Then: (i) ϑ_S = Θ_S on U_S (densities exist there by (a), (b)). (ii) ϑ_A is Borel. (iii) μ_A = ϑ_A·H^n as measures on ℝ^P (Θ^n(μ_A, ·) equals the multiplicity H^n-a.e. on the carrier by Simon Ch. 3, Theorem 1.9 and Ch. 4, Remark 1.8(2), and the upper density vanishes H^n-a.e. off the carrier by Simon Ch. 1, Theorem 3.6 with Remark 3.7(2), applied to the locally finite measure μ_A on ℝ^P). (iv) (Normalization.) Since H^n = c_n·μH[n], (iii) gives μ_A = c_n·ϑ_A·μH[n], i.e. ∫ g·ϑ_A dμH[n] = c_n^{−1}·∫ g dμ_A for every bounded Borel g with compact support; in particular ∫_K ϑ_A dμH[n] = c_n^{−1}·μ_A(K) < ∞ for every compact K, so φ_A (Borel, ‖φ_A‖ = ϑ_A) is locally μH[n]-integrable. (H0) holds for members: if φ_S = φ_{S'} μH[n]-a.e., then ϑ_S = ϑ_{S'} H^n-a.e. (e₁ ≠ 0) (H^n and μH[n] have the same null sets), so μ_S = μ_{S'} by (iii), hence ϑ_S = ϑ_{S'} everywhere (ϑ is computed from μ) and φ_S = φ_{S'}. (v) (Correctly normalized weak pairings.) For every continuous compactly supported f : ℝ^P → ℝ, ∫ f·φ_A dμH[n] = (∫ f·ϑ_A dμH[n])·e₁ = c_n^{−1}(∫ f dμ_A)·e₁. Hence, for currents A_k, A as above, φ_{A_k} ⇀ φ_A in the sense of the sibling abstract_dimension_reduction (∫ f·φ_{A_k} dμH[n] → ∫ f·φ_A dμH[n] for all such f) if and only if ∫ f dμ_{A_k} → ∫ f dμ_A for all such f, i.e. μ_{A_k} → μ_A vaguely on ℝ^P (the factor c_n^{−1} ∈ (0, ∞) and the vector e₁ are fixed). (vi) φ_{η_{y,λ#}A}(w) = φ_A(y + λw) for all w (μ_{η_{y,λ#}A} = λ^{−n}(η_{y,λ})_#μ_A, so μ_{η_{y,λ#}A}(B_ρ(w)) = λ^{−n}μ_A(B_{λρ}(y + λw))). (vii) φ_C(λw) = φ_C(w) for cones C (μ_C(λB) = λ^nμ_C(B) for Borel B and λ > 0). So F := {φ_S : (S, U_S) ∈ 𝒯} satisfies (H0) and local integrability by (iv), A.1 by (c) and (vi), and A.2 of the sibling abstract_dimension_reduction: given φ_S ∈ F, |y| < 1 and a strictly decreasing sequence λ_k > 0 with λ_k → 0, (e) gives a strictly increasing subsequence k_i and a member cone C with μ_{η_{y,λ_{k_i}#}S} → μ_C vaguely on ℝ^P, so φ_S(y + λ_{k_i}·) = φ_{η_{y,λ_{k_i}#}S} ⇀ φ_C ∈ F by (vi) and (v), and φ_C is homogeneous by (vii). Two further facts, (viii) and (ix), and a consequence (T3s): (viii) (domain recovery) for φ with 0 < I(φ) := ∫|φ| dH^n < ∞ (H^n = μHE[n], so I(φ_S) = μ_S(ℝ^P) by (iii)) and ∫|w||φ(w)| dH^n(w) < ∞ put λ(φ) := (m₀/I(φ))^{1/n}, b(φ) := I(φ)^{−1}∫w|φ(w)| dH^n(w), x(φ) := b₀ − λ(φ)b(φ) and U(φ) := B_{2/λ(φ)}(−x(φ)/λ(φ)); otherwise U(φ) := ℝ^P. For members U(φ_S) = U_S (λ > 0: I(φ_S) = μ_S(ℝ^P) = λ^{−n}m₀ and b(φ_S) = (b₀ − x)/λ; λ = 0: I(φ_S) ∈ {0, ∞}), and U(φ_S(y + λ'·)) = η_{y,λ'}(U(φ_S)) by (c); (ix) (domain convergence) if μ_{S_k} → μ_S vaguely (members), every compact K ⊆ U_S lies in U_{S_k} for large k: otherwise, along a subsequence, λ_k > 0 and U_{S_k} ⊇ B_{1/λ_k}(0) force λ_k ≥ λ₀ > 0, the μ_{S_k} then live in closedBall 0 (3/λ₀) with total masses in [m₀, λ₀^{−n}m₀], so their total masses and barycenters converge, μ_S has finite positive mass, S has parameter λ > 0 by (b), (f), and (λ_k, x_k) → (λ, x), whence U_{S_k} → U_S and K ⊆ U_{S_k} for large k, a contradiction. (T3s) (parent T3, support part) If (S_k, U_{S_k}), (S, U_S) ∈ 𝒯 with μ_{S_k} → μ_S vaguely, y_k ∈ spt S_k and y_k → y ∈ U_S, then y ∈ spt S: choose ρ₁ > 0 with closedBall y (3ρ₁) ⊆ U_S; by (ix), closedBall y (3ρ₁) ⊆ U_{S_k} for large k, so (by (a), (b)) e^{Λ₀ρ}ρ^{−n}μ_{S_k}(B_ρ(y_k)) is nondecreasing on (0, ρ₁) for large k, and since Θ_{S_k}(y_k) ≥ 1, μ_{S_k}(B_ρ(y_k)) ≥ e^{−Λ₀ρ}ω_nρ^n for ρ < ρ₁; for η > 0 and large k, B_ρ(y_k) ⊆ closedBall y (ρ + η), so μ_S(closedBall y (ρ + η)) ≥ limsup_k μ_{S_k}(closedBall y (ρ + η)) ≥ e^{−Λ₀ρ}ω_nρ^n > 0 for all small ρ, η, i.e. y ∈ spt μ_S = spt S.
6. (A3: the flatness maps.) For j ≥ 1 put β_j := 2^{−j}. For any φ : ℝ^P → Euclid 1 let spt φ := {w : ∫_{B_ρ(w)}|φ| dμH[n] > 0 for all ρ > 0} (closed), R_j(φ) := {w ∈ spt φ : there are ρ > 0 and an n-dimensional subspace Π with B_ρ(w) ⊆ U(φ) and sup_{y ∈ spt φ ∩ B_ρ(w)}|q_Π(y − w)| < β_jρ} (q_Π the orthogonal projection onto Π^⊥, sup ∅ := 0), and sing_j φ := ((spt φ ∩ U(φ)) ∖ R_j(φ)) ∪ (ℝ^P ∖ U(φ)). For members, spt φ_S = spt μ_S and spt φ_S ∩ U_S = spt S. (Closed.) If (ρ, Π) witnesses w ∈ R_j(φ) with s := sup < β_jρ, and w' ∈ spt φ with t := |w' − w|, (1 + β_j)t < β_jρ − s, then (ρ − t, Π) witnesses w' (B_{ρ−t}(w') ⊆ B_ρ(w) and |q_Π(y − w')| ≤ s + t < β_j(ρ − t)); so R_j(φ) is relatively open in spt φ ∩ U(φ), (spt φ ∩ U(φ)) ∖ R_j(φ) is relatively closed in U(φ), and sing_j φ is closed. (A.3(2).) For members and g(w) := y + λ'w (0 < λ' < 1, |y| ≤ 1 − λ'): spt(φ∘g) = g^{−1}(spt φ), U(φ∘g) = g^{−1}(U(φ)) by (viii), and R_j(φ∘g) = g^{−1}(R_j(φ)) because balls and slabs scale together (B_ρ(w) ↦ B_{λ'ρ}(g(w)), |q_Π(g(y) − g(w))| = λ'|q_Π(y − w)|); hence sing_j(φ∘g) = g^{−1}(sing_j φ). (A.3(1).) If φ = c''·1_Q with Q an n-dimensional subspace: for c'' = 0, spt φ = ∅ and U(φ) = ℝ^P, so sing_j φ = ∅; for c'' ≠ 0, I(φ) = ∞, U(φ) = ℝ^P, spt φ = Q and every w ∈ Q is witnessed by (ρ, Π) = (1, Q) (sup = 0), so sing_j φ = ∅. (A.3(3).) Let φ_{S_k} ⇀ φ_S in F (so μ_{S_k} → μ_S vaguely), ε > 0, and suppose that along a subsequence w_k ∈ B_1(0) ∩ sing_j φ_{S_k} with dist(w_k, sing_j φ_S) ≥ ε. As B_2(0) ⊆ U_{S_k}, w_k ∈ spt S_k ∖ R_j(φ_{S_k}); pass to w_k → w, |w| ≤ 1; by (T3s), w ∈ spt S, and w ∉ sing_j φ_S (distance ≥ ε), w ∈ U_S, so w ∈ R_j(φ_S), witnessed by (ρ, Π) with s := sup_{y ∈ spt S ∩ B_ρ(w)}|q_Π(y − w)| < β_jρ. Take ρ' < ρ with s < β_jρ', τ := (s + β_jρ')/2 and η > 0 with ρ' + 2η < ρ. For large k, |w_k − w| < η, B_{ρ'}(w_k) ⊆ closedBall w (ρ' + η) ⊆ U_{S_k} by (ix), and every y ∈ spt S_k ∩ B_{ρ'}(w_k) has |q_Π(y − w_k)| < τ: otherwise, for infinitely many k there would be such y_k with |q_Π(y_k − w_k)| ≥ τ, a limit point y would lie in spt S (by (T3s)) ∩ closedBall w ρ' ⊆ B_ρ(w) with |q_Π(y − w)| ≥ τ > s, contradicting the definition of s. Then (ρ', Π) witnesses w_k ∈ R_j(φ_{S_k}) (sup ≤ τ < β_jρ'), a contradiction.
7. (A3: applying Appendix A.4.) By the sibling abstract_dimension_reduction (with Q := 1, F, sing := sing_j), (I) or (II) holds. Suppose (II) with d = n − 1: there are ψ = φ_S ∈ F and L with dim L = n − 1, sing_j ψ = L and ψ(y + λx) = ψ(x) for y ∈ L, λ > 0. Since sing_j 0 = ∅ ≠ L, ψ ≠ 0; ψ is homogeneous, so S has parameter 0 by (f), S is minimizing in ℝ^P with ∂S = 0, and Θ_S = ϑ_S is invariant under w ↦ y + λw. By the sibling child cone_splitting (dim L = n − 1 < n) there is S₀ ∈ 𝒟_1(ℝ^P), minimizing, ∂S₀ = 0, a cone, with spt S₀ ⊆ L^⊥ and t + y ∈ spt S ⟺ y ∈ spt S₀; by the sibling child one_dim_cones, spt S₀ ⊆ span{e} for some e. Hence spt S ⊆ L + span{e}, a subspace of dimension ≤ n, contained in some n-dimensional subspace Π''. Then U(ψ) = ℝ^P and every w ∈ spt ψ = spt S is witnessed in R_j(ψ) by (1, Π''), so sing_j ψ = ∅ ≠ L: a contradiction. Hence (I) holds or d ≤ n − 2, and since sing_j φ_{T'} ∩ B_1(0) = (spt T' ∩ B_1(0)) ∖ R_j(φ_{T'}) (B_1(0) ⊆ U(φ_{T'}) = B_2(0)), μH[n − 2 + α]((spt T' ∩ B_1(0)) ∖ R_j(φ_{T'})) = 0 for all α > 0 (n − 2 + α = d + (n − 2 − d + α)); for n = 1 case (II) is impossible, so this set is empty. Put G_{z,r} := spt T' ∩ B_1(0) ∩ ∩_j R_j(φ_{T'}) and F'_{z,r} := (spt T' ∩ B_1(0)) ∖ G_{z,r} = ∪_j((spt T' ∩ B_1(0)) ∖ R_j(φ_{T'})), and F_{z,r} := z + rF'_{z,r}. Then μH[n − 2 + α](F_{z,r}) = r^{n−2+α}μH[n − 2 + α](F'_{z,r}) = 0 for n ≥ 2 and α > 0, and F_{z,r} = ∅ for n = 1.
8. (A4: tangent planes at flat points; corrected (13).) Let w ∈ G_{z,r} and x := z + rw ∈ spt T. For each j there are ρ_j ∈ (0, 2] and Π_j with B_{ρ_j}(w) ⊆ B_2(0) and |q_{Π_j}(y − w)| < 2^{−j}ρ_j for y ∈ spt T' ∩ B_{ρ_j}(w). Pass to a subsequence with Π_j → Π (compactness of the Grassmannian; ‖q_{Π_j} − q_Π‖ → 0) and ρ_j → ρ_∞ ∈ [0, 2]. Case ρ_∞ > 0: every y ∈ spt T' ∩ B_{ρ_∞/2}(w) lies in B_{ρ_j}(w) for large j, so |q_Π(y − w)| = lim|q_{Π_j}(y − w)| = 0, i.e. spt T' ∩ B_{ρ_∞/2}(w) ⊆ w + Π. By the constancy theorem (Simon Ch. 6, 2.34, with ∂T' = 0 and the connectedness of (w + Π) ∩ B_{ρ_∞/2}(w)), T' = c₀[[w + Π]] in B_{ρ_∞/2}(w) for some c₀ ∈ ℤ (T' is integer multiplicity; [[Π]] carries a fixed orientation), and c₀ ≠ 0 as w ∈ spt T'. Then, with λ_i := r/i, blowUp T x λ_i = η_{w,1/i#}T' equals c₀[[Π]] on B_{iρ_∞/2}(0), so blowUp T x λ_i ⇀ C := c₀[[Π]] (ConvergesWeakly), spt C = Π and dim Π = n: HasTangentPlaneAt T x. Case ρ_∞ = 0: by the sibling density_and_tangent_cones (2) at x ∈ spt T (boundarySupport T = ∅) with the scales rρ_j → 0, a further subsequence and a minimizing cone C satisfy blowUp T x (rρ_j) ⇀ C with mass measure convergence and HasMassDensity C 0 Θ(x), Θ(x) ≥ 1; so 0 ∈ spt C and C ≠ 0; ∂C = 0 as a weak limit of cycles. Since B_{ρ_j}(w) ⊆ B_2(0), blowUp T x (rρ_j) = η_{w,ρ_j#}T' on η_{w,ρ_j}(B_2(0)) ⊇ B_1(0), and its support in B_1(0) lies in {v : |q_{Π_j}(v)| < 2^{−j}} ⊆ {v : |q_Π(v)| < 2^{−j} + ‖q_{Π_j} − q_Π‖}. If v ∈ spt C ∩ B_1(0), lower semicontinuity of mass on open sets gives points of spt(blowUp T x (rρ_j)) converging to v, so |q_Π(v)| = 0: spt C ∩ B_1(0) ⊆ Π, and since spt C is a cone, spt C ⊆ Π. By constancy (∂C = 0, C integer multiplicity, Π connected), C = c₀[[Π]] with c₀ ∈ ℤ ∖ {0}, so spt C = Π: HasTangentPlaneAt T x (IsTangentConeAt with the scales rρ_j).
9. (A5: assembly.) Put F := E ∪ ∪_{(z,r)∈𝒞}F_{z,r}, so E ⊆ F. For α > 0: μH[n − 2 + α](E) = 0 (for n ≥ 3 by step 4 with n − 2 + α = n − 3 + (1 + α); for n ≤ 2, E = ∅), and μH[n − 2 + α](F_{z,r}) = 0 (step 7); by countable subadditivity μH[n − 2 + α](F) = 0 (for n = 1, F = ∅). Let x ∈ spt T ∖ F and pick (z, r) ∈ 𝒞 with x ∈ B_r(z). Then μ_T(B_{2r}(z)) > 0, so T' ≠ 0, and w := (x − z)/r ∈ spt T' ∩ B_1(0) with w ∉ F'_{z,r} (as x ∉ F_{z,r}); hence w ∈ G_{z,r}, and step 8 gives HasTangentPlaneAt T x. Together with step 1 (integer densities on U ∖ E) and step 4, this proves IntegerDensityAndTangentPlanes.

## Key steps

1. n = 0: T = 0 by zero_dim_vanishing, take E = F = ∅; for n ≥ 1, monotonicity gives an upper semicontinuous density Θ with Θ ≥ 1 on spt T, and E := {Θ ∉ ℤ}.
2. 7.3.3(1): cover E by the sets E_{m,β}; uniform density bounds pass to zero-scale limits; threshold_reduction with c = m − 1 + β, d₀ = n − 2, where (H1) fails by integrality and (H2) fails by cone_splitting with one_dim_cones (n − d = 1) or White's classification (n − d = 2).
3. 7.3.3(2): per rational ball, Simon's class 𝒯 with domains recovered from mass and barycenter; density functions with the correct normalization ∫_K ϑ_S dμH[n] = c_n⁻¹·μ_S(K), tangent cones of members obtained by an explicit diagonal selection and a countable-test criterion for limits on ℝ^P with exhausting domains; the flatness maps sing_j satisfy A.1–A.3, and an (n−1)-dimensional extremal is a plane by cone_splitting and one_dim_cones, so the non-flat sets are H^{n−2+α}-null.
4. Points flat at all scales β_j = 2^{−j} have a tangent plane, by constancy (ρ_∞ > 0) or by flatness of a tangent cone (ρ_∞ = 0).
5. F := E ∪ ∪F_{z,r} is H^{n−2+α}-null, contains E, and every x ∈ spt T ∖ F has a tangent plane.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n 'μHE\|euclideanHausdorffMeasure' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (same file)`
- `grep -rn 'theorem massOn_le_liminf\|theorem boundary_affinePushforward\|exp_normalizedBallMass_monotoneOn\|theorem bvVariationOn_le_liminf_of_locallyL1\|theorem cone_simonsDefect_lower_bound' simongmt/Poincare`
- `grep -n 'def support\|zeroRegion\|def massOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn dimred --include=*.lean GMT .lake/packages/simongmt/Poincare; grep -c dimred dag.json; grep -rln dimred_ .swarm-worktrees/*/gmt-ch07/GMT (no match anywhere)`
- `python3 inspection of dag.json: sibling lean_statements (abstract_dimension_reduction, density_and_tangent_cones, density_one_implies_regular, compactness_of_minimizing_currents, minimizing_implies_stationary) and similar lemma nodes in other branches (dtc_mass_eq_measure, dor_imrep_massOn_eq_measure_and_support, dtc_dim_zero_eq_zero, imrep_measure_eq_of_represents_same_current, rsd_massOn_eq_measure)`
- `lean -R /tmp/dr-v2-check/src /tmp/dr-v2-check/src/CheckV2Types.lean (private olean of GMT.Ch07.Submission; 12 child types declared as Submission.X in namespace GMT.Ch07 with the contract opens; assembly ⟨A, B, C⟩; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-review-receipt-v1.json`
- `/tmp/dr-v2-check/src/CheckV2Types.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD), mathlib 25730c7c and simongmt 2b36630. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean; its only sorry is the frozen main_theorem.

Normalization (decides correction R1). Mathlib defines μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (Measure.lean, lines 68–101). The scalar is in ℝ≥0 and nonzero (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so μ_A = ϑ_A·μHE[n] gives ∫_K ϑ_A dμH[n] = c_n⁻¹·μ_A(K).

SimonGMT definitions used:
- massOn is the sSup over admissible forms with Euclidean coefficient norm ≤ 1 (Mass.lean).
- support = U \ zeroRegion (CurrentLocalEquality.lean, lines 108–117).
- WeaklyConvergesOn.massOn_le_liminf (Mass.lean:100) gives the lower semicontinuity used for the new mass bounds.

Other cited library facts exist:
- GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188);
- HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn (Chapter04/MeanCurvature.lean:361);
- bvVariationOn_le_liminf_of_locallyL1 (Chapter02/BV.lean:225);
- cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean:228).

The library provides none of the following for the contract's IMRep currents: the mass–measure identity, product currents, Federer–Fleming compactness, or Appendix A.4. These are children or sibling prerequisites.

Lean check. All twelve child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens, with only the stub sorry warnings. The assembly ⟨A, B, C⟩ proves IntegerDensityAndTangentPlanes ∧ SingularSetSmallWhereDensityBelowTwo ∧ CodimensionOneRegularity, and the conditional assembly depends only on propext, Classical.choice and Quot.sound.

Names. No dimred_ identifier occurs in the workspace, SimonGMT, any speculative worktree or dag.json. Similar lemmas in other branches have different types and names, so there is neither reuse nor collision.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
