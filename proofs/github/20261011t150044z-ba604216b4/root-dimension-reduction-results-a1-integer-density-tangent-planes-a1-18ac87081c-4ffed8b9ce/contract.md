<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1 -->

## Theorem `Submission.idtp_cone_sector_endpoint_density`

Let P ∈ ℕ and let C ∈ 𝒟_2(ℝ^P) be minimizing in ℝ^P (IsMinimizingIn C univ), with ∂C = 0 (BoundaryVanishes C), and a cone (IsConeCurrent C). Let Q be a 2-dimensional linear subspace of ℝ^P, a, e ∈ Q with |a| = |e| = 1 and ⟨a, e⟩ = 0 (so Q = span{a, e}), δ > 0 and k ∈ ℕ with k ≥ 1. Assume a ∈ spt C and that for all t > 0 and φ ∈ (0, δ) the point y := t(cos φ·a + sin φ·e) satisfies Θ²(μ_C, y) = k (HasMassDensity C y k) and spt C ∩ B_r(y) ⊆ Q for some r > 0. Then Θ²(μ_C, a) = k (HasMassDensity C a k).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1032

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4800, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4780, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4789

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5644, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5657, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5670, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5683, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5694, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5701, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5713, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5721, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5734, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5751, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5759

## Lean problem

Declaration: `Submission.idtp_cone_sector_endpoint_density`

```lean
∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (δ : ℝ) (k : ℕ), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < δ → 1 ≤ k → a ∈ C.support → (∀ t φ : ℝ, 0 < t → 0 < φ → φ < δ → HasMassDensity C (t • (Real.cos φ • a + Real.sin φ • e)) k ∧ ∃ r : ℝ, 0 < r ∧ C.support ∩ ball (t • (Real.cos φ • a + Real.sin φ • e)) r ⊆ (Q : Set (Euclid P))) → HasMassDensity C a k
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent's step 4, case n − d = 2 (Simon 7.3.3(1), chapter-07.txt lines 497–510), uses the classification of 2-dimensional minimizing cones, which the book cites to [Whi82] and does not prove. This child is the rigidity statement behind that classification. Its proof combines three ingredients: a conservation law of the stationary cone for the rotation field of Q (first variation, Simon Ch. 4, 2.2–2.6, via minimizing_implies_stationary), the weighted area formula on the rectifiable carrier (Simon Ch. 3, 2.4–2.5), which is the sibling child carrier_area_formula (`Submission.idtp_carrier_area_formula`), and the integrality of the multiplicity. Conventions. ℝ^P := Euclid P and B_ρ(x) is the open ball. For an integer multiplicity current A on an open set, μ_A denotes R.measure for any representation R of A (all representations have the same measure), M_W(A) = μ_A(W) for open W inside the domain of A, and spt A = {x in the domain : μ_A(B_ε(x)) > 0 for every ε > 0} (sibling results im_mass_measure (c), (a), (b), `Submission.dimred_im_mass_measure`); hence μ_A vanishes off spt A (Lindelöf). H² := μHE[2] and ω_2 := unitBallVolume 2. For a 2-dimensional subspace Q, H²⌞Q is the image of Lebesgue measure of ℝ² under a linear isometry (Mathlib `Isometry.euclideanHausdorffMeasure_image`, `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`), so H²(Q ∩ B_ρ(y)) = ω_2ρ² for y ∈ Q. η_{y,λ}(w) := λ^{−1}(w − y) (Lean `dilation y λ`) and blowUp A y λ = η_{y,λ#}A. For 2-currents, M_{η_{y,λ}(W)}(η_{y,λ#}A) = λ^{−2}M_W(A) (accepted `Submission.dtc_blowUp_massOn_image`), η_{y,λ#}A has a representation with measure B ↦ λ^{−2}μ_A(η_{y,λ}^{−1}(B)) (accepted `Submission.dtc_blowUp_imrep`), and (η_{y,λ#}A)(ω) = λ^{−2}A(ω∘η_{y,λ}) (accepted `Submission.dtc_blowUp_testForm_corr`). Densities are unique: HasMassDensity A y θ and HasMassDensity A y θ' imply θ = θ' (both are ≥ 0 and ENNReal.ofReal is injective on [0, ∞)). (M) Monotonicity. Let C ∈ 𝒟_2(ℝ^P) be minimizing in ℝ^P with ∂C = 0. If P ≤ 1, every 2-covector on ℝ^P vanishes, so C = 0; hence P ≥ 2 whenever spt C ≠ ∅, and then we write P = 2 + k₀ to apply results stated in ℝ^{n+k}. ℝ^P = univ is an embedded C² P-dimensional submanifold (identity chart), closure ℝ^P ∖ ℝ^P = ∅ and spt C ⊆ ℝ^P, so the sibling result monotonicity (`Submission.dimred_minimizing_monotonicity`, with U = N = ℝ^P, n = 2, d = P) gives: ρ ↦ ρ^{−2}μ_C(B_ρ(y)) is nondecreasing on (0, ∞) for every y; Θ(y) := Θ²(μ_C, y) exists for every y (HasMassDensity C y Θ(y)) and Θ is upper semicontinuous; Θ ≥ 1 on spt C; hence μ_C(B_ρ(y)) ≥ ω_2ρ² for y ∈ spt C and ρ > 0; and Θ(y) = 0 for y ∉ spt C (a ball about y has μ_C-measure 0). (K) Cone facts. Let C ∈ 𝒟_2(ℝ^P) be a cone (IsConeCurrent C). For λ > 0 the domain of blowUp C 0 λ is η_{0,λ}(ℝ^P) = ℝ^P and currentEval(blowUp C 0 λ, ω) = C(ω), so blowUp C 0 λ = C; mass scaling gives M_{λ^{−1}W}(C) = λ^{−2}M_W(C), i.e. μ_C(sW) = s²μ_C(W) for open W and s > 0, hence for all Borel sets (outer regularity of the locally finite measure μ_C). Consequently spt C is invariant under x ↦ sx (s > 0), Θ(sx) = Θ(x), μ_C(B_ρ(0)) = ρ²μ_C(B_1(0)) for ρ > 0, and μ_C({0}) = 0.
0. (Setup.) Since a ∈ spt C, P ≥ 2; write P = 2 + k₀. Let R = (M, θ, ξ) represent C and μ := μ_C = R.measure. Since a, e are orthonormal in the 2-dimensional Q, Q = span{a, e}. Let π be the orthogonal projection onto Q and q := id − π (q(a) = 0). By the sibling child cone_tangent_cone_planar (at a ≠ 0, a ∈ spt C), m := Θ(a) is a positive integer: it equals the integer |c| obtained in step 1 for every sequence (uniqueness of densities).
1. (Every tangent cone at a is ±m[[Q]].) Let λ_j > 0 with λ_j → 0. cone_tangent_cone_planar gives a subsequence (not relabelled), c ∈ ℤ with |c| = m, an orthonormal pair τ' with a ∈ Q' := span τ', and C' with C_j := blowUp C a λ_j ⇀ C', C'(ω) = c∫_{Q'} ω(x)(τ') dH²(x), and MassMeasuresConverge (C_j) C'. C' is represented by (Q', m, sign(c)·(α ↦ α(τ'))) (SimonGMT `hasApproximateTangentSpaceAt_submodule` gives the orientation condition), so μ_{C'} = m·H²⌞Q'; and μ_{C_j}(B) = λ_j^{−2}μ(a + λ_jB). Vague convergence gives limsup_j μ_{C_j}(K) ≤ m·H²(Q' ∩ K) for compact K and liminf_j μ_{C_j}(V) ≥ m·H²(Q' ∩ V) for open V. Claim: Q' = Q. Let w = σa + ue with σ ∈ ℝ and u > 0. For large j, y_j := a + λ_jw = (1 + λ_jσ)a + λ_jue = t_j(cos φ_j·a + sin φ_j·e) with t_j := |y_j| > 0 and φ_j := arctan(λ_ju/(1 + λ_jσ)) ∈ (0, δ). By hypothesis Θ(y_j) = k ≥ 1, so y_j ∈ spt C and μ(B_r(y_j)) ≥ ω_2r² for every r > 0 (M). Hence μ_{C_j}(closedBall(w, r)) ≥ λ_j^{−2}μ(B_{λ_jr}(y_j)) ≥ ω_2r², so m·H²(Q' ∩ closedBall(w, r)) ≥ ω_2r² > 0 for every r > 0, and w ∈ Q' (Q' is closed). Thus {σa + ue : σ ∈ ℝ, u > 0} ⊆ Q', so Q = span{a, e} ⊆ Q' and Q' = Q.
2. (Cusp.) For every ε > 0 there is s_ε > 0 with |q(x)| ≤ ε|x − a| for every x ∈ spt C ∩ B_{s_ε}(a). Otherwise there are ε > 0 and x_j ∈ spt C with s_j := |x_j − a| → 0 and |q(x_j)| > εs_j. Put w_j := (x_j − a)/s_j, so |w_j| = 1 and |q(w_j)| > ε. By step 1 (λ_j := s_j) and compactness, along a subsequence w_j → w with |q(w)| ≥ ε and μ_{C_j} → m·H²⌞Q vaguely. As x_j ∈ spt C, μ_{C_j}(B_r(w_j)) ≥ ω_2r², and B_r(w_j) ⊆ closedBall(w, 2r) for large j, so m·H²(Q ∩ closedBall(w, 2r)) ≥ ω_2r² > 0 for every r > 0. Then w ∈ Q, contradicting |q(w)| ≥ ε.
3. (Coordinates.) Let A(x) := ⟨x, a⟩e − ⟨x, e⟩a. A is linear and antisymmetric (⟨Ax, y⟩ = −⟨x, Ay⟩), |Ax| = |πx|, Aa = e, A = 0 on Q^⊥, and tr(P_T A) = 0 for every orthogonal projection P_T. On Ω := {x : ⟨x, a⟩ > 0} put f(x) := arctan(⟨x, e⟩/⟨x, a⟩) ∈ (−π/2, π/2), so πx = |πx|(cos f(x)·a + sin f(x)·e). f is smooth on Ω, f(sx) = f(x) for s > 0, ∇f(x) = Ax/|πx|², ⟨∇f(x), x⟩ = 0, f(a) = 0 and ∇f(a) = e. Let F : ℝ^P → ℝ² (= Euclid 2) be F(x) := (|x|, arctan(⟨x, e⟩/⟨x, a⟩)), with the convention u/0 := 0 of Lean's division, so that F = (|·|, f) on Ω; F is Borel on ℝ^P (built from continuous maps and the measurable division) and C^∞ on the open set Ω (0 ∉ Ω). For s ∈ (0, 1/4] let Z_s := {x ∈ Ω : ||x| − 1| < s, |f(x)| < s, |q(x)| < s|x|} (open), and for 0 < s' ≤ s let Z_s(s') := {x ∈ Z_s : ||x| − 1| < s', |f(x)| < s'}.
4. (Localization.) Fix s_0 ∈ (0, 1/4] with 5s_0 < s_{1/20} (step 2), and let 0 < s' ≤ s ≤ s_0. (a) If x ∈ spt C ∩ Ω with ||x| − 1| < s', |f(x)| < s' and |q(x)| ≤ 2s|x|, then |q(x)| < (s'/4)|x| and |x − a| < 3s'. Indeed, η := |q(x)|/|x| ≤ 2s ≤ 1/2 and x̂ := x/|x| satisfy |πx̂| = (1 − η²)^{1/2} ≥ 1 − η². So |x̂ − a| ≤ |πx̂ − (cos f(x)·a + sin f(x)·e)| + |cos f(x)·a + sin f(x)·e − a| + |q(x̂)| ≤ η² + |f(x)| + η < s' + 1.5η, and |x − a| ≤ ||x| − 1| + |x̂ − a| < 2s' + 1.5η ≤ 5s < s_{1/20}. By step 2, (3/4)η ≤ η|x| = |q(x)| ≤ |x − a|/20 < (2s' + 1.5η)/20, so η < 4s'/27 < s'/4 and |x − a| < 2s' + 1.5s'/4 < 3s'. (b) Consequently spt C contains no x ∈ Ω with ||x| − 1| < s, |f(x)| < s and s|x|/2 ≤ |q(x)| ≤ 2s|x| (apply (a) with s' := s), and every x ∈ spt C ∩ Z_s(s') lies in B_{3s'}(a) ∩ Z_{s'} and satisfies |q(x)| < (s'/4)|x|.
5. (Stationarity and radial tangency.) minimizing_implies_stationary (`Submission.minimizing_implies_stationary`, with n := 2, k := ℓ := k₀, U = N = ℝ^P) gives R.firstVariation X = 0 for every C¹ compactly supported X : ℝ^P → ℝ^P. By (K), μ(B_ρ(0)) = μ(B_1(0))·ρ² for ρ > 0 with μ(B_1(0)) < ∞, so accepted `Submission.dtc_cone_radial_tangency` gives x ∈ T_x := approxTangentPlane 2 M x for μ-a.e. x. Let E_0 be the set of x ∈ M with x = 0, or without an approximate tangent space of M at x, or such that ξ(x) does not orient T_x, or with x ∉ T_x; H²(E_0) = 0 (the field `orients` of R, μ(E_0) = 0 with θ ≥ 1 on M, and H²({0}) = 0). For x ∈ M ∖ E_0, ξ(x)(α) = ±α(u_1, u_2) for every orthonormal basis (u_1, u_2) of T_x. For x ∈ M ∖ E_0, T_x is 2-dimensional and contains x̂ := x/|x|; for a unit τ ∈ T_x with τ ⊥ x we have P_{T_x}(Ax) = ⟨τ, Ax⟩τ (since ⟨x̂, Ax⟩ = 0), so |P_{T_x}Ax| ≤ |Ax| = |πx| ≤ |x|. For x ∈ Ω put J(x) := |P_{T_x}Ax|/|πx|² and G(x) := |P_{T_x}Ax|²/|πx|² = J(x)·|P_{T_x}Ax| (T_x is defined for every x, and πx ≠ 0 on Ω); since |P_{T_x}Ax| ≤ |Ax| = |πx|, J ≤ 1/|πx| and 0 ≤ G ≤ 1 on Ω, and ⟨P_{T_x}∇f(x), Ax⟩ = ⟨∇f(x), P_{T_x}Ax⟩ = |P_{T_x}Ax|²/|πx|² = G(x) for x ∈ Ω (∇f(x) = Ax/|πx|², and P_{T_x} is an orthogonal projection). For x ∈ (M ∖ E_0) ∩ Ω and τ as above, J(x) = |⟨∇f(x), τ⟩| (⟨∇f(x), τ⟩ = ⟨Ax, τ⟩/|πx|² and P_{T_x}Ax = ⟨τ, Ax⟩τ); in the orthonormal basis (x̂, τ) of T_x, DF(x)x̂ = (⟨x̂, x̂⟩, ⟨∇f(x), x̂⟩) = (1, 0) and DF(x)τ = (⟨x̂, τ⟩, ⟨∇f(x), τ⟩) = (0, ⟨∇f(x), τ⟩), so J(x) is the Jacobian of F along T_x (step 7). Measurability: x ↦ P_{T_x} = (approxTangentPlane 2 M x).starProjection is a.e. strongly measurable for H²⌞M (accepted `Submission.imrep_approxTangent_starProjection_aesm`), so x ↦ |P_{T_x}Ax| and, on Ω, J and G (continuous functions of P_{T_x} and x there) are a.e. measurable for H²⌞M, hence for μ ≪ H²⌞M.
6. (Conservation law.) Let s ∈ (0, s_0]. Fix χ ∈ C^∞(ℝ) with χ = 1 on (−∞, 1/4] and χ = 0 on [1, ∞), and put ζ(x) := χ(|q(x)|²/(s²|x|²)). ζ is smooth on ℝ^P ∖ {0}, ζ = 1 where |q(x)| ≤ s|x|/2 and ζ = 0 where |q(x)| ≥ s|x|. For λ ∈ C¹_c((1 − s, 1 + s)) and ψ ∈ C¹_c((−s, s)) let X(x) := ψ(f(x))λ(|x|)ζ(x)Ax for x ∈ Ω and X(x) := 0 otherwise. X is C¹ with compact support (C^∞ if λ and ψ are). Indeed, on the compact set {||x| − 1| ≤ s, |q(x)| ≤ s|x|} ⊇ spt(λ(|·|)ζ) we have |πx| ≥ (1 − s²)^{1/2}|x| > 0. Moreover ψ(f(x)) = 0 for x ∈ Ω near ∂Ω ∩ {πx ≠ 0} (there |f| → π/2 > s), so ψ∘f extends by 0 to a C¹ function on {πx ≠ 0}. With g := (ψ∘f)·λ(|·|)·ζ, DX = g·A + (Ax) ⊗ ∇g, where (v ⊗ w)(u) := ⟨w, u⟩v. For x ∈ M ∖ E_0 we have tr(P_{T_x}DX(x)) = ⟨P_{T_x}∇g(x), Ax⟩ and ∇g = ψ'(f)λζ∇f + (ψ∘f)ζλ'(|x|)x̂ + (ψ∘f)λ∇ζ. Three observations: ⟨P_{T_x}x̂, Ax⟩ = ⟨x̂, Ax⟩ = 0. ∇ζ(x) = 0 whenever x ∈ spt C and ψ(f(x))λ(|x|) ≠ 0 (by 4(b), either |q(x)| < s|x|/2, where ζ ≡ 1 nearby, or |q(x)| > 2s|x|, where ζ ≡ 0 nearby). If x ∈ spt C and ψ'(f(x))λ(|x|)ζ(x) ≠ 0, then x ∈ Z_s and ζ(x) = 1 (4(b)). Since μ-a.e. point lies in spt C ∩ (M ∖ E_0), R.firstVariation X = 0 becomes
(I) ∫_{Z_s} ψ'(f(x))λ(|x|)G(x) dμ(x) = 0.
7. (Fibres; the area formula on the carrier.) M is Borel and countably 2-rectifiable (fields of IMRep), μHE[2](M ∩ K) ≤ μ(K) < ∞ for every compact K (θ ≥ 1 on M; locallyIntegrable_mult with U = ℝ^P), Z_s is open, and F is C¹ on Z_s ⊆ Ω (step 3). So the sibling child carrier_area_formula (`Submission.idtp_carrier_area_formula`, with n := 2, M, Z := Z_s and F) applies: for every h : ℝ^P → [0, ∞] that is a.e. measurable for H²⌞M, the fibre-sum function (t, α) ↦ Σ_{x∈M∩Z_s∩F^{−1}(t,α)} h(x) is L²-a.e. measurable on ℝ² and (AF) ∫_{ℝ²} Σ_{x∈M∩Z_s∩F^{−1}(t,α)} h(x) dt dα = ∫_{M∩Z_s} J*(x)h(x) dH²(x), where J*(x) := (det(⟨DF(x)u_i, DF(x)u_j⟩)_{i,j})^{1/2} and (u_i) is the standard orthonormal basis of T_x (Lebesgue measure on Euclid 2 is dt dα in the coordinates (t, α)). For x ∈ (M ∖ E_0) ∩ Z_s, J*(x) = J(x): T_x is 2-dimensional; the Gram determinant det(⟨DF(x)v_i, DF(x)v_j⟩) is the same for every orthonormal basis (v_1, v_2) of T_x (another orthonormal basis is vO with O orthogonal, which replaces the Gram matrix Γ by OᵀΓO, of determinant det(O)²det Γ = det Γ); and in the basis (x̂, τ) of step 5 the Gram matrix is diag(1, ⟨∇f(x), τ⟩²). As H²(E_0) = 0, J* = J H²-a.e. on M ∩ Z_s. Finally μ = θ·H²⌞M with θ Borel and finite, so ∫_{Z_s} φ dμ = ∫_{M∩Z_s} θφ dH² for every φ : ℝ^P → [0, ∞] (Mathlib lintegral_withDensity_eq_lintegral_mul_non_measurable). For (t, α) ∈ O_s := (1 − s, 1 + s) × (−s, s) let X(t, α) := M ∩ Z_s ∩ F^{−1}(t, α), N(t, α) := Σ_{x∈X(t,α)} θ(x) ∈ ℕ ∪ {∞} and H(t, α) := Σ_{x∈X(t,α)} θ(x)·|P_{T_x}Ax|; since F(Z_s) ⊆ O_s, these sums vanish for (t, α) ∉ O_s, and N, H are L²-a.e. measurable by (AF) (h := θ, resp. h := θ·|P_{T_x}Ax|, a.e. measurable for H²⌞M by step 5). (a) With h := θ: ∫∫_{O_s} N = ∫_{M∩Z_s} Jθ dH² = ∫_{Z_s} J dμ ≤ ∫_{Z_s} |πx|^{−1} dμ ≤ 2μ(B_2(0)) < ∞ (J ≤ |πx|^{−1} on Z_s ⊆ Ω by step 5, and |πx| > (1 − s²)^{1/2}(1 − s) > 1/2 on Z_s). So N < ∞ a.e. on O_s, and H ≤ (1 + s)N (|P_{T_x}Ax| ≤ |x| < 1 + s on Z_s) is integrable on O_s. (b) With h := ∞·1_{E_0}, which vanishes H²⌞M-a.e. (H²(E_0) = 0) and is therefore a.e. measurable, the right side of (AF) is 0; so Σ_{x∈X(t,α)} h(x) = 0, i.e. X(t, α) ∩ E_0 = ∅, for a.e. (t, α). (c) Let b be a bounded Borel function on ℝ² with positive and negative parts b^±. Apply (AF) to h := θ·(b^±∘F)·|P_{T_x}Ax| (a.e. measurable for H²⌞M): on X(t, α) we have F ≡ (t, α), so the fibre sum is b^±(t, α)H(t, α); and J*h = θ·(b^±∘F)·G H²-a.e. on M ∩ Z_s (J* = J H²-a.e. there, and G = J·|P_{T_x}Ax| on Ω). Hence ∫∫_{O_s} b^±H dt dα = ∫_{Z_s} b^±(F(x))G(x) dμ(x) ≤ sup|b|·μ(Z_s) < ∞ (G ≤ 1), and, subtracting, ∫∫_{O_s} b(t, α)H(t, α) dt dα = ∫_{Z_s} b(F(x))G(x) dμ(x). In particular, by (I) (b(t, α) := ψ'(α)λ(t)), ∫∫_{O_s} ψ'(α)λ(t)H(t, α) dt dα = 0 for all λ, ψ as in step 6.
8. (H depends only on t.) By 7(c), ∫∫_{O_s} ψ'(α)λ(t)H(t, α) dt dα = 0 for all ψ ∈ C¹_c((−s, s)) and λ ∈ C¹_c((1 − s, 1 + s)) (step 6 allows C¹ test functions). For j ≥ 1 the functions in C¹_c((−s, s)) supported in [−s + 1/j, s − 1/j] form a subset of the separable Banach space C¹([−s, s]); choose a countable subset 𝒟_j of it that is dense for the C¹ norm, and put 𝒟_0 := ∪_j 𝒟_j. Then every ψ ∈ C¹_c((−s, s)) is the limit of ψ_i ∈ 𝒟_0 with ψ_i → ψ and ψ_i' → ψ' uniformly and with supports in a common compact subinterval. H is integrable on O_s (7(a)), so by Fubini, for each ψ the function t ↦ ∫ψ'(α)H(t, α) dα is integrable on (1 − s, 1 + s) and has integral 0 against every λ ∈ C¹_c((1 − s, 1 + s)), hence vanishes for a.e. t. So for a.e. t ∈ (1 − s, 1 + s): H(t, ·) is integrable on (−s, s) and ∫ψ'(α)H(t, α) dα = 0 for every ψ ∈ 𝒟_0, hence (uniform convergence of the ψ_i' and dominated convergence) for every ψ ∈ C¹_c((−s, s)). For such t, transport H(t, ·), extended by 0 off (−s, s), to Euclid 1 by the volume-preserving linear isometry ℝ ≅ Euclid 1; it carries the C¹ functions with compact support in (−s, s) to those with compact support in the image U_s of (−s, s), and ψ' to the derivative along the basis vector. SimonGMT `ae_eq_const_of_weak_coordinate_derivatives_zero` (n = 1, U := U_s, open and preconnected; its hypothesis is the vanishing just proved, for C¹ test functions) shows that H(t, ·) is a.e. equal to a constant on (−s, s). Hence, with h(t) := (2s)^{−1}∫_{−s}^{s} H(t, α) dα (measurable and integrable on (1 − s, 1 + s) by Fubini), H(t, α) = h(t) for a.e. (t, α) ∈ O_s (Tonelli, applied to a measurable version of H).
9. (h(t) = ct.) (a) Dilation invariance of the tangent planes. For r > 0, R_r := (rM, θ(·/r), ξ(·/r)) is an integer multiplicity triple in ℝ^P. Indeed, rM is Borel and countably 2-rectifiable, θ(·/r) and ξ(·/r) are measurable, H²(rE) = r²H²(E), and by accepted `Submission.dtc_approxTangent_dilation` (η := dilation 0 r^{−1}) the approximate tangent space of rM at ry equals that of M at y. R_r represents C: by (K) and dtc_blowUp_testForm_corr, C(ω) = (blowUp C 0 r^{−1})(ω) = r²C(ω(r·)) = r²∫_M θ(x)ξ(x)(ω(rx)) dH²(x) = ∫_{rM} θ(y/r)ξ(y/r)(ω(y)) dH²(y). By im_mass_measure (c), θ(·/r)·H²⌞(rM) = θ·H²⌞M, so H²(M Δ rM) = 0 (both multiplicities are ≥ 1). Therefore T_y = approxTangentPlane 2 (rM) y = T_{y/r} for μ-a.e. y (dtc_approxTangent_of_null_diff applied to M ∩ rM ⊆ M and M ∩ rM ⊆ rM, and uniqueness of approximate tangent spaces). Hence G(rx) = G(x) for μ-a.e. x (A and π are linear), and ∫ b dμ = r²∫ b(rx) dμ(x) for Borel b ≥ 0 (μ(rE) = r²μ(E)). (b) Let s_1 := s/4, λ ∈ C^∞_c((1 − 2s_1, 1 + 2s_1)), r ∈ (1 − s_1, 1 + s_1), ψ ∈ C^∞_c((−s, s)) with ∫ψ = 1, and Φ(λ, ψ) := ∫∫_{O_s} λ(t)ψ(α)H(t, α) dt dα = ∫_{Z_s} λ(|x|)ψ(f(x))G(x) dμ(x) (7(c)). f, |q(x)|/|x| and, μ-a.e., G are invariant under x ↦ rx, and λ(|x|/r) ≠ 0 forces |x| ∈ (r(1 − 2s_1), r(1 + 2s_1)) ⊆ (1 − s, 1 + s). So (a) gives Φ(λ(·/r), ψ) = r²Φ(λ, ψ). With H = h(t), this reads ∫λ(t/r)h(t) dt = r²∫λ(t)h(t) dt, i.e. ∫λ(u)(h(ru) − rh(u)) du = 0. As λ is arbitrary, h(ru) = rh(u) for a.e. u ∈ (1 − 2s_1, 1 + 2s_1), for each such r. Put g(u) := h(u)/u. By Fubini, the function (u, r) ↦ g(ru) − g(u) vanishes a.e. on (1 − 2s_1, 1 + 2s_1) × (1 − s_1, 1 + s_1). So there is u_0 with |u_0 − 1| < s_1/4 and g(ru_0) = g(u_0) for a.e. r ∈ (1 − s_1, 1 + s_1). Substituting v = ru_0, g = c := g(u_0) a.e. on (u_0(1 − s_1), u_0(1 + s_1)) ⊇ (1 − s_1/2, 1 + s_1/2). Put s_2 := s_1/2: H(t, α) = ct for a.e. (t, α) ∈ (1 − s_2, 1 + s_2) × (−s, s), and c ≥ 0.
10. (c = m.) For 0 < s' ≤ s_2, 7(c) with b := 1_{(1−s',1+s')×(−s',s')} gives ∫_{Z_s(s')} G dμ = ∫_{1−s'}^{1+s'} 2s'·ct dt = 4cs'². (a) For x ∈ M ∖ E_0 let d(x) := ⟨a, x̂⟩⟨e, τ⟩ − ⟨a, τ⟩⟨e, x̂⟩, with τ as in step 5. Then d(x) = ±(a^♭ ∧ e^♭)(u_1, u_2) for every orthonormal basis (u_1, u_2) of T_x, where (a^♭ ∧ e^♭)(u, v) := ⟨a, u⟩⟨e, v⟩ − ⟨a, v⟩⟨e, u⟩. Since Ax̂ = ⟨x̂, a⟩e − ⟨x̂, e⟩a, ⟨τ, Ax⟩ = |x|·d(x), so G(x) = |x|²d(x)²/|πx|² ≥ d(x)² ≥ 1 − 2(1 − |d(x)|) (|d| ≤ 1); and G ≤ 1. (b) (Tilt.) s'^{−2}∫_{B_{3s'}(a)}(1 − |d|) dμ → 0 as s' → 0⁺. Let s'_j → 0⁺. By step 1 (λ_j := s'_j), along a subsequence C_j := blowUp C a s'_j ⇀ c_0[[Q]], i.e. C'(ω) = c_0∫_Q ω(x)(τ') dH² with |c_0| = m and τ' an orthonormal basis of Q, and μ_{C_j} → m·H²⌞Q vaguely. C_j is represented by (η_j(M), θ∘η_j^{−1}, ξ∘η_j^{−1}) with η_j := dilation a s'_j (dtc_blowUp_testForm_corr and the change of variables w = η_j(x), as in 9(a); approximate tangent spaces by dtc_approxTangent_dilation). Its measure is μ_j := s'_j^{−2}(η_j)_#μ. Fix g ∈ C^∞_c(ℝ^P) with 0 ≤ g ≤ 1 and g = 1 on closedBall(0, 3), and let ω_g := g·(a^♭ ∧ e^♭). Then C_j(ω_g) = ∫ g(w)·ξ(η_j^{−1}w)(a^♭ ∧ e^♭) dμ_j(w), and ξ(x)(a^♭ ∧ e^♭) = ±d(x) for x ∈ M ∖ E_0, so |C_j(ω_g)| ≤ ∫ g·|d∘η_j^{−1}| dμ_j. Also C_j(ω_g) → c_0∫_Q g(x)·(a^♭ ∧ e^♭)(τ') dH² = ±c_0∫_Q g dH² (τ' and (a, e) are orthonormal bases of Q), and ∫ g dμ_j → m∫_Q g dH². Hence 0 ≤ ∫ g(1 − |d∘η_j^{−1}|) dμ_j → 0, and s'_j^{−2}∫_{B_{3s'_j}(a)}(1 − |d|) dμ ≤ ∫ g(1 − |d∘η_j^{−1}|) dμ_j → 0. Since every sequence has such a subsequence, the claim follows. (c) (Mass.) s'^{−2}μ(Z_s(s')) → 4m as s' → 0⁺. By 4(b), μ(Z_s(s')) = μ(Z_s(s') ∩ B_{3s'}(a)) = s'²μ_{(s')}(D_{s'}), where μ_{(s')} := s'^{−2}(η_{a,s'})_#μ and D_{s'} := {w ∈ B_3(0) : a + s'w ∈ Z_s(s')}. For |w| < 3, (|a + s'w| − 1)/s' = ⟨w, a⟩ + O(s') and f(a + s'w)/s' = ⟨w, e⟩ + O(s') uniformly, and |q(a + s'w)| = s'|q(w)| < s|a + s'w| for small s'. So for each η' ∈ (0, 1/2) and all small s', U_{η'} := {w ∈ B_3(0) : |⟨w, a⟩| < 1 − η', |⟨w, e⟩| < 1 − η'} ⊆ D_{s'} ⊆ K_{η'} := {w ∈ closedBall(0, 3) : |⟨w, a⟩| ≤ 1 + η', |⟨w, e⟩| ≤ 1 + η'}. Along subsequences μ_{(s')} → m·H²⌞Q vaguely (step 1), and m·H²(Q ∩ U_{η'}) = 4m(1 − η')², m·H²(Q ∩ K_{η'}) = 4m(1 + η')² (squares in Q contained in B_3(0)). Semicontinuity on open and compact sets and the arbitrariness of η' give the claim. (d) By (a), 1 − 2(1 − |d|) ≤ G ≤ 1 on spt C ∩ Z_s(s') ⊆ B_{3s'}(a). Hence μ(Z_s(s')) − 2∫_{B_{3s'}(a)}(1 − |d|) dμ ≤ 4cs'² ≤ μ(Z_s(s')). Dividing by s'² and letting s' → 0⁺, (b) and (c) give c = m.
11. (Fibre inequalities.) Let s_3 := min(s_2, δ/2). For a.e. (t, α) ∈ (1 − s_2, 1 + s_2) × (−s_3, s_3) the following hold. (i) H(t, α) = mt. (ii) X(t, α) ∩ E_0 = ∅ and N(t, α) < ∞. (iii) Every x ∈ X(t, α) has |x| = t and |P_{T_x}Ax| ≤ |πx| ≤ t, with |πx| < t unless x ∈ Q, and the only point of Q ∩ Ω ∩ F^{−1}(t, α) is x_Q(t, α) := t(cos α·a + sin α·e). By (i) and (iii), N(t, α) ≥ H(t, α)/t = m. (iv) Let Sec' := {t(cos α·a + sin α·e) : |t − 1| < s_2, 0 < α < s_3}, an open subset of Q contained in the sector of the hypothesis. For H²-a.e. y ∈ Sec' we have y ∈ M, θ(y) = k and T_y = Q. Indeed, by density_eq_multiplicity_ae, for H²-a.e. y ∈ ℝ^P the density ratio of μ at y tends to 1_M(y)θ(y), while for y ∈ Sec' it tends to k ≥ 1 by hypothesis; so y ∈ M and θ(y) = k for H²-a.e. y ∈ Sec'. For such y choose r > 0 with spt C ∩ B_r(y) ⊆ Q (hypothesis) and Q ∩ B_r(y) ⊆ Sec'. Since μ vanishes off spt C, H²(M ∖ spt C) = 0 (θ ≥ 1); also H²(Sec' ∖ M) = 0. So M ∩ B_r(y) and Q ∩ B_r(y) differ by an H²-null set. Q has approximate tangent space Q at y (SimonGMT `hasApproximateTangentSpaceAt_submodule`), so by dtc_approxTangent_of_null_diff (applied to M ∩ Q ⊆ Q and M ∩ Q ⊆ M with V := B_r(y)) and uniqueness, T_y = Q. The map (t, α) ↦ x_Q(t, α) is a diffeomorphism of (1 − s_2, 1 + s_2) × (0, s_3) onto Sec' with Jacobian t (polar coordinates in Q). Hence for a.e. (t, α) with α ∈ (0, s_3): x_Q(t, α) ∈ M ∖ E_0 (T_{x_Q} = Q ∋ x_Q), θ(x_Q) = k, x_Q ∈ Z_s (q(x_Q) = 0), hence x_Q ∈ X(t, α), and |P_{T_{x_Q}}Ax_Q| = |Ax_Q| = t (Ax_Q ∈ Q).
12. (Conclusion.) If k > m, then for a.e. (t, α) ∈ (1 − s_2, 1 + s_2) × (0, s_3), H(t, α) ≥ θ(x_Q)·t = kt > mt, contradicting 11(i). Suppose k < m. For a.e. such (t, α) write N = k + N' and H = kt + H', where N', H' are the sums over X(t, α) ∖ {x_Q}. Then H' = (m − k)t > 0, so X(t, α) ∖ {x_Q} ≠ ∅. Each of its points lies off Q, hence has |P_{T_x}Ax| < t, so N' = Σθ(x) > Σθ(x)|P_{T_x}Ax|/t = m − k. N' and m − k being integers, N' ≥ m − k + 1, i.e. N(t, α) ≥ m + 1. With 11(iii), for 0 < s' ≤ s_3: ∫∫_{(1−s',1+s')×(−s',s')} N ≥ 2s'·(s'm + s'(m + 1)) = (4m + 2)s'². On the other hand, with Sq := (1 − s', 1 + s') × (−s', s'), (AF) applied to h := θ·(1_{Sq}∘F) (Borel; its fibre sum is 1_{Sq}·N, as Z_s ∩ F^{−1}(Sq) = Z_s(s')), J* = J H²-a.e. and 4(b) give ∫∫_{Sq} N = ∫_{Z_s(s')} J dμ ≤ ∫_{Z_s(s')} |πx|^{−1} dμ ≤ μ(Z_s(s'))/(1 − 2s') (on spt C ∩ Z_s(s'), |πx| ≥ |x| − |q(x)| ≥ (1 − s')(1 − s'/4)). Since s'^{−2}μ(Z_s(s')) → 4m by 10(c), we get 4m + 2 ≤ 4m in the limit, a contradiction. Therefore k = m = Θ(a), i.e. HasMassDensity C a k. ∎

## Key steps

1. By cone_tangent_cone_planar, every tangent cone at a is ±m[[Q']] with m = Θ(a) ∈ ℕ_{≥1}; the sector forces Q' = Q, so the tangent plane at a is unique, and spt C lies in a cusp around Q near a.
2. Stationarity with the rotation field X = ψ(f)λ(|x|)ζ(x)Ax of Q (A antisymmetric, ζ = 1 on spt C near a by the cusp), radial tangency, and the weighted area formula for F = (|x|, angle) on the carrier (sibling child carrier_area_formula, whose Jacobian equals |P_{T_x}Ax|/|πx|² a.e.) give: the fibre sum H(t, α) = Σ θ|P_{T_x}Ax| is a.e. independent of α.
3. Dilation invariance of the cone gives H = ct, and the tilt convergence of the blow-ups at a (current convergence to ±m[[Q]]) with the mass density m gives c = m.
4. Integrality: on the sector side the fibre contains the sector point (multiplicity k, |P Ax| = t) and, if k < m, further points off Q with |P Ax| < t, whose multiplicities sum to ≥ m − k + 1; so the fibre count N ≥ m + 1 there and N ≥ m elsewhere.
5. This contradicts ∫∫N = ∫J dμ ≤ μ(Z_s(s'))/(1 − 2s') ≈ 4ms'²; and k > m contradicts H = mt directly. Hence Θ(a) = k.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n '^theorem\|^def' simongmt Chapter02/{AreaNoninjective,AreaLipschitz,AreaMultiplicity,AreaBranches,AreaApproximation,WeightedArea}.lean Chapter03/{Rectifiable,Differential,SubmanifoldCover}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|area_image_compl_regularSet_eq_zero|measurable_areaJacobianAt|weightedAreaFiberSum_iUnion|exists_injective_partition_of_regular|ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt/Poincare/SimonGMT`
- `grep -rn 'normDet_sq_eq_det_gram|normDet_comp|euclideanHausdorffMeasure_image|exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|LipschitzWith.ae_differentiableAt|Besicovitch.ae_tendsto_measure_inter_div|extend_finite_dimension|ContDiffOn.exists_lipschitzOnWith|lintegral_withDensity_eq_lintegral_mul_non_measurable|EventuallyEq.fderiv_eq|AEMeasurable.ennreal_tsum|lintegral_tsum|restrict_iUnion|exists_antilipschitzWith' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rln 'C1Approximation|c1_approximation|lusin_c1' simongmt/Poincare/SimonGMT (no match); grep -n 'area formula' book/chapter-03.txt; sed -n 330,412p book/chapter-03.txt`
- `python3 scan of dag.json: lean_names containing idtp (none) or area; lean statements of dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, dpf_area_formula_bilipschitz_rectifiable, imrep_approxTangent_starProjection_aesm, dtc_* lemmas and dimred_* siblings`
- `grep -l idtp_ nodes/*/*.json outside this node (none); for d in .swarm-worktrees/*/gmt-ch07/GMT: grep -rl 'idtp_|carrier_area_formula' (none)`
- `lean /tmp/idtp_v3/check/Probe.lean (normDet, weightedAreaFiberSum, areaJacobianAt, tangentialJacobian are not in the import closure of GMT.Ch07.Submission)`
- `lean /tmp/idtp_v3/check/NewChild.lean; lean /tmp/idtp_v3/check/GramCheck.lean (#print axioms idtp_v3_gram_sqrt_eq_normDet)`
- `lean /tmp/idtp_v3/check/FromJsonV3.lean (#print axioms idtp_parent_check_json_v3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-supplied-natural-proof.md`
- `/tmp/idtp_v3/check/FromJsonV3.lean`
- `/tmp/idtp_v3/check/GramCheck.lean`
- `/tmp/idtp_v3/check/NewChild.lean`
- `/tmp/idtp_v3/check/Probe.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD) and mathlib 25730c7c; SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Library support for the new child.
- SimonGMT provides the Euclidean-domain Lipschitz area formulas: weighted_area_formula_lipschitz_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitz (AreaNoninjective.lean); weighted_area_formula_lipschitz_injOn with arbitrary weights, areaRegularSet, measurableSet_areaRegularSet and area_image_compl_regularSet_eq_zero (AreaLipschitz.lean); measurable_areaJacobianAt; weightedAreaFiberSum_iUnion.
- SimonGMT also provides HasApproximateTangentSpaceAt.unique and ae_eq_const_of_weak_coordinate_derivatives_zero (C¹ test functions).
- SimonGMT has no area formula on rectifiable carriers, no C¹ approximation theorem, and no rectifiable⇒C¹-cover direction of Ch. 3 Lemma 1.2 (searches found no match; the SubmanifoldCover header confirms this). The new child therefore proves Simon 2.4–2.5 from Lipschitz bi-Lipschitz pieces.
- Mathlib provides normDet_sq_eq_det_gram, normDet_comp, LinearMap.euclideanHausdorffMeasure_image, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Rademacher's theorem, Besicovitch density, Lipschitz extension, ContDiffOn.exists_lipschitzOnWith, lintegral_withDensity_eq_lintegral_mul_non_measurable and EventuallyEq.fderiv_eq.

Lean statement of the new child. normDet, weightedAreaFiberSum, areaJacobianAt and tangentialJacobian are not in the import closure of GMT.Ch07.Submission. The new type therefore writes the Jacobian as Real.sqrt (Matrix.det (Matrix.of Gram)) and the fibre sum as a tsum over a subtype. GramCheck.lean proves that this equals normDet of the restricted derivative (axioms propext, Classical.choice, Quot.sound).

DAG. The related other-branch nodes dpf_rectifiable_bilipschitz_pieces and dpf_approxTangent_ae_bilipschitz_piece are not comparator-accepted, so they are not reused; their arguments are re-proved inside the new child. Accepted lemmas cited by children (imrep_approxTangent_starProjection_aesm, dtc_*) have DAG types matching their uses.

Names. No idtp_* name occurs in dag.json, in other nodes' decompositions or in any worktree's GMT sources, so the 11 names are unreserved.

Lean check. All 11 statements elaborate, and the hypothesis-only assembly proves IntegerDensityAndTangentPlanes. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
