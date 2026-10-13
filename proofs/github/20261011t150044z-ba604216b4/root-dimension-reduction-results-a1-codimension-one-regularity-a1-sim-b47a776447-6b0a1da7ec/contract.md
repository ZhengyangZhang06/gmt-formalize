<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1 -->

## Theorem `Submission.codim1_density_one_regular_local_rep`

Local multiplicity-one structure at a regular point of density one. Data: P, m ∈ ℕ with m ≥ 1; an open set U ⊆ ℝ^P; T ∈ 𝒟_m(U) (GeometricCurrentOn U m); y ∈ ℝ^P. Hypotheses: y ∈ reg T (regularSet T: y ∈ spt T and, for some ρ_y > 0 with B_{ρ_y}(y) ⊆ U, T(ω) = m_y∫_{M_y}⟨ω, ξ_y⟩ dH^m whenever tsupport ω ⊆ B_{ρ_y}(y), for an integer m_y ≠ 0 and an embedded C¹ m-submanifold M_y ∋ y with orientation ξ_y and H^m(M_y ∩ K) < ∞ for compact K ⊆ B_{ρ_y}(y)); and Θ^m(μ_T, y) = 1 (HasMassDensity T y 1). Conclusion: there is ρ₀ > 0 with B_{ρ₀}(y) ⊆ U such that for every ρ ∈ (0, ρ₀] there is ξ : ℝ^P → Λ_m(ℝ^P) (MultiVector P m) with (i) spt T ∩ B_ρ(y) an embedded C¹ m-dimensional submanifold of ℝ^P (IsEmbeddedSubmanifold 1 m); (ii) ξ an orientation of spt T ∩ B_ρ(y) (IsOrientation: ξ continuous there and ξ(x) a unit orientation of tangentSpace(spt T ∩ B_ρ(y), x)); (iii) H^m(spt T ∩ B_ρ(y)) < ∞; (iv) T(ω) = ∫_{spt T ∩ B_ρ(y)} ⟨ω(x), ξ(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ B_ρ(y). Here H^m = μHE[m] and B_ρ(y) = ball y ρ.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4352

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4203

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5602, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5619, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5636, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4182, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4192

## Lean problem

Declaration: `Submission.codim1_density_one_regular_local_rep`

```lean
∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (y : Euclid P), 1 ≤ m → IsOpen U → y ∈ regularSet T → HasMassDensity T y 1 → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ball y ρ₀ ⊆ U ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ ξ : Euclid P → MultiVector P m, IsEmbeddedSubmanifold 1 m (T.support ∩ ball y ρ) ∧ IsOrientation m (T.support ∩ ball y ρ) ξ ∧ μHE[m] (T.support ∩ ball y ρ) ≠ ∞ ∧ ∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y ρ → T ω = ∫ x in T.support ∩ ball y ρ, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step B2 (B2a–B2e: local structure of M at a regular point of density one) of the supplied proof of codim1_simons_regular_cone_density, written for an arbitrary open U. Book: Simon 7.4.1 (reg T; contract regularSet), Ch. 3, 1.8(2) (density of a set with a tangent plane, chapter-03.txt lines 298–316), Ch. 6, 2.5 (M_W, chapter-06.txt line 231) and 2.11 (spt T, line 299); Ch. 2, §4, 4.1 (local representations, chapter-02.txt line 854).
Departure from the parent text, stated explicitly. The parent's B2c–B2d get M_W(T) = |m_y|·H^m(M_y ∩ W) from oriented_piece_mass. That declaration is a sibling of the parent node: it is unaccepted and owned by another parent, so it cannot be a dependency of this node. The proof below needs only a lower bound for M_{B_s(y)}(T) (step 4), obtained by testing T with one constant covector times a bump function. Membership of M_y ∩ B_ρ(y) in spt T (the last bullet of B2d) is shown in step 6b by positivity of T on such forms, not through densities.

Reused accepted declarations (sibling subproblems with identical frozen types):
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): there is a continuous linear L : Λ_m(ℝ^P) → Λ^m(ℝ^P) such that every unit orientation ξ of a subspace satisfies (a) |ξ(α)| ≤ |α| for all α, (b) |L(ξ)| ≤ 1, (c) ξ(L(ξ)) = 1.
- chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv): if (V, W, ψ) satisfies the chart clauses of IsEmbeddedSubmanifold r d N with r ≥ 1, then tangentSpace N (ψ v) = range Dψ(v) for every v ∈ V.
- bilipschitz_measure (Submission.dimred_rpd_bilipschitz_image_measure): if E ⊆ ℝ^n, c₁ > 0, c₂ ≥ 0 and c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b| for a, b ∈ E, then c₁ⁿ·Lⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿ·Lⁿ(E).

Notation.
- H^m := μHE[m]. On ℝ^m = Euclid m it is Lebesgue measure L^m, and it is invariant under isometries.
- ω_m := unitBallVolume m = L^m(B_1(0)) ∈ (0, ∞), so L^m(B_r(0)) = ω_m r^m. B_s(x) := ball x s.
- Λ^m := Covector (Euclid P) m and Λ_m := MultiVector P m. ⟨α, ξ⟩ := ξ(α). |α| := covectorEuclideanNorm α, a norm on Λ^m.
- M_W(T) := T.massOn W = sup{ofReal T(ω) : ω ∈ 𝒟^m(U), tsupport ω ⊆ W, |ω(x)| ≤ 1 for all x}. Such ω are admissible for W.
- T vanishes on W if T(ω) = 0 whenever tsupport ω ⊆ W. Z(T) is the union of the open W with closure W compact and contained in U on which T vanishes; spt T = U ∖ Z(T).
- A chart of an embedded C¹ m-submanifold N at w is a triple (V, W, ψ) as in the definition of IsEmbeddedSubmanifold 1 m N with w ∈ W.

Facts on embedded C¹ submanifolds (N an embedded C¹ m-submanifold of ℝ^P).
(F1) Charts are closed embeddings. Let (V, W, ψ) be a chart of N.
 (i) If v_j ∈ V and ψ(v_j) → z ∈ W, then a subsequence of (v_j) converges to some v ∈ V with ψ(v) = z. Indeed K := {z} ∪ {ψ(v_j) : j} is a compact subset of W, so V ∩ ψ⁻¹(K) is compact and contains every v_j; a subsequence converges in it, and ψ(v) = z by continuity of ψ on the open set V.
 (ii) Hence W ∩ N = ψ(V) is closed in W, and ψ⁻¹ : W ∩ N → V is continuous: if ψ(v_j) → ψ(v), every subsequence of (v_j) has a further subsequence converging to some v' with ψ(v') = ψ(v), and v' = v by injectivity. So ψ(V') is relatively open in N for every open V' ⊆ V.
(F0) N is Borel. By (F1)(ii) every w ∈ N has an open W_w ∋ w with W_w ∩ N closed in W_w. By second countability countably many W_{w_k} cover N, and N = ⋃_k (W_{w_k} ∩ N) is a countable union of intersections of an open and a closed set.
(F2) Open pieces. Let O ⊆ ℝ^P be open. Then N ∩ O is an embedded C¹ m-submanifold, and for w ∈ N ∩ O, tangentSpace(N ∩ O, w) = tangentSpace(N, w) = range Dψ(ψ⁻¹(w)) for every chart (V, W, ψ) of N at w. This is an m-dimensional linear subspace.
 Proof. (V ∩ ψ⁻¹(O), W ∩ O, ψ) is a chart of N ∩ O at w:
 - V ∩ ψ⁻¹(O) is open, since ψ is continuous on the open set V;
 - ψ(V ∩ ψ⁻¹(O)) = W ∩ O ∩ N;
 - for compact K ⊆ W ∩ O, (V ∩ ψ⁻¹(O)) ∩ ψ⁻¹(K) = V ∩ ψ⁻¹(K) is compact;
 - C¹-smoothness, injectivity and injectivity of Dψ restrict.
 Both charts have the same derivative at ψ⁻¹(w), so chart_tangent_space gives both tangent-space identities. range Dψ(ψ⁻¹(w)) has dimension m because Dψ(ψ⁻¹(w)) is injective on ℝ^m.
(F3) Positivity. For w ∈ N and r > 0, H^m(N ∩ B_r(w)) > 0.
 Proof. Let (V, W, ψ) be a chart at w, v₀ := ψ⁻¹(w) and A := Dψ(v₀). A is injective, so 2c|a| ≤ |Aa| for some c > 0. By continuity of Dψ choose δ > 0 with closedBall(v₀, δ) ⊆ V, ‖Dψ(v) − A‖ ≤ c on B_δ(v₀), and ψ(B_δ(v₀)) ⊆ B_r(w). For a, b ∈ B_δ(v₀) the mean value inequality for ψ − A gives |ψ(a) − ψ(b) − A(a − b)| ≤ c|a − b|. Hence c|a − b| ≤ |ψ(a) − ψ(b)| ≤ (‖A‖ + c)|a − b|. By bilipschitz_measure, H^m(ψ(B_δ(v₀))) ≥ c^m·L^m(B_δ(v₀)) > 0, and ψ(B_δ(v₀)) ⊆ N ∩ B_r(w).
(F4) Density one (Simon Ch. 3, 1.8(2), C¹ case). For w ∈ N, H^m(N ∩ B_s(w))/(ω_m s^m) → 1 as s ↓ 0.
 Proof. Set-up.
 - Let (V, W, ψ) be a chart at w, v₀ := ψ⁻¹(w), A := Dψ(v₀) and Q := range A (dimension m).
 - Let p be the orthogonal projection onto Q, p^⊥ := id − p, and ι : ℝ^m → ℝ^P a linear isometry with range Q.
 - F := ι⁻¹∘p∘(ψ − w) : V → ℝ^m is C¹ with DF(v₀) = ι⁻¹∘A invertible. By the inverse function theorem there are open V₁ ∋ v₀ (V₁ ⊆ V) and G ∋ 0 such that F : V₁ → G is a C¹ diffeomorphism.
 - Put u := p^⊥∘(ψ − w)∘F⁻¹ : G → Q^⊥ and g(a) := w + ι(a) + u(a). Then ψ∘F⁻¹ = g on G, u is C¹, u(0) = 0, and Du(0) = 0 because A has range Q.
 - By (F1)(ii), ψ(V₁) = N ∩ O₁ for an open O₁ ∋ w. Choose s₁ > 0 with B_{s₁}(w) ⊆ O₁ and closedBall(0, s₁) ⊆ G.
 - For 0 < s < s₁ put L(s) := sup{‖Du(a)‖ : |a| ≤ s}. Then L(s) → 0 as s ↓ 0.
 Estimates for 0 < s < s₁.
 - For |a|, |b| ≤ s: ι(a) − ι(b) ∈ Q is orthogonal to u(a) − u(b) ∈ Q^⊥, and |u(a) − u(b)| ≤ L(s)|a − b|. So |a − b| ≤ |g(a) − g(b)| ≤ (1 + L(s))|a − b|, and |u(a)| ≤ L(s)|a|.
 - N ∩ B_s(w) = g(E_s) with E_s := {a ∈ B_s(0) : |a|² + |u(a)|² < s²}. A point of N ∩ B_s(w) lies in ψ(V₁) = g(G), and |g(a) − w|² = |a|² + |u(a)|², which forces a ∈ E_s. Conversely g(E_s) ⊆ ψ(V₁) ⊆ N.
 - B_{s/√(1+L(s)²)}(0) ⊆ E_s ⊆ B_s(0).
 - bilipschitz_measure (χ := g, E := E_s, c₁ = 1, c₂ = 1 + L(s)) gives L^m(E_s) ≤ H^m(N ∩ B_s(w)) ≤ (1 + L(s))^m L^m(E_s).
 - Hence (1 + L(s)²)^{−m/2} ≤ H^m(N ∩ B_s(w))/(ω_m s^m) ≤ (1 + L(s))^m, and both bounds tend to 1.

Proof.
1. (Unfolding y ∈ reg T.) The definition of regularSet gives:
 - ρ_y > 0 with B_{ρ_y}(y) ⊆ U, and m_y ∈ ℤ ∖ {0};
 - an embedded C¹ m-submanifold M_y ∋ y with an orientation ξ_y: ξ_y is continuous on M_y, and for each w ∈ M_y, ξ_y(w) is a unit orientation of a subspace Q_w with (Q_w : Set) = tangentSpace(M_y, w);
 - H^m(M_y ∩ K) < ∞ for every compact K ⊆ B_{ρ_y}(y);
 - (R) T(ω) = m_y ∫_{M_y} ⟨ω(x), ξ_y(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ B_{ρ_y}(y).
 For such ω the integrand is integrable on M_y. M_y is Borel by (F0). x ↦ ξ_y(x)(ω(x)) is continuous on M_y and vanishes off the compact set tsupport ω ⊆ B_{ρ_y}(y). It is bounded by |ω(x)| ≤ sup|ω| (unit_orientation_dual (a)), and H^m(M_y ∩ tsupport ω) < ∞.
2. (Choice of ρ₀.) Let (V, W, ψ) be a chart of M_y at y. By (F1)(ii), W ∩ M_y is closed in W. Choose ρ₀ > 0 with 2ρ₀ < ρ_y and B_{2ρ₀}(y) ⊆ W. Then:
 - B_{ρ₀}(y) ⊆ U;
 - closedBall(y, ρ₀) is a compact subset of B_{ρ_y}(y), so c₀ := H^m(M_y ∩ closedBall(y, ρ₀)) < ∞;
 - for every ρ ∈ (0, ρ₀], M_y ∩ B_ρ(y) is relatively closed in B_ρ(y).
3. (Dual covectors.) Let L be the map of unit_orientation_dual for (P, m). For w ∈ M_y, |L(ξ_y(w))| ≤ 1 and ξ_y(w)(L(ξ_y(w))) = 1. For fixed β ∈ Λ^m, x ↦ ξ_y(x)(β) is continuous on M_y, because evaluation at β is a continuous linear functional on Λ_m.
4. (|m_y| = 1.) Fix ε ∈ (0, 1). Put β₀ := L(ξ_y(y)) and β := sgn(m_y)·β₀, so |β| ≤ 1. By step 3 there is s₀ ∈ (0, ρ₀] with ξ_y(x)(β₀) ≥ 1 − ε for all x ∈ M_y ∩ B_{s₀}(y).
 Let 0 < s < s₀ and η ∈ (0, 1).
 - Choose a smooth φ : ℝ^P → [0, 1] with φ = 1 on closedBall(y, (1 − η)s) and tsupport φ ⊆ B_s(y).
 - ω := φ·β is smooth with compact tsupport ω ⊆ B_s(y) ⊆ U, so ω ∈ 𝒟^m(U). Also |ω(x)| = φ(x)|β| ≤ 1, so ω is admissible for B_s(y) and ofReal(T(ω)) ≤ M_{B_s(y)}(T).
 - By (R), T(ω) = m_y·sgn(m_y) ∫_{M_y} φ·ξ_y(β₀) dH^m = |m_y| ∫_{M_y} φ(x) ξ_y(x)(β₀) dH^m(x).
 - The integrand is ≥ 0 on M_y: φ = 0 off B_s(y), and ξ_y(β₀) ≥ 1 − ε > 0 on M_y ∩ B_s(y). It is ≥ 1 − ε on M_y ∩ closedBall(y, (1 − η)s).
 - Hence M_{B_s(y)}(T) ≥ |m_y|(1 − ε)·H^m(M_y ∩ closedBall(y, (1 − η)s)).
 As η ↓ 0 the closed balls increase to B_s(y). By continuity of measure from below,
 (4.1) M_{B_s(y)}(T) ≥ |m_y|(1 − ε)·H^m(M_y ∩ B_s(y)) for 0 < s < s₀.
 Divide by ω_m s^m ∈ (0, ∞) and let s ↓ 0:
 - the left side tends to 1 by the hypothesis HasMassDensity T y 1;
 - the right side tends to |m_y|(1 − ε) by (F4) with N := M_y and w := y.
 So |m_y|(1 − ε) ≤ 1 for every ε ∈ (0, 1), and |m_y| ≤ 1. Since m_y is a nonzero integer, m_y ∈ {1, −1}.
5. (The orientation.) Put ξ(x) := m_y·ξ_y(x) = ±ξ_y(x).
 - ξ is continuous on M_y.
 - For w ∈ M_y, ξ(w) is a unit orientation of Q_w, since IsUnitOrientationOf allows either sign. Hence |L(ξ(w))| ≤ 1 and ξ(w)(L(ξ(w))) = 1.
 - (R) becomes (R') T(ω) = ∫_{M_y} ⟨ω, ξ⟩ dH^m whenever tsupport ω ⊆ B_{ρ_y}(y).
6. (Support.) Fix ρ ∈ (0, ρ₀] and put S := spt T ∩ B_ρ(y). We show S = M_y ∩ B_ρ(y).
 (6a) S ⊆ M_y. Let x ∈ B_ρ(y) ∖ M_y.
 - By step 2 there is r > 0 with closedBall(x, r) ⊆ B_ρ(y) and closedBall(x, r) ∩ M_y = ∅.
 - If ω ∈ 𝒟^m(U) and tsupport ω ⊆ B_r(x), then ω = 0 on M_y, so T(ω) = 0 by (R').
 - B_r(x) is open with compact closure closedBall(x, r) ⊆ U. So B_r(x) ⊆ Z(T) and x ∉ spt T.
 (6b) M_y ∩ B_ρ(y) ⊆ S. Let w ∈ M_y ∩ B_ρ(y) and suppose w ∈ Z(T): w ∈ O for an open O with compact closure in U on which T vanishes.
 - Put β_w := L(ξ(w)). By continuity choose r > 0 with B_r(w) ⊆ O ∩ B_ρ(y) and ξ(x)(β_w) ≥ 1/2 for x ∈ M_y ∩ B_r(w).
 - Take a smooth φ : ℝ^P → [0, 1] with φ = 1 on closedBall(w, r/2) and tsupport φ ⊆ B_r(w), and ω := φ·β_w ∈ 𝒟^m(U).
 - tsupport ω ⊆ O, so T(ω) = 0.
 - By (R'), T(ω) = ∫_{M_y} φ·ξ(β_w) dH^m. The integrand is ≥ 0 on M_y and ≥ 1/2 on M_y ∩ B_{r/2}(w), so T(ω) ≥ ½·H^m(M_y ∩ B_{r/2}(w)) > 0 by (F3).
 This contradiction shows w ∉ Z(T). As w ∈ B_ρ(y) ⊆ U, w ∈ spt T.
7. (Conclusions for ρ ∈ (0, ρ₀].)
 (i) By step 6, S = M_y ∩ B_ρ(y). By (F2) with O := B_ρ(y), S is an embedded C¹ m-submanifold and tangentSpace(S, w) = tangentSpace(M_y, w) for w ∈ S.
 (ii) ξ is continuous on S ⊆ M_y. For w ∈ S, ξ(w) is a unit orientation of Q_w with (Q_w : Set) = tangentSpace(M_y, w) = tangentSpace(S, w). So ξ is an orientation of S (IsOrientation m S ξ).
 (iii) H^m(S) ≤ H^m(M_y ∩ closedBall(y, ρ₀)) = c₀ < ∞.
 (iv) Let ω ∈ 𝒟^m(U) with tsupport ω ⊆ B_ρ(y). Then ω(x) = 0 for every x ∈ M_y ∖ B_ρ(y), so the integrand of (R') vanishes on M_y ∖ S. Hence T(ω) = ∫_{M_y} ⟨ω, ξ⟩ dH^m = ∫_S ⟨ω(x), ξ(x)⟩ dH^m(x).
 Together with ρ₀ > 0 and B_{ρ₀}(y) ⊆ U (step 2), this proves the statement. ∎

## Key steps

1. Unfold y ∈ reg T: T = m_y[[M_y]] on B_{ρ_y}(y), with M_y an embedded C¹ submanifold oriented by a continuous ξ_y. Charts are closed embeddings, so M_y ∩ B_ρ(y) is relatively closed in B_ρ(y) for ρ ≤ ρ₀.
2. Testing T with φ·sgn(m_y)·L(ξ_y(y)) gives M_{B_s(y)}(T) ≥ |m_y|(1−ε)·H^m(M_y ∩ B_s(y)). Density one of T and of C¹ submanifolds (graph over the tangent plane, bilipschitz_measure) forces |m_y| = 1.
3. T vanishes off M_y inside B_ρ(y). Bump forms φ·L(ξ(w)), with positivity of H^m on open pieces, put every w ∈ M_y ∩ B_ρ(y) in spt T. So spt T ∩ B_ρ(y) = M_y ∩ B_ρ(y).
4. Open pieces of embedded C¹ submanifolds keep their charts and tangent spaces (chart_tangent_space). So ξ = m_yξ_y orients spt T ∩ B_ρ(y), which has finite H^m-measure and represents T on B_ρ(y).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, IsMinimizingIn, HasMassDensity, IsConeCurrent, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, unitBallVolume)`
- `grep -n 'def support|def zeroRegion|isOpen_zeroRegion|def massOn|structure GeometricCurrentOn|abbrev Covector' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean and Chapter02/{SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldCalculus,AreaFormula}.lean`
- `sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -n 'theorem addHaar_ball_of_pos|theorem ContinuousOn.aestronglyMeasurable|theorem setLIntegral_one|measure_sdiff_null' Mathlib`
- `python3 scans of dag.json: 518 nodes by status; children of codimension_one_regularity; accepted nodes whose statements mention IsConeCurrent, regularSet or HasMassDensity; statuses, frozen types and candidate commits of the 6 reused names; status of codim1_massOn_eq_lintegral_of_oriented_rep (decomposing)`
- `runtime.py of flow gmt-claude-b888e19cffb1: _solve_children, _existing_lean_name_problem, _wait_for_accepted_dependencies, _overlay_accepted_children`
- `git grep over all 2770 refs for the 5 new names (no match); git grep 'PseudoMetrizableSpace (MultiVector' in accepted branches`
- `lean -DautoImplicit=false /tmp/simons-split/check/Types2.lean; lean -DautoImplicit=false /tmp/simons-split/check/Assembly2.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-B.txt 1-282; chapter-02.txt 1162-1440; chapter-05.txt 1290-1380; chapter-06.txt 400-440 and 770-870; chapter-03.txt 290-330; chapter-07-source.txt 900-1010 and 1256-1300`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/simons-split/check/Types2.lean`
- `/tmp/simons-split/check/Assembly2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the selected frozen type and the 6 reused types are unchanged.
Library.
- SimonGMT supplies GeometricCurrentOn, support = U \ zeroRegion with zeroRegion open, and massOn (Chapter06).
- SimonGMT supplies the Appendix B algebra: simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean) and exists_final_exponent (SimonsInequalities.lean).
- It has only pointwise second-fundamental-form algebra (Chapter02/SecondFundamentalForm.lean): no submanifold curvature field, no Simons identity, no Allard theorem, no nonlinear push-forward. These remain book citations inside hypercone_plane and area_comparison.
- The snapshot Mathlib has μHE isometry invariance and μHE = volume on Euclid d (Geometry/Euclidean/Volume/Measure.lean), Measure.euclideanHausdorffMeasure_smul₀, and addHaar_ball_of_pos (MeasureTheory/Measure/Lebesgue/EqHaar.lean:445), used by subspace_ball_measure and offvertex_rep.
DAG.
- codim1_massOn_eq_lintegral_of_oriented_rep is decomposing (unaccepted) under another parent. It cannot be a child or a child dependency here, so only this node's glue uses it.
- The six reused names are accepted with byte-identical types. Candidate commits: dor_ims_unitOrientation_dual 9c8432cb0101, dtc_vanish_off_support 44ef61f79e21, cone_current_apply_dilation_pullback 52115c22ec2d, rsdic_unitOrientation_eq_or_eq_neg fe95347baaed, chart_tangentSpace_eq_range_fderiv d626082a69a0, dimred_rpd_bilipschitz_image_measure 0501e07ced47.
- Overlapping unaccepted nodes cannot be reused: dimred_rpd_submanifold_density_one, dimred_rpd_massOn_eq_mult_measure and imrep_c1_diffeo_pushforward_im. Child sessions may reuse them once accepted.
- The 5 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2770 refs.
Lean.
- Types2.lean elaborates all 11 child types (exit 0).
- Assembly2.lean proves the selected frozen type from 4 child types plus oriented_piece_mass as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound and those 5.
- A MultiVector PseudoMetrizableSpace instance workaround from accepted branches was needed and works.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
