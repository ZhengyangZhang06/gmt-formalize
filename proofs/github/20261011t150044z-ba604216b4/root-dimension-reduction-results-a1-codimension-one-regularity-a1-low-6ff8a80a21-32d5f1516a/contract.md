<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1.tilt_excess_step-a1 -->

## Theorem `Submission.codim1_ldr_ag_tilt_excess_one_step_decay`

For n ≥ 1 and k ≥ 0 there are θ₀ ∈ (0, 1/4] and δ₂ ∈ (0, 1/8] such that for every δ ∈ (0, δ₂] and all data satisfying (SA_δ): U, W ⊆ ℝ^{n+k} with W open and W ⊆ U; R = (M, θ, ξ_R) an integer multiplicity triple in U (IMRep U n; ξ_R = R.orient is its orientation, and ξ below denotes a point) with μ := R.measure = θHⁿ⌞M; H : ℝ^{n+k} → ℝ^{n+k} μ-a.e. strongly measurable with |H(x)| ≤ κ for all x; R.firstVariation X = −∫⟨X, H⟩dμ for every C¹ compactly supported X with tsupport X ⊆ W; ρ > 0 with the closed ball B_ρ(z) ⊆ W; z ∈ spt μ; μ(B_ρ(z)) ≤ (1 + δ)ω_nρⁿ (ω_n = unitBallVolume n); κρ ≤ δ: for every ξ ∈ spt μ ∩ B_{δρ}(z), σ ∈ (0, δρ] and n-dimensional subspace T there is an n-dimensional subspace S with E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T), where E_*(ξ, r, S') := max{r^{−n}∫_{B_r(ξ)} |p_x − p_{S'}|² dμ, κ²r²/δ} ∈ [0, ∞]. Here p_x is the orthogonal projection onto approxTangentPlane n M x, p_S the orthogonal projection onto a subspace S, |A|² := Σ_i |Ae_i|² the Hilbert–Schmidt norm (the Lean sum over EuclideanSpace.single i 1), B_t(y) the closed ball, and integrals of nonnegative functions are lower Lebesgue integrals in [0, ∞] (Lean ∫⁻ of ENNReal.ofReal).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1.tilt_excess_step-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4971

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1952, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1957, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1983, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1990, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5364, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2015, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2022, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2027

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2886, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2892, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2903, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2909, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2917, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2928, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2942

## Lean problem

Declaration: `Submission.codim1_ldr_ag_tilt_excess_one_step_decay`

```lean
∀ (n k : ℕ), 0 < n → ∃ θ₀ δ₂ : ℝ, 0 < θ₀ ∧ θ₀ ≤ 1 / 4 ∧ 0 < δ₂ ∧ δ₂ ≤ 1 / 8 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ : ℝ) (T : Submodule ℝ (Euclid (n + k))), 0 < σ → σ ≤ δ * ρ → Module.finrank ℝ T = n → ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ max (ENNReal.ofReal (1 / (θ₀ * σ) ^ n) * ∫⁻ x in closedBall ξ (θ₀ * σ), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * (θ₀ * σ) ^ 2 / δ)) ≤ ENNReal.ofReal θ₀ * max (ENNReal.ofReal (1 / σ ^ n) * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * σ ^ 2 / δ))
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.low_density_regular-a1.allard_graph-a1.tilt_excess_step-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Role in the parent proof: Claim 7A of Part 7 (Simon Ch. 5, Theorem 4.5 with p = 2n and bounded H) of the proof of the selected Allard theorem Submission.codim1_ldr_allard_bounded_curvature_graph; it is iterated by the sibling tilt_excess_decay (Submission.codim1_ldr_ag_tilt_excess_decay). Provenance: statement, frozen Lean type and proof are identical to those of the independently audited child tilt_excess_step (Submission.dorag_tilt_excess_one_step_decay) of DAG node root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1, whose supplied parent proof equals Parts 0–9 of the selected proof; the only change is that the sibling harmonic_approximation is the declaration Submission.codim1_ldr_ag_harmonic_affine_approximation.

Sibling map (dependency key — frozen Lean declaration — labels used below): tangent_projection_measurable — Submission.dorag_approxTangent_starProjection_aesm (x ↦ p_x is AE-strongly measurable for μ = R.measure); support_null — Submission.dorag_support_sdiff_carrier_null (Hⁿ((spt μ ∩ W) ∖ M) = 0); graph_tangent — Submission.dorag_lipschitz_graph_approxTangent (tangent planes along a Lipschitz graph); tilt_height — Submission.dorag_tilt_height_estimate (constant C_T for the given n, k); harmonic_approximation — Submission.codim1_ldr_ag_harmonic_affine_approximation (constant C_H; δ_h(ε') for each ε' > 0); density_bounds — Submission.dorag_standing_density_bounds (constants δ₁, C₂; (a), (b), (c), (d) are its four conclusions in order); affine_approximation — Submission.dorag_affine_approximation (constants δ₃, C₃; (4a) is its distance bound, (4b) its integral bound); lipschitz_approximation — Submission.dorag_lipschitz_approximation (constants δ₅, β, β', C₇ for the given C₆; 5A is the conjunction before its final implication, 5B is the final implication).
Source: parent proof Part 7, Claim 7A and its proof, Steps 1–10 (Simon Ch. 5, Theorem 4.5 with p = 2n, bounded H, and the corrections recorded there). Conventions: E := ℝ^{n+k}; B_t(y) closed ball, B̆_t(y) open ball, Bⁿ_t, B̆ⁿ_t balls of ℝⁿ about 0; M := R.carrier, θ := R.mult, μ := R.measure = θHⁿ⌞M, Hⁿ := μHE[n], Lⁿ Lebesgue measure on ℝⁿ; ω_n := unitBallVolume n ∈ (0, ∞); p_x := projection onto T_xM := approxTangentPlane n M x; |A|² Hilbert–Schmidt (the Lean sums), ‖A‖ ≤ |A|; E(ξ, r, S) := r^{−n}∫_{B_r(ξ)}|p_x − p_S|²dμ; α := 1/(2n+2); E_*(ξ, r, S) := max{E(ξ, r, S), δ^{−1}κ²r²} (the Lean max of ofReal(1/rⁿ)·∫⁻ and ofReal(κ²r²/δ)). "C" denotes constants depending only on n, k. Siblings used: density_bounds ((a), (b), (d); constant δ₁), affine_approximation (δ₃, C₃), lipschitz_approximation (applied with C₆ := C₁₁ below; δ₅, β, C₇), tilt_height (C_T), harmonic_approximation (C_H, δ_h(ε')), graph_tangent, support_null, tangent_projection_measurable.

Preliminaries. (P1) κ ≥ 0 since κ ≥ ‖H(x)‖. (P2) For compact K ⊆ W, μ(K) = ∫_{M∩K}θ dHⁿ < ∞ (IMRep.locallyIntegrable_mult, K ⊆ W ⊆ U) and Hⁿ(M ∩ K) ≤ μ(K) (θ ≥ 1 on M); if B_t(y) ⊆ W then B_{t'}(y) ⊆ W for some t' > t. (P3) For μ-a.e. x: x ∈ M and T_xM is an n-dimensional approximate tangent plane of M at x (IMRep.orients, the definition of approxTangentPlane and uniqueness HasApproximateTangentSpaceAt.unique), so p_x is the orthogonal projection onto an n-plane and trace p_x = n; x ↦ p_x is μ-AE-strongly measurable (tangent_projection_measurable). (P4) (MC) denotes the hypothesis R.firstVariation X = −∫⟨X, H⟩dμ for every C¹ compactly supported X with tsupport X ⊆ W; for such X, div_M X(x) = trace(p_x∘DX(x)) (Lean tangentialDivergence) is bounded, μ-measurable (P3) and supported in a compact subset of W, hence μ-integrable (P2), and R.firstVariation X = ∫_Mθ div_M X dHⁿ = ∫div_M X dμ; so (MC) reads ∫div_M X dμ = −∫⟨X, H⟩dμ. (P5) μ(E ∖ M) = 0 and μ(E ∖ spt μ) = 0; μ ≪ Hⁿ⌞M and Hⁿ⌞M ≤ μ, so μ-null and Hⁿ⌞M-null sets coincide.
0. Constants. Let C₁₁ := 2C₃ + (8C₃/ω_n)^{1/2} and take δ₅, β, β', C₇ from lipschitz_approximation with C₆ := C₁₁ (≥ C₃ ≥ 1). The constants C₁₂,…,C₁₆ introduced in Steps 6–9 depend only on n, k (through the sibling constants; none depends on θ', ε' or δ). θ', ε', θ₀ := θ'/32 and δ₂ are fixed in Step 10, in this order; θ₀ and δ₂ are the constants asserted to exist.
Claim (the asserted statement): for 0 < δ ≤ δ₂ under the hypotheses, every ξ ∈ spt μ ∩ B_{r₁}(z) (r₁ := δρ), σ ∈ (0, r₁] and n-plane T admit an n-plane S with E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T). Fix such δ, data, ξ, σ and T; Steps 1–10 construct S.
1. Reduction (Simon (1)–(2)). All points used lie in B_{4r₁}(z) and all radii are ≤ 2σ ≤ (1 − 4δ)ρ, so density_bounds applies; κ ≥ 0 and κρ ≤ δ. affine_approximation at (ξ, 2σ) (ξ ∈ spt μ ∩ B_{2r₁}(z), 2σ ≤ 2r₁) gives an n-plane T̃ with E(ξ, σ, T̃) ≤ C₃δ^{2α} and dist(x − ξ, T̃) ≤ 2C₃δ^ασ for x ∈ spt μ ∩ B_{2σ}(ξ). If E(ξ, σ, T) > C₃δ^{2α} then E_*(ξ, σ, T̃) ≤ E_*(ξ, σ, T), and an S with E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T̃) also works for T; so we may assume E(ξ, σ, T) ≤ C₃δ^{2α}. Then |p_T − p_{T̃}|²μ(B_σ(ξ)) ≤ 2∫_{B_σ(ξ)}|p_x − p_T|² + 2∫_{B_σ(ξ)}|p_x − p_{T̃}|² ≤ 4C₃δ^{2α}σⁿ and μ(B_σ(ξ)) ≥ ½ω_nσⁿ (density_bounds (b)), so ‖p_T − p_{T̃}‖ ≤ (8C₃/ω_n)^{1/2}δ^α and
 (2') dist(x − ξ, T) ≤ dist(x − ξ, T̃) + ‖p_T − p_{T̃}‖|x − ξ| ≤ C₁₁δ^ασ for x ∈ spt μ ∩ B_σ(ξ).
 Let E₀ := E_*(ξ, σ, T). Since κσ ≤ κr₁ ≤ δ², δ^{−1}κ²σ² ≤ δ³ ≤ C₃δ^{2α}; so E₀ ≤ C₃δ^{2α} (δ ≤ 1, C₃ ≥ 1). If E₀ = 0 then E(ξ, σ, T) = 0 and κ = 0, and S := T works because E(ξ, θ₀σ, T) ≤ θ₀^{−n}E(ξ, σ, T) = 0. Assume E₀ > 0.
2. Lipschitz approximation (Simon (3)–(4)). Require δ^α ≤ β (Step 10). lipschitz_approximation at (ξ, σ₀ := σ, T₀ := T, L := 1, C₆ := C₁₁) — hypotheses (i) E(ξ, σ, T) ≤ C₃δ^{2α} ≤ C₁₁δ^{2α} and (ii) = (2') — gives linear isometries ι : ℝⁿ → E, ι' : ℝᵏ → E with ⟨ιv, ι'w⟩ = 0 and ι(ℝⁿ) ⊆ T (hence ι(ℝⁿ) = T, ι'(ℝᵏ) = T^⊥ by dimensions), and f : ℝⁿ → ℝᵏ with Lip f ≤ 1, |f| ≤ C₇δ^ασ, and with Φ_f(v) := ξ + ιv + ι'f(v), F := Φ_f(ℝⁿ):
 (4') μ(B_{σ/2}(ξ) ∖ F) + Hⁿ((F ∖ spt μ) ∩ B_{σ/4}(ξ)) ≤ C₇∫_{B_σ(ξ)}|p_x − p_T|²dμ ≤ C₇σⁿE₀.
 Coordinates: for x ∈ E write x − ξ = ιx' + ι'x'' with x' := ι*(x − ξ) ∈ ℝⁿ, x'' := ι'*(x − ξ) ∈ ℝᵏ; |x''| = dist(x − ξ, T); e_{n+j} := ι'(ε_j) (ε_j standard basis of ℝᵏ), fʲ := ⟨f, ε_j⟩, ∇fʲ its a.e. gradient (Rademacher), Df the a.e. derivative of f. Put r := σ/4 and R₀ := r/2 = σ/8. (Correction: Simon works on B_σ; since (4') controls F ∖ spt μ only on B_{σ/4}, the harmonic approximation is done on Bⁿ_{σ/8}.)
3. Height (Simon (5)). Require C₁₁δ^α ≤ 1/16 and C₇δ^α ≤ 1/16. Then x ∈ spt μ ∩ B_σ(ξ) with |x'| < r/2 has |x''| ≤ r/4, hence |x − ξ| < 3r/4; and |Φ_f(v) − ξ| ≤ |v| + |f(v)| < 3r/4 for |v| < r/2.
4. Equation for fʲ (Simon (6)–(9)). Fix j and ζ ∈ C¹_c(B̆_r(ξ)). X := ζe_{n+j} is C¹ with compact support in B_r(ξ) ⊆ B_ρ(z) ⊆ W and div_M X = ⟨p_xe_{n+j}, ∇ζ⟩ μ-a.e.; (MC) gives (6) ∫⟨p_xe_{n+j}, ∇ζ⟩dμ = −∫ζ⟨e_{n+j}, H⟩dμ. Let M₁ := M ∩ F. By graph_tangent (with a := ξ, L := 1; Hⁿ-a.e. on M ∩ W, hence μ-a.e. on W), for μ-a.e. x = Φ_f(v) ∈ M₁ ∩ B_r(ξ), f is differentiable at v and T_xM = {ιw + ι'Df(v)w}; for τ' = ιw + ι'Df(v)w ∈ T_xM, ⟨τ', e_{n+j}⟩ = ⟨Df(v)w, ε_j⟩ = ⟨w, ∇fʲ(v)⟩ = ⟨τ', ι∇fʲ(v)⟩, so (7) p_xe_{n+j} = p_x ι∇fʲ(v) =: ∇^Mf̃ʲ(x). Hence ∫_{M₁}⟨∇^Mf̃ʲ, ∇ζ⟩dμ = −∫_{M∖M₁}⟨p_xe_{n+j}, ∇ζ⟩dμ − ∫ζ⟨e_{n+j}, H⟩dμ. Write ‖g‖_μ := sup_{spt μ}|g| (only values on spt μ matter, as μ(E ∖ spt μ) = 0). Using μ(B_r(ξ) ∖ F) ≤ C₇σⁿE₀ (4'), μ(B_r(ξ)) ≤ 2ω_nrⁿ (density_bounds (a)), |H| ≤ κ, κr ≤ κσ ≤ (δE₀)^{1/2} (as δ^{−1}κ²σ² ≤ E₀) and σⁿ = 4ⁿrⁿ:
 (8') |r^{−n}∫_{M₁∩B_r(ξ)}⟨∇^Mf̃ʲ, ∇ζ⟩dμ| ≤ C(‖∇ζ‖_μE₀ + r^{−1}‖ζ‖_μδ^{1/2}E₀^{1/2}); in particular, since ‖ζ‖_μ ≤ sup|ζ| ≤ r sup|∇ζ|, it is ≤ C sup|∇ζ|(δ^{1/2}E₀^{1/2} + E₀).
 Also |∇^Mf̃ʲ| = |p_xe_{n+j}| = |(p_x − p_T)e_{n+j}| ≤ |p_x − p_T| (p_Te_{n+j} = 0), so (9') r^{−n}∫_{M₁∩B_r(ξ)}|∇^Mf̃ʲ|²dμ ≤ 4ⁿE(ξ, σ, T) ≤ 4ⁿE₀.
5. Tests independent of x'' (Simon (10)–(13)). Let ζ₀ ∈ C¹_c(B̆ⁿ_{r/2}), ζ̃₀(x) := ζ₀(x'), and h₀ ∈ C¹_c(B̆_r(ξ)) with h₀ ≡ 1 on B_{7r/8}(ξ); ζ := ζ̃₀h₀ ∈ C¹_c(B̆_r(ξ)). At x ∈ spt μ: if x ∈ B_σ(ξ) and |x'| < r/2 then x ∈ B̆_{3r/4}(ξ) (Step 3) and ζ = ζ̃₀ near x; if x ∈ B_σ(ξ) and |x'| ≥ r/2 then ζ̃₀ and ζ vanish near x (spt ζ₀ is a compact subset of B̆ⁿ_{r/2}); if x ∉ B_σ(ξ), ζ vanishes near x. Hence ∇ζ = ∇ζ̃₀ = ι∇ζ₀(x') and |ζ| = |ζ̃₀| at every point of spt μ ∩ B_σ(ξ) ⊇ spt μ ∩ B_r(ξ), while ζ = 0 on spt μ ∖ B_σ(ξ); so ‖∇ζ‖_μ ≤ sup|∇ζ₀| and ‖ζ‖_μ ≤ sup|ζ₀| ≤ (r/2)sup|∇ζ₀| (ζ₀ vanishes outside B̆ⁿ_{r/2}). By the first form of (8') applied to ζ, and as μ(E ∖ spt μ) = 0: |r^{−n}∫_{M₁∩B_r(ξ)}⟨∇^Mf̃ʲ, ∇ζ̃₀⟩dμ| ≤ C sup|∇ζ₀|(δ^{1/2}E₀^{1/2} + E₀). At μ-a.e. x ∈ M₁, with a := ι∇fʲ(x') and b := ι∇ζ₀(x') in T: ⟨∇^Mf̃ʲ, ∇ζ̃₀⟩ = ⟨p_xa, b⟩ = ⟨a, b⟩ − ⟨p_Tp_x^⊥p_Ta, b⟩, and p_Tp_x^⊥p_T = (p_T − p_x)p_x^⊥(p_T − p_x), so (11) |⟨∇^Mf̃ʲ, ∇ζ̃₀⟩ − ∇fʲ(x')·∇ζ₀(x')| ≤ |p_x − p_T|²|∇fʲ(x')||∇ζ₀(x')|. With |∇fʲ| ≤ 1 and E(ξ, σ, T) ≤ E₀: (12') |r^{−n}∫_{M₁∩B_r(ξ)}∇fʲ(x')·∇ζ₀(x')dμ| ≤ C sup|∇ζ₀|(δ^{1/2}E₀^{1/2} + E₀). Applying (11) with b := a and (9'): (13') r^{−n}∫_{M₁∩B_r(ξ)}|∇fʲ(x')|²dμ ≤ CE₀.
6. Transfer to ℝⁿ (Simon (14)–(16)). Let J_f(v) := (det(I + Df(v)ᵀDf(v)))^{1/2} ∈ [1, 2^{n/2}], so |J_f − 1| ≤ C|Df|², and θ_F(v) := θ(Φ_f(v)) if Φ_f(v) ∈ M, θ_F(v) := 0 otherwise. Since Φ_f is injective and Lipschitz, the area formula (Simon Ch. 2, 3.5; library injective_area_formula_lipschitz) and Step 3 give, for Borel g on ℝⁿ supported in B̆ⁿ_{r/2} and nonnegative or integrable: ∫_{M₁∩B_r(ξ)}g(x')dμ = ∫_{Bⁿ_{r/2}}g(v)θ_F(v)J_f(v)dv (x' = v for x = Φ_f(v)). Let Z₀ := {v ∈ B̆ⁿ_{r/2} : Φ_f(v) ∉ M} and Z₂ := {v ∈ B̆ⁿ_{r/2} : θ_F(v) ≥ 2}. Since |v − v'| ≤ |Φ_f(v) − Φ_f(v')|, Lⁿ(Z) ≤ Hⁿ(Φ_f(Z)); Φ_f(Z₀) ⊆ ((F ∖ spt μ) ∩ B_r(ξ)) ∪ ((spt μ ∩ W) ∖ M), so by (4') and support_null, Lⁿ(Z₀) ≤ C₇σⁿE₀ = C₇4ⁿrⁿE₀; Φ_f(Z₂) ⊆ {x ∈ M ∩ B_r(ξ) : θ(x) ≥ 2}, which is μ-null by density_bounds (d) and hence Hⁿ-null, so Lⁿ(Z₂) = 0. Off Z₀ ∪ Z₂, θ_F = 1. Hence from (12'), (13'):
 (16') r^{−n}∫_{Bⁿ_{r/2}}|∇fʲ|²dv ≤ CE₀,
 (15') |r^{−n}∫_{Bⁿ_{r/2}}∇fʲ·∇ζ₀dv| ≤ C sup|∇ζ₀|(δ^{1/2}E₀^{1/2} + E₀) ≤ C₁₂δ^αE₀^{1/2}sup|∇ζ₀|,
 using ∫_{Z₀}|∇fʲ||∇ζ₀| ≤ sup|∇ζ₀|Lⁿ(Z₀), |θ_FJ_f − 1| ≤ C|Df|² off Z₀ ∪ Z₂ together with (16') summed over j, E₀ ≤ (C₃δ^{2α})^{1/2}E₀^{1/2} and δ^{1/2} ≤ δ^α. (Correction: Simon's factor δ^{1/2}E₀^{1/2} in (15) becomes δ^{1/(2n+2)}E₀^{1/2}, which suffices.)
7. Harmonic approximation (Simon (17)). By (16') choose C₁₃ with R₀^{−n}∫_{Bⁿ_{R₀}}|∇fʲ|² ≤ C₁₃E₀ for all j. Then w := (C₁₃E₀)^{−1/2}fʲ is Lipschitz, satisfies ∫_{B̆ⁿ_{R₀}}|∇w|² ≤ R₀ⁿ and, by (15') with r = 2R₀, |∫_{B̆ⁿ_{R₀}}∇w·∇ζ₀| ≤ C₁₄δ^αR₀ⁿ G for ζ₀ ∈ C¹_c with tsupport in B̆ⁿ_{R₀} and |∇ζ₀| ≤ G, where C₁₄ := 2ⁿC₁₂C₁₃^{−1/2}. Require C₁₄δ^α ≤ δ_h(n, ε') (Step 10). harmonic_approximation gives a_j ∈ ℝ and a linear b_j : ℝⁿ → ℝ with ‖b_j‖ ≤ C_H, |a_j| ≤ C_H(R₀^{−n}∫_{B̆ⁿ_{R₀}}w²)^{1/2} + C_H√ε'R₀, and ∫_{B̆ⁿ_{θ'R₀}}(w − a_j − b_j)² ≤ C_H(ε'θ'^{−n−2} + θ'²)(θ'R₀)^{n+2} for θ' ∈ (0, 1/4]. Let λ := (λ¹,…,λᵏ), λʲ(v) := (C₁₃E₀)^{1/2}(a_j + b_j(v)), u(0) := λ(0), Du(0) := Dλ (in the parent's notation λ(v) = u(0) + Du(0)v).
8. Affine approximation of f (Simon (18)–(19)). From 7: |Du(0)| ≤ CE₀^{1/2}; since |f| ≤ C₇δ^ασ = 8C₇δ^αR₀ and E₀ ≤ C₃δ^{2α}, ε' ≤ 1: (18') |u(0)| ≤ C₁₅R₀δ^α; and for θ' ∈ (0, 1/4] (summing over j): (19') (θ'R₀)^{−n−2}∫_{Bⁿ_{θ'R₀}}|f − λ|²dv ≤ C(θ'^{−n−2}ε' + θ'²)E₀.
9. The new plane (Simon (20)–(22)). Let S := {ιw + ι'Du(0)w : w ∈ ℝⁿ} (an n-plane) and τ := ξ + ι'u(0). Require C₁₅δ^α ≤ θ'/4; then |τ − ξ| ≤ θ'R₀/4 and B_{θ'R₀}(τ) ⊆ B_{σ/2}(ξ). For x = Φ_f(v) with |v| ≤ θ'R₀, dist(x − τ, S) ≤ |f(v) − λ(v)|, and F ∩ B_{θ'R₀}(τ) ⊆ Φ_f(Bⁿ_{θ'R₀}) (|v| = |x' − τ'| ≤ |x − τ|, τ' = 0). Split ∫_{B_{θ'R₀}(τ)}dist(x − τ, S)²dμ into the parts on F and off F. On F, μ⌞F ≤ Hⁿ⌞F on B_{4r₁}(z) (θ = 1 μ-a.e. there by density_bounds (d), μ = θHⁿ⌞M), and the area formula with J_f ≤ 2^{n/2} bounds it by 2^{n/2}∫_{Bⁿ_{θ'R₀}}|f − λ|². Off F, each x ∈ spt μ ∩ B_{θ'R₀}(τ) has dist(x − τ, S) ≤ |x''| + |u(0)| + |Du(0)||x'| ≤ Cδ^ασ by (2'), (18') and E₀^{1/2} ≤ Cδ^α, and μ(B_{θ'R₀}(τ) ∖ F) ≤ C₇σⁿE₀ by (4'). With σ = 8R₀: (θ'R₀)^{−n−2}∫_{B_{θ'R₀}(τ)}dist(x − τ, S)²dμ ≤ C(θ'^{−n−2}ε' + θ'^{−n−2}δ^{2α} + θ'²)E₀. (Correction: Simon's middle term omits θ'^{−n−2}; harmless as θ' is fixed before δ.) tilt_height at (τ, θ'R₀) (B_{θ'R₀}(τ) ⊆ W, μ(B_{θ'R₀}(τ)) ≤ 2ω_n(θ'R₀)ⁿ by density_bounds (a), κ²(θ'R₀)² ≤ κ²σ² ≤ δE₀) gives (20') E(τ, θ'R₀/2, S) ≤ C(θ'^{−n−2}(ε' + δ^{2α}) + θ'² + δ)E₀, and since B_{θ'R₀/4}(ξ) ⊆ B_{θ'R₀/2}(τ) (21'), (22') E(ξ, θ'R₀/4, S) ≤ 2ⁿE(τ, θ'R₀/2, S) ≤ C₁₆(θ'^{−n−2}(ε' + δ^{2α}) + θ'² + δ)E₀.
10. Choice of constants (Simon (23)). θ₀ := θ'R₀/(4σ) = θ'/32. Choose θ' ∈ (0, 1/4] with C₁₆θ'² ≤ θ'/128, then ε' ∈ (0, 1] with C₁₆θ'^{−n−2}ε' ≤ θ'/128, then δ₂ ∈ (0, min{δ₁, δ₃, δ₅}] so small that for δ ≤ δ₂: δ^α ≤ β, C₁₁δ^α ≤ 1/16, C₇δ^α ≤ 1/16, C₁₄δ^α ≤ δ_h(n, ε'), C₁₅δ^α ≤ θ'/4, C₁₆θ'^{−n−2}δ^{2α} ≤ θ'/128, C₁₆δ ≤ θ'/128. Then E(ξ, θ₀σ, S) ≤ (θ'/32)E₀ = θ₀E₀ and δ^{−1}κ²(θ₀σ)² = θ₀²δ^{−1}κ²σ² ≤ θ₀E₀, so E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T). This proves the Claim; θ₀ ∈ (0, 1/4] and δ₂ ≤ 1/8 depend only on n, k.
11. Lean form. For every 0 < r ≤ r₁ and n-plane S', B_r(ξ) ⊆ B_ρ(z) ⊆ W is compact, so μ(B_r(ξ)) < ∞ (P2), and |p_x − p_{S'}|² ≤ 4n everywhere; hence E_*(ξ, r, S') = max{ofReal(r^{−n})·∫⁻_{B_r(ξ)} ofReal(|p_x − p_{S'}|²)dμ, ofReal(κ²r²/δ)} is a finite element of [0, ∞) whose two entries are E(ξ, r, S') and δ^{−1}κ²r². With r := θ₀σ, S' := S on the left and r := σ, S' := T on the right, the inequality of Step 10 is exactly the asserted ENNReal inequality max(ofReal(1/(θ₀σ)ⁿ)·∫⁻_{B_{θ₀σ}(ξ)}…, ofReal(κ²(θ₀σ)²/δ)) ≤ ofReal(θ₀)·max(ofReal(1/σⁿ)·∫⁻_{B_σ(ξ)}…, ofReal(κ²σ²/δ)) (ofReal is monotone and multiplicative on [0, ∞)). In the case E₀ = 0 of Step 1, let T' denote the plane after the reduction of Step 1 (T' = T̃ if the reduction was applied, T' = T otherwise); then S := T' satisfies E_*(ξ, θ₀σ, S) = 0 ≤ θ₀E_*(ξ, σ, T') ≤ θ₀E_*(ξ, σ, T), which is again the asserted inequality. Since θ₀ ∈ (0, 1/4] and δ₂ ∈ (0, 1/8] depend only on n and k, the statement is proved. ∎

## Key steps

1. Reduce to E(ξ, σ, T) ≤ C₃δ^{2α} using affine_approximation, which also gives the height bound (2'); handle E₀ = 0.
2. Apply lipschitz_approximation with L = 1, giving ι, ι', f and (4').
3. Test the first variation identity with ζe_{n+j}; graph_tangent identifies p_xe_{n+j} on M ∩ F, giving (8')–(13').
4. Transfer to ℝⁿ by the area formula, with Z₀ controlled by support_null and (4'), and Z₂ null by density_bounds (d); this gives (15') and (16').
5. Apply harmonic_approximation to (C₁₃E₀)^{−1/2}fʲ on Bⁿ_{σ/8} to get an affine λ with (18') and (19').
6. Take the new plane S = graph Du(0); tilt_height at (τ, θ'R₀) gives (20')–(22').
7. Choose θ', then ε', then δ₂: E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T) with θ₀ = θ'/32, which is the asserted ENNReal inequality.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n -i 'allard|tilt.?excess|harmonic.?approx|lipschitz.?approx' local-references/123e8435b4a2469b/project/GMT`
- `grep -n 'sorry|^theorem|^lemma|structure RectifiableVarifold|^import' local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `rg -l -i 'rellich|kondrachov|weyl.s lemma' local-references/123e8435b4a2469b/mathlib/Mathlib (exit 1, no match)`
- `rg -n 'theorem ae_tendsto_average_norm_sub|theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem ae_differentiableAt|theorem extend_real|theorem norm_fderiv_le_of_lipschitz' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'dorag_|codim1_ldr' local-references/123e8435b4a2469b/project/GMT (no match)`
- `rg -l -i allard simongmt/Poincare/SimonGMT; sed -n 1,40p simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `python3 -I scans of dag.json (08:30Z–09:01Z): the selected node; dor_allard_bounded_curvature_graph and its 12 children (status, candidate_commit, frozen lean_statement, depends_on) and their subtrees; DAG owners of all 12 proposed lean_names; children of the parent low_density_regular`
- `diff nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-supplied-natural-proof.md nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dc03e60a0d/parent-supplied-natural-proof.md`
- `python3 -I: compare decomposition-v3.json subproblems with each child's parent-child-handoff.json and the dag.json frozen types; read decomposition-audit-v1..v3.json and the parent's decomposition-v2.json and decomposition-audit-v2.json`
- `git show fa8a43ae (speculative assembly of dor_allard_bounded_curvature_graph); git show 67cb4097 ea6fb1e8 0794dd28 (speculative drafts of the 3 originals); git show <candidate>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name> ' for the 9 reused candidates; isolated-comparator-result.json and comparator-v1.log of each reused node`
- `lean -DautoImplicit=false /tmp/ag-ldr-check/Types.lean; lean -DautoImplicit=false /tmp/ag-ldr-check/Assembly.lean (LEAN_PATH from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `grep -c codim1_ldr_ag in the dag.json of all 8 chapter runs; grep -rl codim1_ldr_ag GMT simongmt/Poincare local-references/123e8435b4a2469b/project nodes; git for-each-ref refs/heads refs/remotes (1434 distinct commits) | xargs git grep -l codim1_ldr_ag -- 'GMT/*.lean' (no match)`
- `runtime.py: _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _reference_use_problem, speculative promotion; store.py ensure; swarm config 9c96ace3 (max_children, max_depth, max_nodes)`
- `python3 -I /tmp/ag-ldr-check/cmp.py on the transcribed subproblems (byte-identical to final_subproblems.json)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dc03e60a0d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-dc03e60a0d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-low-b06ad0f914/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-34fbedec8b/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-5e610a0036/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-bca0eeb76e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-8c018a8a8b/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b5982cc9c1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-498c875e36/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9e10fe2792/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db45a55178/isolated-comparator-result.json`
- `/runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9c96ace382df405680ef2a8c9a521a87.json`
- `/tmp/ag-ldr-check/Types.lean`
- `/tmp/ag-ldr-check/Types.log`
- `/tmp/ag-ldr-check/Assembly.lean`
- `/tmp/ag-ldr-check/Assembly.log`
- `/tmp/ag-ldr-check/reuse-evidence.json`
- `/tmp/ag-ldr-check/final_subproblems.json`
- `/tmp/ag-ldr-check/cmp.py`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. simongmt 2b366308 equals the snapshot lake-manifest pin. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter05/Basic.lean leaves Lipschitz approximation, excess decay and Allard regularity unformalized.
- The snapshot GMT/Ch05/Submission.lean only states analogues, for its own RectifiableVarifold, behind a sorry-backed main_theorem.
- The snapshot Mathlib has no Rellich, Kondrachov or Weyl lemma (rg exit 1). It does have the tools the children cite: ae_tendsto_average_norm_sub, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, norm_fderiv_le_of_lipschitz and Rademacher.
- No dorag_ or codim1_ldr declaration exists in the snapshot project.
So the analytic lemmas remain genuine children.
DAG. The selected type equals that of dor_allard_bounded_curvature_graph, whose audited 12-child v3 decomposition is reused.
- 9 children are accepted, with candidate commits, identical frozen types and passing isolated comparators; they are reused by name.
- 3 children are not accepted; they are mirrored under fresh codim1_ldr_ag_ names with no collisions.
Lean. All 12 child types and the selected type elaborate after import GMT.Ch07.Submission. The assembly proves the selected type from the 5 directly used child types, with axioms propext, Classical.choice and Quot.sound only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
