<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1 -->

## Theorem `Submission.dorag_tes_graph_first_variation_estimate`

Let n ≥ 1, k ≥ 0, U ⊆ ℝ^{n+k} any set, W ⊆ U open, R = (M, θ, ξ_R) an integer multiplicity triple in U (IMRep U n) with μ := R.measure = θHⁿ⌞M (Hⁿ = μHE[n]), κ ∈ ℝ and H : ℝ^{n+k} → ℝ^{n+k} μ-a.e. strongly measurable with |H(x)| ≤ κ for all x. Assume R.firstVariation X = −∫⟨X, H⟩dμ for every C¹ compactly supported X : ℝ^{n+k} → ℝ^{n+k} with tsupport X ⊆ W, and that x ↦ p_x is μ-a.e. strongly measurable, where p_x is the orthogonal projection onto T_xM := approxTangentPlane n M x. Let ξ ∈ ℝ^{n+k} and r > 0 with B_r(ξ) ⊆ W (closed ball), T an n-dimensional subspace, ι : ℝⁿ → ℝ^{n+k} and ι' : ℝᵏ → ℝ^{n+k} linear isometries with ⟨ιv, ι'w⟩ = 0 and ιv ∈ T for all v, w, P : ℝ^{n+k} → ℝⁿ continuous linear with P(ιv) = v and P(ι'w) = 0 for all v, w, and f : ℝⁿ → ℝᵏ with |f(v) − f(w)| ≤ |v − w| and |f(v)| ≤ r/4 for all v, w. Assume (height) |(x − ξ) − p_T(x − ξ)| ≤ r/4 for every x ∈ spt μ ∩ B_r(ξ), and (tangent identification) for μ-a.e. x ∈ B_r(ξ) and every v ∈ ℝⁿ with x = ξ + ιv + ι'f(v): f is differentiable at v and T_xM = LinearMap.range(ι + ι'∘Df(v)) = {ιw + ι'Df(v)w : w ∈ ℝⁿ}. Put Φ(v) := ξ + ιv + ι'f(v), F := Φ(ℝⁿ), D := B̆ⁿ_{r/2}(0) (open ball of ℝⁿ), fʲ := EuclideanSpace.proj j ∘ f, ∂_ig(v) := Dg(v)e_i (Dg = fderiv ℝ g, e_i = EuclideanSpace.single i 1), tilt_T(x) := Σ_i|p_xe_i − p_Te_i|². Then: (i) for every j ∈ Fin k: ∫_{Φ(D)} ‖Dfʲ(P(x − ξ))‖² dμ ≤ 2∫_{B_r(ξ)} tilt_T dμ (lower integrals of ENNReal.ofReal); (ii) for every j ∈ Fin k, every C¹ function ζ : ℝⁿ → ℝ with compact support and tsupport ζ ⊆ D, and every G ∈ ℝ with ‖Dζ(v)‖ ≤ G for all v: ofReal|∫_{Φ(D)} Σ_{i=1}^{n} ∂_ifʲ(P(x − ξ))∂_iζ(P(x − ξ)) dμ| ≤ ofReal(G)·(∫_{B_r(ξ)} tilt_T dμ + μ(B_r(ξ) ∖ F) + ofReal(κr/2)·μ(B_r(ξ))), where the left integral is a Bochner integral and the integral of tilt_T is the lower integral of ENNReal.ofReal(tilt_T).

Node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2043

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2886

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3589, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3594, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3601, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3608, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3613, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3619

## Lean problem

Declaration: `Submission.dorag_tes_graph_first_variation_estimate`

```lean
∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r : ℝ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖(x - ξ) - T.starProjection (x - ξ)‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → ∀ v : Euclid n, x = ξ + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ j : Fin k, ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2) ∂R.measure ≤ 2 * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) ∧ ∀ (j : Fin k) (ζ : Euclid n → ℝ) (G : ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ENNReal.ofReal |∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) ∂R.measure| ≤ ENNReal.ofReal G * (∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure + R.measure (closedBall ξ r \ range (fun v => ξ + ι v + ι' (f v))) + ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r))
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

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 3–5 (Simon Ch. 5, proof of 4.5, (5)–(13)): the first variation identity tested with ζe_{n+j}, the graph identity (7) for p_xe_{n+j}, estimates (8′), (9′), (11), (12′), (13′). It is stated here for one component j and with the domain Φ(D), D = B̆ⁿ_{r/2}. Notation: φ(x) := P(x − ξ); for g : ℝⁿ → ℝ differentiable at v, ∇g(v) ∈ ℝⁿ is its gradient (Dg(v)u = ⟨∇g(v), u⟩), so ‖Dg(v)‖ = |∇g(v)| and ∂_ig(v) = ⟨∇g(v), e_i⟩.
Step 0 (frame).
0.1 ι is injective (an isometry), so dim range ι = n = dim T. Since range ι ⊆ T, range ι = T.
0.2 V₁ := range ι and V₂ := range ι' are orthogonal, with dim V₁ = n and dim V₂ = k. Hence V₁ ∩ V₂ = 0 and dim(V₁ + V₂) = n + k, so V₁ + V₂ = ℝ^{n+k}. Since V₂ ⊆ V₁^⊥ and dim V₁^⊥ = k, V₂ = V₁^⊥ = T^⊥.
0.3 Every y ∈ ℝ^{n+k} is y = ιu + ι'w (0.2). Then Py = u, and ⟨ι^*y, u'⟩ = ⟨y, ιu'⟩ = ⟨u, u'⟩ for all u', so P = ι^* (the adjoint of ι). Consequently p_Ty = ιPy, |y|² = |Py|² + |y − p_Ty|², |Py| ≤ |y|, and for g differentiable at v: Dg(v)(Py) = ⟨∇g(v), ι^*y⟩ = ⟨ι∇g(v), y⟩.
0.4 φ(Φ(v)) = P(ιv + ι'f(v)) = v and |Φ(v) − ξ|² = |v|² + |f(v)|². For v ∈ D, |Φ(v) − ξ|² < r²/4 + r²/16 < r², so Φ(D) ⊆ B̆_r(ξ) ⊆ B_r(ξ) ⊆ W. Moreover Φ(D) = {x : x = Φ(φ(x)), φ(x) ∈ D} and F = {x : x = Φ(φ(x))} are Borel sets (Φ, φ continuous; D open).
0.5 B_r(ξ) is compact and contained in W ⊆ U, so μ(B_r(ξ)) = ∫_{M∩B_r(ξ)}θ dHⁿ < ∞ (IMRep.locallyIntegrable_mult). Also μ(ℝ^{n+k} ∖ spt μ) = 0 (complement of the support is null), and tilt_T ≤ 4(n + k) because each |p_xe_i − p_Te_i| ≤ 2.
0.6 Fix j ∈ Fin k. Let ε_j := EuclideanSpace.single j 1 ∈ ℝᵏ and e := ι'ε_j. Then |e| = 1 and e ∈ T^⊥ (0.2). fʲ is 1-Lipschitz (proj_j has norm ≤ 1), so ‖Dfʲ(v)‖ ≤ 1 for every v (norm_fderiv_le_of_lipschitz; Dfʲ(v) = 0 where fʲ is not differentiable).
Step 1 (graph identity (7)). Let N₀ be a μ-null set off which the tangent identification holds. Let x ∈ Φ(D) ∖ N₀ and v := φ(x), so x = Φ(v) (0.4) and x ∈ B_r(ξ). Then f is differentiable at v and T_xM = {ιw + ι'Df(v)w : w ∈ ℝⁿ}. By the chain rule Dfʲ(v) = proj_j ∘ Df(v). Put a(x) := ι∇fʲ(v) ∈ T. For w ∈ ℝⁿ, using the isometries and ⟨ιu, ι'u'⟩ = 0: ⟨ιw + ι'Df(v)w, e⟩ = ⟨Df(v)w, ε_j⟩ = Dfʲ(v)w = ⟨∇fʲ(v), w⟩ = ⟨ιw + ι'Df(v)w, a(x)⟩. Thus e − a(x) ⊥ T_xM, so (1.1) p_xe = p_xa(x). Moreover |a(x)| = |∇fʲ(v)| = ‖Dfʲ(v)‖ ≤ 1.
Step 2 (proof of (i)). Let x ∈ Φ(D) ∖ N₀ and a := a(x). By sibling proj_algebra (Submission.dorag_tes_projection_algebra), part (c), with Q := T_xM and b := a ∈ T: |a|² − ⟨p_xa, a⟩ ≤ tilt_T(x)|a|² ≤ tilt_T(x). Also ⟨p_xa, a⟩ = |p_xa|² (p_x is a self-adjoint idempotent), and |p_xa|² = |p_xe|² ≤ tilt_T(x)|e|² = tilt_T(x) by (1.1) and proj_algebra (d) (e ∈ T^⊥). Hence ‖Dfʲ(φ(x))‖² = |a|² ≤ 2tilt_T(x) for μ-a.e. x ∈ Φ(D). Integrating over Φ(D) ⊆ B_r(ξ) (monotonicity of lower integrals in the integrand a.e. and in the domain; ofReal(2t) = 2ofReal(t)) gives ∫⁻_{Φ(D)} ofReal(‖Dfʲ(φ(x))‖²) dμ ≤ 2∫⁻_{Φ(D)} ofReal(tilt_T) dμ ≤ 2∫⁻_{B_r(ξ)} ofReal(tilt_T) dμ.
Step 3 (the test field). Let ζ and G be as in (ii); then G ≥ ‖Dζ(0)‖ ≥ 0.
3.1 sup|ζ| ≤ Gr/2. ζ is G-Lipschitz by the mean value inequality on the convex space ℝⁿ. If |v| ≥ r/2 then v ∉ D ⊇ tsupport ζ, so ζ(v) = 0. If |v| < r/2, choose a unit vector u (u := v/|v| if v ≠ 0; any unit vector if v = 0, which exists since n ≥ 1) and put w := v + (r/2 − |v|)u. Then |w| = r/2, so ζ(w) = 0, and |ζ(v)| = |ζ(v) − ζ(w)| ≤ G|v − w| = G(r/2 − |v|) ≤ Gr/2.
3.2 Let h₀ : ℝ^{n+k} → [0, 1] be a C^∞ bump with h₀ = 1 on B_{7r/8}(ξ) and support h₀ = B̆_r(ξ) (Mathlib ContDiffBump centred at ξ with rIn = 7r/8 < rOut = r; tsupport h₀ = B_r(ξ)). Put ζ̃(x) := ζ(φ(x))h₀(x) and X(x) := ζ̃(x)e. Since φ is affine and ζ is C¹, X is C¹. Its support lies in B̆_r(ξ), which is bounded, so HasCompactSupport X and tsupport X ⊆ B_r(ξ) ⊆ W.
3.3 Local form on spt μ. Let x ∈ spt μ ∩ B_r(ξ). If |φ(x)| < r/2, then by the height hypothesis and 0.3, |x − ξ|² = |φ(x)|² + |(x − ξ) − p_T(x − ξ)|² < r²/4 + r²/16, so |x − ξ| < (√5/4)r < 7r/8. Hence h₀ = 1 on the open neighbourhood B̆_{7r/8}(ξ) of x, and ζ̃ = ζ∘φ near x. If |φ(x)| ≥ r/2, then φ(x) ∉ tsupport ζ, so ζ vanishes on an open neighbourhood O of φ(x), and ζ̃ = 0 = ζ∘φ on the neighbourhood φ⁻¹(O) of x. In both cases ζ̃ = ζ∘φ near x, so (3.3a) Dζ̃(x) = Dζ(φ(x))∘P and ζ̃(x) = ζ(φ(x)); and if |φ(x)| ≥ r/2 then Dζ̃(x) = 0. For x ∉ B_r(ξ), ζ̃ vanishes on the open set ℝ^{n+k} ∖ B_r(ξ), so ζ̃(x) = 0 and Dζ̃(x) = 0.
3.4 For x ∈ ℝ^{n+k} put b(x) := ι∇ζ(φ(x)) ∈ T. Then |b(x)| = ‖Dζ(φ(x))‖ ≤ G, and by (3.3a) and 0.3, for x ∈ spt μ ∩ B_r(ξ) and y ∈ ℝ^{n+k}: Dζ̃(x)y = Dζ(φ(x))(Py) = ⟨b(x), y⟩.
Step 4 (first variation identity (6)).
4.1 DX(x)y = (Dζ̃(x)y)e, i.e. DX(x) = (Dζ̃(x)).smulRight e. So p_x∘DX(x) = (Dζ̃(x)).smulRight(p_xe), whose trace is Dζ̃(x)(p_xe) (LinearMap.trace_smulRight). Hence tangentialDivergence n M X x = Dζ̃(x)(p_xe) for every x.
4.2 R.firstVariation X = ∫_M θ·div_M X dHⁿ by definition. Since μ is Hⁿ⌞M with the measurable, finite density θ, ∫ g dμ = ∫_M θg dHⁿ for every g (integral_withDensity_eq_integral_toReal_smul applied to μHE[n].restrict M), so R.firstVariation X = ∫ Dζ̃(x)(p_xe) dμ(x). This integrand is μ-a.e. strongly measurable (x ↦ p_x is, and Dζ̃ is continuous) and bounded by sup‖Dζ̃‖ < ∞. It vanishes outside B_r(ξ), which has finite measure (0.5), so it is μ-integrable. Likewise ⟨X(x), H(x)⟩ = ζ̃(x)⟨e, H(x)⟩ is integrable and |ζ̃(x)⟨e, H(x)⟩| ≤ (Gr/2)κ·1_{B_r(ξ)}(x), by 3.1, 0 ≤ h₀ ≤ 1, |e| = 1 and |H| ≤ κ.
4.3 The first-variation hypothesis applies to X (3.2), so ∫ Dζ̃(x)(p_xe) dμ = −∫ ζ̃(x)⟨e, H(x)⟩ dμ. Since both integrands vanish off B_r(ξ): |∫_{B_r(ξ)} Dζ̃(x)(p_xe) dμ| ≤ (Gr/2)κμ(B_r(ξ)).
Step 5 (splitting).
5.1 B_r(ξ) is the disjoint union of Φ(D) and B_r(ξ) ∖ Φ(D) (0.4). For μ-a.e. x ∈ B_r(ξ), namely for x ∈ spt μ ∩ B_r(ξ), 3.4 gives Dζ̃(x)(p_xe) = ⟨b(x), p_xe⟩.
5.2 Off the graph part. Let x ∈ spt μ ∩ (B_r(ξ) ∖ Φ(D)). If x ∈ F, then x = Φ(v) with v = φ(x) ∉ D, so |φ(x)| ≥ r/2 and Dζ̃(x) = 0 by 3.3. If x ∉ F, then |Dζ̃(x)(p_xe)| = |⟨b(x), p_xe⟩| ≤ G·|e| = G. Hence |∫_{B_r(ξ)∖Φ(D)} Dζ̃(x)(p_xe) dμ| ≤ Gμ(B_r(ξ) ∖ F).
5.3 On the graph part. Let g_j(x) := Σ_i ∂_ifʲ(φ(x))∂_iζ(φ(x)), the integrand in (ii). It is Borel (measurable_fderiv) and |g_j| ≤ ‖Dfʲ(φ(x))‖‖Dζ(φ(x))‖ ≤ G by Cauchy–Schwarz in ℝⁿ. For x ∈ Φ(D) ∖ N₀, with v = φ(x) and a = a(x) from Step 1: ⟨a, b(x)⟩ = ⟨∇fʲ(v), ∇ζ(v)⟩ = Σ_i⟨∇fʲ(v), e_i⟩⟨∇ζ(v), e_i⟩ = g_j(x). Also ⟨b(x), p_xe⟩ = ⟨p_xa, b(x)⟩ by (1.1), and by proj_algebra (c) (Q := T_xM; a, b(x) ∈ T): |⟨p_xa, b(x)⟩ − ⟨a, b(x)⟩| ≤ tilt_T(x)|a||b(x)| ≤ G·tilt_T(x).
5.4 All integrands in 5.1–5.3 are bounded, μ-a.e. strongly measurable and vanish off B_r(ξ), so they are μ-integrable. Hence ∫_{Φ(D)} g_j dμ = ∫_{B_r(ξ)} Dζ̃(p_xe) dμ − ∫_{B_r(ξ)∖Φ(D)} Dζ̃(p_xe) dμ − ∫_{Φ(D)} (⟨p_xa, b⟩ − ⟨a, b⟩) dμ. By 4.3, 5.2 and 5.3: |∫_{Φ(D)} g_j dμ| ≤ (Gr/2)κμ(B_r(ξ)) + Gμ(B_r(ξ) ∖ F) + G∫_{Φ(D)} tilt_T dμ ≤ G(∫_{B_r(ξ)} tilt_T dμ + μ(B_r(ξ) ∖ F) + (κr/2)μ(B_r(ξ))).
Step 6 (Lean form). μ(B_r(ξ)) < ∞ and 0 ≤ tilt_T ≤ 4(n + k), so the Bochner integral ∫_{B_r(ξ)} tilt_T dμ equals the real value of the finite lower integral ∫⁻_{B_r(ξ)} ofReal(tilt_T) dμ. All three terms in the bracket of 5.4 are finite and nonnegative, and G ≥ 0, κ ≥ |H(0)| ≥ 0 and r > 0. Apply ENNReal.ofReal to 5.4, using that it is monotone and additive and multiplicative on [0, ∞). This gives ofReal|∫_{Φ(D)} g_j dμ| ≤ ofReal(G)·(∫⁻_{B_r(ξ)} ofReal(tilt_T) dμ + μ(B_r(ξ) ∖ F) + ofReal(κr/2)·μ(B_r(ξ))), which is (ii). (i) was proved in Step 2. ∎

## Key steps

1. Frame: range ι = T, ℝ^{n+k} = range ι ⊕ range ι', P = ι^*, Φ(D) ⊆ B̆_r(ξ), μ(B_r(ξ)) < ∞.
2. Graph identity: for μ-a.e. x = Φ(v) ∈ Φ(D), T_xM = graph(Df(v)) gives p_x(ι'ε_j) = p_x(ι∇fʲ(v)).
3. (i): proj_algebra (c),(d) give |∇fʲ|² ≤ |p_xe|² + tilt_T ≤ 2tilt_T μ-a.e. on Φ(D); integrate.
4. (ii): test the first variation with X = ζ(P(x − ξ))h₀(x)ι'ε_j (h₀ a bump equal to 1 on B_{7r/8}(ξ)). Its divergence is Dζ̃(p_xe), and the height bound gives Dζ̃(x) = Dζ(φ(x))∘P on spt μ ∩ B_r(ξ).
5. Split B_r(ξ) into Φ(D) and its complement. Off Φ(D) the integrand is ≤ G and vanishes on F. On Φ(D), proj_algebra (c) replaces ⟨p_xa, b⟩ by ⟨a, b⟩ = Σ_i∂_ifʲ∂_iζ up to G·tilt_T. The mean-curvature term is ≤ (Gr/2)κμ(B_r).
6. Convert the real bound to the ENNReal form.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'tilt|harmonic approx|lipschitz approx|weakly harmonic|graph.*transfer|area formula' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT --glob '*.lean'`
- `rg -l -i 'weakly harmonic|rellich|harmonic approximation|tilt.excess' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory  (no match)`
- `rg -n --fixed-strings over /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for: lemma fderiv_const_smul_field; theorem addHaar_ball_of_pos; theorem norm_setIntegral_le_of_norm_le_const; theorem pow_rpow_inv_natCast; theorem withDensity_absolutelyContinuous; theorem ae_restrict_iff'; theorem toDual_symm_apply; theorem EuclideanSpace.inner_single_right; theorem measurable_fderiv_apply_const; lemma IntegrableOn.of_bound; theorem integral_finsetSum; theorem norm_fderiv_le_of_lipschitz; theorem integral_eq_lintegral_of_nonneg_ae; theorem toReal_le_of_le_ofReal; theorem lintegral_mono_set; theorem adjoint_inner_left`
- `lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on /tmp/tes-v2/chk/AreaChk.lean: #check/#print axioms Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn and areaJacobianAt_sq_eq_det_adjoint_comp`
- `git log --all -G '^import Poincare.SimonGMT' -- GMT/Ch07/Submission.lean; git show 77fcc7d -- GMT/Ch07/Submission.lean | grep '^+import'`
- `python3 -I: lean_name scan for dorag_tes_* over every workspace runs/*/dag.json and this run's nodes/; frozen sibling lean_statement comparison dag.json vs nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json; lean_contract.validate_lean_statement on the 8 v2 types`
- `lean on /tmp/tes-v2/lean/Integrals.lean (integral-scope dump) and /tmp/tes-v2/lean/Challenge_<key>.lean (8 comparator-format modules)`
- `lean on /tmp/tes-v2/asm/GWH.lean and /tmp/tes-v2/asm/Final.lean with #print axioms Asm.C_graph_weak_harmonic and #print axioms Asm.parent`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-af4665598c/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v3.json`
- `/tmp/tes-v2/lean/Integrals.lean`
- `/tmp/tes-v2/asm/GWH.lean`
- `/tmp/tes-v2/asm/Final.lean`
- `/tmp/tes-v2-review/Parens.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so every child type was checked in the correct compiler context.

Nothing in the snapshot proves the selected theorem or any child:
- GMT/Ch05 has only unproved Prop definitions for a different varifold type (TiltExcessHeightEstimate, LipschitzApproximationLemma, HarmonicApproximationLemma, TiltExcessDecayTheorem, …), used only in main_theorem := by sorry.
- GMT/Ch02 states the area formula as a contract.
- The weakly-harmonic/Rellich/tilt-excess search over Mathlib Analysis and MeasureTheory found no match.
So the split stands, and no identical comparator-approved declaration exists to reuse.

Usable infrastructure:
- The pinned SimonGMT area formula, weighted_area_formula_lipschitz_injOn, with only standard axioms.
- The Mathlib lemmas the v2 assembly uses, all present at the cited paths: fderiv_const_smul_field, Measure.addHaar_ball_of_pos, norm_setIntegral_le_of_norm_le_const, Real.pow_rpow_inv_natCast, withDensity_absolutelyContinuous, ae_restrict_iff', InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right, measurable_fderiv_apply_const, IntegrableOn.of_bound, integral_finsetSum.

Lean results:
- All 8 v2 child types elaborate in comparator scope, and their integral scopes are as intended.
- graph_weak_harmonic is proved from the corrected graph_transfer and graph_variation.
- The exact frozen parent type is proved from the 8 frozen sibling types and the v2 child types. Axioms: propext, Classical.choice, Quot.sound and the assumed contracts only; no sorryAx.

No dorag_tes_* name is reserved in any DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
