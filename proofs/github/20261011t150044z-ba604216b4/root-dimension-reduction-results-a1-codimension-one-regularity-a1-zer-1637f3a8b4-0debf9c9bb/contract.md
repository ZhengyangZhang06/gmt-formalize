<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1 -->

## Theorem `Submission.codim1_zsl_flat_graph_limit`

Let n, k ∈ ℕ, P := n + 1 + k, linear isometries ι : ℝ^{n+1} → ℝ^P and ι' : ℝ^k → ℝ^P with ⟨ιv, ι'w⟩ = 0 for all v, w and such that every y ∈ ℝ^P equals ιv + ι'w for some v, w; ξ_A ∈ Λ_{n+1}(ℝ^P) with ξ_A(α) = α(ιe_0, …, ιe_n) for every (n+1)-covector α (e_j = EuclideanSpace.single j 1); b ∈ ℝ^k; sets U_i ⊆ ℝ^P, currents S_i ∈ 𝒟_n(U_i) and S ∈ 𝒟_n(ℝ^P) with S_i ⇀ S in ℝ^P (ConvergesWeakly: currentEval(S_i)(ω) → S(ω) for every ω ∈ 𝒟^n(ℝ^P)); maps g_i : ℝ^{n+1} → ℝ^k and measurable sets F_i ⊆ ℝ^{n+1}; put G_i(w) := ιw + ι'g_i(w). Assume, for every R > 0 (B_R := ball(0, R) ⊆ ℝ^{n+1}): (H1) for all large i, g_i is differentiable at every w ∈ B_R; (H2) for every ε > 0 and all large i, |g_i(w) − b| < ε and ‖Dg_i(w)‖ < ε for all w ∈ B_R; (H3) for all large i and every ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ ball(0, R) ⊆ ℝ^P, currentEval(S_i)(ω) = ∫_{F_i∩B_R} dω(G_i(w))(DG_i(w)e_0, …, DG_i(w)e_n) dw (DG_i(w) = fderiv ℝ G_i w); (H4) there is c ∈ ℝ such that for all large i and every ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ ball(0, R) and covectorEuclideanNorm(ω(y)) ≤ 1 for all y, currentEval(S_i)(ω) ≤ c. Then there is a measurable F ⊆ {ιw + ι'b : w ∈ ℝ^{n+1}} with S(ω) = ∫_F ξ_A(dω(y)) dH^{n+1}(y) for every ω ∈ 𝒟^n(ℝ^P) (IsBoundaryOfRegion S F (y ↦ ξ_A)).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4348

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5031

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3484, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3501, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5801, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5806, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5822, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5840

## Lean problem

Declaration: `Submission.codim1_zsl_flat_graph_limit`

```lean
∀ (n k : ℕ) (Us : ℕ → Set (Euclid (n + 1 + k))) (Ss : (i : ℕ) → GeometricCurrentOn (Us i) n) (S : GeometricCurrentOn (univ : Set (Euclid (n + 1 + k))) n) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ξA : MultiVector (n + 1 + k) (n + 1)) (b : Euclid k) (gs : ℕ → Euclid (n + 1) → Euclid k) (Fs : ℕ → Set (Euclid (n + 1))), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → (∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξA α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))) → ConvergesWeakly Ss S → (∀ i, MeasurableSet (Fs i)) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, DifferentiableAt ℝ (gs i) w) → (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in Fs i ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) ≤ c) → ∃ F : Set (Euclid (n + 1 + k)), MeasurableSet F ∧ F ⊆ {y | ∃ w, y = ι w + ι' b} ∧ IsBoundaryOfRegion S F (fun _ => ξA)
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 7(b)–(c), 8, 9 and 10 of the supplied proof of the parent node (projected test forms, uniform perimeter bound, BV compactness, identification of the limit), with the rescaled region boundaries entering only through (H1)–(H4). Simon 7.5.3 (chapter-07.txt lines 790–860: "by virtue of (1) and 5.2 we deduce from the BV Compactness 2.6 of Ch. 2 that some subsequence … converges in L¹_loc") and 7.5.5 (lines 862–901). Departures from the supplied proof: (1) test forms are lifted from divergence fields with a cut-off in the normal direction, and only a uniform comass bound K is used (the supplied step 8 used |ζπ_A^#α̃| ≤ 1 via Cauchy–Binet; a uniform constant suffices for the compactness); (2) the representation (H3) is assumed for every test form supported in a ball, so the splitting ω = ζω + (1 − ζ)ω of the supplied step 10 is unnecessary. Sibling child used: bv_compactness (Submission.codim1_zsl_perimeter_compactness).

Notation. P := n + 1 + k; ℝ^d = Euclid d; α(Le) := α(Le_0, …, Le_n) for an (n+1)-covector α and a linear L : ℝ^{n+1} → ℝ^P. ι*, ι'* are the adjoints: ι*ι = id, ι'*ι' = id, ι*ι' = 0, ι'*ι = 0, and (orthogonality and spanning) y = ιι*y + ι'ι'*y and |y|² = |ι*y|² + |ι'*y|² for every y. B_R := ball(0, R) ⊆ ℝ^{n+1}; H^{n+1} := μHE[n+1]; L^{n+1} := volume on ℝ^{n+1}; div φ := trace Dφ; G(w) := ιw + ι'b. |α| := covectorEuclideanNorm α, and a form ω is admissible if |ω(y)| ≤ 1 for all y.

Part A (lifting divergence fields to test forms).
A1. Let Ω be the standard volume form of ℝ^{n+1}, Ω(z_0, …, z_n) := det[z_0 | … | z_n]: the determinant Module.Basis.det of the standard basis, made a continuous alternating map with AlternatingMap.mkContinuous and the Leibniz bound |det[z_0 | … | z_n]| ≤ (n+1)!·∏_j|z_j|. Ω(e_0, …, e_n) = 1, and Ω(z, e_0, …, ê_j, …, e_n) = (−1)^j·z_j for z ∈ ℝ^{n+1} and j ≤ n (moving z to position j takes j transpositions).
A2. For a C^∞ compactly supported vector field φ on ℝ^{n+1} let α̃(v) := Ω(φ(v), ·, …, ·) (ContinuousAlternatingMap.curryLeft), an n-form on ℝ^{n+1}. α̃ is C^∞ (a continuous linear function of φ(v)), tsupport α̃ ⊆ tsupport φ, and by the coordinate formula for d (SimonGMT exteriorDerivative_apply: dβ(v)(e_0, …, e_n) = Σ_j (−1)^j·D[β(·)(e_0, …, ê_j, …, e_n)](v)e_j) together with A1,
 dα̃(v)(e_0, …, e_n) = Σ_j (−1)^j·∂_j((−1)^jφ_j)(v) = Σ_j ∂_jφ_j(v) = div φ(v).
A3. Fix h > 0 and let χ(t) := smoothTransition((4h² − t)/(3h²)) for t ∈ ℝ: χ is C^∞, 0 ≤ χ ≤ 1, χ(t) = 1 for t ≤ h² and χ(t) = 0 for t ≥ 4h². Put ζ(y) := χ(|ι'*y|²), a C^∞ function on ℝ^P.
A4. Define ω_φ(y) := ζ(y)·(α̃(ι*y)∘ι*), i.e. ζ times the pull-back affinePullbackForm ι* 0 α̃. ω_φ is C^∞. If ω_φ(y) ≠ 0 then ι*y ∈ tsupport φ and |ι'*y| < 2h; the set {y : ι*y ∈ tsupport φ, |ι'*y| ≤ 2h} is closed and bounded (|y|² = |ι*y|² + |ι'*y|²), hence compact. So ω_φ ∈ 𝒟^n(ℝ^P) and tsupport ω_φ ⊆ {ιv + ι'w : v ∈ tsupport φ, |w| ≤ 2h}.
A5. (Uniform comass bound.) z ↦ Ω(z, ·)∘ι* is a linear map from ℝ^{n+1} to n-covectors on ℝ^P, and |·| is continuous and absolutely homogeneous; so K := max(1, sup_{|z|≤1}|Ω(z, ·)∘ι*|) is finite (compact unit ball) and depends only on n, k and ι. If |φ| ≤ 1 everywhere, then |ω_φ(y)| = ζ(y)·|Ω(φ(ι*y), ·)∘ι*| ≤ K for all y.
A6. (Key identity.) Let v ∈ ℝ^{n+1}, w ∈ ℝ^k with |w| < h, y₀ := ιv + ι'w, and let L : ℝ^{n+1} → ℝ^P be linear with ι*L = id. Then dω_φ(y₀)(Le) = div φ(v). Indeed |ι'*y|² < h² for y near y₀, so ζ = 1 near y₀ and ω_φ coincides near y₀ with π^#α̃ := affinePullbackForm ι* 0 α̃. The exterior derivative at a point depends only on the germ (Filter.EventuallyEq.fderiv_eq), so dω_φ(y₀) = d(π^#α̃)(y₀) = dα̃(ι*y₀)∘ι* (SimonGMT exteriorDerivative_affinePullbackForm) = dα̃(v)∘ι*. Hence dω_φ(y₀)(Le_0, …, Le_n) = dα̃(v)(ι*Le_0, …, ι*Le_n) = dα̃(v)(e_0, …, e_n) = div φ(v) by A2.

Part B (uniform perimeter bounds).
B1. Fix R > 0 and put h := |b| + 1, R₂ := R + 2h. Let c₂ be the constant of (H4) for R₂. By (H1), (H2) with ε = 1, (H3) and (H4), all for R₂, there is i₀ such that for i ≥ i₀: g_i is differentiable on B_{R₂}; |g_i(w) − b| < 1, hence |g_i(w)| < h, on B_{R₂}; the representation (H3) holds for every ω supported in ball(0, R₂); and currentEval(S_i)(ω) ≤ c₂ for every admissible ω supported in ball(0, R₂).
B2. Let i ≥ i₀ and let φ be C^∞ with compact support, tsupport φ ⊆ B_R and |φ| ≤ 1; let ω := ω_φ with h from B1. For v ∈ tsupport φ and |w| ≤ 2h, |ιv + ι'w| ≤ |v| + |w| < R + 2h, so tsupport ω ⊆ ball(0, R₂). For w ∈ B_{R₂}: G_i(w) = ιw + ι'g_i(w) with |g_i(w)| < h, g_i is differentiable at w, DG_i(w) = ι + ι'Dg_i(w) and ι*DG_i(w) = id; so by A6, dω(G_i(w))(DG_i(w)e) = div φ(w). Hence by (H3), currentEval(S_i)(ω) = ∫_{F_i∩B_{R₂}} div φ = ∫_{F_i} div φ, because div φ vanishes outside tsupport φ ⊆ B_{R₂} (φ vanishes near such points) and F_i is measurable.
B3. ω/K is admissible (A5) and has the same support as ω, and currentEval(S_i) is linear in the form (tsupport(ω/K) = tsupport ω, so the same branch of currentEval applies, and S_i is linear). By B1, ∫_{F_i} div φ = K·currentEval(S_i)(ω/K) ≤ K·c₂. Thus for every R > 0 there are c(R) := K·c₂ and i₀ such that ∫_{F_i} div φ ≤ c(R) for every i ≥ i₀ and every admissible φ with tsupport φ ⊆ B_R: this is the hypothesis of bv_compactness for the measurable sets F_i ⊆ ℝ^{n+1}.

Part C (compactness).
C1. bv_compactness (with m := n + 1) gives a strictly increasing σ and a measurable F' ⊆ ℝ^{n+1} with L^{n+1}((F_{σ(i)} Δ F') ∩ B_R) → 0 for every R.

Part D (identification of S).
D1. Fix ω ∈ 𝒟^n(ℝ^P). tsupport ω is compact, so tsupport ω ⊆ ball(0, R) for some R > 0. Put h_i(w) := dω(G_i(w))(DG_i(w)e) and h(w) := dω(G(w))(ιe). dω is continuous with compact support, hence bounded, say by M, and uniformly continuous.
D2. By (H1)–(H2) (and |ι'u| = |u|), for every ε > 0 and all large i, |G_i(w) − G(w)| = |g_i(w) − b| < ε and ‖DG_i(w) − ι‖ = ‖Dg_i(w)‖ < ε for all w ∈ B_R. The map (y, L) ↦ dω(y)(Le) is uniformly continuous on ℝ^P × {L : ‖L‖ ≤ 2}, because dω is uniformly continuous and bounded and α is multilinear: |α(z) − α'(z')| ≤ ‖α − α'‖·∏_j|z_j| + ‖α'‖·Σ_j|z_j − z'_j|·∏_{l≠j}max(|z_l|, |z'_l|). Hence sup_{B_R}|h_i − h| → 0, and |h_i| ≤ M' := 2^{n+1}M on B_R for all large i.
D3. For large i, h_i is measurable on B_R: G_i is continuous on B_R and w ↦ DG_i(w) = ι + ι'Dg_i(w) is measurable (measurable_fderiv); h is continuous.
D4. By (H3), for all large i, currentEval(S_{σ(i)})(ω) = ∫_{F_{σ(i)}∩B_R} h_{σ(i)}, and
 |∫_{F_{σ(i)}∩B_R} h_{σ(i)} − ∫_{F'∩B_R} h| ≤ ∫_{B_R}|1_{F_{σ(i)}} − 1_{F'}|·|h_{σ(i)}| + ∫_{F'∩B_R}|h_{σ(i)} − h| ≤ M'·L^{n+1}((F_{σ(i)} Δ F') ∩ B_R) + L^{n+1}(B_R)·sup_{B_R}|h_{σ(i)} − h|,
which tends to 0 by C1 and D2.
D5. S_i ⇀ S gives currentEval(S_{σ(i)})(ω) → S(ω). Hence S(ω) = ∫_{F'∩B_R} h = ∫_{F'} h, because for |w| ≥ R, |G(w)|² = |w|² + |b|² ≥ R², so G(w) ∉ ball(0, R) ⊇ tsupport ω ⊇ tsupport dω and h(w) = 0.

Part E (transfer to the plane).
E1. G is an isometry of ℝ^{n+1} onto A_b := {ιw + ι'b : w ∈ ℝ^{n+1}} (|G(w) − G(w')| = |w − w'|), hence a closed embedding and a measurable embedding (Topology.IsClosedEmbedding.measurableEmbedding). F := G(F') is measurable and F ⊆ A_b = {y : ∃ w, y = ιw + ι'b}.
E2. Hausdorff measure is invariant under isometries: G_#(μHE[n+1] on ℝ^{n+1}) = H^{n+1}⌞range G (Isometry.map_euclideanHausdorffMeasure), and μHE[n+1] = L^{n+1} on ℝ^{n+1} (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). As G is injective, H^{n+1}⌞F = G_#(L^{n+1}⌞F') and ∫_F f dH^{n+1} = ∫_{F'} f(G(w)) dw for every f : ℝ^P → ℝ (MeasurableEmbedding.integral_map).
E3. With f(y) := ξ_A(dω(y)) and ξ_A(α) = α(ιe): ∫_F ξ_A(dω(y)) dH^{n+1}(y) = ∫_{F'} dω(G(w))(ιe) dw = ∫_{F'} h = S(ω) by D5. As ω was arbitrary, IsBoundaryOfRegion S F (y ↦ ξ_A), with F measurable and F ⊆ {y : ∃ w, y = ιw + ι'b}. ∎

## Key steps

1. Divergence fields φ on ℝ^{n+1} lift to test forms ω_φ = ζ·(Ω(φ∘ι*, ·)∘ι*) on ℝ^P with |ω_φ| ≤ K, supported in a slab |ι'*y| ≤ 2h, and dω_φ(ιv + ι'w)(Le) = div φ(v) whenever |w| < h and ι*L = id.
2. By (H2) the graphs G_i = ι + ι'g_i lie in that slab and ι*DG_i = id, so (H3) gives currentEval(S_i)(ω_φ) = ∫_{F_i} div φ, which (H4) bounds by K·c₂: uniform local perimeter bounds.
3. bv_compactness yields F' with 1_{F_σ(i)} → 1_{F'} in L¹_loc; (H1)–(H2) give uniform convergence of the integrands, so S(ω) = ∫_{F'} dω(ιw + ι'b)(ιe) dw.
4. The isometry G(w) = ιw + ι'b carries this to S(ω) = ∫_{G(F')} ξ_A(dω) dH^{n+1}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `cat decomposition-audit-v1.json decomposition-review-receipt-v1.json; python3 dump of decomposition-v1.json (12 subproblems: statements, lean_statements, natural proofs, key steps, dependencies)`
- `python3 scan of dag.json: lean_name lookup of the 8 codim1_zsl_* names, the 4 reused names (status, candidate commit, lean_statement byte equality with decomposition-v1.json), dtc_hausdorff_dilation, dor_ims_unitOrientation_dual and codim1_zero_scale_limit_offset_plane; raw count of 'codim1_zsl'; keyword scan 'area formula|BV|perimeter|bvVariation|indicator' over statements and titles`
- `for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl $r -- 'GMT/*.lean' (1277 commits); positive control: the same loop with dgcr_graph_orientation_jacobian; grep -rl codim1_zsl .lake/packages/simongmt/Poincare GMT`
- `grep -n 'def IsTestForm|def exteriorDerivative|theorem exteriorDerivative_apply|def covectorEuclideanNorm|def massOn|def zeroRegion|def support|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem tsupport_exteriorDerivative_subset' simongmt/Poincare/SimonGMT/Chapter06/*.lean, then sed of Forms.lean 25-135, Mass.lean 25-80, CurrentLocalEquality.lean 95-125, AffineCurrentPushforward.lean 30-50 and 145-160, Currents.lean 120-190`
- `rg -n 'theorem tsupport_eq|theorem support_eq|protected theorem neg|symmetric :' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'integral_comp_inv_smul_of_nonneg|support_convolution_subset|exists_isCompact_sdiff_lt|exists_isOpen_sdiff_lt|integral_pos_iff_support_of_nonneg|theorem lintegral_tsum' mathlib/Mathlib; rg -n 'namespace Module.Basis|def det' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `lean -DautoImplicit=false /tmp/zsl-v2/Lib.lean and /tmp/zsl-v2/Lib2.lean (#check of about 70 Mathlib/SimonGMT lemmas cited by the children)`
- `lean -DautoImplicit=false /tmp/zsl-v2/Bump.lean (ρ := (∫b)⁻¹·b for b : ContDiffBump (0 : Euclid m) with radii 1/2, 1: ContDiff ℝ ⊤, ρ ≥ 0, ρ(−z) = ρ(z), tsupport ρ = closedBall 0 1, ∫ρ = 1)`
- `lean -DautoImplicit=false /tmp/zsl-v2/TypesV2.lean (12 child types generated from the v2 JSON plus the assembly of the selected type); lean -DautoImplicit=false /tmp/zsl-v2/AssemblyV2.lean (children as axioms, #print axioms)`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-review-receipt-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/tmp/zsl-v2/Lib.lean`
- `/tmp/zsl-v2/Lib2.lean`
- `/tmp/zsl-v2/Bump.lean`
- `/tmp/zsl-v2/TypesV2.lean`
- `/tmp/zsl-v2/AssemblyV2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG.
- The selected node is 'decomposing' with the handoff's exact frozen type.
- The 4 reused declarations are accepted with types byte-identical to v1: dtc_blowUp_testForm_corr (5e184fbc), setIntegral_blowUpMap_image_eq_inv_pow_mul (713eebc5), rsdic_unitOrientation_eq_or_eq_neg (fe95347b) and dgcr_graph_orientation_jacobian (62aa1f11).
- The 8 codim1_zsl_* names have 0 occurrences in dag.json, SimonGMT, GMT/ and the 1277 commits reachable from refs. The positive control dgcr_graph_orientation_jacobian was found on 6 of those commits.
- No accepted node gives an exact graph area formula or BV compactness. The only area-formula nodes are unaccepted (dpf_area_formula_bilipschitz_rectifiable, idtp_carrier_area_formula) and have other types.
Library.
- The SimonGMT definitions match the children's proofs: exteriorDerivative = extDeriv with the alternating-sum formula, IsTestForm = ContDiff ℝ ∞ ∧ HasCompactSupport, covectorEuclideanNorm, massOn/massAdmissibleOn, zeroRegion/support and affinePullbackForm.
- In the snapshot Mathlib, ContDiffBump.tsupport_eq (BumpFunction/Basic.lean:157) gives closedBall c rOut. This confirms the v1 defect, so step 1 of bv_compactness now claims only tsupport ρ = closedBall(0, 1). ContDiffBump.neg (:132) gives evenness, and support_eq (:151) gives the open-ball support.
- Every lemma cited by the corrected proofs exists in the import closure. Examples: integral_comp_inv_smul_of_nonneg (Haar/NormedSpace.lean:129), support_convolution_subset (Convolution.lean:670), MeasurableSet.exists_isCompact_sdiff_lt/exists_isOpen_sdiff_lt (Regular.lean:843/385), exists_continuous_one_zero_of_isCompact and Module.Basis.det (Determinant.lean:591; the old name Basis.det is fixed).
Lean.
- Bump.lean compiles the corrected mollifier.
- TypesV2.lean elaborates all 12 frozen types taken verbatim from the v2 JSON and proves the selected type; lean exits 0. Its axioms are propext, sorryAx, Classical.choice and Quot.sound.
- With the children as axioms, AssemblyV2.lean depends only on propext, Classical.choice, Quot.sound and the 4 direct children.
- leaf_verification.check_source_delta forbids new declarations and imports in leaf proofs, so the deep lemmas must stay separate children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
