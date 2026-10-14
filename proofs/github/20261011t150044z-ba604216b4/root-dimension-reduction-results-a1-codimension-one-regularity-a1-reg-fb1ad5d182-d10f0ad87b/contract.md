<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.test_form-a1 -->

## Theorem `Submission.codim1_lur_chart_test_form_exists`

Let P, n ∈ ℕ, U ⊆ ℝ^P, x ∈ ℝ^P, let ι : ℝ^{n+1} → ℝ^P be a linear isometry with adjoint A := ι*, let u : ℝ^{n+1} → ℝ^P, δ₁, δ₂ ∈ ℝ and φ : ℝ^{n+1} → ℝ^{n+1}. Write D := B_{δ₁}(0) ⊆ ℝ^{n+1}, G(v) := x + ιv + u(v), DG(v) for the Fréchet derivative of G at v, e_0, …, e_n for the standard basis of ℝ^{n+1}, j.succAbove : {0, …, n−1} → {0, …, n} for the increasing enumeration of {0, …, n} ∖ {j}, and Z := {w ∈ ℝ^P : |A(w − x)| < δ₁ and |w − x − ιA(w − x)| < δ₂}. Assume: δ₂ > 0; closedBall(x, δ₁ + δ₂) ⊆ U; u is differentiable on D; ⟨ιw, u(v)⟩ = 0 for all v ∈ D and w ∈ ℝ^{n+1}; |u(v)| < δ₂/2 for all v ∈ D; φ is C^∞, has compact support, tsupport φ ⊆ D and |φ(y)| ≤ 1 for all y. Then there is a test form ω ∈ 𝒟^n(U) (TestFormOn U n: a C^∞ n-form on ℝ^P with compact support and tsupport ω ⊆ U) such that (i) tsupport ω ⊆ Z; (ii) tsupport ω ⊆ closedBall(x, δ₁ + δ₂); (iii) covectorEuclideanNorm(ω(w)) ≤ (n+1)!·√(P^n) for every w ∈ ℝ^P; and (iv) φ = 1_D · Σ_{j=0}^{n} (−1)^j ω(G(·))(DG(·)e_{j.succAbove 0}, …, DG(·)e_{j.succAbove(n−1)}) e_j, i.e. for v ∈ D, φ(v) = Σ_j ((−1)^j ω(G(v))(DG(v)e_{j.succAbove 0}, …, DG(v)e_{j.succAbove(n−1)})) e_j, and φ(v) = 0 for v ∉ D.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.test_form-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5173

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6058, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6028, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6045, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6022

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_lur_chart_test_form_exists`

```lean
∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ) (φ : Euclid (n + 1) → Euclid (n + 1)), 0 < δ₂ → closedBall x (δ₁ + δ₂) ⊆ U → DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ‖u v‖ < δ₂ / 2) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 δ₁ → (∀ y, ‖φ y‖ ≤ 1) → ∃ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ closedBall x (δ₁ + δ₂) ∧ (∀ w, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) w) ≤ ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n)) ∧ φ = (ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * (ω : DifferentialForm (Euclid P) n) (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ))
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_perimeter-a1.test_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 3–6 and 8 of the supplied proof of chart_perimeter: the test forms of Simon Ch. 6, 2.35 (book/chapter-06.txt lines 606–632; ω = Σ_j (−1)^{j−1} a_j dx^1 ∧ … ∧ \hat{dx^j} ∧ … ∧ dx^n with dω = div a dx^1 ∧ … ∧ dx^n, lines 625–626, where the printed sign (−1)^j is a misprint for (−1)^{j−1}, cf. lines 594–595), transported to the graph chart G; with 0-based indices the sign is (−1)^j, as in the field of chart_divergence. Departures, all inessential: (a) the form is written ω(w) := Λ(ζ(w)φ(π(w))), which equals ζ(w)·Λ(φ(π(w))) of the supplied proof by linearity of Λ; (b) instead of a compact K ⊆ D with tsupport φ ⊆ K the hypothesis is "φ has compact support and tsupport φ ⊆ D" (the supplied proof's K may be taken to be tsupport φ); (c) u is only assumed differentiable on D; (d) conclusion (ii) is recorded separately for the mass estimate of the parent. Siblings used: chart_geometry, det_covector, coeff_bound, det_laplace.

Notation. π(w) := A(w − x) and p^⊥(w) := w − x − ιπ(w) for w ∈ ℝ^P.

Proof.
1. (Chart identities.) By chart_geometry (u is differentiable on D and ⟨ιw, u(v)⟩ = 0 for v ∈ D): ‖A‖ ≤ 1, and for every v ∈ D, π(G(v)) = v, p^⊥(G(v)) = u(v) and A(DG(v)y) = y for all y. The maps π and p^⊥ are affine (continuous linear maps composed with w ↦ w − x), hence C^∞. Since w − x = ιπ(w) + p^⊥(w) and |ιπ(w)| = |π(w)| (ι is an isometry), |w − x| ≤ |π(w)| + |p^⊥(w)| for every w.
2. (Λ.) By det_covector applied to A there is a continuous linear map Λ : ℝ^{n+1} → Λ^n(ℝ^P) with Λ(q)(a_0, …, a_{n−1}) = det[q, Aa_0, …, Aa_{n−1}] (column 0 equal to q, column k+1 equal to Aa_k) for all q and a.
3. (Cut-off.) Put a := (δ₂/2)² and b := (3δ₂/4)²; since δ₂ > 0, b − a = 5δ₂²/16 > 0. Let ζ(w) := smoothTransition((b − |p^⊥(w)|²)/(b − a)), where Real.smoothTransition is C^∞ (Real.smoothTransition.contDiff), takes values in [0, 1], vanishes on (−∞, 0] and equals 1 on [1, ∞). ζ is C^∞, being smoothTransition composed with the C^∞ map w ↦ (b − |p^⊥(w)|²)/(b − a) (contDiff_norm_sq), and 0 ≤ ζ ≤ 1.
  (3a) If ζ(w) ≠ 0, then (b − |p^⊥(w)|²)/(b − a) > 0 (otherwise ζ(w) = 0), so |p^⊥(w)|² < b and |p^⊥(w)| < 3δ₂/4.
  (3b) If |p^⊥(w)| < δ₂/2, then |p^⊥(w)|² < a, so (b − |p^⊥(w)|²)/(b − a) ≥ 1 and ζ(w) = 1.
4. (The form.) Define ω(w) := Λ(ζ(w)·φ(π(w))) for w ∈ ℝ^P. Then ω is C^∞: Λ is continuous linear, and w ↦ ζ(w)φ(π(w)) is C^∞ because ζ, φ and π are.
5. (Support.) Let S := {w : π(w) ∈ tsupport φ and |p^⊥(w)| ≤ 3δ₂/4}. S is closed, as an intersection of preimages of closed sets under the continuous maps π and |p^⊥|. If ω(w) ≠ 0 then ζ(w)φ(π(w)) ≠ 0 (because Λ(0) = 0), so ζ(w) ≠ 0 and φ(π(w)) ≠ 0; hence π(w) ∈ support φ ⊆ tsupport φ and, by (3a), |p^⊥(w)| < 3δ₂/4, i.e. w ∈ S. As S is closed, tsupport ω ⊆ S.
  (5a) (Compact support.) tsupport φ is compact, hence bounded: tsupport φ ⊆ closedBall(0, R) for some R. For w ∈ S, |w − x| ≤ |π(w)| + |p^⊥(w)| ≤ R + 3δ₂/4 by step 1. Thus tsupport ω is a closed subset of the compact ball closedBall(x, R + 3δ₂/4), so it is compact: ω has compact support.
  (5b) (S ⊆ Z.) For w ∈ S, π(w) ∈ tsupport φ ⊆ D, so |π(w)| < δ₁; and |p^⊥(w)| ≤ 3δ₂/4 < δ₂.
  (5c) (Z ⊆ closedBall(x, δ₁ + δ₂).) For w ∈ Z, |w − x| ≤ |π(w)| + |p^⊥(w)| < δ₁ + δ₂ by step 1.
  Hence tsupport ω ⊆ S ⊆ Z ⊆ closedBall(x, δ₁ + δ₂) ⊆ U. By step 4 and (5a), ω is a test form (C^∞ with compact support) with tsupport ω ⊆ U, i.e. ω ∈ 𝒟^n(U); and (i), (ii) hold.
6. ((iii) Coefficient bound.) Fix w ∈ ℝ^P and put q := ζ(w)φ(π(w)). Then |q| = ζ(w)·|φ(π(w))| ≤ 1·1 = 1, ω(w) = Λ(q), and Λ(q)(a) = det[q, Aa_0, …, Aa_{n−1}] for all a by step 2. By coeff_bound (with ‖A‖ ≤ 1 from step 1), covectorEuclideanNorm(ω(w)) ≤ (n+1)!·√(P^n).
7. ((iv) on D.) Let v ∈ D. By step 1, π(G(v)) = v and p^⊥(G(v)) = u(v) with |u(v)| < δ₂/2, so ζ(G(v)) = 1 by (3b) and ω(G(v)) = Λ(φ(v)). Fix j ∈ {0, …, n} and put a_k := DG(v)e_{j.succAbove k} (k = 0, …, n−1). By step 1, Aa_k = e_{j.succAbove k}. Hence, by step 2 and det_laplace, ω(G(v))(a_0, …, a_{n−1}) = det[φ(v), e_{j.succAbove 0}, …, e_{j.succAbove(n−1)}] = (−1)^j φ_j(v), where φ_j(v) is the j-th coordinate of φ(v). Therefore the j-th summand of (iv) is ((−1)^j·(−1)^j φ_j(v)) e_j = φ_j(v) e_j (as (−1)^{2j} = 1), and Σ_j φ_j(v) e_j = φ(v) (expansion of a vector of ℝ^{n+1} in the standard basis). So the right side of (iv) equals φ(v) at every v ∈ D.
8. ((iv) off D.) If v ∉ D, the right side of (iv) is 0 (indicator of D), and v ∉ tsupport φ because tsupport φ ⊆ D, so φ(v) = 0 (image_eq_zero_of_notMem_tsupport).
9. (Conclusion.) Steps 7–8 prove (iv) at every point, hence as an equality of functions (funext). Together with steps 5–6, ω has all the asserted properties. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the contract). The declaration below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b366308 when placed after `import GMT.Ch07.Submission` inside `namespace GMT.Ch07` with the frozen contract's `open` commands (both inside and outside a `noncomputable section`), and `#print axioms` reports only propext, Classical.choice and Quot.sound together with the four sibling declarations.

```lean
theorem Submission.codim1_lur_chart_test_form_exists : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ) (φ : Euclid (n + 1) → Euclid (n + 1)), 0 < δ₂ → closedBall x (δ₁ + δ₂) ⊆ U → DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ‖u v‖ < δ₂ / 2) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 δ₁ → (∀ y, ‖φ y‖ ≤ 1) → ∃ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ closedBall x (δ₁ + δ₂) ∧ (∀ w, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) w) ≤ ((n + 1).factorial : ℝ) * Real.sqrt ((P : ℝ) ^ n)) ∧ φ = (ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * (ω : DifferentialForm (Euclid P) n) (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) := by
  intro P n U x ι u δ₁ δ₂ φ hδ₂ hball hu horth hsmall hφ hφc hφD hφ1
  obtain ⟨hA, -, hG⟩ := Submission.codim1_lur_graph_chart_adjoint_identities P n x ι u δ₁ hu horth
  set A := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hAdef
  obtain ⟨Λ, hΛ⟩ := Submission.codim1_lur_det_covector_clm P n A
  -- the chart projections π(w) = ι*(w - x) and p⊥(w) = w - x - ι π(w)
  set π : Euclid P → Euclid (n + 1) := fun w => A (w - x) with hπdef
  set q : Euclid P → Euclid P := fun w => w - x - ι (A (w - x)) with hqdef
  have hπc : ContDiff ℝ (⊤ : ℕ∞) π := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hqc : ContDiff ℝ (⊤ : ℕ∞) q :=
    (contDiff_id.sub contDiff_const).sub (ι.toContinuousLinearMap.contDiff.comp hπc)
  have hdecomp : ∀ w, ‖w - x‖ ≤ ‖π w‖ + ‖q w‖ := by
    intro w
    have : w - x = ι (π w) + q w := by simp only [hπdef, hqdef]; abel
    rw [this]
    exact (norm_add_le _ _).trans (by rw [ι.norm_map])
  -- the cut-off ζ(w) = χ(|p⊥(w)|²), χ = 1 on [0, (δ₂/2)²], χ = 0 on [(3δ₂/4)², ∞)
  set a : ℝ := (δ₂ / 2) ^ 2 with ha
  set b : ℝ := (3 * δ₂ / 4) ^ 2 with hb
  have hab : 0 < b - a := by rw [ha, hb]; nlinarith
  set ζ : Euclid P → ℝ := fun w => Real.smoothTransition ((b - ‖q w‖ ^ 2) / (b - a)) with hζdef
  have hζc : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_norm_sq ℝ).comp hqc)).div_const _)
  have hζ0 : ∀ w, 0 ≤ ζ w := fun w => Real.smoothTransition.nonneg _
  have hζ1 : ∀ w, ζ w ≤ 1 := fun w => Real.smoothTransition.le_one _
  have hζsupp : ∀ w, ζ w ≠ 0 → ‖q w‖ < 3 * δ₂ / 4 := by
    intro w hw
    by_contra hcon
    push Not at hcon
    apply hw
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hab.le
    have : (3 * δ₂ / 4) ^ 2 ≤ ‖q w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hcon 2
    rw [hb]; linarith
  -- the test form ω(w) = Λ(ζ(w) φ(π(w))) = ζ(w) det[φ(π(w)), ι*·, …, ι*·]
  set ω₀ : DifferentialForm (Euclid P) n := fun w => Λ (ζ w • φ (π w)) with hω₀def
  have hω₀c : ContDiff ℝ (⊤ : ℕ∞) ω₀ := Λ.contDiff.comp (hζc.smul (hφ.comp hπc))
  -- support
  set S : Set (Euclid P) := {w | π w ∈ tsupport φ ∧ ‖q w‖ ≤ 3 * δ₂ / 4} with hSdef
  have hSclosed : IsClosed S :=
    ((isClosed_tsupport φ).preimage hπc.continuous).inter
      (isClosed_le (continuous_norm.comp hqc.continuous) continuous_const)
  have hsuppS : support ω₀ ⊆ S := by
    intro w hw
    have hne : ζ w • φ (π w) ≠ 0 := by
      intro h0; apply hw; simp only [hω₀def, h0, map_zero]
    refine ⟨subset_tsupport _ (right_ne_zero_of_smul hne), (hζsupp w (left_ne_zero_of_smul hne)).le⟩
  have htsS : tsupport ω₀ ⊆ S := closure_minimal hsuppS hSclosed
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall 0
  have hSball : S ⊆ closedBall x (R + 3 * δ₂ / 4) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖π w‖ ≤ R := by simpa using hR hw.1
    linarith [hdecomp w, hw.2]
  have hcpt : HasCompactSupport ω₀ :=
    (isCompact_closedBall x _).of_isClosed_subset (isClosed_tsupport _) (htsS.trans hSball)
  have hSZ : S ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧
      ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} := by
    intro w hw
    refine ⟨?_, ?_⟩
    · have h1 := hφD hw.1
      rw [mem_ball_zero_iff] at h1
      exact h1
    · have := hw.2; show ‖q w‖ < δ₂; linarith
  have hZB : {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧
      ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ⊆
      closedBall x (δ₁ + δ₂) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖π w‖ < δ₁ := hw.1
    have h2 : ‖q w‖ < δ₂ := hw.2
    linarith [hdecomp w]
  let ω : TestFormOn U n := ⟨ω₀, ⟨⟨hω₀c, hcpt⟩, (htsS.trans hSZ).trans (hZB.trans hball)⟩⟩
  refine ⟨ω, htsS.trans hSZ, (htsS.trans hSZ).trans hZB, ?_, ?_⟩
  · -- coefficient bound
    intro w
    apply Submission.codim1_lur_det_covector_norm_le P n A (ζ w • φ (π w)) _ hA _ (hΛ _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ0 w)]
    calc ζ w * ‖φ (π w)‖ ≤ 1 * 1 := mul_le_mul (hζ1 w) (hφ1 _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · -- the pull-back field is φ
    funext v
    by_cases hv : v ∈ ball (0 : Euclid (n + 1)) δ₁
    · rw [Set.indicator_of_mem hv]
      obtain ⟨hπv, hqv, hdv⟩ := hG v hv
      have hζv : ζ (x + ι v + u v) = 1 := by
        apply Real.smoothTransition.one_of_one_le
        rw [le_div_iff₀ hab, one_mul]
        have hq' : q (x + ι v + u v) = u v := hqv
        rw [hq']
        have h0 := hsmall v hv
        have : ‖u v‖ ^ 2 < (δ₂ / 2) ^ 2 := pow_lt_pow_left₀ h0 (norm_nonneg _) two_ne_zero
        rw [ha]; linarith
      have hterm : ∀ j : Fin (n + 1),
          (ω : DifferentialForm (Euclid P) n) (x + ι v + u v)
            (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1)) =
          (-1 : ℝ) ^ (j : ℕ) * φ v j := by
        intro j
        show Λ (ζ (x + ι v + u v) • φ (π (x + ι v + u v))) _ = _
        have hπ' : π (x + ι v + u v) = v := hπv
        rw [hζv, one_smul, hπ', hΛ]
        simp only [hdv]
        exact Submission.codim1_lur_det_laplace_first_column n (φ v) j
      simp only [hterm]
      have hsq : ∀ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * φ v j) = φ v j := by
        intro j
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      simp only [hsq]
      ext i
      simp [Pi.single_apply]
    · rw [Set.indicator_of_notMem hv]
      exact image_eq_zero_of_notMem_tsupport fun h => hv (hφD h)
```

## Key steps

1. chart_geometry: ‖ι*‖ ≤ 1, π∘G = id, p^⊥∘G = u and ι*∘DG = id on D; |w − x| ≤ |π(w)| + |p^⊥(w)|.
2. ω(w) := Λ(ζ(w)φ(π(w))) with Λ from det_covector and the smoothTransition cut-off ζ = χ(|p^⊥|²) is C^∞.
3. tsupport ω ⊆ {π ∈ tsupport φ, |p^⊥| ≤ 3δ₂/4}, a compact subset of Z ⊆ closedBall(x, δ₁ + δ₂) ⊆ U, so ω ∈ 𝒟^n(U).
4. coeff_bound with |ζφ∘π| ≤ 1 gives covectorEuclideanNorm(ω(w)) ≤ (n+1)!·√(P^n).
5. On D, ζ∘G = 1 and ι*DG(v)e_{j.succAbove k} = e_{j.succAbove k}, so det_laplace gives the j-th coefficient (−1)^j(−1)^jφ_j(v) = φ_j(v); off D both sides vanish.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C lake-packages-25730c7c/{mathlib,simongmt} rev-parse HEAD; python3 read of snapshot project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem det_succ_column_zero|theorem det_le |smoothTransition' <snapshot>/mathlib/Mathlib`
- `rg -n 'def curryLeft|def mkContinuous|compContinuousLinearMapCLM|continuous_of_finiteDimensional|toContinuousAlternatingMap' <snapshot>/mathlib/Mathlib/{Topology/Algebra/Module/Alternating,Analysis/Normed/Module/Alternating,LinearAlgebra/Alternating}`
- `rg -n 'volumeForm_robust|abs_volumeForm_apply_le' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean; rg -n 'adjoint_inner_left|norm_adjoint' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n 'ContinuousOn.measurable_piecewise' <snapshot>/mathlib/Mathlib`
- `#check in the GMT.Ch07.Submission import closure: Matrix.det_le (unknown constant), Module.Basis.det, Matrix.det_apply, Fintype.card_perm, ContinuousAlternatingMap.curryLeft_apply_apply, Orientation.abs_volumeForm_apply_le, Orientation.volumeForm_robust', ContinuousOn.measurable_piecewise, Real.smoothTransition.contDiff, PiLp.norm_apply_le, MultilinearMap.continuous_of_finiteDimensional (unknown constant)`
- `grep -n '^theorem|^def|^abbrev|^structure' simongmt Chapter06/{Forms,Currents,Mass}.lean`
- `python3 scans of dag.json (902 then 983 nodes): frozen types of codim1_lur_chart_divergence_formula, dor_ims_massOn_le_measure and the selected node; accepted statements containing covectorEuclideanNorm, massOn with IsIntegerMultiplicity, R.measure … ≠ ∞, succAbove, Matrix.det; lean_name lookup of the five new names (no hits)`
- `grep -rl -E '<five new names>' runs/.../nodes runs/.../dag.json (no match); git for-each-ref | xargs -n 100 sh -c 'git grep -l -E "<five new names>" "$@" -- GMT/*.lean' (0 of 1695 ref tips; control cmr_abs_apply_le_massOn: 3 tips)`
- `git show {7a706164,702e7082,fae4fd1e}:GMT/Ch07/Submission.lean > Cand_*.lean; diff against GMT/Ch07/Contract.lean (additions only); '#print axioms' for cmr_abs_apply_le_massOn, rsd_imrep_compact_measure_ne_top, dor_ims_massOn_le_measure`
- `lean -DautoImplicit=false (LEAN_PATH from 'lake env printenv LEAN_PATH') /tmp/cpsplit/final/{Types,Inst,Assembly,FullChain,FullChainNoSection}.lean, /tmp/cpsplit/proto/{Laplace,DetCov,Coeff,Chart,TestForm}.lean, /tmp/cpsplit/out/Appendices.lean`
- `sed -n 560,640p book/chapter-06.txt (Simon 6.2.34–2.35); grep -n '( 1)j aj dx|!j  D ( 1)j 1' book/chapter-06.txt`
- `read nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-{1a867a3878,5d8d9c70c5}/ (handoff, supplied proof, decomposition-v1.json) and the handoffs/accepted-candidate.json of the two reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1a867a3878/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cpsplit/final/Types.lean`
- `/tmp/cpsplit/final/Inst.lean`
- `/tmp/cpsplit/final/Assembly.lean`
- `/tmp/cpsplit/final/FullChain.lean`
- `/tmp/cpsplit/final/FullChainNoSection.lean`
- `/tmp/cpsplit/out/Appendices.lean`
- `/tmp/cpsplit/reuse/Cand_cmr_abs_apply_le_massOn.lean`
- `/tmp/cpsplit/reuse/Cand_rsd_imrep_compact_measure_ne_top.lean`
- `/tmp/cpsplit/reuse/Cand_dor_ims_massOn_le_measure.lean`

Pins match.
- Snapshot manifest: project b4d606db, Mathlib 25730c7c; both equal workspace HEAD and the lake package checkout (lake-packages-25730c7c/mathlib).
- simongmt is 2b366308 in both the snapshot lake-manifest and the package checkout.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library (what exists).
- In the import closure: Matrix.det_succ_column_zero; Matrix.det_apply with Fintype.card_perm (Leibniz); Module.Basis.det.
- Also present: Orientation.volumeForm_robust' and Orientation.abs_volumeForm_apply_le (Hadamard).
- Alternating-map API: AlternatingMap.mkContinuous, ContinuousAlternatingMap.curryLeft and compContinuousLinearMapCLM.
- Analysis: Real.smoothTransition (ContDiff of every order, values in [0, 1]); ContinuousLinearMap.adjoint_inner_left; ContinuousOn.measurable_piecewise.
- SimonGMT Chapter06 supplies Covector, DifferentialForm, TestFormOn, covectorEuclideanNorm, massAdmissibleOn and GeometricCurrentOn.le_massOn.

Library (what is missing).
- Matrix.det_le (Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean) and MultilinearMap.continuous_of_finiteDimensional are not in the import closure; Lean reports unknown constant.
- coeff_bound therefore proves the entrywise bound from the Leibniz formula, and det_covector obtains continuity from Hadamard's inequality.

DAG.
- Accepted declarations reused with byte-identical types:
  - rsd_imrep_compact_measure_ne_top (candidate 702e7082);
  - cmr_abs_apply_le_massOn (candidate 7a706164).
- Each candidate file only adds to Contract.lean. A fresh compile of each prints only propext, Classical.choice and Quot.sound, as it does for dor_ims_massOn_le_measure (fae4fd1e).
- The five new names occur in no dag.json node (983 nodes), no nodes/ file, and no GMT/*.lean at any of the 1695 ref tips.

Lean.
- Types.lean elaborates all 7 child types after import GMT.Ch07.Submission with the contract opens.
- Inst.lean confirms the matrix-column, coordinate, indicator, adjoint and smoothness-order conventions by rfl.
- Assembly.lean proves the frozen selected type from test_form and the two reused declarations, with chart_divergence and mass_upper_bound as axioms; no sorryAx occurs.
- FullChain.lean proves all five new children and then the selected theorem. Each new child depends only on the standard axioms; the selected theorem adds exactly its two resolved dependencies and the two reused declarations. The same holds with no enclosing noncomputable section.
- An independent review subagent re-ran these files and accepted the split.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
