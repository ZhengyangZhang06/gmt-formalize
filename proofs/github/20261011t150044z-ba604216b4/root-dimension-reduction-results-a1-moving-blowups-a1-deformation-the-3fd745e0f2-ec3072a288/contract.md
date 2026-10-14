<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.shell_series-a1 -->

## Theorem `Submission.dimred_mbl_dtsd_sh_shell_series`

Assume, as hypotheses of the statement, (S) (verbatim the frozen Lean type of the selected node's resolved dependency with key support_calculus, the support calculus of currents on ℝ^P): for all P, n ∈ ℕ, (i) if E ⊆ ℝ^P is closed and X ∈ 𝒟_n(ℝ^P) satisfies X(ω) = 0 for every ω ∈ 𝒟ⁿ(ℝ^P) whose tsupport is disjoint from E, then spt X ⊆ E; (ii) spt X is closed for every X ∈ 𝒟_n(ℝ^P); (iii) spt(A − B) ⊆ spt A ∪ spt B for A, B ∈ 𝒟_n(ℝ^P); (iv) spt 0 = ∅; (v) spt ∂A ⊆ spt A for A ∈ 𝒟_{n+1}(ℝ^P); and (ML) (verbatim the frozen Lean type of the accepted declaration cmc_fcl_massOn_le_measure_inter, the selected node's resolved dependency with key mass_le_measure): for P, d ∈ ℕ, any U ⊆ ℝ^P, X ∈ 𝒟_d(U), a measure μ, ξ : ℝ^P → Λ_d and sets E, V ⊆ ℝ^P, if |ξ(x)(α)| ≤ |α| for every d-covector α for μ-a.e. x and X(ω) = ∫_E ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟^d(U), then M_V(X) ≤ μ(E ∩ V). Let P, k ∈ ℕ, X ∈ 𝒟_k(ℝ^P), A, Y : ℕ → 𝒟_k(ℝ^P), μ a measure on ℝ^P, ξ : ℝ^P → Λ_k, d : ℝ^P → ℝ and r : ℕ → ℝ. Assume: μ is a finite measure; ξ is μ-a.e. strongly measurable; for μ-a.e. x, |ξ(x)(α)| ≤ |α| for every k-covector α; μ(ℝ^P \ spt X) = 0; d is continuous; r is strictly decreasing (StrictAnti); μ({d < r_j}) → 0 as j → ∞; X(ω) = ∫ ξ(x)(ω(x)) dμ(x), A_j(ω) = ∫_{d<r_j} ξ(x)(ω(x)) dμ(x) (for every j), Y_0(ω) = X(ω) − A_0(ω) and Y_{j+1}(ω) = A_j(ω) − A_{j+1}(ω) (for every j), for every ω ∈ 𝒟^k(ℝ^P). Then, for every ω ∈ 𝒟^k(ℝ^P) and j ∈ ℕ: (a) Y_0(ω) = ∫_{r_0≤d} ξ(x)(ω(x)) dμ(x) and Y_{j+1}(ω) = ∫_{r_{j+1}≤d<r_j} ξ(x)(ω(x)) dμ(x), the domains being {x : r_0 ≤ d(x)} and {x : r_{j+1} ≤ d(x) ∧ d(x) < r_j}; (b) Σ_j Y_j(ω) = X(ω) (HasSum (j ↦ Y_j(ω)) (X(ω))); (c) spt Y_j ⊆ spt X ∩ {x : r_j ≤ d(x)} and spt A_j ⊆ spt X; (d) M(Y_0) ≤ μ(ℝ^P) and M(Y_{j+1}) ≤ μ({d < r_j}). Conventions (as in the frozen contract and SimonGMT Chapter06): ℝ^P = Euclid P (EuclideanSpace ℝ (Fin P)). For U ⊆ ℝ^P, 𝒟^k(U) = TestFormOn U k (smooth k-forms on ℝ^P whose compact tsupport lies in U) and 𝒟_k(U) = GeometricCurrentOn U k; X(ω) is the value of X on ω; X − Y is the contract subtraction, (X − Y)(ω) = X(ω) − Y(ω) (definitional); 0 is the zero current; ∂X = X.boundary with ∂X(η) = X(dη) (GeometricCurrentOn.boundary_apply); currents with equal values are equal (GeometricCurrentOn.ext). Λ_k = MultiVector P k (continuous linear functionals on k-covectors) and |α| = covectorEuclideanNorm α (Euclidean coefficient norm of a covector). M_G(X) = X.massOn G ∈ [0, ∞] is the supremum of ENNReal.ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x (massAdmissibleOn U k G); M(X) = X.mass = M_U(X); boundaryMassOn X G = M_G(∂X) if k ≥ 1 and 0 if k = 0. spt X = X.support = U \ X.zeroRegion, where X.zeroRegion is the union of the open W with compact closure contained in U on which X vanishes (X(ω) = 0 whenever tsupport ω ⊆ W). Integrals ∫_E g dμ are Bochner integrals over μ⌞E; {d < t} abbreviates {x : d(x) < t}.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.shell_series-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7097

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_mbl_dtsd_sh_shell_series`

```lean
(∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support)) → (∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V)) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (A Y : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (d : Euclid P → ℝ) (r : ℕ → ℝ), IsFiniteMeasure μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → μ X.supportᶜ = 0 → Continuous d → StrictAnti r → Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), A j ω = ∫ x in {x | d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = X ω - A 0 ω) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = A j ω - A (j + 1) ω) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω)) ∧ (∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (A j).support ⊆ X.support) ∧ (Y 0).mass ≤ μ univ ∧ (∀ j, (Y (j + 1)).mass ≤ μ {x | d x < r j})
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1.shell_series-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 6, 7, 10(a)–(b), 11 and 13 of the parent-supplied proof of the selected node dimred_mbl_dtsd_shell_decomposition, stated for a general current represented by a finite measure (the parent applies it to (T, μ_T, ξ, A_{r_j}, W_j) and to (∂T, μ_∂, ξ_∂, B_{r_j}, D_j)); Simon, Introduction to GMT, Ch. 6, §5, proof of the deformation theorem 5.1, displays (8)–(10) (book/chapter-06.txt lines 1725–1740). Sibling used: EB = eval_mass_bound (cmr_abs_apply_le_massOn: if M_W(Z) ≠ ∞, tsupport ω ⊆ W and |ω(x)| ≤ c for all x, then |Z(ω)| ≤ c·M_W(Z).toReal).
Notation. For ω ∈ 𝒟^k(ℝ^P) put f_ω(x) := ξ(x)(ω(x)). Put E_0 := {x : r_0 ≤ d(x)} and E_{j+1} := {x : r_{j+1} ≤ d(x) ∧ d(x) < r_j}. As d is continuous, {d < t} is open, {t ≤ d} is closed, and all these sets are Borel (measurableSet_lt, measurableSet_le).
1. (Bound for a test form.) Fix ω ∈ 𝒟^k(ℝ^P). The map x ↦ |ω(x)| is continuous: ω is smooth, hence continuous, and α ↦ |α| = √(Σ_I [I strictly increasing] α(e_{I(1)}, …, e_{I(k)})²) is continuous because each evaluation α ↦ α(v) is continuous (continuous_eval_const) and finite sums, squares and Real.sqrt are continuous. It vanishes outside the compact set tsupport ω (|0| = 0, covectorEuclideanNorm_zero; HasCompactSupport.comp_left). Hence it is bounded (Continuous.bounded_above_of_compact_support): there is c_ω with |ω(x)| ≤ c_ω for every x, and c_ω ≥ |ω(0)| ≥ 0.
2. (Integrability.) f_ω is μ-a.e. strongly measurable, as the image of the pair (ξ, ω), with ξ μ-a.e. strongly measurable and ω continuous, under the continuous evaluation map (L, α) ↦ L(α) (Continuous.comp_aestronglyMeasurable₂ with isBoundedBilinearMap_apply.continuous). For μ-a.e. x, |f_ω(x)| ≤ |ω(x)| ≤ c_ω by the a.e. bound on ξ and step 1. As μ is finite, f_ω is μ-integrable (Integrable.of_bound), hence integrable on every set.
3. ((a) Shell integrals.) j = 0: {d < r_0}ᶜ = {r_0 ≤ d} = E_0, so by integral_add_compl (step 2) Y_0(ω) = X(ω) − A_0(ω) = ∫ f_ω dμ − ∫_{d<r_0} f_ω dμ = ∫_{E_0} f_ω dμ. j + 1: as r_{j+1} < r_j, {d < r_{j+1}} ⊆ {d < r_j}, and {d < r_j} \ {d < r_{j+1}} = {r_{j+1} ≤ d ∧ d < r_j} = E_{j+1}; so by setIntegral_sdiff (step 2) Y_{j+1}(ω) = ∫_{d<r_j} f_ω dμ − ∫_{d<r_{j+1}} f_ω dμ = ∫_{E_{j+1}} f_ω dμ. This is (a); thus Y_j(ω) = ∫_{E_j} f_ω dμ for every j.
4. (Shell geometry.) E_j ⊆ {r_j ≤ d} for every j. If i < j then j = j′ + 1 with j′ ≥ i, and E_j ⊆ {d < r_{j′}} ⊆ {d < r_i} since r is decreasing. Hence for i < j no x lies in E_i ∩ E_j (it would satisfy r_i ≤ d(x) < r_i): the E_j are pairwise disjoint Borel sets.
5. ((d) Masses.) By ML with U := ℝ^P, E := E_j and V := ℝ^P (the a.e. bound on ξ and the formula of step 3), M(Y_j) = M_{ℝ^P}(Y_j) ≤ μ(E_j ∩ ℝ^P) = μ(E_j); likewise, by ML with E := {d < r_j} and the hypothesis on A_j, M(A_j) ≤ μ({d < r_j}). In particular M(Y_0) ≤ μ(E_0) ≤ μ(ℝ^P) and M(Y_{j+1}) ≤ μ(E_{j+1}) ≤ μ({d < r_j}) because E_{j+1} ⊆ {d < r_j}. This is (d).
6. (Evaluation bound.) Let Z ∈ 𝒟_k(ℝ^P) and G ⊆ ℝ^P with M(Z) ≤ μ(G). Then M(Z) ≤ μ(G) < ∞ (μ finite), so EB with U = W := ℝ^P, r := c_ω (tsupport ω ⊆ ℝ^P, step 1) gives |Z(ω)| ≤ c_ω·M(Z).toReal ≤ c_ω·μ(G).toReal (ENNReal.toReal_mono, c_ω ≥ 0).
7. (Summability.) By step 4 and countable additivity (measure_iUnion), Σ_j μ(E_j) = μ(⋃_j E_j) ≤ μ(ℝ^P) < ∞, so (μ(E_j).toReal)_j is summable (ENNReal.summable_toReal). By steps 5 and 6, |Y_j(ω)| ≤ c_ω·μ(E_j).toReal, so (Y_j(ω))_j is summable (Summable.of_norm_bounded).
8. (Partial sums.) By induction on N, Σ_{j=0}^{N} Y_j(ω) = X(ω) − A_N(ω): for N = 0 this is the hypothesis on Y_0, and Σ_{j=0}^{N+1} Y_j(ω) = (X(ω) − A_N(ω)) + (A_N(ω) − A_{N+1}(ω)) = X(ω) − A_{N+1}(ω) (Finset.sum_range_succ).
9. (A_N(ω) → 0.) By steps 5 and 6, |A_N(ω)| ≤ c_ω·μ({d < r_N}).toReal. Since μ({d < r_N}) → 0 and toReal is continuous at 0 (ENNReal.tendsto_toReal), c_ω·μ({d < r_N}).toReal → c_ω·0 = 0, so A_N(ω) → 0 (squeeze_zero_norm).
10. ((b) HasSum.) By steps 8 and 9, Σ_{j<N+1} Y_j(ω) = X(ω) − A_N(ω) → X(ω) as N → ∞; shifting the index (tendsto_add_atTop_iff_nat 1), the partial sums Σ_{j<N} Y_j(ω) tend to X(ω). As (Y_j(ω))_j is summable (step 7), Summable.hasSum_iff_tendsto_nat gives HasSum (j ↦ Y_j(ω)) (X(ω)). This is (b).
11. (Vanishing lemma.) Since μ(ℝ^P \ spt X) = 0, μ-a.e. x lies in spt X (measure_eq_zero_iff_ae_notMem). Let G be Borel, F ⊆ ℝ^P with G ⊆ F, and ω ∈ 𝒟^k(ℝ^P) with tsupport ω disjoint from spt X ∩ F. For μ⌞G-a.e. x we have x ∈ G (ae_restrict_mem) and x ∈ spt X (ae_restrict_of_ae), hence x ∈ spt X ∩ F, x ∉ tsupport ω, ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and f_ω(x) = ξ(x)(0) = 0. Hence ∫_G f_ω dμ = 0 (integral_eq_zero_of_ae).
12. ((c) Supports.) spt X is closed by S (ii) and {r_j ≤ d} is closed, so K_j := spt X ∩ {r_j ≤ d} is closed. If tsupport ω is disjoint from K_j, then Y_j(ω) = ∫_{E_j} f_ω dμ = 0 by step 11 with G := E_j ⊆ F := {r_j ≤ d} (step 4); so spt Y_j ⊆ K_j by S (i). If tsupport ω is disjoint from spt X = spt X ∩ ℝ^P, then A_j(ω) = ∫_{d<r_j} f_ω dμ = 0 by step 11 with G := {d < r_j} and F := ℝ^P; so spt A_j ⊆ spt X by S (i) (spt X closed). This is (c). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration `theorem Submission.dimred_mbl_dtsd_sh_shell_series : T := by` followed by the tactic block below, where T is this child's frozen Lean type (field lean_statement) verbatim, was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308. It was placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`) and uses the sibling declaration Submission.cmr_abs_apply_le_massOn (eval_mass_bound) (available as a declaration of its frozen type). The antecedents of the statement are hypotheses of the theorem, so no other DAG declaration is used. The comparator solution `exact Submission.dimred_mbl_dtsd_sh_shell_series` closes the frozen challenge type, and `#print axioms` reports only propext, Classical.choice and Quot.sound beyond those sibling declarations.

```lean
  intro hS hML P k X A Y μ ξ d r hμ hξm hξb hnull hd hr htend hX hA hY0 hYs
  have hdm : Measurable d := hd.measurable
  -- Step 1: the integrand `x ↦ ξ x (ω x)` is bounded, a.e. strongly measurable, integrable
  have hcont : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Continuous (ω : DifferentialForm (Euclid P) k) := fun ω => ω.property.1.1.continuous
  have hnormcont : Continuous (fun α : Covector (Euclid P) k => covectorEuclideanNorm α) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ite_true]; exact (continuous_eval_const _).pow 2
    · simp only [hI, ite_false]; exact continuous_const
  have hbound : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ c : ℝ,
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c := by
    intro ω
    obtain ⟨c, hc⟩ := (hnormcont.comp (hcont ω)).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k))
    exact ⟨c, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hc x)⟩
  have hfm : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω =>
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P k) (α : Covector (Euclid P) k) => L α)
      isBoundedBilinearMap_apply.continuous hξm (hcont ω).aestronglyMeasurable
  have hfi : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω => by
    obtain ⟨c, hc⟩ := hbound ω
    exact Integrable.of_bound (hfm ω) c
      (hξb.mono fun x hx => by rw [Real.norm_eq_abs]; exact (hx _).trans (hc x))
  -- Step 2: the shell integral formulas
  have hlt : ∀ j, MeasurableSet {x | d x < r j} := fun j => measurableSet_lt hdm measurable_const
  have hge : ∀ j, MeasurableSet {x | r j ≤ d x} := fun j => measurableSet_le measurable_const hdm
  have hY0' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro ω
    rw [hY0, hX, hA, ← integral_add_compl (hlt 0) (hfi ω)]
    have h : {x | d x < r 0}ᶜ = {x | r 0 ≤ d x} := by ext x; simp
    rw [h]; ring
  have hYs' : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j},
        ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    have hsub : {x | d x < r (j + 1)} ⊆ {x | d x < r j} :=
      fun x hx => lt_trans hx (hr (Nat.lt_succ_self j))
    have hset : {x | d x < r j} \ {x | d x < r (j + 1)} = {x | r (j + 1) ≤ d x ∧ d x < r j} := by
      ext x; simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]; exact and_comm
    rw [hYs, hA, hA, ← setIntegral_sdiff (hlt (j + 1)) (hfi ω).integrableOn hsub, hset]
  -- the shells as one family
  obtain ⟨E, hE0, hEs⟩ : ∃ E : ℕ → Set (Euclid P), E 0 = {x | r 0 ≤ d x} ∧
      ∀ i, E (i + 1) = {x | r (i + 1) ≤ d x ∧ d x < r i} :=
    ⟨fun j => match j with
      | 0 => {x | r 0 ≤ d x}
      | i + 1 => {x | r (i + 1) ≤ d x ∧ d x < r i}, rfl, fun _ => rfl⟩
  have hEm : ∀ j, MeasurableSet (E j) := by
    intro j
    cases j with
    | zero => rw [hE0]; exact hge 0
    | succ i => rw [hEs]; exact (hge (i + 1)).inter (hlt i)
  have hEge : ∀ j, E j ⊆ {x | r j ≤ d x} := by
    intro j
    cases j with
    | zero => rw [hE0]
    | succ i => rw [hEs]; exact fun x hx => hx.1
  have hElt : ∀ i j, i < j → E j ⊆ {x | d x < r i} := by
    intro i j hij
    cases j with
    | zero => omega
    | succ j =>
      rw [hEs]
      exact fun x hx => lt_of_lt_of_le hx.2 (hr.antitone (by omega))
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r i ≤ d x from hEge i hxi) (not_le.2 (hElt i j h hxj))
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r j ≤ d x from hEge j hxj) (not_le.2 (hElt j i h hxi))
  have hYE : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y j ω = ∫ x in E j, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    cases j with
    | zero => rw [hE0]; exact hY0' ω
    | succ i => rw [hEs]; exact hYs' i ω
  -- Step 3: masses (ML)
  have hmassY : ∀ j, (Y j).massOn univ ≤ μ (E j) := fun j =>
    (hML P k univ (Y j) μ ξ (E j) univ hξb (hYE j)).trans (measure_mono inter_subset_left)
  have hmassA : ∀ j, (A j).massOn univ ≤ μ {x | d x < r j} := fun j =>
    (hML P k univ (A j) μ ξ _ univ hξb (hA j)).trans (measure_mono inter_subset_left)
  -- Step 4: evaluation bound (EB + ML)
  have hEB : ∀ (Z : GeometricCurrentOn (univ : Set (Euclid P)) k) (S : Set (Euclid P))
      (ω : TestFormOn (univ : Set (Euclid P)) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c) →
      Z.massOn univ ≤ μ S → |Z ω| ≤ c * (μ S).toReal := by
    intro Z S ω c hc hZ
    have hne : Z.massOn univ ≠ ∞ := (hZ.trans_lt (measure_lt_top μ S)).ne
    have h0c : 0 ≤ c := (covectorEuclideanNorm_nonneg _).trans (hc 0)
    calc |Z ω| ≤ c * (Z.massOn univ).toReal :=
          Submission.cmr_abs_apply_le_massOn P k univ univ Z ω c hne (subset_univ _) hc
      _ ≤ c * (μ S).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top μ S) hZ) h0c
  -- Step 5: HasSum
  have hpart : ∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (N : ℕ),
      ∑ j ∈ Finset.range (N + 1), Y j ω = X ω - A N ω := by
    intro ω N
    induction N with
    | zero => simp [hY0]
    | succ N ih => rw [Finset.sum_range_succ, ih, hYs]; ring
  have hsum : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω) := by
    intro ω
    obtain ⟨c, hc⟩ := hbound ω
    have hsumE : ∑' j, μ (E j) ≠ ∞ := by
      rw [← measure_iUnion hdisj hEm]; exact measure_ne_top μ _
    have hsummable : Summable (fun j => Y j ω) := by
      refine Summable.of_norm_bounded ((ENNReal.summable_toReal hsumE).mul_left c) (fun j => ?_)
      rw [Real.norm_eq_abs]; exact hEB (Y j) (E j) ω c hc (hmassY j)
    rw [hsummable.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
    simp only [hpart]
    have hbd : ∀ n, ‖A n ω‖ ≤ c * (μ {x | d x < r n}).toReal := fun n => by
      rw [Real.norm_eq_abs]; exact hEB (A n) _ ω c hc (hmassA n)
    have hto : Tendsto (fun n => c * (μ {x | d x < r n}).toReal) atTop (𝓝 0) := by
      have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend).const_mul c
      simpa using h
    simpa using tendsto_const_nhds.sub (squeeze_zero_norm hbd hto)
  -- Step 6: supports (S(i), S(ii))
  have hae : ∀ᵐ x ∂μ, x ∈ X.support := by
    have h := measure_eq_zero_iff_ae_notMem.1 hnull
    exact h.mono fun x hx => by simpa using hx
  have hvanish : ∀ (S F : Set (Euclid P)) (ω : TestFormOn (univ : Set (Euclid P)) k),
      MeasurableSet S → S ⊆ F →
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (X.support ∩ F) →
      ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ = 0 := by
    intro S F ω hSm hSF hdisj
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hae] with x hxS hxX
    have hx : x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
      fun h => Set.disjoint_left.1 hdisj h ⟨hxX, hSF hxS⟩
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hsptY : ∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x} := by
    intro j
    refine (hS P k).1 _ _ (((hS P k).2.1 X).inter (isClosed_le continuous_const hd))
      (fun ω hω => ?_)
    rw [hYE j]
    exact hvanish (E j) _ ω (hEm j) (hEge j) hω
  have hsptA : ∀ j, (A j).support ⊆ X.support := by
    intro j
    refine (hS P k).1 _ _ ((hS P k).2.1 X) (fun ω hω => ?_)
    rw [hA j]
    exact hvanish _ univ ω (hlt j) (subset_univ _) (by rwa [inter_univ])
  refine ⟨hY0', hYs', hsum, hsptY, hsptA, (hmassY 0).trans (measure_mono (subset_univ _)),
    fun j => (hmassY (j + 1)).trans (measure_mono ?_)⟩
  rw [hEs]
  exact fun x hx => hx.2
```

## Key steps

1. Each test form is bounded, |ω(x)| ≤ c_ω, so f_ω = ξ(ω) is μ-a.e. strongly measurable, bounded and μ-integrable.
2. integral_add_compl and setIntegral_sdiff give Y_j(ω) = ∫_{E_j} ξ(ω) dμ over the half-open shells E_j.
3. The E_j are pairwise disjoint Borel sets; ML gives M(Y_j) ≤ μ(E_j) and M(A_j) ≤ μ({d < r_j}).
4. EB with ML: |Y_j(ω)| ≤ c_ω μ(E_j) and |A_N(ω)| ≤ c_ω μ({d < r_N}); Σ μ(E_j) ≤ μ(ℝ^P) < ∞ gives summability.
5. Partial sums telescope to X(ω) − A_N(ω) → X(ω), hence HasSum.
6. μ is carried by spt X, so the integrands vanish a.e. when tsupport ω misses spt X ∩ {r_j ≤ d}; S (i), (ii) give the supports.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db, mathlib_commit 25730c7c); git rev-parse HEAD (b4d606db); git -C .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n "def boundaryMassOn|structure IMRep|def IMRep.Represents|def IsIntegerMultiplicity|def IMRep.measure|def IMRep.action|instance : Sub \(GeometricCurrentOn|def CompactlyContained|abbrev MultiVector" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (lines 48, 61, 79, 83, 88, 92, 96, 120, 127)`
- `rg -n "isOpen_zeroRegion|boundary_boundary|massOn_mono|le_massOn|zero_apply|boundary_apply" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (GeometricCurrentOn.zero_apply, boundary_apply, boundary_boundary in Currents.lean 317/333/365; massOn_mono, le_massOn in Mass.lean 81/90; isOpen_zeroRegion in CurrentLocalEquality.lean 119)`
- `rg -n "theorem integral_add_compl|theorem setIntegral_sdiff|theorem summable_toReal|theorem measure_iUnion|theorem strictAnti_nat_of_succ_lt|theorem tendsto_pow_atTop_nhds_zero_of_lt_one|theorem integral_eq_zero_of_ae|theorem integral_zero_measure|theorem tendsto_add_atTop_iff_nat|theorem measure_eq_zero_iff_ae_notMem" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib (all found)`
- `rg -n -i -l "shell|dyadic|good_radius|goodRadius" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT -g "*.lean" (no match, exit 1); rg -n -i "theorem .*slice|def .*slice" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT -g "*.lean" (only the specification definitions IsSlice in Ch06 Contract/Submission line 129, not imported by Ch07, and SlicesAreRectifiable in Ch03 line 262)`
- `rg -n "dimred_mbl_dtsd_sh_" .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/.. (no match, exit 1); python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json (2138 nodes): no lean_name equals a fresh name or starts with dimred_mbl_dtsd_sh_; the reused names are accepted nodes with byte-identical frozen types`
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: the selected frozen type is byte-identical to the twin node's; the twin's ten child types (decomposition-v1.json of the twin node directory) are reused verbatim; the six resolved dependencies of the selected node have frozen types byte-identical to the twin's six; no accepted node other than the twin's unaccepted children carries any of the seven new types`
- `sed of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _render_parent_supplied_natural) and inherited.py (cited, cited_inherited); python3 -I check with that cited() that no new child proof, key step or this ledger names a not-yet-accepted dependency of the selected node or of its ancestors`
- `lake-env lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/EndToEnd.lean (the twin's verified file renamed to this branch's names, accepted ML proof of commit 1041782e inlined; #print axioms: children only propext, Classical.choice, Quot.sound; selected theorem additionally only the two unaccepted resolved dependencies); python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/compare_types.py (all declared types byte-identical to the frozen ones)`
- `lake-env lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/AssemblyAx.lean (selected type from the ten child and six dependency types as axioms); lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/isolated/Iso_*.lean (each new child with only its declared siblings as axioms, then the comparator solution exact Submission.X)`
- `python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/build_challenges.py with the verifier's child_modules(contract mode) and lean GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/chal/Challenge_*.lean (11 files, 0 errors, one sorry warning each); python3 -I GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/scripts/validate.py (runtime and verifier validate_lean_statement: all accepted unchanged)`
- `git show ae810e9b/ea5c1199/7a706164/1041782e:GMT/Ch07/Submission.lean + #print axioms, compiled with lean (errors 0; propext, Classical.choice, Quot.sound only)`
- `sed -n 1700,1800p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon 6.5.1 displays (8)–(10) at lines 1725–1740)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-303188e8d1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-691b18cd91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b75b9802b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_shell_decomposition_split/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_shell_decomposition_decomposition/types.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

Pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. The snapshot project has no shell, dyadic or good-radius declaration; "slice" occurs there only in the specification definitions IsSlice (Ch06, not imported by Ch07) and SlicesAreRectifiable (Ch03), so no snapshot lemma can replace a child. The fresh prefix dimred_mbl_dtsd_sh_ occurs nowhere in the project, Mathlib, SimonGMT or the DAG. Every Mathlib and SimonGMT lemma that the child proofs cite exists at the pinned revisions. The twin node's audited split applies verbatim, because its frozen type and its six resolved-dependency types are byte-identical to the selected node's. Its seven new child types are reused unchanged under fresh names, since its own child names are reserved and unaccepted. Its three reused declarations are accepted with identical types and recompile from their accepted commits with standard axioms. In this session:
- the children's proofs and the assembly compile;
- each new child compiles alone with only its declared siblings;
- the comparator challenge modules elaborate, and both statement validators accept every type unchanged;
- the assembly proves the exact selected type from the child and dependency types;
- no new child proof, key step or this ledger cites a not-yet-accepted inherited prerequisite.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
