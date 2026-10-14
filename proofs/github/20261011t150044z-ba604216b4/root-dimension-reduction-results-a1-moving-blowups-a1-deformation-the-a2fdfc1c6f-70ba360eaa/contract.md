<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1 -->

## Theorem `Submission.dimred_mbl_dt_lipschitz_pushforward_homotopy`

Assume, as hypotheses of the statement, (VO) for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0 (this is the frozen type of Submission.dtc_vanish_off_support); (MR) for U open and an IMRep R representing T ∈ 𝒟_n(U), M_W(T) = R.measure(W) for every open W (it follows from the frozen type of Submission.dor_imrep_massOn_eq_measure_and_support by taking the first conjunct under the binders, and is byte-identical to the frozen type of the accepted Submission.cmc_massOn_eq_imRep_measure); (REP) for U open and T ∈ 𝒟_n(U) with M_W(T) < ∞ for every open W ⊂⊂ U there are a Borel measure μ (μ(ℝ^P ∖ U) = 0, finite on compact subsets of U) and ξ (μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for all x, α) with M_W(T) = μ(W) for open W, T(ω) = ∫ξ(ω)dμ, and, if also M_W(∂T) < ∞ for open W ⊂⊂ U, μ(E) = 0 whenever Hⁿ(E) = 0 (the first conjunct of the frozen type of Submission.dimred_mbl_current_foundations); (IMC) the conjunction of (a) locality of approximate tangent spaces: for U open and Borel M ⊆ M' ⊆ U with Hⁿ(M' ∩ K) < ∞ for compact K ⊆ U, Hⁿ-a.e. on M the approximate tangent spaces of M and M' coincide; (b) the restriction (M ∩ E, θ, ξ) of an IMRep to a Borel set E is an IMRep representing some current; (c) A − B is integer multiplicity for integer multiplicity A, B (U open); (d) |R.orient(x)(α)| ≤ |α| for Hⁿ-a.e. x in the carrier of an IMRep R (the second conjunct of the frozen type of Submission.dimred_mbl_current_foundations). These antecedents are written into the statement so that the child needs no declaration outside its own subtree; the parent discharges them from its resolved dependencies dtc_vanish_off_support, dor_imrep_massOn_eq_measure_and_support, dimred_mbl_current_foundations and dimred_mbl_slice_mass_bounds. For every P ∈ ℕ there are operations push_k(F, X) ∈ 𝒟_k(ℝ^P) and homot_k(F, G, X) ∈ 𝒟_{k+1}(ℝ^P) (k ∈ ℕ, F, G : ℝ^P → ℝ^P, X ∈ 𝒟_k(ℝ^P), domain univ) such that, calling X normal with compact support (NC) when spt X is compact, M(X) < ∞ and boundaryMassOn X univ < ∞ (= M(∂X) for k ≥ 1, 0 for k = 0), for all Λ ∈ ℝ≥0, all Λ-Lipschitz F, G, F', G' and all NC X, Y of degree k: (1) push_k(id, X) = X; (2) push_k(F, X − Y) = push_k(F, X) − push_k(F, Y) and homot_k(F, G, X − Y) = homot_k(F, G, X) − homot_k(F, G, Y); (3) if F = F' and G = G' on spt X then push_k(F, X) = push_k(F', X) and homot_k(F, G, X) = homot_k(F', G', X); (4) M(push_k(F, X)) ≤ Λ^k M(X), spt push_k(F, X) ⊆ F(spt X), M(homot_k(F, G, X)) ≤ δ(2Λ)^k M(X) whenever δ ∈ ℝ and |F(x) − G(x)| ≤ δ for x ∈ spt X, and spt homot_k(F, G, X) ⊆ {F(x) + t(G(x) − F(x)) : x ∈ spt X, t ∈ [0, 1]}; (5) for X ∈ 𝒟_{k+1}(ℝ^P) with compact support, M(X) < ∞, M(∂X) < ∞ and Λ-Lipschitz F, G: ∂push_{k+1}(F, X) = push_k(F, ∂X), push_{k+1}(G, X) − push_{k+1}(F, X) − homot_k(F, G, ∂X) = ∂homot_{k+1}(F, G, X), and if X is integer multiplicity then push_{k+1}(F, X) and homot_{k+1}(F, G, X) are integer multiplicity; (6) for X ∈ 𝒟_0(ℝ^P) with compact support and finite mass and Λ-Lipschitz F, G, push_0(G, X) − push_0(F, X) = ∂homot_0(F, G, X).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5033

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5912

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6947, https://github.com/ZhengyangZhang06/gmt-formalize/issues/986, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6961, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6974, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4595, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7020, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7032, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7041

## Lean problem

Declaration: `Submission.dimred_mbl_dt_lipschitz_pushforward_homotopy`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ P : ℕ, ∃ (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), (∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F F' X.support → EqOn G G' X.support → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (push k F X).support ⊆ F '' X.support ∧ (∀ δ : ℝ, (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ (homot k F G X).support ⊆ {y : Euclid P | ∃ x ∈ X.support, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (push (k + 1) F X) ∧ IsIntegerMultiplicity (homot (k + 1) F G X))) ∧ ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) 0), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → push 0 G X - push 0 F X = (homot 0 F G X).boundary
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Parts A (A1–A4) and B (B1–B5) of the parent proof with the multilinear facts (L0)–(L3) (Simon Ch. 6, 2.17–2.29 and 3.3–3.9: product with [[0,1]], homotopy formula and mass estimate, Lipschitz push-forward, integrality of push-forwards), packaged as two operators. Differences from the parent's text, all needed only for the packaging used by the sibling dimred_mbl_dt_skeleton_deformation:
 - A4(f) of the parent assumes G − F bounded; here a compactly supported cut-off χ in the straight-line homotopy removes that assumption (only [0,1] × spt X matters, as the parent notes);
 - B3 is used with O = ℝ^P and globally Lipschitz F only (the case B4 needs). The parent's application of B3 to the locally Lipschitz ψ on ℝ^P ∖ L*(a) in E4 is replaced in the sibling dimred_mbl_dt_skeleton_deformation by summing the integer multiplicity shell contributions with the sibling dimred_mbl_dt_im_series (IMS), so B1's refinement clause for an open set O and B4's parametrization-independence remark are not needed;
 - the closing combination step of B3 is the sibling IMS;
 - Part C below defines the two operators and checks the six conjuncts.

Conventions. (VO), (MR), (REP), (IMC) are the four displayed hypotheses of the statement. IMS is the sibling theorem dimred_mbl_dt_im_series, applied to (VO), (MR), (IMC). Currents are on univ in some ℝ^N = Euclid N; 𝒟_k(ℝ^N) are k-currents and 𝒟^k(ℝ^N) test k-forms. |α| is the Euclidean coefficient norm of a covector, ‖ω‖ := sup_x|ω(x)|, and for a k-vector ζ (a continuous linear functional on k-covectors) |ζ| := sup{ζ(α) : |α| ≤ 1}. NC_k(ℝ^N) is the set of X ∈ 𝒟_k(ℝ^N) with compact support, M(X) < ∞ and, if k ≥ 1, M(∂X) < ∞ (the statement's hypothesis IsCompact X.support, X.mass < ∞, boundaryMassOn X univ < ∞). NC is closed under differences: spt(X − Y) ⊆ spt X ∪ spt Y, M(X − Y) ≤ M(X) + M(Y), and for degree ≥ 1, ∂(X − Y) = ∂X − ∂Y (GeometricCurrentOn.ext) and M(∂(X − Y)) ≤ M(∂X) + M(∂Y) (directly from the definitions). |X(ω)| ≤ M(X)‖ω‖ for every current (for ε > 0, ±ω/(‖ω‖ + ε) is admissible, so ±X(ω) ≤ (‖ω‖ + ε)M(X); let ε ↓ 0). The zero current is integer multiplicity (empty carrier, multiplicity 0, orientation 0). If ω_j → 0 in the test-form topology then ‖ω_j‖ → 0 (the 0-th derivatives converge uniformly), so a linear functional bounded by a multiple of ‖·‖ is a current.

1. Multilinear algebra (parent (L0)–(L3)).
(L0) For a k-covector β, k!|β|² = Σ_{i_1,…,i_k}β(e_{i_1},…,e_{i_k})² =: ‖β‖²_HS (each increasing tuple occurs k! times up to sign, tuples with repeats vanish). ‖·‖_HS is the Hilbert–Schmidt norm of the multilinear form, hence invariant under orthogonal changes of basis, and so are |·| and the dual norm on k-vectors.
(L1) For linear A : ℝ^N → ℝ^{N'} and a k-covector β on ℝ^{N'}, |A^#β| ≤ ‖A‖^k|β|; dually |Λ_kAζ| ≤ ‖A‖^k|ζ|, where ⟨β, Λ_kAζ⟩ := ⟨A^#β, ζ⟩. By (L0) it suffices to bound ‖·‖_HS; replacing one slot of a multilinear form γ by A multiplies its HS norm by at most ‖A‖ (for fixed other arguments Σ_iγ(Ae_i, …)² = |Aᵀg|² ≤ ‖A‖²|g|², g the vector representing γ(·, …)); do this k times.
(L2) For a 1-covector β' and a k-covector γ, |β' ∧ γ| ≤ |β'||γ| (rotate so that β' = |β'|e¹ and use (L0)); likewise |ι_vβ| ≤ |v||β|, so |v ∧ ζ| ≤ |v||ζ| for a vector v and a k-vector ζ, where ⟨β, v ∧ ζ⟩ := ⟨ι_vβ, ζ⟩.
(L3) If τ_1,…,τ_k are orthonormal then ζ := τ_1 ∧ ⋯ ∧ τ_k (⟨α, ζ⟩ := α(τ_1,…,τ_k)) has |ζ| = 1. If A : ℝᵏ → ℝ^N is linear and injective, A = OS (S := (AᵀA)^{1/2}, O := AS^{−1} an isometric embedding), so Λ_kA(e_1 ∧ ⋯ ∧ e_k) = det(S)·Oe_1 ∧ ⋯ ∧ Oe_k, |Λ_kA(e)| = √det(AᵀA) =: JA, and Λ_kA(e)/JA is a unit simple k-vector orienting A(ℝᵏ). If A is not injective, Λ_kA(e) = 0 = JA. Two unit simple k-vectors orienting the same k-plane differ by a sign (the change of orthonormal basis has determinant ±1). By (IMC)(d), the orientation ξ of an IMRep satisfies |ξ(x)(α)| ≤ |α| a.e.

Part A. Normal currents with compact support.

2. A0 (Representation; parent "Conventions"). Let X ∈ 𝒟_k(ℝ^N) have compact support and M(X) < ∞. (REP) with U = univ gives a Borel measure μ_X and ξ_X with μ_X(W) = M_W(X) for open W, |ξ_X(x)(α)| ≤ |α| for all x, α, and X(ω) = ∫ξ_X(ω) dμ_X. Then μ_X(ℝ^N) = M(X) < ∞, and μ_X(ℝ^N ∖ spt X) = M_{ℝ^N∖spt X}(X) = 0 because every admissible ω supported in the open set ℝ^N ∖ spt X has X(ω) = 0 by (VO). Hence |X(ω)| ≤ ∫|ω| dμ_X, and X(ω) = 0 whenever ω vanishes on spt X.

3. A1 (Smooth push-forward). Let X ∈ 𝒟_k(ℝ^N) have compact support and F : ℝ^N → ℝ^{N'} be C^∞. For ω ∈ 𝒟^k(ℝ^{N'}) put (F^#ω)(x) := ω(F(x)) ∘ DF(x) (Lean: (ω (F x)).compContinuousLinearMap (fderiv ℝ F x)), a smooth k-form, and F_#X(ω) := X(ζF^#ω) for ζ ∈ C_c^∞(ℝ^N) equal to 1 on a neighbourhood of spt X; this does not depend on ζ (two choices differ by a form vanishing near spt X; (VO)).
 - F_#X is a current. Below A1 is only applied to currents X of finite mass, and then this follows from the bound |F_#X(ω)| ≤ sup_{spt X}‖DF‖^kM(X)‖ω‖ of the last bullet and the criterion in the Conventions (in general it follows from the chain and Leibniz rules: if ω_j → 0 in 𝒟^k(ℝ^{N'}) then ζF^#ω_j → 0 in 𝒟^k(ℝ^N), all derivatives of F being bounded on spt ζ).
 - ∂F_#X = F_#∂X: d commutes with F^# (SimonGMT exteriorDerivativeOn_pullbackFormWithin with U = V = univ), so ∂F_#X(ω) = X(ζd(F^#ω)) = X(d(ζF^#ω)) − X(dζ ∧ F^#ω). The last term vanishes by (VO) since dζ = 0 near spt X, and X(d(ζF^#ω)) = ∂X(ζF^#ω) = F_#∂X(ω) (ζ = 1 near spt ∂X ⊆ spt X).
 - spt F_#X ⊆ F(spt X): if tsupport ω ∩ F(spt X) = ∅, then F^#ω vanishes on the open set F^{-1}(ℝ^{N'} ∖ tsupport ω) ⊇ spt X, so tsupport(ζF^#ω) ∩ spt X = ∅ and F_#X(ω) = 0 by (VO). F(spt X) is compact, and a current vanishing on all forms supported in the complement of a closed set E has support in E (each point outside E has a ball with compact closure disjoint from E).
 - If M(X) < ∞, A0 gives F_#X(ω) = ∫⟨ω(F(x)), Λ_kDF(x)ξ_X(x)⟩ dμ_X(x). Hence by (L1), |F_#X(ω)| ≤ ∫‖DF‖^k|ω∘F| dμ_X and M(F_#X) ≤ sup_{spt X}‖DF‖^kM(X).

4. A2 (Product with [[0,1]]). Work directly in ℝ^{N+1} = Euclid (N + 1), writing its points as (t, x) with t the coordinate of index 0 and x ∈ ℝ^N the remaining ones (a linear isometry ℝ × ℝ^N ≅ ℝ^{N+1}, so no transport of currents is needed); e₀ := ∂_t, ι(v) := (0, v) (v ∈ ℝ^N), π(t, x) := x, i_s(x) := (s, x). For a (k+1)-form ω on ℝ^{N+1} let ω₁(t,x) be the k-covector v ↦ ω(t,x)(e₀, ιv_1,…,ιv_k) on ℝ^N, and ω₀ := ω − dt ∧ π^#ω₁ (dt-free; its restriction to ι-vectors at (t, x) is (i_t^#ω)(x)). For each fixed t, ω₁(t,·) is a test k-form on ℝ^N (smooth, support in the projection of tsupport ω). For X ∈ 𝒟_k(ℝ^N) with compact support and M(X) < ∞ (the only case used below) put
 ([[0,1]] × X)(ω) := ∫_0^1 X(ω₁(t,·)) dt, ({s} × X)(ω) := X(i_s^#ω).
By A0 and Fubini, ([[0,1]] × X)(ω) = ∫_0^1∫⟨ω(t,x), e₀ ∧ ξ_X(x)⟩ dμ_X dt (this equals the parent's X(∫_0^1ω₁(t,·) dt); the t-integral form avoids discussing smoothness of parametric integrals), so by (L2) |([[0,1]] × X)(ω)| ≤ M(X)‖ω‖: it is a current with M([[0,1]] × X) ≤ M(X); likewise {s} × X is a current with M({s} × X) ≤ M(X). Supports: if tsupport ω misses [0,1] × spt X then for each t ∈ [0,1] the form ω₁(t,·) has support disjoint from spt X, so X(ω₁(t,·)) = 0 by (VO); hence spt([[0,1]] × X) ⊆ [0,1] × spt X, and similarly spt({s} × X) ⊆ {s} × spt X. Boundary: writing ω = dt ∧ π^#ω₁ + ω₀, one has d(dt ∧ π^#ω₁) = −dt ∧ d_xω₁ and dω₀ = dt ∧ ∂_tω₀ + d_xω₀, so, as k-forms on ℝ^N for each fixed t, (dω)₁(t,·) = ∂_t(i_t^#ω) − d(ω₁(t,·)). Applying X for each t and integrating: ∫_0^1X(∂_t(i_t^#ω)) dt = ∫∫_0^1∂_t ξ_X((i_t^#ω)(x)) dt dμ_X = X(i_1^#ω) − X(i_0^#ω) (A0, Fubini, fundamental theorem of calculus), and ∫_0^1X(d(ω₁(t,·))) dt = ∫_0^1∂X(ω₁(t,·)) dt = ([[0,1]] × ∂X)(ω) (k ≥ 1, ∂X of finite mass). Hence
 ∂([[0,1]] × X) = {1} × X − {0} × X − [[0,1]] × ∂X (k ≥ 1; for k = 0 the last term is absent).
Hence for X ∈ NC_k(ℝ^N), [[0,1]] × X ∈ NC_{k+1}(ℝ^{N+1}) with M(∂([[0,1]] × X)) ≤ 2M(X) + M(∂X).

5. A3 (Smooth homotopy formula). Let X ∈ NC_k(ℝ^N) and let H : ℝ × ℝ^N → ℝ^{N'} be C^∞ with H(t, x) = F(x) + t(G(x) − F(x)) on a neighbourhood of [0,1] × spt X, F, G smooth. Since ∂H_# = H_#∂ (A1 in ℝ^{N+1}) and H_#({s} × X) = (H ∘ i_s)_#X (as i_s^#(ζH^#ω) = (ζ ∘ i_s)(H ∘ i_s)^#ω and ζ ∘ i_s = 1 near spt X for s ∈ [0,1]) with H ∘ i_1 = G, H ∘ i_0 = F near spt X, A2 gives
 G_#X − F_#X = ∂H_#([[0,1]] × X) + H_#([[0,1]] × ∂X) (last term absent for k = 0).
Mass: near [0,1] × spt X, DH(t,x)e₀ = (G − F)(x) and DH(t,x)(0,v) = ((1 − t)DF(x) + tDG(x))v, so Λ_{k+1}DH(e₀ ∧ ζ) = (G − F)(x) ∧ Λ_k((1 − t)DF + tDG)(x)ζ, and by A1, (L1), (L2)
 M(H_#([[0,1]] × X)) ≤ ∫|G − F|(‖DF‖ + ‖DG‖)^k dμ_X ≤ sup_{spt X}|G − F|·sup_{spt X}(‖DF‖ + ‖DG‖)^k·M(X).

6. A4 (Lipschitz push-forward). Let X ∈ NC_k(ℝ^N) and F : ℝ^N → ℝ^{N'} Lipschitz with constant Λ. F_σ := F ∗ φ_σ (componentwise mollification with a fixed standard mollifier) is C^∞ with Lip F_σ ≤ Λ (so ‖DF_σ‖ ≤ Λ) and |F_σ − F| ≤ Λσ. Apply A3 to F_σ, F_τ (H := F_σ + t(F_τ − F_σ), smooth):
 |(F_σ)_#X(ω) − (F_τ)_#X(ω)| ≤ sup|F_σ − F_τ|((2Λ)^kM(X)‖dω‖ + (2Λ)^{k−1}M(∂X)‖ω‖) → 0 (σ, τ ↓ 0).
So F_#X(ω) := lim_{σ↓0}(F_σ)_#X(ω) exists. Properties:
 (a) |F_#X(ω)| ≤ Λ^kM(X)‖ω‖ (A1 for F_σ). So F_#X is linear and sequentially continuous, i.e. a current, with M(F_#X) ≤ Λ^kM(X).
 (b) ∂F_#X = F_#∂X (A1 for F_σ; ∂X ∈ NC_{k−1} since ∂∂X = 0).
 (c) If F is C^∞ (and Lipschitz), F_#X agrees with A1: DF_σ → DF and F_σ → F uniformly on spt X, so by the representation in A1, (F_σ)_#X(ω) → F_#X(ω) (A1 sense). In particular id_#X(ω) = X(ζω) = X(ω) by (VO).
 (d) spt F_#X ⊆ F(spt X): if tsupport ω ∩ F(spt X) = ∅ then, by compactness, tsupport ω ∩ F_σ(spt X) = ∅ for small σ, so (F_σ)_#X(ω) = 0 (A1).
 (e) If F, G are Lipschitz with constants ≤ Λ and |F − G| ≤ δ on spt X, then |F_#X(ω) − G_#X(ω)| ≤ δ((2Λ)^kM(X)‖dω‖ + (2Λ)^{k−1}M(∂X)‖ω‖) (apply A3 to F_σ, G_σ, with sup_{spt X}|F_σ − G_σ| ≤ δ + 2Λσ, and let σ ↓ 0). In particular F_#X depends only on F|spt X. It is linear in X: F_#(X − Y) = F_#X − F_#Y for X, Y ∈ NC_k (true for each F_σ with a common cut-off ζ).
 (f) Homotopy formula. Let F, G be Λ-Lipschitz, X ∈ NC_k(ℝ^N), and Ĥ : ℝ × ℝ^N → ℝ^{N'} any Lipschitz map with Ĥ(t,x) = F(x) + t(G(x) − F(x)) on [0,1] × spt X. Then
 G_#X − F_#X = ∂Ĥ_#([[0,1]] × X) + Ĥ_#([[0,1]] × ∂X) (last term absent for k = 0), and
 M(Ĥ_#([[0,1]] × X)) ≤ sup_{spt X}|G − F|·(2Λ)^kM(X).
 Proof. By (e) in ℝ^{N+1} (applied to [[0,1]] × X, [[0,1]] × ∂X ∈ NC, whose supports lie in [0,1] × spt X), the right sides do not depend on the choice of Ĥ. Choose χ ∈ C_c^∞(ℝ^N), 0 ≤ χ ≤ 1, χ = 1 near spt X, and s ∈ C^∞(ℝ) with s(t) = t on [−1, 2] and s constant outside [−2, 3] (the parent's bounded smooth s). H_σ(t,x) := F_σ(x) + s(t)χ(x)(G_σ − F_σ)(x) is C^∞ and globally Lipschitz with a constant independent of σ ≤ 1 (∂_tH_σ = s'(t)χ(G_σ − F_σ) and D_xH_σ = DF_σ + s(t)(Dχ ⊗ (G_σ − F_σ) + χ(DG_σ − DF_σ)) are bounded, because s, s', χ, Dχ are bounded and G_σ − F_σ is bounded on the compact spt χ uniformly in σ ≤ 1); H_σ = F_σ + t(G_σ − F_σ) near [0,1] × spt X, and H_σ → H := F + s(t)χ(G − F) uniformly, H Lipschitz and equal to F + t(G − F) on [0,1] × spt X. By A3 for F_σ, G_σ:
 (G_σ)_#X − (F_σ)_#X = ∂H_{σ#}([[0,1]] × X) + H_{σ#}([[0,1]] × ∂X), M(H_{σ#}([[0,1]] × X)) ≤ sup_{spt X}|G_σ − F_σ|(2Λ)^kM(X).
 As σ ↓ 0 the left side converges weakly to G_#X − F_#X (definition); by (c), (e) in ℝ^{N+1}, H_{σ#}Y → H_#Y weakly for Y = [[0,1]] × X, [[0,1]] × ∂X; boundaries converge weakly (SimonGMT WeaklyConvergesOn.boundary); and lower semicontinuity of mass (SimonGMT WeaklyConvergesOn.massOn_le_liminf) gives the estimate with sup_{spt X}|G − F|.

Part B. Integrality (parent B1–B5; Simon 3.3–3.9 and 3.2(2)). Throughout, X = τ(M, θ, ξ) is integer multiplicity in 𝒟_k(ℝ^N), k ≥ 1, X ∈ NC_k. Replacing M by M ∩ spt X ((IMC)(b); by (MR) on the open set W = ℝ^N ∖ spt X and (VO), θHᵏ(M ∖ spt X) = M_W(X) = 0), we may assume M ⊆ spt X, so Hᵏ(M) ≤ ∫_Mθ dHᵏ = M(X) < ∞ (MR). Modifying ξ on an Hᵏ⌞M-null set we may take ξ Borel (this changes neither the action nor the a.e. orientation property). Hᵏ := μHE[k] and Lᵏ is Lebesgue measure.
7. B1 (Parametrization). There are countably many compact A_i ⊆ ℝᵏ, Lipschitz G_i : ℝᵏ → ℝ^N and κ_i > 0 such that G_i is differentiable at every u ∈ A_i with DG_i(u) injective, |G_i(u) − G_i(v)| ≥ κ_i|u − v| on A_i, the sets G_i(A_i) ⊆ M are pairwise disjoint, and Hᵏ(M ∖ ⋃_iG_i(A_i)) = 0.
 Proof: by SimonGMT CountablyRectifiable, M ⊆ M₀ ∪ ⋃_jF_j(ℝᵏ), Hᵏ(M₀) = 0, F_j Lipschitz. By Rademacher (Mathlib LipschitzWith.ae_differentiableAt) the differentiability set D_j of F_j is Borel with null complement, and Hᵏ(F_j(ℝᵏ ∖ D_j)) = 0 (Mathlib LipschitzOnWith.hausdorffMeasure_image_le). On Z_j := {u ∈ D_j : DF_j(u) not injective} the Jacobian vanishes, so Hᵏ(F_j(Z_j)) = 0 (SimonGMT area_image_criticalSet_eq_zero). Let E_j := (D_j ∖ Z_j) ∩ F_j^{-1}(M). For injective A choose K_A > 0 with |Au| ≥ |u|/K_A (Mathlib LinearMap.exists_antilipschitzWith) and r(A) := 1/(2K_A) (r(A) := 1 otherwise). Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt covers E_j by disjoint Borel sets E_j ∩ t_l on which F_j approximates A_l = DF_j(y_l) (y_l ∈ E_j, so A_l injective) with constant r(A_l); there |F_j(u) − F_j(v)| ≥ (2K_{A_l})^{-1}|u − v|. Enumerate the pieces (E_i, G_i, κ_i) and make the images disjoint inductively, E'_i := E_i ∖ G_i^{-1}(⋃_{i'<i}G_{i'}(E'_{i'})), which is Borel by Lusin–Souslin (Mathlib MeasurableSet.image_of_continuousOn_injOn). By inner regularity write each E'_i, up to an Lᵏ-null set (whose image is Hᵏ-null), as a countable disjoint union of compact sets.
8. B2 (Tangent planes of pieces). Let A ⊆ ℝᵏ be compact and G : ℝᵏ → ℝ^N Lipschitz with |G(u) − G(v)| ≥ κ|u − v| on A (κ > 0) and G differentiable on A. Then for Lᵏ-a.e. u ∈ A, V := DG(u)(ℝᵏ) is k-dimensional and HasApproximateTangentSpaceAt k (G(A)) (G(u)) V.
 Proof: let u be a Lebesgue density point of A and a Lebesgue point of 1_A·JG (JG := √det(DGᵀDG)). Density gives points v ∈ A with v − u = rw/|w| + o(r), so |DG(u)w| ≥ κ|w| and JG(u) > 0. Let x := G(u) and f ∈ C_c(ℝ^N) with spt f ⊆ B_ρ(0). The injective area formula (SimonGMT injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum) and the scaling of Hᵏ give ∫_{blowUpMap x r '' G(A)} f dHᵏ = ∫_{ℝᵏ}1_A(u + rw)f((G(u + rw) − G(u))/r)JG(u + rw) dw. The integrand vanishes for |w| ≥ ρ/κ (bi-Lipschitz on A). On B_{ρ/κ}, (G(u + rw) − G(u))/r → DG(u)w uniformly (differentiability at u), 1_A(u + r·) → 1 and 1_A(u + r·)JG(u + r·) → JG(u) in L¹. So the integral tends to ∫f(DG(u)w)JG(u) dw = ∫_Vf dHᵏ (area formula for the linear map DG(u)).
 Consequence: by B1 and (IMC)(a) (G_i(A_i) ⊆ M Borel, Hᵏ(M) < ∞; G_i bi-Lipschitz on A_i, so null sets correspond), for Hᵏ-a.e. x ∈ G_i(A_i) the approximate tangent space T_xM exists and equals DG_i(u)(ℝᵏ), u = G_i^{-1}(x). By the orientation field and (L3), for a.e. u ∈ A_i,
 (B2′) ξ(G_i(u)) = s_i(u)Λ_kDG_i(u)(e)/JG_i(u), e := e_1 ∧ ⋯ ∧ e_k, s_i(u) ∈ {1, −1} Borel.
9. B3 (The integral current is integer multiplicity), for Lipschitz F : ℝ^N → ℝ^{N'}. H_i := F ∘ G_i : ℝᵏ → ℝ^{N'} is globally Lipschitz, differentiable a.e. (Rademacher). At a.e. u ∈ A_i, DH_i(u) = A_u ∘ DG_i(u) with A_u := DH_i(u) ∘ DG_i(u)^{-1} on DG_i(u)(ℝᵏ) = T_{G_iu}M (the parent's d^MF(G_iu)), and ‖A_u‖ ≤ Lip F because |DH_i(u)w| = lim_{t↓0}|F(G_i(u + tw)) − F(G_i(u))|/t ≤ Lip F·|DG_i(u)w|. Hence, by (L1), JH_i(u) := |Λ_kDH_i(u)(e)| = |Λ_kA_u(Λ_kDG_i(u)(e))| ≤ Lip(F)^kJG_i(u), and by the area formula Σ_i∫_{A_i}θ_iJH_i du ≤ Lip(F)^kΣ_i∫_{A_i}θ_iJG_i du = Lip(F)^k∫_Mθ dHᵏ = Lip(F)^kM(X) (θ_i := θ ∘ G_i). Define
 (★) Φ_F(ω) := Σ_i∫_{A_i}θ_is_i⟨ω(H_i(u)), Λ_kDH_i(u)(e)⟩ du,
 an absolutely convergent series. By the area formula for G_i on A_i, (B2′) and the chain rule Λ_kA_u(Λ_kDG_i(e)) = Λ_kDH_i(e), (★) is the parent's Φ_F(ω) = ∫_Mθ⟨ω(F(x)), Λ_k(d^MF(x))ξ(x)⟩ dHᵏ; taking (★) as the definition avoids discussing the measurability of d^MF on M. Where DH_i(u) is not injective, Λ_kDH_i(u)(e) = 0. Partition A_i^+ := {u ∈ A_i : H_i differentiable at u, DH_i(u) injective} as in B1 into compact pieces A_{il} (up to an Lᵏ-null set) on which H_i is injective with |H_i(u) − H_i(v)| ≥ κ_{il}|u − v|. Put N_{il} := H_i(A_{il}) (compact), g_{il} := (θ_is_i) ∘ (H_i|A_{il})^{-1} ∈ ℤ ∖ {0} (Borel: H_i|A_{il} is a homeomorphism onto N_{il}), and η_{il} := (Λ_kDH_i(e)/JH_i) ∘ (H_i|A_{il})^{-1} (a unit simple k-vector by (L3)). The injective area formula for H_i on A_{il} gives
 Φ_F(ω) = Σ_{i,l}Φ_{il}(ω), Φ_{il}(ω) := ∫_{N_{il}}g_{il}⟨ω, η_{il}⟩ dHᵏ, Σ_{i,l}∫_{N_{il}}|g_{il}| dHᵏ = Σ_i∫_{A_i}θ_iJH_i du ≤ Lip(F)^kM(X) < ∞.
 Each Φ_{il} is an integer multiplicity current, (N_{il}, |g_{il}|, sign(g_{il})η_{il}) being an IMRep: N_{il} is compact and countably k-rectifiable (contained in the range of the globally Lipschitz map H_i : ℝᵏ → ℝ^{N'}; SimonGMT countablyRectifiable_range and CountablyRectifiable.mono), with Hᵏ(N_{il}) ≤ ∫|g_{il}| < ∞; the multiplicity is a positive integer and the orientation is Borel; and by B2 applied to H_i on A_{il}, the approximate tangent space of N_{il} at Hᵏ-a.e. point H_i(u) is DH_i(u)(ℝᵏ), which η_{il} orients. Φ_{il} is linear with |Φ_{il}(ω)| ≤ ‖ω‖∫|g_{il}| dHᵏ, hence a current (the action of that IMRep) with M(Φ_{il}) ≤ ∫|g_{il}| dHᵏ, so Σ_{il}M(Φ_{il}) < ∞. Enumerate the countably many pairs (i, l) by ℕ, padding with zero currents. IMS (degree k = (k − 1) + 1) gives an integer multiplicity current S with S(ω) = Σ_{il}Φ_{il}(ω) = Φ_F(ω) for every ω — this is the parent's closing step of B3. Hence Φ_F is (the action of) an integer multiplicity current.
10. B4 (Identification): F_#X (A4) = Φ_F.
 Lemma (weak continuity of Jacobians, parent B4; stated for globally Lipschitz maps, which is all that is used: H_{i,σ} = F_σ ∘ G_i and H_i = F ∘ G_i). Let H_σ, H : ℝᵏ → ℝ^{N'} be Lipschitz with sup_σLip H_σ < ∞ and H_σ → H uniformly on ℝᵏ. Then for ω ∈ 𝒟ᵏ(ℝ^{N'}) and w ∈ L¹(ℝᵏ), ∫_{ℝᵏ}w(H_σ^#ω)(e) du → ∫_{ℝᵏ}w(H^#ω)(e) du (apply it with w := θ_is_i1_{A_i}).
 Proof: (H^#ω)(e) = Σ_Jω_J(H)det D(H^{j_1},…,H^{j_k}) (a.e.) is bounded by a constant independent of σ, so, approximating w in L¹(ℝᵏ) by functions in C_c^∞(ℝᵏ), we may take w ∈ C_c^∞(ℝᵏ); since ω_J(H_σ) → ω_J(H) uniformly and the determinants are uniformly bounded, it suffices to show ∫c det Dv_σ → ∫c det Dv for c := wω_J(H) (continuous with compact support) and Lipschitz v_σ → v uniformly with bounded constants. Prove by induction on r ≤ k that ∫β ∧ dv_σ^1 ∧ ⋯ ∧ dv_σ^r → ∫β ∧ dv^1 ∧ ⋯ ∧ dv^r for every continuous compactly supported (k − r)-form β (r = 0 trivial). For smooth β, with R_σ := dv_σ^2 ∧ ⋯ ∧ dv_σ^r (R likewise for v), integrate by parts: ∫β ∧ dv_σ^1 ∧ R_σ = ±∫v_σ^1dβ ∧ R_σ; this is valid for Lipschitz functions by mollification, because the a.e. derivative of a Lipschitz function is its weak derivative (Mathlib LipschitzWith.integral_lineDeriv_mul_eq), so D(v ∗ φ_δ) = (Dv) ∗ φ_δ → Dv a.e. and boundedly (Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable). Then ∫v_σ^1dβ ∧ R_σ − ∫v^1dβ ∧ R = ∫(v_σ^1 − v^1)dβ ∧ R_σ + ∫v^1dβ ∧ (R_σ − R) → 0 by uniform convergence and the induction hypothesis for the continuous form v^1dβ. General continuous β follow by uniform approximation and the uniform bounds.
 Now (F_σ)_#X(ω) = X(ζF_σ^#ω) = ∫_Mθ⟨ω(F_σ(x)), Λ_kDF_σ(x)ξ(x)⟩ dHᵏ (A1's definition and R.Represents X applied to the test form ζF_σ^#ω, with ζ = 1 on M ⊆ spt X) = Σ_i∫_{A_i}θ_is_i(H_{i,σ}^#ω)(e) du with H_{i,σ} := F_σ ∘ G_i (area formula for G_i, (B2′), chain rule DH_{i,σ} = DF_σ(G_i) ∘ DG_i on A_i). Each term converges to ∫_{A_i}θ_is_i(H_i^#ω)(e) du by the lemma (w = θ_is_i1_{A_i} ∈ L¹ since JG_i ≥ κ_i^k on A_i and ∫_{A_i}θ_iJG_i < ∞), and the i-th term is bounded by ‖ω‖Lip(F)^k∫_{G_i(A_i)}θ dHᵏ (as ‖DF_σ‖ ≤ Lip F), which is summable. By dominated convergence for series the limit is Σ_i∫_{A_i}θ_is_i(H_i^#ω)(e) du = Φ_F(ω) by (★). Hence F_#X = Φ_F is integer multiplicity.
11. B5 (Products). [[0,1]] × X = τ((0,1) × M, θ ∘ pr, e₀ ∧ ξ) is integer multiplicity in ℝ^{N+1} (coordinates (t, x) as in A2).
 Product-null lemma: if Hᵏ(Z) = 0 then H^{k+1}(I × Z) = 0 for every bounded interval I (cover Z by sets C_j with 0 < d_j := max(diam C_j, ε2^{−j}) < 1 and Σ_jd_j^k < 2ε, enlarging degenerate sets, and cover I × C_j by ⌈|I|/d_j⌉ sets of diameter ≤ √2d_j; the sum of (diameter)^{k+1} is ≤ c(|I| + 1)Σ_jd_j^k). So the null parts of M and M ∖ ⋃G_i(A_i) do not matter.
 The maps Ĝ_i(t,u) := (t, G_i(u)) (Lipschitz on ℝ^{k+1}) are injective, bi-Lipschitz on [0,1] × A_i (constant min(1, κ_i)) and differentiable there with JĜ_i(t,u) = JG_i(u); by the area formula H^{k+1}⌞((0,1) × G_i(A_i)) is the product of L¹⌞(0,1) and Hᵏ⌞G_i(A_i), so with the product-null lemma H^{k+1}((0,1) × M) = Hᵏ(M) < ∞. By B2 (for Ĝ_i on the compact set [0,1] × A_i) the approximate tangent space of [0,1] × G_i(A_i) at H^{k+1}-a.e. point (t, G_i(u)) is ℝe₀ ⊕ DG_i(u)(ℝᵏ). Apply (IMC)(a) twice (all sets Borel with finite H^{k+1}-measure): to (0,1) × G_i(A_i) ⊆ [0,1] × G_i(A_i), and to (0,1) × G_i(A_i) ⊆ (0,1) × M. Since (0,1) × (M ∖ ⋃_iG_i(A_i)) is H^{k+1}-null, it follows that H^{k+1}-a.e. on (0,1) × M the approximate tangent space is ℝe₀ ⊕ T_xM, oriented by the unit simple (k+1)-vector e₀ ∧ ξ (if ξ = ±τ_1 ∧ ⋯ ∧ τ_k then e₀ ∧ ξ = ±e₀ ∧ τ_1 ∧ ⋯ ∧ τ_k with (e₀, τ) orthonormal). Fubini and A2 give ∫_{(0,1)×M}θ⟨ω, e₀ ∧ ξ⟩ dH^{k+1} = ∫_0^1∫_Mθ⟨ω₁(t,·), ξ⟩ dHᵏ dt = ([[0,1]] × X)(ω). The remaining IMRep fields (Borel carrier, countable rectifiability via Ĝ_i, integer multiplicity θ ∘ pr ≥ 1, local integrability ∫θ = M(X) < ∞, Borel orientation) are immediate.
12. Summary (used in C6). If Y ∈ NC_k(ℝ^N) is integer multiplicity (k ≥ 1) and F : ℝ^N → ℝ^{N'}, Ĥ : ℝ^{N+1} → ℝ^{N'} are Lipschitz, then F_#Y and Ĥ_#([[0,1]] × Y) are integer multiplicity (B3, B4; and B5 with A2 for the normality of [[0,1]] × Y, then B3, B4 in ℝ^{N+1}).

Part C. The operators (N = N' = P).
13. C1 (Definitions). For k ∈ ℕ, F, G : ℝ^P → ℝ^P and X ∈ 𝒟_k(ℝ^P):
 push k F X := F_#X (A4) if F is Lipschitz and X ∈ NC_k, and 0 otherwise;
 homot k F G X := Ĥ_X#([[0,1]] × X) if F, G are Lipschitz, X ∈ NC_k and spt X ≠ ∅, and 0 otherwise, where Ĥ_X(t,x) := F(x) + c(t)χ_X(x)(G(x) − F(x)), c(t) := min(1, max(0, t)), χ_X(x) := max(0, 1 − dist(x, spt X)).
 For spt X ≠ ∅, Ĥ_X is Lipschitz on ℝ × ℝ^P: χ_X is 1-Lipschitz, bounded and vanishes outside the compact set {dist(·, spt X) ≤ 1}, on which G − F is bounded and Lipschitz; c is 1-Lipschitz and bounded; and a product a·b with a bounded, Lipschitz, supported in a compact set where b is bounded, and b Lipschitz, is Lipschitz. Also Ĥ_X(t,x) = F(x) + t(G(x) − F(x)) on [0,1] × spt X. By A4(e) in ℝ^{P+1} (spt([[0,1]] × X) ⊆ [0,1] × spt X), homot k F G X = Ĥ_#([[0,1]] × X) for every Lipschitz Ĥ with this property (C1′). (C1′) also holds when spt X = ∅: then X = 0 by (VO), so both sides are 0.
Fix Λ and Λ-Lipschitz F, G, F', G'; let X, Y ∈ NC_k(ℝ^P).
14. C2 (Identity). push k id X = X by A4(c).
15. C3 (Linearity). push k F (X − Y) = push k F X − push k F Y by A4(e) (X − Y ∈ NC_k). For homot, let χ be a Lipschitz cut-off with compact support equal to 1 on spt X ∪ spt Y ⊇ spt(X − Y), and Ĥ := F + c(t)χ(G − F); by (C1′) all three homotopy currents are Ĥ_# of [[0,1]] × X, [[0,1]] × Y, [[0,1]] × (X − Y), and both [[0,1]] × · (A2) and Ĥ_# (A4(e) in ℝ^{P+1}) are linear.
16. C4 (Locality). If F = F' and G = G' on spt X, then push k F X = push k F' X by A4(e) (δ = 0); Ĥ_X (built from F, G) equals F' + t(G' − F') on [0,1] × spt X, so homot k F G X = homot k F' G' X by (C1′).
17. C5 (Mass and support). M(push k F X) ≤ Λ^kM(X) and spt push k F X ⊆ F(spt X) by A4(a), (d). If dist(F(x), G(x)) ≤ δ for x ∈ spt X, then M(homot k F G X) ≤ δ(2Λ)^kM(X) by A4(f) applied with Ĥ_X (if spt X = ∅ then X = 0 and both sides vanish, so δ < 0 is harmless). spt homot k F G X ⊆ Ĥ_X(spt([[0,1]] × X)) ⊆ Ĥ_X([0,1] × spt X) = {F(x) + t(G(x) − F(x)) : x ∈ spt X, t ∈ [0,1]} by A4(d) in ℝ^{P+1}.
18. C6 (Degree k + 1: boundary, homotopy formula, integrality). Let X ∈ 𝒟_{k+1}(ℝ^P) have compact support, M(X) < ∞, M(∂X) < ∞, so X ∈ NC_{k+1} and ∂X ∈ NC_k. If spt X = ∅ then X = 0 and ∂X = 0 by (VO), every push/homot term below is 0 (push of the zero current is 0 by A4, homot of a current with empty support is 0 by definition), and the identities hold trivially (0 is integer multiplicity); assume spt X ≠ ∅. ∂push (k+1) F X = push k F ∂X by A4(b). Apply A4(f) with Ĥ := Ĥ_X, which also agrees with F + t(G − F) on [0,1] × spt ∂X, so Ĥ_X#([[0,1]] × ∂X) = homot k F G ∂X by (C1′): push (k+1) G X − push (k+1) F X = ∂homot (k+1) F G X + homot k F G ∂X, i.e. push (k+1) G X − push (k+1) F X − homot k F G ∂X = ∂(homot (k+1) F G X) (GeometricCurrentOn.ext; the contract's subtraction is pointwise). If X is integer multiplicity, push (k+1) F X and homot (k+1) F G X are integer multiplicity by 12.
19. C7 (Degree 0). For X ∈ 𝒟_0(ℝ^P) with compact support and finite mass (boundaryMassOn X univ = 0 by convention): if spt X = ∅ then X = 0 by (VO) and both sides are 0; otherwise A4(f) with k = 0 and Ĥ := Ĥ_X gives push 0 G X − push 0 F X = ∂homot 0 F G X.
20. C8. The pair (push, homot) of C1 satisfies the six conjuncts of the statement by C2, C3, C4, C5, C6 and C7. ∎

## Key steps

1. Representation of finite-mass currents with compact support ((REP), (VO)) and the multilinear estimates (L0)–(L3).
2. A1–A3: smooth push-forward with cut-off, boundary, support and mass bound; [[0,1]] × X with ∂([[0,1]] × X) = {1} × X − {0} × X − [[0,1]] × ∂X; smooth homotopy formula with mass estimate.
3. A4: Lipschitz push-forward as the limit of mollified push-forwards; mass and support bounds, boundary commutation, the locality estimate (e), and the homotopy formula for Lipschitz maps via cut-off homotopies and lower semicontinuity of mass.
4. B1–B5: Lipschitz parametrization of the carrier, approximate tangent planes of bi-Lipschitz pieces via the area formula, integer pieces of Φ_F summed by IMS, F_#X = Φ_F by weak continuity of Jacobians, integrality of [[0,1]] × X.
5. Part C: push := F_#X, homot := Ĥ_X#([[0,1]] × X) with a cut-off straight-line homotopy (0 when spt X = ∅); verification of identity, linearity, locality, mass/support bounds, homotopy formula, integrality and degree 0.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); git rev-parse HEAD (b4d606db); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -i 'deformation theorem|federer|polyhedral|cubical|skeleton|lipschitz.*push|homotopy' SNAPSHOT/project/GMT -g '*.lean' (only the unproved Ch06 specifications DeformationTheorem and LipschitzPushforwardIntegerMultiplicity with main_theorem := by sorry; Ch07 does not import Ch06)`
- `rg -n -i -l 'federer.?fleming|deformation theorem|polyhedral chain|flat norm' SNAPSHOT/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'dimred_mbl_dt' SNAPSHOT/project SNAPSHOT/mathlib GMT lake-packages-25730c7c/simongmt (no match); python3 scan of RUN/dag.json lean_names (1048 nodes) for the eight proposed names (none)`
- `rg -n 'theorem infEDist_smul₀' SNAPSHOT/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean; rg -n "theorem cthickening_subset_thickening'|theorem cthickening_cthickening_subset|theorem cthickening_subset_of_subset|theorem mem_cthickening_iff|protected theorem _root_.IsCompact.cthickening" SNAPSHOT/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean; rg -n 'theorem map_coord_zero' SNAPSHOT/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean (all found)`
- `rg over lake-packages-25730c7c/mathlib/Mathlib and lake-packages-25730c7c/simongmt/Poincare for every Mathlib/SimonGMT name cited in the eight child proofs (all present, e.g. MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ at Geometry/Euclidean/Volume/Measure.lean:152, LipschitzOnWith.hausdorffMeasure_image_le at MeasureTheory/Measure/Hausdorff.lean:733, LipschitzWith.ae_differentiableAt at Analysis/Calculus/Rademacher.lean:385, area_image_criticalSet_eq_zero at SimonGMT Chapter02/AreaCritical.lean:185)`
- `grep/sed of SimonGMT Chapter06 Currents.lean, Mass.lean, CurrentLocalEquality.lean, Forms.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, ext, zero_apply, boundary, massAdmissibleOn, massOn, mass, le_massOn, covectorEuclideanNorm_neg, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, zeroRegion, support, isOpen_zeroRegion, Covector, DifferentialForm, CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `python3 scans of RUN/dag.json: selected node (decomposing, attempt 2, children []); frozen types of the four resolved dependencies (dtc_vanish_off_support and dor_imrep_massOn_eq_measure_and_support accepted; dimred_mbl_current_foundations and dimred_mbl_slice_mass_bounds decomposing); foundations == (cmc_exists_massRepresentation) ∧ (cmc_imRep_locality_restrict_sub), SL == cmc_slice_mass_bounds, MR == accepted cmc_massOn_eq_imRep_measure (all true); twin cmc_deformation_theorem has the same type and its eight children have these eight types (all decomposing)`
- `python3/cat of this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json and decomposition-scope-v1.json (digest 1445be18…, same as this session), and of the twin's decomposition-v2.json, decomposition-review-receipt-v1/v2.json and its children's decomposition-audit-v1.json`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _overlay_accepted_children), decomposition_scope.py, lean_contract.py and verifier/gmt-compare.py (child_modules, contract_scope); both validate_lean_statement implementations on all eight types`
- `lake env lean /tmp/dmdt2/lean/Types.lean and /tmp/dmdt2/chal/Challenge_<key>.lean for all eight keys (only sorry warnings); lake env lean /tmp/dmdt2/lean/InstCheck.lean (clean); lake env lean /tmp/dmdt2/lean/AssemblyAx.lean (#print axioms dmdt_assembly_check: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-theorem-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-theorem-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-theorem-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-theorem-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-review-receipt-v2.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dmdt2/lean/Types.lean`
- `/tmp/dmdt2/lean/InstCheck.lean`
- `/tmp/dmdt2/lean/Assembly.lean`
- `/tmp/dmdt2/lean/AssemblyAx.lean`
- `/tmp/dmdt2/chal/Challenge_skeleton_retraction.lean`
- `/tmp/dmdt2/chal/Challenge_skeleton_deformation.lean`
- `/tmp/dmdt2/chal/Challenge_face_replacement.lean`

Pins match (project b4d606db, Mathlib 25730c7c, SimonGMT 2b366308), and Submission.lean is byte-identical to the frozen contract. Neither the snapshot project nor Mathlib contains a deformation theorem, Lipschitz push-forward of currents, polyhedral chains or flat norms; the snapshot's Ch06 DeformationTheorem is an unproved specification that Ch07 does not import. All eight obligations are therefore new, and every cited Mathlib/SimonGMT name exists. The parent's resolved dependencies enter as exact antecedents. The eight child types are identical to this node's audited but never-activated v1 and to the twin's twice-audited split. They elaborate in the comparator's challenge form, pass both validators and collide with no DAG name. The Lean assembly proves the exact parent type from the four dependency types and the dilation, skeleton_deformation and face_replacement types, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
