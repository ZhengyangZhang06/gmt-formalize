<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1 -->

## Theorem `Submission.dor_lmb_fcd_pushforward_homotopy`

Conventions: ℝ^P = Euclid P and Hᵈ = μHE[d]. For U ⊆ ℝ^P, 𝒟^d(U) = TestFormOn U d (smooth d-forms on ℝ^P with compact support contained in U) and 𝒟_d(U) = GeometricCurrentOn U d; ∂X = X.boundary (∂X(ω) = X(dω)); X − Y is the contract subtraction (pointwise on test forms). For G ⊆ ℝ^P, M_G(X) = X.massOn G is the supremum of max(X(ω), 0) over ω ∈ 𝒟^d(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x, where |·| is the Euclidean coefficient norm of covectors (covectorEuclideanNorm); M(X) = X.mass = M_U(X). An IMRep R = (M, θ, ξ) in U is the contract structure IMRep U d; R represents X when X(ω) = ∫_M θ⟨ω, ξ⟩ dHᵈ for every ω ∈ 𝒟^d(U), where ⟨ω, ξ⟩(x) = ξ(x)(ω(x)); μ_R = θ·Hᵈ⌞M is R.measure and R.action(β) = ∫_M θ ξ(β) dHᵈ for any d-form β; X is integer multiplicity (IM, IsIntegerMultiplicity X) if some IMRep represents it. X vanishes off a set E if X(ω) = 0 for every ω whose tsupport is disjoint from E. Assume (IMS) the exact frozen statement of dor_lmb_fc_im_series (a resolved dependency of the parent node, not yet accepted, hence taken as an antecedent): for all P, m, every open U ⊆ ℝ^P and IM currents X_r ∈ 𝒟_{m+1}(U) (r ∈ ℕ) with Σ_r M(X_r) ≠ ∞ there is an IM Y ∈ 𝒟_{m+1}(U) with Σ_r X_r(ω) = Y(ω) (HasSum) for every ω ∈ 𝒟^{m+1}(U) and M(Y) ≤ Σ_r M(X_r). For every P ∈ ℕ there are operations push_k(F, X) ∈ 𝒟_k(ℝ^P) and homot_k(F, G, X) ∈ 𝒟_{k+1}(ℝ^P) (k ∈ ℕ, F, G : ℝ^P → ℝ^P, X ∈ 𝒟_k(ℝ^P), domain univ) such that, for every k, Λ ∈ ℝ≥0, Λ-Lipschitz F, G, F', G', compact E ⊆ ℝ^P and IM X, Y ∈ 𝒟_k(ℝ^P) vanishing off E: (1) push_k(id, X) = X; (2) push_k(F, X − Y) = push_k(F, X) − push_k(F, Y) and homot_k(F, G, X − Y) = homot_k(F, G, X) − homot_k(F, G, Y); (3) if F = F' and G = G' on E then push_k(F, X) = push_k(F', X) and homot_k(F, G, X) = homot_k(F', G', X); (4) push_k(F, X) and homot_k(F, G, X) are IM, M(push_k(F, X)) ≤ Λ^k·M(X), push_k(F, X) vanishes off F(E), homot_k(F, G, X) vanishes off {F(x) + t(G(x) − F(x)) : x ∈ E, t ∈ [0, 1]}, and for every δ ∈ ℝ with |F(x) − G(x)| ≤ δ for all x ∈ E, M(homot_k(F, G, X)) ≤ δ(2Λ)^k·M(X) (δ via ENNReal.ofReal); (5) if X ∈ 𝒟_{k+1}(ℝ^P) is IM, vanishes off E and ∂X is IM, then ∂push_{k+1}(F, X) = push_k(F, ∂X) and push_{k+1}(G, X) − push_{k+1}(F, X) − homot_k(F, G, ∂X) = ∂homot_{k+1}(F, G, X). (push_k(F, X) = F_#X and homot_k(F, G, X) = h_#([[(0,1)]] × X) for the affine homotopy h(t, x) = F(x) + t(G(x) − F(x)): Simon 2.17–2.29 with 3.2(2), 3.9.)

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5455

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6424, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/986, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4544, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5835, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8480, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8483, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8485, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8487, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8492, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8496

## Lean problem

Declaration: `Submission.dor_lmb_fcd_pushforward_homotopy`

```lean
(∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ r, IsIntegerMultiplicity (X r)) → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity Y ∧ (∀ ω : TestFormOn U (m + 1), HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass) → ∀ P : ℕ, ∃ (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), (∀ (k : ℕ) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → Y ω = 0) → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → EqOn F F' E → EqOn G G' E → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (E) → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ IsIntegerMultiplicity (homot k F G X) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) ({y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) → homot k F G X ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ ∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → IsIntegerMultiplicity X.boundary → (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) (E) → X ω = 0) → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 2.17–2.29 (products 2.17–2.22, push-forward 2.23 and Remark 2.24, the homotopy formula 2.25 and the mass bound 2.27 for affine homotopies, the Lipschitz push-forward 2.29) and 3.2(2), 3.9 (products and push-forwards of integer multiplicity currents), chapter-06.txt lines from "2.17 Definition" to the proof of 2.29 and from "3.2 Remarks" to 3.9; these are the "Results of the book used by the printed proof" listed in the parent proof for steps 4–6 (the operators ψ_# and h_#([[(0,1)]] × ·)). They are specialized to integer multiplicity currents with compact support, which is all the parent uses (every current it pushes forward is IM: restrictions of T and ∂T, slices, and their differences). Integrality is the sibling IPF = dor_lmb_fcd_im_pushforward (Simon 3.6–3.9 with the identification of the limits of 2.29), applied to the antecedent (IMS). Other dependencies: (C1) = the reused sibling dor_imrep_massOn_eq_measure_and_support; (IMC) = the reused sibling cmc_imRep_locality_restrict_sub. Accepted DAG theorems named below (dpf_rectifiable_bilipschitz_pieces) are not siblings of this node: they may be reused as children if this node is decomposed; otherwise the arguments given here are formalized directly.

Notation. All currents are on univ. A current X ∈ 𝒟_k(ℝ^P) is called admissible if it is IM and vanishes off some compact set. ‖ω‖ := sup_y |ω(y)| (Euclidean coefficient norm). For a C¹ map Φ and a form ω, Φ^#ω(x) := ω(Φ(x)) ∘ DΦ(x) (Lean: (ω (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x)). Hadamard's bound |α(v_1, …, v_k)| ≤ |α||v_1|⋯|v_k| (expand α = Σ_I α_I dy^I in the orthonormal basis of increasing coordinate covectors, so α(v) = Σ_I α_I det(v^I); by Cauchy–Schwarz and Cauchy–Binet, |α(v)|² ≤ |α|²Σ_I det(v^I)² = |α|²det(v_i·v_j) ≤ |α|²Π|v_i|², the last step by Hadamard's inequality) and the form of IMRep orientations ((IMC)(d): ξ(x)(α) = ±α(τ) for an orthonormal frame τ of T_xM) give, for an IMRep R and a C¹ Λ-Lipschitz Φ: |R.action(Φ^#ω)| ≤ Λ^k‖ω‖μ_R(ℝ^P)  (★).

1. Admissible currents and their representations. Let X be admissible, vanishing off the compact set E, and R = (M, θ, ξ) an IMRep of X, μ_R := R.measure.
 (a) μ_R(ℝ^P ∖ E) = 0: by (C1), μ_R(W) = M_W(X) for open W, and every admissible form for W := ℝ^P ∖ E has tsupport disjoint from E. Since θ ≥ 1 on M, Hᵏ(M ∖ E) = 0.
 (b) M(X) = μ_R(ℝ^P) = μ_R(E) ≤ ∫_{M∩E}θ dHᵏ < ∞ (C1 and local integrability on the compact E); in particular R satisfies the hypothesis R.measure univ ≠ ∞ of IPF.
 (c) For every bounded Borel k-form γ that equals a test form ζγ' on a neighbourhood of E: R.action(γ) = X(ζγ'), because the integrands agree Hᵏ-a.e. on M by (a). In particular, if ζ ∈ C_c^∞(ℝ^P) equals 1 on a neighbourhood of E and γ is a C^∞ form, R.action(γ) = X(ζγ); and X(ω) = X(ζω) for test forms ω (the difference (1 − ζ)ω has tsupport disjoint from E).
 (d) Canonical data: fix for each admissible X an IMRep R_X, and let E_X := the support of the measure μ_{R_X} (closed). By (a), E_X ⊆ E for every closed E off which X vanishes, so E_X is compact, μ_{R_X}(ℝ^P ∖ E_X) = 0 (Mathlib Measure.measure_compl_support), and X vanishes off E_X (if tsupport ω ∩ E_X = ∅, the integrand θξ(ω) vanishes μ_{R_X}-a.e.). If E_X = ∅ then X = 0.

2. Smooth approximations and the Lipschitz push-forward (Simon 2.23, 2.24(2), 2.29 with 3.9). For a Λ-Lipschitz F : ℝ^P → ℝ^P let F_j := F ∗ φ_{1/j} (componentwise convolution with a standard mollifier): F_j is C^∞, Λ-Lipschitz (|F_j(x) − F_j(y)| ≤ ∫|F(x − z) − F(y − z)|φ_{1/j}(z) dz ≤ Λ|x − y|), and sup|F_j − F| ≤ Λ/j → 0.
 Definition. For admissible X and Lipschitz F, push k F X := Y_{R_X}(F), where Y_{R_X} is the function given by IPF (applied to (IMS) and to R_X); otherwise push k F X := 0.
 Characterization (Char-push). Let X be admissible vanishing off a compact E, F Λ-Lipschitz, F_j any C^∞ Λ-Lipschitz maps with F_j → F uniformly, and ζ ∈ C_c^∞ equal to 1 near E. Then for every test form ω: push k F X (ω) = lim_j R_X.action(F_j^#ω) = lim_j X(ζF_j^#ω). (IPF's limit clause; then 1(c), ζF_j^#ω being a test form.)
 Note: by IPF's limit clause, the value does not depend on Λ (any admissible Λ for F gives the same limit for the mollified sequence).

3. Products (Simon 2.17–2.22, 3.2(2)). Identify ℝ^{P+1} = Euclid (P + 1) with ℝ × ℝ^P (coordinate 0 is t, e_0 its unit vector). For an admissible X with R_X = (M, θ, ξ) define R̂_X := ((0,1) × M, θ∘pr₂, ξ̂) with ξ̂(t, x)(β) := ξ(x)(β₁(t, x)), where for a (k+1)-covector β at (t, x), β₁(v_1, …, v_k) := β(e_0, (0, v_1), …, (0, v_k)) (ξ̂ = e_0 ∧ ξ). Claim: R̂_X is an IMRep of degree k + 1 in univ ⊆ ℝ^{P+1}, μ_{R̂_X}(ℝ^{P+1}) = μ_{R_X}(ℝ^P) < ∞, and for every bounded Borel (k+1)-form β on ℝ^{P+1}: R̂_X.action(β) = ∫_0^1 R_X.action(β₁(t, ·)) dt.
 Proof. (i) Product-null lemma: if Hᵏ(Z) = 0 then H^{k+1}(I × Z) = 0 for every bounded interval I (cover Z by sets C_j with 0 < d_j := max(diam C_j, ε2^{−j}) and Σd_j^k < 2ε, and I × C_j by ⌈|I|/d_j⌉ sets of diameter ≤ √2 d_j; the sum of (diameter)^{k+1} is ≤ c(|I| + 1)Σ_j d_j^k). (ii) Parametrization (Simon 3.1, Ch. 3, 1.1): there are countably many compact B_i ⊆ ℝᵏ, Lipschitz G_i : ℝᵏ → ℝ^P and κ_i > 0 such that G_i is differentiable with injective derivative at every point of B_i, κ_i|u − v| ≤ |G_i(u) − G_i(v)| on B_i, the sets G_i(B_i) ⊆ M are Borel and pairwise disjoint, and Hᵏ(M ∖ ⋃_iG_i(B_i)) = 0. (This is the accepted DAG theorem dpf_rectifiable_bilipschitz_pieces, with Borel pieces, followed by inner regularity: a Borel piece is, up to an Lᵏ-null set whose Lipschitz image is Hᵏ-null (Mathlib LipschitzOnWith.hausdorffMeasure_image_le), a countable disjoint union of compact sets. Its proof: M ⊆ M₀ ∪ ⋃_jF_j(ℝᵏ) with Hᵏ(M₀) = 0 and F_j Lipschitz; by Rademacher the non-differentiability set of F_j is null and has null image; the image of {DF_j not injective} is null by the area formula (SimonGMT area_image_criticalSet_eq_zero); the rest is cut by Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt into Borel pieces on which F_j is bi-Lipschitz, and the pieces are made disjoint inductively using Mathlib MeasurableSet.image_of_continuousOn_injOn.) Let JG_i := √det(DG_iᵀDG_i). The maps Ĝ_i(t, u) := (t, G_i(u)) are injective and bi-Lipschitz on (0,1) × B_i with Jacobian JĜ_i(t, u) = JG_i(u); the injective area formula (SimonGMT) gives H^{k+1}⌞((0,1) × G_i(B_i)) = L¹⌞(0,1) ⊗ Hᵏ⌞G_i(B_i), and with (i), H^{k+1}⌞((0,1) × M) = L¹⌞(0,1) ⊗ Hᵏ⌞M. The same holds for (I × A) whenever A is a Borel countably k-rectifiable set with locally finite Hᵏ and I an interval, and for dilates and translates of such sets. (iii) (0,1) × M is Borel and countably (k+1)-rectifiable ((0,1) × G_i(ℝᵏ) ⊆ Ĝ_i(ℝ^{k+1}), plus the null set (0,1) × (M ∖ ⋃ G_i(B_i)) by (i)); θ∘pr₂ is a Borel positive integer on it; ξ̂ is measurable; local integrability and the mass identity follow from (ii) and Fubini. (iv) Tangent planes: let x ∈ M be a point where M has approximate tangent space T_xM (Hᵏ-a.e. x) and t ∈ (0,1). The blow-up of (0,1) × M at (t, x) with scale r is ((0,1) − t)/r × (M − x)/r, so by (ii), for f ∈ C_c(ℝ^{P+1}), ∫_{blow-up} f dH^{k+1} = ∫_{((0,1)−t)/r} ∫_{(M−x)/r} f(s, y) dHᵏ(y) ds → ∫_ℝ ∫_{T_xM} f(s, y) dHᵏ(y) ds = ∫_{ℝe_0 ⊕ T_xM} f dH^{k+1} (for each s by the tangent property of M at x, dominated convergence in s, f having compact support). So (0,1) × M has approximate tangent space ℝe_0 ⊕ T_xM at H^{k+1}-a.e. point, and e_0 ∧ ξ(x) is a unit orientation of it when ξ(x) = ±τ_1 ∧ ⋯ ∧ τ_k orients T_xM (e_0, τ is an orthonormal frame). (v) Fubini with (ii) gives the action formula. (For k = 0, M is finite and (0,1) × M is a finite union of open unit segments; (i)–(v) are immediate.)

4. The homotopy operator. For Λ-Lipschitz F, G and admissible X with E_X ≠ ∅, let χ_X(x) := max(0, 1 − infDist x E_X) (1-Lipschitz, = 1 on E_X, vanishing outside a compact set), c(t) := min(1, max(0, t)), and Ĥ(t, x) := F(x) + c(t)χ_X(x)(G(x) − F(x)). Ĥ is Lipschitz on ℝ^{P+1}: χ_X(G − F) is bounded and Lipschitz (G − F is bounded on the compact set where χ_X ≠ 0), and c is bounded and 1-Lipschitz. Define homot k F G X := Y_{R̂_X}(Ĥ) (IPF applied to (IMS) and to R̂_X, which has finite mass by 3); in all other cases (F or G not Lipschitz, X not admissible, or E_X = ∅, i.e. X = 0) put homot k F G X := 0.
 Characterization (Char-homot). Let X be admissible vanishing off a compact E (so E_X ⊆ E), F, G Λ-Lipschitz, F_j, G_j C^∞ Λ-Lipschitz with F_j → F, G_j → G uniformly (e.g. mollifications), h_j(t, x) := F_j(x) + t(G_j(x) − F_j(x)), and for a k'-form ω (k' = k + 1) the C^∞ k-form
 (K_jω)(x)(v_1, …, v_k) := ∫_0^1 ω(h_j(t, x))(G_j(x) − F_j(x), D_xh_j(t, x)v_1, …, D_xh_j(t, x)v_k) dt, D_xh_j = (1 − t)DF_j + tDG_j
 (the interior product with ∂_t of h_j^#ω, integrated in t). Let ζ ∈ C_c^∞ equal 1 near E. Then homot k F G X (ω) = lim_j R_X.action(K_jω) = lim_j X(ζK_jω).
 Proof. Choose s ∈ C^∞(ℝ), bounded with bounded derivative and s(t) = t on [−1, 2], and χ̃ ∈ C_c^∞(ℝ^P), 0 ≤ χ̃ ≤ 1, χ̃ = 1 on a neighbourhood of E. Ĥ_j(t, x) := F_j(x) + s(t)χ̃(x)(G_j(x) − F_j(x)) are C^∞ and Lipschitz with a constant independent of j (∂_tĤ_j = s'(t)χ̃(G_j − F_j) and D_xĤ_j = DF_j + s(t)(Dχ̃ ⊗ (G_j − F_j) + χ̃(DG_j − DF_j)) are bounded, G_j − F_j being uniformly bounded on spt χ̃), and Ĥ_j → Ĥ' := F + s(t)χ̃(G − F) uniformly. Ĥ' = Ĥ on [0,1] × E_X, which contains H^{k+1}-almost all of the carrier (0,1) × M of R̂_X (1(d)); by IPF's locality clause (with a common Lipschitz constant for Ĥ and Ĥ'), Y_{R̂_X}(Ĥ) = Y_{R̂_X}(Ĥ'), and by its limit clause, homot k F G X (ω) = lim_j R̂_X.action(Ĥ_j^#ω). By the action formula of 3, R̂_X.action(Ĥ_j^#ω) = ∫_0^1 R_X.action((Ĥ_j^#ω)₁(t, ·)) dt, and for t ∈ (0,1) and x near E (where χ̃ ≡ 1, s(t) = t) (Ĥ_j^#ω)₁(t, x) is the integrand of K_jω. Fubini (bounded integrand, finite measure) and 1(c) give the claim.

5. Properties (1)–(3). Let Λ, F, G, F', G' be as in the statement and X, Y admissible, vanishing off the compact E.
 (1) Identity: with F_j := id in (Char-push), push k id X (ω) = lim X(ζω) = X(ζω) = X(ω) (1(c)).
 (2) Linearity: X − Y is IM by (IMC)(c) and vanishes off E, so it is admissible. With a common ζ, F_j, G_j in (Char-push) and (Char-homot), push k F (X − Y)(ω) = lim (X − Y)(ζF_j^#ω) = lim X(ζF_j^#ω) − lim Y(ζF_j^#ω) = (push k F X − push k F Y)(ω), and likewise for homot with ζK_jω.
 (3) Locality: if F = F' on E then F = F' Hᵏ-a.e. on the carrier of R_X (1(a)); IPF's locality clause gives push k F X = push k F' X. If moreover G = G' on E, the two maps Ĥ, Ĥ' of 4 (built with the same χ_X) agree on [0,1] × E_X ⊆ [0,1] × E, which contains H^{k+1}-almost all of the carrier of R̂_X; so homot k F G X = homot k F' G' X.

6. Properties (4): integrality, masses, vanishing (Simon 2.27, 2.29, 3.9).
 - push k F X and homot k F G X are IM by IPF (for X = 0 or E_X = ∅ they are 0, which is IM: empty carrier).
 - Mass of push: by (★) and 1(b), |X(ζF_j^#ω)| = |R_X.action(F_j^#ω)| ≤ Λ^k‖ω‖M(X); in the limit |push k F X (ω)| ≤ Λ^k‖ω‖M(X), so M(push k F X) ≤ Λ^k M(X).
 - Vanishing of push off F(E): F(E) is compact; if tsupport ω is disjoint from it, the two sets have positive distance, so for large j, F_j(E) ∩ tsupport ω = ∅ and F_j^#ω = 0 on E; then R_X.action(F_j^#ω) = 0 by 1(a), and push k F X (ω) = 0.
 - Vanishing of homot off h([0,1] × E) = {F x + t(G x − F x) : x ∈ E, t ∈ [0,1]} (compact): if tsupport ω is disjoint from it then, h_j → h uniformly on [0,1] × E, for large j h_j([0,1] × E) ∩ tsupport ω = ∅, so K_jω = 0 on E and homot k F G X (ω) = lim R_X.action(K_jω) = 0.
 - Mass of homot (Simon 2.27): let δ be such that |F(x) − G(x)| ≤ δ for x ∈ E. If E = ∅ then X = 0, homot k F G X (ω) = lim X(ζK_jω) = 0 and the bound is trivial; otherwise δ ≥ 0. For x ∈ E, ‖D_xh_j‖ ≤ (1 − t)Λ + tΛ = Λ and |G_j(x) − F_j(x)| ≤ δ + ε_j with ε_j := sup|G_j − G| + sup|F_j − F| → 0, so by Hadamard and the form of ξ, |ξ(x)(K_jω(x))| ≤ (δ + ε_j)Λ^k‖ω‖ for Hᵏ-a.e. x ∈ M ∩ E, hence |R_X.action(K_jω)| ≤ (δ + ε_j)Λ^k‖ω‖M(X) and |homot k F G X (ω)| ≤ δΛ^k‖ω‖M(X). So M(homot k F G X) ≤ ENNReal.ofReal(δ)·Λ^k·M(X) ≤ ENNReal.ofReal(δ)(2Λ)^k M(X).

7. Property (5): boundary commutation and the homotopy formula (Simon 2.24(1), 2.25). Let X ∈ 𝒟_{k+1} be admissible (vanishing off E) with ∂X IM; ∂X vanishes off E too (∂X(ω) = X(dω), tsupport dω ⊆ tsupport ω), so ∂X is admissible. Fix ζ (= 1 near E) and the mollified F_j, G_j.
 (a) Naturality: d(Φ^#ω) = Φ^#(dω) for C^∞ Φ (SimonGMT exteriorDerivativeOn_pullbackFormWithin with U = univ). Since dζ = 0 near E, X(dζ ∧ γ) = 0 for every smooth γ (its tsupport is disjoint from E). Hence ∂X(ζF_j^#ω) = X(d(ζF_j^#ω)) = X(dζ ∧ F_j^#ω) + X(ζF_j^#(dω)) = X(ζF_j^#(dω)). By (Char-push) for ∂X (degree k) and for X (degree k + 1): push k F (∂X)(ω) = lim ∂X(ζF_j^#ω) = lim X(ζF_j^#(dω)) = push (k+1) F X (dω) = (push (k+1) F X).boundary(ω).
 (b) Cartan's homotopy formula for the smooth homotopy h_j (Simon's derivation of 2.25 from 2.21, 2.22 written on forms): for every C^∞ (k+1)-form ω, G_j^#ω − F_j^#ω = d(K_jω) + K_j(dω). Proof: on ℝ × ℝ^P write h_j^#ω = dt ∧ α_t + β_t with α_t, β_t free of dt; then K_jω = ∫_0^1 α_t dt, β_0 = F_j^#ω, β_1 = G_j^#ω, and h_j^#(dω) = d(h_j^#ω) = dt ∧ (∂_tβ_t − d_xα_t) + d_xβ_t, so K_j(dω) = ∫_0^1(∂_tβ_t − d_xα_t) dt = β_1 − β_0 − d(K_jω) (d_x commutes with ∫dt).
 Hence X(ζG_j^#ω) − X(ζF_j^#ω) = X(ζ d(K_jω)) + X(ζK_j(dω)) = X(d(ζK_jω)) − X(dζ ∧ K_jω) + X(ζK_j(dω)) = ∂X(ζK_jω) + X(ζK_j(dω)). Letting j → ∞ with (Char-push) for X and (Char-homot) for ∂X (degree k, k-forms K_jω) and for X (degree k + 1, applied to dω):
 push (k+1) G X (ω) − push (k+1) F X (ω) = homot k F G (∂X)(ω) + homot (k+1) F G X (dω),
 i.e. push (k+1) G X − push (k+1) F X − homot k F G X.boundary = (homot (k+1) F G X).boundary (GeometricCurrentOn.ext).

8. Conclusion. The operations push and homot of steps 2 and 4 satisfy (1)–(3) by step 5, (4) by step 6 and (5) by step 7, for every P. ∎

## Key steps

1. For IM X vanishing off a compact E, (C1) gives μ_R(ℝ^P ∖ E) = 0 and M(X) = μ_R(ℝ^P) < ∞; R.action of a smooth form equals X of its cut-off.
2. push_k(F, X) := the IM current of IPF for R_X and F; it is lim X(ζF_j^#ω) for mollified F_j (Char-push).
3. The product IMRep R̂_X = ((0,1) × M, θ, e₀ ∧ ξ) in ℝ^{P+1} (product-null lemma, area formula on pieces, blow-ups of products) has action ∫_0^1 R_X.action(β₁(t, ·)) dt.
4. homot_k(F, G, X) := IPF for R̂_X and a cut-off affine homotopy Ĥ; by IPF locality it is lim X(ζK_jω) with K_j the homotopy operator of the smooth affine homotopy (Char-homot).
5. Identity, linearity and locality follow from the characterizations and IPF locality; integrality from IPF; mass bounds from Hadamard's inequality and 2.27; vanishing from uniform convergence.
6. ∂-commutation from d(Φ^#ω) = Φ^#dω, and the homotopy formula from Cartan's formula G_j^#ω − F_j^#ω = dK_jω + K_jdω, both passed to the limit.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -l -i "latticeFace|DeformationTheorem|deformation theorem|skeleton|retraction" local-references/123e8435b4a2469b/project -g "*.lean" (only GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean)`
- `rg -n "latticeFace|def DeformationTheorem|IsLatticeChain|pushforward|homotopy|Poincar" local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `rg -n "theorem hausdorffMeasure_smul₀|theorem integral_map_equiv|theorem restrict_map|exists_disjoint_subfamily_covering_enlargement|theorem extend_real|theorem cthickening_cthickening_subset|theorem cthickening_eq_biUnion_closedBall|theorem lipschitz_infDist_pt|theorem ae_differentiableAt" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -c for extend_pi, integral_lineDeriv_mul_eq, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, image_of_continuousOn_injOn, ae_convolution_tendsto_right_of_locallyIntegrable, euclideanHausdorffMeasure_image, hausdorffMeasure_image_le, measure_compl_support, measurable_fderiv in Mathlib (all present)`
- `grep -n "theorem integral_lineDeriv_mul_eq" Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,140p Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d], isometry invariance)`
- `grep -n "^def |^theorem" SimonGMT Chapter06/{Product,GeometricPointProduct,AffineCurrentPushforward,Currents,Mass,CurrentLocalEquality,Forms}.lean (only affine push-forward and point products; no Lipschitz push-forward, no [[(0,1)]] × T, no homotopy formula)`
- `grep -rn "theorem [a-zA-Z_.]*area" .lake/packages/simongmt/Poincare/SimonGMT (Chapter02 area formulas: injective_area_formula_lipschitz, area_image_criticalSet_eq_zero, ...)`
- `grep -n "def HasApproximateTangentSpaceAt|def CountablyRectifiable|def blowUpMap" SimonGMT/Chapter03/Rectifiable.lean`
- `rg -c exteriorDerivativeOn_pullbackFormWithin, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.boundary, countablyRectifiable_of_measure_zero in SimonGMT (present)`
- `python3 -I scans of dag.json (1366 nodes, 2026-10-13T14:15Z): statuses and frozen types of dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub (accepted), dor_lmb_fc_im_series (decomposing), dor_lmb_slicing_lipschitz (speculative-ready), accepted dpf_*/ptd_*/pit_*/dtc_* helpers; byte-identical types of cmcdt_skeleton_retraction, cmcdt_good_center, dimred_mbl_dt_*; freshness of the dor_lmb_fcd_* names`
- `python3 -I parse of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json and nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `sed -n 340,960p and 1400,1965p book/chapter-06.txt; sed -n 470,700p book/chapter-02.txt`
- `sed -n 6660,6760p and 3210,3260p /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py (_existing_lean_name_problem, accepted-child overlay scoping)`
- `lake env lean /tmp/dfm-decomp/lean/Challenge_*.lean (12 exact comparator challenges), AllProps.lean, Assembly.lean and UnitAssembly.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/dfm-decomp/lean/Assembly.lean`
- `/tmp/dfm-decomp/lean/UnitAssembly.lean`
- `/tmp/dfm-decomp/lean/AllProps.lean`

Snapshot: project b4d606db, mathlib 25730c7c; the snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot nor SimonGMT contains a proved Deformation Theorem, Lemma 5.4, a Lipschitz push-forward of currents, the product [[(0,1)]] × T, or the homotopy formula: SimonGMT Chapter06 provides only affine push-forwards and point products (plus currents, boundary, massOn, support, weak convergence with lower semicontinuity); Chapter02 provides area formulas for Lipschitz maps; Chapter03 the literal approximate-tangent-space definition. The snapshot's GMT/Ch06/Contract.lean has only sorry-frozen latticeFace/IsLatticeChain/DeformationTheorem definitions (the same unit and ρ-cells as the child face formulas), not imported by GMT.Ch07.Submission. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (Vitali covering, cthickening lemmas, lipschitz_infDist_pt, integral_map_equiv, MeasurableEquiv.restrict_map, hausdorffMeasure_smul₀, integral_lineDeriv_mul_eq, Rademacher, measurable_fderiv, convolution a.e. convergence, Isometry.euclideanHausdorffMeasure_image, measure_compl_support). Reuse: dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub are accepted with byte-identical frozen types (standard axioms per acceptance); dor_lmb_fc_im_series (decomposing) and dor_lmb_slicing_lipschitz (speculative-ready) are passed as exact-type antecedents. Lean: all 12 child types compile as exact comparator challenges; parent_assembly and unit_assembly compile with axioms [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
