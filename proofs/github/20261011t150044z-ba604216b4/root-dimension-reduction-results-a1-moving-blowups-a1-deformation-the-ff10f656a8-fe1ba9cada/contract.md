<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1 -->

## Theorem `Submission.dimred_mbl_dt_lp_pushforward_operators`

Assume (VO) for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0 (the frozen type of Submission.dtc_vanish_off_support) and (REP) for U open and T ∈ 𝒟_n(U) with M_W(T) < ∞ for every open W ⊂⊂ U there are a Borel measure μ (μ(ℝ^P ∖ U) = 0, finite on compact subsets of U) and ξ (μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for all x, α) with M_W(T) = μ(W) for open W, T(ω) = ∫ ξ(ω) dμ, and, if also M_W(∂T) < ∞ for open W ⊂⊂ U, μ(E) = 0 whenever Hⁿ(E) = 0. Write ι(t, x) := (t, x_1, …, x_N) ∈ ℝ^{N+1} (Lean WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))), e₀ := (1, 0, …, 0) (EuclideanSpace.single 0 1) and Jv := ι(0, v), and call X ∈ 𝒟_k(ℝ^N) = GeometricCurrentOn univ k NC when spt X is compact, M(X) < ∞ and boundaryMassOn X univ < ∞ (= M(∂X) < ∞ for k ≥ 1, automatic for k = 0). Then there are maps lpush_{N,N',k} : (ℝ^N → ℝ^{N'}) → 𝒟_k(ℝ^N) → 𝒟_k(ℝ^{N'}) (all N, N', k ∈ ℕ) and cyl_{N,k} : 𝒟_k(ℝ^N) → 𝒟_{k+1}(ℝ^{N+1}) (all N, k) such that, for all Λ, L ∈ ℝ≥0: (1) lpush(id, X) = X for NC X; (2) lpush(F, X − Y) = lpush(F, X) − lpush(F, Y) for Λ-Lipschitz F and NC X, Y; (3) lpush(F, X) = lpush(G, X) for Λ-Lipschitz F, G, NC X and F = G on spt X; (4) M(lpush(F, X)) ≤ Λ^k M(X) and spt lpush(F, X) ⊆ F(spt X) for Λ-Lipschitz F and NC X; (5) ∂lpush(F, X) = lpush(F, ∂X) for Λ-Lipschitz F and X ∈ 𝒟_{k+1}(ℝ^N) with compact support, M(X) < ∞ and M(∂X) < ∞; (6) for Λ-Lipschitz F and NC X there are C^∞ (ContDiff ℝ (⊤ : ℕ∞)) Λ-Lipschitz maps F_j : ℝ^N → ℝ^{N'} (j ∈ ℕ) converging to F uniformly on ℝ^N such that for every ω ∈ 𝒟^k(ℝ^{N'}) there are η_j ∈ 𝒟^k(ℝ^N), each equal to F_j^#ω (x ↦ (ω(F_j(x))).compContinuousLinearMap (fderiv ℝ F_j x)) on some open set containing spt X, with X(η_j) → lpush(F, X)(ω); (7) for NC X, cyl(X) has compact support, finite mass and finite boundary mass, and spt cyl(X) ⊆ {ι(t, x) : t ∈ [0, 1], x ∈ spt X}; (8) cyl(X − Y) = cyl(X) − cyl(Y) for NC X, Y; (9) for NC X ∈ 𝒟_k(ℝ^N) and every ω ∈ 𝒟^{k+1}(ℝ^{N+1}) there is a family η : ℝ → 𝒟^k(ℝ^N) with η_t(x)(v_1, …, v_k) = ω(ι(t, x))(e₀, Jv_1, …, Jv_k) for all t, x, v, and cyl(X)(ω) = ∫_0^1 X(η_t) dt; (10) for Λ-Lipschitz F, G : ℝ^N → ℝ^{N'}, L-Lipschitz H : ℝ^{N+1} → ℝ^{N'} and X ∈ 𝒟_0(ℝ^N) with compact support and finite mass such that H(ι(t, x)) = F(x) + t(G(x) − F(x)) for all x ∈ spt X and t ∈ [0, 1]: lpush(G, X) − lpush(F, X) = ∂lpush(H, cyl(X)); (11) for F, G, H as in (10) and X ∈ 𝒟_{k+1}(ℝ^N) with compact support, M(X) < ∞, M(∂X) < ∞ and the same agreement of H on [0, 1] × spt X: lpush(G, X) − lpush(F, X) − lpush(H, cyl(∂X)) = ∂lpush(H, cyl(X)); (12) for F, G, H as in (10), NC X ∈ 𝒟_k(ℝ^N) with the same agreement of H on [0, 1] × spt X, and δ ∈ ℝ with |F(x) − G(x)| ≤ δ for x ∈ spt X: M(lpush(H, cyl(X))) ≤ ENNReal.ofReal δ·(2Λ)^k·M(X).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5920

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6961, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6947

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6299, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5117, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7746, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7758, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7767, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7774, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7784, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7792, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7802, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7808, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7812, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7817

## Lean problem

Declaration: `Submission.dimred_mbl_dt_lp_pushforward_operators`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) ∧ (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 2 (A0), 3 (A1, smooth push-forward), 5 (A3, smooth homotopy formula and mass estimate), 6 (A4, Lipschitz push-forward, incl. the cut-off homotopy of A4(f)) and the operator definitions of C1 (Simon Ch. 6, 2.23–2.29). The product with [[0,1]] (parent step 4, A2) is the sibling dimred_mbl_dt_lp_cylinder, whose operator is re-exported as cyl; the sibling dimred_mbl_dt_lp_covector_bounds supplies (L1) |A^#β| ≤ ‖A‖^k|β| and (L2) |ι_vβ| ≤ |v||β|. (VO) and (REP) are the antecedents of the statement (and of the cylinder sibling).

0. Conventions and elementary facts.
 (a) 𝒟_k(ℝ^N) = GeometricCurrentOn univ k, 𝒟^k(ℝ^N) = TestFormOn univ k. |α| := covectorEuclideanNorm α is the Euclidean norm of the coefficient vector (α(e_J))_{J increasing}; the coefficient map is linear and injective, so |·| is a norm on the finite-dimensional space of k-covectors (|α + β| ≤ |α| + |β|, |sα| = |s||α|, equivalent to the operator norm, |∫α_t dt| ≤ ∫|α_t| dt). ‖ω‖ := sup_x|ω(x)| < ∞ for test forms.
 (b) Mass. M_W(T) is the supremum of T(ω) over test forms with tsupport ⊆ W and pointwise norm ≤ 1, M := M_{ℝ^N}. For every current T and test form ω, |T(ω)| ≤ M(T)‖ω‖ (for ε > 0 the forms ±ω/(‖ω‖ + ε) are admissible). A linear functional L on test forms with |L(ω)| ≤ C‖ω‖ is a current (a sequence converging to 0 in the test-form topology converges to 0 uniformly) with M(L) ≤ C. If T_j → T weakly (T_j(ω) → T(ω) for all ω) then ∂T_j → ∂T weakly (SimonGMT WeaklyConvergesOn.boundary) and M(T) ≤ liminf M(T_j) (WeaklyConvergesOn.massOn_le_liminf with W = univ).
 (c) Support. spt T is the complement of the open union Z_T of the open sets with compact closure on which T vanishes. (S1) If E is closed and T(ω) = 0 whenever tsupport ω ∩ E = ∅, then spt T ⊆ E. (S2) spt(X − Y) ⊆ spt X ∪ spt Y, and spt ∂X ⊆ spt X (tsupport dω ⊆ tsupport ω, SimonGMT tsupport_exteriorDerivative_subset). (S3) If test forms η, η' agree on an open W ⊇ spt X then X(η) = X(η'): tsupport(η − η') ⊆ ℝ^N ∖ W is disjoint from spt X, so (VO) gives X(η − η') = 0. (S4) If spt X = ∅ then X = 0 by (VO).
 (d) NC_k(ℝ^N) is the set of X ∈ 𝒟_k(ℝ^N) with IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞ (= M(∂X) < ∞ for k ≥ 1; automatic for k = 0). NC_k is closed under differences: spt(X − Y) is closed and contained in the compact spt X ∪ spt Y; M(X − Y) ≤ M(X) + M(Y) since (X − Y)(ω) = X(ω) + Y(−ω); ∂(X − Y) = ∂X − ∂Y (GeometricCurrentOn.ext). If X ∈ NC_{k+1} then ∂X ∈ NC_k (spt ∂X ⊆ spt X, ∂∂X = 0 by SimonGMT GeometricCurrentOn.boundary_boundary).
 (e) Cut-offs. For compact K ⊆ ℝ^N (or ℝ^{N+1}) and ε > 0 there is ζ ∈ C^∞_c with 0 ≤ ζ ≤ 1, ζ = 1 on the open ε/2-neighbourhood of K and tsupport ζ inside the closed 2ε-neighbourhood of K: convolve the indicator of the closed ε-neighbourhood of K with a normalized smooth bump supported in the ball of radius ε/2 (Mathlib ContDiffBump.normed, HasCompactSupport.contDiff_convolution_left). In particular, if O is open and K ⊆ O, choosing ε with the 2ε-neighbourhood of K inside O (compactness) gives ζ = 1 on an open O' with K ⊆ O' ⊆ O.
 (f) Mollification. Fix normalized smooth bumps ϕ_σ ≥ 0 (σ > 0) supported in B_σ(0) with ∫ϕ_σ = 1. For a Λ-Lipschitz F : ℝ^N → ℝ^{N'} put F_σ(x) := ∫ ϕ_σ(y)F(x − y) dy. F_σ is C^∞, |F_σ(x) − F_σ(x')| ≤ ∫ϕ_σ(y)|F(x − y) − F(x' − y)| dy ≤ Λ|x − x'| (so F_σ is Λ-Lipschitz and ‖DF_σ‖ ≤ Λ), and |F_σ(x) − F(x)| ≤ ∫ϕ_σ(y)|F(x − y) − F(x)| dy ≤ Λσ. The construction does not depend on Λ.
 (g) Coordinates on ℝ^{N+1}: ι(t, x) := (t, x_1, …, x_N) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))), e₀ := ι(1, 0) (EuclideanSpace.single 0 1), Jv := ι(0, v), tail(y) := (y_1, …, y_N); J is linear isometric, ι(t, x) = te₀ + Jx, the derivative of x ↦ ι(t, x) is J and that of t ↦ ι(t, x) is e₀.
 (h) Smooth pull-back. For C^∞ F : ℝ^N → ℝ^{N'} and a k-form ω on ℝ^{N'}, F^#ω(x) := ω(F(x))∘DF(x)^{×k} (Lean (ω (F x)).compContinuousLinearMap (fderiv ℝ F x)). If ω is C^∞ so is F^#ω: x ↦ ω(F(x)) and x ↦ DF(x) are C^∞, and (α, A) ↦ α.compContinuousLinearMap A is the restriction to the diagonal of the continuous multilinear map (α, A_1, …, A_k) ↦ α∘(A_1 × ⋯ × A_k), hence a continuous polynomial map and C^∞ (its derivative is Mathlib ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap; iterate, or use that bounded multilinear maps are C^∞); d(F^#ω) = F^#(dω) (SimonGMT exteriorDerivativeOn_pullbackFormWithin with U = V = ℝ^N, where fderivWithin on univ is fderiv); (G∘F)^#ω = F^#(G^#ω) (chain rule). For a (k+1)-covector β, linear A and vector w: ι_w(β∘A^{×(k+1)}) = (ι_{Aw}β)∘A^{×k}.

1. A0 (Representation). Let X ∈ 𝒟_k(ℝ^N) with M(X) < ∞. For open W with compact closure M_W(X) ≤ M(X) < ∞, so (REP) with U = ℝ^N gives a Borel measure μ_X and ξ_X with μ_X(W) = M_W(X) for open W, ξ_X μ_X-a.e. strongly measurable, |ξ_X(x)(α)| ≤ |α|, and X(ω) = ∫ξ_X(x)(ω(x)) dμ_X(x). Then μ_X(ℝ^N) = M(X), and μ_X(ℝ^N ∖ spt X) = M_{ℝ^N∖spt X}(X) = 0 because every admissible form supported in the open set ℝ^N ∖ spt X is killed by (VO). Hence |X(η)| ≤ ∫_{spt X}|η(x)| dμ_X ≤ M(X)·sup_{x ∈ spt X}|η(x)| for every test form η.

2. A1 (Smooth push-forward). Let X ∈ 𝒟_k(ℝ^N) have compact support and M(X) < ∞, and F : ℝ^N → ℝ^{N'} be C^∞. Choose ζ as in 0(e) for K = spt X, ζ = 1 on an open W_ζ ⊇ spt X. For ω ∈ 𝒟^k(ℝ^{N'}), ζF^#ω ∈ 𝒟^k(ℝ^N) (C^∞ by 0(h), tsupport ⊆ tsupport ζ compact); put F_#X(ω) := X(ζF^#ω). By (S3) this does not depend on ζ, and X(η) = F_#X(ω) for every test form η that equals F^#ω on an open set containing spt X.
 (a) Mass: by A0 (ζ = 1 on spt X) and (L1), |F_#X(ω)| ≤ sup_{x ∈ spt X}‖DF(x)‖^k·|ω(F(x))|·M(X) ≤ Λ_F^k M(X)‖ω‖ with Λ_F := sup_{spt X}‖DF‖ < ∞. F_#X is linear, hence (0(b)) a current with M(F_#X) ≤ Λ_F^k M(X).
 (b) Linearity in X: with one ζ equal to 1 near spt X ∪ spt Y ⊇ spt(X − Y), F_#(X − Y) = F_#X − F_#Y.
 (c) Boundary: if X ∈ 𝒟_{k+1} and M(∂X) < ∞, then ∂F_#X = F_#∂X: ∂F_#X(ω) = X(ζF^#dω), and ζF^#dω = ζ·d(F^#ω) agrees with d(ζF^#ω) on W_ζ (ζ ≡ 1 there), so by (S3) X(ζF^#dω) = X(d(ζF^#ω)) = ∂X(ζF^#ω) = F_#∂X(ω) (the last step by (S3) for ∂X, spt ∂X ⊆ spt X ⊆ W_ζ).
 (d) Support: spt F_#X ⊆ F(spt X): if tsupport ω ∩ F(spt X) = ∅, F^#ω vanishes on the open set F^{-1}(ℝ^{N'} ∖ tsupport ω) ⊇ spt X, so F_#X(ω) = X(0) = 0 by (S3); F(spt X) is compact, and (S1) applies.

3. The product with [[0,1]]. Apply the sibling dimred_mbl_dt_lp_cylinder (its antecedents are (VO), (REP)) and let cyl = cyl_{N,k} be its operator with: (C1) for NC X, spt cyl(X) is compact, M(cyl X) ≤ M(X), M(∂cyl X) < ∞, spt cyl(X) ⊆ ι([0,1] × spt X); (C2) cyl(X − Y) = cyl X − cyl Y for NC X, Y; (C3) for NC X and ω ∈ 𝒟^{k+1}(ℝ^{N+1}) there are test forms η_t (t ∈ ℝ) with η_t(x)(v) = ω(ι(t, x))(e₀, Jv_1, …, Jv_k) and cyl(X)(ω) = ∫_0^1 X(η_t) dt; (C4), (C5) the boundary formulas ∂cyl(X)(ω) = X(β_1) − X(β_0) (degree 0) and ∂cyl(X)(ω) = X(β_1) − X(β_0) − cyl(∂X)(ω) (degree k+1, compact support and M(X), M(∂X) < ∞), where β_s are test forms on ℝ^N with β_s(x)(v) = ω(ι(s, x))(Jv_1, …). In particular cyl(X) ∈ NC_{k+1}(ℝ^{N+1}) for X ∈ NC_k, and cyl(∂X) ∈ NC_k(ℝ^{N+1}) for X ∈ NC_{k+1} (0(d)).

4. A3 (Smooth homotopy formula). Let X ∈ NC_k(ℝ^N), F, G : ℝ^N → ℝ^{N'} C^∞ with ‖DF‖, ‖DG‖ ≤ Λ everywhere, and H : ℝ^{N+1} → ℝ^{N'} C^∞ with H(ι(t, x)) = F(x) + t(G(x) − F(x)) for all ι(t, x) in an open set O ⊇ ι([0,1] × spt X). H_# denotes A1 in ℝ^{N+1}, applicable to cyl(X) and cyl(∂X) by step 3. By 0(e) applied in ℝ^{N+1} to the compact set ι([0,1] × spt X) ⊆ O, fix ζ̃ ∈ C^∞_c(ℝ^{N+1}) with ζ̃ = 1 on an open set O' with ι([0,1] × spt X) ⊆ O' ⊆ O; it is an admissible cut-off for A1 applied to cyl(X) and to cyl(∂X), whose supports lie in ι([0,1] × spt X) by (C1) and (S2). Then:
 (i) G_#X − F_#X = ∂H_#(cyl X) + H_#(cyl ∂X) for k ≥ 1, and G_#X − F_#X = ∂H_#(cyl X) for k = 0.
 Proof. By A1(c) in ℝ^{N+1} (cyl X has compact support, finite mass and finite boundary mass), ∂H_#(cyl X)(ω) = H_#(∂cyl X)(ω) = ∂cyl(X)(ζ̃H^#ω). By (C5) (resp. (C4) if k = 0) applied to the test form ζ̃H^#ω ∈ 𝒟^k(ℝ^{N+1}): ∂cyl(X)(ζ̃H^#ω) = X(β_1) − X(β_0) − cyl(∂X)(ζ̃H^#ω) (last term absent for k = 0), where β_s(x)(v) = (ζ̃H^#ω)(ι(s, x))(Jv_1, …, Jv_k). For s ∈ {0, 1} the open set W_s := {x : ι(s, x) ∈ O'} contains spt X, and for x ∈ W_s: ζ̃ = 1 near ι(s, x), H∘ι(s, ·) equals F (s = 0), resp. G (s = 1), near x, so DH(ι(s, x))J = DF(x), resp. DG(x), and β_0(x) = ω(F(x))∘DF(x)^{×k} = F^#ω(x), β_1(x) = G^#ω(x). By A1, X(β_0) = F_#X(ω) and X(β_1) = G_#X(ω). Finally cyl(∂X)(ζ̃H^#ω) = H_#(cyl ∂X)(ω) by the definition of A1 for cyl(∂X). Rearranging gives (i).
 (ii) M(H_#(cyl X)) ≤ δ₀·(2Λ)^k·M(X), δ₀ := sup_{x ∈ spt X}|G(x) − F(x)|.
 Proof. Put ω̃ := ζ̃H^#ω ∈ 𝒟^{k+1}(ℝ^{N+1}). By A1 and (C3), H_#(cyl X)(ω) = cyl(X)(ω̃) = ∫_0^1 X(η_t) dt with η_t(x)(v) = ω̃(ι(t, x))(e₀, Jv_1, …, Jv_k). For x ∈ spt X and t ∈ [0,1], ω̃ = H^#ω near ι(t, x) ∈ O', and differentiating H(ι(t, x')) = F(x') + t(G(x') − F(x')) (valid near (t, x)) gives DH(ι(t, x))e₀ = G(x) − F(x) and DH(ι(t, x))J = (1 − t)DF(x) + tDG(x) =: A_t(x), ‖A_t(x)‖ ≤ Λ ≤ 2Λ. By 0(h), η_t(x) = (ι_{G(x)−F(x)}ω(H(ι(t, x))))∘A_t(x)^{×k}, so by (L1), (L2): |η_t(x)| ≤ (2Λ)^k·|G(x) − F(x)|·‖ω‖ ≤ (2Λ)^k δ₀‖ω‖ for x ∈ spt X. By A1's last estimate (A0), |X(η_t)| ≤ M(X)·sup_{spt X}|η_t| ≤ δ₀(2Λ)^kM(X)‖ω‖, hence |H_#(cyl X)(ω)| ≤ δ₀(2Λ)^kM(X)‖ω‖ and 0(b) gives (ii).

5. A4 (Lipschitz push-forward). Let X ∈ NC_k(ℝ^N), F : ℝ^N → ℝ^{N'} Λ-Lipschitz, F_σ as in 0(f).
 (E) For C^∞ F', G' : ℝ^N → ℝ^{N'} with ‖DF'‖, ‖DG'‖ ≤ Λ and δ' := sup_{spt X}|F' − G'|: |G'_#X(ω) − F'_#X(ω)| ≤ δ'((2Λ)^kM(X)‖dω‖ + (2Λ)^{k−1}M(∂X)‖ω‖) (second term absent for k = 0). Proof: fix s ∈ C^∞(ℝ) with s(t) = t on (−1, 2) and s, s' bounded (s(t) := t·b(t) with b smooth, b = 1 on [−1, 2], b = 0 outside (−2, 3)), and χ ∈ C^∞_c(ℝ^N), 0 ≤ χ ≤ 1, χ = 1 on an open W_χ ⊇ spt X (0(e)). H(y) := F'(tail y) + s(y_0)χ(tail y)(G' − F')(tail y) is C^∞ and equals F' + t(G' − F') on the open set ι((−1, 2) × W_χ) ⊇ ι([0,1] × spt X). By step 4(i), G'_#X(ω) − F'_#X(ω) = H_#(cyl X)(dω) + H_#(cyl ∂X)(ω); step 4(ii) for X and for ∂X ∈ NC_{k−1} (spt ∂X ⊆ spt X) together with 0(b) gives (E).
 (a) Existence and mass. For σ, τ > 0, sup|F_σ − F_τ| ≤ Λ(σ + τ), so by (E) (F_σ)_#X(ω) is Cauchy as σ ↓ 0; define F_#X(ω) := lim_{σ↓0}(F_σ)_#X(ω). By 2(a), |(F_σ)_#X(ω)| ≤ Λ^kM(X)‖ω‖, so |F_#X(ω)| ≤ Λ^kM(X)‖ω‖; F_#X is linear in ω, hence (0(b)) a current with M(F_#X) ≤ Λ^kM(X). F_#X does not depend on Λ.
 (b) Boundary. For X ∈ NC_{k+1}: ∂F_#X(ω) = F_#X(dω) = lim(F_σ)_#X(dω) = lim(F_σ)_#∂X(ω) = F_#∂X(ω) (2(c); ∂X ∈ NC_k).
 (c) Smooth maps. If F is C^∞ and Λ-Lipschitz, the A4 push-forward equals the A1 push-forward: by (E) with F' = F_σ, G' = F (δ' ≤ Λσ) the difference tends to 0. In particular id_#X(ω) = X(ζω) = X(ω) by (S3), i.e. id_#X = X.
 (d) Support. spt F_#X ⊆ F(spt X): if tsupport ω ∩ F(spt X) = ∅, these compact sets have positive distance d₀, and for Λσ < d₀, F_σ(spt X) ∩ tsupport ω = ∅, so (F_σ)_#X(ω) = 0 (argument of 2(d)); hence F_#X(ω) = 0 and (S1) applies.
 (e) Locality and linearity. If F, G are Λ-Lipschitz and |F − G| ≤ δ on spt X, then |F_#X(ω) − G_#X(ω)| ≤ δ((2Λ)^kM(X)‖dω‖ + (2Λ)^{k−1}M(∂X)‖ω‖): apply (E) to F_σ, G_σ (sup_{spt X}|F_σ − G_σ| ≤ δ + 2Λσ) and let σ ↓ 0. In particular F_#X = G_#X if F = G on spt X. For X, Y ∈ NC_k, (F_σ)_#(X − Y) = (F_σ)_#X − (F_σ)_#Y (2(b)); in the limit F_#(X − Y) = F_#X − F_#Y (X − Y ∈ NC_k by 0(d)).
 (f) Homotopy formula. Let F, G : ℝ^N → ℝ^{N'} be Λ-Lipschitz and H : ℝ^{N+1} → ℝ^{N'} Lipschitz with H(ι(t, x)) = F(x) + t(G(x) − F(x)) for x ∈ spt X, t ∈ [0,1]. Then G_#X − F_#X = ∂H_#(cyl X) + H_#(cyl ∂X) for k ≥ 1 (without the last term for k = 0), and M(H_#(cyl X)) ≤ δ(2Λ)^kM(X) whenever δ ∈ ℝ and |F − G| ≤ δ on spt X. (H_# is the A4 push-forward in ℝ^{N+1} of cyl X ∈ NC_{k+1} and cyl ∂X ∈ NC_k, step 3.)
 Proof. Independence of H: if H, H' are Lipschitz (with a common constant) and agree on ι([0,1] × spt X), which contains spt cyl(X) and spt cyl(∂X) ((C1), (S2)), then H_#Y = H'_#Y for Y = cyl X, cyl ∂X by (e) in ℝ^{N+1} with δ = 0. So it suffices to treat H_*(y) := F(tail y) + s(y_0)χ(tail y)(G − F)(tail y) (s, χ as in (E)), which agrees with F + t(G − F) on ι([0,1] × spt X) and is Lipschitz (uniform limit of the L₀-Lipschitz maps H_σ below). For σ ∈ (0, 1] put H_σ(y) := F_σ(tail y) + s(y_0)χ(tail y)(G_σ − F_σ)(tail y). It is C^∞; ∂_tH_σ = s'χ(G_σ − F_σ) and D_xH_σ = DF_σ + s[(G_σ − F_σ)⊗Dχ + χ(DG_σ − DF_σ)] are bounded uniformly in σ ≤ 1 (|G_σ − F_σ| ≤ |G − F| + 2Λ is bounded on the compact tsupport χ; ‖DF_σ‖, ‖DG_σ‖ ≤ Λ), so all H_σ are L₀-Lipschitz for one L₀; H_σ = F_σ + t(G_σ − F_σ) on ι((−1, 2) × W_χ) ⊇ ι([0,1] × spt X); and sup|H_σ − H_*| ≤ (1 + 2 sup|s|)Λσ. By step 4 for F_σ, G_σ, H_σ (A1 push-forwards, equal to A4 push-forwards by (c)): (G_σ)_#X − (F_σ)_#X = ∂(H_σ)_#(cyl X) + (H_σ)_#(cyl ∂X) and M((H_σ)_#(cyl X)) ≤ sup_{spt X}|G_σ − F_σ|(2Λ)^kM(X). Let σ = σ_j := 1/(j+1). The left side converges weakly to G_#X − F_#X (definition (a)); by (e) in ℝ^{N+1} (Lipschitz constant max(L₀, Lip H_*), δ = sup|H_σ − H_*| → 0), (H_σ)_#Y → (H_*)_#Y weakly for both Y; boundaries of weakly convergent sequences converge weakly (0(b)). The weak limits agree on every test form, so the currents are equal (GeometricCurrentOn.ext). For the mass: sup_{spt X}|G_σ − F_σ| ≤ δ + 2Λσ, and lower semicontinuity (0(b)) gives M((H_*)_#(cyl X)) ≤ δ(2Λ)^kM(X) when δ ≥ 0. If δ < 0 the hypothesis forces spt X = ∅, so X = 0 (S4), cyl X = 0 (by (C3) its value is ∫_0^1 0 dt) and its push-forward is 0; both sides vanish (ENNReal.ofReal δ = 0).

6. Definitions. lpush_{N,N',k}(F, X) := F_#X (A4) if F is Lipschitz for some constant and X ∈ NC_k(ℝ^N), and := 0 otherwise. cyl_{N,k} is the operator of step 3.

7. Verification of the twelve conjuncts (NC X means IsCompact X.support, X.mass < ∞, boundaryMassOn X univ < ∞; push-forwards of NC currents by Lipschitz maps are A4 push-forwards).
 (1) lpush N N k (fun x => x) X = X for NC X: A4(c).
 (2) lpush(F, X − Y) = lpush(F, X) − lpush(F, Y): A4(e); X − Y ∈ NC_k by 0(d).
 (3) EqOn F G (spt X) ⇒ lpush(F, X) = lpush(G, X): A4(e) with δ = 0.
 (4) Mass ≤ Λ^k·M(X) and support ⊆ F '' spt X: A4(a), A4(d).
 (5) X ∈ 𝒟_{k+1} with compact support and M(X), M(∂X) < ∞ is in NC_{k+1} and ∂X ∈ NC_k; A4(b).
 (6) Put F_j := F_{σ_j}, σ_j := 1/(j+1): C^∞ (ContDiff ℝ (⊤ : ℕ∞)), Λ-Lipschitz, sup|F_j − F| ≤ Λσ_j → 0, i.e. TendstoUniformly F_j F. Given ω, fix ζ as in 0(e) for spt X (ζ = 1 on an open W ⊇ spt X) and η_j := ζF_j^#ω ∈ 𝒟^k(ℝ^N). Then η_j = F_j^#ω on W, and X(η_j) = (F_j)_#X(ω) (A1) → F_#X(ω) = lpush(F, X)(ω) (A4(a)).
 (7) (C1): spt cyl(X) is compact, M(cyl X) ≤ M(X) < ∞, M(∂cyl X) < ∞, and spt cyl(X) ⊆ ι([0,1] × spt X) = {y : ∃ t ∈ [0,1], ∃ x ∈ spt X, y = ι(t, x)}.
 (8) cyl(X − Y) = cyl(X) − cyl(Y): (C2).
 (9) (C3) verbatim: for every ω ∈ 𝒟^{k+1}(ℝ^{N+1}) a family η : ℝ → 𝒟^k(ℝ^N) with η t x v = ω(ι(t, x))(Fin.cons e₀ (J∘v)) and cyl N k X ω = ∫_0^1 X(η t) dt.
 (10) Degree 0: X ∈ 𝒟_0 with compact support and finite mass is in NC_0; A4(f) with the given L-Lipschitz H gives lpush(G, X) − lpush(F, X) = ∂lpush(H, cyl(X)).
 (11) Degree k + 1: A4(f) gives lpush(G, X) − lpush(F, X) = ∂lpush(H, cyl(X)) + lpush(H, cyl(∂X)), which is the stated identity after subtracting lpush(H, cyl(∂X)) (currents subtract pointwise on test forms; GeometricCurrentOn.ext).
 (12) A4(f) mass bound, with ENNReal.ofReal δ = max(δ, 0). ∎

## Key steps

1. Conventions: mass/norm facts, support facts (S1)–(S4) from (VO), NC closure, cut-offs, mollifiers F_σ (C^∞, Λ-Lipschitz, |F_σ − F| ≤ Λσ), smooth pull-backs.
2. A0 from (REP), (VO): |X(η)| ≤ M(X) sup_{spt X}|η|.
3. A1: smooth push-forward F_#X(ω) = X(ζF^#ω): a current with mass ≤ sup‖DF‖^k M(X) (L1), linear, ∂F_#X = F_#∂X, spt ⊆ F(spt X).
4. cyl from the sibling cylinder with (C1)–(C5); A3: G_#X − F_#X = ∂H_#(cyl X) + H_#(cyl ∂X) via (C4)/(C5), and M(H_#(cyl X)) ≤ sup|G − F|(2Λ)^kM(X) via (C3), (L1), (L2).
5. A4: estimate (E) with a cut-off smooth homotopy; F_#X := lim(F_σ)_#X; mass, boundary, smooth case and identity, support, locality and linearity; Lipschitz homotopy formula by cut-off homotopies H_σ → H_*, weak limits and lower semicontinuity.
6. Definitions lpush := F_#X (Lipschitz F, NC X; 0 otherwise), cyl := sibling operator; verification of the twelve conjuncts incl. interface (6) via mollifiers and cut-off pull-backs.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git rev-parse HEAD of the workspace (b4d606db) and of SNAPSHOT/mathlib (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical)`
- `rg -c "dimred_mbl_dt_lp" SNAPSHOT lake-packages-25730c7c/simongmt (no match); python3 scan of RUN/dag.json lean_names for the six new names (none) and for the three reused names (accepted nodes with byte-identical lean_statement)`
- `rg -n -i "lipschitz.*push|pushforward.*lipschitz|weak continuity|jacobian.*weak|cylinder|\[\[0, ?1\]\]" SNAPSHOT/project/GMT -g "*.lean" (only the unproved Ch06 specification IsLipschitzPushforward / LipschitzPushforwardIntegerMultiplicity in Ch06/Contract.lean; Ch07 does not import Ch06)`
- `python3 scans of accepted RUN/dag.json lean_statements for covectorEuclideanNorm, curryLeft, compContinuousLinearMap, HasApproximateTangentSpaceAt, CountablyRectifiable, LipschitzWith, Orthonormal, ApproximatesLinearOn/AntilipschitzWith (found covectorEuclideanNorm_gram_bounds, regcomp_covector_eval_orthonormal_le, dpf_rectifiable_bilipschitz_pieces, ptd_piece_image_approxTangent_ae, dpf_approxTangent_ae_bilipschitz_piece; no Lipschitz push-forward, cylinder, Jacobian weak continuity or map-partition lemma)`
- `grep of SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap, HasApproximateTangentSpaceAt.unique, countablyRectifiable_range, CountablyRectifiable.mono, countablyRectifiable_of_measure_zero), Chapter06 Currents/Mass/CurrentLocalEquality/Forms (GeometricCurrentOn, boundary, ext, boundary_boundary, tsupport_exteriorDerivative_subset, exteriorDerivativeTestOn, WeaklyConvergesOn.boundary, covectorEuclideanNorm, massOn, mass, le_massOn, massOn_le_liminf, support, zeroRegion, exteriorDerivative_apply, exteriorDerivativeOn_pullbackFormWithin), Chapter02 AreaDomain/AreaCritical (injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, area_image_criticalSet_eq_zero, areaJacobianWithin)`
- `grep -rnE "(theorem|lemma) ..." SNAPSHOT/mathlib/Mathlib for exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, PiLp.volume_preserving_ofLp, volume_preserving_piFinSuccAbove, lipschitz_infDist_pt, infDist_zero_of_mem, hausdorffMeasure_image_le, MeasurableSet.image_of_continuousOn_injOn, tendsto_tsum_of_dominated_convergence, integral_lineDeriv_mul_eq, ae_convolution_tendsto_right_of_locallyIntegrable, measurableSet_of_differentiableAt, measurable_fderiv, LinearMap.exists_antilipschitzWith, ae_tendsto_measure_inter_div_of_measurableSet, ae_tendsto_average_norm_sub, Orthonormal.exists_orthonormalBasis_extension (all found)`
- `python3/cat of the twin node root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1 decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json and decomposition-scope-v1.json; sentence diff of the two parent-supplied proofs`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _accepted_checkpoint, _install_parent_supplied_child_handoff, _overlay_accepted_children) and store.py ensure; verifier gmt-compare.py contract_scope/child_modules; both validate_lean_statement implementations on all nine types`
- `lake env lean /tmp/dmlp/lean/Types.lean, /tmp/dmlp/lean/Challenge_<key>.lean for all nine keys (only sorry warnings), /tmp/dmlp/lean/Assembly.lean (#print axioms GMT.Ch07.DmlpAsm.assembly: propext, Classical.choice, Quot.sound), /tmp/dmlp/lean/Reexport.lean, /tmp/dmlp/lean/InstCheck.lean (clean)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dmlp/lean/Types.lean`
- `/tmp/dmlp/lean/Assembly.lean`
- `/tmp/dmlp/lean/Reexport.lean`
- `/tmp/dmlp/lean/InstCheck.lean`

Pins match: project b4d606db, Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. Neither the snapshot project nor Mathlib nor SimonGMT contains a Lipschitz push-forward of currents, a product with [[0,1]], or a weak-continuity lemma for Jacobians; the snapshot's Ch06 push-forward specification is unproved and not imported by Ch07. So covector_bounds, cylinder, operators, jacobian_continuity, im_pushforward and im_cylinder are new obligations under fresh, unused names (dimred_mbl_dt_lp_*). Three needed steps already exist as accepted DAG declarations with exactly the required types and are reused verbatim: covectorEuclideanNorm_gram_bounds (L3), dpf_rectifiable_bilipschitz_pieces (B1) and ptd_piece_image_approxTangent_ae (B2). Every cited Mathlib and SimonGMT name exists. All nine types elaborate in the comparator's challenge form and pass both validators. A Lean assembly derives the exact selected type from the operators, im_pushforward, im_cylinder and IMS types, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
