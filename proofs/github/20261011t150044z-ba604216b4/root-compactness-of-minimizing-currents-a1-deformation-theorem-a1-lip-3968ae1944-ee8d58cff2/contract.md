<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1 -->

## Theorem `Submission.cmcdt_lp_pushforward_operators`

Assume, as hypotheses of the statement, (VO) the frozen type of Submission.dtc_vanish_off_support: for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0; and (REP) the frozen type of Submission.cmc_exists_massRepresentation: for U open and T ∈ 𝒟_n(U) with M_W(T) < ∞ for every open W ⊂⊂ U there are a Borel measure μ (μ(ℝ^P ∖ U) = 0, finite on compact subsets of U) and ξ (μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for all x, α) with M_W(T) = μ(W) for open W, T(ω) = ∫ ξ(ω) dμ, and, if also M_W(∂T) < ∞ for open W ⊂⊂ U, μ(E) = 0 whenever Hⁿ(E) = 0. (These are the exact frozen Lean types, written as antecedents.) Currents are on univ: 𝒟_k(ℝ^N) = GeometricCurrentOn univ k, 𝒟^k(ℝ^N) = TestFormOn univ k. Write ι(t, x) := (t, x_1, …, x_N) ∈ ℝ^{N+1} (Lean WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))), e₀ := (1, 0, …, 0) (EuclideanSpace.single 0 1), and call X ∈ 𝒟_k(ℝ^N) NC if spt X is compact, M(X) < ∞ and boundaryMassOn X univ < ∞ (M(∂X) < ∞ for k ≥ 1, automatic for k = 0). Then there are maps lpush_{N,N',k} : (ℝ^N → ℝ^{N'}) → 𝒟_k(ℝ^N) → 𝒟_k(ℝ^{N'}) (all N, N', k ∈ ℕ) and cyl_{N,k} : 𝒟_k(ℝ^N) → 𝒟_{k+1}(ℝ^{N+1}) (all N, k) such that, for all Λ, L ∈ ℝ≥0: (1) lpush(id, X) = X for NC X ∈ 𝒟_k(ℝ^N); (2) lpush(F, X − Y) = lpush(F, X) − lpush(F, Y) for Λ-Lipschitz F and NC X, Y; (3) lpush(F, X) = lpush(G, X) for Λ-Lipschitz F, G, NC X and F = G on spt X; (4) M(lpush(F, X)) ≤ Λ^k M(X) and spt lpush(F, X) ⊆ F(spt X) for Λ-Lipschitz F and NC X; (5) ∂ lpush(F, X) = lpush(F, ∂X) for Λ-Lipschitz F and X ∈ 𝒟_{k+1}(ℝ^N) with compact support, M(X) < ∞ and M(∂X) < ∞; (6) for Λ-Lipschitz F and NC X there are C^∞ (ContDiff ℝ (⊤ : ℕ∞)) Λ-Lipschitz maps F_j : ℝ^N → ℝ^{N'} (j ∈ ℕ) converging to F uniformly on ℝ^N such that for every ω ∈ 𝒟^k(ℝ^{N'}) there are η_j ∈ 𝒟^k(ℝ^N), each equal to F_j^#ω (x ↦ ω(F_j(x)) ∘ DF_j(x)) on some open set containing spt X, with X(η_j) → lpush(F, X)(ω); (7) for NC X, cyl(X) has compact support, finite mass and finite boundary mass, and spt cyl(X) ⊆ {ι(t, x) : t ∈ [0, 1], x ∈ spt X}; (8) cyl(X − Y) = cyl(X) − cyl(Y) for NC X, Y; (9) for NC X ∈ 𝒟_k(ℝ^N) and every ω ∈ 𝒟^{k+1}(ℝ^{N+1}) there is η ∈ 𝒟^k(ℝ^N) with η(x)(v_1, …, v_k) = ∫_0^1 ω(ι(t, x))(e₀, ι(0, v_1), …, ι(0, v_k)) dt for all x and v, and cyl(X)(ω) = X(η); (10) for Λ-Lipschitz F, G : ℝ^N → ℝ^{N'}, L-Lipschitz H : ℝ^{N+1} → ℝ^{N'} and X ∈ 𝒟_0(ℝ^N) with compact support and finite mass such that H(ι(t, x)) = F(x) + t(G(x) − F(x)) for all x ∈ spt X and t ∈ [0, 1]: lpush(G, X) − lpush(F, X) = ∂ lpush(H, cyl(X)); (11) for F, G, H as in (10) and X ∈ 𝒟_{k+1}(ℝ^N) with compact support, M(X) < ∞, M(∂X) < ∞ and the same agreement of H on [0, 1] × spt X: lpush(G, X) − lpush(F, X) − lpush(H, cyl(∂X)) = ∂ lpush(H, cyl(X)); (12) for F, G, H as in (10), NC X ∈ 𝒟_k(ℝ^N) with the same agreement of H on [0, 1] × spt X, and δ ∈ ℝ with |F(x) − G(x)| ≤ δ for x ∈ spt X: M(lpush(H, cyl(X))) ≤ ENNReal.ofReal δ · (2Λ)^k · M(X).

Node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5204

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6049

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6992, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7003, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7014, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7028, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7034, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7042, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7049, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7055

## Lean problem

Declaration: `Submission.cmcdt_lp_pushforward_operators`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) ∧ (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part A of the parent proof (Simon Ch. 6, 2.17–2.29: products with [[0,1]] (2.17–2.22), smooth push-forward (2.23–2.24), homotopy formula and mass estimate (2.25–2.27), Lipschitz push-forward (2.29)), with the cut-off homotopy of the parent's A4(f), and with the two interfaces (6) and (9) that the sibling cmcdt_lp_integer_multiplicity consumes. The sibling cmcdt_lp_covector_norm_bounds supplies (L1) |A^#β| ≤ ‖A‖^k|β| and (L2) |ι_vβ| ≤ |v||β|. (VO) and (REP) are the two antecedents of the statement.

0. Conventions and elementary facts.
 (a) 𝒟_k(ℝ^N) = GeometricCurrentOn univ k, 𝒟^k(ℝ^N) = TestFormOn univ k (C^∞ k-forms with compact support). |α| := covectorEuclideanNorm α. It is the Euclidean norm of the coefficient vector c(α) := (α(e_J))_{J increasing}; c is linear and injective (an alternating map is determined by its values on increasing tuples of basis vectors), so |·| is a norm on the finite-dimensional space of k-covectors: |α + β| ≤ |α| + |β|, |sα| = |s||α|, |·| is equivalent to the operator norm, and |∫ α_t dt| ≤ ∫ |α_t| dt for integrable families (c commutes with Bochner integrals). For a test form put ‖ω‖ := sup_x |ω(x)| < ∞.
 (b) Mass. M_W(T) = sup{T(ω) : ω ∈ 𝒟^k, tsupport ω ⊆ W, |ω(x)| ≤ 1 for all x} ∈ [0, ∞] and M := M_{ℝ^N}. If M(T) < ∞ then |T(ω)| ≤ M(T)‖ω‖ (apply the definition to ±ω/‖ω‖, admissible since |−α| = |α|; ω = 0 if ‖ω‖ = 0). If a linear functional T on 𝒟^k satisfies |T(ω)| ≤ C‖ω‖, it is sequentially continuous (a sequence converging to 0 in Simon's topology converges uniformly, so ‖ω_j‖ → 0), i.e. a current, and M(T) ≤ C. If T_j → T weakly (pointwise on test forms) then ∂T_j → ∂T weakly (SimonGMT WeaklyConvergesOn.boundary) and M(T) ≤ liminf M(T_j) (WeaklyConvergesOn.massOn_le_liminf).
 (c) Support. spt T = ℝ^N ∖ Z_T, Z_T the union of the relatively compact open sets on which T vanishes; spt T is closed. (S1) If E is closed and T(ω) = 0 whenever tsupport ω ∩ E = ∅, then spt T ⊆ E (a point outside E has a ball with compact closure disjoint from E, on which T vanishes). (S2) spt(X − Y) ⊆ spt X ∪ spt Y, and spt ∂X ⊆ spt X (if X vanishes on W so does ∂X, since tsupport dω ⊆ tsupport ω, SimonGMT tsupport_exteriorDerivative_subset). (S3) If test forms η, η' agree on an open set W ⊇ spt X, then X(η) = X(η'): tsupport(η − η') ⊆ ℝ^N ∖ W is disjoint from spt X, so (VO) gives X(η − η') = 0. (S4) If spt X = ∅ then X = 0 by (VO).
 (d) NC_k(ℝ^N) is the set of X ∈ 𝒟_k(ℝ^N) with IsCompact X.support, X.mass < ∞ and boundaryMassOn X univ < ∞ (= M(∂X) < ∞ for k ≥ 1; automatic for k = 0). NC_k is closed under differences: spt(X − Y) is closed and contained in the compact spt X ∪ spt Y; M(X − Y) ≤ M(X) + M(Y) by (b), since (X − Y)(ω) = X(ω) + Y(−ω); ∂(X − Y) = ∂X − ∂Y. If X ∈ NC_{k+1} then ∂X ∈ NC_k (spt ∂X ⊆ spt X, ∂∂X = 0 by SimonGMT GeometricCurrentOn.boundary_boundary).
 (e) Cut-offs. For compact K ⊆ ℝ^N there is ζ ∈ C^∞_c(ℝ^N) with 0 ≤ ζ ≤ 1 and ζ = 1 on an open set containing K: convolve the indicator of the closed 2-neighbourhood of K with a normalized smooth bump supported in the unit ball (Mathlib ContDiffBump.normed, HasCompactSupport.contDiff_convolution_left); the result is 1 on the open 1-neighbourhood of K.
 (f) Mollification. Fix normalized smooth bumps ϕ_σ ≥ 0 (σ > 0) with support in B_σ(0) and ∫ϕ_σ = 1. For a Λ-Lipschitz F : ℝ^N → ℝ^{N'} put F_σ(x) := ∫ ϕ_σ(y) F(x − y) dy. Then F_σ is C^∞ (HasCompactSupport.contDiff_convolution_left), |F_σ(x) − F_σ(x')| ≤ ∫ ϕ_σ(y)|F(x − y) − F(x' − y)| dy ≤ Λ|x − x'| (so F_σ is Λ-Lipschitz and ‖DF_σ‖ ≤ Λ), and |F_σ(x) − F(x)| ≤ ∫ ϕ_σ(y)|F(x − y) − F(x)| dy ≤ Λσ. The construction does not depend on Λ.
 (g) Coordinates on ℝ^{N+1}. ι(t, x) := (t, x_1, …, x_N) (Lean WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))), e₀ := ι(1, 0) (EuclideanSpace.single 0 1), Jv := ι(0, v), tail(y) := (y_1, …, y_N). J is linear and isometric (‖J‖ ≤ 1), ι(t, x) = t·e₀ + Jx, e₀ ⊥ J(ℝ^N), |e₀| = 1, the derivative of x ↦ ι(t, x) is J, and ι is a closed isometric embedding of ℝ × ℝ^N.
 (h) Smooth pull-back. For C^∞ F : ℝ^N → ℝ^{N'} and a k-form ω on ℝ^{N'}, F^#ω(x) := ω(F(x)) ∘ DF(x)^{×k} (Lean (ω (F x)).compContinuousLinearMap (fderiv ℝ F x)). If ω is C^∞ so is F^#ω (x ↦ ω(F(x)) and x ↦ DF(x) are C^∞ and (β, A) ↦ β ∘ A^{×k} is a continuous polynomial map). d(F^#ω) = F^#(dω) (SimonGMT exteriorDerivativeOn_pullbackFormWithin with U = V = ℝ^N; fderivWithin on univ is fderiv), and (G ∘ F)^#ω = F^#(G^#ω) (chain rule). For a (k+1)-covector β, a linear map A and a vector w: ι_w(β ∘ A^{×(k+1)}) = (ι_{Aw}β) ∘ A^{×k} (both sides evaluate to β(Aw, Av_1, …, Av_k)).

1. A0 (Representation). Let X ∈ 𝒟_k(ℝ^N) with M(X) < ∞. For open W ⊂⊂ ℝ^N, M_W(X) ≤ M(X) < ∞ (massOn_mono), so (REP) with U = ℝ^N (open) gives a Borel measure μ_X and ξ_X with μ_X(W) = M_W(X) for every open W, ξ_X μ_X-a.e. strongly measurable, |ξ_X(x)(α)| ≤ |α| for all x, α, and X(ω) = ∫ ξ_X(x)(ω(x)) dμ_X(x). Then μ_X(ℝ^N) = M(X) < ∞, and μ_X(ℝ^N ∖ spt X) = M_{ℝ^N∖spt X}(X) = 0, because every admissible ω with tsupport in the open set ℝ^N ∖ spt X has X(ω) = 0 by (VO). Hence |X(ω)| ≤ ∫_{spt X} |ω(x)| dμ_X, and X(ω) depends only on ω restricted to spt X.

2. A1 (Smooth push-forward). Let X ∈ 𝒟_k(ℝ^N) have compact support and M(X) < ∞, and F : ℝ^N → ℝ^{N'} be C^∞. Choose ζ as in 0(e) for K = spt X, ζ = 1 on an open W_ζ ⊇ spt X. For ω ∈ 𝒟^k(ℝ^{N'}), ζF^#ω ∈ 𝒟^k(ℝ^N) (C^∞ by 0(h), tsupport ⊆ tsupport ζ compact); put F_#X(ω) := X(ζF^#ω). By (S3) this does not depend on ζ, and X(η) = F_#X(ω) for every test form η equal to F^#ω on an open set containing spt X.
 (a) By A0 (ζ = 1 on spt X): F_#X(ω) = ∫ ξ_X(x)(ω(F(x)) ∘ DF(x)) dμ_X. With Λ_F := sup_{spt X}‖DF‖ < ∞ and (L1): |F_#X(ω)| ≤ ∫_{spt X} ‖DF(x)‖^k |ω(F(x))| dμ_X ≤ Λ_F^k M(X)‖ω‖. F_#X is linear in ω, hence by 0(b) a current with M(F_#X) ≤ Λ_F^k M(X).
 (b) Linearity in X: for X, Y as above use one ζ equal to 1 near spt X ∪ spt Y ⊇ spt(X − Y); then F_#(X − Y) = F_#X − F_#Y.
 (c) Boundary: if X ∈ 𝒟_{k+1} and also M(∂X) < ∞, then ∂F_#X = F_#∂X. Indeed ∂F_#X(ω) = F_#X(dω) = X(ζF^#dω); ζF^#dω = ζ·d(F^#ω) agrees with d(ζF^#ω) on W_ζ (ζ ≡ 1 there), so by (S3) X(ζF^#dω) = X(d(ζF^#ω)) = ∂X(ζF^#ω) = F_#∂X(ω), the last step by (S3) for ∂X (spt ∂X ⊆ spt X ⊆ W_ζ).
 (d) Support: spt F_#X ⊆ F(spt X). If tsupport ω ∩ F(spt X) = ∅, F^#ω vanishes on the open set F^{-1}(ℝ^{N'} ∖ tsupport ω) ⊇ spt X, so F_#X(ω) = X(0) = 0 by (S3); F(spt X) is compact, and (S1) applies.

3. A2 (Product with [[0,1]]). For ω ∈ 𝒟^{k+1}(ℝ^{N+1}) put ω₁(t, x) := (ι_{e₀}ω(ι(t, x))) ∘ J^{×k}, i.e. ω₁(t, x)(v_1, …, v_k) = ω(ι(t, x))(e₀, Jv_1, …, Jv_k), and S_ω(x) := ∫_0^1 ω₁(t, x) dt (so S_ω(x)(v) = ∫_0^1 ω₁(t, x)(v) dt, evaluation commuting with the integral). For a k-form ω on ℝ^{N+1} and s ∈ ℝ put i_s^#ω(x) := ω(ι(s, x)) ∘ J^{×k}. The same definitions are used in every degree: for a j-form ω on ℝ^{N+1} (j ≥ 1), ω₁ and S_ω are (j−1)-forms on ℝ^N.
 (a) S_ω ∈ 𝒟^k(ℝ^N), and ω ↦ S_ω is linear and sequentially continuous. (t, x) ↦ ω₁(t, x) is C^∞ (ω composed with the affine map ι, followed by the continuous linear map β ↦ (ι_{e₀}β) ∘ J^{×k}); all its x-derivatives are continuous on [0,1] × ℝ^N, hence bounded on [0,1] × K for compact K, so by repeated differentiation under the integral sign (Mathlib intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le) S_ω is C^∞ with D^mS_ω(x) = ∫_0^1 D_x^m ω₁(t, x) dt. K_ω := {x : ι(t, x) ∈ tsupport ω for some t ∈ [0,1]} is the image of the compact set tsupport ω ∩ {y : y_0 ∈ [0,1]} under tail, hence compact, and S_ω vanishes on the open set ℝ^N ∖ K_ω, so tsupport S_ω ⊆ K_ω. If ω_j → 0 in 𝒟^{k+1}(ℝ^{N+1}) (supports in one compact K, all derivatives → 0 uniformly), then all tsupport S_{ω_j} lie in the compact tail(K ∩ {y_0 ∈ [0,1]}), and D^mS_{ω_j} → 0 uniformly because D_x^m ω_{j,1}(t, x) is a fixed continuous linear image of D^mω_j(ι(t, x)). Likewise i_s^#ω ∈ 𝒟^k(ℝ^N), and ω ↦ i_s^#ω is linear and sequentially continuous: it is the pull-back by the proper affine map x ↦ s·e₀ + Jx (SimonGMT affinePullbackTestOn, TestFormOnConverges.affinePullback).
 (b) For X ∈ 𝒟_k(ℝ^N) define ([[0,1]] × X)(ω) := X(S_ω) for ω ∈ 𝒟^{k+1}(ℝ^{N+1}) and ({s} × X)(ω) := X(i_s^#ω) for ω ∈ 𝒟^k(ℝ^{N+1}). By (a) these are currents in 𝒟_{k+1}(ℝ^{N+1}) and 𝒟_k(ℝ^{N+1}); both are linear in X.
 (c) Support: if spt X is compact, spt([[0,1]] × X) ⊆ ι([0,1] × spt X) and spt({s} × X) ⊆ ι({s} × spt X). If tsupport ω ∩ ι([0,1] × spt X) = ∅ then spt X ∩ K_ω = ∅, S_ω vanishes on the open set ℝ^N ∖ K_ω ⊇ spt X, and X(S_ω) = 0 by (S3); ι([0,1] × spt X) is compact, so (S1) applies. The same argument works for {s} × X.
 (d) Boundary formula: ∂([[0,1]] × X) = {1} × X − {0} × X − [[0,1]] × ∂X for X ∈ 𝒟_k(ℝ^N), k ≥ 1, and ∂([[0,1]] × X) = {1} × X − {0} × X for k = 0. Proof: let ω ∈ 𝒟^k(ℝ^{N+1}); ∂([[0,1]] × X)(ω) = X(S_{dω}). Fix x, t, v_1, …, v_k and put β_t(x) := i_t^#ω(x). By the coordinate formula for d (SimonGMT exteriorDerivative_apply) with the constant vectors w_0 = e₀, w_i = Jv_i:
  dω(ι(t, x))(e₀, Jv_1, …, Jv_k) = ∂_t[ω(ι(t, x))(Jv_1, …, Jv_k)] + Σ_{i=1}^{k} (−1)^i D_{Jv_i}[ω(·)(e₀, Jv_1, …, Jv_{i−1}, Jv_{i+1}, …, Jv_k)](ι(t, x)).
  The first term is ∂_t[β_t(x)(v)]. Since D_{Jv_i}g(ι(t, x)) = D_{v_i}[g(ι(t, ·))](x), the sum is −d_x(ω₁(t, ·))(x)(v) (coordinate formula for the exterior derivative of the (k−1)-form ω₁(t, ·) on ℝ^N, whose i-th term carries the sign (−1)^{i−1}). Hence (dω)₁(t, x) = ∂_tβ_t(x) − d_x(ω₁(t, ·))(x), and for k = 0 only the first term occurs. Integrating over t ∈ [0,1] (fundamental theorem of calculus, Mathlib intervalIntegral.integral_eq_sub_of_hasDerivAt, for the C^1 function t ↦ β_t(x)(v); differentiation under the integral sign for ∫_0^1 d_xω₁(t, ·)dt = dS_ω) gives S_{dω} = i_1^#ω − i_0^#ω − dS_ω (k ≥ 1), resp. S_{dω} = i_1^#ω − i_0^#ω (k = 0). Applying X and using X(dS_ω) = ∂X(S_ω) = ([[0,1]] × ∂X)(ω) gives the formula.
 (e) Mass: if M(X) < ∞ then M([[0,1]] × X) ≤ M(X) and M({s} × X) ≤ M(X). By A0, ([[0,1]] × X)(ω) = ∫ ξ_X(x)(S_ω(x)) dμ_X, and by 0(a), (L1) with ‖J‖ ≤ 1 and (L2) with |e₀| = 1: |S_ω(x)| ≤ ∫_0^1 |ω₁(t, x)| dt ≤ ∫_0^1 |ι_{e₀}ω(ι(t, x))| dt ≤ ‖ω‖. So |([[0,1]] × X)(ω)| ≤ M(X)‖ω‖; similarly |i_s^#ω(x)| ≤ |ω(ι(s, x))| by (L1). Conclude by 0(b).
 (f) Consequently, for X ∈ NC_k(ℝ^N): [[0,1]] × X has compact support (a closed subset of the compact ι([0,1] × spt X)), M([[0,1]] × X) ≤ M(X) < ∞, and by (d), (e) and ∂X ∈ NC_{k−1}: M(∂([[0,1]] × X)) ≤ 2M(X) + M(∂X) < ∞ (≤ 2M(X) for k = 0). Thus [[0,1]] × X ∈ NC_{k+1}(ℝ^{N+1}), and [[0,1]] × ∂X ∈ NC_k(ℝ^{N+1}) for k ≥ 1.

4. A3 (Smooth homotopy formula). Let X ∈ NC_k(ℝ^N), F, G : ℝ^N → ℝ^{N'} C^∞ with ‖DF‖, ‖DG‖ ≤ Λ everywhere, and H : ℝ^{N+1} → ℝ^{N'} C^∞ with H(ι(t, x)) = F(x) + t(G(x) − F(x)) for all ι(t, x) in an open set O ⊇ ι([0,1] × spt X). H_# denotes A1 in ℝ^{N+1}, applicable to [[0,1]] × X and [[0,1]] × ∂X by A2(f). Then
 (i) G_#X − F_#X = ∂H_#([[0,1]] × X) + H_#([[0,1]] × ∂X) for k ≥ 1, and G_#X − F_#X = ∂H_#([[0,1]] × X) for k = 0;
 (ii) M(H_#([[0,1]] × X)) ≤ sup_{x ∈ spt X}|G(x) − F(x)| · (2Λ)^k · M(X).
 Proof of (i). By A1(c) in ℝ^{N+1}, A2(d) and A1(b): ∂H_#([[0,1]] × X) = H_#({1} × X) − H_#({0} × X) − H_#([[0,1]] × ∂X) (last term absent for k = 0). For s ∈ {0, 1}, H_#({s} × X)(ω) = X(i_s^#(ζ̃H^#ω)) with ζ̃ = 1 near ι([0,1] × spt X); by the chain rule i_s^#(H^#ω) = (H ∘ ι(s, ·))^#ω, and H ∘ ι(s, ·) equals G (s = 1), resp. F (s = 0), on the open set {x : ι(s, x) ∈ O} ⊇ spt X, where also ζ̃(ι(s, ·)) = 1 near spt X. By (S3), H_#({1} × X) = G_#X and H_#({0} × X) = F_#X; rearrange.
 Proof of (ii). With ω̃ := ζ̃H^#ω: H_#([[0,1]] × X)(ω) = X(S_{ω̃}) = ∫ ξ_X(x)(S_{ω̃}(x)) dμ_X (A0). For x ∈ spt X and t ∈ [0,1], ω̃ = H^#ω near ι(t, x), DH(ι(t, x))e₀ = G(x) − F(x) and DH(ι(t, x)) ∘ J = (1 − t)DF(x) + tDG(x) =: A_t(x) (differentiate the identity H(ι(t, x)) = F(x) + t(G(x) − F(x)) valid on O), ‖A_t(x)‖ ≤ 2Λ. By 0(h), ω̃₁(t, x) = (ι_{G(x)−F(x)}ω(H(ι(t, x)))) ∘ A_t(x)^{×k}, so by (L1), (L2) |ω̃₁(t, x)| ≤ (2Λ)^k|G(x) − F(x)|‖ω‖. Integrating in t and against μ_X (total mass M(X), concentrated on spt X): |H_#([[0,1]] × X)(ω)| ≤ δ₀(2Λ)^kM(X)‖ω‖ with δ₀ := sup_{spt X}|G − F|; conclude by 0(b).

5. A4 (Lipschitz push-forward). Let X ∈ NC_k(ℝ^N), F : ℝ^N → ℝ^{N'} Λ-Lipschitz, F_σ as in 0(f).
 (E) For C^∞ F', G' : ℝ^N → ℝ^{N'} with ‖DF'‖, ‖DG'‖ ≤ Λ and δ' := sup_{spt X}|F' − G'|: |G'_#X(ω) − F'_#X(ω)| ≤ δ'((2Λ)^kM(X)‖dω‖ + (2Λ)^{k−1}M(∂X)‖ω‖) (second term absent for k = 0). Proof: fix s ∈ C^∞(ℝ) with s(t) = t on (−1, 2) and s, s' bounded (s(t) := t·b(t), b smooth, b = 1 on [−1, 2], b = 0 outside (−2, 3)), and χ ∈ C^∞_c(ℝ^N), 0 ≤ χ ≤ 1, χ = 1 on an open W_χ ⊇ spt X (0(e)). H(y) := F'(tail y) + s(y_0)χ(tail y)(G' − F')(tail y) is C^∞ and equals F' + t(G' − F') on the open set ι((−1, 2) × W_χ) ⊇ ι([0,1] × spt X). By A3(i), G'_#X(ω) − F'_#X(ω) = H_#([[0,1]] × X)(dω) + H_#([[0,1]] × ∂X)(ω); by A3(ii) for X and for ∂X ∈ NC_{k−1} (spt ∂X ⊆ spt X) and 0(b), (E) follows.
 (a) Existence and mass. For σ, τ > 0, sup|F_σ − F_τ| ≤ Λ(σ + τ), so by (E) (F_σ)_#X(ω) is Cauchy as σ ↓ 0; define F_#X(ω) := lim_{σ↓0}(F_σ)_#X(ω). By A1(a), |(F_σ)_#X(ω)| ≤ Λ^kM(X)‖ω‖, hence |F_#X(ω)| ≤ Λ^kM(X)‖ω‖. F_#X is linear in ω, so (0(b)) it is a current with M(F_#X) ≤ Λ^kM(X). F_#X does not depend on Λ.
 (b) Boundary. For X ∈ NC_{k+1}: ∂F_#X(ω) = F_#X(dω) = lim(F_σ)_#X(dω) = lim(F_σ)_#∂X(ω) = F_#∂X(ω) (A1(c); ∂X ∈ NC_k).
 (c) Smooth maps. If F is C^∞ and Λ-Lipschitz, the A4 push-forward equals the A1 push-forward: by (E) with F' = F_σ, G' = F (δ' ≤ Λσ) the difference tends to 0. In particular id_#X(ω) = X(ζω) = X(ω) by (S3), i.e. id_#X = X.
 (d) Support. spt F_#X ⊆ F(spt X): if tsupport ω ∩ F(spt X) = ∅, these compact sets have positive distance d₀, and for Λσ < d₀, F_σ(spt X) ∩ tsupport ω = ∅, so (F_σ)_#X(ω) = 0 (argument of A1(d)); hence F_#X(ω) = 0 and (S1) applies. (If spt X = ∅ then X = 0 by (S4) and F_#X = 0.)
 (e) Locality and linearity. If F, G are Λ-Lipschitz and |F − G| ≤ δ on spt X, then |F_#X(ω) − G_#X(ω)| ≤ δ((2Λ)^kM(X)‖dω‖ + (2Λ)^{k−1}M(∂X)‖ω‖): apply (E) to F_σ, G_σ (sup_{spt X}|F_σ − G_σ| ≤ δ + 2Λσ) and let σ ↓ 0. In particular F_#X = G_#X if F = G on spt X. For X, Y ∈ NC_k, (F_σ)_#(X − Y) = (F_σ)_#X − (F_σ)_#Y (A1(b)); in the limit F_#(X − Y) = F_#X − F_#Y (X − Y ∈ NC_k by 0(d)).
 (f) Homotopy formula. Let F, G : ℝ^N → ℝ^{N'} be Λ-Lipschitz and H : ℝ^{N+1} → ℝ^{N'} Lipschitz with H(ι(t, x)) = F(x) + t(G(x) − F(x)) for x ∈ spt X, t ∈ [0,1]. Then G_#X − F_#X = ∂H_#([[0,1]] × X) + H_#([[0,1]] × ∂X) for k ≥ 1 (without the last term for k = 0), and M(H_#([[0,1]] × X)) ≤ δ(2Λ)^kM(X) whenever δ ∈ ℝ and |F − G| ≤ δ on spt X. (Here H_# is the A4 push-forward in ℝ^{N+1} of [[0,1]] × X ∈ NC_{k+1} and [[0,1]] × ∂X ∈ NC_k, A2(f).)
 Proof. Independence of H: if H, H' are Lipschitz (common constant) and agree on ι([0,1] × spt X), which contains spt([[0,1]] × X) and spt([[0,1]] × ∂X) (A2(c), (S2)), then H_#Y = H'_#Y for Y = [[0,1]] × X, [[0,1]] × ∂X by (e) in ℝ^{N+1} with δ = 0. So it suffices to treat H_*(y) := F(tail y) + s(y_0)χ(tail y)(G − F)(tail y) (s, χ as in (E)), which agrees with F + t(G − F) on ι([0,1] × spt X) and is Lipschitz (uniform limit of the L₀-Lipschitz maps H_σ below). For σ ∈ (0, 1] put H_σ(y) := F_σ(tail y) + s(y_0)χ(tail y)(G_σ − F_σ)(tail y). It is C^∞; ∂_tH_σ = s'χ(G_σ − F_σ) and D_xH_σ = DF_σ + s[(G_σ − F_σ) ⊗ Dχ + χ(DG_σ − DF_σ)] are bounded uniformly in σ ≤ 1 (|G_σ − F_σ| ≤ |G − F| + 2Λ is bounded on the compact tsupport χ; ‖DF_σ‖, ‖DG_σ‖ ≤ Λ), so all H_σ are L₀-Lipschitz for one L₀; H_σ = F_σ + t(G_σ − F_σ) on ι((−1, 2) × W_χ) ⊇ ι([0,1] × spt X); and sup|H_σ − H_*| ≤ (1 + 2 sup|s|)Λσ. By A3 for F_σ, G_σ, H_σ (A1 push-forwards, equal to A4 push-forwards by (c)): (G_σ)_#X − (F_σ)_#X = ∂(H_σ)_#([[0,1]] × X) + (H_σ)_#([[0,1]] × ∂X) and M((H_σ)_#([[0,1]] × X)) ≤ sup_{spt X}|G_σ − F_σ|(2Λ)^kM(X). Let σ = σ_j := 1/(j+1). The left side converges weakly to G_#X − F_#X (definition (a)); by (e) in ℝ^{N+1} (constant max(L₀, Lip H_*), δ = sup|H_σ − H_*| → 0), (H_σ)_#Y → (H_*)_#Y weakly for both Y; boundaries of weakly convergent sequences converge weakly. The weak limits agree on every test form, so the currents are equal (GeometricCurrentOn.ext). For the mass: sup_{spt X}|G_σ − F_σ| ≤ δ + 2Λσ, and lower semicontinuity (0(b)) gives M((H_*)_#([[0,1]] × X)) ≤ δ(2Λ)^kM(X) when δ ≥ 0. If δ < 0 the hypothesis forces spt X = ∅, so X = 0 (S4), [[0,1]] × X = 0 and its push-forward is 0 by (e); both sides vanish (ENNReal.ofReal δ = 0).

6. Definitions. lpush_{N,N',k}(F, X) := F_#X (A4) if F is Lipschitz for some constant and X ∈ NC_k(ℝ^N), and := 0 otherwise. cyl_{N,k}(X) := [[0,1]] × X (A2(b)).

7. Verification of the twelve conjuncts (NC X means IsCompact X.support, X.mass < ∞, boundaryMassOn X univ < ∞; push-forwards of NC currents by Lipschitz maps are A4 push-forwards).
 (1) lpush N N k (fun x => x) X = X for NC X: A4(c).
 (2) lpush(F, X − Y) = lpush(F, X) − lpush(F, Y): A4(e); X − Y ∈ NC_k by 0(d).
 (3) EqOn F G (spt X) ⇒ lpush(F, X) = lpush(G, X): A4(e) with δ = 0.
 (4) Mass ≤ Λ^k·M(X) and support ⊆ F '' spt X: A4(a), A4(d).
 (5) X ∈ 𝒟_{k+1} with compact support and M(X), M(∂X) < ∞ is in NC_{k+1} and ∂X ∈ NC_k; A4(b).
 (6) Put F_j := F_{σ_j}, σ_j := 1/(j+1): C^∞ (ContDiff ℝ (⊤ : ℕ∞)), Λ-Lipschitz, sup|F_j − F| ≤ Λσ_j → 0, i.e. TendstoUniformly F_j F. Given ω, fix ζ as in 0(e) for spt X (ζ = 1 on an open W ⊇ spt X) and η_j := ζF_j^#ω ∈ 𝒟^k(ℝ^N). Then η_j = F_j^#ω on W, and X(η_j) = (F_j)_#X(ω) (A1) → F_#X(ω) = lpush(F, X)(ω) (A4(a)).
 (7) A2(f) and A2(c): cyl(X) has compact support, finite mass and finite boundary mass, and spt cyl(X) ⊆ ι([0,1] × spt X) = {y : ∃ t ∈ [0,1], ∃ x ∈ spt X, y = ι(t, x)}.
 (8) cyl(X − Y) = cyl(X) − cyl(Y): A2(b) (both sides send ω to X(S_ω) − Y(S_ω)).
 (9) Given ω ∈ 𝒟^{k+1}(ℝ^{N+1}), η := S_ω ∈ 𝒟^k(ℝ^N) (A2(a)) satisfies η(x)(v) = ∫_0^1 ω₁(t, x)(v) dt = ∫_0^1 ω(ι(t, x))(e₀, Jv_1, …, Jv_k) dt for all x, v (Lean: the integrand is ω (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))), and cyl(X)(ω) = X(S_ω) by definition.
 (10) Degree 0: X ∈ 𝒟_0 with compact support and finite mass is in NC_0; A4(f) with the given L-Lipschitz H gives lpush(G, X) − lpush(F, X) = ∂lpush(H, cyl(X)).
 (11) Degree k + 1: A4(f) gives lpush(G, X) − lpush(F, X) = ∂lpush(H, cyl(X)) + lpush(H, cyl(∂X)), which is the stated identity after subtracting lpush(H, cyl(∂X)) (currents subtract pointwise on test forms).
 (12) A4(f) mass bound, with ENNReal.ofReal δ = max(δ, 0). ∎

## Key steps

1. Conventions: |·| is a norm; |T(ω)| ≤ M(T)‖ω‖ and bounded functionals are currents; support facts (S1)–(S4) from (VO); NC closed under differences and ∂; cut-offs; mollifiers F_σ (C^∞, Λ-Lipschitz, |F_σ − F| ≤ Λσ).
2. A0: a finite-mass current is ∫ξ_X dμ_X with μ_X(ℝ^N) = M(X) and μ_X concentrated on spt X (REP, VO).
3. A1: smooth push-forward F_#X(ω) = X(ζF^#ω): a current with mass ≤ sup‖DF‖^k M(X) (L1), ∂F_#X = F_#∂X, spt ⊆ F(spt X), linear in X.
4. A2: [[0,1]] × X(ω) = X(S_ω) with the slice integral S_ω; S_ω is a test form depending continuously on ω; support in ι([0,1] × spt X); ∂([[0,1]] × X) = {1}×X − {0}×X − [[0,1]]×∂X from the coordinate formula for d; mass ≤ M(X) by (L1), (L2); NC preserved.
5. A3: smooth homotopy formula G_#X − F_#X = ∂H_#([[0,1]]×X) + H_#([[0,1]]×∂X) and M(H_#([[0,1]]×X)) ≤ sup|G − F|(2Λ)^k M(X).
6. A4: estimate (E) via a cut-off smooth homotopy; F_#X := lim (F_σ)_#X; mass, boundary, smooth case and identity, support, locality and linearity; Lipschitz homotopy formula by H_σ → H_*, weak convergence and lower semicontinuity of mass.
7. Definitions lpush := F_#X (Lipschitz F, NC X; 0 otherwise), cyl := [[0,1]] × X, and verification of the twelve conjuncts, including interface (6) (mollifiers F_{1/(j+1)} with cut-off pull-backs ζF_j^#ω) and interface (9) (η := S_ω).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest.json)`
- `rg -n 'cmcdt_lp' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n -i 'lipschitz.*push|pushforward|homotopy|LipschitzPushforward' project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm|polyhedral chain' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'noncomputable def curryLeft|theorem curryLeft_apply_apply' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem LipschitzWith.ae_differentiableAt|theorem LinearMap.exists_antilipschitzWith|theorem integral_lineDeriv_mul_eq|theorem ae_convolution_tendsto_right_of_locallyIntegrable|theorem Orthonormal.exists_orthonormalBasis_extension|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|lemma tendsto_tsum_of_dominated_convergence|theorem volume_preserving_piFinSuccAbove|theorem exists_contDiff_tsupport_subset|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le|theorem _root_.MeasurableSet.exists_isCompact_lt_add' mathlib/Mathlib -g '*.lean' (all found)`
- `grep -rn for measurableSet_of_differentiableAt, measurable_fderiv, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, ContDiffBump.normed, HasCompactSupport.contDiff_convolution_left, intervalIntegral.integral_eq_sub_of_hasDerivAt, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp in the pinned Mathlib (all found)`
- `grep in lake-packages-25730c7c/simongmt/Poincare/SimonGMT (Chapter06 Currents/Mass/CurrentLocalEquality/Forms/AffineCurrentPushforward/Product, Chapter03/Rectifiable, Chapter02/AreaDomain/AreaCritical): GeometricCurrentOn, massOn, support, boundary, boundary_boundary, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, exteriorDerivative_apply, exteriorDerivativeOn_pullbackFormWithin, tsupport_exteriorDerivative_subset, affinePullbackTestOn, TestFormOnConverges.affinePullback, CountablyRectifiable, countablyRectifiable_range, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, area_image_criticalSet_eq_zero (all found)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: frozen types of the selected node, its siblings and cmcdt_im_series; lean_name scan for push/homot/covector/tangent/rectifiable lemmas; accepted covectorEuclideanNorm and HasApproximateTangentSpaceAt declarations; no name with prefix cmcdt_lp_`
- `grep of the controller (runtime/flows/*/_recursive_lean/runtime.py: _existing_lean_name_problem, _install_parent_supplied_child_handoff, _overlay_accepted_children) for the cross-branch reuse semantics`
- `lake env lean /tmp/lpdecomp/lean/T_L.lean, T_O.lean, T_I.lean (child types elaborate); lake env lean /tmp/lpdecomp/lean/Interface.lean (instance checks and interface derivation; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/lpdecomp/lean/AssemblyFull.lean (sorry-free Part C assembly from the IMS, operators and integrality types to the exact selected frozen type; axioms propext, Classical.choice, Quot.sound)`
- `sed -n 360,620p and 760,900p book/chapter-06.txt (Simon 6.2.17–2.33 and 6.3.3–3.12, the source of Parts A and B)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lpdecomp/lean/T_L.lean`
- `/tmp/lpdecomp/lean/T_O.lean`
- `/tmp/lpdecomp/lean/T_I.lean`
- `/tmp/lpdecomp/lean/Interface.lean`
- `/tmp/lpdecomp/lean/AssemblyFull.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Contract.lean and Submission.lean. Its only Lipschitz push-forward material is the unsolved Ch06 specification (project/GMT/Ch06/Contract.lean and Submission.lean: IsLipschitzPushforward, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). It is written over a different Euclidean type (Eucl), cannot be imported into Ch07 and contains no proofs, so nothing in it is reusable. Mathlib has no flat-norm, deformation or polyhedral-chain results (no match). It does provide every tool cited by the child proofs: curryLeft as interior product, Rademacher, the approximately-linear partition, antilipschitz bounds for injective maps, mollification with a.e. convergence of derivatives, density and Lebesgue points, inner regularity, differentiation under interval integrals, the Fubini splitting of volume on Euclid (n+1), and Tannery's theorem. SimonGMT provides currents, mass, support, weak convergence with lower semicontinuity of mass, the exterior-derivative and pull-back formulas, affine pull-back of test forms, rectifiability, approximate tangent spaces with uniqueness, and the area formulas. No DAG node, snapshot file or Mathlib declaration uses the prefix cmcdt_lp_. All three child types elaborate. The interface derivation compiles with axioms propext, Classical.choice and Quot.sound. The sorry-free Part C assembly compiles to the exact selected frozen type with axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
