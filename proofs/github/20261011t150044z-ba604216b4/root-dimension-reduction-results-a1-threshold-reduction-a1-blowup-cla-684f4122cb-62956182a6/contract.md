<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1 -->

## Theorem `Submission.dimred_tr_bc_class_tangent`

Assume (IM) — the frozen type of the grandparent's registered dependency im_mass_measure, which is the selected node's first leading hypothesis: for all P, n ∈ ℕ, every open U ⊆ ℝ^P, every T ∈ 𝒟_n(U) and every IMRep R of T in U: (a) M_W(T) = R.measure(W) for every open W ⊆ U; (b) for x ∈ U, x ∈ spt T if and only if R.measure(B_ε(x)) ≠ 0 for every ε > 0; (c) R′.measure = R.measure for every IMRep R′ of T in U. Assume (MON) — the frozen type of the grandparent's registered dependency monotonicity (the selected node's second leading hypothesis): for all P, n, d ∈ ℕ with 1 ≤ n ≤ d ≤ P, every open U ⊆ ℝ^P, every embedded C² d-dimensional submanifold N with (closure N ∖ N) ∩ U = ∅ and every T ∈ 𝒟_n(U) minimizing in U ∩ N with spt T ⊆ U ∩ N and ∂T = 0: (i) for every compact K ⊆ U there is Λ ≥ 0 such that ρ ↦ ofReal(e^{Λρ}/ρⁿ)·M_{B_ρ(y)}(T) is monotone on (0, R) whenever B̄_R(y) ⊆ K; (ii) if N = ℝ^P, then ρ ↦ ofReal(1/ρⁿ)·M_{B_ρ(y)}(T) is monotone on (0, R) whenever B_R(y) ⊆ U; (iii) there is Θ, upper semicontinuous on U, with HasMassDensity T y (Θ y) for all y ∈ U; (iv) every density of T at a point of spt T is ≥ 1. Assume (MB) — the frozen type of the grandparent's registered dependency moving_blowups (the selected node's third leading hypothesis): for all n, k, ℓ ∈ ℕ with ℓ ≤ k, U, N ⊆ ℝ^{n+k} and T ∈ 𝒟_n(U) with 1 ≤ n, U open, N an embedded C² (n+ℓ)-dimensional submanifold, (closure N ∖ N) ∩ U = ∅, T minimizing in U ∩ N, spt T ⊆ U ∩ N and ∂T = 0 in U, and for all x ∈ U, x_j → x and λ_j > 0 with λ_j → 0, there are a strictly increasing φ and C ∈ 𝒟_n(ℝ^{n+k}) such that blowUp T x_{φ(j)} λ_{φ(j)} ⇀ C in ℝ^{n+k} (ConvergesWeakly), MassMeasuresConverge holds for the same sequence, C is minimizing in ℝ^{n+k} and ∂C = 0. Assume (TAN) — the selected node's fourth leading hypothesis, verbatim the conclusion of tangent_measure_homogeneous (a sibling of the selected node, not a dependency of this child) after its hypotheses (MON), (MB); here (TAN) is used only as a hypothesis and no declaration is needed: for n, k, ℓ, U, N, T as in (MB), every x ∈ spt T and every sequence λ_j > 0 with λ_j → 0 there are a strictly increasing φ and C ∈ 𝒟_n(ℝ^{n+k}) with blowUp T x λ_{φ(j)} ⇀ C (ConvergesWeakly), MassMeasuresConverge for the same sequence, C minimizing in ℝ^{n+k}, and R.measure((v ↦ λv)(A)) = ofReal(λⁿ)·R.measure(A) for every IMRep R of C in ℝ^{n+k}, every λ > 0 and every Borel A. Assume (BC) — the frozen type of the selected node's registered dependency blowup_calculus: for all P, n ∈ ℕ, U ⊆ ℝ^P, T ∈ 𝒟_n(U), x ∈ ℝ^P and λ > 0: (i) M_W(blowUp T x λ) = ofReal(λ⁻¹ⁿ)·M_{(dilation x λ)⁻¹(W)}(T) for every W; (ii) currentEval (blowUp T x λ) ω = currentEval T (affinePullbackForm (dilationCLM P λ) (−(λ⁻¹•x)) ω) for every n-form ω on ℝ^P; (iii) currentEval (blowUp (blowUp T x λ) y μ) ω = currentEval (blowUp T (x + λ•y) (λμ)) ω for all y ∈ ℝ^P, μ > 0 and n-forms ω. Assume (BUI) — the frozen type of the selected node's registered dependency blowup_imrep (the reused accepted rep_pushforward): for all P, n ∈ ℕ, U ⊆ ℝ^P, T ∈ 𝒟_n(U), x ∈ ℝ^P, λ > 0 and every IMRep R of T in U there is an IMRep R′ in dilation x λ '' U representing blowUp T x λ with R′.measure(s) = ofReal(λ⁻¹ⁿ)·R.measure((dilation x λ)⁻¹(s)) for every Borel s. Assume (IBL) — the frozen type of the selected node's registered dependency iterated_blowup_limit: for all P, n ∈ ℕ, every open U ⊆ ℝ^P, T ∈ 𝒟_n(U), x ∈ U, x_i → x, λ_i > 0 with λ_i → 0, S ∈ 𝒟_n(ℝ^P), y ∈ ℝ^P, s_k > 0 with s_k → 0 and C ∈ 𝒟_n(ℝ^P): if there are δ > 0 and Γ with M_{B_ρ(x′)}(T) ≤ ofReal(Γρⁿ) for all x′ ∈ B_δ(x) and 0 < ρ < δ, blowUp T x_i λ_i ⇀ S and blowUp S y s_k ⇀ C (ConvergesWeakly), then there is a strictly increasing φ with blowUp T (x_{φ(k)} + λ_{φ(k)}•y) (λ_{φ(k)}s_k) ⇀ C. Let n, k, ℓ ∈ ℕ with ℓ ≤ k and 1 ≤ n, let U ⊆ ℝ^{n+k} be open, N an embedded C² (n+ℓ)-dimensional submanifold with (closure N ∖ N) ∩ U = ∅, and T ∈ 𝒟_n(U) minimizing in U ∩ N with spt T ⊆ U ∩ N and ∂T = 0 in U. Let z ∈ ℝ^{n+k} and r > 0 with B̄_{2r}(z) ⊆ U, and let RT be an IMRep of T in U; write μ_T := RT.measure, W := B_{2r}(z) and η_{a,t} := dilation a t (η_{a,t}(v) = t⁻¹(v − a)). Let 𝓜 be a set of measures on ℝ^{n+k} such that μ ∈ 𝓜 if and only if either (PS) μ = ofReal(t⁻¹ⁿ) • (μ_T⌞W).map η_{a,t} for some a ∈ ℝ^{n+k} and some t with 0 < t ≤ r and dist(a, z) ≤ r − t; or (ZS) μ = RS.measure for some S ∈ 𝒟_n(ℝ^{n+k}) and some IMRep RS of S in ℝ^{n+k} for which there are points c_i, scales t_i > 0 (i ∈ ℕ) and a point b with dist(c_i, z) < r − t_i for every i, t_i → 0, c_i → b, and blowUp T c_i t_i ⇀ S in ℝ^{n+k} (ConvergesWeakly). (These are the selected node's positive-scale members μ_{x,λ} and zero-scale members, with (a, t) = (z + rx, rλ), c_i = z + rx_i, t_i = rλ_i, b = z + rx̄.) Then for every μ ∈ 𝓜, every y ∈ ℝ^{n+k} with ‖y‖ < 1 and every strictly decreasing sequence λ_j > 0 with λ_j → 0 there are a strictly increasing sub : ℕ → ℕ and ν ∈ 𝓜 such that ν((v ↦ λv)(s)) = ofReal(λⁿ)·ν(s) for every λ > 0 and every Borel s, and ∫ f d(ofReal(λ_{sub(j)}⁻¹ⁿ) • μ.map(dilation y λ_{sub(j)})) → ∫ f dν as j → ∞ for every continuous f : ℝ^{n+k} → ℝ with compact support.

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7948

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6873, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8618, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8623

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8825, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8829, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8830, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8831, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7512

## Lean problem

Declaration: `Submission.dimred_tr_bc_class_tangent`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ x ∈ T.support, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ ∀ R : IMRep (univ : Set (Euclid (n + k))) n, R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid (n + k)), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → Tendsto ss atTop (𝓝 0) → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball x δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => blowUp T (xs (φ k) + lams (φ k) • y) (lams (φ k) * ss k) (mul_pos (hlams (φ k)) (hss k)).ne') C) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → (∀ μ ∈ 𝓜, ∀ y : Euclid (n + k), ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid (n + k))), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ lam : ℝ, 0 < lam → ∀ s : Set (Euclid (n + k)), MeasurableSet s → ν ((fun x => lam • x) '' s) = ENNReal.ofReal (lam ^ n) * ν s) ∧ ∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν)))
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

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the selected node's supplied proof (parent 2(e), 3(vii); Simon 7.3.3, proof of (1): the hypotheses of A.4 for 𝒯, chapter-07.txt lines 443–486, with the tangent cones of 7.3.1(2) and 7.3.2), together with the preliminaries (0a)–(0l) it uses, in the parametrization (a, t) = (z + rx, rλ) of positive-scale members and (c_i, t_i, b) = (z + rx_i, rλ_i, z + rx̄) of zero-scale data. Siblings used: zero_limit_minimizing (Submission.dimred_tr_bc_zero_limit_minimizing, with (MB)), vanishing_blowup (Submission.dimred_tr_bc_vanishing_blowup, with (BC)) and ambient_calculus (Submission.idtp_fons_cc_ambient_calculus) parts (1), (2), (3), (7). The hypotheses (IM), (MON), (TAN), (BUI), (IBL) are used exactly where the supplied proof cites them.
Notation: E := ℝ^{n+k}; Hⁿ := μHE[n]; for a measure m, a ∈ E and s > 0, m^{a,s} := ofReal(s⁻¹ⁿ) • m.map(dilation a s); μ_T := RT.measure; W := B_{2r}(z); K := B̄_{2r}(z).
Preliminaries.
P1. (Mass equals weight.) By (IM)(a) for T (U open, RT represents T), M_O(T) = μ_T(O) for every open O ⊆ U. By locallyIntegrable_mult of RT, μ_T(K) = ∫⁻_{RT.carrier ∩ K} RT.mult dHⁿ < ∞ (withDensity_apply, Measure.restrict_restrict; K compact, K ⊆ U), hence μ_T(W) < ∞.
P2. (Integrals against rescaled measures.) For a measure m on E, a ∈ E, s > 0 and continuous f: ∫ f dm^{a,s} = s⁻ⁿ·∫ f∘(dilation a s) dm. Indeed (ofReal(s⁻¹ⁿ)).toReal = s⁻ⁿ (integral_smul_measure), and dilation a s is continuous, so integral_map applies (f is continuous, hence AEStronglyMeasurable).
P3. (Support of f∘η.) If tsupport f ⊆ B_{R_f}(0) and η := dilation a s with s > 0, then f(η(v)) ≠ 0 implies v ∈ η⁻¹(B_{R_f}(0)) = B_{sR_f}(a) (ambient_calculus (3) with w = 0). Every continuous f with compact support admits such an R_f > 0 (compact sets are bounded).
P4. (The zero member.) Let R_∅ be the IMRep in E with carrier ∅, multiplicity 0 and orientation 0. Its fields hold: ∅ is Borel and ∅ ⊆ E; ∅ is countably n-rectifiable (countablyRectifiable_of_measure_zero, Hⁿ(∅) = 0); mult_pos is vacuous; lower integrals over ∅ are 0 ≠ ∞; Hⁿ⌞∅ = 0, so the two a.e. fields hold trivially. R_∅.action ω = ∫_∅ … = 0 = (0 : GeometricCurrentOn univ n) ω, so R_∅ represents 0, and R_∅.measure = (Hⁿ⌞∅).withDensity 0 = 0. The zero measure is n-homogeneous: 0((v ↦ λv)(s)) = 0 = ofReal(λⁿ)·0.
P5. (E as ambient manifold.) ambient_calculus (1) gives IsEmbeddedSubmanifold 2 (n + k) univ; also (closure univ ∖ univ) ∩ univ = ∅, univ ∩ univ = univ, IsOpen univ, k ≤ k and spt S ⊆ univ. Hence (TAN) (with ℓ := k and U = N = univ) applies to every S ∈ 𝒟_n(E) that is minimizing in E with ∂S = 0, at every point of spt S.
P6. (Zero-scale data.) If (c_i, t_i, b) are zero-scale data for S (dist(c_i, z) < r − t_i, t_i → 0, c_i → b, blowUp T c_i t_i ⇀ S), then dist(b, z) ≤ r (dist(c_i, z) ≤ r for all i and dist(·, z) is continuous: le_of_tendsto), so b ∈ B̄_r(z) ⊆ K ⊆ U. zero_limit_minimizing (with (MB), the hypotheses of T and x := b) shows that S is minimizing in E and ∂S = 0.
P7. (IMReps of blow-ups.) For a current A on a domain O with an IMRep R, a ∈ E and s > 0, (BUI) gives an IMRep R′ in dilation a s '' O representing blowUp A a s with R′.measure(B) = ofReal(s⁻¹ⁿ)·R.measure((dilation a s)⁻¹(B)) for Borel B. The measure (R.measure)^{a,s} is given on Borel sets by the same formula (Measure.smul_apply, Measure.map_apply; dilation is measurable), so R′.measure = (R.measure)^{a,s} (Measure.ext).
P8. (Mass bound for (IBL).) Apply (MON) to T with d := n + ℓ (1 ≤ n ≤ n + ℓ ≤ n + k) and part (i) to the compact K ⊆ U: there is Λ_K ≥ 0 such that τ ↦ ofReal(e^{Λ_Kτ}/τⁿ)·M_{B_τ(c′)}(T) is monotone on (0, R′) whenever B̄_{R′}(c′) ⊆ K. Let b ∈ B̄_r(z), δ := r/4, Γ′ := ofReal(e^{Λ_K r/4}/(r/4)ⁿ)·μ_T(W) (finite by P1) and Γ := Γ′.toReal. Let x′ ∈ B_δ(b) and 0 < ρ < δ. Then dist(x′, z) < 5r/4, so B̄_{r/2}(x′) ⊆ K and B_{r/4}(x′) ⊆ W ⊆ U. Monotonicity on (0, r/2), at ρ < r/4, gives ofReal(e^{Λ_Kρ}/ρⁿ)·M_{B_ρ(x′)}(T) ≤ ofReal(e^{Λ_K r/4}/(r/4)ⁿ)·M_{B_{r/4}(x′)}(T) ≤ Γ′, because M_{B_{r/4}(x′)}(T) = μ_T(B_{r/4}(x′)) ≤ μ_T(W) (P1). As e^{Λ_Kρ} ≥ 1, ofReal(1/ρⁿ)·M_{B_ρ(x′)}(T) ≤ Γ′, so M_{B_ρ(x′)}(T) ≤ ofReal(ρⁿ)·Γ′ = ofReal(Γρⁿ). Thus the mass hypothesis of (IBL) holds at b with (δ, Γ).
P9. (Tails and parameter congruence.) If evaluations converge along a sequence, they converge along each tail j ↦ j + j₀ (Tendsto.comp with tendsto_add_atTop_nat); so ConvergesWeakly passes to tails. Blow-ups with equal centres and scales are equal currents (the nonvanishing proofs are irrelevant).
Main argument. Let μ ∈ 𝓜, y ∈ E with ‖y‖ < 1, and λ_j > 0 strictly decreasing with λ_j → 0 (only λ_j > 0 and λ_j → 0 are used). By the class hypothesis μ is (PS) or (ZS).
1. Case (PS): μ = (μ_T⌞W)^{a,t} with 0 < t ≤ r and dist(a, z) ≤ r − t. Put p := a + t•y.
 (a) By ambient_calculus (7), μ^{y,s} = (μ_T⌞W)^{p,ts} for every s > 0.
 (b) dist(p, z) ≤ dist(a, z) + t‖y‖ ≤ r − t + t‖y‖ < r. Put d := r − dist(p, z) > 0. Then p ∈ B_r(z) ⊆ U, and B_ρ(p) ⊆ W for every ρ ≤ r.
 (c) Choose j₀ with tλ_j < d for all j ≥ j₀ (λ_j → 0).
 Case (PS-i): p ∈ spt T. Apply (TAN) to T (with its hypotheses) at x := p with the scales tλ_j > 0 (tλ_j → 0). It gives a strictly increasing φ and C ∈ 𝒟_n(E) with blowUp T p (tλ_{φ(j)}) ⇀ C, MassMeasuresConverge for the same sequence, C minimizing in E, and n-homogeneous weights for every IMRep of C. C is integer multiplicity (the first conjunct of IsMinimizingIn); fix an IMRep R_C of C in E and put ν := R_C.measure, sub := φ.
 – ν ∈ 𝓜: c′_j := p, t′_j := tλ_{φ(j+j₀)} and b′ := p are zero-scale data for C. Indeed φ(j + j₀) ≥ j + j₀ ≥ j₀ (StrictMono.id_le), so t′_j < d, i.e. dist(p, z) < r − t′_j; t′_j → 0; the constant sequence tends to p; and blowUp T p t′_j ⇀ C by P9. As R_C represents C, the class hypothesis gives ν ∈ 𝓜.
 – Homogeneity of ν is the last conclusion of (TAN), applied to R_C.
 – Convergence: let f be continuous with compact support, tsupport f ⊆ B_{R_f}(0). Let R_j be the IMRep of blowUp T p (tλ_{φ(j)}) given by P7 from RT, so R_j.measure = μ_T^{p,tλ_{φ(j)}}. MassMeasuresConverge, applied to (R_j), R_C, f and tsupport f ⊆ univ, gives ∫ f dR_j.measure → ∫ f dν. For every j with tλ_{φ(j)}R_f < r (all large j), put η := dilation p (tλ_{φ(j)}). By P2 and (a), ∫ f dμ^{y,λ_{φ(j)}} = (tλ_{φ(j)})⁻ⁿ ∫ f∘η d(μ_T⌞W) and ∫ f dR_j.measure = (tλ_{φ(j)})⁻ⁿ ∫ f∘η dμ_T. By P3 and (b), f∘η vanishes outside B_{tλ_{φ(j)}R_f}(p) ⊆ W, so ∫ f∘η d(μ_T⌞W) = ∫ f∘η dμ_T (setIntegral_eq_integral_of_forall_compl_eq_zero). The two sequences agree eventually, hence ∫ f dμ^{y,λ_{φ(j)}} → ∫ f dν (Tendsto.congr').
 Case (PS-ii): p ∉ spt T. As p ∈ U, vanishing_blowup (with (BC)) gives ε > 0 with B_ε(p) ⊆ U, M_{B_ε(p)}(T) = 0 and blowUp T p s_j ⇀ 0 for every sequence s_j > 0 with s_j → 0. By P1, μ_T(B_ε(p)) = 0. Put ν := 0 = R_∅.measure (P4) and sub := id.
 – ν ∈ 𝓜: c′_j := p, t′_j := tλ_{j+j₀} and b′ := p are zero-scale data for the zero current: dist(p, z) < r − t′_j by (c); t′_j → 0; c′_j → p; and blowUp T p t′_j ⇀ 0 by vanishing_blowup. As R_∅ represents 0, 0 ∈ 𝓜.
 – ν = 0 is homogeneous (P4).
 – Convergence: for f as above and j with tλ_jR_f < ε, put η := dilation p (tλ_j). By P2 and (a), ∫ f dμ^{y,λ_j} = (tλ_j)⁻ⁿ ∫ f∘η d(μ_T⌞W). By P3, f∘η vanishes outside B_ε(p), which is μ_T-null and hence (μ_T⌞W)-null, so f∘η = 0 a.e. and the integral is 0 (integral_eq_zero_of_ae). The sequence is eventually 0, so it tends to 0 = ∫ f d0 (integral_zero_measure).
2. Case (ZS): μ = RS.measure, RS an IMRep of S in E, with zero-scale data (c_i, t_i, b). By P6, S is minimizing in E with ∂S = 0, and b ∈ B̄_r(z) ⊆ U. By P8, the mass hypothesis of (IBL) holds at b.
 Case (ZS-i): y ∈ spt S. By P5, (TAN) applies to S at y with the scales λ_j: it gives a strictly increasing φ and C ∈ 𝒟_n(E) with blowUp S y λ_{φ(j)} ⇀ C, MassMeasuresConverge for the same sequence, C minimizing in E, and n-homogeneous weights. Fix an IMRep R_C of C; ν := R_C.measure, sub := φ.
 – Convergence: by P7 (A := S, R := RS), the IMRep R′_j of blowUp S y λ_{φ(j)} has weight RS.measure^{y,λ_{φ(j)}} = μ^{y,λ_{φ(j)}}. MassMeasuresConverge, applied to (R′_j), R_C, f and tsupport f ⊆ univ, gives ∫ f dμ^{y,λ_{φ(j)}} → ∫ f dν.
 – Homogeneity of ν: the last conclusion of (TAN).
 – ν ∈ 𝓜: apply (IBL) with P := n + k, U (open), T, x := b ∈ U, xs := (c_i), lams := (t_i), S, y, ss := (λ_{φ(k)}) (positive, → 0) and C. Its hypotheses are c_i → b, t_i → 0, λ_{φ(k)} → 0, the mass bound of P8, blowUp T c_i t_i ⇀ S and blowUp S y λ_{φ(k)} ⇀ C. It yields a strictly increasing φ′ with blowUp T (c_{φ′(k)} + t_{φ′(k)}•y) (t_{φ′(k)}λ_{φ(k)}) ⇀ C. Since λ_{φ(k)} → 0 and 1 − ‖y‖ > 0, choose k₀ with λ_{φ(k)} ≤ 1 − ‖y‖ for all k ≥ k₀. Put i(k) := φ′(k + k₀), c″_k := c_{i(k)} + t_{i(k)}•y, t″_k := t_{i(k)}λ_{φ(k+k₀)} > 0 and b″ := b. These are zero-scale data for C: dist(c″_k, z) ≤ dist(c_{i(k)}, z) + t_{i(k)}‖y‖ < (r − t_{i(k)}) + t_{i(k)}(1 − λ_{φ(k+k₀)}) = r − t″_k; t″_k → 0 (a product of two sequences tending to 0); c″_k → b + 0•y = b; and blowUp T c″_k t″_k ⇀ C by P9. As R_C represents C, ν ∈ 𝓜.
 Case (ZS-ii): y ∉ spt S. vanishing_blowup, applied to S (domain univ, y ∈ univ), gives ε > 0 with M_{B_ε(y)}(S) = 0 and blowUp S y s_k ⇀ 0 for every sequence s_k > 0 with s_k → 0. By (IM)(a) for S (univ open, RS represents S), μ(B_ε(y)) = RS.measure(B_ε(y)) = M_{B_ε(y)}(S) = 0. Put ν := 0 = R_∅.measure and sub := id.
 – ν ∈ 𝓜: apply (IBL) as in (ZS-i), now with ss := (λ_k), C := 0 and blowUp S y λ_k ⇀ 0. With k₀ such that λ_k ≤ 1 − ‖y‖ for all k ≥ k₀, the data c″_k := c_{φ′(k+k₀)} + t_{φ′(k+k₀)}•y, t″_k := t_{φ′(k+k₀)}λ_{k+k₀} and b are zero-scale data for 0 (same estimates), and R_∅ represents 0. So 0 ∈ 𝓜.
 – ν = 0 is homogeneous (P4).
 – Convergence: for f with tsupport f ⊆ B_{R_f}(0) and λ_jR_f < ε, P2 gives ∫ f dμ^{y,λ_j} = λ_j⁻ⁿ ∫ f∘(dilation y λ_j) dμ, and by P3 the integrand vanishes outside the μ-null set B_ε(y). So the integrals are eventually 0, and they tend to 0 = ∫ f d0.
3. In every case sub is strictly increasing, ν ∈ 𝓜, ν is n-homogeneous, and ∫ f dμ^{y,λ_{sub(j)}} → ∫ f dν for every continuous compactly supported f. ∎

## Key steps

1. Preliminaries: mass equals weight on open sets ((IM)(a)), integrals against rescaled measures, the zero IMRep, ℝ^{n+k} as ambient manifold, minimality of zero-scale limits (zero_limit_minimizing), IMReps of blow-ups ((BUI)), and the mass bound required by (IBL) from (MON)(i).
2. Positive-scale member, p = a + ty ∈ spt T: (TAN) at p with scales tλ_j gives a homogeneous minimizing tangent limit C; its weight is a zero-scale member (constant centres p) and the vague limit, since the rescaled member and the IMRep weight of the blow-up agree on test functions supported in B_{2r}(z).
3. Positive-scale member with p ∉ spt T: vanishing_blowup gives blow-ups ⇀ 0 and a μ_T-null ball, so ν = 0 = R_∅.measure works.
4. Zero-scale member, y ∈ spt S: (TAN) for S at y gives C and vague convergence via MassMeasuresConverge; (IBL) plus a tail argument shows C is again a zero-scale limit of blow-ups of T, so its weight lies in 𝓜.
5. Zero-scale member with y ∉ spt S: vanishing_blowup and (IBL) with C = 0 show 0 ∈ 𝓜, and the rescaled integrals vanish eventually.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Submission.lean`
- `rg -n dimred_tr_bc <snapshot>/project (exit 1, no match); grep -rn dimred_tr_bc GMT .lake/packages/simongmt/Poincare (no match)`
- `rg -n 'def VanishesOn|def zeroRegion|def support|def blowUp|def currentEval|def ConvergesWeakly|def MassMeasuresConverge|structure IMRep|def IMRep.measure' <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem tendsto_nhds_unique |theorem integral_smul_measure|theorem integral_map |theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem withDensity_congr_ae|theorem withDensity_indicator |theorem tendsto_add_atTop_nat|theorem integral_zero_measure|theorem integral_eq_zero_of_ae|theorem StrictMono.id_le' <snapshot>/mathlib/Mathlib`
- `rg -n -e '(theorem|lemma) [A-Za-z_.]*(StrictMono.tendsto_atTop|Tendsto.limsup_eq|closedBall_subset_closedBall_iff|Homeomorph.isProperMap|withDensity_apply |restrict_restrict )' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem tsupport_affinePullbackForm_subset|theorem affinePullbackForm_isTestForm' .lake/packages/simongmt/Poincare/SimonGMT; sed -n on SimonGMT Chapter06 Currents.lean, CurrentLocalEquality.lean, Mass.lean, AffineCurrentPushforward.lean`
- `python3 inspection of dag.json: selected node, its four registered dependencies, all ancestors' dependencies (lean names and status), and accepted lean_statements matching 'IsEmbeddedSubmanifold … univ', '∀ᵐ x ∂μHE[n], Tendsto', 'Set (Measure', 'ConvergesWeakly' uniqueness`
- `python3 reading of the accepted precedent cone_class decomposition-v1.json and of the parent-child-handoff.json of ambient_calculus, density_representation and borel_restriction`
- `python3 /tmp/bc-a1/scripts/check_reuse.py (git show <candidate>:GMT/Ch07/Submission.lean; declared type vs dag.json; sorry count) for aebb2ae, 1f0fe9f, 90d679a, cb3c7f3; git show 90d679a:GMT/Ch07/Submission.lean | grep '^theorem Submission'`
- `lake env lean /tmp/bc-a1/lean/Types.lean; lake env lean /tmp/bc-a1/lean/Assembly.lean; lake env lean /tmp/bc-a1/lean/Skeleton.lean; lake env lean /tmp/bc-a1/lean/Skeleton2.lean`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,inherited,store}.py?ref=feature/humanize-api-update-claude; grep -n '_inherited_prerequisites|_overlay_accepted_children|_render_parent_supplied_natural|_dependency_problem'`
- `grep -n on book/chapter-07.txt (class 𝒯 in the proof of 7.3.3, lines 443–486) and book/chapter-A.txt (A.4, line 35)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-class-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-class-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4e8b16732b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-699466b76b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/tmp/bc-a1/lean/Types.lean`
- `/tmp/bc-a1/lean/Assembly.lean`
- `/tmp/bc-a1/lean/Skeleton.lean`
- `/tmp/bc-a1/lean/Skeleton2.lean`
- `/tmp/bc-a1/scripts/check_reuse.py`
- `/tmp/bc-a1/scripts/build.py`
- `/tmp/bc-a1/mlf/inherited.py`
- `/tmp/bc-a1/mlf/runtime.py`

Pins and contract:
- The snapshot manifest pins project b4d606d and Mathlib 25730c7c. These equal the workspace HEAD and .lake/packages/mathlib.
- The snapshot Contract.lean, snapshot Submission.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- No dimred_tr_bc_* identifier exists in the snapshot (rg exit 1), in GMT, in SimonGMT or in dag.json.

Library facts cited by the children exist at these paths:
- tendsto_nhds_unique (Topology/Separation/Hausdorff.lean:180)
- StrictMono.tendsto_atTop (Order/Filter/AtTopBot/Tendsto.lean:84)
- integral_smul_measure and integral_map (MeasureTheory/Integral/Bochner/Basic.lean:1052, 1081)
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- withDensity_apply, withDensity_congr_ae and withDensity_indicator (Measure/WithDensity.lean:44, 88, 192)
- Filter.Tendsto.limsup_eq (Topology/Order/LiminfLimsup.lean:190)
- tendsto_add_atTop_nat (AtTopBot/Basic.lean:331)
- Homeomorph.isProperMap (Topology/Maps/Proper/Basic.lean:264)
- StrictMono.id_le (Order/WellFounded.lean:267)
- integral_eq_zero_of_ae and integral_zero_measure (Bochner/Basic.lean:349, 1020)
closedBall_subset_closedBall_iff has no match; the children use a unit-vector argument instead.

SimonGMT facts:
- affinePullbackForm, tsupport_affinePullbackForm_subset and affinePullbackForm_isTestForm are at AffineCurrentPushforward.lean:35–64.
- countablyRectifiable_of_measure_zero is at Rectifiable.lean:45.
- support = U ∖ zeroRegion, with VanishesOn, is at CurrentLocalEquality.lean:101–118.

Reuse:
- ambient_calculus (aebb2ae), density_representation (1f0fe9f) and dor_lmb_imrep_restrict_current (90d679a) are accepted, and their isolated comparators passed.
- Their candidates' declared types equal the DAG types, and each candidate's only sorry is main_theorem.
- The precedent cone_class decomposition reused the same three in the same way.

Lean checks:
- All 8 new child types elaborate.
- The assembly of the selected frozen type compiles from the 5 class children and the 4 registered dependencies, with only standard axioms otherwise.
- class_rescale is fully proved from its siblings.
- The key steps of class_tangent, class_monotone and class_finite_density compile.

Framework (math-lean-flow inherited.py) and its effect on the split:
- A child inherits every ancestor dependency whose Lean name appears in its proof text, and waits for it to be accepted.
- So new children take unaccepted results as hypotheses, and a script checks that their proofs avoid all twelve ancestor-dependency names.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
