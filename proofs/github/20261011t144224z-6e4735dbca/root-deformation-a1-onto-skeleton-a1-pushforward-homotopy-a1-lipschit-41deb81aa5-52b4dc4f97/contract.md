<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1 -->

## Theorem `Submission.dph_lpf_existence`

Notation: ℝ^p := Eucl p; D_q(ℝ^p) := GeometricCurrentOn univ q and D^q(ℝ^p) := TestFormOn univ q; M = mass, spt = support, ∂ = boundary; for a test form φ, dφ := exteriorDerivativeTestOn univ q φ, whose underlying form is exteriorDerivative φ; |γ| := covectorEuclideanNorm γ; A_ρ := thickening ρ A; C^∞ means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞); a map g is proper on F if g⁻¹(K) ∩ F is compact for every compact K. For g : ℝ^p → ℝ^q, ω ∈ D^j(ℝ^q), η ∈ D^j(ℝ^p) and A ⊆ ℝ^p, 'η is compatible with (g, ω) near A' means: there is an open N ⊇ A with η(x) = ω(g(x)).compContinuousLinearMap (fderiv ℝ g x) for all x ∈ N. For X ∈ D_k(ℝ^m), G : ℝ^m → ℝ^{m′} and S ∈ D_k(ℝ^{m′}), LipPF(X, G, S) means: for every sequence (G_n) of C^∞ maps ℝ^m → ℝ^{m′}, every open O ⊇ spt X and every L ∈ ℝ such that eventually ‖fderiv ℝ G_n x‖ ≤ L for all x ∈ O, and G_n → G uniformly on O, and for every ω ∈ D^k(ℝ^{m′}) and every sequence (η_n) in D^k(ℝ^m) such that eventually η_n is compatible with (G_n, ω) near spt X, the sequence X(η_n) converges to S(ω). Assume (RS): for all m, m′ ∈ ℕ, G : ℝ^m → ℝ^{m′}, Λ ∈ ℝ≥0, r ∈ ℝ and F ⊆ ℝ^m such that r > 0, F is closed, G is Λ-Lipschitz on F_r and G is proper on F, there are C^∞ maps G_n : ℝ^m → ℝ^{m′} (n ∈ ℕ) with ‖fderiv ℝ G_n x‖ ≤ Λ for all n and all x ∈ F_{r/2}, G_n → G uniformly on F_{r/2}, and G_n proper on F for all sufficiently large n (this is the conclusion of the sibling reference_sequence); and (CL): for all m, m′, k ∈ ℕ, every X ∈ D_k(ℝ^m) with M(X) < ∞ such that M(∂Y) < ∞ for every j ∈ ℕ and Y ∈ D_{j+1}(ℝ^m) with k = j + 1 and HEq Y X, every G : ℝ^m → ℝ^{m′} proper on spt X, all sequences (G_n), (G′_n) of C^∞ maps ℝ^m → ℝ^{m′}, all open O, O′ ⊇ spt X and all L, L′ ∈ ℝ such that eventually ‖fderiv ℝ G_n x‖ ≤ L for all x ∈ O and eventually ‖fderiv ℝ G′_n x‖ ≤ L′ for all x ∈ O′, G_n → G uniformly on O and G′_n → G uniformly on O′, every ω ∈ D^k(ℝ^{m′}) and all sequences (η_n), (η′_n) in D^k(ℝ^m) such that eventually η_n is compatible with (G_n, ω) near spt X and eventually η′_n is compatible with (G′_n, ω) near spt X: X(η′_n) − X(η_n) → 0 (this is the conclusion of the sibling comparison). Then the following holds: (I) For all m, m′, k ∈ ℕ, X ∈ D_k(ℝ^m) with M(X) < ∞ such that M(∂Y) < ∞ for every j ∈ ℕ and Y ∈ D_{j+1}(ℝ^m) with k = j + 1 and HEq Y X, G : ℝ^m → ℝ^{m′}, Λ ∈ ℝ≥0 and r > 0 such that G is Λ-Lipschitz on thickening r (spt X) and G⁻¹(K) ∩ spt X is compact for every compact K: there is S ∈ D_k(ℝ^{m′}) with LipPF(X, G, S) such that every S′ ∈ D_k(ℝ^{m′}) with LipPF(X, G, S′) equals S, M(S) ≤ Λ^k·M(X) (in ℝ≥0∞) and spt S ⊆ closure(G(spt X)).

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5257

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5572, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2481

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2481, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5941, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5947, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5953

## Lean problem

Declaration: `Submission.dph_lpf_existence`

```lean
(∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧ (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧ S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support))
```

### Frozen project context

`GMT/Ch06/Contract.lean` at `d8d46c9587747dee0751a1f780fcafdba16a3886` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 6 "Currents" (pp. 131–180)

Frozen contract.  Currents, boundary, mass and weak convergence are the clean SimonGMT
objects (`Poincare.SimonGMT.Chapter06`):

* `GeometricCurrentOn U n`: sequentially continuous linear functionals on `𝒟ⁿ(U)` (Simon 2.1);
* `T.boundary` (2.3), `T.massOn W` (2.5, Euclidean coefficient norm of Remark 2.6),
  `T.mass = T.massOn U` (2.4), `T.support` (2.11), `WeaklyConvergesOn` (2.13).

Integer multiplicity currents `τ(M, θ, ξ)` (3.1), restriction `T ⌞ A` (2.9), slices (4.6),
the Lipschitz push-forward (3.6), lattice polyhedral chains (§5) and the flat pseudometric
`d_W` (7.1) are defined below from primitive data.  Hausdorff measure `Hⁿ` is Mathlib's
normalized `μHE[n]` (equal to Lebesgue measure on `ℝⁿ`).

**Degree convention.**  `GeometricCurrentOn.boundary` is defined on degree `m + 1`.  Whenever
the book's statement involves `∂T` for an `n`-current with `n ≥ 1`, the Lean statement writes
the book's `n` as `m + 1`.  The ambient space is `ℝ^P` (book: `ℝ^P` in §2, §8, `ℝ^{n+ℓ}`
elsewhere); in §5–§6, where constants are `c(n, ℓ)`, the ambient space is `ℝ^{(m+1)+ℓ}`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace GMT.Ch06

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt)
open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity)

noncomputable section

/-- Euclidean space `ℝ^P`. -/
abbrev Eucl (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Basic notions -/

/-- Simon's `W ⊂⊂ U` for open `W`: `W` is open and `closure W` is a compact subset of `U`. -/
def CompactlyContainedOpen (W U : Set (Eucl P)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U

/-- Simon Ch. 6, 3.1 (p. 146) and 8.1 (p. 173): the conditions on the triple `(M, θ, ξ)`.

* `M ⊆ U` is `Hⁿ`-measurable and countably `n`-rectifiable (Ch. 3, 1.1);
* `θ` is positive on `M` and locally `Hⁿ`-integrable on `M` in `U`;
* `ξ : M → Λₙ(ℝ^P)` is `Hⁿ`-measurable and for `Hⁿ`-a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an
  orthonormal basis `τ` of the approximate tangent space `TₓM` of `M` (w.r.t. `θ`, Ch. 3, 1.7).

`n`-vectors are `NVector (ℝ^P) n` (the dual of `n`-covectors), so `⟨ω, ξ⟩ = ξ ω` and
`τ₁ ∧ ⋯ ∧ τₙ = simpleNVector τ`.  The sign `±` (as printed in 8.1) is only needed for `n = 0`,
where there is no frame to flip. -/
structure IsRectifiableTriple (U : Set (Eucl P)) (n : ℕ) (M : Set (Eucl P))
    (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) : Prop where
  subset : M ⊆ U
  nullMeasurableSet : NullMeasurableSet M (μHE[n] : Measure (Eucl P))
  countablyRectifiable : CountablyRectifiable n M
  pos : ∀ x ∈ M, 0 < θ x
  integrableOn : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
    IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))
  aestronglyMeasurable : AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M)
  orients : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∃ τ : Fin n → Eucl P,
    Orthonormal ℝ τ ∧
    HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
    (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)

/-- Simon Ch. 6, 3.1 (‡) (p. 146): `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)`. -/
def tauAction (n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (ω : DifferentialForm (Eucl P) n) : ℝ :=
  ∫ x in M, θ x * ξ x (ω x) ∂(μHE[n] : Measure (Eucl P))

/-- Simon Ch. 6, 8.1 (p. 173): `T` is *rectifiable*, `T = τ(M, θ, ξ)` with `θ` real-valued
(positive, locally `Hⁿ`-integrable; footnote 4). -/
def IsRectifiableCurrent {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Simon Ch. 6, 3.1 (p. 146): `T ∈ 𝒟ₙ(U)` is an *integer multiplicity (rectifiable) current*:
`T = τ(M, θ, ξ)` with `θ` positive integer-valued. -/
def IsIntegerMultiplicity {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ (∀ x ∈ M, ∃ k : ℕ, θ x = k) ∧
    ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Integral current (the hypothesis of Simon Ch. 6, 8.2, p. 176): `T` and `∂T` are both integer
multiplicity (both then have locally finite mass). -/
def IsIntegralCurrent {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) : Prop :=
  IsIntegerMultiplicity T ∧ IsIntegerMultiplicity T.boundary

/-! ## Measure representation, restriction, slices -/

/-- Simon Ch. 6, (2.7) (p. 136): `T(ω) = ∫ ⟨ω, v⟩ dμ`, with `⟨ω, v⟩` `μ`-integrable for every
test form `ω` (testing with `φ dx^α`, `φ = 1` on a compact `K ⊆ U`, this is equivalent to `v`
being locally `μ`-integrable on `U`).  No normalization of `v` is required: such `(μ, v)` exists
iff `T` has locally finite mass (Riesz, Ch. 1, 4.14), and the vector measure `v μ` on `U` is
then uniquely determined by `T`. -/
def IsMeasureRepresentation {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) : Prop :=
  ∀ ω : TestFormOn U n, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) n) x)) μ ∧
    T ω = ∫ x, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.9) (p. 136): `S = T ⌞ A` for a Borel set `A`, i.e.
`S(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`.  Defined through any representation of `T` as in (2.7); the result
does not depend on the representation (uniqueness of the vector measure `T⃗ μ_T`). -/
def IsRestriction {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) (A : Set (Eucl P))
    (S : GeometricCurrentOn U n) : Prop :=
  MeasurableSet A ∧ ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
    IsMeasureRepresentation T μ v ∧
    ∀ ω : TestFormOn U n, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.8) (p. 136): `μ` is the total variation (mass) measure `μ_T` of `T`:
`μ_T(W) = M_W(T)` for every open `W ⊂⊂ U`, and `μ_T` lives on `U`. -/
def IsMassMeasure {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) : Prop :=
  μ Uᶜ = 0 ∧ ∀ W, CompactlyContainedOpen W U → μ W = T.massOn W

/-- Simon Ch. 6, (4.6) (p. 157): the slice `⟨T, f, t₋⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}`
(sets taken inside `U`), for `T` with `M_W(T) + M_W(∂T) < ∞`. -/
def IsSlice {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ)
    (t : ℝ) (S : GeometricCurrentOn U m) : Prop :=
  ∃ (A : GeometricCurrentOn U (m + 1)) (B : GeometricCurrentOn U m),
    IsRestriction T {x | x ∈ U ∧ f x < t} A ∧
    IsRestriction T.boundary {x | x ∈ U ∧ f x < t} B ∧
    ∀ ω : TestFormOn U m, S ω = A.boundary ω - B ω

/-! ## Lipschitz push-forward -/

/-- Simon Ch. 6, (3.6) (p. 147) and Ch. 3, 2.1–2.2: `S = f_# T` for `T = τ(M, θ, ξ)` and `f`
locally Lipschitz, `f_# T(ω) = ∫_M ⟨ω(f(x)), (d^M f_x)_# ξ(x)⟩ θ(x) dHⁿ(x)`.

`L x` is any linear map agreeing with `d^M f_x` on `TₓM`; by Ch. 3, §2 (p. 76),
`d^M f_x(τ) = (d/dt) f(x + tτ)|_{t=0}` for `τ ∈ TₓM`, `Hⁿ`-a.e. `x ∈ M`.  As `ξ(x) ∈ Λₙ(TₓM)`,
the integrand only depends on `L x` restricted to `TₓM`, so `S` is uniquely determined. -/
def IsLipschitzPushforward {Q n : ℕ} {U : Set (Eucl P)} {V : Set (Eucl Q)}
    (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q) (S : GeometricCurrentOn V n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)),
    IsRectifiableTriple U n M θ ξ ∧ (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) ∧
    (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt n M θ x Tx →
        ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) ∧
    ∀ ω : TestFormOn V n, S ω =
      ∫ x in M, θ x * nVectorPushforward n (L x) (ξ x)
        ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))

/-! ## Lattice polyhedral chains (§5) -/

/-- Index of an `n`-face of the cubical lattice in `ℝ^N` (Simon Ch. 6, §5, p. 159): a lattice
point `z ∈ ℤ^N` and the increasing multi-index `α` of the `n` coordinate directions spanned. -/
abbrev LatticeFaceIndex (n N : ℕ) := (Fin N → ℤ) × SimonMultiIndex n N

/-- The closed face `ρ (z + F_α) ∈ 𝓛ₙ(ρ)`, `F_α = {x : xᵢ ∈ [0,1] (i ∈ α), xᵢ = 0 (i ∉ α)}`.
Every closed `n`-face of the decomposition `⋃_z ρ(z + C)` arises from exactly one index. -/
def latticeFace {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N) : Set (Eucl N) :=
  {x | ∀ i : Fin N,
    (i ∈ range F.2 → ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)) ∧
    (i ∉ range F.2 → x i = ρ * (F.1 i : ℝ))}

/-- `[[F]](ω) = ∫_F ⟨ω, e_{α₁} ∧ ⋯ ∧ e_{αₙ}⟩ dHⁿ` (2.2), `F` oriented by its coordinate
directions in increasing order. -/
def latticeFaceAction {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N)
    (ω : DifferentialForm (Eucl N) n) : ℝ :=
  ∫ x in latticeFace ρ F, ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))
    ∂(μHE[n] : Measure (Eucl N))

/-- `Pc = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]` as a current in `U` (the sum is locally finite). -/
def IsLatticeChain {n N : ℕ} {U : Set (Eucl N)} (ρ : ℝ) (β : LatticeFaceIndex n N → ℝ)
    (Pc : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, Pc ω = ∑' F, β F * latticeFaceAction ρ F ω

/-! ## Flat pseudometric (§7) -/

/-- Simon Ch. 6, (7.1) (p. 170): `d_W(T₁, T₂) = inf {M_W(S) + M_W(R) : T₁ − T₂ = ∂R + S,
R ∈ 𝒟ₙ₊₁(U), S ∈ 𝒟ₙ(U) integer multiplicity}`. -/
def flatDistance {U : Set (Eucl P)} {n : ℕ} (W : Set (Eucl P))
    (T₁ T₂ : GeometricCurrentOn U n) : ℝ≥0∞ :=
  ⨅ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n)
    (_ : IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
      ∀ ω : TestFormOn U n, T₁ ω - T₂ ω = R.boundary ω + S ω),
    S.massOn W + R.massOn W

/-! ## Headline results -/

/-- **Simon Ch. 6, Lemma 2.15 (p. 137).**  If `T_q ∈ 𝒟ₙ(U)` and `sup_q M_W(T_q) < ∞` for each
`W ⊂⊂ U`, there are a subsequence `T_{q'}` and `T ∈ 𝒟ₙ(U)` with `T_{q'} ⇀ T` and
`∫ ⟨ω, T⃗_{q'}⟩ dμ_{T_{q'}} → ∫ ⟨ω, T⃗⟩ dμ_T` for every continuous compactly supported `n`-form
`ω` on `U` (for all representations (2.7) of the `T_{q'}` and of `T`). -/
def CompactnessUnderMassBounds : Prop :=
  ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U n,
    (∀ W, CompactlyContainedOpen W U → (⨆ q, (T q).massOn W) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U n), StrictMono φ ∧
      WeaklyConvergesOn (fun q => T (φ q)) T₀ ∧
      ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U →
        ∀ (μ : ℕ → Measure (Eucl P)) (v : ℕ → Eucl P → NVector (Eucl P) n)
          (μ₀ : Measure (Eucl P)) (v₀ : Eucl P → NVector (Eucl P) n),
          (∀ q, IsMeasureRepresentation (T (φ q)) (μ q) (v q)) →
          IsMeasureRepresentation T₀ μ₀ v₀ →
          Tendsto (fun q => ∫ x, v q x (ω x) ∂(μ q)) atTop (𝓝 (∫ x, v₀ x (ω x) ∂μ₀))

/-- **Simon Ch. 6, Theorem 2.34 (Constancy Theorem, p. 142).**  If `U ⊆ ℝⁿ` is open and
connected, `T ∈ 𝒟ₙ(U)` and `∂T = 0`, then `T = c [[U]]` for a constant `c`, where
`[[U]](ω) = ∫_U ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.  (Book `n = m + 1`.) -/
def ConstancyTheorem : Prop :=
  ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → IsConnected U →
    ∀ T : GeometricCurrentOn U (m + 1), T.boundary = 0 →
      ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1),
        T ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume

/-- **Simon Ch. 6, Lemma 3.9 (p. 148).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity,
`f : U → V` (`V ⊆ ℝ^Q` open) is locally Lipschitz and `f | spt T` is proper, then the
push-forward `f_# T` of (3.6) exists in `𝒟ₙ(V)` and is integer multiplicity. -/
def LipschitzPushforwardIntegerMultiplicity : Prop :=
  ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
    ∀ (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q),
      IsIntegerMultiplicity T → LocallyLipschitzOn U f → MapsTo f U V →
      (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) →
      ∃ S : GeometricCurrentOn V n, IsLipschitzPushforward T f S ∧ IsIntegerMultiplicity S

/-- **Simon Ch. 6, Theorem 3.11 (Federer–Fleming Compactness Theorem, p. 149).**  If
`T_j ∈ 𝒟ₙ(U)` are integer multiplicity and `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all
`W ⊂⊂ U`, then some subsequence converges weakly in `U` to an integer multiplicity
`T ∈ 𝒟ₙ(U)`.  (Book `n = m + 1`.) -/
def FedererFlemingCompactness : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U (m + 1),
    (∀ j, IsIntegerMultiplicity (T j)) →
    (∀ W, CompactlyContainedOpen W U → (⨆ j, ((T j).massOn W + (T j).boundary.massOn W)) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U (m + 1)), StrictMono φ ∧
      IsIntegerMultiplicity T₀ ∧ WeaklyConvergesOn (fun j => T (φ j)) T₀

/-- **Simon Ch. 6, §4 Slicing (4.4–4.10, pp. 153–158).**  Let `T ∈ 𝒟ₙ(U)` with
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, and `f` Lipschitz on `U` (constant `L`).  Then the
slices `⟨T, f, t⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}` (4.6) exist for every `t`, satisfy
`spt ⟨T, f, t⟩ ⊆ spt T ∩ {f = t}` (4.8); if `T` is integer multiplicity they are integer
multiplicity for `L¹`-a.e. `t` (4.4, 4.5(2)); and for every open `W ⊆ U`, every `L_W` with
`|Df| ≤ L_W` a.e. on `W` (i.e. `L_W ≥ ess sup_W |Df|`) and `a < b` (4.10, upper integral):
`∫*_a^b M_W(⟨T, f, t⟩) dt ≤ L_W · M_W(T ⌞ {a < f < b})`.
The book prints `M(T ⌞ {a < f < b})` on the right of 4.10; its proof (4.9) gives the stronger
`M_W`, stated here.  (Book `n = m + 1`.) -/
def SlicingTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
    ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
    ∃ S : ℝ → GeometricCurrentOn U m,
      (∀ t, IsSlice T f t (S t)) ∧
      (∀ t, (S t).support ⊆ T.support ∩ {x | f x = t}) ∧
      (IsIntegerMultiplicity T → ∀ᵐ t ∂(volume : Measure ℝ), IsIntegerMultiplicity (S t)) ∧
      ∀ W, IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ a b : ℝ, a < b →
        ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R →
          ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧
            ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W

/-- **Simon Ch. 6, 5.3 (Deformation Theorem, scaled version, p. 160); `ρ = 1` is 5.1 (p. 159).**
For `n, ℓ ≥ 1` there is `C = C(n, ℓ)` such that for every `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`M(T) + M(∂T) < ∞` and every `ρ > 0`, `T − P = ∂R + S` where `P = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]`,
`M(P) ≤ C M(T)`, `M(∂P) ≤ C M(∂T)`, `M(R) ≤ C ρ M(T)`, `M(S) ≤ C ρ M(∂T)`,
`spt P ∪ spt R ⊆ {dist(·, spt T) < 2√(n+ℓ) ρ}`, `spt ∂P ∪ spt S ⊆ {dist(·, spt ∂T) < 2√(n+ℓ) ρ}`;
if `T` is integer multiplicity, `P, R` are integer multiplicity with `β_F ∈ ℤ`, and if moreover
`∂T` is integer multiplicity then so is `S`.
Errata: the book prints `n, k ∈ {1,2,…}` and `C(n, k)` for `n, ℓ`; `𝓛_j(ρ)` for `𝓛ₙ(ρ)`;
"so is s" for "so is S".  (Book `n = m + 1`.) -/
def DeformationTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ (T : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
    T.mass + T.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ →
    ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1))
      (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ)
      (R : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 2))
      (S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
      IsLatticeChain ρ β Pc ∧
      (∀ ω, T ω - Pc ω = R.boundary ω + S ω) ∧
      Pc.mass ≤ C * T.mass ∧ Pc.boundary.mass ≤ C * T.boundary.mass ∧
      R.mass ≤ C * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ C * ENNReal.ofReal ρ * T.boundary.mass ∧
      Pc.support ∪ R.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.support ∧
      Pc.boundary.support ∪ S.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.boundary.support ∧
      (IsIntegerMultiplicity T →
        (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity R) ∧
      (IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → IsIntegerMultiplicity S)

/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem, p. 168).**  For `n ≥ 2`, `ℓ ≥ 1` there is
`c = c(n, ℓ)` such that every integer multiplicity `T ∈ 𝒟ₙ₋₁(ℝ^{n+ℓ})` with compact support and
`∂T = 0` bounds an integer multiplicity `R ∈ 𝒟ₙ(ℝ^{n+ℓ})` with compact support and
`M(R)^{(n−1)/n} ≤ c M(T)`.  (Book `n = m + 2`.) -/
def IsoperimetricTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 1),
    IsIntegerMultiplicity T → IsCompact T.support → T.boundary = 0 →
    ∃ R : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = T ∧
      R.mass ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤ c * T.mass

/-- **Simon Ch. 6, 6.2 (Weak Polyhedral Approximation Theorem, p. 169).**  For integer
multiplicity `T ∈ 𝒟ₙ(U)`, `U ⊆ ℝ^{n+ℓ}` open, with `M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U`,
there are `ρ_k ↓ 0` and `P_k = ∑_{F ∈ 𝓛ₙ(ρ_k)} β^{(k)}_F [[F]]` with `β^{(k)}_F ∈ ℤ` and
`P_k ⇀ T` in `U`.  (Printed `F_n(ρ_k)`, `β_R^{(k)}` mean `𝓛ₙ(ρ_k)`, `β_F^{(k)}`.  Book `n = m + 1`.) -/
def PolyhedralApproximation : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ U : Set (Eucl (m + 1 + ℓ)), IsOpen U →
    ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℤ)
        (Pk : ℕ → GeometricCurrentOn U (m + 1)),
        (∀ k, 0 < ρ k) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧
        WeaklyConvergesOn Pk T

/-- **Simon Ch. 6, 6.3 (Boundary Rectifiability Theorem, p. 170).**  If `T ∈ 𝒟ₙ(U)` is integer
multiplicity and `M_W(∂T) < ∞` for all `W ⊂⊂ U` (printed `M(∂T)`), then `∂T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def BoundaryRectifiability : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) →
    IsIntegerMultiplicity T.boundary

/-- **Simon Ch. 6, Theorem 7.2 (p. 170).**  Let `T, T_j ∈ 𝒟ₙ(U)` be integer multiplicity with
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`.  Then `T_j ⇀ T` iff `d_W(T_j, T) → 0`
for every `W ⊂⊂ U`.  (Book `n = m + 1`.) -/
def FlatConvergenceIffWeakConvergence : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      (WeaklyConvergesOn Tj T ↔
        ∀ W, CompactlyContainedOpen W U →
          Tendsto (fun j => flatDistance W (Tj j) T) atTop (𝓝 0))

/-- **Simon Ch. 6, 8.1 (Rectifiability Theorem, p. 173).**  If `T ∈ 𝒟ₙ(U)` has
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and the upper density `Θ*ⁿ(μ_T, x) > 0` for `μ_T`-a.e.
`x ∈ U`, then `T = τ(M, θ, ξ)` is rectifiable (with real `θ`).  (Book `n = m + 1`.) -/
def RectifiabilityTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) →
    (∃ μ : Measure (Eucl P), IsMassMeasure T μ ∧
      ∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) →
    IsRectifiableCurrent T

/-- **Simon Ch. 6, Theorem 8.2 (p. 176).**  If `T_j, ∂T_j` are integer multiplicity,
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U` and `T_j ⇀ T ∈ 𝒟ₙ(U)`, then `T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def IntegralityOfWeakLimits : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)),
      (∀ j, IsIntegralCurrent (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      WeaklyConvergesOn Tj T → IsIntegerMultiplicity T

end

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 2–6 of the supplied proof of lipschitz_pushforward (reference sequence, existence of the limit, LipPF, uniqueness, support), with two adaptations: the reference sequence is taken from the hypothesis (RS), and the linearity of the limit functional is obtained from the hypothesis (CL) with equal approximating sequences instead of the locality fact (F2′); fact (CF) (compatible forms with support control and bounds) is proved inline in step 3. For γ ∈ Covector and a linear T, γ∘T := γ.compContinuousLinearMap T. Assume (RS) and (CL) and fix m, m′, k, X, G, Λ, r with M(X) < ∞, the HEq hypothesis, r > 0, G Λ-Lipschitz on (spt X)_r and G proper on spt X.

1. (Reference sequence.) spt X = univ ∖ zeroRegion(X) is closed. (RS) with F := spt X gives C^∞ maps G_n with ‖fderiv ℝ G_n x‖ ≤ Λ for all n and x ∈ O₀ := (spt X)_{r/2}, G_n → G uniformly on O₀, and n₀ such that G_n is proper on spt X for all n ≥ n₀. O₀ is open (isOpen_thickening) and spt X ⊆ O₀ (r/2 > 0). Hence (G_n, O₀, Λ) satisfies every requirement imposed on an approximating sequence in LipPF(X, G, ·) and in (CL) (the derivative bound holds for every n, in particular eventually).
2. (Homogeneity of |·|.) For a ∈ ℝ and a covector γ, |a·γ| = |a|·|γ|: each coefficient satisfies (a·γ)(e_I) = a·γ(e_I), so the sum of squares defining |·|² is multiplied by a², and √(a²·Σ) = |a|·√Σ.
3. (Compatible forms with bounds.) Let n ≥ n₀ and ω ∈ D^k(ℝ^{m′}). The reused compatible_form (P := m, Q := m′, j := k, U := O₀ (open, spt X ⊆ O₀), V := univ, A := spt X, f := G_n, which is C^∞ and proper on spt X) gives η ∈ TestFormOn O₀ k, ζ : ℝ^m → ℝ with 0 ≤ ζ ≤ 1 and an open N ⊇ spt X with η(x) = ζ(x)·(ω(G_n x)∘DG_n(x)) for all x and η(x) = ω(G_n x)∘DG_n(x) for x ∈ N. Since tsupport η ⊆ O₀ ⊆ univ, the same form is an element η_n(ω) of D^k(ℝ^m), and it is compatible with (G_n, ω) near spt X (on N). Let C ∈ ℝ with |ω(y)| ≤ C for all y (so C ≥ 0). For x ∈ O₀: |η_n(ω)(x)| = ζ(x)·|ω(G_n x)∘DG_n(x)| ≤ ‖DG_n(x)‖^k·|ω(G_n x)| ≤ Λ^k·C, by step 2, 0 ≤ ζ(x) ≤ 1, the reused pullback_norm, ‖DG_n(x)‖ ≤ Λ and the monotonicity of u ↦ u^k on [0, ∞). For x ∉ O₀: x ∉ tsupport η, so η_n(ω)(x) = 0 and |η_n(ω)(x)| = 0 ≤ Λ^k·C. For n < n₀ put η_n(ω) := 0. Thus, for every ω: (a) η_n(ω) is compatible with (G_n, ω) near spt X for all n ≥ n₀; (b) for every C with |ω(y)| ≤ C for all y, |η_n(ω)(x)| ≤ Λ^k·C for all n and x (trivially when η_n(ω) = 0, as Λ^k·C ≥ 0).
4. (Uniform bound.) The reused mass_bound (P := m, n := k, U := W := univ, T := X, B := M(X).toReal ≥ 0, which satisfies X.massOn univ = M(X) = ENNReal.ofReal B because M(X) < ∞; tsupport ⊆ univ; C := Λ^k·C) gives |X(η_n(ω))| ≤ M(X).toReal·Λ^k·C for all n, whenever |ω(y)| ≤ C for all y.
5. (Subsequences.) If p : ℕ → ℕ tends to ∞, then the maps G_{p(i)} are C^∞, satisfy ‖fderiv ℝ G_{p(i)} x‖ ≤ Λ on O₀, and converge to G uniformly on O₀ (for every ε > 0 the statement 'dist(G(x), G_n(x)) < ε for all x ∈ O₀' holds for all large n, hence for n = p(i) for all large i); and η_{p(i)}(ω) is compatible with (G_{p(i)}, ω) near spt X as soon as p(i) ≥ n₀, i.e. for all large i.
6. (Existence of the limit.) Fix ω and let a_n := X(η_n(ω)). Claim: for all p, q : ℕ → ℕ tending to ∞, a_{q(i)} − a_{p(i)} → 0. Indeed, apply (CL) to X and G (M(X) < ∞, the HEq hypothesis, G proper on spt X), to the approximations (G_{p(i)})_i with O₀, Λ and (G_{q(i)})_i with O₀, Λ, to the form ω and to the sequences (η_{p(i)}(ω))_i and (η_{q(i)}(ω))_i; all its hypotheses hold by steps 1 and 5. Now (a_n) is a Cauchy sequence: otherwise there is ε > 0 such that for every i there are p(i), q(i) ≥ i with |a_{q(i)} − a_{p(i)}| ≥ ε; then p and q tend to ∞ while a_{q(i)} − a_{p(i)} does not tend to 0, contradicting the claim. Since ℝ is complete, (a_n) converges; let S₀(ω) := lim_n X(η_n(ω)).
7. (Linearity.) Let ω, ω′ ∈ D^k(ℝ^{m′}), a, b ∈ ℝ and ω″ := a·ω + b·ω′. For n ≥ n₀ the form a·η_n(ω) + b·η_n(ω′) is compatible with (G_n, ω″) near spt X: on the open set N ∩ N′ ⊇ spt X (N, N′ the open sets of step 3 for ω and ω′) its value at x is a·(ω(G_n x)∘DG_n(x)) + b·(ω′(G_n x)∘DG_n(x)) = (a·ω(G_n x) + b·ω′(G_n x))∘DG_n(x) = ω″(G_n x)∘DG_n(x), because γ ↦ γ∘T is linear. Apply (CL) with both approximations equal to (G_n) with O₀, Λ, to the form ω″ and to the sequences η_n(ω″) and a·η_n(ω) + b·η_n(ω′) (both eventually compatible with (G_n, ω″) near spt X): X(a·η_n(ω) + b·η_n(ω′)) − X(η_n(ω″)) → 0. As X is linear, X(a·η_n(ω) + b·η_n(ω′)) = a·X(η_n(ω)) + b·X(η_n(ω′)) → a·S₀(ω) + b·S₀(ω′) (step 6). Hence X(η_n(ω″)) → a·S₀(ω) + b·S₀(ω′), and by uniqueness of limits S₀(a·ω + b·ω′) = a·S₀(ω) + b·S₀(ω′). In particular (a = b = 1, and b = 0 with ω′ := ω) S₀ is additive and homogeneous.
8. (Bound, current and mass.) Passing to the limit in step 4 (the closed condition |·| ≤ const is preserved under limits) gives |S₀(ω)| ≤ (Λ^k·M(X).toReal)·C whenever |ω(y)| ≤ C for all y. The sibling current_criterion (P := m′, n := k, U := univ, T₀ := S₀, B := Λ^k·M(X).toReal) gives S ∈ D_k(ℝ^{m′}) with S(ω) = S₀(ω) for every ω and M(S) ≤ ENNReal.ofReal(Λ^k·M(X).toReal). Since Λ^k ≥ 0 and M(X) < ∞, ENNReal.ofReal(Λ^k·M(X).toReal) = ENNReal.ofReal(Λ^k)·ENNReal.ofReal(M(X).toReal) = (Λ : ℝ≥0∞)^k·M(X) (ENNReal.ofReal_mul, ENNReal.ofReal_pow, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal). This is the mass conjunct M(S) ≤ Λ^k·M(X).
9. (LipPF(X, G, S).) Let (G′_n) be C^∞, O′ open with spt X ⊆ O′, L′ ∈ ℝ with eventually ‖fderiv ℝ G′_n x‖ ≤ L′ on O′, G′_n → G uniformly on O′, ω ∈ D^k(ℝ^{m′}) and (η′_n) eventually compatible with (G′_n, ω) near spt X. (CL) applied to (G_n) with O₀, Λ and the sequence η_n(ω), and to (G′_n) with O′, L′ and the sequence η′_n, gives X(η′_n) − X(η_n(ω)) → 0; and X(η_n(ω)) → S₀(ω) = S(ω) by step 6. Hence X(η′_n) = (X(η′_n) − X(η_n(ω))) + X(η_n(ω)) → S(ω).
10. (Uniqueness.) Let S′ ∈ D_k(ℝ^{m′}) satisfy LipPF(X, G, S′). Applying it to (G_n) with O₀, Λ, to ω and to η_n(ω) (eventually compatible by step 3) gives X(η_n(ω)) → S′(ω); by step 6 also X(η_n(ω)) → S(ω). By uniqueness of limits in ℝ, S′(ω) = S(ω) for every ω, so S′ = S (GeometricCurrentOn.ext).
11. (Support.) Let y₀ ∉ closure(G(spt X)). The closure is closed, so there is ρ > 0 such that ball(y₀, 3ρ) is disjoint from closure(G(spt X)); then dist(G(x), y₀) ≥ 3ρ for every x ∈ spt X. Let W := ball(y₀, ρ): W is open, closure W ⊆ closedBall(y₀, ρ) is compact, and closure W ⊆ univ. Let ω ∈ D^k(ℝ^{m′}) with tsupport ω ⊆ W and put K := tsupport ω (closed). For z ∈ K and x ∈ spt X: dist(G(x), z) ≥ dist(G(x), y₀) − dist(z, y₀) > 3ρ − ρ = 2ρ. By uniform convergence on O₀ ⊇ spt X, for all large n we have dist(G(x), G_n(x)) < ρ for every x ∈ spt X, hence dist(G_n(x), z) > ρ > 0 for all z ∈ K, i.e. G_n(x) ∉ K. For such n, N_n := G_n⁻¹(ℝ^{m′} ∖ K) is open (G_n is continuous and K is closed) and contains spt X, and for x ∈ N_n we have ω(G_n x) = 0 (as G_n x ∉ tsupport ω), so ω(G_n x)∘DG_n(x) = 0, which is the value at x of the zero form. Thus the zero sequence η′_n := 0 is eventually compatible with (G_n, ω) near spt X, and step 9 (with the approximation (G_n), O₀, Λ) gives X(0) = 0 → S(ω), so S(ω) = 0. Hence S vanishes on W (S(ω) = 0 for every test form ω with tsupport ω ⊆ W), so W belongs to the family of open sets whose union is zeroRegion(S), and y₀ ∈ W ⊆ zeroRegion(S), i.e. y₀ ∉ spt S = univ ∖ zeroRegion(S). Therefore spt S ⊆ closure(G(spt X)).
12. (Conclusion.) S satisfies LipPF(X, G, S) (step 9), uniqueness among currents with this property (step 10), M(S) ≤ Λ^k·M(X) (step 8) and spt S ⊆ closure(G(spt X)) (step 11), which is the conclusion of (I). ∎

## Key steps

1. (RS) with F := spt X gives C^∞ maps G_n with ‖DG_n‖ ≤ Λ on O₀ = (spt X)_{r/2}, G_n → G uniformly on O₀, G_n eventually proper on spt X.
2. compatible_form with U := O₀, pullback_norm and 0 ≤ ζ ≤ 1 give compatible η_n(ω) with |η_n(ω)| ≤ Λ^k·sup|ω|; mass_bound gives |X(η_n(ω))| ≤ M(X)Λ^k·sup|ω|.
3. (CL) along pairs of subsequences shows X(η_n(ω)) is Cauchy; its limit S₀(ω) is linear by (CL) with equal sequences.
4. current_criterion turns S₀ into a current S with M(S) ≤ ofReal(Λ^k·M(X).toReal) = Λ^k·M(X).
5. (CL) against the reference sequence gives LipPF(X, G, S); applying LipPF(X, G, S′) to the reference sequence gives uniqueness.
6. Support: off closure(G(spt X)) the zero form is eventually compatible, so S vanishes on a small ball around such a point.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 over dag.json (662 nodes): statuses, lean_names, statements, candidate commits; grep of all accepted lean_statements for support/boundary-support, locality, pull-back norm, covector-norm smul, bounded-functional current criteria and extDeriv lemmas -> found iwl_cr_support_lemmas, iwl_cr_ce_apply_eq_of_eqOn_nhds_support, iwl_sp_covectorEuclideanNorm_pullback_le, fiw_ims_sc_continuous_of_bound, fiw_tb_ext_covectorNorm_smul, lpf_pic_current_of_dominated_density; no accepted 'bounded linear functional -> current with mass ≤ B' lemma (no match)`
- `python3 over nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json: frozen lean_statements of the siblings smooth_approx (889 chars), interval_product (5579), smooth_homotopy (8216), identical to dag.json`
- `rg -n 'theorem extDeriv_pullback|theorem Filter.EventuallyEq.extDeriv_eq|theorem TendstoUniformlyOn.congr_right|theorem TendstoUniformly.tendstoUniformlyOn|theorem IsCompact.cthickening|theorem mem_cthickening_of_dist_le|theorem self_subset_thickening|theorem cons_self_tail|theorem tail_cons|theorem cauchySeq_tendsto_of_complete|theorem tendsto_nhds_unique' over the snapshot mathlib/Mathlib (all found: DifferentialForm/Basic.lean:259,188; UniformSpace/UniformConvergence.lean:218,222; MetricSpace/Thickening.lean:283,201,309; Data/Fin/Tuple/Basic.lean:171,117; UniformSpace/Cauchy.lean:425; Separation/Hausdorff.lean:180)`
- `grep -n '^def|^structure|^theorem|^abbrev' over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality}.lean: GeometricCurrentOn (toCurrent, continuous'), TestFormOnConverges, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply/boundary_boundary/ext, exteriorDerivative = extDeriv, massAdmissibleOn, massOn, mass, covectorEuclideanNorm, VanishesOn, zeroRegion, support`
- `rg -n 'dph_lpf|LipPF' over the snapshot project and mathlib (*.lean): no match; git log --all -S dph_lpf_ over 3993 refs: no match`
- `read /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py (_existing_lean_name_problem, reuse-by-name id mapping, _dependency_problem, _overlay_accepted_children over children+depends_on) and store.py (ensure returns existing nodes unchanged)`
- `git show <candidate> for the 5 reused declarations (fd5f1e29, 02f3305f, 5c248501, ba202ac0, 3e52d3e8): declarations present together with their own accepted prerequisites; isolated-comparator-result.json passed = True for all five`
- `python3 -I verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem); verifier/lean_contract.py validate_lean_statement on all 12 child statements (all valid)`
- `lake env lean /tmp/lpf_decomp/AllStmts.lean (7 child statements + parent; only sorry warnings), /tmp/lpf_decomp/IfaceCheck.lean (parent proved from children + uncles; no errors), /tmp/lpf_decomp/Skel.lean and Endpt.lean (comparison instantiation of (E0),(E1),(Aff), compatible_form, support_lemmas; endpoint identities by rfl), /tmp/lpf_decomp/Checks3.lean (current_criterion fully proved; (dP); mass arithmetic), /tmp/lpf_review/lean/T2-T8.lean (independent full proofs of the new children modulo declared dependencies; exit 0, no errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1-continuity-criterion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpf_decomp/AllStmts.lean`
- `/tmp/lpf_decomp/IfaceCheck.lean`
- `/tmp/lpf_decomp/Skel.lean`
- `/tmp/lpf_decomp/Checks3.lean`
- `/tmp/lpf_review/lean/T6.lean`
- `/tmp/lpf_review/lean/T7.lean`

The pinned project and SimonGMT contain no Lipschitz push-forward of normal currents, no products with [[0,1]] and no homotopy formula, so the supplied Parts 1–8 are new obligations. Their smooth-approximation, product and homotopy inputs come from the three unaccepted uncle nodes, which are therefore passed as explicit hypotheses. Five accepted declarations are reused by name with byte-identical types: compatible forms (R3), the support facts (S)/(F3c), the mass bound (R1), the pull-back norm bound (F7), and the continuity criterion for (F5/F6). No accepted lemma already turns a bounded linear functional into a current with a mass bound, so this becomes the new child current_criterion. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (extDeriv_pullback, EventuallyEq.extDeriv_eq, TendstoUniformlyOn.congr_right, IsCompact.cthickening, mem_cthickening_of_dist_le, self_subset_thickening, Fin.cons_self_tail, cauchySeq_tendsto_of_complete, tendsto_nhds_unique). All statements elaborate in the exact comparator scope. The parent follows from the children by a checked 4-line assembly, and each new child has an independent Lean proof modulo its declared dependencies. The dph_lpf_* names are globally unused.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
