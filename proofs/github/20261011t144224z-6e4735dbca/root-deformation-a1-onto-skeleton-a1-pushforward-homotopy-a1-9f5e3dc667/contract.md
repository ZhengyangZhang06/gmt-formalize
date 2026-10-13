<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1 -->

## Theorem `Submission.deformation_pushforward_homotopy`

Assume (S5′), the conclusion of the sibling theorem deformation_im_pushforward_limit after its premise LipschitzPushforwardIntegerMultiplicity: for all P, Q, k, every integer multiplicity X = τ(M, θ, ξ) ∈ D_k(ℝ^P) (IsRectifiableTriple univ k M θ ξ, θ natural-valued on M, X(ω) = tauAction k M θ ξ ω) and every Λ-Lipschitz g : ℝ^P → ℝ^Q with g⁻¹(K) ∩ spt X compact for compact K, there is S ∈ D_k(ℝ^Q) with IsLipschitzPushforward X g S, S integer multiplicity, and ∫_M θ(x)·nVectorPushforward k (Dg_j(x)) (ξ(x)) (ω(g_j(x))) dH^k(x) → S(ω) for every sequence of C¹ maps g_j with a common Lipschitz bound converging uniformly to g and every test form ω. Then for every D ∈ ℕ there are constants c_k ≥ 0 (k ∈ ℕ, depending only on D, k) such that for every map f : ℝ^D → ℝ^D there are operators P_k : D_k(ℝ^D) → D_k(ℝ^D) and H_k : D_k(ℝ^D) → D_{k+1}(ℝ^D) (all k) with the following properties. (I) For every k, closed E ⊆ ℝ^D, Λ ≥ 0, δ > 0, b ∈ ℝ such that f is Λ-Lipschitz on the open δ-neighbourhood thickening δ E and |f(x) − x| ≤ b for x ∈ E, and every X ∈ D_k(ℝ^D) with M(X) < ∞, M(∂X) < ∞ in case k = j + 1 (formally: every Y ∈ D_{j+1} with k = j + 1 and HEq Y X has M(∂Y) < ∞) and spt X ⊆ E: (1) M(P_kX) ≤ c_kΛ^kM(X); (2) M(H_kX) ≤ c_k·b·(1 + Λ)^k·M(X); (3) spt P_kX ⊆ closure f(spt X); (4) spt H_kX ⊆ cthickening b (spt X); (5) if X is integer multiplicity then so are P_kX and H_kX; (6) (tangential vanishing) if α ∈ SimonMultiIndex k D, z ∈ ℝ^D, ω ∈ D^k(ℝ^D), ε > 0, every x ∈ thickening ε (spt X) with f(x) ∈ thickening ε (tsupport ω) satisfies f(x)_i = z_i for all i ∉ range α, and ω(y)(e_{α(1)},…,e_{α(k)}) = 0 for every y, then P_kX(ω) = 0; (7) (linearity) if X₁ ∈ D_k(ℝ^D) satisfies the same hypotheses (M(X₁) < ∞, the boundary condition, spt X₁ ⊆ E) and X₂(ω) = aX(ω) + a₁X₁(ω) for all ω, then P_kX₂(ω) = aP_kX(ω) + a₁P_kX₁(ω) and H_kX₂(ω) = aH_kX(ω) + a₁H_kX₁(ω) for all ω. (II) For every j, E, Λ, δ, b as above and X ∈ D_{j+1}(ℝ^D) with M(X) < ∞, M(∂X) < ∞, spt X ⊆ E: (8) ∂(P_{j+1}X) = P_j(∂X); (9) X(ω) − P_{j+1}X(ω) = ∂(H_{j+1}X)(ω) + H_j(∂X)(ω) for every ω (homotopy from f at t = 0 to the identity at t = 1).

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1115

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/755, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2732, https://github.com/ZhengyangZhang06/gmt-formalize/issues/720, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1070

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5222, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5233, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5242, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5252, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5257, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5263, https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/755, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3624, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2463, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5270

## Lean problem

Declaration: `Submission.deformation_pushforward_homotopy`

```lean
(∀ (P Q k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → (∀ x ∈ M, ∃ j : ℕ, θ x = j) → (∀ ω : TestFormOn (univ : Set (Eucl P)) k, X ω = tauAction k M θ ξ ω) → ∀ (g : Eucl P → Eucl Q) (Λ : ℝ≥0), LipschitzWith Λ g → (∀ K : Set (Eucl Q), IsCompact K → IsCompact (g ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl Q)) k, IsLipschitzPushforward X g S ∧ IsIntegerMultiplicity S ∧ ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : TestFormOn (univ : Set (Eucl Q)) k, Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) ((ω : DifferentialForm (Eucl Q) k) (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (S ω))) → ∀ D : ℕ, ∃ c : ℕ → ℝ≥0, ∀ f : Eucl D → Eucl D, ∃ (Pf : (k : ℕ) → GeometricCurrentOn (univ : Set (Eucl D)) k → GeometricCurrentOn (univ : Set (Eucl D)) k) (Hf : (k : ℕ) → GeometricCurrentOn (univ : Set (Eucl D)) k → GeometricCurrentOn (univ : Set (Eucl D)) (k + 1)), (∀ (k : ℕ) (E : Set (Eucl D)) (Λ : ℝ≥0) (δ b : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl D)) k), IsClosed E → 0 < δ → LipschitzOnWith Λ f (thickening δ E) → (∀ x ∈ E, dist (f x) x ≤ b) → X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl D)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → X.support ⊆ E → (Pf k X).mass ≤ (c k : ℝ≥0∞) * (Λ : ℝ≥0∞) ^ k * X.mass ∧ (Hf k X).mass ≤ (c k : ℝ≥0∞) * ENNReal.ofReal b * (1 + (Λ : ℝ≥0∞)) ^ k * X.mass ∧ (Pf k X).support ⊆ closure (f '' X.support) ∧ (Hf k X).support ⊆ cthickening b X.support ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (Pf k X) ∧ IsIntegerMultiplicity (Hf k X)) ∧ (∀ (α : SimonMultiIndex k D) (z : Eucl D) (ω : TestFormOn (univ : Set (Eucl D)) k) (ε : ℝ), 0 < ε → (∀ x ∈ thickening ε X.support, f x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl D) k)) → ∀ i, i ∉ range α → f x i = z i) → (∀ y, (ω : DifferentialForm (Eucl D) k) y (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) → Pf k X ω = 0) ∧ ∀ (X₁ X₂ : GeometricCurrentOn (univ : Set (Eucl D)) k) (a a₁ : ℝ), X₁.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl D)) (j + 1)), k = j + 1 → HEq Y X₁ → Y.boundary.mass < ∞) → X₁.support ⊆ E → (∀ ω, X₂ ω = a * X ω + a₁ * X₁ ω) → (∀ ω, Pf k X₂ ω = a * Pf k X ω + a₁ * Pf k X₁ ω) ∧ ∀ ω, Hf k X₂ ω = a * Hf k X ω + a₁ * Hf k X₁ ω) ∧ ∀ (j : ℕ) (E : Set (Eucl D)) (Λ : ℝ≥0) (δ b : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl D)) (j + 1)), IsClosed E → 0 < δ → LipschitzOnWith Λ f (thickening δ E) → (∀ x ∈ E, dist (f x) x ≤ b) → X.mass < ∞ → X.boundary.mass < ∞ → X.support ⊆ E → (Pf (j + 1) X).boundary = Pf j X.boundary ∧ ∀ ω, X ω - Pf (j + 1) X ω = (Hf (j + 1) X).boundary ω + Hf j X.boundary ω
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

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part I of the supplied proof of deformation_onto_skeleton — A2 (Simon Ch. 6, 2.17–2.29: products with [[(0,1)]], push-forward by smooth maps, the homotopy formula 2.25, the affine-homotopy estimate 2.27, Lemmas 2.28–2.29 on Lipschitz push-forwards), A4(a),(d) (Simon 3.2(2): products of integer multiplicity currents), I.6 (the maps ψ̄_σ, h̄_σ near a region {d_a ≥ σ}, independence of σ, linearity, masses, supports, homotopy formula) and I.7 (integrality of push-forwards through the sibling deformation_im_pushforward_limit, whose conclusion is the premise (S5′) of this child) — together with the analytic core of Step 7 (mollified maps with locally constant normal coordinates kill forms without tangential component). The parent applies these tools to the single map f = ψ of deformation_retraction on the regions E = {d_a ≥ σ}; here they are stated for an arbitrary map f : ℝ^D → ℝ^D on an arbitrary closed region E on whose δ-neighbourhood f is Lipschitz. Using one map f for all regions replaces the parent's σ-dependent extensions ψ̄_σ, h̄_σ: the operators below depend only on f, and their independence of the region is proved in Step 6.2 exactly as the parent's I.6 proves independence of σ (via the support clause of 2.28). Sign convention: the homotopy is taken from f (t = 0) to the identity (t = 1); by 2.25 this gives X − f_#X = ∂H + H∂, i.e. the corrected sign of the parent's erratum (iii) is built into H.

PART 0 — NOTATION AND STANDING FACTS.

0.1 (Notation.) For m ∈ ℕ, ℝ^m = Eucl m with standard basis e_1,…,e_m (indexed by Fin m) and Euclidean norm |·|. D_k(ℝ^m) := GeometricCurrentOn univ k, D^k(ℝ^m) := TestFormOn univ k. For a k-covector α, |α| := covectorEuclideanNorm α = (Σ_{γ∈I(k,m)} α(e_γ)²)^{1/2}; for a k-form ω, ‖ω‖ := sup_x |ω(x)| (finite for continuous compactly supported ω). M = mass, M_W = massOn W, spt = support. ‖A‖ is the operator norm of a linear map. For a C¹ map g : ℝ^m → ℝ^{m′} and a k-form ω on ℝ^{m′}, g^#ω(x) := (ω(g(x))).compContinuousLinearMap(Dg(x)), i.e. g^#ω(x)(v_1,…,v_k) = ω(g(x))(Dg(x)v_1,…,Dg(x)v_k). For A ⊆ ℝ^m and r > 0, A_r := thickening r A = {x : dist(x, A) < r} (open; mem_thickening_iff: x ∈ A_r iff some a ∈ A has |x − a| < r; ∅_r = ∅). A current X ∈ D_k(ℝ^m) is called normal if M(X) < ∞ and, when k = j + 1, M(∂X) < ∞. (In the Lean statement the boundary condition for a general degree k is written "for every j and Y ∈ D_{j+1} with k = j + 1 and HEq Y X, M(∂Y) < ∞"; for k = 0 it is vacuous, and for k = j + 1 it is equivalent to M(∂X) < ∞, by specializing to Y := X, resp. by Nat.succ.inj and eq_of_heq.)

0.2 (Reused facts; sibling children. (F1)–(F3), (F9), (F10) are reused comparator-accepted declarations declared as dependencies of this child; (F4) is a SimonGMT theorem; (F5)–(F8), (F11) are proved here.)
 (F1) mass_bound: if 0 ≤ B′, M_W(Y) ≤ B′, tsupport ω ⊆ W and |ω(x)| ≤ C′ for all x, then |Y(ω)| ≤ B′C′. In particular |Y(ω)| ≤ M(Y)‖ω‖ when M(Y) < ∞.
 (F2) vanish_off_support: Y(ω) = 0 whenever tsupport ω ∩ spt Y = ∅.
 (F2′) Consequence: if η, η′ ∈ D^k agree on an open set N ⊇ spt Y, then Y(η) = Y(η′). Indeed η − η′ vanishes on N, so tsupport(η − η′) ⊆ closure(ℝ^m ∖ N) = ℝ^m ∖ N (N open), which is disjoint from spt Y; apply (F2) and linearity. Also: a current with empty support is 0 (apply (F2) to every ω).
 (F3) support_lemmas: (1) spt ∂Y ⊆ spt Y; (2) weak limits of currents supported in a closed set F are supported in F; (3) spt(aY₁ + bY₂) ⊆ spt Y₁ ∪ spt Y₂ (for a current equal pointwise to aY₁ + bY₂).
 (F4) Lower semicontinuity (SimonGMT WeaklyConvergesOn.massOn_le_liminf): if Y_j ⇀ Y then M(Y) ≤ liminf_j M(Y_j).
 (F5) If TestFormOnConverges ω_j 0 then ‖ω_j‖ → 0 and ‖dω_j‖ → 0: all supports lie in one compact K, iteratedFDeriv ℝ q ω_j → 0 uniformly on K for q = 0, 1; ‖iteratedFDeriv ℝ 0 ω_j x‖ = ‖ω_j(x)‖ and dω_j(x) = alternatizeUncurryFin(Dω_j(x)) has operator norm ≤ (k+1)‖Dω_j(x)‖; finally |α| ≤ √(m^k)·‖α‖ for every k-covector (each coefficient α(e_γ) has absolute value ≤ ‖α‖).
 (F6) Criterion: if T : D^k(ℝ^m) → ℝ is linear and |T(ω)| ≤ B‖ω‖ for all ω, then T is a current (sequential continuity by (F5)). More generally it suffices that for every compact K there is B_K with |T(ω)| ≤ B_K‖ω‖ for all ω with tsupport ω ⊆ K.
 (F7) Pull-back bound: for a linear A : ℝ^m → ℝ^{m′} and a k-covector α on ℝ^{m′}, |α∘A| ≤ ‖A‖^k|α|, where (α∘A)(v) := α(Av_1,…,Av_k). Proof: for an alternating k-form γ on ℝ^p, Σ_{I∈[p]^k} γ(e_{I_1},…,e_{I_k})² = k!·|γ|² (tuples with a repeated index contribute 0; each increasing γ-tuple arises from k! orderings, with the same square). One-slot bound: for a linear functional λ on ℝ^{m′}, Σ_{a} λ(Ae_a)² = |Aᵀλ|² ≤ ‖A‖²|λ|² = ‖A‖² Σ_b λ(e_b)². Applying the one-slot bound successively to slots 1,…,k (the other slots fixed) gives Σ_{I∈[m]^k} α(Ae_{I_1},…,Ae_{I_k})² ≤ ‖A‖^{2k} Σ_{J∈[m′]^k} α(e_{J_1},…,e_{J_k})², i.e. k!|α∘A|² ≤ ‖A‖^{2k}k!|α|². (The same computation is carried out in the accepted declarations iwl_sp_pn_sum_sq_comp_basis_le and iwl_sp_pn_multilinear_sum_sq_le of another branch, which a later decomposition of this child may reuse; the argument given here is complete.)
 (F8) Interior product: for a (k+1)-covector α on ℝ^{m′} and w ∈ ℝ^{m′}, the k-covector α(w, ·) satisfies |α(w, ·)| ≤ c₁|w||α| with c₁ = c₁(m′, k) := √(m′^k)·√m′: indeed α(w, e_γ) = Σ_i w_i α(e_i, e_γ) and each α(e_i, e_γ) is ± a coefficient of α or 0, so |α(w, e_γ)| ≤ √m′|w||α|. Consequently, for linear A : ℝ^m → ℝ^{m′}, the k-covector v ↦ α(w, Av_1,…,Av_k) has norm ≤ c₁|w|‖A‖^k|α| (by (F7) applied to α(w, ·)).
 (F9) support_null (reused sibling lpf_rectifiable_support_null): if IsRectifiableTriple U k M θ ξ and Y(ω) = tauAction k M θ ξ ω for all test forms ω, then H^k(M ∖ spt Y) = 0.
 (F10) lipschitz_area (reused sibling lpf_raf_local_lipschitz_area; the area formula with multiplicities): for Ω ⊆ ℝ^n open, u locally Lipschitz on Ω, D ⊆ Ω Lebesgue-null-measurable and w ≥ 0 a.e.-measurable on D, the fibre sum y ↦ Σ_{x∈D, u(x)=y} w(x) is H^n-a.e.-measurable and ∫_D w(x)·Ju(x) dx = ∫ Σ_{x∈D, u(x)=y} w(x) dH^n(y), where Ju(x) := √det(⟨Du(x)e_i, Du(x)e_j⟩)_{i,j}.
 (F11) Coefficient bound: for a k-covector α on ℝ^p and vectors τ_1,…,τ_k with |τ_i| ≤ 1, |α(τ_1,…,τ_k)| ≤ p^{k/2}|α|. Expand each τ_i = Σ_a τ_i^a e_a: α(τ) = Σ_{J∈[p]^k} (Π_i τ_i^{J_i}) α(e_{J_1},…,e_{J_k}); each |α(e_J)| ≤ |α| (it is ± a coefficient of α or 0), and Σ_J Π_i|τ_i^{J_i}| = Π_i Σ_a|τ_i^a| ≤ (√p)^k.

PART 1 — LIPSCHITZ MAPS: EXTENSION AND MOLLIFICATION.

1.1 (McShane extension.) If F : ℝ^m → ℝ^{m′} is Λ-Lipschitz on a set A, there is F̂ : ℝ^m → ℝ^{m′}, √m′·Λ-Lipschitz on ℝ^m, with F̂ = F on A: each coordinate F_i is Λ-Lipschitz on A (|F_i(x) − F_i(y)| ≤ |F(x) − F(y)|), extend it by LipschitzOnWith.extend_real to a Λ-Lipschitz F̂_i on ℝ^m, and put F̂ := (F̂_i)_i; then |F̂(x) − F̂(y)|² = Σ_i|F̂_i(x) − F̂_i(y)|² ≤ m′Λ²|x − y|².

1.2 (Mollifier.) Fix a C^∞ function ϕ ≥ 0 on ℝ^m with tsupport ϕ ⊆ closedBall(0, 1/2) and ∫ϕ = 1 (take a smooth bump b ≥ 0 with b(0) = 1 and tsupport b ⊆ closedBall(0, 1/2) from exists_contDiff_tsupport_subset, and normalize by ∫b > 0). For σ > 0 put ϕ_σ(w) := σ^{−m}ϕ(w/σ): C^∞, ≥ 0, support in the open ball B_σ(0), ∫ϕ_σ = 1. For a continuous G : ℝ^m → ℝ^{m′} put G_σ(x) := ∫ G(x − w)ϕ_σ(w)dw (the convolution of ϕ_σ with G for the scalar action).
 (a) G_σ is C^∞ (HasCompactSupport.contDiff_convolution_left: ϕ_σ is C^∞ with compact support and G is locally integrable).
 (b) (Locality.) G_σ(x) only depends on G restricted to B_σ(x) (the integrand vanishes for |w| ≥ σ). In particular: if G = G′ on B_σ(x) then G_σ(x) = G′_σ(x); if the i-th coordinate G_i equals a constant c on B_σ(x), then (G_σ)_i(x) = c (∫ϕ_σ = 1).
 (c) (Lipschitz bounds.) If G is Λ-Lipschitz on the open ball B_{2σ}(x), then G_σ is Λ-Lipschitz on B_σ(x) (for y, y′ ∈ B_σ(x) and |w| < σ, y − w, y′ − w ∈ B_{2σ}(x), so |G_σ(y) − G_σ(y′)| ≤ ∫Λ|y − y′|ϕ_σ), hence ‖DG_σ(x)‖ ≤ Λ (difference quotients along any v at x stay in B_σ(x)); and |G_σ(x) − G(x)| = |∫(G(x − w) − G(x))ϕ_σ(w)dw| ≤ ∫Λ|w|ϕ_σ(w)dw ≤ Λσ. If G is L-Lipschitz on all of ℝ^m, then G_σ is L-Lipschitz on ℝ^m, ‖DG_σ‖ ≤ L everywhere (norm_fderiv_le_of_lipschitz) and sup|G_σ − G| ≤ Lσ, so G_{1/j} → G uniformly.
 Terminology: for a globally L-Lipschitz G, an admissible approximating sequence is a sequence of C^∞ maps G_j : ℝ^m → ℝ^{m′} with a common Lipschitz constant L′ and G_j → G uniformly on ℝ^m. By (a), (c) the mollifications G_{1/j} form one (with L′ = L).

PART 2 — PUSH-FORWARD BY SMOOTH MAPS (Simon 2.23–2.24).
Throughout this part X ∈ D_k(ℝ^m), A ⊆ ℝ^m is closed with spt X ⊆ A, g : ℝ^m → ℝ^{m′} is C^∞, and g|A is proper: g⁻¹(K) ∩ A is compact for every compact K.

2.1 (Compatible forms.) For ω ∈ D^k(ℝ^{m′}) call η ∈ D^k(ℝ^m) compatible with (g, ω) near A if η = g^#ω on some open N ⊇ A. Such η exist, and for every open O containing C := A ∩ g⁻¹(tsupport ω) they can be chosen of the form η = ζ·g^#ω with ζ ∈ C_c^∞(ℝ^m), 0 ≤ ζ ≤ 1, tsupport ζ ⊆ O. Proof: C is compact (properness). Choose r > 0 with C_{4r} ⊆ O (IsCompact.exists_thickening_subset_open) and let ζ(x) := ∫ 1_{C_{2r}}(x − w)ϕ_r(w)dw be the mollification at scale r (1.2) of the indicator of the open set C_{2r}. Then ζ is C^∞ (1.2(a)), 0 ≤ ζ ≤ 1, ζ = 1 on the open set V := C_r (for x ∈ C_r and |w| < r, x − w ∈ C_{2r}), and tsupport ζ ⊆ cthickening (3r) C ⊆ C_{4r} ⊆ O is compact (any smooth Urysohn function with these properties will do; the accepted declarations fiw_tb_ext_cutoff and iwl_sp_exists_compatible_testForm of other branches contain the same construction and may be reused by a later decomposition). Then η := ζ·g^#ω is C^∞ (ω∘g and Dg are C^∞, and compContinuousLinearMap is continuous bilinear), has compact support (⊆ tsupport ζ), so η ∈ D^k(ℝ^m); and η = g^#ω on the open set N := V ∪ (ℝ^m ∖ g⁻¹(tsupport ω)), which contains A (points of A with g(x) ∈ tsupport ω lie in C ⊆ V; at the others g^#ω(x) = 0 = η(x) on the open complement).
2.2 (Definition and linearity.) g_#X(ω) := X(η) for any η compatible with (g, ω) near A. By (F2′) this does not depend on η (two compatible forms agree on the intersection of their open sets, which contains spt X), nor on the closed set A ⊇ spt X used (a form compatible near A is compatible near spt X; compatibility near spt X is all that (F2′) needs). g_#X is linear in ω (if η₁, η₂ are compatible for ω₁, ω₂ then aη₁ + bη₂ is compatible for aω₁ + bω₂ on the intersection of the open sets). It is linear in X: if X, X′ have supports in A and X″ = aX + a′X′ pointwise, then spt X″ ⊆ A (F3(3)) and, with one η compatible near A, g_#X″(ω) = X″(η) = aX(η) + a′X′(η).
2.3 (Current and mass.) Assume M(X) < ∞. (i) g_#X is a current: if TestFormOnConverges ω_j 0 with supports in a compact K, put C_K := A ∩ g⁻¹(K) (compact) and fix one ζ for C_K as in 2.1; then η_j := ζ·g^#ω_j are compatible for all j, |η_j(x)| ≤ sup_{tsupport ζ}‖Dg‖^k·‖ω_j‖ by (F7), so |g_#X(ω_j)| ≤ M(X)·sup_{tsupport ζ}‖Dg‖^k·‖ω_j‖ → 0 by (F1), (F5). (ii) If O ⊇ spt X is open and ‖Dg(x)‖ ≤ L for x ∈ O, then |g_#X(ω)| ≤ L^kM(X)‖ω‖ for all ω, hence M(g_#X) ≤ L^kM(X): choose η = ζ·g^#ω with tsupport ζ ⊆ O (2.1 with A replaced by the closed set spt X); then |η(x)| ≤ ‖Dg(x)‖^k|ω(g(x))| ≤ L^k‖ω‖ on O by (F7), η = 0 off O, and (F1) applies; for ω mass-admissible (‖ω‖ ≤ 1) this gives ofReal(g_#X(ω)) ≤ L^kM(X).
2.4 (Support.) spt g_#X ⊆ closure g(spt X). If tsupport ω ∩ g(spt X) = ∅, then g^#ω = 0 on the open set ℝ^m ∖ g⁻¹(tsupport ω) ⊇ spt X, so η := 0 is compatible near spt X and g_#X(ω) = X(0) = 0. If y ∉ closure g(spt X), a small ball W around y (compact closure) misses closure g(spt X), every ω with tsupport ω ⊆ W gives g_#X(ω) = 0, so W lies in the zero region and y ∉ spt g_#X.
2.5 (Boundary; Simon 2.24(1).) If k = j + 1 then ∂(g_#X) = g_#(∂X) (spt ∂X ⊆ spt X ⊆ A by (F3)(1), so g_#(∂X) is defined). For φ ∈ D^j(ℝ^{m′}) let θ be compatible with (g, φ) near A, θ = g^#φ on the open N. The exterior derivative is local and commutes with pull-back by C^∞ maps (Mathlib extDeriv_pullback: d(g^#φ) = g^#(dφ)), so dθ = d(g^#φ) = g^#(dφ) on N: dθ is compatible with (g, dφ). Hence ∂(g_#X)(φ) = g_#X(dφ) = X(dθ) = ∂X(θ) = g_#(∂X)(φ). (The accepted declaration iwl_sp_boundary_apply_eq_of_compatible of another branch states the same fact and may be reused by a later decomposition.)
2.6 (Rectifiable representation; Simon 2.24(2)–(3).) Let X = τ(M, θ, ξ) with IsRectifiableTriple univ k M θ ξ (θ > 0 real). Then H^k(M ∖ spt X) = 0, and for every ω and every η compatible with (g, ω) near spt X:
   g_#X(ω) = X(η) = ∫_M θ(x)·nVectorPushforward k (Dg(x)) (ξ(x)) (ω(g(x))) dH^k(x).
 Proof. H^k(M ∖ spt X) = 0 by (F9) (this is the bracket in the parent's I.7: X kills test forms supported in ℝ^m ∖ spt X, so the vector measure θξH^k⌞M vanishes there, while θ > 0 and ξ ≠ 0 a.e. on M). (Formula.) X(η) = tauAction k M θ ξ η = ∫_M θ(x)ξ(x)(η(x)) dH^k. For x ∈ M ∩ spt X (H^k-almost all of M) we have x ∈ N, so η(x) = (ω(g(x))).compContinuousLinearMap(Dg(x)) = covectorPullback k (Dg(x)) (ω(g(x))) and ξ(x)(η(x)) = (ξ(x) ∘ covectorPullback k (Dg(x)))(ω(g(x))) = nVectorPushforward k (Dg(x)) (ξ(x)) (ω(g(x))) by the definition of nVectorPushforward (w ↦ w.comp(covectorPullback n L)). ∎(2.6)
PART 3 — PRODUCTS WITH [[(0,1)]] (Simon 2.17–2.22, 3.2(2); parent A2(a), A4(d)).
Coordinates: ℝ^{1+m} ∋ y = (t, x) with t ∈ ℝ the first coordinate and x ∈ ℝ^m (identify Eucl(m+1) with ℝ × ℝ^m by Fin.cons, as in the frozen statement of iwl_cr_interval_product_im); e_0 := (1, 0); ι : ℝ^m → ℝ^{1+m}, ι(v) := (0, v); j_s : ℝ^m → ℝ^{1+m}, j_s(x) := (s, x); pr(t, x) := x. Let X ∈ D_k(ℝ^m) with M(X) < ∞.

3.1 (Slice forms.) For φ ∈ D^{k+1}(ℝ^{1+m}) and t ∈ ℝ define the dt-coefficient form φ^{(t)} ∈ D^k(ℝ^m), φ^{(t)}(x)(v_1,…,v_k) := φ(t, x)(e_0, ιv_1,…,ιv_k); for ψ ∈ D^k(ℝ^{1+m}) and s ∈ ℝ define the slice ψ_s := j_s^#ψ, ψ_s(x)(v) := ψ(s, x)(ιv_1,…,ιv_k). Both are C^∞ in (t, x) (compositions of C^∞ maps with continuous multilinear operations), with tsupport φ^{(t)} ⊆ {x : (t, x) ∈ tsupport φ} (compact), so they are test forms. Their coefficients are ± coefficients of φ(t, x), resp. ψ(s, x), so |φ^{(t)}(x)| ≤ |φ(t, x)| and |ψ_s(x)| ≤ |ψ(s, x)|; and t ↦ φ^{(t)}, s ↦ ψ_s are continuous for ‖·‖ (φ, ψ are uniformly continuous), with supports in a fixed compact set; likewise ∂_tψ_t (the t-derivative of the slice) is a test form, and (ψ_{t+h} − ψ_t)/h → ∂_tψ_t in ‖·‖ as h → 0 (uniform continuity of Dψ).
3.2 (Definition.) ([[0,1]]×X)(φ) := ∫_0^1 X(φ^{(t)}) dt. By (F1), |X(φ^{(t)}) − X(φ^{(t′)})| ≤ M(X)‖φ^{(t)} − φ^{(t′)}‖, so the integrand is continuous and the integral exists; it is linear in φ and in X; |([[0,1]]×X)(φ)| ≤ M(X)‖φ‖. Hence [[0,1]]×X ∈ D_{k+1}(ℝ^{1+m}) by (F6), with M([[0,1]]×X) ≤ M(X). Similarly ({s}×X)(ψ) := X(ψ_s) defines {s}×X ∈ D_k(ℝ^{1+m}) with M({s}×X) ≤ M(X).
3.3 (Supports.) spt([[0,1]]×X) ⊆ [0,1] × spt X and spt({s}×X) ⊆ {s} × spt X (closed sets). If tsupport φ misses [0,1] × spt X, then for t ∈ [0,1], tsupport φ^{(t)} ∩ spt X = ∅, so X(φ^{(t)}) = 0 (F2) and ([[0,1]]×X)(φ) = 0; conclude as in 2.4. Same for {s}×X.
3.4 (Boundary; Simon 2.19, 2.21.) If k = j + 1 and M(∂X) < ∞, then ∂([[0,1]]×X) = {1}×X − {0}×X − [[0,1]]×∂X; if k = 0, ∂([[0,1]]×X) = {1}×X − {0}×X. Proof. Let ψ ∈ D^k(ℝ^{1+m}). The exterior derivative is dψ(y)(u_0,…,u_k) = Σ_{i=0}^k (−1)^i Dψ(y)(u_i)(u_0,…,û_i,…,u_k) (Mathlib's alternatizeUncurryFin, used by SimonGMT's exteriorDerivative). Take y = (t, x), u_0 = e_0, u_i = ιv_i (i ≥ 1). The i = 0 term is Dψ(y)(e_0)(ιv_1,…,ιv_k) = ∂_t[ψ(t, x)(ιv)] = (∂_tψ_t)(x)(v). For i ≥ 1 the term is (−1)^i Dψ(y)(ιv_i)(e_0, ιv_1,…,ι̂v_i,…,ιv_k) = (−1)^i D(ψ^{(t)})(x)(v_i)(v_1,…,v̂_i,…,v_k), where ψ^{(t)} is the (k−1)-form x ↦ ψ(t, x)(e_0, ι·); and d(ψ^{(t)})(x)(v_1,…,v_k) = Σ_{i=1}^k (−1)^{i−1} D(ψ^{(t)})(x)(v_i)(…v̂_i…). Hence
   (dψ)^{(t)} = ∂_t(ψ_t) − d(ψ^{(t)})   (for k = 0 only the first term occurs).
 Therefore ∂([[0,1]]×X)(ψ) = ([[0,1]]×X)(dψ) = ∫_0^1 X(∂_tψ_t) dt − ∫_0^1 X(d(ψ^{(t)})) dt. By 3.1 and (F1), t ↦ X(ψ_t) is differentiable with derivative X(∂_tψ_t), which is continuous, so the first integral is X(ψ_1) − X(ψ_0) = ({1}×X)(ψ) − ({0}×X)(ψ) (intervalIntegral.integral_eq_sub_of_hasDerivAt). The second is ∫_0^1 ∂X(ψ^{(t)}) dt = ([[0,1]]×∂X)(ψ) (3.2 applied to ∂X, which has finite mass).
3.5 (Integer multiplicity; Simon 3.2(2), parent A4(d).) Let X = τ(M, θ, ξ) with IsRectifiableTriple univ k M θ ξ and θ(M) ⊆ ℕ. Put M̃ := (0,1) × M ⊆ ℝ^{1+m}, θ̃ := θ∘pr, and ξ̃(t, x) := e_0∧ξ(x), the (k+1)-vector α ↦ ξ(x)(α(e_0, ι·)) (note simpleNVector(e_0, ιτ_1,…,ιτ_k)(α) = α(e_0, ιτ) = simpleNVector(τ)(α(e_0, ι·)), so e_0∧simpleNVector τ = simpleNVector(e_0, ιτ)). Then (M̃, θ̃, ξ̃) is a rectifiable triple in ℝ^{1+m}, θ̃(M̃) ⊆ ℕ, and [[0,1]]×X = τ(M̃, θ̃, ξ̃); in particular [[0,1]]×X is integer multiplicity. Proof.
 (a) (Local finiteness.) θ ≥ 1 on M, so H^k(M ∩ K) ≤ ∫_{M∩K}θ dH^k < ∞ for compact K.
 (b) (Product formula; Federer 2.10.45, 3.2.23.) For every bounded open interval I ⊆ ℝ, every H^k-null-measurable, countably k-rectifiable M′ ⊆ ℝ^m with H^k⌞M′ locally finite (e.g. M′ = M, or a rescaling η_{x,r}(M) = (M − x)/r of M), and every Borel F ≥ 0 on ℝ^{1+m}: ∫_{I×M′} F dH^{k+1} = ∫_I ∫_{M′} F(t, x) dH^k(x) dt. (It then also holds for every F ≥ 0 that agrees H^{k+1}⌞(I×M′)-a.e. and, for a.e. t, H^k⌞M′-a.e. with a Borel function, by the null part below; this covers θ∘pr, since θ agrees H^k⌞M-a.e. with a Borel function.) We write M′ = M, I = (0,1); the general case is identical. Proof.
   (Null part.) If H^k(B) = 0 then H^{k+1}(ℝ × B) = 0. For k = 0, H^0(B) = 0 forces B = ∅. For k ≥ 1, fix η ∈ (0,1) and R > 0; cover B by sets B_i with diameters d_i < η and Σ_i d_i^k < η, and replace d_i by d′_i := d_i + (η2^{−i})^{1/k} > 0, so that d′_i < 2η^{1/k} and Σ_i d′_i^k ≤ 2^{k−1}(Σ_i d_i^k + η) ≤ 2^kη. Cover [−R, R] × B_i by ⌈2R/d′_i⌉ + 1 sets [a, a + d′_i] × B_i of diameter ≤ √2·d′_i. Then the size-(2√2η^{1/k}) Hausdorff premeasure of [−R, R] × B is ≤ Σ_i (2R/d′_i + 2)(√2d′_i)^{k+1} ≤ c(k)(R + 1)Σ_i d′_i^k ≤ c(k)(R + 1)2^kη → 0 as η → 0. Hence H^{k+1}([−R, R] × B) = 0 for every R, and H^{k+1}(ℝ × B) = 0. Consequently ℝ × M₀ and ℝ × (M Δ M″) are H^{k+1}-null, where M ⊆ M₀ ∪ ⋃_j F_j(ℝ^k) (H^k(M₀) = 0, F_j Lipschitz; CountablyRectifiable; we enlarge M₀ to a Borel H^k-null set) and M″ is a Borel set with H^k(M Δ M″) = 0 (null-measurability), which we replace by the Borel set M″ ∩ (M₀ ∪ ⋃_j F_j(ℝ^k)) (each F_j(ℝ^k) is σ-compact); this does not enlarge M Δ M″ because M ⊆ M₀ ∪ ⋃_j F_j(ℝ^k). In particular (0,1) × M is H^{k+1}-null-measurable.
   (Borel pieces.) Let (Q_q)_q be the countable partition of ℝ^k into half-open unit cubes. Each F_j(Q_q) is σ-compact, hence Borel. Enumerate the pairs (j, q) and let P_{j,q} := (M″ ∩ F_j(Q_q)) ∖ (M₀ ∪ earlier F_{j′}(Q_{q′})): pairwise disjoint Borel subsets of M″ with M″ ∖ M₀ = ⋃_{j,q} P_{j,q} (as M″ ⊆ M₀ ∪ ⋃_{j,q} F_j(Q_q)). Fix (j, q), write u := F_j, P := P_{j,q}, C := Q_q ∩ u⁻¹(P) (Borel, bounded) and N(x) := #(C ∩ u⁻¹(x)) ∈ [0, ∞]. Then N ≥ 1 on P, N = 0 off P, N is H^k-a.e.-measurable and ∫ N dH^k = ∫_C Ju ≤ Lip(u)^k·L^k(Q_q) < ∞ by (F10) (Ω = ℝ^k, D = C, w = 1); hence P_∞ := P ∩ {N = ∞} is H^k-null.
   (Product formula on a piece, without injectivity.) Let G(s, v) := (s, u(v)) on ℝ^{1+k} = ℝ × ℝ^k (Lebesgue measure = L¹ ⊗ L^k). G is Lipschitz; where u is differentiable, DG(s, v) maps e_0 to e_0 and e_i to ιDu(v)e_i, so the Gram matrix is block diagonal with blocks 1 and (⟨Du e_i, Du e_j⟩) and JG(s, v) = Ju(v) (where u is not differentiable, neither is G and both Jacobians are 0). The fibre of G over (t, x) inside I × C is {t} × (C ∩ u⁻¹(x)) if t ∈ I and empty otherwise. Fix a Borel function N′ : ℝ^m → [0, ∞] with N′ = N H^k-a.e. (N is H^k-a.e.-measurable); Z := {N ≠ N′} is H^k-null, so ℝ × Z is H^{k+1}-null (null part). For Borel h ≥ 0 on ℝ^{1+m} put w(s, v) := h(s, u(v))/N′(u(v)) if 1 ≤ N′(u(v)) < ∞ and w := 0 otherwise (a Borel function). Then for (t, x) ∉ ℝ × Z: Σ_{(s,v) ∈ (I×C)∩G⁻¹(t,x)} w(s, v) = 1_I(t)·1_{P∖P_∞}(x)·h(t, x) (the fibre has N(x) = N′(x) points, each contributing h(t, x)/N(x), when t ∈ I and x ∈ P ∖ P_∞; it is empty when t ∉ I or x ∉ P; and w = 0 on it when x ∈ P_∞). By (F10) for G (D = I × C) and Tonelli (Lebesgue measure on ℝ^{1+k} is L¹ ⊗ L^k), ∫_{I×(P∖P_∞)} h dH^{k+1} = ∫_{I×C} w·JG = ∫_I [∫_C w(s, v)·Ju(v) dv] ds, and by (F10) for u with the Borel weight v ↦ w(s, v) (whose fibre sum at x ∉ Z is 1_{P∖P_∞}(x)·h(s, x)) the inner integral is ∫_{P∖P_∞} h(s, x) dH^k(x). Since P_∞ is H^k-null, I × P_∞ is H^{k+1}-null (null part), so ∫_{I×P} h dH^{k+1} = ∫_I ∫_P h(s, x) dH^k(x) ds.
   (Summation.) Both sides are countably additive over the disjoint pieces P_{j,q}. Since M Δ ⋃_{j,q}P_{j,q} ⊆ M₀ ∪ (M Δ M″) (both inclusions: points of M outside ⋃P lie in M₀ ∪ (M ∖ M″), and ⋃P ∖ M ⊆ M″ ∖ M), the sets I × (M Δ ⋃P_{j,q}) and M Δ ⋃P_{j,q} are null for H^{k+1}, resp. H^k, by the null part. Summing gives (b) for indicators of Borel sets, hence for all Borel F ≥ 0 (monotone convergence through simple functions).
 (c) (Triple conditions.) M̃ ⊆ univ; null-measurable by (b); countably (k+1)-rectifiable: M̃ ⊆ (ℝ × M₀) ∪ ⋃_j range G_j with G_j(s, u) = (s, F_j(u)) Lipschitz on ℝ^{1+k} (= ℝ^{k+1}), and H^{k+1}(ℝ × M₀) = 0 by the null part of (b); θ̃ > 0 and natural-valued on M̃; for compact K̃, ∫_{M̃∩K̃} θ̃ dH^{k+1} ≤ ∫_0^1∫_{M∩pr(K̃)} θ dH^k dt < ∞ by (b) (pr(K̃) compact); ξ̃ is H^{k+1}⌞M̃-measurable (composition of the measurable ξ∘pr with a continuous linear map). Orientation: by (b) and the orientation clause of (M, θ, ξ), for H^{k+1}-a.e. (t, x) ∈ M̃ we have t ∈ (0,1) and x is a point where ξ(x) = ±simpleNVector τ with τ orthonormal and HasWeightedApproximateTangentSpaceAt k M θ x (span τ). At such a point, (e_0, ιτ_1,…,ιτ_k) is orthonormal, ξ̃(t, x) = ±simpleNVector(e_0, ιτ), and HasWeightedApproximateTangentSpaceAt (k+1) M̃ θ̃ (t, x) (span(e_0, ιτ)): span(e_0, ιτ) has dimension k + 1; for f ∈ C_c(ℝ^{1+m}) supported in [−R, R] × B_R(0), the blow-up η_{(t,x),r}(M̃) equals (−t/r, (1−t)/r) × η_{x,r}(M), and by (b) (applied to the rescaled set, which satisfies the same hypotheses)
   ∫_{η_{(t,x),r}(M̃)} f(y)θ̃((t,x) + ry) dH^{k+1}(y) = ∫_{−t/r}^{(1−t)/r} [∫_{η_{x,r}(M)} f(s, y′)θ(x + ry′) dH^k(y′)] ds.
 For each fixed s the bracket tends to θ(x)∫_{span τ} f(s, ·) dH^k as r ↓ 0 (the hypothesis at x applied to f(s, ·) ∈ C_c(ℝ^m)); the brackets vanish for |s| > R and are bounded uniformly in s and in small r by ‖f‖_∞ ∫_{η_{x,r}(M)} g(y′)θ(x + ry′) dH^k(y′), which converges (hence is bounded for small r) for any g ∈ C_c(ℝ^m) with g ≥ 1 on B_R(0); and (−t/r, (1−t)/r) increases to ℝ. Dominated convergence in s gives the limit θ(x)∫_ℝ∫_{span τ} f(s, v) dH^k(v) ds = θ̃(t, x)∫_{span(e_0,ιτ)} f dH^{k+1} (the product formula (b) for (−R−1, R+1) × span τ, which contains the support of f on the plane ℝ × span τ = span(e_0, ιτ); equivalently, Lebesgue measure on that plane is L¹ ⊗ H^k⌞span τ). The exceptional set is contained in (0,1) × (an H^k-null subset of M), which is H^{k+1}-null by (b).
 (d) (Action.) For φ ∈ D^{k+1}(ℝ^{1+m}): τ(M̃, θ̃, ξ̃)(φ) = ∫_{M̃} θ̃(y)ξ̃(y)(φ(y)) dH^{k+1}(y) = ∫_0^1 ∫_M θ(x)ξ(x)(φ^{(t)}(x)) dH^k(x) dt = ∫_0^1 X(φ^{(t)}) dt = ([[0,1]]×X)(φ), by (b) and Fubini (the integrand is integrable: it vanishes unless x ∈ pr(tsupport φ), a compact set, and there |θ(x)ξ(x)(φ^{(t)}(x))| ≤ c·θ(x)‖φ‖ for H^k-a.e. x, because ξ(x) = ±simpleNVector τ with τ orthonormal a.e. and |simpleNVector τ (α)| = |α(τ)| ≤ m^{k/2}|α| by (F11)). ∎(3.5)

PART 4 — THE HOMOTOPY FORMULA FOR SMOOTH MAPS AND THE AFFINE ESTIMATE (Simon 2.25–2.27).
Let X ∈ D_k(ℝ^m) be normal and G : ℝ^{1+m} → ℝ^{m′} be C^∞ with G|([0,1] × spt X) proper; put F_s := G∘j_s (s = 0, 1), C^∞ maps ℝ^m → ℝ^{m′} with F_s|spt X proper. Put Z := [[0,1]]×X (normal: M(Z) ≤ M(X), and by 3.4, M(∂Z) ≤ 2M(X) + M(∂X)).

4.1 (Push-forward of slices.) G_#({s}×X) = (F_s)_#X. Let η be compatible with (G, ω) near the closed set {s} × spt X (2.1; G is proper there), η = G^#ω on the open Ñ. Then η_s = j_s^#η and, by the chain rule D(G∘j_s)(x) = DG(s, x)∘ι, j_s^#(G^#ω) = (F_s)^#ω; so η_s is compatible with (F_s, ω) near spt X (on j_s⁻¹(Ñ) ⊇ spt X), and G_#({s}×X)(ω) = ({s}×X)(η) = X(η_s) = (F_s)_#X(ω).
4.2 (Homotopy formula; Simon 2.25.) For k = j + 1: (F_1)_#X − (F_0)_#X = ∂G_#Z + G_#([[0,1]]×∂X); for k = 0: (F_1)_#X − (F_0)_#X = ∂G_#Z. Proof: all supports involved lie in [0,1] × spt X, on which G is proper; by 2.5, 2.2 (linearity) and 3.4, ∂G_#Z = G_#∂Z = G_#({1}×X) − G_#({0}×X) − G_#([[0,1]]×∂X), and 4.1 identifies the first two terms.
4.3 (Affine estimate; Simon 2.27.) Suppose moreover G(t, x) = F_0(x) + t(F_1(x) − F_0(x)) and O ⊇ spt X is an open set with |F_1 − F_0| ≤ s and ‖DF_0‖, ‖DF_1‖ ≤ L on O. Then for every ψ ∈ D^{k+1}(ℝ^{m′}): |G_#Z(ψ)| ≤ c₁(m′, k)·s·L^k·M(X)·‖ψ‖. Proof: G^#ψ(t, x)(e_0, ιv_1,…,ιv_k) = ψ(G(t, x))(F_1(x) − F_0(x), A_t(x)v_1,…,A_t(x)v_k) with A_t := (1 − t)DF_0 + tDF_1, ‖A_t‖ ≤ L on O for t ∈ [0,1]. Choose η̃ = ζ̃·G^#ψ compatible with (G, ψ) near [0,1] × spt X with tsupport ζ̃ ⊆ ℝ × O (2.1 with the open set ℝ × O ⊇ C̃). For t ∈ [0,1]: η̃^{(t)}(x) = 0 if x ∉ O, and otherwise |η̃^{(t)}(x)| ≤ c₁|F_1(x) − F_0(x)|‖A_t(x)‖^k|ψ(G(t, x))| ≤ c₁sL^k‖ψ‖ by (F8). So |G_#Z(ψ)| = |∫_0^1 X(η̃^{(t)}) dt| ≤ M(X)·c₁sL^k‖ψ‖ (F1).
4.4 (Consequence; Simon 2.28.) Under 4.3, for ω ∈ D^k(ℝ^{m′}): |(F_1)_#X(ω) − (F_0)_#X(ω)| ≤ c₁(m′, k)·s·L^k·M(X)·‖dω‖ + c₁(m′, k−1)·s·L^{k−1}·M(∂X)·‖ω‖ (the second term only for k ≥ 1). Indeed by 4.2, (F_1)_#X(ω) − (F_0)_#X(ω) = G_#Z(dω) + G_#([[0,1]]×∂X)(ω), and 4.3 applies to X with the form dω and to ∂X (degree k − 1, finite mass, spt ∂X ⊆ spt X) with the form ω.
PART 5 — PUSH-FORWARD BY LIPSCHITZ MAPS (Simon 2.28–2.29; parent A2(e), I.7).
Let X ∈ D_k(ℝ^m) be normal and G : ℝ^m → ℝ^{m′} globally L-Lipschitz with G|spt X proper. If (G_j) is an admissible approximating sequence (Part 1) with constant L′, then for j large (sup|G_j − G| ≤ 1) G_j|spt X is proper (G_j⁻¹(K) ∩ spt X ⊆ G⁻¹(cthickening 1 K) ∩ spt X, a closed subset of a compact set), so (G_j)_#X is defined (Part 2), and by 2.3(ii) with O = ℝ^m, |(G_j)_#X(ω)| ≤ L′^kM(X)‖ω‖.

5.1 (Existence and independence of the limit; Simon 2.29.) For every admissible approximating sequence (G_j) and every ω ∈ D^k(ℝ^{m′}), lim_j (G_j)_#X(ω) exists, and it is the same for all admissible approximating sequences of G. Proof. For i, j large let G_{ij}(t, x) := G_i(x) + t(G_j(x) − G_i(x)); it is C^∞ and proper on [0,1] × spt X (|G_{ij}(t, x) − G(x)| ≤ 1 there). Apply 4.4 with O = ℝ^m, L = L′, s = sup|G_i − G_j|: |(G_j)_#X(ω) − (G_i)_#X(ω)| ≤ sup|G_i − G_j|·(c₁L′^kM(X)‖dω‖ + c₁′L′^{k−1}M(∂X)‖ω‖) → 0 as i, j → ∞. So the real sequence is Cauchy and converges. If (G′_j) is a second admissible approximating sequence, the interleaved sequence G_1, G′_1, G_2, G′_2, … is admissible (common constant max(L′, L″)), so its limit exists and equals both subsequential limits.
 Definition: G_#X(ω) := lim_j (G_j)_#X(ω) (any admissible approximating sequence; e.g. the mollifications G_{1/j}).
5.2 (Characterization.) By definition and 2.2: for every admissible approximating sequence (G_j) and every choice of η_j compatible with (G_j, ω) near spt X, X(η_j) → G_#X(ω).
5.3 (Current.) ω ↦ G_#X(ω) is linear (limit of linear maps) and |G_#X(ω)| ≤ L′^kM(X)‖ω‖ (take G_j = G_{1/j}, L′ = L), so G_#X ∈ D_k(ℝ^{m′}) by (F6), and (G_{1/j})_#X ⇀ G_#X.
5.4 (Locality.) If G, G′ are globally Lipschitz, proper on spt X, and G = G′ on (spt X)_r for some r > 0, then G_#X = G′_#X. Proof: for σ < r/2, the mollifications satisfy G_σ = G′_σ on the open set (spt X)_{r/2} (1.2(b): B_σ(x) ⊆ (spt X)_r for x ∈ (spt X)_{r/2}); a form compatible with (G_σ, ω) on N is compatible with (G′_σ, ω) on N ∩ (spt X)_{r/2} ⊇ spt X; so (G_σ)_#X = (G′_σ)_#X, and the limits agree.
5.5 (Mass with a local Lipschitz constant; Simon 2.29.) If G is Λ-Lipschitz on (spt X)_r for some r > 0, then M(G_#X) ≤ Λ^kM(X). Proof: for σ < r/4 and x ∈ O := (spt X)_{r/2}, B_{2σ}(x) ⊆ (spt X)_r, so ‖DG_σ(x)‖ ≤ Λ by 1.2(c); by 2.3(ii), M((G_σ)_#X) ≤ Λ^kM(X); and (G_σ)_#X ⇀ G_#X (5.3 with σ = 1/j), so (F4) gives M(G_#X) ≤ Λ^kM(X).
5.6 (Support.) spt G_#X ⊆ closure G(spt X). If tsupport ω misses closure G(spt X), then ρ₀ := dist(tsupport ω, G(spt X)) > 0 (compact versus closed, disjoint); for j with sup|G_j − G| < ρ₀, G_j(spt X) ∩ tsupport ω = ∅, so (G_j)_#X(ω) = 0 as in 2.4, hence G_#X(ω) = 0; conclude as in 2.4.
5.7 (Boundary.) If k = j + 1 then ∂(G_#X) = G_#(∂X) (∂X is normal: M(∂X) < ∞ and ∂∂X = 0; G is proper on spt ∂X ⊆ spt X). Indeed ∂(G_#X)(φ) = G_#X(dφ) = lim_j (G_j)_#X(dφ) = lim_j (G_j)_#(∂X)(φ) = G_#(∂X)(φ) by 2.5.
5.8 (Linearity in X.) If X, X′ are normal, G is proper on spt X ∪ spt X′ and X″ = aX + a′X′ pointwise (X″ is then normal), then G_#X″ = aG_#X + a′G_#X′, by 2.2 and passage to the limit.
5.9 (Integrality; parent I.7.) If moreover X is integer multiplicity, X = τ(M, θ, ξ) with IsRectifiableTriple univ k M θ ξ and θ(M) ⊆ ℕ, then G_#X is integer multiplicity. Proof: apply the premise (S5′) to X, (M, θ, ξ), g := G, Λ := L (G is L-Lipschitz, and G⁻¹(K) ∩ spt X is compact for compact K): there is an integer multiplicity S ∈ D_k(ℝ^{m′}) such that for every sequence of C¹ maps with a common Lipschitz bound converging uniformly to G and every ω, ∫_M θ(x)·nVectorPushforward k (Dg_j(x)) (ξ(x)) (ω(g_j(x))) dH^k(x) → S(ω). Take g_j := G_{1/j} (C^∞ ⊆ C¹, L-Lipschitz, uniformly convergent). By 2.6, (G_{1/j})_#X(ω) equals that integral; by 5.3 it converges to G_#X(ω). Hence G_#X(ω) = S(ω) for all ω, G_#X = S (GeometricCurrentOn.ext), and G_#X is integer multiplicity.

PART 6 — THE OPERATORS P_k, H_k AND THE NINE CLAUSES (parent I.6, I.7, Step 7).
Fix D and put c_k := max{1, c₁(D, k)} (c₁ from (F8)); c_k depends only on (D, k). Fix f : ℝ^D → ℝ^D. Write E_δ = thickening δ E. Data (E, Λ, δ, b) are admissible for X ∈ D_k(ℝ^D) if E is closed, δ > 0, f is Λ-Lipschitz on E_δ, |f(x) − x| ≤ b for x ∈ E, X is normal and spt X ⊆ E. For such data put b₊ := max(b, 0) and b′ := b₊ + (1 + Λ)δ ≥ 0; then |x − f(x)| ≤ b′ on E_δ (if E_δ ≠ ∅, pick y ∈ E with |x − y| < δ; both x, y ∈ E_δ, so |x − f(x)| ≤ |x − y| + |y − f(y)| + |f(y) − f(x)| ≤ (1 + Λ)δ + b). (If E = ∅ then E_δ = ∅, X = 0 and everything below is trivial.) Define the straight-line homotopy from f to the identity, h(t, x) := f(x) + t(x − f(x)) (h(0, ·) = f, h(1, ·) = id). On Ã_E := [−1, 2] × E_δ ⊆ ℝ^{1+D}, h is L_h-Lipschitz with L_h := 3Λ + 2 + b′: h(t,x) − h(t′,x′) = (f(x) − f(x′)) + t[(x − x′) − (f(x) − f(x′))] + (t − t′)(x′ − f(x′)), so |h(t,x) − h(t′,x′)| ≤ (Λ + 2(1 + Λ))|x − x′| + b′|t − t′|.
 Choices: f̂_E := a √D·Λ-Lipschitz extension of f|E_δ to ℝ^D, and ĥ_E := a √D·L_h-Lipschitz extension of h|Ã_E to ℝ^{1+D} (1.1). Properness: on spt X ⊆ E, f̂_E = f and |f(x) − x| ≤ b, so f̂_E⁻¹(K) ∩ spt X ⊆ cthickening b K ∩ spt X is compact; on [0,1] × spt X, ĥ_E = h and |h(t, x) − x| = (1 − t)|f(x) − x| ≤ b, so ĥ_E⁻¹(K) ∩ ([0,1] × spt X) ⊆ [0,1] × (cthickening b K ∩ spt X) is compact.

6.1 (Definition.) If X ∈ D_k(ℝ^D) admits admissible data (E, Λ, δ, b), put P_kX := (f̂_E)_#X and H_kX := (ĥ_E)_#([[0,1]]×X) (Part 5; [[0,1]]×X is normal by 3.2, 3.4, with spt ⊆ [0,1] × spt X by 3.3, so ĥ_E is proper on its support). Otherwise put P_kX := 0, H_kX := 0. (Classical choice of data and extensions.)
6.2 (Independence of the choices; the parent's "independence of σ".) If (E, Λ, δ, b), (E′, Λ′, δ′, b″) are two admissible data for X, with extensions f̂_E, f̂_{E′}, ĥ_E, ĥ_{E′}, then f̂_E = f = f̂_{E′} on E_δ ∩ E′_{δ′} ⊇ (spt X)_{r} with r := min(δ, δ′), so (f̂_E)_#X = (f̂_{E′})_#X by 5.4; and ĥ_E = h = ĥ_{E′} on Ã_E ∩ Ã_{E′} ⊇ ([0,1] × spt X)_{r′} with r′ := min(1, δ, δ′) (a point within r′ of (t₀, x₀) ∈ [0,1] × spt X has t ∈ (−1, 2) and x ∈ (spt X)_{r′}), so (ĥ_E)_#([[0,1]]×X) = (ĥ_{E′})_#([[0,1]]×X) by 5.4 (in ℝ^{1+D}). Hence P_kX, H_kX do not depend on the choices, and for any admissible data they may be computed with f̂_E, ĥ_E. If spt X = ∅ then X = 0 (F2′) and P_kX = H_kX = 0.
Now fix X ∈ D_k(ℝ^D) with admissible data (E, Λ, δ, b) (this is exactly the hypothesis list of the first clause of the Lean statement, by 0.1).
6.3 (Clause (1), mass of P.) f̂_E = f is Λ-Lipschitz on (spt X)_δ ⊆ E_δ, so by 5.5, M(P_kX) ≤ Λ^kM(X) ≤ c_kΛ^kM(X).
6.4 (Clause (2), mass of H; Simon 2.27, parent (13), (14), (16).) If spt X = ∅ both sides vanish. Otherwise b ≥ 0. Let ĥ := ĥ_E and ĥ_σ its mollifications (on ℝ^{1+D}); they form an admissible approximating sequence of ĥ (σ = 1/j), so (ĥ_σ)_#Z ⇀ H_kX with Z := [[0,1]]×X (5.3), and M(H_kX) ≤ liminf_σ M((ĥ_σ)_#Z) (F4). Fix ε₁ ∈ (0, min(1, δ)/4) and σ < ε₁. For t ∈ [0,1] and x ∈ (spt X)_{ε₁}, the ball B_{2σ}((t, x)) lies in (−1, 2) × (spt X)_{3ε₁} ⊆ Ã_E (3ε₁ < δ), where ĥ = h. Since h is affine in t, ĥ_σ(t + τ, x) − ĥ_σ(t, x) = τ∫(x − w_x − f(x − w_x))ϕ_σ(w)dw for small τ, so ∂_tĥ_σ(t, x) = ∫(x − w_x − f(x − w_x))ϕ_σ(w)dw and |∂_tĥ_σ(t, x)| ≤ sup_{x′∈B_σ(x)}|x′ − f(x′)| ≤ b + (1 + Λ)·2ε₁ (each such x′ lies within ε₁ + σ < 2ε₁ of a point y ∈ spt X, where |y − f(y)| ≤ b, and x′, y ∈ E_δ, so |x′ − f(x′)| ≤ |y − f(y)| + (1 + Λ)|x′ − y|). For |t′ − t| < σ the map x′ ↦ h(t′, x′) = (1 − t′)f(x′) + t′x′ is (|1 − t′|Λ + |t′|)-Lipschitz on E_δ, hence x ↦ ĥ_σ(t, x) is (1 + σ)(1 + Λ)-Lipschitz near x and ‖D_xĥ_σ(t, x)‖ ≤ (1 + ε₁)(1 + Λ) (as in 1.2(c)). Let ψ ∈ D^{k+1}(ℝ^D) with ‖ψ‖ ≤ 1 and choose η̃ = ζ̃·ĥ_σ^#ψ compatible with (ĥ_σ, ψ) near [0,1] × spt X with tsupport ζ̃ ⊆ (−ε₁, 1 + ε₁) × (spt X)_{ε₁} (2.1). For t ∈ [0,1], η̃^{(t)}(x) = 0 unless x ∈ (spt X)_{ε₁}, and then, by (F8), |η̃^{(t)}(x)| ≤ |ψ(ĥ_σ(t, x))(∂_tĥ_σ(t, x), D_xĥ_σ(t, x)·)| ≤ c₁(b + 2(1 + Λ)ε₁)(1 + ε₁)^k(1 + Λ)^k. Hence |(ĥ_σ)_#Z(ψ)| = |∫_0^1 X(η̃^{(t)}) dt| ≤ c₁(b + 2(1 + Λ)ε₁)(1 + ε₁)^k(1 + Λ)^kM(X) for all σ < ε₁, so M(H_kX) ≤ c₁(b + 2(1 + Λ)ε₁)(1 + ε₁)^k(1 + Λ)^kM(X). Letting ε₁ ↓ 0: M(H_kX) ≤ c₁·b·(1 + Λ)^k·M(X) ≤ c_k·b·(1 + Λ)^k·M(X).
6.5 (Clause (3), support of P.) By 5.6, spt P_kX ⊆ closure f̂_E(spt X) = closure f(spt X).
6.6 (Clause (4), support of H.) By 5.6 and 3.3, spt H_kX ⊆ closure ĥ_E(spt Z) ⊆ closure h([0,1] × spt X); and |h(t, x) − x| = (1 − t)|f(x) − x| ≤ b for x ∈ spt X ⊆ E, so h([0,1] × spt X) ⊆ cthickening b (spt X), which is closed. (This is the convexity argument of the parent's Step 6.)
6.7 (Clause (5), integrality.) If X is integer multiplicity, P_kX = (f̂_E)_#X is integer multiplicity by 5.9. By 3.5, Z = [[0,1]]×X is integer multiplicity, and it is normal; hence H_kX = (ĥ_E)_#Z is integer multiplicity by 5.9 applied in ℝ^{1+D} → ℝ^D (the premise (S5′) is stated for all P, Q).
6.8 (Clause (6), tangential vanishing; the analytic core of the parent's Step 7.) Let α ∈ I(k, D), z ∈ ℝ^D, ω ∈ D^k(ℝ^D), ε > 0 satisfy: every x ∈ (spt X)_ε with f(x) ∈ (tsupport ω)_ε has f(x)_i = z_i for all i ∉ range α; and ω(y)(e_{α(1)},…,e_{α(k)}) = 0 for all y. Put r := min(ε, δ)/2, N := (spt X)_{r/2} (open, ⊇ spt X) and let σ < min(r/4, ε/(4Λ + 4)). Write F := f̂_E and F_σ for its mollification. Claim: F_σ^#ω = 0 on N. Let x ∈ N. If F_σ(x) ∉ tsupport ω then ω(F_σ(x)) = 0. Otherwise, for y ∈ B_{2σ}(x): y ∈ (spt X)_{r} ⊆ (spt X)_ε ∩ (spt X)_δ, so F(y) = f(y); B_{2σ}(x) ⊆ (spt X)_δ ⊆ E_δ, where f is Λ-Lipschitz, so |F_σ(x) − f(x)| ≤ Λσ (1.2(c)) and |f(y) − F_σ(x)| ≤ 2Λσ + Λσ < ε; thus f(y) ∈ (tsupport ω)_ε and, by hypothesis, f(y)_i = z_i for i ∉ range α. For x′ ∈ B_σ(x) and |w| < σ, x′ − w ∈ B_{2σ}(x), so (F_σ)_i(x′) = ∫ f(x′ − w)_i ϕ_σ(w)dw = z_i (1.2(b)). So for i ∉ range α the coordinate (F_σ)_i is constant on the open ball B_σ(x), D(F_σ)_i(x) = 0, and DF_σ(x) maps ℝ^D into V_α := span{e_{α(1)},…,e_{α(k)}}. An alternating k-form β with β(e_{α(1)},…,e_{α(k)}) = 0 vanishes on V_α^k (expand u_i = Σ_j c_{ij}e_{α(j)} multilinearly: terms with a repeated basis vector vanish and the others are ± β(e_{α(1)},…,e_{α(k)}) = 0, i.e. β(u) = det(c)·β(e_α)). Applying this to β := ω(F_σ(x)) and u_i := DF_σ(x)v_i gives F_σ^#ω(x) = 0. So the zero form is compatible with (F_σ, ω) near spt X, and (F_σ)_#X(ω) = X(0) = 0 for all small σ. By 5.2 (with the admissible approximating sequence F_{σ_j}, σ_j ↓ 0), P_kX(ω) = lim 0 = 0.
6.9 (Clause (7), linearity.) Let X₁ have the same admissible data (E, Λ, δ, b) and X₂(ω) = aX(ω) + a₁X₁(ω) for all ω. Then X₂ is normal (M(X₂) ≤ |a|M(X) + |a₁|M(X₁) by (F1) applied to mass-admissible forms; for k = j + 1, ∂X₂ = a∂X + a₁∂X₁ pointwise, so M(∂X₂) ≤ |a|M(∂X) + |a₁|M(∂X₁) < ∞) and spt X₂ ⊆ spt X ∪ spt X₁ ⊆ E (F3(3)); so (E, Λ, δ, b) is admissible for X₂ as well. Computing all three operators with the same f̂_E and ĥ_E (6.2): P_kX₂ = (f̂_E)_#X₂ = a(f̂_E)_#X + a₁(f̂_E)_#X₁ by 5.8; and [[0,1]]×X₂ = a[[0,1]]×X + a₁[[0,1]]×X₁ (3.2 is linear in X), so H_kX₂ = aH_kX + a₁H_kX₁ by 5.8 in ℝ^{1+D}.
6.10 (Clause (8), boundary.) Let k = j + 1 and X ∈ D_{j+1}(ℝ^D) with admissible data (M(X), M(∂X) < ∞, spt X ⊆ E). Then ∂X ∈ D_j has the same admissible data (M(∂X) < ∞; ∂∂X = 0 has mass 0 when j ≥ 1; spt ∂X ⊆ spt X ⊆ E by (F3)(1)). By 5.7 with G = f̂_E: ∂P_{j+1}X = ∂((f̂_E)_#X) = (f̂_E)_#(∂X) = P_j(∂X).
6.11 (Clause (9), homotopy formula; Simon 2.25 with f at t = 0 and the identity at t = 1, i.e. the parent's corrected (20).) Same X. Let ĥ := ĥ_E and ĥ_σ its mollifications (σ = 1/j), and Z := [[0,1]]×X. For σ ≤ 1, ĥ_σ is C^∞ and proper on [0,1] × spt X (|ĥ_σ − ĥ| ≤ √D L_hσ), so 4.2 applies to G := ĥ_σ: with F_s^σ := ĥ_σ∘j_s,
   (F_1^σ)_#X − (F_0^σ)_#X = ∂(ĥ_σ)_#Z + (ĥ_σ)_#([[0,1]]×∂X).
 Let σ → 0 and evaluate on a fixed ω ∈ D^{j+1}(ℝ^D). (i) (ĥ_σ)_#Z ⇀ ĥ_#Z = H_{j+1}X (5.3), so ∂(ĥ_σ)_#Z(ω) = (ĥ_σ)_#Z(dω) → H_{j+1}X(dω) = ∂H_{j+1}X(ω). (ii) [[0,1]]×∂X is normal with support in [0,1] × spt ∂X ⊆ [0,1] × spt X, and ∂X has the admissible data (E, Λ, δ, b) (6.10), so (ĥ_σ)_#([[0,1]]×∂X)(ω) → ĥ_#([[0,1]]×∂X)(ω) = H_j(∂X)(ω). (iii) F_s^σ is C^∞, √D L_h-Lipschitz and converges uniformly to ĥ∘j_s; hence (F_s^σ)_#X(ω) → (ĥ∘j_s)_#X(ω) (5.1). Now ĥ∘j_1 = h(1, ·) = id on E_δ ⊇ (spt X)_δ, and id_#X = X (the constant sequence id is admissible, and a form compatible with (id, ω) near spt X agrees with ω near spt X, so (F2′) gives id_#X(ω) = X(ω)); by 5.4, (ĥ∘j_1)_#X = X. Similarly ĥ∘j_0 = h(0, ·) = f = f̂_E on (spt X)_δ, so (ĥ∘j_0)_#X = (f̂_E)_#X = P_{j+1}X. Passing to the limit: X(ω) − P_{j+1}X(ω) = ∂H_{j+1}X(ω) + H_j(∂X)(ω) for every ω.
6.12 (Conclusion.) The operators P := (P_k)_k, H := (H_k)_k depend only on f (6.1, 6.2) and the constants c_k only on (D, k); 6.3–6.9 are the seven conjuncts of the first clause of the statement (for every k, closed E, Λ, δ > 0, b, and normal X supported in E with f Λ-Lipschitz on E_δ and |f − id| ≤ b on E), and 6.10–6.11 are the two conjuncts of the second clause (degree j + 1). ∎

## Key steps

1. Standing facts: |Y(ω)| ≤ M(Y)‖ω‖, vanishing off the support, support lemmas, lower semicontinuity of mass, pull-back and interior-product bounds |α∘A| ≤ ‖A‖^k|α|, |α(w,A·)| ≤ c₁|w|‖A‖^k|α|.
2. McShane extension and mollification of Lipschitz maps: smooth, same Lipschitz constant, uniformly close, local (values and constant coordinates on B_σ(x) are inherited).
3. Smooth push-forward g_#X(ω) := X(η) for η compatible with g^#ω near spt X: well defined, linear, a current, M ≤ sup‖Dg‖^k M(X), support in closure g(spt X), ∂g_# = g_#∂, and the rectifiable formula ∫_M θ⟨ω(g), Dg_#ξ⟩ dH^k (H^k(M ∖ spt X) = 0).
4. Products [[0,1]]×X(φ) := ∫_0^1 X(φ^{(t)})dt and slices {s}×X: currents, supports, ∂([[0,1]]×X) = {1}×X − {0}×X − [[0,1]]×∂X from (dφ)^{(t)} = ∂_tφ_t − d(φ^{(t)}), and integer multiplicity of [[0,1]]×X (3.2(2)) via the product formula H^{k+1}⌞((0,1)×M) = L¹ × H^k⌞M (reused multiplicity area formula with weights 1/multiplicity on bounded pieces, null cylinders) and blow-ups.
5. Smooth homotopy formula (F_1)_#X − (F_0)_#X = ∂G_#([[0,1]]×X) + G_#([[0,1]]×∂X) and the affine estimate |G_#([[0,1]]×X)(ψ)| ≤ c₁ s L^k M(X)‖ψ‖ (2.25, 2.27).
6. Lipschitz push-forward of normal currents as the limit of smooth push-forwards along any admissible approximating sequence (Cauchy by 2.28), with locality, local-Lipschitz mass bound, support, boundary, linearity, and integrality through (S5′).
7. Operators: P_kX := (f̂)_#X and H_kX := (ĥ)_#([[0,1]]×X) for Lipschitz extensions of f near E and of h(t,x) = f(x) + t(x − f(x)) near [−1,2] × E, independent of the choices by locality.
8. Verification: masses (lower semicontinuity; derivative bounds of mollified ĥ), supports, integrality, tangential vanishing (mollified f has constant normal coordinates near spt X, so the pulled-back form vanishes there), linearity, boundary commutation, and the homotopy formula X − P X = ∂H X + H ∂X by passing to the limit in 2.25.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cat -n GMT/Ch06/Contract.lean (IsRectifiableTriple, tauAction, IsIntegerMultiplicity, IsMeasureRepresentation, IsRestriction, IsSlice, IsLipschitzPushforward, latticeFace, SlicingTheorem, LipschitzPushforwardIntegerMultiplicity, DeformationTheorem)`
- `grep -n "^structure\|^def \|^instance\|^theorem" .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,FormsDuality,AffineCurrentPushforward}.lean (GeometricCurrentOn has only Zero/ext, no Add; massOn = sSup over covectorEuclideanNorm ≤ 1; support = U \ zeroRegion; nVectorPushforward n L w = w.comp (covectorPullback n L); only affine push-forwards exist)`
- `grep -n "def HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable" -A14 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n "theorem extDeriv_pullback|theorem extDerivWithin_pullback" local-references/.../mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (lines 239, 259)`
- `lake env lean Test1/Test3/Test4.lean: #check HasCompactSupport.contDiff_convolution_left, LipschitzOnWith.extend_real, norm_fderiv_le_of_lipschitz, extDeriv_pullback, LocallyFinite.isClosed_iUnion, IsCompact.exists_thickening_subset_open, ENNReal.tendsto_sum_nat_add, exists_contDiff_tsupport_subset, mul_meas_ge_le_lintegral, lintegral_eq_zero_iff, Real.volume_Ioo, norm_iteratedFDeriv_zero (all available); ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, exists_smooth_tsupport_subset (not in the import closure)`
- `sed -n 330,560p and 1640,1900p book/chapter-06.txt (Simon 2.17-2.33 and the printed proof of 5.1, displays (1)-(33))`
- `python3 over dag.json (544 nodes): statuses, lean_names, depends_on, statements of the deformation subtree and of push-forward/product/homotopy/cutoff/area-formula nodes in other branches`
- `python3 over nodes/<id>/parent-child-handoff.json and isolated-comparator-result.json for the seven reused declarations (status accepted, candidate commit, comparator passed, byte-identical lean_statement)`
- `grep over the DAG node summary and rg over project + simongmt sources for the four new names deformation_pushforward_homotopy, deformation_telescope_limit, deformation_good_radius, deformation_skeleton_isClosed (no match)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on all 11 lean_statements (all valid)`
- `lake env lean /tmp/onto_skel/lean/AllStmts2.lean: all 11 statements as `theorem _root_.HumanizeNodeComparator.target_<key> : (stmt) := by sorry` in the replayed contract scope (only sorry warnings)`
- `lake env lean /tmp/onto_skel/lean/Check2.lean: `hA (hS5full hLp)` with the sibling deformation_im_pushforward_limit statement, HEq normality discharge at degree m+1, degree m+1+1 = m+2 (no errors)`
- `Independent adversarial subagent review of all child statements, natural proofs and the assembly (two rounds; final: no BLOCKER/MAJOR)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-simple-nvector-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-2809c506b6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-fiber-sum-glue-a1/parent-child-handoff.json`
- `/tmp/onto_skel/lean/AllStmts2.lean`
- `/tmp/onto_skel/lean/Check2.lean`

The pinned contract and SimonGMT provide currents, boundary, mass, support, restrictions and only affine push-forwards. There are no products with [[(0,1)]], no smooth or Lipschitz push-forward of normal currents and no homotopy formula, and the in-flight DAG nodes for these (iwl_cr_interval_product_im, iwl_smooth_pushforward) are unaccepted and integer-multiplicity-only. So the parent's Part I becomes the new child deformation_pushforward_homotopy. Its premise is byte-compatible with the sibling deformation_im_pushforward_limit after LipschitzPushforwardIntegerMultiplicity (checked in Lean). Mathlib supplies the analytic tools it uses: convolution smoothness, McShane extension, extDeriv_pullback, local finiteness, Markov's inequality. Seven accepted declarations are reused by name with byte-identical types: cmb_abs_apply_le_of_massOn_le, isoperimetric_apply_eq_zero_of_disjoint_support, iwl_cr_support_lemmas, lpf_rectifiable_support_null, lpf_simple_nvector_algebra, lpf_raf_local_lipschitz_area and lpf_raf_fiber_sum_glue; their dependencies are mirrored. The four new names are globally unique. All 11 statements pass lexical validation and elaborate in the comparator scope, and an adversarial review found no remaining blocker.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
