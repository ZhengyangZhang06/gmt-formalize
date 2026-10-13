<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1 -->

## Theorem `Submission.dph_interval_product`

Notation: for s ∈ ℝ and x ∈ ℝ^m, cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1}; ι(v) := cons(0, v); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; for y ∈ ℝ^{m+1}, t(y) := EuclideanSpace.equiv (Fin (m+1)) ℝ y 0 and tl(y) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ y)); cyl(A) := {y : t(y) ∈ [0,1], tl(y) ∈ A}. D_q(ℝ^p) := GeometricCurrentOn univ q, D^q(ℝ^p) := TestFormOn univ q, M = mass, spt = support, ∂ = boundary. For X ∈ D_k(ℝ^m) and Z ∈ D_{k+1}(ℝ^{m+1}), ProdChar(X, Z) means: for every η ∈ D^{k+1}(ℝ^{m+1}) and every φ : ℝ → D^k(ℝ^m) with φ(s)(x)(v_1, …, v_k) = η(cons(s, x))(e₀, ι(v_1), …, ι(v_k)) for all s ∈ [0,1], x ∈ ℝ^m, v ∈ (ℝ^m)^k (Fin.cons e₀ (ι ∘ v)), one has Z(η) = ∫_0^1 X(φ(s)) ds (interval integral). (I) For all m, k ∈ ℕ and X ∈ D_k(ℝ^m) with M(X) < ∞ there is Z ∈ D_{k+1}(ℝ^{m+1}) such that: ProdChar(X, Z); every Z′ ∈ D_{k+1}(ℝ^{m+1}) with ProdChar(X, Z′) equals Z; M(Z) ≤ M(X); spt Z ⊆ cyl(spt X); for every η and φ as in ProdChar the map s ↦ X(φ(s)) is continuous on [0,1]; and, if for every j ∈ ℕ and Y ∈ D_{j+1}(ℝ^m) with k = j + 1 and HEq Y X one has M(∂Y) < ∞, then M(∂Z) < ∞. (II) For all m, every X ∈ D_0(ℝ^m) with M(X) < ∞, every Z ∈ D_{0+1}(ℝ^{m+1}) with ProdChar(X, Z), every ψ ∈ D^0(ℝ^{m+1}) and all ψ₀, ψ₁ ∈ D^0(ℝ^m) with ψ_i(x)(v) = ψ(cons(i, x))(ι ∘ v) for all x, v (i = 0, 1): ∂Z(ψ) = X(ψ₁) − X(ψ₀). (III) For all m, j, every X ∈ D_{j+1}(ℝ^m) with M(X) < ∞, every Z ∈ D_{j+1+1}(ℝ^{m+1}) with ProdChar(X, Z), every ψ ∈ D^{j+1}(ℝ^{m+1}), all ψ₀, ψ₁ ∈ D^{j+1}(ℝ^m) with ψ_i(x)(v) = ψ(cons(i, x))(ι(v_1), …, ι(v_{j+1})) for all x, v (i = 0, 1), and every φ : ℝ → D^j(ℝ^m) with φ(s)(x)(v) = ψ(cons(s, x))(e₀, ι(v_1), …, ι(v_j)) for s ∈ [0,1]: ∂Z(ψ) = X(ψ₁) − X(ψ₀) − ∫_0^1 ∂X(φ(s)) ds.

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4586

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/755, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3624

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5642, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5655, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5679, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5688, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5690, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5698, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5709, https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/755, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3624

## Lean problem

Declaration: `Submission.dph_interval_product`

```lean
(∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) ∧ (∀ Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X (φ s)) → Z' = Z) ∧ Z.mass ≤ X.mass ∧ Z.support ⊆ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ∧ (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → ContinuousOn (fun s => X (φ s)) (Icc (0 : ℝ) 1)) ∧ ((∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → Z.boundary.mass < ∞)) ∧ (∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0) (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) 0), (∀ (x : Eucl m) (v : Fin 0 → Eucl m), (ψ₀ : DifferentialForm (Eucl m) 0) x v = (ψ : DifferentialForm (Eucl (m + 1)) 0) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → (∀ (x : Eucl m) (v : Fin 0 → Eucl m), (ψ₁ : DifferentialForm (Eucl m) 0) x v = (ψ : DifferentialForm (Eucl (m + 1)) 0) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z.boundary ψ = X ψ₁ - X ψ₀) ∧ (∀ (m j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (ψ₀ : DifferentialForm (Eucl m) (j + 1)) x v = (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (ψ₁ : DifferentialForm (Eucl m) (j + 1)) x v = (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z.boundary ψ = X ψ₁ - X ψ₀ - ∫ s in (0 : ℝ)..1, X.boundary (φ s))
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

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part 3, items 3.1–3.4 of the supplied proof of deformation_pushforward_homotopy (Simon Ch. 6, 2.17–2.22: slice forms, the product current [[0,1]]×X(φ) := ∫_0^1 X(φ^{(t)})dt, its mass and support, and the boundary formula ∂([[0,1]]×X) = {1}×X − {0}×X − [[0,1]]×∂X from (dψ)^{(t)} = ∂_tψ_t − d(ψ^{(t)})), together with the normality estimate M(∂Z) ≤ 2M(X) + M(∂X) of its Part 4. The coordinates are those of the frozen statement of iwl_cr_interval_product_im: the time coordinate is the 0-th coordinate.

Notation. ℝ^p = Eucl p, e_i = EuclideanSpace.single i 1. For s ∈ ℝ, x ∈ ℝ^m: cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1}; ι(v) := cons(0, v) (a linear isometry, ι(e_i) = e_{i.succ}); e₀ := EuclideanSpace.single 0 1 = cons(1, 0); j_s(x) := cons(s, x) = s·e₀ + ι(x) (affine, derivative ι, |j_s(x) − j_s(x′)| = |x − x′|). For y ∈ ℝ^{m+1}: t(y) := EuclideanSpace.equiv (Fin (m+1)) ℝ y 0 and tl(y) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ y)), so y = cons(t(y), tl(y)), t(cons(s,x)) = s, tl(cons(s,x)) = x, and |y|² = t(y)² + |tl(y)|². cyl(A) := {y : t(y) ∈ [0,1], tl(y) ∈ A}. For a q-covector γ, |γ| := covectorEuclideanNorm γ = (Σ_{I strictly increasing} γ(e_{I_1},…,e_{I_q})²)^{1/2}; ‖ω‖ := sup_y |ω(y)| for a form ω (finite for continuous compactly supported ω). D_q(ℝ^p) := GeometricCurrentOn univ q, D^q(ℝ^p) := TestFormOn univ q. M := mass, spt := support.
 Slice notions. For η ∈ D^{k+1}(ℝ^{m+1}), a family φ : ℝ → D^k(ℝ^m) is a dt-slice family of η on [0,1] if φ_s(x)(v) = η(cons(s,x))(e₀, ιv_1, …, ιv_k) for s ∈ [0,1], x, v (exactly the hypothesis of the characterization ProdChar(X, Z): "Z(η) = ∫_0^1 X(φ_s) ds for every η and every dt-slice family φ of η on [0,1]"). For ψ ∈ D^q(ℝ^{m+1}) and s ∈ ℝ, the horizontal slice ψ_s is the q-form ψ_s(x)(v) := ψ(cons(s,x))(ιv_1, …, ιv_q) (= j_s^#ψ).
 Reused facts: (R1) mass_bound (cmb_abs_apply_le_of_massOn_le): 0 ≤ B, M_W(T) ≤ ofReal B, tsupport ω ⊆ W, |ω(x)| ≤ C for all x ⇒ |T(ω)| ≤ B·C; with W = univ and B = M(T).toReal: |T(ω)| ≤ M(T).toReal·C whenever M(T) < ∞. (R2) vanish_off_support (isoperimetric_apply_eq_zero_of_disjoint_support): tsupport ω ∩ spt T = ∅ ⇒ T(ω) = 0. (R3) compatible_form (iwl_sp_exists_compatible_testForm). (R4) slice_forms (iwl_cr_ci_slice_testForm): every η ∈ D^{k+1}(ℝ^{m+1}) has a dt-slice family φ^η defined for all s ∈ ℝ, with (s, x) ↦ φ^η_s(x) continuous.

1. (Coefficient bounds.) (C1) For a (k+1)-covector γ on ℝ^{m+1} let γ′(v) := γ(e₀, ιv_1, …, ιv_k). For strictly increasing I : Fin k → Fin m, γ′(e_I) = γ(e_0, e_{I_1.succ}, …, e_{I_k.succ}) is the coefficient of γ at the strictly increasing tuple Fin.cons 0 (succ ∘ I); this assignment is injective, so Σ_I γ′(e_I)² ≤ Σ_J γ(e_J)², i.e. |γ′| ≤ |γ|. (C2) Likewise for a q-covector γ on ℝ^{m+1}, γ″(v) := γ(ιv_1, …, ιv_q) satisfies |γ″| ≤ |γ| (I ↦ succ ∘ I is injective into strictly increasing tuples). Both γ ↦ γ′, γ ↦ γ″ are linear, so |γ′ − δ′| ≤ |γ − δ| and |γ″ − δ″| ≤ |γ − δ|. (C3) For any q-covector γ on ℝ^p, |γ| ≤ √(p^q)·‖γ‖ (operator norm): each coefficient satisfies |γ(e_I)| ≤ ‖γ‖Π|e_{I_i}| = ‖γ‖ and there are at most p^q tuples.

2. (Horizontal slices are test forms.) Let ψ ∈ D^q(ℝ^{m+1}) and s ∈ ℝ. The map j_s is C^∞ and proper (j_s⁻¹(K) is closed and bounded for compact K, since j_s is an isometric embedding). Apply (R3) with U = V = univ, A = univ, f = j_s: it yields η ∈ D^q(ℝ^m) with η(x) = ψ(j_s(x)).compContinuousLinearMap(Dj_s(x)) for all x (N ⊇ univ); since j_s(x) = s·e₀ + ι(x) is affine, fderiv ℝ j_s x = ι, so η = ψ_s. Also tsupport ψ_s ⊆ tl(tsupport ψ) =: K(ψ), a compact set independent of s; similarly tsupport φ^η_s ⊆ K(η) for every s.

3. (Continuity in s.) Let M(X) < ∞, η ∈ D^{k+1}(ℝ^{m+1}) and φ a dt-slice family of η on [0,1]. For s, s′ ∈ [0,1] and every x, by (C1) |φ_s(x) − φ_{s′}(x)| ≤ |η(cons(s,x)) − η(cons(s′,x))|. As η is continuous with compact support it is uniformly continuous, and |cons(s,x) − cons(s′,x)| = |s − s′|; with (C3) the right side tends to 0 uniformly in x as s′ → s. By (R1), |X(φ_s) − X(φ_{s′})| = |X(φ_s − φ_{s′})| ≤ M(X).toReal·sup_x|φ_s(x) − φ_{s′}(x)| → 0. Hence s ↦ X(φ_s) is continuous on [0,1]; this is conjunct (e) of part (I). Moreover |X(φ_s)| ≤ M(X).toReal·‖η‖ for s ∈ [0,1] by (C1) and (R1). The same argument applies to horizontal slices (with (C2)). In particular it applies to the family s ↦ ∂_sψ_s of step 7, which consists of the horizontal slices of the test form ψ′ = Dψ(·)(e₀).

4. (Current criterion.) (F5) If ω_j → 0 in the sense TestFormOnConverges (all supports in one compact K, iteratedFDeriv ℝ q ω_j → 0 uniformly on K for every q), then ‖ω_j‖ → 0: for q = 0, ‖iteratedFDeriv ℝ 0 ω_j x‖ = ‖ω_j x‖ (norm_iteratedFDeriv_zero), ω_j = 0 off K, and |ω_j(x)| ≤ √(p^k)‖ω_j(x)‖ by (C3). (F6) Hence if T₀ : D^q(ℝ^p) → ℝ is linear and |T₀(ω)| ≤ B‖ω‖ for all ω (some B ≥ 0), then T₀ is sequentially continuous at 0 and defines T ∈ D_q(ℝ^p) with T(ω) = T₀(ω); and for every ω ∈ massAdmissibleOn univ q univ (|ω(x)| ≤ 1 for all x), T(ω) ≤ B, so M(T) ≤ ofReal B.

5. (Definition; conjuncts (a), (b), (c) of part (I).) Let M(X) < ∞ and B := M(X).toReal. For η ∈ D^{k+1}(ℝ^{m+1}) let φ^η be given by (R4) and put Z₀(η) := ∫_0^1 X(φ^η_s) ds. If φ is any dt-slice family of η on [0,1], then φ_s = φ^η_s (as test forms, Subtype.ext and funext) for s ∈ [0,1], so ∫_0^1 X(φ_s) ds = Z₀(η) (intervalIntegral.integral_congr on uIcc 0 1 = [0,1]). Linearity: aφ^η + bφ^{η′} is a dt-slice family of aη + bη′, and both integrands are continuous on [0,1] (step 3), hence interval integrable, so Z₀(aη + bη′) = ∫_0^1 (aX(φ^η_s) + bX(φ^{η′}_s)) ds = aZ₀(η) + bZ₀(η′). Bound: |Z₀(η)| ≤ B‖η‖ (step 3 and intervalIntegral.norm_integral_le_of_norm_le_const, interval of length 1). By step 4 there is Z ∈ D_{k+1}(ℝ^{m+1}) with Z(η) = Z₀(η) for all η, and M(Z) ≤ ofReal(B) = M(X) (M(X) < ∞): conjunct (c). Conjunct (a), ProdChar(X, Z), is the first sentence of this step. Conjunct (b): if Z′ also satisfies ProdChar(X, Z′), then Z′(η) = ∫_0^1 X(φ^η_s) ds = Z(η) for every η (φ^η is a dt-slice family on [0,1]), so Z′ = Z by GeometricCurrentOn.ext.

6. (Support; conjunct (d).) cyl(spt X) is closed (t, tl continuous; [0,1] and spt X closed). Let y₀ ∉ cyl(spt X); choose ρ > 0 with closedBall(y₀, 2ρ) ∩ cyl(spt X) = ∅ and put W := ball(y₀, ρ) (open, closure compact). Let η ∈ D^{k+1}(ℝ^{m+1}) with tsupport η ⊆ W. For s ∈ [0,1], tsupport φ^η_s ⊆ {x : cons(s,x) ∈ tsupport η} (support of φ^η_s lies in the preimage of support η under the continuous j_s, and the preimage of the closed set tsupport η is closed); if x ∈ spt X then cons(s,x) ∈ cyl(spt X), which is disjoint from tsupport η ⊆ W. So tsupport φ^η_s ∩ spt X = ∅, X(φ^η_s) = 0 by (R2), and Z(η) = 0. Thus Z vanishes on W, W lies in the zero region of Z, and y₀ ∉ spt Z. Hence spt Z ⊆ cyl(spt X).

7. (Calculus identity.) Let ψ ∈ D^q(ℝ^{m+1}) (q = k for the boundary formulas below) and y = cons(s, x). By exteriorDerivative_apply (extDeriv_apply), dψ(y)(u_0, …, u_q) = Σ_{i=0}^{q} (−1)^i Dψ(y)(u_i)(u_0, …, û_i, …, u_q) (i.e. Fin.removeNth). Take u_0 = e₀, u_i = ιv_i (1 ≤ i ≤ q):
 dψ(cons(s,x))(e₀, ιv_1, …, ιv_q) = Dψ(cons(s,x))(e₀)(ιv_1, …, ιv_q) − Σ_{i=1}^{q} (−1)^{i−1} Dψ(cons(s,x))(ιv_i)(e₀, ιv_1, …, ι̂v_i, …, ιv_q).
 The first term is ∂_sψ_s(x)(v), where ∂_sψ_s denotes the horizontal slice at s of the q-form ψ′(y) := Dψ(y)(e₀) (C^∞ with compact support ⊆ tsupport ψ, hence a test form on ℝ^{m+1}; ∂_sψ_s is a test form on ℝ^m by step 2). If q = j + 1 and φ is a dt-slice family of ψ on [0,1] (φ_s(x)(w) = ψ(cons(s,x))(e₀, ιw_1, …, ιw_j)), then for s ∈ [0,1] the chain rule (x ↦ cons(s,x) has derivative ι) gives Dφ_s(x)(v_i)(w) = Dψ(cons(s,x))(ιv_i)(e₀, ιw), so by exteriorDerivative_apply for φ_s the sum equals dφ_s(x)(v_1, …, v_q). Hence, for s ∈ [0,1] and a dt-slice family φ^{dψ} of dψ on [0,1]:
 (∗) φ^{dψ}_s = ∂_sψ_s − dφ_s (q = j + 1), φ^{dψ}_s = ∂_sψ_s (q = 0),
 as test forms on ℝ^m.

8. (Fundamental theorem of calculus.) Let M(X) < ∞ and g(s) := X(ψ_s). For every s and h ≠ 0, (ψ_{s+h} − ψ_s)/h − ∂_sψ_s is the horizontal slice (C2) of the form x ↦ [ψ(cons(s+h,x)) − ψ(cons(s,x))]/h − Dψ(cons(s,x))(e₀) = ∫_0^1 [Dψ(cons(s+τh,x)) − Dψ(cons(s,x))](e₀) dτ, whose operator norm is ≤ sup{‖Dψ(y) − Dψ(y′)‖ : |y − y′| ≤ |h|} → 0 as h → 0 (Dψ is continuous with compact support, hence uniformly continuous); by (C2), (C3) and (R1), |(g(s+h) − g(s))/h − X(∂_sψ_s)| → 0. So g has derivative X(∂_sψ_s) at every s, and s ↦ X(∂_sψ_s) is continuous (step 3 applied to ψ′). By intervalIntegral.integral_eq_sub_of_hasDerivAt, ∫_0^1 X(∂_sψ_s) ds = X(ψ_1) − X(ψ_0). If ψ₀, ψ₁ ∈ D^q(ℝ^m) satisfy the horizontal-slice identities of the statement at s = 0, 1, then ψ₀ = ψ_0 and ψ₁ = ψ_1 as test forms, so this equals X(ψ₁) − X(ψ₀).

9. (Boundary formulas, parts (II) and (III).) Let Z satisfy ProdChar(X, Z) with M(X) < ∞ (Z need not be the current of step 5). By GeometricCurrentOn.boundary_apply, ∂Z(ψ) = Z(exteriorDerivativeTestOn univ q ψ), whose underlying form is dψ. Let φ^{dψ} be a dt-slice family of dψ (R4). By ProdChar, ∂Z(ψ) = ∫_0^1 X(φ^{dψ}_s) ds. For q = 0, (∗) and step 8 give ∂Z(ψ) = ∫_0^1 X(∂_sψ_s) ds = X(ψ₁) − X(ψ₀): part (II). For q = j + 1 and a given dt-slice family φ of ψ on [0,1], (∗) and linearity of X give X(φ^{dψ}_s) = X(∂_sψ_s) − X(dφ_s) = X(∂_sψ_s) − ∂X(φ_s) for s ∈ [0,1] (boundary_apply). Both s ↦ X(∂_sψ_s) and s ↦ X(dφ_s) are continuous on [0,1]. The first is continuous by step 3 for the horizontal slices of ψ′. For the second, (∗) gives X(dφ_s) = X(∂_sψ_s) − X(φ^{dψ}_s) for s ∈ [0,1], and s ↦ X(φ^{dψ}_s) is continuous on [0,1] by step 3 applied to the dt-slice family φ^{dψ} of dψ. So the integral splits (intervalIntegral.integral_sub) and step 8 gives ∂Z(ψ) = X(ψ₁) − X(ψ₀) − ∫_0^1 ∂X(φ_s) ds: part (III).

10. (Normality; conjunct (f) of part (I).) Let Z be the current of step 5 and assume the HEq-normality hypothesis. Case k = 0: for ψ ∈ massAdmissibleOn univ 0 univ, take ψ₀, ψ₁ from step 2 (|ψ_i(x)| ≤ |ψ(cons(i,x))| ≤ 1 by (C2)); part (II) and (R1) give ∂Z(ψ) ≤ 2B, so M(∂Z) ≤ ofReal(2B) < ∞. Case k = j + 1: the hypothesis with Y := X (HEq.rfl) gives M(∂X) < ∞; put B′ := M(∂X).toReal. For ψ ∈ massAdmissibleOn univ (j+1) univ take ψ₀, ψ₁ (step 2) and a dt-slice family φ of ψ (R4), with |φ_s(x)| ≤ 1 (C1); part (III), (R1) for X and for ∂X give |∂Z(ψ)| ≤ B + B + ∫_0^1 B′ ds = 2B + B′, so M(∂Z) ≤ ofReal(2B + B′) < ∞. ∎

## Key steps

1. Coefficient bounds: dt-slices and horizontal slices of a covector have Euclidean norm ≤ that of the covector; horizontal slices are test forms (compatible_form with j_s), dt-slices come from slice_forms.
2. s ↦ X(φ_s) is continuous on [0,1] by uniform continuity of η and |X(ω)| ≤ M(X)‖ω‖ (mass_bound).
3. Z(η) := ∫_0^1 X(φ^η_s)ds is linear and bounded by M(X)‖η‖, hence a current (test-form convergence forces sup norms to 0) with M(Z) ≤ M(X); ProdChar holds for every slice family, which also gives uniqueness.
4. spt Z ⊆ cyl(spt X): a form supported near a point off the closed cylinder has slices supported off spt X (vanish_off_support).
5. (dψ)^{(s)} = ∂_sψ_s − dφ_s from extDeriv_apply and the chain rule; s ↦ X(ψ_s) has derivative X(∂_sψ_s), so ∫_0^1 X(∂_sψ_s) = X(ψ_1) − X(ψ_0); ProdChar for dψ gives the boundary formulas.
6. Normality: the boundary formula and mass_bound give M(∂Z) ≤ 2M(X) + M(∂X).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,364p GMT/Ch06/Contract.lean; diff GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical): IsRectifiableTriple, tauAction, IsIntegerMultiplicity, IsLipschitzPushforward, scope namespace GMT.Ch06 with its opens`
- `grep -n '^structure|^def|^abbrev|^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormsDuality,Product,GeometricPointProduct,ParametricCurrentContinuity,AffineCurrentPushforward}.lean: GeometricCurrentOn (sequential continuity at 0), TestFormOnConverges, boundary = T ∘ exteriorDerivativeTestOn, massOn = sSup over covectorEuclideanNorm ≤ 1, support = U \ zeroRegion, covectorPullback = compContinuousLinearMapCLM, nVectorPushforward n L w = w.comp (covectorPullback n L), SimonMultiIndex = Fin n ↪o Fin p. Only point products {p}×T on E × F and affine push-forwards exist; there are no products with [[0,1]] in Eucl (m+1), no Lipschitz push-forward of normal currents and no homotopy formula`
- `grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (lines 34, 330, 96)`
- `sed -n 180,275p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, extDeriv_pullback)`
- `grep for the library inputs cited in the child proofs: weighted_area_formula_lipschitz_injOn, areaRegularSet, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero (simongmt Chapter02/AreaLipschitz.lean:101,31,34,59); measurable_areaJacobianAt (AreaApproximation.lean:44); exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255); MeasurableSet.image_of_continuousOn_injOn (Constructions/Polish/Basic.lean:821); LinearMap.normDet_sq_eq_det_gram (InnerProductSpace/NormDet.lean:303); LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308); HasCompactSupport.contDiff_convolution_left (Calculus/ContDiff/Convolution.lean:427); exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45); norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939); intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148). All found`
- `python3 over dag.json (645 nodes): statuses, lean_names, depends_on and candidate commits of the deformation subtree and of all push-forward/product/homotopy/cutoff/mollifier/slice/hausdorff nodes. Also the isolated-comparator-result.json of the five reused nodes (passed) and the accepted status of every declaration that the child proofs name as reusable later`
- `python3: byte comparison of the hausdorff_product proof, key steps, lean_statement, title and statement with nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json (identical)`
- `git show --stat 0bfba9891418f887822d6878214d8c1c46326aaa; git show 0bfba989:GMT/Ch06/Submission.lean | grep iwl_cr_hp_ (the accepted Lean proof of the identical statement and its four sub-lemmas are present)`
- `rg 'dph_' over GMT/, the local reference project snapshot and simongmt; python3 over dag.json lean_names; git grep 'dph_' over the 1581 distinct commits of all 3680 local refs (no match)`
- `read /runtime/flows/*/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, child activation by Lean name, accepted reused children without handoff) and store.py (Store.update refreshes the shared DAG). Attempt 1's name check ran on a DAG view taken when its attempt started, before the hausdorff node was accepted`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all 12 child statements and the parent statement (all valid); verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) for the exact child-comparator scope`
- `lake env lean /tmp/dph2/lean/AllStmts.lean: the 12 child statements and the parent statement, each as `theorem _root_.HumanizeNodeComparator.target_<key> : (stmt) := by sorry` after the replayed scope (EXIT 0, 13 sorry warnings, no errors)`
- `lake env lean /tmp/dph2/lean/IfaceCheck.lean: attempt-1 interface check whose hypotheses are byte-identical to the current lipschitz_pushforward and smooth_homotopy statements (clause (8), tail/cons, (E1) and (Aff) instantiations); EXIT 0, no errors`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dph2/lean/AllStmts.lean`
- `/tmp/dph2/lean/IfaceCheck.lean`

The pinned project and SimonGMT have no push-forward of normal currents, no products with [[0,1]] in Eucl (m+1) and no homotopy formula (only point products on E × F and affine push-forwards), so Parts 1–5 of the supplied proof are new obligations. Five comparator-accepted declarations with no sibling prerequisites cover facts that the supplied proof uses as black boxes, and they are reused by name with byte-identical types: cmb_abs_apply_le_of_massOn_le (F1), isoperimetric_apply_eq_zero_of_disjoint_support (F2), iwl_sp_exists_compatible_testForm (2.1), iwl_cr_ci_slice_testForm (3.1 slices) and iwl_sp_rectifiable_support_null (F9, same type as lpf_rectifiable_support_null). The product formula 3.5(b) becomes the fresh child dph_hausdorff_product_formula, as attempt 1's correction requires; its type is identical to the accepted iwl_cr_hausdorff_product_formula, its proof is that node's accepted proof verbatim, and its accepted Lean code and four accepted sub-declarations can be reused. iwl_cr_interval_product_im (unaccepted) and iwl_smooth_pushforward (integer multiplicity only) are not reused. Every library lemma cited in the child proofs exists in the pinned snapshot. All 12 child statements and the parent elaborate in the exact comparator scope. The seven new names are globally unique, and the Lean interface check of the parent's operator plumbing recompiles against the current statements.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
