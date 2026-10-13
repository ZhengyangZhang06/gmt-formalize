<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1 -->

## Theorem `Submission.dph_sh_affine_estimate`

(Aff) For all m, m′, k ∈ ℕ there is c ≥ 0 such that for all X ∈ D_k(ℝ^m), Z ∈ D_{k+1}(ℝ^{m+1}), C^∞ maps F₀, F₁ : ℝ^m → ℝ^{m′}, open O ⊆ ℝ^m and s, L, B ∈ ℝ with 0 ≤ s, 0 ≤ L, 0 ≤ B, M(X) ≤ ofReal B, ProdChar(X, Z), spt X ⊆ O, dist(F₁(x), F₀(x)) ≤ s, ‖fderiv ℝ F₀ x‖ ≤ L and ‖fderiv ℝ F₁ x‖ ≤ L for x ∈ O, and F₀⁻¹(K) ∩ spt X compact for every compact K: for every ψ ∈ D^{k+1}(ℝ^{m′}), every C ∈ ℝ with covectorEuclideanNorm (ψ(y)) ≤ C for all y, and every η′ ∈ D^{k+1}(ℝ^{m+1}) compatible near cyl(spt X) with (G, ψ) — i.e. there is an open N ⊇ cyl(spt X) with η′(y) = ψ(G(y)).compContinuousLinearMap (fderiv ℝ G y) for all y ∈ N — where G(y) := F₀(tl(y)) + t(y)·(F₁(tl(y)) − F₀(tl(y))), one has |Z(η′)| ≤ c·s·L^k·B·C. This is verbatim the third conjunct of the selected parent dph_smooth_homotopy. Notation: ℝ^p := Eucl p = EuclideanSpace ℝ (Fin p). For s ∈ ℝ and x ∈ ℝ^m, cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1}; ι(v) := cons(0, v); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; for y ∈ ℝ^{m+1}, t(y) := EuclideanSpace.equiv (Fin (m+1)) ℝ y 0 and tl(y) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ y)); cyl(A) := {y : t(y) ∈ [0,1] ∧ tl(y) ∈ A}. D_q(ℝ^p) := GeometricCurrentOn univ q, D^q(ℝ^p) := TestFormOn univ q, M = mass, spt = support, |γ| := covectorEuclideanNorm γ. For X ∈ D_q(ℝ^m) and Z ∈ D_{q+1}(ℝ^{m+1}), ProdChar(X, Z) means: for every η ∈ D^{q+1}(ℝ^{m+1}) and every φ : ℝ → D^q(ℝ^m) with φ(s)(x)(v) = η(cons(s, x))(Fin.cons e₀ (i ↦ ι(v_i))) for all s ∈ [0,1], x ∈ ℝ^m and v : Fin q → ℝ^m, one has Z(η) = ∫_0^1 X(φ(s)) ds (interval integral).

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5252

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3624, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5452, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5475

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5681, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5689

## Lean problem

Declaration: `Submission.dph_sh_affine_estimate`

```lean
∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C
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

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part 3 (Aff) of the supplied proof of dph_smooth_homotopy (Simon Ch. 6, 2.27: |h_#([[0,1]]×X)(ψ)| ≤ c·s·L^k·M(X)·sup|ψ|). The interior-product bound (F8) is the sibling interior_bound, whose constant is √(k+1), so here c := √(k+1); the supplied value c₁ = √(m′^k)·√m′ is not needed, since the statement only asks for some c ≥ 0 depending on (m, m′, k). Siblings used: mass_bound (cmb_abs_apply_le_of_massOn_le), compatible_form (iwl_sp_exists_compatible_testForm), slice_forms (iwl_cr_ci_slice_testForm), slice_comparison (dph_sh_apply_eq_of_eqOn_nhds_cyl) and interior_bound (dph_sh_covectorEuclideanNorm_interior_le).

Notation: ℝ^p := Eucl p = EuclideanSpace ℝ (Fin p). For s ∈ ℝ and x ∈ ℝ^m, cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1}; ι(v) := cons(0, v); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; for y ∈ ℝ^{m+1}, t(y) := EuclideanSpace.equiv (Fin (m+1)) ℝ y 0 and tl(y) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ y)); cyl(A) := {y : t(y) ∈ [0,1] ∧ tl(y) ∈ A}. D_q(ℝ^p) := GeometricCurrentOn univ q, D^q(ℝ^p) := TestFormOn univ q, M = mass, spt = support, |γ| := covectorEuclideanNorm γ. For X ∈ D_q(ℝ^m) and Z ∈ D_{q+1}(ℝ^{m+1}), ProdChar(X, Z) means: for every η ∈ D^{q+1}(ℝ^{m+1}) and every φ : ℝ → D^q(ℝ^m) with φ(s)(x)(v) = η(cons(s, x))(Fin.cons e₀ (i ↦ ι(v_i))) for all s ∈ [0,1], x ∈ ℝ^m and v : Fin q → ℝ^m, one has Z(η) = ∫_0^1 X(φ(s)) ds (interval integral). As continuous linear maps: t : ℝ^{m+1} →L[ℝ] ℝ is (ContinuousLinearMap.proj 0) ∘ EuclideanSpace.equiv (Fin (m+1)) ℝ; tl : ℝ^{m+1} →L[ℝ] ℝ^m is (EuclideanSpace.equiv (Fin m) ℝ).symm ∘ (ContinuousLinearMap.pi (i ↦ proj i.succ)) ∘ EuclideanSpace.equiv (Fin (m+1)) ℝ, whose middle factor is Fin.tail; and ι : ℝ^m →L[ℝ] ℝ^{m+1} is (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm ∘ ((0 : ℝ^m →L[ℝ] ℝ).finCons (EuclideanSpace.equiv (Fin m) ℝ)), so ι(v) = cons(0, v). The elementary identities t(cons(s, x)) = s, tl(cons(s, x)) = x, cons(t(y), tl(y)) = y, t(e₀) = 1, tl(e₀) = 0, t(ι v) = 0 and tl(ι v) = v follow from ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply, Fin.cons_zero, Fin.tail_cons and Fin.cons_self_tail (and EuclideanSpace.single 0 1 = (1, 0, …, 0)).

Fix m, m′, k and put c := √(k+1) ≥ 0. Let X, Z, F₀, F₁, O, s, L, B, ψ, C, η′ satisfy the hypotheses, let N′ be the open set ⊇ A := cyl(spt X) on which η′ = G^#ψ, and let G be the map of the statement.

1. (G is C^∞; its derivative.) G = F₀∘tl + t·(F₁∘tl − F₀∘tl). Since t and tl are continuous linear and F₀, F₁ are C^∞, G is C^∞ (ContDiff.comp, ContDiff.add, ContDiff.sub, ContDiff.smul). By the chain rule and the product rule for a scalar factor (HasFDerivAt.comp, HasFDerivAt.add, HasFDerivAt.sub, HasFDerivAt.smul), for every y and h:
   DG(y)h = DF₀(tl y)(tl h) + t(y)·(DF₁(tl y)(tl h) − DF₀(tl y)(tl h)) + t(h)·(F₁(tl y) − F₀(tl y)).
   In particular, for y = cons(s₀, x): DG(y)e₀ = F₁(x) − F₀(x), because tl(e₀) = 0 and t(e₀) = 1; and DG(y)(ι v) = DF₀(x)v + s₀·(DF₁(x)v − DF₀(x)v) = (1 − s₀)·DF₀(x)v + s₀·DF₁(x)v, because tl(ι v) = v and t(ι v) = 0.
2. (A is closed.) spt X = univ ∖ zeroRegion(X) is the complement of the open zero region (GeometricCurrentOn.isOpen_zeroRegion), so it is closed. Hence A = t⁻¹([0,1]) ∩ tl⁻¹(spt X) is closed.
3. (G is proper on A; (3a).) Let K ⊆ ℝ^{m′} be compact. K_s := cthickening s K is compact (IsCompact.cthickening; ℝ^{m′} is proper), so F₀⁻¹(K_s) ∩ spt X is compact by hypothesis, and so is its product with [0,1] and the image Q of that product under the continuous map (τ, x) ↦ cons(τ, x). Claim: G⁻¹(K) ∩ A ⊆ Q. Let y ∈ A with G(y) ∈ K, and put τ := t(y) ∈ [0,1] and x := tl(y) ∈ spt X ⊆ O. Then y = cons(τ, x), and dist(F₀(x), G(y)) = ‖τ·(F₁(x) − F₀(x))‖ = τ·dist(F₁(x), F₀(x)) ≤ 1·s, so F₀(x) ∈ K_s (Metric.mem_cthickening_of_dist_le). The set G⁻¹(K) ∩ A is closed (G is continuous, K is closed, step 2), hence compact (IsCompact.of_isClosed_subset).
4. (A compatible test form supported over O; (3b).) U := tl⁻¹(O) is open, and A ⊆ U because spt X ⊆ O. Apply compatible_form with P := m+1, Q := m′, j := k+1, this U, V := univ, A, f := G and ω := ψ; its properness hypothesis is step 3. We obtain η̂ ∈ TestFormOn U (k+1), ζ : ℝ^{m+1} → ℝ and an open N̂ with A ⊆ N̂, 0 ≤ ζ ≤ 1, η̂(y) = ζ(y)·ψ(G(y)).compContinuousLinearMap (DG(y)) for every y, and η̂(y) = ψ(G(y)).compContinuousLinearMap (DG(y)) for y ∈ N̂. Since η̂ is a test form with tsupport η̂ ⊆ U ⊆ univ, the same underlying form defines η̃ ∈ D^{k+1}(ℝ^{m+1}) = TestFormOn univ (k+1). Moreover η̃(y) = 0 whenever y ∉ U, because then y ∉ tsupport η̂ (image_eq_zero_of_notMem_tsupport).
5. (Replacing η′.) η′ and η̃ both equal G^#ψ on the open set N′ ∩ N̂ ⊇ A = cyl(spt X). By slice_comparison (with q := k), Z(η′) = Z(η̃).
6. (Slices.) slice_forms (P := m, m := k) applied to η̃ gives φ̂ : ℝ → D^k(ℝ^m) with φ̂(s₀)(x)(v) = η̃(cons(s₀, x))(Fin.cons e₀ (i ↦ ι(v_i))) for all s₀, x, v. By ProdChar(X, Z), Z(η̃) = ∫_0^1 X(φ̂(s₀)) ds₀.
7. (C ≥ 0.) 0 ≤ |ψ(0)| ≤ C.
8. (Pointwise bound; (3c).) Claim: |φ̂(s₀)(x)| ≤ c·s·L^k·C for every s₀ ∈ [0,1] and x ∈ ℝ^m. Put y := cons(s₀, x), so t(y) = s₀ and tl(y) = x.
   (a) If x ∉ O, then y ∉ U, so η̃(y) = 0 by step 4. Hence φ̂(s₀)(x)(v) = 0 for all v, i.e. φ̂(s₀)(x) = 0, and |0| = 0 ≤ c·s·L^k·C because all factors are ≥ 0 (step 7; covectorEuclideanNorm_zero).
   (b) If x ∈ O, let w := F₁(x) − F₀(x) and T := DG(y)∘ι : ℝ^m →L[ℝ] ℝ^{m′}. By step 1, DG(y)e₀ = w and T(v) = (1 − s₀)·DF₀(x)v + s₀·DF₁(x)v. For every v : Fin k → ℝ^m, step 4 and DG(y) ∘ Fin.cons e₀ (i ↦ ι(v_i)) = Fin.cons (DG(y)e₀) (i ↦ DG(y)(ι(v_i))) (Fin.comp_cons) give
   φ̂(s₀)(x)(v) = ζ(y)·ψ(G(y))(DG(y)e₀, DG(y)ι(v_1), …, DG(y)ι(v_k)) = ζ(y)·ψ(G(y))(Fin.cons w (i ↦ T(v_i))).
   So interior_bound, with γ := ψ(G(y)), a := ζ(y) and β := φ̂(s₀)(x), gives |φ̂(s₀)(x)| ≤ |ζ(y)|·√(k+1)·‖w‖·‖T‖^k·|ψ(G(y))|. Now |ζ(y)| ≤ 1; ‖w‖ = dist(F₁(x), F₀(x)) ≤ s; ‖T‖ ≤ L by ContinuousLinearMap.opNorm_le_bound, because ‖T(v)‖ ≤ (1 − s₀)·‖DF₀(x)‖·‖v‖ + s₀·‖DF₁(x)‖·‖v‖ ≤ ((1 − s₀)L + s₀L)‖v‖ = L‖v‖ (s₀ ∈ [0,1] and x ∈ O), hence ‖T‖^k ≤ L^k (pow_le_pow_left₀); and |ψ(G(y))| ≤ C. All factors are ≥ 0, so |φ̂(s₀)(x)| ≤ 1·√(k+1)·s·L^k·C = c·s·L^k·C.
9. (Mass bound; (3d).) For s₀ ∈ [0,1], mass_bound with P := m, n := k, U = W := univ, T := X, ω := φ̂(s₀), the bound B (0 ≤ B, and X.massOn univ = X.mass ≤ ofReal B by the definition of mass), tsupport φ̂(s₀) ⊆ univ and the pointwise bound of step 8 gives |X(φ̂(s₀))| ≤ B·(c·s·L^k·C).
10. (Integral bound.) Ι(0, 1) = (0, 1] ⊆ [0,1] (Set.uIoc_of_le), so by step 9 the integrand is bounded by B·c·s·L^k·C on Ι(0, 1), and intervalIntegral.norm_integral_le_of_norm_le_const gives |∫_0^1 X(φ̂(s₀)) ds₀| ≤ B·c·s·L^k·C·|1 − 0|. With steps 5 and 6: |Z(η′)| = |Z(η̃)| ≤ c·s·L^k·B·C. Since c = √(k+1) ≥ 0 depends only on k, this proves (Aff). ∎

## Key steps

1. G(y) = F₀(tl y) + t(y)(F₁ − F₀)(tl y) is C^∞ with DG(cons(s₀,x))e₀ = F₁(x) − F₀(x) and DG(cons(s₀,x))(ιv) = (1−s₀)DF₀(x)v + s₀DF₁(x)v.
2. G is proper on A = cyl(spt X): G⁻¹(K) ∩ A is closed and lies in cons([0,1] × (F₀⁻¹(cthickening s K) ∩ spt X)).
3. compatible_form with U = tl⁻¹(O) gives η̂ = ζ·G^#ψ (0 ≤ ζ ≤ 1), supported over O and equal to G^#ψ near A; slice_comparison gives Z(η′) = Z(η̂).
4. The dt-slices of η̂ vanish over ℝ^m ∖ O and over O equal ζ·ψ(G y)(w, T·) with ‖w‖ ≤ s and ‖T‖ ≤ L, so interior_bound gives |φ̂_{s₀}(x)| ≤ √(k+1)·s·L^k·C.
5. mass_bound, ProdChar and the interval-integral bound give |Z(η′)| ≤ √(k+1)·s·L^k·B·C, i.e. c := √(k+1).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -n '^open|^namespace|^end|^noncomputable section|^theorem' GMT/Ch06/Contract.lean; python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch06.main_theorem) -> open MeasureTheory Filter Set Metric / open scoped ENNReal NNReal Topology / namespace GMT.Ch06 / open Poincare.SimonGMT.Chapter06 / open ...Chapter03 (...) / open ...Chapter01 (...) / noncomputable section / end`
- `grep -n '^structure|^def|^abbrev|^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality}.lean: GeometricCurrentOn, TestFormOn (IsTestForm ∧ tsupport ⊆ U), exteriorDerivative = extDeriv, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply (∂T ω = T(dω)), support = U \ zeroRegion, isOpen_zeroRegion, mass = massOn U, covectorEuclideanNorm (strictly increasing tuples), covectorEuclideanNorm_zero/_nonneg`
- `sed -n 180,275p local-references/.../mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (Filter.EventuallyEq.extDeriv_eq, extDeriv_pullback with minSmoothness 𝕜 2 ≤ r); diff with .lake/packages/mathlib copy (identical)`
- `grep Mathlib: ContinuousAlternatingMap.curryLeft/curryLeft_apply_apply (Analysis/Normed/Module/Alternating/Curry.lean), HasFDerivAt.finCons (Analysis/Calculus/FDeriv/Prod.lean:567), intervalIntegral.norm_integral_le_of_norm_le_const (IntervalIntegral/Basic.lean:769), intervalIntegral.integral_congr (:1077), Fin.comp_cons (Data/Fin/Tuple/Basic.lean:260), Fin.consEquiv (:184), EuclideanSpace.real_norm_sq_eq (InnerProductSpace/PiL2.lean:153), Finset.sum_mul_sq_le_sq_mul_sq (Algebra/Order/BigOperators/Ring/Finset.lean:171), Isometry.isClosedEmbedding (Topology/MetricSpace/Isometry.lean:209), Topology.IsClosedEmbedding.isCompact_preimage (Topology/Compactness/Compact.lean:1016)`
- `python3 -I over dag.json (662 nodes): accepted statements matching covectorEuclideanNorm | boundary.support | .support ⊆ | exteriorDerivative | compContinuousLinearMap | EqOn; found iwl_cr_ce_apply_eq_of_eqOn_nhds_support, iwl_cr_support_lemmas, iwl_sp_covectorEuclideanNorm_pullback_le, iwl_sp_pn_sum_sq_tuples_eq_factorial_mul, iwl_cr_ci_cutoff_pullback_testForm, iwl_sp_boundary_apply_eq_of_compatible, iwl_cr_ci_product_support; statuses and lean_statements of dph_* siblings (all decomposing) and of the five prerequisites of the selected node`
- `python3 -I: for the 7 reused nodes compare DAG title/statement/lean_statement with their parent-child-handoff.json subproblem (all equal), read isolated-comparator-result.json (passed, same candidate commit), and git grep -E 'theorem (Submission\.)?<name>' <candidate_commit> -- '*.lean' (each found in GMT/Ch06/Submission.lean)`
- `name collisions: python3 over dag.json lean_names; grep -rn dph_sh GMT/ .lake/packages/simongmt/Poincare and the local reference project snapshot; git grep -q 'dph_sh_' over all 1703 distinct commits of the 3993 local refs (-- '*.lean'): no match`
- `read /runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py (_existing_lean_name_problem, child activation by Lean name, _install_parent_supplied_child_handoff skips accepted checkpoints, _accepted_checkpoint) and store.py (ensure returns existing nodes unchanged)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on all 12 child statements, the selected statement and dph_interval_product (all valid)`
- `lake env lean /tmp/dsh/lean/AllStmts.lean (14 statements after the replayed scope; 14 sorry warnings, no errors)`
- `lake env lean /tmp/dsh/lean/Iface.lean and IfaceAx.lean (selected type proved from the frozen child types + dph_interval_product as hypotheses; no errors or warnings; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/dsh/lean/ChildSC.lean, ChildSLC.lean, ChildED.lean, ChildIB.lean, ChildAFF.lean (each new child proved from exactly its declared sibling dependencies; axioms propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-locality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-71535d6e53/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-locality-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-71535d6e53/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/store.py`
- `/tmp/dsh/lean/AllStmts.lean`
- `/tmp/dsh/lean/Iface.lean`
- `/tmp/dsh/lean/ChildSC.lean`
- `/tmp/dsh/lean/ChildSLC.lean`
- `/tmp/dsh/lean/ChildED.lean`
- `/tmp/dsh/lean/ChildIB.lean`
- `/tmp/dsh/lean/ChildAFF.lean`

The pinned project and SimonGMT contain no interval-product locality, no slice or chain-rule lemma for compatible forms, no local d∘pull-back lemma for currents' test forms and no interior-product covector bound, so the five new children are genuine obligations. Mathlib supplies the analytic inputs: extDeriv_pullback and EventuallyEq.extDeriv_eq (identical in the snapshot and .lake), curryLeft, HasFDerivAt.finCons and the interval-integral lemmas. Seven accepted declarations cover the remaining black boxes and are reused with byte-identical types and passed comparators: cmb_abs_apply_le_of_massOn_le, iwl_sp_exists_compatible_testForm, iwl_cr_ci_slice_testForm, iwl_cr_ce_apply_eq_of_eqOn_nhds_support, iwl_cr_support_lemmas, iwl_sp_covectorEuclideanNorm_pullback_le and iwl_sp_pn_sum_sq_tuples_eq_factorial_mul. All statements elaborate in the exact comparator scope. A Lean interface theorem proves the selected type from the children plus dph_interval_product, and each new child was proved in Lean from its declared dependencies; both checks use standard axioms only. The five new dph_sh_ names are globally unused.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
