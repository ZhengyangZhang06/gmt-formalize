<!-- theorem-id: gmt-ch06/root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1 -->

## Theorem `Submission.lpf_pi_source_charts`

Assume (SNA) [the frozen statement of the uncle lemma lpf_simple_nvector_algebra]: for all P, n and v : Fin n → ℝ^P, ‖simpleNVector v‖² = det(⟨v_i, v_j⟩)_{i,j}; and for all P, n, every real n×n matrix B and τ : Fin n → ℝ^P, simpleNVector(i ↦ Σ_j B_ij τ_j) = det(B) • simpleNVector τ; (CRC) [the frozen statement of lpf_countably_rectifiable_c1_cover]: if M ⊆ ℝ^P is countably n-rectifiable, there are C¹ maps Φ_j : ℝⁿ → ℝ^P and open Ω_j ⊆ ℝⁿ (j ∈ ℕ), each Φ_j Lipschitz on Ω_j and c_j-antilipschitz on Ω_j for some c_j > 0, with Hⁿ(M ∖ ⋃_j Φ_j(Ω_j)) = 0; (CCR) [the frozen statement of lpf_chart_chain_rule]: if U ⊆ ℝ^P is open, IsRectifiableTriple U n M θ ξ, f is locally Lipschitz on U, L satisfies the derivative clause, Ω ⊆ ℝⁿ is open and Φ : ℝⁿ → ℝ^P is C¹ and antilipschitz on Ω, then for Lⁿ-a.e. w ∈ Ω ∩ Φ⁻¹(M): HasWeightedApproximateTangentSpaceAt n M θ (Φ w) (range DΦ(w)), and f∘Φ has Fréchet derivative L(Φ(w))∘DΦ(w) at w; and (LCIP) [the frozen statement of lpf_lipschitz_c1_immersion_pieces]: if Ω ⊆ ℝⁿ is open and u : ℝⁿ → ℝ^Q is locally Lipschitz on Ω, there are C¹ maps G_k : ℝⁿ → ℝ^Q, open O_k ⊆ ℝⁿ with G_k antilipschitz on O_k, and pairwise disjoint Borel E_k ⊆ O_k ∩ Ω (k ∈ ℕ), such that u(w) = G_k(w) and u has Fréchet derivative DG_k(w) at w for every w ∈ E_k, and Lⁿ-a.e. w ∈ Ω at which u has an injective Fréchet derivative lies in ⋃_k E_k. Let P, Q, n ∈ ℕ, U ⊆ ℝ^P open, (M, θ, ξ) with IsRectifiableTriple U n M θ ξ, f : ℝ^P → ℝ^Q locally Lipschitz on U, and L : ℝ^P → L(ℝ^P, ℝ^Q) satisfying the derivative clause. Then there are C¹ maps G_k : ℝⁿ → ℝ^Q and open sets O_k ⊆ ℝⁿ (k ∈ ℕ), each G_k c_k-antilipschitz on O_k for some c_k > 0, with the following property. For Hⁿ⌞M-a.e. x with L(x)_#ξ(x) ≠ 0 there are k ∈ ℕ, w ∈ O_k with G_k(w) = f(x), and an orthonormal σ : Fin n → ℝ^Q with span(range σ) = range DG_k(w), such that L(x)_#ξ(x) = ‖L(x)_#ξ(x)‖ • simpleNVector σ or L(x)_#ξ(x) = −(‖L(x)_#ξ(x)‖ • simpleNVector σ).

Node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/741

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2576

Decomposition children: None

## Lean problem

Declaration: `Submission.lpf_pi_source_charts`

```lean
((∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ) → (∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0) → (∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), HasWeightedApproximateTangentSpaceAt n M θ (Φ w) (LinearMap.range (fderiv ℝ Φ w).toLinearMap) ∧ HasFDerivAt (f ∘ Φ) ((L (Φ w)).comp (fderiv ℝ Φ w)) w) → (∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → ∃ (G : ℕ → Eucl n → Eucl Q) (O E : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ (∀ k, MeasurableSet (E k)) ∧ (∀ k, E k ⊆ O k ∩ Ω) ∧ Pairwise (Function.onFun Disjoint E) ∧ (∀ k, ∀ w ∈ E k, u w = G k w ∧ HasFDerivAt u (fderiv ℝ (G k) w) w) ∧ ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω → (∃ D : Eucl n →L[ℝ] Eucl Q, HasFDerivAt u D w ∧ Function.Injective D) → w ∈ ⋃ k, E k) → ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → ∃ (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧ ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), nVectorPushforward n (L x) (ξ x) ≠ 0 → ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧ (nVectorPushforward n (L x) (ξ x) = ‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ ∨ nVectorPushforward n (L x) (ξ x) = -(‖nVectorPushforward n (L x) (ξ x)‖ • simpleNVector σ))
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

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) (Lean `Eucl P`) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which equals Lebesgue measure Lⁿ = volume on ℝⁿ. An n-covector on E is a continuous alternating n-linear map α : Eⁿ → ℝ with the operator norm. An n-vector is a continuous linear functional on n-covectors (`NVector E n`), also with the operator norm. simpleNVector v is the n-vector α ↦ α(v₁,…,vₙ). For a continuous linear map A, A_#u := nVectorPushforward n A u = u ∘ A^#, where A^#α = α(A·,…,A·). Thus A_# is linear in u, and A_#(simpleNVector v) = simpleNVector(A∘v) (`nVectorPushforward_simple`). `HasWeightedApproximateTangentSpaceAt n M θ x T` is Simon's weighted approximate tangent space (Ch. 3, 1.7). By SimonGMT `HasWeightedApproximateTangentSpaceAt.unique` it is unique when θ(x) ≠ 0, and its first component says dim T = n. The derivative clause for (M, θ, f, L) means: for Hⁿ⌞M-a.e. x, for every subspace T with HasWeightedApproximateTangentSpaceAt n M θ x T and every v ∈ T, the map t ↦ f(x + t v) has derivative L(x)v at t = 0. Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is Step 6 of the parent proof, together with the regular-point analysis of Step 1 and the induced orientation of Step 3. The parent's disjoint pieces A_{j,k} are replaced by an a.e. statement at the source point x: disjointness, and injectivity of f on the pieces, are not needed for this conclusion. Write Ξ(x) := L(x)_#ξ(x).

1. (Source charts.) The field `countablyRectifiable` says M is countably n-rectifiable, so (CRC) gives C¹ maps Φ_j : ℝⁿ → ℝ^P and open Ω_j ⊆ ℝⁿ with Φ_j K_j-Lipschitz on Ω_j, Φ_j c_j-antilipschitz on Ω_j (c_j > 0), and Hⁿ(M ∖ ⋃_j Φ_j(Ω_j)) = 0. Put Ω′_j := Ω_j ∩ Φ_j⁻¹(U), open since Φ_j is continuous and U is open. Φ_j is still K_j-Lipschitz and c_j-antilipschitz on Ω′_j. Since M ⊆ U, M ∩ Φ_j(Ω_j) ⊆ Φ_j(Ω′_j), so Hⁿ(M ∖ ⋃_j Φ_j(Ω′_j)) = 0.
2. (u_j := f∘Φ_j is locally Lipschitz on Ω′_j.) Let w ∈ Ω′_j and x := Φ_j(w) ∈ U. Since U is open, f is Λ-Lipschitz on a neighbourhood N ⊆ U of x. Then Ω′_j ∩ Φ_j⁻¹(N) is a neighbourhood of w within Ω′_j on which u_j is ΛK_j-Lipschitz. (In Lean: unfold `LocallyLipschitzOn`; Ω′_j ∩ Φ_j⁻¹(N) ∈ 𝓝[Ω′_j] w by continuity of Φ_j at w; then use `LipschitzOnWith.comp` and `LipschitzOnWith.mono`. Note that `LocallyLipschitzOn.comp` does not exist at this Mathlib pin.)
3. (Target charts.) For each j apply (LCIP) to u_j on the open set Ω′_j. This gives C¹ maps G_{j,k}, open O_{j,k} with G_{j,k} antilipschitz on O_{j,k}, and Borel E_{j,k} ⊆ O_{j,k} ∩ Ω′_j, such that u_j(w) = G_{j,k}(w) and u_j has Fréchet derivative DG_{j,k}(w) at w for w ∈ E_{j,k}. It also gives an Lⁿ-null set Z^c_j such that every w ∈ Ω′_j ∖ Z^c_j at which u_j has an injective Fréchet derivative lies in ⋃_k E_{j,k}. Re-index by m ∈ ℕ: G_m := G_{a,b} and O_m := O_{a,b} with (a, b) := Nat.unpair m. These G_m, O_m are C¹, open and antilipschitz, as required.
4. (Exceptional sets.) Let R be the set of x ∈ M at which the conclusion of `orients` fails, i.e. there is no orthonormal τ with HasWeightedApproximateTangentSpaceAt n M θ x (span(range τ)) and ξ(x) = ±simpleNVector τ. Since M is null-measurable and `orients` holds Hⁿ⌞M-a.e., Hⁿ(R) = Hⁿ⌞M(R) = 0 (`Measure.restrict_apply₀'`). Let B be the set of x ∈ M with Ξ(x) ≠ 0 at which the required conclusion (existence of m, w, σ) fails. Again by null-measurability of M, the asserted a.e. statement is equivalent to Hⁿ(B) = 0, which we now prove.
5. (Chart preimages of Hⁿ-null sets are Lⁿ-null.) Let Z ⊆ ℝ^P with Hⁿ(Z) = 0. Φ_j is injective on Ω′_j, so it has an inverse Ψ_j on Φ_j(Ω′_j) (`Function.invFunOn`). By antilipschitz-ness Ψ_j is c_j⁻¹-Lipschitz on Φ_j(Ω′_j), and Ω′_j ∩ Φ_j⁻¹(Z) = Ψ_j(Z ∩ Φ_j(Ω′_j)). A K-Lipschitz map multiplies Hⁿ by at most Kⁿ (SimonGMT `Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n : LipschitzOnWith K f A → μHE[n] (f '' A) ≤ K ^ n * μHE[n] A`, available through the imports of GMT.Ch06.Submission; equivalently Mathlib's `LipschitzOnWith.hausdorffMeasure_image_le` transferred to μHE), and Hⁿ = Lⁿ on ℝⁿ (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). Hence Lⁿ(Ω′_j ∩ Φ_j⁻¹(Z)) = 0.
6. Fix j. Let Z^a_j be the set of w ∈ Ω′_j ∩ Φ_j⁻¹(M) at which the conclusion of (CCR) fails. Apply (CCR) to (U, M, θ, ξ, f, L, Φ_j, Ω′_j); its hypotheses are U open, the triple, f locally Lipschitz on U, the derivative clause, Ω′_j open, Φ_j C¹ and antilipschitz on Ω′_j. Since μ(t ∩ s) ≤ μ⌞s(t) (`Measure.le_restrict_apply`), Z^a_j is Lⁿ-null. Let Z^b_j := Ω′_j ∩ Φ_j⁻¹(R), which is Lⁿ-null by Step 5. Claim: Ω′_j ∩ Φ_j⁻¹(B) ⊆ Z^a_j ∪ Z^b_j ∪ Z^c_j. Let w ∈ Ω′_j with x := Φ_j(w) ∈ B, and suppose w ∉ Z^a_j ∪ Z^b_j ∪ Z^c_j.
 (i) x ∈ M ∖ R, so there is an orthonormal τ with HasWeightedApproximateTangentSpaceAt n M θ x (span(range τ)) and ξ(x) = ±simpleNVector τ.
 (ii) w ∉ Z^a_j, so HasWeightedApproximateTangentSpaceAt n M θ x (range DΦ_j(w)) and u_j = f∘Φ_j has Fréchet derivative D := L(x)∘DΦ_j(w) at w. θ(x) > 0 (field `pos`), so uniqueness of weighted approximate tangent spaces (`HasWeightedApproximateTangentSpaceAt.unique`) gives range DΦ_j(w) = span(range τ).
 (iii) Ξ(x) ≠ 0, so the sibling lemma lpf_pi_induced_orientation (applied with (SNA), A := L(x), w := ξ(x)) shows that L(x)∘τ is linearly independent. It also gives an orthonormal σ with span(range σ) = span(range(L(x)∘τ)) and Ξ(x) = ‖Ξ(x)‖ • simpleNVector σ or Ξ(x) = −(‖Ξ(x)‖ • simpleNVector σ).
 (iv) D is injective. DΦ_j(w) : ℝⁿ → ℝ^P has range span(range τ), of dimension n (τ orthonormal), so it is injective by rank–nullity. L(x) is injective on span(range τ), since it maps the basis τ to the linearly independent family L(x)∘τ.
 (v) w ∈ Ω′_j ∖ Z^c_j and u_j has the injective Fréchet derivative D at w, so w ∈ E_{j,k} for some k. Then w ∈ O_{j,k}, G_{j,k}(w) = u_j(w) = f(Φ_j(w)) = f(x), and u_j has Fréchet derivative DG_{j,k}(w) at w. By uniqueness of Fréchet derivatives (`HasFDerivAt.unique`), DG_{j,k}(w) = D. Hence range DG_{j,k}(w) = L(x)(range DΦ_j(w)) = L(x)(span(range τ)) = span(range(L(x)∘τ)) = span(range σ) (`Submodule.map_span`).
 (vi) With m := Nat.pair j k (so G_m = G_{j,k}, O_m = O_{j,k}), (v) and (iii) give the required conclusion at x, contradicting x ∈ B. This proves the claim.
7. By Step 6, Lⁿ(Ω′_j ∩ Φ_j⁻¹(B)) = 0. Since Φ_j is K_j-Lipschitz on Ω′_j, Hⁿ(B ∩ Φ_j(Ω′_j)) ≤ Hⁿ(Φ_j(Ω′_j ∩ Φ_j⁻¹(B))) ≤ K_jⁿ·Lⁿ(Ω′_j ∩ Φ_j⁻¹(B)) = 0 (Step 5's Lipschitz bound). Finally B ⊆ (M ∖ ⋃_j Φ_j(Ω′_j)) ∪ ⋃_j (B ∩ Φ_j(Ω′_j)), so countable subadditivity and Step 1 give Hⁿ(B) = 0. ∎

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_source_charts : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses the declared sibling `Submission.lpf_pi_induced_orientation`. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro hsna CRC CCR LCIP P Q n U M θ ξ f L hU htri hf hderiv
  -- antilipschitz chart preimage of an Hⁿ-null set is Lⁿ-null
  have hnull : ∀ (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c →
      (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ (Z : Set (Eucl P)),
      (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
    intro Φ Ω c hc hanti Z hZ
    classical
    have hinj : InjOn Φ Ω := by
      intro w hw w' hw' h
      have h1 := hanti w hw w' hw'
      rw [h, sub_self, norm_zero] at h1
      have h2 : ‖w - w'‖ ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have := mul_pos hc hcon
        linarith
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
    have hΨlip : LipschitzOnWith (Real.toNNReal c⁻¹) (Function.invFunOn Φ Ω) (Φ '' Ω) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      rw [hinj.leftInvOn_invFunOn hw, hinj.leftInvOn_invFunOn hw', dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hanti w hw w' hw'
    have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω) := by
      rintro w ⟨hw, hwZ⟩
      exact ⟨Φ w, ⟨hwZ, w, hw, rfl⟩, hinj.leftInvOn_invFunOn hw⟩
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    apply measure_mono_null hsub
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl n)) (Function.invFunOn Φ Ω '' (Z ∩ Φ '' Ω))
        ≤ (Real.toNNReal c⁻¹ : ℝ≥0∞) ^ n * μHE[n] (Z ∩ Φ '' Ω) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hΨlip.mono inter_subset_right)
      _ = 0 := by rw [measure_mono_null inter_subset_left hZ, mul_zero]
  -- linear algebra of step 6(iv)-(v)
  have hlinalg : ∀ (D : Eucl n →L[ℝ] Eucl P) (A : Eucl P →L[ℝ] Eucl Q) (τ : Fin n → Eucl P),
      LinearMap.range D.toLinearMap = Submodule.span ℝ (range τ) →
      LinearIndependent ℝ (fun i => A (τ i)) →
      Function.Injective (A.comp D) ∧
        LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
    intro D A τ hD hAτ
    have hrange : LinearMap.range (A.comp D).toLinearMap = Submodule.span ℝ (range (fun i => A (τ i))) := by
      rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, hD, Submodule.map_span, ← range_comp]
      rfl
    refine ⟨?_, hrange⟩
    have hfr : Module.finrank ℝ (LinearMap.range (A.comp D).toLinearMap) = n := by
      rw [hrange, finrank_span_eq_card hAτ, Fintype.card_fin]
    have hker := LinearMap.finrank_range_add_finrank_ker (A.comp D).toLinearMap
    rw [hfr, finrank_euclideanSpace_fin] at hker
    have hker0 : Module.finrank ℝ (LinearMap.ker (A.comp D).toLinearMap) = 0 := by omega
    have : LinearMap.ker (A.comp D).toLinearMap = ⊥ := Submodule.finrank_eq_zero.mp hker0
    exact LinearMap.ker_eq_bot.mp this
  -- covering argument of steps 1, 4, 7
  have hcover_null : ∀ (Φ : ℕ → Eucl n → Eucl P) (Ω Ω' : ℕ → Set (Eucl n)), (∀ j, Ω' j ⊆ Ω j) →
      (∀ j, ∀ w ∈ Ω j, Φ j w ∈ M → w ∈ Ω' j) →
      (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) →
      (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 →
      ∀ (good : Eucl P → Prop),
      (∀ j, (volume : Measure (Eucl n)) {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} = 0) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), good x := by
    intro Φ Ω Ω' hΩ'sub hΩ'cov hΦlip hcover good hbad
    rw [ae_iff, Measure.restrict_apply₀' htri.nullMeasurableSet]
    have hsub : {x | ¬ good x} ∩ M ⊆
        (M \ ⋃ j, Φ j '' Ω j) ∪ ⋃ j, Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} := by
      rintro x ⟨hx, hxM⟩
      by_cases hc : x ∈ ⋃ j, Φ j '' Ω j
      · right
        obtain ⟨j, hj⟩ := mem_iUnion.mp hc
        obtain ⟨w, hw, rfl⟩ := hj
        exact mem_iUnion.mpr ⟨j, w, ⟨hΩ'cov j w hw hxM, hxM, hx⟩, rfl⟩
      · left; exact ⟨hxM, hc⟩
    refine measure_mono_null hsub (measure_union_null hcover (measure_iUnion_null fun j => ?_))
    obtain ⟨K, hK⟩ := hΦlip j
    apply le_antisymm _ zero_le
    calc (μHE[n] : Measure (Eucl P)) (Φ j '' {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] {w | w ∈ Ω' j ∧ Φ j w ∈ M ∧ ¬ good (Φ j w)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hK.mono fun w hw => hΩ'sub j hw.1)
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hbad j, mul_zero]
  have hio := Submission.lpf_pi_induced_orientation hsna
  obtain ⟨Φ, Ω, hΩo, hΦc, hΦlip, hΦanti, hcover⟩ := CRC P n M htri.countablyRectifiable
  have hΩ'o : ∀ j, IsOpen (Ω j ∩ Φ j ⁻¹' U) := fun j =>
    (hΩo j).inter ((hΦc j).continuous.isOpen_preimage U hU)
  have hΦanti' : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j ∩ Φ j ⁻¹' U, ∀ w' ∈ Ω j ∩ Φ j ⁻¹' U,
      c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖ := by
    intro j
    obtain ⟨c, hc, h⟩ := hΦanti j
    exact ⟨c, hc, fun w hw w' hw' => h w hw.1 w' hw'.1⟩
  have hloc : ∀ j, LocallyLipschitzOn (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) := by
    intro j w hw
    obtain ⟨K, hK⟩ := hΦlip j
    obtain ⟨Λ, t, ht, hft⟩ := hf hw.2
    rw [hU.nhdsWithin_eq hw.2] at ht
    refine ⟨Λ * K, (Ω j ∩ Φ j ⁻¹' U) ∩ Φ j ⁻¹' t,
      inter_mem_nhdsWithin _ ((hΦc j).continuous.continuousAt.preimage_mem_nhds ht), ?_⟩
    exact hft.comp (hK.mono fun w hw => hw.1.1) fun w hw => hw.2
  choose G O E hOo hGc hGanti hEm hEsub hEdisj hEeq hEcov using
    fun j => LCIP n Q (Ω j ∩ Φ j ⁻¹' U) (f ∘ Φ j) (hΩ'o j) (hloc j)
  refine ⟨fun m => G m.unpair.1 m.unpair.2, fun m => O m.unpair.1 m.unpair.2,
    fun m => hOo _ _, fun m => hGc _ _, fun m => hGanti _ _, ?_⟩
  have hR : (μHE[n] : Measure (Eucl P)) ({x | ¬ ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
      (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp htri.orients).le) zero_le
  apply hcover_null Φ Ω (fun j => Ω j ∩ Φ j ⁻¹' U)
    (fun j => inter_subset_left) (fun j w hw hwM => ⟨hw, htri.subset hwM⟩) hΦlip hcover
  intro j
  have hCCR := CCR P Q n U M θ ξ f L (Φ j) (Ω j ∩ Φ j ⁻¹' U) hU htri hf hderiv (hΩ'o j) (hΦc j)
    (hΦanti' j)
  have hZa := le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp hCCR).le) zero_le
  obtain ⟨c, hc, hanti⟩ := hΦanti' j
  have hZb := hnull (Φ j) (Ω j ∩ Φ j ⁻¹' U) c hc hanti _ hR
  have hZc := ae_iff.mp (hEcov j)
  refine measure_mono_null ?_ (measure_union_null (measure_union_null hZa hZb) hZc)
  rintro w ⟨hw, hxM, hng⟩
  obtain ⟨hΞ, hngood⟩ := not_imp.mp hng
  by_cases ha : HasWeightedApproximateTangentSpaceAt n M θ (Φ j w)
      (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
      HasFDerivAt (f ∘ Φ j) ((L (Φ j w)).comp (fderiv ℝ (Φ j) w)) w
  swap
  · exact Or.inl (Or.inl ⟨ha, hw, hxM⟩)
  by_cases hb : ∃ τ : Fin n → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt n M θ (Φ j w) (Submodule.span ℝ (range τ)) ∧
      (ξ (Φ j w) = simpleNVector τ ∨ ξ (Φ j w) = -simpleNVector τ)
  swap
  · exact Or.inl (Or.inr ⟨hw, hb, hxM⟩)
  refine Or.inr ?_
  show ¬ _
  intro hc'
  apply hngood
  obtain ⟨τ, hτ, htan, hξ⟩ := hb
  obtain ⟨htanΦ, hfd⟩ := ha
  have huniq : LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap = Submodule.span ℝ (range τ) :=
    htanΦ.unique (htri.pos _ hxM).ne' htan
  obtain ⟨hli, σ, hσ, hσspan, hσeq⟩ := hio P Q n τ (L (Φ j w)) (ξ (Φ j w)) hτ hξ hΞ
  obtain ⟨hinj, hrange⟩ := hlinalg (fderiv ℝ (Φ j) w) (L (Φ j w)) τ huniq hli
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hc' hw ⟨_, hfd, hinj⟩)
  obtain ⟨hueq, hufd⟩ := hEeq j k w hk
  have hDeq : fderiv ℝ (G j k) w = (L (Φ j w)).comp (fderiv ℝ (Φ j) w) := hufd.unique hfd
  refine ⟨Nat.pair j k, w, ?_, ?_, σ, hσ, ?_, hσeq⟩
  · simp only [Nat.unpair_pair]; exact (hEsub j k hk).1
  · simp only [Nat.unpair_pair]; exact hueq.symm
  · simp only [Nat.unpair_pair]; rw [hDeq, hrange, hσspan]
```

## Key steps

1. Source charts Φ_j on Ω′_j = Ω_j ∩ Φ_j⁻¹U from (CRC); u_j = f∘Φ_j locally Lipschitz
2. Target charts G_{j,k}, O_{j,k}, E_{j,k} from (LCIP), re-indexed by Nat.pair
3. Antilipschitz charts pull Hⁿ-null sets back to Lⁿ-null sets
4. At a.e. parameter w: orients + (CCR) + tangent uniqueness give range DΦ_j(w) = span τ and D(f∘Φ_j)(w) = L(x)∘DΦ_j(w)
5. Ξ(x) ≠ 0 ⇒ induced orientation σ and injective derivative ⇒ w ∈ E_{j,k}, DG_{j,k}(w) = L(x)∘DΦ_j(w), range = span σ
6. Bad parameters are Lⁿ-null ⇒ bad points Hⁿ-null via Lipschitz images and countable subadditivity

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean (identical)`
- `python3 over dag.json: frozen lean_statement/status of the 8 uncle nodes; all lean_name fields (226 unique); grep -c 'lpf_pi_' dag.json (0 matches)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (replay: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `lean_contract.validate_lean_statement on all 11 child statements`
- `grep -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def covectorPullback|def nVectorPushforward|def simpleNVector|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' Chapter06/Forms.lean; 'abbrev TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; 'def GeometricCurrentOn.support|theorem GeometricCurrentOn.support_subset_domain' Chapter06/CurrentLocalEquality.lean`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (line 216)`
- `grep -n 'LocallyLipschitzOn.comp|protected lemma comp' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean (only LocallyLipschitz.comp exists)`
- `lake build GMT.Ch06.Submission in /tmp/lpi3_scratch (scratch copy, .lake/packages linked to the pinned package tree)`
- `lake env lean Scratch/Stmts.lean (11 statements in comparator scope, only sorry warnings)`
- `lake env lean Scratch/Names.lean (#check of ~90 cited Mathlib/SimonGMT names; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm, ENorm via SeminormedAddGroup.toContinuousENorm, MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace, Norm (Covector ..) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm)`
- `lake env lean Scratch/Inst.lean (#synth ContinuousAdd / PseudoMetrizableSpace / ContinuousENorm (NVector (Eucl 3) 2) fail; documented workarounds compile)`
- `lake env lean Scratch/Assembly.lean (parent from 19 stubs; #print axioms propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean Scratch/AllChildren.lean and Scratch/E2E.lean (all 11 children proved in dependency order + parent assembly; per-child #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpi3_scratch/Scratch/Stmts.lean`
- `/tmp/lpi3_scratch/Scratch/Names.lean`
- `/tmp/lpi3_scratch/Scratch/Inst.lean`
- `/tmp/lpi3_scratch/Scratch/Assembly.lean`
- `/tmp/lpi3_scratch/Scratch/AllChildren.lean`
- `/tmp/lpi3_scratch/Scratch/E2E.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) is byte-identical to the workspace Contract and Submission. The child scope is import GMT.Ch06.Submission plus the replayed namespace and opens. It provides the contract notions (IsRectifiableTriple, tauAction, IsIntegerMultiplicity) and SimonGMT Ch03 Rectifiable (CountablyRectifiable with mono/range/iUnion, HasWeightedApproximateTangentSpaceAt, .unique for θ x ≠ 0). It also provides Ch06 n-vectors (NVector = Covector →L[ℝ] ℝ with the operator norm, simpleNVector, nVectorPushforward_simple), test forms, currents and support_subset_domain, plus Ch02 euclideanHausdorffMeasure_image_le_of_lipschitzOn.

It does not provide:
- SimonGMT SubmanifoldCover (countablyRectifiable_image_contDiffOn_open) or Mathlib's Multilinear.FiniteDimensional; both facts are therefore separate import-free leaves.
- LocallyLipschitzOn.comp.
- Instance search on NVector for ContinuousAdd, PseudoMetrizableSpace, ContinuousENorm and NormSMulClass; the verified workarounds are recorded in the child texts.

No lpf_pi_* name is reserved in dag.json, and leaf plans forbid helper declarations, so every child script is a single theorem. All 11 frozen statements validate and elaborate in the comparator scope. All 11 children are fully proved in Lean with only propext, Classical.choice and Quot.sound, using only their declared siblings. The frozen parent type follows from them and the eight uncles by the stated assembly; its only sorryAx comes from the uncle stubs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
