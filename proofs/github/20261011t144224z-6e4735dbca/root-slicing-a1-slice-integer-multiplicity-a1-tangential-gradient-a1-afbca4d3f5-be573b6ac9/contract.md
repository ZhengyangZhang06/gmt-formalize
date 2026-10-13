<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.c1_range_chart_cover-a1 -->

## Theorem `Submission.slicing_im_tg_cc_contDiff_range_chart_cover`

Let n, P ∈ ℕ (ℝᵏ = EuclideanSpace ℝ (Fin k); Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure on ℝ^P) and let G : ℝⁿ → ℝ^P be of class C¹. Then there are open sets O_k ⊆ ℝⁿ (k ∈ ℕ) with the following properties. For every k, G is Lipschitz on O_k with some constant K_k ≥ 0, and G is antilipschitz on O_k: there is c_k > 0 with c_k|w − w′| ≤ |G(w) − G(w′)| for all w, w′ ∈ O_k. Moreover Hⁿ(G(ℝⁿ) ∖ ⋃_k G(O_k)) = 0.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.c1_range_chart_cover-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3324

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1148

Decomposition children: None

## Lean problem

Declaration: `Submission.slicing_im_tg_cc_contDiff_range_chart_cover`

```lean
∀ (n P : ℕ) (G : Eucl n → Eucl P), ContDiff ℝ 1 G → ∃ O : ℕ → Set (Eucl n), (∀ k, IsOpen (O k)) ∧ (∀ k, ∃ K : ℝ≥0, LipschitzOnWith K G (O k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G w - G w'‖) ∧ (μHE[n] : Measure (Eucl P)) (range G \ ⋃ k, G '' O k) = 0
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.c1_range_chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) with Euclidean norm |·|. B_r(w) := Metric.ball w r. DG(w) := fderiv ℝ G w ∈ L(ℝⁿ, ℝ^P). Hⁿ := μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure on ℝ^P. G(S) is the image of S ⊆ ℝⁿ, and G(ℝⁿ) = range G. Call a set S ⊆ ℝⁿ good if both:
- G is K-Lipschitz on S for some K ≥ 0;
- there is c > 0 with c|w − w′| ≤ |G(w) − G(w′)| for all w, w′ ∈ S.

Source. This is steps 5–6 of the parent proof (slicing_im_tg_c1_chart_cover) for a single C¹ map G = G_ij.
- In Simon's printed proof (Ch. 3, Lemma 1.2) it is the last paragraph: by the area formula Hⁿ(G_ij({x : JG_ij = 0})) = 0; and if JG_ij(x) ≠ 0, then there is σ > 0 such that G_ij(B_σ(x)) is an embedded C¹ submanifold, with G_ij providing a local representation.
- It also includes the passage to countably many patches (Simon Ch. 3, Remark 1.3; the rational balls of step 6 of the parent proof).
- It uses the sibling c1_local_antilipschitz (Submission.lpf_c1_local_antilipschitz): if G : ℝⁿ → ℝ^Q is C¹ and DG(w) is injective, there are r > 0 and c > 0 with c|z − z′| ≤ |G(z) − G(z′)| for all z, z′ ∈ B_r(w).

1. (A countable family of candidate sets.) ℝⁿ is second countable, so it has a countable topological basis 𝔅 (Mathlib TopologicalSpace.exists_countable_basis; the open balls with rational centres and rational radii are one example). Let 𝒢 := {U ∈ 𝔅 : U is good} and 𝒢′ := 𝒢 ∪ {∅}. 𝒢 is countable as a subset of 𝔅, so 𝒢′ is countable, and 𝒢′ is nonempty because ∅ ∈ 𝒢′. Hence there is a surjection ℕ → 𝒢′, k ↦ O_k (Set.Countable.exists_eq_range).

2. (Each O_k has the required properties.) Fix k ∈ ℕ. Either O_k = ∅ or O_k ∈ 𝒢.
 (a) If O_k = ∅: ∅ is open, G is 0-Lipschitz on ∅, and the antilipschitz inequality on ∅ holds vacuously with c := 1 > 0.
 (b) If O_k ∈ 𝒢: O_k ∈ 𝔅, and members of a topological basis are open. O_k is good by definition of 𝒢, so G is Lipschitz on O_k with some constant and antilipschitz on O_k with some positive constant.
So every O_k is open, and G is both Lipschitz and antilipschitz (with a positive constant) on O_k.

3. (Regular points lie in some O_k.) Let w ∈ ℝⁿ be such that DG(w) is injective.
 (a) By c1_local_antilipschitz (with Q := P) there are r > 0 and c > 0 with c|z − z′| ≤ |G(z) − G(z′)| for all z, z′ ∈ B_r(w).
 (b) G is C¹, hence locally Lipschitz (Mathlib ContDiff.locallyLipschitz). Directly: DG is continuous, so ‖DG(z)‖ ≤ ‖DG(w)‖ + 1 on some ball B_ρ(w), and the mean value inequality on this convex ball shows that G is (‖DG(w)‖ + 1)-Lipschitz there. So there are K ≥ 0 and a neighbourhood t of w on which G is K-Lipschitz.
 (c) B_r(w) ∩ t is a neighbourhood of w, as the intersection of two neighbourhoods (r > 0). By the basis property there is U ∈ 𝔅 with w ∈ U ⊆ B_r(w) ∩ t.
 - Since U ⊆ t, G is K-Lipschitz on U.
 - Since U ⊆ B_r(w), the inequality of (a) holds for all z, z′ ∈ U.
 Hence U is good, so U ∈ 𝒢 ⊆ 𝒢′, and by surjectivity U = O_k for some k ∈ ℕ. Thus w ∈ O_k.

4. (The critical image is Hⁿ-null; step 5 of the parent proof.) Let Crit := {w ∈ ℝⁿ : DG(w) is not injective}.
- G is C¹ and 1 ≠ 0, so G is differentiable at every point (ContDiff.differentiable). Hence Crit = {w ∈ ℝⁿ : G is differentiable at w and DG(w) is not injective}.
- SimonGMT Chapter02.area_image_criticalSet_eq_zero is the area formula in the following form: for every map f : E → F between finite-dimensional real inner-product spaces, μHE[dim E](f({x : f is differentiable at x and Df(x) is not injective})) = 0. It is Chapter02.area_image_eq_zero_of_critical applied to that Borel set.
- Apply it with E := ℝⁿ, F := ℝ^P and dim ℝⁿ = n (finrank_euclideanSpace_fin). This gives Hⁿ(G(Crit)) = 0.

5. (The uncovered part of G(ℝⁿ) lies in G(Crit).) Let y ∈ G(ℝⁿ) ∖ ⋃_k G(O_k) and write y = G(w) with w ∈ ℝⁿ. If DG(w) were injective, step 3 would give k with w ∈ O_k, so y = G(w) ∈ G(O_k) ⊆ ⋃_k G(O_k), a contradiction. Hence DG(w) is not injective, w ∈ Crit and y ∈ G(Crit). Thus G(ℝⁿ) ∖ ⋃_k G(O_k) ⊆ G(Crit).

6. (Conclusion.) Step 5, monotonicity and step 4 give Hⁿ(G(ℝⁿ) ∖ ⋃_k G(O_k)) ≤ Hⁿ(G(Crit)) = 0. Together with step 2 this proves the statement. For n = 0 the argument applies verbatim: every linear map on ℝ⁰ = {0} is injective, so Crit = ∅. ∎

Implementation notes.
- Add `import Poincare.SimonGMT.Chapter02.AreaCritical` to Submission.lean. It is prebuilt in the shared package.
- Reference Lean proof: kernel-checked in an isolated scratch build importing the frozen GMT.Ch06.Submission and Poincare.SimonGMT.Chapter02.AreaCritical, in the comparator's contract scope, placed after the contract's `end` inside namespace GMT.Ch06. The sibling Submission.lpf_c1_local_antilipschitz must be present. With the sibling's accepted proof, `#print axioms` shows only propext, Classical.choice and Quot.sound.

theorem Submission.slicing_im_tg_cc_contDiff_range_chart_cover : ∀ (n P : ℕ) (G : Eucl n → Eucl P), ContDiff ℝ 1 G → ∃ O : ℕ → Set (Eucl n), (∀ k, IsOpen (O k)) ∧ (∀ k, ∃ K : ℝ≥0, LipschitzOnWith K G (O k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G w - G w'‖) ∧ (μHE[n] : Measure (Eucl P)) (range G \ ⋃ k, G '' O k) = 0 := by
  intro n P G hG
  -- step 1: countable basis 𝔅, good members 𝒢, and an enumeration of 𝒢 ∪ {∅}
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Eucl n)
  set good : Set (Set (Eucl n)) := {U | U ∈ b ∧ (∃ K : ℝ≥0, LipschitzOnWith K G U) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ U, ∀ w' ∈ U, c * ‖w - w'‖ ≤ ‖G w - G w'‖} with hgood
  have hgc : (insert ∅ good).Countable := (hbc.mono fun U hU => hU.1).insert ∅
  obtain ⟨O, hO⟩ := hgc.exists_eq_range (insert_nonempty _ _)
  have hOk : ∀ k, O k = ∅ ∨ O k ∈ good := fun k => by
    have : O k ∈ insert ∅ good := hO ▸ mem_range_self k
    simpa using this
  -- step 2: each O k is open, and G is Lipschitz and antilipschitz on it
  refine ⟨O, fun k => ?_, fun k => ?_, fun k => ?_, ?_⟩
  · rcases hOk k with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h.1
  · rcases hOk k with h | h
    · exact ⟨0, by rw [h]; exact lipschitzOnWith_empty _ _⟩
    · exact h.2.1
  · rcases hOk k with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact h.2.2
  · -- step 3: regular points are covered
    have hreg : ∀ w, Function.Injective (fderiv ℝ G w) → ∃ k, w ∈ O k := by
      intro w hw
      obtain ⟨r, hr, c, hc, hcr⟩ := Submission.lpf_c1_local_antilipschitz n P G w hG hw
      obtain ⟨K, t, ht, hKt⟩ := hG.locallyLipschitz w
      have hmem : ball w r ∩ t ∈ 𝓝 w := inter_mem (ball_mem_nhds w hr) ht
      obtain ⟨U, hUb, hwU, hUs⟩ := hb.mem_nhds_iff.1 hmem
      have hUg : U ∈ good := ⟨hUb, ⟨K, hKt.mono fun x hx => (hUs hx).2⟩,
        ⟨c, hc, fun z hz z' hz' => hcr z (hUs hz).1 z' (hUs hz').1⟩⟩
      obtain ⟨k, hk⟩ : U ∈ range O := hO ▸ mem_insert_of_mem _ hUg
      exact ⟨k, hk ▸ hwU⟩
    -- step 4: the critical image is Hⁿ-null (SimonGMT area formula)
    have hcrit := Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero
      (E := Eucl n) (F := Eucl P) G
    rw [finrank_euclideanSpace_fin] at hcrit
    -- steps 5–6: G(ℝⁿ) ∖ ⋃_k G(O k) ⊆ G(Crit)
    refine measure_mono_null ?_ hcrit
    rintro y ⟨⟨w, rfl⟩, hy⟩
    refine ⟨w, ⟨(hG.differentiable one_ne_zero) w, fun hinj => ?_⟩, rfl⟩
    obtain ⟨k, hk⟩ := hreg w hinj
    exact hy (mem_iUnion.2 ⟨k, w, hk, rfl⟩)

## Key steps

1. Fix a countable basis 𝔅 of ℝⁿ. Enumerate the countable nonempty set {∅} ∪ {U ∈ 𝔅 : G is Lipschitz and antilipschitz on U} by a surjection k ↦ O_k from ℕ. Each O_k is open, and G is Lipschitz and antilipschitz (with a positive constant) on it.
2. If DG(w) is injective, c1_local_antilipschitz (Submission.lpf_c1_local_antilipschitz) gives an antilipschitz ball B_r(w), and C¹ ⇒ locally Lipschitz gives a Lipschitz neighbourhood t of w. A basis set U with w ∈ U ⊆ B_r(w) ∩ t is good, so w lies in some O_k.
3. Since G is differentiable everywhere, Crit := {w : DG(w) not injective} is the critical set of SimonGMT area_image_criticalSet_eq_zero; with finrank ℝⁿ = n this gives Hⁿ(G(Crit)) = 0.
4. Every w with DG(w) injective lies in some O_k (proof step 3), so G(ℝⁿ) ∖ ⋃_k G(O_k) ⊆ G(Crit), which is Hⁿ-null.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean (identical); git show fe5ecf7a:GMT/Ch06/Submission.lean = frozen contract (this node's proof base has no lemmas)`
- `rg -n 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem exists_countable_basis|theorem Countable.exists_eq_range|tendsto_inv_nat_nhds_zero|theorem finrank_euclideanSpace_fin|theorem lipschitzOnWith_empty|def eqv' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'ContDiff.locallyLipschitz' local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus; rg -n 'theorem measure_mono_null|theorem measure_union_null' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -c 'slicing_im_tg_cc|lipschitz_range_c1_cover|contDiff_range_chart_cover' local-references/197bdd4b88278494 (exit 1: no match)`
- `grep -n 'def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; grep -n 'import' Chapter03/Rectifiable.lean (public import Poincare.SimonGMT.Chapter02.Lipschitz)`
- `grep -n 'theorem area_image_eq_zero_of_critical|theorem area_image_criticalSet_eq_zero' simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean; grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' Chapter02/Lipschitz.lean`
- `ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 (AreaCritical.olean, Lipschitz.olean, AreaLipschitz.olean, AreaDomain.olean present)`
- `python3 over dag.json (467 nodes): status/type/candidate of lpf_c1_approximation_eucl, lpf_c1_local_antilipschitz, lpf_c1_approximation_real, lpf_countably_rectifiable_c1_cover, lpf_lipschitz_c1_immersion_pieces, slicing_im_coarea_chart_cover; new-name uniqueness; no node with either new type; cross-branch reuse precedents and their parents' statuses`
- `read nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json, nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/decomposition-v1.json (reuse-child conventions)`
- `json fields proof/key_steps of nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-9651ace1ab/parent-supplied-natural-proof.json and ...-c1-fa0007faad/parent-supplied-natural-proof.json (copied verbatim)`
- `git show eff6bc80:GMT/Ch06/Submission.lean and 961fc108:GMT/Ch06/Submission.lean (accepted Lean code; frozen types byte-equal to dag.json); survey of extra imports in accepted candidates (AreaDomain x6, AreaBranches, DensityComparison, RadonPolarRepresentation, RadonCaratheodoryIntegral)`
- `python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem'); python3 -I verifier/lean_contract.py validate_lean_statement on all 5 types (OK)`
- `lean Scratch/{Stmts,Assembly,Imports,OnlyE,OnlyE_noimport,OnlyD,OnlyParent,Full,FullTargets,Final}.lean in /tmp/cc_split_Zpx7V0 (LEAN_PATH to shared prebuilt oleans; frozen Submission.olean rebuilt in scratch)`
- `sed -n 1,80p book/chapter-03.txt (Simon Ch. 3, 1.1, Lemma 1.2 printed proof, Remark 1.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-9651ace1ab/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-fa0007faad/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/cc_split_Zpx7V0/Scratch/Stmts.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/Final.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/OnlyE_noimport.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/OnlyD.lean`
- `/tmp/cc_split_Zpx7V0/Scratch/OnlyParent.lean`

Snapshot and base:
- The snapshot (project d8d46c95, Mathlib 25730c7c) Contract.lean is byte-identical to the workspace contract.
- This node's proof base fe5ecf7a has Submission.lean = the frozen contract, so accepted lemmas from other branches are usable only as reuse children.

Library facts used by the new children (all verified):
- Mathlib (snapshot paths above):
 - μHE[d] = volume on ℝ^d: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Geometry/Euclidean/Volume/Measure.lean:187;
 - ContDiff.locallyLipschitz, Analysis/Calculus/ContDiff/RCLike.lean:143;
 - TopologicalSpace.exists_countable_basis, Topology/Bases.lean:810;
 - Set.Countable.exists_eq_range, Data/Set/Countable.lean:149;
 - ENNReal.tendsto_inv_nat_nhds_zero, Topology/Instances/ENNReal/Lemmas.lean:486;
 - finrank_euclideanSpace_fin, Analysis/InnerProductSpace/PiL2.lean:205;
 - lipschitzOnWith_empty, measure_mono_null, measure_union_null and Denumerable.eqv.
- SimonGMT:
 - CountablyRectifiable is ∃ M₀, μHE[n] M₀ = 0 ∧ ∃ F, (∀ j, ∃ K, LipschitzWith K (F j)) ∧ M ⊆ M₀ ∪ ⋃ j, range (F j) (Chapter03/Rectifiable.lean:34);
 - Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216; already in the frozen import closure via Chapter03.Rectifiable);
 - Chapter02.area_image_criticalSet_eq_zero (Chapter02/AreaCritical.lean:185; no hypotheses on f; AreaCritical.olean is prebuilt).
 Both SimonGMT lemmas depend only on propext, Classical.choice and Quot.sound.

Reuse:
- lpf_c1_approximation_eucl (eff6bc80) and lpf_c1_local_antilipschitz (961fc108) are accepted. Their frozen types are byte-identical to dag.json and to the accepted Lean code.
- The identical-type twin lpf_countably_rectifiable_c1_cover is only speculative-ready, and the coarea twin is decomposing, so neither is reused.
- The new names slicing_im_tg_cc_lipschitz_range_c1_cover and slicing_im_tg_cc_contDiff_range_chart_cover have no match in the snapshot (rg exit 1), in SimonGMT, or among the 467 DAG nodes.

Kernel checks:
- All 5 types pass validate_lean_statement and elaborate in the exact comparator scope.
- Final.lean (real accepted proofs + new children + assembly + `exact Submission.X` targets) compiles cleanly, and every target depends only on propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
