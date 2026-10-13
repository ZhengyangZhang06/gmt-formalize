<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1 -->

## Theorem `Submission.slicing_im_tg_cg_gram_field`

Let P, n ∈ ℕ (ℝᵏ = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩), let Ω ⊆ ℝⁿ be open, let Φ : ℝⁿ → ℝ^P be of class C¹ such that DΦ(w) := fderiv ℝ Φ w is injective for every w ∈ Ω, and let h : ℝⁿ → ℝ be an arbitrary function, with Dh(w) := fderiv ℝ h w (Mathlib's Fréchet derivative, 0 where h is not differentiable). Then there is a Borel measurable γ : ℝⁿ → ℝ^P such that for every w ∈ Ω: γ(w) ∈ DΦ(w)(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w), and ⟨γ(w), DΦ(w)u⟩ = Dh(w)u for every u ∈ ℝⁿ.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3351

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.slicing_im_tg_cg_gram_field`

```lean
∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (h : Eucl n → ℝ), IsOpen Ω → ContDiff ℝ 1 Φ → (∀ w ∈ Ω, Function.Injective (fderiv ℝ Φ w)) → ∃ γ : Eucl n → Eucl P, Measurable γ ∧ ∀ w ∈ Ω, γ w ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u : Eucl n, inner ℝ (γ w) (fderiv ℝ Φ w u) = fderiv ℝ h w u
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) (Lean Eucl k): a finite-dimensional, hence complete and second countable, real inner product space with inner product ⟨·,·⟩, norm |·| and its Borel σ-algebra. L(E, F) := E →L[ℝ] F with the operator norm and its Borel σ-algebra (Mathlib's instance on continuous linear maps). Hypotheses: Ω ⊆ ℝⁿ open; Φ : ℝⁿ → ℝ^P of class C¹; DΦ(w) := fderiv ℝ Φ w injective for every w ∈ Ω; h : ℝⁿ → ℝ arbitrary. Notation for w ∈ ℝⁿ: A_w := fderiv ℝ Φ w ∈ L(ℝⁿ, ℝ^P); A_w* := ContinuousLinearMap.adjoint A_w ∈ L(ℝ^P, ℝⁿ), characterised by ⟨A_w* y, x⟩ = ⟨y, A_w x⟩ (Mathlib ContinuousLinearMap.adjoint_inner_left); the Gram operator G_w := A_w* ∘ A_w ∈ L(ℝⁿ, ℝⁿ); ℓ_w := fderiv ℝ h w ∈ L(ℝⁿ, ℝ) (Mathlib's Fréchet derivative, 0 where h is not differentiable); a_w := (InnerProductSpace.toDual ℝ ℝⁿ)⁻¹(ℓ_w) ∈ ℝⁿ, the Riesz vector of ℓ_w, so ⟨a_w, u⟩ = ℓ_w(u) for every u ∈ ℝⁿ (Mathlib InnerProductSpace.toDual_symm_apply). L(ℝⁿ, ℝⁿ) is a complete normed ring (product = composition, unit = identity), and R := Ring.inverse on it (R(T) = T⁻¹ if T is a unit, R(T) = 0 otherwise). This is Steps 4–5 of the parent proof (pointwise Gram representation of the chart derivative and Borel measurability of γ), with the antilipschitz lower bound replaced by its consequence that DΦ(w) is injective for w ∈ Ω.

1. (G_w is a unit for w ∈ Ω.) Let w ∈ Ω and u ∈ ℝⁿ with G_w u = 0. Then 0 = ⟨G_w u, u⟩ = ⟨A_w*(A_w u), u⟩ = ⟨A_w u, A_w u⟩ = |A_w u|², so A_w u = 0, and u = 0 because A_w is injective. Thus G_w is an injective linear endomorphism of the finite-dimensional space ℝⁿ, hence surjective (Mathlib LinearMap.injective_iff_surjective), hence bijective, hence a unit of the ring L(ℝⁿ, ℝⁿ) (Mathlib ContinuousLinearMap.isUnit_iff_bijective; ℝⁿ is complete). In particular R(G_w) is the two-sided inverse of G_w, so G_w(R(G_w)x) = x for every x ∈ ℝⁿ.

2. (Definition of γ.) For w ∈ ℝⁿ put B_w := A_w ∘ R(G_w) ∈ L(ℝⁿ, ℝ^P); put B̃_w := B_w if w ∈ Ω and B̃_w := 0 if w ∉ Ω; and define γ(w) := B̃_w(a_w) ∈ ℝ^P. Thus γ(w) = A_w(R(G_w)a_w) = A_w(A_w*A_w)⁻¹a_w for w ∈ Ω, and γ(w) = 0 for w ∉ Ω.

3. (Range.) Let w ∈ Ω. Then γ(w) = A_w(x_w) with x_w := R(G_w)a_w ∈ ℝⁿ, so γ(w) ∈ A_w(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w).

4. (Representation identity.) Let w ∈ Ω, u ∈ ℝⁿ and x_w := R(G_w)a_w. Then
 ⟨γ(w), A_w u⟩ = ⟨A_w x_w, A_w u⟩ = ⟨A_w*(A_w x_w), u⟩ = ⟨G_w x_w, u⟩ = ⟨a_w, u⟩ = ℓ_w(u) = fderiv ℝ h w u,
 by the adjoint identity, the definition of G_w, step 1 (G_w x_w = a_w) and the Riesz property of a_w.

5. (w ↦ B_w is continuous on Ω.) Since Φ is C¹, w ↦ A_w = fderiv ℝ Φ w is continuous on ℝⁿ (Mathlib ContDiff.continuous_fderiv, with 1 ≠ 0). The adjoint map L(ℝⁿ, ℝ^P) → L(ℝ^P, ℝⁿ) is a (conjugate-)linear isometric equivalence, hence continuous, and composition (S, T) ↦ S ∘ T of continuous linear maps is jointly continuous (Mathlib Continuous.clm_comp); so w ↦ G_w = A_w* ∘ A_w is continuous on ℝⁿ. Now fix w ∈ Ω. By step 1, G_w is a unit, and Ring.inverse is continuous at every unit of a complete normed ring (Mathlib NormedRing.inverse_continuousAt); since w′ ↦ G_{w′} is continuous at w, the composite w′ ↦ R(G_{w′}) is continuous at w, and then w′ ↦ B_{w′} = A_{w′} ∘ R(G_{w′}) is continuous at w (Mathlib ContinuousAt.clm_comp). Hence B is continuous at every point of Ω, in particular continuous on Ω.

6. (w ↦ B̃_w is Borel.) Ω is open, hence Borel. B̃ is the piecewise map equal to B on Ω and to the constant 0 on ℝⁿ ∖ Ω; B is continuous on Ω (step 5) and the constant map is continuous on ℝⁿ ∖ Ω, so B̃ : ℝⁿ → L(ℝⁿ, ℝ^P) is Borel measurable (Mathlib ContinuousOn.measurable_piecewise).

7. (w ↦ a_w is Borel.) For every function h : ℝⁿ → ℝ the map w ↦ ℓ_w = fderiv ℝ h w is Borel measurable (Mathlib measurable_fderiv; ℝ is complete), and (InnerProductSpace.toDual ℝ ℝⁿ)⁻¹ : L(ℝⁿ, ℝ) → ℝⁿ is a (conjugate-)linear isometric equivalence, hence continuous, hence Borel. So w ↦ a_w is Borel measurable.

8. (γ is Borel.) The evaluation map ev : L(ℝⁿ, ℝ^P) × ℝⁿ → ℝ^P, (T, x) ↦ T x, is a bounded bilinear map, hence continuous (Mathlib isBoundedBilinearMap_apply), and ℝⁿ is second countable. By Mathlib Continuous.measurable2, w ↦ ev(B̃_w, a_w) = γ(w) is Borel measurable, because B̃ (step 6) and a (step 7) are.

9. (Conclusion.) γ : ℝⁿ → ℝ^P is Borel measurable (step 8), and for every w ∈ Ω, γ(w) ∈ LinearMap.range (fderiv ℝ Φ w) (step 3) and ⟨γ(w), fderiv ℝ Φ w u⟩ = fderiv ℝ h w u for every u ∈ ℝⁿ (step 4). ∎ (The degenerate cases n = 0 or P = 0 need no separate treatment: the argument above applies verbatim; for n = 0 every endomorphism of ℝ⁰ = {0} is the identity, hence a unit.)

Lean remark. The following tactic proof was verified in the exact comparator scope (import GMT.Ch06.Submission, then the prefix replayed by verifier gmt-compare.contract_scope: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06 with the contract's three opens; noncomputable section followed by end) as `theorem Submission.slicing_im_tg_cg_gram_field : (<frozen statement>) := by`, with toolchain Lean v4.35.0-rc3 and Mathlib 25730c7c. Axioms: propext, Classical.choice, Quot.sound.
  intro P n Φ Ω h hΩ hΦ hinj
  classical
  set A : Eucl n → (Eucl n →L[ℝ] Eucl P) := fderiv ℝ Φ with hA
  have hAc : Continuous A := hΦ.continuous_fderiv one_ne_zero
  let G : Eucl n → (Eucl n →L[ℝ] Eucl n) := fun w => (ContinuousLinearMap.adjoint (A w)).comp (A w)
  have hGc : Continuous G := by
    have h1 : Continuous fun w => ContinuousLinearMap.adjoint (A w) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Eucl n) (F := Eucl P)).continuous.comp hAc
    exact h1.clm_comp hAc
  have hGunit : ∀ w ∈ Ω, IsUnit (G w) := by
    intro w hw
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hi : Function.Injective (G w) := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have h1 : inner ℝ (G w u) u = ‖A w u‖ ^ 2 := by
        simp only [G, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
      rw [hu, inner_zero_left] at h1
      have h2 : A w u = 0 := by
        have h3 : ‖A w u‖ ^ 2 = 0 := h1.symm
        exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
      exact (injective_iff_map_eq_zero _).mp (hinj w hw) u h2
    refine ⟨hi, ?_⟩
    exact (LinearMap.injective_iff_surjective
      (f := ((G w : Eucl n →L[ℝ] Eucl n) : Eucl n →ₗ[ℝ] Eucl n))).mp hi
  let B : Eucl n → (Eucl n →L[ℝ] Eucl P) := fun w => (A w).comp (Ring.inverse (G w))
  have hBc : ContinuousOn B Ω := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun w => Ring.inverse (G w)) w := by
      obtain ⟨U, hU⟩ := hGunit w hw
      have h2 := NormedRing.inverse_continuousAt U
      rw [hU] at h2
      exact h2.comp hGc.continuousAt
    exact hAc.continuousAt.clm_comp h1
  let a : Eucl n → Eucl n := fun w => (InnerProductSpace.toDual ℝ (Eucl n)).symm (fderiv ℝ h w)
  have ham : Measurable a :=
    (InnerProductSpace.toDual ℝ (Eucl n)).symm.continuous.measurable.comp (measurable_fderiv ℝ h)
  let Bt : Eucl n → (Eucl n →L[ℝ] Eucl P) := Ω.piecewise B 0
  have hBtm : Measurable Bt :=
    ContinuousOn.measurable_piecewise hBc continuousOn_const hΩ.measurableSet
  refine ⟨fun w => Bt w (a w), ?_, ?_⟩
  · exact isBoundedBilinearMap_apply.continuous.measurable2 hBtm ham
  · intro w hw
    have hBt : Bt w = B w := Set.piecewise_eq_of_mem _ _ _ hw
    simp only [hBt]
    refine ⟨LinearMap.mem_range.mpr ⟨Ring.inverse (G w) (a w), rfl⟩, ?_⟩
    intro u
    obtain ⟨U, hU⟩ := hGunit w hw
    have hGR : G w (Ring.inverse (G w) (a w)) = a w := by
      rw [← hU, Ring.inverse_unit]
      show ((U : Eucl n →L[ℝ] Eucl n) * ((U⁻¹ : (Eucl n →L[ℝ] Eucl n)ˣ) : Eucl n →L[ℝ] Eucl n)) (a w)
        = a w
      rw [Units.mul_inv]
      rfl
    calc inner ℝ (B w (a w)) (A w u)
        = inner ℝ ((ContinuousLinearMap.adjoint (A w)) (A w (Ring.inverse (G w) (a w)))) u := by
          rw [ContinuousLinearMap.adjoint_inner_left]; rfl
      _ = inner ℝ (G w (Ring.inverse (G w) (a w))) u := rfl
      _ = inner ℝ (a w) u := by rw [hGR]
      _ = fderiv ℝ h w u := InnerProductSpace.toDual_symm_apply

## Key steps

1. For w ∈ Ω the Gram operator G_w = DΦ(w)*DΦ(w) is injective since ⟨G_w u, u⟩ = |DΦ(w)u|², hence (finite dimension) a unit of L(ℝⁿ, ℝⁿ).
2. Define γ(w) := DΦ(w)G_w⁻¹a_w on Ω and 0 off Ω, where a_w is the Riesz vector of fderiv ℝ h w; then γ(w) ∈ range DΦ(w).
3. Adjoint identity: ⟨γ(w), DΦ(w)u⟩ = ⟨G_w G_w⁻¹a_w, u⟩ = ⟨a_w, u⟩ = fderiv ℝ h w u.
4. w ↦ DΦ(w)G_w⁻¹ is continuous on Ω (C¹, continuity of adjoint and composition, Ring.inverse continuous at units), so its extension by 0 off the open set Ω is Borel.
5. w ↦ a_w is Borel (measurable_fderiv and the Riesz isometry), and evaluation (T, x) ↦ Tx is continuous on second-countable spaces, so γ is Borel.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (all identical; git rev-parse HEAD = d8d46c9587747dee0751a1f780fcafdba16a3886)`
- `grep -rn 'slicing_im_tg_cg' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem measurable_fderiv\b|theorem measurable_fderiv_apply_const\b|theorem measurableSet_of_differentiableAt\b|theorem MeasurableSet.image_of_continuousOn_injOn|theorem ContinuousOn.measurableEmbedding|theorem MeasurableEmbedding.measurable_extend|theorem NormedRing.inverse_continuousAt|theorem ContinuousOn.measurable_piecewise|theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem|le_of_lip|theorem HasDerivAt.le_of_lipschitz' local-references/197bdd4b88278494/mathlib/Mathlib`
- `sed -n 330,400p Mathlib/Analysis/Calculus/FDeriv/Measurable.lean; sed -n 815,880p Mathlib/MeasureTheory/Constructions/Polish/Basic.lean; sed -n 515,535p Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean; sed -n 420,460p and grep 'def HasLineDerivAt' Mathlib/Analysis/Calculus/LineDeriv/Basic.lean (snapshot mathlib)`
- `lake env lean /tmp/cg_split_q7/Avail.lean: #check NormedRing.inverse_continuousAt, Continuous.measurable2, MeasurableEmbedding.measurable_extend, Function.Injective.extend_apply, Function.extend_apply', LipschitzWith.locallyLipschitz, LocallyLipschitz.locallyLipschitzOn, ContinuousLinearEquiv.funUnique, EuclideanSpace.equiv, ContinuousLinearMap.adjoint, adjoint_inner_left/right, InnerProductSpace.toDual, toDual_symm_apply, ContDiff.continuous_fderiv, measurable_fderiv, ContinuousOn.measurable_piecewise, HasLineDerivAt.le_of_lipschitz, LipschitzOnWith.ae_differentiableWithinAt_of_mem, injective_iff_map_eq_zero, ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective, isBoundedBilinearMap_apply, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ContinuousLinearEquiv.comp_differentiableAt_iff (all present; Measurable.clm_apply and ContinuousLinearMap.continuous_comp absent)`
- `python3 scans of dag.json: the tangential_gradient subtree (statuses and types of chart_cover, chart_gradient, chart_tangent, line_deriv); the lpf twins tangential_differential_exists, chart_chain_rule and weighted_tangent_on_c1_chart; lean_statements containing InjOn, Function.extend, inner ℝ, MeasurableEmbedding, adjoint or Ring.inverse; multi-parent and cross-branch child edges (53 multi-parent, 102 cross-branch); exact-type duplicates of the four child types; occurrences of the new names`
- `read nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json plus its scope, audit and receipt files, and nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json (reuse-child mechanism; rule that a solution PR proves only its tracked theorem)`
- `read the parent-child-handoff.json of nodes …-char-837491fcd9 (fderiv_lower_bound), …-tangential-differential-exists-a1-ch-34870e43f7 (chart_nondiff_image_null), …-tangential-gradient-a1-5d0f3ce1cd (line_deriv) and …-tangential-gradient-a1-661abdfbe7 (selected node)`
- `git show 8cfbc487a3d10545b0ea005ad58122242bbcc072 / 019ad40a7219b394f7e3a76a9361c778b6a98739 / 32fbf107157ca3b51c06f62670856410738101f5 -- GMT/Ch06/Submission.lean (accepted Lean proofs)`
- `python3: verifier/lean_contract.validate_lean_statement on the four child types; verifier/gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem')`
- `lake env lean /tmp/cg_split_q7/Stmts.lean, Assembly.lean, Final.lean, FinalFull.lean`
- `grep -c slicing_im_tg_cg_gram_field|slicing_im_tg_cg_borel_transfer in dag.json, DAG.md, dag.mmd, issue-workers.json, problem.json, nodes/, GMT/, lake-packages-25730c7c/simongmt/Poincare; git for-each-ref (1882 refs, no chart_gradient refs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-34870e43f7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-5d0f3ce1cd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cg_split_q7/Stmts.lean`
- `/tmp/cg_split_q7/Avail.lean`
- `/tmp/cg_split_q7/Assembly.lean`
- `/tmp/cg_split_q7/Final.lean`
- `/tmp/cg_split_q7/FinalFull.lean`
- `/tmp/cg_split_q7/proposal.json`

Snapshot and scope:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) holds the frozen Ch06 contract. It is byte-identical to the workspace Contract.lean and Submission.lean.
- The child comparator scope is import GMT.Ch06.Submission plus the replayed prefix: opens, namespace GMT.Ch06, its three opens, then noncomputable section … end.
- No `slicing_im_tg_cg*` declaration exists in the snapshot project, the GMT sources, SimonGMT, dag.json (508 nodes) or any git ref.

Mathlib supplies every tool used by the new children and the assembly:
- measurable_fderiv and measurableSet_of_differentiableAt (FDeriv/Measurable.lean);
- MeasurableSet.image_of_continuousOn_injOn and ContinuousOn.measurableEmbedding, the latter producing s.domRestrict f (Polish/Basic.lean);
- ContinuousOn.measurable_piecewise and Continuous.measurable2 (BorelSpace/Basic.lean);
- MeasurableEmbedding.measurable_extend;
- NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint with adjoint_inner_left, and InnerProductSpace.toDual_symm_apply;
- ContinuousLinearMap.isUnit_iff_bijective, LinearMap.injective_iff_surjective and isBoundedBilinearMap_apply;
- HasLineDerivAt.le_of_lipschitz (LineDeriv/Basic.lean), which reduces the parent's Step 8 to a single line;
- ContinuousLinearEquiv.comp_differentiableAt_iff and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.

DAG and reuse:
- Steps 1 and 2–3 are already comparator-accepted as lpf_wtc_cat_fderiv_lower_bound (candidate 8cfbc487) and lpf_tde_chart_nondiff_image_null (candidate 019ad40a). Both are reused with byte-identical types; cross-branch reuse is established in this DAG (102 edges).
- No accepted or active node has the type of gram_field or borel_transfer. lpf_tde_mcd_single_chart differs: it gives an operator-valued field with no range condition.

Kernel checks:
- All four child types pass validate_lean_statement and elaborate in the exact scope.
- Both new children are fully proved with standard axioms.
- The frozen parent type is proved from the four children and line_deriv. With the accepted proofs substituted, every declaration depends only on propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced these checks with its own assembly and returned ACCEPT.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
