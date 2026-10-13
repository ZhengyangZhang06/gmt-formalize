<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1 -->

## Theorem `Submission.slicing_im_tg_c1_chart_cover`

Let P, n ∈ ℕ and let M ⊆ ℝ^P (ℝᵏ = EuclideanSpace ℝ (Fin k)) be countably n-rectifiable in the sense of Simon Ch. 3, 1.1 (SimonGMT `CountablyRectifiable n M`: there are M₀ ⊆ ℝ^P with Hⁿ(M₀) = 0 and Lipschitz maps F_j : ℝⁿ → ℝ^P, j ∈ ℕ, with M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ); Hⁿ = μHE[n]). Then there are maps Φ_j : ℝⁿ → ℝ^P of class C¹ and open sets Ω_j ⊆ ℝⁿ (j ∈ ℕ) such that each Φ_j is Lipschitz on Ω_j (with some constant K_j ≥ 0), each Φ_j is antilipschitz on Ω_j (there is c_j > 0 with c_j|w − w′| ≤ |Φ_j(w) − Φ_j(w′)| for all w, w′ ∈ Ω_j), and Hⁿ(M ∖ ⋃_j Φ_j(Ω_j)) = 0.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2474

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1147, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1148, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4039, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4049

## Lean problem

Declaration: `Submission.slicing_im_tg_c1_chart_cover`

```lean
∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k) with Euclidean norm |·| and inner product ⟨·,·⟩; Lⁿ := volume on ℝⁿ; Hⁿ := μHE[n] (Mathlib's Euclidean-normalised n-dimensional Hausdorff measure; on ℝⁿ it equals Lⁿ by Mathlib `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). A map Ψ is c-antilipschitz on a set S if c|w − w′| ≤ |Ψ(w) − Ψ(w′)| for all w, w′ ∈ S. SimonGMT `CountablyRectifiable n M` (Simon Ch. 3, 1.1) means: there are M₀ ⊆ ℝ^P with Hⁿ(M₀) = 0 and Lipschitz maps F_j : ℝⁿ → ℝ^P (j ∈ ℕ) with M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ). This lemma is Step 1 of the parent proof: Simon Ch. 3, Lemma 1.2 (“only if”; the printed proof is followed in steps 4–5) together with Remark 1.3 (passage to countably many coordinate patches, done in steps 6–7 with bi-Lipschitz rational balls). The C¹ Approximation Theorem used by the printed proof is Simon Ch. 2, Theorem 1.5; its printed proof is reproduced in step 2.

(N) Null images. If Ψ : ℝⁿ → ℝ^P is Λ-Lipschitz on a set S ⊆ ℝⁿ then Hⁿ(Ψ(S)) ≤ Λⁿ Hⁿ(S) (SimonGMT `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`); hence Ψ maps Lⁿ-null subsets of S to Hⁿ-null sets.

1. (Case n = 0.) ℝ⁰ = {0}. Write M ⊆ M₀ ∪ ⋃_j F_j(ℝ⁰) with H⁰(M₀) = 0. Put Φ_j := F_j and Ω_j := ℝ⁰ (open). Every map on the one-point space ℝ⁰ is constant, hence C¹, 0-Lipschitz and 1-antilipschitz (both sides of the antilipschitz inequality are 0). Since M ∖ ⋃_j Φ_j(Ω_j) ⊆ M₀, we get H⁰(M ∖ ⋃_j Φ_j(Ω_j)) = 0. From now on n ≥ 1 (the argument below is also valid for n = 0).

2. (C¹ Approximation Theorem, Simon Ch. 2, 1.5; printed proof.) Claim: if g : ℝⁿ → ℝ is Lipschitz and ε > 0, there are a closed A ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ A) < ε and h ∈ C¹(ℝⁿ) with h = g on A.
 (a) By Rademacher's theorem (Mathlib `LipschitzWith.ae_differentiableAt`) the set B := {x : g is differentiable at x}, which is Borel (Mathlib `measurableSet_of_differentiableAt`), satisfies Lⁿ(ℝⁿ ∖ B) = 0. The map Dg := fderiv ℝ g : ℝⁿ → L(ℝⁿ, ℝ) is Borel (Mathlib `measurable_fderiv`), and ‖Dg(x)‖ ≤ Lip g for every x.
 (b) (Lusin, also on sets of infinite measure.) For a ≥ 1 let S_a := {x : a − 1 ≤ |x| < a} (bounded Borel annuli). Lusin's theorem for the finite measure Lⁿ⌞(S_a ∩ B) (SimonGMT `Chapter01.exists_isClosed_continuousOn_of_measurable` applied to the n coordinates x ↦ Dg(x)(e_i), intersecting the resulting closed sets) gives a closed C_a ⊆ S_a ∩ B with Dg|C_a continuous and Lⁿ((S_a ∩ B) ∖ C_a) < ε/2^{a+3}. Put C := ⋃_a C_a. Every bounded set meets only finitely many S_a, hence finitely many C_a; so C is closed (locally finite union of closed sets) and Dg|C is continuous (near each point C is a finite union of closed sets on each of which Dg is continuous). Moreover C ⊆ B and Lⁿ(ℝⁿ ∖ C) ≤ Lⁿ(ℝⁿ ∖ B) + Σ_a Lⁿ((S_a ∩ B) ∖ C_a) < ε/2. (The accepted DAG lemma `lpf_c1r_lusin_closed` states exactly this for an arbitrary Borel set S ⊆ ℝⁿ, here S = B.)
 (c) For x, y ∈ C with x ≠ y put R(x,y) := (g(y) − g(x) − Dg(x)(y − x))/|y − x|; then |R(x,y)| ≤ 2 Lip g. For k ≥ 1 and x ∈ C put η_k(x) := sup{|R(x,y)| : y ∈ C, 0 < |y − x| < 1/k} (sup ∅ := 0). For fixed y, x ↦ R(x,y) is continuous on C ∖ {y} (g and Dg|C are continuous). Hence if η_k(x) > t, witnessed by some y, then η_k(x′) > t for all x′ ∈ C sufficiently close to x; so η_k is lower semicontinuous on C, hence Borel. The η_k decrease in k, and η_k(x) → 0 for every x ∈ C because g is differentiable at x ∈ C ⊆ B with derivative Dg(x).
 (d) (Egoroff.) By Egoroff's theorem (Mathlib `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`) on each finite-measure set C ∩ S_a with tolerance ε/2^{a+3} (applied to the sequence (η_k)_k), there is a measurable A₀ ⊆ C with Lⁿ(C ∖ A₀) < ε/4 such that η_k → 0 uniformly on every bounded subset of A₀ (a bounded set meets only finitely many S_a). By inner regularity of Lⁿ, again annulus by annulus, there is a closed A ⊆ A₀ with Lⁿ(A₀ ∖ A) < ε/4 (the union of the closed pieces is closed by local finiteness). Hence Lⁿ(ℝⁿ ∖ A) < ε/2 + ε/4 + ε/4 = ε. (The accepted DAG lemma `lpf_c1r_egoroff_closed` is this closed-set form of Egoroff's theorem; the accepted DAG lemma `lpf_c1r_uniform_remainder` packages (c)–(d) together with the Whitney condition of (e): for Lipschitz g, closed C on which g is differentiable with Dg|C continuous, and ε > 0, it yields a closed A ⊆ C with Lⁿ(C ∖ A) < ε satisfying that condition.)
 (e) (Whitney.) g|A and Dg|A are continuous. If K ⊆ A is compact and δ > 0, choose k with sup_K η_k < δ (K is bounded); then for x ∈ K and y ∈ A with 0 < |y − x| < 1/k: |g(y) − g(x) − Dg(x)(y − x)| = |R(x,y)| |y − x| ≤ η_k(x)|y − x| ≤ δ|y − x|. This is Whitney's condition (Simon Ch. 2, 1.6(‡)). By Whitney's Extension Theorem (Simon Ch. 2, Theorem 1.6; proof in [EG92, §6.5] or [Fed69, 3.1.14]; in Lean it is the accepted DAG lemma `lpf_c1r_whitney_extension`, whose hypotheses are exactly: A closed, g and Dg continuous on A, and the compact-uniform remainder estimate just proved) there is h ∈ C¹(ℝⁿ) with h = g on A (and Dh = Dg on A). □

3. (Vector-valued version.) Let F : ℝⁿ → ℝ^P be Lipschitz and ε > 0. If P = 0 put G :≡ 0 and A := ℝⁿ. Otherwise apply step 2 to each coordinate F^l := ⟨F, e_l⟩ (Lipschitz), l = 1, …, P, with ε/P, obtaining closed A_l and h_l ∈ C¹(ℝⁿ) with h_l = F^l on A_l; put A := ⋂_l A_l (closed, Lⁿ(ℝⁿ ∖ A) ≤ Σ_l Lⁿ(ℝⁿ ∖ A_l) < ε) and G := Σ_l h_l e_l ∈ C¹(ℝⁿ; ℝ^P). Then F = G on A.

4. (Simon's proof of Lemma 1.2: reduction to C¹ maps.) By hypothesis M ⊆ M₀ ∪ ⋃_{j∈ℕ} F_j(ℝⁿ) with Hⁿ(M₀) = 0 and each F_j Lipschitz. For j ∈ ℕ and i ≥ 1, step 3 gives G_{ij} ∈ C¹(ℝⁿ; ℝ^P) and a closed A_{ij} with F_j = G_{ij} on A_{ij} and Lⁿ(ℝⁿ ∖ A_{ij}) < 1/i. Put Z_j := ℝⁿ ∖ ⋃_i A_{ij}. Then Lⁿ(Z_j) ≤ 1/i for every i, so Lⁿ(Z_j) = 0, and E_j := F_j(Z_j) satisfies Hⁿ(E_j) = 0 by (N). If w ∉ Z_j then w ∈ A_{ij} for some i and F_j(w) = G_{ij}(w). Hence
 (1) M ⊆ M₀ ∪ ⋃_j E_j ∪ ⋃_{i,j} G_{ij}(ℝⁿ).

5. (Critical points have Hⁿ-null image; Simon: “by the area formula …{x : JG_{ij} = 0}…”.) Fix G := G_{ij} and let Crit := {w ∈ ℝⁿ : DG(w) is not injective}. The set of injective linear maps ℝⁿ → ℝ^P is open in L(ℝⁿ, ℝ^P): if A is injective there is m > 0 with |As| ≥ m|s| for all s (finite dimension; any m > 0 works when n = 0), and then every B with ‖B − A‖ < m satisfies |Bs| ≥ (m − ‖B − A‖)|s|, so B is injective. Since DG is continuous, Crit is closed, hence Borel. G is differentiable at every point. By the area formula in the form of SimonGMT `Chapter02.area_image_eq_zero_of_critical` (for a Borel set s on which a map ℝⁿ → ℝ^P is differentiable with non-injective derivative, the Hⁿ-measure of the image of s is 0; here finrank ℝ ℝⁿ = n), Hⁿ(G(Crit)) = 0.

6. (Regular points: bi-Lipschitz balls; inverse-function argument.) Let w₀ ∈ ℝⁿ ∖ Crit and A := DG(w₀). As A is an injective linear map on the finite-dimensional space ℝⁿ, there is m > 0 with |As| ≥ m|s| for all s ∈ ℝⁿ. Put c := m/2. By continuity of DG choose r > 0 with ‖DG(z) − A‖ ≤ c for |z − w₀| < r. For z, z′ in the convex ball B_r(w₀), the mean value inequality applied to z ↦ G(z) − Az gives |G(z) − G(z′) − A(z − z′)| ≤ c|z − z′|, hence |G(z) − G(z′)| ≥ m|z − z′| − c|z − z′| = c|z − z′|; and since ‖DG‖ ≤ ‖A‖ + c on B_r(w₀), the mean value inequality also gives |G(z) − G(z′)| ≤ (‖A‖ + c)|z − z′|. (Accepted DAG lemma `lpf_c1_local_antilipschitz` is the antilipschitz part.) Choose an open ball O with rational centre and rational radius with w₀ ∈ O ⊆ B_r(w₀); G is Lipschitz and c-antilipschitz on O. Let 𝒪_{ij} be the countable set of open balls O with rational centre and rational radius such that G_{ij} is Lipschitz on O (with some constant) and c-antilipschitz on O for some c > 0. We have shown ℝⁿ ∖ Crit_{ij} ⊆ ⋃_{O∈𝒪_{ij}} O, so
 (2) G_{ij}(ℝⁿ) ⊆ G_{ij}(Crit_{ij}) ∪ ⋃_{O∈𝒪_{ij}} G_{ij}(O).

7. (The charts.) Let 𝒯 be the countable set of triples (i, j, O) with i ≥ 1, j ∈ ℕ and O ∈ 𝒪_{ij}. If 𝒯 = ∅ put Φ_k :≡ 0 and Ω_k := ∅ for all k ∈ ℕ (∅ is open, constants are C¹, and the Lipschitz and antilipschitz conditions on ∅ hold vacuously, e.g. with constants 0 and 1). Otherwise choose a surjection k ↦ (i_k, j_k, O_k) from ℕ onto 𝒯 and put Φ_k := G_{i_k j_k}, Ω_k := O_k. In both cases every Ω_k is open, every Φ_k is C¹ on ℝⁿ (`ContDiff ℝ 1`), Lipschitz on Ω_k and antilipschitz on Ω_k with a positive constant, and ⋃_k Φ_k(Ω_k) = ⋃_{(i,j,O)∈𝒯} G_{ij}(O).

8. (Conclusion.) By (1) and (2), M ∖ ⋃_k Φ_k(Ω_k) ⊆ M₀ ∪ ⋃_j E_j ∪ ⋃_{i,j} G_{ij}(Crit_{ij}), a countable union of Hⁿ-null sets (hypothesis, step 4 and step 5). By countable subadditivity Hⁿ(M ∖ ⋃_k Φ_k(Ω_k)) = 0, which together with step 7 is the claim. ∎

Implementation remarks (not part of the mathematical argument). (i) The frozen type of this lemma is byte-identical to that of `lpf_countably_rectifiable_c1_cover` (lipschitz-pushforward branch; speculative-ready, not comparator-accepted at the time of this split, hence the fresh name). If that declaration is comparator-accepted when this node is decomposed, it can be reused as a reuse child with its exact name and identical type. (ii) Otherwise, in this node's own decomposition the following comparator-accepted declarations can be included as reuse children (exact names, identical frozen types): `lpf_c1r_lusin_closed` (step 2(b)), `lpf_c1r_egoroff_closed` (step 2(d)), `lpf_c1r_uniform_remainder` (steps 2(c)–(e), Whitney condition), `lpf_c1r_whitney_extension` (step 2(e)), `lpf_c1_local_antilipschitz` (antilipschitz part of step 6). (iii) Imports: `Poincare.SimonGMT.Chapter02.AreaCritical` (step 5) and `Chapter01.Lusin` are prebuilt in the shared package and may be added to Submission.lean, as accepted nodes do; `Poincare.SimonGMT.Chapter02.WhitneyExtension` is not prebuilt in the read-only shared package, so SimonGMT's `exists_contDiff_one_extension_of_whitney` must not be imported — use `lpf_c1r_whitney_extension` instead.

## Key steps

1. Case n = 0: take Φ_j := F_j and Ω_j := ℝ⁰.
2. C¹ Approximation Theorem (Simon Ch. 2, 1.5, printed proof): Rademacher + Lusin + Egoroff yield a closed A with Lⁿ(ℝⁿ∖A) < ε satisfying Whitney's condition, and Whitney extension gives h ∈ C¹ with h = g on A; apply componentwise for ℝ^P-valued maps.
3. Simon's Lemma 1.2: F_j = G_ij on A_ij, so M ⊆ M₀ ∪ ⋃_j F_j(Z_j) ∪ ⋃_{i,j} G_ij(ℝⁿ) with Lⁿ(Z_j) = 0 and hence Hⁿ(F_j(Z_j)) = 0.
4. The image of the critical set {DG_ij not injective} (closed) is Hⁿ-null by the area formula.
5. At regular points the mean value inequality makes G_ij Lipschitz and antilipschitz on a small rational ball; countably many such balls cover the regular set.
6. Enumerate the triples (i, j, O) as charts (Φ_k, Ω_k) and conclude by countable subadditivity.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (both identical; workspace HEAD d8d46c95)`
- `python3 importlib verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') -> scope prefix: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n '^theorem|^def' simongmt Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,AreaDomain,WhitneyExtension,WhitneyJet}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/{SubmanifoldCover,Differential,DisjointCover}.lean`
- `grep -n '^theorem' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_smul0)`
- `grep -rn 'theorem Measurable.find|theorem measurable_find|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem DifferentiableWithinAt.differentiableAt|theorem ae_restrict_iff|theorem tendstoUniformlyOn_of_ae_tendsto|IsSigmaCompact.image|theorem normDet_sq_eq_det_gram|theorem normDet_nonneg|theorem hausdorffMeasure_image_le' mathlib/Mathlib`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 and Chapter01 (WhitneyExtension.olean absent; AreaCritical, AreaLipschitz, AreaDomain, WhitneyJet, Lusin, DensityComparison present)`
- `python3 scan of dag.json (360 nodes): uniqueness of slicing_im_tg_* names; byte-identity of child types with lpf_countably_rectifiable_c1_cover / lpf_weighted_tangent_on_c1_chart (speculative-ready); live statuses and statements of lpf_c1r_*, lpf_c1_local_antilipschitz, lpf_lipschitz_c1_immersion_pieces, lpf_wtc_*, lpf_tde_chart_directional_deriv, lpf_ccr_hasDerivAt_line_of_comp, rectifiability_weighted_tangent_ae, br_weightedTangent_congr, iwl_weighted_tangent_locality`
- `read nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (twin proofs; reuse-child mechanism)`
- `git show <workspace_result_commit>:GMT/Ch06/Submission.lean for 138 accepted nodes (extra SimonGMT imports such as Chapter02.AreaDomain, Chapter01.DensityComparison, Chapter02.AreaBranches are allowed)`
- `lake env lean /tmp/tg_split/Stmts.lean (four child types in exact comparator scope; 0 errors)`
- `lake env lean /tmp/tg_split/Assembly.lean (frozen parent type proved from chart_cover, chart_tangent, chart_gradient stubs; #print axioms: propext, sorryAx [stubs only], Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/CProof.lean (complete proof of the line_deriv frozen type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/Avail.lean (#check of cited Mathlib and SimonGMT lemmas in the Submission import closure)`
- `python3 verifier/lean_contract.py validate_lean_statement on the four child types (all OK)`
- `rg 'slicing_im_tg' local-references/197bdd4b88278494/project and lake-packages-25730c7c/simongmt (no match)`
- `sed book/chapter-03.txt (1.1-1.9, 2.1-2.2), chapter-02.txt (1.4-1.8, 4.1-4.11), chapter-01.txt (3.6-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/tmp/tg_split/Stmts.lean`
- `/tmp/tg_split/Assembly.lean`
- `/tmp/tg_split/CProof.lean`
- `/tmp/tg_split/Avail.lean`

Snapshot and imports:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract.lean and Submission.lean. Child types may therefore use only contract, SimonGMT and Mathlib names. The comparator scope is namespace GMT.Ch06 with the contract's opens.
- SimonGMT supplies the following:
  - CountablyRectifiable as countably many Lipschitz images plus an Hⁿ-null set, and HasWeightedApproximateTangentSpaceAt with uniqueness at θ(x) ≠ 0.
  - Lipschitz image bounds for μHE[n].
  - Area-formula critical-image and injective results (AreaCritical, AreaLipschitz, AreaDomain), Lusin (Chapter01.Lusin) and the upper density theorem 3.6 (Chapter01.DensityComparison). These modules are not imported by the contract but are prebuilt and may be added to the imports, as accepted nodes do.
  - Its Chapter02.WhitneyExtension module is not prebuilt, so it cannot be imported.
- SimonGMT lacks the chart-cover direction of Simon Lemma 1.2 (SubmanifoldCover proves only the easy direction), a tangential gradient for Lipschitz functions, and tangent identification on C¹ charts.
- Mathlib supplies Rademacher on sets (LipschitzOnWith.ae_differentiableWithinAt_of_mem), μHE[n] = volume on ℝⁿ, measurable_fderiv, measurableSet_of_differentiableAt, Lusin–Souslin images and measurable embeddings, Measurable.find, Egorov, and normDet_sq_eq_det_gram.

DAG and reuse:
- The chart-cover and chart-tangent lemmas exist in the DAG only as the speculative-ready lpf twins. Their types are byte-identical to the children chart_cover and chart_tangent, but they are not yet comparator-accepted, so fresh names are used.
- Many of the twins' leaves are comparator-accepted and are listed in the child proofs for reuse in those children's own decompositions.
- No accepted declaration has a type identical to any child. slicing_im_tg_* matches nowhere: not in the snapshot project, not in SimonGMT, not among the 360 DAG nodes.

Kernel checks:
- All four child types elaborate in the exact scope and pass the verifier's statement validator.
- The frozen parent type is proved from chart_cover, chart_tangent and chart_gradient; sorryAx comes only from the stubs.
- line_deriv is fully proved with standard axioms.

These checks do not certify the analytic proofs of chart_cover, chart_tangent and chart_gradient.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
