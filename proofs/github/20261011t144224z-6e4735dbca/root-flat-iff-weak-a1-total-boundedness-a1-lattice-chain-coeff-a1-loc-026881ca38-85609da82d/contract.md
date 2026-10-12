<!-- theorem-id: gmt-ch06/root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1 -->

## Theorem `Submission.fiw_tb_lcc_local_isolating_form`

Let n, N ∈ ℕ, ρ > 0, F₀ = (z, α) ∈ LatticeFaceIndex n N, x ∈ latticeFace ρ F₀, and W ⊆ ℝ^N open with x ∈ W. Then there is a test form ω ∈ TestFormOn univ n (a C^∞ compactly supported n-form on ℝ^N) with three properties. (1) tsupport ω ⊆ W. (2) latticeFaceAction ρ F ω = 0 for every face index F ≠ F₀. (3) latticeFaceAction ρ F₀ ω > 0. Here latticeFaceAction ρ F ω = ∫_{latticeFace ρ F} ω(y)(e_{F.2(0)}, …, e_{F.2(n−1)}) dH^n(y), with e_a = EuclideanSpace.single a 1 and H^n = μHE[n].

Node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2364

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1227, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1229, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3233

Decomposition children: None

## Lean problem

Declaration: `Submission.fiw_tb_lcc_local_isolating_form`

```lean
∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n)
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

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 2–6 (coordinate covector, separation of parallel faces, evaluation formula, positive bump at an interior point, approximation of a face point by interior points), specialized to produce one localized test form. The separation of step 3 is supplied by the accepted cut-off isoperimetric_lattice_face_cutoff, which the parent's Remark allows: that cut-off vanishes on all other faces of direction α₀, which is all step 4 uses.

Notation.
- F₀ = (z, α) and A := range α.
- e_a := EuclideanSpace.single a 1; H := μHE[n] on ℝ^N.
- dx^α := wedgeCovectors n (i ↦ EuclideanSpace.proj (α i)).
- [[F]](ω) := latticeFaceAction ρ F ω.
- For δ > 0, K_δ := {y : ρ(z_i + δ) ≤ y_i ≤ ρ(z_i + 1 − δ) (i ∈ A), y_i = ρz_i (i ∉ A)}.
- Hypotheses: ρ > 0; x ∈ latticeFace ρ F₀, i.e. ρz_i ≤ x_i ≤ ρ(z_i + 1) for i ∈ A and x_i = ρz_i for i ∉ A; W open; x ∈ W.

1. Centre. Let c ∈ ℝ^N with c_i := ρ(z_i + 1/2) for i ∈ A and c_i := ρz_i for i ∉ A.
2. A nearby point. The map t ↦ x + t(c − x), ℝ → ℝ^N, is continuous and sends 0 to x ∈ W. So the preimage of the open set W is open and contains 0, and there is ε > 0 with x + t(c − x) ∈ W whenever |t| < ε (Metric.isOpen_iff). Let t := min(ε/2, 1). Then 0 < t ≤ 1 and t < ε, so p := x + t(c − x) ∈ W. Coordinatewise, p_i = x_i + t(c_i − x_i).
3. p ∈ K_{t/2}.
 - For i ∈ A: p_i − ρ(z_i + t/2) = (1 − t)(x_i − ρz_i) ≥ 0 and ρ(z_i + 1 − t/2) − p_i = (1 − t)(ρ(z_i + 1) − x_i) ≥ 0. This uses c_i = ρ(z_i + 1/2), 0 < t ≤ 1 and ρz_i ≤ x_i ≤ ρ(z_i + 1).
 - For i ∉ A: x_i = c_i = ρz_i, so p_i = ρz_i.
 Consequently p is a relative-interior point of the face: for i ∈ A, ρz_i < ρ(z_i + t/2) ≤ p_i ≤ ρ(z_i + 1 − t/2) < ρ(z_i + 1), because ρt/2 > 0; and p_i = ρz_i for i ∉ A.
4. Bump. W is a neighbourhood of p. By exists_contDiff_tsupport_subset (ℝ^N is finite-dimensional; smoothness ⊤ : ℕ∞) there is ψ : ℝ^N → ℝ, C^∞, with compact support, tsupport ψ ⊆ W, range ψ ⊆ [0, 1] and ψ(p) = 1.
5. Cut-off. Apply sibling face_cutoff (isoperimetric_lattice_face_cutoff) with δ := t/2 > 0, z and α. It gives φ : ℝ^N → ℝ that is C^∞, compactly supported, with 0 ≤ φ ≤ 1, φ = 1 on K_{t/2} (so φ(p) = 1 by step 3), and φ(y) = 0 for every y ∈ latticeFace ρ (z', α) with z' ≠ z.
6. Covector. Apply sibling coord_covector (isoperimetric_coord_covector_eval n N α): dx^α(e_{α(0)}, …, e_{α(n−1)}) = 1, and dx^α(e_{α'(0)}, …, e_{α'(n−1)}) = 0 for every α' ∈ SimonMultiIndex n N with α' ≠ α.
7. The form. Let g := ψ·φ (pointwise product).
 - g is C^∞ as a product of C^∞ functions, has compact support because ψ does (HasCompactSupport.mul_right), satisfies g ≥ 0, and g(p) = ψ(p)φ(p) = 1.
 - Define ω(y) := g(y) • dx^α. It is C^∞ (a smooth scalar times a constant covector), has compact support (HasCompactSupport.smul_right) and tsupport ω ⊆ univ. So ω ∈ TestFormOn univ n, and ω(y)(v) = g(y)·dx^α(v).
 - tsupport ω ⊆ tsupport g ⊆ tsupport ψ ⊆ W (tsupport_smul_subset_left, tsupport_mul_subset_left, step 4). This is property (1).
8. Other faces. Let F = (z', α') ≠ F₀.
 - If α' = α, then z' ≠ z. For y ∈ latticeFace ρ F the integrand is ψ(y)φ(y)·dx^α(e_α) = 0, since φ(y) = 0 by step 5. A set integral of a function vanishing on the set is 0 (setIntegral_eq_zero_of_forall_eq_zero).
 - If α' ≠ α, the integrand is g(y)·dx^α(e_{α'}) = 0 for all y by step 6, so the integral is 0.
 Hence [[F]](ω) = 0, which is property (2).
9. The face F₀. By step 6, [[F₀]](ω) = ∫_{latticeFace ρ F₀} g(y)·1 dH(y) = ∫_{latticeFace ρ F₀} g dH. Apply sibling face_integral_pos to (n, N, ρ, F₀, g, p). Its hypotheses hold: ρ > 0; g is continuous (being C^∞); g ≥ 0; g(p) = 1 > 0; and p satisfies the relative-interior condition by step 3. Hence [[F₀]](ω) > 0, which is property (3). ∎

Remark (optional, not part of the argument): this Lean text compiled in a scratch copy of the project (Lean v4.35.0-rc3, Mathlib 25730c7c) with the accepted Submission.isoperimetric_lattice_face_cutoff, Submission.isoperimetric_coord_covector_eval and the sibling Submission.fiw_tb_lcc_face_integral_pos available; #print axioms gives [propext, Classical.choice, Quot.sound].

theorem Submission.fiw_tb_lcc_local_isolating_form : ∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n) := by
  intro n N ρ F₀ x W hρ hx hW hxW
  obtain ⟨z, α⟩ := F₀
  -- Step 1: the centre `c` of the face.
  set c : Eucl N := WithLp.toLp 2 (fun i => if i ∈ range α then ρ * ((z i : ℝ) + 1 / 2)
    else ρ * (z i : ℝ)) with hc
  -- Step 2: a point `p = x + t (c - x)`, `0 < t ≤ 1`, of `W`.
  have hcont : Continuous fun t : ℝ => x + t • (c - x) := by fun_prop
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => x + t • (c - x)) ⁻¹' W := by simpa using hxW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hW.preimage hcont) 0 h0
  set t : ℝ := min (ε / 2) 1 with ht
  have ht0 : 0 < t := lt_min (half_pos hε) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set p : Eucl N := x + t • (c - x) with hp
  have hpW : p ∈ W := hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε)
  have hpcoord : ∀ i, p i = x i + t * (c i - x i) := fun i => by simp [hp]
  -- Step 3: `p` lies in the shrunken face `K_{t/2}`, hence in the open face.
  have hpK : ∀ i : Fin N, (i ∈ range α → ρ * ((z i : ℝ) + t / 2) ≤ p i ∧
      p i ≤ ρ * ((z i : ℝ) + 1 - t / 2)) ∧ (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    constructor
    · intro hi
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      have hci : c i = ρ * ((z i : ℝ) + 1 / 2) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci]
      constructor <;> nlinarith
    · intro hi
      have hci : c i = ρ * (z i : ℝ) := by
        simp only [hc, PiLp.toLp_apply, hi, ↓reduceIte]
      rw [hpcoord, hci, (hx i).2 hi]
      ring
  have hpopen : ∀ i : Fin N, (i ∈ range α → ρ * (z i : ℝ) < p i ∧ p i < ρ * ((z i : ℝ) + 1)) ∧
      (i ∉ range α → p i = ρ * (z i : ℝ)) := by
    intro i
    refine ⟨fun hi => ?_, (hpK i).2⟩
    obtain ⟨h1, h2⟩ := (hpK i).1 hi
    constructor <;> nlinarith
  -- Step 4: a bump `ψ` at `p` supported in `W`, the cut-off `φ` of the face, `dx^α`.
  obtain ⟨ψ, hψW, hψc, hψs, hψr, hψp⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hW.mem_nhds hpW)
  obtain ⟨φ, hφs, hφc, hφ01, hφ1, hφ0⟩ :=
    Submission.isoperimetric_lattice_face_cutoff n N ρ (t / 2) z α hρ (half_pos ht0)
  obtain ⟨hηα, hηne, -⟩ := Submission.isoperimetric_coord_covector_eval n N α
  set η : Covector (Eucl N) n := wedgeCovectors n (fun i => EuclideanSpace.proj (α i))
  -- Step 5: the test form `ω = (ψ φ) • dx^α`.
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y * φ y) := hψs.mul hφs
  have hgc : HasCompactSupport (fun y => ψ y * φ y) := hψc.mul_right
  obtain ⟨ω, hωx⟩ : ∃ ω : TestFormOn (univ : Set (Eucl N)) n,
      ∀ y, (ω : DifferentialForm (Eucl N) n) y = (ψ y * φ y) • η :=
    ⟨⟨fun y => (ψ y * φ y) • η, ⟨hgs.smul contDiff_const, hgc.smul_right (f' := fun _ => η)⟩,
      subset_univ _⟩, fun _ => rfl⟩
  have hωv : ∀ y (v : Fin n → Eucl N), (ω : DifferentialForm (Eucl N) n) y v = ψ y * φ y * η v :=
    fun y v => by rw [hωx, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  refine ⟨ω, ?_, ?_, ?_⟩
  -- Step 6: `tsupport ω ⊆ tsupport ψ ⊆ W`.
  · have hω : (ω : DifferentialForm (Eucl N) n) = fun y => (ψ y * φ y) • η := funext hωx
    rw [hω]
    exact (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hψW)
  -- Step 7: every other face contributes `0`.
  · rintro ⟨z', α'⟩ hF
    rw [latticeFaceAction]
    by_cases hα : α' = α
    · have hz : z' ≠ z := fun h => hF (by rw [h, hα])
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hωv, hφ0 z' hz y (by rwa [hα] at hy), mul_zero, zero_mul]
    · simp only [hωv, hηne α' hα, mul_zero, integral_zero]
  -- Step 8: `[[F₀]](ω) = ∫_{F₀} ψ φ dHⁿ > 0`.
  · have hval : latticeFaceAction ρ ((z, α) : LatticeFaceIndex n N) (ω : DifferentialForm (Eucl N) n) =
        ∫ y in latticeFace ρ ((z, α) : LatticeFaceIndex n N), ψ y * φ y ∂(μHE[n] : Measure (Eucl N)) := by
      simp only [latticeFaceAction, hωv, hηα, mul_one]
    rw [hval]
    refine Submission.fiw_tb_lcc_face_integral_pos n N ρ (z, α) (fun y => ψ y * φ y) p hρ
      hgs.continuous (fun y => mul_nonneg (hψr ⟨y, rfl⟩).1 (hφ01 y).1) ?_ hpopen
    rw [hψp, hφ1 p hpK, one_mul]
    exact one_pos

## Key steps

1. Move x toward the face centre c: p = x + t(c − x) lies in W for some t ∈ (0,1].
2. p lies in the shrunken face K_{t/2}, hence in the relative interior of F₀.
3. Take a bump ψ at p with tsupport ψ ⊆ W and ψ(p) = 1, and the cut-off φ (1 on K_{t/2}, 0 on the other faces of direction α).
4. ω = (ψφ) dx^α is a test form on ℝ^N with tsupport ω ⊆ W.
5. dx^α kills faces of other directions and φ kills the parallel faces, so [[F]](ω) = 0 for F ≠ F₀.
6. [[F₀]](ω) = ∫_{F₀} ψφ dH^n > 0 by face_integral_pos (ψφ is continuous, nonnegative and equals 1 at p).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (snapshot = .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494): mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d`
- `rg -n 'latticeFaceAction|IsLatticeChain|zeroRegion|latticeFace ' <snapshot>/project`
- `rg -n 'isoperimetric_lattice_chain_mass_ge|fiw_tb_lcc|local_isolating|face_integral_pos|lattice_face_cutoff' <snapshot>/project (no match, rc=1)`
- `rg in <snapshot>/mathlib/Mathlib: 'theorem exists_contDiff_tsupport_subset', 'theorem setIntegral_pos_iff_support_of_nonneg_ae', 'theorem _root_.IsOpen.measure_pos', 'theorem isOpen_set_pi', 'Continuous.isOpen_mulSupport', 'tprod_eq_mulSingle', 'theorem HasCompactSupport.mul_right', 'theorem tsupport_smul_subset_left', 'theorem tsupport_mul_subset_left', 'theorem setIntegral_eq_zero_of_forall_eq_zero', 'theorem isOpen_iff', 'theorem ContinuousOn.integrableOn_compact'`
- `python3 -I scan of dag.json: lean_name/lean_statement/status/candidate_commit of isoperimetric_lattice_chain_mass_ge, isoperimetric_coord_covector_eval, isoperimetric_lattice_face_cutoff, br_latticeFace_setIntegral_eq_cube; search for lean_names containing fiw_tb_lcc / local_isolating / face_integral_pos`
- `git log --all --oneline -S fiw_tb_lcc_ (no match)`
- `git show b1a770c375be212de585c186965d7d1f653fb13a:GMT/Ch06/Submission.lean ; git show 0561b355216f4041a30f4aaf2a4b139abdf038ca:GMT/Ch06/Submission.lean`
- `grep -n 'def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|def GeometricCurrentOn.VanishesOn|def massAdmissibleOn|theorem GeometricCurrentOn.le_massOn|theorem covectorEuclideanNorm_neg|abbrev TestFormOn|structure GeometricCurrentOn' in SimonGMT Chapter06`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_install_parent_supplied_child_handoff|def ensure' /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py store.py`
- `lake build Scratch.Acc; lake env lean Scratch/Pos.lean, Scratch/Iso.lean, Scratch/All.lean (#print axioms) in /tmp/lcc-scratch-Z3tV82`
- `python3 -I /tmp/lcc-tools/gen_challenges.py and gen_solutions.py (verifier/gmt-compare.py child_modules contract mode + lean_contract.validate_lean_statement); lake env lean Scratch/Ch_*.lean and Scratch/NodeSolution_*.lean`
- `sed -n 2028,2095p book/chapter-06.txt (Simon 7.2 proof, display (2): Σ_F |β_F| ρ^n ≤ c M(T))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lcc-scratch-Z3tV82/Scratch/Acc.lean`
- `/tmp/lcc-scratch-Z3tV82/Scratch/All.lean`

Pinned snapshot: project d8d46c95, Mathlib 25730c7c.
- Its project tree holds only the frozen Ch06 contract (latticeFace, latticeFaceAction, IsLatticeChain). Submission.lean is a byte copy.
- A search for a lattice-chain coefficient or support lemma, or for the proposed new names, finds nothing (rc=1).
- The accepted Submission declarations live in run commits. dag.json shows four of them are accepted and have exactly the needed frozen types:
  - isoperimetric_lattice_chain_mass_ge @ b1a770c3, the whole of part (b);
  - isoperimetric_coord_covector_eval @ 3d98b187;
  - isoperimetric_lattice_face_cutoff @ b27494a6;
  - br_latticeFace_setIntegral_eq_cube @ 0561b355.
  They are reused, and their proofs are reproduced from git show.
- SimonGMT supplies zeroRegion, support (= U \ zeroRegion), VanishesOn, TestFormOn and le_massOn.
- The Mathlib snapshot supplies every lemma the new children use:
  - exists_contDiff_tsupport_subset (FiniteDimension.lean:45);
  - setIntegral_pos_iff_support_of_nonneg_ae (Bochner/Set.lean:633);
  - IsOpen.measure_pos (OpenPos.lean:47);
  - isOpen_set_pi (Constructions.lean:1072);
  - Continuous.isOpen_support, the to_additive form of Continuous.isOpen_mulSupport (Separation/Basic.lean:383);
  - tsum_eq_single, the to_additive form of tprod_eq_mulSingle (InfiniteSum/Basic.lean:495);
  - HasCompactSupport.mul_right / smul_right (Support.lean:477/466);
  - tsupport_smul_subset_left / tsupport_mul_subset_left (Support.lean:168/124);
  - Metric.isOpen_iff (Pseudo/Defs.lean:833);
  - ContinuousOn.integrableOn_compact (LocallyIntegrable.lean:592).
- Scratch builds confirm all child types elaborate in the comparator scope. They also confirm that the new children and the parent assembly are provable with only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
