<!-- theorem-id: gmt-ch06/root.slicing-a1 -->

## Theorem `Submission.slicing_theorem`

For all P, m, open U ⊆ ℝ^P, every T ∈ D_{m+1}(U) with M_W(T) < ∞ and M_W(∂T) < ∞ for all W ⊂⊂ U, and every f : ℝ^P → ℝ which is L-Lipschitz on U, there is a family S_t ∈ D_m(U) (t ∈ ℝ) with: (i) IsSlice T f t S_t, i.e. S_t = ∂(T⌞{f<t}) − (∂T)⌞{f<t}, for every t; (ii) spt S_t ⊆ spt T ∩ {f = t} for every t; (iii) if T is integer multiplicity, S_t is integer multiplicity for L¹-a.e. t; (iv) for every open W ⊆ U, every L_W ≥ 0 with ‖Df‖ ≤ L_W Lebesgue-a.e. on W, every a < b and every R with IsRestriction T {x ∈ U : a < f x < b} R, there is a measurable g : ℝ → [0,∞] with M_W(S_t) ≤ g(t) for all t ∈ (a,b) and ∫_{(a,b)} g ≤ L_W·M_W(R).

Node: `root.slicing-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/664, https://github.com/ZhengyangZhang06/gmt-formalize/issues/666, https://github.com/ZhengyangZhang06/gmt-formalize/issues/669, https://github.com/ZhengyangZhang06/gmt-formalize/issues/672, https://github.com/ZhengyangZhang06/gmt-formalize/issues/676, https://github.com/ZhengyangZhang06/gmt-formalize/issues/678

## Lean problem

Declaration: `Submission.slicing_theorem`

```lean
SlicingTheorem
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

- Parent DAG node: `root`
- Child DAG node: `root.slicing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, §4 (pp. 153–158): Lemma 4.1, Remark 4.2, 4.3, Definition 4.4, Lemma 4.5 and its printed proof, the definitions 4.6–4.7, the properties 4.8–4.10 and their printed proof via 4.11 (including the closing sentence “To handle general Lipschitz f we simply use f^{(σ)} in place of f … then let σ ↓ 0”). Book n = m + 1. The printed proofs are copied below in numbered form; the steps the book leaves implicit (the measure representation used for restrictions, the a.e.-independence of exceptional sets, the passage from 4.9 to the measurable majorant required by the Lean statement) are filled in. Errata applied: (i) the right side of 4.10 is printed M(T ⌞ {a < f < b}); the proof (4.9) gives M_W(T ⌞ {a < f < b}), which is what is proved (Lean statement, README); (ii) in 4.9/4.10 the printed constant ess sup_W|Df| is used in the form “any L_W ≥ |Df| Lebesgue-a.e. on W”; (iii) in 4.11 “conclude the first part of 4.11” should read “the first part of 4.9”; (iv) the proof of 4.8–4.9 is printed for ⟨T,f,t₊⟩ (“similarly for t₋”); it is written here for the slice ⟨T,f,t₋⟩ of 4.6, which is the slice of the Lean statement. Correction of the previous draft (R1–R3): the mass measures are now constructed by the Riesz theorem on the locally compact space U (Radon on U, i.e. finite on compact subsets of U only) and then extended by zero to ℝ^P; no finiteness on compact subsets of ℝ^P is asserted (it can fail near ∂U, see R1′), and the representation, uniqueness and restriction statements R1–R3 and all later steps use only these local hypotheses.

Setting. U ⊆ ℝ^P open, T ∈ D_{m+1}(U) with M_W(T) < ∞ and M_W(∂T) < ∞ for every W ⊂⊂ U; f : ℝ^P → ℝ with |f(x) − f(y)| ≤ L|x − y| for x, y ∈ U. Write n := m + 1. Notation |α|, ‖ω‖, w^β, |w| and Fact A (w(α) = Σ_β α(e_β)w^β, |w(α)| ≤ |α||w|) as in the conventions (|α| = `covectorEuclideanNorm`). Hⁿ = μHE[n].

Preliminaries (Simon 2.7–2.9 and 2.12 with proofs).
(R0) Mass estimate: |X(ω)| ≤ M_W(X)‖ω‖ whenever tsupport ω ⊆ W (±ω/‖ω‖ is mass-admissible).
(R1) Representation (2.7), constructed on U and extended by zero. Let X ∈ D_k(U) with M_W(X) < ∞ for all W ⊂⊂ U. By R0, X is bounded for ‖·‖ on test forms supported in any W ⊂⊂ U; test forms are ‖·‖-dense in the continuous forms with compact support in W (mollification ω_ε = ϕ_ε*ω keeps |ω_ε| ≤ ‖ω‖ and support in W for small ε), so X extends uniquely to a linear functional X̄ on C_c(U; Λ^k(ℝ^P)) (continuous k-forms on the open set U with compact support in U) which is bounded on each C_c(W; Λ^k), W ⊂⊂ U. Apply the vector-valued Riesz representation theorem on the locally compact Hausdorff space U itself (Simon Ch. 1, 4.14; SimonGMT `simon_theorem_4_14` with the space U and H := Λ^k(ℝ^P) ≅ ℝ^{#I(k,P)} carrying the Euclidean coefficient inner product): there are a Radon measure μ_U on U — a Borel regular measure on U which is finite on every compact subset of U — and a μ_U-measurable ν : U → H with |ν| = 1 μ_U-a.e. and X̄(ω) = ∫_U Σ_β ω(e_β)ν^β dμ_U. Moreover μ_U(W) = sup{X̄(ω) : ω ∈ C_c(W;Λ^k), |ω| ≤ 1} for every open W ⊆ U (the total variation of the vector measure νμ_U on W; “≥” by Cauchy–Schwarz, “≤” by Lusin approximation of ν on compact subsets of W), and by the same mollification this supremum equals the supremum over test forms, i.e. μ_U(W) = M_W(X). (`simon_theorem_4_14` gives ν measurable for the Carathéodory σ-algebra of μ_U; since μ_U is Borel regular and σ-finite — U is σ-compact and μ_U is finite on compact subsets of U — ν agrees μ_U-a.e. with a Borel map, which we use instead, and we use the Borel restriction of μ_U.) Extend by zero: μ_X(A) := μ_U(A ∩ U) for Borel A ⊆ ℝ^P (the push-forward of μ_U under the inclusion U ↪ ℝ^P), X⃗^β := ν^β on U (Fact A) and X⃗ := 0 on ℝ^P ∖ U. Then: μ_X(ℝ^P ∖ U) = 0; μ_X(K) < ∞ for every compact K ⊆ U; μ_X(W) = M_W(X) ∈ [0,∞] for every open W ⊆ U; |X⃗| = 1 μ_X-a.e.; and for every ω ∈ D^k(U) the function x ↦ ⟨ω(x), X⃗(x)⟩ is μ_X-integrable (it is bounded by ‖ω‖ and vanishes off the compact set tsupport ω ⊆ U, on which μ_X is finite) with X(ω) = ∫⟨ω, X⃗⟩dμ_X; that is, `IsMeasureRepresentation X μ_X X⃗`.
(R1′) Warning and bookkeeping. μ_X is in general not a Radon measure on ℝ^P: it may be infinite on compact subsets of ℝ^P which meet ∂U. Example: P = 1, U = (0,1), X(a dx) := ∫_0^1 a(x)x⁻¹dx; X and ∂X (∂X(φ) = ∫_0^1 φ′(x)x⁻¹dx = ∫_0^1 φ(x)x⁻²dx) have locally finite mass in U, but μ_X([0,1]) = ∫_0^1 x⁻¹dx = ∞. Accordingly no finiteness of μ_T or μ_{∂T} beyond compact subsets of U is used anywhere below: every integral that occurs has an integrand vanishing outside the compact support (⊆ U) of a test form, or is a quantity μ_T(W ∩ B) for an open W ⊆ U, which is allowed to be +∞ (all mass bounds are inequalities in [0,∞]); the finiteness of μ_T(K ∩ ·) and μ_{∂T}(K ∩ ·) is used only for compact K ⊆ U.
(R2) Uniqueness. If (μ, v) satisfies `IsMeasureRepresentation X μ v`, then ∫_A v(ω)dμ = ∫_A ⟨ω, X⃗⟩dμ_X for every Borel A ⊆ ℝ^P and every ω ∈ D^k(U). Proof: (i) for every compact K ⊆ U, testing with χ dx^β (χ ∈ C_c^∞(U), 0 ≤ χ ≤ 1, χ = 1 on K) shows that χv^β is μ-integrable, so v^β ∈ L¹(μ⌞K); hence for every open W ⊂⊂ U the signed measures ν_β := (v^βμ)⌞W and ν′_β := (X⃗^βμ_X)⌞W have finite total variation. (ii) For φ ∈ C_c^∞(W), testing with φ dx^β gives ∫φ dν_β = X(φ dx^β) = ∫φ dν′_β; approximating φ ∈ C_c(W) uniformly by mollifications supported in a fixed compact subset of W (dominated convergence) gives ∫φ dν_β = ∫φ dν′_β for all φ ∈ C_c(W). (iii) Two finite signed Borel measures on the open set W that agree on C_c(W) are equal: the indicator of an open subset of W is an increasing limit of functions in C_c(W) with values in [0,1], so they agree on open subsets of W (dominated convergence), and the Borel sets on which they agree form a Dynkin system containing the π-system of open sets. (iv) Given ω ∈ D^k(U), choose an open W ⊂⊂ U with tsupport ω ⊆ W; for Borel A ⊆ ℝ^P, ∫_A v(ω)dμ = Σ_β∫_{A∩W}ω(e_β)dν_β = Σ_β∫_{A∩W}ω(e_β)dν′_β = ∫_A⟨ω, X⃗⟩dμ_X (Fact A; v(ω) = Σ_βω(e_β)v^β vanishes off tsupport ω; the integrands are bounded Borel functions).
(R3) Restriction (2.9). For a Borel set A ⊆ ℝ^P define X⌞A(ω) := ∫_A ⟨ω, X⃗⟩dμ_X (absolutely convergent by R1: the integrand vanishes off the compact set tsupport ω ⊆ U, where μ_X is finite). Then X⌞A ∈ D_k(U): it is linear, and if ω_j → ω in D^k(U) with tsupports in a fixed compact K ⊆ U, then ⟨ω_j, X⃗⟩ → ⟨ω, X⃗⟩ uniformly with the dominating function (sup_j‖ω_j‖)1_K, μ_X(K) < ∞, so X⌞A(ω_j) → X⌞A(ω). `IsRestriction X A (X⌞A)` holds (A measurable, representation (μ_X, X⃗) of R1), and any S with `IsRestriction X A S` equals X⌞A (R2). Mass of a restriction: for open W ⊆ U, M_W(X⌞A) = sup{X⌞A(ω) : ω test form, tsupport ω ⊆ W, |ω| ≤ 1} equals, by the mollification of R1, the supremum of ∫_{A}⟨ω, X⃗⟩dμ_X over continuous ω with compact support in W and |ω| ≤ 1; since |X⃗| = 1 μ_X-a.e. and μ_U⌞A is a Radon measure on U (a Borel measure finite on compact subsets of the σ-compact metric space U), this supremum is μ_U(W ∩ A) (“≤” by Cauchy–Schwarz; “≥” by inner regularity of μ_U⌞A on W and Lusin approximation of X⃗ on compact subsets of W, as in R1). Hence M_W(X⌞A) = μ_X(W ∩ A) ∈ [0,∞] for every open W ⊆ U. More generally for bounded h : ℝ^P → ℝ whose restriction to U is Borel (e.g. h = χ∘f with f continuous on U and χ continuous; the values of h off U are irrelevant because μ_X(ℝ^P ∖ U) = 0, so h may be replaced by h·1_U), X⌞h(ω) := ∫ h⟨ω, X⃗⟩dμ_X, and if h is smooth on a neighbourhood of tsupport ω then hω is a test form and X⌞h(ω) = X(hω).
(R4) Locality. If X vanishes on an open W ⊆ U (X(ω) = 0 whenever tsupport ω ⊆ W), then μ_X(W) = M_W(X) = 0.
(R5) For a 1-covector α and a k-covector γ, |α∧γ| ≤ |α||γ| (rotate coordinates so that α = |α|dx¹; then α∧γ = |α|dx¹∧γ, and dx¹∧ kills the coefficients of γ containing dx¹ and maps the others isometrically; the Euclidean coefficient norm is invariant under orthogonal changes of coordinates).

Apply R1 to T and to ∂T (both have locally finite mass in U): μ_T, T⃗, μ_{∂T}, ∂T⃗ (Radon on U, extended by zero to ℝ^P; by R1′ only their finiteness on compact subsets of U is used).

Proof.

1. (Definition of the slices, 4.6.) For t ∈ ℝ let A_t := {x ∈ U : f(x) < t}; f is continuous on U and U is open, so A_t is open, in particular Borel. Define S_t(ω) := (T⌞A_t)(dω) − ((∂T)⌞A_t)(ω) for ω ∈ D^m(U). S_t is linear and sequentially continuous (each term is, and d is continuous on test forms), so S_t ∈ D_m(U). With A := T⌞A_t and B := (∂T)⌞A_t, R3 gives `IsRestriction T {x | x ∈ U ∧ f x < t} A` and `IsRestriction T.boundary {…} B`, and S_t(ω) = A.boundary(ω) − B(ω). Hence `IsSlice T f t (S_t)` for every t.

2. (Support, 4.8.) (a) If tsupport ω ⊆ A_t, then tsupport dω ⊆ A_t, so (T⌞A_t)(dω) = T(dω) and ((∂T)⌞A_t)(ω) = ∂T(ω) = T(dω) (the integrands vanish off A_t); hence S_t(ω) = 0. (b) If tsupport ω ⊆ B_t := {x ∈ U : f(x) > t}, then dω and ω vanish on A_t, so both terms are 0. (c) If W ⊆ U is open and T vanishes on W, then ∂T vanishes on W, so μ_T(W) = μ_{∂T}(W) = 0 (R4), and for tsupport ω ⊆ W both integrals defining S_t(ω) vanish. Now let x ∈ U with x ∉ spt T ∩ {f = t}. If f(x) ≠ t, continuity of f on U gives a ball around x with compact closure inside A_t or inside B_t, on which S_t vanishes by (a)/(b). If x ∉ spt T, x lies in one of the open sets W (closure compact ⊆ U) on which T vanishes, and S_t vanishes on W by (c). In both cases x ∈ zeroRegion(S_t). Hence (S_t).support ⊆ T.support ∩ {x | f x = t}.

3. (Pointwise mass bound, 4.9–4.11 with f^{(σ)} in place of f.) Let W ⊆ U be open and L_W ≥ 0 with ‖Df(x)‖ ≤ L_W for Lebesgue-a.e. x ∈ W (`fderiv`; by Rademacher f is differentiable a.e. on U, and the weak and classical derivatives agree). Fix t ∈ ℝ and ω ∈ D^m(U) with tsupport ω =: K ⊆ W and ‖ω‖ ≤ 1. Choose δ₀ > 0 with the closed δ₀-neighbourhood of K inside W. For 0 < σ < δ₀ let f_σ := ϕ_σ * f on the δ₀−σ neighbourhood of K (ϕ_σ a mollifier on ℝ^P; only values of f on W are used). Then f_σ is smooth near K, |f_σ − f| ≤ Lσ on K, and Df_σ(x) = ∫Df(x−y)ϕ_σ(y)dy, so |Df_σ| ≤ L_W on K.
Fix h > 0 and ε > 0 and a smooth nonincreasing χ : ℝ → [0,1] with χ = 1 on (−∞, t−h], χ = 0 on [t, ∞) and |χ′| ≤ (1+ε)/h. The forms χ(f_σ)ω and χ′(f_σ)df_σ∧ω are test forms with tsupport ⊆ K, and (4.11)
∂T(χ(f_σ)ω) = T(d(χ(f_σ)ω)) = T(χ′(f_σ)df_σ∧ω) + T(χ(f_σ)dω).
By R1 and R5, |T(χ′(f_σ)df_σ∧ω)| ≤ ∫|χ′(f_σ)||df_σ||ω| dμ_T ≤ ((1+ε)/h)·L_W·μ_T(K ∩ {t−h < f_σ < t}) ≤ ((1+ε)/h)L_W μ_T(K ∩ {t−h−Lσ < f < t+Lσ}).
As σ ↓ 0, χ(f_σ) → χ(f) uniformly on K, so by dominated convergence (μ_T(K), μ_{∂T}(K) < ∞) ∂T(χ(f_σ)ω) = ∫χ(f_σ)⟨ω,∂T⃗⟩dμ_{∂T} → (∂T)⌞χ(f)(ω) and T(χ(f_σ)dω) → T⌞χ(f)(dω); and μ_T(K ∩ {t−h−Lσ < f < t+Lσ}) ↓ μ_T(K ∩ {t−h ≤ f ≤ t}) (finite measure, decreasing sets). Hence
|(∂T)⌞χ(f)(ω) − T⌞χ(f)(dω)| ≤ ((1+ε)/h)·L_W·μ_T(W ∩ {t−h ≤ f ≤ t}).
Now let h ↓ 0 (with corresponding χ = χ_h): χ_h(f(x)) → 1_{A_t}(x) for every x ∈ U (if f(x) < t then χ_h(f(x)) = 1 once h < t − f(x); if f(x) ≥ t it is 0), so by dominated convergence the left side tends to |((∂T)⌞A_t)(ω) − (T⌞A_t)(dω)| = |S_t(ω)|. Therefore |S_t(ω)| ≤ (1+ε)·L_W·liminf_{h↓0} h⁻¹μ_T(W ∩ {t−h ≤ f ≤ t}), where the product is 0 if L_W = 0 (each approximant is then 0, the measures involved being finite). Letting ε ↓ 0 and taking the supremum over admissible ω:
(4.9) M_W(S_t) ≤ L_W·Λ(t) for every t ∈ ℝ, Λ(t) := liminf_{h↓0} h⁻¹ μ_T(W ∩ {t−h ≤ f ≤ t}) ∈ [0,∞]   (with 0·∞ := 0).

4. (Integral bound 4.10 with a measurable majorant.) Fix a < b and R with `IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R`. By R3, R = T⌞{a < f < b} and M_W(R) = μ_T(W ∩ {a < f < b}) =: Q.
 • If L_W = 0: take g ≡ 0. By (4.9), M_W(S_t) = 0 ≤ g(t), and ∫⁻ g = 0.
 • If L_W > 0 and Q = ∞: take g ≡ ∞; then M_W(S_t) ≤ g(t) and ∫⁻_{(a,b)} g ≤ ∞ = L_W·Q.
 • If L_W > 0 and Q < ∞: let G(s) := μ_T(W ∩ {a < f ≤ s}) (G = 0 for s ≤ a, nondecreasing, G(s) ≤ Q < ∞ for s < b, and right-continuous on (−∞, b) by continuity from above of the measure μ_T⌞W on sets of finite measure; only right-continuity at points < b is used below — for s ≥ b, G may be +∞ when W is not relatively compact in U). For t ∈ (a,b) and small h > 0 (t−h−h² > a), {t−h ≤ f ≤ t} ⊆ {t−h−h² < f ≤ t}, so h⁻¹μ_T(W ∩ {t−h ≤ f ≤ t}) ≤ (1+h)·(G(t) − G(t−k))/k with k := h + h² (h⁻¹ = (1+h)/k); since h ↦ h + h² is an increasing bijection near 0 and 1+h → 1, Λ(t) ≤ D(t) := liminf_{k↓0}(G(t) − G(t−k))/k. Define g(t) := L_W·D(t) for t ∈ (a,b) and g(t) := 0 otherwise. Measurability: for fixed t, k ↦ G(t) − G(t−k) is left-continuous (right-continuity of G), so the infimum over k ∈ (0,1/j) equals the infimum over rational k ∈ (0,1/j); each t ↦ (G(t)−G(t−k))/k is Borel (G monotone), so D = lim_j inf_{k∈ℚ∩(0,1/j)} (…) is Borel. By (4.9), M_W(S_t) ≤ L_W Λ(t) ≤ g(t) for all t ∈ (a,b). By Lebesgue's theorem for monotone functions, G is differentiable a.e. with G′ = D a.e. and ∫_{[a′,b′]} G′ ≤ G(b′) − G(a′) for a < a′ < b′ < b; by monotone convergence ∫_{(a,b)} D ≤ G(b−) − G(a) ≤ μ_T(W ∩ {a < f < b}) = Q. Hence ∫⁻_{(a,b)} g ≤ L_W·Q = L_W·M_W(R).
This proves the last conjunct of `SlicingTheorem` (the printed 4.10 is the upper-integral form of exactly this).

5. (Slicing of rectifiable sets, Lemma 4.1 and Remark 4.2. The Ch. 3 results used below (1.6, 1.8, 1.9, 2.10, co-area) are applied on M ∩ U_i for open U_i ⊂⊂ U exhausting U, since θ is integrable only on compact subsets of U; weighted tangent spaces are local.) Assume now T = τ(M, θ, ξ) is integer multiplicity (n = m+1, `IsRectifiableTriple U n M θ ξ`, θ ∈ {1,2,…} on M). By McShane extension (`LipschitzOnWith.extend_real`) we may replace f by an L-Lipschitz function on ℝ^P agreeing with f on U; nothing below depends on f off U (M ⊆ U and all sets are intersected with U). Let ∇^Mf be the tangential gradient (Simon Ch. 3, 2.1; defined Hⁿ-a.e. on M via the C¹ decomposition M = ⋃M_j, M_j ⊆ N_j, Hⁿ(M₀) = 0), M₊ := {x ∈ M : ∇^Mf(x) ≠ 0}, M_t := f⁻¹(t) ∩ M₊. Lemma 4.1 (printed proof: (1) is Ch. 3, 2.10(2); (2) follows from Ch. 3, 1.6 together with ∇^Mf(x) ∈ T_xM and ⟨∇^Mf(x), τ⟩ = 0 for τ ∈ T_xM_t; the last part is the co-area formula of Ch. 3, §2): for L¹-a.e. t, M_t is countably (n−1)-rectifiable and Hⁿ⁻¹-measurable, and for Hⁿ⁻¹-a.e. x ∈ M_t both T_xM_t and T_xM exist, T_xM_t ⊆ T_xM is (n−1)-dimensional and T_xM = T_xM_t ⊕ ℝ∇^Mf(x); and for every nonnegative Hⁿ-measurable g on M, ∫_{−∞}^{∞}∫_{M_t} g dHⁿ⁻¹ dt = ∫_M |∇^Mf| g dHⁿ. Remark 4.2: applying this to g·1_{f<s} gives that s ↦ ∫_{M∩{f<s}}|∇^Mf|g dHⁿ is absolutely continuous with derivative ∫_{M_s} g dHⁿ⁻¹ for L¹-a.e. s (for integrable signed g as well, by splitting g = g⁺ − g⁻).

6. (The integer multiplicity slice, 4.3–4.4.) For the L¹-a.e. t of Step 5, define for x ∈ M_t: ξ_t(x) := ξ(x) ⌞ (∇^Mf(x)/|∇^Mf(x)|) (interior product: ⟨ξ⌞w, α⟩ = ⟨ξ, w*∧α⟩ for α ∈ Λ^{n−1}), and θ_t := θ|M_t. By 4.3, ξ_t(x) is a unit simple (n−1)-vector orienting T_xM_t for Hⁿ⁻¹-a.e. x ∈ M_t (if ξ = ±τ₁∧⋯∧τ_n with τ_n = ∇^Mf/|∇^Mf| and τ₁,…,τ_{n−1} an orthonormal basis of T_xM_t, then ξ_t = ±τ₁∧⋯∧τ_{n−1}, up to the sign (−1)^{n−1}). Define ⟨T,f,t⟩ := τ(M_t, θ_t, ξ_t) (Definition 4.4). It is integer multiplicity for L¹-a.e. t: (i) M_t ⊆ U, Hⁿ⁻¹-measurable, countably (n−1)-rectifiable (Step 5); (ii) θ_t ∈ {1,2,…}; (iii) local integrability: choose compacts K_i ↑ U; by the co-area formula ∫∫_{M_t∩K_i} θ dHⁿ⁻¹dt = ∫_{M∩K_i}|∇^Mf|θ dHⁿ ≤ L∫_{M∩K_i}θ dHⁿ < ∞, so for a.e. t every ∫_{M_t∩K_i}θ < ∞, hence θ_t is integrable on M_t ∩ K for every compact K ⊆ U; (iv) measurability of ξ_t on M_t for a.e. t (restrictions of Hⁿ-measurable functions on M to the slices M_t are Hⁿ⁻¹-measurable for a.e. t, by the co-area formula applied to indicator functions of the null sets where the measurable modifications differ); (v) orientation: the properties “T_xM exists and ξ(x) = ±(orthonormal frame of T_xM)” hold outside an Hⁿ-null set Z ⊆ M; by the co-area formula ∫Hⁿ⁻¹(Z ∩ M_t)dt = ∫_Z|∇^Mf|dHⁿ = 0, so for a.e. t they hold Hⁿ⁻¹-a.e. on M_t, and then 4.3 applies Hⁿ⁻¹-a.e. on M_t. θ_t is a positive integer-valued locally integrable function on the countably (n−1)-rectifiable M_t, so by Ch. 3, Theorem 1.9 and Remark 1.8(1) the weighted approximate tangent space of (M_t, θ_t) exists Hⁿ⁻¹-a.e. on M_t and equals T_xM_t, which ξ_t orients. (For n = 1, M_t is countable and locally finite, the weighted tangent space at each point is {0}, and ξ_t = ±1.)

7. (Lemma 4.5(2): the integer multiplicity slice equals S_t for a.e. t.) The printed proof: First (1): for a Lipschitz h on ℝ^P with mollifications h^{(σ)} and any bounded Hⁿ-measurable vector field v with compact support in U, ∫_Mθ v·∇^Mh^{(σ)}dHⁿ → ∫_Mθ v·∇^Mh dHⁿ as σ ↓ 0 (the printed “weak convergence in L²(μ_T)”, localized since μ_T is only locally finite) (check it on each N_j with v vanishing off M_j: in C¹ charts, h^{(σ)} → h uniformly with uniformly bounded gradients, so the tangential gradients converge weakly-* in L^∞; approximate v by continuous fields). Fix t, ε > 0 and let ψ(s) := 1 for s < t−ε, ψ linear on [t−ε, t], ψ(s) := 0 for s > t, and h := ψ∘f. For ω ∈ D^m(U):
(2) (∂T)⌞h(ω) = lim_{σ↓0} ∂T(h^{(σ)}ω) = lim_{σ↓0}[T(dh^{(σ)}∧ω) + T(h^{(σ)}dω)] = lim_{σ↓0}T(dh^{(σ)}∧ω) + T⌞h(dω)
(using R1 for T and ∂T and dominated convergence). Since ξ(x) orients T_xM, ⟨ξ, dh^{(σ)}∧ω⟩ = ⟨ξ ⌞ ∇^Mh^{(σ)}, ω⟩, so by (1)
(3) lim_{σ↓0}T(dh^{(σ)}∧ω) = ∫_M θ⟨ξ⌞∇^Mh, ω⟩ dHⁿ.
By the chain rule (4) ∇^Mh = ψ′(f)∇^Mf Hⁿ-a.e. on M (with ψ′(f) := 0 at the values t, t−ε; ∇^Mf = 0 Hⁿ-a.e. on each level set {f = c} ∩ M). Hence
(∂T)⌞h(ω) = −ε⁻¹∫_{M∩{t−ε<f<t}} θ⟨ξ⌞∇^Mf, ω⟩dHⁿ + T⌞h(dω).
Now let ε ↓ 0. By Remark 4.2 applied to g := θ⟨ξ⌞(∇^Mf/|∇^Mf|), ω⟩1_{M₊} (integrable on M ∩ tsupport ω), for L¹-a.e. t the first term tends to −∫_{M_t}θ⟨ξ_t, ω⟩dHⁿ⁻¹ = −⟨T,f,t⟩(ω); and h = h_ε → 1_{A_t} pointwise on U, so (∂T)⌞h(ω) → ((∂T)⌞A_t)(ω) and T⌞h(dω) → (T⌞A_t)(dω). Hence ⟨T,f,t⟩(ω) = (T⌞A_t)(dω) − ((∂T)⌞A_t)(ω) = S_t(ω) for all t outside an L¹-null set F_ω. To make the null set independent of ω: choose a countable family {ω_k} ⊆ D^m(U) such that every ω ∈ D^m(U) is the limit of some subsequence ω_{k_i} in the C¹ norm with tsupports in a fixed compact K ⊆ U (separability of C¹ on compacts, as in the 2.15 argument). Off F := ⋃_k F_{ω_k} ∪ (the exceptional set of Step 6), both ⟨T,f,t⟩ (a current of locally finite mass, continuous for the C⁰ norm on forms supported in K) and S_t (continuous for the C¹ norm on forms supported in K: by R1, R3, |S_t(ω)| ≤ μ_T(K)‖dω‖ + μ_{∂T}(K)‖ω‖ when tsupport ω ⊆ K, with μ_T(K), μ_{∂T}(K) < ∞ as K ⊆ U is compact) agree on all ω_k, hence on all ω. So for L¹-a.e. t, S_t = ⟨T,f,t⟩ is integer multiplicity (Step 6). This proves the third conjunct of `SlicingTheorem`: if T is integer multiplicity then ∀ᵐ t, `IsIntegerMultiplicity (S t)`.

8. (Conclusion.) The family S : ℝ → D_m(U), S(t) := S_t, satisfies: `IsSlice T f t (S t)` for all t (Step 1); (S t).support ⊆ T.support ∩ {f = t} for all t (Step 2); integer multiplicity for a.e. t when T is (Step 7); and for every open W ⊆ U, every L_W with ‖Df‖ ≤ L_W a.e. on W, every a < b and every R with `IsRestriction T {a < f < b} R`, a measurable g with M_W(S t) ≤ g(t) on (a,b) and ∫⁻_{(a,b)} g ≤ L_W·M_W(R) (Steps 3–4). This is `SlicingTheorem`.

## Key steps

1. Riesz representation (2.7) on the locally compact space U, extended by zero to ℝ^P: μ_T, μ_∂T are finite only on compact subsets of U (an example shows the ambient Radon property can fail), and only this local finiteness is used.
2. Uniqueness of measure representations (finite signed measures on W ⊂⊂ U agreeing on C_c(W)); restrictions (2.9) are unique and M_W(X⌞A) = μ_X(W∩A) ∈ [0,∞].
3. Define S_t := ∂(T⌞{f<t}) − (∂T)⌞{f<t}; IsSlice holds for every t.
4. Support: S_t vanishes on {f<t}, on {f>t} and on the zero region of T (4.8).
5. Mollify f and use 4.11 with cutoffs χ_h (all integrands supported in the compact tsupport ω ⊆ U) to get M_W(S_t) ≤ L_W·liminf_h h⁻¹μ_T(W∩{t−h≤f≤t}) for every t (4.9).
6. Majorant g := L_W·(lower left Dini derivative of G(s) = μ_T(W∩{a<f≤s})) is Borel; Lebesgue's theorem gives ∫g ≤ L_W M_W(R) (4.10); cases L_W = 0 and infinite mass separately.
7. For T = τ(M,θ,ξ): co-area slicing of M (4.1–4.2) and the integer multiplicity slice τ(M_t,θ,ξ⌞∇^Mf/|∇^Mf|) (4.3–4.4).
8. 4.5(2): the integer multiplicity slice equals S_t for a.e. t (mollification, chain rule, co-area differentiation, countable dense family of forms).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^theorem main_theorem' project/GMT/Ch06/Contract.lean`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all byte-identical)`
- `python3 listing of dag.json nodes (only 'root'; no reserved child lean_name)`
- `python3 audit of nodes/root/decomposition-audit-v2.json and decomposition-v2.json (only deformation A3 rejected; search of all 12 proofs for 'θ′ ≥ 1', 'σ-finite', 'Radon–Nikodym', 'IsLipschitzPushforward', 'LipschitzPushforwardIntegerMultiplicity', 'as in the conventions')`
- `rg -n 'theorem sigmaFinite_of_countable' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `rg -n 'theorem mul_meas_ge_le_lintegral₀' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n 'theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite|theorem Integrable.ae_eq_of_forall_setIntegral_eq' mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n 'theorem hausdorffMeasure_image_le (h : LipschitzWith' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem restrict_congr_set|theorem restrict_restrict [(]|theorem ae_restrict_iff.₀|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -il 'coarea|co-area' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -il 'Besicovitch.Federer|purely unrectifiable' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'abbrev NVector|def simpleNVector|def nVectorPushforward|theorem nVectorPushforward_simple|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/`
- `#print MeasureTheory.Measure.euclideanHausdorffMeasure (μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `grep -n '1.12|1.15|Borel-regular|3.19|3.24' book/chapter-01.txt`
- `lake build GMT.Ch06.Submission (scratch /tmp/gmt_ch06_v3_check, frozen commit d8d46c9, pinned packages)`
- `lake env lean Scratch/V3_Stmts.lean (12 child statements in gmt-compare.py contract_scope; 0 errors)`
- `lake env lean Scratch/V3_Assembly.lean (exact Submission.<name>; 12-way assembly vs type_of% GMT.Ch06.main_theorem; ff_from_siblings; parent_from_children; #print axioms)`
- `lake env lean Scratch/V3_SigmaFinite.lean (v3_sigmaFinite_restrict; #print axioms)`
- `lake env lean Scratch/V3_Tangent.lean (v3_weightedTangent_congr; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Stmts.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Assembly.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_SigmaFinite.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Tangent.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, a byte-identical Submission with no Submission.* declarations, and the README. The DAG contains only root, so the 12 bare child names are unreserved. All 12 conjuncts are `def … : Prop` in namespace GMT.Ch06. In a scratch build of the frozen project, every child statement elaborates in the comparator's child scope, `exact Submission.<name>` resolves for all 12 children, and the 12-way assembly typechecks against `type_of% GMT.Ch06.main_theorem`. FedererFlemingCompactness follows from its three declared siblings and the parent from the other 11 children, with axioms [propext, Classical.choice, Quot.sound]. The contract's `IsLipschitzPushforward` supplies only an `IsRectifiableTriple` representation (θ′ > 0 real, integrable on compacts), confirming the v2 defect. The repaired deformation A3 uses only that. Its σ-finiteness step is kernel-checked as `v3_sigmaFinite_restrict` (via Mathlib `Measure.sigmaFinite_of_countable`, `mul_meas_ge_le_lintegral₀`, `Measure.restrict_restrict`, `ae_restrict_mem₀`), and its tangent-space step as `v3_weightedTangent_congr`, against the actual SimonGMT `HasWeightedApproximateTangentSpaceAt`/`blowUpMap` definitions (via `LipschitzWith.hausdorffMeasure_image_le`, `Measure.restrict_congr_set`, `ae_restrict_iff'₀`; μHE[d] is a scalar multiple of μH[d]), both with standard axioms only. Mathlib provides Radon–Nikodym-type uniqueness (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`, `Integrable.ae_eq_of_forall_setIntegral_eq`). SimonGMT provides `nVectorPushforward_simple`, `covectorEuclideanNorm` and `HasWeightedApproximateTangentSpaceAt.unique`. Simon Ch. 1 gives 1.12 (μ⌞Y is Borel regular for measurable Y of finite measure), 1.15(2) (inner regularity) and 2.6 (H^m is Borel regular), as cited. There is no Mathlib match for co-area or for Besicovitch–Federer/purely unrectifiable; these are cited from Simon Ch. 3, as SimonGMT omits them. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
