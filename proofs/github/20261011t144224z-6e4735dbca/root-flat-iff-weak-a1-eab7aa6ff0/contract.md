<!-- theorem-id: gmt-ch06/root.flat_iff_weak-a1 -->

## Theorem `Submission.flat_convergence_iff_weak_convergence`

For all P, m ∈ ℕ, every open U ⊆ ℝ^P and integer multiplicity T, T_j ∈ D_{m+1}(U) with sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every open W ⊂⊂ U: T_j ⇀ T in U if and only if flatDistance W (T_j) T → 0 for every open W ⊂⊂ U, where d_W(X,Y) = inf{M_W(S) + M_W(R) : X − Y = ∂R + S, R ∈ D_{m+2}(U), S ∈ D_{m+1}(U) integer multiplicity}.

Node: `root.flat_iff_weak-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325, https://github.com/ZhengyangZhang06/gmt-formalize/issues/322, https://github.com/ZhengyangZhang06/gmt-formalize/issues/334

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/806, https://github.com/ZhengyangZhang06/gmt-formalize/issues/809, https://github.com/ZhengyangZhang06/gmt-formalize/issues/814, https://github.com/ZhengyangZhang06/gmt-formalize/issues/817, https://github.com/ZhengyangZhang06/gmt-formalize/issues/819, https://github.com/ZhengyangZhang06/gmt-formalize/issues/824, https://github.com/ZhengyangZhang06/gmt-formalize/issues/826, https://github.com/ZhengyangZhang06/gmt-formalize/issues/828

## Lean problem

Declaration: `Submission.flat_convergence_iff_weak_convergence`

```lean
FlatConvergenceIffWeakConvergence
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
- Child DAG node: `root.flat_iff_weak-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, §7: definition 7.1, Theorem 7.2 and its printed proof (pp. 170–172), which uses the deformation theorem (5.3; total boundedness (1)–(3)), the localization “by 4.5(1),(2) and an argument as in 6.7(2) of Ch. 2” ((4)), and 3.13 (the series R^{(ℓ)}, S^{(ℓ)}). Book n = m + 1. The printed proof is copied below in numbered form. Points filled in for the exact Lean statement: (a) the integrality of the S produced by the deformation theorem requires ∂T integer multiplicity, which holds by 6.3 for every T in the class I of 7.1 (footnote 2 to 5.1: “if M(∂T) < ∞ then ∂T is automatically integer multiplicity if T is — see 6.3”); (b) the printed reduction (4) to currents supported in a fixed W̄ requires that the localized currents converge weakly to the localized limit, which is proved below (Step 4) for almost every localization level after passing to a subsequence; (c) the pigeonhole form of the total boundedness, which is what makes the R_r, S_r in (5) of small global mass with support in W̃; (d) for P = m + 1 (book ℓ = 0) the deformation theorem is replaced by the printed steps (27)–(37) of the proof of 5.1 with Q = T (the retraction is the identity, R = 0); for P ≤ m all currents vanish. Errata applied: in (1) the printed “Σ_{j=1}^N B_{ε,W̃}(P_j)” means the union ⋃_{j=1}^N B_{ε,W̃}(P_j); in the last paragraph “T − T_{j_ℓ}” is used with the sign convention of the Lean `flatDistance W (Tj j) T`, which concerns T_j − T = ∂R + S (replace R, S by −R, −S; negatives of integer multiplicity currents are integer multiplicity).

Sibling results used: `DeformationTheorem` (5.3), `SlicingTheorem` (§4), `BoundaryRectifiability` (6.3).

Setting. U ⊆ ℝ^P open, T, T_j ∈ D_n(U) (n = m+1) integer multiplicity, B_W := sup_j(M_W(T_j) + M_W(∂T_j)) < ∞ for all W ⊂⊂ U. d_W(X,Y) := `flatDistance W X Y` = inf{M_W(S) + M_W(R) : R ∈ D_{n+1}(U), S ∈ D_n(U) integer multiplicity, X − Y = ∂R + S}.

Preliminaries. (P1) Representation and restriction (Simon 2.7–2.9): currents of locally finite mass are X(ω) = ∫⟨ω,X⃗⟩dμ_X with μ_X(W) = M_W(X) (W open), X⌞A(ω) := ∫_A⟨ω,X⃗⟩dμ_X, M_W(X⌞A) = μ_X(W∩A), |X(ω)| ≤ M_W(X)‖ω‖ for tsupport ω ⊆ W. Mass is lower semicontinuous under weak convergence (2.14). (P2) Integer multiplicity calculus (3.2(1), 3.13): restrictions to Borel sets, integer linear combinations and M-limits (in particular M-absolutely convergent series) of integer multiplicity currents are integer multiplicity; 0 is integer multiplicity. (P3) Extension and restriction of domains: if X ∈ D_k(U) has compact support K ⊆ U, X̃(ω) := X(χω) for ω ∈ D^k(ℝ^P), with χ ∈ C_c^∞(U), 0 ≤ χ ≤ 1, χ = 1 on a neighbourhood of K, defines X̃ ∈ D_k(ℝ^P) independent of χ (X annihilates test forms vanishing near spt X); ∂X̃ = (∂X)~, M(X̃) = M(X), spt X̃ = spt X, X̃ = X on D^k(U), and X̃ = τ(M∩K,θ,ξ) is integer multiplicity if X = τ(M,θ,ξ) is (Hᵏ(M∖spt X) = 0). Conversely Y ∈ D_k(ℝ^P) restricts to Y|_U(ω) := Y(ω), ω ∈ D^k(U); Y|_U = τ(M∩U,θ,ξ) is integer multiplicity if Y is, M_W(Y|_U) = M_W(Y) for W ⊆ U, and ∂(Y|_U) = (∂Y)|_U. (P4) Integer lattice chains Σ_{F∈𝓛_n(ρ)}β_F[[F]] (β_F ∈ ℤ) are integer multiplicity with mass Σ|β_F|ρⁿ (test with forms ±φdx^α near the relative interior of a face; faces of other directions are annihilated). (P5) Approximation with control (P ≥ n): for X ∈ D_n(ℝ^P) integer multiplicity with ∂X integer multiplicity, M(X) + M(∂X) ≤ M₀, spt X ⊆ K compact, and ρ > 0, there are an integer lattice chain Pc = Σ_{F∈𝓛_n(ρ)}β_F[[F]] and integer multiplicity R, S with X − Pc = ∂R + S, M(Pc) ≤ CM₀, M(R) + M(S) ≤ CρM₀, and spt Pc ∪ spt R ∪ spt S ⊆ {dist(·,K) < 2√P ρ}: if P ≥ n+1 this is `DeformationTheorem` with ℓ := P − n ≥ 1 (after rewriting P = m+1+ℓ); if P = n it is the printed (27)–(37) of the proof of 5.1 with Q := X (2.35 gives X = θ[[ℝⁿ]] with θ ∈ BV integer valued; β_F := integer medians of θ on the cubes F ∈ 𝓛_n(ρ), Pc := Σβ_F[[F]], R := 0, S := X − Pc = Σ_F(θ−β_F)1_{F̊}[[ℝⁿ]] integer multiplicity, M(S) ≤ cρM(∂X) by Ch. 2, 2.7, M(Pc) ≤ 2M(X); β_F ≠ 0 or (θ − β_F)1_{F̊} ≠ 0 forces F̊ ∩ spt X ≠ ∅, so the supports lie within √n·ρ of K).

Proof.

0. (Trivial dimensions.) If P < n, every n- and (n+1)-covector on ℝ^P vanishes, all currents in the statement are 0, d_W(T_j,T) ≤ M_W(0) + M_W(0) = 0 (take R = S = 0), and both sides of the equivalence hold. Assume P ≥ n.

1. (“If” — printed: trivial.) Suppose d_W(T_j,T) → 0 for every W ⊂⊂ U. Let ω ∈ Dⁿ(U) and choose W ⊂⊂ U open with tsupport ω ⊆ W. Given ε > 0, for large j there are integer multiplicity R, S with T_j − T = ∂R + S and M_W(S) + M_W(R) < ε (definition of the infimum). Then |T_j(ω) − T(ω)| = |R(dω) + S(ω)| ≤ M_W(R)‖dω‖ + M_W(S)‖ω‖ ≤ ε(‖dω‖ + ‖ω‖). Hence T_j ⇀ T.

2. (“Only if” — reduction to subsequences.) Assume T_j ⇀ T. Since M_W ≤ M_{W″} for W ⊆ W″ (`massOn_mono`), d_W ≤ d_{W″}; so it suffices to treat nonempty W (if W = ∅ then M_W ≡ 0 and the decomposition R = 0, S = T_j − T, which is integer multiplicity, gives d_∅(T_j,T) = 0; if U = ∅ all currents vanish). It suffices to show: for every W ⊂⊂ U and every subsequence of (T_j) there is a further subsequence along which d_W(T_j,T) → 0 (a real sequence all of whose subsequences have subsequences tending to 0 tends to 0). Fix W ⊂⊂ U and a subsequence, still denoted T_j.

3. (Integrality of boundaries.) For each j, M_V(∂T_j) ≤ B_V < ∞ for all V ⊂⊂ U, so ∂T_j is integer multiplicity by `BoundaryRectifiability`. Similarly every integer multiplicity current of the class I of 7.1 has integer multiplicity boundary.

4. (Localization — printed (4) with the weak convergence of the localized currents.) Choose an open W′ with closure(W) ⊆ W′ ⊂⊂ U and let φ(x) := dist(x, ℝ^P∖W′) (1-Lipschitz), 2r₀ := min_{closure W} φ > 0, and A_s := {x ∈ U : φ(x) ≥ s} for s ∈ (r₀/2, r₀) (compact ⊆ W′, ⊇ closure W). (i) Measures: the functions F_j(s) := μ_{T_j}({φ ≥ s}) are nonincreasing and bounded by B_{W′}; by Helly's selection theorem a subsequence (not relabelled) converges pointwise on (0, ∞) to a nonincreasing F, which is continuous outside a countable set. (ii) Slices: apply `SlicingTheorem` to each T_j with f = φ, W′, L_W = 1, (a,b) = (r₀/2, r₀): the slices S^j_s satisfy ∫_{r₀/2}^{r₀}g_j ≤ M_{W′}(T_j) ≤ B_{W′} with g_j ≥ M_{W′}(S^j_s); by Fatou, ∫ liminf_j g_j ≤ B_{W′}, so for a.e. s, liminf_j M(S^j_s) < ∞ (spt S^j_s ⊆ {φ = s} ⊆ W′). (iii) Fix s ∈ (r₀/2,r₀) which is a continuity point of F (all but countably many s) and has liminf_j M(S^j_s) < ∞ (a.e. s), and such that every S^j_s is integer multiplicity (a.e. s, T_j integer multiplicity); such s exist (a full-measure set); pass to a subsequence with sup_j M(S^j_s) < ∞. Put T′_j := T_j⌞A_s, T′ := T⌞A_s. Then T′_j, T′ are integer multiplicity (P2), spt ⊆ A_s ⊆ W′, ∂T′_j = (∂T_j)⌞A_s − S^j_s (from `IsSlice`: T_j⌞A_s = T_j − T_j⌞{φ<s}), so sup_j(M(T′_j) + M(∂T′_j)) ≤ B_{W′} + sup_jM(S^j_s) =: M₀ < ∞, and ∂T′_j is integer multiplicity (`BoundaryRectifiability`, or P2 with Step 3 and the integrality of a.e. slice). (iv) T′_j ⇀ T′: for ω ∈ Dⁿ(U) and 0 < η < s − r₀/2, let χ_η be smooth with χ_η = 1 on {φ ≥ s}, χ_η = 0 on {φ ≤ s − η}, 0 ≤ χ_η ≤ 1 (smooth function of a mollified φ). Then |T′_j(ω) − T_j(χ_ηω)| ≤ ‖ω‖μ_{T_j}({s−η < φ < s}) ≤ ‖ω‖(F_j(s−η) − F_j(s)), and likewise |T′(ω) − T(χ_ηω)| ≤ ‖ω‖μ_T({s−η < φ < s}). Since T_j(χ_ηω) → T(χ_ηω), limsup_j|T′_j(ω) − T′(ω)| ≤ ‖ω‖[(F(s−η) − F(s)) + μ_T({s−η<φ<s})] → 0 as η ↓ 0 (continuity of F at s; continuity of the finite measure μ_T⌞W′). (v) Back to T_j: T_j − T = (T′_j − T′) + Z_j with Z_j := T_j⌞(U∖A_s) − T⌞(U∖A_s), integer multiplicity (P2) with M_W(Z_j) = 0 because W ⊆ {φ > s} and Z_j vanishes on forms supported there. Hence if T′_j − T′ = ∂R + S with R, S integer multiplicity then T_j − T = ∂R + (S + Z_j) and d_W(T_j,T) ≤ M_W(S) + M_W(R) (S + Z_j is integer multiplicity, M_W(S + Z_j) ≤ M_W(S)). So it suffices to find a subsequence with d_W(T′_j, T′) → 0, and for this we may assume spt T_j ⊆ A_s, sup_j(M(T_j) + M(∂T_j)) ≤ M₀ and T_j ⇀ T (this is printed (4)). Let W̃ be open with A_s ⊆ … ⊆ closure(W′) ⊆ W̃ ⊂⊂ U and δ := dist(closure W′, ℝ^P ∖ W̃) > 0.

5. (Total boundedness — printed (1)–(3), pigeonhole form.) Extend each T_j to ℝ^P (P3). For ρ > 0 with 2√P ρ < δ, (P5) applied to T_j (with K := closure W′) gives an integer lattice chain Pc_j^{(ρ)} = Σ_{F∈𝓛_n(ρ)}β_F[[F]] and integer multiplicity R_j^{(ρ)}, S_j^{(ρ)} with T_j − Pc_j^{(ρ)} = ∂R_j^{(ρ)} + S_j^{(ρ)}, M(Pc_j^{(ρ)}) ≤ CM₀, M(R_j^{(ρ)}) + M(S_j^{(ρ)}) ≤ CρM₀, and all supports in {dist(·, closure W′) < 2√Pρ} ⊆ W̃. The set of such chains is finite: only the finitely many faces meeting the bounded set {dist(·, closure W′) < 2√Pρ} can carry β_F ≠ 0, and |β_F|ρⁿ ≤ M(Pc) ≤ CM₀ (P4) bounds the integers β_F. Hence among infinitely many indices j, infinitely many share the same chain Pc^{(ρ)}; for two such indices j, j′, T_j − T_{j′} = ∂(R_j^{(ρ)} − R_{j′}^{(ρ)}) + (S_j^{(ρ)} − S_{j′}^{(ρ)}) with integer multiplicity terms (P2), global mass ≤ 2CρM₀ and supports in W̃.

6. (Cauchy subsequence — printed (5).) Choose ρ_r ↓ 0 with 2√Pρ_r < δ and 2Cρ_rM₀ ≤ 2^{−r}. Inductively pick infinite index sets J₁ ⊇ J₂ ⊇ ⋯ such that all j ∈ J_r share the same chain at scale ρ_r (Step 5), and j₁ < j₂ < ⋯ with j_r ∈ J_r. Then for each r, j_r, j_{r+1} ∈ J_r, so (5) T_{j_{r+1}} − T_{j_r} = ∂R_r + S_r with R_r, S_r integer multiplicity, spt R_r ∪ spt S_r ⊆ W̃, M(R_r) + M(S_r) ≤ 2^{−r}.

7. (Limit — printed last paragraph, with 3.13.) The series R^{(ℓ)} := Σ_{r≥ℓ}R_r, S^{(ℓ)} := Σ_{r≥ℓ}S_r converge absolutely in mass, so they define integer multiplicity currents (P2, 3.13) with M(R^{(ℓ)}) + M(S^{(ℓ)}) ≤ 2^{−ℓ+1} and supports in closure(W̃) ⊆ U (restrict them to U, P3). Summing (5) for r = ℓ,…,N−1: T_{j_N} − T_{j_ℓ} = ∂(Σ_{r=ℓ}^{N−1}R_r) + Σ_{r=ℓ}^{N−1}S_r; letting N → ∞ (T_{j_N} ⇀ T; mass convergence of the partial sums implies weak convergence of their boundaries) gives T − T_{j_ℓ} = ∂R^{(ℓ)} + S^{(ℓ)}, i.e. T_{j_ℓ} − T = ∂(−R^{(ℓ)}) + (−S^{(ℓ)}). Hence d_W(T_{j_ℓ},T) ≤ M_W(−S^{(ℓ)}) + M_W(−R^{(ℓ)}) ≤ 2^{−ℓ+1} → 0.

8. (Conclusion.) Steps 4–7 produce, from any subsequence, a further subsequence with d_W(T_j, T) → 0 (via Step 4(v) for the original currents). By Step 2, d_W(T_j,T) → 0 for every W ⊂⊂ U. Together with Step 1 this proves `FlatConvergenceIffWeakConvergence`.

## Key steps

1. 'If': |T_j(ω) − T(ω)| ≤ M_W(R)‖dω‖ + M_W(S)‖ω‖ for a near-optimal decomposition.
2. 'Only if': reduce to showing every subsequence has a further subsequence with d_W → 0; trivial dimensions and W = ∅ handled.
3. ∂T_j integer multiplicity by the sibling boundary rectifiability theorem.
4. Localize at a good level s of a distance function (slicing + Fatou + Helly): localized currents have bounded mass and boundary mass and converge weakly to the localized limit; the remainder has zero M_W.
5. Total boundedness via the sibling deformation theorem (or (27)–(37) of 5.1 when P = m+1): finitely many possible lattice chains, pigeonhole gives differences T_j − T_j′ = ∂R + S of small global mass with supports in W̃.
6. Extract a subsequence with T_{j_{r+1}} − T_{j_r} = ∂R_r + S_r, M(R_r) + M(S_r) ≤ 2^{−r}.
7. Sum the series (3.13): T_{j_ℓ} − T = ∂(−R^{(ℓ)}) − S^{(ℓ)}, so d_W(T_{j_ℓ}, T) ≤ 2^{1−ℓ}.

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/8796

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
