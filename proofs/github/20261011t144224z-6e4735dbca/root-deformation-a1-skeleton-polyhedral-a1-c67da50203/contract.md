<!-- theorem-id: gmt-ch06/root.deformation-a1.skeleton_polyhedral-a1 -->

## Theorem `Submission.deformation_skeleton_polyhedral`

Replacement of a skeleton current by a lattice chain (Simon, printed displays (26)–(37) of the proof of 5.1). For all m, ℓ ∈ ℕ with ℓ ≥ 1 (n := m + 1, d := n + ℓ) there is C = C(m,ℓ) ∈ [0,∞) such that for every Q ∈ D_n(ℝ^d) with M(Q) + M(∂Q) < ∞, spt Q ⊆ L_n := ⋃_F latticeFace 1 F, and the tangential property [for every face index F = (z, α), every open ball B with B ∩ L_n ⊆ latticeFace 1 F and every test n-form ω with tsupport ω ⊆ B and ω(x)(e_{α₁},…,e_{α_n}) = 0 for all x, Q(ω) = 0], there are β : LatticeFaceIndex (m+1) (m+1+ℓ) → ℝ and P, S ∈ D_n(ℝ^d) with IsLatticeChain 1 β P (P = Σ_F β_F[[F]]), Q(ω) − P(ω) = S(ω) for all ω, M(P) ≤ C M(Q), M(∂P) ≤ C M(∂Q), M(S) ≤ C M(∂Q), spt P ⊆ {dist(·, spt Q) ≤ √n}, spt ∂P ∪ spt S ⊆ {dist(·, spt ∂Q) ≤ √n} (closed thickenings), and, if Q is integer multiplicity, β_F ∈ ℤ for all F and P is integer multiplicity.

Node: `root.deformation-a1.skeleton_polyhedral-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1104

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/691, https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1228, https://github.com/ZhengyangZhang06/gmt-formalize/issues/980, https://github.com/ZhengyangZhang06/gmt-formalize/issues/687, https://github.com/ZhengyangZhang06/gmt-formalize/issues/966, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1051, https://github.com/ZhengyangZhang06/gmt-formalize/issues/946, https://github.com/ZhengyangZhang06/gmt-formalize/issues/948, https://github.com/ZhengyangZhang06/gmt-formalize/issues/847, https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1072

## Lean problem

Declaration: `Submission.deformation_skeleton_polyhedral`

```lean
∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ Q : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), Q.mass + Q.boundary.mass < ∞ → Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F → (∀ (F : LatticeFaceIndex (m + 1) (m + 1 + ℓ)) (y : Eucl (m + 1 + ℓ)) (r : ℝ), ball y r ∩ (⋃ G : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 G) ⊆ latticeFace 1 F → ∀ ω : TestFormOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) ⊆ ball y r → (∀ x, (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = 0) → Q ω = 0) → ∃ (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ) (P S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)), IsLatticeChain 1 β P ∧ (∀ ω, Q ω - P ω = S ω) ∧ P.mass ≤ C * Q.mass ∧ P.boundary.mass ≤ C * Q.boundary.mass ∧ S.mass ≤ C * Q.boundary.mass ∧ P.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.support ∧ P.boundary.support ∪ S.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.boundary.support ∧ (IsIntegerMultiplicity Q → (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity P)
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

- Parent DAG node: `root.deformation-a1`
- Child DAG node: `root.deformation-a1.skeleton_polyhedral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, §5, printed “Proof of the Deformation Theorem”, displays (26)–(37) (pp. 167–168), as in C7–C8 of the parent proof, with the tools cited there: Remark 2.35 (with the argument of the Constancy Theorem 2.34), Lemma 2.36 with Remark 2.37(1), Ch. 2, Lemma 2.7, Lemma 2.8 and Remark 2.9, and the lattice-chain facts A7 of the parent. Ch. 2, 2.7–2.9 are applied to the open unit cube Ω = (0,1)^n with centre q, outer radius R = √n/2 and δ = 1/(2√n), so that δ ∈ (0,1) for every n ≥ 1 and the inner ball B_{δR}(q) = B_{1/4}(q) lies at distance 1/4 > 0 from ∂Ω, as the cut-off argument of the printed proof of 2.8 requires; the Poincaré and cut-off estimates are carried out with these parameters in (T4). In the printed proof, display (26) — Q(ω) = Q(ω(e₁,…,e_n)dx¹∧⋯∧dxⁿ) for ω supported in a ball B_y around a point y of an open face F̊ with B_y ∩ L_n = B_y ∩ F̊ — is derived from the construction of Q; here it is the hypothesis (H3) (it is established for the deformed current by the sibling theorem deformation_onto_skeleton), and everything from (27) on is the printed argument. Errata as in the parent: book k = ℓ; supports are stated with “≤ √n”, the parent then passes to the strict bound.

Setting. n := m + 1, d := n + ℓ, ℓ ≥ 1, ℝ^d = Eucl(m+1+ℓ).
Conventions (stated here so that this proof is self-contained). For an ambient dimension D, e₁,…,e_D is the standard basis of ℝ^D, I(k,D) the set of strictly increasing multi-indices γ = (γ₁ < ⋯ < γ_k) in {1,…,D}, e_γ := (e_{γ₁},…,e_{γ_k}) and dx^γ := dx^{γ₁}∧⋯∧dx^{γ_k}. For a k-covector α (`Covector (Eucl D) k`), |α| := (Σ_γ α(e_γ)²)^{1/2} (`covectorEuclideanNorm`); for a k-form ω, ‖ω‖ := sup_x |ω(x)|; for a k-vector w (`NVector (Eucl D) k`, a linear functional on k-covectors), ⟨α, w⟩ := w(α), w^γ := w(dx^γ) and |w| := (Σ_γ (w^γ)²)^{1/2}; ‖A‖ is the operator norm of a linear map A. Coordinate fact: every k-covector satisfies α = Σ_γ α(e_γ)dx^γ (an alternating k-linear map is determined by its values on increasing tuples of basis vectors, and dx^γ(e_δ) = δ_{γδ}); hence w(α) = Σ_γ α(e_γ)w^γ and |w(α)| ≤ |α|·|w| (Cauchy–Schwarz). Push-forward of k-vectors: for a linear map A : ℝ^D → ℝ^{D′}, A_# = Λ_kA := `nVectorPushforward k A` is characterized by ⟨α, A_#w⟩ = ⟨A^#α, w⟩ with A^#α := α(A·,…,A·) (Simon 1.8–1.9); it is linear and A_#(simpleNVector τ) = simpleNVector(Aτ₁,…,Aτ_k) (Simon 1.10; SimonGMT `nVectorPushforward_simple`). Unit fact: if τ₁,…,τ_k ∈ ℝ^D are orthonormal then |simpleNVector τ| = 1, because its coordinates (simpleNVector τ)^γ = det(τ_i·e_{γ_j}) are the k×k minors of the D×k matrix with columns τ₁,…,τ_k and, by the Cauchy–Binet formula, Σ_γ det(τ_i·e_{γ_j})² = det(τ_i·τ_j) = 1; consequently, whenever `IsRectifiableTriple U k M θ ξ` holds, |ξ| = 1 H^k-a.e. on M (orientation clause). Mass M = `mass`, spt = `support`. For a face index F = (z, α) ∈ LatticeFaceIndex (m+1) (m+1+ℓ) write F also for latticeFace 1 F, and let F̊ := {x : z_i < x_i < z_i + 1 (i ∈ range α), x_i = z_i (i ∉ range α)} (relative interior), Π_F := {x : x_i = z_i (i ∉ range α)}, e_α := (e_{α₁},…,e_{α_n}), dx^α := dx^{α₁}∧⋯∧dx^{α_n} (so dx^α(e_α) = 1), Ω := (0,1)^n and ι_F : ℝ^n → Π_F, ι_F(u) := z + Σ_j u_j e_{α_j}, an affine isometry with ι_F(Ω) = F̊ and H^n⌞Π_F = ι_F#L^n. [[F]](ω) := latticeFaceAction 1 F ω = ∫_F ω(x)(e_α)dH^n(x). L_n := ⋃_F F, L_{n−1} := ⋃_F (F ∖ F̊). Hypotheses: (H1) M(Q) + M(∂Q) < ∞; (H2) spt Q ⊆ L_n; (H3) for every F, every ball B = ball y r with B ∩ L_n ⊆ F, and every test n-form ω with tsupport ω ⊆ B and ω(x)(e_α) = 0 for all x, Q(ω) = 0. (H3) is the printed (26) in ball form: by linearity it says Q(ω) = Q(ω(·)(e_α)dx^α) for every test form ω supported in such a ball, i.e. near each point of the open face F̊ the current Q only sees the tangential component of ω, which is the content of p_#(Q⌞F̊) = Q⌞F̊ in (26).

1. Geometry of the skeleton. (a) Every closed n-face of the unit cubical lattice is latticeFace 1 F for exactly one F; a bounded set meets only finitely many faces (local finiteness); hence L_n and L_{n−1} are closed, and a union of any subfamily of faces is closed. (b) The sets F̊ are pairwise disjoint and disjoint from L_{n−1} (two distinct n-faces meet in a common face of dimension < n, which lies in the relative boundaries of both), so L_n = L_{n−1} ⊔ ⨆_F F̊. (c) H^n(L_{n−1}) = 0, and for every γ ∈ I(n,d) the coordinate projection p_γ maps L_{n−1} into a countable union of affine (n−1)-planes of ℝ^n, so L^n(p_γ(L_{n−1})) = 0. (d) For y ∈ F̊ there is r > 0 with B_r(y) ∩ L_n ⊆ F̊: y does not belong to the closed set L_{n−1} ∪ ⋃_{G≠F} G (by (b)), so it has positive distance from it. Let 𝓑_F be the family of open balls B centred in F̊ with B ∩ L_n ⊆ F̊; by (d), F̊ ⊆ ⋃𝓑_F. (e) diam F = √n and M([[F]]) ≤ H^n(F) = 1 (|ω(x)(e_α)| ≤ |ω(x)|).

2. Tools.
 (T1) The sibling theorem deformation_mass_restriction applied to Q and to ∂Q (finite masses by (H1)) gives finite Borel measures μ_Q, μ_∂ with representations (μ_Q, v_Q), (μ_∂, v_∂), μ_Q(ℝ^d ∖ spt Q) = 0, μ_∂(ℝ^d ∖ spt ∂Q) = 0, restrictions Q⌞A, (∂Q)⌞A (Q⌞A(ω) = ∫_A v_Q(ω)dμ_Q) with M_W(Q⌞A) = μ_Q(W ∩ A) for open W, the uniqueness of restrictions and of representing vector measures, and integer multiplicity of Q⌞A when Q is integer multiplicity. In particular μ_Q(W) = M_W(Q), μ_Q(ℝ^d ∖ L_n) = 0 by (H2), and |Q(ω)| ≤ μ_Q(W)‖ω‖ if tsupport ω ⊆ W (same for ∂Q).
 (T2) Lemma 2.36 and Remark 2.37(1) (printed proof): if X ∈ D_n(ℝ^d) has M_W(X), M_W(∂X) < ∞ and E is closed with L^n(p_γ(E)) = 0 for all γ ∈ I(n,d), then X⌞E = 0. [Printed proof: writing ω = Σ_γ ω_γdx^γ, X(ω) = Σ_γ p_γ#(X⌞ω_γ)(dy), dy := dy¹∧⋯∧dyⁿ; for each γ the current p_γ#(X⌞ω_γ) ∈ D_n(ℝ^n) has M(∂p_γ#(X⌞ω_γ)) ≤ M_W(∂X)|ω_γ| + M_W(X)|dω_γ| < ∞ (because ∂(X⌞ω_γ)(ζ) = ∂X(ω_γζ) − X(dω_γ ∧ ζ)), so by 2.35 it is given by a BV function and p_γ#(X⌞ω_γ)⌞p_γ(E) = 0 since L^n(p_γ(E)) = 0; hence M(p_γ#(X⌞ω_γ)) ≤ M_W(X⌞(ℝ^d ∖ p_γ⁻¹p_γ(E)))|ω_γ| ≤ M_W(X⌞(ℝ^d ∖ E))|ω_γ| for spt ω ⊆ W; summing, M_W(X) ≤ cM_W(X⌞(ℝ^d ∖ E)), i.e. μ_X(W ∩ E) ≤ cμ_X(W ∖ E); taking W ↓ K for compact K ⊆ E gives μ_X(K) = 0, and inner regularity gives μ_X(E) = 0.]
 (T3) Remark 2.35 (with the argument of 2.34): if V ⊆ ℝ^n is open and Y ∈ D_n(V) with M_W(Y), M_W(∂Y) < ∞ for open W ⊂⊂ V, then there is θ ∈ BV_loc(V) with Y(g dy) = ∫ gθ dL^n for g ∈ C_c^∞(V), M_W(Y) = ∫_W|θ| and M_W(∂Y) = |Dθ|(W) for open W ⊂⊂ V. [Proof: |Y(g dy)| ≤ M_W(Y)‖g‖, and for g ∈ C_c^∞(W), Y(∂_jg dy) = ∂Y((−1)^{j−1}g dy^{1..ĵ..n}) so |Y(∂_jg dy)| ≤ M_W(∂Y)‖g‖. With θ^{(σ)}(x) := Y(ϕ_σ(x − ·)dy) (ϕ_σ a mollifier), θ^{(σ)} is smooth on V_σ := {dist(·, ∂V) > σ}, ∫_W|θ^{(σ)}| ≤ M_{W_σ}(Y) and ∫_W|Dθ^{(σ)}| ≤ M_{W_σ}(∂Y) for W ⊂⊂ V, W_σ the σ-neighbourhood; by the BV compactness theorem (Ch. 2, 2.6) θ^{(σ_k)} → θ in L¹_loc(V) with θ ∈ BV_loc(V), and Y(g dy) = lim ∫gθ^{(σ_k)} = ∫gθ (ϕ_σ * g → g in C_c^∞). Then M_W(Y) = sup{∫gθ : |g| ≤ 1, spt g ⊆ W} = ∫_W|θ|, and since every (n−1)-form is Σ_j(−1)^{j−1}a_j dy^{1..ĵ..n} with d of it = (div a)dy and |form| = |a|, M_W(∂Y) = sup{∫θ div a : a ∈ C_c^∞(W;ℝ^n), |a| ≤ 1} = |Dθ|(W) (Ch. 2, 2.4; smooth and Lipschitz test fields give the same supremum by mollification).]
 (T4) Ch. 2, Lemma 2.7, Lemma 2.8 and Remark 2.9 for the open unit cube Ω = (0,1)^n, with the parameters R := √n/2 and δ := 1/(2√n). Statement: let q := (1/2,…,1/2) be the centre of Ω, let u ∈ BV(Ω) (u ∈ L¹(Ω) and |Du|(Ω) < ∞, where |Du| is the total variation measure of Ch. 2, 2.2–2.4) and let β ∈ ℝ be a median of u, i.e. L^n{x ∈ Ω : u(x) ≥ β} ≥ 1/2 and L^n{x ∈ Ω : u(x) ≤ β} ≥ 1/2. Then (T4.i) ∫_Ω|u − β| dL^n ≤ c₁|Du|(Ω), and (T4.ii) the function w := (u − β)1_Ω (extended by 0 outside Ω) belongs to BV(ℝ^n) and |Dw|(ℝ^n) ≤ c₂|Du|(Ω), where c₁ = c₁(n) and c₂ = c₂(n) are given below. Proof:
  (a) The hypotheses of 2.7 and 2.8, with a strictly interior inner ball. Ω is bounded, open and convex. Take as centre the point q (the point ξ of 2.7), R = √n/2 and δ = 1/(2√n); then 0 < δ ≤ 1/2 < 1 for every n = m + 1 ≥ 1 (for n = 1: R = δ = 1/2), and δR = 1/4. Outer ball: if x ∈ Ω then |x_i − 1/2| < 1/2 for every i, so |x − q| < √n/2 = R; thus Ω ⊆ B_R(q). Inner ball: if |x − q| < 1/4 then |x_i − 1/2| < 1/4 < 1/2 for every i, so x ∈ Ω; thus B_{δR}(q) = B_{1/4}(q) ⊆ Ω. Strict interiority: if |x − q| ≤ 1/4 and y ∉ Ω, then some coordinate satisfies y_i ∉ (0,1), i.e. |y_i − 1/2| ≥ 1/2, while |x_i − 1/2| ≤ 1/4, so |x − y| ≥ |y_i − x_i| ≥ 1/4; hence d_Ω(x) := dist(x, ℝ^n ∖ Ω) ≥ 1/4 for every x in the closed ball B̄_{1/4}(q), and dist(B_{δR}(q), ∂Ω) = 1/4 > 0 (with equality at the centres of the facets). Finally the median condition is condition (⋆) of 2.7 with ϑ := 1/2 ∈ (0,1), because L^n(Ω) = 1: min{L^n{u ≥ β}, L^n{u ≤ β}} ≥ 1/2 = ϑL^n(Ω). (Both requirements are used: 2.7 and 2.8 are stated for δ ∈ (0,1), and the cut-off argument (c) below uses display (1) only at points x with d_Ω(x) < dist(B_{δR}(q), ∂Ω), so this distance must be positive.)
  (b) Poincaré inequality: Lemma 2.7 with U := Ω, centre q and R, δ, ϑ as in (a) gives ∫_Ω|u − β| ≤ C(ϑ, δ, n)R|Du|(Ω) with a constant depending only on n. The printed proof of 2.7, written out in these parameters with an explicit constant: for 0 < ε ≤ 1/4 let W_ε := (ε, 1 − ε)^n, a convex open set whose closure lies in Ω, with diam W_ε ≤ √n and L^n(W_ε) = (1 − 2ε)^n ≥ 2^{−n}. For 0 < σ < ε the mollified function u_σ := ϕ_σ * u (Ch. 2, §2; on a neighbourhood of the closure of W_ε only values of u on Ω enter) is smooth there, and ∫_{W_ε}|Du_σ| ≤ |Du|(Ω): for every C¹ vector field g with compact support in W_ε and |g| ≤ 1, ∫u_σ div g = ∫u div(ϕ_σ * g) ≤ |Du|(Ω), because ϕ_σ is symmetric and ϕ_σ * g is a smooth field with compact support in Ω and |ϕ_σ * g| ≤ 1. The Poincaré inequality for smooth functions on bounded convex domains ([GT01], Lemma 7.16 and (7.45) with p = 1 and S = W_ε) gives ∫_{W_ε}|u_σ − (u_σ)_{W_ε}| ≤ K_n∫_{W_ε}|Du_σ| ≤ K_n|Du|(Ω), where f_W := L^n(W)⁻¹∫_W f denotes a mean value and K_n := (2^nω_n)^{1−1/n}n^{n/2} ≥ (ω_n/L^n(W_ε))^{1−1/n}(diam W_ε)^n. Letting σ ↓ 0 (u_σ → u in L¹(W_ε), Ch. 2, 2.5) gives ∫_{W_ε}|u − u_{W_ε}| ≤ K_n|Du|(Ω); letting ε ↓ 0 (u ∈ L¹(Ω), so u_{W_ε} → u_Ω, |u_{W_ε}| ≤ 2^n∫_Ω|u|, and dominated convergence applies) gives ∫_Ω|u − u_Ω| ≤ K_n|Du|(Ω). Passage from the mean to the median (this is where (⋆) enters): if u_Ω ≤ β, then |u − u_Ω| ≥ β − u_Ω on {u ≥ β}, a set of measure ≥ 1/2, so β − u_Ω ≤ 2∫_Ω|u − u_Ω|; if u_Ω ≥ β, the same bound for u_Ω − β follows using {u ≤ β}. Hence ∫_Ω|u − β| ≤ ∫_Ω|u − u_Ω| + |u_Ω − β| ≤ 3K_n|Du|(Ω), i.e. (T4.i) holds with c₁ := 3K_n.
  (c) Cut-off estimate: the printed proof of Lemma 2.8 (displays (1)–(5)), carried out in the original coordinates with centre q, outer radius R = √n/2 and inner radius δR = 1/4. Let v := u − β on Ω (so v ∈ BV(Ω) and |Dv| = |Du|). On ℝ^n the function d_Ω of (a) is 1-Lipschitz, vanishes off Ω, and equals min_i min{x_i, 1 − x_i} on Ω; hence it is concave on Ω (a minimum of affine functions), and at a.e. x ∈ Ω (off the null set where two of these 2n affine functions coincide) it is differentiable with Dd_Ω(x) ∈ {±e₁,…,±e_n}, so |Dd_Ω(x)| = 1.
   (1) For a.e. x ∈ Ω with d_Ω(x) < 1/4: (x − q)·Dd_Ω(x) ≤ −1/4. [Printed argument: y := q − (1/4)Dd_Ω(x) satisfies |y − q| = 1/4, so d_Ω(y) ≥ 1/4 > d_Ω(x) by (a); concavity gives d_Ω(x + t(y − x)) ≥ (1 − t)d_Ω(x) + t d_Ω(y) ≥ d_Ω(x) for t ∈ [0,1], hence Dd_Ω(x)·(y − x) ≥ 0, i.e. (q − x)·Dd_Ω(x) ≥ (1/4)|Dd_Ω(x)|² = 1/4. Directly for the cube: if d_Ω(x) = x_i < 1/4 then Dd_Ω(x) = e_i and (x − q)·e_i = x_i − 1/2 < −1/4; if d_Ω(x) = 1 − x_i < 1/4 then Dd_Ω(x) = −e_i and (x − q)·(−e_i) = 1/2 − x_i < −1/4.]
   (2) Fix ε with 0 < ε < 1/4 = dist(B_{δR}(q), ∂Ω) (such ε exist because this distance is positive, by (a)), let h_ε : ℝ → [0,1] be a nondecreasing C¹ function with h_ε = 0 on (−∞, ε/2] and h_ε = 1 on [ε, ∞), and put ψ_ε := h_ε∘d_Ω. Then ψ_ε is Lipschitz, 0 ≤ ψ_ε ≤ 1, ψ_ε = 0 outside the compact set {x : d_Ω(x) ≥ ε/2} ⊆ Ω, ψ_ε = 1 on {d_Ω ≥ ε}, and ψ_ε → 1_Ω pointwise as ε ↓ 0.
   (3) For a.e. x ∈ ℝ^n, Dψ_ε(x) = h_ε′(d_Ω(x))Dd_Ω(x), which vanishes unless ε/2 < d_Ω(x) < ε; at such x, d_Ω(x) < ε < 1/4, so by (1), (x − q)·Dψ_ε(x) = h_ε′(d_Ω(x))(x − q)·Dd_Ω(x) ≤ −(1/4)h_ε′(d_Ω(x)) = −(1/4)|Dψ_ε(x)|. Hence (1/4)|Dψ_ε(x)| ≤ −(x − q)·Dψ_ε(x) for a.e. x ∈ ℝ^n.
   (4) ψ_εv (extended by 0 outside Ω) belongs to BV(ℝ^n) and |D(ψ_εv)|(ℝ^n) ≤ ∫_Ω|Dψ_ε||v| dL^n + ∫_Ωψ_ε d|Dv|: for g ∈ C¹_c(ℝ^n;ℝ^n) with |g| ≤ 1, ∫ψ_εv div g = ∫_Ωv div(ψ_εg) − ∫_Ωv Dψ_ε·g (div(ψ_εg) = ψ_ε div g + Dψ_ε·g a.e.), and ψ_εg is a Lipschitz field with compact support in Ω and |ψ_εg| ≤ ψ_ε, so |∫_Ωv div(ψ_εg)| ≤ ∫_Ωψ_ε d|Dv| by the representation 2.2 of Dv (valid for compactly supported Lipschitz fields by mollifying them, as in 2.4).
   (5) The field x ↦ (x − q)ψ_ε(x) is Lipschitz with compact support in Ω and has length < R = √n/2 there (Ω ⊆ B_R(q)), and div((x − q)ψ_ε) = nψ_ε + (x − q)·Dψ_ε a.e.; hence, by (3) and the definition 2.4 of |D|v||(Ω),
    (1/4)∫_Ω|Dψ_ε||v| ≤ −∫_Ω(x − q)·Dψ_ε|v| = n∫_Ωψ_ε|v| − ∫_Ω|v| div((x − q)ψ_ε) ≤ n∫_Ω|v| + R|D|v||(Ω) ≤ n∫_Ω|v| + (√n/2)|Dv|(Ω),
    where |D|v||(Ω) ≤ |Dv|(Ω): for W ⊂⊂ Ω and small σ, the mollified functions satisfy |D|v_σ|| ≤ |Dv_σ| a.e. and ∫_W|Dv_σ| ≤ |Dv|(Ω) (as in (b)), while |v_σ| → |v| in L¹(W) gives |D|v||(W) ≤ liminf_σ∫_W|D|v_σ|| (2.5); take the supremum over W.
   Combining (4) and (5): |D(ψ_εv)|(ℝ^n) ≤ 4n∫_Ω|v| + (2√n + 1)|Dv|(Ω) for every ε ∈ (0, 1/4). As ε ↓ 0, ψ_εv → v1_Ω = w in L¹(ℝ^n) (dominated convergence), and the total variation on ℝ^n, a supremum of the L¹-continuous linear functionals f ↦ ∫f div g, is lower semicontinuous under L¹ convergence; hence w ∈ BV(ℝ^n) and |Dw|(ℝ^n) ≤ 4n∫_Ω|v| + (2√n + 1)|Dv|(Ω). This is Lemma 2.8 for w, in the printed form C(∫_Ω|Dv| + R⁻¹∫_Ω|v|).
  (d) Remark 2.9 (combination of 2.7 and 2.8): by (b), ∫_Ω|v| = ∫_Ω|u − β| ≤ c₁|Du|(Ω), and |Dv| = |Du|, so |Dw|(ℝ^n) ≤ (4nc₁ + 2√n + 1)|Du|(Ω); i.e. (T4.ii) holds with c₂ := 4nc₁ + 2√n + 1. In Step 5, (T4) is applied with u := θ_F, and c := max{c₁, c₂} depends only on n.
 (T5) Lattice chains (parent A7). For any β : LatticeFaceIndex (m+1) (m+1+ℓ) → ℝ, P(ω) := Σ_F β_F[[F]](ω) has only finitely many nonzero terms for each test form ω (local finiteness, 1(a)), |P(ω)| ≤ (Σ_{F∩tsupport ω≠∅}|β_F|)‖ω‖, so P is linear and sequentially continuous: P ∈ GeometricCurrentOn univ (m+1); the tsum of a finitely supported family equals its finite sum, so IsLatticeChain 1 β P. If every β_F ∈ ℤ then P = τ(M_P, θ_P, ξ_P) with M_P := ⋃_{β_F≠0}F̊, θ_P := |β_F| and ξ_P := sign(β_F)·simpleNVector e_α on F̊ (the relative boundaries are H^n-null by 1(c)): M_P is Borel and countably n-rectifiable (contained in countably many n-planes), θ_P is locally integrable (local finiteness), and at every x ∈ F̊ the weighted approximate tangent space of (M_P, θ_P) is span e_α (near x the set M_P coincides with the open subset F̊ of the plane Π_F and θ_P is constant, so the blow-ups converge to θ_P(x)H^n⌞span e_α), with e_α orthonormal; so P is integer multiplicity. Also spt P ⊆ ⋃{F : β_F ≠ 0} (P vanishes on the open complement of this closed set).

3. Q lives on the open faces (printed (33)). By 1(c), (T2) applies to Q and E := L_{n−1}: Q⌞L_{n−1} = 0, i.e. μ_Q(L_{n−1}) = 0. With μ_Q(ℝ^d ∖ L_n) = 0 and 1(b), μ_Q is concentrated on ⨆_F F̊, and for every test form ω, Q(ω) = ∫ v_Q(ω)dμ_Q = Σ_F (Q⌞F̊)(ω), only the finitely many F meeting tsupport ω contributing; also Σ_F μ_Q(F̊) ≤ μ_Q(ℝ^d) = M(Q).

4. The current on one open face (printed (26)–(28)). Fix F.
 (a) For B ∈ 𝓑_F and a test form ω with tsupport ω ⊆ B: Q(ω) = Q(ω^α), ω^α(x) := ω(x)(e_α)dx^α (a test form supported in B), by (H3) applied to ω − ω^α, whose value on e_α vanishes (ω^α(x)(e_α) = ω(x)(e_α)).
 (b) For B ∈ 𝓑_F and g ∈ C_c^∞(B): Q(g dx^α) = ∫ g·v_Q(dx^α)dμ_Q depends only on g|_{F̊}, because μ_Q(B ∖ F̊) ≤ μ_Q(ℝ^d ∖ L_n) + μ_Q(L_{n−1}) = 0 (B ∩ L_n ⊆ F̊).
 (c) Extensions. For g ∈ C_c^∞(Ω) let ĝ(x) := g(ι_F⁻¹(p_F(x)))χ(x − p_F(x)), where p_F is the orthogonal projection onto Π_F and χ is a smooth function of the normal coordinates with 0 ≤ χ ≤ 1, χ(0) = 1, supported in the ball of radius ϱ; for ϱ small the support of ĝ lies in the ϱ-tube around the compact set ι_F(spt g) ⊆ F̊ and inside ⋃𝓑_F (an open set containing F̊). If ĝ₁, ĝ₂ are two smooth compactly supported functions with supports in ⋃𝓑_F and ĝ₁ = ĝ₂ on F̊, then, using a smooth partition of unity subordinate to finitely many balls of 𝓑_F covering the support of ĝ₁ − ĝ₂, (b) gives Q(ĝ₁dx^α) = Q(ĝ₂dx^α). Define Y_F(g du¹∧⋯∧duⁿ) := Q(ĝ dx^α); by the above, Y_F does not depend on ϱ, χ. Y_F is linear and |Y_F(g du)| ≤ μ_Q(tube)‖g‖; as ϱ ↓ 0 the tubes decrease to ι_F(spt g), so |Y_F(g du)| ≤ μ_Q(ι_F(W))‖g‖ whenever spt g ⊆ W ⊆ Ω; in particular Y_F is sequentially continuous: Y_F ∈ D_n(Ω), and M_W(Y_F) ≤ μ_Q(ι_F(W)) for open W ⊆ Ω.
 (d) Boundary. Let φ = Σ_{i=1}^n g_i du^{1..î..n} be an (n−1)-form on Ω (g_i ∈ C_c^∞(Ω)) and φ̂ := Σ_i ĝ_i dx^{α∖α_i} (with the same χ, ϱ for all i), a test (n−1)-form on ℝ^d supported in ⋃𝓑_F with |φ̂| ≤ |φ∘ι_F⁻¹∘p_F|. Then ∂Q(φ̂) = Q(dφ̂) = Q((dφ̂)^α) by (a) (through a partition of unity subordinate to balls of 𝓑_F), and (dφ̂)(x)(e_α) = Σ_i(−1)^{i−1}∂_{α_i}ĝ_i(x), which on F̊ equals (Σ_i(−1)^{i−1}∂_ig_i)(ι_F⁻¹x) (tangential derivatives of ĝ_i on Π_F are those of g_i); so by (c), ∂Q(φ̂) = Y_F(dφ) = ∂Y_F(φ). Hence |∂Y_F(φ)| ≤ μ_∂(tube)‖φ‖, and letting ϱ ↓ 0, M_W(∂Y_F) ≤ μ_∂(ι_F(W)) for open W ⊆ Ω.
 (e) By (T3) on V := Ω: Y_F(g du) = ∫_Ωgθ_F dL^n with θ_F ∈ BV_loc(Ω), ∫_W|θ_F| = M_W(Y_F) ≤ μ_Q(ι_F(W)) and |Dθ_F|(W) = M_W(∂Y_F) ≤ μ_∂(ι_F(W)); letting W ↑ Ω: ∫_Ω|θ_F| ≤ μ_Q(F̊) and |Dθ_F|(Ω) ≤ μ_∂(F̊). So θ_F ∈ BV(Ω) (printed (28)).
 (f) Printed (27): (Q⌞F̊)(ω) = ∫_Ωθ_F(u)ω(ι_F(u))(e_α)du for every test n-form ω. For ω supported in some B ∈ 𝓑_F: (Q⌞F̊)(ω) = Q(ω) (μ_Q(B ∖ F̊) = 0) = Q(ω^α) by (a) = Y_F(ω(ι_F(·))(e_α)du) (by (c), as ĝ := ω(·)(e_α) is an admissible extension of g := ω(ι_F(·))(e_α) after multiplying by a cut-off equal to 1 near F̊ ∩ spt ω; here g ∈ C_c^∞(Ω), its support being contained in the compact set ι_F⁻¹(tsupport ω ∩ Π_F) ⊆ ι_F⁻¹(B ∩ Π_F) ⊆ ι_F⁻¹(F̊) = Ω, because B ∩ Π_F ⊆ B ∩ L_n ⊆ F̊ — indeed Π_F ⊆ L_n, a point x ∈ Π_F lying in latticeFace 1 (z′, α) with z′_i := ⌊x_i⌋ for i ∈ range α and z′_i := z_i otherwise) = ∫θ_Fω(ι_F(u))(e_α)du. Thus the vector measures (v_Q)·μ_Q⌞F̊ and θ_F∘ι_F⁻¹·simpleNVector(e_α)·H^n⌞F̊ (both of finite total variation) agree on test forms supported in balls of 𝓑_F. For a ball B ∈ 𝓑_F and a covector α′, the two finite signed measures A ↦ ∫_A v_Q(α′)dμ_Q⌞F̊ and A ↦ ∫_A (θ_F∘ι_F⁻¹)α′(e_α)dH^n⌞F̊ on the Borel subsets of B therefore agree on C_c^∞(B) (test forms φα′), hence on C_c(B) (mollification and dominated convergence), on compact subsets of B (decreasing continuous approximations of indicators) and on all Borel subsets of B (compact sets form a π-system generating the Borel σ-algebra of B, and the sets of agreement form a Dynkin system; Dynkin's π–λ theorem). Since countably many balls of 𝓑_F cover F̊ (Lindelöf) and both vector measures are concentrated on F̊, they are equal, which is (27).

5. Medians and the face estimates (printed (29)–(32)). For each F let β_F := sup{t : L^n{u ∈ Ω : θ_F(u) ≥ t} ≥ 1/2}. Since L^n(Ω) = 1 and θ_F ∈ L¹(Ω), β_F is finite, and by monotone continuity of measure L^n{θ_F ≥ β_F} ≥ 1/2 and L^n{θ_F ≤ β_F} ≥ 1/2 (printed (31)); if θ_F is integer valued a.e. then t ↦ L^n{θ_F ≥ t} is constant on each interval (j, j+1], j ∈ ℤ, so β_F ∈ ℤ; if θ_F = 0 a.e. then β_F = 0. Let D_F := Q⌞F̊ − β_F[[F]]; by (27), D_F(ω) = ∫_Ωw_F(u)ω(ι_F(u))(e_α)du with w_F := θ_F − β_F (printed (29)). By (T4) applied to u := θ_F ∈ BV(Ω) (4(e)) and its median β_F, with c := max{c₁, c₂} = c(n):
 M(D_F) ≤ ∫_Ω|w_F| ≤ c|Dθ_F|(Ω) ≤ cμ_∂(F̊)  (by (T4.i)).
 For a test (n−1)-form φ on ℝ^d, ∂D_F(φ) = D_F(dφ) = ∫_{ℝ^n}(w_F1_Ω)(u)·div G(u)du with G_i(u) := (−1)^{i−1}φ(ι_F(u))(e_{α∖α_i}) (because (dφ)(ι_F(u))(e_α) = div G(u)), and |G(u)| ≤ |φ(ι_F(u))|; hence (printed (30), (32))
 M(∂D_F) ≤ |D(w_F1_Ω)|(ℝ^n) ≤ c|Dθ_F|(Ω) ≤ cμ_∂(F̊)  (by (T4.ii)).

6. The chain P and the remainder S (printed (34)–(37)). Let P := Σ_Fβ_F[[F]] as in (T5) (so IsLatticeChain 1 β P) and S(ω) := Q(ω) − P(ω) (a current: difference of two currents). By Step 3, for every test form ω, S(ω) = Σ_F D_F(ω) and ∂S(φ) = Σ_F ∂D_F(φ), with finitely many nonzero terms. Hence for admissible ω (|ω| ≤ 1): S(ω) ≤ Σ_F M(D_F) ≤ cΣ_Fμ_∂(F̊) ≤ cμ_∂(ℝ^d) = cM(∂Q) (the F̊ are disjoint), i.e. M(S) ≤ cM(∂Q); likewise M(∂S) ≤ cM(∂Q), and since ∂P = ∂Q − ∂S, M(∂P) ≤ (1 + c)M(∂Q) (37). If β_F > 0 then ∫_Ω|θ_F| ≥ β_F L^n{θ_F ≥ β_F} ≥ β_F/2, and similarly if β_F < 0, so |β_F| ≤ 2∫_Ω|θ_F| ≤ 2μ_Q(F̊) (35); hence for admissible ω, P(ω) ≤ Σ_F|β_F|·M([[F]]) ≤ 2Σ_Fμ_Q(F̊) ≤ 2M(Q), i.e. M(P) ≤ 2M(Q) (36).

7. Supports. (a) If F ∩ spt Q = ∅ then μ_Q(F̊) = 0, so θ_F = 0 a.e. by 4(e) and β_F = 0. Hence spt P ⊆ ⋃{F : β_F ≠ 0} ⊆ ⋃{F : F ∩ spt Q ≠ ∅} ⊆ {x : dist(x, spt Q) ≤ √n} = cthickening √n (spt Q) (diam F = √n). (b) If F ∩ spt ∂Q = ∅ then μ_∂(F̊) = 0, so |Dθ_F|(Ω) = 0 by 4(e); a BV function with vanishing derivative on the connected open set Ω is a.e. equal to a constant κ (its mollifications have zero gradient), the median of an a.e. constant function is that constant, so β_F = κ and D_F = 0. Hence S = Σ_F D_F vanishes on the open complement of the closed set ⋃{F : F ∩ spt ∂Q ≠ ∅}, so spt S ⊆ cthickening √n (spt ∂Q); and spt ∂P ⊆ spt ∂Q ∪ spt ∂S ⊆ spt ∂Q ∪ spt S ⊆ cthickening √n (spt ∂Q) (∂P = ∂Q − ∂S; a current vanishing on an open set has vanishing boundary there).

8. Integrality. Suppose Q is integer multiplicity. By (T1) (deformation_mass_restriction applied to Q with A := F̊), Q⌞F̊ is integer multiplicity, say Q⌞F̊ = τ(M′, θ′, ξ′) with IsRectifiableTriple univ n M′ θ′ ξ′ and θ′(x) ∈ {1,2,…} for x ∈ M′. Since |ξ′| = 1 H^n-a.e. on M′ (unit fact) and θ′ is integrable on M′ ∩ K for compact K, (H^n⌞M′, θ′ξ′) is a measure representation of Q⌞F̊ (the integrands θ′ξ′(ω) are integrable and integrate to (Q⌞F̊)(ω)); by (27), so is (H^n⌞F̊, (θ_F∘ι_F⁻¹)·simpleNVector e_α). By the uniqueness conjunct of deformation_mass_restriction applied to X := Q⌞F̊ (which has finite mass μ_Q(F̊)), both representations have the same integrals over bounded Borel sets as the canonical one, hence as each other: for every bounded Borel set A and every covector α′, ∫_A θ′ξ′(α′)1_{M′}dH^n = ∫_A (θ_F∘ι_F⁻¹)α′(e_α)1_{F̊}dH^n. Both integrands are integrable on bounded sets with respect to the σ-finite measure λ := H^n⌞(M′ ∪ F̊) (H^n⌞M′ is locally finite because θ′ ≥ 1 is locally integrable), and two such functions with equal integrals over all bounded Borel sets agree λ-a.e. (apply the equality to the sets B_j(0) ∩ {±(difference) > 0}, after replacing the functions by λ-a.e. equal Borel functions). With α′ = dx^γ for every γ ∈ I(n,d) (coordinate fact): θ′ξ′1_{M′} = (θ_F∘ι_F⁻¹)·simpleNVector(e_α)·1_{F̊} λ-a.e. Taking Euclidean norms (|ξ′| = 1 a.e. on M′, |simpleNVector e_α| = 1): θ′1_{M′} = |θ_F∘ι_F⁻¹|1_{F̊} λ-a.e., so |θ_F∘ι_F⁻¹| ∈ ℕ H^n-a.e. on F̊. Hence θ_F is a.e. integer valued and β_F ∈ ℤ by Step 5, for every F; by (T5), P is integer multiplicity.

9. Conclusion. With C := max{2, 1 + c} (c = max{c₁, c₂} = c(n) from (T4) and Step 5), β, P and S satisfy IsLatticeChain 1 β P, Q(ω) − P(ω) = S(ω) for all ω, M(P) ≤ CM(Q), M(∂P) ≤ CM(∂Q), M(S) ≤ CM(∂Q), spt P ⊆ cthickening √n (spt Q), spt ∂P ∪ spt S ⊆ cthickening √n (spt ∂Q), and, if Q is integer multiplicity, β_F ∈ ℤ for all F and P is integer multiplicity. ∎

## Key steps

1. Geometry of L_n: local finiteness, disjoint open faces, H^n(L_{n−1}) = 0, balls meeting L_n only in one open face.
2. Q⌞L_{n−1} = 0 by 2.36/2.37(1); Q = Σ_F Q⌞F̊ (printed (33)).
3. Near an open face, Q(ω) = Q(ω(e_α)dx^α) (hypothesis = printed (26)) and Q depends only on values on F̊; this defines a top-dimensional current Y_F on (0,1)^n with M(Y_F) ≤ μ_Q(F̊), M(∂Y_F) ≤ μ_∂Q(F̊).
4. 2.35: Y_F = θ_F with θ_F ∈ BV((0,1)^n); identification (27)–(28).
5. Ch. 2, 2.7–2.9 on Ω = (0,1)^n with centre q, R = √n/2 and δ = 1/(2√n) ∈ (0,1) (δR = 1/4; inner ball B_{1/4}(q) at distance 1/4 > 0 from ∂Ω), ϑ = 1/2: Poincaré inequality ∫_Ω|u − β| ≤ c₁|Du|(Ω) for a median β (convex inner cubes, mollification, smooth Poincaré, mean to median), and the cut-off estimate of the printed proof of 2.8 (cut-offs at levels ε < 1/4) giving |D((u − β)1_Ω)|(ℝ^n) ≤ c₂|Du|(Ω).
6. Integer-friendly medians β_F of θ_F; with c = max{c₁, c₂}: M(Q⌞F̊ − β_F[[F]]), M(∂(Q⌞F̊ − β_F[[F]])) ≤ cμ_∂Q(F̊) (printed (29)–(32)).
7. Sum over faces: M(Q − P), M(∂Q − ∂P) ≤ cM(∂Q), |β_F| ≤ 2∫|θ_F|, M(P) ≤ 2M(Q), M(∂P) ≤ (1+c)M(∂Q) (printed (34)–(37)).
8. Supports within distance √n of spt Q resp. spt ∂Q; integrality of θ_F, β_F and P when Q is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (all byte-identical)`
- `rg -n '^def (latticeFace|latticeFaceAction|IsLatticeChain|DeformationTheorem|IsRestriction|IsMeasureRepresentation)' project/GMT/Ch06/Contract.lean (lines 107, 115, 164, 171, 177, 274)`
- `python3 over dag.json: lean_name of all 86 nodes vs the nine proposed deformation_* names (no collision; only deformation_theorem, the selected node, is reserved)`
- `rg -n 'deformation_(retraction|good_center|mass_restriction|im_completeness|im_pushforward_limit|onto_skeleton|skeleton_polyhedral|im_combination|dilation)' project lake-packages-25730c7c/simongmt (no match)`
- `python3 over nodes/root-deformation-a1/decomposition-audit-v1.json (only skeleton_polyhedral natural_proof_acceptable = false; required change: R = √n/2, δ = 1/(2√n))`
- `rg -il 'poincar' mathlib/Mathlib (curve integrals, Lie algebras, dynamics, Poincaré conjecture only: no BV Poincaré inequality on convex domains)`
- `rg -l 'BoundedVariationOn|eVariationOn' mathlib/Mathlib (one-dimensional bounded variation only)`
- `rg -l 'Sobolev|GagliardoNirenberg|gagliardo' mathlib/Mathlib; rg -n '^theorem [a-zA-Z_.]*(lintegral_pow_le|eLpNorm_le_eLpNorm_fderiv)' mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean (Gagliardo–Nirenberg–Sobolev for compactly supported C¹ maps only)`
- `rg -n 'theorem (cthickening_subset_thickening'|cthickening_cthickening_subset|mem_thickening_iff) ' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean (lines 143, 261, 638)`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib (Topology/MetricSpace/Lipschitz.lean:308, McShane extension)`
- `sed -n '440,780p' book/chapter-02.txt (Simon Ch. 2, 2.1–2.9: 2.7 assumes δ ∈ (0,1) and B_{δR}(ξ) ⊂ U ⊂ B_R(ξ); the proof of 2.8 uses display (1) only where d(x) < dist(B_δ(0), ∂U))`
- `sed -n '560,720p;1780,1920p' book/chapter-06.txt (2.34–2.37 and printed displays (18)–(37) of the proof of 5.1)`
- `python3 -I: validate_lean_statement (verifier/lean_contract.py) on the nine lean_statements (all valid and unchanged)`
- `lake env lean Scratch/V2_NC_<key>.lean for the nine keys: `theorem _root_.HumanizeNodeComparator.target : (stmt) := by sorry` in the contract scope (all exit 0; only the expected sorry warning)`
- `lake env lean Scratch/V2_Assembly.lean (assembly : SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → Stmt_onto_skeleton → Stmt_skeleton_polyhedral → Stmt_im_combination → Stmt_dilation → DeformationTheorem; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/deform_check/Scratch/V2_Assembly.lean`
- `/tmp/deform_check/Scratch/V2_NC_skeleton_polyhedral.lean`
- `/tmp/deform_v2/logs/assembly.log`
- `/tmp/deform_v2/logs/nc_skeleton_polyhedral.log`

Pinned revisions confirmed and the frozen contract is byte-identical to the snapshot (Submission = Contract), so the nine v1 interfaces remain valid. None of the nine bare names collides with a DAG reservation or with a declaration in the project or SimonGMT sources. All nine statements pass validate_lean_statement and elaborate in the exact comparator NodeChallenge scope. The parent assembly re-derives DeformationTheorem from onto_skeleton, skeleton_polyhedral, im_combination and dilation plus SlicingTheorem and LipschitzPushforwardIntegerMultiplicity, with axioms [propext, Classical.choice, Quot.sound]. No Matrix/IsUnit construction occurs. The pinned Mathlib has no multi-dimensional BV Poincaré inequality or BV cut-off/extension lemma (only one-dimensional BoundedVariationOn and the compact-support Gagliardo–Nirenberg–Sobolev inequality), so (T4) of deformation_skeleton_polyhedral is proved from Simon Ch. 2, 2.7–2.9 and [GT01, (7.45)]. Simon's printed 2.7 requires δ ∈ (0,1), and his proof of 2.8 needs the inner ball at positive distance from ∂U. The corrected parameters R = √n/2, δ = 1/(2√n) (δR = 1/4, distance 1/4) meet both requirements for every n ≥ 1, as the revised (T4) verifies explicitly.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
