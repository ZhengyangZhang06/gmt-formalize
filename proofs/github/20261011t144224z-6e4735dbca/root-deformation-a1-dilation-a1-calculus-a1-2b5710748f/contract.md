<!-- theorem-id: gmt-ch06/root.deformation-a1.dilation-a1.calculus-a1 -->

## Theorem `Submission.deformation_dilation_calculus`

Dilation calculus on ℝ^N (Simon Ch. 6, 2.23 and 2.24(1) for η_ρ(x) = ρx). Let N ∈ ℕ, ρ > 0 and k ∈ ℕ. Test forms are elements of TestFormOn univ (C^∞, compact support) and currents are elements of GeometricCurrentOn univ, on ℝ^N = Eucl N. Then: (1) for every test k-form ω there is a test k-form η with η(x) = ρ^k ω(ρx) for all x; (2) for every X ∈ D_k(ℝ^N) there is Y ∈ D_k(ℝ^N) with Y(ω) = X(η) for all test k-forms ω, η satisfying η(x) = ρ^k ω(ρx) for all x; (3) if X, Y ∈ D_{k+1}(ℝ^N) satisfy Y(ω) = X(η) for all test (k+1)-forms ω, η with η(x) = ρ^{k+1} ω(ρx) for all x, then ∂Y(ω) = ∂X(η) for all test k-forms ω, η with η(x) = ρ^k ω(ρx) for all x.

Node: `root.deformation-a1.dilation-a1.calculus-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1120

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.deformation_dilation_calculus`

```lean
∀ (N : ℕ) (ρ : ℝ), 0 < ρ → ∀ k : ℕ, (∀ ω : TestFormOn (univ : Set (Eucl N)) k, ∃ η : TestFormOn (univ : Set (Eucl N)) k, ∀ x, (η : DifferentialForm (Eucl N) k) x = ρ ^ k • (ω : DifferentialForm (Eucl N) k) (ρ • x)) ∧ (∀ X : GeometricCurrentOn (univ : Set (Eucl N)) k, ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) k, (∀ ω η : TestFormOn (univ : Set (Eucl N)) k, (∀ x, (η : DifferentialForm (Eucl N) k) x = ρ ^ k • (ω : DifferentialForm (Eucl N) k) (ρ • x)) → Y ω = X η)) ∧ ∀ X Y : GeometricCurrentOn (univ : Set (Eucl N)) (k + 1), (∀ ω η : TestFormOn (univ : Set (Eucl N)) (k + 1), (∀ x, (η : DifferentialForm (Eucl N) (k + 1)) x = ρ ^ (k + 1) • (ω : DifferentialForm (Eucl N) (k + 1)) (ρ • x)) → Y ω = X η) → ∀ ω η : TestFormOn (univ : Set (Eucl N)) k, (∀ x, (η : DifferentialForm (Eucl N) k) x = ρ ^ k • (ω : DifferentialForm (Eucl N) k) (ρ • x)) → Y.boundary ω = X.boundary η
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

- Parent DAG node: `root.deformation-a1.dilation-a1`
- Child DAG node: `root.deformation-a1.dilation-a1.calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Notation and Steps 1, 2 and 9. These specialise Simon Ch. 6, 2.23 (push-forward f_#T(ω) = T(f^#ω) by a smooth proper map), 2.24(1) (∂f_#T = f_#∂T) and §1, 1.14 (pull-back commutes with d) to the dilation η_ρ(x) = ρx.

Conventions.
- ℝ^N := Eucl N.
- A j-form is a map ℝ^N → Covector (ℝ^N) j, i.e. into the continuous alternating j-linear maps.
- A test j-form is an element of TestFormOn univ j: a C^∞ form with compact support (tsupport ⊆ univ is automatic). Two test forms with the same underlying form are equal (Subtype.ext).
- Fix N, ρ > 0 and k, and let L := ρ • id : ℝ^N →L[ℝ] ℝ^N.
- For a j-form ω, L^#ω is the j-form x ↦ ω(Lx) ∘ (L, …, L), i.e. (L^#ω)(x)(v₁,…,v_j) = ω(ρx)(ρv₁,…,ρv_j).

Formalization note. L^#ω is SimonGMT's affinePullbackForm L 0 ω, from Poincare.SimonGMT.Chapter06.AffineCurrentPushforward in the pinned simongmt package (rev 2b366308). That module is not in the import closure of the frozen contract. Add `import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward` at the top of GMT/Ch06/Submission.lean: the comparator byte-checks only the frozen files other than Submission.lean, and accepted nodes already add imports. Auxiliary lemmas need globally unique names, e.g. prefixed deformation_dilation_calculus_.

1. Scaling identity. For every j, every j-covector α and all v₁,…,v_j ∈ ℝ^N, α(ρv₁,…,ρv_j) = ρ^j·α(v₁,…,v_j), because α is linear in each of its j slots. For j = 0 the product of the factors is empty and ρ^0 = 1. Hence (L^#ω)(x) = ρ^j • ω(ρ • x) for every j-form ω and every x.
[Lean: ext v. Then (ω (ρ • x)).map_smul_univ (fun _ => ρ) v gives ω(ρx)(fun i => ρ • v i) = (∏ i : Fin j, ρ) • ω(ρx) v. Finset.prod_const, Finset.card_univ and Fintype.card_fin turn the product into ρ ^ j. Unfold affinePullbackForm with ContinuousAlternatingMap.compContinuousLinearMap_apply, zero_add and Function.comp_def.]

2. L is proper. L is a homeomorphism of ℝ^N (its inverse is y ↦ ρ⁻¹y, since ρ ≠ 0), and homeomorphisms are proper maps.
[Lean: (fun x => 0 + L x) = ⇑(Homeomorph.smulOfNeZero ρ hρ.ne') by funext and simp; then Homeomorph.isProperMap.]

3. First conjunct. Let ω be a test k-form and put η := L^#ω.
(a) η is C^∞. The map x ↦ ω(Lx) is the composite of the C^∞ map ω with the linear map L. The map α ↦ α ∘ (L,…,L) is a continuous linear map on k-covectors.
(b) tsupport η ⊆ L⁻¹(tsupport ω). If ω vanishes on a neighbourhood V of Lx, then η vanishes on the neighbourhood L⁻¹(V) of x.
(c) tsupport ω is compact, so L⁻¹(tsupport ω) is compact by step 2. Hence the closed set tsupport η ⊆ L⁻¹(tsupport ω) is compact, and tsupport η ⊆ univ.
So η ∈ TestFormOn univ k, and η(x) = ρ^k • ω(ρ • x) for every x by step 1.
[Lean: η := affinePullbackTestOn L 0 hproper univ k ω, built from affinePullbackForm_isSmoothForm, tsupport_affinePullbackForm_subset and affinePullbackForm_isTestForm. Its type TestFormOn ((fun x => 0 + L x) ⁻¹' univ) k is definitionally TestFormOn univ k, since Set.preimage_univ is rfl. The pointwise identity is step 1.]

4. The pull-back operator. Let P : TestFormOn univ k → TestFormOn univ k be P ω := L^#ω (step 3).
(a) P is ℝ-linear: L^#(aω + bω′) = a·L^#ω + b·L^#ω′ pointwise.
(b) P is sequentially continuous at 0 for Simon's test-form topology. Suppose TestFormOnConverges ω_j 0. Then there is a compact K with tsupport ω_j ⊆ K for all j, and for every i ∈ ℕ the i-th iterated derivatives D^iω_j converge uniformly on K to D^i0 = 0.
(i) tsupport(Pω_j) ⊆ L⁻¹(K) for all j by step 3(b), and L⁻¹(K) is a fixed compact set by step 2. Also tsupport(P0) = tsupport 0 = ∅ ⊆ L⁻¹(K).
(ii) By the chain rule, D^i(Pω_j)(x) = J_i(D^iω_j(Lx)). Here J_i is the fixed continuous linear map on i-jets that precomposes each of the i derivative slots and each of the k covector slots with L. For x ∈ L⁻¹(K) we have Lx ∈ K, and J_i is uniformly continuous. So D^i(Pω_j) → J_i(0) = 0 = D^i(P0) uniformly on L⁻¹(K).
Thus TestFormOnConverges (Pω_j) (P0), and P0 = 0.
[Lean: affinePullbackTestOn is a LinearMap; use iteratedFDeriv_affinePullbackForm and TestFormOnConverges.affinePullback.]

5. Second conjunct. Let X ∈ GeometricCurrentOn univ k and define Y := X ∘ P.
- Y is ℝ-linear, as a composite of linear maps.
- Continuity: if TestFormOnConverges ω_j 0, then TestFormOnConverges (Pω_j) 0 by step 4(b). So Y(ω_j) = X(Pω_j) → 0 by the continuity field of X. Hence Y ∈ GeometricCurrentOn univ k.
- Pair property: let ω, η be test k-forms with η(x) = ρ^k • ω(ρ • x) for all x. By step 1, η and Pω have the same underlying form. So η = Pω, and Y(ω) = X(Pω) = X(η).
[Lean: Y := GeometricCurrentOn.affinePushforward (V := univ) L 0 hproper X. The explicit (V := univ) lets X : GeometricCurrentOn univ k be accepted, since preimage_univ is rfl. To unfold Y ω, use `show X.toCurrent (affinePullbackTestOn L 0 hproper univ k ω) = X.toCurrent η`. Rewriting with affinePushforward_apply fails, because the term is only well-typed up to that defeq. Then congr 1, Subtype.ext, funext x, rw [hη x], and step 1.]

6. d commutes with the pull-back. For a C^∞ j-form ω, d(L^#ω) = L^#(dω).
- By the chain rule, D(L^#ω)(x)(v) = Dω(Lx)(Lv) ∘ (L,…,L).
- By Simon 1.11, dβ(x)(v₀,…,v_j) = Σ_i (−1)^i Dβ(x)(v_i)(v₀,…,v̂_i,…,v_j).
- Together: d(L^#ω)(x)(v₀,…,v_j) = Σ_i (−1)^i Dω(Lx)(Lv_i)(Lv₀,…,(Lv_i)^,…,Lv_j) = dω(Lx)(Lv₀,…,Lv_j) = (L^#dω)(x)(v₀,…,v_j). This is Simon 1.14 (Mathlib extDeriv_pullback).
With step 1 in degree j + 1, d(L^#ω)(x) = ρ^{j+1} • dω(ρ • x) for every x.
[Lean: exteriorDerivative_affinePullbackForm L 0 h, where h : IsSmoothForm ω is ω.property.1.1; then step 1 with j + 1.]

7. Third conjunct. Let X, Y ∈ GeometricCurrentOn univ (k+1) satisfy Y(ω′) = X(η′) for all test (k+1)-forms ω′, η′ with η′(x) = ρ^{k+1} • ω′(ρ • x) for all x. Let ω, η be test k-forms with η(x) = ρ^k • ω(ρ • x) for all x.
- By step 1, η = L^#ω as forms.
- Put dω := exteriorDerivativeTestOn univ k ω and dη := exteriorDerivativeTestOn univ k η. These are test (k+1)-forms whose underlying forms are the exterior derivatives (exteriorDerivative = extDeriv).
- Since ω is C^∞, step 6 gives dη(x) = d(L^#ω)(x) = ρ^{k+1} • dω(ρ • x) for every x.
- The hypothesis applied to (ω′, η′) := (dω, dη) gives Y(dω) = X(dη).
- By definition of the boundary (GeometricCurrentOn.boundary_apply: T.boundary ω = T(exteriorDerivativeTestOn univ k ω)), Y.boundary ω = Y(dω) = X(dη) = X.boundary η.
[Lean: rw [boundary_apply, boundary_apply]; apply the hypothesis; intro x. Rewrite the underlying form of η as affinePullbackForm L 0 ω (funext, hη, step 1). Change the goal to exteriorDerivative η x = ρ ^ (k+1) • exteriorDerivative ω (ρ • x). Then rw [exteriorDerivative_affinePullbackForm L 0 ω.property.1.1] and close with step 1 in degree k + 1.]

8. Conclusion. Steps 3, 5 and 7 give the three conjuncts for arbitrary N, ρ > 0 and k. ∎

## Key steps

1. Multilinearity gives α(ρv₁,…,ρv_j) = ρ^jα(v), so the pull-back L^#ω by L = ρ·id is x ↦ ρ^jω(ρx) (ContinuousAlternatingMap.map_smul_univ on affinePullbackForm L 0 ω).
2. L is a homeomorphism, hence proper. L^#ω is C^∞ with tsupport ⊆ L⁻¹(tsupport ω), which is compact. This is the first conjunct (affinePullbackTestOn; preimage_univ is rfl).
3. Pull-back is linear and sequentially continuous in the test-form topology, so Y := X∘L^# is a current (affinePushforward with V := univ). The pair property follows from Subtype.ext and the scaling identity. This is the second conjunct.
4. d commutes with L^# (exteriorDerivative_affinePullbackForm), so dη(x) = ρ^{k+1}dω(ρx). Apply the (k+1)-pair property to (dω, dη) and unfold ∂ via boundary_apply. This is the third conjunct.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in lake-packages-25730c7c/simongmt and .lake/packages/simongmt (2b3663083f3fe399b6296fb8eaee52169170e197 = lakefile.toml rev)`
- `cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (byte-identical)`
- `python3 -I over dag.json: lean_statement of root.deformation-a1.dilation-a1 == selected frozen type == handoff lean_statement (True); six proposed names vs all 554 lean_names (no collision)`
- `rg -n 'deformation_dilation_(calculus|hausdorff|mass|support|integer_multiplicity|lattice_chain)' local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt (no match, exit 1); git grep -l 'deformation_dilation_' -- '*.lean' over all 2352 refs (no match)`
- `grep -n '^theorem|^def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean (affinePullbackForm:35, affinePullbackTestOn:65, iteratedFDeriv_affinePullbackForm:109, TestFormOnConverges.affinePullback:127, exteriorDerivative_affinePullbackForm:147, GeometricCurrentOn.affinePushforward:172, boundary_affinePushforward:188)`
- `cat simongmt Chapter06/Currents.lean, Mass.lean, CurrentLocalEquality.lean, FormsDuality.lean, Forms.lean; grep -n 'def blowUpMap|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable' Chapter03/Rectifiable.lean (lines 96, 330, 34)`
- `rg -n 'euclideanHausdorffMeasure_smul₀|def MeasureTheory.Measure.euclideanHausdorffMeasure' mathlib/Mathlib (Geometry/Euclidean/Volume/Measure.lean:152, :67)`
- `rg -n 'theorem (MeasurePreserving\.)?(setIntegral_image_emb|integrableOn_image|restrict_image_emb)|aestronglyMeasurable_map_iff|theorem ae_map_iff|theorem extDeriv_pullback|theorem map_smul_univ|theorem image_compl_eq|theorem ae_smul_measure|theorem integral_smul_measure' mathlib/Mathlib (Integral/Bochner/Set.lean:576, Integral/IntegrableOn.lean:324, Dynamics/Ergodic/MeasurePreserving.lean:86, StronglyMeasurable/AEStronglyMeasurable.lean:668, Measure/Restrict.lean:887, Calculus/DifferentialForm/Basic.lean:259, Topology/Algebra/Module/Alternating/Basic.lean:518, Data/Set/Image.lean:372, Measure/Module.lean:191, Integral/Bochner/Basic.lean:1052)`
- `python3 over dag.json for integrality_weak_limits-a1.integer_density-a1.rescale-a1 children (ind_rs_dilation_measurePreserving, ind_rs_massOn_dilation_le, ind_rs_tauAction_dilation, ind_rs_weightedTangent_dilation accepted; ind_rs_rectifiableTriple_dilation comparing; all for y ↦ r⁻¹(y − x), different frozen types); git show <triple-image and tau-action branches>:GMT/Ch06/Submission.lean (proof templates)`
- `header imports of GMT/Ch06/Submission.lean on all theorems/solutions/* branches (accepted solutions add imports, e.g. Poincare.SimonGMT.Chapter02.AreaDomain x7); sed -n 334,372p verifier/gmt-compare.py (candidate_inputs byte-checks only frozen files other than Submission.lean)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the six child statements and the parent (all valid, returned unchanged)`
- `lake env lean /tmp/dil-decomp-6e47/Scratch/NC_<key>.lean for the six keys in the exact comparator scope (all exit 0, only the expected sorry warning); Assembly.lean (dilation_assembly: [propext, Classical.choice, Quot.sound]); Proto_calculus, Proto_hmass, Proto_support, Proto_im, Proto_lattice and EndToEnd.lean (sha256 3f159720…; exit 0, 0 errors; all seven Submission declarations [propext, Classical.choice, Quot.sound])`
- `sed -n '385,440p;1450,1475p' book/chapter-06.txt (2.23 f_#T(ω) = T(ζ f^#ω), 2.24(1) ∂f_#T = f_#∂T, ‘scaled version … changing scale … then changing scale back by x → ρx’)`
- `web search: scaling of Hausdorff measure H^s(λA) = λ^s H^s(A) (Wikipedia ‘Hausdorff measure’; Imperial College M345PA46 notes ch. 2, similarity scaling via δ-covers); Evans–Gariepy theorem number could not be verified, so not cited`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dil-decomp-6e47/stmts.json`
- `/tmp/dil-decomp-6e47/Scratch/Assembly.lean`
- `/tmp/dil-decomp-6e47/Scratch/EndToEnd.lean`
- `/tmp/dil-decomp-6e47/logs/EndToEnd.log`
- `/tmp/dil-decomp-6e47/logs/Assembly.log`
- `/tmp/dil-decomp-6e47/logs/NC_calculus.log`
- `/tmp/dil-decomp-6e47/logs/NC_hausdorff.log`
- `/tmp/dil-decomp-6e47/logs/NC_mass.log`
- `/tmp/dil-decomp-6e47/logs/NC_support.log`
- `/tmp/dil-decomp-6e47/logs/NC_integer_multiplicity.log`
- `/tmp/dil-decomp-6e47/logs/NC_lattice_chain.log`

The pinned revisions are confirmed, and Contract = Submission = the snapshot Contract byte for byte. No project, SimonGMT or Mathlib declaration already proves the selected statement. The pinned simongmt module Poincare.SimonGMT.Chapter06.AffineCurrentPushforward supplies all of the push-forward calculus for proper affine maps: the pull-back test-form map, its sequential continuity, the push-forward current, and commutation with d. It is not in the frozen import closure, but Submission.lean may add the import, since only the other frozen files are byte-checked and accepted solutions already add imports. Mathlib supplies Measure.euclideanHausdorffMeasure_smul₀ (μHE[k](r•S) = ‖r‖₊^k μHE[k] S) and the measure-preserving-embedding toolkit used by the children. The accepted ind_rs_* dilation lemmas concern y ↦ r⁻¹(y − x), have different frozen types and belong to another branch, so they are only optional templates. The six child names are globally unused. All six statements validate and elaborate in the comparator scope. The parent's exact type follows from them with standard axioms only, and a complete end-to-end prototype of every child plus the parent compiles with [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
