<!-- theorem-id: gmt-ch06/root.deformation-a1.dilation-a1.integer_multiplicity-a1.rectifiable_triple-a1 -->

## Theorem `Submission.deformation_dilation_im_rectifiableTriple`

Let N, k ∈ ℕ, let ρ ∈ ℝ with ρ > 0, M ⊆ ℝ^N, θ : ℝ^N → ℝ and ξ : ℝ^N → NVector(ℝ^N, k). Put φ(x) := ρ • x, μ := H^k = μHE[k] and c := ENNReal.ofReal(ρ^k). Assume (H1) φ is a measurable embedding and (H2) φ is measure preserving from c • μ to μ. If (M, θ, ξ) is a rectifiable triple in ℝ^N (IsRectifiableTriple univ k M θ ξ), then so is (φ(M), θ(ρ⁻¹·), ξ(ρ⁻¹·)). In Lean: IsRectifiableTriple univ k ((fun x => ρ • x) '' M) (fun y => θ (ρ⁻¹ • y)) (fun y => ξ (ρ⁻¹ • y)).

Node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1.rectifiable_triple-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4546

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4905

Decomposition children: None

## Lean problem

Declaration: `Submission.deformation_dilation_im_rectifiableTriple`

```lean
∀ (N k : ℕ) (ρ : ℝ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) k), 0 < ρ → MeasurableEmbedding (fun x : Eucl N => ρ • x) → MeasurePreserving (fun x : Eucl N => ρ • x) (ENNReal.ofReal (ρ ^ k) • (μHE[k] : Measure (Eucl N))) (μHE[k] : Measure (Eucl N)) → IsRectifiableTriple (univ : Set (Eucl N)) k M θ ξ → IsRectifiableTriple (univ : Set (Eucl N)) k ((fun x : Eucl N => ρ • x) '' M) (fun y : Eucl N => θ (ρ⁻¹ • y)) (fun y : Eucl N => ξ (ρ⁻¹ • y))
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

- Parent DAG node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1`
- Child DAG node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1.rectifiable_triple-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Steps 0(a), 0(c), 0(d) and Step 5, fields (i)–(vii). Here the measure facts come from the hypotheses (H1) and (H2), not from the sibling deformation_dilation_hausdorff. Its conclusion is exactly (H1) ∧ (H2), and the parent discharges the hypotheses with it.
Sibling used: weighted_tangent (Submission.deformation_dilation_im_weightedTangent).

Conventions.
- ℝ^N := Eucl N, μ := μHE[k], φ(x) := ρ • x and c := ENNReal.ofReal(ρ^k). Note c ≠ ∞ (ENNReal.ofReal_ne_top).
- M′ := φ(M), θ′(y) := θ(ρ⁻¹ • y) and ξ′(y) := ξ(ρ⁻¹ • y).
- (★) For every x, ρ⁻¹ • φ(x) = x (inv_smul_smul₀, ρ ≠ 0). Hence θ′(φ x) = θ(x), ξ′(φ x) = ξ(x), θ′ ∘ φ = θ and ξ′ ∘ φ = ξ.
- IsRectifiableTriple univ k S ϑ ζ has seven fields:
  subset: S ⊆ univ.
  nullMeasurableSet: S is μ-null measurable.
  countablyRectifiable: CountablyRectifiable k S.
  pos: ϑ > 0 on S.
  integrableOn: for every compact K ⊆ univ, ϑ is μ-integrable on S ∩ K.
  aestronglyMeasurable: ζ is AE strongly measurable for μ|_S.
  orients: for μ|_S-a.e. x there is an orthonormal τ : Fin k → ℝ^N with HasWeightedApproximateTangentSpaceAt k S ϑ x (span(range τ)) and ζ(x) = simpleNVector τ or ζ(x) = −simpleNVector τ.
- Let hT denote the hypothesis IsRectifiableTriple univ k M θ ξ.

1. Null sets map to null sets. Claim: if μ(S) = 0 then μ(φ(S)) = 0.
   - By (H2), map φ (c • μ) = μ (MeasurePreserving.map_eq).
   - For the measurable embedding φ of (H1), (map φ ν)(A) = ν(φ⁻¹(A)) for every set A (MeasurableEmbedding.map_apply).
   - φ is injective by (H1), so φ⁻¹(φ(S)) = S (preimage_image_eq).
   Therefore μ(φ S) = (c • μ)(φ⁻¹(φ S)) = (c • μ)(S) = c·μ(S) = c·0 = 0 (Measure.smul_apply, smul_zero).

2. Restricted measures. Claim: φ is measure preserving from c • (μ|_M) to μ|_{M′}.
   First, c • (μ|_M) = (c • μ)|_M (Measure.restrict_smul). Then MeasurePreserving.restrict_image_emb, applied to (H2), (H1) and M, shows φ is measure preserving from (c • μ)|_M to μ|_{φ(M)}. In particular map φ (c • (μ|_M)) = μ|_{M′}.

3. Field subset. M′ ⊆ univ (subset_univ).

4. Field nullMeasurableSet.
   - Let B := toMeasurable μ M. Then B is measurable (measurableSet_toMeasurable).
   - B =ᵐ[μ] M (NullMeasurableSet.toMeasurable_ae_eq applied to hT.nullMeasurableSet). By ae_eq_set this means μ(B ∖ M) = 0 and μ(M ∖ B) = 0.
   - φ(B) is measurable (MeasurableEmbedding.measurableSet_image with (H1)), hence null measurable.
   - By injectivity, φ(B) ∖ φ(M) = φ(B ∖ M) and φ(M) ∖ φ(B) = φ(M ∖ B) (Set.image_sdiff). Both are μ-null by Step 1.
   - So φ(B) =ᵐ[μ] φ(M) (ae_eq_set), and φ(M) is null measurable (NullMeasurableSet.congr).

5. Field countablyRectifiable. From hT.countablyRectifiable obtain M₀ with μ(M₀) = 0 and F : ℕ → (ℝ^k → ℝ^N) such that each F_j is LipschitzWith K_j and M ⊆ M₀ ∪ ⋃_j range F_j.
   (a) φ is LipschitzWith ‖ρ‖₊, since dist(ρ • a, ρ • b) = ‖ρ‖·dist(a, b) (dist_smul₀; LipschitzWith.of_dist_le_mul).
   (b) Take M₀′ := φ(M₀), which is μ-null by Step 1. Take F′_j := φ ∘ F_j, which is LipschitzWith (‖ρ‖₊·K_j) (LipschitzWith.comp).
   (c) Let y ∈ M′, say y = φ(x) with x ∈ M. If x ∈ M₀, then y ∈ φ(M₀) = M₀′. Otherwise x = F_j(w) for some j and w, and y = F′_j(w) ∈ range F′_j. Hence M′ ⊆ M₀′ ∪ ⋃_j range F′_j, which is CountablyRectifiable k M′.

6. Field pos. For y = φ(x) ∈ M′ with x ∈ M, θ′(y) = θ(x) > 0, by (★) and hT.pos.

7. Field integrableOn. Let K be compact (K ⊆ univ).
   (a) M′ ∩ K = φ(M ∩ φ⁻¹(K)) (Set.image_inter_preimage).
   (b) φ⁻¹(K) is compact, because φ is the homeomorphism Homeomorph.smulOfNeZero ρ for ρ ≠ 0 (Homeomorph.isCompact_preimage).
   (c) By MeasurePreserving.integrableOn_image with (H2) and (H1), θ′ is μ-integrable on φ(M ∩ φ⁻¹K) iff θ′ ∘ φ = θ is (c • μ)-integrable on M ∩ φ⁻¹K. That is, Integrable θ ((c • μ)|_{M ∩ φ⁻¹K}), which equals Integrable θ (c • (μ|_{M ∩ φ⁻¹K})) (Measure.restrict_smul).
   (d) hT.integrableOn at the compact set φ⁻¹(K) ⊆ univ gives Integrable θ (μ|_{M ∩ φ⁻¹K}). Since c ≠ ∞, also Integrable θ (c • (μ|_{M ∩ φ⁻¹K})) (Integrable.smul_measure).
   By (a)–(d), θ′ is μ-integrable on M′ ∩ K.

8. Field aestronglyMeasurable. By Step 2, μ|_{M′} = map φ (c • (μ|_M)). For the measurable embedding φ, AEStronglyMeasurable ξ′ (map φ ν) ⟺ AEStronglyMeasurable (ξ′ ∘ φ) ν (MeasurableEmbedding.aestronglyMeasurable_map_iff). Also ξ′ ∘ φ = ξ by (★). hT.aestronglyMeasurable gives AEStronglyMeasurable ξ (μ|_M), hence also for c • (μ|_M) (AEStronglyMeasurable.smul_measure).

9. Field orients.
   By Step 2, μ|_{M′} = map φ (c • (μ|_M)). For the measurable embedding φ, (∀ᵐ y ∂ map φ ν, P y) ⟺ (∀ᵐ x ∂ν, P (φ x)) (MeasurableEmbedding.ae_map_iff). So it suffices to prove the orientation property P(φ x) of (M′, θ′, ξ′) for c • (μ|_M)-a.e. x.
   hT.orients holds μ|_M-a.e., hence c • (μ|_M)-a.e. (Measure.ae_smul_measure; filter_upwards). Fix such an x, with τ orthonormal, HasWeightedApproximateTangentSpaceAt k M θ x (span(range τ)), and ξ(x) = ±simpleNVector τ. Use the same τ at φ(x) = ρ • x:
   (a) τ is orthonormal.
   (b) The sibling weighted_tangent, i.e. Submission.deformation_dilation_im_weightedTangent N k ρ M θ x (span(range τ)) hρ applied to the tangent hypothesis, gives HasWeightedApproximateTangentSpaceAt k M′ θ′ (ρ • x) (span(range τ)).
   (c) ξ′(φ x) = ξ(x) by (★), so ξ′(φ x) = simpleNVector τ or ξ′(φ x) = −simpleNVector τ.

10. Conclusion. Steps 3–9 establish all seven fields, so IsRectifiableTriple univ k M′ θ′ ξ′. ∎

Optional formalization aid (verified). The following declaration compiled in GMT/Ch06/Submission.lean position. That means after the contract definitions, inside namespace GMT.Ch06 with the contract's open commands, and needing no extra imports. It requires the sibling Submission.deformation_dilation_im_weightedTangent. Toolchain: Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308. #print axioms reports [propext, Classical.choice, Quot.sound].

theorem Submission.deformation_dilation_im_rectifiableTriple : ∀ (N k : ℕ) (ρ : ℝ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) k), 0 < ρ → MeasurableEmbedding (fun x : Eucl N => ρ • x) → MeasurePreserving (fun x : Eucl N => ρ • x) (ENNReal.ofReal (ρ ^ k) • (μHE[k] : Measure (Eucl N))) (μHE[k] : Measure (Eucl N)) → IsRectifiableTriple (univ : Set (Eucl N)) k M θ ξ → IsRectifiableTriple (univ : Set (Eucl N)) k ((fun x : Eucl N => ρ • x) '' M) (fun y : Eucl N => θ (ρ⁻¹ • y)) (fun y : Eucl N => ξ (ρ⁻¹ • y)) := by
  intro N k ρ M θ ξ hρ hemb hmp hT
  set φ : Eucl N → Eucl N := fun x => ρ • x with hφ
  set c : ℝ≥0∞ := ENNReal.ofReal (ρ ^ k)
  have hinv : ∀ x, ρ⁻¹ • φ x = x := fun x => inv_smul_smul₀ hρ.ne' x
  have hnull : ∀ S : Set (Eucl N), (μHE[k] : Measure (Eucl N)) S = 0 →
      (μHE[k] : Measure (Eucl N)) (φ '' S) = 0 := by
    intro S hS
    rw [← hmp.map_eq, hemb.map_apply, preimage_image_eq _ hemb.injective, Measure.smul_apply, hS,
      smul_zero]
  have hres : MeasurePreserving φ (c • (μHE[k] : Measure (Eucl N)).restrict M)
      ((μHE[k] : Measure (Eucl N)).restrict (φ '' M)) := by
    rw [← Measure.restrict_smul]
    exact hmp.restrict_image_emb hemb M
  refine ⟨subset_univ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hB := hT.nullMeasurableSet.toMeasurable_ae_eq
    rw [ae_eq_set] at hB
    refine (hemb.measurableSet_image.2
      (measurableSet_toMeasurable (μHE[k] : Measure (Eucl N)) M)).nullMeasurableSet.congr ?_
    rw [ae_eq_set, ← image_sdiff hemb.injective, ← image_sdiff hemb.injective]
    exact ⟨hnull _ hB.1, hnull _ hB.2⟩
  · obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hT.countablyRectifiable
    have hφL : LipschitzWith ‖ρ‖₊ φ := LipschitzWith.of_dist_le_mul fun a b => by
      show dist (ρ • a) (ρ • b) ≤ ‖ρ‖₊ * dist a b
      rw [dist_smul₀, coe_nnnorm]
    refine ⟨φ '' M₀, hnull M₀ hM₀, fun j => φ ∘ F j, fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨‖ρ‖₊ * K, hφL.comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hMF hy with hy₀ | hy₁
      · exact Or.inl (mem_image_of_mem φ hy₀)
      · obtain ⟨j, w, rfl⟩ := mem_iUnion.1 hy₁
        exact Or.inr (mem_iUnion.2 ⟨j, w, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < θ (ρ⁻¹ • φ y)
    rw [hinv]
    exact hT.pos y hy
  · intro K hK _
    have hK' : IsCompact (φ ⁻¹' K) :=
      (Homeomorph.smulOfNeZero ρ hρ.ne').isCompact_preimage.2 hK
    have hθ : (fun y => θ (ρ⁻¹ • y)) ∘ φ = θ := funext fun y => by
      simp only [Function.comp_apply, hinv]
    rw [← image_inter_preimage, hmp.integrableOn_image hemb, hθ, IntegrableOn,
      Measure.restrict_smul]
    exact Integrable.smul_measure (hT.integrableOn _ hK' (subset_univ _)) ENNReal.ofReal_ne_top
  · have hξ : (fun y => ξ (ρ⁻¹ • y)) ∘ φ = ξ := funext fun y => by
      simp only [Function.comp_apply, hinv]
    rw [← hres.map_eq, hemb.aestronglyMeasurable_map_iff, hξ]
    exact hT.aestronglyMeasurable.smul_measure c
  · rw [← hres.map_eq, hemb.ae_map_iff]
    filter_upwards [Measure.ae_smul_measure hT.orients c] with y hy
    obtain ⟨τ, hτ, htan, hξy⟩ := hy
    refine ⟨τ, hτ, Submission.deformation_dilation_im_weightedTangent N k ρ M θ y _ hρ htan, ?_⟩
    show ξ (ρ⁻¹ • φ y) = _ ∨ ξ (ρ⁻¹ • φ y) = _
    rw [hinv]
    exact hξy

## Key steps

1. (★) ρ⁻¹ • (ρ • x) = x, so θ′ ∘ φ = θ and ξ′ ∘ φ = ξ.
2. From (H1) and (H2): μ(S) = 0 implies μ(φ S) = 0 (map_eq, MeasurableEmbedding.map_apply, preimage_image_eq).
3. From (H1) and (H2): φ is measure preserving from c • μ|_M to μ|_{φM} (restrict_smul, restrict_image_emb).
4. subset is trivial. nullMeasurableSet: measurable hull B = toMeasurable μ M, then image_sdiff and the null-set step. countablyRectifiable: φ(M₀) and φ ∘ F_j, with φ LipschitzWith ‖ρ‖₊. pos: by (★).
5. integrableOn: φM ∩ K = φ(M ∩ φ⁻¹K), φ⁻¹K is compact (Homeomorph.smulOfNeZero), then integrableOn_image, restrict_smul, and Integrable.smul_measure with c ≠ ∞.
6. aestronglyMeasurable: μ|_{φM} = map φ (c • μ|_M), then aestronglyMeasurable_map_iff, ξ′ ∘ φ = ξ and smul_measure.
7. orients: ae_map_iff and ae_smul_measure. Keep the frame τ, transport the tangent plane with sibling weighted_tangent, and use ξ′(φ x) = ξ(x) = ±simpleNVector τ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git rev-parse HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum + cmp of local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean, GMT/Ch06/Contract.lean, GMT/Ch06/Submission.lean (all ea3ee0dd…, byte-identical)`
- `grep -n -E '^(open|namespace|noncomputable section|section|end|variable|universe|set_option)' GMT/Ch06/Contract.lean (comparator replay scope; variable {P : ℕ} is not replayed)`
- `sed -n 25,50p;90,110p;320,345p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable:34, blowUpMap:96, HasWeightedApproximateTangentSpaceAt:330); grep -n '^(abbrev|def|structure)' Chapter06/Forms.lean Chapter06/Currents.lean (DifferentialForm and TestFormOn are abbrevs)`
- `grep -rn -E 'mem_inv_smul_set_iff₀|euclideanHausdorffMeasure_smul₀|aestronglyMeasurable_map_iff|setIntegral_image_emb|integrableOn_image\b|smulOfNeZero' mathlib/Mathlib, and grep -rn for restrict_image_emb|ae_map_iff|ae_smul_measure|dist_smul₀|image_sdiff|integral_smul_measure (all found: Bochner/Set.lean:576, IntegrableOn.lean:324, AEStronglyMeasurable.lean:668, MeasurePreserving.lean:86, Restrict.lean:887, Module.lean:191, ConstMulAction.lean:394, Volume/Measure.lean:152, MulAction.lean:153, Set/Image.lean:379, Bochner/Basic.lean:1052)`
- `python3 -I over dag.json: statuses and lean_statements of the root.deformation-a1.dilation-a1 children and the rescale-a1 children (ind_rs_* accepted); sibling types of calculus, hausdorff and integer_multiplicity asserted equal to the strings used; the three proposed names checked against all 619 lean_names and the raw text of dag.json and issue-workers.json (0 occurrences)`
- `grep -rl 'deformation_dilation_im_' runs/…/nodes/ (no match); git for-each-ref refs/heads refs/remotes | xargs git grep -l 'deformation_dilation_im_' -- GMT/Ch06/Submission.lean (no match)`
- `python3 over dag.json for split nodes with depends_on (e.g. local_to_global_im-a1, lattice_approximation-a1): no grandchild cites its parent's sibling dependency`
- `git show proof-workspace/…/rescale-a1-triple-image-a1-efeaf8ca5e:GMT/Ch06/Submission.lean and …/rescale-a1-tau-action-a1-c14ddccfbd:GMT/Ch06/Submission.lean (template proofs for y ↦ r⁻¹(y − x))`
- `python3 -I scripts/gen.py: lean_contract.validate_lean_statement + gmt-compare.child_modules(contract mode) for the parent and the three children -> Scratch/NC_<key>.lean`
- `lean Scratch/NC_parent.lean, NC_weighted_tangent.lean, NC_rectifiable_triple.lean, NC_tau_action.lean (LEAN_PATH from lake env; all EXIT=0, only the expected sorry warning)`
- `lean Scratch/Proto2.lean and Proto3.lean (three children and the hausdorff type proved, [propext, Classical.choice, Quot.sound]; parent compiles, with sorryAx only from the calculus stub; solution-side exact Submission.X checks pass); lean Scratch/Assembly.lean (dilation_im_assembly: [propext, Classical.choice, Quot.sound])`
- `sed -n 1455,1475p book/chapter-06.txt (5.3 scaled version: first changing scale, applying 5.1, then changing scale back)`
- `web search: Hausdorff measure scaling H^s(λA) = λ^s H^s(A) dilation (Imperial College M345PA46 ch. 2; McGill MATH 565 notes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-integer-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-integer-multiplicity-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Image.lean`
- `proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-triple-image-a1-efeaf8ca5e:GMT/Ch06/Submission.lean`
- `proof-workspace/gmt-ch06/20261011t144224z-6e4735dbca/theorems/solutions/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-tau-action-a1-c14ddccfbd:GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ddim-decomp-7c21/stmts.json`
- `/tmp/ddim-decomp-7c21/Scratch/NC_parent.lean`
- `/tmp/ddim-decomp-7c21/Scratch/NC_weighted_tangent.lean`
- `/tmp/ddim-decomp-7c21/Scratch/NC_rectifiable_triple.lean`
- `/tmp/ddim-decomp-7c21/Scratch/NC_tau_action.lean`
- `/tmp/ddim-decomp-7c21/Scratch/Proto2.lean`
- `/tmp/ddim-decomp-7c21/Scratch/Proto3.lean`
- `/tmp/ddim-decomp-7c21/Scratch/Assembly.lean`
- `/tmp/ddim-decomp-7c21/logs/NC_parent.log`
- `/tmp/ddim-decomp-7c21/logs/NC_weighted_tangent.log`
- `/tmp/ddim-decomp-7c21/logs/NC_rectifiable_triple.log`
- `/tmp/ddim-decomp-7c21/logs/NC_tau_action.log`
- `/tmp/ddim-decomp-7c21/logs/Proto2.log`
- `/tmp/ddim-decomp-7c21/logs/Proto3.log`
- `/tmp/ddim-decomp-7c21/logs/Assembly.log`

No project, SimonGMT or Mathlib declaration proves the selected statement or any proposed child. The accepted ind_rs_* lemmas on the rescale branch treat y ↦ r⁻¹(y − x), have different frozen types and live on another DAG branch, so they serve only as proof templates. The pinned Mathlib supplies everything needed: the measure-transport API (MeasurePreserving.setIntegral_image_emb, integrableOn_image, restrict_image_emb, MeasurableEmbedding.aestronglyMeasurable_map_iff and ae_map_iff, Measure.ae_smul_measure, Homeomorph.smulOfNeZero) plus Measure.euclideanHausdorffMeasure_smul₀, all inside the frozen import closure, so no import changes are needed. The snapshot Contract, the workspace Contract and Submission are byte-identical at the manifest commit. All three child statements validate, elaborate in the exact comparator scope, and have complete compiled proofs with [propext, Classical.choice, Quot.sound]; these are embedded verbatim in each child's proof. Their names are globally unused. Together with the resolved siblings calculus and hausdorff, they imply the selected frozen type with standard axioms only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
