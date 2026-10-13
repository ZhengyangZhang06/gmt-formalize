<!-- theorem-id: gmt-ch06/root.deformation-a1.im_completeness-a1.mass_lower_bound-a1 -->

## Theorem `Submission.imc_lintegral_coordNorm_le_mass`

Let N, k ∈ ℕ, let Y ∈ D_k(ℝ^N) (GeometricCurrentOn univ k), let μ be a measure on ℝ^N and κ : ℝ^N → Λ_k(ℝ^N) a field of k-vectors (NVector (Eucl N) k) such that (μ, κ) represents Y (IsMeasureRepresentation Y μ κ): for every test form ω ∈ D^k(ℝ^N) the function x ↦ κ(x)(ω(x)) is μ-integrable and Y(ω) = ∫ κ(x)(ω(x)) dμ(x). Then ∫ |κ(x)| dμ(x) ≤ M(Y) in [0, ∞], where |w| := (Σ_γ w(dx^γ)²)^{1/2} is the Euclidean norm of a k-vector w (w(dx^γ) = euclideanNVectorCoordinate w γ, dx^γ = wedgeCovectors k (proj ∘ γ), γ ranging over the strictly increasing multi-indices SimonMultiIndex k N) and M(Y) = Y.mass = Y.massOn univ.

Node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1106

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/527

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1783, https://github.com/ZhengyangZhang06/gmt-formalize/issues/699, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2611, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2636, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4229, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4241, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4252

## Lean problem

Declaration: `Submission.imc_lintegral_coordNorm_le_mass`

```lean
∀ (N k : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ : Measure (Eucl N)) (κ : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation Y μ κ → ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ Y.mass
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

- Parent DAG node: `root.deformation-a1.im_completeness-a1`
- Child DAG node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: printed display (1) of Simon Ch. 6, Lemma 3.13 (M_W(T_Q − T_P) ≥ ∫_W |θ_Pξ_P − θ_Qξ_Q| dHⁿ), i.e. the lower half of the mass formula M(T) = ∫|T⃗| dμ_T of Ch. 6, 2.7–2.8. This is the Lemma of Step 2 of the parent proof (λ′ := μ, κ := κ), stated for an arbitrary measure representation, and its argument is followed: restrict to a ball, choose a continuous field of norm ≤ 1 that is close to κ/|κ| on most of the |κ|-mass, cut it off, mollify it into a test form and rescale it into the admissible class. The parent proof obtains the continuous field from inner regularity, Lusin's theorem and Tietze's theorem. Those two theorems are not in the frozen import closure (Mathlib.Topology.TietzeExtension, Mathlib.MeasureTheory.Function.ContinuousMapDense and SimonGMT Chapter01.Lusin are not imported by GMT/Ch06/Contract.lean). Steps 4–6 below therefore produce the same estimate ν(ℝ^N) − O(ε) through the elementary density of continuous compactly supported maps in L¹ of a finite Borel measure, which is proved in Step 4 from regularity and Urysohn's lemma (the usual proof of Lusin's theorem). The hypothesis IsMeasureRepresentation replaces "λ′ locally finite and κ λ′-integrable on bounded sets"; Step 1 derives the local integrability that is needed.

Notation. e_i := EuclideanSpace.single i 1 = EuclideanSpace.basisFun (Fin N) ℝ i. I := SimonMultiIndex k N (order embeddings γ : Fin k ↪o Fin N, i.e. strictly increasing γ), m := #I. For γ ∈ I: e_γ := (e_{γ(0)}, …, e_{γ(k−1)}) and dx^γ := wedgeCovectors k (fun j ↦ EuclideanSpace.proj (γ j)). For a k-covector α: α_γ := α(e_γ) = euclideanCovectorCoordinate α γ, |α| := covectorEuclideanNorm α, and ‖α‖ is its operator norm. For a k-vector w: w^γ := w(dx^γ) = euclideanNVectorCoordinate w γ, c(w) := (w^γ)_γ ∈ ℝ^I := EuclideanSpace ℝ I, and |w| := ‖c(w)‖ = (Σ_γ (w^γ)²)^{1/2}. ‖·‖ and ⟨·,·⟩ on ℝ^I are Euclidean. B_R := ball 0 R, B̄_R := closedBall 0 R, h(x) := |κ(x)|. M := M(Y) = Y.mass = Y.massOn univ.

0. Linear algebra.
 (a) (Pairing; sibling pairing_expansion.) w(α) = Σ_γ α_γ w^γ for every k-vector w and k-covector α, and |α_γ| ≤ |α|.
 (b) |α|² = Σ_γ α_γ². Indeed covectorEuclideanNorm α = (Σ_{J : Fin k → Fin N} [J strictly increasing] α(basisFun ∘ J)²)^{1/2}; the strictly increasing J correspond bijectively to the γ ∈ I (OrderEmbedding.ofStrictMono, and the coercion of an order embedding to a strictly increasing map), and basisFun (J i) = e_{J i}. So |α| is the Euclidean norm of the coefficient vector (α_γ)_γ ∈ ℝ^I. In particular |s·α| = |s|·|α| for s ∈ ℝ.
 (c) (Cauchy–Schwarz.) By (a), (b) and the Cauchy–Schwarz inequality in ℝ^I, |w(α)| ≤ |α|·|w|.
 (d) (Kronecker.) For γ, β ∈ I, dx^γ(e_β) = 1 if γ = β and 0 otherwise. By wedgeCovectors_apply_det, dx^γ(e_β) = det[δ_{γ(i), β(j)}]_{i,j}. For γ = β this is det 1 = 1. For γ ≠ β the ranges differ, because a strictly increasing map is determined by its range; both ranges have k elements, so some γ(i) ∉ range β, row i of the matrix is zero, and the determinant is 0.
 (e) For a ∈ ℝ^I let a♭ := Σ_γ a_γ dx^γ, a k-covector depending linearly (hence continuously) on a. By (d), (a♭)_β = a_β. Hence |a♭| = ‖a‖ by (b), and w(a♭) = Σ_γ a_γ w^γ = ⟨a, c(w)⟩ by (a).
 (f) (Radial retraction.) For a ∈ ℝ^I let π(a) := a / max{1, ‖a‖}. Then π is continuous, ‖π(a)‖ ≤ 1, and π(a) = a when ‖a‖ ≤ 1. Moreover ‖π(a) − b‖ ≤ ‖a − b‖ whenever ‖b‖ ≤ 1. This is trivial if ‖a‖ ≤ 1. If t := ‖a‖ > 1, then ‖a − b‖² − ‖a/t − b‖² = t² − 1 − 2(1 − 1/t)⟨a, b⟩ ≥ t² − 1 − 2(1 − 1/t)·t = (t − 1)² ≥ 0, using ⟨a, b⟩ ≤ ‖a‖‖b‖ ≤ t.

1. (Local integrability of the coordinates.) Let R > 0 and choose a C^∞ function φ_R : ℝ^N → [0, 1] with compact support and φ_R = 1 on B̄_R (a smooth bump function, e.g. ContDiffBump or exists_contDiff_tsupport_subset). For γ ∈ I the form x ↦ φ_R(x) • dx^γ is smooth with compact support, hence an element of TestFormOn univ k. By hypothesis x ↦ κ(x)(φ_R(x) • dx^γ) = φ_R(x)κ^γ(x) is μ-integrable. As φ_R = 1 on B̄_R, κ^γ is μ-integrable on B̄_R. Hence h = ‖(κ^γ)_γ‖ ≤ Σ_γ |κ^γ| is μ-integrable on B̄_R; put C_R := ∫_{B̄_R} h dμ < ∞. Each κ^γ, hence h, is μ-a.e. strongly measurable on every B̄_R, hence on ℝ^N = ⋃_{R ∈ ℕ} B̄_R.

2. (Continuous competitors.) Claim: let R > 0 and let f : ℝ^N → Λ^k(ℝ^N) be continuous, with tsupport f compact and contained in B_R, and |f(x)| ≤ 1 for all x. Then x ↦ κ(x)(f(x)) is μ-integrable, and if M < ∞ then ∫ κ(x)(f(x)) dμ ≤ M.toReal.
 (a) Integrability. By 0(a), κ(x)(f(x)) = Σ_γ f(x)_γ κ^γ(x). Each f_γ is continuous, |f_γ| ≤ 1 by 0(b), and f_γ = 0 off B̄_R, while κ^γ is μ-integrable on B̄_R (Step 1).
 (b) Smoothing. Since tsupport f is a compact subset of the open ball B_R, there is d > 0 such that the closed d-thickening of tsupport f is still contained in B_R (IsCompact.exists_cthickening_subset_open; this also covers tsupport f = ∅ and N = 0). Let δ ∈ (0, 1). Every k-covector satisfies |α| ≤ c‖α‖ with c := √m + 1, since |α_γ| = |α(e_γ)| ≤ ‖α‖·∏_j ‖e_{γ(j)}‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm). f is uniformly continuous (continuous with compact support), so choose σ ∈ (0, d) with ‖f(x) − f(y)‖ ≤ δ/c whenever |x − y| < σ. Let ψ : ℝ^N → [0, ∞) be C^∞ with support in the ball B_σ(0) and ∫ψ = 1 (a smooth bump with compact support in B_σ(0), divided by its positive integral). Put η := ψ ⋆ f (convolution: η(x) = ∫ψ(y) f(x − y) dy). Then η is C^∞ (HasCompactSupport.contDiff_convolution_left), its support lies in tsupport f + B_σ(0), so tsupport η lies in the closed σ-thickening of tsupport f, hence is compact and contained in B_R, and ‖η(x) − f(x)‖ ≤ δ/c for every x (dist_convolution_le). Hence |η(x) − f(x)| ≤ δ for every x, and η is a test form, η ∈ TestFormOn univ k.
 (c) If M = ∞ there is nothing to prove; let M < ∞. By (b) and 0(b), |η(x)| ≤ 1 + δ. So η′ := (1 + δ)⁻¹ • η is a test form with tsupport η′ ⊆ univ and |η′(x)| ≤ 1 for all x, i.e. η′ ∈ massAdmissibleOn univ k univ. GeometricCurrentOn.le_massOn gives ENNReal.ofReal(Y(η′)) ≤ Y.massOn univ = M, so Y(η′) ≤ M.toReal, i.e. Y(η) ≤ (1 + δ)M.toReal.
 (d) Y(η) = ∫ κ(η) dμ by the representation. By 0(c), and since η − f vanishes off B_R, |∫ κ(η) dμ − ∫ κ(f) dμ| ≤ ∫_{B̄_R} h·|η − f| dμ ≤ δ·C_R. Hence ∫ κ(f) dμ ≤ (1 + δ)M.toReal + δC_R. Letting δ ↓ 0 gives ∫ κ(f) dμ ≤ M.toReal.

3. (The finite measure ν and the polar field.) Fix R > 0 and ε > 0. By Step 1 choose Borel functions κ̃^γ with κ̃^γ = κ^γ μ-a.e. on B̄_R. Put h̃ := ‖(κ̃^γ)_γ‖ (Borel), Z := {x ∈ B_R : h̃(x) > 0} (Borel), and let u : ℝ^N → ℝ^I be u(x) := (κ̃^γ(x)/h̃(x))_γ for x ∈ Z and u(x) := 0 otherwise. Then u is Borel, ‖u‖ ≤ 1 everywhere and ‖u‖ = 1 on Z. Let ν := (μ⌞B_R).withDensity h̃, i.e. ν(A) = ∫_{A ∩ B_R} h̃ dμ for Borel A. ν is a finite Borel measure: ν(ℝ^N) = ∫_{B_R} h dμ ≤ C_R. Also ν(ℝ^N ∖ Z) = 0. Finally c(κ(x)) = h̃(x)u(x) for μ-a.e. x ∈ B_R: where h̃(x) > 0 this is c(κ̃(x)) = c(κ(x)), and where h̃(x) = 0 both sides vanish (c(κ̃(x)) = 0 and κ^γ = κ̃^γ a.e.).

4. (Continuous approximation.) Claim: there is a continuous map g₀ : ℝ^N → ℝ^I with compact support and ∫ ‖g₀ − u‖ dν < ε.
 (a) u is Borel and bounded and ν is finite, so u ∈ L¹(ν; ℝ^I).
 (b) Indicators. Let t ⊆ ℝ^N be Borel, a ∈ ℝ^I and ϵ > 0. A finite Borel measure on ℝ^N is inner regular with respect to compact sets and outer regular with respect to open sets (MeasurableSet.exists_isCompact_isClosed_sdiff_lt, MeasurableSet.exists_isOpen_sdiff_lt). So there are a compact s ⊆ t with ν(t ∖ s) < ϵ and an open V ⊇ s with ν(V ∖ s) < ϵ. Intersecting V with a relatively compact open neighbourhood of s, we may assume closure V is compact. By Urysohn's lemma (exists_continuous_zero_one_of_isClosed) there is a continuous φ : ℝ^N → [0, 1] with φ = 1 on s and φ = 0 off V. Then φ·a is continuous with compact support, and ∫ ‖φa − 1_t a‖ dν ≤ ‖a‖·(ν(V ∖ s) + ν(t ∖ s)) < 2‖a‖ϵ, because φa − 1_t a vanishes on s and off V ∪ t and has norm ≤ ‖a‖.
 (c) Simple functions Σ_i 1_{t_i} a_i (finitely many Borel t_i) are dense in L¹(ν; ℝ^I) (MemLp.induction_dense, or the standard approximation of integrable functions by simple functions). Approximating u within ε/2 by such a simple function, and each of its finitely many terms within ε/(2·#terms) by (b), gives g₀ by the triangle inequality.

5. (The competitor.) The sets B_R ∖ B̄_{R − 1/j} decrease to ∅ and ν is finite, so choose R′ ∈ (0, R) with ν(B_R ∖ B̄_{R′}) < ε. Let R″ := (R + R′)/2 and χ(x) := min{1, max{0, (R″ − |x|)/(R″ − R′)}}. Then χ is continuous, 0 ≤ χ ≤ 1, χ = 1 on B̄_{R′}, and χ = 0 outside B̄_{R″}. Put f(x) := χ(x)·(π(g₀(x)))♭ (0(e), 0(f)). f is continuous, tsupport f ⊆ B̄_{R″} ⊆ B_R is compact, and |f(x)| = χ(x)·‖π(g₀(x))‖ ≤ 1 by 0(e) and 0(f).

6. (Estimate.) For μ-a.e. x ∈ B_R, κ(x)(f(x)) = χ(x)⟨π(g₀(x)), c(κ(x))⟩ = χ(x)h̃(x)⟨π(g₀(x)), u(x)⟩ (0(e) and Step 3), and f = 0 off B_R. Hence ∫ κ(f) dμ = ∫ χ⟨π(g₀), u⟩ dν. For x ∈ Z, ‖u(x)‖ = 1, so by 0(f) with b := u(x),
 ⟨π(g₀(x)), u(x)⟩ = 1 + ⟨π(g₀(x)) − u(x), u(x)⟩ ≥ 1 − ‖π(g₀(x)) − u(x)‖ ≥ 1 − ‖g₀(x) − u(x)‖.
 Since ν(ℝ^N ∖ Z) = 0, 0 ≤ χ ≤ 1, χ = 1 on B̄_{R′} and ν is carried by B_R,
 ∫ κ(f) dμ ≥ ∫ χ dν − ∫ ‖g₀ − u‖ dν ≥ ν(B̄_{R′}) − ε ≥ ν(ℝ^N) − 2ε.

7. (Conclusion.) If M = ∞ the statement is trivial. Otherwise, by Step 2 applied to f and by Step 6, ∫_{B_R} h dμ = ν(ℝ^N) ≤ ∫ κ(f) dμ + 2ε ≤ M.toReal + 2ε. As ε > 0 is arbitrary, ∫⁻_{B_R} ENNReal.ofReal(h) dμ = ENNReal.ofReal(∫_{B_R} h dμ) ≤ M for every R > 0. Since B_R ↑ ℝ^N as R ↑ ∞ (R ∈ ℕ), monotone convergence gives ∫⁻ ENNReal.ofReal(|κ(x)|) dμ(x) = sup_R ∫⁻_{B_R} ENNReal.ofReal(h) dμ ≤ M. ∎

Remarks. (i) For k > N the index set I is empty, so both sides of the claim are trivial (the left side is ∫⁻ 0 = 0); k = 0 needs no change. (ii) The comparator-accepted declaration fiw_im_mass_formula (another branch; not a dependency here) proves the related identity M_W(τ(M,θ,ξ)) = ∫_{M∩W} θ dHⁿ inside the same import closure. It re-proves the L¹ density of Step 4 (via MemLp.induction_dense, exists_eLpNorm_indicator_le and Urysohn) and the mollification of Step 2(b) (via HasCompactSupport.contDiff_convolution_left and dist_convolution_le); its Lean source at candidate commit 83e1f618 is a usable model for Steps 2 and 4. (iii) Step 2 is the special case U := univ, W := B_R, T := Y, B := M.toReal (Y.massOn B_R ≤ Y.massOn univ = M = ofReal(M.toReal)), C := 1, ω := f of the comparator-accepted declaration cmb_measureRepresentation_continuous_bound (DAG node root.compactness_mass_bounds-a1.repr_bound-a1), which gives integrability of κ(f) and |∫ κ(f) dμ| ≤ M.toReal. If this child is decomposed further, that declaration can be reused by name for Step 2, and the mollification in Step 2(b) is then not needed.

## Key steps

1. Pairing expansion, |α|² = Σ_γ α(e_γ)², Cauchy–Schwarz |w(α)| ≤ |α||w|, Kronecker dx^γ(e_β) = δ_{γβ}, a♭ := Σ a_γ dx^γ with |a♭| = ‖a‖, and the 1-Lipschitz radial retraction π onto the unit ball of ℝ^I.
2. Test forms φ_R dx^γ give μ-integrability of the coordinates κ^γ on balls, so h = |κ| is locally integrable and a.e. measurable.
3. Every continuous f with compact support in B_R and |f| ≤ 1 satisfies ∫κ(f) dμ ≤ M(Y): convolution with a smooth bump, rescaling by (1+δ)⁻¹ into massAdmissibleOn, Cauchy–Schwarz error δ∫_{B̄_R}h.
4. ν := |κ|μ⌞B_R is a finite Borel measure and u = κ/|κ| a Borel unit field; regularity, Urysohn and density of simple functions give a continuous compactly supported g₀ with ∫‖g₀ − u‖dν < ε.
5. f := χ·(π∘g₀)♭ is admissible and ∫κ(f) dμ = ∫χ⟨π(g₀), u⟩dν ≥ ν(ℝ^N) − 2ε; hence ∫_{B_R}|κ| dμ ≤ M(Y), and monotone convergence in R.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp <snapshot>/project/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Submission.lean (all byte-identical)`
- `grep '^import' <snapshot>/project/GMT/Ch06/Contract.lean (8 imports) and a transitive SimonGMT import-closure walk (13 modules; Chapter01.Lusin not included)`
- `rg -n 'theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le|exists_hasCompactSupport_integral_sub_le' <snapshot>/mathlib/Mathlib (ContinuousMapDense.lean:141, :226); rg -n 'theorem ContinuousMap.exists_extension' <snapshot>/mathlib/Mathlib (TietzeExtension.lean:77): both files are outside the frozen closure`
- `rg -n 'theorem cauchySeq_of_edist_le_of_tsum_ne_top|theorem edist_le_tsum_of_edist_le_of_tendsto|theorem tendsto_integral_of_L1|theorem lintegral_tsum|theorem integral_indicator₀|theorem dist_convolution_le|theorem exists_continuous_zero_one_of_isClosed' <snapshot>/mathlib/Mathlib`
- `rg -n 'imc_' <snapshot>/project <snapshot>/mathlib and lake-packages-25730c7c/simongmt (no match); git log --all -S <each new imc_ name> (no commit); grep of the new names over runs/*/nodes (no match)`
- `python3 -I over dag.json: status, candidate commit, parent and lean_statement of the five reused names and of lpf_wtc_ae_zero_density_off_set; comparison of every new child type against all DAG node types (no duplicate); simulation of runtime.py _existing_lean_name_problem/_accepted_checkpoint and _topological on the current DAG (no problem; acyclic)`
- `sed -n 6532,6575p /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (reuse rule), leaf_verification.py check_source_delta (no set_option in a leaf delta), decomposition_scope.py (recomputed parent_contract_digest 94deade2…)`
- `git show 12d217bba2a4:GMT/Ch06/Submission.lean (accepted zero-density proof) and git show 83e1f61809c1:GMT/Ch06/Submission.lean (accepted fiw_im_mass_formula: inline L¹ density and mollification)`
- `lake env lean /tmp/imc_v2/lean/Avail2.lean, Api3–Api7.lean (closure probes: Tietze, ContinuousMapDense, UniformContinuous.exists_contDiff_dist_le and Measurable.nat_floor absent; ContDiffBump, HasCompactSupport.contDiff_convolution_left and Lp.ae_tendsto_of_cauchy_eLpNorm present; NVector ContinuousAdd/PseudoMetrizableSpace workarounds)`
- `python3 -I /tmp/imc_v2/scripts/build_stmts.py (validate_lean_statement on all 13 types) and lake env lean /tmp/imc_v2/lean/Stmts.lean (all elaborate; only sorry warnings)`
- `lake env lean /tmp/imc_v2/lean/Test_deformation_im_completeness.lean, Test_imc_im_density_limit.lean, Test_imc_isRectifiableTriple_of_eventually_mem.lean, Test_imc_ae_tendsto_of_summable_lintegral.lean, Test_imc_ae_zero_density_off_set.lean (all compile at default heartbeats; standard axioms plus the stand-in sibling axioms)`
- `sed -n 560,735p book/sources/chapter-01-source.txt (Simon Ch. 1, 3.3–3.7 and the 5-times covering lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-lusi-5c440af24d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-blow-7c8d1035a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-mass-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/decomposition_scope.py`
- `/tmp/imc_v2/lean/Stmts.lean`
- `/tmp/imc_v2/lean/Test_deformation_im_completeness.lean`
- `/tmp/imc_v2/lean/Test_imc_im_density_limit.lean`
- `/tmp/imc_v2/lean/Test_imc_isRectifiableTriple_of_eventually_mem.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_tendsto_of_summable_lintegral.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_zero_density_off_set.lean`

Pinned revisions confirmed: the frozen contract is byte-identical to the snapshot (Submission = Contract). The frozen import closure lacks Tietze (TietzeExtension.lean), L¹ density of C_c (ContinuousMapDense.lean) and SimonGMT Lusin. So mass_lower_bound's approximation step is proved inline from regularity, Urysohn and MemLp.induction_dense, as the accepted fiw_im_mass_formula does. Mathlib supplies the Riesz–Fischer and limit tools used by l1_cauchy_limit and density_limit (cauchySeq_of_edist_le_of_tsum_ne_top, edist_le_tsum_of_edist_le_of_tendsto, tendsto_integral_of_L1). Following the correction, the zero-density child uses the fresh name imc_ae_zero_density_off_set and is the W = ℝ^Q case of the accepted lpf_wtc_ae_zero_density_off_set; its Lean proof embeds that accepted proof (commit 12d217bb) and compiles. The five reused names are accepted checkpoints with identical types, and the controller's name check simulated on the current DAG passes. All 13 types validate and elaborate in the comparator scope. The parent compiles from mass_lower_bound, density_limit and tau_integrable; density_limit, limit_triple and l1_cauchy_limit also compile from their siblings; all at default heartbeats with axioms propext, Classical.choice and Quot.sound only. No imc_ name occurs in the project, SimonGMT, Mathlib, git history or the DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
