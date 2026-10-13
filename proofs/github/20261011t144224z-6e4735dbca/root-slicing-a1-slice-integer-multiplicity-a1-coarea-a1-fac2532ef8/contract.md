<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1 -->

## Theorem `Submission.slicing_im_coarea`

Let P, m ∈ ℕ, n := m+1, U ⊆ ℝ^P open, (M, θ, ξ) with IsRectifiableTriple U n M θ ξ, f : ℝ^P → ℝ L-Lipschitz, and G : ℝ^P → ℝ^P Borel with |G(x)| ≤ L for all x and with the tangential-gradient property: for Hⁿ-a.e. x ∈ M and every weighted approximate tangent plane Q of (M, θ) at x, G(x) ∈ Q and s ↦ f(x + su) has derivative ⟨G(x), u⟩ at 0 for all u ∈ Q. Then for every Borel g : ℝ^P → [0, ∞] the function t ↦ ∫_{M∩f⁻¹{t}} g dH^m (the integral of g against the restriction of H^m to M ∩ f⁻¹{t}) is a.e.-measurable for Lebesgue measure on ℝ, and ∫_ℝ ∫_{M∩f⁻¹{t}} g dH^m dt = ∫_M |G| g dHⁿ (Hᵏ := μHE[k]).

Node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/678

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3389, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3394, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3405, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3410, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3422, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3428, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3440, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3443, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3444

## Lean problem

Declaration: `Submission.slicing_im_coarea`

```lean
∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → ∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P; Hᵏ := μHE[k] (Mathlib's Euclidean Hausdorff measure, equal to Lebesgue measure Lᵏ on ℝᵏ; H⁰ is counting measure by `euclideanHausdorffMeasure_zero` and `hausdorffMeasure_zero_singleton`). n := m+1. A k-covector is α ∈ Covector (Eucl P) k (continuous alternating k-form), ‖α‖ its operator norm; a k-vector is w ∈ NVector (Eucl P) k = (Covector (Eucl P) k →L[ℝ] ℝ); simple(τ) := simpleNVector τ, simple(τ)(α) = α(τ). For w ∈ ℝ^P and α ∈ Λ^k put w♭∧α := ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ w).smulRight α) ∈ Λ^{k+1}; by `alternatizeUncurryFin_apply`, (w♭∧α)(v₀,…,v_k) = Σ_{i=0}^{k} (−1)^i ⟨w, v_i⟩ α(v₀,…,v̂_i,…,v_k); it is bilinear in (w, α), ‖w♭∧α‖ ≤ (k+1)|w|‖α‖, and it equals ((alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (smulRightL ℝ (Eucl P) (Covector (Eucl P) k) (innerSL ℝ w))) α by `rfl`. Fact U: if τ is orthonormal and w = ±simple(τ) then |w(α)| = |α(τ)| ≤ ‖α‖·∏|τ_i| = ‖α‖. Fact F (frame sign): if τ, τ' are orthonormal bases of the same k-dimensional subspace, τ'_i = Σ_j B_ij τ_j with B orthogonal, then by multilinearity and alternation simple(τ') = det(B)·simple(τ) and det B = ±1. IsRectifiableTriple U k M θ ξ means: M ⊆ U; M is Hᵏ-null-measurable; M is countably k-rectifiable; θ > 0 on M; θ is Hᵏ-integrable on M ∩ K for every compact K ⊆ U; ξ is Hᵏ⌞M-a.e. strongly measurable; for Hᵏ-a.e. x ∈ M there is an orthonormal τ : Fin k → ℝ^P with HasWeightedApproximateTangentSpaceAt k M θ x (span τ) and ξ(x) = ±simple(τ). The weighted approximate tangent plane (Simon Ch. 3, 1.7) is unique at points where θ(x) ≠ 0 (SimonGMT `HasWeightedApproximateTangentSpaceAt.unique`); when it exists at x ∈ M we call it T_x. TG(f, G) abbreviates the tangential-gradient property: for Hⁿ-a.e. x ∈ M and every Q with HasWeightedApproximateTangentSpaceAt n M θ x Q, G(x) ∈ Q and for every u ∈ Q the map s ↦ f(x + s u) has derivative ⟨G(x), u⟩ at s = 0.
This is Simon Ch. 3, (2.8)–(2.9) for real-valued f (there J*_f = |∇^M f|); we follow the printed proof: the C¹ case (Simon Ch. 2, 6.3 and 6.6) on the pieces of the decomposition of Remark 1.3, combined with the C¹ approximation theorem (Simon Ch. 2, 1.5).
1. Charts (Simon Ch. 3, Lemma 1.2 and Remark 1.3). Since M is countably n-rectifiable, M ⊆ N₀ ∪ ⋃_{j≥1} N_j with Hⁿ(N₀) = 0 and N_j embedded C¹ n-dimensional submanifolds of ℝ^P. Covering every N_j by countably many relatively compact coordinate patches we obtain countably many open Ω_j ⊆ ℝⁿ and C¹ maps Φ_j : ℝⁿ → ℝ^P which are Lipschitz on Ω_j and satisfy c_j|w − w'| ≤ |Φ_j(w) − Φ_j(w')| (w, w' ∈ Ω_j, some c_j > 0), with Hⁿ(M ∖ ⋃_j Φ_j(Ω_j)) = 0. Consequently Φ_j|Ω_j is injective, DΦ_j(w) is injective for w ∈ Ω_j (|DΦ_j(w)u| ≥ c_j|u|), Φ_j(Ω_j) is σ-compact hence Borel, (Φ_j|Ω_j)⁻¹ is (1/c_j)-Lipschitz hence Borel, Φ_j maps Lⁿ-null subsets of Ω_j to Hⁿ-null sets and Φ_j⁻¹ maps Hⁿ-null subsets of Φ_j(Ω_j) to Lⁿ-null sets. Put A_j(w) := DΦ_j(w) and T_j(w) := range A_j(w) (an n-dimensional subspace). Since M is Hⁿ-null-measurable there is a Borel B ⊆ M with Hⁿ(M ∖ B) = 0 (`NullMeasurableSet.exists_measurable_subset_ae_eq`).
2. (C¹ approximation.) Fix j. f∘Φ_j is Lipschitz on Ω_j; let u_j be a Lipschitz extension to ℝⁿ (`LipschitzOnWith.extend_real`). By the C¹ approximation theorem (Simon Ch. 2, Theorem 1.5) applied to u_j with ε = 1/k, k ≥ 1, there are C¹ functions h_{jk} : ℝⁿ → ℝ and Borel sets A_{jk} ⊆ Ω_j with Lⁿ(Ω_j ∖ ⋃_k A_{jk}) = 0 such that on A_{jk}: f∘Φ_j is differentiable, f∘Φ_j = h_{jk} and D(f∘Φ_j) = Dh_{jk}. (Take A_{jk} := Ω_j ∩ D ∩ {u_j = h_{jk}, ∇u_j = ∇h_{jk}} with D the Borel set of differentiability points of u_j.)
3. (Gradient identification.) Directional derivatives (Simon Ch. 2, 4.10). Let Φ be C¹ near w, x = Φ(w), F : ℝ^P → ℝ Lipschitz with constant C, and suppose F∘Φ is differentiable at w. Then for every u ∈ ℝⁿ, s ↦ F(x + s DΦ(w)u) has derivative D(F∘Φ)(w)u at s = 0: indeed F(x + sDΦ(w)u) − F(x) = [F(Φ(w+su)) − F(Φ(w))] + [F(x + sDΦ(w)u) − F(Φ(w+su))], the first bracket is sD(F∘Φ)(w)u + o(s), and the second is bounded by C|Φ(w) + sDΦ(w)u − Φ(w+su)| = o(s). Tangent identification (Simon Ch. 3, Remark 1.5(2), proof of Theorem 1.6 '⟹' and Remark 1.8(1), weighted version): if M' ⊆ U is Hᵏ-null-measurable, θ > 0 on M' and θ is Hᵏ-integrable on M' ∩ K for compact K ⊆ U, and Ψ : ℝᵏ → ℝ^P is C¹ on an open V ⊆ ℝᵏ, Lipschitz on V with a positive lower Lipschitz bound on V, then for Hᵏ-a.e. x ∈ M' ∩ Ψ(V) the pair (M', θ) has weighted approximate tangent plane range DΨ(Ψ⁻¹x) at x. (For φ ∈ C_c(ℝ^P), r^{-k}∫_{M'} φ((z−x)/r)θ(z) dHᵏ(z) splits into θ(x)·r^{-k}∫_{Ψ(V)} φ((z−x)/r) dHᵏ, which tends to θ(x)∫_{range DΨ} φ dHᵏ because Ψ(V) is a C¹ k-submanifold at x; the error r^{-k}∫_{M'∩Ψ(V)} φ(·)(θ − θ(x)) dHᵏ, which tends to 0 at Lebesgue points of θ for the Radon measure Hᵏ⌞(M'∩Ψ(V)∩K); and the parts over Ψ(V) ∖ M' and M' ∖ Ψ(V), which tend to 0 at Hᵏ-a.e. point of M' ∩ Ψ(V) by the upper-density theorem, Simon Ch. 1, 3.6, since Hᵏ⌞(Ψ(V)∖M') and θHᵏ⌞(M'∖Ψ(V)) are locally finite and vanish on M' ∩ Ψ(V).) Uniqueness at θ(x) > 0 then identifies every weighted approximate tangent plane at such x with range DΨ(Ψ⁻¹x). Applying the tangent identification with k = n, M' = M, Ψ = Φ_j, together with TG(f, G), we get an Hⁿ-null set Z_j such that for x ∈ (M ∩ Φ_j(A_{jk})) ∖ Z_j, w := (Φ_j|Ω_j)⁻¹(x): the weighted tangent plane is T_x = T_j(w), G(x) ∈ T_j(w), and for every u ∈ ℝⁿ, ⟨G(x), A_j(w)u⟩ = (d/ds) f(x + sA_j(w)u)|_{s=0} = D(f∘Φ_j)(w)u = Dh_{jk}(w)u. Let N_j := Φ_j(Ω_j), an embedded C¹ n-submanifold, and F_{jk} := h_{jk}∘(Φ_j|Ω_j)⁻¹ : N_j → ℝ, a C¹ function on N_j. Its N_j-gradient at x = Φ_j(w) is the vector of T_j(w) representing u ↦ Dh_{jk}(w)u on A_j(w)u, so ∇^{N_j}F_{jk}(x) = G(x) and F_{jk}(x) = f(x) for those x.
4. (Pieces.) Enumerate the pairs (j, k) and let W_{jk} be the disjointification of the Borel sets (B ∩ Φ_j(A_{jk})) ∖ Z'_j, where Z'_j ⊇ Z_j is a Borel Hⁿ-null set (`toMeasurable`). The sets Φ_j(A_{jk}) are Borel (Lusin–Souslin, `MeasurableSet.image_of_continuousOn_injOn`), so the W_{jk} are pairwise disjoint Borel subsets of M, and Z := M ∖ ⋃ W_{jk} ⊆ (M ∖ B) ∪ (M ∖ ⋃_j Φ_j(Ω_j)) ∪ ⋃_j Φ_j(Ω_j ∖ ⋃_k A_{jk}) ∪ ⋃_j Z'_j is Hⁿ-null (Φ_j maps Lⁿ-null sets to Hⁿ-null sets).
5. (Null part, Eilenberg's inequality.) For every set A ⊆ ℝ^P, ∫* H^m(A ∩ f⁻¹{t}) dt ≤ c(m)·L·Hⁿ(A) (Federer 2.10.25). With A = Z this gives H^m(Z ∩ f⁻¹{t}) = 0 for L¹-a.e. t. For such t the sets M ∩ f⁻¹{t} and ⋃_{jk}(W_{jk} ∩ f⁻¹{t}) differ by an H^m-null set, so the restrictions of H^m to them coincide (`Measure.restrict_congr_set`), and, the W_{jk} ∩ f⁻¹{t} being disjoint Borel sets, ∫_{M∩f⁻¹{t}} g dH^m = Σ_{jk} ∫_{W_{jk}∩f⁻¹{t}} g dH^m.
6. (C¹ co-area formula on a piece.) Fix (j, k). On the C¹ n-submanifold N_j the function F_{jk} is C¹ with co-area Jacobian J F_{jk} = |∇^{N_j}F_{jk}| (for a real-valued map, √det(dF∘dF*) = |∇F|). By the co-area formula for C¹ maps on C¹ submanifolds (Simon Ch. 2, 6.3 and its consequence 6.6 for non-negative measurable integrands; Federer 3.2.12, 3.2.22), for the Borel set W_{jk} ⊆ N_j and Borel g ≥ 0, the function t ↦ ∫_{W_{jk}∩F_{jk}⁻¹{t}} g dH^m is Lebesgue measurable and ∫_ℝ ∫_{W_{jk}∩F_{jk}⁻¹{t}} g dH^m dt = ∫_{W_{jk}} g |∇^{N_j}F_{jk}| dHⁿ. By Step 3 (F_{jk} = f and ∇^{N_j}F_{jk} = G on W_{jk}), W_{jk} ∩ F_{jk}⁻¹{t} = W_{jk} ∩ f⁻¹{t} and ∫_ℝ ∫_{W_{jk}∩f⁻¹{t}} g dH^m dt = ∫_{W_{jk}} |G| g dHⁿ.
7. (Summation.) By Step 5 the function Ψ_g(t) := ∫_{M∩f⁻¹{t}} g dH^m agrees for L¹-a.e. t with the countable sum Σ_{jk} ∫_{W_{jk}∩f⁻¹{t}} g dH^m of Lebesgue-measurable [0,∞]-valued functions, hence is a.e.-measurable. By monotone convergence (`lintegral_tsum`) and Step 6, ∫_ℝ Ψ_g dt = Σ_{jk} ∫_{W_{jk}} |G| g dHⁿ = ∫_{⋃W_{jk}} |G| g dHⁿ = ∫_M |G| g dHⁿ, the last step because Hⁿ(M ∖ ⋃ W_{jk}) = Hⁿ(Z) = 0. ∎

## Key steps

1. Charts Φ_j and a Borel B ⊆ M of full measure (Simon Ch. 3, 1.2–1.3).
2. C¹ approximation of f∘Φ_j (Simon Ch. 2, 1.5): Borel A_{jk} where f∘Φ_j = h_{jk} with equal derivatives.
3. Simon Ch. 2, 4.10 and the weighted tangent identification: on the pieces, f = F_{jk} := h_{jk}∘Φ_j⁻¹ and ∇^{N_j}F_{jk} = G.
4. Eilenberg's inequality: the Hⁿ-null remainder has H^m-null slices for a.e. t.
5. C¹ co-area formula on each C¹ piece with Jacobian |∇^{N_j}F_{jk}| = |G| (Simon Ch. 2, 6.3, 6.6; Federer 3.2.22).
6. Sum over the disjoint Borel pieces (monotone convergence) and use a.e. equality for measurability.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical); read Contract.lean: IsRectifiableTriple, tauAction, IsIntegerMultiplicity, IsMeasureRepresentation, IsRestriction, IsSlice`
- `grep -n '^def |^theorem |^structure |^abbrev |^noncomputable def ' simongmt Chapter03/{Rectifiable,Differential}.lean and Chapter06/{Forms,FormsDuality,Currents,Mass,WedgeForms,CurrentLocalEquality}.lean`
- `grep -rn 'def alternatizeUncurryFinCLM|def smulRightL|def innerSL' mathlib/Mathlib`
- `grep -rn 'theorem LipschitzOnWith.extend_real|theorem ae_ball_iff|theorem LipschitzWith.ae_differentiableAt|theorem ae_tendsto_average|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem exists_measurable_subset_ae_eq|theorem MeasurableSet.image_of_continuousOn_injOn|theorem lintegral_tsum|theorem restrict_congr_set|theorem norm_iteratedFDeriv_zero|theorem iteratedFDeriv_sub|theorem fderiv_smul|aestronglyMeasurable_iUnion_iff|contDiff_convolution_left' mathlib/Mathlib`
- `grep -rn 'μHE\[' mathlib/Mathlib; read Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, euclideanHausdorffMeasure_zero)`
- `read mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean (ContinuousMap.instSecondCountableTopology)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission in scratch /tmp/sim_split (frozen d8d46c9, shared packages lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean (seven child types and the parent type in the exact comparator scope; 0 errors; #print output checked for binder scopes)`
- `lake env lean Scratch/Assembly.lean (parent type from children tangential_gradient, slice_triple, slice_identity, testform_determining, tau_current; #print axioms)`
- `lake env lean Scratch/Api.lean (interior-product CLM evaluates by rfl to alternatizeUncurryFin ((innerSL ℝ w).smulRight α); alternatizeUncurryFin expansion; cited lemma signatures)`
- `python3 scan of dag.json lean_name values (260 nodes) for the seven proposed names and for reusable accepted declarations (rectifiability_weighted_tangent_ae, cmb_exists_countable_dense_testForms, lpf_pic_current_of_dominated_density, lpf_weighted_tangent_on_c1_chart, lpf_countably_rectifiable_c1_cover)`
- `rg 'slicing_im_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project (no match)`
- `sed book/chapter-06.txt §4 (4.1–4.6), chapter-03.txt §1–2 (1.2–1.9, 2.1–2.10), chapter-02.txt (1.5, 4.5–4.14, 6.1–6.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/decomposition-v1.json`
- `/tmp/sim_split/Scratch/Stmts.lean`
- `/tmp/sim_split/Scratch/Assembly.lean`
- `/tmp/sim_split/Scratch/Api.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract; Submission is byte-identical, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies currents, test forms, TestFormOnConverges, simpleNVector and the weighted approximate tangent plane with uniqueness at θ(x) ≠ 0. It has no tangential gradient for Lipschitz functions on rectifiable sets, no co-area formula beyond the linear case and no slicing; Mathlib has none of these either. Those results (Simon Ch. 2, 1.5, 4.10, 6.3–6.6; Ch. 3, 1.2–1.9, 2.1–2.10; Federer 2.10.25, 3.2.22) are therefore cited inside the child proofs. Mathlib does provide: McShane (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzWith.ae_differentiableAt`), Lebesgue differentiation (`IsUnifLocDoublingMeasure.ae_tendsto_average`), `ae_ball_iff`, `measurable_fderiv`, Lusin–Souslin images, `alternatizeUncurryFinCLM`/`smulRightL`/`innerSL` and second countability of C(K, F). The interior product ξ⌞(G/|G|) is written with these CLMs and evaluates by `rfl` to ξ(ν♭∧α). All seven child types elaborate in the comparator scope with the intended binder structure. The parent type is kernel-checked from five of them (axioms propext, Classical.choice, Quot.sound). None of the seven names occurs in the snapshot project or among the 260 DAG nodes. The chart-cover and C¹-chart tangent lemmas of the lipschitz-pushforward branch are not yet accepted, so they cannot be reused; no accepted declaration has an identical type to any child. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
