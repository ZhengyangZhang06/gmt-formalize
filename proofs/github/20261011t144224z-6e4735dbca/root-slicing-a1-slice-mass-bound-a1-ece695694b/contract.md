<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_mass_bound-a1 -->

## Theorem `Submission.slicing_mass_bound`

For all P, m, every open U ⊆ ℝ^P, every T ∈ D_{m+1}(U) with M_W(T) < ∞ and M_W(∂T) < ∞ for all open W ⊂⊂ U, every f : ℝ^P → ℝ which is L-Lipschitz on U, and every family S : ℝ → D_m(U) with IsSlice T f t (S t) for every t: for every open W ⊆ U, every L_W ≥ 0 with ‖Df(x)‖ ≤ L_W for Lebesgue-a.e. x ∈ W (Df = fderiv), every a < b and every R with IsRestriction T {x ∈ U : a < f(x) < b} R, there is a measurable g : ℝ → [0,∞] with M_W(S t) ≤ g(t) for all t ∈ (a,b) and ∫_{(a,b)} g dt ≤ L_W·M_W(R).

Node: `root.slicing-a1.slice_mass_bound-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/322

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/664, https://github.com/ZhengyangZhang06/gmt-formalize/issues/666

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1869, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1871, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1874, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1881, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1883, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1888, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1894

## Lean problem

Declaration: `Submission.slicing_mass_bound`

```lean
∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ S : ℝ → GeometricCurrentOn U m, (∀ t, IsSlice T f t (S t)) → ∀ W, IsOpen W → W ⊆ U → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → ∀ a b : ℝ, a < b → ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W
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

- Parent DAG node: `root.slicing-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (as in the parent proof). D^k(U) is the space of test k-forms on U (smooth, compact support, tsupport ⊆ U; `TestFormOn U k`), D_k(U) the currents (`GeometricCurrentOn U k`: linear, and X(ω_j) → 0 whenever ω_j → 0 in D^k(U), i.e. all tsupports lie in one compact K ⊆ U and every iterated derivative of ω_j tends to 0 uniformly on K). I(k,P) is the set of strictly increasing β : {1,…,k} → {1,…,P}; e_β := (e_{β_1},…,e_{β_k}); dx^β is the coordinate k-covector, dx^β(e_γ) = δ_{βγ} for β, γ ∈ I(k,P). Fact A: every k-covector α equals Σ_β α(e_β) dx^β, and |α|² = Σ_β α(e_β)², where |α| := covectorEuclideanNorm α. A k-vector is a continuous linear functional w on k-covectors (`NVector`); put w^β := w(dx^β), so w(α) = Σ_β α(e_β) w^β and |w(α)| ≤ |α|·|w| with |w| := (Σ_β (w^β)²)^{1/2} (Cauchy–Schwarz). For a form ω, ‖ω‖ := sup_x |ω(x)|. M_W(X) = X.massOn W is the supremum of X(ω) over ω ∈ D^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. ρ_ε is a standard mollifier (smooth, ≥ 0, supported in the closed ε-ball, ∫ρ_ε = 1); for a continuous compactly supported form φ, ρ_ε*φ (componentwise convolution) is smooth, supported in the closed ε-neighbourhood of tsupport φ, satisfies |ρ_ε*φ(x)| ≤ ‖φ‖ (|·| is a norm, hence convex) and ρ_ε*φ → φ uniformly as ε ↓ 0. All measures are Borel measures on ℝ^P = Eucl P.

Source: Simon Ch. 6, 4.9–4.11 (pp. 157–158), including the closing sentence “To handle general Lipschitz f we simply use f^{(σ)} in place of f … then let σ ↓ 0”, i.e. the parent proof's Steps 3–4, with the parent's errata: (i) the right side of 4.10 is M_W(T⌞{a<f<b}) (printed M(T⌞{a<f<b})); (ii) ess sup_W|Df| is used as “any L_W ≥ |Df| a.e. on W”; (iii) in 4.11 “the first part of 4.11” reads “the first part of 4.9”; (iv) the argument is written for the slice ⟨T,f,t₋⟩ of 4.6. The parent's preliminaries R1–R3 are replaced by the siblings `slicing_mass_representation` and `slicing_representation_unique`, and the argument is run for an arbitrary family S with IsSlice T f t (S t). Products in [0,∞] use 0·∞ = 0.

Setting. P, m, U open; T ∈ D_{m+1}(U) with M_W(T) < ∞ and M_W(∂T) < ∞ for every open W with compact closure ⊆ U; f : ℝ^P → ℝ with |f(x) − f(y)| ≤ L|x−y| for x, y ∈ U; S : ℝ → D_m(U) with IsSlice T f t (S t) for every t; W ⊆ U open; L_W ≥ 0 with ‖Df(x)‖ ≤ L_W for Lebesgue-a.e. x ∈ W (Df(x) = fderiv ℝ f x); a < b; R ∈ D_{m+1}(U) with IsRestriction T A_ab R, A_ab := {x | x ∈ U ∧ a < f x ∧ f x < b}.

1. (Normalized representation of T.) Apply `slicing_mass_representation` to X := T (degree m+1). It gives μ_T, T⃗ with: IsMeasureRepresentation T μ_T T⃗; μ_T(K) < ∞ for every compact K ⊆ U; |T⃗(x)(α)| ≤ |α| for all x and all (m+1)-covectors α; and, for every Borel A and every Y ∈ D_{m+1}(U) with Y(η) = ∫_A T⃗(η) dμ_T for all η, M_{W′}(Y) = μ_T(W′ ∩ A) for every open W′ ⊆ U. In particular, for every η ∈ D^{m+1}(U),
 (**) |T(η)| = |∫ T⃗(x)(η(x)) dμ_T| ≤ ∫ |η(x)| dμ_T(x).

2. (Identification of R, R2.) IsRestriction T A_ab R gives that A_ab is measurable and a pair (μ_R, v_R) with IsMeasureRepresentation T μ_R v_R and R(η) = ∫_{A_ab} v_R(η) dμ_R for all η. Both pairs represent T, so ∫ v_R(η) dμ_R = T(η) = ∫ T⃗(η) dμ_T for every η ∈ D^{m+1}(U); `slicing_representation_unique` (degree m+1, open set ℝ^P) gives ∫_{A_ab} v_R(η) dμ_R = ∫_{A_ab} T⃗(η) dμ_T, i.e. R(η) = ∫_{A_ab} T⃗(η) dμ_T for all η. By step 1 (with A := A_ab, Y := R, W′ := W), M_W(R) = μ_T(W ∩ A_ab) =: Q ∈ [0,∞].

3. (Auxiliary facts.)
 (i) (McShane, `LipschitzOnWith.extend_real`.) There is f̃ : ℝ^P → ℝ, L-Lipschitz on ℝ^P, with f̃ = f on U. For σ > 0 let f_σ := ρ_σ * f̃; f_σ is smooth on ℝ^P and |f_σ − f̃| ≤ Lσ everywhere.
 (ii) (Rademacher, `LipschitzOnWith.ae_differentiableWithinAt_of_mem` for the open set U.) f is differentiable at a.e. point of U, and since f̃ = f near every point of U, Df̃ = Df there. With the hypothesis: for a.e. z ∈ W, f̃ is differentiable at z and ‖Df̃(z)‖ ≤ L_W.
 (iii) (Gradient bound.) Let K ⊆ W be compact and δ₀ > 0 with the closed 2δ₀-neighbourhood K_{2δ₀} of K contained in W. For 0 < σ < δ₀, x ∈ K and a unit vector e: (f_σ(x+se) − f_σ(x))/s = ∫ ρ_σ(y)(f̃(x+se−y) − f̃(x−y))/s dy; the integrand is bounded by Lρ_σ(y) and, for 0 < |s| < δ₀, x − y ∈ K_{2δ₀} ⊆ W for |y| ≤ σ, so by (ii) (the exceptional set is Lebesgue-null and Lebesgue measure is translation invariant) it converges to ρ_σ(y)Df̃(x−y)e for a.e. y as s → 0. By dominated convergence Df_σ(x)e = ∫ ρ_σ(y)Df̃(x−y)e dy, hence |Df_σ(x)e| ≤ L_W. So ‖Df_σ(x)‖ ≤ L_W for x ∈ K.
 (iv) (R5.) For a 1-covector α and an m-covector γ, |α∧γ| ≤ |α||γ|: if α ≠ 0 choose an orthonormal basis ε₁,…,ε_P with α = |α|ε₁*; the Euclidean coefficient norm is the norm of the inner product induced on covectors, so it may be computed in this basis; writing γ = Σ_β c_β ε^β, α∧γ = |α|Σ_{β ∌ 1} c_β ε^1∧ε^β with pairwise distinct multi-indices, so |α∧γ|² = |α|²Σ_{β∌1}c_β² ≤ |α|²|γ|². For smooth g, |dg(x)| = ‖Dg(x)‖.
 (v) (Cut-offs.) For h > 0 and ε > 0 there is a smooth nonincreasing χ = χ_{h,ε} : ℝ → [0,1] with χ = 1 on (−∞, t−h], χ = 0 on [t,∞) and |χ′| ≤ (1+ε)/h (mollify, with radius < κ, the piecewise linear function equal to 1 on (−∞, t−h+κ], to 0 on [t−κ,∞) and linear in between, κ > 0 small); then χ′ = 0 outside (t−h, t).

4. (Pointwise bound 4.9, for every t ∈ ℝ.) Fix t. IsSlice T f t (S t) gives currents A, B, a representation (μ, v) of T and a representation (μ′, v′) of ∂T such that A(η) = ∫_{A_t} v(η) dμ, B(ω) = ∫_{A_t} v′(ω) dμ′ and (S t)(ω) = A(dω) − B(ω), where A_t := {x ∈ U : f(x) < t}. Fix ω admissible for M_W(S t): ω ∈ D^m(U), K := tsupport ω ⊆ W, |ω(x)| ≤ 1. If K = ∅ then (S t)(ω) = 0; otherwise choose δ₀ as in 3(iii). Fix h > 0, ε > 0, χ := χ_{h,ε} and 0 < σ < δ₀.
 (4a) (4.11.) χ∘f_σ is smooth, so χ(f_σ)ω ∈ D^m(U) with tsupport ⊆ K, and d(χ(f_σ)ω) = χ′(f_σ)df_σ∧ω + χ(f_σ)dω with both terms in D^{m+1}(U), tsupport ⊆ K. Hence ∂T(χ(f_σ)ω) − T(χ(f_σ)dω) = T(χ′(f_σ)df_σ∧ω).
 (4b) By the representations from IsSlice, ∂T(χ(f_σ)ω) = ∫ χ(f_σ)v′(ω) dμ′ and T(χ(f_σ)dω) = ∫ χ(f_σ)v(dω) dμ.
 (4c) By (**), (iv) and (iii): |T(χ′(f_σ)df_σ∧ω)| ≤ ∫ |χ′(f_σ)||df_σ||ω| dμ_T ≤ ((1+ε)/h)·L_W·μ_T(K ∩ {t−h < f_σ < t}) ≤ ((1+ε)/h)·L_W·μ_T(K ∩ {x ∈ U : t−h−Lσ < f(x) < t+Lσ}), because χ′(f_σ(x)) ≠ 0 only if t−h < f_σ(x) < t, and |f_σ − f| ≤ Lσ on K ⊆ U.
 (4d) Let σ ↓ 0. f_σ → f̃ uniformly on ℝ^P, so χ(f_σ) → χ(f̃) uniformly; the integrands v′(ω), v(dω) are integrable and vanish off K; by dominated convergence the two integrals in (4b) converge to ∫ χ(f̃)v′(ω) dμ′ and ∫ χ(f̃)v(dω) dμ (χ∘f̃ is continuous on ℝ^P, and f̃ = f on K ⊆ U). As σ ↓ 0 the sets K ∩ {x ∈ U : t−h−Lσ < f(x) < t+Lσ} decrease, their intersection is contained in K ∩ {x ∈ U : t−h ≤ f(x) ≤ t} (with equality if L > 0), and μ_T(K) < ∞; hence lim_{σ↓0} μ_T(K ∩ {t−h−Lσ < f < t+Lσ}) ≤ μ_T(K ∩ {t−h ≤ f ≤ t}). Hence
 |∫ χ(f̃)v′(ω) dμ′ − ∫ χ(f̃)v(dω) dμ| ≤ ((1+ε)/h)·L_W·μ_T(K ∩ {x ∈ U : t−h ≤ f(x) ≤ t}).
 (4e) Let h ↓ 0 (with χ = χ_{h,ε}). For x ∈ U, χ_{h,ε}(f̃(x)) = χ_{h,ε}(f(x)) → 1_{A_t}(x) (it equals 1 once h < t − f(x) if f(x) < t, and 0 if f(x) ≥ t); the integrands vanish off K ⊆ U; by dominated convergence the left side tends to |B(ω) − A(dω)| = |(S t)(ω)|. Therefore |(S t)(ω)| ≤ liminf_{h↓0} ((1+ε)/h)·L_W·μ_T(K ∩ {t−h ≤ f ≤ t}). If L_W = 0 every term is 0 (μ_T(K) < ∞), so (S t)(ω) = 0. If L_W > 0, since K ⊆ W this is ≤ (1+ε)·L_W·Λ(t), where
 Λ(t) := liminf_{h↓0} h⁻¹·μ_T(W ∩ {x ∈ U : t−h ≤ f(x) ≤ t}) ∈ [0,∞].
 (4f) Letting ε ↓ 0 and taking the supremum over admissible ω (M_W(S t) is the supremum of ofReal((S t)(ω)) ≤ |(S t)(ω)|):
 (4.9) M_W(S t) ≤ L_W·Λ(t) for every t ∈ ℝ; in particular M_W(S t) = 0 for every t if L_W = 0.

5. (Measurable majorant and 4.10.)
 Case L_W = 0: g :≡ 0 is measurable; M_W(S t) = 0 = g(t) by (4.9); ∫⁻_{(a,b)} g = 0 ≤ L_W·M_W(R).
 Case L_W > 0 and Q = ∞: g :≡ ∞ is measurable, M_W(S t) ≤ g(t), and ∫⁻_{(a,b)} g ≤ ∞ = L_W·Q = L_W·M_W(R).
 Case L_W > 0 and Q < ∞: let G(s) := μ_T(W ∩ {x ∈ U : a < f(x) ≤ s}) for s ∈ ℝ. G is nondecreasing, G = 0 on (−∞, a], G(s) ≤ Q < ∞ for s < b, and G is right-continuous on (−∞, b) (continuity from above for the decreasing sets W ∩ {a < f ≤ s′}, s′ ↓ s, of finite measure). For t ∈ (a,b) and k > 0 let Δ_t(k) := (G(t) − G(t−k))/k and D(t) := liminf_{k↓0} Δ_t(k) ∈ [0,∞]. Define g(t) := L_W·D(t) for t ∈ (a,b) and g(t) := 0 otherwise.
 (5a) Λ(t) ≤ D(t) for t ∈ (a,b): for h > 0 with h + h² < t − a and k := h + h², {t−h ≤ f ≤ t} ⊆ {t−k < f ≤ t}, so h⁻¹μ_T(W ∩ {t−h ≤ f ≤ t}) ≤ h⁻¹(G(t) − G(t−k)) = (1+h)Δ_t(k). Choose k_j ↓ 0 with Δ_t(k_j) → D(t) and h_j > 0 with h_j + h_j² = k_j; then h_j ↓ 0 and Λ(t) ≤ liminf_j h_j⁻¹μ_T(W ∩ {t−h_j ≤ f ≤ t}) ≤ lim_j (1+h_j)Δ_t(k_j) = D(t).
 (5b) g is Borel: for t ∈ (a,b), k ↦ G(t−k) is left-continuous on (0,∞) (right-continuity of G at t − k < b, and G = 0 on (−∞,a] with G(s) → 0 as s ↓ a), so Δ_t is left-continuous and its infimum over (0,1/j) equals its infimum over ℚ ∩ (0,1/j). Thus D(t) = sup_j inf_{q∈ℚ∩(0,1/j)} Δ_t(q), and each t ↦ Δ_t(q) is Borel on (a,b) (G is monotone on (−∞, b), hence Borel). Hence D, and g, are Borel measurable.
 (5c) For t ∈ (a,b): M_W(S t) ≤ L_W·Λ(t) ≤ L_W·D(t) = g(t), by (4.9) and (5a).
 (5d) Let a < a′ < b′ < b and G̃(s) := G(min(max(s,a′),b′)), a real-valued monotone function on ℝ. By Lebesgue's theorem (`Monotone.ae_differentiableAt`), G̃ is differentiable at a.e. s; at such s ∈ (a′,b′), G̃ = G near s, so Δ_s(k) → deriv G̃(s) and D(s) = deriv G̃(s). By `MonotoneOn.intervalIntegrable_deriv` and `MonotoneOn.intervalIntegral_deriv_mem_uIcc`, deriv G̃ ≥ 0 is integrable on [a′,b′] with ∫_{a′}^{b′} deriv G̃ ≤ G̃(b′) − G̃(a′) ≤ Q. Hence ∫⁻_{(a′,b′)} D ≤ Q, and by monotone convergence (a′ ↓ a, b′ ↑ b) ∫⁻_{(a,b)} D ≤ Q. Therefore ∫⁻_{(a,b)} g = L_W·∫⁻_{(a,b)} D ≤ L_W·Q = L_W·M_W(R).

6. (Conclusion.) In every case g : ℝ → [0,∞] is measurable, M_W(S t) ≤ g(t) for all t ∈ (a,b), and ∫⁻_{t∈(a,b)} g(t) ≤ L_W·M_W(R). (This is 4.10 in its upper-integral form with M_W(T⌞{a<f<b}) on the right.) ∎

## Key steps

1. slicing_mass_representation gives a normalized representation (μ_T, T⃗) of T: |T(η)| ≤ ∫|η| dμ_T, μ_T finite on compacts of U, restriction masses M_W′(T⌞A) = μ_T(W′∩A).
2. slicing_representation_unique identifies the given restriction R with T⌞{a<f<b} computed in (μ_T, T⃗), so M_W(R) = μ_T(W ∩ {a<f<b}) = Q.
3. McShane extension, mollification f_σ = ρ_σ * f̃ and Rademacher give |Df_σ| ≤ L_W near tsupport ω ⊆ W.
4. 4.11 with cut-offs χ_h: ∂T(χ(f_σ)ω) − T(χ(f_σ)dω) = T(χ′(f_σ)df_σ∧ω), bounded by ((1+ε)/h) L_W μ_T(K ∩ {t−h−Lσ < f < t+Lσ}); restriction terms evaluated in the IsSlice representations.
5. σ ↓ 0, then h ↓ 0 (dominated convergence), then ε ↓ 0 and sup over ω: M_W(S t) ≤ L_W · liminf_h h⁻¹ μ_T(W ∩ {t−h ≤ f ≤ t}) for every t (4.9).
6. Cases L_W = 0 (g ≡ 0) and Q = ∞ (g ≡ ∞); otherwise g = L_W · lower left Dini derivative of G(s) = μ_T(W ∩ {a<f≤s}): Borel via rational infima, dominates the mass, and ∫g ≤ L_W Q by Lebesgue's theorem for monotone functions (4.10).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all identical)`
- `read project/GMT/Ch06/Contract.lean: IsMeasureRepresentation, IsRestriction, IsSlice, IsIntegerMultiplicity, IsRectifiableTriple, CompactlyContainedOpen, SlicingTheorem`
- `read simongmt Chapter06/{Currents,Mass,FormsDuality,CurrentLocalEquality,Forms,Representation}.lean: GeometricCurrentOn, TestFormOnConverges, GeometricCurrentOn.boundary, tsupport_exteriorDerivative_subset, massOn, massAdmissibleOn, covectorEuclideanNorm, zeroRegion, support, NVector`
- `grep -rn 'theorem simon_theorem_4_14' simongmt/Poincare/SimonGMT/Chapter01 (RadonPolarRepresentation.lean; IsLocallyBoundedCcFunctional in VectorFunctionalEnvelope.lean; IsRadonOuterMeasure in RadonOuterMeasure.lean)`
- `grep -rln 'coarea|co-area' simongmt/Poincare/SimonGMT (only linear co-area: Chapter02/CoareaLinear.lean, CoareaProjection.lean; no co-area formula for rectifiable sets)`
- `grep -n '^def |^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt)`
- `grep -rn 'Monotone.ae_differentiableAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegrable_deriv' mathlib/Mathlib`
- `grep -rn 'LipschitzOnWith.extend_real|LipschitzOnWith.ae_differentiableWithinAt_of_mem|theorem measurable_deriv|theorem ext_of_generate_finite' mathlib/Mathlib`
- `grep -rln 'Lusin' mathlib/Mathlib/MeasureTheory (only Lusin–Souslin; Lusin's continuity theorem is cited from Simon Ch. 1, 1.17)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission (scratch /tmp/slicing_split_check_r1, frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalChallenge.lean (6 child statements as _root_ comparator targets in the contract scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (SlicingTheorem from slicing_exists, slicing_support_subset, slicing_mass_bound, slicing_integer_multiplicity_ae; #print axioms)`
- `lake env lean Scratch/Glue.lean (slicing_exists from slicing_mass_representation; slicing_support_subset from slicing_representation_unique; restriction-mass identification from both; #print axioms)`
- `python3 listing of dag.json lean_name values (20 nodes) and grep of the run's nodes/ for the six proposed names (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/parent-child-handoff.json`
- `/tmp/slicing_split_check_r1/Scratch/Stmts.lean`
- `/tmp/slicing_split_check_r1/Scratch/FinalChallenge.lean`
- `/tmp/slicing_split_check_r1/Scratch/Assembly.lean`
- `/tmp/slicing_split_check_r1/Scratch/Glue.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract; Submission is byte-identical, so child statements may use only contract, SimonGMT and Mathlib names. SimonGMT provides currents with sequential continuity, boundary, massOn (Euclidean coefficient norm), support/zeroRegion and the vector Riesz theorem `simon_theorem_4_14` on any locally compact Hausdorff space (Radon outer measure, unit field a.e.). It has only linear co-area and no co-area for rectifiable sets, and Mathlib has neither (nor Lusin's continuity theorem), so these are cited from Simon Ch. 3 §2 and Ch. 1, 1.17. Mathlib provides McShane (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`), Lebesgue's theorem for monotone functions (`Monotone.ae_differentiableAt`, `MonotoneOn.intervalIntegral_deriv_mem_uIcc`) and π-system uniqueness of finite measures (`ext_of_generate_finite`). In a scratch build of the frozen project, all six child statements elaborate in the comparator's child scope. `SlicingTheorem` follows from the four property children by `choose` plus assembly. `slicing_exists` follows from `slicing_mass_representation`, `slicing_support_subset` from `slicing_representation_unique`, and the restriction-mass identification used by `slicing_mass_bound` from both. All of these are kernel-checked with axioms [propext, Classical.choice, Quot.sound]. The DAG (20 nodes) reserves none of the six proposed names; the concurrently added polyhedral children have different names and types. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
