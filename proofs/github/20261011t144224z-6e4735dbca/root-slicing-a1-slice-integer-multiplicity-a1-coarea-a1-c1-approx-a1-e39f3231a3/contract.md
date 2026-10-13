<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.c1_approx-a1 -->

## Theorem `Submission.slicing_im_coarea_c1_approx`

Let n ∈ ℕ, K ≥ 0, g : ℝⁿ → ℝ K-Lipschitz and ε ∈ (0, ∞]. There exist a closed set A ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ A) < ε and a C¹ function h : ℝⁿ → ℝ such that for every x ∈ A, g(x) = h(x) and g is Fréchet differentiable at x with derivative Dh(x).

Node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.c1_approx-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2483

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1896, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1910, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1921, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1932

## Lean problem

Declaration: `Submission.slicing_im_coarea_c1_approx`

```lean
∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ ε : ℝ≥0∞, 0 < ε → ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧ (volume : Measure (Eucl n)) Aᶜ < ε ∧ ContDiff ℝ 1 h ∧ ∀ x ∈ A, g x = h x ∧ HasFDerivAt g (fderiv ℝ h x) x
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.c1_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. ℝⁿ = Eucl n with Euclidean norm |·|; Lⁿ = volume, a locally finite, weakly regular additive Haar measure. (ℝⁿ)* = L(ℝⁿ, ℝ) carries the operator norm ‖·‖. For x ∈ ℝⁿ let Dg(x) := fderiv ℝ g x ∈ (ℝⁿ)*; by Mathlib's convention Dg(x) = 0 where g is not differentiable. For y ≠ x let R(x,y) := (g(y) − g(x) − Dg(x)(y − x))/|y − x|.

Source. Simon, Ch. 2, Theorem 1.5 (C¹ Approximation Theorem), in the stronger form that Simon's printed proof (p. 44) establishes: a closed set A on which g is differentiable.
Printed proof: “By Rademacher's Theorem f is differentiable on a set B ⊆ ℝⁿ with Lⁿ(ℝⁿ ∖ B) = 0. By Lusin's theorem (which applies to sets of infinite measure for Lⁿ) there is a closed set C ⊆ B such that ∇f|C is continuous and Lⁿ(ℝⁿ ∖ C) < ε/2. On C we define h(x) = f(x), τ(x) = ∇f(x) and R(x,y) for x, y ∈ C is as defined in 1.6 (‡). Evidently (since C ⊆ B) we have lim_{y→x, y∈C} R(x,y) = 0 ∀ x ∈ C, but not necessarily uniformly with respect to x on compact subsets of C as in 1.6 (‡). We therefore proceed as follows. For each k = 1, 2, … let η_k(x) = sup{|R(x,y)| : y ∈ C ∩ B_{1/k}(x) ∖ {x}}. Then η_k ↓ 0 pointwise in C, and hence by Egoroff's Theorem (applied to the finite measure sets C ∩ B_j(0), j = 1, 2, …) there is an Lⁿ-measurable set A₀ ⊆ C such that Lⁿ(C ∖ A₀) < ε/4 and η_k converges uniformly to zero on each bounded subset of A₀. Since we can take a closed set A ⊆ A₀ with Lⁿ(A₀ ∖ A) < ε/4 we thus have Lⁿ(ℝⁿ ∖ A) < ε and 1.6 (‡) holds. Hence we can apply the Whitney Theorem 1.6, and the proof is complete.”
Structure. Part I (Steps 1–4) derives the theorem from three facts:
 - (F1) Lusin's theorem for operator-valued maps on a Borel set of possibly infinite measure;
 - (F2) a closed set with a uniform first-order remainder;
 - (F3) the C¹ Whitney extension theorem.
Each of (F1)–(F3) is literally a comparator-accepted DAG lemma with a frozen Lean type: lpf_c1r_lusin_closed, lpf_c1r_uniform_remainder and lpf_c1r_whitney_extension. A decomposition of this node may reuse them unchanged; a Lean 4 assembly of exactly Part I from these three types compiled during review (axioms propext, Classical.choice, Quot.sound). Part II (Steps 5–12) proves (F1)–(F3) along the printed argument with every step filled in, so the proof is self-contained. Part II is the reviewed proof of the identically stated lipschitz-pushforward node lpf_c1_approximation_real.
 (F1) For every Borel S ⊆ ℝⁿ, Borel F : ℝⁿ → (ℝⁿ)* and η ∈ (0, ∞] there is a closed C ⊆ S with Lⁿ(S ∖ C) < η and F continuous on C.
 (F2) If g is K-Lipschitz, C is closed, g is differentiable at every point of C and Dg is continuous on C, then for every η ∈ (0, ∞] there is a closed A ⊆ C with Lⁿ(C ∖ A) < η such that for every compact L ⊆ A and δ > 0 there is ρ > 0 with |g(y) − g(x) − Dg(x)(y − x)| ≤ δ|y − x| for all x ∈ L, y ∈ A, |x − y| < ρ.
 (F3) If A is closed, f : ℝⁿ → ℝ and τ : ℝⁿ → (ℝⁿ)* are continuous on A and satisfy the conclusion of (F2) with τ in place of Dg, then there is a C¹ function h with h(a) = f(a) and HasFDerivAt h (τ(a)) a for every a ∈ A.

Part I.
1. (Rademacher.) D := {x : g is differentiable at x} is Borel (`measurableSet_of_differentiableAt`), x ↦ Dg(x) is Borel (`measurable_fderiv`), and Lⁿ(ℝⁿ ∖ D) = 0 by Rademacher's theorem (`LipschitzWith.ae_differentiableAt`).
2. (Lusin.) By (F1) with S := D, F := Dg and η := ε/2 there is a closed C ⊆ D with Lⁿ(D ∖ C) < ε/2 and Dg continuous on C.
3. (Uniform remainder.) g is differentiable at every point of C ⊆ D. By (F2) with η := ε/2 there is a closed A ⊆ C with Lⁿ(C ∖ A) < ε/2 and the uniform remainder estimate on compact subsets of A.
4. (Whitney and conclusion.) g is continuous and Dg is continuous on A ⊆ C. By (F3) with f := g and τ := Dg there is a C¹ h with h = g on A and HasFDerivAt h (Dg(a)) a for a ∈ A.
 - Since ℝⁿ ∖ A ⊆ (ℝⁿ ∖ D) ∪ (D ∖ C) ∪ (C ∖ A), we get Lⁿ(ℝⁿ ∖ A) < 0 + ε/2 + ε/2 = ε; for ε = ∞ this is trivial.
 - For x ∈ A, g(x) = h(x) and fderiv ℝ h x = Dg(x) (uniqueness of derivatives). As x ∈ D, HasFDerivAt g (Dg(x)) x, i.e. HasFDerivAt g (fderiv ℝ h x) x. ∎ (modulo (F1)–(F3))

Part II: proofs of (F1)–(F3), following the printed proof. Steps 5–7 prove (F1), in the form needed with S := D. Steps 8–11 prove (F2) for the closed set C of step 7. Step 12 is (F3). Applied in sequence, they also give a direct proof of the theorem.

5. (Reductions and annuli.)
- If ε > 1, in particular if ε = ∞, replace ε by 1: a set A with Lⁿ(ℝⁿ ∖ A) < 1 also has Lⁿ(ℝⁿ ∖ A) < ε. So assume 0 < ε ≤ 1.
- Let S₁ := {x : |x| < 1} and S_j := {x : j − 1 < |x| < j} for j ≥ 2. The S_j are open, pairwise disjoint and bounded, so Lⁿ(S_j) < ∞.
- Z := ℝⁿ ∖ ⋃_j S_j = ⋃_{j≥1} {x : |x| = j} is a countable union of spheres of nonzero radius, so Lⁿ(Z) = 0 (Mathlib `MeasureTheory.Measure.addHaar_sphere_of_ne_zero`; for n = 0 these spheres are empty).
- Gluing fact (★), closedness: if F_j ⊆ S_j is closed for every j ≥ 1, then F := ⋃_j F_j is closed. The family (F_j) is locally finite, since the ball {|x| < r} meets S_j only if j − 1 < r (Mathlib `LocallyFinite.isClosed_iUnion`).
- Gluing fact (★), continuity: if a map φ is continuous on every F_j, then φ is continuous on F. Each x ∈ F_j has the open neighbourhood S_j with S_j ∩ F = F_j, because the S_l are pairwise disjoint. So near x the restriction of φ to F coincides with its restriction to F_j.

6. (Rademacher.) g is K-Lipschitz. By Rademacher's theorem (Simon Ch. 2, Theorem 1.4; Mathlib `LipschitzWith.ae_differentiableAt`), the set D := {x : g is differentiable at x} has Lⁿ(ℝⁿ ∖ D) = 0. D is Borel (Mathlib `measurableSet_of_differentiableAt`), and x ↦ Dg(x) is Borel measurable (Mathlib `measurable_fderiv`). For x ∈ D, ‖Dg(x)‖ ≤ K, because |Dg(x)v| = lim_{t→0} |g(x + tv) − g(x)|/|t| ≤ K|v| (Mathlib `norm_fderiv_le_of_lipschitz`).

7. (Lusin's theorem for Lⁿ on all of ℝⁿ.) Claim: there is a closed C ⊆ D such that Dg is continuous on C and Lⁿ(ℝⁿ ∖ C) ≤ ε/4 < ε/2.
- Let e₁, …, e_n be the standard basis of ℝⁿ and fix j ≥ 1. S_j ∩ D is Borel and has finite measure.
- By inner regularity of Lⁿ by closed sets (Mathlib `MeasurableSet.exists_isClosed_sdiff_lt`) there is a closed F_j ⊆ S_j ∩ D with Lⁿ((S_j ∩ D) ∖ F_j) < ε/2^{j+3}.
- For l = 1, …, n the real function x ↦ Dg(x)e_l is Borel measurable. Lusin's theorem on the finite-measure set S_j ∩ D gives a closed C_{j,l} ⊆ S_j ∩ D with Lⁿ((S_j ∩ D) ∖ C_{j,l}) < ε/(2^{j+3}(n+1)) on which x ↦ Dg(x)e_l is continuous. Here Lusin is Simon Ch. 1, Theorem 1.17, i.e. SimonGMT `Poincare.SimonGMT.Chapter01.exists_isClosed_continuousOn_of_measurable`. It lives in the built module Poincare.SimonGMT.Chapter01.Lusin, which must be imported explicitly; its closed-inner-approximation hypothesis for Lⁿ is again `MeasurableSet.exists_isClosed_sdiff_lt`.
- Put C_j := F_j ∩ ⋂_{l=1}^{n} C_{j,l} (C_j = F_j if n = 0). Then C_j is closed and C_j ⊆ S_j ∩ D.
- Its measure defect is Lⁿ((S_j ∩ D) ∖ C_j) < ε/2^{j+3} + n·ε/(2^{j+3}(n+1)) < ε/2^{j+2}.
- Dg is continuous on C_j, because all its coordinates are: λ ↦ (λ(e₁), …, λ(e_n)) is a linear homeomorphism (ℝⁿ)* → ℝⁿ.
- Let C := ⋃_j C_j. By (★), C is closed and Dg is continuous on C; also C ⊆ D.
- Since ℝⁿ ∖ C ⊆ Z ∪ (ℝⁿ ∖ D) ∪ ⋃_j ((S_j ∩ D) ∖ C_j), we get Lⁿ(ℝⁿ ∖ C) ≤ 0 + 0 + Σ_{j≥1} ε/2^{j+2} = ε/4.

8. (The functions η_k.) For k ≥ 1 and x ∈ C let η_k(x) := sup({|R(x,y)| : y ∈ C, 0 < |y − x| < 1/k} ∪ {0}); for x ∉ C let η_k(x) := 0.
(a) Bounds. For x ∈ C ⊆ D and y ≠ x, |R(x,y)| ≤ |g(y) − g(x)|/|y − x| + ‖Dg(x)‖ ≤ 2K. Hence 0 ≤ η_k ≤ 2K and η_k is real-valued.
(b) Convergence. η_{k+1} ≤ η_k, and η_k(x) → 0 for every x ∈ C. Given δ > 0, differentiability of g at x ∈ D gives ρ > 0 with |g(y) − g(x) − Dg(x)(y − x)| ≤ δ|y − x| whenever |y − x| < ρ. So η_k(x) ≤ δ once 1/k ≤ ρ.
(c) Measurability: η_k is Borel measurable.
- For fixed y ∈ C let φ_y : C → [0, ∞) be φ_y(x) := |R(x,y)| if 0 < |x − y| < 1/k, and φ_y(x) := 0 otherwise.
- φ_y is lower semicontinuous on C. The set U_y := {x ∈ C : 0 < |x − y| < 1/k} is relatively open in C, and φ_y is continuous on U_y: g is continuous, Dg is continuous on C by step 7, and |y − x| > 0 on U_y. This gives lower semicontinuity at points of U_y. At x₀ ∈ C ∖ U_y we have φ_y(x₀) = 0 ≤ φ_y(x) for all x ∈ C.
- As φ_y ≥ 0, η_k|C = sup_{y∈C} φ_y is a pointwise supremum of lower semicontinuous functions, hence lower semicontinuous on C.
- So each set {x ∈ C : η_k(x) > t} (t ∈ ℝ) is relatively open in the closed set C, hence Borel. Since η_k vanishes off C, η_k is Borel measurable on ℝⁿ.
- Alternatively: if C′ ⊆ C is countable and dense in C, then η_k(x) = sup_{y∈C′} φ_y(x) for x ∈ C. This holds because y ↦ R(x,y) is continuous at every y ≠ x and the condition 0 < |y − x| < 1/k is open in y. So η_k is a countable supremum of Borel functions.

9. (Egoroff on bounded pieces.) Fix j ≥ 1.
- C_j = C ∩ S_j is Borel with Lⁿ(C_j) ≤ Lⁿ(S_j) < ∞. Every η_k is Borel measurable by 8(c), and η_k → 0 at every point of C_j by 8(b).
- By Egoroff's theorem (Mathlib `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`) there is a measurable T_j ⊆ C_j with Lⁿ(T_j) ≤ ε/2^{j+3} such that η_k → 0 uniformly on C_j ∖ T_j.
- Put A₀ := ⋃_j (C_j ∖ T_j) ⊆ C. Since C = ⋃_j C_j, we have C ∖ A₀ ⊆ ⋃_j T_j, so Lⁿ(C ∖ A₀) ≤ Σ_{j≥1} ε/2^{j+3} = ε/8.

10. (A closed A ⊆ A₀.)
- For every j, C_j ∖ T_j is measurable with finite measure. By inner regularity (`MeasurableSet.exists_isClosed_sdiff_lt`) there is a closed A_j ⊆ C_j ∖ T_j with Lⁿ((C_j ∖ T_j) ∖ A_j) < ε/2^{j+3}.
- Let A := ⋃_j A_j. Since A_j ⊆ C_j ⊆ S_j, A is closed by (★).
- A ⊆ A₀ ⊆ C ⊆ D and A₀ ∖ A ⊆ ⋃_j ((C_j ∖ T_j) ∖ A_j), so Lⁿ(A₀ ∖ A) ≤ ε/8.
- As ℝⁿ ∖ A ⊆ (ℝⁿ ∖ C) ∪ (C ∖ A₀) ∪ (A₀ ∖ A), we get Lⁿ(ℝⁿ ∖ A) ≤ ε/4 + ε/8 + ε/8 = ε/2 < ε.
- Uniformity on bounded sets: suppose W ⊆ {|x| < J} with J ∈ ℕ. Then W ∩ A ⊆ ⋃_{j≤J} (C_j ∖ T_j), because A_j ⊆ S_j ⊆ {|x| > j − 1} does not meet {|x| < J} when j > J. This is a finite union of sets on each of which η_k → 0 uniformly, so η_k → 0 uniformly on W ∩ A.

11. (Whitney's hypothesis (‡) on A.)
(i) g is Lipschitz, hence continuous on A.
(ii) Dg is continuous on A ⊆ C by step 7.
(iii) Let K′ ⊆ A be compact and δ > 0. K′ is bounded, so by step 10 there is k ≥ 1 with η_k(x) ≤ δ for all x ∈ K′. Let x ∈ K′ and y ∈ A with |x − y| < 1/k. If y = x, then |g(y) − g(x) − Dg(x)(y − x)| = 0 ≤ δ|y − x|. If y ≠ x, then y ∈ C and 0 < |y − x| < 1/k, so |g(y) − g(x) − Dg(x)(y − x)| = |R(x,y)| |y − x| ≤ η_k(x)|y − x| ≤ δ|y − x|.
Hence for every compact K′ ⊆ A and δ > 0 there is ρ := 1/k > 0 such that |g(y) − g(x) − Dg(x)(y − x)| ≤ δ|y − x| for all x ∈ K′ and y ∈ A with |x − y| < ρ. This is Simon's condition 1.6 (‡) for h := g|A and τ := Dg|A, i.e. SimonGMT's HasWhitneyC1Compatibility A g (fderiv ℝ g).

12. (Whitney extension and conclusion.)
- By the Whitney Extension Theorem (Simon Ch. 2, Theorem 1.6; see [EG92, §6.5], [Fed69, 3.1.14]) there is a C¹ function h : ℝⁿ → ℝ with h(a) = g(a) and HasFDerivAt h (Dg(a)) a for every a ∈ A. In Lean this is SimonGMT `Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney`, in Poincare/SimonGMT/Chapter02/WhitneyExtension.lean of the pinned simongmt package. That module has no prebuilt .olean in the shared package tree, but its source compiles unchanged (axioms propext, Classical.choice, Quot.sound) when copied into a new file under GMT/Ch06/ that imports GMT.Ch06.Submission, Poincare.SimonGMT.Chapter02.WhitneyJet and Poincare.SimonGMT.Chapter02.WhitneyPartition, both of which are built.
- Let x ∈ A. Then g(x) = h(x), and by uniqueness of the Fréchet derivative fderiv ℝ h x = Dg(x).
- Since x ∈ A ⊆ D, g is differentiable at x, i.e. HasFDerivAt g (Dg(x)) x, which is HasFDerivAt g (fderiv ℝ h x) x.
- Together with step 10 (A is closed and Lⁿ(ℝⁿ ∖ A) < ε), this proves the theorem. ∎

## Key steps

1. Rademacher: D := {x : g differentiable at x} is Borel and co-null, and Dg is Borel.
2. (F1) Lusin (accepted lpf_c1r_lusin_closed with S := D, ε/2): a closed C ⊆ D with Lⁿ(D∖C) < ε/2 and Dg continuous on C.
3. (F2) Uniform remainder (accepted lpf_c1r_uniform_remainder, ε/2): a closed A ⊆ C with Lⁿ(C∖A) < ε/2 and a uniform first-order remainder on compact subsets of A.
4. (F3) Whitney extension (accepted lpf_c1r_whitney_extension; SimonGMT exists_contDiff_one_extension_of_whitney): a C¹ h with h = g and Dh = Dg on A; Lⁿ(Aᶜ) < ε.
5. Part II proves (F1)–(F3) along Simon's printed proof: annuli, Lusin, Egoroff for the remainder sups η_k, and Whitney's condition (‡).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean (byte-identical); read Contract.lean (IsRectifiableTriple, Eucl, scope commands)`
- `grep -rn 'slicing_im_coarea_' local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json: statuses and lean_statement of all lipschitz_pushforward nodes; byte comparison of candidate child types with lpf_c1_approximation_real, lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (identical, all speculative-ready) and lpf_ccr_hasDerivAt_line_of_comp (accepted 18:04Z, Eucl Q-valued); collision check of the nine names against all 369 DAG lean_name values (none)`
- `read nodes/root-lipschitz-pushforward-im-a1-{countably-rectifiable-c1-cover-a1,weighted-tangent-on-c1-chart-a1,lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1,chart-chain-rule-a1-line-deriv-comp-a1}/parent-supplied-natural-proof.md and nodes/root-slicing-a1-slice-integer-multiplicity-a1/{parent-supplied-natural-proof.md,decomposition-v1.json}`
- `grep -n '^theorem|^def' SimonGMT Chapter03/{Rectifiable,Differential,DisjointCover,SubmanifoldCover}.lean and Chapter02/{AreaLipschitz,AreaDomain,AreaCritical,Area,Lipschitz,CoareaLinear,CoareaProjection,WhitneyExtension}.lean`
- `grep for SimonGMT names weighted_area_formula_lipschitzOn_fiberSum, weighted_area_formula_lipschitz_injOn, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, exists_contDiff_one_extension_of_whitney, exists_isClosed_continuousOn_of_measurable, simon_theorem_3_6, coarea_projection_lintegral (all present)`
- `grep in pinned Mathlib for hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum, euclideanHausdorffMeasure_def, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, normDet_comp_of_finrank_eq, normDet_eq_abs_det, normDet_codRestrict, lintegral_image_eq_lintegral_abs_det_fderiv_mul, OpenPartialHomeomorph.contDiffAt_symm, measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, Measurable.lintegral_prod_right', MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_apply₀', restrict_congr_set, lintegral_iUnion, lintegral_tsum, lintegral_inter_add_sdiff, LipschitzOnWith.extend_real, isOpen_iUnion_countable (all present)`
- `sed book/chapter-02.txt §6 (6.1–6.7) and book/chapter-03.txt §1–2 (1.1–1.9, 2.1–2.10)`
- `lake build GMT.Ch06.Submission in scratch /tmp/coarea-decomp-47PgtZ/proj (frozen d8d46c9 contract, shared lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalCheck.lean (nine child types and the parent type in the exact comparator scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (parent type from eilenberg, glue, pieces, chart_critical, chart_regular; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/Pieces.lean (pieces from c1_approx, chart_cover, chart_tangent, line_deriv; standard axioms) and Scratch/GradId.lean`
- `lake env lean Scratch/Glue.lean (glue proved outright; standard axioms); lake env lean Scratch/Review_C1.lean (c1_approx from the accepted lpf_c1r_lusin_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension types; standard axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-line-deriv-comp-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Stmts.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/FinalCheck.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Assembly.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Pieces.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Glue.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/GradId.lean`
- `/tmp/coarea-decomp-47PgtZ/proj/Scratch/Review_C1.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract. Submission is byte-identical to it, and no `slicing_im_coarea_*` name exists in the project or in the 369 DAG nodes. SimonGMT supplies the needed area-formula library: weighted_area_formula_lipschitzOn_fiberSum, injective_area_formula_lipschitzOn, area_image_criticalSet_eq_zero, euclideanHausdorffMeasure_image_le_of_lipschitzOn, a Whitney extension (source only, no .olean), Lusin, the upper density theorem, the linear co-area formula and HasWeightedApproximateTangentSpaceAt with uniqueness. It has no nonlinear co-area formula and no Eilenberg inequality. Mathlib supplies the Hausdorff measure covering lemmas, the μHE normalization, normDet, the inverse function theorem, change of variables, Fubini/Tonelli and Lusin–Souslin. The lipschitz-pushforward branch has speculative-ready nodes byte-identical to three proposed children (c1_approx, chart_cover, chart_tangent); because they are not accepted, they get new names here, and their accepted sub-lemmas (lpf_c1r_*, lpf_wtc_*, lpf_c1_local_antilipschitz, lpf_raf_chart_change_of_variables) are cited for reuse at the next level. lpf_ccr_hasDerivAt_line_of_comp was accepted during this session and is cited as an alternative route for line_deriv. Lean checks in the exact comparator scope: all nine child types elaborate; the parent type follows from five children; pieces follows from four; glue is proved outright; c1_approx follows from three accepted types. All of these use only propext, Classical.choice and Quot.sound. These checks do not certify the remaining analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
