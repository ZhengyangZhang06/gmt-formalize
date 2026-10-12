<!-- theorem-id: gmt-ch06/root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.whitney_extension-a1 -->

## Theorem `Submission.lpf_c1r_whitney_extension`

Let n ∈ ℕ, let A ⊆ ℝⁿ (ℝⁿ = EuclideanSpace ℝ (Fin n)) be closed, and let f : ℝⁿ → ℝ and τ : ℝⁿ → (ℝⁿ)* = L(ℝⁿ, ℝ) be continuous on A. Assume that for every compact L ⊆ A and every δ > 0 there is ρ > 0 with |f(y) − f(x) − τ(x)(y − x)| ≤ δ|y − x| for all x ∈ L and y ∈ A with |x − y| < ρ. Then there is a C¹ function h : ℝⁿ → ℝ such that for every a ∈ A, h(a) = f(a) and h is Fréchet differentiable at a with derivative τ(a).

Node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.whitney_extension-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1146

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.lpf_c1r_whitney_extension`

```lean
∀ (n : ℕ) (A : Set (Eucl n)) (f : Eucl n → ℝ) (τ : Eucl n → (Eucl n →L[ℝ] ℝ)), IsClosed A → ContinuousOn f A → ContinuousOn τ A → (∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - τ x (y - x)‖ ≤ δ * ‖y - x‖) → ∃ h : Eucl n → ℝ, ContDiff ℝ 1 h ∧ ∀ a ∈ A, h a = f a ∧ HasFDerivAt h (τ a) a
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

- Parent DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.whitney_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Statement. Let n ∈ ℕ, let A ⊆ ℝⁿ be closed, and let f : ℝⁿ → ℝ and τ : ℝⁿ → (ℝⁿ)* be continuous on A and satisfy the compact-uniform condition (‡) stated below. Then there is a C¹ function h : ℝⁿ → ℝ such that for every a ∈ A, h(a) = f(a) and h is Fréchet differentiable at a with derivative τ(a).

Source. This is Simon Ch. 2, Theorem 1.6 (Whitney Extension Theorem), with derivatives as continuous linear maps instead of gradients. It is the result applied in the last step of Simon's printed proof of Theorem 1.5 and in step 8 of the parent proof. Simon gives no proof (“For the proof see for example [EG92] or [Fed69]”). The proof below is the standard Whitney construction (Evans–Gariepy, Measure Theory and Fine Properties of Functions, §6.5; Federer 3.1.14). It is exactly the construction kernel-checked in the pinned SimonGMT files Poincare/SimonGMT/Chapter02/WhitneyJet.lean, WhitneyCover.lean, WhitneyPartition.lean and WhitneyExtension.lean, whose final theorem is Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney. Its hypothesis HasWhitneyC1Compatibility A f τ consists exactly of: f continuous on A, τ continuous on A, and condition (‡) below.

Notation and hypotheses. ℝⁿ = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|; B_r(x) is the open ball and B̄_r(x) the closed ball. (ℝⁿ)* = L(ℝⁿ, ℝ) carries the operator norm ‖·‖. A ⊆ ℝⁿ is closed. f : ℝⁿ → ℝ and τ : ℝⁿ → (ℝⁿ)* are continuous on A, and they satisfy
(‡) for every compact L ⊆ A and every δ > 0 there is ρ > 0 such that |f(y) − f(x) − τ(x)(y − x)| ≤ δ|y − x| for all x ∈ L and y ∈ A with |x − y| < ρ.
Values of f and τ off A play no role. For b ∈ ℝⁿ put P_b(y) := f(b) + τ(b)(y − b). This is an affine function of y with derivative DP_b ≡ τ(b), and P_b(b) = f(b).
(I) For all a, b, y ∈ ℝⁿ: P_b(y) − P_a(y) = [f(b) − f(a) − τ(a)(b − a)] + (τ(b) − τ(a))(y − b). Expand both sides, using τ(a)(y − a) = τ(a)(y − b) + τ(a)(b − a). Consequently |P_b(y) − P_a(y)| ≤ |f(b) − f(a) − τ(a)(b − a)| + ‖τ(b) − τ(a)‖ |y − b|.

0. (Trivial case and distance function.) If A = ∅, the function h :≡ 0 is C^∞, and the conditions at points of A hold vacuously. From now on A ≠ ∅.
- Let d(x) := dist(x, A) = inf_{a∈A} |x − a|. It is 1-Lipschitz, d(x) ≤ |x − a| for every a ∈ A, and d(x) > 0 iff x ∉ A, because A is closed.
- Since ℝⁿ is proper and A is closed and nonempty, every p ∈ ℝⁿ has a nearest point in A. Fix a choice π(p) ∈ A with |p − π(p)| = d(p). Then π(a) = a for a ∈ A, and |π(p) − a| ≤ |π(p) − p| + |p − a| ≤ 2|p − a| for every a ∈ A.
- If n = 0, then ℝ⁰ is a single point, so A = ℝ⁰. The constructions below then concern the empty set ℝ⁰ ∖ A, and h := f works.

1. (Local uniform estimate.) For every a ∈ A and η > 0 there is δ ∈ (0, 1] such that
(i) ‖τ(b) − τ(a)‖ ≤ η for all b ∈ A with |b − a| < δ, and
(ii) |f(c) − f(b) − τ(b)(c − b)| ≤ η|c − b| for all b, c ∈ A with |b − a| < δ and |c − a| < δ.
Proof.
- K := A ∩ B̄₁(a) is compact (closed and bounded). Apply (‡) to K with the constant η to get ρ > 0.
- By continuity of τ|A at a there is ρ′ > 0 with ‖τ(b) − τ(a)‖ < η for b ∈ A with |b − a| < ρ′.
- Put δ := min(1, ρ′, ρ/3). Then (i) holds.
- For (ii): b ∈ K because |b − a| < δ ≤ 1, and |b − c| ≤ |b − a| + |a − c| < 2δ < ρ. So (‡) with x := b and y := c gives the inequality.

2. (Whitney radius.) Let r(x) := min(1, d(x))/100.
- Then 0 ≤ r(x) ≤ 1/100; r(x) > 0 iff x ∉ A; and 100 r(x) ≤ d(x).
- |r(x) − r(y)| ≤ |x − y|/100, since t ↦ min(1, t) is 1-Lipschitz.
- If x ∉ A and |y − x| < 100 r(x), then y ∉ A, since |y − x| < d(x). In particular B_{r(x)}(x) ⊆ ℝⁿ ∖ A.
Comparability. If |x − c| ≤ r(x) + 10 r(c), then r(x)/2 ≤ r(c) ≤ 2 r(x) and |x − c| ≤ 21 r(x). Indeed:
- r(c) ≤ r(x) + |x − c|/100 ≤ r(x) + r(x)/100 + r(c)/10 gives (9/10) r(c) ≤ (101/100) r(x), hence r(c) ≤ 2 r(x);
- r(x) ≤ r(c) + |x − c|/100 ≤ r(c) + r(x)/100 + r(c)/10 gives (99/100) r(x) ≤ (11/10) r(c), hence r(c) ≥ (9/10) r(x) ≥ r(x)/2;
- finally |x − c| ≤ r(x) + 10 r(c) ≤ 21 r(x).

3. (Disjoint Whitney balls.) There is a set Z ⊆ ℝⁿ ∖ A of centres with two properties: the balls B_{r(c)}(c), c ∈ Z, are pairwise disjoint, and every x ∈ ℝⁿ ∖ A has some c ∈ Z with |x − c| < 4 r(c).
- Apply the Vitali covering lemma to the family of balls with centres x ∈ ℝⁿ ∖ A and radii r(x) ∈ (0, 1/100]; the radii are uniformly bounded. Use Simon Ch. 1, Lemma 3.4 (5-times covering lemma, property (*)) for the closed balls B̄_{r(x)}(x).
- It gives a pairwise disjoint subfamily {B̄_{r(c)}(c) : c ∈ Z}. As n ≥ 1 and r > 0, each closed ball determines its centre and radius, so the subfamily is indexed by its set Z of centres. Every B̄_{r(x)}(x) meets some B̄_{r(c)}(c), c ∈ Z, with diam B̄_{r(c)}(c) ≥ diam B̄_{r(x)}(x)/2, i.e. r(c) ≥ r(x)/2 (for n ≥ 1, diam B̄_r = 2r).
- Then |x − c| ≤ r(x) + r(c) ≤ 3 r(c) < 4 r(c), and disjointness of the closed balls implies disjointness of the open balls.
- Equivalently, apply Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement_ball with enlargement factor 4 > 3. Every B_{r(x)}(x) is contained in some B_{4r(c)}(c), and x ∈ B_{r(x)}(x) since r(x) > 0.
Separation. For distinct c, c′ ∈ Z, |c − c′| ≥ r(c). Otherwise c′ ∈ B_{r(c)}(c) ∩ B_{r(c′)}(c′), using r(c′) > 0, which contradicts disjointness.

4. (Bounded overlap.) There is N ∈ ℕ, depending only on n, such that for every x ∈ ℝⁿ ∖ A the set
N(x) := {c ∈ Z : |x − c| ≤ r(x) + 10 r(c)}
is finite with at most N elements.
- The compact ball B̄₂₁(0) is covered by finitely many, say N, open balls of radius 1/4. Let x ∉ A and ρ := r(x) > 0.
- For c ∈ N(x) let p_c := (c − x)/ρ. By comparability |p_c| ≤ 21.
- For distinct c, c′ ∈ N(x), separation and comparability give |p_c − p_{c′}| = |c − c′|/ρ ≥ r(c)/ρ ≥ 1/2.
- Two points of one ball of radius 1/4 are at distance < 1/2. So each of the N small balls contains at most one p_c, and c ↦ p_c is injective. Hence #N(x) ≤ N.

5. (Rescaled bumps.)
- Fix a C^∞ function φ : ℝⁿ → [0, 1] with φ = 1 on B̄₄(0) and φ = 0 outside B₈(0) (Mathlib ContDiffBump with rIn = 4, rOut = 8).
- φ is C¹ with compact support, so it is Λ-Lipschitz for some Λ ≥ 0. Put B := Λ + 1 > 0.
- For c ∈ Z let φ_c(y) := φ((y − c)/r(c)). Then φ_c is C^∞ with 0 ≤ φ_c ≤ 1, φ_c(y) = 1 if |y − c| ≤ 4 r(c), and φ_c(y) = 0 if |y − c| ≥ 8 r(c).
- φ_c is (Λ/r(c))-Lipschitz, so ‖Dφ_c(y)‖ ≤ B/r(c) for all y (Mathlib norm_fderiv_le_of_lipschitz).

6. (Partition of unity on ℝⁿ ∖ A.) Let x ∉ A and y ∈ B_{r(x)}(x); then y ∉ A by step 2.
- If c ∈ Z ∖ N(x), then |y − c| ≥ |x − c| − |x − y| > (r(x) + 10 r(c)) − r(x) = 10 r(c) ≥ 8 r(c), so φ_c(y) = 0.
- So on B_{r(x)}(x) only the finitely many φ_c with c ∈ N(x) can be nonzero. Hence s(y) := Σ_{c∈Z} φ_c(y) (y ∉ A) is a well-defined finite sum, s = Σ_{c∈N(x)} φ_c on B_{r(x)}(x), and s is C^∞ on the open set ℝⁿ ∖ A.
- For y ∉ A, step 3 gives c ∈ Z with |y − c| < 4 r(c), so φ_c(y) = 1 and s(y) ≥ 1.
- Define w_c := φ_c/s on ℝⁿ ∖ A. Each w_c is C^∞ on ℝⁿ ∖ A, and 0 ≤ w_c ≤ 1.
- For x ∉ A and y ∈ B_{r(x)}(x): w_c(y) = 0 for c ∉ N(x), and Σ_{c∈N(x)} w_c(y) = 1. Differentiating this identity on the open ball B_{r(x)}(x) gives Σ_{c∈N(x)} Dw_c(x) = 0.

7. (Gradient bound.) With M := 2B(N + 1)², for every x ∉ A we have Σ_{c∈N(x)} ‖Dw_c(x)‖ ≤ M/r(x).
- For c ∈ N(x), comparability gives r(c) ≥ r(x)/2, so ‖Dφ_c(x)‖ ≤ B/r(c) ≤ 2B/r(x) =: T.
- Ds(x) = Σ_{c∈N(x)} Dφ_c(x), so ‖Ds(x)‖ ≤ N T.
- Dw_c = Dφ_c/s − φ_c Ds/s², with s ≥ 1 and 0 ≤ φ_c ≤ 1. Hence ‖Dw_c(x)‖ ≤ ‖Dφ_c(x)‖ + ‖Ds(x)‖ ≤ T + N T.
- Summing over at most N indices: Σ_{c∈N(x)} ‖Dw_c(x)‖ ≤ N(N + 1)T ≤ (N + 1)² · 2B/r(x) = M/r(x).

8. (Anchors.) Let x ∉ A and c ∈ N(x). Then
(a) |x − π(c)| ≤ 2 d(x), and
(b) |π(c) − a| ≤ 3|x − a| for every a ∈ A.
Proof.
- |x − π(c)| ≤ |x − c| + d(c) ≤ |x − c| + (d(x) + |x − c|) = d(x) + 2|x − c|.
- By comparability and step 2, |x − c| ≤ 21 r(x) ≤ 0.21 d(x). So |x − π(c)| ≤ 1.42 d(x) ≤ 2 d(x).
- For (b): |π(c) − a| ≤ |π(c) − x| + |x − a| ≤ 2 d(x) + |x − a| ≤ 3|x − a|.

9. (The extension.) Define h(y) := f(y) for y ∈ A, and h(y) := Σ_{c∈Z} w_c(y) P_{π(c)}(y) for y ∉ A.
- For y ∉ A this is a finite sum, by step 6 applied with x := y.
- For x ∉ A, step 6 gives h = Σ_{c∈N(x)} w_c P_{π(c)} on B_{r(x)}(x) ⊆ ℝⁿ ∖ A. So h is C^∞ on the open set ℝⁿ ∖ A, and
Dh(x) = Σ_{c∈N(x)} [ w_c(x) τ(π(c)) + P_{π(c)}(x) Dw_c(x) ].
- Since Σ_{c∈N(x)} w_c(x) = 1, also h(x) − P_a(x) = Σ_{c∈N(x)} w_c(x) (P_{π(c)}(x) − P_a(x)) for every a.

10. (h has derivative τ(a) at every a ∈ A.) Let a ∈ A and ε > 0. Take δ from step 1 with η := ε/5, and let |x − a| < δ/4.
- If x ∈ A: by step 1(ii) with b := a and c := x, |h(x) − h(a) − τ(a)(x − a)| = |f(x) − f(a) − τ(a)(x − a)| ≤ (ε/5)|x − a| ≤ ε|x − a|.
- If x ∉ A: h(a) = f(a), so h(a) + τ(a)(x − a) = P_a(x). By step 9, h(x) − P_a(x) = Σ_{c∈N(x)} w_c(x)(P_{π(c)}(x) − P_a(x)).
- For c ∈ N(x) put b := π(c) ∈ A. By step 8, |b − a| ≤ 3|x − a| < δ and |x − b| ≤ 2 d(x) ≤ 2|x − a|.
- By (I) and step 1, |P_b(x) − P_a(x)| ≤ (ε/5)|b − a| + (ε/5)|x − b| ≤ (ε/5)(3 + 2)|x − a| = ε|x − a|.
- The weights w_c(x), c ∈ N(x), are ≥ 0 with sum 1, so |h(x) − h(a) − τ(a)(x − a)| = |h(x) − P_a(x)| ≤ ε|x − a|.
Hence h(x) = h(a) + τ(a)(x − a) + o(|x − a|), i.e. h is differentiable at a with Dh(a) = τ(a). With step 9, h is differentiable at every point of ℝⁿ.

11. (Dh is continuous at every a ∈ A.) Let a ∈ A and ε > 0. Put η := ε/(2(1 + 700M)), take δ ∈ (0, 1] from step 1 with this η, and let |x − a| < δ/4. We show ‖Dh(x) − τ(a)‖ ≤ ε/2.
- If x ∈ A: by step 10, Dh(x) = τ(x), and by step 1(i), ‖τ(x) − τ(a)‖ ≤ η ≤ ε/2.
- If x ∉ A, let b := π(x) ∈ A. By steps 6 and 9 (Σ w_c(x) = 1 and Σ Dw_c(x) = 0),
Dh(x) − τ(a) = Σ_{c∈N(x)} w_c(x)(τ(π(c)) − τ(a)) + Σ_{c∈N(x)} (P_{π(c)}(x) − P_b(x)) Dw_c(x).
- First sum: for c ∈ N(x), |π(c) − a| ≤ 3|x − a| < δ, so ‖τ(π(c)) − τ(a)‖ ≤ η. The convex combination therefore has norm ≤ η.
- Second sum, setup: d(x) ≤ |x − a| < δ/4 < 1, so r(x) = d(x)/100. Also |b − a| ≤ 2|x − a| < δ, so ‖τ(b) − τ(a)‖ ≤ η.
- For c ∈ N(x) let e := π(c). Then |e − a| < δ and ‖τ(e) − τ(a)‖ ≤ η, so ‖τ(e) − τ(b)‖ ≤ 2η. Moreover |x − e| ≤ 2 d(x) and |e − b| ≤ |e − x| + |x − b| ≤ 3 d(x).
- By (I) with the pair (b, e) and step 1(ii) (both b and e lie within δ of a):
|P_e(x) − P_b(x)| ≤ |f(e) − f(b) − τ(b)(e − b)| + ‖τ(e) − τ(b)‖ |x − e| ≤ 3η d(x) + 4η d(x) = 7η d(x) = 700 η r(x).
- With step 7 the second sum has norm ≤ 700 η r(x) · M/r(x) = 700 η M.
- Altogether ‖Dh(x) − τ(a)‖ ≤ η(1 + 700M) = ε/2 < ε.
So Dh is continuous at every point of A. At points x ∉ A, Dh is continuous because h is C^∞ near x (step 9). Hence h is differentiable with continuous derivative, i.e. h ∈ C¹(ℝⁿ) (Mathlib contDiff_one_iff_fderiv).

12. (Conclusion.) h is C¹. For every a ∈ A, h(a) = f(a) by definition, and h is Fréchet differentiable at a with derivative τ(a) by step 10. ∎

Lean realization (checked during decomposition). The pinned SimonGMT source Poincare/SimonGMT/Chapter02/WhitneyExtension.lean (simongmt 2b36630) proves this construction. Its .olean is absent from the shared package tree, but it imports only the built modules Poincare.SimonGMT.Chapter02.WhitneyJet and Poincare.SimonGMT.Chapter02.WhitneyPartition. Copied verbatim to a new file GMT/Ch06/WhitneyExtension.lean (module GMT.Ch06.WhitneyExtension; new .lean files under GMT/Ch06/ are accepted by the comparator), it compiles. The child theorem is then
obtain ⟨h, hh, hEq, hD⟩ := Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney (E := Eucl n) (h := f) (D := τ) hA ⟨hf, hτ, hrem⟩; exact ⟨h, hh, fun a ha => ⟨hEq ha, hD a ha⟩⟩.
The axioms are exactly propext, Classical.choice and Quot.sound. No other DAG branch vendors this file, so it must be added only once.

## Key steps

1. A = ∅ is trivial. Use the affine jets P_b(y) = f(b) + τ(b)(y − b) and the identity (I) for P_b − P_a. Condition (‡) on A ∩ B̄₁(a) and continuity of τ give a local uniform estimate.
2. Whitney radius r = min(1, d)/100 with comparability. Vitali (Simon 1.3.4 / Mathlib) gives disjoint balls B_{r(c)}(c), c ∈ Z, whose 4-fold enlargements cover ℝⁿ ∖ A, with overlap bounded by N(n).
3. Rescaled bumps φ_c and weights w_c = φ_c/Σφ form a locally finite partition of unity on ℝⁿ ∖ A with Σ_{N(x)} ‖Dw_c(x)‖ ≤ M/r(x).
4. Nearest anchors π(c) ∈ A satisfy |x − π(c)| ≤ 2d(x) and |π(c) − a| ≤ 3|x − a|.
5. h := f on A and h := Σ_c w_c P_{π(c)} off A; h is C^∞ on ℝⁿ ∖ A.
6. At a ∈ A, the convex combination of jet differences is ≤ ε|x − a|, so Dh(a) = τ(a).
7. Dh is continuous at a ∈ A because ‖Dh(x) − τ(a)‖ ≤ η(1 + 700M). Hence h ∈ C¹ with h = f and Dh = τ on A.
8. Lean: vendor SimonGMT WhitneyExtension.lean verbatim under GMT/Ch06/ and apply exists_contDiff_one_extension_of_whitney (standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project, project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in workspace and lake-packages-25730c7c/{simongmt,mathlib} = d8d46c95…, 2b3663083f3fe399b6296fb8eaee52169170e197, 25730c7c…`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean (identical); cmp workspace Contract.lean vs Submission.lean (identical)`
- `python3 -I over dag.json: id/lean_name/status of all 200 nodes; regex scan Whitney|Lusin|Luzin|Egoroff|Egorov|Rademacher|ContDiff ℝ 1|tendstoUniformly|IsClosed; assert the selected node's lean_statement is byte-equal to the frozen type; check lpf_c1r_lusin_closed, lpf_c1r_egoroff_closed, lpf_c1r_uniform_remainder, lpf_c1r_whitney_extension are unused`
- `grep -rl 'lpf_c1r' and 'exists_contDiff_one_extension_of_whitney|WhitneyExtension' over runs/…/nodes (no other branch vendors Whitney; names free)`
- `sed -n 150,275p book/chapter-02.txt (Simon Thm 1.5, Thm 1.6 (‡), Remark 1.7, printed proof of 1.5; no printed proof of 1.6)`
- `grep -n 'Vitali|Covering Lemma|Lusin|Egoroff' book/chapter-01.txt; sed -n 340,372p and 605,640p (Lusin 1.17, 5-times Covering Lemma 3.4 with property (*))`
- `sed SimonGMT Chapter02/{WhitneyJet,WhitneyCover,WhitneyPartition,WhitneyExtension}.lean and Chapter01/Lusin.lean; grep '^theorem|^def|^structure'; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter0{1,2} (Lusin, WhitneyJet/Cover/Partition built; WhitneyExtension.olean absent)`
- `grep in snapshot mathlib: LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385), measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372,378), MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean:1036; exists_isClosed_diff_lt deprecated), tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205, ε : ℝ≥0∞), addHaar_sphere_of_ne_zero (MeasureTheory/Measure/Lebesgue/EqHaar.lean:519), LocallyFinite.isClosed_iUnion (Topology/LocallyFinite.lean:128), continuousOn_clm_apply (Analysis/Normed/Module/FiniteDimension.lean:518), norm_fderiv_le_of_lipschitz (Analysis/Calculus/FDeriv/Basic.lean:947)`
- `python3 -I scope.py (verifier gmt-compare.contract_scope → opens MeasureTheory Filter Set Metric; scoped ENNReal NNReal Topology; namespace GMT.Ch06; Chapter06/03/01 opens; noncomputable section; end); python3 -I validate.py (lean_contract.validate_lean_statement on all 4 child statements: OK)`
- `sed gmt-compare.py child_modules/candidate_inputs (generated NodeChallenge imports GMT.Ch06.Submission; new .lean files allowed under GMT/Ch06/)`
- `lean src/Submission.lean -o build/GMT/Ch06/Submission.olean in scratch /tmp/c1real-decomp with LEAN_PATH to the shared package builds (shared tree untouched)`
- `lean tests/Stmts.lean, tests/Assembly.lean, tests/Interface.lean, tests/Api.lean, tests/Combined.lean, tests/WhitneyChild.lean, tests/Verbatim.lean with #check and #print axioms; lean vend2/WhitneyExtension.lean -o build/GMT/Ch06/WhitneyExtension.olean (verbatim SimonGMT source)`
- `Agent (independent adversarial review of the four child proofs, the Lean statements and the assembly): all OK; optional wording polish applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/tmp/c1real-tools/stmts.json`
- `/tmp/c1real-tools/scope.py`
- `/tmp/c1real-tools/validate.py`
- `/tmp/c1real-decomp/tests/Stmts.lean`
- `/tmp/c1real-decomp/tests/Assembly.lean`
- `/tmp/c1real-decomp/tests/Interface.lean`
- `/tmp/c1real-decomp/tests/Api.lean`
- `/tmp/c1real-decomp/tests/WhitneyChild.lean`
- `/tmp/c1real-decomp/tests/Verbatim.lean`
- `/tmp/c1real-decomp/tests/Combined.lean`
- `/tmp/c1real-decomp/vend/WhitneyVendored.lean`
- `/tmp/c1real-decomp/vend2/WhitneyExtension.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c, simongmt 2b36630) holds the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Simon prints a proof of Thm 1.5 (p. 44) but none of Whitney's Thm 1.6.

Mathlib has no Lusin theorem for measurable functions, but provides Rademacher (LipschitzWith.ae_differentiableAt), measurableSet_of_differentiableAt, measurable_fderiv, closed inner regularity (MeasurableSet.exists_isClosed_sdiff_lt), Egorov (tendstoUniformlyOn_of_ae_tendsto, ε : ℝ≥0∞), addHaar_sphere_of_ne_zero, LocallyFinite.isClosed_iUnion, continuousOn_clm_apply and norm_fderiv_le_of_lipschitz.

SimonGMT provides:
- finite-measure Lusin, Chapter01.exists_isClosed_continuousOn_of_measurable (built; importable next to GMT.Ch06.Submission; standard axioms);
- the full Whitney C¹ extension, Chapter02.exists_contDiff_one_extension_of_whitney, whose hypothesis HasWhitneyC1Compatibility is exactly continuity of f and τ on A plus (‡). Its .olean is absent, but the source compiles verbatim as GMT/Ch06/WhitneyExtension.lean (it imports only the built WhitneyJet and WhitneyPartition), and the comparator accepts new .lean files under GMT/Ch06/.

All four child statements elaborate in the exact comparator child scope and pass validate_lean_statement. Combined.lean kernel-checks:
- the frozen parent type from the four children;
- uniform_remainder from egoroff_closed, with only the η_k facts stubbed;
- whitney_extension outright, with axioms propext, Classical.choice and Quot.sound.

The proposed lpf_c1r_* names are unused by all 200 DAG nodes and by every node artifact, and no other branch vendors Whitney.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
