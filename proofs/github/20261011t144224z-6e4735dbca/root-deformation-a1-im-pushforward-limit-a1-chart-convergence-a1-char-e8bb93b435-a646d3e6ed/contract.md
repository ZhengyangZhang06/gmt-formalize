<!-- theorem-id: gmt-ch06/root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1 -->

## Theorem `Submission.deformation_ipl_cc_chart_orientation_sign`

Let P, k ∈ ℕ, let U ⊆ ℝ^P be open, and let (M, θ, ξ) satisfy IsRectifiableTriple U k M θ ξ (H^k = μHE[k] on ℝ^P). Let Φ : ℝ^k → ℝ^P be C¹ and c-antilipschitz on an open set Ω ⊆ ℝ^k for some c > 0. Write ∂_bΦ(w) := DΦ(w)e_b (DΦ(w) = fderiv ℝ Φ w, e_b = EuclideanSpace.single b 1), ∂Φ(w) := (∂_0Φ(w), …, ∂_{k−1}Φ(w)) and JΦ(w) := √det(⟨∂_aΦ(w), ∂_bΦ(w)⟩)_{a,b}. Then there is σ : ℝ^k → ℝ, a.e.-strongly measurable for L^k⌞(Ω ∩ Φ⁻¹(M)) (L^k = volume), such that for L^k-a.e. w ∈ Ω ∩ Φ⁻¹(M): σ(w) ∈ {1, −1} and JΦ(w)·ξ(Φ(w)) = σ(w)·simpleNVector(∂Φ(w)).

Node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4399

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/731, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2422

Decomposition children: None

## Lean problem

Declaration: `Submission.deformation_ipl_cc_chart_orientation_sign`

```lean
∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)), IsOpen U → IsRectifiableTriple U k M θ ξ → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∃ σ : Eucl k → ℝ, AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) ∧ ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)), (σ w = 1 ∨ σ w = -1) ∧ Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • ξ (Φ w) = σ w • simpleNVector (fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1))
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

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (6c) of the parent proof, together with the measurability of the sign claimed in (6d), for a triple on an arbitrary open U. The parent's ingredients are: good parameters; ξ(x) = ε·simpleNVector τ with span τ = range DΦ(w); simpleNVector(∂Φ(w)) = det B·simpleNVector τ; |det B| = JΦ(w); and the sign built from the covector β_w with β_w(∂Φ(w)) = JΦ(w)². Two harmless changes are made:
 - the sign is σ(w) := 1 if ξ(Φ(w))(β_w) ≥ 0 and σ(w) := −1 otherwise, so σ is ±1 everywhere and no division by JΦ is needed;
 - β_w is written as the pull-back of one fixed covector, which makes w ↦ β_w visibly continuous.

Conventions. H := μHE[k] on ℝ^P; L := volume on ℝ^k; S := Ω ∩ Φ⁻¹(M). For a k-vector N and a k-covector γ, N(γ) is the pairing; simpleNVector v (γ) = γ(v); covectorPullback k A γ = γ(A·, …, A·). † is the Hilbert-space adjoint (ContinuousLinearMap.adjoint), and ‖·‖ on k-vectors is the operator norm.

1. (A Borel representative of ξ.) ξ is a.e.-strongly measurable for H⌞M (field aestronglyMeasurable of the triple). Fix a strongly measurable ξ̃ with ξ = ξ̃ H⌞M-a.e. (AEStronglyMeasurable.mk).
2. (Good points of M ∩ Φ(Ω).) For H⌞(M ∩ Φ(Ω))-a.e. y, the following three statements hold.
 (a) For every w ∈ Ω with Φ(w) = y, range DΦ(w) is a weighted approximate tangent space of (M, θ) at y. This is the sibling weighted_tangent_on_c1_chart with V := U. Its hypotheses hold: U is open; M ⊆ U, M is H-null-measurable, θ > 0 on M, and θ is H-integrable on M ∩ K for compact K ⊆ U (the fields subset, nullMeasurableSet, pos and integrableOn of the triple); Ω is open and Φ is C¹ and antilipschitz on Ω.
 (b) There is an orthonormal τ : Fin k → ℝ^P such that span τ is a weighted approximate tangent space of (M, θ) at y and ξ(y) = simpleNVector τ or ξ(y) = −simpleNVector τ. This is the field orients, an H⌞M-a.e. statement, restricted to M ∩ Φ(Ω) ⊆ M (ae_restrict_of_ae_restrict_of_subset).
 (c) ξ(y) = ξ̃(y), by step 1 restricted in the same way.
3. (Pull-back to parameters.) Apply the sibling ae_pullback to M, Φ, Ω and the property p(y) := (a) ∧ (b) ∧ (c). Its hypotheses hold: Ω is measurable (open), Φ is measurable (continuous), Φ is antilipschitz on Ω, and M is H-null-measurable. Hence S is L-null-measurable and p(Φ(w)) holds for L⌞S-a.e. w. Moreover L⌞S-a.e. w lies in S (ae_restrict_mem₀).
4. (The test covector.) Let β₀ := wedgeCovectors k (a ↦ EuclideanSpace.proj a), a k-covector on ℝ^k. Let β_w := covectorPullback k (DΦ(w)†) β₀, a k-covector on ℝ^P.
 - Formula. By wedgeCovectors_apply_det, for u = (u_0, …, u_{k−1}) in ℝ^P:
  β_w(u) = det(proj_a(DΦ(w)†u_b))_{a,b} = det(⟨e_a, DΦ(w)†u_b⟩)_{a,b} = det(⟨DΦ(w)e_a, u_b⟩)_{a,b}
  (EuclideanSpace.inner_single_left, adjoint_inner_right). In particular β_w(∂Φ(w)) = det(⟨∂_aΦ(w), ∂_bΦ(w)⟩)_{a,b} =: Δ(w).
 - Continuity of w ↦ β_w. w ↦ DΦ(w) is continuous because Φ is C¹ (ContDiff.continuous_fderiv); the adjoint is a linear isometry; A ↦ covectorPullback k A is continuous (it is ContinuousAlternatingMap.compContinuousLinearMapCLM, continuous by ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM); and evaluating a continuous linear map at the fixed β₀ is continuous.
5. (The sign and its measurability.) Put p(w) := ξ(Φ(w))(β_w). Put σ(w) := 1 if p(w) ≥ 0 and σ(w) := −1 if p(w) < 0; so σ(w) ∈ {1, −1} for every w.
 - By step 3(c), w ↦ ξ(Φ(w)) agrees L⌞S-a.e. with w ↦ ξ̃(Φ(w)), which is strongly measurable (ξ̃ strongly measurable, Φ measurable). So it is a.e.-strongly measurable for L⌞S.
 - The pairing (N, γ) ↦ N(γ) is bounded bilinear, hence continuous, on NVector × Covector (isBoundedBilinearMap_apply). With step 4, p is a.e.-strongly measurable for L⌞S.
 - σ = s∘p with the Borel function s(t) = 1 (t ≥ 0), s(t) = −1 (t < 0). So σ is a.e.-measurable, hence a.e.-strongly measurable, for L⌞S.
6. (The identity at good parameters.) Fix w ∈ S at which p(Φ(w)) holds; this is L⌞S-a.e. by step 3. Let x := Φ(w) and v := ∂Φ(w), and let τ be as in 2(b).
 (6.1) θ(x) > 0 since x ∈ M. By 2(a) (with this w) and 2(b), range DΦ(w) and span τ are both weighted approximate tangent spaces of (M, θ) at x. So they are equal (HasWeightedApproximateTangentSpaceAt.unique, which needs θ(x) ≠ 0).
 (6.2) Each v_b = DΦ(w)e_b lies in range DΦ(w) = span τ. So v_b = Σ_a c_a τ_a for some coefficients (Submodule.mem_span_range_iff_exists_fun), and pairing with τ_a gives c_a = ⟨τ_a, v_b⟩ by orthonormality (Orthonormal.inner_right_fintype). Let B be the k×k matrix B_{ba} := ⟨τ_a, v_b⟩ (Matrix.of); then v_b = Σ_a B_{ba} τ_a. The second identity of the sibling simple_nvector_algebra gives simpleNVector v = d·simpleNVector τ, where d := det B.
 (6.3) Norms. The first identity of simple_nvector_algebra for τ gives ‖simpleNVector τ‖² = det(⟨τ_a, τ_b⟩) = det I = 1, so ‖simpleNVector τ‖ = 1 (norms are ≥ 0). Hence ‖simpleNVector v‖ = |d|·‖simpleNVector τ‖ = |d|. For k-vectors use the operator-norm inequality ‖r·N‖ ≤ |r|·‖N‖ twice, with r = d and r = d⁻¹; the case d = 0 is direct.
 - The first identity for v gives Δ(w) = ‖simpleNVector v‖² = d². So JΦ(w) = √(d²) = |d|.
 - By step 4, simpleNVector v (β_w) = β_w(v) = Δ(w) = d².
 (6.4) If d = 0, then JΦ(w) = 0 and simpleNVector v = 0. So both sides of JΦ(w)·ξ(x) = σ(w)·simpleNVector v are 0.
 (6.5) If d ≠ 0: from simpleNVector v = d·simpleNVector τ and (6.3), d·simpleNVector τ(β_w) = d². Hence simpleNVector τ(β_w) = d.
  - If ξ(x) = simpleNVector τ, then p(w) = d. So σ(w) = 1 when d > 0 and σ(w) = −1 when d < 0; in both cases |d| = σ(w)·d. Therefore JΦ(w)·ξ(x) = |d|·simpleNVector τ = σ(w)·d·simpleNVector τ = σ(w)·simpleNVector v.
  - If ξ(x) = −simpleNVector τ, then p(w) = −d. So σ(w) = 1 when d < 0 and σ(w) = −1 when d > 0; in both cases −|d| = σ(w)·d. Therefore JΦ(w)·ξ(x) = −|d|·simpleNVector τ = σ(w)·d·simpleNVector τ = σ(w)·simpleNVector v.
 Thus σ(w) ∈ {1, −1} and JΦ(w)·ξ(Φ(w)) = σ(w)·simpleNVector(∂Φ(w)) for L⌞S-a.e. w. Together with step 5 this is the assertion. ∎
 For k = 0 every step holds verbatim: Fin 0-families are empty, B is the empty matrix with det B = 1, and JΦ ≡ 1.

Lean remark. The script below was verified with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b36630 as `theorem Submission.deformation_ipl_cc_chart_orientation_sign : (<frozen type>) := by` inside `namespace GMT.Ch06` of GMT/Ch06/Submission.lean. It uses the sibling declarations `Submission.lpf_simple_nvector_algebra`, `Submission.lpf_weighted_tangent_on_c1_chart`, `Submission.lpf_ccr_ae_pullback`, which were present as declarations of exactly their frozen types. With those sibling statements taken as hypotheses, #print axioms gives only propext, Classical.choice and Quot.sound. Its dependencies are `Submission.lpf_simple_nvector_algebra`, `Submission.lpf_weighted_tangent_on_c1_chart` and `Submission.lpf_ccr_ae_pullback`; no extra import is needed. `NormSMulClass ℝ (NVector (Eucl P) k)` is not synthesized in this environment, so the script proves ‖d • s‖ = |d|·‖s‖ from `ContinuousLinearMap.opNorm_smul_le` and uses `ContinuousLinearMap.opNorm_nonneg`.
Tactic script:
  intro P k U M θ ξ Φ Ω hU hT hΩ hΦC1 hΦanti
  have hΦc : Continuous Φ := hΦC1.continuous
  have hΦm : Measurable Φ := hΦc.measurable
  -- strongly measurable representative of ξ
  set ξt := hT.aestronglyMeasurable.mk ξ with hξt
  have hξtm : StronglyMeasurable ξt := hT.aestronglyMeasurable.stronglyMeasurable_mk
  have hξeq : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ξ x = ξt x :=
    hT.aestronglyMeasurable.ae_eq_mk
  -- the good property at points of M ∩ Φ(Ω)
  have hgoodH : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ Φ '' Ω)),
      (∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt k M θ y
          (LinearMap.range (fderiv ℝ Φ w).toLinearMap)) ∧
      (∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt k M θ y (Submodule.span ℝ (range τ)) ∧
        (ξ y = simpleNVector τ ∨ ξ y = -simpleNVector τ)) ∧
      ξ y = ξt y := by
    have h1 := Submission.lpf_weighted_tangent_on_c1_chart P k U M θ Φ Ω hU hT.subset hT.nullMeasurableSet hT.pos hT.integrableOn hΩ hΦC1
      hΦanti
    have h2 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M ∩ Φ '' Ω ⊆ M) hT.orients
    have h3 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M ∩ Φ '' Ω ⊆ M) hξeq
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  obtain ⟨hSm, hgood⟩ := Submission.lpf_ccr_ae_pullback P k M Φ Ω _ hΩ.measurableSet hΦm hΦanti hT.nullMeasurableSet hgoodH
  have hmemS : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)), w ∈ Ω ∩ Φ ⁻¹' M :=
    ae_restrict_mem₀ hSm
  -- notation
  set v : Eucl k → Fin k → Eucl P := fun w b => fderiv ℝ Φ w (EuclideanSpace.single b 1) with hv
  set J : Eucl k → ℝ := fun w => Real.sqrt (Matrix.of fun i j => inner ℝ
    (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det
    with hJdef
  -- the test covector β_w
  set β₀ : Covector (Eucl k) k := wedgeCovectors k (fun a => (EuclideanSpace.proj a : Eucl k →L[ℝ] ℝ))
    with hβ₀
  set β : Eucl k → Covector (Eucl P) k :=
    fun w => covectorPullback k (ContinuousLinearMap.adjoint (fderiv ℝ Φ w)) β₀ with hβdef
  have hβv : ∀ w, β w (v w) = (Matrix.of fun i j => inner ℝ (v w i) (v w j)).det := by
    intro w
    simp only [hβdef, covectorPullback_apply, hβ₀, wedgeCovectors_apply_det]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply]
    have h1 := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ)
      (ContinuousLinearMap.adjoint (fderiv ℝ Φ w) (v w j))
    rw [ContinuousLinearMap.adjoint_inner_right] at h1
    simp only [map_one, one_mul] at h1
    rw [h1]
    rfl
  have hβc : Continuous β := by
    have hfd : Continuous (fderiv ℝ Φ) := hΦC1.continuous_fderiv one_ne_zero
    have hadj : Continuous (fun w => ContinuousLinearMap.adjoint (fderiv ℝ Φ w)) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Eucl k) (F := Eucl P)).continuous.comp hfd
    have hcomp : Continuous (fun A : Eucl P →L[ℝ] Eucl k =>
        (covectorPullback k A : Covector (Eucl k) k →L[ℝ] Covector (Eucl P) k)) :=
      ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM
    exact (hcomp.comp hadj).clm_apply continuous_const
  -- the pairing and the sign
  set p : Eucl k → ℝ := fun w => ξ (Φ w) (β w) with hp
  set σ : Eucl k → ℝ := fun w => if 0 ≤ p w then 1 else -1 with hσdef
  have hpm : AEStronglyMeasurable p ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) := by
    have hξΦ : AEStronglyMeasurable (fun w => ξ (Φ w))
        ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) := by
      refine (hξtm.comp_measurable hΦm).aestronglyMeasurable.congr ?_
      filter_upwards [hgood] with w hw
      exact hw.2.2.symm
    have hpair : Continuous (fun q : NVector (Eucl P) k × Covector (Eucl P) k => q.1 q.2) :=
      isBoundedBilinearMap_apply.continuous
    exact hpair.comp_aestronglyMeasurable (hξΦ.prodMk hβc.aestronglyMeasurable)
  have hσm : AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) := by
    have hs : Measurable (fun t : ℝ => if 0 ≤ t then (1 : ℝ) else -1) :=
      Measurable.ite measurableSet_Ici measurable_const measurable_const
    exact (hs.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  refine ⟨σ, hσm, ?_⟩
  filter_upwards [hgood, hmemS] with w hw hwS
  obtain ⟨hw1, ⟨τ, hτ, hτT, hξτ⟩, -⟩ := hw
  have hθpos : 0 < θ (Φ w) := hT.pos _ hwS.2
  have hrange : LinearMap.range (fderiv ℝ Φ w).toLinearMap = Submodule.span ℝ (range τ) :=
    HasWeightedApproximateTangentSpaceAt.unique hθpos.ne' (hw1 w hwS.1 rfl) hτT
  have hσval : σ w = 1 ∨ σ w = -1 := by
    simp only [hσdef]; split_ifs <;> simp
  refine ⟨hσval, ?_⟩
  have hvmem : ∀ b, v w b ∈ Submodule.span ℝ (range τ) := by
    intro b; rw [← hrange]; exact LinearMap.mem_range_self _ _
  have hvexp : ∀ b, (∑ a, inner ℝ (τ a) (v w b) • τ a) = v w b := by
    intro b
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hvmem b)
    have hc : ∀ a, inner ℝ (τ a) (v w b) = cf a := by
      intro a; rw [← hcf]; exact hτ.inner_right_fintype cf a
    simp_rw [hc]; exact hcf
  set B : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun b a => inner ℝ (τ a) (v w b) with hB
  have hS : simpleNVector (v w) = B.det • simpleNVector τ := by
    rw [← Submission.lpf_simple_nvector_algebra.2 P k B τ]
    congr 1
    funext b
    simp only [hB, Matrix.of_apply]
    exact (hvexp b).symm
  have hsτ : ‖simpleNVector τ‖ = 1 := by
    have h := Submission.lpf_simple_nvector_algebra.1 P k τ
    have hG : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ]
    rw [hG, Matrix.det_one] at h
    have h0 : 0 ≤ ‖simpleNVector τ‖ := ContinuousLinearMap.opNorm_nonneg _
    nlinarith [h]
  have hnsmul : ∀ (d : ℝ) (s : NVector (Eucl P) k), ‖d • s‖ = |d| * ‖s‖ := by
    intro d s
    apply le_antisymm
    · simpa [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le d s
    · by_cases hd : d = 0
      · simp only [hd, abs_zero, zero_mul]; exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le d⁻¹ (d • s)
        rw [smul_smul, inv_mul_cancel₀ hd, one_smul, Real.norm_eq_abs, abs_inv] at h
        have hpos : 0 < |d| := abs_pos.mpr hd
        calc |d| * ‖s‖ ≤ |d| * (|d|⁻¹ * ‖d • s‖) := by gcongr
          _ = ‖d • s‖ := by field_simp
  have hnormS : ‖simpleNVector (v w)‖ = |B.det| := by
    rw [hS, hnsmul, hsτ, mul_one]
  have hJ : J w = |B.det| := by
    have h := Submission.lpf_simple_nvector_algebra.1 P k (v w)
    show Real.sqrt (Matrix.of fun i j => inner ℝ (v w i) (v w j)).det = |B.det|
    rw [← h, Real.sqrt_sq (ContinuousLinearMap.opNorm_nonneg _), hnormS]
  have hSβ : simpleNVector (v w) (β w) = B.det ^ 2 := by
    rw [simpleNVector_apply, hβv, ← Submission.lpf_simple_nvector_algebra.1 P k (v w), hnormS, sq_abs]
  by_cases hd : B.det = 0
  · have hJ0 : J w = 0 := by rw [hJ, hd, abs_zero]
    have hS0 : simpleNVector (v w) = 0 := by rw [hS, hd, zero_smul]
    show J w • ξ (Φ w) = σ w • simpleNVector (v w)
    rw [hJ0, zero_smul, hS0, smul_zero]
  · have hs : simpleNVector τ (β w) = B.det := by
      have h1 : B.det * simpleNVector τ (β w) = B.det * B.det := by
        have := hSβ
        rw [hS, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
        rw [this]; ring
      exact mul_left_cancel₀ hd h1
    show J w • ξ (Φ w) = σ w • simpleNVector (v w)
    rw [hJ, hS, smul_smul]
    rcases hξτ with h | h
    · have hp' : p w = B.det := by
        show ξ (Φ w) (β w) = B.det
        rw [h, hs]
      rw [h]
      congr 1
      simp only [hσdef, hp']
      split_ifs with h0
      · rw [abs_of_nonneg h0]; ring
      · rw [abs_of_neg (lt_of_not_ge h0)]; ring
    · have hp' : p w = -B.det := by
        show ξ (Φ w) (β w) = -B.det
        rw [h, ContinuousLinearMap.neg_apply, hs]
      rw [h]
      have hcoef : -|B.det| = σ w * B.det := by
        simp only [hσdef, hp']
        split_ifs with h0
        · have hneg : B.det < 0 := lt_of_le_of_ne (by linarith) hd
          rw [abs_of_neg hneg]; ring
        · have hpos : 0 < B.det := by linarith
          rw [abs_of_pos hpos]; ring
      ext γ
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
      rw [← hcoef]; ring

## Key steps

1. Good points: weighted_tangent_on_c1_chart, the orientation clause and a Borel representative ξ̃ = ξ hold H^k⌞(M ∩ Φ(Ω))-a.e.; ae_pullback moves them to L^k⌞(Ω ∩ Φ⁻¹(M))-a.e. parameters.
2. β_w := covectorPullback k (DΦ(w)†) (wedge of the coordinate projections) is continuous in w with β_w(u) = det(⟨DΦ(w)e_a, u_b⟩); σ := sign of ξ(Φ(w))(β_w) (values ±1) is a.e.-strongly measurable.
3. At a good w: range DΦ(w) = span τ (uniqueness, θ > 0); ∂Φ = Bτ gives simpleNVector(∂Φ) = det B·simpleNVector τ, ‖simpleNVector τ‖ = 1, JΦ = |det B| and β_w(∂Φ) = (det B)².
4. If det B = 0 both sides vanish; otherwise simpleNVector τ(β_w) = det B, ξ(Φ(w))(β_w) = ±det B, and a sign case analysis gives JΦ·ξ(Φ(w)) = σ·simpleNVector(∂Φ(w)).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of workspace GMT/Ch06/Submission.lean, GMT/Ch06/Contract.lean and the snapshot project/GMT/Ch06/Contract.lean (byte-identical)`
- `python3 -I over dag.json: status, candidate_commit and lean_statement of the node's dependencies lpf_simple_nvector_algebra, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables (accepted), deformation_ipl_minor_weak_continuity and deformation_ipl_tangential_pushforward_aestronglyMeasurable (decomposing)`
- `python3 -I over dag.json: regex search jacob|change_of_var|antilip|gram|det|tannery|dominat|chart|area|orient|simple|pushforward over lean names, then lean_statement of lpf_wtc_cat_fderiv_lower_bound, lpf_wtc_cat_gram_jacobian_continuous, lpf_wtc_caf_signed_of_lintegral, lpf_pi_jacobian_local_bound, lpf_pi_measurability, lpf_pic_density_dominated, lpf_raf_chart_preimage_null, lpf_ccr_ae_pullback, lpf_weighted_tangent_on_c1_chart, lpf_wtc_chart_image_measurable_locally_finite, iwl_sp_sn_signed_simpleNVector_bound_ne_zero, fiw_ims_frame_sign, slicing_im_ll_twl_chart_integral_eq (decomposing, not reusable)`
- `python3 -I over nodes/*/parent-child-handoff.json: map the six reused node ids to their directories and check title/statement/lean_statement/lean_name byte-identity with dag.json (all True)`
- `python3 -I over dag.json: lean-name collision check for deformation_ipl_cc_gram_det_lower_bound, deformation_ipl_cc_signed_change_of_variables, deformation_ipl_cc_chart_orientation_sign, deformation_ipl_cc_chart_integral_representation, deformation_ipl_cc_pushforward_integrand_bound, deformation_ipl_cc_tendsto_setIntegral_of_partition (none); rg -l deformation_ipl_cc over GMT, snapshot project, snapshot Mathlib and SimonGMT (no match); git grep over all local branches (no match)`
- `rg -n 'abbrev (Covector|NVector)|def (simpleNVector|nVectorPushforward|covectorPullback|wedgeCovectors)|theorem wedgeCovectors_apply_det|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06; rg -n 'HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n over snapshot Mathlib: IsOpen.isSigmaCompact (no match), NullMeasurableSet.disjointed, disjointed_subset|iUnion_disjointed|disjoint_disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, setIntegral_congr_set, setIntegral_indicator, aestronglyMeasurable_indicator_iff₀, aestronglyMeasurable_iUnion_iff, Matrix.IsHermitian det_eq_prod_eigenvalues|eigenvalues_eq|mulVec_eigenvectorBasis, prod_le_prod₀, adjoint_inner_right, continuous_compContinuousLinearMapCLM, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, Orthonormal.inner_right_fintype, mem_span_range_iff_exists_fun, HasDerivAt.le_of_lipschitz, norm_fderiv_le_of_lipschitz, IsCompact.cthickening, mem_cthickening_of_dist_le, image_eq_zero_of_notMem_tsupport, HasCompactSupport.exists_bound_of_continuous, opNorm_smul_le, NormedSpace.toNormSMulClass`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted declaration format) and the import lines of all accepted candidate Submissions (extra imports already accepted)`
- `python3 -I verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (mode contract) for the twelve types`
- `lake env lean /tmp/ccv-decomp/ExactScope.lean (twelve types, exit 0); /tmp/ccv-decomp/Assembly.lean (parent from child and dependency types); /tmp/ccv-decomp/Dproof.lean, Cproof.lean, Bproof.lean, Aproof.lean (+Mathlib.Analysis.Matrix.Spectrum), Eproof.lean, Fproof.lean (+Mathlib.Analysis.Normed.Group.Tannery); /tmp/ccv-decomp/Final_*.lean (final Submission.* forms against stubs); /tmp/ccv-decomp/Inst.lean (NormSMulClass ℝ (NVector …) not synthesized)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-simple-nvector-algebra-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-pullback-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ccv-decomp/ExactScope.lean`
- `/tmp/ccv-decomp/Assembly.lean`
- `/tmp/ccv-decomp/Dproof.lean`
- `/tmp/ccv-decomp/Cproof.lean`
- `/tmp/ccv-decomp/Final_parent.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- Six accepted declarations are reused by name: lpf_simple_nvector_algebra, lpf_weighted_tangent_on_c1_chart, lpf_ccr_ae_pullback, lpf_raf_chart_change_of_variables, lpf_wtc_cat_fderiv_lower_bound and lpf_wtc_chart_image_measurable_locally_finite.
- Each has status accepted with a candidate commit, and its title, statement and Lean type are copied byte-for-byte from dag.json (identical to its handoff).
- The node's other dependencies (c1_cover, chart_chain_rule, minor_weak_continuity, pushforward_measurable) are used only by the parent assembly.
- No accepted DAG node or library lemma states the signed chart change of variables, the measurable chart orientation sign, the chart integral representation or the partition Tannery lemma. slicing_im_ll_twl_chart_integral_eq is still decomposing, so it cannot be reused.
New names: the six deformation_ipl_cc_ names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot):
- Matrix.IsHermitian spectral theorem (det_eq_prod_eigenvalues, eigenvalues_eq) and tendsto_tsum_of_dominated_convergence; both modules need an extra import.
- NullMeasurableSet.disjointed, integral_iUnion_ae, hasSum_integral_iUnion_ae, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, ContinuousLinearMap.adjoint_inner_right and ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.
- SimonGMT: wedgeCovectors_apply_det, nVectorPushforward_simple and HasWeightedApproximateTangentSpaceAt.unique.
- IsOpen.isSigmaCompact does not exist; the open-set exhaustion is written out explicitly.
- NormSMulClass ℝ (NVector …) is not synthesized; opNorm_smul_le is used instead.
Lean checks:
- All twelve types validate and elaborate in the exact comparator scope.
- The parent assembly compiles from the frozen child and dependency types.
- Every new child compiles from exactly its declared sibling types.
- All of these give only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
