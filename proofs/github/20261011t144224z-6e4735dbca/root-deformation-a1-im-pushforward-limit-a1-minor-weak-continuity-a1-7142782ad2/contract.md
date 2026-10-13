<!-- theorem-id: gmt-ch06/root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1 -->

## Theorem `Submission.deformation_ipl_minor_weak_continuity`

Let k, Q ∈ ℕ, Ω ⊆ ℝ^k (= Eucl k) open, ψ : ℝ^k → ℝ Lebesgue-integrable on Ω, α : ℝ^Q → Covector (Eucl Q) k (k-covectors on ℝ^Q) continuous with compact support, C ≥ 0, and let u_j : ℝ^k → ℝ^Q (j ∈ ℕ) and u₀ : ℝ^k → ℝ^Q all be C-Lipschitz on Ω, with u_j → u₀ uniformly on Ω. Then ∫_Ω ψ(w)·α(u_j(w))(∂_0u_j(w), …, ∂_{k−1}u_j(w)) dw → ∫_Ω ψ(w)·α(u₀(w))(∂_0u₀(w), …, ∂_{k−1}u₀(w)) dw as j → ∞, where ∂_bv(w) := fderiv ℝ v w (EuclideanSpace.single b 1) is the b-th partial derivative (Mathlib fderiv, equal to 0 where v is not differentiable) and dw is Lebesgue measure (volume).

Node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1111

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/691

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/691, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3577, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2202, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2185, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4929, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4932, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4947, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4952, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4960, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4965

## Lean problem

Declaration: `Submission.deformation_ipl_minor_weak_continuity`

```lean
∀ (k Q : ℕ) (Ω : Set (Eucl k)) (ψ : Eucl k → ℝ) (α : Eucl Q → Covector (Eucl Q) k) (C : ℝ≥0) (u : ℕ → Eucl k → Eucl Q) (u₀ : Eucl k → Eucl Q), IsOpen Ω → IntegrableOn ψ Ω (volume : Measure (Eucl k)) → Continuous α → HasCompactSupport α → (∀ j, LipschitzOnWith C (u j) Ω) → LipschitzOnWith C u₀ Ω → TendstoUniformlyOn u u₀ atTop Ω → Tendsto (fun j => ∫ w in Ω, ψ w * α (u j w) (fun b => fderiv ℝ (u j) w (EuclideanSpace.single b 1)) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, ψ w * α (u₀ w) (fun b => fderiv ℝ u₀ w (EuclideanSpace.single b 1)) ∂(volume : Measure (Eucl k))))
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

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the claim “weak continuity of minors” in step (f) of the parent proof and the estimate that follows it (“∫ψ(ω_γ∘u_j)M_γ(Du_j) − ∫ψ(ω_γ∘u)M_γ(Du) = ∫ψ(ω_γ∘u_j − ω_γ∘u)M_γ(Du_j) + ∫ψ(ω_γ∘u)(M_γ(Du_j) − M_γ(Du)) → 0”), proved here in full for an arbitrary continuous compactly supported covector field α in place of the test form ω. This is the classical weak continuity of Jacobian minors in W^{1,∞} (J. M. Ball, Convexity conditions and existence theorems in nonlinear elasticity, Arch. Rational Mech. Anal. 63 (1977) 337–403; I. Fonseca, G. Leoni, J. Malý, Weak continuity and lower semicontinuity results for determinants, Arch. Rational Mech. Anal. 178 (2005) 411–448, https://link.springer.com/article/10.1007/s00205-005-0377-2; L. C. Evans, Partial Differential Equations, §8.1.4(b), Lemma 1 for the divergence-free rows of cofactor matrices).

Conventions. ℝ^k = Eucl k with Lebesgue measure dw = volume; e_b := EuclideanSpace.single b 1 (b ∈ Fin k). For a map v : ℝ^k → ℝ^Q, v^a := EuclideanSpace.proj a ∘ v (a ∈ Fin Q), ∂_bv(w) := Dv(w)e_b = fderiv ℝ v w e_b (Mathlib's fderiv, which is 0 where v is not differentiable) and ∂_bv^a(w) := (∂_bv(w))^a. For r ∈ ℕ, a : Fin r → Fin Q and b : Fin r → Fin k let M_{a,b}(v)(w) := det(∂_{b(s)}v^{a(t)}(w))_{t,s ∈ Fin r} (an r×r minor of the Jacobian matrix; the empty determinant is 1). Covectors carry the operator norm (|β(v₁,…,v_k)| ≤ ‖β‖Π|v_s|) and ‖α‖_∞ := sup_y‖α(y)‖ < ∞ (α is continuous with compact support). I(k,Q) := SimonMultiIndex k Q, dy^γ := wedgeCovectors k (fun t => EuclideanSpace.proj (γ t)), α_γ(y) := euclideanCovectorCoordinate (α y) γ = α(y)(e_{γ(0)},…,e_{γ(k−1)}).

0. (Rademacher bounds; integrability.) Let v be C-Lipschitz on Ω. By Rademacher's theorem (Mathlib LipschitzOnWith.ae_differentiableWithinAt_of_mem; Ω is open, so differentiability within Ω at w ∈ Ω is differentiability at w), v is differentiable at a.e. w ∈ Ω; at such w, v is C-Lipschitz on a ball around w, so ‖Dv(w)‖ ≤ C; at the other points Dv(w) = 0. Hence |∂_bv^a(w)| ≤ C for all w ∈ Ω, and by the Leibniz formula |M_{a,b}(v)(w)| ≤ r!·C^r on Ω. The map w ↦ Dv(w) is Borel (Mathlib measurable_fderiv) and v is continuous on Ω, so w ↦ α(v(w))(∂_0v(w),…,∂_{k−1}v(w)) is a.e.-strongly measurable on Ω and bounded by ‖α‖_∞C^k there. Multiplied by ψ it is integrable on Ω. All integrals below exist (for u_j, j ∈ ℕ, and for u₀).

1. (Reduction to minors.) By the sibling covector_expansion, α(y) = Σ_{γ∈I(k,Q)} α_γ(y)•dy^γ for every y, and by SimonGMT wedgeCovectors_apply_det, dy^γ(v_0,…,v_{k−1}) = det(EuclideanSpace.proj (γ t) (v_s))_{t,s} = det((v_s)^{γ(t)})_{t,s}. Taking v_s := ∂_sv(w): α(v(w))(∂_0v(w),…,∂_{k−1}v(w)) = Σ_γ α_γ(v(w))·M_{γ,id}(v)(w), where id : Fin k → Fin k is the identity. The sum over γ is finite, so it suffices to show for each γ ∈ I(k,Q):
 ∫_Ω ψ·(α_γ∘u_j)·M_{γ,id}(u_j) dw → ∫_Ω ψ·(α_γ∘u₀)·M_{γ,id}(u₀) dw.

2. (Splitting.) The difference of the two sides equals D₁(j) + D₂(j) with D₁(j) := ∫_Ω ψ(α_γ∘u_j − α_γ∘u₀)M_{γ,id}(u_j) and D₂(j) := ∫_Ω ψ(α_γ∘u₀)(M_{γ,id}(u_j) − M_{γ,id}(u₀)).
 (a) α_γ is continuous with compact support, hence bounded and uniformly continuous; since sup_{w∈Ω}|u_j(w) − u₀(w)| → 0 (uniform convergence on Ω), ε_j := sup_{w∈Ω}|α_γ(u_j(w)) − α_γ(u₀(w))| → 0, and by Step 0 |D₁(j)| ≤ ε_j·k!C^k·∫_Ω|ψ| → 0.
 (b) η := ψ·(α_γ∘u₀) is integrable on Ω (α_γ is bounded and α_γ∘u₀ is continuous on Ω). By the Claim of Step 3 with v_j := u_j, v := u₀, r := k, a := γ, b := id, we get D₂(j) → 0.

3. (Claim: weak-* convergence of minors.) Let v_j (j ∈ ℕ) and v be maps ℝ^k → ℝ^Q, all C-Lipschitz on Ω, with v_j → v uniformly on Ω. Then for all r ∈ ℕ, a : Fin r → Fin Q, b : Fin r → Fin k and every η integrable on Ω: ∫_Ω η·M_{a,b}(v_j) → ∫_Ω η·M_{a,b}(v). Proof by induction on r (for all a, b, η simultaneously).
 (3.0) (Smooth test functions suffice.) Assume the convergence for all φ ∈ C_c^∞(Ω) (C^∞, compact support, tsupport φ ⊆ Ω). Given η integrable on Ω and ε > 0, choose φ ∈ C_c^∞(Ω) with ∫_Ω|η − φ| < ε (C_c^∞(Ω) is dense in L¹(Ω): approximate η·1_Ω in L¹ by a continuous function with compact support in the open set Ω and mollify it). By Step 0, |∫ηM_{a,b}(v_j) − ∫ηM_{a,b}(v)| ≤ 2·r!C^r·ε + |∫φ(M_{a,b}(v_j) − M_{a,b}(v))|, and the claim for η follows. Fix φ ∈ C_c^∞(Ω) and K := tsupport φ (compact, K ⊆ Ω).
 (3.1) (r = 0.) M_{a,b} ≡ 1 and there is nothing to prove.
 (3.2) (Integration-by-parts identity.) Let r ≥ 1. For q ∈ Fin r let a′ : Fin (r−1) → Fin Q list a(1),…,a(r−1) (all rows except row 0), b^{(q)} : Fin (r−1) → Fin k list b without its q-th entry, and C_q(v) := (−1)^q·M_{a′,b^{(q)}}(v), the cofactor of the entry (0,q). Laplace expansion along row 0 gives M_{a,b}(v) = Σ_q ∂_{b(q)}v^{a(0)}·C_q(v). We prove, for every map v that is C-Lipschitz on Ω,
 (P) ∫_Ω φ·M_{a,b}(v) dw = −Σ_q ∫_Ω v^{a(0)}·C_q(v)·∂_{b(q)}φ dw.
 (i) Piola identity. If v is C² on a neighbourhood of K, then Σ_q ∂_{b(q)}[C_q(v)] = 0 there. For r = 1, C_0 ≡ 1. For r ≥ 2 let R_t := (∂_{b(0)}v^{a(t)},…,∂_{b(r−1)}v^{a(t)}) (t = 1,…,r−1) and let ε_q be the q-th unit row vector; expanding along row 0, C_q(v) = det N_q where N_q has row 0 equal to ε_q and row t equal to R_t. Differentiating the determinant row by row, ∂_{b(q)}det N_q = Σ_{t≥1} det(N_q with row t replaced by ∂_{b(q)}R_t), and ∂_{b(q)}R_t = Σ_s H^t_{qs}ε_s with H^t_{qs} := ∂_{b(q)}∂_{b(s)}v^{a(t)}. Hence Σ_q∂_{b(q)}C_q(v) = Σ_{t≥1}Σ_{q,s}H^t_{qs}·D_t(q,s), where D_t(q,s) is the determinant of the matrix with row 0 equal to ε_q, row t equal to ε_s and the remaining rows R_u. H^t is symmetric in (q,s) (Schwarz's theorem, v ∈ C²) and D_t is antisymmetric in (q,s) (exchange of rows 0 and t), so every double sum vanishes.
 (ii) (P) for v of class C² near K. By (i), M_{a,b}(v) = Σ_q[∂_{b(q)}v^{a(0)}·C_q(v) + v^{a(0)}·∂_{b(q)}C_q(v)] = Σ_q ∂_{b(q)}(v^{a(0)}C_q(v)) near K. Multiplying by φ and integrating by parts in the direction e_{b(q)} (φ is C^∞ with compact support K ⊆ Ω, v^{a(0)}C_q(v) is C¹ near K) gives (P).
 (iii) (P) for v C-Lipschitz on Ω. Choose d > 0 with K_{3d} := {w : dist(w,K) ≤ 3d} ⊆ Ω (K compact, Ω open). Extend each coordinate v^a|_Ω to a C-Lipschitz function ṽ^a on ℝ^k (McShane extension, Mathlib LipschitzOnWith.extend_real); then ṽ = v on Ω, so Dṽ = Dv at every point of Ω where either is differentiable, and |∂_bṽ^a| ≤ C everywhere. Let ρ_δ (0 < δ < d) be a standard mollifier (C^∞, ≥ 0, supported in the ball B_δ(0), ∫ρ_δ = 1) and v_δ := ρ_δ * ṽ componentwise. Then v_δ is C^∞; v_δ → ṽ uniformly on ℝ^k as δ → 0 (ṽ is uniformly continuous); ∂_bv_δ = ρ_δ * ∂_bṽ (differentiate under the integral sign: the difference quotients (ṽ(z + te_b) − ṽ(z))/t are bounded by C and converge a.e. to ∂_bṽ(z) by Rademacher, so dominated convergence applies), hence |∂_bv_δ^a| ≤ C; and ∂_bv_δ → ∂_bṽ a.e. along any sequence δ_m → 0 (Lebesgue differentiation for mollifiers, Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable). Apply (ii) to v_{δ_m} and let m → ∞: on K the integrands φ·M_{a,b}(v_{δ_m}) and v_{δ_m}^{a(0)}C_q(v_{δ_m})∂_{b(q)}φ converge a.e. (M_{a,b} and C_q are polynomials in the first derivatives) and are bounded by r!C^r|φ| and (sup_K|ṽ| + 1)(r−1)!C^{r−1}|∂_{b(q)}φ| respectively (for large m), which are integrable and vanish off K; dominated convergence gives (P) for ṽ. Since ṽ = v on Ω and Dṽ = Dv a.e. on K ⊆ Ω, (P) holds for v.
 (3.3) (Induction step, r ≥ 1.) By (P) for v_j and for v,
 ∫φM_{a,b}(v_j) − ∫φM_{a,b}(v) = −Σ_q[∫(v_j^{a(0)} − v^{a(0)})C_q(v_j)∂_{b(q)}φ + ∫v^{a(0)}(C_q(v_j) − C_q(v))∂_{b(q)}φ].
 The first integral is bounded by sup_Ω|v_j − v|·(r−1)!C^{r−1}·∫|∂_{b(q)}φ| → 0 (Step 0 for the cofactors). The second tends to 0 by the induction hypothesis for the (r−1)×(r−1) minors C_q = ±M_{a′,b^{(q)}}, tested against η_q := v^{a(0)}∂_{b(q)}φ, which is integrable on Ω (bounded, since v is continuous on the compact K, and supported in K). Hence ∫φM_{a,b}(v_j) → ∫φM_{a,b}(v); with (3.0) the Claim is proved.

4. (Conclusion.) Steps 2(a), 2(b) and 3 give D₁(j) + D₂(j) → 0 for every γ ∈ I(k,Q); summing over the finitely many γ (Step 1) proves the statement. Degenerate cases: for k = 0 the integrand is ψ(w)α(u_j(w))(()), I(0,Q) has a single element with M ≡ 1, and Step 2(a) alone suffices; for Q < k, Covector (Eucl Q) k = 0 (I(k,Q) is empty in the expansion), so both sides are 0; Ω = ∅ is trivial. ∎

## Key steps

1. Rademacher: |∂_bu^a| ≤ C on Ω, so all integrands are dominated by ‖α‖_∞C^k|ψ| and every minor of order r is bounded by r!C^r.
2. Sibling covector_expansion and wedgeCovectors_apply_det: α(u)(∂_0u,…,∂_{k−1}u) = Σ_γ α_γ(u)·M_γ(Du), a finite sum of k×k Jacobian minors.
3. Splitting: uniform continuity of α_γ and uniform convergence handle ψ(α_γ∘u_j − α_γ∘u₀)M_γ(Du_j); the rest is weak-* convergence of minors tested against ψ·(α_γ∘u₀) ∈ L¹(Ω).
4. Weak-* convergence of minors by induction on the order: density of C_c^∞(Ω) in L¹(Ω), and ∫φM = −Σ_q∫v^{a(0)}C_q∂_{b(q)}φ from Laplace expansion and the Piola identity (symmetric Hessian against antisymmetric determinants), extended from C² to Lipschitz maps by mollification.
5. Induction step: uniform convergence of v_j and the induction hypothesis for the cofactors tested against v^{a(0)}∂_{b(q)}φ.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: node root.deformation-a1.im_pushforward_limit-a1 has status decomposing, 'subproblem decomposition attempt 3', children [] (attempts 1-2 accepted by review but never activated)`
- `python3 -I over dag.json: status/candidate_commit/lean_statement of ltg_tau_unique_on_open, lpf_rectifiable_support_null, br_weightedTangent_congr, lpf_simple_nvector_algebra, cmb_covector_eq_sum_coord_smul_wedge, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables, lpf_tde_measurable_chart_differential (all accepted with candidate commits; types byte-identical to their handoffs and, for tau_unique/support_null, to the v2 children)`
- `python3 -I over dag.json: lean_name collisions for deformation_ipl_minor_weak_continuity, deformation_ipl_tangential_pushforward_aestronglyMeasurable, deformation_ipl_chart_convergence (none)`
- `rg -l 'deformation_ipl_' snapshot project, snapshot mathlib/Mathlib, lake-packages-25730c7c/simongmt/Poincare, GMT (no match)`
- `rg -n 'theorem HasWeightedApproximateTangentSpaceAt.unique|def nVectorPushforward|theorem nVectorPushforward_simple|def simpleNVector|theorem wedgeCovectors_apply_det|def covectorPullback' simongmt/Poincare/SimonGMT`
- `sed -n '205,260p' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `rg -n 'lemma locallyLipschitzOn_univ|LipschitzWith.locallyLipschitz|theorem IntegrableOn.mono_set_ae|theorem ae_le_set |theorem continuous_compContinuousLinearMapCLM|lemma tendsto_tsum_of_dominated_convergence|theorem integral_iUnion_ae|euclideanHausdorffMeasure_eq_volume|theorem measurable_fderiv |aestronglyMeasurable_iUnion_iff|LipschitzOnWith.extend_real|ae_convolution_tendsto_right_of_locallyIntegrable' snapshot mathlib/Mathlib`
- `git show a2a69a08f815abcf63c2e24fa1b57c6c02fdd1eb:GMT/Ch06/Submission.lean (accepted lpf_pi_measurability: continuity of (A, w) ↦ A_#w via ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM)`
- `python3 -I /tmp/ipl3/gen_types.py: verifier/lean_contract.py validate_lean_statement and gmt-compare.py contract_scope/child_modules for the twelve types`
- `lake env lean /tmp/ipl3/build/AllTypes.lean (exit 0, twelve sorry warnings); lake env lean /tmp/ipl3/build/Assembly.lean (exit 0, axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/ipl3/build/ProtoPM.lean (exit 0, same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-unique-on-open-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ipl3/build/AllTypes.lean`
- `/tmp/ipl3/build/Assembly.lean`
- `/tmp/ipl3/build/ProtoPM.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- The nine reused declarations are comparator-accepted with candidate commits.
- Their titles, statements and Lean types are copied byte-for-byte from dag.json.
- ltg_tau_unique_on_open and lpf_rectifiable_support_null are byte-identical to the v2 children tau_unique and support_null, which were then unaccepted.
New names: the three new names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot, the SimonGMT names in the pinned package):
- SimonGMT: HasWeightedApproximateTangentSpaceAt.unique (needs θ x ≠ 0), nVectorPushforward_simple, wedgeCovectors_apply_det, euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib: integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, measurable_fderiv, aestronglyMeasurable_iUnion_iff, continuous_compContinuousLinearMapCLM, LipschitzOnWith.extend_real, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable.
- No general weak-continuity-of-minors theorem exists in Mathlib or SimonGMT, and no accepted DAG node provides one (slicing_im_ll_gradient_weak_star, the first-order case, is still decomposing). minor_weak_continuity therefore stays a new child.
Lean checks:
- All twelve statements validate and elaborate in the exact comparator scope.
- The parent assembly compiles from four child types with only propext, Classical.choice and Quot.sound.
- The new measurability child compiles from its three sibling types with the same axioms.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
