<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_ftc-a1 -->

## Theorem `Submission.dph_iprod_horizontal_ftc`

Let m, q ∈ ℕ, X ∈ D_q(ℝ^m) = GeometricCurrentOn univ q with M(X) < ∞, ψ ∈ D^q(ℝ^{m+1}) and Ψ, Ψ′ : ℝ → D^q(ℝ^m) with Ψ(s)(x)(v) = ψ(cons(s,x))(fun i => ι(v i)) and Ψ′(s)(x)(v) = (fderiv ℝ ψ (cons(s,x)) e₀)(fun i => ι(v i)) for all s ∈ ℝ, x ∈ ℝ^m, v : Fin q → ℝ^m (cons, ι, e₀ as above). Then s ↦ X(Ψ′(s)) is continuous on ℝ; for every s ∈ ℝ the map t ↦ X(Ψ(t)) has derivative X(Ψ′(s)) at s; and ∫_0^1 X(Ψ′(s)) ds = X(Ψ(1)) − X(Ψ(0)).

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_ftc-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5233

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5642, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5679

Decomposition children: None

## Lean problem

Declaration: `Submission.dph_iprod_horizontal_ftc`

```lean
∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) q) (Ψ Ψ' : ℝ → TestFormOn (univ : Set (Eucl m)) q), X.mass < ∞ → (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v = (ψ : DifferentialForm (Eucl (m + 1)) q) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v = fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (EuclideanSpace.single 0 1) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Continuous (fun s => X (Ψ' s)) ∧ (∀ s : ℝ, HasDerivAt (fun t => X (Ψ t)) (X (Ψ' s)) s) ∧ ∫ s in (0 : ℝ)..1, X (Ψ' s) = X (Ψ 1) - X (Ψ 0)
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

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_ftc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent-supplied proof (fundamental theorem of calculus for s ↦ X(ψ_s)), with the uniform estimate of the difference quotient obtained from the mean value inequality (equivalently, the supplied integral representation ∫_0^1 [Dψ(cons(s+τh,x)) − Dψ(cons(s,x))](e₀) dτ). Siblings used: mass_bound (cmb_abs_apply_le_of_massOn_le), slice_norm (dph_iprod_slice_covector_norm_le, conjuncts (C2), (C3)) and slice_continuity (dph_iprod_slice_continuity, conjunct (D2)).

Notation. ℝ^p = Eucl p; cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1} for s ∈ ℝ, x ∈ ℝ^m; ι(v) := cons(0, v) = (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; ι∘v := (fun i => ι (v i)) and (e₀, ι∘v) := Fin.cons e₀ (fun i => ι (v i)) for tuples v; for a q-covector γ on ℝ^p (γ : Covector (Eucl p) q), |γ| := covectorEuclideanNorm γ = (Σ_{I : Fin q → Fin p strictly increasing} γ(b_{I 0}, …, b_{I (q−1)})²)^{1/2} with b_i := EuclideanSpace.basisFun (Fin p) ℝ i, and ‖γ‖ is its operator norm; D^q(ℝ^p) := TestFormOn univ q, D_q(ℝ^p) := GeometricCurrentOn univ q, M := mass; for a test form ω, ω(x) denotes (ω : DifferentialForm (Eucl p) q) x; Dψ(y) := fderiv ℝ ψ y.

Let X, ψ, Ψ, Ψ′ be as in the statement; g(t) := X(Ψ(t)).
0. (Mass estimate.) Let B := M(X).toReal ≥ 0 and c := √((m+1)^q) ≥ 0. As M(X) < ∞, X.massOn univ = M(X) = ENNReal.ofReal B (ENNReal.ofReal_toReal), so mass_bound with U = W = univ gives (MB): |X(ω)| ≤ B·C for every ω ∈ D^q(ℝ^m) and C with |ω(x)| ≤ C for all x.
1. (The form ψ′.) Let ψ′(y) := Dψ(y)(e₀). ψ is C^∞, so y ↦ Dψ(y) is continuous (ContDiff.continuous_fderiv) and ψ′ is continuous (evaluation at the constant e₀, Continuous.clm_apply). ψ′ has compact support: fderiv ℝ ψ has compact support (HasCompactSupport.fderiv) and ψ′ = (L ↦ L e₀) ∘ fderiv ℝ ψ maps 0 to 0 (HasCompactSupport.comp_left). By hypothesis Ψ′(s)(x)(v) = ψ′(cons(s,x))(ι∘v) for all s, x, v.
2. (Continuity, first conjunct.) By (D2) of slice_continuity with ω := ψ′ and the family Ψ′, s ↦ X(Ψ′(s)) is continuous on ℝ.
3. (Lines in the time direction.) cons(s + τ, x) = cons(s, x) + τ·e₀ for all s, τ, x: apply EuclideanSpace.equiv and compare coordinates by Fin.cases (coordinate 0: s + τ = s + τ·1; coordinate i.succ: x_i = x_i + τ·0).
4. (Derivative, second conjunct.) Fix s. By hasDerivAt_iff_isLittleO_nhds_zero and Asymptotics.isLittleO_iff it suffices, for every ε > 0, to show |g(s+h) − g(s) − h·X(Ψ′(s))| ≤ ε|h| for all h near 0. ψ′ is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). Choose ε′ > 0 with B·c·ε′ ≤ ε (e.g. ε′ := ε/(B·c + 1)) and δ > 0 with ‖ψ′(y) − ψ′(y′)‖ < ε′ whenever dist(y, y′) < δ; let |h| < δ. Put Θ_h := Ψ(s+h) − Ψ(s) − h·Ψ′(s) ∈ D^q(ℝ^m), so Θ_h(x)(v) = Ψ(s+h)(x)(v) − Ψ(s)(x)(v) − h·Ψ′(s)(x)(v).
   Fix x, put y := cons(s, x) and define the curve f(τ) := ψ(y + τe₀) − τ·ψ′(y) of q-covectors on ℝ^{m+1}. By the chain rule (τ ↦ y + τe₀ has derivative e₀, and ψ is differentiable), f has derivative f′(τ) = Dψ(y + τe₀)(e₀) − ψ′(y) = ψ′(y + τe₀) − ψ′(y) at every τ. For τ in the segment uIcc 0 h we have |τ| ≤ |h| < δ and dist(y + τe₀, y) = ‖τe₀‖ = |τ| (EuclideanSpace.norm_single), so ‖f′(τ)‖ < ε′. The mean value inequality on the convex set uIcc 0 h (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le) gives ‖f(h) − f(0)‖ ≤ ε′|h|. By step 3, f(h) − f(0) = ψ(cons(s+h,x)) − ψ(cons(s,x)) − h·ψ′(cons(s,x)), and hence, by the hypotheses on Ψ and Ψ′, Θ_h(x)(v) = (f(h) − f(0))(ι∘v) for every v. So (C2) and (C3) give |Θ_h(x)| ≤ |f(h) − f(0)| ≤ c·‖f(h) − f(0)‖ ≤ c·ε′·|h|.
   By (MB) for Θ_h, |X(Θ_h)| ≤ B·c·ε′·|h| ≤ ε|h|, and by linearity of X (map_sub, map_smul) X(Θ_h) = g(s+h) − g(s) − h·X(Ψ′(s)). Hence g has derivative X(Ψ′(s)) at s.
5. (Integral identity, third conjunct.) By step 4 for every s ∈ uIcc 0 1 and step 2 (a continuous function is interval integrable, Continuous.intervalIntegrable), intervalIntegral.integral_eq_sub_of_hasDerivAt gives ∫_0^1 X(Ψ′(s)) ds = X(Ψ(1)) − X(Ψ(0)). ∎

Lean aid (verified, optional). The following tactic block was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in the exact comparator scope (import GMT.Ch06.Submission; the contract's opens; namespace GMT.Ch06) as the proof of `theorem Submission.dph_iprod_horizontal_ftc : (<the frozen lean_statement>) := by`, with the sibling declarations present under their Submission names (zero errors; `#print axioms` lists only propext, Classical.choice and Quot.sound apart from sorryAx inherited from stubs that stood in for the already-accepted reused declarations). It can be used as is or as a guide:

```lean
  have hMB := Submission.cmb_abs_apply_le_of_massOn_le
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  have hC := Submission.dph_iprod_slice_continuity
  intro m q X ψ Ψ Ψ' hX hΨ hΨ'
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  have hmb : X.massOn univ ≤ ENNReal.ofReal X.mass.toReal := by
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  have hC2 := hSN.2.1 m q
  have hC3 := hSN.2.2 (m + 1) q
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt ((((m + 1 : ℕ)) : ℝ) ^ q) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Real.sqrt_nonneg _
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Eucl (m + 1), e₀ = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'def⟩ : ∃ ψ' : Eucl (m + 1) → Covector (Eucl (m + 1)) q,
      ψ' = fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y e₀ := ⟨_, rfl⟩
  have hψd : Differentiable ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) :=
    ψ.property.1.1.differentiable (by simp)
  have hψ'c : Continuous ψ' := by
    rw [hψ'def]
    exact (ψ.property.1.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ's : HasCompactSupport ψ' := by
    rw [hψ'def]
    exact (ψ.property.1.2.fderiv ℝ).comp_left
      (g := fun L : Eucl (m + 1) →L[ℝ] Covector (Eucl (m + 1)) q => L e₀) rfl
  have hΨ'2 : ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v =
      ψ' ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
    intro s x v
    rw [hΨ' s x v, hψ'def, he₀]
  have hcont := (hC.2 m q X hX ψ' Ψ' hψ'c hψ's hΨ'2).1
  have hpath : ∀ (s τ : ℝ) (x : Eucl m),
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons (s + τ) (EuclideanSpace.equiv (Fin m) ℝ x)) =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) +
        τ • e₀ := by
    intro s τ x
    rw [he₀]
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t => X (Ψ t)) (X (Ψ' s)) s := by
    intro s
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    have huc := hψ's.uniformContinuous_of_continuous hψ'c
    obtain ⟨ε', hε', hε'ε⟩ : ∃ ε' > 0, X.mass.toReal * c * ε' ≤ ε := by
      refine ⟨ε / (X.mass.toReal * c + 1), by positivity, ?_⟩
      have hpos : 0 < X.mass.toReal * c + 1 := by positivity
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      nlinarith [mul_nonneg hB0 hc0]
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc ε' hε'
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    obtain ⟨Θ, hΘdef⟩ : ∃ Θ : TestFormOn (univ : Set (Eucl m)) q, Θ = Ψ (s + h) - Ψ s - h • Ψ' s :=
      ⟨_, rfl⟩
    have hΘx : ∀ (x : Eucl m) (v : Fin q → Eucl m), (Θ : DifferentialForm (Eucl m) q) x v =
        (Ψ (s + h) : DifferentialForm (Eucl m) q) x v - (Ψ s : DifferentialForm (Eucl m) q) x v -
          h * (Ψ' s : DifferentialForm (Eucl m) q) x v := by
      intro x v
      rw [hΘdef]
      rfl
    have hΘ : ∀ x, covectorEuclideanNorm ((Θ : DifferentialForm (Eucl m) q) x) ≤ c * (ε' * |h|) := by
      intro x
      obtain ⟨y, hy⟩ : ∃ y : Eucl (m + 1),
          y = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) :=
        ⟨_, rfl⟩
      obtain ⟨f, hfdef⟩ : ∃ f : ℝ → Covector (Eucl (m + 1)) q,
          f = fun τ => (ψ : DifferentialForm (Eucl (m + 1)) q) (y + τ • e₀) - τ • ψ' y := ⟨_, rfl⟩
      have hf : ∀ τ ∈ Set.uIcc (0 : ℝ) h,
          HasDerivWithinAt f (ψ' (y + τ • e₀) - ψ' y) (Set.uIcc (0 : ℝ) h) τ := by
        intro τ _
        have h1 : HasDerivAt (fun τ : ℝ => y + τ • e₀) e₀ τ := by
          simpa using ((hasDerivAt_id τ).smul_const e₀).const_add y
        have h2 : HasDerivAt (fun τ : ℝ => (ψ : DifferentialForm (Eucl (m + 1)) q) (y + τ • e₀))
            (ψ' (y + τ • e₀)) τ := by
          rw [hψ'def]
          exact (hψd _).hasFDerivAt.comp_hasDerivAt τ h1
        have h3 : HasDerivAt (fun τ : ℝ => τ • ψ' y) (ψ' y) τ := by
          simpa using (hasDerivAt_id τ).smul_const (ψ' y)
        rw [hfdef]
        exact (h2.sub h3).hasDerivWithinAt
      have hbound : ∀ τ ∈ Set.uIcc (0 : ℝ) h, ‖ψ' (y + τ • e₀) - ψ' y‖ ≤ ε' := by
        intro τ hτ
        rw [← dist_eq_norm]
        apply le_of_lt
        apply hδ'
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he₀, EuclideanSpace.norm_single, norm_one,
          mul_one, Real.norm_eq_abs]
        have : |τ| ≤ |h| := by
          rcases le_total 0 h with h0 | h0
          · rw [Set.uIcc_of_le h0] at hτ
            rw [abs_of_nonneg hτ.1, abs_of_nonneg h0]; exact hτ.2
          · rw [Set.uIcc_of_ge h0] at hτ
            rw [abs_of_nonpos hτ.2, abs_of_nonpos h0]; linarith [hτ.1]
        exact lt_of_le_of_lt this hh
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound (convex_uIcc 0 h)
        Set.left_mem_uIcc Set.right_mem_uIcc
      rw [sub_zero, Real.norm_eq_abs] at hmv
      have hγ : ∀ v : Fin q → Eucl m, (f h - f 0) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) = (Θ : DifferentialForm (Eucl m) q) x v := by
        intro v
        rw [hΘx, hΨ, hΨ, hΨ'2, hfdef, hpath, ← hy]
        simp only [zero_smul, add_zero, ContinuousAlternatingMap.sub_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
        ring
      have h4 := hC2 (f h - f 0) ((Θ : DifferentialForm (Eucl m) q) x) (fun v => (hγ v).symm)
      refine h4.trans ((hC3 _).trans ?_)
      rw [← hc]
      exact mul_le_mul_of_nonneg_left hmv hc0
    have h5 := hMB m q univ univ X Θ X.mass.toReal (c * (ε' * |h|)) hB0 hmb (subset_univ _) hΘ
    have hlin : X Θ = X (Ψ (s + h)) - X (Ψ s) - h • X (Ψ' s) := by
      rw [hΘdef]
      have e1 := map_sub X.toCurrent (Ψ (s + h) - Ψ s) (h • Ψ' s)
      have e2 := map_sub X.toCurrent (Ψ (s + h)) (Ψ s)
      have e3 := map_smul X.toCurrent h (Ψ' s)
      exact e1.trans (by rw [e2, e3])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, ← hlin]
    calc |X Θ| ≤ X.mass.toReal * (c * (ε' * |h|)) := h5
      _ = (X.mass.toReal * c * ε') * |h| := by ring
      _ ≤ ε * |h| := mul_le_mul_of_nonneg_right hε'ε (abs_nonneg h)
  refine ⟨hcont, hderiv, ?_⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcont.intervalIntegrable 0 1)
```

## Key steps

1. ψ′ := Dψ(·)(e₀) is continuous with compact support, so (D2) gives continuity of s ↦ X(Ψ′(s)).
2. cons(s+τ, x) = cons(s,x) + τ·e₀.
3. Mean value inequality and uniform continuity of ψ′: ‖ψ(cons(s+h,x)) − ψ(cons(s,x)) − h·ψ′(cons(s,x))‖ ≤ ε′|h| uniformly in x.
4. (C2), (C3), mass_bound and linearity of X give |X(Ψ(s+h)) − X(Ψ(s)) − h·X(Ψ′(s))| ≤ ε|h|, i.e. HasDerivAt.
5. intervalIntegral.integral_eq_sub_of_hasDerivAt gives the integral identity.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); python3 -I verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) → namespace GMT.Ch06 with its opens (exact child-comparator scope)`
- `grep -n '^def|^abbrev|^theorem|^structure' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormSupNorm,Product,GeometricPointProduct,ParametricCurrentContinuity,AffineCurrentPushforward,FormsDuality,FixedSupportCurrentTopology}.lean: GeometricCurrentOn (continuous' = sequential continuity at 0), TestFormOnConverges, exteriorDerivativeTestOn and GeometricCurrentOn.boundary_apply, exteriorDerivative = extDeriv, covectorEuclideanNorm, massAdmissibleOn, massOn/mass, zeroRegion/support; no product with [[0,1]], no slice-continuity, FTC or current-from-sup-bound lemma`
- `python3 -I over dag.json (662 nodes): statuses, lean_names and lean_statements of the four handoff prerequisites and of every accepted declaration mentioning covectorEuclideanNorm with ‖·‖, Fin.cons, HasDerivAt, ContinuousOn (fun s …) or →ₗ[ℝ] (found fiw_ims_sc_covectorNorm_le_opNorm = (C3), fiw_ims_sc_continuous_of_bound, iwl_sp_covectorEuclideanNorm_pullback_le; none covers (C1), slice continuity, (∗) or the FTC); isolated-comparator-result.json of the four reused nodes (passed = True)`
- `git show c8cb71851ed3018dcc8a0a89a946b8610884f81a:GMT/Ch06/Submission.lean (accepted Lean proof of fiw_ims_sc_covectorNorm_le_opNorm, reproduced as (C3) of slice_norm)`
- `grep in the snapshot mathlib for the library inputs of the child proofs: extDeriv_apply, Fin.cons_comp_succ_succAbove, Fin.removeNth_zero, fderiv_continuousAlternatingMap_apply_const_apply, HasCompactMulSupport.uniformContinuous_of_continuous (to_additive), Convex.norm_image_sub_le_of_norm_hasDerivWithin_le, hasDerivAt_iff_isLittleO_nhds_zero, intervalIntegral.integral_eq_sub_of_hasDerivAt, tsupport_fderiv_subset, norm_iteratedFDeriv_zero, EuclideanSpace.equiv, ContinuousAlternatingMap.le_opNorm: all found`
- `read /runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py (_existing_lean_name_problem; _solve_children maps a child to an accepted node with identical lean_name and lean_statement) and store.py (ensure returns existing nodes unchanged)`
- `uniqueness of the new names: python3 over dag.json lean_names; grep -rn 'dph_ip' GMT/ .lake/packages/simongmt/ and the reference project; git log --all -S 'dph_ip_' (no match)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on all 12 child statements; lake env lean on /tmp/dphip/lean/{Parent,Children}.lean (parent and 8 new statements elaborate) and on the interface/proof checks IfaceParent, IfaceBoundary, IfaceExists, ChkSliceNorm, ChkHSlices, ChkCriterion, ChkContinuity, ChkExtDeriv, ChkFTC and the assembled Recheck.lean built from the final JSON (0 errors; #print axioms: propext, Classical.choice, Quot.sound, plus sorryAx only via stubs of the four accepted reused declarations)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `GMT/Ch06/Contract.lean`
- `GMT/Ch06/Submission.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/parent-supplied-natural-proof.md`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/isolated-comparator-result.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/store.py`
- `/tmp/dphip/lean/Recheck.lean`

The pinned project and SimonGMT contain no product of a current with [[0,1]] in Eucl (m+1), no continuity of currents along slices, no slice identity for exterior derivatives, no FTC along slices and no current-from-sup-bound criterion, so steps 1–10 of the supplied proof are new obligations. Its black boxes (R1)–(R4) are comparator-accepted declarations with no sibling prerequisites (cmb_abs_apply_le_of_massOn_le, isoperimetric_apply_eq_zero_of_disjoint_support, iwl_sp_exists_compatible_testForm, iwl_cr_ci_slice_testForm; isolated comparators passed). They are reused by name with byte-identical frozen types, titles and statements. (C3) equals the accepted fiw_ims_sc_covectorNorm_le_opNorm of another branch; its accepted proof is reproduced inside the new child slice_norm. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot. All 12 child statements are valid one-line types and elaborate in the exact comparator scope. The eight new dph_iprod_* names are globally unique. A Lean file assembled from the final JSON proves every new child from exactly its declared dependencies, and the selected parent from the children, with 0 errors and only standard axioms besides the four reused stubs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
