<!-- theorem-id: gmt-ch06/root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1 -->

## Theorem `Submission.deformation_ipl_mwc_minor_weak_star`

Let k, Q ∈ ℕ, let Ω ⊆ ℝ^k (ℝ^k = Eucl k) be open, C ≥ 0, and let v_j : ℝ^k → ℝ^Q (j ∈ ℕ) and v₀ : ℝ^k → ℝ^Q all be C-Lipschitz on Ω with v_j → v₀ uniformly on Ω. For r ∈ ℕ, a : Fin r → Fin Q, b : Fin r → Fin k and u : ℝ^k → ℝ^Q let M_{a,b}(u)(w) := det(EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))_{t,s ∈ Fin r} (the r×r Jacobian minor with rows a and columns b; Mathlib fderiv, 0 where u is not differentiable; the empty determinant is 1). Then for every r, every a, b and every η : ℝ^k → ℝ that is Lebesgue-integrable on Ω: ∫_Ω η(w)·M_{a,b}(v_j)(w) dw → ∫_Ω η(w)·M_{a,b}(v₀)(w) dw as j → ∞ (dw = Lebesgue measure).

Node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4382

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4952, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4947

Decomposition children: None

## Lean problem

Declaration: `Submission.deformation_ipl_mwc_minor_weak_star`

```lean
∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q), IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω → TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k) (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))
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

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the Claim of step 3 of the parent proof together with its proof (3.0)–(3.3): induction on the order r, for all a, b, η simultaneously; step (3.0) is the sibling test_density and the identity (P) of (3.2) is the sibling minor_ibp_lipschitz. This is the classical weak continuity of Jacobian minors in W^{1,∞} (J. M. Ball, Arch. Rational Mech. Anal. 63 (1977) 337–403; I. Fonseca, G. Leoni, J. Malý, Arch. Rational Mech. Anal. 178 (2005) 411–448).

Notation. λ = Lebesgue measure; e_i := EuclideanSpace.single i 1; u^c := EuclideanSpace.proj c ∘ u. For a : Fin (r+1) → Fin Q, b : Fin (r+1) → Fin k and q ∈ Fin (r+1) put a′ := (t ↦ a(t.succ)) : Fin r → Fin Q and b^{(q)} := (s ↦ b(q.succAbove s)) : Fin r → Fin k. Then the cofactor of the sibling minor_ibp_lipschitz is C_q(u) = (−1)^q·M_{a′,b^{(q)}}(u).

0. (Bounds and measurability.) Let u be C-Lipschitz on Ω and w ∈ Ω. Since Ω is a neighbourhood of w, ‖fderiv ℝ u w‖ ≤ C (Mathlib norm_fderiv_le_of_lipschitzOn). Hence every entry satisfies |EuclideanSpace.proj c (fderiv ℝ u w (e_i))| ≤ ‖fderiv ℝ u w (e_i)‖ ≤ ‖fderiv ℝ u w‖·‖e_i‖ ≤ C (PiLp.norm_apply_le, ‖e_i‖ = 1), and by the Leibniz formula and the triangle inequality |M_{a,b}(u)(w)| ≤ r!·C^r for w ∈ Ω (an n×n matrix with entries bounded by c has |det| ≤ n!·c^n; prove it from Matrix.det_apply, since Matrix.det_le is not imported). The function w ↦ M_{a,b}(u)(w) is Borel measurable: each entry is EuclideanSpace.proj c applied to the measurable function w ↦ fderiv ℝ u w (e_i) (measurable_fderiv_apply_const), and the determinant is continuous in the entries (Continuous.matrix_det on the function space, measurable_pi_iff). Also u is continuous on Ω (LipschitzOnWith.continuousOn).

We prove by induction on r the statement P(r): for all a : Fin r → Fin Q, b : Fin r → Fin k and all η integrable on Ω, ∫_Ω η·M_{a,b}(v_j) → ∫_Ω η·M_{a,b}(v₀).

1. (r = 0.) A 0×0 determinant equals 1 (Matrix.det_isEmpty), so every term of the sequence equals ∫_Ω η: the sequence is constant.

2. (Step r → r+1: reduction to C¹ test functions.) Assume P(r) and fix a : Fin (r+1) → Fin Q and b : Fin (r+1) → Fin k. Apply the sibling test_density with f_j := M_{a,b}(v_j), f₀ := M_{a,b}(v₀) and B := (r+1)!·C^{r+1}: by Step 0 these functions are a.e.-strongly measurable for λ restricted to Ω and bounded by B on Ω. So it suffices to prove, for every φ : ℝ^k → ℝ of class C¹ with compact support and tsupport φ ⊆ Ω,
 ∫_Ω φ·M_{a,b}(v_j) → ∫_Ω φ·M_{a,b}(v₀).  (★)

3. (Integration by parts.) Fix such φ, let K := tsupport φ (compact, K ⊆ Ω) and dφ_q(w) := fderiv ℝ φ w (e_{b(q)}). dφ_q is continuous (φ ∈ C¹) and vanishes outside K (support_fderiv_subset), hence it has compact support and is integrable. By the sibling minor_ibp_lipschitz, for u ∈ {v_j, v₀},
 ∫_Ω φ·M_{a,b}(u) = −Σ_{q∈Fin(r+1)} ∫_Ω u^{a(0)}·((−1)^q·M_{a′,b^{(q)}}(u))·dφ_q.
 Hence (★) follows (tendsto_finsetSum, Tendsto.neg) once we show, for each fixed q,
 I_j := ∫_Ω v_j^{a(0)}·((−1)^q M_{a′,b^{(q)}}(v_j))·dφ_q → I_0 := ∫_Ω v₀^{a(0)}·((−1)^q M_{a′,b^{(q)}}(v₀))·dφ_q.  (★★)

4. (Integrability.) Each u ∈ {v_j, v₀} is continuous on Ω ⊇ K, so |u^{a(0)}| ≤ P_u on the compact set K for some constant P_u ≥ 0 (IsCompact.exists_bound_of_continuousOn). Every function F used below is a.e.-strongly measurable for λ restricted to Ω and satisfies |F(w)| ≤ c·|dφ_q(w)| for all w ∈ Ω with a constant c (on K use the bounds P_u and Step 0; off K, F(w) = 0 because F contains the factor dφ_q(w) = 0). Hence F is integrable on Ω (Integrable.mono′ with the integrable majorant c|dφ_q|). This applies to (v_j^{a(0)} − v₀^{a(0)})·((−1)^q M_{a′,b^{(q)}}(v_j))·dφ_q (c = (P_{v_j} + P_{v₀})·r!C^r) and to η_q·M_{a′,b^{(q)}}(u) (c = P_{v₀}·r!C^r), where η_q := v₀^{a(0)}·dφ_q. In particular η_q itself is integrable on Ω (c = P_{v₀}).

5. (Splitting.) By linearity (Step 4),
 I_j = ∫_Ω (v_j^{a(0)} − v₀^{a(0)})·((−1)^q M_{a′,b^{(q)}}(v_j))·dφ_q + (−1)^q·∫_Ω η_q·M_{a′,b^{(q)}}(v_j), and I_0 = 0 + (−1)^q·∫_Ω η_q·M_{a′,b^{(q)}}(v₀).

6. (First term → 0.) Let ε > 0, B′ := r!·C^r, I_φ := ∫ |dφ_q| dλ and δ := ε/(2(B′I_φ + 1)) > 0. By uniform convergence on Ω (Metric.tendstoUniformlyOn_iff) there is N with ‖v_j(w) − v₀(w)‖ < δ for all j ≥ N and w ∈ Ω; then |v_j^{a(0)}(w) − v₀^{a(0)}(w)| ≤ ‖v_j(w) − v₀(w)‖ < δ (PiLp.norm_apply_le). Using |M_{a′,b^{(q)}}(v_j)| ≤ B′ on Ω (Step 0), the first integrand is bounded on Ω by δB′|dφ_q|, so for j ≥ N the first integral has absolute value ≤ δB′I_φ < ε (norm_integral_le_of_norm_le, setIntegral_le_integral). Hence it tends to 0.

7. (Second term: induction hypothesis.) P(r), applied to a′, b^{(q)} and the function η_q, which is integrable on Ω by Step 4, gives ∫_Ω η_q·M_{a′,b^{(q)}}(v_j) → ∫_Ω η_q·M_{a′,b^{(q)}}(v₀); multiplication by the constant (−1)^q preserves the limit.

8. (Conclusion of the step.) By Steps 5–7, I_j → 0 + (−1)^q·∫_Ω η_q·M_{a′,b^{(q)}}(v₀) = I_0, which is (★★). Hence (★) holds for every admissible φ, and Step 2 gives P(r+1). By induction P(r) holds for every r, which is the statement. ∎

Reference implementation (compiled). The following single theorem, whose hypotheses hA and hD are the frozen types of the siblings test_density and minor_ibp_lipschitz (instantiate hA := Submission.deformation_ipl_mwc_test_density and hD := Submission.deformation_ipl_mwc_minor_ibp_lipschitz, or replace them by these names), was compiled with `lake env lean` against the frozen `import GMT.Ch06.Submission` in the exact comparator scope (namespace GMT.Ch06 and the Contract's opens). It needs no new import, is fully proved, and #print axioms gives propext, Classical.choice, Quot.sound. It follows Steps 0–8 above; the prose proof governs.

theorem _root_.TestMWC4.weak_star_ref (hA : ∀ (k : ℕ) (Ω : Set (Eucl k)) (B : ℝ) (f : ℕ → Eucl k → ℝ) (f₀ : Eucl k → ℝ), IsOpen Ω → (∀ j, AEStronglyMeasurable (f j) ((volume : Measure (Eucl k)).restrict Ω)) → AEStronglyMeasurable f₀ ((volume : Measure (Eucl k)).restrict Ω) → (∀ j, ∀ w ∈ Ω, |f j w| ≤ B) → (∀ w ∈ Ω, |f₀ w| ≤ B) → (∀ φ : Eucl k → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → Tendsto (fun j => ∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k))))) → ∀ η : Eucl k → ℝ, IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k))))) (hD : ∀ (k Q r : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (a : Fin (r + 1) → Fin Q) (b : Fin (r + 1) → Fin k) (v : Eucl k → Eucl Q) (φ : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∫ w in Ω, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) => EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k)) = -∑ q : Fin (r + 1), ∫ w in Ω, EuclideanSpace.proj (a 0) (v w) * ((-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ) (fderiv ℝ v w (EuclideanSpace.single (b (q.succAbove s)) 1)))) * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k))) : (∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q), IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω → TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k) (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))) := by
  intro k Q Ω C v v₀ hΩ hv hv₀ hconv r
  -- |det A| ≤ n! c^n for entries bounded by c (Matrix.det_le is not imported)
  have abs_det_le : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
      (∀ i j, |A i j| ≤ c) → |A.det| ≤ (Nat.factorial n : ℝ) * c ^ n := by
    intro n A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
          gcongr with σ
          have h1 : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [h1, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ n := by simp
      _ = (Nat.factorial n : ℝ) * c ^ n := by simp [Fintype.card_perm]
  -- bound and measurability of the minors of a map Lipschitz on Ω
  have minor_facts : ∀ {n : ℕ} (a : Fin n → Fin Q) (b : Fin n → Fin k) (u : Eucl k → Eucl Q),
      LipschitzOnWith C u Ω →
      (∀ w ∈ Ω, |Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))| ≤ (Nat.factorial n : ℝ) * (C : ℝ) ^ n) ∧
      Measurable (fun w => Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))) := by
    intro n a b u hu
    constructor
    · intro w hw
      apply abs_det_le
      intro t s
      have h1 : ‖fderiv ℝ u w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hu
      calc |EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1))|
          = ‖(fderiv ℝ u w (EuclideanSpace.single (b s) 1)) (a t)‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖fderiv ℝ u w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ := (fderiv ℝ u w).le_opNorm _
        _ ≤ C := by simpa using h1
    · have hdetc : Continuous fun A : Fin n → Fin n → ℝ => (Matrix.of A).det :=
        Continuous.matrix_det continuous_id
      have : ∀ t s : Fin n, Measurable fun w =>
          EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)) := fun t s =>
        (EuclideanSpace.proj (a t)).continuous.measurable.comp (measurable_fderiv_apply_const ℝ u _)
      exact hdetc.measurable.comp (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => this t s)
  induction r with
  | zero =>
    intro a b η hη
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro a b η hη
    let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w => Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
      EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))
    refine hA k Ω ((Nat.factorial (r + 1) : ℝ) * (C : ℝ) ^ (r + 1)) (fun j => M (v j)) (M v₀) hΩ
      (fun j => (minor_facts a b (v j) (hv j)).2.aestronglyMeasurable)
      (minor_facts a b v₀ hv₀).2.aestronglyMeasurable
      (fun j => (minor_facts a b (v j) (hv j)).1)
      (minor_facts a b v₀ hv₀).1 ?_ η hη
    intro φ hφ hφc hφΩ
    let M' : Fin (r + 1) → (Eucl k → Eucl Q) → Eucl k → ℝ := fun q u w =>
      Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ)
        (fderiv ℝ u w (EuclideanSpace.single (b (q.succAbove s)) 1)))
    let dφ : Fin (r + 1) → Eucl k → ℝ := fun q w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1)
    let p : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w => EuclideanSpace.proj (a 0) (u w)
    have hDu : ∀ u, LipschitzOnWith C u Ω → ∫ w in Ω, φ w * M u w ∂(volume : Measure (Eucl k)) =
        -∑ q : Fin (r + 1), ∫ w in Ω, p u w * ((-1 : ℝ) ^ (q : ℕ) * M' q u w) * dφ q w
          ∂(volume : Measure (Eucl k)) :=
      fun u hu => hD k Q r Ω C a b u φ hΩ hu hφ hφc hφΩ
    have hfun : (fun j => ∫ w in Ω, φ w * M (v j) w ∂(volume : Measure (Eucl k))) = fun j =>
        -∑ q : Fin (r + 1), ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
          ∂(volume : Measure (Eucl k)) := funext fun j => hDu _ (hv j)
    rw [hfun, hDu v₀ hv₀]
    refine (tendsto_finsetSum _ fun q _ => ?_).neg
    -- facts about the test function and the maps on K = tsupport φ
    set K := tsupport φ with hK
    have hKc : IsCompact K := hφc
    have hdφc : Continuous (dφ q) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdφ0 : ∀ w, w ∉ K → dφ q w = 0 := by
      intro w hw
      have : fderiv ℝ φ w = 0 := by
        by_contra h
        exact hw (support_fderiv_subset ℝ (Function.mem_support.2 h))
      simp [dφ, this]
    have hdφsupp : HasCompactSupport (dφ q) :=
      HasCompactSupport.of_support_subset_isCompact hKc fun w hw => by
        by_contra h; exact hw (hdφ0 w h)
    have hdφint : Integrable (dφ q) (volume : Measure (Eucl k)) :=
      hdφc.integrable_of_hasCompactSupport hdφsupp
    have hpbd : ∀ u, LipschitzOnWith C u Ω → ∃ P : ℝ, 0 ≤ P ∧ ∀ w ∈ K, |p u w| ≤ P := by
      intro u hu
      obtain ⟨P, hP⟩ := hKc.exists_bound_of_continuousOn
        (((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn hu.continuousOn).mono hφΩ)
      refine ⟨max P 0, le_max_right _ _, fun w hw => le_trans ?_ (le_max_left _ _)⟩
      have := hP w hw
      simp only [Function.comp_apply, Real.norm_eq_abs] at this
      exact this
    have hpm : ∀ u, LipschitzOnWith C u Ω →
        AEStronglyMeasurable (p u) ((volume : Measure (Eucl k)).restrict Ω) := fun u hu =>
      ((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn hu.continuousOn).aestronglyMeasurable
        hΩ.measurableSet
    have hM'b : ∀ u, LipschitzOnWith C u Ω → ∀ w ∈ Ω, |M' q u w| ≤ (Nat.factorial r : ℝ) * (C : ℝ) ^ r :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).1
    have hM'm : ∀ u, LipschitzOnWith C u Ω → Measurable (M' q u) :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).2
    set B' : ℝ := (Nat.factorial r : ℝ) * (C : ℝ) ^ r with hB'
    have hB'0 : 0 ≤ B' := by positivity
    -- generic integrability: anything a.e.-measurable on Ω and bounded by c * |dφ q| on Ω
    have hint : ∀ (F : Eucl k → ℝ) (c : ℝ), AEStronglyMeasurable F ((volume : Measure (Eucl k)).restrict Ω) →
        (∀ w ∈ Ω, |F w| ≤ c * |dφ q w|) → IntegrableOn F Ω (volume : Measure (Eucl k)) := by
      intro F c hFm hFb
      refine Integrable.mono' ((hdφint.abs.const_mul c).integrableOn) hFm ?_
      exact (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
        simpa [Real.norm_eq_abs] using hFb w hw)
    -- η_q and the induction hypothesis
    let ηq : Eucl k → ℝ := fun w => p v₀ w * dφ q w
    obtain ⟨P0, hP00, hP0⟩ := hpbd v₀ hv₀
    have hηq : IntegrableOn ηq Ω (volume : Measure (Eucl k)) := by
      refine hint ηq P0 ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict) fun w hw => ?_
      by_cases hwK : w ∈ K
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hP0 w hwK) (abs_nonneg _)
      · simp [ηq, hdφ0 w hwK]
    have hih := ih (fun t => a t.succ) (fun s => b (q.succAbove s)) ηq hηq
    -- integrability of the pieces
    have hI1 : ∀ j, IntegrableOn (fun w => (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w)
        Ω (volume : Measure (Eucl k)) := by
      intro j
      obtain ⟨Pj, hPj0, hPj⟩ := hpbd (v j) (hv j)
      refine hint _ ((Pj + P0) * B') ((((hpm _ (hv j)).sub (hpm _ hv₀)).mul
        ((hM'm _ (hv j)).aestronglyMeasurable.const_mul _)).mul hdφc.aestronglyMeasurable.restrict) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        gcongr
        · exact (abs_sub _ _).trans (add_le_add (hPj w hwK) (hP0 w hwK))
        · exact hM'b _ (hv j) w hw
      · simp [hdφ0 w hwK]
    have hI2 : ∀ u, LipschitzOnWith C u Ω → IntegrableOn (fun w => ηq w * M' q u w) Ω (volume : Measure (Eucl k)) := by
      intro u hu
      refine hint _ (P0 * B') ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict
        |>.mul (hM'm _ hu).aestronglyMeasurable) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · simp only [ηq, abs_mul]
        calc |p v₀ w| * |dφ q w| * |M' q u w| ≤ P0 * |dφ q w| * B' := by
              gcongr
              · exact hP0 w hwK
              · exact hM'b _ hu w hw
          _ = P0 * B' * |dφ q w| := by ring
      · simp [ηq, hdφ0 w hwK]
    -- algebraic splitting
    have hsplit : ∀ j, ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k)) =
        (∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k))) +
          (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q (v j) w ∂(volume : Measure (Eucl k)) := by
      intro j
      rw [← integral_const_mul, ← integral_add (hI1 j) ((hI2 _ (hv j)).const_mul _)]
      congr 1; funext w; simp only [ηq]; ring
    have hlim : ∫ w in Ω, p v₀ w * ((-1 : ℝ) ^ (q : ℕ) * M' q v₀ w) * dφ q w ∂(volume : Measure (Eucl k)) =
        0 + (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q v₀ w ∂(volume : Measure (Eucl k)) := by
      rw [zero_add, ← integral_const_mul]
      congr 1; funext w; simp only [ηq]; ring
    -- first piece tends to zero by uniform convergence
    have h1 : Tendsto (fun j => ∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
        ∂(volume : Measure (Eucl k))) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set I := ∫ w, |dφ q w| ∂(volume : Measure (Eucl k)) with hI
      have hI0 : 0 ≤ I := integral_nonneg fun w => abs_nonneg _
      set δ := ε / (2 * (B' * I + 1)) with hδ
      have hδ0 : 0 < δ := by positivity
      obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv δ hδ0)
      refine ⟨N, fun j hj => ?_⟩
      rw [dist_zero_right]
      have hbound : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict Ω),
          ‖(p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w‖ ≤ δ * B' * |dφ q w| := by
        refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
        have e1 : |p (v j) w - p v₀ w| ≤ δ := by
          have h' := (hN j hj w hw).le
          rw [dist_comm, dist_eq_norm] at h'
          calc |p (v j) w - p v₀ w| = |EuclideanSpace.proj (a 0) (v j w - v₀ w)| := by simp [p]
            _ = ‖(v j w - v₀ w) (a 0)‖ := by simp [Real.norm_eq_abs]
            _ ≤ ‖v j w - v₀ w‖ := PiLp.norm_apply_le _ _
            _ ≤ δ := h'
        have e2 := hM'b _ (hv j) w hw
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        gcongr
      calc ‖∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k))‖
          ≤ ∫ w in Ω, δ * B' * |dφ q w| ∂(volume : Measure (Eucl k)) :=
            norm_integral_le_of_norm_le ((hdφint.abs.const_mul _).integrableOn) hbound
        _ ≤ ∫ w, δ * B' * |dφ q w| ∂(volume : Measure (Eucl k)) :=
            setIntegral_le_integral (hdφint.abs.const_mul _) (ae_of_all _ fun w => by positivity)
        _ = δ * (B' * I) := by rw [integral_const_mul, hI]; ring
        _ < ε := by
            rw [hδ]
            have : 0 < B' * I + 1 := by positivity
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
    rw [hlim]
    exact (h1.add (hih.const_mul _)).congr fun j => (hsplit j).symm

## Key steps

1. Rademacher-type bound ‖Du‖ ≤ C on Ω gives |M_{a,b}(u)| ≤ r!C^r on Ω; minors are Borel measurable.
2. Induction on r; r = 0 is trivial (empty determinant 1).
3. Step r → r+1: by test_density (bound (r+1)!C^{r+1}) it suffices to test against φ ∈ C¹_c(Ω).
4. minor_ibp_lipschitz rewrites ∫_Ω φM_{a,b}(u) = −Σ_q ∫_Ω u^{a(0)}(−1)^q M_{a′,b^{(q)}}(u)∂_{b(q)}φ for u = v_j, v₀.
5. Split each term: uniform convergence handles (v_j^{a(0)} − v₀^{a(0)}); the induction hypothesis for the (r×r) minors tested against η_q = v₀^{a(0)}∂_{b(q)}φ ∈ L¹(Ω) handles the rest.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886 = git HEAD; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: this node (depth 3, status decomposing, attempt 1, depends_on root.compactness_mass_bounds-a1.covector_expansion-a1) and the parent's decomposition-v3.json (format of reused children)`
- `python3 -I regex over dag.json titles/statements/lean statements: mollif|Piola|dense in|density of|C_c|integration by parts|weak-*|weak star|cofactor|convolution|minors|smooth approximation|ContDiffBump`
- `python3 -I over dag.json: status, candidate_commit, title/statement/lean_statement equality with the handoff for constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close, cmb_covector_eq_sum_coord_smul_wedge (all accepted, equal); lean_name collisions for deformation_ipl_mwc_* (none)`
- `grep -rn deformation_ipl_mwc over GMT/, the snapshot project, simongmt/Poincare and the snapshot Mathlib (no match)`
- `rg -n 'abbrev Covector|SimonMultiIndex|def wedgeCovectors|theorem wedgeCovectors_apply_det|def euclideanCovectorCoordinate' simongmt/Poincare/SimonGMT`
- `rg -n 'theorem norm_fderiv_le_of_lipschitzOn|LipschitzOnWith.extend_real|extend_finite_dimension|lipschitzExtensionConstant' snapshot Mathlib`
- `rg -n '^theorem' Mathlib/Analysis/Calculus/Rademacher.lean and Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; sed ContinuousMapDense.lean 135-240, LineDeriv/IntegrationByParts.lean 215-245, ContDiff/Convolution.lean 50-100 and 415-435, Matrix/AbsoluteValue.lean det_le, ContDiff/RCLike.lean lipschitzWith_of_hasCompactSupport, FDeriv/Mul.lean finsetProd`
- `git log --all -G'^import' -- GMT/Ch06/Submission.lean; git show cdfc95dc (leaf gate rejects added imports); git show 2219dd32 (accepted ae-mollifier proof uses IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub)`
- `lake env lean /tmp/mwc_decomp/build/Avail.lean, build_v2/Avail2.lean, build_v2/Avail3.lean, build_v2/Small2.lean (#check availability under import GMT.Ch06.Submission)`
- `python3 -I /tmp/mwc_decomp/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode) and lake env lean on the eleven /tmp/mwc_decomp/build_final/*_challenge.lean (all exit 0, sorry warnings only)`
- `lake env lean /tmp/mwc_decomp/build/Assembly.lean, build_v2/F_from_E.lean, build_v2/E_from_AD.lean, build_v2/RefImpl.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `grep 'Your solution is okay' in comparator-v1.log and isolated-comparator-result.json (passed: true) of the four reused nodes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/speculative-prompt-v4.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-close-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/mwc_decomp/build_final`
- `/tmp/mwc_decomp/build/Assembly.lean`
- `/tmp/mwc_decomp/build_v2/F_from_E.lean`
- `/tmp/mwc_decomp/build_v2/E_from_AD.lean`
- `/tmp/mwc_decomp/build_v2/RefImpl.lean`
- `/tmp/mwc_decomp/build/Avail.lean`
- `/tmp/mwc_decomp/build_v2/Avail2.lean`
- `/tmp/mwc_decomp/build_v2/Avail3.lean`

Pinned revisions are confirmed (HEAD = project_commit), and Contract = Submission = the snapshot Contract byte-for-byte.
No existing proof: neither Mathlib, SimonGMT nor any accepted DAG node proves weak continuity of Jacobian minors, the Piola identity or L¹-density by smooth functions. (The r = 1 analogue slicing_im_ll_gradient_weak_star and the density node slicing_im_ll_gws_smooth_dense are not accepted.) Hence seven new children; their names deformation_ipl_mwc_* collide with nothing.
Reused, with byte-identical types and comparator-passed: cmb_covector_eq_sum_coord_smul_wedge, constancy_mdc_smooth_approx_identity_ae_tendsto, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_sa_mollify_lipschitz_close.
Import closure: the leaf gate forbids new imports (commit cdfc95dc).
- Available in the frozen closure: SimonGMT wedgeCovectors_apply_det; Mathlib norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, extend_finite_dimension, LipschitzOnWith.ae_differentiableWithinAt_of_mem, LipschitzWith.integral_lineDeriv_mul_eq, HasCompactSupport.contDiff_convolution_left/right, ContDiffAt.isSymmSndFDerivAt, HasFDerivAt.finsetProd, Matrix.det_succ_row_zero, Matrix.det_apply, measurable_fderiv(_apply_const), tendsto_integral_filter_of_dominated_convergence, IsCompact.exists_cthickening_subset_open, ContDiff.lipschitzWith_of_hasCompactSupport.
- Not available: ContDiffBump.normed and BumpFunction/Convolution, ContinuousMapDense, LineDeriv/IntegrationByParts, Matrix.det_le. The children replace them by the reused siblings or by short arguments.
Lean checks:
- All eleven statements validate and elaborate in the exact comparator scope.
- Three links compile with only propext, Classical.choice and Quot.sound: parent ⇐ coeff_minor_continuity + covector expansion; coeff_minor_continuity ⇐ minor_weak_star; minor_weak_star ⇐ test_density + minor_ibp_lipschitz.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
