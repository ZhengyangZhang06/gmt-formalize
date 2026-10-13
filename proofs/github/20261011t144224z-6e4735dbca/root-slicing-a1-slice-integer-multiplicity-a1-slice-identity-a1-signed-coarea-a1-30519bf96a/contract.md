<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.signed_coarea-a1 -->

## Theorem `Submission.slicing_im_si_signed_coarea`

Let P ∈ ℕ, let μ and ν be measures on ℝ^P, and let M ⊆ ℝ^P. Let f : ℝ^P → ℝ, G : ℝ^P → ℝ^P and g : ℝ^P → ℝ be Borel, with x ↦ |G(x)|·g(x) integrable for μ⌞M. Assume the co-area identity (CA): for every Borel h : ℝ^P → [0, ∞], t ↦ ∫_{M∩f⁻¹{t}} h dν is Lebesgue-a.e.-measurable and ∫_ℝ ∫_{M∩f⁻¹{t}} h dν dt = ∫_M |G| h dμ (integrals against restricted measures). Let φ(t) := ∫_{M∩f⁻¹{t}} g dν be the Bochner integral against ν⌞(M ∩ f⁻¹{t}), which is 0 if g is not integrable there. Then φ is Lebesgue-integrable on ℝ, and for all a, b ∈ ℝ, ∫_{M∩f⁻¹((a,b))} |G| g dμ = ∫_{(a,b)} φ(t) dt.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.signed_coarea-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2519

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.slicing_im_si_signed_coarea`

```lean
∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (g : Eucl P → ℝ), Measurable f → Measurable G → Measurable g → Integrable (fun x => ‖G x‖ * g x) (μ.restrict M) → (∀ h : Eucl P → ℝ≥0∞, Measurable h → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * h x ∂μ) → Integrable (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∀ a b : ℝ, ∫ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ * g x ∂μ = ∫ t in Ioo a b, (∫ x in M ∩ f ⁻¹' {t}, g x ∂ν)
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.signed_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 4, i.e. Simon Ch. 6, Remark 4.2: replace g in the co-area formula of Lemma 4.1 by g times the characteristic function of a band in f to get ∫_{M∩{f<t}} |∇^M f| g dHⁿ = ∫_{−∞}^{t} ∫_{M_s} g dH^{n−1} ds. Here it is written out for a signed L¹ density, with arbitrary measures μ, ν and an open band (a, b). The parent takes μ = H^{m+1}, ν = H^m, and its sibling slicing_im_coarea supplies (CA).

Notation. ∫_S denotes integration against the restricted measure (defined for every S ⊆ ℝ^P). (CA) is the hypothesis: for every Borel h : ℝ^P → [0, ∞], t ↦ ∫_{M∩f⁻¹{t}} h dν is L¹-a.e.-measurable and ∫_ℝ ∫_{M∩f⁻¹{t}} h dν dt = ∫_M |G| h dμ. Put g⁺ := ofReal(g) and g⁻ := ofReal(−g); both are [0, ∞]-valued and Borel. For real x, ofReal(x) + ofReal(−x) = |x|. Put φ₊(t) := ∫_{M∩f⁻¹{t}} g⁺ dν and φ₋(t) := ∫_{M∩f⁻¹{t}} g⁻ dν, both in [0, ∞]. φ(t) := ∫_{M∩f⁻¹{t}} g dν is the Bochner integral, which is 0 when g is not integrable there.

1. (Products.) Since |G(x)| ≥ 0, ofReal(|G(x)|·g(x)) = |G(x)|·g⁺(x) and ofReal(−|G(x)|·g(x)) = |G(x)|·g⁻(x), with |G(x)| read as an extended nonnegative number.
2. (Finiteness.) By (CA) with h = g^±, φ_± is L¹-a.e.-measurable and ∫_ℝ φ_± dt = ∫_M |G|·g^± dμ = ∫_M ofReal(±|G|g) dμ. This is ≤ ∫_M ||G|g| dμ, which is finite because |G|g is μ⌞M-integrable. Hence φ_±(t) < ∞ for L¹-a.e. t.
3. (Slice integrability.) Let t satisfy φ₊(t) < ∞ and φ₋(t) < ∞. Then ∫_{M∩f⁻¹{t}} |g| dν = φ₊(t) + φ₋(t) < ∞, because |g| = g⁺ + g⁻ and the lower integral is additive (g⁺ is measurable). Since g is Borel, g is integrable for ν⌞(M∩f⁻¹{t}). Splitting into positive and negative parts gives φ(t) = φ₊(t).toReal − φ₋(t).toReal.
4. (φ is integrable.) Put ψ(t) := φ₊(t).toReal − φ₋(t).toReal. Each φ_±.toReal is L¹-integrable: φ_± is a.e.-measurable with finite integral (step 2). So ψ is integrable. By step 3, φ = ψ L¹-a.e., so φ is integrable. This is the first conclusion.
5. (Band identity for a nonnegative Borel h.) Fix a, b ∈ ℝ and let E := f⁻¹((a, b)), a Borel set. Let h : ℝ^P → [0, ∞] be Borel and apply (CA) to 1_E·h.
 (a) Fix t. The set {x : f(x) ≠ t} is Borel and ν({f ≠ t} ∩ M ∩ f⁻¹{t}) = ν(∅) = 0. So f(x) = t for ν⌞(M∩f⁻¹{t})-a.e. x. For such x, 1_E(x) = 1_{(a,b)}(t). Hence ∫_{M∩f⁻¹{t}} 1_E h dν = 1_{(a,b)}(t)·∫_{M∩f⁻¹{t}} h dν.
 (b) So the left side of (CA) is ∫_ℝ 1_{(a,b)}(t)·∫_{M∩f⁻¹{t}} h dν dt = ∫_{(a,b)} ∫_{M∩f⁻¹{t}} h dν dt.
 (c) For the right side, |G|·1_E h = 1_E·(|G|h). The restriction of μ⌞M to the Borel set E is μ⌞(E ∩ M), so ∫_M |G| 1_E h dμ = ∫_{M∩E} |G| h dμ.
 Hence ∫_{M∩E} |G| h dμ = ∫_{(a,b)} ∫_{M∩f⁻¹{t}} h dν dt.
6. (Left side of the claim.) |G|g is μ⌞(M∩E)-integrable, being the restriction of a μ⌞M-integrable function. So, splitting into positive and negative parts and using step 1:
 ∫_{M∩E} |G| g dμ = (∫_{M∩E} |G| g⁺ dμ).toReal − (∫_{M∩E} |G| g⁻ dμ).toReal.
 By step 5 with h = g⁺ and h = g⁻, this equals (∫_{(a,b)} φ₊ dt).toReal − (∫_{(a,b)} φ₋ dt).toReal.
7. (Right side of the claim.) Since φ = ψ a.e., ∫_{(a,b)} φ = ∫_{(a,b)} ψ = ∫_{(a,b)} φ₊.toReal − ∫_{(a,b)} φ₋.toReal, both terms being integrable. Each φ_± is a.e.-measurable and a.e. finite on (a, b), so ∫_{(a,b)} φ_±.toReal = (∫_{(a,b)} φ_±).toReal.
8. Steps 6 and 7 give ∫_{M∩f⁻¹((a,b))} |G| g dμ = ∫_{(a,b)} φ(t) dt for all a, b. If a ≥ b, both sides are integrals over empty sets and equal 0. ∎

Formalization notes (a complete Lean proof of exactly this statement was checked in a scratch build of the frozen commit d8d46c9: written as `theorem Submission.<lean_name>` inside `namespace GMT.Ch06` of a file importing GMT.Ch06.Submission, with the comparator-form restatement `theorem _root_.X : (<lean_statement>) := by exact Submission.<lean_name>` also checked; axioms propext, Classical.choice, Quot.sound; the verified proof is appended at the end):
- Products: `ENNReal.ofReal_mul (norm_nonneg _)` and `ofReal_norm` (for the negative part, first `← mul_neg`).
- Finiteness: `hGg.lintegral_lt_top` and `hGg.neg.lintegral_lt_top`, then `ae_lt_top'`.
- Slice integrability: `Real.enorm_eq_ofReal_abs`, `ENNReal.ofReal_of_nonpos`, `lintegral_add_left`, `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`.
- φ integrable: `integrable_toReal_of_lintegral_ne_top`, `Integrable.sub`, `Integrable.congr`.
- Step 5(a): state `have hmeas : MeasurableSet {a | ¬f a = t}`. Rewriting with `Measure.restrict_apply (hf (measurableSet_singleton t)).compl` fails because the pattern does not match syntactically. Then `lintegral_congr_ae` (rewrite the zero case with `← lintegral_zero`).
- Step 5(b),(c): `lintegral_indicator measurableSet_Ioo`, `lintegral_indicator hE`, `Measure.restrict_restrict hE`, `inter_comm`.
- Steps 6–7: `hGg.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)`, `simp_rw [← hprod, ← hprodn]`, `integral_congr_ae (ae_restrict_of_ae hae)`, `integral_sub` with `Integrable.restrict`, `integral_toReal` with `AEMeasurable.restrict` and `ae_restrict_of_ae`.

Verified Lean proof (scratch build of d8d46c9; place it in GMT/Ch06/Submission.lean after the contract's closing `end` of the noncomputable section and before `theorem main_theorem`, inside `namespace GMT.Ch06`; it uses only the frozen imports):
```lean
theorem Submission.slicing_im_si_signed_coarea :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (g : Eucl P → ℝ), Measurable f → Measurable G → Measurable g → Integrable (fun x => ‖G x‖ * g x) (μ.restrict M) → (∀ h : Eucl P → ℝ≥0∞, Measurable h → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * h x ∂μ) → Integrable (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∀ a b : ℝ, ∫ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ * g x ∂μ = ∫ t in Ioo a b, (∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) := by
  intro P μ ν M f G g hf hG hg hGg CA
  have hgp : Measurable (fun x => ENNReal.ofReal (g x)) := ENNReal.measurable_ofReal.comp hg
  have hgn : Measurable (fun x => ENNReal.ofReal (-g x)) := ENNReal.measurable_ofReal.comp hg.neg
  obtain ⟨hφpm, hφp⟩ := CA _ hgp
  obtain ⟨hφnm, hφn⟩ := CA _ hgn
  have hprod : ∀ x, ‖G x‖ₑ * ENNReal.ofReal (g x) = ENNReal.ofReal (‖G x‖ * g x) := by
    intro x; rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  have hprodn : ∀ x, ‖G x‖ₑ * ENNReal.ofReal (-g x) = ENNReal.ofReal (-(‖G x‖ * g x)) := by
    intro x; rw [← mul_neg, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  have hfinp : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (g x) ∂ν) ∂(volume : Measure ℝ) ≠ ∞ := by
    rw [hφp]; simp_rw [hprod]; exact hGg.lintegral_lt_top.ne
  have hfinn : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (-g x) ∂ν) ∂(volume : Measure ℝ) ≠ ∞ := by
    rw [hφn]; simp_rw [hprodn]; exact hGg.neg.lintegral_lt_top.ne
  have hltp := ae_lt_top' hφpm hfinp
  have hltn := ae_lt_top' hφnm hfinn
  -- the slice integral equals the difference of the parts for a.e. `t`
  have hae : (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) =ᵐ[volume]
      fun t => (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (g x) ∂ν).toReal -
        (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (-g x) ∂ν).toReal := by
    filter_upwards [hltp, hltn] with t htp htn
    have hint : Integrable g (ν.restrict (M ∩ f ⁻¹' {t})) := by
      refine ⟨hg.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      have : (fun x => ‖g x‖ₑ) = fun x => ENNReal.ofReal (g x) + ENNReal.ofReal (-g x) := by
        funext x
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (g x) with h | h
        · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -g x ≤ 0), add_zero]
        · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
      rw [this, lintegral_add_left hgp]
      exact ENNReal.add_lt_top.2 ⟨htp, htn⟩
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  have hψ : Integrable (fun t => (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (g x) ∂ν).toReal -
        (∫⁻ x in M ∩ f ⁻¹' {t}, ENNReal.ofReal (-g x) ∂ν).toReal) (volume : Measure ℝ) :=
    (integrable_toReal_of_lintegral_ne_top hφpm hfinp).sub
      (integrable_toReal_of_lintegral_ne_top hφnm hfinn)
  refine ⟨hψ.congr hae.symm, fun a b => ?_⟩
  have hE : MeasurableSet (f ⁻¹' Ioo a b) := hf measurableSet_Ioo
  -- interval identity for a nonnegative part
  have part : ∀ h : Eucl P → ℝ≥0∞, Measurable h →
      ∫⁻ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ₑ * h x ∂μ = ∫⁻ t in Ioo a b, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) := by
    intro h hh
    obtain ⟨-, hCA⟩ := CA ((f ⁻¹' Ioo a b).indicator h) (hh.indicator hE)
    have hL : ∀ t, ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' Ioo a b).indicator h x ∂ν =
        (Ioo a b).indicator (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) t := by
      intro t
      have hft : ∀ᵐ x ∂(ν.restrict (M ∩ f ⁻¹' {t})), f x = t := by
        have hmeas : MeasurableSet {a | ¬f a = t} := (hf (measurableSet_singleton t)).compl
        rw [ae_iff, Measure.restrict_apply hmeas]
        convert measure_empty (μ := ν)
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false, not_and]
        intro h1 _ h2
        exact h1 h2
      by_cases ht : t ∈ Ioo a b
      · rw [indicator_of_mem ht]
        apply lintegral_congr_ae
        filter_upwards [hft] with x hx
        rw [indicator_of_mem (show x ∈ f ⁻¹' Ioo a b by simp [mem_preimage, hx, ht])]
      · rw [indicator_of_notMem ht]
        rw [← lintegral_zero]
        apply lintegral_congr_ae
        filter_upwards [hft] with x hx
        rw [indicator_of_notMem (show x ∉ f ⁻¹' Ioo a b by simp [mem_preimage, hx, ht])]
    simp_rw [hL] at hCA
    rw [lintegral_indicator measurableSet_Ioo] at hCA
    rw [hCA]
    have : ∀ x, ‖G x‖ₑ * (f ⁻¹' Ioo a b).indicator h x = (f ⁻¹' Ioo a b).indicator (fun x => ‖G x‖ₑ * h x) x := by
      intro x
      by_cases hx : x ∈ f ⁻¹' Ioo a b
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    simp_rw [this]
    rw [lintegral_indicator hE, Measure.restrict_restrict hE, inter_comm]
  have hpp := part _ hgp
  have hnn := part _ hgn
  have hGgE : Integrable (fun x => ‖G x‖ * g x) (μ.restrict (M ∩ f ⁻¹' Ioo a b)) :=
    hGg.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGgE]
  simp_rw [← hprod, ← hprodn]
  rw [hpp, hnn]
  rw [integral_congr_ae (ae_restrict_of_ae hae)]
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hφpm hfinp).restrict
    (integrable_toReal_of_lintegral_ne_top hφnm hfinn).restrict]
  rw [integral_toReal hφpm.restrict (ae_restrict_of_ae hltp),
    integral_toReal hφnm.restrict (ae_restrict_of_ae hltn)]
```

## Key steps

1. split g = g⁺ − g⁻ with g^± = ofReal(±g); |G|·g^± = ofReal(±|G|g)
2. (CA) for g^±: φ_± a.e.-measurable with ∫φ_± = ∫_M |G|g^± < ∞, so φ_± < ∞ a.e.
3. where φ_± < ∞, g is slice-integrable and φ = φ₊.toReal − φ₋.toReal; hence φ is L¹-integrable
4. (CA) for 1_{f⁻¹(a,b)} g^±: on the slice f = t the indicator is 1_{(a,b)}(t), giving ∫_{M∩f⁻¹(a,b)} |G|g^± dμ = ∫_{(a,b)} φ_± dt
5. subtracting the finite parts gives ∫_{M∩f⁻¹(a,b)} |G| g dμ = ∫_{(a,b)} φ dt

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical); read Contract.lean: IsRectifiableTriple, tauAction, IsMeasureRepresentation, IsRestriction, IsSlice`
- `grep -n 'def testFormOnSubmodule|def exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|boundary_apply' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents}.lean`
- `python3 scan of dag.json: decomposition of root.slicing-a1.slice_integer_multiplicity-a1 (sibling types slicing_im_coarea, slicing_im_lipschitz_leibniz, statuses decomposing); accepted nodes matching 'f ⁻¹' {t}|HasDerivAt (fun s|max 0|𝓝[>] 0|toMeasurable|simpleNVector|innerSL|alternatizeUncurryFin|IsSlice' -> reusable slicing_mb_pointwise_cutoff_tendsto (012eb78d) and fiw_ims_tt_unit_bound (27af9b19)`
- `git show 012eb78d57e01b1e54de6b8f0e5cf786950b91c0:GMT/Ch06/Submission.lean; git show 27af9b191b732eae73e3d693d8903e52f89962ce:GMT/Ch06/Submission.lean (accepted proofs, isolated-comparator-result.json passed)`
- `grep -rn 'theorem ae_tendsto_average|ae_hasDerivAt_integral|tendsto_Icc_vitaliFamily_left' mathlib/Mathlib; read MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `lake env lean Avail*.lean: availability under `import GMT.Ch06.Submission` of LocallyIntegrable.ae_hasDerivAt_integral (unknown constant), VitaliFamily.ae_tendsto_average, Real.tendsto_Icc_vitaliFamily_left, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_congr_set, Measure.le_restrict_apply, lintegral_eq_zero_iff', integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integrable_toReal_of_lintegral_ne_top, integral_toReal, ae_lt_top', ContinuousAlternatingMap.norm_alternatizeUncurryFin_le, isBoundedBilinearMap_smulRight, Integrable.bdd_mul`
- `lake env lean /tmp/sid_split_scratch/Stmts.lean (eight child types in the exact comparator scope; #print checked)`
- `lake env lean /tmp/sid_split_scratch/Assembly.lean (parent type from child and sibling types; #print axioms)`
- `lake env lean /tmp/sid_split_scratch/Full.lean (#print axioms ParentFromUncles: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/sid_split_scratch/E2Echildren.lean (embedded child proofs verbatim + comparator-form exact; no errors, no warnings)`
- `rg 'slicing_im_si_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project (no match); grep -rn 'slicing_im_si_' simongmt/Poincare (no match); dag.json lean_name scan for slicing_im_si_* (no match among 464 nodes)`
- `sed -n 1150,1345p book/chapter-06.txt (Simon Ch. 6, 4.1, Remark 4.2, 4.4, Lemma 4.5 and its proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/OneDim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/isolated-comparator-result.json`
- `/tmp/sid_split_scratch/Stmts.lean`
- `/tmp/sid_split_scratch/Assembly.lean`
- `/tmp/sid_split_scratch/Full.lean`
- `/tmp/sid_split_scratch/E2Echildren.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission is byte-identical, so child types may use only contract, SimonGMT and Mathlib names in the comparator scope. SimonGMT provides TestFormOn (smooth, compact support, tsupport ⊆ U), exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset and GeometricCurrentOn.boundary_apply. Neither SimonGMT nor Mathlib has co-area, slicing or cut-off tangential-gradient results; the six new children isolate exactly those steps of the supplied proof (Simon Ch. 6, Remark 4.2 and proof of 4.5(2)). Mathlib's interval Lebesgue differentiation lemma is not importable from Submission, but VitaliFamily.ae_tendsto_average and Real.tendsto_Icc_vitaliFamily_left are, so the one-sided version is proved from them. Two accepted DAG declarations are reused with byte-identical types: slicing_mb_pointwise_cutoff_tendsto (Step 9) and fiw_ims_tt_unit_bound (Fact U). All eight child types elaborate in the exact comparator scope. In scratch Lean the six new children are fully proved, and the parent's frozen type follows from the children plus the two declared sibling types slicing_im_coarea and slicing_im_lipschitz_leibniz, using only propext, Classical.choice and Quot.sound. No new name collides with the snapshot, SimonGMT or the 464 DAG nodes. These checks do not cover the proofs of the two sibling dependencies, which remain their own nodes.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
