import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter02.AreaBranches
import Poincare.SimonGMT.Chapter01.DensityComparison

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

/-- Exhaustion of an open `U ⊆ ℝ^P` by open sets `W i ⊂⊂ U` such that every compact `K ⊆ U`
lies in some `W i`: `W i = {x : |x| < i, (i + 1)⁻¹ < infEDist x (ℝ^P ∖ U)}`. -/
theorem Submission.cmb_exists_compactly_contained_exhaustion :
    ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ W : ℕ → Set (Eucl P),
      (∀ i, CompactlyContainedOpen (W i) U) ∧
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ i, K ⊆ W i := by
  intro P U hU
  -- `d x = infEDist x Uᶜ` is continuous and positive exactly on `U`.
  have hd : Continuous fun x : Eucl P => infEDist x Uᶜ := continuous_infEDist
  have hpos : ∀ x ∈ U, 0 < infEDist x Uᶜ := fun x hx => by
    rw [infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq, notMem_compl_iff]
    exact hx
  refine ⟨fun i => {x | ‖x‖ < i} ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}, fun i => ?_,
    fun K hK hKU => ?_⟩
  · -- `closure (W i) ⊆ closedBall 0 i ∩ {(i + 1)⁻¹ ≤ d}`, a compact subset of `U`.
    have hcl : closure ({x : Eucl P | ‖x‖ < i} ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}) ⊆
        closedBall 0 i ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ} :=
      closure_minimal (fun x hx => ⟨mem_closedBall_zero_iff.2 hx.1.le,
        show ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ from hx.2.le⟩)
        (isClosed_closedBall.inter (isClosed_le continuous_const hd))
    refine ⟨(isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd),
      (isCompact_closedBall 0 _).of_isClosed_subset isClosed_closure (hcl.trans inter_subset_left),
      fun x hx => ?_⟩
    by_contra hxU
    have h : ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ := (hcl hx).2
    rw [infEDist_zero_of_mem hxU, nonpos_iff_eq_zero, ENNReal.inv_eq_zero] at h
    exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top i, ENNReal.one_ne_top⟩ h
  · -- A compact `K ⊆ U` is bounded and `d` has a positive minimum on it.
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, empty_subset _⟩
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
    obtain ⟨i₁, hi₁⟩ := exists_nat_gt R
    obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hd.continuousOn
    obtain ⟨i₂, hi₂⟩ := ENNReal.exists_inv_nat_lt (hpos x₀ (hKU hx₀K)).ne'
    refine ⟨max i₁ i₂, fun x hx => ⟨?_, ?_⟩⟩
    · show ‖x‖ < ((max i₁ i₂ : ℕ) : ℝ)
      calc ‖x‖ ≤ R := hR x hx
        _ < i₁ := hi₁
        _ ≤ (max i₁ i₂ : ℕ) := Nat.cast_le.2 (le_max_left _ _)
    · show (((max i₁ i₂ : ℕ) : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ
      calc (((max i₁ i₂ : ℕ) : ℝ≥0∞) + 1)⁻¹ ≤ (i₂ : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.2 (by exact_mod_cast (le_max_right i₁ i₂).trans (Nat.le_succ _))
        _ < infEDist x₀ Uᶜ := hi₂
        _ ≤ infEDist x Uᶜ := isMinOn_iff.1 hx₀ x hx
/-- Mass estimate: if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ C` everywhere
(Euclidean covector norm), then `|T(ω)| ≤ B · C`. -/
theorem Submission.cmb_abs_apply_le_of_massOn_le :
    ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B C : ℝ),
      0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      |T ω| ≤ B * C := by
  intro P n U W T ω B C hB hM hW hC
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- `C ≥ 0`, by evaluating the pointwise bound at `0`.
  have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
  -- For every `c > C`, both `±c⁻¹ ω` are mass-admissible for `W`, hence `|T ω| ≤ B c`.
  have key : ∀ c, C < c → |T ω| ≤ B * c := by
    intro c hc
    have hc0 : 0 < c := hC0.trans_lt hc
    have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * T ω ≤ B := by
      intro s hs
      have hadm : s • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hW, fun x => ?_⟩
        change covectorEuclideanNorm (s • (ω : DifferentialForm (Eucl P) n) x) ≤ 1
        rw [hsmul, hs, inv_mul_le_iff₀ hc0, mul_one]
        exact (hC x).trans hc.le
      have hle := (T.le_massOn hadm).trans hM
      rw [ENNReal.ofReal_le_ofReal_iff hB] at hle
      have hlin : T (s • ω) = s * T ω := by
        rw [map_smul, smul_eq_mul]
      rwa [hlin] at hle
    have h1 := hbound c⁻¹ (abs_of_pos (inv_pos.mpr hc0))
    have h2 := hbound (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc0)])
    have e1 : c * (c⁻¹ * T ω) = T ω := by field_simp
    have e2 : c * (-c⁻¹ * T ω) = -T ω := by field_simp
    rw [abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left h2 hc0.le
      rw [e2] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h1 hc0.le
      rw [e1] at this
      linarith
  -- Let `c ↓ C`: take `c = C + ε / (B + 1)`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < ε / (B + 1) := div_pos hε hB1
  have hBδ : B * (ε / (B + 1)) ≤ ε := by
    calc B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := by field_simp
  have := key (C + ε / (B + 1)) (by linarith)
  calc |T ω| ≤ B * (C + ε / (B + 1)) := this
    _ = B * C + B * (ε / (B + 1)) := by ring
    _ ≤ B * C + ε := by linarith
/-- Coordinate expansion of an `n`-covector on `ℝ^P` in the wedge basis:
`α = ∑_β α(e_{β(0)}, …, e_{β(n-1)}) dx^β` over the increasing multi-indices `β`. -/
theorem Submission.cmb_covector_eq_sum_coord_smul_wedge :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n), α = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) := by
  intro P n α
  classical
  -- `e v = (e_{v 0}, …, e_{v (n - 1)})` for a tuple `v` of coordinate indices.
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1
  set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
    euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) with hR
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P,
      wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · -- the matrix `[δ_{β i, β j}]` is the identity
      subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · -- some `β i` is not among the `γ j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
        by_contra! h
        apply hβγ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range β ⊆ Set.range γ := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range γ)
        rw [Set.ncard_range_of_injective γ.injective, Set.ncard_range_of_injective β.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [e, PiLp.single_apply, hi j]
  -- `R` agrees with `α` on increasing tuples of basis vectors.
  have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
    intro γ
    rw [hR, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  -- `R` agrees with `α` on injective tuples: sort them and use `map_perm`.
  have h2 : ∀ v : Fin n → Fin P, Function.Injective v → R (e v) = α (e v) := by
    intro v hv
    have hsm : StrictMono (v ∘ Tuple.sort v) :=
      (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
    have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
    have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
    rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
      ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
      AlternatingMap.map_perm] at hγ
    exact smul_left_cancel _ hγ
  -- Conclude by extensionality on the standard basis.
  symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  exact h2 v hv
/-- Simon Ch. 1, Theorem 3.3 (with `A₁ = A`, `A₂ = V`): if `Θ*ⁿ(ν, x) ≥ t` on `A ⊆ V`, `V` open,
then `t Hⁿ(A) ≤ ν(V)`.  The isodiametric inequality (coordinate Steiner symmetrization)
shows that a closed ball of radius `r` has `μHE[n]`-cost at most `ωₙ rⁿ`, and the five-times
covering argument with its finite-tail step bounds `μHE[n](A)` by the cost of a disjoint family
of balls `B̄ ⊆ V` with `τ ωₙ rⁿ ≤ ν(B̄)`. -/
theorem Submission.rectifiability_density_comparison : ∀ (P n : ℕ) (ν : Measure (Eucl P)) (A V : Set (Eucl P)) (t : ℝ≥0∞), IsOpen V → A ⊆ V → (∀ x ∈ A, t ≤ dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x) → t * (μHE[n] : Measure (Eucl P)) A ≤ ν V := by
  -- Normalization: `μHE[m] = c • μH[m]` with `c 2ᵐ ≤ ωₘ` (Simon Ch. 1, 2.9–2.10).
  have hnorm : ∀ m : ℕ, ((Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin m))) μH[(m : ℝ)] : ℝ≥0) : ℝ≥0∞) * 2 ^ m ≤
        Poincare.SimonGMT.Chapter01.realUnitBallVolume (m : ℝ) := by
    intro m
    rcases m with _ | k
    · -- Dimension zero: `μHE[0] = μH[0]` forces the scalar to be one.
      have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 0)) => μ {0})
        (Measure.euclideanHausdorffMeasure_zero (X := EuclideanSpace ℝ (Fin 0)))
      simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Nat.cast_zero,
        Measure.hausdorffMeasure_zero_singleton, ENNReal.smul_def, smul_eq_mul, mul_one] at h
      simp [h, Poincare.SimonGMT.Chapter01.realUnitBallVolume_zero]
    obtain ⟨ω, hω⟩ : ∃ ω, Poincare.SimonGMT.Chapter01.realUnitBallVolume ((k + 1 : ℕ) : ℝ) = ω :=
      ⟨_, rfl⟩
    rw [hω]
    have hω0 : ω ≠ 0 :=
      hω ▸ (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (by positivity)).ne'
    have hωtop : ω ≠ ∞ := hω ▸ Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
    -- The isodiametric inequality `Lᵏ⁺¹(C) ≤ ω (diam C / 2)ᵏ⁺¹`, by coordinate Steiner
    -- symmetrization (Simon Ch. 1, 2.10).
    have isodiam : ∀ C : Set (EuclideanSpace ℝ (Fin (k + 1))),
        volume C ≤ ω * (ediam C / 2) ^ (k + 1) := by
      -- Two real slices at cross-distance `≤ d` have total length `≤ 2d`.
      have vol_add_le : ∀ S T : Set ℝ, S.Nonempty → T.Nonempty → ∀ d : ℝ,
          (∀ a ∈ S, ∀ b ∈ T, dist a b ≤ d) → volume S + volume T ≤ ENNReal.ofReal (2 * d) := by
        intro S T hS hT d hcross
        obtain ⟨a₀, ha₀⟩ := hS
        obtain ⟨b₀, hb₀⟩ := hT
        have hdist : ∀ a ∈ S, ∀ b ∈ T, a - b ≤ d ∧ b - a ≤ d := fun a ha b hb =>
          abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
        have hSl : BddBelow S := ⟨b₀ - d, fun a ha => by have := (hdist a ha b₀ hb₀).2; linarith⟩
        have hSu : BddAbove S := ⟨b₀ + d, fun a ha => by have := (hdist a ha b₀ hb₀).1; linarith⟩
        have hTl : BddBelow T := ⟨a₀ - d, fun b hb => by have := (hdist a₀ ha₀ b hb).1; linarith⟩
        have hTu : BddAbove T := ⟨a₀ + d, fun b hb => by have := (hdist a₀ ha₀ b hb).2; linarith⟩
        have hST : sSup S ≤ d + sInf T := by
          apply csSup_le ⟨a₀, ha₀⟩
          intro a ha
          have h : a - d ≤ sInf T := le_csInf ⟨b₀, hb₀⟩ fun b hb => by
            have := (hdist a ha b hb).1
            linarith
          linarith
        have hTS : sSup T ≤ d + sInf S := by
          apply csSup_le ⟨b₀, hb₀⟩
          intro b hb
          have h : b - d ≤ sInf S := le_csInf ⟨a₀, ha₀⟩ fun a ha => by
            have := (hdist a ha b hb).2
            linarith
          linarith
        have hwS : 0 ≤ sSup S - sInf S :=
          sub_nonneg.mpr ((csInf_le hSl ha₀).trans (le_csSup hSu ha₀))
        have hwT : 0 ≤ sSup T - sInf T :=
          sub_nonneg.mpr ((csInf_le hTl hb₀).trans (le_csSup hTu hb₀))
        calc
          volume S + volume T ≤ volume (Icc (sInf S) (sSup S)) + volume (Icc (sInf T) (sSup T)) :=
            add_le_add (measure_mono (subset_Icc_csInf_csSup hSl hSu))
              (measure_mono (subset_Icc_csInf_csSup hTl hTu))
          _ = ENNReal.ofReal ((sSup S - sInf S) + (sSup T - sInf T)) := by
            rw [Real.volume_Icc, Real.volume_Icc, ENNReal.ofReal_add hwS hwT]
          _ ≤ ENNReal.ofReal (2 * d) := ENNReal.ofReal_le_ofReal (by linarith)
      -- The centered interval `cs S` of the same length as a real slice `S`.
      obtain ⟨cs, hcs⟩ : ∃ cs : Set ℝ → Set ℝ,
          ∀ S t, t ∈ cs S ↔ (S.Nonempty ∧ |t| ≤ (volume S).toReal / 2) :=
        ⟨fun S => {t | S.Nonempty ∧ |t| ≤ (volume S).toReal / 2}, fun _ _ => Iff.rfl⟩
      have cs_dist : ∀ (S T : Set ℝ) (d : ℝ), (∀ a ∈ S, ∀ b ∈ T, dist a b ≤ d) →
          ∀ x ∈ cs S, ∀ y ∈ cs T, dist x y ≤ d := by
        intro S T d hcross x hx y hy
        rw [hcs] at hx hy
        have hsum := vol_add_le S T hx.1 hy.1 d hcross
        have hfin : volume S + volume T ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
        have hSfin : volume S ≠ ∞ := (ENNReal.add_ne_top.mp hfin).1
        have hTfin : volume T ≠ ∞ := (ENNReal.add_ne_top.mp hfin).2
        have hd : 0 ≤ d := by
          obtain ⟨a, ha⟩ := hx.1
          obtain ⟨b, hb⟩ := hy.1
          exact dist_nonneg.trans (hcross a ha b hb)
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
        rw [ENNReal.toReal_add hSfin hTfin, ENNReal.toReal_ofReal (by positivity)] at hreal
        calc
          dist x y = |x - y| := Real.dist_eq _ _
          _ ≤ |x| + |y| := abs_sub _ _
          _ ≤ (volume S).toReal / 2 + (volume T).toReal / 2 := add_le_add hx.2 hy.2
          _ ≤ d := by linarith
      have cs_vol : ∀ S : Set ℝ, volume S ≠ ∞ → volume (cs S) = volume S := by
        intro S hfin
        rcases S.eq_empty_or_nonempty with rfl | hS
        · have hempty : cs ∅ = ∅ := by
            ext t
            simp [hcs]
          simp [hempty]
        · have hinterval : cs S = Icc (-(volume S).toReal / 2) ((volume S).toReal / 2) := by
            ext x
            simp [hcs, hS, abs_le, neg_div]
          rw [hinterval, Real.volume_Icc]
          convert ENNReal.ofReal_toReal hfin using 1
          congr 1
          ring
      have cs_neg : ∀ S t, t ∈ cs S → -t ∈ cs S := by
        intro S t h
        rw [hcs] at h ⊢
        simpa only [abs_neg] using h
      -- Changing one coordinate changes the squared distance by that coordinate's change.
      have dist_update : ∀ (j : Fin (k + 1)) (x y : EuclideanSpace ℝ (Fin (k + 1))) (a b : ℝ),
          dist (WithLp.toLp 2 (Function.update x.ofLp j a))
              (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
            dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
        intro j x y a b
        rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
        have hsum := Finset.sum_erase_add Finset.univ
          (fun i : Fin (k + 1) => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
        have hsum' := Finset.sum_erase_add Finset.univ
          (fun i : Fin (k + 1) => dist (Function.update x.ofLp j a i)
            (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
        have hrest : (∑ i ∈ Finset.univ.erase j,
            dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
            ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
        rw [hrest, Function.update_self, Function.update_self] at hsum'
        linarith
      -- Coordinate slices `sl j A x` and the Steiner symmetrization `st j A`.
      obtain ⟨sl, hsl⟩ : ∃ sl : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin (k + 1))) →
          EuclideanSpace ℝ (Fin (k + 1)) → Set ℝ,
          ∀ j A x t, t ∈ sl j A x ↔ WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A :=
        ⟨fun j A x => {t | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A},
          fun _ _ _ _ => Iff.rfl⟩
      obtain ⟨st, hst⟩ : ∃ st : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin (k + 1))) →
          Set (EuclideanSpace ℝ (Fin (k + 1))), ∀ j A x, x ∈ st j A ↔ x j ∈ cs (sl j A x) :=
        ⟨fun j A => {x | x j ∈ cs (sl j A x)}, fun _ _ _ => Iff.rfl⟩
      -- Steiner symmetrization does not increase the diameter.
      have st_diam : ∀ j A, ediam (st j A) ≤ ediam A := by
        intro j A
        by_cases hfin : ediam A = ∞
        · rw [hfin]
          exact le_top
        have hbounded : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
        have hdiam : ediam (st j A) ≤ ENNReal.ofReal (diam A) := by
          apply ediam_le_of_forall_dist_le
          intro x hx y hy
          rw [hst] at hx hy
          obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 :=
            ⟨_, rfl⟩
          have hsq : ∀ a ∈ sl j A x, ∀ b ∈ sl j A y, dist a b ^ 2 ≤ D := by
            intro a ha b hb
            rw [hsl] at ha hb
            have hd := dist_le_diam_of_mem hbounded ha hb
            have hsq' : dist (WithLp.toLp 2 (Function.update x.ofLp j a))
                (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 ≤ diam A ^ 2 :=
              pow_le_pow_left₀ dist_nonneg hd 2
            rw [dist_update] at hsq'
            linarith
          have hD : 0 ≤ D := by
            obtain ⟨a, ha⟩ := ((hcs _ _).1 hx).1
            obtain ⟨b, hb⟩ := ((hcs _ _).1 hy).1
            exact (sq_nonneg (dist a b)).trans (hsq a ha b hb)
          have hsqrt := Real.sq_sqrt hD
          have hcross : ∀ a ∈ sl j A x, ∀ b ∈ sl j A y, dist a b ≤ Real.sqrt D := by
            intro a ha b hb
            have h := hsq a ha b hb
            nlinarith [dist_nonneg (x := a) (y := b), Real.sqrt_nonneg D]
          have hcentered := cs_dist _ _ _ hcross _ hx _ hy
          have hcentered_sq : dist (x j) (y j) ^ 2 ≤ D := by
            nlinarith [dist_nonneg (x := x j) (y := y j), Real.sqrt_nonneg D]
          rw [hD_def] at hcentered_sq
          nlinarith [dist_nonneg (x := x) (y := y), diam_nonneg (s := A)]
        simpa only [diam, ENNReal.ofReal_toReal hfin] using hdiam
      -- Steiner symmetrization of a compact set does not decrease the volume (Fubini).
      have st_vol : ∀ j A, IsCompact A → volume A ≤ volume (st j A) := by
        intro j A hA
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) j
        let φ : ℝ × (Fin k → ℝ) → EuclideanSpace ℝ (Fin (k + 1)) :=
          fun p => WithLp.toLp 2 (e.symm p)
        have hφ : MeasurePreserving φ volume volume :=
          (PiLp.volume_preserving_toLp (Fin (k + 1))).comp
            (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
        have hφcoord : ∀ (t : ℝ) (z : Fin k → ℝ), φ (t, z) j = t := fun t z =>
          Fin.insertNth_apply_same (α := fun _ : Fin (k + 1) => ℝ) j t z
        let T := toMeasurable volume (st j A)
        have hT : MeasurableSet T := measurableSet_toMeasurable volume (st j A)
        have hTA : st j A ⊆ T := subset_toMeasurable volume (st j A)
        have hslice : ∀ (t : ℝ) (z : Fin k → ℝ),
            sl j A (φ (t, z)) = (fun s => φ (s, z)) ⁻¹' A := by
          intro t z
          ext s
          rw [hsl]
          change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ A) ↔
            WithLp.toLp 2 (j.insertNth s z) ∈ A
          rw [Fin.update_insertNth]
        have hfinite : ∀ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) ≠ ∞ := by
          intro z
          have hproj : IsCompact ((fun x : EuclideanSpace ℝ (Fin (k + 1)) => x j) '' A) :=
            hA.image (by fun_prop)
          have hsub : (fun t => φ (t, z)) ⁻¹' A ⊆
              (fun x : EuclideanSpace ℝ (Fin (k + 1)) => x j) '' A := by
            intro t ht
            exact ⟨φ (t, z), ht, hφcoord t z⟩
          exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
        calc
          volume A = volume (φ ⁻¹' A) :=
            (hφ.measure_preimage hA.measurableSet.nullMeasurableSet).symm
          _ = ∫⁻ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) :=
            Measure.prod_apply_symm (hA.measurableSet.preimage hφ.measurable)
          _ = ∫⁻ z : Fin k → ℝ, volume (cs ((fun t => φ (t, z)) ⁻¹' A)) := by
            apply lintegral_congr
            intro z
            exact (cs_vol _ (hfinite z)).symm
          _ ≤ ∫⁻ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' T) := by
            apply lintegral_mono
            intro z
            apply measure_mono
            intro t ht
            apply hTA
            show φ (t, z) ∈ st j A
            rw [hst, hφcoord, hslice]
            exact ht
          _ = volume (φ ⁻¹' T) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
          _ = volume T := hφ.measure_preimage hT.nullMeasurableSet
          _ = volume (st j A) := measure_toMeasurable (st j A)
      -- Coordinate reflections `rf j`.
      obtain ⟨rf, hrf⟩ : ∃ rf : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)) →
          EuclideanSpace ℝ (Fin (k + 1)),
          ∀ j x, rf j x = WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :=
        ⟨fun j x => WithLp.toLp 2 (Function.update x.ofLp j (-x j)), fun _ _ => rfl⟩
      have rf_same : ∀ j x, rf j x j = -x j := by
        intro j x
        simp [hrf]
      have rf_ne : ∀ i j, i ≠ j → ∀ x, rf j x i = x i := by
        intro i j hij x
        rw [hrf]
        exact Function.update_of_ne hij _ _
      have rf_invol : ∀ j x, rf j (rf j x) = x := by
        intro j x
        ext i
        by_cases hij : i = j
        · subst i
          simp [rf_same]
        · simp only [rf_ne i j hij]
      have rf_cont : ∀ j, Continuous (rf j) := by
        intro j
        have hfun : rf j = fun x => WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :=
          funext (hrf j)
        rw [hfun]
        apply (PiLp.continuous_toLp 2 (fun _ : Fin (k + 1) => ℝ)).comp
        apply continuous_pi
        intro i
        by_cases hij : i = j
        · subst i
          simpa only [Function.update_self] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (k + 1)) => -x j) by fun_prop)
        · simpa only [Function.update_of_ne hij] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (k + 1)) => x i) by fun_prop)
      have sl_rf_same : ∀ j A x, sl j A (rf j x) = sl j A x := by
        intro j A x
        ext t
        rw [hsl, hsl, hrf]
        change (WithLp.toLp 2 (Function.update (Function.update x.ofLp j (-x j)) j t) ∈ A) ↔ _
        rw [Function.update_idem]
      have rf_update : ∀ i j, i ≠ j → ∀ x t,
          rf i (WithLp.toLp 2 (Function.update x.ofLp j t)) =
            WithLp.toLp 2 (Function.update (rf i x).ofLp j t) := by
        intro i j hij x t
        ext l
        by_cases hli : l = i
        · subst l
          simp [hrf, hij]
        · by_cases hlj : l = j
          · subst l
            simp [hrf, hij, Ne.symm hij]
          · simp [hrf, Function.update_apply, hli, hlj]
      have sl_rf_symm : ∀ i j, i ≠ j → ∀ A, (∀ x ∈ A, rf i x ∈ A) →
          ∀ x, sl j A (rf i x) = sl j A x := by
        intro i j hij A hA x
        ext t
        rw [hsl, hsl, ← rf_update i j hij]
        constructor
        · intro h
          simpa only [rf_invol] using hA _ h
        · exact hA _
      have st_rf_same : ∀ j A, ∀ x ∈ st j A, rf j x ∈ st j A := by
        intro j A x hx
        rw [hst] at hx ⊢
        rw [rf_same, sl_rf_same]
        exact cs_neg _ _ hx
      have st_rf_pres : ∀ i j, i ≠ j → ∀ A, (∀ x ∈ A, rf i x ∈ A) →
          ∀ x ∈ st j A, rf i x ∈ st j A := by
        intro i j hij A hA x hx
        rw [hst] at hx ⊢
        rw [rf_ne j i (Ne.symm hij), sl_rf_symm i j hij A hA]
        exact hx
      have closure_rf : ∀ i (A : Set (EuclideanSpace ℝ (Fin (k + 1)))),
          (∀ x ∈ A, rf i x ∈ A) → ∀ x ∈ closure A, rf i x ∈ closure A := by
        intro i A hA x hx
        have hsub : A ⊆ rf i ⁻¹' closure A := fun y hy => subset_closure (hA y hy)
        exact closure_minimal hsub (isClosed_closure.preimage (rf_cont i)) hx
      -- Successive closed Steiner symmetrizations in all coordinates.
      have hfinite : ∀ K₀ : Set (EuclideanSpace ℝ (Fin (k + 1))), IsCompact K₀ →
          ∀ s : Finset (Fin (k + 1)), ∃ K : Set (EuclideanSpace ℝ (Fin (k + 1))), IsCompact K ∧
            ediam K ≤ ediam K₀ ∧ volume K₀ ≤ volume K ∧ ∀ i ∈ s, ∀ x ∈ K, rf i x ∈ K := by
        intro K₀ hK₀ s
        induction s using Finset.induction_on with
        | empty => exact ⟨K₀, hK₀, le_rfl, le_rfl, by simp⟩
        | @insert i s hi ih =>
          obtain ⟨K, hK, hdiam, hvol, hsym⟩ := ih
          have hdK : ediam (closure (st i K)) ≤ ediam K := by
            rw [ediam_closure]
            exact st_diam i K
          refine ⟨closure (st i K), ?_, hdK.trans hdiam,
            hvol.trans ((st_vol i K hK).trans (measure_mono subset_closure)), ?_⟩
          · apply Bornology.IsBounded.isCompact_closure
            apply isBounded_iff_ediam_ne_top.mpr
            exact ne_top_of_le_ne_top hK.isBounded.ediam_ne_top (st_diam i K)
          · intro l hl
            rcases Finset.mem_insert.mp hl with rfl | hls
            · exact closure_rf l _ (st_rf_same l K)
            · apply closure_rf l _
              apply st_rf_pres l i _ K (hsym l hls)
              rintro rfl
              exact hi hls
      -- Symmetry in every coordinate hyperplane gives central symmetry.
      have neg_mem : ∀ K : Set (EuclideanSpace ℝ (Fin (k + 1))),
          (∀ i, ∀ x ∈ K, rf i x ∈ K) → ∀ x ∈ K, -x ∈ K := by
        intro K hK x hx
        have hmem : ∀ s : Finset (Fin (k + 1)),
            WithLp.toLp 2 (fun l => if l ∈ s then -x l else x l) ∈ K := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using hx
          | @insert i s hi ih =>
            have h := hK i _ ih
            convert h using 1
            ext l
            by_cases hli : l = i
            · subst l
              simp [hrf, hi]
            · simp [hrf, hli]
        have heq : (WithLp.toLp 2 fun l => -x l) = -x := by
          ext l
          rfl
        simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ
      -- Conclusion for a general set `C`.
      intro C
      by_cases hfin : ediam C = ∞
      · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
          ENNReal.top_pow (Nat.succ_ne_zero k), ENNReal.mul_top hω0]
        exact le_top
      have hbdd : Bornology.IsBounded C := isBounded_iff_ediam_ne_top.mpr hfin
      obtain ⟨K, hK, hdiamK, hvolK, hsymK⟩ :=
        hfinite (closure C) hbdd.isCompact_closure Finset.univ
      have hneg := neg_mem K (fun i => hsymK i (Finset.mem_univ i))
      have hKb : Bornology.IsBounded K := hK.isBounded
      have hsub : K ⊆ closedBall 0 (diam K / 2) := by
        intro x hx
        have hdist := dist_le_diam_of_mem hKb hx (hneg x hx)
        rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at hdist
        norm_num at hdist
        rw [mem_closedBall, dist_zero_right]
        linarith
      have hpi : Real.sqrt Real.pi ^ (k + 1) = Real.pi ^ (((k + 1 : ℕ) : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
        congr 1
        push_cast
        ring
      have hball : volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) (diam K / 2)) =
          ω * ENNReal.ofReal (diam K / 2) ^ (k + 1) := by
        rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, hpi, ← hω,
          Poincare.SimonGMT.Chapter01.realUnitBallVolume_eq, mul_comm]
      calc
        volume C ≤ volume (closure C) := measure_mono subset_closure
        _ ≤ volume K := hvolK
        _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) (diam K / 2)) :=
          measure_mono hsub
        _ = ω * ENNReal.ofReal (diam K / 2) ^ (k + 1) := hball
        _ = ω * (ediam K / 2) ^ (k + 1) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat, diam,
            ENNReal.ofReal_toReal hKb.ediam_ne_top]
        _ ≤ ω * (ediam C / 2) ^ (k + 1) := by
          have hKC : ediam K ≤ ediam C := (ediam_closure C) ▸ hdiamK
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ zero_le (ENNReal.div_le_div_right hKC 2) _) zero_le
    -- Hence `ω⁻¹ 2ᵏ⁺¹ Lᵏ⁺¹ ≤ μH[k+1]`, and comparing on the unit ball gives `c 2ᵏ⁺¹ ≤ ω`.
    have hle : (ω⁻¹ * 2 ^ (k + 1)) •
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) ≤ μH[((k + 1 : ℕ) : ℝ)] := by
      refine Measure.le_mkMetric (fun r : ℝ≥0∞ => r ^ ((k + 1 : ℕ) : ℝ)) _ 1 one_pos fun s _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
      calc
        ω⁻¹ * 2 ^ (k + 1) * volume s ≤ ω⁻¹ * 2 ^ (k + 1) * (ω * (ediam s / 2) ^ (k + 1)) := by
          gcongr
          exact isodiam s
        _ = (2 * (ediam s / 2)) ^ (k + 1) := by
          rw [mul_pow, mul_assoc, mul_left_comm (2 ^ (k + 1)), ← mul_assoc,
            ENNReal.inv_mul_cancel hω0 hωtop, one_mul]
        _ = ediam s ^ (k + 1) := by
          rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    have hB : volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) = ω := by
      rw [Poincare.SimonGMT.Chapter01.volume_closedBall_eq_densityNormalization (k + 1) 0 one_pos,
        hω]
      simp
    have hHB : 2 ^ (k + 1) ≤ (μH[((k + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        (closedBall 0 1) := by
      have h := Measure.le_iff'.1 hle (closedBall 0 1)
      rwa [Measure.smul_apply, smul_eq_mul, hB, mul_comm, ← mul_assoc,
        ENNReal.mul_inv_cancel hω0 hωtop, one_mul] at h
    have hvol := Measure.isAddLeftInvariant_eq_smul
      (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) (μH[((k + 1 : ℕ) : ℝ)])
    have h2 := congrArg
      (fun μ : Measure (EuclideanSpace ℝ (Fin (k + 1))) => μ (closedBall 0 1)) hvol
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hB] at h2
    calc
      _ ≤ ((Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))
            μH[((k + 1 : ℕ) : ℝ)] : ℝ≥0) : ℝ≥0∞) *
          (μH[((k + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (k + 1)))) (closedBall 0 1) := by
        gcongr
      _ = _ := h2.symm
  intro P n ν A V t hV hAV hden
  obtain ⟨ω, hω⟩ : ∃ ω, Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) = ω := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)] = c := ⟨_, rfl⟩
  have hcω : (c : ℝ≥0∞) * 2 ^ n ≤ ω := hc ▸ hω ▸ hnorm n
  have hω0 : ω ≠ 0 := hω ▸ (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (by positivity)).ne'
  have hωtop : ω ≠ ∞ := hω ▸ Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
  -- `μHE[n] = c • μH[n]`, and `μH[n]` is the supremum of its size-`δ` approximations `pre δ`.
  have hHE : (μHE[n] : Measure (Eucl P)) A = c * ⨆ (δ : ℝ≥0∞) (_ : 0 < δ),
      OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A := by
    rw [Measure.euclideanHausdorffMeasure_def, hc, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul, ← Measure.toOuterMeasure_apply, Measure.hausdorffMeasure,
      Measure.mkMetric_toOuterMeasure, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
      OuterMeasure.iSup_apply]
    simp only [OuterMeasure.iSup_apply]
  by_cases hVfin : ν V = ∞
  · rw [hVfin]
    exact le_top
  -- It suffices to prove `τ μHE[n](A) ≤ ν(V)` for `0 < τ < t`, scale by scale.
  rw [hHE]
  conv_lhs => rw [← ENNReal.iSup_lt_eq_self t]
  simp only [ENNReal.iSup_mul]
  refine iSup₂_le fun τ hτ => ?_
  rcases eq_or_ne τ 0 with rfl | hτ0
  · simp
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine iSup_le fun δ => ?_
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine iSup_le fun hδ => ?_
  obtain ⟨R, -, hR0, hRδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
  -- The fine family of closed balls `B̄ᵣ(x) ⊆ V`, `x ∈ A`, `r < R/10`, `τ ω rⁿ ≤ ν(B̄ᵣ(x))`.
  let B : Set (Eucl P × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ b.2 < R / 10 ∧
    closedBall b.1 b.2 ⊆ V ∧ τ * (ω * ENNReal.ofReal b.2 ^ (n : ℝ)) ≤ ν (closedBall b.1 b.2)}
  have hfine : ∀ x ∈ A, ∀ ε > 0, ∃ b ∈ B,
      x ∈ closedBall b.1 b.2 ∧ diam (closedBall b.1 b.2) < ε := by
    intro x hx ε hε
    obtain ⟨RV, hRV, hRVV⟩ := nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds (hAV hx))
    have hpos : 0 < min (min (R / 10) (ε / 2)) RV :=
      lt_min (lt_min (by positivity) (half_pos hε)) hRV
    have hτx : τ < dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x :=
      hτ.trans_le (hden x hx)
    obtain ⟨r, hqr, hr⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hτx).and_eventually
      (Ioo_mem_nhdsGT hpos)).exists
    have hr0 : 0 < r := hr.1
    have hrR : r < R / 10 := hr.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hrε : r < ε / 2 := hr.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hrV : r < RV := hr.2.trans_le (min_le_right _ _)
    have hnorm0 : ω * ENNReal.ofReal r ^ (n : ℝ) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr0) ENNReal.ofReal_ne_top).ne'
    have hnormtop : ω * ENNReal.ofReal r ^ (n : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    rw [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient, hω, univ_inter,
      Measure.toOuterMeasure_apply] at hqr
    have hmass : τ * (ω * ENNReal.ofReal r ^ (n : ℝ)) ≤ ν (closedBall x r) :=
      ((ENNReal.lt_div_iff_mul_lt (Or.inl hnorm0) (Or.inl hnormtop)).mp hqr).le
    refine ⟨(x, r), ⟨hx, hr0, hrR, (closedBall_subset_closedBall hrV.le).trans hRVV, hmass⟩,
      mem_closedBall_self hr0.le, (diam_closedBall hr0.le).trans_lt (by linarith)⟩
  -- The five-times covering lemma (Simon Ch. 1, 3.4) gives a disjoint subfamily `D`.
  obtain ⟨D, hDB, hdisj, hcover⟩ := Poincare.SimonGMT.Chapter01.exists_fiveTimesCovering B
    Prod.fst Prod.snd (fun b hb => hb.2.1.le) R
    (fun b hb => (diam_closedBall hb.2.1.le).trans (by have := hb.2.2.1; linarith))
  have hdisj' : Pairwise (fun i j : D =>
      Disjoint (closedBall i.val.1 i.val.2) (closedBall j.val.1 j.val.2)) :=
    fun i j hij => hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hpos : ∀ b : D, 0 < ν (closedBall b.val.1 b.val.2) := by
    intro b
    have hb := hDB b.property
    exact (pos_iff_ne_zero.mpr (mul_ne_zero hτ0 (mul_ne_zero hω0
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hb.2.1) ENNReal.ofReal_ne_top).ne'))).trans_le
      hb.2.2.2.2
  have hUV : (⋃ b : D, closedBall b.val.1 b.val.2) ⊆ V :=
    iUnion_subset fun b => (hDB b.property).2.2.2.1
  have hcount := ν.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
    (fun b : D => measurableSet_closedBall) hdisj' (ne_top_of_le_ne_top hVfin (measure_mono hUV))
  have hDc : Countable D := countable_univ_iff.mp (by simpa only [hpos, ofPred_true] using hcount)
  -- Total cost of the disjoint family: `τ ∑ ω rⁿ ≤ ∑ ν(B̄ᵣ) ≤ ν(V)`.
  let w : D → ℝ≥0∞ := fun b => ω * ENNReal.ofReal b.val.2 ^ (n : ℝ)
  have hsum : τ * ∑' b : D, w b ≤ ν V := by
    rw [← ENNReal.tsum_mul_left]
    calc
      ∑' b : D, τ * w b ≤ ∑' b : D, ν (closedBall b.val.1 b.val.2) :=
        ENNReal.tsum_le_tsum fun b => (hDB b.property).2.2.2.2
      _ = ν (⋃ b : D, closedBall b.val.1 b.val.2) :=
        (measure_iUnion hdisj' (fun _ => measurableSet_closedBall)).symm
      _ ≤ ν V := measure_mono hUV
  have hsumfin : ∑' b : D, w b ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hτ0] at hsum
    exact hVfin (top_le_iff.mp hsum)
  -- Costs of the selected balls and of their five-times enlargements at scale `δ`.
  have hediam : ∀ (x : Eucl P) (r : ℝ), ediam (closedBall x r) ≤ 2 * ENNReal.ofReal r := by
    intro x r
    calc
      ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
        ediam_le_of_forall_dist_le fun y hy z hz => by
          have hy' := mem_closedBall.mp hy
          have hz' := mem_closedBall.mp hz
          linarith [dist_triangle_right y z x]
      _ = 2 * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hcost : ∀ (x : Eucl P) (r : ℝ), 0 ≤ r → 2 * r ≤ R →
      (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
        (closedBall x r) ≤ ω * ENNReal.ofReal r ^ (n : ℝ) := by
    intro x r hr hrR
    have hle : ediam (closedBall x r) ≤ δ := by
      refine (hediam x r).trans (le_trans ?_ hRδ.le)
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hrR
    calc
      (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
          (closedBall x r) ≤ c * ediam (closedBall x r) ^ (n : ℝ) := by
        gcongr
        exact OuterMeasure.mkMetric'.pre_le hle
      _ ≤ c * (2 * ENNReal.ofReal r) ^ (n : ℝ) := by
        gcongr
        exact hediam x r
      _ = (c * 2 ^ n) * ENNReal.ofReal r ^ (n : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.rpow_natCast, mul_assoc]
      _ ≤ ω * ENNReal.ofReal r ^ (n : ℝ) := by
        gcongr
  have hsmall : ∀ b : D, (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
      (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ (closedBall b.val.1 b.val.2) ≤ w b := by
    intro b
    have hb := hDB b.property
    exact hcost _ _ hb.2.1.le (by linarith [hb.2.2.1])
  have hlarge : ∀ b : D, (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
      (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ (closedBall b.val.1 (5 * b.val.2)) ≤
        5 ^ n * w b := by
    intro b
    have hb := hDB b.property
    refine (hcost _ _ (by linarith [hb.2.1]) (by linarith [hb.2.2.1])).trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.rpow_natCast, ENNReal.ofReal_ofNat]
    simp only [w]
    ring
  -- Simon's finite-tail step (Corollary 3.5): the enlarged tail costs vanish in the limit.
  have hlim : Tendsto (fun F : Finset D => (∑' b, w b) + 5 ^ n * ∑' b : {b // b ∉ F}, w b)
      atTop (𝓝 (∑' b, w b)) := by
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_tsum_compl_atTop_zero hsumfin) (Or.inr (by simp)))
  have hηA : (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
      (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A ≤ ∑' b, w b := by
    apply ge_of_tendsto' hlim
    intro F
    let F' : Finset (Eucl P × ℝ) := F.image Subtype.val
    have hsub : A ⊆ (⋃ b ∈ F, closedBall b.val.1 b.val.2) ∪
        ⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2) := by
      intro x hx
      by_cases hxF : x ∈ ⋃ b ∈ F, closedBall b.val.1 b.val.2
      · exact Or.inl hxF
      · right
        have hxF' : x ∉ ⋃ b ∈ F', closedBall b.1 b.2 := by
          simpa only [F', Finset.mem_image, mem_iUnion, exists_prop,
            exists_exists_and_eq_and] using hxF
        obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp
          (Poincare.SimonGMT.Chapter01.fiveTimesCovering_finite_remainder A B D Prod.fst
            Prod.snd hfine (fun b hb => by
              obtain ⟨d, hd, hinter, _, hsub⟩ := hcover b hb
              exact ⟨d, hd, hinter, hsub⟩) F' ⟨hx, hxF'⟩)
        have hbF : (⟨b, hb.1⟩ : D) ∉ F := by
          intro h
          exact hb.2 (Finset.mem_image.mpr ⟨⟨b, hb.1⟩, h, rfl⟩)
        exact mem_iUnion.mpr ⟨⟨⟨b, hb.1⟩, hbF⟩, hxb⟩
    set η := OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
    calc
      (c : ℝ≥0∞) * η A ≤ c * (η (⋃ b ∈ F, closedBall b.val.1 b.val.2) +
          η (⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2))) := by
        gcongr
        exact (measure_mono hsub).trans (measure_union_le _ _)
      _ = c * η (⋃ b ∈ F, closedBall b.val.1 b.val.2) +
          c * η (⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2)) :=
        mul_add _ _ _
      _ ≤ (∑ b ∈ F, w b) + ∑' b : {b : D // b ∉ F}, 5 ^ n * w b := by
        gcongr
        · calc
            (c : ℝ≥0∞) * η (⋃ b ∈ F, closedBall b.val.1 b.val.2) ≤
                c * ∑ b ∈ F, η (closedBall b.val.1 b.val.2) := by
              gcongr
              exact measure_biUnion_finset_le _ _
            _ = ∑ b ∈ F, c * η (closedBall b.val.1 b.val.2) := Finset.mul_sum _ _ _
            _ ≤ ∑ b ∈ F, w b := Finset.sum_le_sum fun b _ => hsmall b
        · calc
            (c : ℝ≥0∞) * η (⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2)) ≤
                c * ∑' b : {b : D // b ∉ F}, η (closedBall b.val.val.1 (5 * b.val.val.2)) := by
              gcongr
              exact measure_iUnion_le _
            _ = ∑' b : {b : D // b ∉ F}, c * η (closedBall b.val.val.1 (5 * b.val.val.2)) :=
              ENNReal.tsum_mul_left.symm
            _ ≤ ∑' b : {b : D // b ∉ F}, 5 ^ n * w b :=
              ENNReal.tsum_le_tsum fun b => hlarge b
      _ ≤ (∑' b, w b) + 5 ^ n * ∑' b : {b : D // b ∉ F}, w b := by
        rw [ENNReal.tsum_mul_left]
        exact add_le_add (ENNReal.sum_le_tsum F) le_rfl
  calc
    τ * ((c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
        (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A) ≤ τ * ∑' b, w b := by
      gcongr
    _ ≤ ν V := hsum
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the
proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to
`Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets, `V ∋ x` open.  If `B_δ(x) ⊆ V` and
`f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off
`W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and
`(M', θ')` agree for all small `r`. -/
theorem Submission.br_weightedTangent_congr :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P) (V : Set (Eucl P)),
      IsOpen V → x ∈ V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ y = θ' y) → θ x = θ' x →
      ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k M' θ' x L := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k M M' θ θ' x V hV hxV hMM' hθθ' hθx L hL
  -- `η_r(y) = r⁻¹ (y - x)` maps `Hᵏ`-null sets to `Hᵏ`-null sets: `Hᵏ(η_r Z) = r⁻ᵏ Hᵏ(Z)`.
  have hnull : ∀ r : ℝ, r ≠ 0 → ∀ Z : Set (Eucl P), (μHE[k] : Measure (Eucl P)) Z = 0 →
      (μHE[k] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- A measurable `N ⊇ {θ ≠ θ'}` with `Hᵏ(N ∩ M ∩ V) = 0`.
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hθθ')
  rw [Measure.restrict_apply hNmeas] at hN0
  refine ⟨hL.1, fun f => ?_⟩
  rw [← hθx]
  refine (hL.2 f).congr' ?_
  -- `f = 0` off `B_R(0)` and `B_δ(x) ⊆ V`; the blow-up integrals agree for `0 < r < δ / R`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hcont : Continuous fun y : Eucl P => x + r • y :=
    continuous_const.add (continuous_const_smul r)
  -- `W = η_r(V)` is open and the integrands `f(y) g(x + r y)` vanish off `W`.
  set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' V with hW
  have hWmeas : MeasurableSet W := (hV.preimage hcont).measurableSet
  have hvan : ∀ g : Eucl P → ℝ, ∀ y, y ∉ W → f y * g (x + r • y) = 0 := by
    intro g y hy
    have hfy : f y = 0 := by
      apply hfR
      have h1 : x + r • y ∉ ball x δ := fun h => hy (hδV h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, not_lt] at h1
      rw [lt_div_iff₀ hR] at hrR
      exact le_of_lt (lt_of_mul_lt_mul_left (hrR.trans_le h1) hr0.le)
    rw [hfy, zero_mul]
  -- Cutting by `W`: `∫_{η_r(S)} = ∫_{W ∩ η_r(S)}`.
  have hcut : ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ y in W ∩ blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
    intro S g
    rw [← Measure.restrict_restrict hWmeas,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan g)]
  -- `W ∩ η_r(M) = W ∩ η_r(M')` up to the null set `η_r((M ∆ M') ∩ V)`.
  have hset : W ∩ blowUpMap x r '' M =ᵐ[(μHE[k] : Measure (Eucl P))] W ∩ blowUpMap x r '' M' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inl ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inr ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
  -- `θ(x + r y) = θ'(x + r y)` a.e. on `W ∩ η_r(M)`, off the null set `η_r(N ∩ M ∩ V)`.
  have hae : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (W ∩ blowUpMap x r '' M)),
      f y * θ (x + r • y) = f y * θ' (x + r • y) := by
    have hN'meas : MeasurableSet ((fun y => x + r • y) ⁻¹' N) :=
      hNmeas.preimage hcont.measurable
    rw [ae_iff]
    refine measure_mono_null (t := (fun y => x + r • y) ⁻¹' N) ?_ ?_
    · intro y hy
      by_contra hyN
      apply hy
      have hθy : θ (x + r • y) = θ' (x + r • y) := by
        by_contra hne
        exact hyN (hNsub hne)
      rw [hθy]
    · rw [Measure.restrict_apply hN'meas]
      refine measure_mono_null ?_ (hnull r hr0.ne' _ hN0)
      rintro y ⟨hyN, hyW, z, hzM, rfl⟩
      refine ⟨z, ⟨?_, hzM, ?_⟩, rfl⟩
      · simpa [hinv r hr0.ne' z] using hyN
      · simpa [hW, hinv r hr0.ne' z] using hyW
  calc ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P))
      = ∫ y in W ∩ blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        hcut M θ
    _ = ∫ y in W ∩ blowUpMap x r '' M, f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        integral_congr_ae hae
    _ = ∫ y in W ∩ blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
        rw [Measure.restrict_congr_set hset]
    _ = ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        (hcut M' θ').symm

/-- Simon Ch. 3, Theorem 1.9 "⇒" (via Theorem 1.6 and Remark 1.8(1)), localized to an open
`U`: if `M ⊆ U` is `Hⁿ`-measurable and countably `n`-rectifiable and `θ > 0` is locally
`Hⁿ`-integrable on `M` in `U`, then `M` has an approximate tangent space with respect to `θ` at
`Hⁿ`-a.e. point of `M` (`n = m + 1`).

Proof.  Localize to `M ∩ W_q` with `W_q ⊂⊂ U` (`cmb_exists_compactly_contained_exhaustion`,
`br_weightedTangent_congr`) and pass to a Borel subset of full measure, so that `θ ∈ L¹(Hⁿ⌞M)`.
Cut the Lipschitz parametrizations `F_j : ℝⁿ → ℝ^P` of `M` into Borel pieces `T_p` on which
`G_p = F_j` is differentiable with injective derivative and uniformly bi-Lipschitz
(Rademacher, null critical images, approximately linear partition).  Fix `p`, put
`A = T_p ∩ G_p⁻¹(M)` and `h = 1_A J_{G_p} (θ ∘ G_p) ∈ L¹(ℝⁿ)` (injective area formula).  At
`x = G_p(b)` with `b ∈ A` a Lebesgue point of `h` and `θ Hⁿ⌞(M ∖ G_p(T_p))` of zero `n`-density at
`x` (Simon Ch. 1, 3.6), the area formula and the substitution `b' = b + r c` give
`∫_{η_{x,r}(M)} f(y) θ(x + r y) dHⁿ(y) = ∫ h(b + r c) f((G_p(b + r c) - x) / r) dc + o(1)`,
the integrand vanishes for `|c| > R'` (lower bound on `T_p`), and the right side tends to
`h(b) ∫ f(dG_p(b) c) dc = θ(x) ∫_{dG_p(b)(ℝⁿ)} f dHⁿ` (Lebesgue point, dominated convergence,
linear area formula).  The exceptional sets are countably many `Hⁿ`-null sets. -/
theorem Submission.rectifiability_weighted_tangent_ae :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ), IsOpen U → M ⊆ U →
      NullMeasurableSet M (μHE[m + 1] : Measure (Eucl P)) → CountablyRectifiable (m + 1) M →
      (∀ x ∈ M, 0 < θ x) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) →
      ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∃ V : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x V := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P m
  -- Blow-ups rescale `Hⁿ`: `∫_{η_{x,r}(S)} F dHⁿ = r⁻ⁿ ∫_S F ∘ η_{x,r} dHⁿ`.
  have hblow : ∀ (x : Eucl P) (r : ℝ), 0 < r → ∀ (S : Set (Eucl P)) (F : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, F y ∂(μHE[m + 1] : Measure (Eucl P)) =
        (r ^ (m + 1))⁻¹ * ∫ z in S, F (blowUpMap x r z) ∂(μHE[m + 1] : Measure (Eucl P)) := by
    intro x r hr S F
    set μ := (μHE[m + 1] : Measure (Eucl P)) with hμ
    let e : Eucl P ≃ₜ Eucl P :=
      (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
    have he : (e : Eucl P → Eucl P) = blowUpMap x r := rfl
    have hemb : MeasurableEmbedding (blowUpMap x r) := he ▸ e.measurableEmbedding
    have himg : ∀ Z : Set (Eucl P), μ (blowUpMap x r '' Z) =
        ((‖r⁻¹‖₊ ^ (m + 1) : ℝ≥0) : ℝ≥0∞) * μ Z := by
      open scoped Pointwise in
      intro Z
      have h1 : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
        rw [← Set.image_smul, Set.image_image]
        rfl
      rw [h1, hμ, Measure.euclideanHausdorffMeasure_smul₀ _ (inv_ne_zero hr.ne'),
        (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
      rfl
    have hmeas : μ.restrict (blowUpMap x r '' S) =
        (‖r⁻¹‖₊ ^ (m + 1)) • Measure.map (blowUpMap x r) (μ.restrict S) := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.smul_apply, Measure.map_apply hemb.measurable hT,
        Measure.restrict_apply (hemb.measurable hT), ← Set.image_preimage_inter, himg]
      rfl
    rw [hmeas, integral_smul_nnreal_measure, hemb.integral_map, NNReal.smul_def, smul_eq_mul]
    congr 1
    rw [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_pow]
  -- Simon Ch. 1, 3.6 for `θ Hⁿ⌞S`: zero `n`-density at `Hⁿ`-a.e. point off `S`.
  have hdensity : ∀ (θ : Eucl P → ℝ) (S : Set (Eucl P)), MeasurableSet S →
      IntegrableOn θ S (μHE[m + 1] : Measure (Eucl P)) →
      ∀ᵐ x ∂(μHE[m + 1] : Measure (Eucl P)), x ∉ S →
        Tendsto (fun ρ => (∫ z in S ∩ closedBall x ρ, |θ z| ∂(μHE[m + 1] : Measure (Eucl P))) /
          ρ ^ (m + 1)) (𝓝[>] 0) (𝓝 0) := by
    intro θ S hS hθ
    set μ := (μHE[m + 1] : Measure (Eucl P)) with hμ
    set ν : Measure (Eucl P) := (μ.restrict S).withDensity (fun z => ‖θ z‖ₑ) with hν
    have hνS : ν.toOuterMeasure S < ∞ := by
      rw [Measure.toOuterMeasure_apply, hν, withDensity_apply _ hS, Measure.restrict_restrict hS,
        inter_self]
      exact hθ.2
    have hcar : Poincare.SimonGMT.Chapter01.IsCaratheodoryMeasurable ν.toOuterMeasure S :=
      le_toOuterMeasure_caratheodory ν S hS
    have h1 := Poincare.SimonGMT.Chapter01.ae_dimensionalUpperDensity_eq_zero_outside
      ν.toOuterMeasure (Poincare.SimonGMT.Chapter01.measure_toOuterMeasure_isBorelRegular ν)
      (n := ((m + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _) hcar hνS
    rw [Poincare.SimonGMT.Chapter02.simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure]
      at h1
    filter_upwards [(Measure.absolutelyContinuous_smul
      (Poincare.SimonGMT.Chapter02.simonAreaNormalization_pos (m + 1)).ne').ae_le h1] with x hx hxS
    have hlim := hx hxS
    have htend : Tendsto (Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient ν.toOuterMeasure
        ((m + 1 : ℕ) : ℝ) S x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_of_le_liminf_of_limsup_le bot_le hlim.le
    set ω := Poincare.SimonGMT.Chapter01.realUnitBallVolume ((m + 1 : ℕ) : ℝ) with hω
    have hω0 : ω ≠ 0 := (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg _)).ne'
    have hωtop : ω ≠ ∞ := Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
    have hωreal : ω.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hω0, hωtop⟩
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    rw [ENNReal.toReal_zero] at hreal
    have hmul := hreal.const_mul ω.toReal
    rw [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    simp only [Function.comp_apply, Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient]
    have hI : 0 ≤ ∫ z in S ∩ closedBall x ρ, |θ z| ∂μ := integral_nonneg fun z => abs_nonneg (θ z)
    have hball : ν.toOuterMeasure (S ∩ closedBall x ρ) =
        ENNReal.ofReal (∫ z in S ∩ closedBall x ρ, |θ z| ∂μ) := by
      have hSB : (S ∩ closedBall x ρ) ∩ S = S ∩ closedBall x ρ := by
        ext z; simp only [mem_inter_iff]; tauto
      rw [Measure.toOuterMeasure_apply, hν, withDensity_apply _ (hS.inter measurableSet_closedBall),
        Measure.restrict_restrict (hS.inter measurableSet_closedBall), hSB,
        ← ofReal_integral_norm_eq_lintegral_enorm (hθ.mono_set inter_subset_left)]
      simp only [Real.norm_eq_abs]
    rw [hball, ENNReal.toReal_div, ENNReal.toReal_ofReal hI, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hρ0.le, Real.rpow_natCast, ← hω]
    field_simp
  -- Cover by uniformly bi-Lipschitz pieces of the Lipschitz parametrizations, up to a null set.
  have hparam : ∀ M : Set (Eucl P), CountablyRectifiable (m + 1) M →
      ∃ N : Set (Eucl P), (μHE[m + 1] : Measure (Eucl P)) N = 0 ∧
      ∃ (G : ℕ → Eucl (m + 1) → Eucl P) (T : ℕ → Set (Eucl (m + 1))) (κ : ℕ → ℝ),
        (∀ p, ∃ K, LipschitzWith K (G p)) ∧ (∀ p, MeasurableSet (T p)) ∧ (∀ p, 0 < κ p) ∧
        (∀ p, ∀ b ∈ T p, DifferentiableAt ℝ (G p) b ∧ Function.Injective (fderiv ℝ (G p) b)) ∧
        (∀ p, ∀ b ∈ T p, ∀ b' ∈ T p, κ p * ‖b - b'‖ ≤ ‖G p b - G p b'‖) ∧
        M ⊆ N ∪ ⋃ p, G p '' T p := by
    intro M hM
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
    -- Linear maps with a small enough approximation constant are uniformly bi-Lipschitz.
    have hchoice : ∀ L : Eucl (m + 1) →L[ℝ] Eucl P, ∃ δ : ℝ≥0, 0 < δ ∧ ∃ k : ℝ, 0 < k ∧
        (Function.Injective L → ∀ (t : Set (Eucl (m + 1))) (g : Eucl (m + 1) → Eucl P),
          ApproximatesLinearOn g L t δ → ∀ b ∈ t, ∀ b' ∈ t, k * ‖b - b'‖ ≤ ‖g b - g b'‖) := by
      intro L
      by_cases hL : Function.Injective L
      · obtain ⟨K, hKpos, hK⟩ := (L : Eucl (m + 1) →ₗ[ℝ] Eucl P).exists_antilipschitzWith
          (LinearMap.ker_eq_bot.mpr hL)
        have hK0 : (0 : ℝ) < K := hKpos
        refine ⟨(2 * K)⁻¹, by positivity, (2 * (K : ℝ))⁻¹, by positivity,
          fun _ t g hg b hb b' hb' => ?_⟩
        have h1 : ‖b - b'‖ ≤ K * ‖L (b - b')‖ := by
          have := hK.le_mul_dist b b'
          simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe, map_sub] using this
        have h2 : ‖g b - g b' - L (b - b')‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖b - b'‖ := hg b hb b' hb'
        have h3 : ‖L (b - b')‖ ≤ ‖g b - g b'‖ + ‖g b - g b' - L (b - b')‖ := by
          have := norm_sub_le (g b - g b') (g b - g b' - L (b - b'))
          simpa using this
        push_cast at h2
        have h4 : ‖b - b'‖ / K ≤ ‖L (b - b')‖ := by
          rw [div_le_iff₀ hK0]; linarith
        have h5 : (2 * (K : ℝ))⁻¹ * ‖b - b'‖ = ‖b - b'‖ / K - (2 * (K : ℝ))⁻¹ * ‖b - b'‖ := by
          field_simp; ring
        linarith
      · exact ⟨1, one_pos, 1, one_pos, fun h => (hL h).elim⟩
    choose δ hδpos k hkpos hk using hchoice
    -- Partition of the regular set of each parametrization into bi-Lipschitz pieces.
    have hpart : ∀ j, ∃ (t : ℕ → Set (Eucl (m + 1))) (κ : ℕ → ℝ),
        (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)) ∧
        Poincare.SimonGMT.Chapter02.areaRegularSet (F j) ⊆ ⋃ i, t i ∧ (∀ i, 0 < κ i) ∧
        ∀ i, ∀ b ∈ t i, ∀ b' ∈ t i, κ i * ‖b - b'‖ ≤ ‖F j b - F j b'‖ := by
      intro j
      set R := Poincare.SimonGMT.Chapter02.areaRegularSet (F j) with hRdef
      have hRmeas : MeasurableSet R := Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet _
      rcases eq_empty_or_nonempty R with hR | hR
      · refine ⟨fun _ => ∅, fun _ => 1, fun _ => MeasurableSet.empty, fun _ => empty_subset _,
          by rw [hR]; exact empty_subset _, fun _ => one_pos, fun i b hb => hb.elim⟩
      obtain ⟨t, A, -, ht, hcov, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) R (fderiv ℝ (F j))
          (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) δ (fun L => (hδpos L).ne')
      refine ⟨fun i => R ∩ t i, fun i => k (A i), fun i => hRmeas.inter (ht i),
        fun i => inter_subset_left, ?_, fun i => hkpos _, ?_⟩
      · intro b hb
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hb)
        exact mem_iUnion.2 ⟨i, hb, hi⟩
      · intro i b hb b' hb'
        obtain ⟨y, hy, hAy⟩ := hactual hR i
        exact hk (A i) (hAy ▸ hy.2) (R ∩ t i) (F j) (happrox i) b hb b' hb'
    choose t κ ht_meas ht_sub ht_cov hκpos hlow using hpart
    have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
    refine ⟨M₀ ∪ ⋃ j, F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)), ?_,
      fun p => F p.unpair.1, fun p => t p.unpair.1 p.unpair.2, fun p => κ p.unpair.1 p.unpair.2,
      fun p => hF p.unpair.1, fun p => ht_meas _ _, fun p => hκpos _ _,
      fun p b hb => ht_sub _ _ hb, fun p => hlow _ _, ?_⟩
    · refine measure_union_null hM₀ (measure_iUnion_null fun j => ?_)
      obtain ⟨K, hK⟩ := hF j
      have := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero hK univ
      rwa [hfin] at this
    · intro x hx
      rcases hcover hx with h0 | h1
      · exact Or.inl (Or.inl h0)
      · obtain ⟨j, b, rfl⟩ := mem_iUnion.1 h1
        by_cases hb : b ∈ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)
        · obtain ⟨i, hi⟩ := mem_iUnion.1 (ht_cov j hb)
          refine Or.inr (mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
          simp only [Nat.unpair_pair]
          exact ⟨b, hi, rfl⟩
        · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, hb⟩, rfl⟩))
  -- Linear area formula: `∫_{L(ℝⁿ)} f dHⁿ = J_L ∫_{ℝⁿ} f ∘ L`.
  have hlinear : ∀ L : Eucl (m + 1) →L[ℝ] Eucl P, Function.Injective L → ∀ f : Eucl P → ℝ,
      ∫ y in (LinearMap.range (L : Eucl (m + 1) →ₗ[ℝ] Eucl P) : Set (Eucl P)), f y
          ∂(μHE[m + 1] : Measure (Eucl P)) =
        (L : Eucl (m + 1) →ₗ[ℝ] Eucl P).normDet *
          ∫ c, f (L c) ∂(volume : Measure (Eucl (m + 1))) := by
    intro L hL f
    have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
    have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume := by
      have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Eucl (m + 1))
      rwa [hfin] at this
    have hmp := Poincare.SimonGMT.Chapter02.measurePreserving_linearMap_normDet_smul
      (L : Eucl (m + 1) →ₗ[ℝ] Eucl P) hL
    rw [hfin, hvol] at hmp
    have hemb : MeasurableEmbedding (L : Eucl (m + 1) →ₗ[ℝ] Eucl P) :=
      (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hL)).measurableEmbedding
    have h := hmp.integral_comp hemb f
    rw [integral_smul_measure, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)] at h
    rw [LinearMap.coe_range]
    simp only [ContinuousLinearMap.coe_coe] at h ⊢
    rw [← h, smul_eq_mul]
  -- The blow-up at a good point of a bi-Lipschitz piece.
  have hblowup : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ), MeasurableSet M →
      IntegrableOn θ M (μHE[m + 1] : Measure (Eucl P)) →
      ∀ (G : Eucl (m + 1) → Eucl P) (K : ℝ≥0), LipschitzWith K G →
      ∀ T : Set (Eucl (m + 1)), MeasurableSet T → ∀ κ : ℝ, 0 < κ →
      (∀ b ∈ T, DifferentiableAt ℝ G b ∧ Function.Injective (fderiv ℝ G b)) →
      (∀ b ∈ T, ∀ b' ∈ T, κ * ‖b - b'‖ ≤ ‖G b - G b'‖) →
      ∀ h : Eucl (m + 1) → ℝ,
      h = (T ∩ G ⁻¹' M).indicator
        (fun c => Poincare.SimonGMT.Chapter02.areaJacobianAt G c * θ (G c)) →
      Integrable h volume →
      ∀ b : Eucl (m + 1), b ∈ T → G b ∈ M →
      (∀ c : ℝ, 0 < c →
        Tendsto (fun r => ⨍ z in closedBall b (c * r), ‖h z - h b‖) (𝓝[>] 0) (𝓝 0)) →
      Tendsto (fun ρ => (∫ z in (M \ G '' T) ∩ closedBall (G b) ρ, |θ z|
        ∂(μHE[m + 1] : Measure (Eucl P))) / ρ ^ (m + 1)) (𝓝[>] 0) (𝓝 0) →
      HasWeightedApproximateTangentSpaceAt (m + 1) M θ (G b)
        (LinearMap.range (fderiv ℝ G b : Eucl (m + 1) →ₗ[ℝ] Eucl P)) := by
    intro M θ hM hθ G K hG T hT κ hκ hreg hlow h hh hint b hbT hbM hleb hdens
    set μ := (μHE[m + 1] : Measure (Eucl P)) with hμ
    set x := G b with hx
    set L := fderiv ℝ G b with hLdef
    obtain ⟨hdiff, hLinj⟩ := hreg b hbT
    have hLd : HasFDerivAt G L b := hdiff.hasFDerivAt
    set A := T ∩ G ⁻¹' M with hAdef
    have hA : MeasurableSet A := hT.inter (hG.continuous.measurable hM)
    have hinjT : InjOn G T := by
      intro b₁ h₁ b₂ h₂ he
      have h12 := hlow b₁ h₁ b₂ h₂
      rw [he, sub_self, norm_zero] at h12
      have h0 : ‖b₁ - b₂‖ ≤ 0 := by nlinarith [norm_nonneg (b₁ - b₂)]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
    have hY : MeasurableSet (G '' T) :=
      hT.image_of_continuousOn_injOn hG.continuous.continuousOn hinjT
    set S := M \ G '' T with hSdef
    have hS : MeasurableSet S := hM.diff hY
    have hGA : G '' A = M ∩ G '' T := by
      rw [hAdef, image_inter_preimage, inter_comm]
    have hMsplit : G '' A ∪ S = M := by
      rw [hGA, hSdef, inter_union_sdiff]
    have hdisj : Disjoint (G '' A) S := by
      rw [hGA, hSdef]
      exact disjoint_sdiff_inter.symm
    have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
    have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume := by
      have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Eucl (m + 1))
      rwa [hfin] at this
    have hηx : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
      intro r hr z
      simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
    -- Change of variables `b' = b + r c` in the parameter space.
    have hDscale : ∀ (Φ : Eucl (m + 1) → ℝ) (r : ℝ), 0 < r →
        ∫ c, Φ (b + r • c) ∂volume = (r ^ (m + 1))⁻¹ * ∫ z, Φ z ∂volume := by
      intro Φ r hr
      rw [Measure.integral_comp_smul volume (fun y => Φ (b + y)) r, integral_add_left_eq_self, hfin,
        abs_of_pos (inv_pos.2 (pow_pos hr _)), smul_eq_mul]
    refine ⟨?_, fun f => ?_⟩
    · rw [LinearMap.finrank_range_of_inj hLinj, hfin]
    obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    obtain ⟨KL, hKLpos, hKL⟩ := (L : Eucl (m + 1) →ₗ[ℝ] Eucl P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hLinj)
    have hKL0 : (0 : ℝ) < KL := hKLpos
    have hLlow : ∀ c, ‖c‖ ≤ KL * ‖L c‖ := fun c => by
      have := hKL.le_mul_dist c 0
      rwa [dist_zero_right, ContinuousLinearMap.coe_coe, map_zero, dist_zero_right] at this
    set κ₀ := min κ (KL : ℝ)⁻¹ with hκ₀def
    have hκ₀ : 0 < κ₀ := lt_min hκ (inv_pos.2 hKL0)
    set R' := R / κ₀ with hR'def
    have hR' : 0 < R' := div_pos hR hκ₀
    have hκ₀R' : κ₀ * R' = R := by rw [hR'def]; field_simp
    -- Continuity of the blown-up parametrization.
    have hcontΔ : ∀ r : ℝ, Continuous fun c => f (blowUpMap x r (G (b + r • c))) := by
      intro r
      have hGc := hG.continuous
      have hfc := f.continuous
      unfold blowUpMap
      fun_prop
    -- Step 1: the blow-up integral as a rescaled integral over `M`.
    have step1 : ∀ r : ℝ, 0 < r → ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂μ =
        (r ^ (m + 1))⁻¹ * ∫ z in M, f (blowUpMap x r z) * θ z ∂μ := by
      intro r hr
      rw [hblow x r hr M (fun y => f y * θ (x + r • y))]
      simp only [hηx r hr.ne']
    -- Step 2: split `M` into the parametrized piece `G '' A` and the rest `S`.
    have hFint : ∀ r : ℝ, IntegrableOn (fun z => f (blowUpMap x r z) * θ z) M μ := by
      intro r
      refine Integrable.bdd_mul (c := C) hθ ?_ (Eventually.of_forall fun z => hC _)
      have hfc := f.continuous
      unfold blowUpMap
      exact (by fun_prop : Continuous fun z => f (r⁻¹ • (z - x))).aestronglyMeasurable
    have step2 : ∀ r : ℝ, ∫ z in M, f (blowUpMap x r z) * θ z ∂μ =
        ∫ z in G '' A, f (blowUpMap x r z) * θ z ∂μ + ∫ z in S, f (blowUpMap x r z) * θ z ∂μ := by
      intro r
      have := setIntegral_union hdisj hS
        ((hFint r).mono_set (hMsplit ▸ subset_union_left))
        ((hFint r).mono_set (hMsplit ▸ subset_union_right))
      rwa [hMsplit] at this
    -- Step 3: the area formula on the injective piece.
    have step3 : ∀ r : ℝ, ∫ z in G '' A, f (blowUpMap x r z) * θ z ∂μ =
        ∫ c, h c * f (blowUpMap x r (G c)) ∂volume := by
      intro r
      have harea := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative hA
        (fun c hc => (hreg c hc.1).1) (fun c hc => (hreg c hc.1).2) (hinjT.mono inter_subset_left)
        (fun z => f (blowUpMap x r z) * θ z)
      rw [hfin, hvol] at harea
      rw [harea, ← integral_indicator hA]
      congr 1
      funext c
      rw [hh]
      by_cases hc : c ∈ A
      · rw [indicator_of_mem hc, indicator_of_mem hc, smul_eq_mul]
        ring
      · rw [indicator_of_notMem hc, indicator_of_notMem hc, zero_mul]
    -- Step 4: rescaling in the parameter space.
    have step4 : ∀ r : ℝ, 0 < r → (r ^ (m + 1))⁻¹ * ∫ c, h c * f (blowUpMap x r (G c)) ∂volume =
        ∫ c, h (b + r • c) * f (blowUpMap x r (G (b + r • c))) ∂volume := by
      intro r hr
      rw [hDscale (fun c => h c * f (blowUpMap x r (G c))) r hr]
    -- Step 5a: the rescaled integrand vanishes for `‖c‖ > R'` (lower bound on `T`).
    have van1 : ∀ r : ℝ, 0 < r → ∀ c : Eucl (m + 1), R' < ‖c‖ →
        h (b + r • c) * f (blowUpMap x r (G (b + r • c))) = 0 := by
      intro r hr c hc
      by_cases hmem : b + r • c ∈ A
      · have hlb := hlow (b + r • c) hmem.1 b hbT
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hlb
        have hfz : f (blowUpMap x r (G (b + r • c))) = 0 := by
          apply hfR
          rw [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, le_inv_mul_iff₀ hr]
          have h1 : κ₀ ≤ κ := min_le_left _ _
          have h2 : R < κ₀ * ‖c‖ := by rw [← hκ₀R']; exact mul_lt_mul_of_pos_left hc hκ₀
          have h3 : κ₀ * ‖c‖ ≤ κ * ‖c‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          nlinarith
        rw [hfz, mul_zero]
      · rw [hh, indicator_of_notMem hmem, zero_mul]
    -- Step 5b: the model integrand vanishes for `‖c‖ > R'`.
    have van2 : ∀ c : Eucl (m + 1), R' < ‖c‖ → f (L c) = 0 := by
      intro c hc
      apply hfR
      have h1 : κ₀ ≤ (KL : ℝ)⁻¹ := min_le_right _ _
      have h2 : R < κ₀ * ‖c‖ := by rw [← hκ₀R']; exact mul_lt_mul_of_pos_left hc hκ₀
      have h3 : κ₀ * ‖c‖ ≤ (KL : ℝ)⁻¹ * ‖c‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h4 : (KL : ℝ)⁻¹ * ‖c‖ ≤ ‖L c‖ := by
        rw [inv_mul_le_iff₀ hKL0]; exact hLlow c
      linarith
    set B : Set (Eucl (m + 1)) := closedBall 0 R' with hBdef
    have hBc : ∀ c, c ∉ B → R' < ‖c‖ := fun c hc => by
      rw [hBdef, mem_closedBall_zero_iff, not_le] at hc; exact hc
    have hBfin : volume B ≠ ∞ := measure_closedBall_lt_top.ne
    -- Integrability of the rescaled density.
    have hhcomp : ∀ r : ℝ, 0 < r → Integrable (fun c => h (b + r • c)) volume := fun r hr =>
      (hint.comp_add_left b).comp_smul hr.ne'
    -- Step 5e: Lebesgue point estimate.
    set ω : ℝ := volume.real (closedBall (0 : Eucl (m + 1)) 1) with hωdef
    have hvolball : ∀ ρ : ℝ, 0 ≤ ρ → volume.real (closedBall b ρ) = ρ ^ (m + 1) * ω := by
      intro ρ hρ
      rw [measureReal_def, Measure.addHaar_closedBall' volume b hρ, hfin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hρ _), hωdef, measureReal_def]
    have step5e :
        Tendsto (fun r : ℝ => ∫ c in B, |h (b + r • c) - h b| ∂volume) (𝓝[>] 0) (𝓝 0) := by
      have hlim := (hleb R' hR').const_mul (R' ^ (m + 1) * ω)
      rw [mul_zero] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      have hρ : 0 ≤ R' * r := by positivity
      have hvpos : 0 < volume.real (closedBall b (R' * r)) := by
        rw [hvolball _ hρ]
        have : 0 < ω := by
          rw [hωdef, measureReal_def]
          exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
            measure_closedBall_lt_top.ne
        positivity
      symm
      calc ∫ c in B, |h (b + r • c) - h b| ∂volume
          = ∫ c, (closedBall b (R' * r)).indicator (fun z => |h z - h b|) (b + r • c) ∂volume := by
            rw [← integral_indicator measurableSet_closedBall]
            congr 1
            funext c
            by_cases hc : c ∈ B
            · have hc' : b + r • c ∈ closedBall b (R' * r) := by
                rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
                  Real.norm_eq_abs, abs_of_pos hr0]
                rw [hBdef, mem_closedBall_zero_iff] at hc
                nlinarith
              rw [indicator_of_mem hc, indicator_of_mem hc']
            · have hc' : b + r • c ∉ closedBall b (R' * r) := by
                rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
                  Real.norm_eq_abs, abs_of_pos hr0, not_le]
                have := hBc c hc
                nlinarith
              rw [indicator_of_notMem hc, indicator_of_notMem hc']
        _ = (r ^ (m + 1))⁻¹ * ∫ z in closedBall b (R' * r), |h z - h b| ∂volume := by
            rw [hDscale _ r hr0, integral_indicator measurableSet_closedBall]
        _ = (r ^ (m + 1))⁻¹ * (volume.real (closedBall b (R' * r)) *
              ⨍ z in closedBall b (R' * r), ‖h z - h b‖) := by
            rw [setAverage_eq, smul_eq_mul, mul_inv_cancel_left₀ hvpos.ne']
            simp only [Real.norm_eq_abs]
        _ = R' ^ (m + 1) * ω * ⨍ z in closedBall b (R' * r), ‖h z - h b‖ := by
            rw [hvolball _ hρ, mul_pow]
            field_simp
    -- Step 5f: the oscillation term tends to zero.
    have step5f : Tendsto (fun r : ℝ => ∫ c in B, (h (b + r • c) - h b) *
        f (blowUpMap x r (G (b + r • c))) ∂volume) (𝓝[>] 0) (𝓝 0) := by
      have hlim := step5e.const_mul C
      rw [mul_zero] at hlim
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun c => ?_)
      · exact (((hhcomp r hr0).integrableOn.sub (integrableOn_const hBfin)).abs).const_mul C
      · rw [norm_mul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
    -- Step 5g: dominated convergence for the blown-up parametrization.
    have step5g : Tendsto (fun r : ℝ => ∫ c in B, f (blowUpMap x r (G (b + r • c))) ∂volume)
        (𝓝[>] 0) (𝓝 (∫ c in B, f (L c) ∂volume)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
        (Eventually.of_forall fun r => (hcontΔ r).aestronglyMeasurable)
        (Eventually.of_forall fun r => Eventually.of_forall fun c => hC _)
        (integrableOn_const hBfin) (Eventually.of_forall fun c => ?_)
      have hd : HasDerivAt (fun t : ℝ => b + t • c) c 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add b
      have hLd' : HasFDerivAt G L (b + (0 : ℝ) • c) := by simpa using hLd
      have hcomp := (hLd'.comp_hasDerivAt (0 : ℝ) hd).tendsto_slope_zero_right
      have hlim : Tendsto (fun t : ℝ => blowUpMap x t (G (b + t • c))) (𝓝[>] 0) (𝓝 (L c)) := by
        refine hcomp.congr' (Eventually.of_forall fun t => ?_)
        simp [blowUpMap, hx]
      exact (f.continuous.tendsto _).comp hlim
    -- Step 5: the parametrized part converges to the model integral.
    have step5 : Tendsto
        (fun r : ℝ => ∫ c, h (b + r • c) * f (blowUpMap x r (G (b + r • c))) ∂volume)
        (𝓝[>] 0) (𝓝 (h b * ∫ c, f (L c) ∂volume)) := by
      have hmodel : ∫ c, f (L c) ∂volume = ∫ c in B, f (L c) ∂volume :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun c hc => van2 c (hBc c hc)).symm
      rw [hmodel]
      have hlim := step5f.add (step5g.const_mul (h b))
      rw [zero_add] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun c hc => van1 r hr0 c (hBc c hc),
        ← integral_const_mul, ← integral_add]
      · congr 1
        funext c
        ring
      · exact (((hhcomp r hr0).integrableOn.sub (integrableOn_const hBfin)).mul_bdd
          (hcontΔ r).aestronglyMeasurable (Eventually.of_forall fun c => hC _))
      · exact (((hcontΔ r).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).const_mul
          (h b))
    -- Step 6: the part of `M` off the parametrized piece has density zero at `x`.
    have step6 : Tendsto (fun r : ℝ => (r ^ (m + 1))⁻¹ * ∫ z in S, f (blowUpMap x r z) * θ z ∂μ)
        (𝓝[>] 0) (𝓝 0) := by
      have hRr : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hc : Continuous fun r : ℝ => R * r := by fun_prop
          have := hc.tendsto 0
          simp only [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hR hr
      have hlim := (hdens.comp hRr).const_mul (C * R ^ (m + 1))
      rw [mul_zero] at hlim
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      have hvanS : ∀ z, z ∉ closedBall x (R * r) → f (blowUpMap x r z) * θ z = 0 := by
        intro z hz
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [hfR, zero_mul]
        rw [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, le_inv_mul_iff₀ hr0]
        nlinarith
      have hcut : ∫ z in S, f (blowUpMap x r z) * θ z ∂μ =
          ∫ z in S ∩ closedBall x (R * r), f (blowUpMap x r z) * θ z ∂μ := by
        rw [inter_comm, ← Measure.restrict_restrict measurableSet_closedBall,
          setIntegral_eq_integral_of_forall_compl_eq_zero hvanS]
      have hθS : IntegrableOn θ (S ∩ closedBall x (R * r)) μ :=
        hθ.mono_set (inter_subset_left.trans sdiff_subset)
      have hbound : ‖∫ z in S ∩ closedBall x (R * r), f (blowUpMap x r z) * θ z ∂μ‖ ≤
          C * ∫ z in S ∩ closedBall x (R * r), |θ z| ∂μ := by
        rw [← integral_const_mul]
        refine norm_integral_le_of_norm_le (hθS.abs.const_mul C) (Eventually.of_forall fun z => ?_)
        rw [norm_mul, Real.norm_eq_abs (θ z)]
        exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
      rw [hcut, norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hr0]
      calc (r ^ (m + 1))⁻¹ * ‖∫ z in S ∩ closedBall x (R * r), f (blowUpMap x r z) * θ z ∂μ‖
          ≤ (r ^ (m + 1))⁻¹ * (C * ∫ z in S ∩ closedBall x (R * r), |θ z| ∂μ) :=
            mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = C * R ^ (m + 1) *
            ((∫ z in S ∩ closedBall x (R * r), |θ z| ∂μ) / (R * r) ^ (m + 1)) := by
            rw [mul_pow]
            field_simp
    -- Step 7: the limit is `θ(x) ∫_{L(ℝⁿ)} f dHⁿ`.
    have step7 : h b * ∫ c, f (L c) ∂volume =
        θ x * ∫ y in (LinearMap.range (L : Eucl (m + 1) →ₗ[ℝ] Eucl P) : Set (Eucl P)), f y ∂μ := by
      rw [hlinear L hLinj f, hh, indicator_of_mem (show b ∈ A from ⟨hbT, hbM⟩),
        Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
      ring
    rw [← step7]
    have hmain := step5.add step6
    rw [add_zero] at hmain
    refine hmain.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    rw [step1 r hr0, step2 r, mul_add, step3 r, step4 r hr0]
  -- The case of a Borel `M` with `θ ∈ L¹(Hⁿ⌞M)`.
  have hcore : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ), MeasurableSet M →
      IntegrableOn θ M (μHE[m + 1] : Measure (Eucl P)) → CountablyRectifiable (m + 1) M →
      ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∃ V : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x V := by
    intro M θ hM hθ hrect
    set μ := (μHE[m + 1] : Measure (Eucl P)) with hμ
    obtain ⟨N, hN, G, T, κ, hGlip, hTmeas, hκ, hreg, hlow, hcov⟩ := hparam M hrect
    have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
    have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume := by
      have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Eucl (m + 1))
      rwa [hfin] at this
    have hp : ∀ p, ∀ᵐ x ∂μ.restrict (M ∩ G p '' T p), ∃ V : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x V := by
      intro p
      obtain ⟨K, hK⟩ := hGlip p
      have hinjT : InjOn (G p) (T p) := by
        intro b₁ h₁ b₂ h₂ he
        have h12 := hlow p b₁ h₁ b₂ h₂
        rw [he, sub_self, norm_zero] at h12
        have h0 : ‖b₁ - b₂‖ ≤ 0 := by nlinarith [norm_nonneg (b₁ - b₂), hκ p]
        exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
      have hY : MeasurableSet (G p '' T p) :=
        (hTmeas p).image_of_continuousOn_injOn hK.continuous.continuousOn hinjT
      set A := T p ∩ G p ⁻¹' M with hAdef
      have hA : MeasurableSet A := (hTmeas p).inter (hK.continuous.measurable hM)
      set h := A.indicator
        (fun c => Poincare.SimonGMT.Chapter02.areaJacobianAt (G p) c * θ (G p c)) with hh
      have hhint : Integrable h volume := by
        rw [hh, integrable_indicator_iff hA]
        have hGA : G p '' A = M ∩ G p '' T p := by
          rw [hAdef, image_inter_preimage, inter_comm]
        have himg :=
          (Poincare.SimonGMT.Chapter02.integrableOn_image_iff_integrableOn_areaJacobian_smul
            hA (fun c hc => (hreg p c hc.1).1) (fun c hc => (hreg p c hc.1).2)
            (hinjT.mono inter_subset_left) θ).1
        rw [hfin, hvol] at himg
        simpa only [smul_eq_mul] using himg (hθ.mono_set (hGA ▸ inter_subset_left))
      -- Lebesgue points of `h`.
      have hleb_ae : ∀ᵐ c ∂(volume : Measure (Eucl (m + 1))), ∀ t : ℝ, 0 < t →
          Tendsto (fun r : ℝ => ⨍ z in closedBall c (t * r), ‖h z - h c‖) (𝓝[>] 0) (𝓝 0) := by
        filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
          hhint.locallyIntegrable 1] with c hc t ht
        refine hc (fun _ => c) (fun r => t * r) ?_ ?_
        · refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have hcont : Continuous fun r : ℝ => t * r := by fun_prop
            have := hcont.tendsto 0
            simp only [mul_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with r hr
            exact mul_pos ht hr
        · filter_upwards [self_mem_nhdsWithin] with r hr
          rw [one_mul]
          exact mem_closedBall_self (mul_pos ht hr).le
      -- Zero density of the rest of `M` at almost every point of the piece.
      have hdens_ae := hdensity θ (M \ G p '' T p) (hM.diff hY) (hθ.mono_set sdiff_subset)
      -- Images of non-Lebesgue points are null.
      set Abad := {c | c ∈ A ∧ ¬ ∀ t : ℝ, 0 < t →
        Tendsto (fun r : ℝ => ⨍ z in closedBall c (t * r), ‖h z - h c‖) (𝓝[>] 0) (𝓝 0)}
        with hAbaddef
      have hAbad : (volume : Measure (Eucl (m + 1))) Abad = 0 :=
        measure_mono_null (fun c hc => hc.2) (ae_iff.1 hleb_ae)
      have hGAbad : μ (G p '' Abad) = 0 := by
        have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
          (m + 1) (hK.lipschitzOnWith (s := Abad))
        rw [hvol, hAbad, mul_zero] at this
        exact le_antisymm this bot_le
      have hbad : ∀ᵐ x ∂μ, x ∉ G p '' Abad := measure_eq_zero_iff_ae_notMem.1 hGAbad
      filter_upwards [ae_restrict_of_ae hbad, ae_restrict_of_ae hdens_ae,
        ae_restrict_mem (hM.inter hY)] with x hx1 hx2 hx3
      obtain ⟨c, hcT, rfl⟩ := hx3.2
      have hcA : c ∈ A := ⟨hcT, hx3.1⟩
      have hcleb : ∀ t : ℝ, 0 < t →
          Tendsto (fun r : ℝ => ⨍ z in closedBall c (t * r), ‖h z - h c‖) (𝓝[>] 0) (𝓝 0) := by
        by_contra hcon
        exact hx1 ⟨c, ⟨hcA, hcon⟩, rfl⟩
      have hcdens := hx2 (fun hmem => hmem.2 ⟨c, hcT, rfl⟩)
      exact ⟨_, hblowup M θ hM hθ (G p) K hK (T p) (hTmeas p) (κ p) (hκ p) (hreg p) (hlow p) h hh
        hhint c hcT hx3.1 hcleb hcdens⟩
    have hMcov : M ⊆ N ∪ ⋃ p, M ∩ G p '' T p := by
      intro x hx
      rcases hcov hx with h0 | h1
      · exact Or.inl h0
      · obtain ⟨p, hp⟩ := mem_iUnion.1 h1
        exact Or.inr (mem_iUnion.2 ⟨p, hx, hp⟩)
    refine ae_restrict_of_ae_restrict_of_subset hMcov ?_
    rw [ae_restrict_union_iff]
    refine ⟨?_, (ae_restrict_iUnion_iff _ _).2 hp⟩
    rw [Measure.restrict_eq_zero.2 hN, ae_zero]
    exact Filter.eventually_bot
  -- Localization to `M ∩ W_q`, `W_q ⊂⊂ U`, and to a Borel subset of full measure.
  intro U M θ hU hMU hMm hrect hpos hint
  set μ := (μHE[m + 1] : Measure (Eucl P)) with hμ
  obtain ⟨W, hWcc, hWcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
  have hloc : ∀ q, ∀ᵐ x ∂μ.restrict (M ∩ W q), ∃ V : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt (m + 1) M θ x V := by
    intro q
    obtain ⟨hWo, hWc, hWU⟩ := hWcc q
    have hMq : NullMeasurableSet (M ∩ W q) μ := hMm.inter hWo.measurableSet.nullMeasurableSet
    obtain ⟨M', hM'sub, hM'meas, hM'ae⟩ := hMq.exists_measurable_subset_ae_eq
    have hθM' : IntegrableOn θ M' μ :=
      (hint _ hWc hWU).mono_set (hM'sub.trans (inter_subset_inter_right _ subset_closure))
    have hcore := hcore M' θ hM'meas hθM' (hrect.mono (hM'sub.trans inter_subset_left))
    rw [← Measure.restrict_congr_set hM'ae]
    filter_upwards [hcore, ae_restrict_mem hM'meas] with x hx hxM'
    obtain ⟨V, hV⟩ := hx
    refine ⟨V, Submission.br_weightedTangent_congr P (m + 1) M' M θ θ x (W q) hWo
      (hM'sub hxM').2 ?_ (Eventually.of_forall fun _ => rfl) rfl V hV⟩
    refine measure_mono_null ?_ (ae_eq_set.1 hM'ae).2
    rintro y ⟨hy | hy, hyW⟩
    · exact absurd (hM'sub hy.1).1 hy.2
    · exact ⟨⟨hy.1, hyW⟩, hy.2⟩
  have hcov : M ⊆ ⋃ q, M ∩ W q := by
    intro x hx
    obtain ⟨i, hi⟩ := hWcov {x} isCompact_singleton (singleton_subset_iff.2 (hMU hx))
    exact mem_iUnion.2 ⟨i, hx, hi rfl⟩
  exact ae_restrict_of_ae_restrict_of_subset hcov ((ae_restrict_iUnion_iff _ _).2 hloc)

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
