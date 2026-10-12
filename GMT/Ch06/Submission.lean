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
