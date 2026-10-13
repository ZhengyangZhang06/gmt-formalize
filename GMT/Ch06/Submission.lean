import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation
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
/-- A coordinate of an `n`-covector is bounded by its Euclidean coefficient norm:
`|α(e_{β(0)}, …, e_{β(n-1)})| ≤ |α|` for every increasing multi-index `β`. -/
theorem Submission.cmb_rb_abs_euclideanCovectorCoordinate_le :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n) (β : SimonMultiIndex n P),
      |euclideanCovectorCoordinate α β| ≤ covectorEuclideanNorm α := by
  intro P n α β
  -- `|c| = √(c²)` and `√` is monotone, so it suffices to bound `c²` by the defining sum.
  rw [covectorEuclideanNorm, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  -- `c²` is the summand of the strictly increasing tuple `β`; every summand is nonnegative.
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun I _ => ?_) (Finset.mem_univ ⇑β))
  · simp only [euclideanCovectorCoordinate, β.strictMono, ↓reduceIte,
      EuclideanSpace.basisFun_apply]
  · exact ite_nonneg (sq_nonneg _) le_rfl

/-- Evaluation bound for an `n`-covector at an arbitrary tuple of vectors:
`|φ(v)| ≤ (∑_β |dx^β(v)|) · |φ|`, summing over the increasing multi-indices `β`. -/
theorem Submission.rpn_moc_abs_covector_apply_le :
    ∀ (P n : ℕ) (φ : Covector (Eucl P) n) (v : Fin n → Eucl P), |φ v| ≤
      (∑ β : SimonMultiIndex n P,
        |wedgeCovectors n (fun j => (EuclideanSpace.proj (β j) : Eucl P →L[ℝ] ℝ)) v|) *
        covectorEuclideanNorm φ := by
  intro P n φ v
  -- Evaluate the coordinate expansion `φ = ∑_β φ(e_β) dx^β` at `v`.
  have hexp := DFunLike.congr_fun (Submission.cmb_covector_eq_sum_coord_smul_wedge P n φ) v
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at hexp
  -- Triangle inequality, then `|φ(e_β)| ≤ |φ|` termwise.
  rw [hexp, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right
    (Submission.cmb_rb_abs_euclideanCovectorCoordinate_le P n φ β) (abs_nonneg _)).trans_eq
    (mul_comm _ _)

/-- Pairing bound for a unit `n`-vector on `ℝ^P`: if `∑_β w(dx^β)² = 1`, then
`|w(θ)| ≤ ∑_β |θ(e_{β(0)}, …, e_{β(n-1)})|`. -/
theorem Submission.rpn_moc_abs_nvector_apply_le :
    ∀ (P n : ℕ) (w : NVector (Eucl P) n) (θ : Covector (Eucl P) n),
      ∑ β : SimonMultiIndex n P, (euclideanNVectorCoordinate w β) ^ 2 = 1 →
      |w θ| ≤ ∑ β : SimonMultiIndex n P, |euclideanCovectorCoordinate θ β| := by
  intro P n w θ hw
  -- Each coordinate `w(dx^β)` is one nonnegative summand of `∑_γ w(dx^γ)² = 1`.
  have hcoord : ∀ β : SimonMultiIndex n P, |euclideanNVectorCoordinate w β| ≤ 1 := by
    intro β
    rw [← sq_le_one_iff_abs_le_one, ← hw]
    exact Finset.single_le_sum (f := fun γ => euclideanNVectorCoordinate w γ ^ 2)
      (fun γ _ => sq_nonneg _) (Finset.mem_univ β)
  -- Expand `θ = ∑_β θ(e_β) dx^β` and apply the linear map `w`.
  have hexp : w θ = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate θ β * euclideanNVectorCoordinate w β := by
    conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P n θ]
    simp only [map_sum, map_smul, smul_eq_mul, euclideanNVectorCoordinate]
  -- Triangle inequality, then `|θ(e_β)| |w(dx^β)| ≤ |θ(e_β)|`.
  rw [hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hcoord β)
/-- A smooth compactly supported `f` with `tsupport f ⊆ U` times a constant `n`-covector `θ`
is a test form in `𝒟ⁿ(U)`: `φ(x) = f(x) θ`. -/
theorem Submission.rpn_moc_exists_testForm_smul :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (f : Eucl P → ℝ) (θ : Covector (Eucl P) n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U →
        ∃ φ : TestFormOn U n, ∀ x, (φ : DifferentialForm (Eucl P) n) x = f x • θ := by
  intro P n U f θ hf hcf hsf
  -- `x ↦ f x • θ` is smooth, compactly supported, and `tsupport (f • θ) ⊆ tsupport f ⊆ U`.
  exact ⟨⟨fun x => f x • θ, ⟨⟨hf.smul contDiff_const, hcf.smul_right⟩,
    (tsupport_smul_subset_left f fun _ => θ).trans hsf⟩⟩, fun _ => rfl⟩
/-- Representation estimate on `W \ K`: if `φ = h • θ` where `|h| ≤ c`, `h = 0` off `W` and on
`K`, and `|ξ(x)(θ)| ≤ c'` for `μ`-a.e. `x`, then `|T φ| ≤ c c' μ(W \ K)`. -/
theorem Submission.rpn_moc_abs_apply_le_mul_measure_diff :
    ∀ (P n : ℕ) (U W K : Set (Eucl P)) (T : GeometricCurrentOn U n) (μ : Measure (Eucl P))
      (ξ : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ ξ → IsOpen W →
      IsCompact K → μ (W \ K) ≠ ∞ → ∀ (θ : Covector (Eucl P) n) (h : Eucl P → ℝ) (c c' : ℝ),
      (∀ x, |h x| ≤ c) → (∀ x, x ∉ W → h x = 0) → (∀ x ∈ K, h x = 0) →
      (∀ᵐ x ∂μ, |ξ x θ| ≤ c') → ∀ φ : TestFormOn U n,
      (∀ x, (φ : DifferentialForm (Eucl P) n) x = h x • θ) →
      |T φ| ≤ c * c' * (μ (W \ K)).toReal := by
  intro P n U W K T μ ξ hrep hW hK hμ θ h c c' hc hW0 hK0 hξ φ hφ
  have hA : MeasurableSet (W \ K) := hW.measurableSet.diff hK.isClosed.measurableSet
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- the integrand is `h x * ξ(x)(θ)`
  have hg : ∀ x, ξ x ((φ : DifferentialForm (Eucl P) n) x) = h x * ξ x θ := fun x => by
    rw [hφ x, map_smul, smul_eq_mul]
  -- `μ`-a.e. domination by `c c' 1_{W \ K}`
  have hbound : ∀ᵐ x ∂μ, ‖ξ x ((φ : DifferentialForm (Eucl P) n) x)‖ ≤
      (W \ K).indicator (fun _ => c * c') x := by
    filter_upwards [hξ] with x hx
    rw [hg x, Real.norm_eq_abs, abs_mul]
    by_cases hxA : x ∈ W \ K
    · rw [Set.indicator_of_mem hxA]
      exact mul_le_mul (hc x) hx (abs_nonneg _) hc0
    · have hx0 : h x = 0 := by
        by_cases hxW : x ∈ W
        · exact hK0 x (not_not.mp fun hxK => hxA ⟨hxW, hxK⟩)
        · exact hW0 x hxW
      rw [Set.indicator_of_notMem hxA, hx0, abs_zero, zero_mul]
  have hG : Integrable ((W \ K).indicator fun _ => c * c') μ :=
    (integrable_indicator_iff hA).2 (integrableOn_const hμ)
  rw [(hrep φ).2, ← Real.norm_eq_abs]
  calc ‖∫ x, ξ x ((φ : DifferentialForm (Eucl P) n) x) ∂μ‖
      ≤ ∫ x, (W \ K).indicator (fun _ => c * c') x ∂μ := norm_integral_le_of_norm_le hG hbound
    _ = c * c' * (μ (W \ K)).toReal := by
      rw [integral_indicator_const _ hA, measureReal_def, smul_eq_mul, mul_comm]

/-- Cut-off estimate for the top-degree form `f θ_L`, `θ_L = L^*(dy¹ ∧ ⋯ ∧ dyⁿ)` (Simon Ch. 6,
proof of Lemma 2.36, display (2)): from the pullback bound (H1) and cut-offs `b = 1` on `L(K)`
with `𝓛ⁿ(spt b)` arbitrarily small (H2), `|T(f θ_L)| ≤ c c' μ(W \ K)`. -/
theorem Submission.rpn_moc_abs_apply_top_form_le :
    ∀ (P m : ℕ) (U W K : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ ξ → IsOpen W →
      W ⊆ U → IsCompact K → μ (W \ K) ≠ ∞ →
      ∀ (L : Eucl P →L[ℝ] Eucl (m + 1)) (f : Eucl P → ℝ) (c c' : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ W →
      (∀ x, |f x| ≤ c) →
      (∀ᵐ x ∂μ, |ξ x (wedgeCovectors (m + 1)
        (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L))| ≤ c') →
      (∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a →
        HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ φ : TestFormOn U (m + 1),
        (∀ x, (φ : DifferentialForm (Eucl P) (m + 1)) x = (f x * a (L x)) •
          wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) →
        |T φ| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))) →
      (∀ δ : ℝ, 0 < δ → ∃ b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧
        HasCompactSupport b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∈ L '' K, b y = 1) ∧
        ((volume : Measure (Eucl (m + 1))) (tsupport b)).toReal ≤ δ) →
      ∀ ζ : TestFormOn U (m + 1), (∀ x, (ζ : DifferentialForm (Eucl P) (m + 1)) x =
        f x • wedgeCovectors (m + 1)
          (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) →
      |T ζ| ≤ c * c' * (μ (W \ K)).toReal := by
  intro P m U W K T μ ξ hrep hW hWU hK hμK L f c c' hf hfc hfW hfle hξ hH1 hH2 ζ hζ
  obtain ⟨C, hC⟩ := hH1
  set θ : Covector (Eucl P) (m + 1) :=
    wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)
  -- Step 1: it suffices to prove `|T ζ| ≤ c c' μ(W \ K) + ε` for every `ε > 0`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Step 2: a cut-off `b` from (H2) for `δ = (ε / (|C| + 1))ⁿ`.
  have hA : 0 < |C| + 1 := by positivity
  obtain ⟨b, hb, hbc, hb01, hbK, hbδ⟩ := hH2 ((ε / (|C| + 1)) ^ (m + 1)) (by positivity)
  -- Step 3: the test form `φ₁ = (f · (b ∘ L)) θ_L`.
  obtain ⟨φ₁, hφ₁⟩ := Submission.rpn_moc_exists_testForm_smul P (m + 1) U
    (fun x => f x * b (L x)) θ (hf.mul (hb.comp L.contDiff))
    (hfc.mul_right (f' := fun x => b (L x))) (tsupport_mul_subset_left.trans (hfW.trans hWU))
  -- Step 4: (H1) with `a = b`, `M = 1` gives `|T φ₁| ≤ |C| 𝓛ⁿ(spt b)^{1/n} ≤ ε`.
  have h₁ : |T φ₁| ≤ ε := by
    set v : ℝ := ((volume (tsupport b)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))
    have hv0 : 0 ≤ v := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hvε : v ≤ ε / (|C| + 1) :=
      calc v ≤ ((ε / (|C| + 1)) ^ (m + 1)) ^ ((1 : ℝ) / ((m : ℝ) + 1)) :=
            Real.rpow_le_rpow ENNReal.toReal_nonneg hbδ (by positivity)
        _ = ε / (|C| + 1) := by
            rw [show (1 : ℝ) / ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ)⁻¹ by push_cast; ring]
            exact Real.pow_rpow_inv_natCast (by positivity) (Nat.succ_ne_zero m)
    calc |T φ₁| ≤ C * 1 * v :=
          hC b hb hbc 1 (fun y => (abs_of_nonneg (hb01 y).1).trans_le (hb01 y).2) φ₁ hφ₁
      _ ≤ |C| * (ε / (|C| + 1)) := by
          rw [mul_one]
          exact mul_le_mul (le_abs_self C) hvε hv0 (abs_nonneg C)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ hA]
          nlinarith [abs_nonneg C]
  -- Step 5: `φ₂ = ζ - φ₁ = h θ_L` with `h = f · (1 - b ∘ L)`.
  have hφ₂ : ∀ x, ((ζ - φ₁ : TestFormOn U (m + 1)) : DifferentialForm (Eucl P) (m + 1)) x =
      (f x * (1 - b (L x))) • θ := by
    intro x
    rw [Submodule.coe_sub, Pi.sub_apply, hζ x, hφ₁ x]
    ext v
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  -- Step 6: `|h| ≤ c`, `h = 0` off `W` and `h = 0` on `K`.
  have hh_le : ∀ x, |f x * (1 - b (L x))| ≤ c := by
    intro x
    have h01 := hb01 (L x)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr h01.2)]
    calc |f x| * (1 - b (L x)) ≤ |f x| * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [h01.1]) (abs_nonneg _)
      _ ≤ c := by rw [mul_one]; exact hfle x
  have hh_W : ∀ x, x ∉ W → f x * (1 - b (L x)) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (hfW hx'), zero_mul]
  have hh_K : ∀ x ∈ K, f x * (1 - b (L x)) = 0 := by
    intro x hx
    rw [hbK (L x) (mem_image_of_mem L hx), sub_self, mul_zero]
  -- Step 7: the remainder bound for `φ₂`.
  have h₂ : |T (ζ - φ₁)| ≤ c * c' * (μ (W \ K)).toReal :=
    Submission.rpn_moc_abs_apply_le_mul_measure_diff P (m + 1) U W K T μ ξ hrep hW hK hμK θ
      (fun x => f x * (1 - b (L x))) c c' hh_le hh_W hh_K hξ (ζ - φ₁) hφ₂
  -- Step 8: `T ζ = T φ₁ + T φ₂` and the triangle inequality.
  have hsplit : T ζ = T φ₁ + T (ζ - φ₁) := by
    rw [show T (ζ - φ₁) = T ζ - T φ₁ from map_sub T.toCurrent ζ φ₁]
    ring
  calc |T ζ| ≤ |T φ₁| + |T (ζ - φ₁)| := by rw [hsplit]; exact abs_add_le _ _
    _ ≤ c * c' * (μ (W \ K)).toReal + ε := by linarith
/-- Polar coordinates for an integrable `g` on `ℝ^{m+1}`, with `σ = (Lᵐ⁺¹).toSphere`:
`∫ g = ∫_{S^m} ∫_0^∞ r^m g(rθ) dr dσ(θ)`.  As in Mathlib's `integral_fun_norm_addHaar`,
`homeomorphUnitSphereProd` carries Lebesgue measure on `ℝ^{m+1} ∖ {0}` to `σ ⊗ volumeIoiPow m`,
Fubini splits the product, and `volumeIoiPow m` is `r^m dr` on `(0, ∞)`. -/
theorem Submission.rpn_pe_integral_eq_polar :
    ∀ (m : ℕ) (g : Eucl (m + 1) → ℝ), Integrable g → ∫ x, g x =
      ∫ θ : sphere (0 : Eucl (m + 1)) 1, (∫ r in Ioi (0 : ℝ), r ^ m * g (r • (θ : Eucl (m + 1))))
        ∂(volume : Measure (Eucl (m + 1))).toSphere := by
  intro m g hg
  -- `Φ = homeomorphUnitSphereProd` is measure preserving onto `σ ⊗ volumeIoiPow m`.
  have hdim : Module.finrank ℝ (Eucl (m + 1)) - 1 = m := by simp
  have hmp : MeasurePreserving (homeomorphUnitSphereProd (Eucl (m + 1)))
      ((volume : Measure (Eucl (m + 1))).comap (↑))
      ((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    have := (volume : Measure (Eucl (m + 1))).measurePreserving_homeomorphUnitSphereProd
    rwa [hdim] at this
  -- `G(θ, r) = g(rθ)` satisfies `G ∘ Φ = g` on `ℝ^{m+1} ∖ {0}`.
  set G : sphere (0 : Eucl (m + 1)) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => g ((p.2 : ℝ) • (p.1 : Eucl (m + 1))) with hG
  have hGΦ : ∀ x : ({0}ᶜ : Set (Eucl (m + 1))), G (homeomorphUnitSphereProd _ x) = g x := by
    intro x
    have hx : ‖(x : Eucl (m + 1))‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    simp only [hG, homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
    rw [smul_smul, mul_inv_cancel₀ hx, one_smul]
  -- Remove the null point `0`, then change variables along `Φ`.
  have h3 : ∫ x, g x = ∫ x : ({0}ᶜ : Set (Eucl (m + 1))), g x
      ∂((volume : Measure (Eucl (m + 1))).comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]
  have h4 : ∫ x : ({0}ᶜ : Set (Eucl (m + 1))), g x
      ∂((volume : Measure (Eucl (m + 1))).comap (↑)) =
      ∫ p, G p ∂((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) G]
    simp only [hGΦ]
  have h5 : Integrable G
      ((volume : Measure (Eucl (m + 1))).toSphere.prod (Measure.volumeIoiPow m)) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : G ∘ homeomorphUnitSphereProd (Eucl (m + 1)) = g ∘ Subtype.val := funext hGΦ
    rw [this, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hg.integrableOn
  -- Fubini, then unfold `volumeIoiPow m = r^m dr` on `(0, ∞)` for each `θ`.
  rw [h3, h4, integral_prod G h5]
  congr 1
  funext θ
  simp only [hG, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ m) • g (a • (θ : Eucl (m + 1)))),
    setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal
/-- The radial integral `∫_{B_ρ(0)} |w|^{1-n} dw = n ω_n ρ` in `ℝⁿ`, `n = m + 1`, `ρ > 0`,
`ω_n = Lⁿ(B_1(0))` (formula (R) of the potential estimate in the proof of Simon Ch. 6, 8.1);
`|w|^{1-n}` is written `(‖w‖ ^ m)⁻¹`.  In polar coordinates (`integrableOn_fun_norm_addHaar`,
`integral_fun_norm_addHaar`) the radial profile `r^{n-1} (r^{n-1})⁻¹` is `1` on `(0, ρ)`: this
gives integrability, and with `1_{B_ρ(0)}(w) = 1_{(-∞, ρ)}(|w|)` the value `n ω_n ρ`. -/
theorem Submission.rpn_pe_inv_norm_pow_ball :
    ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) (ball (0 : Eucl (m + 1)) ρ) ∧ ∫ t in ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ = ((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ρ := by
  intro m ρ hρ
  have hdim : Module.finrank ℝ (Eucl (m + 1)) - 1 = m := by
    rw [finrank_euclideanSpace_fin, Nat.add_sub_cancel]
  constructor
  · -- Integrability: `r ^ m • (r ^ m)⁻¹ = 1` is integrable on `(0, ρ)`.
    rw [integrableOn_fun_norm_addHaar (volume : Measure (Eucl (m + 1)))
      (f := fun r : ℝ => (r ^ m)⁻¹), hdim]
    refine (integrableOn_congr_fun (g := fun _ => (1 : ℝ)) (fun r hr => ?_) measurableSet_Ioo).2
      (integrableOn_const measure_Ioo_lt_top.ne)
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hr.1))
  · -- `h = 1_{(-∞, ρ)} · (r ↦ (r ^ m)⁻¹)`, so `1_{B_ρ(0)}(w) (‖w‖ ^ m)⁻¹ = h ‖w‖`.
    set h : ℝ → ℝ := (Iio ρ).indicator fun r => (r ^ m)⁻¹ with hh
    have hind : (ball (0 : Eucl (m + 1)) ρ).indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) =
        fun t => h ‖t‖ := by
      ext t
      simp [hh, indicator]
    -- For `r > 0`, `r ^ m • h r = 1_{(-∞, ρ)}(r)`, so the radial integral is `L¹((0, ρ)) = ρ`.
    have hrad : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Eucl (m + 1)) - 1) • h y = ρ := by
      rw [hdim, setIntegral_congr_fun measurableSet_Ioi
        (g := (Iio ρ).indicator fun _ => (1 : ℝ)) (fun y hy => ?_)]
      · rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          setIntegral_const, Iio_inter_Ioi, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one, sub_zero]
      · by_cases hy' : y < ρ
        · simp [hh, indicator, hy', mul_inv_cancel₀ (pow_ne_zero m (ne_of_gt (mem_Ioi.1 hy)))]
        · simp [hh, indicator, hy']
    rw [← integral_indicator measurableSet_ball, hind,
      integral_fun_norm_addHaar (volume : Measure (Eucl (m + 1))) h, hrad,
      finrank_euclideanSpace_fin, measureReal_def, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-- Potential estimate over a set of finite measure (Gilbarg–Trudinger, proof of Lemma 7.12, with
the cruder constant `n + 1`): for measurable `S ⊆ ℝⁿ`, `n = m + 1`, with `Lⁿ(S) < ∞`, the kernel
`|w|^{1-n} = (|w|^m)⁻¹` is integrable on `S` and
`∫_S |w|^{1-n} dw ≤ (n + 1) ω^{(n-1)/n} Lⁿ(S)^{1/n}`, `ω = Lⁿ(B_1(0))`.  Split `S` at the radius
`ρ = (Lⁿ(S)/ω)^{1/n}`: the part inside `B_ρ(0)` contributes at most `∫_{B_ρ(0)} |w|^{1-n} = nωρ`,
the part outside at most `ρ^{1-n} Lⁿ(S) = ωρ`. -/
theorem Submission.rpn_pe_inv_norm_pow_set_bound : ∀ (m : ℕ) (S : Set (Eucl (m + 1))), MeasurableSet S → volume S ≠ ⊤ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) S ∧ ∫ t in S, (‖t‖ ^ m)⁻¹ ≤ ((m : ℝ) + 2) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal ^ ((m : ℝ) / ((m : ℝ) + 1)) * (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro m S hS hSfin
  -- Step 1: `f = (‖·‖ ^ m)⁻¹` is measurable and nonnegative.
  have hf_meas : Measurable (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) :=
    (measurable_norm.pow_const m).inv
  have hf_nonneg : ∀ t : Eucl (m + 1), 0 ≤ (‖t‖ ^ m)⁻¹ := fun t => by positivity
  -- Step 2: off `B_ρ(0)`, `f ≤ (ρ ^ m)⁻¹`; as `Lⁿ(S \ B_ρ(0)) < ∞`, `f` is integrable there.
  have hfar_le : ∀ ρ : ℝ, 0 < ρ → ∀ t ∈ S \ ball (0 : Eucl (m + 1)) ρ,
      (‖t‖ ^ m)⁻¹ ≤ (ρ ^ m)⁻¹ := by
    intro ρ hρ t ht
    have hρt : ρ ≤ ‖t‖ := by simpa using ht.2
    exact inv_anti₀ (pow_pos hρ m) (pow_le_pow_left₀ hρ.le hρt m)
  have hfar_fin : ∀ ρ : ℝ, volume (S \ ball (0 : Eucl (m + 1)) ρ) ≠ ⊤ := fun ρ =>
    ne_top_of_le_ne_top hSfin (measure_mono sdiff_subset)
  have hfar_int : ∀ ρ : ℝ, 0 < ρ →
      IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) (S \ ball (0 : Eucl (m + 1)) ρ) := by
    intro ρ hρ
    refine Measure.integrableOn_of_bounded (M := (ρ ^ m)⁻¹) (hfar_fin ρ)
      hf_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (hS.diff measurableSet_ball)] with t ht
    rw [Real.norm_of_nonneg (hf_nonneg t)]
    exact hfar_le ρ hρ t ht
  -- Step 3: with the ball integral, `f` is integrable on `S = (S ∩ B_ρ(0)) ∪ (S \ B_ρ(0))`.
  have hint : ∀ ρ : ℝ, 0 < ρ → IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) S := by
    intro ρ hρ
    have h : IntegrableOn (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹)
        (S ∩ ball (0 : Eucl (m + 1)) ρ ∪ S \ ball (0 : Eucl (m + 1)) ρ) :=
      ((Submission.rpn_pe_inv_norm_pow_ball m ρ hρ).1.mono_set inter_subset_right).union
        (hfar_int ρ hρ)
    rwa [inter_union_sdiff] at h
  refine ⟨hint 1 one_pos, ?_⟩
  set ω := (volume (ball (0 : Eucl (m + 1)) 1)).toReal
  set L := (volume S).toReal
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hL_nonneg : 0 ≤ L := ENNReal.toReal_nonneg
  rcases hL_nonneg.eq_or_lt with hL0 | hL_pos
  · -- Step 4: if `Lⁿ(S) = 0`, both sides vanish.
    have hS0 : volume S = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 hL0.symm).resolve_right hSfin
    rw [Measure.restrict_eq_zero.2 hS0, integral_zero_measure, ← hL0,
      Real.zero_rpow (by positivity), mul_zero]
  · -- Step 5: the radius `ρ = (L / ω) ^ (1/(m+1))`, so that `L = ω ρ ^ (m + 1)`.
    set p : ℝ := 1 / ((m : ℝ) + 1) with hp
    set ρ : ℝ := (L / ω) ^ p with hρ
    have hLω : 0 < L / ω := div_pos hL_pos hω_pos
    have hρ_pos : 0 < ρ := Real.rpow_pos_of_pos hLω p
    have hL_eq : L = ω * ρ ^ (m + 1) := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hLω.le,
        show p * ((m + 1 : ℕ) : ℝ) = 1 by rw [hp]; push_cast; field_simp, Real.rpow_one]
      field_simp
    obtain ⟨hball_int, hball_eq⟩ := Submission.rpn_pe_inv_norm_pow_ball m ρ hρ_pos
    -- Step 6: split `∫_S f` along `B_ρ(0)`.
    rw [← integral_inter_add_sdiff (measurableSet_ball : MeasurableSet (ball (0 : Eucl (m + 1)) ρ))
      (hint ρ hρ_pos)]
    -- Step 7: the near part is at most `∫_{B_ρ(0)} f = (m + 1) ω ρ`.
    have hnear : ∫ t in S ∩ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ ≤ ((m : ℝ) + 1) * ω * ρ := by
      rw [← hball_eq]
      exact setIntegral_mono_set hball_int (ae_of_all _ hf_nonneg)
        (ae_of_all _ fun t ht => ht.2)
    -- Step 8: the far part is at most `Lⁿ(S \ B_ρ(0)) (ρ ^ m)⁻¹ ≤ L (ρ ^ m)⁻¹ = ω ρ`.
    have hfar : ∫ t in S \ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹ ≤ ω * ρ := by
      calc ∫ t in S \ ball (0 : Eucl (m + 1)) ρ, (‖t‖ ^ m)⁻¹
          ≤ ∫ _ in S \ ball (0 : Eucl (m + 1)) ρ, (ρ ^ m)⁻¹ :=
            setIntegral_mono_on (hfar_int ρ hρ_pos) (integrableOn_const (hfar_fin ρ))
              (hS.diff measurableSet_ball) (hfar_le ρ hρ_pos)
        _ = volume.real (S \ ball (0 : Eucl (m + 1)) ρ) * (ρ ^ m)⁻¹ := by
            rw [setIntegral_const, smul_eq_mul]
        _ ≤ L * (ρ ^ m)⁻¹ := by
            gcongr
            exact measureReal_mono sdiff_subset hSfin
        _ = ω * ρ := by
            rw [hL_eq, pow_succ]
            field_simp
    -- Steps 9–10: the sum is `(m + 2) ω ρ = (m + 2) ω ^ (m/(m+1)) L ^ (1/(m+1))`.
    have hωρ : ω * ρ = ω ^ ((m : ℝ) / ((m : ℝ) + 1)) * L ^ p := by
      rw [hρ, Real.div_rpow hL_pos.le hω_pos.le,
        show (m : ℝ) / ((m : ℝ) + 1) = 1 - p by rw [hp]; field_simp; ring,
        Real.rpow_sub hω_pos, Real.rpow_one]
      ring
    calc _ ≤ ((m : ℝ) + 1) * ω * ρ + ω * ρ := add_le_add hnear hfar
      _ = ((m : ℝ) + 2) * (ω * ρ) := by ring
      _ = ((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) * L ^ p := by
        rw [hωρ, mul_assoc]
/-- The kernels `K(w) = w_j / (c|w|^{m+1})` on `ℝ^{m+1}` are locally integrable. This is Step 2 of
the potential estimate (Gilbarg–Trudinger §7.8) that replaces the BV argument of Simon Ch. 6,
Remark 2.35 in the proof of 8.1; there `c = nωₙ`. With `x / 0 = 0`, `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹`
everywhere, and `(|w|^m)⁻¹` is integrable on every ball about `0`
(`Submission.rpn_pe_inv_norm_pow_ball`). -/
theorem Submission.rpn_pe_kernel_locallyIntegrable : ∀ (m : ℕ) (j : Fin (m + 1)) (c : ℝ), LocallyIntegrable (fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1))) := by
  intro m j c
  -- Step 1: `K` is Borel measurable.
  have hmeas : Measurable fun t : Eucl (m + 1) => t j / (c * ‖t‖ ^ (m + 1)) := by fun_prop
  -- Step 2: `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹`. If `c = 0` or `w = 0` the left side is `0`; otherwise
  -- `|w_j| ≤ |w|`.
  have hbound : ∀ t : Eucl (m + 1), ‖t j / (c * ‖t‖ ^ (m + 1))‖ ≤ |c|⁻¹ * (‖t‖ ^ m)⁻¹ := by
    intro t
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    rcases eq_or_ne t 0 with rfl | ht
    · simp only [PiLp.zero_apply, zero_div, norm_zero]
      positivity
    have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht
    rw [norm_div, norm_mul, norm_pow, norm_norm, Real.norm_eq_abs c]
    calc ‖t j‖ / (|c| * ‖t‖ ^ (m + 1)) ≤ ‖t‖ / (|c| * ‖t‖ ^ (m + 1)) := by
          gcongr
          exact PiLp.norm_apply_le t j
      _ = |c|⁻¹ * (‖t‖ ^ m)⁻¹ := by
          field_simp
          ring
  -- Step 3: around `x` use the ball `B_{|x|+1}(0)`, where `(|w|^m)⁻¹` is integrable.
  intro x
  refine ⟨ball (0 : Eucl (m + 1)) (‖x‖ + 1), isOpen_ball.mem_nhds (by simp), ?_⟩
  exact ((Submission.rpn_pe_inv_norm_pow_ball m (‖x‖ + 1) (by positivity)).1.const_mul |c|⁻¹).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ hbound)
/-- Convolution of a locally integrable kernel with a `C^∞` compactly supported function:
`ψ(y) = ∫ K(t) a(y - t) dt` is `C^∞`, and for all `y, v`, `t ↦ K(t) Da(y - t)v` is integrable with
`Dψ(y)v = ∫ K(t) Da(y - t)v dt`.  Here `ψ = K ⋆ a` for the pairing `lsmul ℝ ℝ`, so
`HasCompactSupport.contDiff_convolution_right` gives smoothness, `convolutionExists_right`
applied to the continuous compactly supported `z ↦ Da(z)v` gives integrability, and
`hasFDerivAt_convolution_right` with `convolution_precompR_apply` gives the derivative. -/
theorem Submission.rpn_pe_convolution_contDiff_fderiv :
    ∀ (n : ℕ) (K a : Eucl n → ℝ), LocallyIntegrable K → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a →
      HasCompactSupport a → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t, K t * a (y - t)) ∧
      ∀ y v : Eucl n, Integrable (fun t => K t * fderiv ℝ a (y - t) v) ∧
        fderiv ℝ (fun y => ∫ t, K t * a (y - t)) y v = ∫ t, K t * fderiv ℝ a (y - t) v := by
  intro n K a hK ha hsupp
  -- `ψ = K ⋆ a` for the scalar multiplication pairing (`convolution_lsmul`).
  have hψ : (fun y => ∫ t, K t * a (y - t)) =
      convolution K a (ContinuousLinearMap.lsmul ℝ ℝ) volume := rfl
  -- `a` is `C¹`, so `Da` is continuous.
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast le_top)
  have hDa : Continuous (fderiv ℝ a) := ha.continuous_fderiv (by simp)
  refine ⟨hψ ▸ hsupp.contDiff_convolution_right _ hK ha, fun y v => ⟨?_, ?_⟩⟩
  · -- `z ↦ Da(z)v` is continuous with compact support, so the convolution integrand is integrable.
    exact (hsupp.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hK (hDa.clm_apply continuous_const) y
  · -- `Dψ(y) = (K ⋆[precompR] Da)(y)`, evaluated at `v` by `convolution_precompR_apply`.
    rw [hψ, (hsupp.hasFDerivAt_convolution_right _ hK ha1 y).fderiv,
      convolution_precompR_apply _ hK (hsupp.fderiv (𝕜 := ℝ)) hDa]
    rfl
/-- The fundamental theorem of calculus along a ray: for `a` of class `C¹` with compact support
and `θ ≠ 0`, `∫_{(0,∞)} Da(y - rθ)θ dr = a(y)`.  The function `h(r) = a(y - rθ)` is `C¹` with
`h'(r) = -Da(y - rθ)θ`.  It has compact support because `r ↦ y - rθ` is a closed embedding.
So `HasCompactSupport.integral_Ioi_deriv_eq` gives `∫_{(0,∞)} h' = -h(0) = -a(y)`. -/
theorem Submission.rpn_pe_ray_ftc :
    ∀ (n : ℕ) (a : Eucl n → ℝ), ContDiff ℝ 1 a → HasCompactSupport a → ∀ y θ : Eucl n, θ ≠ 0 →
      ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • θ) θ = a y := by
  intro n a ha hsupp y θ hθ
  -- `h(r) = a(y - rθ)` is `C¹` and compactly supported (the line is a closed embedding as `θ ≠ 0`).
  have hh : ContDiff ℝ 1 (fun r : ℝ => a (y - r • θ)) :=
    ha.comp (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have hhsupp : HasCompactSupport (fun r : ℝ => a (y - r • θ)) :=
    hsupp.comp_isClosedEmbedding
      ((Homeomorph.subLeft y).isClosedEmbedding.comp (isClosedEmbedding_smul_left hθ))
  -- Chain rule: `h'(r) = Da(y - rθ)(-θ)`.
  have hderiv : ∀ r : ℝ, deriv (fun r : ℝ => a (y - r • θ)) r = -fderiv ℝ a (y - r • θ) θ := by
    intro r
    have hline : HasDerivAt (fun r : ℝ => y - r • θ) (-θ) r := by
      simpa using ((hasDerivAt_id r).smul_const θ).const_sub y
    exact (((ha.differentiable one_ne_zero) (y - r • θ)).hasFDerivAt.comp_hasDerivAt r
      hline).deriv.trans (map_neg _ _)
  -- FTC on `(0, ∞)`: `∫_{(0,∞)} h' = -h(0) = -a(y)`.
  have key := HasCompactSupport.integral_Ioi_deriv_eq hh hhsupp 0
  simp_rw [hderiv, integral_neg, zero_smul, sub_zero] at key
  exact neg_injective key

/-- **Representation formula (Gilbarg–Trudinger, §7.8, proof of Lemma 7.14).**  For `n = m + 1`,
`ω = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)`, the kernels `K_j(t) = t_j / (n ω |t|ⁿ)` satisfy
`∑_j ∫ K_j(t) ∂_j a(y - t) dt = a(y)`.  Expanding `t` in the standard basis, the sum is `∫ G` with
`G(t) = Da(y - t) t / (n ω |t|ⁿ)`.  In polar coordinates `r^m G(rθ) = Da(y - rθ) θ / (n ω)`, so
each ray integral is `a(y) / (n ω)` (fundamental theorem of calculus along the ray), and the unit
sphere has measure `n ω`. -/
theorem Submission.rpn_pe_kernel_representation : ∀ (m : ℕ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ y : Eucl (m + 1), ∑ j : Fin (m + 1), ∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) = a y := by
  intro m a ha hca y
  -- Step 1: `ω = Lⁿ(B₁(0)) ∈ (0, ∞)`, so `c = (m + 1) ω > 0`.
  set ω : ℝ := (volume (ball (0 : Eucl (m + 1)) 1)).toReal with hω
  set c : ℝ := ((m : ℝ) + 1) * ω with hc
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hc_pos : 0 < c := by positivity
  -- Step 2: `K_j` is locally integrable, so `t ↦ K_j(t) ∂_j a(y - t)` is integrable.
  have hint : ∀ j : Fin (m + 1), Integrable fun t : Eucl (m + 1) =>
      t j / (c * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ)) := fun j =>
    ((Submission.rpn_pe_convolution_contDiff_fderiv (m + 1) _ a
      (Submission.rpn_pe_kernel_locallyIntegrable m j c) ha hca).2 y _).1
  -- Step 3: move the sum inside the integral.
  rw [← integral_finsetSum _ fun j _ => hint j]
  -- Step 4: `Λ v = ∑_j v_j Λ e_j`, so `∑_j K_j(t) ∂_j a(y - t) = G(t)`.
  have hexp : ∀ (Λ : Eucl (m + 1) →L[ℝ] ℝ) (v : Eucl (m + 1)),
      Λ v = ∑ j : Fin (m + 1), v j * Λ (EuclideanSpace.single j (1 : ℝ)) := by
    intro Λ v
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr v]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  set G : Eucl (m + 1) → ℝ := fun t => fderiv ℝ a (y - t) t / (c * ‖t‖ ^ (m + 1)) with hG
  have hsum : (fun t : Eucl (m + 1) => ∑ j : Fin (m + 1),
      t j / (c * ‖t‖ ^ (m + 1)) * fderiv ℝ a (y - t) (EuclideanSpace.single j (1 : ℝ))) = G := by
    funext t
    simp only [hG]
    rw [hexp (fderiv ℝ a (y - t)) t, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- Step 5: `G` is integrable and the left side is `∫ G`.
  have hG_int : Integrable G := by
    rw [← hsum]
    exact integrable_finsetSum _ fun j _ => hint j
  rw [hsum]
  -- Step 6: polar coordinates.
  rw [Submission.rpn_pe_integral_eq_polar m G hG_int]
  -- Step 7: for `|θ| = 1` and `r > 0`, `r^m G(rθ) = Da(y - rθ) θ / c`; integrate along the ray.
  have hray : ∀ θ : sphere (0 : Eucl (m + 1)) 1,
      ∫ r in Ioi (0 : ℝ), r ^ m * G (r • (θ : Eucl (m + 1))) = a y / c := by
    intro θ
    calc ∫ r in Ioi (0 : ℝ), r ^ m * G (r • (θ : Eucl (m + 1)))
        = ∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • (θ : Eucl (m + 1))) θ / c := by
          refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
          simp only [hG]
          rw [norm_smul, norm_eq_of_mem_sphere, mul_one, Real.norm_of_nonneg hr.le, map_smul,
            smul_eq_mul]
          field_simp
          ring
      _ = (∫ r in Ioi (0 : ℝ), fderiv ℝ a (y - r • (θ : Eucl (m + 1))) θ) / c := integral_div c _
      _ = a y / c := by
          rw [Submission.rpn_pe_ray_ftc (m + 1) a (ha.of_le (by norm_cast)) hca y θ
            (ne_zero_of_mem_unit_sphere θ)]
  -- Step 8: the inner integral is the constant `a(y) / c`, and `σ(S) = (m + 1) ω = c`.
  rw [integral_congr_ae (Eventually.of_forall hray), integral_const, smul_eq_mul,
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, measureReal_def, ← hω,
    show ((m + 1 : ℕ) : ℝ) * ω = c by rw [hc]; push_cast; ring, mul_div_cancel₀ _ hc_pos.ne']

/-- Sup bound for the kernel potentials (Step 5 of the potential estimate).  With
`ω = Lⁿ(B₁(0))`, `c = (m + 1) ω` and `K_j(t) = t_j / (c |t|^{m+1})`, every compactly supported
`a` with `|a| ≤ M` satisfies `|∫ K_j(t) a(y - t) dt| ≤ C M Lⁿ(spt a)^{1/(m+1)}` with
`C = (m + 2) ω^{m/(m+1)} / c`.  Proof: `|K_j(t) a(y - t)| ≤ (M / c) 1_{S_y}(t) |t|^{-m}` on
`S_y = {t : y - t ∈ spt a}`, a translate of `spt a`; integrate and apply
`rpn_pe_inv_norm_pow_set_bound` to `S_y`.  No measurability of `a` is needed. -/
theorem Submission.rpn_pe_kernel_sup_bound : ∀ m : ℕ, ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ (j : Fin (m + 1)) (y : Eucl (m + 1)), |∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1)) * a (y - t)| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro m
  set ω : ℝ := (volume (ball (0 : Eucl (m + 1)) 1)).toReal
  set c : ℝ := ((m : ℝ) + 1) * ω
  have hω_pos : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Eucl (m + 1)) one_pos).ne'
      measure_ball_lt_top.ne
  have hc_pos : 0 < c := mul_pos (by positivity) hω_pos
  refine ⟨((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) / c, ?_⟩
  intro a ha M hM j y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- The translated support `S_y = {t : y - t ∈ spt a}` has the measure of `spt a`.
  set S : Set (Eucl (m + 1)) := tsupport a
  set Sy : Set (Eucl (m + 1)) := (fun t => y - t) ⁻¹' S
  have hSy_meas : MeasurableSet Sy :=
    ((isClosed_tsupport a).preimage (continuous_const.sub continuous_id)).measurableSet
  have hvol : volume Sy = volume S :=
    (Measure.measurePreserving_sub_left volume y).measure_preimage
      (isClosed_tsupport a).measurableSet.nullMeasurableSet
  have hSy_fin : volume Sy ≠ ⊤ := by
    rw [hvol]
    exact (IsCompact.measure_lt_top ha).ne
  obtain ⟨hint, hbound⟩ := Submission.rpn_pe_inv_norm_pow_set_bound m Sy hSy_meas hSy_fin
  rw [hvol] at hbound
  -- Pointwise domination by `(M / c) 1_{S_y}(t) |t|^{-m}`.
  have hg_int : Integrable (fun t => M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t) :=
    ((integrable_indicator_iff hSy_meas).2 hint).const_mul (M / c)
  have hdom : ∀ t : Eucl (m + 1), ‖t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)‖ ≤
      M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t := by
    intro t
    by_cases ht : t ∈ Sy
    · rw [indicator_of_mem ht, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hK : |t j / (c * ‖t‖ ^ (m + 1))| ≤ (‖t‖ ^ m)⁻¹ / c := by
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * ‖t‖ ^ (m + 1))]
        rcases (norm_nonneg t).eq_or_lt with h0 | hpos
        · rw [← h0, zero_pow (Nat.succ_ne_zero m), mul_zero, div_zero]
          positivity
        · rw [div_le_iff₀ (by positivity)]
          calc |t j| = ‖t j‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖t‖ := PiLp.norm_apply_le t j
            _ = (‖t‖ ^ m)⁻¹ / c * (c * ‖t‖ ^ (m + 1)) := by
              field_simp
              ring
      calc |t j / (c * ‖t‖ ^ (m + 1))| * |a (y - t)| ≤ (‖t‖ ^ m)⁻¹ / c * M :=
            mul_le_mul hK (hM _) (abs_nonneg _) (by positivity)
        _ = M / c * (‖t‖ ^ m)⁻¹ := by ring
    · have hyt : y - t ∉ tsupport a := ht
      rw [indicator_of_notMem ht, image_eq_zero_of_notMem_tsupport hyt]
      simp
  calc |∫ t, t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)|
      = ‖∫ t, t j / (c * ‖t‖ ^ (m + 1)) * a (y - t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, M / c * Sy.indicator (fun t : Eucl (m + 1) => (‖t‖ ^ m)⁻¹) t :=
        norm_integral_le_of_norm_le hg_int (Eventually.of_forall hdom)
    _ = M / c * ∫ t in Sy, (‖t‖ ^ m)⁻¹ := by
        rw [integral_const_mul, integral_indicator hSy_meas]
    _ ≤ M / c * (((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) *
          (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hbound (div_nonneg hM0 hc_pos.le)
    _ = ((m : ℝ) + 2) * ω ^ ((m : ℝ) / ((m : ℝ) + 1)) / c * M *
          (volume S).toReal ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
        ring

/-- **Potential estimate (replaces Simon Ch. 6, Remark 2.35; Gilbarg–Trudinger, Lemma 7.14 and
§7.8).**  For `n = m + 1`, `ω_n = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)` with `|a| ≤ M`, the potentials
`ψ_j(y) = ∫ K_j(t) a(y - t) dt` of the kernels `K_j(t) = t_j / (n ω_n |t|ⁿ)` are `C^∞`, satisfy
`∑_j ∂_j ψ_j = a` and `|ψ_j| ≤ C M Lⁿ(spt a)^{1/n}` with `C` depending only on `m`.  The kernels
are locally integrable, so `ψ_j` is smooth with `∂_k ψ_j = K_j ⋆ ∂_k a`; summing `∂_j ψ_j` over
`j` gives `a` by the representation formula, and the bound is the kernel sup estimate. -/
theorem Submission.rpn_potential_estimate : ∀ m : ℕ, ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∃ ψ : Fin (m + 1) → Eucl (m + 1) → ℝ, (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ j)) ∧ (∀ y, ∑ j : Fin (m + 1), fderiv ℝ (ψ j) y (EuclideanSpace.single j (1 : ℝ)) = a y) ∧ ∀ j y, |ψ j y| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  have hli := @Submission.rpn_pe_kernel_locallyIntegrable
  have hconv := @Submission.rpn_pe_convolution_contDiff_fderiv
  have hrep := @Submission.rpn_pe_kernel_representation
  have hsup := @Submission.rpn_pe_kernel_sup_bound
  intro m
  -- Step 1: the constant `C` of the kernel sup bound, chosen before `a` and `M`.
  obtain ⟨C, hC⟩ := hsup m
  refine ⟨C, fun a ha hca M hM => ?_⟩
  -- Steps 2–3: `K_j(t) = t_j / (n ω_n |t|ⁿ)` is locally integrable, so `ψ_j = K_j ⋆ a` is `C^∞`
  -- and `Dψ_j(y) v = ∫ K_j(t) Da(y - t) v dt`.
  have hψ := fun j : Fin (m + 1) => hconv (m + 1)
    (fun t : Eucl (m + 1) =>
      t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal * ‖t‖ ^ (m + 1))) a
    (hli m j (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal)) ha hca
  -- Step 5: `|ψ_j(y)| ≤ C M Lⁿ(spt a)^{1/n}` is the kernel sup bound.
  refine ⟨fun j y => ∫ t, t j / (((m : ℝ) + 1) * (volume (ball (0 : Eucl (m + 1)) 1)).toReal *
      ‖t‖ ^ (m + 1)) * a (y - t), fun j => (hψ j).1, fun y => ?_, fun j y => hC a hca M hM j y⟩
  -- Step 4: `∑_j ∂_j ψ_j(y) = ∑_j ∫ K_j(t) ∂_j a(y - t) dt = a(y)` (representation formula).
  rw [← hrep m a ha hca y]
  exact Finset.sum_congr rfl fun j _ => ((hψ j).2 y (EuclideanSpace.single j 1)).2
/-- The wedge `γ ∧ β₀ ∧ ⋯ ∧ β_{m-1}` is linear in its first factor `γ`. -/
theorem Submission.rpn_pfd_wedge_cons_isLinearMap :
    ∀ (P m : ℕ) (β : Fin m → (Eucl P →L[ℝ] ℝ)), IsLinearMap ℝ (fun γ : Eucl P →L[ℝ] ℝ =>
      wedgeCovectors (m + 1) (Fin.cons γ β : Fin (m + 1) → (Eucl P →L[ℝ] ℝ))) := by
  intro P m β
  -- Unfolding, `wedgeCovectors (m + 1) (Fin.cons γ β)` is
  -- `alternatizeUncurryFin (γ.smulRight (wedgeCovectors m β))`; `alternatizeUncurryFin` is
  -- linear, so it remains to see that `γ ↦ γ.smulRight (wedgeCovectors m β)` is linear.
  constructor
  · intro γ δ
    simp only [wedgeCovectors, Fin.cons_zero, Fin.tail_cons]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFin_add]
    congr 1
    ext v w
    simp [add_smul]
  · intro c γ
    simp only [wedgeCovectors, Fin.cons_zero, Fin.tail_cons]
    rw [← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    congr 1
    ext v w
    simp [mul_smul]
/-- Sign lemma for wedges of one-covectors: moving the factor `l j` to the front costs
`(-1)^j`, while putting another factor `l i` (`i ≠ j`) in front repeats a factor. -/
theorem Submission.rpn_pfd_wedge_cons_succAbove_sign :
    ∀ (P m : ℕ) (l : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) (j : Fin (m + 1)),
      wedgeCovectors (m + 1) (Fin.cons (l j) (fun k => l (j.succAbove k)) :
          Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = ((-1 : ℝ) ^ (j : ℕ)) • wedgeCovectors (m + 1) l ∧
        ∀ i : Fin (m + 1), i ≠ j → wedgeCovectors (m + 1) (Fin.cons (l i)
          (fun k => l (j.succAbove k)) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) = 0 := by
  intro P m l j
  refine ⟨?_, fun i hij => ?_⟩
  · -- `Fin.cons (l j) (l ∘ j.succAbove) = l ∘ σ` with `σ = (cycleRange j)⁻¹`, so its value
    -- matrix is that of `l` with rows permuted by `σ`.
    have hσ : (Fin.cons (l j) (fun k => l (j.succAbove k)) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) =
        fun a => l (j.cycleRange.symm a) := by
      funext a
      cases a using Fin.cases <;> simp
    ext v
    have h := Matrix.det_permute j.cycleRange.symm (Matrix.of fun a b => l a (v b))
    rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange] at h
    push_cast at h
    rw [hσ, ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_det,
      wedgeCovectors_apply_det, smul_eq_mul, ← h]
    rfl
  · -- `i = j.succAbove k` for some `k`, so rows `0` and `k.succ` of the value matrix coincide.
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    ext v
    rw [wedgeCovectors_apply_det, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    refine Matrix.det_zero_of_row_eq (Fin.succ_ne_zero k).symm ?_
    funext b
    simp [hk]
/-- `d(∑ⱼ gⱼ θⱼ) = ∑ⱼ dgⱼ ∧ θⱼ` for constant covectors `θⱼ = βⱼ,₀ ∧ ⋯ ∧ βⱼ,ₘ₋₁` (Simon Ch. 6,
(1.11), p. 134: `d(a dx^α) = da ∧ dx^α`, with general constant one-covectors `βⱼ` in place of the
coordinate differentials).  `extDeriv Φ x = Alt (DΦ(x))` only needs `gⱼ` differentiable at `x`. -/
theorem Submission.rpn_pfd_extDeriv_sum_smul_wedge : ∀ (P m : ℕ) (ι : Type) [Fintype ι] (g : ι → Eucl P → ℝ) (β : ι → Fin m → (Eucl P →L[ℝ] ℝ)) (x : Eucl P), (∀ j, DifferentiableAt ℝ (g j) x) → extDeriv (fun z => ∑ j : ι, g j z • wedgeCovectors m (β j)) x = ∑ j : ι, wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ (g j) x) (β j) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) := by
  intro P m ι _ g β x hg
  -- `z ↦ ∑ⱼ gⱼ(z) • θⱼ` has derivative `∑ⱼ Dgⱼ(x).smulRight θⱼ` at `x`.
  have hD : HasFDerivAt (fun z => ∑ j : ι, g j z • wedgeCovectors m (β j))
      (∑ j : ι, (fderiv ℝ (g j) x).smulRight (wedgeCovectors m (β j))) x :=
    HasFDerivAt.fun_sum fun j _ => (hg j).hasFDerivAt.smul_const (wedgeCovectors m (β j))
  -- `extDeriv Φ x = Alt (fderiv Φ x)`, and `Alt` is linear, so it commutes with the sum.
  rw [extDeriv, hD.fderiv, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_sum]
  -- Each term is the successor case of `wedgeCovectors` at `Fin.cons (Dgⱼ(x)) βⱼ`.
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, wedgeCovectors, Fin.cons_zero,
    Fin.tail_cons]

/-- One term of the divergence identity of Simon Ch. 6, 2.35 (`dω = div a dx¹ ∧ ⋯ ∧ dxⁿ`),
pulled back by a linear `L : ℝ^P → ℝ^{m+1}`: for `λᵢ = yⁱ ∘ L` and `ℓ ∈ (ℝ^{m+1})*`,
`(ℓ ∘ L) ∧ λ₀ ∧ ⋯ ∧ λ̂ⱼ ∧ ⋯ ∧ λₘ = (-1)ʲ ℓ(eⱼ) λ₀ ∧ ⋯ ∧ λₘ`.  Expand `ℓ ∘ L = ∑ᵢ ℓ(eᵢ) λᵢ`; the
wedge is linear in its first factor, and by the sign lemma only the term `i = j` survives. -/
theorem Submission.rpn_pfd_wedge_cons_comp_succAbove :
    ∀ (P m : ℕ) (L : Eucl P →L[ℝ] Eucl (m + 1)) (ℓ : Eucl (m + 1) →L[ℝ] ℝ) (j : Fin (m + 1)),
      wedgeCovectors (m + 1) (Fin.cons (ℓ.comp L)
          (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) :
          Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) =
        ((-1 : ℝ) ^ (j : ℕ) * ℓ (EuclideanSpace.single j (1 : ℝ))) •
          wedgeCovectors (m + 1)
            (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) := by
  intro P m L ℓ j
  -- `λᵢ = yⁱ ∘ L`; `Λ γ = γ ∧ λ_{j.succAbove 0} ∧ ⋯ ∧ λ_{j.succAbove (m - 1)}` is linear in `γ`.
  let lam : Fin (m + 1) → (Eucl P →L[ℝ] ℝ) := fun i =>
    (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L
  let Λ := IsLinearMap.mk' _
    (Submission.rpn_pfd_wedge_cons_isLinearMap P m fun k => lam (j.succAbove k))
  have hΛ : ∀ γ, Λ γ = wedgeCovectors (m + 1)
      (Fin.cons γ fun k => lam (j.succAbove k) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) :=
    fun _ => rfl
  -- `ℓ ∘ L = ∑ᵢ ℓ(eᵢ) λᵢ`: expand `L v` in the standard basis of `ℝ^{m+1}`.
  have hexp : ℓ.comp L = ∑ i, ℓ (EuclideanSpace.single i (1 : ℝ)) • lam i := by
    ext v
    have hv := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr (L v)
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hv
    conv_lhs => rw [ContinuousLinearMap.comp_apply, ← hv]
    simp [lam, mul_comm]
  -- Sign lemma for `l = λ`: the term `i = j` is `(-1)ʲ λ₀ ∧ ⋯ ∧ λₘ`, the others vanish.
  obtain ⟨hj, hne⟩ := Submission.rpn_pfd_wedge_cons_succAbove_sign P m lam j
  calc wedgeCovectors (m + 1)
        (Fin.cons (ℓ.comp L) fun k => lam (j.succAbove k) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ))
      = Λ (∑ i, ℓ (EuclideanSpace.single i (1 : ℝ)) • lam i) := by rw [hΛ, hexp]
    _ = ∑ i, ℓ (EuclideanSpace.single i (1 : ℝ)) • Λ (lam i) := by
        simp only [map_sum, map_smul]
    _ = ℓ (EuclideanSpace.single j (1 : ℝ)) • Λ (lam j) := by
        refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (Finset.mem_univ j) h)
        rw [hΛ, hne i hij, smul_zero]
    _ = ((-1 : ℝ) ^ (j : ℕ) * ℓ (EuclideanSpace.single j (1 : ℝ))) •
          wedgeCovectors (m + 1) lam := by
        rw [hΛ, hj, smul_smul, mul_comm]

/-- Exterior derivative of the pulled-back potential form (Simon Ch. 6, 1.14 and the divergence
identity `dψ̂ = (div ψ) dy` of Remark 2.35).  For `λᵢ = yⁱ ∘ L`, `θⱼ = λ₀ ∧ ⋯ ∧ λ̂ⱼ ∧ ⋯ ∧ λₘ` and
`Φ(z) = ∑ⱼ (-1)ʲ f(z) ψⱼ(Lz) θⱼ`,
`dΦ(x) = f(x) (∑ⱼ ∂ⱼψⱼ(Lx)) λ₀ ∧ ⋯ ∧ λₘ + ∑ⱼ (-1)ʲ ψⱼ(Lx) Df(x) ∧ θⱼ`. -/
theorem Submission.rpn_extDeriv_potential_form :
    ∀ (P m : ℕ) (L : Eucl P →L[ℝ] Eucl (m + 1)) (f : Eucl P → ℝ)
      (ψ : Fin (m + 1) → Eucl (m + 1) → ℝ) (x : Eucl P),
      DifferentiableAt ℝ f x → (∀ j, DifferentiableAt ℝ (ψ j) (L x)) →
      extDeriv (fun z => ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) •
          wedgeCovectors m
            (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L)) x =
        (f x * ∑ j : Fin (m + 1), fderiv ℝ (ψ j) (L x) (EuclideanSpace.single j (1 : ℝ))) •
            wedgeCovectors (m + 1)
              (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) +
          ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) •
            wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ f x)
              (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) :
              Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) := by
  intro P m L f ψ x hf hψ
  -- Chain and product rules: `gⱼ(z) = (-1)ʲ f(z) ψⱼ(Lz)` has derivative
  -- `(-1)ʲ (f(x) Dψⱼ(Lx) ∘ L + ψⱼ(Lx) Df(x))` at `x`.
  have hg : ∀ j : Fin (m + 1), HasFDerivAt (fun z => (-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z)))
      ((-1 : ℝ) ^ (j : ℕ) • (f x • (fderiv ℝ (ψ j) (L x)).comp L + ψ j (L x) • fderiv ℝ f x))
      x :=
    fun j => (hf.hasFDerivAt.fun_mul ((hψ j).hasFDerivAt.comp x L.hasFDerivAt)).const_mul _
  -- `dΦ(x) = ∑ⱼ Dgⱼ(x) ∧ θⱼ`; compare with the right side term by term.
  rw [Submission.rpn_pfd_extDeriv_sum_smul_wedge P m (Fin (m + 1))
      (fun j z => (-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z)))
      (fun j i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) x
      fun j => (hg j).differentiableAt,
    Finset.mul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- The wedge is linear in its first factor, the `Dψⱼ(Lx) ∘ L` part is
  -- `(-1)ʲ ∂ⱼψⱼ(Lx) λ₀ ∧ ⋯ ∧ λₘ`, and `(-1)ʲ (-1)ʲ = 1`.
  have hlin := Submission.rpn_pfd_wedge_cons_isLinearMap P m
    fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L
  have hsq : (-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [(hg j).fderiv, hlin.map_smul, hlin.map_add, hlin.map_smul, hlin.map_smul,
    Submission.rpn_pfd_wedge_cons_comp_succAbove P m L (fderiv ℝ (ψ j) (L x)) j, smul_add,
    smul_smul, smul_smul, smul_smul]
  congr 2
  linear_combination (f x * fderiv ℝ (ψ j) (L x) (EuclideanSpace.single j (1 : ℝ))) * hsq
/-- The Euclidean coefficient norm of an `n`-covector on `ℝ^P` is at most `√(P^n)` times its
operator norm: each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` (`b` the standard
orthonormal basis) is bounded by `‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.fiw_ims_sc_covectorNorm_le_opNorm :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
  intro P n α
  -- Every coefficient is at most `‖α‖`, since the standard basis vectors are unit vectors.
  have hcoef : ∀ I : Fin n → Fin P,
      |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
    intro I
    have h := ContinuousAlternatingMap.le_opNorm α
      (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
    simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
      Real.norm_eq_abs] at h
    exact h
  rw [covectorEuclideanNorm]
  calc Real.sqrt _ ≤ Real.sqrt ((P : ℝ) ^ n * ‖α‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        -- The sum has `P ^ n` terms, each at most `‖α‖ ^ 2`.
        calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro I _
              split_ifs
              · rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) (hcoef I) 2
              · positivity
          _ = (P : ℝ) ^ n * ‖α‖ ^ 2 := by simp [Finset.card_univ]
    _ = Real.sqrt ((P : ℝ) ^ n) * ‖α‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
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

/-- Mass estimate with the operator norm: if `M_W(T) ≤ B` and `ω` is supported in `W` with
`‖ω(x)‖ ≤ C` everywhere (operator norm), then `|T(ω)| ≤ P^n · B · C`, because the Euclidean
coefficient norm is at most `√(P^n) · ‖·‖ ≤ P^n · ‖·‖`. -/
theorem Submission.rpn_abs_apply_le_opNorm_mul_massOn :
    ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B C : ℝ),
      0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, ‖(ω : DifferentialForm (Eucl P) n) x‖ ≤ C) →
      |T ω| ≤ (P : ℝ) ^ n * B * C := by
  intro P n U W T ω B C hB hM hW hC
  -- `C ≥ 0`, by evaluating the pointwise bound at `0`.
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- `√(P^n) ≤ P^n`, since `P^n` is a natural number.
  have hsqrt : Real.sqrt ((P : ℝ) ^ n) ≤ (P : ℝ) ^ n := by
    rw [Real.sqrt_le_self_iff]
    rcases (P ^ n).eq_zero_or_pos with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  -- Hence the Euclidean coefficient norm of `ω(x)` is at most `P^n · C`.
  have hE : ∀ x,
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ (P : ℝ) ^ n * C := by
    intro x
    calc covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)
        ≤ Real.sqrt ((P : ℝ) ^ n) * ‖(ω : DifferentialForm (Eucl P) n) x‖ :=
          Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
      _ ≤ (P : ℝ) ^ n * C := mul_le_mul hsqrt (hC x) (norm_nonneg _) (by positivity)
  calc |T ω| ≤ B * ((P : ℝ) ^ n * C) :=
        Submission.cmb_abs_apply_le_of_massOn_le P n U W T ω B _ hB hM hW hE
    _ = (P : ℝ) ^ n * B * C := by ring

/-- Currents of degree `n > P` in `ℝ^P` vanish (step 1 of the proof of Simon Ch. 6, 6.2): any `n`
vectors of `ℝ^P` are linearly dependent, so every `n`-covector is `0`, every test form is `0`, and
`X(ω) = X(0) = 0`. -/
theorem Submission.br_la_apply_eq_zero_of_lt_degree :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U n), P < n →
      ∀ ω : TestFormOn U n, X ω = 0 := by
  intro P n U X hPn ω
  -- `ω(x)(v) = 0`: `v` is linearly dependent, since otherwise `n ≤ finrank ℝ^P = P`.
  have hω : ω = 0 := by
    apply Subtype.ext
    funext x
    ext v
    refine AlternatingMap.map_linearDependent
      ((ω : DifferentialForm (Eucl P) n) x).toAlternatingMap v fun hv => ?_
    have hle := hv.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hle
    exact absurd hle (Nat.not_le.2 hPn)
  change X.toCurrent ω = 0
  rw [hω, map_zero]
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
/-- Simon Ch. 6, the estimate behind Lemma 2.36 (via Remark 2.35), for a linear map
`L : ℝ^P → ℝⁿ`, `n = m + 1`: if `M_W(T), M_W(∂T) < ∞` and `f` is a smooth compactly supported
cutoff with `tsupport f ⊆ W`, then every test form `φ = f · (a ∘ L) · L^*dy` satisfies
`|T(φ)| ≤ C · M · Lⁿ(spt a)^{1/n}` whenever `|a| ≤ M`, with `C` independent of `a`, `M`, `φ`.

Write `a = ∑ⱼ ∂ⱼψⱼ` with `|ψⱼ| ≤ R = C₁ M Lⁿ(spt a)^{1/n}` (`rpn_potential_estimate`) and
`Φ = ∑ⱼ (-1)ʲ f (ψⱼ ∘ L) θⱼ`, `θⱼ = ⋀_{i ≠ j} (yⁱ ∘ L)`.  Then `dΦ = φ + Ξ` with
`Ξ = ∑ⱼ (-1)ʲ (ψⱼ ∘ L) Df ∧ θⱼ` (`rpn_extDeriv_potential_form`), so `T(φ) = ∂T(Φ) - T(Ξ)`,
and both terms are bounded through `M_W(∂T)` and `M_W(T)`
(`rpn_abs_apply_le_opNorm_mul_massOn`). -/
theorem Submission.rpn_pullback_top_form_bound :
    ∀ (P m : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)), W ⊆ U →
      T.massOn W < ∞ → T.boundary.massOn W < ∞ → ∀ f : Eucl P → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ W →
      ∀ L : Eucl P →L[ℝ] Eucl (m + 1), ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ,
      (∀ y, |a y| ≤ M) → ∀ φ : TestFormOn U (m + 1),
      (∀ x, (φ : DifferentialForm (Eucl P) (m + 1)) x = (f x * a (L x)) •
        wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) →
      |T φ| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
  intro P m U W T hWU hT hbT f hf hfc hfW L
  /- Step 1: constants depending only on `T`, `W`, `f` and `L`. -/
  obtain ⟨C₁, hC₁⟩ := Submission.rpn_potential_estimate m
  -- `θⱼ = ⋀_{i ≠ j} (yⁱ ∘ L)`, an `m`-covector.
  let θ : Fin (m + 1) → Covector (Eucl P) m := fun j =>
    wedgeCovectors m (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L)
  -- `ηⱼ(x) = Df(x) ∧ θⱼ = Λⱼ(Df(x))`, where `Λⱼ γ = Alt(γ ⊗ θⱼ)` is continuous linear.
  let η : Fin (m + 1) → DifferentialForm (Eucl P) (m + 1) := fun j x =>
    wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ f x)
      (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) :
        Fin (m + 1) → (Eucl P →L[ℝ] ℝ))
  have hηΛ : ∀ j, η j = fun x =>
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        ((ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)).flip (θ j)))
          (fderiv ℝ f x) := by
    intro j
    funext x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
    rfl
  -- `Df` is continuous and vanishes off `tsupport f`, so each `ηⱼ` is continuous with compact
  -- support, hence bounded by some `Hⱼ`.
  have hηbdd : ∀ j, ∃ H : ℝ, ∀ x, ‖η j x‖ ≤ H := by
    intro j
    rw [hηΛ j]
    exact (ContinuousLinearMap.continuous _).comp (hf.continuous_fderiv (by simp))
      |>.bounded_above_of_compact_support ((hfc.fderiv ℝ).comp_left (map_zero _))
  choose H hH using hηbdd
  have hηzero : ∀ j x, x ∉ tsupport f → η j x = 0 := by
    intro j x hx
    rw [hηΛ j]
    simp only [fderiv_of_notMem_tsupport ℝ hx, map_zero]
  -- `F₀ = sup |f|`, `B₀ = M_W(T)`, `B₁ = M_W(∂T)`.
  obtain ⟨F₀, hF₀⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hF₀nn : 0 ≤ F₀ := (norm_nonneg _).trans (hF₀ 0)
  set B₀ : ℝ := (T.massOn W).toReal
  set B₁ : ℝ := (T.boundary.massOn W).toReal
  have hTB₀ : T.massOn W ≤ ENNReal.ofReal B₀ := (ENNReal.ofReal_toReal hT.ne).ge
  have hbTB₁ : T.boundary.massOn W ≤ ENNReal.ofReal B₁ := (ENNReal.ofReal_toReal hbT.ne).ge
  refine ⟨C₁ * ((P : ℝ) ^ m * B₁ * F₀ * ∑ j, ‖θ j‖ + (P : ℝ) ^ (m + 1) * B₀ * ∑ j, H j), ?_⟩
  intro a ha hac M hM φ hφ
  /- Step 2: the potential `ψ`, with `∑ⱼ ∂ⱼψⱼ = a` and `|ψⱼ| ≤ R`. -/
  obtain ⟨ψ, hψ, hdiv, hψb⟩ := hC₁ a ha hac M hM
  set R : ℝ := C₁ * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) with hR
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hψb 0 0)
  /- Step 3: the test `m`-form `Φ = ∑ⱼ (-1)ʲ f (ψⱼ ∘ L) θⱼ`, supported in `tsupport f ⊆ W`. -/
  let Φf : DifferentialForm (Eucl P) m := fun z =>
    ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) • θ j
  have hΦsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φf :=
    ContDiff.sum fun j _ =>
      (contDiff_const.mul (hf.mul ((hψ j).comp L.contDiff))).smul contDiff_const
  have hΦsupp : Function.support Φf ⊆ Function.support f := by
    intro z hz
    rw [Function.mem_support] at hz ⊢
    contrapose! hz
    simp [Φf, hz]
  have hΦts : tsupport Φf ⊆ tsupport f := closure_mono hΦsupp
  let Φ : TestFormOn U m := ⟨Φf, ⟨⟨hΦsmooth, hfc.mono hΦsupp⟩, hΦts.trans (hfW.trans hWU)⟩⟩
  /- Step 4: `dΦ = φ + Ξ` with `Ξ = ∑ⱼ (-1)ʲ (ψⱼ ∘ L) ηⱼ`. -/
  let dΦ : TestFormOn U (m + 1) := exteriorDerivativeTestOn U m Φ
  have hdΦ : ∀ x, (dΦ : DifferentialForm (Eucl P) (m + 1)) x =
      (f x * a (L x)) •
        wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) • η j x := by
    intro x
    have hd := Submission.rpn_extDeriv_potential_form P m L f ψ x
      (hf.differentiable (by simp) x) (fun j => (hψ j).differentiable (by simp) (L x))
    rw [hdiv (L x)] at hd
    exact hd
  let Ξ : TestFormOn U (m + 1) := dΦ - φ
  have hΞ : ∀ x, (Ξ : DifferentialForm (Eucl P) (m + 1)) x =
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) • η j x := by
    intro x
    change (dΦ : DifferentialForm (Eucl P) (m + 1)) x -
      (φ : DifferentialForm (Eucl P) (m + 1)) x = _
    rw [hdΦ x, hφ x, add_sub_cancel_left]
  -- `Ξ` vanishes off `tsupport f`, because every `ηⱼ` does.
  have hΞts : tsupport (Ξ : DifferentialForm (Eucl P) (m + 1)) ⊆ W := by
    refine (closure_minimal (fun x hx => ?_) (isClosed_tsupport f)).trans hfW
    by_contra hxf
    exact hx (by rw [hΞ x]; simp [hηzero _ x hxf])
  /- Step 5: `T(φ) = T(dΦ) - T(Ξ) = ∂T(Φ) - T(Ξ)`. -/
  have hsplit : T φ = T.boundary Φ - T Ξ := by
    rw [GeometricCurrentOn.boundary_apply]
    change T.toCurrent φ = T.toCurrent dΦ - T.toCurrent (dΦ - φ)
    rw [T.toCurrent.map_sub dΦ φ]
    ring
  /- Step 6: pointwise bounds `‖Φ‖ ≤ F₀ R ∑ⱼ ‖θⱼ‖` and `‖Ξ‖ ≤ R ∑ⱼ Hⱼ`. -/
  have hΦbound : ∀ z, ‖(Φ : DifferentialForm (Eucl P) m) z‖ ≤ F₀ * R * ∑ j, ‖θ j‖ := by
    intro z
    change ‖∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) • θ j‖ ≤ _
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul]
    have hfz : |f z| ≤ F₀ := by simpa only [Real.norm_eq_abs] using hF₀ z
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hfz (hψb j (L z)) (abs_nonneg _) hF₀nn) (norm_nonneg _)
  have hΞbound : ∀ x, ‖(Ξ : DifferentialForm (Eucl P) (m + 1)) x‖ ≤ R * ∑ j, H j := by
    intro x
    rw [hΞ x, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact mul_le_mul (hψb j (L x)) (hH j x) (norm_nonneg _) hR0
  /- Step 7: the mass bounds for `∂T(Φ)` and `T(Ξ)`. -/
  have hbΦ := Submission.rpn_abs_apply_le_opNorm_mul_massOn P m U W T.boundary Φ B₁
    (F₀ * R * ∑ j, ‖θ j‖) ENNReal.toReal_nonneg hbTB₁ (hΦts.trans hfW) hΦbound
  have hTΞ := Submission.rpn_abs_apply_le_opNorm_mul_massOn P (m + 1) U W T Ξ B₀
    (R * ∑ j, H j) ENNReal.toReal_nonneg hTB₀ hΞts hΞbound
  /- Step 8: conclusion. -/
  rw [hsplit]
  calc |T.boundary Φ - T Ξ| ≤ |T.boundary Φ| + |T Ξ| := abs_sub _ _
    _ ≤ (P : ℝ) ^ m * B₁ * (F₀ * R * ∑ j, ‖θ j‖) + (P : ℝ) ^ (m + 1) * B₀ * (R * ∑ j, H j) :=
      add_le_add hbΦ hTΞ
    _ = C₁ * ((P : ℝ) ^ m * B₁ * F₀ * ∑ j, ‖θ j‖ + (P : ℝ) ^ (m + 1) * B₀ * ∑ j, H j) * M *
        ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := by
      rw [hR]
      ring
/-- **Kronecker duality of coordinate wedges (Simon Ch. 6, 1.1–1.2).**  For an increasing
multi-index `I`, `dx^I = dx^{I₁} ∧ ⋯ ∧ dx^{Iₙ}` has coordinate `1` at `I` and `0` at every
increasing `J ≠ I`: by (1.1), `dx^I(e_{J₁}, …, e_{Jₙ}) = det [I i = J j]`.  For `J = I` this matrix
is the identity, as `I` is injective.  For `J ≠ I` some `I i ∉ range J` (otherwise the finite
ranges, of equal cardinality, coincide, and increasing enumerations with equal ranges are equal),
so row `i` vanishes. -/
theorem Submission.polyhedral_approx_pairing_wedge_kronecker : ∀ (P n : ℕ) (I : SimonMultiIndex n P), euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) I = 1 ∧ ∀ J : SimonMultiIndex n P, J ≠ I → euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J = 0 := by
  intro P n I
  -- (1)–(2) The coordinate at `J` is the determinant of the matrix `[I i = J j]`.
  have hdet : ∀ J : SimonMultiIndex n P,
      euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        Matrix.det (Matrix.of fun i j => if I i = J j then (1 : ℝ) else 0) := by
    intro J
    rw [euclideanCovectorCoordinate, wedgeCovectors_apply_det]
    congr 1
    ext i j
    simp [PiLp.single_apply]
  refine ⟨?_, fun J hJ => ?_⟩
  · -- (3) For `J = I` the matrix is the identity, as `I` is injective.
    have hone : (Matrix.of fun i j => if I i = I j then (1 : ℝ) else 0) = 1 := by
      ext i j
      simp [Matrix.one_apply, I.injective.eq_iff]
    rw [hdet, hone, Matrix.det_one]
  · -- (4) Some `I i` lies outside `range J`: otherwise `range I = range J` and `I = J`.
    obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
      by_contra h
      have hsub : range I ⊆ range J := by
        rintro _ ⟨i, rfl⟩
        by_contra hi
        exact h ⟨i, fun j hj => hi ⟨j, hj.symm⟩⟩
      have hrange : range I = range J :=
        Set.eq_of_subset_of_ncard_le hsub (by
          rw [Set.ncard_range_of_injective I.injective, Set.ncard_range_of_injective J.injective])
      exact hJ (OrderEmbedding.range_inj_of_wellFoundedLT.mp hrange).symm
    -- (5) Row `i` of the matrix vanishes, so the determinant is `0`.
    rw [hdet]
    exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [hi j]
/-- An `n`-covector on `ℝ^P` is determined by its coordinates on increasing multi-indices
(Simon Ch. 6, 1.2): if `α(e_{I(0)}, …, e_{I(n-1)}) = β(e_{I(0)}, …, e_{I(n-1)})` for every
increasing `I`, then `α = β`.  Alternating maps agreeing on injective tuples of basis vectors are
equal; sorting an injective tuple `v` by `σ = Tuple.sort v` gives the increasing `I = v ∘ σ`, and
`e_v = e_I ∘ σ⁻¹` gives `γ(e_v) = sign(σ⁻¹) γ(e_I)` for `γ = α, β`. -/
theorem Submission.polyhedral_approx_pairing_covector_ext : ∀ (P n : ℕ) (α β : Covector (Eucl P) n), (∀ I : SimonMultiIndex n P, euclideanCovectorCoordinate α I = euclideanCovectorCoordinate β I) → α = β := by
  intro P n α β h
  -- Reduce to the underlying alternating maps on injective tuples of standard basis vectors.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  -- Sorting `v` by `σ = Tuple.sort v` gives the increasing multi-index `I = v ∘ σ`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  let I : SimonMultiIndex n P := OrderEmbedding.ofStrictMono _ hsm
  -- `e_v = e_I ∘ σ⁻¹`.
  have he : (fun i => EuclideanSpace.single (v i) (1 : ℝ)) =
      (fun j => EuclideanSpace.single (I j) (1 : ℝ)) ∘ ⇑(Tuple.sort v)⁻¹ := by
    funext i
    simp [I]
  -- `γ(e_v) = sign(σ⁻¹) • γ(e_I)` for `γ = α, β`, and `α(e_I) = β(e_I)`.
  rw [he, AlternatingMap.map_perm, AlternatingMap.map_perm]
  congr 1
  exact h I

/-- **Rotated coordinate expansion of a covector (Simon Ch. 6, 1.2; Lemma 2.36, Remark 2.37(2)).**
For a linear isometry `Q` of `ℝ^P`, every `n`-covector expands as
`φ = ∑_α φ(Q⁻¹e_{α(0)}, …, Q⁻¹e_{α(n-1)}) Q^*dx^α`, where
`Q^*dx^α = (dx^{α(0)} ∘ Q) ∧ ⋯ ∧ (dx^{α(n-1)} ∘ Q)`.  The pull-back `φ' = (Q⁻¹)^*φ` has
coordinates `φ'(e_α) = φ(Q⁻¹e_α)`, so the Kronecker property `dx^α(e_I) = δ_{αI}` gives
`φ' = ∑_α φ'(e_α) dx^α` on increasing coordinates, hence everywhere.  Pulling back by `Q` gives
`φ = Q^*φ'`. -/
theorem Submission.rpn_covector_rotated_expansion : ∀ (P n : ℕ) (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (φ : Covector (Eucl P) n), φ = ∑ α : SimonMultiIndex n P, φ (fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ))) • wedgeCovectors n (fun i => (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P)) := by
  intro P n Q φ
  -- (2) Standard expansion of `φ' = (Q⁻¹)^*φ`: both sides have the same increasing coordinates.
  have hexp : covectorPullback n (Q.symm : Eucl P →L[ℝ] Eucl P) φ =
      ∑ α : SimonMultiIndex n P, φ (fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ))) •
        wedgeCovectors n (fun i => EuclideanSpace.proj (α i)) := by
    refine Submission.polyhedral_approx_pairing_covector_ext P n _ _ fun I => ?_
    -- (1) By the Kronecker property only the `α = I` summand survives.
    have hK := Submission.polyhedral_approx_pairing_wedge_kronecker P n
    simp only [euclideanCovectorCoordinate] at hK ⊢
    rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single I]
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, (hK I).1, mul_one]
      rfl
    · intro α _ hα
      rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, (hK α).2 I (Ne.symm hα), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  -- (3) `φ = Q^*φ'` since `Q⁻¹ Q = id`, and `Q^*dx^α = wedgeCovectors n (fun i => dx^{α(i)} ∘ Q)`.
  have hφ : φ = covectorPullback n (Q : Eucl P →L[ℝ] Eucl P)
      (covectorPullback n (Q.symm : Eucl P →L[ℝ] Eucl P) φ) := by
    ext v
    simp [Function.comp_def]
  conv_lhs => rw [hφ, hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_smul, covectorPullback_wedgeCovectors]
/-- Smooth cutoffs for a compact Lebesgue-null set (Simon Ch. 6, proof of Lemma 2.36, display
(2)): if `F ⊆ ℝ^N` is compact with `Lᴺ(F) = 0` and `δ > 0`, there is a `C^∞` function
`b : ℝ^N → [0, 1]` with compact support, `b = 1` on `F` and `Lᴺ(spt b) ≤ δ`.  By outer regularity
pick an open `G ⊇ F` with `Lᴺ(G) < δ`, then an open `V` with `F ⊆ V ⊆ closure V ⊆ G` and
`closure V` compact, and a smooth Urysohn function equal to `1` on `F` and to `0` off `V`. -/
theorem Submission.rpn_null_compact_cutoff : ∀ (N : ℕ) (F : Set (Eucl N)), IsCompact F → (volume : Measure (Eucl N)) F = 0 → ∀ δ : ℝ, 0 < δ → ∃ b : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∈ F, b y = 1) ∧ ((volume : Measure (Eucl N)) (tsupport b)).toReal ≤ δ := by
  intro N F hF hF0 δ hδ
  -- Step 1: outer regularity of `Lᴺ` gives an open `G ⊇ F` with `Lᴺ(G) < δ`.
  obtain ⟨G, hFG, hGo, hGδ⟩ := Set.exists_isOpen_lt_of_lt F (ENNReal.ofReal δ)
    (by rw [hF0]; exact ENNReal.ofReal_pos.mpr hδ)
  -- Step 2: an open `V` with `F ⊆ V`, `closure V ⊆ G` and `closure V` compact.
  obtain ⟨V, hVo, hFV, hVG, hVc⟩ := exists_open_between_and_isCompact_closure hF hGo hFG
  -- Step 3: a smooth Urysohn function `b : ℝ^N → [0, 1]` with `b = 0` off `V` and `b = 1` on `F`.
  obtain ⟨b, hb0, hb1, hb01⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ (Eucl N)) (n := ⊤) hVo.isClosed_compl hF.isClosed
    (Set.disjoint_compl_left_iff_subset.mpr hFV)
  -- Step 4: `spt b ⊆ closure V ⊆ G`, so `spt b` is compact and `Lᴺ(spt b) ≤ Lᴺ(G) < δ`.
  have hsupp : tsupport b ⊆ closure V :=
    closure_mono fun x hx => by_contra fun hxV => hx (hb0 hxV)
  refine ⟨b, contMDiff_iff_contDiff.mp b.contMDiff,
    hVc.of_isClosed_subset (isClosed_tsupport _) hsupp, fun y => hb01 y, fun y hy => hb1 hy, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hδ.le ((measure_mono (hsupp.trans hVG)).trans hGδ.le)

/-- **Mass off a compact set with null projections (Simon Ch. 6, proof of Lemma 2.36, displays
(1)–(3), run for `Q_#T` as in Remark 2.37(2)).**  Let `T ∈ 𝒟ₙ(U)` (`n = m + 1`) have
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and be represented by `(μ, ξ)` with
`Σ_β ξ(x)(dx^β)² = 1` for `μ`-a.e. `x`.  If `K` is compact and `Lⁿ(π_α(K)) = 0` for every
`α ∈ I(n, P)`, where `π_α(x) = ((Qx)_{α(0)}, …, (Qx)_{α(m)})`, then `M_W(T) ≤ C μ(W∖K)` for every
open `W ⊂⊂ U`.  Each admissible `ω` expands as `Σ_α ω_α θ_α` with `ω_α = ω(Q⁻¹e_α)` and
`θ_α = Q^*dx^α` (the top form of `π_α`).  For each `α` the cut-off estimate gives
`|T(ω_α θ_α)| ≤ c_α c'_α μ(W∖K)`, with `c_α = Σ_β |dx^β(Q⁻¹e_α)|` and `c'_α = Σ_β |θ_α(e_β)|`. -/
theorem Submission.rpn_massOn_le_mul_measure_diff : ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ (μ : Measure (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ ξ → (∀ᵐ x ∂μ, ∑ β : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) β) ^ 2 = 1) → ∀ (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (K : Set (Eucl P)), IsCompact K → (∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' K) = 0) → ∃ C : ℝ≥0, ∀ W, CompactlyContainedOpen W U → T.massOn W ≤ (C : ℝ≥0∞) * μ (W \ K) := by
  intro P m U T hmass μ ξ hrep hξ Q K hK hnull
  classical
  -- Step 1: `π_α x = ((Qx)_{α(0)}, …, (Qx)_{α(m)})` is linear and `y^i ∘ π_α = x^{α(i)} ∘ Q`, so
  -- the top form of `π_α` is `θ_α = Q^*dx^α`; `π_α(K)` is the null set of the hypothesis.
  let π : SimonMultiIndex (m + 1) P → Eucl P →L[ℝ] Eucl (m + 1) := fun α =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i =>
        (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P))
  let θ : SimonMultiIndex (m + 1) P → Covector (Eucl P) (m + 1) := fun α =>
    wedgeCovectors (m + 1)
      (fun i => (EuclideanSpace.proj (α i) : Eucl P →L[ℝ] ℝ).comp (Q : Eucl P →L[ℝ] Eucl P))
  have hθπ : ∀ α, wedgeCovectors (m + 1)
      (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp (π α)) = θ α := fun α =>
    congrArg (wedgeCovectors (m + 1)) (funext fun i => ContinuousLinearMap.ext fun x => rfl)
  have hπK : ∀ α, (volume : Measure (Eucl (m + 1))) (π α '' K) = 0 := hnull
  -- Step 4: the constants `c_α = Σ_β |dx^β(e^Q_α)|` and `c'_α = Σ_β |θ_α(e_β)|`.
  let e : SimonMultiIndex (m + 1) P → Fin (m + 1) → Eucl P := fun α i =>
    Q.symm (EuclideanSpace.single (α i) (1 : ℝ))
  let c : SimonMultiIndex (m + 1) P → ℝ := fun α => ∑ β : SimonMultiIndex (m + 1) P,
    |wedgeCovectors (m + 1) (fun j => (EuclideanSpace.proj (β j) : Eucl P →L[ℝ] ℝ)) (e α)|
  let c' : SimonMultiIndex (m + 1) P → ℝ := fun α => ∑ β : SimonMultiIndex (m + 1) P,
    |euclideanCovectorCoordinate (θ α) β|
  have hc : ∀ α, 0 ≤ c α := fun α => Finset.sum_nonneg fun β _ => abs_nonneg _
  have hc' : ∀ α, 0 ≤ c' α := fun α => Finset.sum_nonneg fun β _ => abs_nonneg _
  set S : ℝ := ∑ α : SimonMultiIndex (m + 1) P, c α * c' α
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun α _ => mul_nonneg (hc α) (hc' α)
  -- Step 4(b): `|ξ(x)(θ_α)| ≤ c'_α` for `μ`-a.e. `x`.
  have hξθ : ∀ α, ∀ᵐ x ∂μ, |ξ x (θ α)| ≤ c' α := fun α =>
    hξ.mono fun x hx => Submission.rpn_moc_abs_nvector_apply_le P (m + 1) (ξ x) (θ α) hx
  refine ⟨Real.toNNReal (1 + S), fun W hW => ?_⟩
  -- Step 5: `W ⊆ U` with finite masses; the case `μ(W∖K) = ∞` is trivial.
  have hW' : IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U := hW
  have hWU : W ⊆ U := subset_closure.trans hW'.2.2
  have hfin := ENNReal.add_lt_top.mp (hmass W hW)
  have hC0 : ((Real.toNNReal (1 + S) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
    linarith
  by_cases hD : μ (W \ K) = ∞
  · rw [hD, ENNReal.mul_top hC0]
    exact le_top
  apply sSup_le
  rintro _ ⟨ω, hω, rfl⟩
  -- Step 6: `ω_α(x) = ω(x)(e^Q_α)` is smooth, supported in `W` and bounded by `c_α`.
  let f : SimonMultiIndex (m + 1) P → Eucl P → ℝ := fun α x =>
    (ω : DifferentialForm (Eucl P) (m + 1)) x (e α)
  have hf_smooth : ∀ α, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f α) := fun α =>
    (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (e α)).contDiff.comp ω.property.1.1
  have hf_cs : ∀ α, HasCompactSupport (f α) := fun α =>
    ω.property.1.2.comp_left (g := fun φ : Covector (Eucl P) (m + 1) => φ (e α)) rfl
  have hf_supp : ∀ α, tsupport (f α) ⊆ W := fun α =>
    (tsupport_comp_subset (g := fun φ : Covector (Eucl P) (m + 1) => φ (e α)) rfl _).trans hω.1
  have hf_bound : ∀ α x, |f α x| ≤ c α := fun α x =>
    (Submission.rpn_moc_abs_covector_apply_le P (m + 1) _ (e α)).trans
      (mul_le_of_le_one_right (hc α) (hω.2 x))
  -- The test forms `ζ_α = ω_α θ_α`; by the rotated expansion `ω = Σ_α ζ_α`.
  choose ζ hζ using fun α => Submission.rpn_moc_exists_testForm_smul P (m + 1) U (f α) (θ α)
    (hf_smooth α) (hf_cs α) ((hf_supp α).trans hWU)
  have hωζ : ω = ∑ α, ζ α := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    simp only [hζ]
    exact Submission.rpn_covector_rotated_expansion P (m + 1) Q _
  -- Step 7: `|T(ζ_α)| ≤ c_α c'_α μ(W∖K)`, cutting off near `π_α(K)` (printed display (2)).
  have hTζ : ∀ α, |T (ζ α)| ≤ c α * c' α * (μ (W \ K)).toReal := fun α =>
    Submission.rpn_moc_abs_apply_top_form_le P m U W K T μ ξ hrep hW'.1 hWU hK hD (π α) (f α)
      (c α) (c' α) (hf_smooth α) (hf_cs α) (hf_supp α) (hf_bound α)
      (by rw [hθπ α]; exact hξθ α)
      (Submission.rpn_pullback_top_form_bound P m U W T hWU hfin.1 hfin.2 (f α) (hf_smooth α)
        (hf_cs α) (hf_supp α) (π α))
      (fun δ hδ => Submission.rpn_null_compact_cutoff (m + 1) (π α '' K)
        (hK.image (π α).continuous) (hπK α) δ hδ)
      (ζ α) (fun x => by rw [hθπ α]; exact hζ α x)
  -- Step 8: sum over `α` (printed display (3)).
  have hTω : T ω ≤ (1 + S) * (μ (W \ K)).toReal := by
    calc T ω = ∑ α, T (ζ α) := by rw [hωζ]; exact map_sum T.toCurrent ζ Finset.univ
      _ ≤ ∑ α, |T (ζ α)| := Finset.sum_le_sum fun α _ => le_abs_self _
      _ ≤ ∑ α, c α * c' α * (μ (W \ K)).toReal := Finset.sum_le_sum fun α _ => hTζ α
      _ = S * (μ (W \ K)).toReal := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + S) * (μ (W \ K)).toReal :=
        mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
  calc ENNReal.ofReal (T ω) ≤ ENNReal.ofReal ((1 + S) * (μ (W \ K)).toReal) :=
        ENNReal.ofReal_le_ofReal hTω
    _ = ((Real.toNNReal (1 + S) : ℝ≥0) : ℝ≥0∞) * μ (W \ K) := by
      rw [ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hD]
      rfl
/-- Shrinking neighbourhoods (Simon Ch. 6, proof of Lemma 2.36, after (4)): if `K ⊆ U` is
compact, `μ(W) < ∞` and `μ(W) ≤ C μ(W ∖ K)` for every open `W ⊂⊂ U`, then `μ(K) = 0`.  The
thickenings `W_q = {dist(·, K) < r₀/(q+1)}` are `⊂⊂ U` and decrease to `K`, so continuity from
above gives `μ(K) ≤ μ(W_q) ≤ C μ(W_q ∖ K) → 0`. -/
theorem Submission.rpn_compact_null_of_le_mul_diff : ∀ (P : ℕ) (U K : Set (Eucl P)) (μ : Measure (Eucl P)) (C : ℝ≥0), IsOpen U → IsCompact K → K ⊆ U → (∀ W, CompactlyContainedOpen W U → μ W < ∞) → (∀ W, CompactlyContainedOpen W U → μ W ≤ (C : ℝ≥0∞) * μ (W \ K)) → μ K = 0 := by
  intro P U K μ C hU hK hKU hfin hle
  -- Step 1: some closed neighbourhood `cthickening r₀ K`, `r₀ > 0`, lies in `U`.
  obtain ⟨r₀, hr₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Step 2: `W_q = thickening (r₀ / (q + 1)) K` is open, `⊂⊂ U`, decreasing in `q`, `K ⊆ W_q`.
  have hr_pos : ∀ q : ℕ, 0 < r₀ / ((q : ℝ) + 1) := fun q => div_pos hr₀ (Nat.cast_add_one_pos q)
  have hcc : ∀ q : ℕ, CompactlyContainedOpen (thickening (r₀ / ((q : ℝ) + 1)) K) U := by
    intro q
    have hle₀ : r₀ / ((q : ℝ) + 1) ≤ r₀ :=
      div_le_self hr₀.le (le_add_of_nonneg_left (Nat.cast_nonneg q))
    refine ⟨isOpen_thickening, ?_, ?_⟩
    · exact hK.cthickening.of_isClosed_subset isClosed_closure
        (closure_thickening_subset_cthickening _ K)
    · exact (closure_thickening_subset_cthickening _ K).trans ((cthickening_mono hle₀ K).trans hsub)
  have hanti : Antitone fun q : ℕ => thickening (r₀ / ((q : ℝ) + 1)) K := by
    intro p q hpq
    refine thickening_mono (div_le_div_of_nonneg_left hr₀.le (Nat.cast_add_one_pos p) ?_) K
    have hpq' : (p : ℝ) ≤ q := Nat.cast_le.mpr hpq
    linarith
  -- Step 3: `⋂_q W_q ⊆ closure K = K`.
  have hInter : ∀ x, (∀ q : ℕ, x ∈ thickening (r₀ / ((q : ℝ) + 1)) K) → x ∈ K := by
    intro x hx
    rw [← hK.isClosed.closure_eq, closure_eq_iInter_thickening, mem_iInter₂]
    intro δ hδ
    obtain ⟨q, hq⟩ := exists_nat_gt (r₀ / δ)
    have hqδ : r₀ / ((q : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hδ] at hq
      rw [div_lt_iff₀ (Nat.cast_add_one_pos q)]
      nlinarith
    exact thickening_mono hqδ.le K (hx q)
  -- Step 4: the Borel sets `W_q ∖ K` decrease to `∅` and `μ(W_0 ∖ K) < ∞`, so
  -- `μ(W_q ∖ K) → 0` by continuity from above.
  have hdiff : Tendsto (fun q : ℕ => μ (thickening (r₀ / ((q : ℝ) + 1)) K \ K)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun q : ℕ => thickening (r₀ / ((q : ℝ) + 1)) K \ K)
      (fun q => (isOpen_thickening.measurableSet.diff hK.isClosed.measurableSet).nullMeasurableSet)
      (fun p q hpq => sdiff_subset_sdiff_left (hanti hpq))
      ⟨0, ((measure_mono sdiff_subset).trans_lt (hfin _ (hcc 0))).ne⟩
    have hempty : ⋂ q : ℕ, (thickening (r₀ / ((q : ℝ) + 1)) K \ K) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      rw [mem_iInter] at hx
      exact (hx 0).2 (hInter x fun q => (hx q).1)
    rw [hempty, measure_empty] at h
    exact h
  -- Step 5: `μ(K) ≤ μ(W_q) ≤ C μ(W_q ∖ K) → C · 0 = 0`.
  have hlim : Tendsto (fun q : ℕ => (C : ℝ≥0∞) * μ (thickening (r₀ / ((q : ℝ) + 1)) K \ K))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hdiff (Or.inr ENNReal.coe_ne_top)
  refine le_antisymm (ge_of_tendsto' hlim fun q => ?_) bot_le
  exact (measure_mono (self_subset_thickening (hr_pos q) K)).trans (hle _ (hcc q))
/-- Simon Ch. 6, end of the proof of Lemma 2.36 and Remark 2.37(1), via Ch. 1, 1.15(2): if `U`
is open, `μ(ℝ^P ∖ U) = 0` and `μ(W) < ∞` for every `W ⊂⊂ U`, then a Borel set `E` whose compact
subsets inside `U` are all `μ`-null is itself `μ`-null. -/
theorem Submission.rpn_null_of_compact_null : ∀ (P : ℕ) (U E : Set (Eucl P)) (μ : Measure (Eucl P)), IsOpen U → μ Uᶜ = 0 → (∀ W, CompactlyContainedOpen W U → μ W < ∞) → MeasurableSet E → (∀ K, IsCompact K → K ⊆ E → K ⊆ U → μ K = 0) → μ E = 0 := by
  intro P U E μ hU hUc hfin hE hK
  -- Countably many balls `B(x, ε_x / 2) ⊂⊂ U`, `x ∈ S`, cover `U` (Lindelöf).
  choose ε hε hεU using fun x : U => Metric.isOpen_iff.1 hU x x.2
  have hcc : ∀ x : U, CompactlyContainedOpen (ball (x : Eucl P) (ε x / 2)) U := fun x =>
    ⟨isOpen_ball, (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self (hε x))).trans
        (hεU x))⟩
  obtain ⟨S, hS, hSU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun x : U => ball (x : Eucl P) (ε x / 2))
      fun _ => isOpen_ball
  have hcover : U ⊆ ⋃ x ∈ S, ball (x : Eucl P) (ε x / 2) := fun y hy =>
    hSU.superset (mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (half_pos (hε _))⟩)
  -- Each `E ∩ V` with `V = B(x, ε_x / 2)` is null: `μ ⌞ V` is finite, hence inner regular by
  -- closed sets, and a closed `F ⊆ E ∩ V` lies in the compact `closure V ⊆ U`.
  have hpiece : ∀ x : U, μ (E ∩ ball (x : Eucl P) (ε x / 2)) = 0 := by
    intro x
    obtain ⟨hVo, hVc, hVU⟩ := hcc x
    have : IsFiniteMeasure (μ.restrict (ball (x : Eucl P) (ε x / 2))) :=
      ⟨(Measure.restrict_apply_univ _).trans_lt (hfin _ (hcc x))⟩
    have hA : MeasurableSet (E ∩ ball (x : Eucl P) (ε x / 2)) := hE.inter hVo.measurableSet
    rw [← Measure.restrict_eq_self μ inter_subset_right]
    by_contra hne
    obtain ⟨F, hFA, hFc, hF⟩ :=
      hA.exists_lt_isClosed_of_ne_top (measure_ne_top _ _) (pos_iff_ne_zero.2 hne)
    have hFV : F ⊆ closure (ball (x : Eucl P) (ε x / 2)) :=
      (hFA.trans inter_subset_right).trans subset_closure
    have hF0 : μ F = 0 :=
      hK F (hVc.of_isClosed_subset hFc hFV) (hFA.trans inter_subset_left) (hFV.trans hVU)
    exact lt_irrefl _ (hF.trans_le ((Measure.restrict_apply_le _ _).trans hF0.le))
  -- Countable subadditivity gives `μ(E ∩ U) = 0`, and `μ(E ∖ U) ≤ μ(Uᶜ) = 0`.
  have hEU : μ (E ∩ U) = 0 := by
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hS).2 fun x _ => hpiece x)
    rintro y ⟨hyE, hyU⟩
    obtain ⟨x, hxS, hyx⟩ := mem_iUnion₂.1 (hcover hyU)
    exact mem_iUnion₂.2 ⟨x, hxS, hyE, hyx⟩
  have hEUc : μ (E \ U) = 0 := measure_mono_null (sdiff_subset_compl E U) hUc
  refine nonpos_iff_eq_zero.1 ((measure_le_inter_add_sdiff μ E U).trans_eq ?_)
  rw [hEU, hEUc, add_zero]
/-- **Mollification step of Simon Ch. 6, Lemma 2.15 (p. 137).**  A continuous compactly supported
`n`-form `ω` with `tsupport ω ⊆ V`, `V` open, is a uniform limit, in the Euclidean coefficient
norm, of test forms supported in `V`.  As `|α| ≤ √N ‖α‖` (`N = #(Fin n → Fin P)`, `‖α‖` the
operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ ω)`: `ψ ⋆ ω`
is the convolution of `ω` with a normalized smooth bump `ψ` supported in a ball whose radius is
a uniform-continuity modulus of `ω`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to
`1` exactly on `tsupport ω`, whose support `V'` has compact closure in `V`. -/
theorem Submission.cmb_exists_testForm_uniform_approx : ∀ (P n : ℕ) (U V : Set (Eucl P)) (ω : Eucl P → Covector (Eucl P) n), IsOpen V → V ⊆ U → Continuous ω → HasCompactSupport ω → tsupport ω ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U n, tsupport (η : DifferentialForm (Eucl P) n) ⊆ V ∧ ∀ x, covectorEuclideanNorm (ω x - (η : DifferentialForm (Eucl P) n) x) ≤ ε := by
  intro P n U V ω hV hVU hω hωc hωV ε hε
  -- Step 1: `|α| ≤ √N ‖α‖`, since every coefficient satisfies `|α(e_I)| ≤ ‖α‖ ∏ ‖e_{I j}‖ = ‖α‖`.
  set N : ℝ := Real.sqrt (Fintype.card (Fin n → Fin P)) with hN_def
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hcmp : ∀ α : Covector (Eucl P) n, covectorEuclideanNorm α ≤ N * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hN_def, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin n → Fin P,
          (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
        ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg α)] using h)
          · positivity
      _ = (Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  have hN1 : 0 < N + 1 := by linarith
  set ε' : ℝ := ε / (N + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε hN1
  -- Step 2: an open `V'` with `tsupport ω ⊆ V'` and `closure V' ⊆ V` compact.
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ :=
    exists_open_between_and_isCompact_closure hωc.isCompact hV hωV
  -- Step 3: a smooth cutoff `χ : ℝ^P → [0, 1]` with `support χ = V'` and `χ = 1` exactly on
  -- `tsupport ω`.
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV'o (isClosed_tsupport ω) hKV'
  -- Step 4: mollification.  `ω` is uniformly continuous with modulus `δ` at accuracy `ε'`; `ψ` is
  -- a smooth bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `g = ψ ⋆ ω` is smooth and
  -- `dist (g x) (ω x) ≤ ε'`.
  obtain ⟨δ, hδ, hωδ⟩ :=
    Metric.uniformContinuous_iff.mp (hωc.uniformContinuous_of_continuous hω) ε' hε'
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ0⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
  have hφnn : ∀ y, 0 ≤ φ y := fun y => (hφr (mem_range_self y)).1
  have hφint : 0 < ∫ y, φ y :=
    hφd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hφc (fun y => hφnn y)
      (hφ0.symm ▸ one_ne_zero : φ 0 ≠ 0)
  set ψ : Eucl P → ℝ := fun y => (∫ z, φ z)⁻¹ * φ y with hψ_def
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hφd
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hφint.le) (hφnn y)
  have hψs : Function.support ψ ⊆ ball 0 δ :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport φ).trans hφs)
  have hψ1 : ∫ y, ψ y = 1 := by
    rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hφint.ne']
  obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → Covector (Eucl P) n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (ω x) ≤ ε' :=
    ⟨convolution ψ ω (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      hψc.contDiff_convolution_left _ hψd hω.locallyIntegrable,
      fun x => dist_convolution_le hε'.le hψs hψnn hψ1 hω.aestronglyMeasurable
        fun y hy => (hωδ (mem_ball.mp hy)).le⟩
  -- Step 5: `η = χ • g` is a test form with `tsupport η ⊆ closure V' ⊆ V ⊆ U`.
  have hη_supp : tsupport (fun x => χ x • g x) ⊆ closure V' := by
    refine (tsupport_smul_subset_left χ g).trans ?_
    rw [tsupport, hχs]
  have hη_cpt : HasCompactSupport (fun x => χ x • g x) :=
    hV'c.of_isClosed_subset (isClosed_tsupport _) hη_supp
  refine ⟨⟨fun x => χ x • g x, ⟨⟨hχ.smul hg, hη_cpt⟩, hη_supp.trans (hV'V.trans hVU)⟩⟩,
    hη_supp.trans hV'V, fun x => ?_⟩
  -- Step 6: `‖ω x - η x‖ ≤ ε'` (on `tsupport ω`, `η = g`; off it, `ω = 0` and `0 ≤ χ ≤ 1`),
  -- hence `|ω x - η x| ≤ √N ε' ≤ ε`.
  have hle : ‖ω x - χ x • g x‖ ≤ ε' := by
    by_cases hx : x ∈ tsupport ω
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : ω x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε' := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  calc covectorEuclideanNorm (ω x - χ x • g x) ≤ N * ‖ω x - χ x • g x‖ := hcmp _
    _ ≤ N * ε' := mul_le_mul_of_nonneg_left hle hN
    _ ≤ ε := by
      rw [hε'_def, mul_div_assoc', div_le_iff₀ hN1]
      nlinarith

open scoped CompactlySupported in
theorem Submission.rectifiability_mass_measure_representation : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U k, (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞) → (∃ μ : Measure (Eucl P), IsMassMeasure T μ) ∧ ∀ μ : Measure (Eucl P), IsMassMeasure T μ → ∃ ξ : Eucl P → NVector (Eucl P) k, StronglyMeasurable ξ ∧ (∀ᵐ x ∂μ, ∑ α : SimonMultiIndex k P, (euclideanNVectorCoordinate (ξ x) α) ^ 2 = 1) ∧ IsMeasureRepresentation T μ ξ := by
  -- Step 1 (coordinates), from the reused expansion `cmb_covector_eq_sum_coord_smul_wedge`.
  have hexp := Submission.cmb_covector_eq_sum_coord_smul_wedge
  have h_coordinates : ∀ (P k : ℕ), ∃ e : Covector (Eucl P) k ≃L[ℝ] EuclideanSpace ℝ (SimonMultiIndex k P), (∀ (φ : Covector (Eucl P) k) (α : SimonMultiIndex k P), e φ α = euclideanCovectorCoordinate φ α) ∧ (∀ φ : Covector (Eucl P) k, ‖e φ‖ = covectorEuclideanNorm φ) ∧ (∀ α : SimonMultiIndex k P, euclideanCovectorCoordinate (wedgeCovectors k (fun j => EuclideanSpace.proj (α j))) α = 1) ∧ ∀ α β : SimonMultiIndex k P, α ≠ β → euclideanCovectorCoordinate (wedgeCovectors k (fun j => EuclideanSpace.proj (α j))) β = 0 := by
    intro P k
    classical
    -- Kronecker property
    have hK : ∀ β γ : SimonMultiIndex k P,
        euclideanCovectorCoordinate (wedgeCovectors k (fun j => EuclideanSpace.proj (β j))) γ =
          if β = γ then 1 else 0 := by
      intro β γ
      rw [euclideanCovectorCoordinate, wedgeCovectors_apply_det]
      split_ifs with hβγ
      · subst hβγ
        convert Matrix.det_one (n := Fin k) (R := ℝ)
        ext i j
        simp [Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
      · obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
          by_contra! h
          apply hβγ
          rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
          have hsub : Set.range β ⊆ Set.range γ := by
            rintro _ ⟨i, rfl⟩
            obtain ⟨j, hj⟩ := h i
            exact ⟨j, hj.symm⟩
          refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range γ)
          rw [Set.ncard_range_of_injective γ.injective, Set.ncard_range_of_injective β.injective]
        exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
    set H := EuclideanSpace ℝ (SimonMultiIndex k P)
    set dx : SimonMultiIndex k P → Covector (Eucl P) k :=
      fun β => wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) with hdx
    -- coordinate map
    let cL : Covector (Eucl P) k →L[ℝ] H :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : SimonMultiIndex k P => ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun α =>
          ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (fun j => EuclideanSpace.single (α j) (1 : ℝ)))
    have hcL : ∀ φ α, cL φ α = euclideanCovectorCoordinate φ α := fun φ α => rfl
    let dL : H →L[ℝ] Covector (Eucl P) k :=
      ∑ β : SimonMultiIndex k P, (EuclideanSpace.proj β : H →L[ℝ] ℝ).smulRight (dx β)
    have hdL : ∀ h : H, dL h = ∑ β, h β • dx β := by
      intro h
      simp only [dL, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
      rfl
    have h1 : Function.LeftInverse dL cL := by
      intro φ
      rw [hdL]
      exact (hexp P k φ).symm
    have h2 : Function.RightInverse dL cL := by
      intro h
      ext α
      rw [hcL, hdL]
      simp only [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      have : ∀ β, dx β (fun j => EuclideanSpace.single (α j) (1:ℝ)) = if β = α then 1 else 0 :=
        fun β => hK β α
      simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    let e : Covector (Eucl P) k ≃L[ℝ] H := ContinuousLinearEquiv.equivOfInverse cL dL h1 h2
    refine ⟨e, fun φ α => rfl, ?_, fun α => by rw [hK]; simp, fun α β h => by rw [hK]; simp [h]⟩
    intro φ
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs]
    -- reindex: order embeddings ↔ strictly monotone maps
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij (fun α => ⇑α) ?_ ?_ ?_ ?_
    · intro α _; simp [α.strictMono]
    · intro α _ β _ h; exact DFunLike.coe_injective h
    · intro I hI
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hI
      exact ⟨OrderEmbedding.ofStrictMono I hI, by simp, rfl⟩
    · intro α _
      show (e φ α) ^ 2 = _
      simp [e, ContinuousLinearEquiv.equivOfInverse, hcL, euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]
  -- Steps 3 and 9 (exhaustion and uniqueness), from `cmb_exists_compactly_contained_exhaustion`.
  have hexh := Submission.cmb_exists_compactly_contained_exhaustion
  have h_measure_uniqueness : ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ μ₁ μ₂ : Measure (Eucl P), μ₁ Uᶜ = 0 → μ₂ Uᶜ = 0 → (∀ W, CompactlyContainedOpen W U → μ₁ W = μ₂ W) → (∀ W, CompactlyContainedOpen W U → μ₁ W < ∞) → μ₁ = μ₂ := by
    intro P U hU μ₁ μ₂ h1 h2 hagree hfin
    obtain ⟨W, hW, hK⟩ := hexh P U hU
    have hUcov : U = ⋃ i, W i := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨i, hi⟩ := hK {x} isCompact_singleton (singleton_subset_iff.2 hx)
        exact mem_iUnion.2 ⟨i, hi rfl⟩
      · exact iUnion_subset fun i => subset_closure.trans (hW i).2.2
    let C : Set (Set (Eucl P)) := {S | CompactlyContainedOpen S U} ∪ {S | MeasurableSet S ∧ S ⊆ Uᶜ}
    have hcc_inter : ∀ S S', CompactlyContainedOpen S U → IsOpen S' → CompactlyContainedOpen (S ∩ S') U := by
      intro S S' hS hS'
      refine ⟨hS.1.inter hS', ?_, ?_⟩
      · exact hS.2.1.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
      · exact (closure_mono inter_subset_left).trans hS.2.2
    have hpi : IsPiSystem C := by
      rintro S (hS | hS) S' (hS' | hS') _
      · exact Or.inl (hcc_inter S S' hS hS'.1)
      · right
        refine ⟨hS.1.measurableSet.inter hS'.1, ?_⟩
        exact inter_subset_right.trans hS'.2
      · right
        refine ⟨hS.1.inter hS'.1.measurableSet, inter_subset_left.trans hS.2⟩
      · exact Or.inr ⟨hS.1.inter hS'.1, inter_subset_left.trans hS.2⟩
    have hgen : (inferInstance : MeasurableSpace (Eucl P)) = MeasurableSpace.generateFrom C := by
      apply le_antisymm
      · rw [BorelSpace.measurable_eq (α := Eucl P)]
        refine MeasurableSpace.generateFrom_le fun O hO => ?_
        have hO : IsOpen O := hO
        have hO' : O = (O ∩ Uᶜ) ∪ ⋃ i, (W i ∩ O) := by
          ext x
          constructor
          · intro hx
            by_cases hxU : x ∈ U
            · rw [hUcov] at hxU
              obtain ⟨i, hi⟩ := mem_iUnion.1 hxU
              exact Or.inr (mem_iUnion.2 ⟨i, hi, hx⟩)
            · exact Or.inl ⟨hx, hxU⟩
          · rintro (hx | hx)
            · exact hx.1
            · obtain ⟨i, hi⟩ := mem_iUnion.1 hx; exact hi.2
        rw [hO']
        refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun i => ?_)
        · exact MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hO.measurableSet.inter hU.isClosed_compl.measurableSet, inter_subset_right⟩)
        · exact MeasurableSpace.measurableSet_generateFrom (Or.inl (hcc_inter _ _ (hW i) hO))
      · refine MeasurableSpace.generateFrom_le fun S hS => ?_
        rcases hS with hS | hS
        · exact hS.1.measurableSet
        · exact hS.1
    let B : ℕ → Set (Eucl P) := fun i => Nat.casesOn i Uᶜ (fun j => W j)
    refine Measure.ext_of_generateFrom_of_iUnion C B hgen hpi ?_ ?_ ?_ ?_
    · apply eq_univ_of_forall
      intro x
      by_cases hx : x ∈ U
      · rw [hUcov] at hx
        obtain ⟨i, hi⟩ := mem_iUnion.1 hx
        exact mem_iUnion.2 ⟨i + 1, hi⟩
      · exact mem_iUnion.2 ⟨0, hx⟩
    · intro i
      cases i with
      | zero => exact Or.inr ⟨hU.isClosed_compl.measurableSet, subset_rfl⟩
      | succ j => exact Or.inl (hW j)
    · intro i
      cases i with
      | zero => simp [B, h1]
      | succ j => exact (hfin _ (hW j)).ne
    · rintro S (hS | hS)
      · exact hagree S hS
      · rw [measure_mono_null hS.2 h1, measure_mono_null hS.2 h2]
  -- Steps 4, 5 and the bound of Step 7, from `cmb_abs_apply_le_of_massOn_le` and
  -- `cmb_exists_testForm_uniform_approx`.
  have hmass := Submission.cmb_abs_apply_le_of_massOn_le
  have hmoll := Submission.cmb_exists_testForm_uniform_approx
  have hcoord := h_coordinates
  have h_extension : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U k, (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞) → ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ, (∀ ω : TestFormOn U k, L (ω : DifferentialForm (Eucl P) k) = T ω) ∧ (∀ g₁ g₂ : Eucl P → Covector (Eucl P) k, Continuous g₁ → HasCompactSupport g₁ → tsupport g₁ ⊆ U → Continuous g₂ → HasCompactSupport g₂ → tsupport g₂ ⊆ U → L (g₁ + g₂) = L g₁ + L g₂) ∧ (∀ (c : ℝ) (g : Eucl P → Covector (Eucl P) k), Continuous g → HasCompactSupport g → tsupport g ⊆ U → L (c • g) = c * L g) ∧ ∀ (W : Set (Eucl P)) (g : Eucl P → Covector (Eucl P) k), CompactlyContainedOpen W U → Continuous g → tsupport g ⊆ W → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → ENNReal.ofReal (L g) ≤ T.massOn W := by
    intro P k U hU T hT
    classical
    obtain ⟨e, -, he_norm, -, -⟩ := hcoord P k
    -- `|·|` is a norm on covectors (it is `‖e ·‖`).
    have hN : ∀ a : Covector (Eucl P) k, covectorEuclideanNorm a = ‖e a‖ := fun a => (he_norm a).symm
    have hN_add : ∀ a b : Covector (Eucl P) k,
        covectorEuclideanNorm (a + b) ≤ covectorEuclideanNorm a + covectorEuclideanNorm b := by
      intro a b; simp only [hN, map_add]; exact norm_add_le _ _
    have hN_sub : ∀ a b : Covector (Eucl P) k,
        covectorEuclideanNorm (a - b) ≤ covectorEuclideanNorm a + covectorEuclideanNorm b := by
      intro a b; simp only [hN, map_sub]; exact norm_sub_le _ _
    have hN_smul : ∀ (c : ℝ) (a : Covector (Eucl P) k),
        covectorEuclideanNorm (c • a) = |c| * covectorEuclideanNorm a := by
      intro c a; simp only [hN, map_smul, norm_smul, Real.norm_eq_abs]
    -- Compactly contained open sets are closed under finite unions.
    have hcco_union : ∀ W₁ W₂, CompactlyContainedOpen W₁ U → CompactlyContainedOpen W₂ U →
        CompactlyContainedOpen (W₁ ∪ W₂) U := by
      intro W₁ W₂ h₁ h₂
      refine ⟨h₁.1.union h₂.1, ?_, ?_⟩
      · rw [closure_union]; exact h₁.2.1.union h₂.2.1
      · rw [closure_union]; exact union_subset h₁.2.2 h₂.2.2
    -- Step 4 (mass bound) in difference form.
    have hdiff : ∀ W, CompactlyContainedOpen W U → ∀ (η ζ : TestFormOn U k) (δ : ℝ),
        tsupport (η : DifferentialForm (Eucl P) k) ⊆ W →
        tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ W →
        (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) k) x -
          (ζ : DifferentialForm (Eucl P) k) x) ≤ δ) →
        |T η - T ζ| ≤ (T.massOn W).toReal * δ := by
      intro W hW η ζ δ hη hζ hδ
      have hB : T.massOn W ≤ ENNReal.ofReal (T.massOn W).toReal := by
        rw [ENNReal.ofReal_toReal (hT W hW).ne]
      have hsupp : tsupport ((η - ζ : TestFormOn U k) : DifferentialForm (Eucl P) k) ⊆ W := by
        have : ((η - ζ : TestFormOn U k) : DifferentialForm (Eucl P) k) =
            fun x => (η : DifferentialForm (Eucl P) k) x - (ζ : DifferentialForm (Eucl P) k) x := rfl
        rw [this]
        exact (tsupport_sub _ _).trans (union_subset hη hζ)
      have h := hmass P k U W T (η - ζ) (T.massOn W).toReal δ ENNReal.toReal_nonneg hB hsupp
        (fun x => hδ x)
      have hsub : T (η - ζ) = T η - T ζ := map_sub T.toCurrent η ζ
      rwa [hsub] at h
    -- Approximation of every `g ∈ 𝒦` by test forms supported in some `W ⊂⊂ U` (Step 5).
    have happrox : ∀ g : Eucl P → Covector (Eucl P) k, Continuous g → HasCompactSupport g →
        tsupport g ⊆ U → ∃ W, CompactlyContainedOpen W U ∧ tsupport g ⊆ W ∧
          ∃ η : ℕ → TestFormOn U k, (∀ j, tsupport (η j : DifferentialForm (Eucl P) k) ⊆ W) ∧
            ∀ j x, covectorEuclideanNorm (g x - (η j : DifferentialForm (Eucl P) k) x) ≤
              1 / ((j : ℝ) + 1) := by
      intro g hg hgc hgU
      obtain ⟨W, hWo, hgW, hWU, hWc⟩ :=
        exists_open_between_and_isCompact_closure hgc.isCompact hU hgU
      refine ⟨W, ⟨hWo, hWc, hWU⟩, hgW, ?_⟩
      have := fun j : ℕ => hmoll P k U W g hWo (subset_closure.trans hWU) hg hgc hgW
        (1 / ((j : ℝ) + 1)) (by positivity)
      choose η hηW hη using this
      exact ⟨η, hηW, hη⟩
    choose! Wg hWg hgWg ηg hηgW hηg using happrox
    let L : (Eucl P → Covector (Eucl P) k) → ℝ := fun g => limUnder atTop (fun j => T (ηg g j))
    have hinv : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    -- The approximating values converge to `L g`.
    have hconv : ∀ g : Eucl P → Covector (Eucl P) k, Continuous g → HasCompactSupport g →
        tsupport g ⊆ U → Tendsto (fun j => T (ηg g j)) atTop (𝓝 (L g)) := by
      intro g hg hgc hgU
      apply CauchySeq.tendsto_limUnder
      set B := (T.massOn (Wg g)).toReal with hBdef
      refine cauchySeq_of_le_tendsto_0 (fun M : ℕ => B * (2 * (1 / ((M : ℝ) + 1)))) ?_ ?_
      · intro n m M hn hm
        rw [Real.dist_eq]
        have hδ : ∀ x, covectorEuclideanNorm ((ηg g n : DifferentialForm (Eucl P) k) x -
            (ηg g m : DifferentialForm (Eucl P) k) x) ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
          intro x
          have h1 := hηg g hg hgc hgU n x
          have h2 := hηg g hg hgc hgU m x
          have := hN_sub (g x - (ηg g m : DifferentialForm (Eucl P) k) x)
            (g x - (ηg g n : DifferentialForm (Eucl P) k) x)
          have hrw : (g x - (ηg g m : DifferentialForm (Eucl P) k) x) -
              (g x - (ηg g n : DifferentialForm (Eucl P) k) x) =
              (ηg g n : DifferentialForm (Eucl P) k) x - (ηg g m : DifferentialForm (Eucl P) k) x := by
            abel
          rw [hrw] at this
          linarith
        have h := hdiff (Wg g) (hWg g hg hgc hgU) (ηg g n) (ηg g m) _
          (hηgW g hg hgc hgU n) (hηgW g hg hgc hgU m) hδ
        have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
        have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
        have hm' : 1 / ((m : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hm 1
        calc |T (ηg g n) - T (ηg g m)| ≤ B * (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := h
          _ ≤ B * (2 * (1 / ((M : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hB0; linarith
      · have := (hinv.const_mul 2).const_mul B
        simpa using this
    -- Independence of the approximating sequence (and of its support set `W`).
    have hlim : ∀ g : Eucl P → Covector (Eucl P) k, Continuous g → HasCompactSupport g →
        tsupport g ⊆ U → ∀ (W : Set (Eucl P)) (ζ : ℕ → TestFormOn U k) (δ : ℕ → ℝ),
        CompactlyContainedOpen W U → (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ W) →
        Tendsto δ atTop (𝓝 0) →
        (∀ j x, covectorEuclideanNorm (g x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ δ j) →
        Tendsto (fun j => T (ζ j)) atTop (𝓝 (L g)) := by
      intro g hg hgc hgU W ζ δ hW hζW hδ hζ
      have hW' := hcco_union W (Wg g) hW (hWg g hg hgc hgU)
      set B := (T.massOn (W ∪ Wg g)).toReal
      refine (hconv g hg hgc hgU).congr_dist ?_
      refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_) (g := fun j : ℕ => B * (1 / ((j : ℝ) + 1) + δ j)) ?_
      · rw [Real.dist_eq]
        apply hdiff (W ∪ Wg g) hW' (ηg g j) (ζ j)
        · exact (hηgW g hg hgc hgU j).trans subset_union_right
        · exact (hζW j).trans subset_union_left
        · intro x
          have h1 := hηg g hg hgc hgU j x
          have h2 := hζ j x
          have := hN_sub (g x - (ζ j : DifferentialForm (Eucl P) k) x)
            (g x - (ηg g j : DifferentialForm (Eucl P) k) x)
          have hrw : (g x - (ζ j : DifferentialForm (Eucl P) k) x) -
              (g x - (ηg g j : DifferentialForm (Eucl P) k) x) =
              (ηg g j : DifferentialForm (Eucl P) k) x - (ζ j : DifferentialForm (Eucl P) k) x := by
            abel
          rw [hrw] at this
          linarith
      · have := (hinv.add hδ).const_mul B
        simpa using this
    -- Membership of a test form in `𝒦`.
    have hmemω : ∀ ω : TestFormOn U k, Continuous (ω : DifferentialForm (Eucl P) k) ∧
        HasCompactSupport (ω : DifferentialForm (Eucl P) k) ∧
        tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U :=
      fun ω => ⟨ω.property.1.1.continuous, ω.property.1.2, ω.property.2⟩
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    · -- (a) `L` extends `T`.
      intro ω
      obtain ⟨hc, hcs, hsU⟩ := hmemω ω
      have h := hlim _ hc hcs hsU (Wg (ω : DifferentialForm (Eucl P) k)) (fun _ => ω) (fun _ => 0)
        (hWg _ hc hcs hsU) (fun _ => hgWg _ hc hcs hsU) tendsto_const_nhds
        (fun j x => by simp)
      exact tendsto_nhds_unique h tendsto_const_nhds
    · -- (b) additivity on `𝒦`.
      intro g₁ g₂ h1 h1c h1U h2 h2c h2U
      have h12 : Continuous (g₁ + g₂) := h1.add h2
      have h12c : HasCompactSupport (g₁ + g₂) := h1c.add h2c
      have h12U : tsupport (g₁ + g₂) ⊆ U := (tsupport_add g₁ g₂).trans (union_subset h1U h2U)
      have h := hlim (g₁ + g₂) h12 h12c h12U (Wg g₁ ∪ Wg g₂)
        (fun j => ηg g₁ j + ηg g₂ j) (fun j => 2 * (1 / ((j : ℝ) + 1)))
        (hcco_union _ _ (hWg g₁ h1 h1c h1U) (hWg g₂ h2 h2c h2U)) ?_ ?_ ?_
      · have hsum : Tendsto (fun j => T (ηg g₁ j + ηg g₂ j)) atTop (𝓝 (L g₁ + L g₂)) := by
          have := (hconv g₁ h1 h1c h1U).add (hconv g₂ h2 h2c h2U)
          refine this.congr fun j => ?_
          exact (map_add T.toCurrent (ηg g₁ j) (ηg g₂ j)).symm
        exact tendsto_nhds_unique h hsum
      · intro j
        have : ((ηg g₁ j + ηg g₂ j : TestFormOn U k) : DifferentialForm (Eucl P) k) =
            (ηg g₁ j : DifferentialForm (Eucl P) k) + (ηg g₂ j : DifferentialForm (Eucl P) k) := rfl
        rw [this]
        exact (tsupport_add _ _).trans (union_subset_union (hηgW g₁ h1 h1c h1U j)
          (hηgW g₂ h2 h2c h2U j))
      · simpa using hinv.const_mul 2
      · intro j x
        have e1 := hηg g₁ h1 h1c h1U j x
        have e2 := hηg g₂ h2 h2c h2U j x
        have := hN_add (g₁ x - (ηg g₁ j : DifferentialForm (Eucl P) k) x)
          (g₂ x - (ηg g₂ j : DifferentialForm (Eucl P) k) x)
        have hrw : (g₁ + g₂) x - ((ηg g₁ j + ηg g₂ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x
            = (g₁ x - (ηg g₁ j : DifferentialForm (Eucl P) k) x) +
              (g₂ x - (ηg g₂ j : DifferentialForm (Eucl P) k) x) := by
          simp only [Pi.add_apply, Submodule.coe_add]
          abel
        rw [hrw]
        linarith
    · -- (c) homogeneity on `𝒦`.
      intro c g hg hgc hgU
      have hcg : Continuous (c • g) := hg.const_smul c
      have hcgc : HasCompactSupport (c • g) := hgc.smul_left
      have hcgU : tsupport (c • g) ⊆ U := (tsupport_smul_subset_right (fun _ => c) g).trans hgU
      have h := hlim (c • g) hcg hcgc hcgU (Wg g) (fun j => c • ηg g j)
        (fun j => |c| * (1 / ((j : ℝ) + 1))) (hWg g hg hgc hgU) ?_ ?_ ?_
      · have hsc : Tendsto (fun j => T (c • ηg g j)) atTop (𝓝 (c * L g)) := by
          have := (hconv g hg hgc hgU).const_mul c
          refine this.congr fun j => ?_
          exact (map_smul T.toCurrent c (ηg g j)).symm
        exact tendsto_nhds_unique h hsc
      · intro j
        have : ((c • ηg g j : TestFormOn U k) : DifferentialForm (Eucl P) k) =
            fun x => c • (ηg g j : DifferentialForm (Eucl P) k) x := rfl
        rw [this]
        exact (tsupport_smul_subset_right (fun _ => c) _).trans (hηgW g hg hgc hgU j)
      · simpa using hinv.const_mul |c|
      · intro j x
        have e1 := hηg g hg hgc hgU j x
        have hrw : (c • g) x - ((c • ηg g j : TestFormOn U k) : DifferentialForm (Eucl P) k) x =
            c • (g x - (ηg g j : DifferentialForm (Eucl P) k) x) := by
          simp only [Pi.smul_apply, Submodule.coe_smul, smul_sub]
        rw [hrw, hN_smul]
        exact mul_le_mul_of_nonneg_left e1 (abs_nonneg c)
    · -- (d) the mass bound `L g ≤ M_W(T)`.
      intro W g hW hg hgW hg1
      have hgc : HasCompactSupport g :=
        hW.2.1.of_isClosed_subset (isClosed_tsupport g) (hgW.trans subset_closure)
      have hgU : tsupport g ⊆ U := hgW.trans (subset_closure.trans hW.2.2)
      have := fun j : ℕ => hmoll P k U W g hW.1 (subset_closure.trans hW.2.2) hg hgc hgW
        (1 / ((j : ℝ) + 1)) (by positivity)
      choose η hηW hη using this
      have h := hlim g hg hgc hgU W η (fun j => 1 / ((j : ℝ) + 1)) hW hηW hinv hη
      set B := (T.massOn W).toReal with hBdef
      have hB : T.massOn W ≤ ENNReal.ofReal B := by rw [hBdef, ENNReal.ofReal_toReal (hT W hW).ne]
      have hbound : ∀ j, T (η j) ≤ B * (1 + 1 / ((j : ℝ) + 1)) := by
        intro j
        have hj := hmass P k U W T (η j) B (1 + 1 / ((j : ℝ) + 1)) ENNReal.toReal_nonneg hB (hηW j)
          (fun x => by
            have h1 := hη j x
            have h2 := hg1 x
            have := hN_sub (g x) (g x - (η j : DifferentialForm (Eucl P) k) x)
            have hrw : g x - (g x - (η j : DifferentialForm (Eucl P) k) x) =
                (η j : DifferentialForm (Eucl P) k) x := by abel
            rw [hrw] at this
            linarith)
        exact (le_abs_self _).trans hj
      have hlimB : Tendsto (fun j : ℕ => B * (1 + 1 / ((j : ℝ) + 1))) atTop (𝓝 B) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).add hinv
        simpa using this.const_mul B
      have hLB : L g ≤ B := le_of_tendsto_of_tendsto' h hlimB hbound
      calc ENNReal.ofReal (L g) ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hLB
        _ = T.massOn W := by rw [hBdef, ENNReal.ofReal_toReal (hT W hW).ne]
  -- Steps 6, 8 and 10 (Simon 1, 4.14 on the open set `U`, push-forward, Borel version).
  have h_riesz_open : ∀ (P : ℕ) (ι : Type) [Fintype ι] (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ ι) → ℝ, (∀ g₁ g₂ : Eucl P → EuclideanSpace ℝ ι, Continuous g₁ → HasCompactSupport g₁ → tsupport g₁ ⊆ U → Continuous g₂ → HasCompactSupport g₂ → tsupport g₂ ⊆ U → L (g₁ + g₂) = L g₁ + L g₂) → (∀ (c : ℝ) (g : Eucl P → EuclideanSpace ℝ ι), Continuous g → HasCompactSupport g → tsupport g ⊆ U → L (c • g) = c * L g) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Eucl P → EuclideanSpace ℝ ι, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → L g ≤ C) → ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ ι), μ Uᶜ = 0 ∧ StronglyMeasurable ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ (∀ g : Eucl P → EuclideanSpace ℝ ι, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Integrable (fun x => inner ℝ (g x) (ν x)) μ ∧ L g = ∫ x, inner ℝ (g x) (ν x) ∂μ) ∧ ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → μ W = ⨆ (g : Eucl P → EuclideanSpace ℝ ι) (_ : Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ W ∧ ∀ x, ‖g x‖ ≤ 1), ENNReal.ofReal (L g) := by
    intro P ι _ U hU L hLadd hLsmul hLbdd
    classical
    have : LocallyCompactSpace U := hU.locallyCompactSpace
    -- Zero extension of compactly supported continuous maps on the open subspace `U`.
    let ext : C_c(U, EuclideanSpace ℝ ι) → Eucl P → EuclideanSpace ℝ ι :=
      fun f x => if hx : x ∈ U then f ⟨x, hx⟩ else 0
    have hext_eq : ∀ f : C_c(U, EuclideanSpace ℝ ι), ext f = Function.extend Subtype.val f 0 := by
      intro f; funext x
      by_cases hx : x ∈ U
      · simp only [ext, hx, ↓reduceDIte]
        exact (Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩).symm
      · simp only [ext, hx, ↓reduceDIte]
        rw [Function.extend_apply']
        · rfl
        · rintro ⟨y, rfl⟩; exact hx y.2
    have hext_val : ∀ (f : C_c(U, EuclideanSpace ℝ ι)) (y : U), ext f y = f y := by
      intro f y; simp [ext, y.2]
    have hext_out : ∀ (f : C_c(U, EuclideanSpace ℝ ι)) (x : Eucl P), x ∉ U → ext f x = 0 := by
      intro f x hx; simp [ext, hx]
    have hext_cont : ∀ f : C_c(U, EuclideanSpace ℝ ι), Continuous (ext f) := by
      intro f; rw [hext_eq]
      exact HasCompactSupport.continuous_extend_zero hU f.continuous f.hasCompactSupport
    have hext_tsupp : ∀ f : C_c(U, EuclideanSpace ℝ ι),
        tsupport (ext f) ⊆ Subtype.val '' tsupport f := by
      intro f
      have hK : IsCompact (Subtype.val '' tsupport f) :=
        f.hasCompactSupport.isCompact.image continuous_subtype_val
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_cases hxU : x ∈ U
      · refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
        rw [Function.mem_support] at hx ⊢
        rwa [← hext_val f ⟨x, hxU⟩]
      · exact absurd (hext_out f x hxU) hx
    have hext_cs : ∀ f : C_c(U, EuclideanSpace ℝ ι), HasCompactSupport (ext f) := by
      intro f
      exact (f.hasCompactSupport.isCompact.image continuous_subtype_val).of_isClosed_subset
        (isClosed_tsupport _) (hext_tsupp f)
    have hext_U : ∀ f : C_c(U, EuclideanSpace ℝ ι), tsupport (ext f) ⊆ U := by
      intro f
      refine (hext_tsupp f).trans ?_
      rintro _ ⟨y, -, rfl⟩; exact y.2
    have hext_add : ∀ f g : C_c(U, EuclideanSpace ℝ ι), ext (f + g) = ext f + ext g := by
      intro f g; funext x
      by_cases hx : x ∈ U
      · simp [ext, hx]
      · simp [ext, hx]
    have hext_smul : ∀ (c : ℝ) (f : C_c(U, EuclideanSpace ℝ ι)), ext (c • f) = c • ext f := by
      intro c f; funext x
      by_cases hx : x ∈ U
      · simp [ext, hx]
      · simp [ext, hx]
    have hext_norm : ∀ (f : C_c(U, EuclideanSpace ℝ ι)) (b : ℝ), 0 ≤ b → (∀ y, ‖f y‖ ≤ b) →
        ∀ x, ‖ext f x‖ ≤ b := by
      intro f b hb hf x
      by_cases hx : x ∈ U
      · rw [show ext f x = f ⟨x, hx⟩ from hext_val f ⟨x, hx⟩]; exact hf _
      · rw [hext_out f x hx, norm_zero]; exact hb
    -- The functional on `C_c(U, H)` (Step 6, `X := U`).
    let Λ : C_c(U, EuclideanSpace ℝ ι) →ₗ[ℝ] ℝ :=
      { toFun := fun f => L (ext f)
        map_add' := fun f g => by
          simp only [hext_add]
          exact hLadd _ _ (hext_cont f) (hext_cs f) (hext_U f) (hext_cont g) (hext_cs g) (hext_U g)
        map_smul' := fun c f => by
          simp only [hext_smul, RingHom.id_apply, smul_eq_mul]
          exact hLsmul c _ (hext_cont f) (hext_cs f) (hext_U f) }
    have hΛ : Poincare.SimonGMT.Chapter01.IsLocallyBoundedCcFunctional Λ := by
      intro K hK
      have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
      obtain ⟨C, hC⟩ := hLbdd _ hK' (by rintro _ ⟨y, -, rfl⟩; exact y.2)
      refine ⟨C, ?_⟩
      rintro _ ⟨ω, ⟨hω1, hωK⟩, rfl⟩
      exact hC (ext ω) (hext_cont ω) ((hext_tsupp ω).trans (image_mono hωK))
        (hext_norm ω 1 zero_le_one hω1)
    -- Simon 1, 4.14 (vector Riesz) and the envelope identity (†).
    obtain ⟨ν₀, hν₀, hν₀1, hrep⟩ := Poincare.SimonGMT.Chapter01.simon_theorem_4_14_caratheodory Λ hΛ
    set μU := Poincare.SimonGMT.Chapter01.vectorFunctionalEnvelopeMeasure Λ hΛ with hμU
    have : SigmaCompactSpace U := inferInstance
    have : IsFiniteMeasureOnCompacts μU := inferInstance
    -- Step 10: a Borel version of the Carathéodory-measurable field.
    have hcarath_null : ∀ A : Set U, MeasurableSet[μU.toOuterMeasure.caratheodory] A →
        NullMeasurableSet A μU := by
      intro A hA
      set An : ℕ → Set U := fun n => A ∩ compactCovering U n
      have hAn : ∀ n, MeasurableSet[μU.toOuterMeasure.caratheodory] (An n) := fun n =>
        hA.inter (le_toOuterMeasure_caratheodory μU _
          (isCompact_compactCovering U n).isClosed.measurableSet)
      have hfin : ∀ n, μU (An n) < ∞ := fun n =>
        (measure_mono inter_subset_right).trans_lt (isCompact_compactCovering U n).measure_lt_top
      set B : ℕ → Set U := fun n => toMeasurable μU (An n)
      have hnull : ∀ n, μU (B n \ An n) = 0 := by
        intro n
        have h := (OuterMeasure.isCaratheodory_iff μU.toOuterMeasure).1 (hAn n) (B n)
        have hinter : B n ∩ An n = An n := inter_eq_right.2 (subset_toMeasurable μU _)
        rw [hinter] at h
        change μU (B n) = μU (An n) + μU (B n \ An n) at h
        rw [measure_toMeasurable] at h
        exact (ENNReal.add_right_inj (hfin n).ne).1 (h.symm.trans (add_zero _).symm)
      have hAB : A ⊆ ⋃ n, B n := by
        intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.1 ((iUnion_compactCovering U).symm ▸ mem_univ x)
        exact mem_iUnion.2 ⟨n, subset_toMeasurable μU _ ⟨hx, hn⟩⟩
      have hdiff : μU ((⋃ n, B n) \ A) = 0 := by
        apply measure_mono_null _ (measure_iUnion_null hnull)
        intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.1 hx.1
        exact mem_iUnion.2 ⟨n, hn, fun h => hx.2 h.1⟩
      refine (MeasurableSet.iUnion fun n => measurableSet_toMeasurable μU (An n)).nullMeasurableSet.congr ?_
      refine ae_eq_set.2 ⟨hdiff, ?_⟩
      rw [sdiff_eq_empty.2 hAB, measure_empty]
    have hν₀null : NullMeasurable ν₀ μU := by
      intro s hs
      exact hcarath_null _ (hν₀.measurable hs)
    have hν₀ae : AEMeasurable ν₀ μU := hν₀null.aemeasurable
    have hν₀1' : ∀ᵐ y ∂μU, ‖ν₀ y‖ = 1 :=
      (Poincare.SimonGMT.Chapter01.ae_radonCaratheodoryMeasure_iff μU).1 hν₀1
    obtain ⟨ν₂, hν₂m, hν₂le, hν₀₂⟩ : ∃ ν₂ : U → EuclideanSpace ℝ ι, Measurable ν₂ ∧
        (∀ y, ‖ν₂ y‖ ≤ 1) ∧ ν₀ =ᵐ[μU] ν₂ := by
      obtain ⟨ν₁, hν₁m, hν₀₁⟩ : ∃ ν₁ : U → EuclideanSpace ℝ ι, Measurable ν₁ ∧ ν₀ =ᵐ[μU] ν₁ :=
        ⟨hν₀ae.mk ν₀, hν₀ae.measurable_mk, hν₀ae.ae_eq_mk⟩
      refine ⟨fun y => if ‖ν₁ y‖ ≤ 1 then ν₁ y else 0,
        Measurable.ite (measurableSet_le hν₁m.norm measurable_const) hν₁m measurable_const,
        fun y => ?_, ?_⟩
      · show ‖(if ‖ν₁ y‖ ≤ 1 then ν₁ y else 0)‖ ≤ 1
        split_ifs with h
        · exact h
        · simp
      · filter_upwards [hν₀₁, hν₀1'] with y h1 h2
        simp only [← h1, h2, le_refl, ite_true]
    have hν₂1 : ∀ᵐ y ∂μU, ‖ν₂ y‖ = 1 := by
      filter_upwards [hν₀₂, hν₀1'] with y h1 h2
      rw [← h1, h2]
    have hrepU : ∀ f : C_c(U, EuclideanSpace ℝ ι), Λ f = ∫ y, inner ℝ (f y) (ν₂ y) ∂μU := by
      intro f
      rw [hrep f]
      have hae : (fun y => inner ℝ (f y) (ν₀ y)) =ᵐ[Poincare.SimonGMT.Chapter01.radonCaratheodoryMeasure μU]
          (fun y => inner ℝ (f y) (ν₂ y)) := by
        refine (Poincare.SimonGMT.Chapter01.ae_radonCaratheodoryMeasure_iff μU).2 ?_
        filter_upwards [hν₀₂] with y hy
        rw [hy]
      rw [integral_congr_ae hae]
      apply Poincare.SimonGMT.Chapter01.integral_radonCaratheodoryMeasure
      have : Measurable fun y => inner ℝ (f y) (ν₂ y) :=
        (continuous_fst.inner continuous_snd).measurable.comp (f.continuous.measurable.prodMk hν₂m)
      exact this.stronglyMeasurable
    have hintU : ∀ f : C_c(U, EuclideanSpace ℝ ι), Integrable (fun y => inner ℝ (f y) (ν₂ y)) μU := by
      intro f
      have hf : Integrable (fun y => f y) μU := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      refine hf.norm.mono' ?_ (Eventually.of_forall fun y => ?_)
      · exact ((continuous_fst.inner continuous_snd).measurable.comp
          (f.continuous.measurable.prodMk hν₂m)).aestronglyMeasurable
      · calc ‖inner ℝ (f y) (ν₂ y)‖ ≤ ‖f y‖ * ‖ν₂ y‖ := norm_inner_le_norm _ _
          _ ≤ ‖f y‖ * 1 := mul_le_mul_of_nonneg_left (hν₂le y) (norm_nonneg _)
          _ = ‖f y‖ := mul_one _
    -- Step 8: push forward to `ℝ^P`.
    have hemb : MeasurableEmbedding (Subtype.val : U → Eucl P) :=
      MeasurableEmbedding.subtype_coe hU.measurableSet
    obtain ⟨μ, hμdef⟩ : ∃ μ : Measure (Eucl P), μ = Measure.map Subtype.val μU := ⟨_, rfl⟩
    obtain ⟨ν, hνval, hνout, hνm⟩ : ∃ ν : Eucl P → EuclideanSpace ℝ ι, (∀ y : U, ν y = ν₂ y) ∧
        (∀ x, x ∉ U → ν x = 0) ∧ Measurable ν := by
      refine ⟨fun x => if hx : x ∈ U then ν₂ ⟨x, hx⟩ else 0, fun y => by simp,
        fun x hx => by simp [hx], ?_⟩
      exact Measurable.dite (f := ν₂) (g := fun _ => (0 : EuclideanSpace ℝ ι)) hν₂m
        measurable_const hU.measurableSet
    have hνle : ∀ x, ‖ν x‖ ≤ 1 := by
      intro x; by_cases hx : x ∈ U
      · rw [show ν x = ν₂ ⟨x, hx⟩ from hνval ⟨x, hx⟩]; exact hν₂le _
      · rw [hνout x hx, norm_zero]; exact zero_le_one
    -- Restriction of a compactly supported map on `ℝ^P` to `U`.
    have hrestr : ∀ g : Eucl P → EuclideanSpace ℝ ι, Continuous g → HasCompactSupport g →
        tsupport g ⊆ U → ∃ f : C_c(U, EuclideanSpace ℝ ι), (∀ y : U, f y = g y) ∧ ext f = g := by
      intro g hg hgc hgU
      have hcomp : IsCompact (Subtype.val ⁻¹' tsupport g : Set U) := by
        rw [Subtype.isCompact_iff]
        have : Subtype.val '' (Subtype.val ⁻¹' tsupport g : Set U) = tsupport g := by
          rw [image_preimage_eq_inter_range, Subtype.range_coe]; exact inter_eq_left.2 hgU
        rw [this]; exact hgc.isCompact
      let f : C_c(U, EuclideanSpace ℝ ι) :=
        { toFun := fun y => g y
          continuous_toFun := hg.comp continuous_subtype_val
          hasCompactSupport' := hcomp.of_isClosed_subset (isClosed_tsupport _)
            (tsupport_comp_subset_preimage g continuous_subtype_val) }
      refine ⟨f, fun y => rfl, ?_⟩
      funext x
      by_cases hx : x ∈ U
      · rw [show ext f x = f ⟨x, hx⟩ from hext_val f ⟨x, hx⟩]; rfl
      · rw [hext_out f x hx]
        exact (image_eq_zero_of_notMem_tsupport fun h => hx (hgU h)).symm
    refine ⟨μ, ν, ?_, hνm.stronglyMeasurable, ?_, ?_, ?_⟩
    · -- `μ(ℝ^P ∖ U) = 0`
      rw [hμdef, hemb.map_apply]
      have : (Subtype.val ⁻¹' Uᶜ : Set U) = ∅ := by
        ext y; simp
      rw [this, measure_empty]
    · -- `‖ν‖ = 1` `μ`-a.e.
      rw [hμdef, hemb.ae_map_iff]
      filter_upwards [hν₂1] with y hy
      rw [hνval]; exact hy
    · -- integrability and the representation (Step 11 in coordinates)
      intro g hg hgc hgU
      obtain ⟨f, hf, hfg⟩ := hrestr g hg hgc hgU
      have hcomp : (fun y : U => inner ℝ (g y) (ν y)) = fun y => inner ℝ (f y) (ν₂ y) := by
        funext y; rw [hf, hνval]
      constructor
      · rw [hμdef, hemb.integrable_map_iff]
        change Integrable (fun y : U => inner ℝ (g y) (ν y)) μU
        rw [hcomp]; exact hintU f
      · rw [hμdef, hemb.integral_map, hcomp, ← hrepU f]
        show L g = L (ext f)
        rw [hfg]
    · -- the envelope formula for `μ(W)`
      intro W hWo hWU
      set S : ℝ≥0∞ := ⨆ (g : Eucl P → EuclideanSpace ℝ ι) (_ : Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ W ∧ ∀ x, ‖g x‖ ≤ 1), ENNReal.ofReal (L g) with hS
      have hμW : μ W = μU (Subtype.val ⁻¹' W) := by rw [hμdef]; exact hemb.map_apply μU W
      apply le_antisymm
      · -- `μ(W) ≤ S`: inner regularity, Urysohn and the envelope identity
        rw [hμW]
        have hW'o : IsOpen (Subtype.val ⁻¹' W : Set U) := hWo.preimage continuous_subtype_val
        rw [hW'o.measure_eq_iSup_isCompact μU]
        refine iSup_le fun K => iSup_le fun hKW => iSup_le fun hK => ?_
        obtain ⟨φ, hφ1, hφc, hφW, hφr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hW'o hKW
        obtain ⟨u, hu⟩ : ∃ u : C_c(U, ℝ≥0), ∀ y, (u y : ℝ) = φ y := by
          refine ⟨⟨⟨fun y => ⟨φ y, (Set.mem_Icc.1 (hφr y)).1⟩, φ.continuous.subtype_mk _⟩, ?_⟩,
            fun y => rfl⟩
          refine hφc.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
          intro y hy h0
          exact hy (Subtype.ext h0)
        have hu_int : Integrable (fun y => (u y : ℝ)) μU :=
          (NNReal.continuous_coe.comp u.continuous).integrable_of_hasCompactSupport
            (u.hasCompactSupport.comp_left (by simp))
        have hKu : μU K ≤ ENNReal.ofReal (∫ y, (u y : ℝ) ∂μU) := by
          rw [ofReal_integral_eq_lintegral_ofReal hu_int (Eventually.of_forall fun y => (u y).2),
            ← lintegral_indicator_one hK.isClosed.measurableSet]
          apply lintegral_mono
          intro y
          by_cases hy : y ∈ K
          · simp [indicator_of_mem hy, hu, hφ1 hy]
          · simp [indicator_of_notMem hy]
        have henv := Poincare.SimonGMT.Chapter01.simon_theorem_4_14_positive_envelope Λ hΛ u
        rw [← henv] at hKu
        refine hKu.trans ?_
        by_cases hStop : S = ∞
        · rw [hStop]; exact le_top
        · have hbd : ∀ b ∈ Λ '' {ω : C_c(U, EuclideanSpace ℝ ι) | ∀ x, ‖ω x‖ ≤ (u x : ℝ)},
              b ≤ S.toReal := by
            rintro _ ⟨ω, hω, rfl⟩
            have hωsupp : tsupport ω ⊆ tsupport φ := by
              apply closure_mono
              intro y hy
              rw [Function.mem_support] at hy ⊢
              intro h0
              apply hy
              have := hω y
              rw [hu, h0] at this
              exact norm_le_zero_iff.1 this
            have hadm : Continuous (ext ω) ∧ HasCompactSupport (ext ω) ∧ tsupport (ext ω) ⊆ W ∧
                ∀ x, ‖ext ω x‖ ≤ 1 := by
              refine ⟨hext_cont ω, hext_cs ω, ?_, hext_norm ω 1 zero_le_one fun y => ?_⟩
              · refine (hext_tsupp ω).trans ?_
                rintro _ ⟨y, hy, rfl⟩
                exact hφW (hωsupp hy)
              · exact (hω y).trans (by rw [hu]; exact (Set.mem_Icc.1 (hφr y)).2)
            have hle : ENNReal.ofReal (L (ext ω)) ≤ S :=
              le_iSup₂_of_le (f := fun (g : Eucl P → EuclideanSpace ℝ ι)
                (_ : Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ W ∧ ∀ x, ‖g x‖ ≤ 1) =>
                  ENNReal.ofReal (L g)) (ext ω) hadm le_rfl
            exact (ENNReal.ofReal_le_iff_le_toReal hStop).1 hle
          have hne : (Λ '' {ω : C_c(U, EuclideanSpace ℝ ι) | ∀ x, ‖ω x‖ ≤ (u x : ℝ)}).Nonempty :=
            ⟨Λ 0, 0, fun x => by simp, rfl⟩
          calc ENNReal.ofReal (sSup (Λ '' {ω : C_c(U, EuclideanSpace ℝ ι) | ∀ x, ‖ω x‖ ≤ (u x : ℝ)}))
              ≤ ENNReal.ofReal S.toReal := ENNReal.ofReal_le_ofReal (csSup_le hne hbd)
            _ = S := ENNReal.ofReal_toReal hStop
      · -- `S ≤ μ(W)`: the representation and `‖ν‖ ≤ 1`
        refine iSup₂_le fun g hg => ?_
        obtain ⟨hgc, hgcs, hgW, hg1⟩ := hg
        have hgU : tsupport g ⊆ U := hgW.trans hWU
        obtain ⟨f, hf, hfg⟩ := hrestr g hgc hgcs hgU
        have hLg : L g = ∫ y, inner ℝ (f y) (ν₂ y) ∂μU := by
          rw [← hrepU f]; show L g = L (ext f); rw [hfg]
        rw [hLg, hμW]
        set A : Set U := Subtype.val ⁻¹' tsupport g
        have hA : MeasurableSet A := (isClosed_tsupport g).measurableSet.preimage measurable_subtype_coe
        have hAW : A ⊆ Subtype.val ⁻¹' W := preimage_mono hgW
        have hAfin : μU A < ∞ := by
          have : IsCompact A := by
            rw [Subtype.isCompact_iff]
            have : Subtype.val '' A = tsupport g := by
              rw [image_preimage_eq_inter_range, Subtype.range_coe]; exact inter_eq_left.2 hgU
            rw [this]; exact hgcs.isCompact
          exact this.measure_lt_top
        have hle : ∫ y, inner ℝ (f y) (ν₂ y) ∂μU ≤ ∫ y, A.indicator 1 y ∂μU := by
          apply integral_mono (hintU f)
          · exact (integrable_indicator_iff hA).2 (integrableOn_const hAfin.ne)
          · intro y
            by_cases hy : y ∈ A
            · rw [indicator_of_mem hy]
              calc inner ℝ (f y) (ν₂ y) ≤ ‖f y‖ * ‖ν₂ y‖ := real_inner_le_norm _ _
                _ ≤ 1 * 1 := by
                  apply mul_le_mul _ (hν₂le y) (norm_nonneg _) zero_le_one
                  rw [hf]; exact hg1 _
                _ = 1 := one_mul 1
            · rw [indicator_of_notMem hy]
              have : f y = 0 := by rw [hf]; exact image_eq_zero_of_notMem_tsupport hy
              simp [this]
        rw [integral_indicator_one hA] at hle
        calc ENNReal.ofReal (∫ y, inner ℝ (f y) (ν₂ y) ∂μU) ≤ ENNReal.ofReal (μU.real A) :=
              ENNReal.ofReal_le_ofReal hle
          _ = μU A := by rw [measureReal_def, ENNReal.ofReal_toReal hAfin.ne]
          _ ≤ μU (Subtype.val ⁻¹' W) := measure_mono hAW
  -- Assembly (Steps 2, 7, 8, 9, 10, 11).
  intro P k U hU T hT
  by_cases hkP : P < k
  · -- Step 2 (degenerate case `k > P`): `T = 0`, every mass measure is `0`, and `ξ := 0`.
    have hT0 : ∀ ω : TestFormOn U k, T ω = 0 :=
      Submission.br_la_apply_eq_zero_of_lt_degree P k U T hkP
    have hmass0 : ∀ W, T.massOn W = 0 := by
      intro W
      refine le_antisymm (sSup_le ?_) bot_le
      rintro _ ⟨ω, -, rfl⟩
      simp [hT0 ω]
    have hMM0 : IsMassMeasure T (0 : Measure (Eucl P)) :=
      ⟨by simp, fun W _ => by simp [hmass0 W]⟩
    refine ⟨⟨0, hMM0⟩, fun μ hμ => ?_⟩
    have hμ0 : μ = 0 := h_measure_uniqueness P U hU μ 0 hμ.1 (by simp)
      (fun W hW => by rw [hμ.2 W hW, hmass0 W]; simp)
      (fun W hW => by rw [hμ.2 W hW, hmass0 W]; exact ENNReal.zero_lt_top)
    subst hμ0
    exact ⟨fun _ => 0, stronglyMeasurable_const, by simp, fun ω => ⟨by simp, by simp [hT0 ω]⟩⟩
  · -- Main case.
    obtain ⟨e, he_coord, he_norm, he_diag, he_off⟩ := h_coordinates P k
    obtain ⟨L, hLT, hLadd, hLsmul, hLmass⟩ := h_extension P k U hU T hT
    -- the functional in coordinates: L_H g := L (e.symm ∘ g)
    let LH : (Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P)) → ℝ :=
      fun g => L (fun x => e.symm (g x))
    have hcont : ∀ g : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P), Continuous g →
        Continuous (fun x => e.symm (g x)) := fun g hg => e.symm.continuous.comp hg
    have htsupp : ∀ g : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P),
        tsupport (fun x => e.symm (g x)) ⊆ tsupport g := fun g =>
      tsupport_comp_subset (g := fun v => e.symm v) (map_zero e.symm) g
    have hcs : ∀ g : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P), HasCompactSupport g →
        HasCompactSupport (fun x => e.symm (g x)) := fun g hg =>
      hg.comp_left (g := fun v => e.symm v) (map_zero e.symm)
    have hnorm_symm : ∀ v : EuclideanSpace ℝ (SimonMultiIndex k P),
        covectorEuclideanNorm (e.symm v) = ‖v‖ := fun v => by
      rw [← he_norm, e.apply_symm_apply]
    have hLHadd : ∀ g₁ g₂ : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P), Continuous g₁ →
        HasCompactSupport g₁ → tsupport g₁ ⊆ U → Continuous g₂ → HasCompactSupport g₂ →
        tsupport g₂ ⊆ U → LH (g₁ + g₂) = LH g₁ + LH g₂ := by
      intro g₁ g₂ h1 h1c h1U h2 h2c h2U
      have := hLadd _ _ (hcont g₁ h1) (hcs g₁ h1c) ((htsupp g₁).trans h1U)
        (hcont g₂ h2) (hcs g₂ h2c) ((htsupp g₂).trans h2U)
      have hf : (fun x => e.symm ((g₁ + g₂) x)) =
          (fun x => e.symm (g₁ x)) + (fun x => e.symm (g₂ x)) := by
        funext x; simp
      simp only [LH, hf]
      exact this
    have hLHsmul : ∀ (c : ℝ) (g : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P)), Continuous g →
        HasCompactSupport g → tsupport g ⊆ U → LH (c • g) = c * LH g := by
      intro c g hg hgc hgU
      have := hLsmul c _ (hcont g hg) (hcs g hgc) ((htsupp g).trans hgU)
      have hf : (fun x => e.symm ((c • g) x)) = c • (fun x => e.symm (g x)) := by
        funext x; simp
      simp only [LH, hf]
      exact this
    have hLHbdd : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ C : ℝ,
        ∀ g : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P), Continuous g → tsupport g ⊆ K →
          (∀ x, ‖g x‖ ≤ 1) → LH g ≤ C := by
      intro K hK hKU
      obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
      have hW : CompactlyContainedOpen W U := ⟨hWo, hWc, hWU⟩
      refine ⟨(T.massOn W).toReal, fun g hg hgK hg1 => ?_⟩
      have h := hLmass W _ hW (hcont g hg) ((htsupp g).trans (hgK.trans hKW))
        (fun x => by rw [hnorm_symm]; exact hg1 x)
      exact (ENNReal.ofReal_le_iff_le_toReal (hT W hW).ne).1 h
    obtain ⟨μ₀, ν, hμ₀U, hνmeas, hνunit, hrep, hμ₀W⟩ :=
      h_riesz_open P (SimonMultiIndex k P) U hU LH hLHadd hLHsmul hLHbdd
    have hLHω : ∀ ω : TestFormOn U k,
        LH (fun x => e ((ω : DifferentialForm (Eucl P) k) x)) = T ω := by
      intro ω
      have : (fun x => e.symm (e ((ω : DifferentialForm (Eucl P) k) x))) =
          (ω : DifferentialForm (Eucl P) k) := by
        funext x; simp
      simp only [LH, this, hLT]
    have hωcont : ∀ ω : TestFormOn U k, Continuous (ω : DifferentialForm (Eucl P) k) :=
      fun ω => ω.property.1.1.continuous
    have hωcs : ∀ ω : TestFormOn U k,
        HasCompactSupport (fun x => e ((ω : DifferentialForm (Eucl P) k) x)) := fun ω =>
      ω.property.1.2.comp_left (g := fun v => e v) (map_zero e)
    have hωts : ∀ ω : TestFormOn U k,
        tsupport (fun x => e ((ω : DifferentialForm (Eucl P) k) x)) ⊆
          tsupport (ω : DifferentialForm (Eucl P) k) := fun ω =>
      tsupport_comp_subset (g := fun v => e v) (map_zero e) _
    -- (2.8): μ₀(W) = M_W(T) for W ⊂⊂ U
    have hmass : ∀ W, CompactlyContainedOpen W U → μ₀ W = T.massOn W := by
      intro W hW
      rw [hμ₀W W hW.1 (subset_closure.trans hW.2.2)]
      apply le_antisymm
      · refine iSup₂_le fun g hg => ?_
        exact hLmass W _ hW (hcont g hg.1) ((htsupp g).trans hg.2.2.1)
          (fun x => by rw [hnorm_symm]; exact hg.2.2.2 x)
      · refine sSup_le ?_
        rintro _ ⟨ω, hω, rfl⟩
        show ENNReal.ofReal (T ω) ≤ _
        rw [← hLHω ω]
        refine le_iSup₂_of_le (f := fun (g : Eucl P → EuclideanSpace ℝ (SimonMultiIndex k P))
          (_ : Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ W ∧ ∀ x, ‖g x‖ ≤ 1) =>
            ENNReal.ofReal (LH g))
          (fun x => e ((ω : DifferentialForm (Eucl P) k) x)) ⟨e.continuous.comp (hωcont ω),
            hωcs ω, (hωts ω).trans hω.1, fun x => by rw [he_norm]; exact hω.2 x⟩ le_rfl
    have hMM : IsMassMeasure T μ₀ := ⟨hμ₀U, hmass⟩
    refine ⟨⟨μ₀, hMM⟩, fun μ hμ => ?_⟩
    -- uniqueness: every mass measure equals μ₀
    have hμeq : μ = μ₀ := h_measure_uniqueness P U hU μ μ₀ hμ.1 hμ₀U
      (fun W hW => by rw [hμ.2 W hW, hmass W hW]) (fun W hW => by rw [hμ.2 W hW]; exact hT W hW)
    subst hμeq
    -- ξ(x) := ⟨ν(x), e(·)⟩
    let eL : Covector (Eucl P) k →L[ℝ] EuclideanSpace ℝ (SimonMultiIndex k P) := e
    let Φ : EuclideanSpace ℝ (SimonMultiIndex k P) → NVector (Eucl P) k :=
      fun v => (innerSL ℝ v).comp eL
    have hΦc : Continuous Φ := (innerSL ℝ).continuous.clm_comp_const eL
    have hΦ : ∀ v φ, Φ v φ = inner ℝ v (e φ) := fun v φ => rfl
    refine ⟨fun x => Φ (ν x), hΦc.comp_stronglyMeasurable hνmeas, ?_, ?_⟩
    · filter_upwards [hνunit] with x hx
      have hcoord : ∀ α, euclideanNVectorCoordinate (Φ (ν x)) α = ν x α := by
        intro α
        rw [euclideanNVectorCoordinate, hΦ, PiLp.inner_apply]
        rw [Finset.sum_eq_single α]
        · rw [he_coord, he_diag]; simp
        · intro β _ hβ
          rw [he_coord, he_off α β (Ne.symm hβ)]; simp
        · simp
      simp only [hcoord]
      have h2 := EuclideanSpace.norm_eq (ν x)
      rw [hx] at h2
      have h3 : (∑ i, ‖(ν x) i‖ ^ 2) = 1 := by
        have h4 := congrArg (· ^ 2) h2
        simp only [one_pow] at h4
        rw [h4, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
      simpa [Real.norm_eq_abs, sq_abs] using h3
    · intro ω
      have hfun : (fun x => Φ (ν x) ((ω : DifferentialForm (Eucl P) k) x)) =
          (fun x => inner ℝ (e ((ω : DifferentialForm (Eucl P) k) x)) (ν x)) := by
        funext x; rw [hΦ, real_inner_comm]
      obtain ⟨hint, heq⟩ := hrep (fun x => e ((ω : DifferentialForm (Eucl P) k) x))
        (e.continuous.comp (hωcont ω)) (hωcs ω) ((hωts ω).trans ω.property.2)
      refine ⟨by rw [hfun]; exact hint, ?_⟩
      rw [hfun, ← heq, hLHω ω]
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

/-- Simon Ch. 6, proof of Theorem 8.1 (pp. 174–175), (10)–(13) and the concluding argument:
the orientation of a rectifiable representation of a current with locally finite boundary mass.
For `Hⁿ`-a.e. `x ∈ M` (weighted tangent space `L`, Lebesgue point of `ξ` for `μ = θ Hⁿ⌞M`,
finite upper densities of `μ` and of the mass measure `ν` of `∂T`), the blow-ups of `T` at `x`
converge to `S_x(ω) = θ(x) ∫_L ⟨ω, ξ(x)⟩ dHⁿ`, while the boundary bound
`|∂T(η^#φ)| ≤ sup |η^#φ| ν(B_{4r}(x)) = O(rⁿ⁺¹)` gives `∂S_x = 0`.  Testing with
`φ = (a ϕ) β`, `a` a covector vanishing on `L`, shows `⟨a ∧ β, ξ(x)⟩ = 0`; in an orthonormal
frame adapted to `L` this forces `ξ(x) = c τ₁ ∧ ⋯ ∧ τₙ`, and `|ξ(x)| = 1` gives `c = ±1`. -/
theorem Submission.rectifiability_orientation : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)), M ⊆ U → NullMeasurableSet M (μHE[m + 1] : Measure (Eucl P)) → CountablyRectifiable (m + 1) M → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) → AEStronglyMeasurable ξ ((μHE[m + 1] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∑ α : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) α) ^ 2 = 1) → (∀ ω : TestFormOn U (m + 1), T ω = tauAction (m + 1) M θ ξ ω) → ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∃ τ : Fin (m + 1) → Eucl P, Orthonormal ℝ τ ∧ HasWeightedApproximateTangentSpaceAt (m + 1) M θ x (Submodule.span ℝ (range τ)) ∧ (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P m
  classical
  -- Concluding argument of the proof of 8.1: a unit `n`-vector killing every `a ∧ β` with `a`
  -- vanishing on the `n`-plane `L` is `±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `L`.
  have hLA : ∀ (w : NVector (Eucl P) (m + 1)) (L : Submodule ℝ (Eucl P)),
      Module.finrank ℝ L = m + 1 →
      (∑ α : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate w α) ^ 2 = 1) →
      (∀ a : Eucl P →L[ℝ] ℝ, (∀ z ∈ L, a z = 0) → ∀ β : Covector (Eucl P) m,
        w (ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight β)) = 0) →
      ∃ τ : Fin (m + 1) → Eucl P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = L ∧
        (w = simpleNVector τ ∨ w = -simpleNVector τ) := by
    intro w L hL hw hvan
    classical
    -- `n ≤ P`
    have hnP : m + 1 ≤ P := by
      have := Submodule.finrank_le L
      rwa [hL, finrank_euclideanSpace_fin] at this
    -- an orthonormal basis `τ` of `L`
    let v : OrthonormalBasis (Fin (m + 1)) ℝ L := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
    let τ : Fin (m + 1) → Eucl P := fun k => ((v k : L) : Eucl P)
    have hτon : Orthonormal ℝ τ := v.orthonormal.comp_linearIsometry L.subtypeₗᵢ
    have hτspan : Submodule.span ℝ (range τ) = L := by
      have hr : range τ = L.subtype '' range (fun k => v k) := by
        rw [← range_comp]; rfl
      have htop : Submodule.span ℝ (range (fun k => v k)) = ⊤ := by
        simpa using v.toBasis.span_eq
      rw [hr, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]
    -- extend `τ` to an orthonormal basis `b` of `ℝ^P`: `b (β₀ k) = τ k`
    let β₀ : SimonMultiIndex (m + 1) P := Fin.castLEOrderEmb hnP
    obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin P) ℝ (Eucl P), ∀ k, b (β₀ k) = τ k := by
      let v' : Fin P → Eucl P := fun i => if h : (i : ℕ) < m + 1 then τ ⟨i, h⟩ else 0
      have hs : Orthonormal ℝ ({i : Fin P | (i : ℕ) < m + 1}.domRestrict v') := by
        have he : Function.Injective
            (fun i : {i : Fin P | (i : ℕ) < m + 1} => (⟨(i : Fin P), i.2⟩ : Fin (m + 1))) := by
          intro i j hij
          apply Subtype.ext
          apply Fin.ext
          simpa using congrArg Fin.val hij
        have heq : {i : Fin P | (i : ℕ) < m + 1}.domRestrict v' =
            τ ∘ (fun i : {i : Fin P | (i : ℕ) < m + 1} => (⟨(i : Fin P), i.2⟩ : Fin (m + 1))) := by
          funext i
          have hi : ((i : Fin P) : ℕ) < m + 1 := i.2
          simp only [Set.domRestrict, v', Function.comp_apply]
          rw [dite_eq_left hi]
        rw [heq]
        exact hτon.comp _ he
      obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq (by simp)
      refine ⟨b, fun k => ?_⟩
      have hk : ((β₀ k : Fin P) : ℕ) < m + 1 := k.isLt
      rw [hb (β₀ k) hk]
      simp only [v']
      rw [dite_eq_left hk]
      rfl
    -- the dual coframe `dτ i = ⟨b i, ·⟩`
    let R : Eucl P →L[ℝ] Eucl P :=
      (b.repr.toContinuousLinearEquiv : Eucl P →L[ℝ] EuclideanSpace ℝ (Fin P))
    have hR : R = (b.repr.toContinuousLinearEquiv : Eucl P →L[ℝ] EuclideanSpace ℝ (Fin P)) := rfl
    let dτ : Fin P → (Eucl P →L[ℝ] ℝ) := fun i => (EuclideanSpace.proj i).comp R
    have hdτ : ∀ i z, dτ i z = inner ℝ (b i) z := fun i z => b.repr_apply_apply z i
    have hdτb : ∀ i j, dτ i (b j) = if i = j then 1 else 0 := by
      intro i j
      rw [hdτ, orthonormal_iff_ite.mp b.orthonormal i j]
    -- coordinates in the frame `b`
    have hexp : ∀ ω : Covector (Eucl P) (m + 1), ω = ∑ β : SimonMultiIndex (m + 1) P,
        ω (fun j => b (β j)) • wedgeCovectors (m + 1) (fun j => dτ (β j)) := by
      intro ω
      let S : Eucl P →L[ℝ] Eucl P :=
        (b.repr.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin P) →L[ℝ] Eucl P)
      have hS : S = (b.repr.symm.toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin P) →L[ℝ] Eucl P) := rfl
      have h1 := Submission.cmb_covector_eq_sum_coord_smul_wedge P (m + 1)
        (covectorPullback (m + 1) S ω)
      have h2 : ω = covectorPullback (m + 1) R (covectorPullback (m + 1) S ω) := by
        ext u
        simp [covectorPullback_apply, hS, hR, Function.comp_def]
      conv_lhs => rw [h2, h1]
      rw [map_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [map_smul, covectorPullback_wedgeCovectors]
      congr 1
      simp [euclideanCovectorCoordinate, covectorPullback_apply, hS, Function.comp_def,
        b.repr_symm_single]
    -- `dτ i` vanishes on `L` for `i ∉ range β₀`
    have hdτL : ∀ i : Fin P, m + 1 ≤ (i : ℕ) → ∀ z ∈ L, dτ i z = 0 := by
      intro i hi z hz
      have hle : Submodule.span ℝ (range τ) ≤ LinearMap.ker (dτ i : Eucl P →ₗ[ℝ] ℝ) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have hik : i ≠ β₀ k := by
          intro h
          have h' : (i : ℕ) = (k : ℕ) := congrArg Fin.val h
          omega
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        rw [← hb k, hdτb, ite_eq_right hik]
      have := hle (hτspan ▸ hz)
      simpa using this
    -- the wedge of a permuted coframe
    have hperm : ∀ (γ : Fin (m + 1) → (Eucl P →L[ℝ] ℝ)) (σ : Equiv.Perm (Fin (m + 1))),
        wedgeCovectors (m + 1) (γ ∘ σ) =
          ((Equiv.Perm.sign σ : ℤ) : ℝ) • wedgeCovectors (m + 1) γ := by
      intro γ σ
      ext u
      rw [ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_det, wedgeCovectors_apply_det,
        smul_eq_mul]
      exact Matrix.det_permute σ (Matrix.of fun i j => γ i (u j))
    -- `w` kills every frame wedge other than `τ*₁ ∧ ⋯ ∧ τ*ₙ`
    have hzero : ∀ β : SimonMultiIndex (m + 1) P, β ≠ β₀ →
        w (wedgeCovectors (m + 1) (fun j => dτ (β j))) = 0 := by
      intro β hβ
      -- the last index of `β` is at least `n`
      have hlast : m + 1 ≤ ((β (Fin.last m) : Fin P) : ℕ) := by
        by_contra hcon
        rw [not_le] at hcon
        apply hβ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : range β ⊆ range β₀ := by
          rintro _ ⟨k, rfl⟩
          have hk : ((β k : Fin P) : ℕ) < m + 1 :=
            lt_of_le_of_lt (β.monotone (Fin.le_last k)) hcon
          exact ⟨⟨β k, hk⟩, Fin.ext rfl⟩
        exact Set.eq_of_subset_of_ncard_le hsub
          (by rw [Set.ncard_range_of_injective β₀.injective,
            Set.ncard_range_of_injective β.injective]) (Set.finite_range _)
      -- rotate the last factor to the front
      let γ : Fin (m + 1) → (Eucl P →L[ℝ] ℝ) :=
        Fin.cons (dτ (β (Fin.last m))) (fun k => dτ (β (Fin.castSucc k)))
      have hrot : (fun j => dτ (β j)) = γ ∘ finRotate (m + 1) := by
        have h := Fin.snoc_eq_cons_rotate (Fin.init (fun j => dτ (β j))) (dτ (β (Fin.last m)))
        rw [Fin.snoc_init_self] at h
        exact h
      have hγw : wedgeCovectors (m + 1) γ = ContinuousAlternatingMap.alternatizeUncurryFin
          ((dτ (β (Fin.last m))).smulRight
            (wedgeCovectors m (fun k => dτ (β (Fin.castSucc k))))) := rfl
      rw [hrot, hperm, map_smul, hγw,
        hvan _ (hdτL _ hlast) (wedgeCovectors m (fun k => dτ (β (Fin.castSucc k)))), smul_zero]
    have hbτ : (fun j => b (β₀ j)) = τ := funext hb
    -- hence `w = c τ₁ ∧ ⋯ ∧ τₙ`
    let c := w (wedgeCovectors (m + 1) (fun j => dτ (β₀ j)))
    have hwc : w = c • simpleNVector τ := by
      ext ω
      rw [smul_apply, simpleNVector_apply, smul_eq_mul]
      conv_lhs => rw [hexp ω]
      rw [map_sum, Finset.sum_eq_single β₀]
      · rw [map_smul, smul_eq_mul, hbτ, mul_comm]
      · intro β _ hβ
        rw [map_smul, hzero β hβ, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    -- `|τ₁ ∧ ⋯ ∧ τₙ| = 1` (Cauchy–Binet for an orthonormal family)
    have hnorm1 : ∑ α : SimonMultiIndex (m + 1) P,
        (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (α j)) τ) ^ 2 = 1 := by
      let Θ := wedgeCovectors (m + 1) (fun j => dτ (β₀ j))
      have hΘ : Θ = wedgeCovectors (m + 1) (fun j => dτ (β₀ j)) := rfl
      have h1 := Submission.cmb_covector_eq_sum_coord_smul_wedge P (m + 1) Θ
      have h2 : Θ τ = 1 := by
        rw [hΘ, wedgeCovectors_apply_det]
        convert Matrix.det_one (n := Fin (m + 1)) (R := ℝ)
        ext i j
        rw [Matrix.of_apply, ← hb j, hdτb, Matrix.one_apply]
        simp [β₀.injective.eq_iff]
      have h3 : ∀ α : SimonMultiIndex (m + 1) P, euclideanCovectorCoordinate Θ α =
          wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (α j)) τ := by
        intro α
        rw [euclideanCovectorCoordinate, hΘ, wedgeCovectors_apply_det, wedgeCovectors_apply_det,
          ← Matrix.det_transpose]
        congr 1
        ext i j
        rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, hdτ, hb,
          EuclideanSpace.inner_single_right]
        simp
      calc ∑ α : SimonMultiIndex (m + 1) P,
            (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (α j)) τ) ^ 2
          = ∑ α : SimonMultiIndex (m + 1) P, euclideanCovectorCoordinate Θ α *
              wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (α j)) τ := by
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [h3, sq]
        _ = Θ τ := by
            conv_rhs => rw [h1]
            rw [ContinuousAlternatingMap.sum_apply]
            simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        _ = 1 := h2
    have hc2 : c ^ 2 = 1 := by
      rw [hwc] at hw
      simp only [euclideanNVectorCoordinate, smul_apply, simpleNVector_apply,
        smul_eq_mul, mul_pow] at hw
      rwa [← Finset.mul_sum, hnorm1, mul_one] at hw
    refine ⟨τ, hτon, hτspan, ?_⟩
    have hcc : c * c = 1 := by rw [← sq]; exact hc2
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · left
      rw [hwc, h, one_smul]
    · right
      rw [hwc, h]
      ext ω
      simp only [smul_apply, neg_apply, simpleNVector_apply, smul_eq_mul,
        neg_one_mul]
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hnormsmul : ∀ (t : ℝ) (α : Covector (Eucl P) m),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- An `n`-vector of coefficient norm `1` has operator norm at most `#I(n, P)`.
  have hξbd : ∀ w : NVector (Eucl P) (m + 1),
      ∑ α : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate w α) ^ 2 = 1 →
      ‖w‖ ≤ (Fintype.card (SimonMultiIndex (m + 1) P) : ℝ) := by
    intro w hw
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ω => ?_
    have hω := congrArg w (Submission.cmb_covector_eq_sum_coord_smul_wedge P (m + 1) ω)
    rw [map_sum] at hω
    rw [hω]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α : SimonMultiIndex (m + 1) P, ‖w (euclideanCovectorCoordinate ω α •
            wedgeCovectors (m + 1) fun j => EuclideanSpace.proj (α j))‖
        ≤ ∑ _α : SimonMultiIndex (m + 1) P, ‖ω‖ := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [map_smul, smul_eq_mul, norm_mul]
          have h1 : ‖euclideanCovectorCoordinate ω α‖ ≤ ‖ω‖ := by
            have h := ω.le_opNorm (fun j => EuclideanSpace.single (α j) (1 : ℝ))
            simpa [euclideanCovectorCoordinate, PiLp.norm_single] using h
          have h2 : ‖w (wedgeCovectors (m + 1) fun j => EuclideanSpace.proj (α j))‖ ≤ 1 := by
            have hle : (euclideanNVectorCoordinate w α) ^ 2 ≤ 1 := hw ▸
              Finset.single_le_sum (fun β _ => sq_nonneg (euclideanNVectorCoordinate w β))
                (Finset.mem_univ α)
            rw [Real.norm_eq_abs]
            exact (sq_le_one_iff_abs_le_one _).1 hle
          calc ‖euclideanCovectorCoordinate ω α‖ *
                ‖w (wedgeCovectors (m + 1) fun j => EuclideanSpace.proj (α j))‖
              ≤ ‖ω‖ * 1 := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
            _ = ‖ω‖ := mul_one _
      _ = (Fintype.card (SimonMultiIndex (m + 1) P) : ℝ) * ‖ω‖ := by simp
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
  -- Finite upper density gives `λ(B̄_r(x)) ≤ C rⁿ` for small `r`.
  have hdens : ∀ (κ : Measure (Eucl P)) (x : Eucl P),
      dimensionalUpperDensity κ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x < ⊤ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ),
        κ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (m + 1)) := by
    intro κ x hx
    obtain ⟨c, hc1, hc2⟩ := exists_between hx
    have hω0 : Poincare.SimonGMT.Chapter01.realUnitBallVolume ((m + 1 : ℕ) : ℝ) ≠ 0 :=
      (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg _)).ne'
    have hωtop : Poincare.SimonGMT.Chapter01.realUnitBallVolume ((m + 1 : ℕ) : ℝ) ≠ ⊤ :=
      Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
    refine ⟨(c * Poincare.SimonGMT.Chapter01.realUnitBallVolume ((m + 1 : ℕ) : ℝ)).toReal,
      ENNReal.toReal_nonneg, ?_⟩
    filter_upwards [eventually_lt_of_limsup_lt hc1, self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    simp only [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient,
      Measure.toOuterMeasure_apply, univ_inter] at hr
    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hr0'.le] at hr
    rw [ENNReal.div_lt_iff
      (Or.inl (mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hr0' _)).ne'))
      (Or.inl (ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top))] at hr
    calc κ (closedBall x r)
        ≤ c * (Poincare.SimonGMT.Chapter01.realUnitBallVolume ((m + 1 : ℕ) : ℝ) *
            ENNReal.ofReal (r ^ (m + 1))) := hr.le
      _ = ENNReal.ofReal ((c * Poincare.SimonGMT.Chapter01.realUnitBallVolume
            ((m + 1 : ℕ) : ℝ)).toReal * r ^ (m + 1)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (ENNReal.mul_ne_top hc2.ne hωtop), mul_assoc]
  intro U hU T hbd M θ ξ hMU hMm hrect hpos hint hξm hξn hT
  set μ := (μHE[m + 1] : Measure (Eucl P)) with hμ
  -- Localization to `W_q ⊂⊂ U`; `ν` is the mass measure of `∂T` and `L_x` the tangent space.
  obtain ⟨W, hWcc, hWcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
  obtain ⟨ν, hν⟩ :=
    (Submission.rectifiability_mass_measure_representation P m U hU T.boundary hbd).1
  have htan := Submission.rectifiability_weighted_tangent_ae P m U M θ hU hMU hMm hrect hpos hint
  have hloc : ∀ q, ∀ᵐ x ∂μ.restrict (M ∩ W q), ∃ τ : Fin (m + 1) → Eucl P, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt (m + 1) M θ x (Submodule.span ℝ (range τ)) ∧
      (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
    intro q
    obtain ⟨hVo, hVc, hVcU⟩ := hWcc q
    set V := W q with hVdef
    have hVU : V ⊆ U := subset_closure.trans hVcU
    have hMV : NullMeasurableSet (M ∩ V) μ := hMm.inter hVo.measurableSet.nullMeasurableSet
    have hθV : IntegrableOn θ (M ∩ V) μ :=
      (hint _ hVc hVcU).mono_set (inter_subset_inter_right _ subset_closure)
    have hθm : AEMeasurable (fun y => ENNReal.ofReal (θ y)) (μ.restrict (M ∩ V)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hθV.aestronglyMeasurable.aemeasurable
    -- The finite measure `μq = θ Hⁿ ⌞ (M ∩ V)`.
    set μq : Measure (Eucl P) :=
      (μ.restrict (M ∩ V)).withDensity (fun y => ENNReal.ofReal (θ y)) with hμq
    have : IsFiniteMeasure μq := by
      refine ⟨?_⟩
      rw [hμq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hθV.2
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    have hac : μ.restrict (M ∩ V) ≪ μq := withDensity_absolutelyContinuous' hθm (by
      filter_upwards [ae_restrict_mem₀ hMV] with y hy
      exact (ENNReal.ofReal_pos.2 (hpos y hy.1)).ne')
    have hμqac : μq ≪ μ.restrict M :=
      (withDensity_absolutelyContinuous _ _).trans
        (Measure.absolutelyContinuous_of_le (Measure.restrict_mono inter_subset_left le_rfl))
    -- `∫_M θ F dHⁿ = ∫ F dμq` for `F` vanishing off `V`.
    have hμq_int : ∀ F : Eucl P → ℝ, (∀ y ∉ V, F y = 0) →
        ∫ y in M, θ y * F y ∂μ = ∫ y, F y ∂μq := by
      intro F hF
      rw [hμq, integral_withDensity_eq_integral_toReal_smul₀ hθm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      have h1 : ∫ y in M ∩ V, θ y * F y ∂μ = ∫ y in M, θ y * F y ∂μ := by
        rw [inter_comm, ← Measure.restrict_restrict hVo.measurableSet]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hF y hy, mul_zero]
      rw [← h1]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem₀ hMV] with y hy
      rw [ENNReal.toReal_ofReal (hpos y hy.1).le, smul_eq_mul]
    -- `ξ ∈ L¹(μq)` and its Lebesgue points (Besicovitch differentiation).  The normed-group
    -- instances of `NVector (ℝ^P) n = (Λⁿ ℝ^P)*` need one more pending synthesis level.
    set_option maxSynthPendingDepth 2 in
    have hξq : Integrable ξ μq := Integrable.of_bound (hξm.mono_ac hμqac) _ (by
      filter_upwards [hμqac.ae_le hξn] with y hy
      exact hξbd _ hy)
    have hleb : ∀ᵐ x ∂μq,
        Tendsto (fun r => ⨍ y in closedBall x r, ‖ξ y - ξ x‖ ∂μq) (𝓝[>] 0) (𝓝 0) := by
      filter_upwards [(Besicovitch.vitaliFamily μq).ae_tendsto_average_norm_sub
        hξq.locallyIntegrable] with x hx
      exact hx.comp (Besicovitch.tendsto_filterAt μq x)
    -- Finite upper densities of `μq` and of `ν` (Simon (2), (3); Ch. 1, 3.3).
    have hdμ : ∀ᵐ x ∂μ, dimensionalUpperDensity μq.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x < ⊤ := by
      have h := Submission.rectifiability_density_comparison P (m + 1) μq
        {x | dimensionalUpperDensity μq.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x = ⊤} univ ⊤
        isOpen_univ (subset_univ _) (fun x hx => le_of_eq hx.symm)
      have h0 : μ {x | dimensionalUpperDensity μq.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x = ⊤} =
          0 := by
        by_contra hne
        rw [ENNReal.top_mul hne] at h
        exact (measure_lt_top μq univ).ne (top_le_iff.mp h)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
      exact lt_top_iff_ne_top.2 hx
    have hdν : ∀ᵐ x ∂μ, x ∈ V →
        dimensionalUpperDensity ν.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x < ⊤ := by
      have h := Submission.rectifiability_density_comparison P (m + 1) ν
        {x | x ∈ V ∧ dimensionalUpperDensity ν.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x = ⊤} V ⊤
        hVo (fun x hx => hx.1) (fun x hx => le_of_eq hx.2.symm)
      have hνV : ν V < ⊤ := by
        rw [hν.2 V (hWcc q)]
        exact hbd V (hWcc q)
      have h0 : μ {x | x ∈ V ∧
          dimensionalUpperDensity ν.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x = ⊤} = 0 := by
        by_contra hne
        rw [ENNReal.top_mul hne] at h
        exact hνV.ne (top_le_iff.mp h)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx hxV
      exact lt_top_iff_ne_top.2 fun h => hx ⟨hxV, h⟩
    -- Simon (11)–(13) at a good point: `⟨a ∧ β, ξ(x)⟩ = 0` whenever `a` vanishes on `L`.
    have hpoint : ∀ x ∈ V, 0 < θ x → ∀ L : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x L →
        Tendsto (fun r => ⨍ y in closedBall x r, ‖ξ y - ξ x‖ ∂μq) (𝓝[>] 0) (𝓝 0) →
        ∀ Cμ : ℝ, 0 ≤ Cμ →
        (∀ᶠ r in 𝓝[>] (0 : ℝ), μq (closedBall x r) ≤ ENNReal.ofReal (Cμ * r ^ (m + 1))) →
        ∀ Cν : ℝ, 0 ≤ Cν →
        (∀ᶠ r in 𝓝[>] (0 : ℝ), ν (closedBall x r) ≤ ENNReal.ofReal (Cν * r ^ (m + 1))) →
        ∀ a : Eucl P →L[ℝ] ℝ, (∀ z ∈ L, a z = 0) → ∀ β : Covector (Eucl P) m,
          ξ x (ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight β)) = 0 := by
      intro x hxV hθx L hL hleb Cμ hCμ0 hCμ Cν hCν0 hCν a ha β
      -- a closed ball around `x` inside `V`
      obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo x hxV
      have hδV : closedBall x (ε / 2) ⊆ V := (closedBall_subset_ball (half_lt_self hε)).trans hεV
      -- the cutoff `ϕ` and the model `(n - 1)`-form `Ψ = (a ϕ) β`
      let ϕ : ContDiffBump (0 : Eucl P) := ⟨1, 2, one_pos, one_lt_two⟩
      let Ψ : DifferentialForm (Eucl P) m := fun z => (a z * ϕ z) • β
      have hΨ : Ψ = fun z => (a z * ϕ z) • β := rfl
      have hΨsm : IsSmoothForm Ψ := (a.contDiff.mul ϕ.contDiff).smul contDiff_const
      have hΨsupp : tsupport Ψ ⊆ closedBall 0 2 := by
        have hsub : Function.support Ψ ⊆ Function.support ϕ := fun z hz h0 => hz (by simp [hΨ, h0])
        exact (closure_mono hsub).trans ϕ.tsupport_eq.subset
      have hΨtest : IsTestForm Ψ :=
        ⟨hΨsm, (isCompact_closedBall 0 2).of_isClosed_subset (isClosed_tsupport _) hΨsupp⟩
      let Ω : DifferentialForm (Eucl P) (m + 1) := exteriorDerivative Ψ
      have hΩtest : IsTestForm Ω := exteriorDerivative_isTestForm hΨtest
      have hΩcont : Continuous Ω := hΩtest.1.continuous
      have hΩzero : ∀ z : Eucl P, 2 < ‖z‖ → Ω z = 0 := by
        intro z hz
        refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
        have h2 := hΨsupp (tsupport_exteriorDerivative_subset Ψ hmem)
        rw [mem_closedBall_zero_iff] at h2
        linarith
      obtain ⟨CΩ, hCΩ⟩ := hΩcont.bounded_above_of_compact_support hΩtest.2
      have hCΩ0 : 0 ≤ CΩ := (norm_nonneg _).trans (hCΩ 0)
      -- on `L`, `Ω = ϕ G`
      have hΩL : ∀ z ∈ L,
          Ω z = ϕ z • ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight β) := by
        intro z hz
        have hd : HasFDerivAt Ψ ((a z • fderiv ℝ ϕ z + ϕ z • a).smulRight β) z :=
          (a.hasFDerivAt.mul
            ((ϕ.contDiff (n := 1)).differentiable (by simp) z).hasFDerivAt).smul_const β
        show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ Ψ z) = _
        rw [hd.fderiv, ha z hz, zero_smul, zero_add,
          ← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        congr 1
        ext v
        simp [smul_smul]
      -- the blow-up forms `ψ r (y) = r Ψ((y - x) / r)`, with `dψ r (y) = Ω((y - x) / r)`
      let A : ℝ → Eucl P → Eucl P := fun r y => r⁻¹ • (y - x)
      have hA : A = fun r y => r⁻¹ • (y - x) := rfl
      let ψ : ℝ → DifferentialForm (Eucl P) m := fun r y => r • Ψ (A r y)
      have hψ : ψ = fun r y => r • Ψ (A r y) := rfl
      have hAnorm : ∀ r : ℝ, 0 < r → ∀ y, ‖A r y‖ = ‖y - x‖ / r := by
        intro r hr y
        rw [hA, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div]
      have hAcont : ∀ r : ℝ, Continuous (A r) := fun r => by
        simp only [hA]
        fun_prop
      have hψsupp : ∀ r : ℝ, 0 < r → tsupport (ψ r) ⊆ closedBall x (2 * r) := by
        intro r hr
        refine closure_minimal (fun y hy => ?_) isClosed_closedBall
        have hΨy : Ψ (A r y) ≠ 0 := fun h => hy (by simp only [hψ, h, smul_zero])
        have h2 := hΨsupp (subset_tsupport _ hΨy)
        rw [mem_closedBall_zero_iff, hAnorm r hr, div_le_iff₀ hr] at h2
        rw [mem_closedBall, dist_eq_norm]
        linarith
      have hψtest : ∀ r : ℝ, 0 < r → IsTestForm (ψ r) := by
        intro r hr
        refine ⟨?_, (isCompact_closedBall x (2 * r)).of_isClosed_subset (isClosed_tsupport _)
          (hψsupp r hr)⟩
        exact (hΨsm.comp ((contDiff_id.sub (contDiff_const (c := x))).const_smul r⁻¹)).const_smul r
      have hdψ : ∀ r : ℝ, 0 < r → ∀ y, exteriorDerivative (ψ r) y = Ω (A r y) := by
        intro r hr y
        have hAd : HasFDerivAt (A r) (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P)) y :=
          ((hasFDerivAt_id y).sub_const x).const_smul r⁻¹
        have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ (A r y)) (A r y) :=
          (hΨsm.differentiable (by simp) _).hasFDerivAt
        have hψd : HasFDerivAt (ψ r)
            (r • (fderiv ℝ Ψ (A r y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P))) y :=
          (hΨd.comp y hAd).const_smul r
        have heq : r • (fderiv ℝ Ψ (A r y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P)) =
            fderiv ℝ Ψ (A r y) := by
          ext v
          simp [smul_smul, mul_inv_cancel₀ hr.ne']
        show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (ψ r) y) =
          ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ Ψ (A r y))
        rw [hψd.fderiv, heq]
      have hΩA : ∀ r : ℝ, 0 < r → ∀ y, y ∉ closedBall x (2 * r) → Ω (A r y) = 0 := by
        intro r hr y hy
        apply hΩzero
        rw [hAnorm r hr, lt_div_iff₀ hr]
        rw [mem_closedBall, dist_eq_norm, not_le] at hy
        linarith
      -- the Euclidean coefficient norm of `ψ r` is `O(r)`
      have hψnorm : ∀ r : ℝ, 0 < r → ∀ y,
          covectorEuclideanNorm (ψ r y) ≤ 2 * r * ‖a‖ * covectorEuclideanNorm β := by
        intro r hr y
        have h1 : ψ r y = (r * (a (A r y) * ϕ (A r y))) • β := by
          simp only [hψ, hΨ, smul_smul]
        have hz : |a (A r y) * ϕ (A r y)| ≤ 2 * ‖a‖ := by
          by_cases h0 : ϕ (A r y) = 0
          · rw [h0, mul_zero, abs_zero]
            positivity
          · have hlt : ‖A r y‖ < 2 := by
              have hmem : A r y ∈ Function.support ϕ := h0
              rw [ϕ.support_eq, mem_ball_zero_iff] at hmem
              exact hmem
            rw [abs_mul, abs_of_nonneg ϕ.nonneg]
            have ha' : |a (A r y)| ≤ ‖a‖ * ‖A r y‖ := by
              rw [← Real.norm_eq_abs]
              exact a.le_opNorm _
            calc |a (A r y)| * ϕ (A r y) ≤ (‖a‖ * ‖A r y‖) * 1 :=
                  mul_le_mul ha' ϕ.le_one ϕ.nonneg (by positivity)
              _ ≤ 2 * ‖a‖ := by
                rw [mul_one, mul_comm]
                exact mul_le_mul_of_nonneg_right hlt.le (norm_nonneg a)
        rw [h1, hnormsmul, abs_mul, abs_of_pos hr]
        have hβ0 := covectorEuclideanNorm_nonneg β
        calc r * |a (A r y) * ϕ (A r y)| * covectorEuclideanNorm β
            ≤ r * (2 * ‖a‖) * covectorEuclideanNorm β :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hr.le) hβ0
          _ = 2 * r * ‖a‖ * covectorEuclideanNorm β := by ring
      -- `I r = ∫ ⟨Ω(A r y), ξ(y)⟩ dμq` and `I₀ r = ∫ ⟨Ω(A r y), ξ(x)⟩ dμq`
      let I : ℝ → ℝ := fun r => ∫ y, ξ y (Ω (A r y)) ∂μq
      let I₀ : ℝ → ℝ := fun r => ∫ y, ξ x (Ω (A r y)) ∂μq
      have hvanV : ∀ r : ℝ, 0 < r → 2 * r ≤ ε / 2 → ∀ y, y ∉ V → Ω (A r y) = 0 :=
        fun r hr hrε y hy => hΩA r hr y fun h => hy (hδV (closedBall_subset_closedBall hrε h))
      have hscale : ∀ c : ℝ, 0 < c → Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
        intro c hc
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hcont : Continuous fun r : ℝ => c * r := by fun_prop
          simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hc hr
      -- Simon (12): `|I r| = |∂T(ψ r)| ≤ M_{B(x, 4r)}(∂T) sup |ψ r| = O(r^{n + 1})`
      have hbdry : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          |I r| ≤ Cν * (4 * r) ^ (m + 1) * (2 * r * ‖a‖ * covectorEuclideanNorm β) := by
        filter_upwards [(hscale 4 four_pos).eventually hCν,
          Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 8 by positivity)] with r hrν hr
        obtain ⟨hr0, hrε⟩ := hr
        have h4ε : 4 * r ≤ ε / 2 := by linarith
        have hmem : ψ r ∈ testFormOnSubmodule U m :=
          show IsTestForm (ψ r) ∧ tsupport (ψ r) ⊆ U from ⟨hψtest r hr0, (hψsupp r hr0).trans
            ((closedBall_subset_closedBall (by linarith)).trans (hδV.trans hVU))⟩
        have hval : T.boundary ⟨ψ r, hmem⟩ = I r := by
          rw [GeometricCurrentOn.boundary_apply, hT, tauAction]
          have hω : ∀ y, ((exteriorDerivativeTestOn U m ⟨ψ r, hmem⟩ : TestFormOn U (m + 1)) :
              DifferentialForm (Eucl P) (m + 1)) y = Ω (A r y) := hdψ r hr0
          simp only [hω]
          exact hμq_int (fun y => ξ y (Ω (A r y)))
            fun y hy => by rw [hvanV r hr0 (by linarith) y hy, map_zero]
        have hcc : CompactlyContainedOpen (ball x (4 * r)) U :=
          ⟨isOpen_ball, (isCompact_closedBall x (4 * r)).of_isClosed_subset isClosed_closure
            closure_ball_subset_closedBall,
            closure_ball_subset_closedBall.trans
              ((closedBall_subset_closedBall h4ε).trans (hδV.trans hVU))⟩
        rw [← hval]
        refine Submission.cmb_abs_apply_le_of_massOn_le P m U (ball x (4 * r)) T.boundary
          ⟨ψ r, hmem⟩ (Cν * (4 * r) ^ (m + 1)) _ (by positivity) ?_ ?_ (hψnorm r hr0)
        · rw [← hν.2 _ hcc]
          exact (measure_mono ball_subset_closedBall).trans hrν
        · exact (hψsupp r hr0).trans (closedBall_subset_ball (by linarith))
      -- the test function `f = ⟨Ω, ξ(x)⟩ ∈ C_c(ℝ^P)`
      let f : CompactlySupportedContinuousMap (Eucl P) ℝ :=
        ⟨⟨fun z => ξ x (Ω z), (ξ x).continuous.comp hΩcont⟩, hΩtest.2.comp_left (map_zero (ξ x))⟩
      -- Simon (11), main part: `r⁻ⁿ I₀ r → θ(x) ∫_L f dHⁿ`
      have hmain : Tendsto (fun r => (r ^ (m + 1))⁻¹ * I₀ r) (𝓝[>] 0)
          (𝓝 (θ x * ∫ z in (L : Set (Eucl P)), f z ∂μ)) := by
        refine (hL.2 f).congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 4 by positivity)] with r hr
        obtain ⟨hr0, hrε⟩ := hr
        rw [hblow x r hr0 M (fun y => f y * θ (x + r • y))]
        congr 1
        show _ = ∫ y, ξ x (Ω (A r y)) ∂μq
        rw [← hμq_int (fun y => ξ x (Ω (A r y)))
          fun y hy => by rw [hvanV r hr0 (by linarith) y hy, map_zero]]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        show ξ x (Ω (r⁻¹ • (z - x))) * θ (x + r • (r⁻¹ • (z - x))) = θ z * ξ x (Ω (r⁻¹ • (z - x)))
        rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel, mul_comm]
      -- Simon (11), error part: `r⁻ⁿ |I r - I₀ r| ≤ CΩ Cμ 2ⁿ ⨍_{B(x, 2r)} |ξ - ξ(x)| dμq → 0`
      have hξΩ : ∀ r : ℝ, Integrable (fun y => ξ y (Ω (A r y))) μq := by
        intro r
        have : SecondCountableTopologyEither (Eucl P) (Covector (Eucl P) (m + 1)) :=
          secondCountableTopologyEither_of_left _ _
        refine Integrable.mono' (hξq.norm.mul_const CΩ) ?_ (Eventually.of_forall fun y => ?_)
        · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
            (hξq.aestronglyMeasurable.prodMk (hΩcont.comp (hAcont r)).aestronglyMeasurable)
        · exact ((ξ y).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hCΩ _) (norm_nonneg (ξ y)))
      have hxΩ : ∀ r : ℝ, Integrable (fun y => ξ x (Ω (A r y))) μq := fun r =>
        Integrable.of_bound ((ξ x).continuous.comp (hΩcont.comp (hAcont r))).aestronglyMeasurable
          (‖ξ x‖ * CΩ) (Eventually.of_forall fun y =>
            ((ξ x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hCΩ _) (norm_nonneg (ξ x))))
      have herr : Tendsto (fun r => (r ^ (m + 1))⁻¹ * (I r - I₀ r)) (𝓝[>] 0) (𝓝 0) := by
        have hlim := (hleb.comp (hscale 2 two_pos)).const_mul (CΩ * Cμ * 2 ^ (m + 1))
        rw [mul_zero] at hlim
        refine squeeze_zero_norm' ?_ hlim
        filter_upwards [(hscale 2 two_pos).eventually hCμ, self_mem_nhdsWithin] with r hrμ hr
        have hr0 : (0 : ℝ) < r := hr
        have hdiff : I r - I₀ r = ∫ y, (ξ y - ξ x) (Ω (A r y)) ∂μq := by
          show (∫ y, ξ y (Ω (A r y)) ∂μq) - ∫ y, ξ x (Ω (A r y)) ∂μq = _
          rw [← integral_sub (hξΩ r) (hxΩ r)]
          rfl
        have hle : ‖∫ y, (ξ y - ξ x) (Ω (A r y)) ∂μq‖ ≤
            ∫ y, CΩ * (closedBall x (2 * r)).indicator (fun y => ‖ξ y - ξ x‖) y ∂μq := by
          refine norm_integral_le_of_norm_le
            (((hξq.sub (integrable_const (ξ x))).norm.indicator
              measurableSet_closedBall).const_mul CΩ)
            (Eventually.of_forall fun y => ?_)
          by_cases hy : y ∈ closedBall x (2 * r)
          · rw [indicator_of_mem hy]
            calc ‖(ξ y - ξ x) (Ω (A r y))‖ ≤ ‖ξ y - ξ x‖ * ‖Ω (A r y)‖ := (ξ y - ξ x).le_opNorm _
              _ ≤ ‖ξ y - ξ x‖ * CΩ := mul_le_mul_of_nonneg_left (hCΩ _) (norm_nonneg (ξ y - ξ x))
              _ = CΩ * ‖ξ y - ξ x‖ := mul_comm _ _
          · simp [indicator_of_notMem hy, hΩA r hr0 y hy]
        have hint : ∫ y, CΩ * (closedBall x (2 * r)).indicator (fun y => ‖ξ y - ξ x‖) y ∂μq =
            CΩ * (μq.real (closedBall x (2 * r)) *
              ⨍ y in closedBall x (2 * r), ‖ξ y - ξ x‖ ∂μq) := by
          rw [integral_const_mul, integral_indicator measurableSet_closedBall,
            ← measure_smul_setAverage _ (measure_ne_top μq (closedBall x (2 * r))), smul_eq_mul]
        have hμB : μq.real (closedBall x (2 * r)) ≤ Cμ * (2 * r) ^ (m + 1) := by
          rw [measureReal_def]
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hrμ
        have havg0 : 0 ≤ ⨍ y in closedBall x (2 * r), ‖ξ y - ξ x‖ ∂μq := by
          rw [setAverage_eq]
          exact smul_nonneg (inv_nonneg.2 measureReal_nonneg)
            (integral_nonneg fun y => norm_nonneg (ξ y - ξ x))
        simp only [Function.comp_apply]
        rw [norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos hr0, hdiff]
        calc (r ^ (m + 1))⁻¹ * ‖∫ y, (ξ y - ξ x) (Ω (A r y)) ∂μq‖
            ≤ (r ^ (m + 1))⁻¹ * (CΩ * (μq.real (closedBall x (2 * r)) *
                ⨍ y in closedBall x (2 * r), ‖ξ y - ξ x‖ ∂μq)) := by
              rw [← hint]
              exact mul_le_mul_of_nonneg_left hle (by positivity)
          _ ≤ (r ^ (m + 1))⁻¹ * (CΩ * (Cμ * (2 * r) ^ (m + 1) *
                ⨍ y in closedBall x (2 * r), ‖ξ y - ξ x‖ ∂μq)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hμB havg0) hCΩ0) (by positivity)
          _ = CΩ * Cμ * 2 ^ (m + 1) * ⨍ y in closedBall x (2 * r), ‖ξ y - ξ x‖ ∂μq := by
              have hrn : (r ^ (m + 1))⁻¹ * r ^ (m + 1) = 1 :=
                inv_mul_cancel₀ (pow_ne_zero _ hr0.ne')
              rw [mul_pow]
              linear_combination
                (CΩ * Cμ * 2 ^ (m + 1) * ⨍ y in closedBall x (2 * r), ‖ξ y - ξ x‖ ∂μq) * hrn
      -- the two limits of `r⁻ⁿ I r`
      have hlim1 : Tendsto (fun r => (r ^ (m + 1))⁻¹ * I r) (𝓝[>] 0)
          (𝓝 (θ x * ∫ z in (L : Set (Eucl P)), f z ∂μ)) := by
        have h := hmain.add herr
        rw [add_zero] at h
        refine h.congr' (Eventually.of_forall fun r => ?_)
        show (r ^ (m + 1))⁻¹ * I₀ r + (r ^ (m + 1))⁻¹ * (I r - I₀ r) = (r ^ (m + 1))⁻¹ * I r
        ring
      have hlim2 : Tendsto (fun r => (r ^ (m + 1))⁻¹ * I r) (𝓝[>] 0) (𝓝 0) := by
        have hlin : Tendsto
            (fun r : ℝ => Cν * 4 ^ (m + 1) * (2 * ‖a‖ * covectorEuclideanNorm β) * r)
            (𝓝[>] 0) (𝓝 0) := by
          have h0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          simpa using h0.const_mul (Cν * 4 ^ (m + 1) * (2 * ‖a‖ * covectorEuclideanNorm β))
        refine squeeze_zero_norm' ?_ hlin
        filter_upwards [hbdry, self_mem_nhdsWithin] with r hr hr0
        have hr0' : (0 : ℝ) < r := hr0
        rw [norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0']
        calc (r ^ (m + 1))⁻¹ * |I r|
            ≤ (r ^ (m + 1))⁻¹ *
                (Cν * (4 * r) ^ (m + 1) * (2 * r * ‖a‖ * covectorEuclideanNorm β)) :=
              mul_le_mul_of_nonneg_left hr (by positivity)
          _ = Cν * 4 ^ (m + 1) * (2 * ‖a‖ * covectorEuclideanNorm β) * r := by
              have hrn : (r ^ (m + 1))⁻¹ * r ^ (m + 1) = 1 :=
                inv_mul_cancel₀ (pow_ne_zero _ hr0'.ne')
              rw [mul_pow]
              linear_combination (Cν * 4 ^ (m + 1) * (2 * ‖a‖ * covectorEuclideanNorm β) * r) * hrn
      -- `∫_L f = ⟨G, ξ(x)⟩ ∫_L ϕ` and `∫_L ϕ > 0`
      have hfL : ∫ z in (L : Set (Eucl P)), f z ∂μ =
          ξ x (ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight β)) *
            ∫ z in (L : Set (Eucl P)), ϕ z ∂μ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun L.closed_of_finiteDimensional.measurableSet fun z hz => ?_
        show ξ x (Ω z) = ξ x (ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight β)) * ϕ z
        rw [hΩL z hz, map_smul, smul_eq_mul, mul_comm]
      have hLϕ : 0 < ∫ z in (L : Set (Eucl P)), ϕ z ∂μ := by
        have :=
          Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hL.1
        rw [integral_pos_iff_support_of_nonneg (fun z => ϕ.nonneg)
          (ϕ.continuous.integrable_of_hasCompactSupport ϕ.hasCompactSupport), ϕ.support_eq]
        have h0 : (0 : Eucl P) ∈ (μ.restrict (L : Set (Eucl P))).support := by
          rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hL.1]
          exact L.zero_mem
        exact (Measure.mem_support_iff_forall _).1 h0 _ (ball_mem_nhds 0 ϕ.rOut_pos)
      have h0 := tendsto_nhds_unique hlim1 hlim2
      rw [hfL] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hθx.ne'
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hLϕ.ne'
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left htan,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hξn, hac.ae_le hleb,
      ae_restrict_of_ae hdμ, ae_restrict_of_ae hdν, ae_restrict_mem₀ hMV]
      with x hxL hxn hxleb hxdμ hxdν hxMV
    obtain ⟨L, hL⟩ := hxL
    obtain ⟨Cμ, hCμ0, hCμ⟩ := hdens μq x hxdμ
    obtain ⟨Cν, hCν0, hCν⟩ := hdens ν x (hxdν hxMV.2)
    obtain ⟨τ, hτon, hτspan, hsign⟩ := hLA (ξ x) L hL.1 hxn
      (hpoint x hxMV.2 (hpos x hxMV.1) L hL hxleb Cμ hCμ0 hCμ Cν hCν0 hCν)
    refine ⟨τ, hτon, ?_, hsign⟩
    rw [hτspan]
    exact hL
  have hcov : M ⊆ ⋃ q, M ∩ W q := by
    intro x hx
    obtain ⟨i, hi⟩ := hWcov {x} isCompact_singleton (singleton_subset_iff.2 (hMU hx))
    exact mem_iUnion.2 ⟨i, hx, hi rfl⟩
  exact ae_restrict_of_ae_restrict_of_subset hcov ((ae_restrict_iUnion_iff _ _).2 hloc)

/-- **Simon Ch. 6, Lemma 2.36 with Remarks 2.37(1)–(2) (pp. 144–145).**  Let `T ∈ 𝒟ₙ(U)`,
`n = m + 1`, satisfy `M_W(T) + M_W(∂T) < ∞` for every `W ⊂⊂ U`, let `μ = μ_T` be its mass
measure and `Q` a linear isometry of `ℝ^P`.  If `E` is Borel and `Lⁿ(p_α(Q(E))) = 0` for every
`α ∈ I(n, P)`, then `μ(E) = 0`.  (2.37(2) prints `Lⁿ(Q(E)) = 0`; the projections `p_α ∘ Q` are
meant.)  With `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `|ξ| = 1` `μ`-a.e. (2.7–2.8), printed (1)–(4) give
`μ(W) = M_W(T) ≤ C μ(W ∖ K)` for every compact `K ⊆ E` and open `W ⊂⊂ U`; letting `W ↓ K` gives
`μ(K) = 0`, and inner regularity (Ch. 1, 1.15) extends this to `E`. -/
theorem Submission.rectifiability_projection_null : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ μ : Measure (Eucl P), IsMassMeasure T μ → ∀ (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (E : Set (Eucl P)), MeasurableSet E → (∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' E) = 0) → μ E = 0 := by
  intro P m U hU T hmass μ hμ Q E hE hproj
  -- Step 1: `M_W(T) ≤ M_W(T) + M_W(∂T) < ∞`, so 2.7–2.8 give `ξ` with `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and
  -- `|ξ| = 1` `μ`-a.e.
  have hT : ∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ := fun W hW =>
    (ENNReal.add_lt_top.1 (hmass W hW)).1
  obtain ⟨ξ, -, hξ, hrep⟩ :=
    (Submission.rectifiability_mass_measure_representation P (m + 1) U hU T hT).2 μ hμ
  -- Step 2: `μ(W) = M_W(T) < ∞` for every open `W ⊂⊂ U`.
  have hfin : ∀ W, CompactlyContainedOpen W U → μ W < ∞ := fun W hW =>
    (hμ.2 W hW).trans_lt (hT W hW)
  -- Step 3 (inner regularity): it suffices that every compact `K ⊆ E` with `K ⊆ U` is `μ`-null.
  refine Submission.rpn_null_of_compact_null P U E μ hU hμ.1 hfin hE fun K hK hKE hKU => ?_
  -- Step 4: `p_α(Q(K)) ⊆ p_α(Q(E))` is `Lⁿ`-null for every `α`, so printed (1)–(3) give
  -- `μ(W) = M_W(T) ≤ C μ(W ∖ K)` (printed (4)), and shrinking `W ↓ K` gives `μ(K) = 0`.
  obtain ⟨C, hC⟩ := Submission.rpn_massOn_le_mul_measure_diff P m U T hmass μ ξ hrep hξ Q K hK
    fun α => measure_mono_null (image_mono hKE) (hproj α)
  exact Submission.rpn_compact_null_of_le_mul_diff P U K μ C hU hK hKU hfin fun W hW =>
    (hμ.2 W hW).trans_le (hC W hW)

/-- **Simon Ch. 6, Remark 2.37(1) (p. 144).**  If `M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, the
mass measure `μ_T` is absolutely continuous with respect to `Hⁿ`.  Each coordinate projection
`p_α` is 1-Lipschitz, so a Borel set `B` with `Hⁿ(B) = 0` has `Lⁿ(p_α(B)) = Hⁿ(p_α(B)) ≤ Hⁿ(B) = 0`
for every `α`, and Lemma 2.36 (`projection_null`, with `Q = id`) gives `μ_T(B) = 0`; an arbitrary
`Hⁿ`-null set lies in a Borel `Hⁿ`-null set.  (Book `n = m + 1`.) -/
theorem Submission.rectifiability_mass_measure_abs_continuous :
    ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
      (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) →
      ∀ μ : Measure (Eucl P), IsMassMeasure T μ → μ ≪ (μHE[m + 1] : Measure (Eucl P)) := by
  intro P m U hU T hT μ hμ
  -- It suffices to treat Borel `Hⁿ`-null sets `B` (measurable hulls).
  refine Measure.AbsolutelyContinuous.mk fun B hB hB0 => ?_
  -- Lemma 2.36 with `Q = id` and `E = B`.
  refine Submission.rectifiability_projection_null P m U hU T hT μ hμ
    (LinearIsometryEquiv.refl ℝ (Eucl P)) B hB fun α => nonpos_iff_eq_zero.mp ?_
  -- `Lⁿ = Hⁿ` on `ℝⁿ`, and `Hⁿ(p_α(B)) ≤ 1ⁿ · Hⁿ(B) = 0`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)]
  refine (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (K := 1)
    (m + 1) (LipschitzWith.lipschitzOnWith ?_)).trans_eq (by rw [hB0, mul_zero])
  -- `p_α` is 1-Lipschitz since `α` is injective.
  refine LipschitzWith.mk_one fun x y => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [LinearIsometryEquiv.coe_refl, id]
  exact Finset.sum_le_sum_of_injOn α α.injective.injOn (Finset.subset_univ _)
    (fun _ _ => le_rfl) fun _ _ _ => sq_nonneg _
/-- Compact inner approximation: a `μ`-null-measurable `A ⊆ ℝ^P` with `μ ⌞ A` σ-finite is,
up to a `μ`-null set, the union of countably many compact subsets of `A`. -/
theorem Submission.lpf_lli_inner_compact_approx : ∀ (P : ℕ) (μ : Measure (Eucl P)) (A : Set (Eucl P)), NullMeasurableSet A μ → SigmaFinite (μ.restrict A) → ∃ C : ℕ → Set (Eucl P), (∀ k, IsCompact (C k)) ∧ (∀ k, C k ⊆ A) ∧ μ (A \ ⋃ k, C k) = 0 := by
  intro P μ A hA hσ
  -- Step 1: a Borel set `A' ⊆ A` with `μ (A \ A') = 0`.
  obtain ⟨A', hA'A, hA'm, hA'ae⟩ := hA.exists_measurable_subset_ae_eq
  have hAA' : μ (A \ A') = 0 := (ae_eq_set.1 hA'ae).2
  -- Step 2: the Borel pieces `B m = A' ∩ S m`, `S = spanningSets (μ ⌞ A)`, have finite measure.
  set S := spanningSets (μ.restrict A) with hS
  set B : ℕ → Set (Eucl P) := fun m => A' ∩ S m
  have hBA : ∀ m, B m ⊆ A := fun m => inter_subset_left.trans hA'A
  have hBm : ∀ m, MeasurableSet (B m) := fun m => hA'm.inter (measurableSet_spanningSets _ m)
  have hBfin : ∀ m, μ (B m) ≠ ∞ := by
    intro m
    have h : μ.restrict A (B m) = μ (B m) := by
      rw [Measure.restrict_apply (hBm m), inter_eq_left.2 (hBA m)]
    rw [← h]
    exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ m)).ne
  -- Step 3: the finite measure `μ ⌞ B m` on `ℝ^P` is regular, so there are compact
  -- `K m j ⊆ B m` with `μ (B m \ K m j) < (j + 1)⁻¹`.
  have hK : ∀ m j : ℕ, ∃ K, K ⊆ B m ∧ IsCompact K ∧ μ (B m \ K) < ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro m j
    have : IsFiniteMeasure (μ.restrict (B m)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hBfin m).lt_top⟩
    have : (μ.restrict (B m)).Regular :=
      Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    obtain ⟨K, hKB, hKc, hKlt⟩ := (hBm m).exists_isCompact_sdiff_lt (μ := μ.restrict (B m))
      (measure_ne_top _ _) (ε := ((j : ℝ≥0∞) + 1)⁻¹) (by simp)
    refine ⟨K, hKB, hKc, ?_⟩
    rwa [Measure.restrict_apply ((hBm m).diff hKc.measurableSet),
      inter_eq_left.2 sdiff_subset] at hKlt
  choose K hKB hKc hKlt using hK
  -- Step 4: `μ (B m \ ⋃ j, K m j) < (j + 1)⁻¹` for every `j`, hence it vanishes.
  have hnull : ∀ m, μ (B m \ ⋃ j, K m j) = 0 := by
    intro m
    by_contra h
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
    have h1 : μ (B m \ ⋃ j, K m j) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      (measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ n))).trans_lt (hKlt m n)
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact lt_irrefl _ ((h1.trans_le h2).trans hn)
  -- Steps 5 and 6: re-index `K m j` along `Nat.unpair`; the rest of `A` lies in the null set
  -- `(A \ A') ∪ ⋃ m, (B m \ ⋃ j, K m j)`.
  refine ⟨fun k => K (Nat.unpair k).1 (Nat.unpair k).2, fun k => hKc _ _,
    fun k => (hKB _ _).trans (hBA _), measure_mono_null ?_
      (measure_union_null hAA' (measure_iUnion_null hnull))⟩
  rintro x ⟨hxA, hxC⟩
  by_cases hx : x ∈ A'
  · have hxS : x ∈ ⋃ m, S m := by rw [hS, iUnion_spanningSets]; exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxS
    refine Or.inr (mem_iUnion.2 ⟨m, ⟨hx, hm⟩, fun hxK => hxC ?_⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.1 hxK
    exact mem_iUnion.2 ⟨Nat.pair m j, by simpa only [Nat.unpair_pair] using hj⟩
  · exact Or.inl ⟨hxA, hx⟩
/-- Eilenberg finiteness: if `f : ℝ^N → ℝ^{m+1}` is Lipschitz and `E ⊆ ℝ^N` is Borel with
`H^{m+1}(E) < ∞`, then `E ∩ f⁻¹{y}` is finite for Lebesgue-a.e. `y ∈ ℝ^{m+1}`. -/
theorem Submission.rectifiability_bf_infinite_fibre_null : ∀ (N m : ℕ) (E : Set (Eucl N)) (f : Eucl N → Eucl (m + 1)) (K : ℝ≥0), MeasurableSet E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → LipschitzWith K f → (volume : Measure (Eucl (m + 1))) {y : Eucl (m + 1) | (E ∩ f ⁻¹' {y}).Infinite} = 0 := by
  intro N m E f K hE hEfin hf
  -- Step 1: `Lᵏ(f '' S) ≤ K ^ k * Hᵏ(S)` (`k = m + 1`), as `μHE[k] = volume` on `ℝᵏ`.
  have himage : ∀ S : Set (Eucl N), (volume : Measure (Eucl (m + 1))) (f '' S) ≤
      (K : ℝ≥0∞) ^ (m + 1) * μHE[m + 1] S := by
    intro S
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (m + 1) (hf.lipschitzOnWith (s := S))
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  -- Step 2: the dyadic cubes `g i ⁻¹' {z}`, `g i x = (⌊2 ^ i * x j⌋)_j`, are Borel, and two
  -- distinct points lie in distinct cubes for all large `i`.
  set g : ℕ → Eucl N → (Fin N → ℤ) := fun i x j => ⌊(2 : ℝ) ^ i * x j⌋ with hg
  have hQm : ∀ i z, MeasurableSet (g i ⁻¹' {z}) := by
    intro i z
    have hQ : g i ⁻¹' {z} =
        ⋂ j, (fun x : Eucl N => (2 : ℝ) ^ i * x j) ⁻¹' Ico (z j : ℝ) (z j + 1) := by
      ext x
      simp [hg, funext_iff, Int.floor_eq_iff]
    rw [hQ]
    exact MeasurableSet.iInter fun j =>
      (by fun_prop : Measurable fun x : Eucl N => (2 : ℝ) ^ i * x j) measurableSet_Ico
  have hsep : ∀ x x' : Eucl N, x ≠ x' → ∀ᶠ i in atTop, g i x ≠ g i x' := by
    intro x x' hne
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ x' j :=
      not_forall.1 fun h => hne (by ext j; exact h j)
    have hc : 0 < |x j - x' j| := abs_pos.2 (sub_ne_zero.2 hj)
    filter_upwards [((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const
      hc).eventually_ge_atTop 1] with i hi heq
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun heq j)
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i)] at h1
    linarith
  -- Step 3: `∑_z Hᵏ(E ∩ g i ⁻¹' {z}) = Hᵏ(E)`.
  have hsplit : ∀ i, ∑' z, (μHE[m + 1] : Measure (Eucl N)) (E ∩ g i ⁻¹' {z}) =
      μHE[m + 1] E := by
    intro i
    have hdisj : Pairwise (Function.onFun Disjoint fun z => E ∩ g i ⁻¹' {z}) := by
      intro z z' hzz'
      refine Set.disjoint_left.2 fun x hx hx' => hzz' ?_
      exact (show g i x = z from hx.2).symm.trans hx'.2
    have hU : (⋃ z, E ∩ g i ⁻¹' {z}) = E := by
      ext x
      simp
    rw [← measure_iUnion hdisj fun z => hE.inter (hQm i z), hU]
  -- Step 4: for Borel hulls `B i z ⊇ f '' (E ∩ g i ⁻¹' {z})`, the counts
  -- `n i = ∑_z 1_{B i z}` satisfy `∫ n i ≤ C := K ^ k * Hᵏ(E) < ∞`.
  set B : ℕ → (Fin N → ℤ) → Set (Eucl (m + 1)) :=
    fun i z => toMeasurable volume (f '' (E ∩ g i ⁻¹' {z})) with hB
  have hBm : ∀ i z, MeasurableSet (B i z) := fun i z => measurableSet_toMeasurable _ _
  set n : ℕ → Eucl (m + 1) → ℝ≥0∞ := fun i y => ∑' z, (B i z).indicator 1 y
  have hnm : ∀ i, Measurable (n i) := fun i =>
    Measurable.tsum fun z => measurable_one.indicator (hBm i z)
  set C : ℝ≥0∞ := (K : ℝ≥0∞) ^ (m + 1) * μHE[m + 1] E
  have hCfin : C < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hEfin
  have hint : ∀ i, ∫⁻ y, n i y ≤ C := by
    intro i
    calc ∫⁻ y, n i y = ∑' z, ∫⁻ y, (B i z).indicator 1 y :=
          lintegral_tsum fun z => (measurable_one.indicator (hBm i z)).aemeasurable
      _ = ∑' z, volume (f '' (E ∩ g i ⁻¹' {z})) := by
          congr 1; ext z; rw [lintegral_indicator_one (hBm i z), hB, measure_toMeasurable]
      _ ≤ ∑' z, (K : ℝ≥0∞) ^ (m + 1) * μHE[m + 1] (E ∩ g i ⁻¹' {z}) :=
          ENNReal.tsum_le_tsum fun z => himage _
      _ = C := by rw [ENNReal.tsum_mul_left, hsplit i]
  -- Step 5: over an infinite fibre, `M ≤ n i y` for all large `i`, since `M` points of the
  -- fibre eventually lie in `M` distinct cubes.
  have hlarge : ∀ y ∈ {y : Eucl (m + 1) | (E ∩ f ⁻¹' {y}).Infinite}, ∀ M : ℕ,
      ∀ᶠ i in atTop, (M : ℝ≥0∞) ≤ n i y := by
    intro y hy M
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hy M
    have hev : ∀ᶠ i in atTop, ∀ p ∈ T ×ˢ T, p.1 ≠ p.2 → g i p.1 ≠ g i p.2 := by
      refine (eventually_all_finset (T ×ˢ T)).2 fun p _ => ?_
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun i h => absurd hp h
      · exact (hsep p.1 p.2 hp).mono fun i hi _ => hi
    filter_upwards [hev] with i hi
    have hinj : InjOn (g i) T := by
      intro x hx x' hx' hxx'
      by_contra hne
      exact hi (x, x') (Finset.mem_product.2 ⟨hx, hx'⟩) hne hxx'
    calc (M : ℝ≥0∞) = ∑ z ∈ T.image (g i), (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_image_of_injOn hinj, hTcard, nsmul_one]
      _ = ∑ z ∈ T.image (g i), (B i z).indicator 1 y := by
          refine Finset.sum_congr rfl fun z hz => ?_
          obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.1 hz
          have hxE : x ∈ E ∩ f ⁻¹' {y} := hTsub (Finset.mem_coe.2 hxT)
          have hyB : y ∈ B i (g i x) := subset_toMeasurable _ _ ⟨x, ⟨hxE.1, rfl⟩, hxE.2⟩
          rw [indicator_of_mem hyB]
          rfl
      _ ≤ n i y := ENNReal.sum_le_tsum _
  -- Step 6: Fatou's lemma gives `∫ F ≤ C` for `F = liminf_i n i`, so `F < ∞` a.e.
  set F : Eucl (m + 1) → ℝ≥0∞ := fun y => liminf (fun i => n i y) atTop
  have hFm : Measurable F := Measurable.liminf hnm
  have hFint : ∫⁻ y, F y ≤ C :=
    (lintegral_liminf_le hnm).trans (liminf_le_of_frequently_le' (Frequently.of_forall hint))
  have hFae : ∀ᵐ y, F y < ∞ := ae_lt_top hFm (hFint.trans_lt hCfin).ne
  -- Step 7: the infinite fibres lie over the null set `{F = ∞}`.
  refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hFae)
  have hFy : F y = ∞ := by
    refine top_unique ?_
    rw [← ENNReal.iSup_natCast]
    exact iSup_le fun M => le_liminf_of_le (by isBoundedDefault) (hlarge y hy M)
  simp [hFy]
/-- **Conical density lemma for purely unrectifiable sets** (Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, 15.13–15.15; Hovila–Järvenpää–Järvenpää–Ledrappier,
arXiv:1104.3453, Lemma 2.2).  Let `k = m + 1`, `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩) ∈ ℝᵏ` and
`X_v(a,r,s) = {x : |x - a| < r, |L_v(x - a)| < s |x - a|}`.  If `E ⊆ ℝ^N` is purely
`k`-unrectifiable, the set of `a ∈ E` at which, for every `η > 0`, some aperture `s ∈ (0,1)`
gives `Hᵏ(E ∩ X_v(a,r,s)) ≤ η (r s)ᵏ` for all `r ∈ (0,δ)` is `Hᵏ`-null.  The three steps of the
proof (the conical density estimate, the uniform density bound forcing measure zero, and the
reduction to rational apertures) are local `have`s of this single declaration. -/
theorem Submission.rectifiability_bf_cone_density : ∀ (N m : ℕ) (E : Set (Eucl N)) (v : Fin (m + 1) → Eucl N) (δ : ℝ), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → 0 < δ → (μHE[m + 1] : Measure (Eucl N)) {a | a ∈ E ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))} = 0 := by
  -- Step 1(a) (Mattila 15.13): a set on which `L_v` is bi-Lipschitz lies in a Lipschitz image of `ℝᵏ`, hence is countably `k`-rectifiable, hence null in the purely unrectifiable `E`.
  have graph_null : ∀ (N m : ℕ) (E F : Set (Eucl N)) (v : Fin (m + 1) → Eucl N) (c : ℝ), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → F ⊆ E → 0 < c → (∀ a ∈ F, ∀ b ∈ F, c * ‖b - a‖ ≤ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖) → (μHE[m + 1] : Measure (Eucl N)) F = 0 := by
    classical
    intro N m E F v c hE hFE hc hbi
    let L : Eucl N → Eucl (m + 1) := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      ext i
      simp only [L, PiLp.sub_apply]
      rw [← inner_sub_right]
    have hinj : InjOn L F := by
      intro a ha b hb hab
      have h1 := hbi a ha b hb
      have h2 : L (b - a) = 0 := by rw [← hLsub, hab, sub_self]
      change c * ‖b - a‖ ≤ ‖L (b - a)‖ at h1
      rw [h2, norm_zero] at h1
      have h3 : ‖b - a‖ ≤ 0 := by nlinarith [norm_nonneg (b - a)]
      exact (sub_eq_zero.1 (norm_le_zero_iff.1 h3)).symm
    let g : Eucl (m + 1) → Eucl N := Function.invFunOn L F
    have hg : ∀ a ∈ F, g (L a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
    have hglip : LipschitzOnWith (Real.toNNReal c⁻¹) g (L '' F) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hg a ha, hg b hb, dist_eq_norm, dist_eq_norm, hLsub,
        Real.coe_toNNReal _ (inv_nonneg.2 hc.le)]
      have h1 : c * ‖a - b‖ ≤ ‖L (a - b)‖ := hbi b hb a ha
      rw [inv_mul_eq_div, le_div_iff₀ hc]
      linarith
    obtain ⟨G, hGlip, hGeq⟩ := hglip.extend_finite_dimension
    have hFrange : F ⊆ range G := fun a ha =>
      ⟨L a, (hGeq (mem_image_of_mem L ha)).symm.trans (hg a ha)⟩
    have hrect : CountablyRectifiable (m + 1) F :=
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hGlip).mono hFrange
    exact hE F hFE hrect
  -- Step 1(b), geometry: with `h = h(a)` and a partner `b` with `3h/4 < |b - a| ≤ h` in the `s/4`-cone, the cylinder `{|L_v(x - a)| < sh/4}` meets `F` inside `X_v(a,2h,s) ∪ X_v(b,2h,s)`.
  have two_cone_cover : ∀ (N m : ℕ) (v : Fin (m + 1) → Eucl N) (F : Set (Eucl N)) (a b : Eucl N) (s h : ℝ), 0 < s → (∀ c ∈ F, ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ < s / 4 * ‖c - a‖ → ‖c - a‖ ≤ h) → ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖ < s / 4 * ‖b - a‖ → 3 * h / 4 < ‖b - a‖ → ‖b - a‖ ≤ h → F ∩ {x | ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * h / 4} ⊆ {x | dist x a < 2 * h ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} ∪ {x | dist x b < 2 * h ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - b)) : Eucl (m + 1))‖ < s * ‖x - b‖} := by
    intro N m v F a b s h hs hmax hb1 hb2 hb3
    have hh : 0 < h := by linarith [norm_nonneg (b - a)]
    have hlin : ∀ c : Eucl N,
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - b)) : Eucl (m + 1)) =
          WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) +
            WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) := by
      intro c
      ext i
      simp only [PiLp.add_apply]
      rw [← inner_add_right]
      congr 1
      abel
    have hneg : ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) : Eucl (m + 1))‖ =
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖ := by
      rw [← norm_neg]
      congr 1
      ext i
      simp only [PiLp.neg_apply]
      rw [← inner_neg_right, neg_sub]
    rintro c ⟨hcF, hc⟩
    change ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ <
      s * h / 4 at hc
    have hca : ‖c - a‖ ≤ h := by
      by_contra hlt
      push Not at hlt
      have hin : ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ <
          s / 4 * ‖c - a‖ := by
        calc _ < s * h / 4 := hc
          _ < s / 4 * ‖c - a‖ := by nlinarith
      linarith [hmax c hcF hin]
    by_cases hfar : h / 4 ≤ ‖c - a‖
    · left
      refine ⟨by rw [dist_eq_norm]; linarith, ?_⟩
      calc _ < s * h / 4 := hc
        _ ≤ s * ‖c - a‖ := by nlinarith
    · right
      push Not at hfar
      have htri1 : ‖b - a‖ ≤ ‖c - b‖ + ‖c - a‖ := by
        calc ‖b - a‖ ≤ ‖b - c‖ + ‖c - a‖ := norm_sub_le_norm_sub_add_norm_sub b c a
          _ = ‖c - b‖ + ‖c - a‖ := by rw [norm_sub_rev b c]
      have htri2 : ‖c - b‖ ≤ ‖c - a‖ + ‖b - a‖ := by
        calc ‖c - b‖ ≤ ‖c - a‖ + ‖a - b‖ := norm_sub_le_norm_sub_add_norm_sub c a b
          _ = ‖c - a‖ + ‖b - a‖ := by rw [norm_sub_rev a b]
      have hcb1 : h / 2 < ‖c - b‖ := by linarith
      have hcb2 : ‖c - b‖ < 2 * h := by linarith
      refine ⟨by rw [dist_eq_norm]; exact hcb2, ?_⟩
      rw [hlin c]
      calc _ ≤ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ +
            ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) : Eucl (m + 1))‖ :=
            norm_add_le _ _
        _ < s * h / 4 + s / 4 * ‖b - a‖ := by rw [hneg]; linarith
        _ ≤ s * h / 2 := by nlinarith
        _ < s * ‖c - b‖ := by nlinarith
  -- Step 1(c): Vitali covering (factor `τ = 2`, so `5r` enlargements) of the projected balls in `ℝᵏ`, countability, and the volume packing bound `Σ ρᵏ ≤ (M + R)ᵏ`.
  have vitali_packing : ∀ (N m : ℕ) (A : Set (Eucl N)) (y : Eucl N → Eucl (m + 1)) (ρ : Eucl N → ℝ) (y₀ : Eucl (m + 1)) (R M : ℝ), (∀ a ∈ A, 0 < ρ a ∧ ρ a ≤ R) → (∀ a ∈ A, dist (y a) y₀ ≤ M) → ∃ I : Set (Eucl N), I ⊆ A ∧ I.Countable ∧ I.PairwiseDisjoint (fun b => ball (y b) (ρ b)) ∧ (∀ a ∈ A, ∃ b ∈ I, ball (y a) (ρ a) ⊆ ball (y b) (5 * ρ b)) ∧ ∑' b : I, ENNReal.ofReal (ρ b ^ (m + 1)) ≤ ENNReal.ofReal ((M + R) ^ (m + 1)) := by
    intro N m A y ρ y₀ R M hρ hy
    obtain ⟨u, huA, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a => ball (y a) (ρ a)) A ρ 2 one_lt_two (fun a ha => (hρ a ha).1.le) R
      (fun a ha => (hρ a ha).2) (fun a ha => nonempty_ball.2 (hρ a ha).1)
    have hucount : u.Countable := hudisj.countable_of_isOpen (fun a _ => isOpen_ball)
      (fun a ha => nonempty_ball.2 (hρ a (huA ha)).1)
    refine ⟨u, huA, hucount, hudisj, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hbu, ⟨z, hza, hzb⟩, hab⟩ := hucov a ha
      refine ⟨b, hbu, fun w hw => ?_⟩
      rw [mem_ball] at hw hza hzb ⊢
      calc dist w (y b) ≤ dist w (y a) + dist (y a) z + dist z (y b) := dist_triangle4 _ _ _ _
        _ < ρ a + ρ a + ρ b := by rw [dist_comm (y a) z]; linarith
        _ ≤ 5 * ρ b := by linarith
    · rcases u.eq_empty_or_nonempty with hu | ⟨b₀, hb₀⟩
      · subst hu
        simp
      have hR : 0 < R := (hρ b₀ (huA hb₀)).1.trans_le (hρ b₀ (huA hb₀)).2
      have hM : 0 ≤ M := dist_nonneg.trans (hy b₀ (huA hb₀))
      set μ : Measure (Eucl (m + 1)) := volume with hμ
      have hω0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
      have hωtop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
      have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
      have hsub : (⋃ b ∈ u, ball (y b) (ρ b)) ⊆ ball y₀ (M + R) := by
        intro w hw
        obtain ⟨b, hbu, hwb⟩ := mem_iUnion₂.1 hw
        rw [mem_ball] at hwb ⊢
        calc dist w y₀ ≤ dist w (y b) + dist (y b) y₀ := dist_triangle _ _ _
          _ < ρ b + M := by linarith [hy b (huA hbu)]
          _ ≤ M + R := by linarith [(hρ b (huA hbu)).2]
      have key : (∑' b : u, ENNReal.ofReal (ρ b ^ (m + 1))) * μ (ball 0 1) ≤
          ENNReal.ofReal ((M + R) ^ (m + 1)) * μ (ball 0 1) := by
        rw [← ENNReal.tsum_mul_right]
        calc ∑' b : u, ENNReal.ofReal (ρ b ^ (m + 1)) * μ (ball 0 1)
            = ∑' b : u, μ (ball (y b) (ρ b)) := by
              congr 1
              funext b
              rw [Measure.addHaar_ball_of_pos μ _ (hρ b (huA b.2)).1, hfin]
          _ = μ (⋃ b ∈ u, ball (y b) (ρ b)) :=
              (measure_biUnion hucount hudisj (fun b _ => measurableSet_ball)).symm
          _ ≤ μ (ball y₀ (M + R)) := measure_mono hsub
          _ = ENNReal.ofReal ((M + R) ^ (m + 1)) * μ (ball 0 1) := by
              rw [Measure.addHaar_ball μ _ (by linarith), hfin]
      exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key
  -- Step 1 (Mattila 15.14): the conical density estimate `Hᵏ(B ∩ B(x₀,δ′/6)) ≤ C₁ λ δ′ᵏ`, `C₁ = 2(20/3)ᵏ(‖L_v‖ + 1)ᵏ`.
  have conical_density_estimate : ∀ (N m : ℕ) (E : Set (Eucl N)) (v : Fin (m + 1) → Eucl N), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (B : Set (Eucl N)) (s δ' l : ℝ), B ⊆ E → 0 < s → s < 1 → 0 < δ' → 0 ≤ l → (∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ δ' → (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (l * (r * s) ^ (m + 1))) → ∀ x₀ : Eucl N, (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₀ (δ' / 6)) ≤ ENNReal.ofReal (C₁ * l * δ' ^ (m + 1)) := by
    intro N m E v hE
    -- the linear map `L_v` and an operator-norm bound `Λ`
    let Lₗ : Eucl N →ₗ[ℝ] Eucl (m + 1) :=
      { toFun := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
        map_add' := fun x y => by
          ext i
          simp [inner_add_right]
        map_smul' := fun c x => by
          ext i
          simp [inner_smul_right] }
    let Lc : Eucl N →L[ℝ] Eucl (m + 1) := LinearMap.toContinuousLinearMap Lₗ
    let L : Eucl N → Eucl (m + 1) := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
    have hLc : ∀ x, Lc x = L x := fun x => rfl
    set Λ : ℝ := ‖Lc‖ with hΛ
    have hΛ0 : 0 ≤ Λ := norm_nonneg _
    have hLsub : ∀ x y, L x - L y = L (x - y) := fun x y => by
      rw [← hLc, ← hLc, ← hLc]; exact (map_sub Lc x y).symm
    have hLbound : ∀ x, ‖L x‖ ≤ Λ * ‖x‖ := fun x => by
      rw [← hLc]; exact Lc.le_opNorm x
    have hL0 : L 0 = 0 := by rw [← hLc]; exact map_zero Lc
    refine ⟨2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1), by positivity, ?_⟩
    intro B s δ' l hBE hs0 hs1 hδ' hl hcone x₀
    set F : Set (Eucl N) := B ∩ ball x₀ (δ' / 6) with hFdef
    have hFB : F ⊆ B := inter_subset_left
    have hFE : F ⊆ E := hFB.trans hBE
    have hFdist : ∀ a ∈ F, ∀ b ∈ F, ‖b - a‖ < δ' / 3 := by
      intro a ha b hb
      have h1 : dist a x₀ < δ' / 6 := ha.2
      have h2 : dist b x₀ < δ' / 6 := hb.2
      rw [← dist_eq_norm]
      calc dist b a ≤ dist b x₀ + dist a x₀ := dist_triangle_right b a x₀
        _ < δ' / 6 + δ' / 6 := add_lt_add h2 h1
        _ = δ' / 3 := by ring
    -- the partition `F = F₀ ∪ F₁`
    set F₀ : Set (Eucl N) := {a | a ∈ F ∧ ∀ b ∈ F, s / 4 * ‖b - a‖ ≤ ‖L (b - a)‖} with hF₀def
    set F₁ : Set (Eucl N) := {a | a ∈ F ∧ ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖} with hF₁def
    have hFsplit : F ⊆ F₀ ∪ F₁ := by
      intro a ha
      by_cases h : ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖
      · exact Or.inr ⟨ha, h⟩
      · push Not at h
        exact Or.inl ⟨ha, h⟩
    -- (a) graph part
    have hF₀null : (μHE[m + 1] : Measure (Eucl N)) F₀ = 0 :=
      graph_null N m E F₀ v (s / 4) hE (fun a ha => hFE ha.1)
        (by positivity) (fun a ha b hb => ha.2 b hb.1)
    -- (b) the function `h`
    let hfun : Eucl N → ℝ := fun a =>
      sSup ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖})
    have hbdd : ∀ a ∈ F,
        BddAbove ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖}) := by
      intro a ha
      refine ⟨δ' / 3, ?_⟩
      rintro t ⟨b, hb, rfl⟩
      exact (hFdist a ha b hb.1).le
    have hS_le : ∀ a ∈ F, ∀ c ∈ F, ‖L (c - a)‖ < s / 4 * ‖c - a‖ → ‖c - a‖ ≤ hfun a := by
      intro a ha c hc hc'
      exact le_csSup (hbdd a ha) ⟨c, ⟨hc, hc'⟩, rfl⟩
    have hpos : ∀ a ∈ F₁, 0 < hfun a := by
      rintro a ⟨ha, b, hb, hlt⟩
      have hba : b ≠ a := by
        rintro rfl
        simp only [sub_self, hL0, norm_zero, mul_zero, lt_self_iff_false] at hlt
      have : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hba)
      exact this.trans_le (hS_le a ha b hb hlt)
    have hle : ∀ a ∈ F₁, hfun a ≤ δ' / 3 := by
      rintro a ⟨ha, b, hb, hlt⟩
      refine csSup_le ⟨‖b - a‖, ⟨b, ⟨hb, hlt⟩, rfl⟩⟩ ?_
      rintro t ⟨c, hc, rfl⟩
      exact (hFdist a ha c hc.1).le
    have hpartner : ∀ a ∈ F₁, ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖ ∧
        3 * hfun a / 4 < ‖b - a‖ ∧ ‖b - a‖ ≤ hfun a := by
      intro a haF₁
      have hp := hpos a haF₁
      obtain ⟨ha, b, hb, hlt⟩ := haF₁
      have hne : ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖}).Nonempty :=
        ⟨‖b - a‖, ⟨b, ⟨hb, hlt⟩, rfl⟩⟩
      obtain ⟨t, ⟨c, hc, rfl⟩, htc⟩ := exists_lt_of_lt_csSup hne
        (show 3 * hfun a / 4 < hfun a by linarith)
      exact ⟨c, hc.1, hc.2, htc, hS_le a ha c hc.1 hc.2⟩
    -- two cones cover each cylinder
    have hcyl : ∀ a ∈ F₁, (μHE[m + 1] : Measure (Eucl N)) (F ∩ {x | ‖L (x - a)‖ < s * hfun a / 4}) ≤
        2 * ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) := by
      intro a haF₁
      obtain ⟨b, hbF, hb1, hb2, hb3⟩ := hpartner a haF₁
      have haF : a ∈ F := haF₁.1
      have hincl := two_cone_cover N m v F a b s (hfun a) hs0
        (hS_le a haF) hb1 hb2 hb3
      have h2h0 : 0 < 2 * hfun a := by linarith [hpos a haF₁]
      have h2hle : 2 * hfun a ≤ δ' := by linarith [hle a haF₁]
      calc (μHE[m + 1] : Measure (Eucl N)) (F ∩ {x | ‖L (x - a)‖ < s * hfun a / 4})
          ≤ (μHE[m + 1] : Measure (Eucl N))
              ((E ∩ {x | dist x a < 2 * hfun a ∧ ‖L (x - a)‖ < s * ‖x - a‖}) ∪
                (E ∩ {x | dist x b < 2 * hfun a ∧ ‖L (x - b)‖ < s * ‖x - b‖})) := by
            apply measure_mono
            intro x hx
            rcases hincl hx with h | h
            · exact Or.inl ⟨hFE hx.1, h⟩
            · exact Or.inr ⟨hFE hx.1, h⟩
        _ ≤ (μHE[m + 1] : Measure (Eucl N))
              (E ∩ {x | dist x a < 2 * hfun a ∧ ‖L (x - a)‖ < s * ‖x - a‖}) +
            (μHE[m + 1] : Measure (Eucl N))
              (E ∩ {x | dist x b < 2 * hfun a ∧ ‖L (x - b)‖ < s * ‖x - b‖}) :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) +
            ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) :=
            add_le_add (hcone a (hFB haF) _ h2h0 h2hle) (hcone b (hFB hbF) _ h2h0 h2hle)
        _ = 2 * ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) := (two_mul _).symm
    -- (c) Vitali covering of the projected balls
    obtain ⟨I, hIF₁, hIcount, -, hIcover, hIsum⟩ :=
      vitali_packing N m F₁ L (fun a => s * hfun a / 20) (L x₀)
        (s * δ' / 60) (Λ * δ' / 6)
        (fun a ha => by
          have h1 := hpos a ha
          have h2 := hle a ha
          refine ⟨by positivity, ?_⟩
          calc s * hfun a / 20 ≤ s * (δ' / 3) / 20 := by gcongr
            _ = s * δ' / 60 := by ring)
        (fun a ha => by
          have hax : ‖a - x₀‖ < δ' / 6 := by
            have := ha.1.2
            rwa [mem_ball, dist_eq_norm] at this
          rw [dist_eq_norm, hLsub]
          calc ‖L (a - x₀)‖ ≤ Λ * ‖a - x₀‖ := hLbound _
            _ ≤ Λ * (δ' / 6) := mul_le_mul_of_nonneg_left hax.le hΛ0
            _ = Λ * δ' / 6 := by ring)
    -- (d) covering of `F`
    have hcover : F ⊆ F₀ ∪ ⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4}) := by
      intro a ha
      rcases hFsplit ha with h0 | h1
      · exact Or.inl h0
      · right
        obtain ⟨b, hbI, hsub⟩ := hIcover a h1
        have hmem : L a ∈ ball (L a) (s * hfun a / 20) := by
          have := hpos a h1
          exact mem_ball_self (by positivity)
        have hab := hsub hmem
        rw [mem_ball, dist_eq_norm, hLsub] at hab
        refine mem_iUnion₂.2 ⟨b, hbI, ha, ?_⟩
        show ‖L (a - b)‖ < s * hfun b / 4
        linarith
    -- (e) the estimate
    have hsum' : ∑' b : I, ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) ≤
        ENNReal.ofReal ((Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) := hIsum
    calc (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₀ (δ' / 6))
        = (μHE[m + 1] : Measure (Eucl N)) F := rfl
      _ ≤ (μHE[m + 1] : Measure (Eucl N))
            (F₀ ∪ ⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4})) := measure_mono hcover
      _ ≤ (μHE[m + 1] : Measure (Eucl N)) F₀ + (μHE[m + 1] : Measure (Eucl N))
            (⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4})) := measure_union_le _ _
      _ ≤ 0 + ∑' b : I, (μHE[m + 1] : Measure (Eucl N))
            (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4}) := by
          rw [hF₀null]
          gcongr
          exact measure_biUnion_le _ hIcount _
      _ ≤ ∑' b : I, 2 * ENNReal.ofReal (l * (2 * hfun b * s) ^ (m + 1)) := by
          rw [zero_add]
          exact ENNReal.tsum_le_tsum fun b => hcyl b (hIF₁ b.2)
      _ = ∑' b : I, ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) := by
          congr 1
          funext b
          have hreal : 2 * l * 40 ^ (m + 1) * (s * hfun b / 20) ^ (m + 1) =
              2 * (l * (2 * hfun b * s) ^ (m + 1)) := by
            rw [show 2 * hfun b * s = 40 * (s * hfun b / 20) by ring, mul_pow]
            ring
          have h40 : (0 : ℝ) ≤ 2 * l * 40 ^ (m + 1) := mul_nonneg (mul_nonneg (by norm_num) hl) (by positivity)
          rw [← ENNReal.ofReal_mul h40, hreal, ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ∑' b : I, ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ENNReal.ofReal ((Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) := by gcongr
      _ = ENNReal.ofReal (2 * l * 40 ^ (m + 1) * (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) :=
          (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hl) (by positivity))).symm
      _ ≤ ENNReal.ofReal (2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1) * l * δ' ^ (m + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : Λ * δ' / 6 + s * δ' / 60 ≤ (Λ + 1) * δ' / 6 := by nlinarith
          have h2 : (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1) ≤ ((Λ + 1) * δ' / 6) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) h1 _
          calc 2 * l * 40 ^ (m + 1) * (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)
              ≤ 2 * l * 40 ^ (m + 1) * ((Λ + 1) * δ' / 6) ^ (m + 1) := by gcongr
            _ = 2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1) * l * δ' ^ (m + 1) := by
                rw [show (Λ + 1) * δ' / 6 = (Λ + 1) * δ' * (1 / 6) by ring, mul_pow, mul_pow,
                  show (20 / 3 : ℝ) = 40 * (1 / 6) by norm_num, mul_pow]
                ring
  -- Step 2 (Mattila 6.2(1), uniform form): `Hᵏ(B ∩ B̄(x,ρ)) ≤ (c_k/2) ρᵏ` for `x ∈ B`, `ρ ≤ ρ₀` forces `Hᵏ(B) = 0`, where `μHE[k] = c_k • μH[k]`.
  have uniform_density_null : ∀ (N m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (B : Set (Eucl N)) (ρ₀ : ℝ), 0 < ρ₀ → (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → (μHE[m + 1] : Measure (Eucl N)) (B ∩ closedBall x ρ) ≤ ENNReal.ofReal (c * ρ ^ (m + 1))) → (μHE[m + 1] : Measure (Eucl N)) B = 0 := by
    intro N m
    set κ : ℝ≥0 := Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      (μH[((m + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (m + 1)))) with hκ
    have hκ0 : κ ≠ 0 := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (m + 1)
    have hκ0' : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0
    have hdef : ∀ S : Set (Eucl N), (μHE[m + 1] : Measure (Eucl N)) S =
        (κ : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) S := by
      intro S
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have hκpos : (0 : ℝ) < κ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ0)
    refine ⟨(κ : ℝ) / 2, div_pos hκpos two_pos, ?_⟩
    intro B ρ₀ hρ₀ hB
    set c : ℝ := (κ : ℝ) / 2 with hc
    have hc0 : 0 < c := div_pos hκpos two_pos
    have : NullSingletonClass (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) :=
      Measure.nullSingletonClass_hausdorff (Eucl N) (by positivity)
    -- local claim on balls of radius `ρ₀ / 2`
    have hloc : ∀ x₁ ∈ B, (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₁ (ρ₀ / 2)) = 0 := by
      intro x₁ hx₁
      set B' : Set (Eucl N) := B ∩ ball x₁ (ρ₀ / 2) with hB'
      have hfin : (μHE[m + 1] : Measure (Eucl N)) B' < ⊤ := by
        calc (μHE[m + 1] : Measure (Eucl N)) B'
            ≤ (μHE[m + 1] : Measure (Eucl N)) (B ∩ closedBall x₁ (ρ₀ / 2)) :=
              measure_mono (inter_subset_inter_right _ ball_subset_closedBall)
          _ ≤ ENNReal.ofReal (c * (ρ₀ / 2) ^ (m + 1)) :=
              hB x₁ hx₁ _ (by positivity) (by linarith)
          _ < ⊤ := ENNReal.ofReal_lt_top
      have hcov : ∀ t : ℕ → Set (Eucl N), B' ⊆ ⋃ n, t n →
          (∀ n, ediam (t n) ≤ ENNReal.ofReal ρ₀) →
          (μHE[m + 1] : Measure (Eucl N)) B' ≤
            ENNReal.ofReal c * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
        intro t ht hdiam
        have hterm : ∀ n, (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n) ≤
            ENNReal.ofReal c * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
          intro n
          rcases (B' ∩ t n).eq_empty_or_nonempty with he | ⟨x, hxB', hxt⟩
          · rw [he, measure_empty]
            exact zero_le
          · have hne : (t n).Nonempty := ⟨x, hxt⟩
            rw [iSup_pos hne]
            have hdfin : ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
            set d : ℝ := (ediam (t n)).toReal with hd
            have hdeq : ENNReal.ofReal d = ediam (t n) := ENNReal.ofReal_toReal hdfin
            have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
            have hdle : d ≤ ρ₀ := by
              rw [← ENNReal.ofReal_le_ofReal_iff hρ₀.le, hdeq]
              exact hdiam n
            have hpow : ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) = ENNReal.ofReal (d ^ (m + 1)) := by
              rw [← hdeq, ENNReal.rpow_natCast, ENNReal.ofReal_pow hd0]
            rw [hpow, ← ENNReal.ofReal_mul hc0.le]
            rcases hd0.eq_or_lt with hd0' | hdpos
            · have hsub : B' ∩ t n ⊆ {x} := by
                rintro z ⟨-, hz⟩
                have h1 : edist z x ≤ ediam (t n) := edist_le_ediam_of_mem hz hxt
                rw [← hdeq, ← hd0', ENNReal.ofReal_zero, nonpos_iff_eq_zero, edist_eq_zero] at h1
                exact h1
              calc (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n)
                  ≤ (μHE[m + 1] : Measure (Eucl N)) {x} := measure_mono hsub
                _ = 0 := by rw [hdef, measure_singleton, mul_zero]
                _ ≤ _ := zero_le
            · have hsub : B' ∩ t n ⊆ B ∩ closedBall x d := by
                rintro z ⟨hzB', hz⟩
                refine ⟨hzB'.1, ?_⟩
                rw [mem_closedBall, ← ENNReal.ofReal_le_ofReal_iff hd0, ← edist_dist, hdeq]
                exact edist_le_ediam_of_mem hz hxt
              exact (measure_mono hsub).trans (hB x hxB'.1 d hdpos hdle)
        calc (μHE[m + 1] : Measure (Eucl N)) B'
            ≤ (μHE[m + 1] : Measure (Eucl N)) (⋃ n, B' ∩ t n) := by
              refine measure_mono fun x hx => ?_
              obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hx)
              exact mem_iUnion.2 ⟨n, hx, hn⟩
          _ ≤ ∑' n, (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n) := measure_iUnion_le _
          _ ≤ ∑' n, ENNReal.ofReal c * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) :=
              ENNReal.tsum_le_tsum hterm
          _ = ENNReal.ofReal c * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) :=
              ENNReal.tsum_mul_left
      have hc' : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc0).ne'
      have hle : (μHE[m + 1] : Measure (Eucl N)) B' ≤
          ENNReal.ofReal c * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' := by
        have hinf : (μHE[m + 1] : Measure (Eucl N)) B' ≤ ENNReal.ofReal c *
            ⨅ (t : ℕ → Set (Eucl N)) (_ : B' ⊆ ⋃ n, t n)
              (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal ρ₀),
              ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
          rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top)]
          refine le_iInf fun t => le_iInf fun ht => le_iInf fun hdiam => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hcov t ht hdiam
        refine hinf.trans ?_
        gcongr
        rw [Measure.hausdorffMeasure_apply]
        exact le_iSup₂_of_le (ENNReal.ofReal ρ₀) (ENNReal.ofReal_pos.2 hρ₀) le_rfl
      rw [hdef] at hle hfin ⊢
      have hμHfin : (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.mul_top hκ0'] at hfin
        exact lt_irrefl _ hfin
      by_contra hne
      have hμH0 : (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hκle : (κ : ℝ≥0∞) ≤ ENNReal.ofReal c := (ENNReal.mul_le_mul_iff_left hμH0 hμHfin).1 hle
      have hlt : ENNReal.ofReal c < κ := by
        rw [hc, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat]
        exact ENNReal.half_lt_self hκ0' ENNReal.coe_ne_top
      exact absurd hκle (not_le.2 hlt)
    -- globalize with a countable subcover
    obtain ⟨T, hTB, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable B
      (fun x => ball x (ρ₀ / 2)) (fun _ _ => isOpen_ball)
    have hcover : B ⊆ ⋃ x ∈ T, (B ∩ ball x (ρ₀ / 2)) := by
      intro z hz
      have hz' : z ∈ ⋃ x ∈ B, ball x (ρ₀ / 2) := mem_iUnion₂.2 ⟨z, hz, mem_ball_self (by positivity)⟩
      rw [← hTU] at hz'
      obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.1 hz'
      exact mem_iUnion₂.2 ⟨x, hxT, hz, hzx⟩
    exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 fun x hx => hloc x (hTB hx))
  -- Step 3: rational apertures, then Steps 1 and 2 on each `B_q`.
  intro N m E v δ hE hδ
  obtain ⟨c, hc, hudn⟩ := uniform_density_null N m
  obtain ⟨C₁, hC₁, hcde⟩ := conical_density_estimate N m E v hE
  set η₀ : ℝ := c / (C₁ * 24 ^ (m + 1)) with hη₀
  have hη₀pos : 0 < η₀ := by positivity
  -- the sets `B_{s'}` for rational apertures `s'`
  set Bq : ℚ → Set (Eucl N) := fun q => {a | a ∈ E ∧ ∀ r ∈ Ioo (0 : ℝ) δ,
    (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
      ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
        (q : ℝ) * ‖x - a‖}) ≤ ENNReal.ofReal (2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1))} with hBq
  -- Step 3(a)
  have hsub : {a | a ∈ E ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ,
      (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
          s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))} ⊆
      ⋃ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < 1), Bq q := by
    rintro a ⟨haE, ha⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := ha η₀ hη₀pos
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s / 2 < s by linarith)
    have hq0 : (0 : ℝ) < q := by linarith
    refine mem_iUnion₂.2 ⟨q, ⟨hq0, by linarith⟩, haE, fun r hr => ?_⟩
    calc (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            (q : ℝ) * ‖x - a‖})
        ≤ (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖}) := by
          refine measure_mono (inter_subset_inter_right _ fun x hx => ⟨hx.1, hx.2.trans_le ?_⟩)
          exact mul_le_mul_of_nonneg_right hq2.le (norm_nonneg _)
      _ ≤ ENNReal.ofReal (η₀ * (r * s) ^ (m + 1)) := hs r hr
      _ ≤ ENNReal.ofReal (2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have hr0 : 0 ≤ r := hr.1.le
          have h1 : (r * s) ^ (m + 1) ≤ (2 * (r * q)) ^ (m + 1) := by
            apply pow_le_pow_left₀ (by positivity)
            nlinarith
          calc η₀ * (r * s) ^ (m + 1) ≤ η₀ * (2 * (r * q)) ^ (m + 1) :=
                mul_le_mul_of_nonneg_left h1 hη₀pos.le
            _ = 2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1) := by rw [mul_pow]; ring
  -- Step 3(b)
  have hnull : ∀ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 → (μHE[m + 1] : Measure (Eucl N)) (Bq q) = 0 := by
    rintro q ⟨hq0, hq1⟩
    apply hudn (Bq q) (δ / 13) (by positivity)
    intro x hx ρ hρ hρle
    have hcd := hcde (Bq q) q (12 * ρ) (2 ^ (m + 1) * η₀) (fun a ha => ha.1) hq0 hq1
      (by positivity) (by positivity) (fun a ha r hr0 hrle => ha.2 r ⟨hr0, by linarith⟩) x
    calc (μHE[m + 1] : Measure (Eucl N)) (Bq q ∩ closedBall x ρ)
        ≤ (μHE[m + 1] : Measure (Eucl N)) (Bq q ∩ ball x (12 * ρ / 6)) :=
          measure_mono (inter_subset_inter_right _ (closedBall_subset_ball (by linarith)))
      _ ≤ ENNReal.ofReal (C₁ * (2 ^ (m + 1) * η₀) * (12 * ρ) ^ (m + 1)) := hcd
      _ = ENNReal.ofReal (c * ρ ^ (m + 1)) := by
          congr 1
          have h24 : (24 : ℝ) ^ (m + 1) = 2 ^ (m + 1) * 12 ^ (m + 1) := by
            rw [← mul_pow]; norm_num
          rw [hη₀, mul_pow, h24]
          field_simp
  apply measure_mono_null hsub
  refine measure_iUnion_null fun q => measure_iUnion_null fun hq => hnull q hq
/-- The upper limit of `f : ℝ → [0,∞]` at `0⁺` is computed along the radii `1/(n+1)`:
`limsup_{t→0⁺} f(t) = inf_{n ∈ ℕ} sup_{0<t<1/(n+1)} f(t)`.  The intervals `(0, ε)`, `ε > 0`, form
a basis of `𝓝[>] 0`, so the upper limit is `inf_{ε>0} sup_{(0,ε)} f`; each radius `1/(n+1)` is
admissible, and every `ε > 0` exceeds some `1/(n+1)`, below which the supremum is smaller. -/
theorem Submission.rectifiability_mickle_rado_limsup_eq_iInf :
    ∀ f : ℝ → ℝ≥0∞, limsup f (𝓝[>] (0 : ℝ)) =
      ⨅ n : ℕ, ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), f t := by
  intro f
  rw [(nhdsGT_basis (0 : ℝ)).limsup_eq_iInf_iSup]
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact iInf₂_le (1 / ((n : ℝ) + 1)) (by positivity)
  · refine le_iInf₂ fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine (iInf_le _ n).trans ?_
    exact biSup_mono fun t ht => ⟨ht.1, ht.2.trans hn⟩
theorem Submission.rectifiability_mickle_rado_sup_lsc : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))), (∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ')) → ∀ r : ℝ, LowerSemicontinuous (fun c : Eucl (m + 1) => ⨆ t ∈ Ioo (0 : ℝ) r, ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) := by
  intro m ψ hball r
  -- step 1: `c ↦ ψ (ball c τ)` is lower semicontinuous, by inner continuity on balls
  have hlsc : ∀ τ : ℝ, LowerSemicontinuous (fun c : Eucl (m + 1) => ψ (ball c τ)) := by
    intro τ c a ha
    change a < ψ (ball c τ) at ha
    rw [hball c τ] at ha
    obtain ⟨τ', hτ', hlt⟩ := lt_biSup_iff.1 ha
    filter_upwards [ball_mem_nhds c (sub_pos.2 hτ'.2)] with c' hc'
    refine hlt.trans_le (measure_mono ?_)
    intro z hz
    rw [mem_ball] at hz hc' ⊢
    calc dist z c' ≤ dist z c + dist c c' := dist_triangle _ _ _
      _ < τ' + (τ - τ') := by rw [dist_comm c c']; exact add_lt_add hz hc'
      _ = τ := by ring
  -- step 2: divide by the positive finite `tᵏ`, then take the supremum over `t ∈ (0, r)`
  apply lowerSemicontinuous_biSup
  intro t ht
  have hden : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht.1 _)).ne'
  exact (ENNReal.continuous_div_const _ hden).comp_lowerSemicontinuous (hlsc t)
    (fun _ _ h => ENNReal.div_le_div_right h _)
/-- Vitali covering estimate off a `ψ`-null closed set, a covering step for the Mickle–Radó
density theorem (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439).  If `K` is closed,
`ψ K = 0` and `ψ(B(z,τ)) ≤ C τᵏ` for `z ∈ K`, `0 < τ < r` (`k = m + 1`), then
`ψ(B(c₀,t)) · Lᵏ(B(0,1)) ≤ C 6ᵏ Lᵏ(B(c₀,2t) ∖ K)` for `c₀ ∈ K`, `0 < t`, `6t ≤ r`.  The balls
`B(z, d z)`, `d z = dist(z,K)`, `z ∈ B(c₀,t) ∖ K`, miss `K` and lie in `B(c₀,2t)`.  A disjoint
(hence countable) Vitali subfamily has `5`-fold enlargements covering `B(c₀,t) ∖ K`, and
`B(b, 5 d b) ⊆ B(z'_b, 6 d b)` for a nearest point `z'_b ∈ K` of `b`, where `6 d b < 6t ≤ r`. -/
theorem Submission.rectifiability_mickle_rado_vitali_bound : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ c₀ ∈ K, ∀ t : ℝ, 0 < t → 6 * t ≤ r → ψ (ball c₀ t) * (volume : Measure (Eucl (m + 1))) (ball 0 1) ≤ C * 6 ^ (m + 1) * (volume : Measure (Eucl (m + 1))) (ball c₀ (2 * t) \ K) := by
  intro m ψ K C r hK hψK hbound c₀ hc₀ t ht htr
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  set ω := μ (ball 0 1) with hω
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  have hKne : K.Nonempty := ⟨c₀, hc₀⟩
  -- step 1: `ψ(B(c₀,t)) ≤ ψ(B(c₀,t) ∖ K) + ψ(K) = ψ(B(c₀,t) ∖ K)`
  have h1 : ψ (ball c₀ t) ≤ ψ (ball c₀ t \ K) := by
    calc ψ (ball c₀ t) ≤ ψ ((ball c₀ t \ K) ∪ K) := measure_mono (fun x hx => by
          by_cases h : x ∈ K
          · exact Or.inr h
          · exact Or.inl ⟨hx, h⟩)
      _ ≤ ψ (ball c₀ t \ K) + ψ K := measure_union_le _ _
      _ = ψ (ball c₀ t \ K) := by rw [hψK, add_zero]
  set T := ball c₀ t \ K with hT
  -- step 2: on `T`, the radius `d z = dist(z, K)` satisfies `0 < d z ≤ dist(z, c₀) < t`
  set d : Eucl (m + 1) → ℝ := fun z => infDist z K with hd
  have hd_pos : ∀ z ∈ T, 0 < d z := fun z hz => (hK.notMem_iff_infDist_pos hKne).1 hz.2
  have hd_lt : ∀ z ∈ T, d z < t := fun z hz =>
    (infDist_le_dist_of_mem hc₀).trans_lt (mem_ball.1 hz.1)
  -- steps 3–4: a disjoint, hence countable, Vitali subfamily `u ⊆ T` with enlargement factor `5`
  obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    T (fun z => z) d t (fun z hz => (hd_lt z hz).le) 5 (by norm_num)
  have hu_count : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun z hz => ⟨z, mem_ball_self (hd_pos z (huT hz))⟩)
  -- step 5: recentre at nearest points `z' b ∈ K`, so that `T ⊆ ⋃_{b ∈ u} B(z' b, 6 d b)`
  have hnear : ∀ z, ∃ y ∈ K, infDist z K = dist z y := fun z => hK.exists_infDist_eq_dist hKne z
  choose z' hz'K hz'd using hnear
  have hcover : T ⊆ ⋃ b ∈ u, ball (z' b) (6 * d b) := by
    intro a ha
    obtain ⟨b, hbu, hab⟩ := hcov a ha
    have hab' : a ∈ ball b (5 * d b) := hab (mem_ball_self (hd_pos a ha))
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hab' ⊢
    have hbz : dist b (z' b) = d b := (hz'd b).symm
    calc dist a (z' b) ≤ dist a b + dist b (z' b) := dist_triangle _ _ _
      _ < 5 * d b + d b := by rw [hbz]; linarith
      _ = 6 * d b := by ring
  -- steps 6–7: as `0 < 6 d b < 6t ≤ r`, `ψ(T) ≤ ∑_{b ∈ u} C 6ᵏ (d b)ᵏ`
  have h2 : ψ T ≤ ∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
    calc ψ T ≤ ψ (⋃ b ∈ u, ball (z' b) (6 * d b)) := measure_mono hcover
      _ ≤ ∑' b : u, ψ (ball (z' b) (6 * d b)) := measure_biUnion_le ψ hu_count _
      _ ≤ ∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        have hb : (b : Eucl (m + 1)) ∈ T := huT b.2
        have hpos := hd_pos b hb
        have hlt := hd_lt b hb
        calc ψ (ball (z' b) (6 * d b)) ≤ C * ENNReal.ofReal ((6 * d b) ^ (m + 1)) :=
              hbound (z' b) (hz'K b) (6 * d b) ⟨by linarith, by linarith⟩
          _ = C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
            rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
            simp [mul_assoc]
  -- step 8: for the disjoint balls `B(b, d b) ⊆ B(c₀,2t) ∖ K`,
  -- `∑_{b ∈ u} (d b)ᵏ ω = Lᵏ(⋃_{b ∈ u} B(b, d b)) ≤ Lᵏ(B(c₀,2t) ∖ K)`
  have h3 : ∑' b : u, ENNReal.ofReal ((d b) ^ (m + 1)) * ω ≤ μ (ball c₀ (2 * t) \ K) := by
    have heq : ∀ b : u,
        ENNReal.ofReal ((d b) ^ (m + 1)) * ω = μ (ball (b : Eucl (m + 1)) (d b)) := by
      intro b
      rw [Measure.addHaar_ball μ _ (hd_pos b (huT b.2)).le, hfin]
    simp_rw [heq]
    rw [← measure_biUnion hu_count hdisj (fun _ _ => measurableSet_ball)]
    apply measure_mono
    intro y hy
    obtain ⟨b, hbu, hyb⟩ := mem_iUnion₂.1 hy
    have hbT := huT hbu
    refine ⟨?_, ?_⟩
    · rw [mem_ball] at hyb ⊢
      have hbc := mem_ball.1 hbT.1
      have := hd_lt b hbT
      calc dist y c₀ ≤ dist y b + dist b c₀ := dist_triangle _ _ _
        _ < 2 * t := by linarith
    · intro hyK
      exact Set.disjoint_left.1 (disjoint_ball_infDist (x := b) (s := K)) hyb hyK
  -- step 9: combine, pulling the constants out of the sums
  calc ψ (ball c₀ t) * ω
      ≤ (∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1))) * ω := by
        gcongr; exact h1.trans h2
    _ = C * 6 ^ (m + 1) * ∑' b : u, ENNReal.ofReal ((d b) ^ (m + 1)) * ω := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, mul_assoc]
    _ ≤ C * 6 ^ (m + 1) * μ (ball c₀ (2 * t) \ K) := by gcongr

/-- Mickle–Radó density step (Mattila, Thm 18.5, step 3 with `ε ↓ 0`): if `ψ(B(z,τ)) ≤ C τᵏ`
for `z ∈ K`, `0 < τ < r`, where `K` is closed and `ψ(K) = 0`, then the upper `k`-density of `ψ`
vanishes at `Lᵏ`-a.e. point of `K`.  At a Lebesgue density point `c ∈ K` of `K`, the Vitali
estimate `ψ(B(c,t))·ω ≤ C·6ᵏ·Lᵏ(B(c,2t) ∖ K)` together with
`Lᵏ(B̄(c,2t) ∖ K) = (2t)ᵏ·ω·(1 − R_c(2t))`, `R_c(ρ) = Lᵏ(K ∩ B̄(c,ρ))/Lᵏ(B̄(c,ρ)) → 1`, gives
`ψ(B(c,t))/tᵏ ≤ C·12ᵏ·(1 − R_c(2t)) → 0`. -/
theorem Submission.rectifiability_mickle_rado_density_zero : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → C ≠ ⊤ → 0 < r → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ᵐ c ∂((volume : Measure (Eucl (m + 1))).restrict K), limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) = 0 := by
  intro m ψ K C r hK hψK hC hr hbound
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ K, ae_restrict_mem hK.measurableSet]
    with c hc hcK
  apply Tendsto.limsup_eq
  set ω := μ (ball 0 1) with hω
  have hω0 : ω ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hωtop : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  -- the density ratio at radius 2t
  have hR2 : Tendsto (fun t : ℝ => μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))
      (𝓝[>] 0) (𝓝 1) := by
    refine hc.comp ?_
    have h2 : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] (2 * 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_const.mul continuous_id).tendsto' _ _ rfl |>.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mem_Ioi.2 (by simpa using ht))
    simpa using h2
  have hlim : Tendsto (fun t : ℝ => C * 12 ^ (m + 1) *
      (1 - μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.sub tendsto_const_nhds hR2 (Or.inl ENNReal.one_ne_top)
    have h12 : C * 12 ^ (m + 1) ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.pow_ne_top (by norm_num))
    have h2 := ENNReal.Tendsto.const_mul (a := C * 12 ^ (m + 1)) h1 (Or.inr h12)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 6 by positivity)] with t ht
  have ht0 : 0 < t := ht.1
  have h0 := Submission.rectifiability_mickle_rado_vitali_bound m ψ K C r hK hψK hbound c hcK t ht0
    (by linarith [ht.2])
  -- measure of the complement in the closed ball
  set V := μ (closedBall c (2 * t)) with hV
  set A := μ (K ∩ closedBall c (2 * t)) with hA
  have hVball : V = ENNReal.ofReal ((2 * t) ^ (m + 1)) * ω := by
    rw [hV, Measure.addHaar_closedBall μ c (by positivity), hfin]
  have hV0 : V ≠ 0 := by
    rw [hVball]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hω0
  have hVtop : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hAle : A ≤ V := measure_mono inter_subset_right
  have hdiff : μ (ball c (2 * t) \ K) ≤ V * (1 - A / V) := by
    have hsplit : μ (closedBall c (2 * t) \ K) + A = V := by
      rw [hA, inter_comm]; exact measure_sdiff_add_inter _ hK.measurableSet
    have h1 : μ (ball c (2 * t) \ K) ≤ μ (closedBall c (2 * t) \ K) :=
      measure_mono (sdiff_subset_sdiff_left ball_subset_closedBall)
    have h2 : μ (closedBall c (2 * t) \ K) = V - A :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hVtop hAle) hsplit
    have h3 : V * (1 - A / V) = V - A := by
      rw [ENNReal.mul_sub (fun _ _ => hVtop), mul_one, ENNReal.mul_div_cancel hV0 hVtop]
    rw [h3, ← h2]; exact h1
  -- conclude
  have hpowt : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
  rw [ENNReal.div_le_iff_le_mul (Or.inl hpowt) (Or.inl ENNReal.ofReal_ne_top)]
  have h2t : ENNReal.ofReal ((2 * t) ^ (m + 1)) = 2 ^ (m + 1) * ENNReal.ofReal (t ^ (m + 1)) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  have key : ψ (ball c t) * ω ≤
      (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
    calc ψ (ball c t) * ω ≤ C * 6 ^ (m + 1) * μ (ball c (2 * t) \ K) := h0
      _ ≤ C * 6 ^ (m + 1) * (V * (1 - A / V)) := by gcongr
      _ = (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
        rw [hVball, h2t]
        have : (12 : ℝ≥0∞) ^ (m + 1) = 6 ^ (m + 1) * 2 ^ (m + 1) := by
          rw [← mul_pow]; norm_num
        rw [this]; ring
  exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key

/-- **Mickle–Radó density theorem** (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439;
Mattila, Thm 18.5).  Let `ψ` be an outer measure on `ℝᵏ`, `k = m + 1`, inner continuous on open
balls, and `D` a Borel set with `ψ(D) = 0`.  Then the upper density
`ϑ(c) = limsup_{t↓0} ψ(B(c,t))/tᵏ` lies in `{0, ∞}` at `Lᵏ`-a.e. point of `D`.  With
`g_n(c) = sup_{0<t<1/(n+1)} ψ(B(c,t))/tᵏ`, each `g_n` is lower semicontinuous and `ϑ = inf_n g_n`,
so `ϑ` is Borel.  The set `{c ∈ D : 0 < ϑ(c) < ∞}` is covered by the Borel sets
`S_n = {c ∈ D : (n+1)⁻¹ < ϑ(c), g_n(c) ≤ n+1}`.  If `Lᵏ(S_n) > 0`, a compact `K ⊆ S_n` with
`Lᵏ(K) > 0` has `ψ(K) = 0` and `ψ(B(z,τ)) ≤ (n+1)τᵏ` for `z ∈ K`, `0 < τ < 1/(n+1)`; hence
`ϑ = 0` at `Lᵏ`-a.e. point of `K`, contradicting `ϑ > (n+1)⁻¹` on `K`. -/
theorem Submission.rectifiability_mickle_rado : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (D : Set (Eucl (m + 1))), (∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ')) → MeasurableSet D → ψ D = 0 → (volume : Measure (Eucl (m + 1))) {c | c ∈ D ∧ 0 < limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) < ⊤} = 0 := by
  intro m ψ D hball hD hψD
  let g : ℕ → Eucl (m + 1) → ℝ≥0∞ := fun n c =>
    ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))
  let ϑ : Eucl (m + 1) → ℝ≥0∞ := fun c =>
    limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0)
  -- step 1: `ϑ = inf_n g_n` with every `g_n` lower semicontinuous, so `ϑ` is Borel
  have hϑ : ∀ c, ϑ c = ⨅ n, g n c := fun c =>
    Submission.rectifiability_mickle_rado_limsup_eq_iInf
      (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1)))
  have hg_meas : ∀ n, Measurable (g n) := fun n =>
    (Submission.rectifiability_mickle_rado_sup_lsc m ψ hball _).measurable
  have hϑ_meas : Measurable ϑ := by
    have h : ϑ = fun c => ⨅ n, g n c := funext hϑ
    rw [h]
    exact Measurable.iInf hg_meas
  have hg_anti : ∀ c, Antitone (fun n => g n c) := by
    intro c n n' hnn'
    apply biSup_mono
    intro t ht
    refine ⟨ht.1, lt_of_lt_of_le ht.2 ?_⟩
    have h1 : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
    gcongr
  -- step 2: `{c ∈ D : 0 < ϑ c < ∞} ⊆ ⋃_n S_n` for the Borel sets `S_n`
  let S : ℕ → Set (Eucl (m + 1)) := fun n =>
    {c | c ∈ D ∧ ((n : ℝ≥0∞) + 1)⁻¹ < ϑ c ∧ g n c ≤ (n : ℝ≥0∞) + 1}
  have hS_meas : ∀ n, MeasurableSet (S n) := by
    intro n
    exact hD.inter ((measurableSet_lt measurable_const hϑ_meas).inter
      (measurableSet_le (hg_meas n) measurable_const))
  have hsub : {c | c ∈ D ∧ 0 < limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) < ⊤} ⊆ ⋃ n, S n := by
    rintro c ⟨hcD, hpos, hfin⟩
    change ϑ c < ⊤ at hfin
    change 0 < ϑ c at hpos
    rw [hϑ c] at hfin
    obtain ⟨n₀, hn₀⟩ := iInf_lt_iff.1 hfin
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hn₀.ne
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    set n := max n₀ (max N n₁) with hn
    refine mem_iUnion.2 ⟨n, hcD, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hn₁
      apply ENNReal.inv_le_inv.2
      have : n₁ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
      have : (n₁ : ℝ≥0∞) ≤ n := by exact_mod_cast this
      exact this.trans le_self_add
    · calc g n c ≤ g n₀ c := hg_anti c (le_max_left _ _)
        _ ≤ N := hN.le
        _ ≤ (n : ℝ≥0∞) := by
          have : N ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
          exact_mod_cast this
        _ ≤ (n : ℝ≥0∞) + 1 := le_self_add
  -- step 3: `Lᵏ(S_n) = 0`, via a compact `K ⊆ S_n` and the density-zero step on `K`
  have hS_null : ∀ n, (volume : Measure (Eucl (m + 1))) (S n) = 0 := by
    intro n
    by_contra hne
    obtain ⟨K, hKS, hKc, hKpos⟩ := (hS_meas n).exists_lt_isCompact (pos_iff_ne_zero.2 hne)
    have hψK : ψ K = 0 := measure_mono_null (fun x hx => (hKS hx).1) hψD
    have hbound : ∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ψ (ball z τ) ≤ ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (τ ^ (m + 1)) := by
      intro z hz τ hτ
      have h1 : ψ (ball z τ) / ENNReal.ofReal (τ ^ (m + 1)) ≤ g n z :=
        le_iSup₂ (f := fun t (_ : t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))) =>
          ψ (ball z t) / ENNReal.ofReal (t ^ (m + 1))) τ hτ
      have h2 := h1.trans (hKS hz).2.2
      rwa [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.ofReal_pos.2 (pow_pos hτ.1 _)).ne')
        (Or.inl ENNReal.ofReal_ne_top)] at h2
    have hae := Submission.rectifiability_mickle_rado_density_zero m ψ K ((n : ℝ≥0∞) + 1)
      (1 / ((n : ℝ) + 1)) hKc.isClosed hψK (by simp) (by positivity) hbound
    obtain ⟨c, hcK, hc0⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hKpos.ne' hae
    have h3 : ((n : ℝ≥0∞) + 1)⁻¹ < ϑ c := (hKS hcK).2.1
    change _ < limsup _ _ at h3
    rw [hc0] at h3
    exact (ENNReal.not_lt_zero h3).elim
  exact measure_mono_null hsub (measure_iUnion_null hS_null)

/-- For an s-finite `μ` and measurable sets `G r s ⊆ Z × Y`, increasing in `s` and with
`G r s = ⋃_{0<r'<r} G r' s` for `r > 0`, the map
`z ↦ limsup_{s→0⁺} sup_{0<r<δ} μ{y | (z, y) ∈ G r s} / (r s)ᵏ` is measurable.  Each section
measure is measurable in `z` (Tonelli).  By continuity from below along rational `r' < r` the
supremum over `r` may be taken over rational `r`, and since `F(s) ≤ (s'/s)ᵏ F(s')` for
`0 < s ≤ s'`, the supremum over `s ∈ (0, ε)` may be taken over rational `s`.  Computing the upper
limit along the radii `1/(n+1)` then gives a countable `inf`–`sup` of measurable functions. -/
theorem Submission.rectifiability_bf_limsup_sup_measurable :
    ∀ (Z Y : Type) [MeasurableSpace Z] [MeasurableSpace Y] (k : ℕ) (μ : Measure Y) (δ : ℝ)
      (G : ℝ → ℝ → Set (Z × Y)), SFinite μ → (∀ r s, MeasurableSet (G r s)) →
      (∀ r s s', s ≤ s' → G r s ⊆ G r s') →
      (∀ r s, 0 < r → G r s = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' s) →
      Measurable (fun z : Z => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ,
        μ {y | (z, y) ∈ G r s} / ENNReal.ofReal ((r * s) ^ k)) (𝓝[>] 0)) := by
  intro Z Y _ _ k μ δ G hμ hG hmono hcont
  -- `g z r s` is the section measure and `F z s` the supremum over `r ∈ (0, δ)`
  let g : Z → ℝ → ℝ → ℝ≥0∞ := fun z r s => μ {y | (z, y) ∈ G r s}
  let F : Z → ℝ → ℝ≥0∞ := fun z s => ⨆ r ∈ Ioo (0 : ℝ) δ, g z r s / ENNReal.ofReal ((r * s) ^ k)
  show Measurable fun z => limsup (F z) (𝓝[>] 0)
  have hgm : ∀ r s, Measurable fun z => g z r s := fun r s =>
    measurable_measure_prodMk_left (hG r s)
  -- `G` is monotone in `r` on `(0, ∞)`
  have hGr : ∀ s r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → G r₁ s ⊆ G r₂ s := by
    intro s r₁ r₂ h1 h12
    rcases h12.lt_or_eq with h | rfl
    · rw [hcont r₂ s (h1.trans h)]
      exact subset_biUnion_of_mem (u := fun r' => G r' s) ⟨h1, h⟩
    · exact le_rfl
  -- the supremum over `r` is a supremum over rational `r`
  have hFq : ∀ z s, 0 < s → F z s = ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
      g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := by
    intro z s hs
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      have hU : {y | (z, y) ∈ G r s} =
          ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, {y | (z, y) ∈ G (q.1 : ℝ) s} := by
        ext y
        simp only [mem_iUnion, mem_ofPred_eq]
        constructor
        · intro hy
          rw [hcont r s hr.1] at hy
          simp only [mem_iUnion] at hy
          obtain ⟨r', hr', hy'⟩ := hy
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr'.2
          exact ⟨⟨q, hr'.1.trans hq1, hq2⟩, hGr s r' q hr'.1 hq1.le hy'⟩
        · rintro ⟨q, hy⟩
          exact hGr s q r q.2.1 q.2.2.le hy
      have hdir : Directed (· ⊆ ·)
          (fun q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r} => {y | (z, y) ∈ G (q.1 : ℝ) s}) := by
        intro q₁ q₂
        refine ⟨⟨max q₁.1 q₂.1, ?_, ?_⟩, ?_, ?_⟩
        · exact lt_of_lt_of_le q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1)
        · rw [Rat.cast_max]; exact max_lt q₁.2.2 q₂.2.2
        · intro y hy
          exact hGr s q₁.1 _ q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1) hy
        · intro y hy
          exact hGr s q₂.1 _ q₂.2.1 (by exact_mod_cast le_max_right q₁.1 q₂.1) hy
      have hgr : g z r s = ⨆ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, g z (q.1 : ℝ) s := by
        show μ {y | (z, y) ∈ G r s} = _
        rw [hU]
        exact hdir.measure_iUnion
      rw [hgr, ENNReal.iSup_div]
      refine iSup_le fun q => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ) =>
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k)) q.1 ⟨q.2.1, q.2.2.trans hr.2⟩)
      apply ENNReal.div_le_div_left
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (mul_pos q.2.1 hs).le
      exact mul_le_mul_of_nonneg_right q.2.2.le hs.le
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) => g z r s / ENNReal.ofReal ((r * s) ^ k))
        (q : ℝ) hq
  have hFm : ∀ s, 0 < s → Measurable fun z => F z s := by
    intro s hs
    have : (fun z => F z s) = fun z => ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := funext fun z => hFq z s hs
    rw [this]
    exact Measurable.iSup fun q => Measurable.iSup fun _ => (hgm q s).div_const _
  -- scaling in `s`: `F z s ≤ (s'/s)ᵏ F z s'` for `0 < s ≤ s'`
  have hscale : ∀ z s s', 0 < s → s ≤ s' → F z s ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
    intro z s s' hs hss'
    refine iSup₂_le fun r hr => ?_
    have hs' : 0 < s' := hs.trans_le hss'
    have h1 : g z r s ≤ g z r s' := measure_mono (fun y hy => hmono r s s' hss' hy)
    have hA : ENNReal.ofReal ((r * s') ^ k) =
        ENNReal.ofReal ((s' / s) ^ k) * ENNReal.ofReal ((r * s) ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      congr 2
      field_simp
    have hc0 : ENNReal.ofReal ((s' / s) ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    calc g z r s / ENNReal.ofReal ((r * s) ^ k)
        ≤ g z r s' / ENNReal.ofReal ((r * s) ^ k) := ENNReal.div_le_div_right h1 _
      _ = ENNReal.ofReal ((s' / s) ^ k) * (g z r s' / ENNReal.ofReal ((r * s') ^ k)) := by
          rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
          gcongr
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            g z r s' / ENNReal.ofReal ((r * s') ^ k)) r hr
  -- the supremum over `s ∈ (0, ε)` is a supremum over rational `s`
  have hsupq : ∀ z (ε : ℝ), 0 < ε → ⨆ s ∈ Ioo (0 : ℝ) ε, F z s =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
    intro z ε hε
    apply le_antisymm
    · refine iSup₂_le fun s hs => ?_
      have hn : ∀ n : ℕ, F z s ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
          ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
        intro n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hlt : s < min ε (s * (1 + 1 / ((n : ℝ) + 1))) := by
          refine lt_min hs.2 ?_
          have := mul_pos hs.1 hpos
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        have hqε : (q : ℝ) < ε := hq2.trans_le (min_le_left _ _)
        have hq0 : 0 < (q : ℝ) := hs.1.trans hq1
        calc F z s ≤ ENNReal.ofReal (((q : ℝ) / s) ^ k) * F z q := hscale z s q hs.1 hq1.le
          _ ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
              ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
            gcongr ?_ * ?_
            · apply ENNReal.ofReal_le_ofReal
              apply pow_le_pow_left₀ (div_pos hq0 hs.1).le
              rw [div_le_iff₀ hs.1]
              have := hq2.trans_le (min_le_right _ _)
              linarith
            · exact le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε) => F z q) q
                ⟨hq0, hqε⟩
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k)) atTop
          (𝓝 1) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.tendsto_ofReal
        have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1).pow k
        simpa using this
      have htend := ENNReal.Tendsto.mul_const h1
        (Or.inl one_ne_zero) (b := ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q)
      rw [one_mul] at htend
      exact ge_of_tendsto' htend hn
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun s (_ : s ∈ Ioo (0 : ℝ) ε) => F z s) (q : ℝ) hq
  -- the upper limit along the radii `1/(n+1)`, with rational `s`
  have hform : ∀ z, limsup (F z) (𝓝[>] 0) = ⨅ n : ℕ, ⨆ q : ℚ,
      ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))), F z q := by
    intro z
    rw [Submission.rectifiability_mickle_rado_limsup_eq_iInf (F z)]
    congr 1
    funext n
    exact hsupq z _ (by positivity)
  rw [funext hform]
  exact Measurable.iInf fun n => Measurable.iSup fun q => Measurable.iSup fun hq => hFm q hq.1
/-- The parameter set of fibre witnesses (alternative T3 of the Besicovitch–Federer trichotomy in
the proof of Simon Ch. 6, 8.1) is Borel.  For `E ⊆ ℝ^N` σ-compact, `δ ∈ ℝ` and
`L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`), the set `W` of `(a, v)` admitting `x ∈ E` with
`x ≠ a`, `|x − a| < δ` and `L_v x = L_v a` is measurable.  With `E = ⋃ₙ Kₙ`, `Kₙ` compact,
`W = ⋃_{n,l} π(C_{n,l})`, where `π(x, (a, v)) = (a, v)` and `C_{n,l}` is the compact set of
`(x, (a, v))` with `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)` and
`L_v x = L_v a`. -/
theorem Submission.rectifiability_bf_witness_set_measurable : (∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → MeasurableSet {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))}) := by
  intro N m E δ hE
  -- `E = ⋃ₙ Kₙ` with every `Kₙ` compact.
  obtain ⟨K, hK, hKE⟩ := hE
  -- `(x, (a, v)) ↦ L_v x` and `(x, (a, v)) ↦ L_v a` are continuous.
  have hLc : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner continuous_fst
  have hLc' : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner
      (continuous_fst.comp continuous_snd)
  -- `C_{n,l}`: `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)`, `L_v x = L_v a`.
  let C : ℕ → ℕ → Set (Eucl N × (Eucl N × (Fin (m + 1) → Eucl N))) := fun n l =>
    (K n ×ˢ closedBall (0 : Eucl N × (Fin (m + 1) → Eucl N)) l) ∩
      ({q | 1 / ((l : ℝ) + 1) ≤ dist q.1 q.2.1} ∩ {q | dist q.1 q.2.1 ≤ δ - 1 / ((l : ℝ) + 1)} ∩
        {q | (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1)) =
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))})
  -- A compact set intersected with closed conditions is compact.
  have hCc : ∀ n l, IsCompact (C n l) := by
    intro n l
    refine ((hK n).prod (isCompact_closedBall _ _)).inter_right ?_
    refine ((isClosed_le continuous_const ?_).inter (isClosed_le ?_ continuous_const)).inter
      (isClosed_eq hLc hLc')
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
  -- `W = ⋃_{n,l} π(C_{n,l})`, choosing `l` by the Archimedean property.
  have key : {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) =
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))} =
      ⋃ n, ⋃ l : ℕ, Prod.snd '' C n l := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨x, hxE, hxa, hxδ, hL⟩
      rw [← hKE, mem_iUnion] at hxE
      obtain ⟨n, hn⟩ := hxE
      have hd0 : 0 < dist x p.1 := dist_pos.2 hxa
      have hmin : 0 < min (dist x p.1) (δ - dist x p.1) := lt_min hd0 (by linarith)
      obtain ⟨l₁, hl₁⟩ := exists_nat_one_div_lt hmin
      obtain ⟨l₂, hl₂⟩ := exists_nat_ge ‖p‖
      refine ⟨n, max l₁ l₂, (x, p), ?_, rfl⟩
      have hle : 1 / ((max l₁ l₂ : ℕ) + 1 : ℝ) ≤ 1 / ((l₁ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (l₁ : ℝ) ≤ ((max l₁ l₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left l₁ l₂
        linarith
      have h1 := lt_of_le_of_lt hle hl₁
      refine ⟨⟨hn, ?_⟩, ⟨?_, ?_⟩, hL⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hl₂.trans (by exact_mod_cast le_max_right l₁ l₂)
      · exact (h1.trans_le (min_le_left _ _)).le
      · have := h1.trans_le (min_le_right _ _)
        simp only [mem_ofPred_eq]
        linarith
    · rintro ⟨n, l, q, ⟨⟨hq1, -⟩, ⟨hd1, hd2⟩, hL⟩, rfl⟩
      refine ⟨q.1, ?_, ?_, ?_, hL⟩
      · rw [← hKE]; exact mem_iUnion.2 ⟨n, hq1⟩
      · intro h
        have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq, h, dist_self] at hd1
        linarith
      · have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq] at hd2
        linarith
  -- Each `π(C_{n,l})` is compact, hence Borel; so is the countable union.
  rw [key]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun l =>
    ((hCc n l).image continuous_snd).measurableSet

/-- **Borel measurability of the cone ratio** (step 2(a)–(c) of the Besicovitch–Federer
trichotomy, Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 18.9).  For
`v ∈ (ℝ^N)^k`, `k = m + 1`, let `L_v y = (⟨v₁, y⟩, …, ⟨v_k, y⟩)` and
`X_v(a, r, s) = {x : |x - a| < r, |L_v (x - a)| < s |x - a|}`.  Then
`Φ(a, v) = limsup_{s → 0⁺} sup_{0 < r < δ} μ(X_v(a, r, s)) / (rs)ᵏ` is measurable in `(a, v)`:
the cones are the sections of `G(r, s) = {((a, v), x) : |x - a| < r, |L_v (x - a)| < s |x - a|}`,
which is open, monotone in `s` and left continuous in `r`, so `limsup_sup_measurable` applies. -/
theorem Submission.rectifiability_bf_cone_ratio_measurable : ∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ), SFinite μ → Measurable (fun p : Eucl N × (Fin (m + 1) → Eucl N) => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) := by
  intro N m μ δ hμ
  -- Step 1: the cone `X_v(a, r, s)` is the section of `G(r, s)` at `z = (a, v)`.
  refine Submission.rectifiability_bf_limsup_sup_measurable (Eucl N × (Fin (m + 1) → Eucl N))
    (Eucl N) (m + 1) μ δ (fun r s => {q | dist q.2 q.1.1 < r ∧
      ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) : Eucl (m + 1))‖ <
        s * ‖q.2 - q.1.1‖}) hμ ?_ ?_ ?_
  -- Step 2: `G(r, s)` is open (strict inequalities between continuous functions), hence
  -- measurable in the second-countable product.
  · intro r s
    have hL : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N =>
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) :
          Eucl (m + 1))‖ :=
      continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
        ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).inner
          (continuous_snd.sub (continuous_fst.comp continuous_fst))))
    have hd : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N => dist q.2 q.1.1 :=
      by fun_prop
    have hn : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N =>
        s * ‖q.2 - q.1.1‖ := by fun_prop
    exact ((isOpen_lt hd continuous_const).inter (isOpen_lt hL hn)).measurableSet
  -- Step 3: `G(r, s)` is monotone in `s`, as `s |x - a| ≤ s' |x - a|` for `s ≤ s'`.
  · intro r s s' hss' q hq
    exact ⟨hq.1, hq.2.trans_le (by gcongr)⟩
  -- Step 4: `G(r, s) = ⋃_{0 < r' < r} G(r', s)`; for `|x - a| < r` take `r' = (|x - a| + r) / 2`.
  · intro r s hr
    ext q
    simp only [mem_iUnion, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 q.1.1 + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨-, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
/-- Cone-ratio dichotomy.  Write `L x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`),
`X(r, s) = {x : |x − a| < r, |L(x − a)| < s|x − a|}` and
`Φ = limsup_{s→0⁺} sup_{0<r<δ} μ(X(r, s))/(rs)ᵏ`.  If `Φ = 0`, then for each `η > 0` some
`s ∈ (0, 1)` has `μ(X(r, s)) ≤ η(rs)ᵏ` for all `r ∈ (0, δ)`.  If `Φ = ∞`, then
`X(r, s) ⊆ L⁻¹(B̄(La, rs))`, so the push-forward `L_# μ` has infinite upper `k`-density at
`La`: its density quotients at the radii `rs → 0⁺` are unbounded. -/
theorem Submission.rectifiability_bf_cone_ratio_reduction :
    (∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (v : Fin (m + 1) → Eucl N),
      (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = 0 →
        ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∧
      (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = ⊤ →
        dimensionalUpperDensity (Measure.map (fun x : Eucl N =>
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) μ).toOuterMeasure
          ((m + 1 : ℕ) : ℝ) univ
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤)) := by
  intro N m μ δ a v
  -- `X r s` is the cone, `F s` the supremum of the ratios `μ(X r s)/(rs)ᵏ` over `r ∈ (0, δ)`
  set X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧
    ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}
  set F : ℝ → ℝ≥0∞ := fun s =>
    ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1)) with hF
  constructor
  · -- `Φ = 0`: eventually `F s < η`; take such an `s ∈ (0, 1)`
    intro h0 η hη
    have hlt : limsup F (𝓝[>] 0) < ENNReal.ofReal η := by
      rw [h0]; exact ENNReal.ofReal_pos.2 hη
    obtain ⟨s, hs1, hs2⟩ :=
      ((eventually_lt_of_limsup_lt hlt).and (Ioo_mem_nhdsGT one_pos)).exists
    refine ⟨s, hs2, fun r hr => ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos (mul_pos hr.1 hs2.1) _
    have h3 : μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1)) < ENNReal.ofReal η :=
      (le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
        μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))) r hr).trans_lt hs1
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 hpos).ne') (Or.inl ENNReal.ofReal_ne_top)]
      at h3
    rw [ENNReal.ofReal_mul hη.le]
    exact h3.le
  · -- `Φ = ∞`: ratios above `b ω_k` at `r < δ`, small `s` give density quotients above `b` at `rs`
    intro htop
    set L : Eucl N → Eucl (m + 1) := fun x =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) with hL
    have hLc : Continuous L :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_const.inner continuous_id)
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      simp only [hL, ← WithLp.toLp_sub]
      congr 1
      funext i
      simp [inner_sub_right]
    set ω := Poincare.SimonGMT.Chapter01.realUnitBallVolume (((m + 1 : ℕ) : ℝ)) with hω
    have hω0 : ω ≠ 0 := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      refine (ENNReal.ofReal_pos.2 (div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
        (Real.Gamma_pos_of_pos ?_))).ne'
      positivity
    have hωt : ω ≠ ⊤ := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      exact ENNReal.ofReal_ne_top
    -- `δ > 0`, since otherwise `F = 0` and `Φ = 0`
    have hδ : 0 < δ := by
      by_contra hδ
      have hF0 : F = fun _ => 0 := by
        funext s
        rw [hF, Ioo_eq_empty (not_lt.2 (not_lt.1 hδ))]
        simp
      rw [hF0, limsup_const] at htop
      exact ENNReal.zero_ne_top htop
    unfold dimensionalUpperDensity
    refine ENNReal.eq_top_of_forall_nnreal_le fun b => ?_
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    rw [(nhdsGT_basis (0 : ℝ)).frequently_iff]
    intro ρ₀ hρ₀
    have hΛ : (b : ℝ≥0∞) * ω < limsup F (𝓝[>] 0) := by
      rw [htop]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.2 hωt)
    obtain ⟨s, hs1, hs2⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hΛ).and_eventually
      (Ioo_mem_nhdsGT (div_pos hρ₀ hδ))).exists
    obtain ⟨r, hr, hrs⟩ := lt_biSup_iff.1 hs1
    have hrs0 : 0 < r * s := mul_pos hr.1 hs2.1
    have hrsρ : r * s < ρ₀ := by
      have h1 : r * s < δ * (ρ₀ / δ) := mul_lt_mul'' hr.2 hs2.2 hr.1.le hs2.1.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at h1
    refine ⟨r * s, ⟨hrs0, hrsρ⟩, ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos hrs0 _
    -- the cone lies in the preimage of the closed ball `B̄(La, rs)`
    have hsub : X r s ⊆ L ⁻¹' closedBall (L a) (r * s) := by
      intro x hx
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, hLsub]
      have h1 : ‖x - a‖ < r := by rw [← dist_eq_norm]; exact hx.1
      calc ‖L (x - a)‖ ≤ s * ‖x - a‖ := hx.2.le
        _ ≤ s * r := by gcongr; exact hs2.1.le
        _ = r * s := mul_comm _ _
    have hmap :
        μ (X r s) ≤ (Measure.map L μ).toOuterMeasure (univ ∩ closedBall (L a) (r * s)) := by
      rw [Measure.coe_toOuterMeasure, univ_inter,
        Measure.map_apply hLc.measurable isClosed_closedBall.measurableSet]
      exact measure_mono hsub
    unfold Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
    rw [ENNReal.ofReal_rpow_of_nonneg hrs0.le (by positivity), Real.rpow_natCast,
      ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 (ENNReal.ofReal_pos.2 hpos).ne'))
        (Or.inl (ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top))]
    refine le_trans ?_ hmap
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at hrs
    rw [← mul_assoc]
    exact hrs.le
/-- Cones versus unions of coordinate fibres (step 4 of the Besicovitch–Federer trichotomy,
Mattila 18.9, used for Simon Ch. 6, 8.1).  Let `k = m + 1`, `L_u(y) = (⟨u₁, y⟩, …, ⟨u_k, y⟩)`,
`X_u(a, r, s) = {x : |x − a| < r, |L_u(x − a)| < s|x − a|}`, `u ⊕_j c = (uᵢ + cᵢ e_j)ᵢ` and
`K_j(t) = {x ≠ a : L_{u ⊕_j c}(x − a) = 0 for some |c| < t}`.  With
`Φ = limsup_{s → 0⁺} sup_{0<r<δ} μ(X_u(a, r, s))/(rs)ᵏ` and
`ϑ_j = limsup_{t → 0⁺} sup_{0<r<δ} μ(B(a, r) ∩ K_j(t))/(rt)ᵏ`, we have `ϑ_j ≤ Φ` for every `j`
and `Φ ≤ (√N)ᵏ Σ_j ϑ_j`.  Since `L_{u ⊕_j c}(y) = L_u(y) + y_j c`,
`B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` and `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(√N s)`. -/
theorem Submission.rectifiability_bf_fibre_cone_comparison :
    ∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (u : Fin (m + 1) → Eucl N), (∀ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ≤ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) ∧ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) := by
  intro N m μ δ a u
  -- `L = L_u`, `K j t = K_j(t)`, `X r s = X_u(a, r, s)`, `F = F`, `Fj j = F_j`.
  let L : Eucl N → Eucl (m + 1) := fun y => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let K : Fin N → ℝ → Set (Eucl N) := fun j t => {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t,
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧ ‖L (x - a)‖ < s * ‖x - a‖}
  let F : ℝ → ℝ≥0∞ := fun s => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
  let Fj : Fin N → ℝ → ℝ≥0∞ := fun j t => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ K j t) / ENNReal.ofReal ((r * t) ^ (m + 1))
  show (∀ j, limsup (Fj j) (𝓝[>] 0) ≤ limsup F (𝓝[>] 0)) ∧
    limsup F (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (Fj j) (𝓝[>] 0)
  -- Step 1, fibre identity: `L_{u ⊕_j c}(y) = L_u(y) + y_j c`.
  have hfib : ∀ (j : Fin N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) : Eucl (m + 1)) =
        L y + (y j) • c := by
    intro j c y
    ext i
    simp [L, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  -- Step 2, inclusion (ii): `B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` for `t > 0`.
  have hincl2 : ∀ (j : Fin N) (r t : ℝ), 0 < t → ball a r ∩ K j t ⊆ X r t := by
    rintro j r t ht x ⟨hxr, hxa, c, hc, hx0⟩
    refine ⟨hxr, ?_⟩
    rw [hfib] at hx0
    have hL : L (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left hx0
    rw [hL, norm_neg, norm_smul]
    have hy : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hxa)
    have hc' : ‖c‖ < t := by simpa using hc
    have hyj : ‖(x - a) j‖ ≤ ‖x - a‖ := PiLp.norm_apply_le _ _
    calc ‖(x - a) j‖ * ‖c‖ ≤ ‖x - a‖ * ‖c‖ := by gcongr
      _ < ‖x - a‖ * t := mul_lt_mul_of_pos_left hc' hy
      _ = t * ‖x - a‖ := mul_comm _ _
  refine ⟨fun j => ?_, ?_⟩
  -- Step 3: `F_j ≤ F` on `(0, ∞)`, hence `ϑ_j ≤ Φ`.
  · refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine iSup₂_mono fun r hr => ?_
    exact ENNReal.div_le_div_right (measure_mono (hincl2 j r t ht)) _
  · rcases Nat.eq_zero_or_pos N with hN | hN
    -- Step 4: for `N = 0` every cone is empty, so `Φ = 0`.
    · subst hN
      have hF0 : F = fun _ => 0 := by
        funext s
        have hX : ∀ r, X r s = ∅ := by
          intro r
          ext x
          have hxa : x - a = 0 := Subsingleton.elim _ _
          simp [X, hxa]
        simp [F, hX]
      rw [hF0, limsup_const]
      exact zero_le
    · set σ : ℝ := Real.sqrt (N : ℝ) with hσdef
      have hσ : 0 < σ := Real.sqrt_pos.2 (by exact_mod_cast hN)
      have hσsq : σ ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      -- Step 5, inclusion (i): `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(σ s)` for `s > 0`.
      have hincl1 : ∀ r s, 0 < s → X r s ⊆ ⋃ j, ball a r ∩ K j (σ * s) := by
        rintro r s hs x ⟨hxr, hx⟩
        set y := x - a with hydef
        have hy : 0 < ‖y‖ := by
          rcases (norm_nonneg y).lt_or_eq with h | h
          · exact h
          · exfalso
            rw [← h, mul_zero] at hx
            exact (norm_nonneg _).not_gt hx
        obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖y j‖)
          (Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩)
        have hsq : ‖y‖ ^ 2 ≤ (σ * ‖y j‖) ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2, mul_pow, hσsq]
          calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin N, ‖y j‖ ^ 2 :=
                Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hj i (Finset.mem_univ i)) 2
            _ = (N : ℝ) * ‖y j‖ ^ 2 := by simp
        have hle : ‖y‖ ≤ σ * ‖y j‖ :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
        have hyj : 0 < ‖y j‖ := by
          by_contra hcon
          have : ‖y j‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
          rw [this, mul_zero] at hle
          linarith
        have hyj0 : y j ≠ 0 := norm_pos_iff.1 hyj
        refine mem_iUnion.2 ⟨j, mem_ball.2 hxr, ?_, (-(y j)⁻¹) • L y, ?_, ?_⟩
        · intro h
          rw [hydef, h, sub_self, norm_zero] at hy
          exact lt_irrefl _ hy
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv]
          rw [inv_mul_lt_iff₀ hyj]
          calc ‖L y‖ < s * ‖y‖ := hx
            _ ≤ s * (σ * ‖y j‖) := by gcongr
            _ = ‖y j‖ * (σ * s) := by ring
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj0, neg_smul, one_smul, add_neg_cancel]
      -- Step 6, pointwise bound: `F(s) ≤ σᵏ Σ_j F_j(σ s)` for `s > 0`.
      have hpt : ∀ s, 0 < s → F s ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by
        intro s hs
        refine iSup₂_le fun r hr => ?_
        have hc0 : ENNReal.ofReal (σ ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
        have hA : ENNReal.ofReal ((r * (σ * s)) ^ (m + 1)) =
            ENNReal.ofReal (σ ^ (m + 1)) * ENNReal.ofReal ((r * s) ^ (m + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          congr 2
          ring
        calc μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
            ≤ (∑ j, μ (ball a r ∩ K j (σ * s))) / ENNReal.ofReal ((r * s) ^ (m + 1)) := by
              refine ENNReal.div_le_div_right ?_ _
              exact (measure_mono (hincl1 r s hs)).trans (measure_iUnion_fintype_le μ _)
          _ = ∑ j, ENNReal.ofReal (σ ^ (m + 1)) *
                (μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) := by
              rw [ENNReal.sum_div]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
          _ ≤ ∑ j, ENNReal.ofReal (σ ^ (m + 1)) * Fj j (σ * s) := by
              refine Finset.sum_le_sum fun j _ => ?_
              gcongr
              exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) r hr
          _ = ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by rw [Finset.mul_sum]
      -- Step 8: `limsup` is subadditive along `𝓝[>] 0` (direct `ε`-argument).
      have hadd : ∀ (v w : ℝ → ℝ≥0∞), limsup (fun s => v s + w s) (𝓝[>] (0 : ℝ)) ≤
          limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) := by
        intro v w
        refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
        have hv : limsup v (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_self_add hlt
        have hw : limsup w (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_add_self hlt
        have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by
          simp [ENNReal.div_eq_zero_iff, hε.ne']
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv.ne hε2),
          eventually_lt_of_limsup_lt (ENNReal.lt_add_right hw.ne hε2)] with x h1 h2
        calc v x + w x ≤ (limsup v (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) + (limsup w (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) :=
              add_le_add h1.le h2.le
          _ = limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) + ε := by
              rw [add_add_add_comm, ENNReal.add_halves]
      have hsum : ∀ (S : Finset (Fin N)) (h : Fin N → ℝ → ℝ≥0∞),
          limsup (fun s => ∑ j ∈ S, h j s) (𝓝[>] (0 : ℝ)) ≤ ∑ j ∈ S, limsup (h j) (𝓝[>] 0) := by
        intro S h
        induction S using Finset.induction_on with
        | empty => simp
        | insert j S hj ih =>
          simp only [Finset.sum_insert hj]
          exact (hadd (h j) (fun s => ∑ i ∈ S, h i s)).trans (add_le_add le_rfl ih)
      -- Step 9, change of variable `t = σ s`: `s ↦ σ s` maps `𝓝[>] 0` into `𝓝[>] 0`.
      have hT : Tendsto (fun s : ℝ => σ * s) (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => σ * s) (𝓝 0) (𝓝 (σ * 0)) :=
            ((continuous_const.mul continuous_id).tendsto 0)
          rw [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact mul_pos hσ hs
      have hcv : ∀ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ)) ≤ limsup (Fj j) (𝓝[>] 0) := by
        intro j
        calc limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ))
            = limsup (Fj j) (map (fun s : ℝ => σ * s) (𝓝[>] 0)) := Filter.limsup_comp (Fj j) _ _
          _ ≤ limsup (Fj j) (𝓝[>] 0) := limsup_le_limsup_of_le hT (by isBoundedDefault) (by isBoundedDefault)
      -- Steps 7 and 10: pull out the constant `σᵏ`, then apply steps 8 and 9.
      calc limsup F (𝓝[>] 0) ≤ limsup (fun s => ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s)) (𝓝[>] 0) := by
            refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
            filter_upwards [self_mem_nhdsWithin] with s hs
            exact hpt s hs
        _ = ENNReal.ofReal (σ ^ (m + 1)) * limsup (fun s => ∑ j, Fj j (σ * s)) (𝓝[>] 0) :=
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] 0) := by
            gcongr
            exact hsum Finset.univ (fun j s => Fj j (σ * s))
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (Fj j) (𝓝[>] 0) := by
            gcongr with j
            exact hcv j
/-- **Slice densities of the exceptional parameters** (Mattila, *Geometry of Sets and Measures in
Euclidean Spaces*, Lemma 18.9; for transversal families, Hovila–Järvenpää–Järvenpää–Ledrappier,
arXiv:1104.3453, Lemma 2.5).  Let `k = m + 1`, `L_u y = (⟨u_i, y⟩)_i`,
`w ⊕ c = (w_i + c_i e_j)_i`, `K_w(C) = {x ≠ a : L_{w ⊕ c}(x − a) = 0 for some c ∈ C}` and
`ϑ_j(u) = limsup_{t↓0} sup_{0<r<δ} μ(B(a,r) ∩ K_u(B(0,t)))/(rt)ᵏ`.  Then the set `𝔅_j` of `u`
with `0 < ϑ_j(u) < ∞` and no `x ∈ E` with `0 < |x − a| < δ` and `L_u x = L_u a` is Lebesgue-null.
For fixed `w`, `ψ_w(C) = sup_{0<r<δ} μ(B(a,r) ∩ K_w(C))/rᵏ` is an outer measure on `ℝᵏ`, inner
continuous on open balls, and vanishes on the Borel set `D_w` of those `c` for which `w ⊕ c` has
no such `x`, because `μ(ℝ^N ∖ E) = 0`.  As `K_w(B(c,t)) = K_{w ⊕ c}(B(0,t))`, the upper
`k`-density of `ψ_w` at `c` is `ϑ_j(w ⊕ c)`, so by the Mickle–Radó theorem
`Lᵏ{c : w ⊕ c ∈ 𝔅_j} = 0` for every `w`.  `𝔅_j` is Borel, and Tonelli for `(w, c) ↦ w ⊕ c` in both
orders, with translation invariance, gives `𝓛(𝔅_j) · ∞ = 0`. -/
theorem Submission.rectifiability_bf_slice_density_null : ∀ (N m : ℕ) (μ : Measure (Eucl N)) (E : Set (Eucl N)) (δ : ℝ) (a : Eucl N) (j : Fin N), SFinite μ → IsSigmaCompact E → μ Eᶜ = 0 → (volume : Measure (Fin (m + 1) → Eucl N)) {u : Fin (m + 1) → Eucl N | ¬ (∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) a) : Eucl (m + 1))) ∧ 0 < limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) < ⊤} = 0 := by
  intro N m μ E δ a j hμ hE hEc
  let Lu : (Fin (m + 1) → Eucl N) → Eucl N → Eucl (m + 1) := fun u y =>
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let T3 : (Fin (m + 1) → Eucl N) → Prop := fun u => ∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) x) : Eucl (m + 1)) =
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) a) : Eucl (m + 1))
  let Ks : (Fin (m + 1) → Eucl N) → ℝ → Set (Eucl N) := fun u t => {x | x ≠ a ∧
    ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) =>
      inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let θ : (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun u => limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ,
    μ (ball a r ∩ Ks u t) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0)
  let B : Set (Fin (m + 1) → Eucl N) := {u | ¬ T3 u ∧ 0 < θ u ∧ θ u < ⊤}
  show (volume : Measure (Fin (m + 1) → Eucl N)) B = 0
  -- step 1(a), 1(c): `L_{u ⊕ c} y = L_u y + y_j c` and `L_v (x - y) = L_v x - L_v y`
  have hfib : ∀ (u : Fin (m + 1) → Eucl N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) =>
        inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) : Eucl (m + 1)) =
          Lu u y + (y j) • c := by
    intro u c y
    ext i
    simp [Lu, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  have hLsub : ∀ (v : Fin (m + 1) → Eucl N) (x y : Eucl N), Lu v (x - y) = Lu v x - Lu v y := by
    intro v x y
    ext i
    simp [Lu, inner_sub_right]
  -- step 1(f): explicit form of `K_{j,u}(t)` for `t > 0`
  have hKs : ∀ u t, 0 < t → Ks u t = {x | ‖Lu u (x - a)‖ < t * ‖(x - a) j‖} ∪
      {x | x ≠ a ∧ (x - a) j = 0 ∧ Lu u (x - a) = 0} := by
    intro u t ht
    ext x
    simp only [Ks, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨hxa, c, hc, h0⟩
      rw [hfib] at h0
      by_cases hyj : (x - a) j = 0
      · right
        refine ⟨hxa, hyj, ?_⟩
        rw [hyj, zero_smul, add_zero] at h0
        exact h0
      · left
        have hL : Lu u (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left h0
        rw [hL, norm_neg, norm_smul]
        have hc' : ‖c‖ < t := mem_ball_zero_iff.1 hc
        have hpos : 0 < ‖(x - a) j‖ := norm_pos_iff.2 hyj
        calc ‖(x - a) j‖ * ‖c‖ < ‖(x - a) j‖ * t := mul_lt_mul_of_pos_left hc' hpos
          _ = t * ‖(x - a) j‖ := mul_comm _ _
    · rintro (h | ⟨hxa, hyj, h0⟩)
      · have hyj : (x - a) j ≠ 0 := by
          intro h'
          rw [h', norm_zero, mul_zero] at h
          exact (norm_nonneg _).not_gt h
        have hxa : x ≠ a := by
          intro h'
          apply hyj
          rw [h', sub_self]
          rfl
        refine ⟨hxa, (-((x - a) j)⁻¹) • Lu u (x - a), ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv,
            inv_mul_lt_iff₀ (norm_pos_iff.2 hyj)]
          linarith [h]
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj, neg_smul, one_smul, add_neg_cancel]
      · refine ⟨hxa, 0, mem_ball_self ht, ?_⟩
        rw [hfib, smul_zero, add_zero]
        exact h0
  -- step 8(a): `ϑ_j` is measurable (`limsup_sup_measurable`; `G` is Borel by step 1(f))
  let G : ℝ → ℝ → Set ((Fin (m + 1) → Eucl N) × Eucl N) := fun r t =>
    {q | q.2 ∈ ball a r ∩ Ks q.1 t}
  have hc1 : Continuous fun q : (Fin (m + 1) → Eucl N) × Eucl N => Lu q.1 (q.2 - a) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp continuous_fst).inner (continuous_snd.sub continuous_const)
  have hc2 : Continuous fun q : (Fin (m + 1) → Eucl N) × Eucl N => (q.2 - a) j :=
    (PiLp.continuous_apply 2 _ j).comp (continuous_snd.sub continuous_const)
  have hGm : ∀ r t, MeasurableSet (G r t) := by
    intro r t
    rcases le_or_gt t 0 with ht | ht
    · have : G r t = ∅ := by
        ext q
        simp only [G, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨-, -, c, hc, -⟩
        rw [ball_eq_empty.2 ht] at hc
        exact hc
      rw [this]
      exact MeasurableSet.empty
    · have : G r t = {q | dist q.2 a < r} ∩ ({q | ‖Lu q.1 (q.2 - a)‖ < t * ‖(q.2 - a) j‖} ∪
          ({q | q.2 ≠ a} ∩ {q | (q.2 - a) j = 0} ∩ {q | Lu q.1 (q.2 - a) = 0})) := by
        ext q
        simp only [G, mem_ofPred_eq, mem_inter_iff, mem_ball]
        rw [hKs q.1 t ht]
        simp only [mem_union, mem_ofPred_eq, mem_inter_iff, and_assoc]
      rw [this]
      refine (isOpen_lt (continuous_snd.dist continuous_const) continuous_const).measurableSet.inter
        (MeasurableSet.union ?_ ?_)
      · exact (isOpen_lt hc1.norm (continuous_const.mul hc2.norm)).measurableSet
      · exact ((isOpen_ne_fun continuous_snd continuous_const).measurableSet.inter
          (isClosed_eq hc2 continuous_const).measurableSet).inter
          (isClosed_eq hc1 continuous_const).measurableSet
  have hGmono : ∀ r t t', t ≤ t' → G r t ⊆ G r t' := by
    rintro r t t' htt' q ⟨hq1, hxa, c, hc, h0⟩
    exact ⟨hq1, hxa, c, ball_subset_ball htt' hc, h0⟩
  have hGcont : ∀ r t, 0 < r → G r t = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' t := by
    intro r t hr
    ext q
    simp only [G, mem_iUnion, mem_ofPred_eq, mem_inter_iff, mem_ball, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 a + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨-, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
  have hθm : Measurable θ :=
    Submission.rectifiability_bf_limsup_sup_measurable (Fin (m + 1) → Eucl N) (Eucl N) (m + 1)
      μ δ G hμ hGm hGmono hGcont
  -- step 8(b), 8(c): `𝔅_j` is measurable (`witness_set_measurable`)
  have hW := Submission.rectifiability_bf_witness_set_measurable N m E δ hE
  have hT3m : MeasurableSet {u : Fin (m + 1) → Eucl N | ¬ T3 u} :=
    (measurable_const.prodMk measurable_id) hW.compl
  have hBm : MeasurableSet B :=
    hT3m.inter ((measurableSet_lt measurable_const hθm).inter
      (measurableSet_lt hθm measurable_const))
  -- steps 2–7: `Lᵏ{c : w ⊕ c ∈ 𝔅_j} = 0` for every `w`
  let sh : Eucl (m + 1) → (Fin (m + 1) → Eucl N) := fun c i => c i • EuclideanSpace.single j (1 : ℝ)
  have hsh : Continuous sh :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).smul continuous_const
  have hslice : ∀ w : Fin (m + 1) → Eucl N,
      (volume : Measure (Eucl (m + 1))) {c | w + sh c ∈ B} = 0 := by
    intro w
    let KC : Set (Eucl (m + 1)) → Set (Eucl N) := fun C => {x | x ≠ a ∧ ∃ c ∈ C,
      (WithLp.toLp 2 (fun i : Fin (m + 1) =>
        inner ℝ (w i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
    -- step 1(d): `K_w` is monotone and commutes with countable unions
    have hKCmono : ∀ C₁ C₂, C₁ ⊆ C₂ → KC C₁ ⊆ KC C₂ := by
      rintro C₁ C₂ h x ⟨hxa, c, hc, h0⟩
      exact ⟨hxa, c, h hc, h0⟩
    have hKCunion : ∀ (s : ℕ → Set (Eucl (m + 1))), KC (⋃ i, s i) = ⋃ i, KC (s i) := by
      intro s
      ext x
      simp only [KC, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxa, c, ⟨i, hci⟩, h0⟩
        exact ⟨i, hxa, c, hci, h0⟩
      · rintro ⟨i, hxa, c, hci, h0⟩
        exact ⟨hxa, c, ⟨i, hci⟩, h0⟩
    -- step 2: the outer measure `ψ_w`
    let ψ : OuterMeasure (Eucl (m + 1)) :=
      { measureOf := fun C =>
          ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC C) / ENNReal.ofReal (r ^ (m + 1))
        empty := by
          have : KC ∅ = ∅ := by
            ext x
            simp [KC]
          simp [this]
        mono := fun {s₁ s₂} h => iSup₂_mono fun r _ =>
          ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _ (hKCmono _ _ h))) _
        iUnion_nat := fun s _ => by
          refine iSup₂_le fun r hr => ?_
          rw [hKCunion, inter_iUnion]
          calc μ (⋃ i, ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1))
              ≤ (∑' i, μ (ball a r ∩ KC (s i))) / ENNReal.ofReal (r ^ (m + 1)) :=
                ENNReal.div_le_div_right (measure_iUnion_le _) _
            _ = ∑' i, μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1)) := by
                simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
            _ ≤ ∑' i, ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1)) :=
                ENNReal.tsum_le_tsum fun i => le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                  μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1))) r hr }
    have hψ : ∀ C, ψ C = ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC C) / ENNReal.ofReal (r ^ (m + 1)) :=
      fun C => rfl
    -- step 3: inner continuity of `ψ_w` on open balls
    have hball : ∀ (c : Eucl (m + 1)) (τ : ℝ),
        ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ') := by
      intro c τ
      apply le_antisymm
      · rcases le_or_gt τ 0 with hτ | hτ
        · rw [ball_eq_empty.2 hτ, measure_empty]
          exact zero_le
        · rw [hψ]
          refine iSup₂_le fun r hr => ?_
          let τn : ℕ → ℝ := fun n => τ - τ / ((n : ℝ) + 2)
          have hτn_mono : Monotone τn := by
            intro n n' hnn'
            simp only [τn]
            have : τ / ((n' : ℝ) + 2) ≤ τ / ((n : ℝ) + 2) := by
              apply div_le_div_of_nonneg_left hτ.le (by positivity)
              have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
              linarith
            linarith
          have hτn_mem : ∀ n, τn n ∈ Ioo 0 τ := by
            intro n
            have h1 : τ / ((n : ℝ) + 2) < τ := by
              rw [div_lt_iff₀ (by positivity)]
              have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
              nlinarith
            have h2 : 0 < τ / ((n : ℝ) + 2) := by positivity
            exact ⟨by simp only [τn]; linarith, by simp only [τn]; linarith⟩
          have hballU : ball c τ = ⋃ n, ball c (τn n) := by
            ext c'
            simp only [mem_ball, mem_iUnion]
            constructor
            · intro hd
              obtain ⟨n, hn⟩ := exists_nat_gt (τ / (τ - dist c' c))
              refine ⟨n, ?_⟩
              simp only [τn]
              have hpos : 0 < τ - dist c' c := by linarith
              have : τ / ((n : ℝ) + 2) < τ - dist c' c := by
                rw [div_lt_iff₀ (by positivity)]
                rw [div_lt_iff₀ hpos] at hn
                nlinarith
              linarith
            · rintro ⟨n, hn⟩
              exact hn.trans (hτn_mem n).2
          have hmono_sets : Monotone (fun n => ball a r ∩ KC (ball c (τn n))) := by
            intro n n' hnn'
            exact inter_subset_inter_right _ (hKCmono _ _ (ball_subset_ball (hτn_mono hnn')))
          have hmeas : μ (ball a r ∩ KC (ball c τ)) = ⨆ n, μ (ball a r ∩ KC (ball c (τn n))) := by
            rw [hballU, hKCunion, inter_iUnion]
            exact hmono_sets.measure_iUnion
          rw [hmeas, ENNReal.iSup_div]
          refine iSup_le fun n => ?_
          refine le_trans ?_ (le_iSup₂ (f := fun τ' (_ : τ' ∈ Ioo (0 : ℝ) τ) => ψ (ball c τ'))
            (τn n) (hτn_mem n))
          rw [hψ]
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            μ (ball a r ∩ KC (ball c (τn n))) / ENNReal.ofReal (r ^ (m + 1))) r hr
      · exact iSup₂_le fun τ' hτ' => ψ.mono (ball_subset_ball hτ'.2.le)
    -- steps 4–6: `D_w` is Borel and `ψ_w`-null, so Mickle–Radó applies
    let D : Set (Eucl (m + 1)) := {c | ¬ T3 (w + sh c)}
    have hDm : MeasurableSet D :=
      (measurable_const.prodMk (continuous_const.add hsh).measurable) hW.compl
    have hψD : ψ D = 0 := by
      rw [hψ]
      refine le_antisymm (iSup₂_le fun r hr => ?_) zero_le
      have : μ (ball a r ∩ KC D) = 0 := by
        refine measure_mono_null (fun x hx => ?_) hEc
        obtain ⟨hxr, hxa, c, hcD, hx0⟩ := hx
        intro hxE
        apply hcD
        refine ⟨x, hxE, hxa, (mem_ball.1 hxr).trans hr.2, ?_⟩
        have h0 : Lu (w + sh c) (x - a) = 0 := hx0
        rw [hLsub] at h0
        exact sub_eq_zero.1 h0
      rw [this, ENNReal.zero_div]
    have hMR := Submission.rectifiability_mickle_rado m ψ D hball hDm hψD
    -- step 7: `K_w(B(c,t)) = K_{w ⊕ c}(B(0,t))`, so the slice density at `c` is `ϑ_j(w ⊕ c)`
    have hKCtr : ∀ (c : Eucl (m + 1)) (t : ℝ), KC (ball c t) = Ks (w + sh c) t := by
      intro c t
      ext x
      simp only [KC, Ks, mem_ofPred_eq]
      constructor
      · rintro ⟨hxa, c', hc', h0⟩
        refine ⟨hxa, c' - c, ?_, ?_⟩
        · rw [mem_ball_zero_iff, ← mem_ball_iff_norm]
          exact hc'
        · have hv : ∀ i, (w + sh c) i + (c' - c) i • EuclideanSpace.single j (1 : ℝ) =
              w i + c' i • EuclideanSpace.single j (1 : ℝ) := by
            intro i
            simp only [sh, Pi.add_apply, PiLp.sub_apply, sub_smul]
            abel
          simp only [hv]
          exact h0
      · rintro ⟨hxa, c'', hc'', h0⟩
        refine ⟨hxa, c + c'', ?_, ?_⟩
        · rw [mem_ball_iff_norm, add_sub_cancel_left, ← mem_ball_zero_iff]
          exact hc''
        · have hv : ∀ i, w i + (c + c'') i • EuclideanSpace.single j (1 : ℝ) =
              (w + sh c) i + c'' i • EuclideanSpace.single j (1 : ℝ) := by
            intro i
            simp only [sh, Pi.add_apply, PiLp.add_apply, add_smul]
            abel
          simp only [hv]
          exact h0
    have hid : ∀ c : Eucl (m + 1),
        limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) =
          θ (w + sh c) := by
      intro c
      apply limsup_congr
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [hψ, ENNReal.iSup_div]
      refine iSup_congr fun r => ?_
      rw [ENNReal.iSup_div]
      refine iSup_congr fun hr => ?_
      rw [hKCtr c t]
      have hr0 : 0 < r := hr.1
      have hA0 : ENNReal.ofReal (r ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
        ← ENNReal.mul_inv (Or.inl hA0) (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    refine le_antisymm (le_trans (measure_mono ?_) hMR.le) zero_le
    intro c hc
    refine ⟨hc.1, ?_, ?_⟩
    · rw [hid c]; exact hc.2.1
    · rw [hid c]; exact hc.2.2
  -- step 9: Tonelli for `(w, c) ↦ w ⊕ c` in both orders
  have hP : MeasurableSet ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) :=
    (continuous_fst.add (hsh.comp continuous_snd)).measurable hBm
  have h1 : ((volume : Measure (Fin (m + 1) → Eucl N)).prod (volume : Measure (Eucl (m + 1))))
      ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) = 0 := by
    rw [Measure.prod_apply hP]
    have : ∀ w : Fin (m + 1) → Eucl N, (volume : Measure (Eucl (m + 1)))
        (Prod.mk w ⁻¹'
          ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B)) = 0 :=
      fun w => hslice w
    simp [this]
  have h2 : ((volume : Measure (Fin (m + 1) → Eucl N)).prod (volume : Measure (Eucl (m + 1))))
      ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) =
        (volume : Measure (Fin (m + 1) → Eucl N)) B * ⊤ := by
    rw [Measure.prod_apply_symm hP]
    have : ∀ c : Eucl (m + 1), (volume : Measure (Fin (m + 1) → Eucl N))
        ((fun w => (w, c)) ⁻¹'
          ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B)) =
            (volume : Measure (Fin (m + 1) → Eucl N)) B :=
      fun c => measure_preimage_add_right (volume : Measure (Fin (m + 1) → Eucl N)) (sh c) B
    simp only [this]
    rw [lintegral_const, measure_univ_of_isAddLeftInvariant]
  rw [h1] at h2
  rcases mul_eq_zero.1 h2.symm with h | h
  · exact h
  · exact absurd h ENNReal.top_ne_zero

/-- **Besicovitch–Federer trichotomy for almost every linear map** (Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, Lemma 18.9; Hovila–Järvenpää–Järvenpää–Ledrappier, Geom. Dedicata
161 (2012), Lemma 2.4).  Let `k = m + 1`, `μ = Hᵏ⌞E`, `L_v x = (⟨v_i, x⟩)_i`,
`X_v(a,r,s) = {x : |x − a| < r, |L_v(x − a)| < s|x − a|}` and
`Φ(a,v) = limsup_{s↓0} sup_{0<r<δ} μ(X_v(a,r,s))/(rs)ᵏ`.  Fix `a`.  By Mickle–Radó on the slices
`v ⊕_j c`, for a.e. `v` without a fibre witness (T3) every fibre density `ϑ_j(v)` lies in `{0, ∞}`,
and `ϑ_j ≤ Φ ≤ N^{k/2} Σ_j ϑ_j` puts `Φ(a,v)` in `{0, ∞}`.  The set of such `(a,v)` is Borel, so
Fubini gives the same for a.e. `v` and `μ`-a.e. `a`; `Φ = 0` is (T1) and `Φ = ∞` gives the
infinite projected density (T2). -/
theorem Submission.rectifiability_bf_trichotomy : ∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → 0 < δ → ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)), ∀ᵐ a ∂((μHE[m + 1] : Measure (Eucl N)).restrict E), (∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∨ dimensionalUpperDensity (Measure.map (fun x : Eucl N => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) ((μHE[m + 1] : Measure (Eucl N)).restrict E)).toOuterMeasure ((m + 1 : ℕ) : ℝ) univ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤ ∨ ∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) := by
  intro N m E δ hE hEfin _
  -- step 1: `E` is Borel and `μ = Hᵏ⌞E` is a finite measure carried by `E`
  have hEmeas : MeasurableSet E := by
    obtain ⟨K, hK, hKE⟩ := hE
    rw [← hKE]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have : IsFiniteMeasure ((μHE[m + 1] : Measure (Eucl N)).restrict E) :=
    isFiniteMeasure_restrict.2 hEfin.ne
  have hμE : ((μHE[m + 1] : Measure (Eucl N)).restrict E) Eᶜ = 0 := by
    rw [Measure.restrict_apply' hEmeas, compl_inter_self, measure_empty]
  have hμS : ∀ S : Set (Eucl N),
      (μHE[m + 1] : Measure (Eucl N)) (E ∩ S) = ((μHE[m + 1] : Measure (Eucl N)).restrict E) S := by
    intro S
    rw [Measure.restrict_apply' hEmeas, inter_comm]
  set μ : Measure (Eucl N) := (μHE[m + 1] : Measure (Eucl N)).restrict E
  -- step 2: the cone ratio `Φ(a,v)` and the fibre-witness set `W` of (T3) are Borel in `(a,v)`
  set Φ : Eucl N × (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun p => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)
  set W : Set (Eucl N × (Fin (m + 1) → Eucl N)) := {p | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))}
  have hΦ : Measurable Φ := Submission.rectifiability_bf_cone_ratio_measurable N m μ δ inferInstance
  have hW : MeasurableSet W := Submission.rectifiability_bf_witness_set_measurable N m E δ hE
  have hG : MeasurableSet
      {p : Eucl N × (Fin (m + 1) → Eucl N) | (Φ (p.1, p.2) = 0 ∨ Φ (p.1, p.2) = ⊤) ∨ (p.1, p.2) ∈ W} :=
    ((hΦ (measurableSet_singleton 0)).union (hΦ (measurableSet_singleton ⊤))).union hW
  -- step 3: for every `a`, `Φ(a,v) ∈ {0, ∞}` or (T3) holds for a.e. `v`
  have hslice : ∀ a : Eucl N, ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)),
      (Φ (a, v) = 0 ∨ Φ (a, v) = ⊤) ∨ (a, v) ∈ W := by
    intro a
    set ϑ : Fin N → (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun j u => limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0)
    -- Mickle–Radó on the slices: `0 < ϑ_j(v) < ∞` without (T3) only for a null set of `v`
    have hnull : ∀ j : Fin N, ∀ᵐ u ∂(volume : Measure (Fin (m + 1) → Eucl N)),
        ¬ ((a, u) ∉ W ∧ 0 < ϑ j u ∧ ϑ j u < ⊤) := by
      intro j
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (Submission.rectifiability_bf_slice_density_null N m μ E δ a j inferInstance hE hμE)]
        with u hu
      exact hu
    filter_upwards [ae_all_iff.2 hnull] with u hu
    by_cases hT3 : (a, u) ∈ W
    · exact Or.inr hT3
    refine Or.inl ?_
    -- cones versus unions of fibres: `ϑ_j ≤ Φ ≤ N^{k/2} Σ_j ϑ_j`
    obtain ⟨hle, hge⟩ := Submission.rectifiability_bf_fibre_cone_comparison N m μ δ a u
    have hle' : ∀ j, ϑ j u ≤ Φ (a, u) := hle
    have hge' : Φ (a, u) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, ϑ j u :=
      hge
    have h0top : ∀ j, ϑ j u = 0 ∨ ϑ j u = ⊤ := by
      intro j
      by_contra hcon
      exact hu j ⟨hT3, pos_iff_ne_zero.2 (not_or.1 hcon).1, lt_top_iff_ne_top.2 (not_or.1 hcon).2⟩
    by_cases htop : ∃ j, ϑ j u = ⊤
    · obtain ⟨j, hj⟩ := htop
      have h := hle' j
      rw [hj, top_le_iff] at h
      exact Or.inr h
    · refine Or.inl (nonpos_iff_eq_zero.1 (hge'.trans_eq ?_))
      rw [Finset.sum_eq_zero fun j _ => (h0top j).resolve_right (not_exists.1 htop j), mul_zero]
  -- step 4: Fubini turns `∀ a, ∀ᵐ v` into `∀ᵐ v, ∀ᵐ a ∂μ`
  have hswap : ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)), ∀ᵐ a ∂μ,
      (Φ (a, v) = 0 ∨ Φ (a, v) = ⊤) ∨ (a, v) ∈ W :=
    (Measure.ae_ae_comm (μ := μ) (ν := (volume : Measure (Fin (m + 1) → Eucl N)))
      (p := fun a v => (Φ (a, v) = 0 ∨ Φ (a, v) = ⊤) ∨ (a, v) ∈ W) hG).1
      (Eventually.of_forall hslice)
  -- step 5: `Φ = 0` gives (T1) and `Φ = ∞` gives (T2)
  filter_upwards [hswap] with v hv
  filter_upwards [hv] with a ha
  rcases ha with (h0 | htop) | hT3
  · refine Or.inl fun η hη => ?_
    obtain ⟨s, hs, hsr⟩ :=
      (Submission.rectifiability_bf_cone_ratio_reduction N m μ δ a v).1 h0 η hη
    exact ⟨s, hs, fun r hr => (hμS _).trans_le (hsr r hr)⟩
  · exact Or.inr (Or.inl ((Submission.rectifiability_bf_cone_ratio_reduction N m μ δ a v).2 htop))
  · exact Or.inr (Or.inr hT3)

/-- Simon Ch. 6, proof of 8.1, (1) and (6): a set `S` of positive upper density `Θ*ⁿ(ν, ·)`,
covered by open sets `W q` of finite `ν`-measure, is covered by countably many sets of finite
`Hⁿ`-measure, and it is `Hⁿ`-null when it is `ν`-null.  The pieces
`{x ∈ S ∩ W q : (j + 1)⁻¹ ≤ Θ*ⁿ(ν, x)}` are controlled by the density comparison with
`V = W q`, and, when `ν(S) = 0`, with `V = O ∩ W q` for an open `O ⊇ S` given by outer
regularity of the finite measure `ν ⌞ W q`. -/
theorem Submission.rectifiability_positive_density_cover_null : ∀ (P n : ℕ) (ν : Measure (Eucl P)) (W : ℕ → Set (Eucl P)) (S : Set (Eucl P)), (∀ q, IsOpen (W q)) → (∀ q, ν (W q) < ∞) → S ⊆ ⋃ q, W q → (∀ x ∈ S, 0 < dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x) → (∃ C : ℕ → Set (Eucl P), S ⊆ ⋃ i, C i ∧ ∀ i, (μHE[n] : Measure (Eucl P)) (C i) < ∞) ∧ (ν S = 0 → (μHE[n] : Measure (Eucl P)) S = 0) := by
  intro P n ν W S hWo hWfin hSW hpos
  -- The pieces `A j q = {x ∈ S ∩ W q : (j + 1)⁻¹ ≤ Θ*ⁿ(ν, x)}` cover `S`.
  obtain ⟨A, hAS, hAW, hAD, hcover⟩ : ∃ A : ℕ → ℕ → Set (Eucl P), (∀ j q, A j q ⊆ S) ∧
      (∀ j q, A j q ⊆ W q) ∧ (∀ j q, ∀ x ∈ A j q,
        ((j : ℝ≥0∞) + 1)⁻¹ ≤ dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x) ∧
      S ⊆ ⋃ j, ⋃ q, A j q := by
    refine ⟨fun j q => {x | x ∈ S ∧ x ∈ W q ∧
      ((j : ℝ≥0∞) + 1)⁻¹ ≤ dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x},
      fun j q x hx => hx.1, fun j q x hx => hx.2.1, fun j q x hx => hx.2.2, ?_⟩
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.1 (hSW hx)
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (hpos x hx).ne'
    refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨q, hx, hq, ?_⟩⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ ≤ _ := hk.le
  have ht0 : ∀ j : ℕ, ((j : ℝ≥0∞) + 1)⁻¹ ≠ 0 := fun j =>
    ENNReal.inv_ne_zero.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top j, ENNReal.one_ne_top⟩)
  refine ⟨⟨fun i => A (Nat.unpair i).1 (Nat.unpair i).2, ?_, ?_⟩, ?_⟩
  · -- Reindex the pieces by `Nat.pair`.
    intro x hx
    obtain ⟨j, q, hjq⟩ : ∃ j q, x ∈ A j q := by simpa only [mem_iUnion] using hcover hx
    refine mem_iUnion.2 ⟨Nat.pair j q, ?_⟩
    simpa only [Nat.unpair_pair] using hjq
  · -- Density comparison with `V = W q`: `(j + 1)⁻¹ Hⁿ(A j q) ≤ ν(W q) < ∞`.
    intro i
    have h := Submission.rectifiability_density_comparison P n ν
      (A (Nat.unpair i).1 (Nat.unpair i).2) (W (Nat.unpair i).2) _ (hWo _) (hAW _ _) (hAD _ _)
    rcases ENNReal.mul_lt_top_iff.1 (h.trans_lt (hWfin _)) with h1 | h1 | h1
    · exact h1.2
    · exact absurd h1 (ht0 _)
    · simp [h1]
  · -- If `ν(S) = 0`, every piece is `Hⁿ`-null.
    intro hS0
    have hpiece : ∀ j q, (μHE[n] : Measure (Eucl P)) (A j q) = 0 := by
      intro j q
      by_contra hne
      have hc : 0 < ((j : ℝ≥0∞) + 1)⁻¹ * (μHE[n] : Measure (Eucl P)) (A j q) :=
        ENNReal.mul_pos (ht0 j) hne
      -- Outer regularity of the finite measure `ν ⌞ W q` gives an open `O ⊇ S` with
      -- `ν(O ∩ W q) < (j + 1)⁻¹ Hⁿ(A j q)`.
      have : IsFiniteMeasure (ν.restrict (W q)) := isFiniteMeasure_restrict.2 (hWfin q).ne
      obtain ⟨O, hSO, hOo, hOlt⟩ := Set.exists_isOpen_lt_of_lt (μ := ν.restrict (W q)) S _
        (((Measure.restrict_apply_le _ _).trans hS0.le).trans_lt hc)
      rw [Measure.restrict_apply hOo.measurableSet] at hOlt
      exact (Submission.rectifiability_density_comparison P n ν (A j q) (O ∩ W q) _
        (hOo.inter (hWo q)) (fun x hx => ⟨hSO (hAS j q hx), hAW j q hx⟩) (hAD j q)).not_gt hOlt
    exact measure_mono_null hcover
      (measure_iUnion_null fun j => measure_iUnion_null fun q => hpiece j q)
/-- Simon Ch. 6, proof of 8.1, (8) (p. 174): σ-finite Radon–Nikodym with a positive real density.
If `ν⌞B` and `μ` are σ-finite, `μ(X ∖ B) = 0` and `μ ≪ ν`, then `μ = (ν⌞M).withDensity θ` with
`M = B ∩ {0 < dμ/d(ν⌞B) < ∞}` and `θ = (dμ/d(ν⌞B)).toReal`; `θ` is `ν`-integrable on `M ∩ K`
whenever `μ K < ∞`, since `∫_{M ∩ K} θ dν = μ K`. -/
theorem Submission.rectifiability_rn_positive_real_density : ∀ (X : Type) [MeasurableSpace X] (ν μ : Measure X) (B : Set X), MeasurableSet B → SigmaFinite (ν.restrict B) → SigmaFinite μ → μ Bᶜ = 0 → μ ≪ ν → ∃ (M : Set X) (θ : X → ℝ), M ⊆ B ∧ MeasurableSet M ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ K : Set X, MeasurableSet K → μ K < ∞ → IntegrableOn θ (M ∩ K) ν) ∧ μ = (ν.restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) := by
  intro X _ ν μ B hB _ _ hμB hμν
  -- Step 1: `μ ≪ ν⌞B`, since `μ ≪ ν` and `μ(X ∖ B) = 0`.
  have hac : μ ≪ ν.restrict B := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
    rw [Measure.restrict_apply hs] at hs0
    exact measure_mono_null (inter_union_sdiff s B).symm.subset
      (measure_union_null (hμν hs0) (measure_mono_null (fun x hx => hx.2) hμB))
  -- Step 2: Radon–Nikodym for the σ-finite pair `(μ, ν⌞B)`: `μ = (ν⌞B).withDensity h` with
  -- `h = dμ/d(ν⌞B)` measurable and `(ν⌞B)`-a.e. finite.
  obtain ⟨h, hh, hrep, hfin⟩ : ∃ h : X → ℝ≥0∞, Measurable h ∧
      μ = (ν.restrict B).withDensity h ∧ ∀ᵐ x ∂(ν.restrict B), h x < ∞ := by
    refine ⟨μ.rnDeriv (ν.restrict B), Measure.measurable_rnDeriv _ _, ?_,
      Measure.rnDeriv_lt_top _ _⟩
    conv_lhs => rw [Measure.haveLebesgueDecomposition_add μ (ν.restrict B)]
    rw [Measure.singularPart_eq_zero_of_ac hac, zero_add]
  -- Step 3: `θ = h.toReal` and `M = B ∩ {0 < θ} = B ∩ {0 < h < ∞}`.
  have hθ : Measurable fun x => (h x).toReal := hh.ennreal_toReal
  have hM : MeasurableSet (B ∩ {x | 0 < (h x).toReal}) :=
    hB.inter (measurableSet_lt measurable_const hθ)
  -- Steps 4–5: `h = 1_M · ofReal θ` `(ν⌞B)`-a.e., hence `μ = (ν⌞M).withDensity (ofReal ∘ θ)`.
  have hrepM : μ = (ν.restrict (B ∩ {x | 0 < (h x).toReal})).withDensity
      (fun x => ENNReal.ofReal (h x).toReal) := by
    have hae : h =ᵐ[ν.restrict B] (B ∩ {x | 0 < (h x).toReal}).indicator
        (fun x => ENNReal.ofReal (h x).toReal) := by
      filter_upwards [hfin, ae_restrict_mem hB] with x hxfin hxB
      by_cases hx : 0 < (h x).toReal
      · rw [indicator_of_mem (show x ∈ B ∩ {x | 0 < (h x).toReal} from ⟨hxB, hx⟩),
          ENNReal.ofReal_toReal hxfin.ne]
      · rw [indicator_of_notMem fun hxM => hx hxM.2]
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          (le_antisymm (not_lt.mp hx) ENNReal.toReal_nonneg)).resolve_right hxfin.ne
    rw [hrep, withDensity_congr_ae hae, withDensity_indicator hM, Measure.restrict_restrict hM,
      inter_eq_left.mpr inter_subset_left]
  -- Step 6: for measurable `K` with `μ K < ∞`, `∫_{M ∩ K} |θ| dν = μ K < ∞`.
  refine ⟨B ∩ {x | 0 < (h x).toReal}, fun x => (h x).toReal, inter_subset_left, hM, hθ,
    fun x hx => hx.2, fun K hK hμK => ⟨hθ.aestronglyMeasurable, ?_⟩, hrepM⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => ENNReal.toReal_nonneg)]
  rw [hrepM, withDensity_apply _ hK, Measure.restrict_restrict hK, inter_comm K] at hμK
  exact hμK
open scoped CompactlySupported in
/-- **Besicovitch–Federer projection theorem, finite-measure case** (Mattila, *Geometry of Sets
and Measures in Euclidean Spaces*, Theorem 18.1; Hovila–Järvenpää–Järvenpää–Ledrappier,
arXiv:1104.3453, Theorem 1.2).  Let `k = m + 1` and `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩) ∈ ℝᵏ`.  If
`E ⊆ ℝ^N` is Borel and purely `k`-unrectifiable with `Hᵏ(E) < ∞`, then `Lᵏ(L_v(E)) = 0` for
Lebesgue-a.e. `v ∈ (ℝ^N)ᵏ`.  After passing to a σ-compact core of `E`, the trichotomy splits `E`,
up to an `Hᵏ`-null set, into the cone-density sets (`Hᵏ`-null), the points over which
`(L_v)_# (Hᵏ ⌞ E)` has infinite density (Lebesgue-null image by density comparison) and the
points with infinite `L_v`-fibres (Lebesgue-null image by Eilenberg finiteness). -/
theorem Submission.rectifiability_bf_projection_null_ae : ∀ (N m : ℕ) (E : Set (Eucl N)), MeasurableSet E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)), (volume : Measure (Eucl (m + 1))) ((fun x : Eucl N => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) '' E) = 0 := by
  intro N m E hE hEfin hPU
  -- Step 1: a σ-compact Borel core `E' ⊆ E` with `Hᵏ(E \ E') = 0` (`k = m + 1`).
  have : IsFiniteMeasure ((μHE[m + 1] : Measure (Eucl N)).restrict E) :=
    isFiniteMeasure_restrict.2 hEfin.ne
  obtain ⟨C, hCc, hCE, hCnull⟩ := Submission.lpf_lli_inner_compact_approx N
    (μHE[m + 1] : Measure (Eucl N)) E hE.nullMeasurableSet inferInstance
  set E' := ⋃ k, C k
  have hE'E : E' ⊆ E := iUnion_subset hCE
  have hE'm : MeasurableSet E' := MeasurableSet.iUnion fun k => (hCc k).measurableSet
  have hE'fin : (μHE[m + 1] : Measure (Eucl N)) E' < ∞ := (measure_mono hE'E).trans_lt hEfin
  -- Step 2: the trichotomy at every scale `δ_l = 1/(l+1)`, for a.e. `v` simultaneously.
  have htri := fun l : ℕ => Submission.rectifiability_bf_trichotomy N m E' (1 / ((l : ℝ) + 1))
    (isSigmaCompact_iUnion_of_isCompact C hCc) hE'fin (by positivity)
  filter_upwards [ae_all_iff.2 htri] with v hv
  -- Fix `v` and write `L x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)`; `L` is linear, hence Lipschitz.
  set L : Eucl N → Eucl (m + 1) :=
    fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) with hL
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, LipschitzWith K L := by
    let ℓ : Eucl N →ₗ[ℝ] Eucl (m + 1) :=
      { toFun := L
        map_add' := fun x y => by ext i; simp [hL, inner_add_right]
        map_smul' := fun c x => by ext i; simp [hL, inner_smul_right] }
    exact ⟨_, (LinearMap.toContinuousLinearMap ℓ).lipschitzWith⟩
  -- `L` maps `Hᵏ`-null sets to Lebesgue-null sets, as `μHE[k] = volume` on `ℝᵏ`.
  have himage : ∀ S : Set (Eucl N), (μHE[m + 1] : Measure (Eucl N)) S = 0 →
      (volume : Measure (Eucl (m + 1))) (L '' S) = 0 := by
    intro S hS
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (m + 1) (hK.lipschitzOnWith (s := S))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hS, mul_zero] at h
    exact nonpos_iff_eq_zero.1 h
  -- The image of `E \ E'` is null, so it suffices to treat `E'`.
  rw [← union_sdiff_cancel hE'E, image_union]
  refine measure_union_null ?_ (himage _ hCnull)
  -- A full-measure set `G` of points of `E'` at which the trichotomy holds at every scale.
  obtain ⟨G, hG, hGP⟩ :=
    eventually_iff_exists_mem.1 ((ae_restrict_iff' hE'm).1 (ae_all_iff.2 hv))
  -- (T1) The cone-density sets `E₁ l` are `Hᵏ`-null (`bf_cone_density` with `δ = 1/(l+1)`).
  set E₁ : ℕ → Set (Eucl N) := fun l => {a | a ∈ E' ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1,
    ∀ r ∈ Ioo (0 : ℝ) (1 / ((l : ℝ) + 1)), (μHE[m + 1] : Measure (Eucl N))
      (E' ∩ {x | dist x a < r ∧ ‖L (x - a)‖ < s * ‖x - a‖}) ≤
        ENNReal.ofReal (η * (r * s) ^ (m + 1))}
  have hE₁null : ∀ l, (μHE[m + 1] : Measure (Eucl N)) (E₁ l) = 0 := fun l =>
    Submission.rectifiability_bf_cone_density N m E' v (1 / ((l : ℝ) + 1)) (hPU.mono hE'E)
      (by positivity)
  -- (T2) The set `Y₂` where `ν = L_# (Hᵏ ⌞ E')` has infinite upper density is null: density
  -- comparison with `t = ∞` and `V = ℝᵏ` gives `∞ · Lᵏ(Y₂) ≤ ν(ℝᵏ) = Hᵏ(E') < ∞`.
  set Y₂ : Set (Eucl (m + 1)) := {y | dimensionalUpperDensity
    (Measure.map L ((μHE[m + 1] : Measure (Eucl N)).restrict E')).toOuterMeasure
      ((m + 1 : ℕ) : ℝ) univ y = ⊤}
  have hY₂null : (volume : Measure (Eucl (m + 1))) Y₂ = 0 := by
    have h := Submission.rectifiability_density_comparison (m + 1) (m + 1)
      (Measure.map L ((μHE[m + 1] : Measure (Eucl N)).restrict E')) Y₂ univ ⊤ isOpen_univ
      (subset_univ _) fun y hy => ge_of_eq hy
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.map_apply hK.continuous.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ] at h
    by_contra hne
    rw [ENNReal.top_mul hne] at h
    exact lt_irrefl _ (h.trans_lt hE'fin)
  -- (T3) The set `Y₃` of points with infinite `L`-fibre in `E'` is null (Eilenberg finiteness),
  -- and a point with fibre partners at every scale `δ_l` has an infinite fibre.
  set Y₃ : Set (Eucl (m + 1)) := {y | (E' ∩ L ⁻¹' {y}).Infinite}
  have hY₃null : (volume : Measure (Eucl (m + 1))) Y₃ = 0 :=
    Submission.rectifiability_bf_infinite_fibre_null N m E' L K hE'm hE'fin hK
  have hinf : ∀ a ∈ E', (∀ l : ℕ, ∃ x ∈ E', x ≠ a ∧ dist x a < 1 / ((l : ℝ) + 1) ∧
      L x = L a) → L a ∈ Y₃ := by
    intro a ha h3 hfin
    have hcl : IsClosed ((E' ∩ L ⁻¹' {L a}) \ {a}) := hfin.sdiff.isClosed
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl a fun h => h.2 rfl
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hε
    obtain ⟨x, hxE, hxa, hdist, hLx⟩ := h3 l
    exact hball (mem_ball.2 (hdist.trans hl)) ⟨⟨hxE, hLx⟩, hxa⟩
  -- Step 3: `L(E') ⊆ L(Gᶜ) ∪ ⋃ₗ L(E₁ l) ∪ Y₂ ∪ Y₃`, and every piece is Lebesgue-null.
  refine measure_mono_null (t := ((L '' Gᶜ ∪ ⋃ l, L '' E₁ l) ∪ Y₂) ∪ Y₃) ?_
    (measure_union_null (measure_union_null (measure_union_null (himage _ (mem_ae_iff.1 hG))
      (measure_iUnion_null fun l => himage _ (hE₁null l))) hY₂null) hY₃null)
  rintro _ ⟨a, ha, rfl⟩
  by_cases haG : a ∈ G
  swap
  · exact Or.inl (Or.inl (Or.inl ⟨a, haG, rfl⟩))
  by_cases h2 : L a ∈ Y₂
  · exact Or.inl (Or.inr h2)
  by_cases h3 : L a ∈ Y₃
  · exact Or.inr h3
  -- Otherwise (T3) fails at some scale `δ_l`, where (T1) must then hold.
  obtain ⟨l, hl⟩ : ∃ l, a ∈ E₁ l := by
    by_contra hno
    refine h3 (hinf a ha fun l => ?_)
    rcases hGP a haG ha l with h1 | h2' | h3'
    · exact (hno ⟨l, ha, h1⟩).elim
    · exact (h2 h2').elim
    · exact h3'
  exact Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨l, a, hl, rfl⟩)))

/-- **Simon Ch. 3, Structure Theorem 3.6, as used in Ch. 6, 8.1 (p. 174).**  If `A ⊆ ℝ^P` is
purely `n`-unrectifiable and `Hⁿ`-σ-finite (`n = m + 1`), then some rotation `Q` makes every
coordinate projection `p_α(Q(A))`, `α ∈ I(n, P)`, Lebesgue-null.  Up to an `Hⁿ`-null set, `A`
is a countable union of compact purely unrectifiable pieces of finite measure, and their images
under `x ↦ (⟪vᵢ, x⟫)ᵢ` are null for almost every frame `v`
(`rectifiability_bf_projection_null_ae`).  Gram–Schmidt applied to a random frame, together with
Tonelli's theorem, gives an orthonormal frame all of whose coordinate subframes avoid the null
set of bad frames. -/
theorem Submission.rectifiability_structure_projection : ∀ (P m : ℕ) (A : Set (Eucl P)), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) A → (∃ S : ℕ → Set (Eucl P), A ⊆ ⋃ j, S j ∧ ∀ j, (μHE[m + 1] : Measure (Eucl P)) (S j) < ∞) → ∃ Q : Eucl P ≃ₗᵢ[ℝ] Eucl P, ∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' A) = 0 := by
  have bf := Submission.rectifiability_bf_projection_null_ae
  classical
  intro P m A hA hS
  -- Step 1: if `P < m + 1` there is no strictly increasing `α`.
  by_cases hnP : m + 1 ≤ P
  swap
  · refine ⟨LinearIsometryEquiv.refl ℝ _, fun α => absurd ?_ hnP⟩
    simpa using Fintype.card_le_of_injective α α.injective
  -- Steps 4-6 (frame avoidance): for every null Borel set `Z` of `(m + 1)`-frames whose complement
  -- is stable under row recombination, some orthonormal basis has all coordinate subframes outside `Z`.
  have hFA : ∀ Z : Set (Fin (m + 1) → Eucl P), MeasurableSet Z →
      (volume : Measure (Fin (m + 1) → Eucl P)) Z = 0 →
      (∀ (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (w : Fin (m + 1) → Eucl P),
        (fun i => ∑ l, G i l • w l) ∈ Z → w ∈ Z) →
      ∃ Q : Eucl P ≃ₗᵢ[ℝ] Eucl P, ∀ α : SimonMultiIndex (m + 1) P,
        (fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ))) ∉ Z := by
    intro Z hZm hZ0 hZpre
    -- an orthonormal frame `c` gives the isometry `x ↦ ∑ xₖ cₖ`
    have hUc : ∀ c : Fin P → Eucl P, Orthonormal ℝ c →
        ∃ U : Eucl P ≃ₗᵢ[ℝ] Eucl P, ∀ x : Eucl P, U x = ∑ k, x k • c k := by
      intro c hc
      have hsp : ⊤ ≤ Submodule.span ℝ (Set.range c) :=
        (hc.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
      refine ⟨(OrthonormalBasis.mk hc hsp).repr.symm, fun x => ?_⟩
      rw [← (OrthonormalBasis.mk hc hsp).sum_repr_symm]
      simp
    -- the transpose of an orthonormal frame is orthonormal
    have hTON : ∀ b : Fin P → Eucl P, Orthonormal ℝ b →
        Orthonormal ℝ (fun k : Fin P => (WithLp.toLp 2 (fun i : Fin P => b i k) : Eucl P)) := by
      intro b hb
      have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) :=
        (hb.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
      rw [orthonormal_iff_ite]
      intro k l
      have h := (OrthonormalBasis.mk hb hsp).sum_inner_mul_inner
        (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))
      simp only [OrthonormalBasis.coe_mk, EuclideanSpace.inner_single_left,
        EuclideanSpace.inner_single_right, PiLp.single_apply] at h
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial] at h ⊢
      convert h using 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_comm]
      · by_cases hkl : k = l <;> simp [hkl, eq_comm]
    -- Tonelli: for an isometry-invariant finite measure on independent frames and an equivariant
    -- orthonormalization, the orthonormalized frame and its transpose have the same law
    have hTonGen : ∀ (μ : Measure (Fin P → Eucl P)), IsFiniteMeasure μ → μ univ ≠ 0 →
        (∀ (O : Eucl P ≃ₗᵢ[ℝ] Eucl P) (S' : Set (Fin P → Eucl P)), MeasurableSet S' →
          μ ((fun a i => O (a i)) ⁻¹' S') = μ S') →
        (∀ᵐ a ∂μ, LinearIndependent ℝ a) →
        ∀ (GS : (Fin P → Eucl P) → (Fin P → Eucl P)), Measurable GS →
        (∀ (O : Eucl P ≃ₗᵢ[ℝ] Eucl P) a, GS (fun i => O (a i)) = fun i => O (GS a i)) →
        (∀ a, LinearIndependent ℝ a → Orthonormal ℝ (GS a)) →
        ∀ (S' : Set (Fin P → Eucl P)), MeasurableSet S' →
        μ (GS ⁻¹' S') =
          μ ((fun a k => (WithLp.toLp 2 (fun i : Fin P => GS a i k) : Eucl P)) ⁻¹' S') := by
      intro μ hfin hμ0 hμinv hμind GS hGSm hGSeq hGSon S' hS'
      set T : (Fin P → Eucl P) → (Fin P → Eucl P) :=
        fun b k => (WithLp.toLp 2 (fun i : Fin P => b i k) : Eucl P) with hT
      set st : (Fin P → Eucl P) → (Fin P → Eucl P) → (Fin P → Eucl P) :=
        fun c b i => ∑ k, b i k • c k with hst
      have hco : ∀ k : Fin P, Continuous fun x : Eucl P => x k := fun k =>
        (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
      have hTc : Continuous T := by
        refine continuous_pi fun k => (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
        exact (hco k).comp (continuous_apply i)
      have hstc : Continuous (fun p : (Fin P → Eucl P) × (Fin P → Eucl P) => st p.1 p.2) := by
        refine continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
        exact ((hco k).comp ((continuous_apply i).comp continuous_snd)).smul
          ((continuous_apply k).comp continuous_fst)
      have hTT : ∀ b, T (T b) = b := by
        intro b; funext k; ext i; simp [hT]
      have hstT : ∀ b c, st c b = T (st (T b) (T c)) := by
        intro b c; funext i; ext j; simp [hT, hst, mul_comm]
      have hUst : ∀ c, Orthonormal ℝ c →
          ∃ U : Eucl P ≃ₗᵢ[ℝ] Eucl P, ∀ b, st c b = fun i => U (b i) := by
        intro c hc
        obtain ⟨U, hU⟩ := hUc c hc
        exact ⟨U, fun b => by funext i; simp [hst, hU]⟩
      have hTm : Measurable T := hTc.measurable
      set M : Set ((Fin P → Eucl P) × (Fin P → Eucl P)) :=
        {p | st (T (GS p.2)) (GS p.1) ∈ S'} with hM
      have hMm : MeasurableSet M :=
        hS'.preimage (hstc.measurable.comp ((hTm.comp (hGSm.comp measurable_snd)).prodMk
          (hGSm.comp measurable_fst)))
      have h1 : (μ.prod μ) M = μ ((fun a => T (GS a)) ⁻¹' S') * μ univ := by
        rw [Measure.prod_apply hMm]
        have hae : ∀ᵐ x ∂μ, μ (Prod.mk x ⁻¹' M) = μ ((fun a => T (GS a)) ⁻¹' S') := by
          filter_upwards [hμind] with x hx
          obtain ⟨U, hU⟩ := hUst (T (GS x)) (hTON _ (hGSon x hx))
          have hset : Prod.mk x ⁻¹' M =
              (fun a i => U (a i)) ⁻¹' ((fun a => T (GS a)) ⁻¹' S') := by
            ext y
            simp only [hM, mem_preimage, mem_ofPred_eq]
            rw [hstT, hTT, hU, ← hGSeq]
          rw [hset, hμinv U ((fun a => T (GS a)) ⁻¹' S') ((hTm.comp hGSm) hS')]
        rw [lintegral_congr_ae hae, lintegral_const, mul_comm]
      have h2 : (μ.prod μ) M = μ (GS ⁻¹' S') * μ univ := by
        rw [Measure.prod_apply_symm hMm]
        have hae : ∀ᵐ y ∂μ, μ ((fun x => (x, y)) ⁻¹' M) = μ (GS ⁻¹' S') := by
          filter_upwards [hμind] with y hy
          obtain ⟨U, hU⟩ := hUst (T (GS y)) (hTON _ (hGSon y hy))
          have hset : (fun x => (x, y)) ⁻¹' M = (fun a i => U (a i)) ⁻¹' (GS ⁻¹' S') := by
            ext x
            simp only [hM, mem_preimage, mem_ofPred_eq]
            rw [hU, ← hGSeq]
          rw [hset, hμinv U (GS ⁻¹' S') (hGSm hS')]
        rw [lintegral_congr_ae hae, lintegral_const, mul_comm]
      exact (ENNReal.mul_left_inj hμ0 (measure_ne_top μ univ)).mp (h2.symm.trans h1)
    -- Gram-Schmidt is equivariant under linear isometries
    have hGSeq : ∀ (O : Eucl P ≃ₗᵢ[ℝ] Eucl P) (a : Fin P → Eucl P),
        InnerProductSpace.gramSchmidtNormed ℝ (fun i => O (a i)) =
          fun i => O (InnerProductSpace.gramSchmidtNormed ℝ a i) := by
      intro O a
      have key : ∀ k, InnerProductSpace.gramSchmidt ℝ (fun i => O (a i)) k =
          O (InnerProductSpace.gramSchmidt ℝ a k) := by
        intro k
        induction k using WellFoundedLT.induction with
        | _ k ih =>
          rw [InnerProductSpace.gramSchmidt_def ℝ (fun i => O (a i)) k,
            InnerProductSpace.gramSchmidt_def ℝ a k]
          simp only [Submodule.starProjection_singleton]
          rw [map_sub, map_sum]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [ih i (Finset.mem_Iio.mp hi)]
          simp [LinearIsometryEquiv.inner_map_map, map_smul]
      funext k
      simp only [InnerProductSpace.gramSchmidtNormed, key, LinearIsometryEquiv.norm_map, map_smul]
    -- Gram-Schmidt is measurable
    have hGSm : Measurable (fun a : Fin P → Eucl P => InnerProductSpace.gramSchmidtNormed ℝ a) := by
      have key : ∀ k, Measurable (fun a : Fin P → Eucl P =>
          InnerProductSpace.gramSchmidt ℝ a k) := by
        intro k
        induction k using WellFoundedLT.induction with
        | _ k ih =>
          have h : (fun a : Fin P → Eucl P => InnerProductSpace.gramSchmidt ℝ a k) = fun a =>
              a k - ∑ i ∈ Finset.Iio k, (inner ℝ (InnerProductSpace.gramSchmidt ℝ a i) (a k) /
                ‖InnerProductSpace.gramSchmidt ℝ a i‖ ^ 2) • InnerProductSpace.gramSchmidt ℝ a i := by
            funext a
            have := InnerProductSpace.gramSchmidt_def'' ℝ a k
            simp only [RCLike.ofReal_real_eq_id, id] at this
            exact eq_sub_of_add_eq this.symm
          rw [h]
          refine (measurable_pi_apply k).sub (Finset.measurable_sum _ fun i hi => ?_)
          have hi' := ih i (Finset.mem_Iio.mp hi)
          have hin : Measurable fun a : Fin P → Eucl P =>
              inner ℝ (InnerProductSpace.gramSchmidt ℝ a i) (a k) :=
            continuous_inner.measurable.comp (hi'.prodMk (measurable_pi_apply k))
          exact (hin.div (hi'.norm.pow_const 2)).smul hi'
      refine measurable_pi_iff.mpr fun k => ?_
      simp only [InnerProductSpace.gramSchmidtNormed, RCLike.ofReal_real_eq_id, id]
      exact ((key k).norm.inv).smul (key k)
    -- the first `m + 1` Gram-Schmidt vectors recombine the first `m + 1` input vectors
    have hGSspan : ∀ a : Fin P → Eucl P, ∃ G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        ∀ i : Fin (m + 1), InnerProductSpace.gramSchmidtNormed ℝ a (Fin.castLE hnP i) =
          ∑ l, G i l • a (Fin.castLE hnP l) := by
      intro a
      have h : ∀ i : Fin (m + 1), ∃ c : Fin (m + 1) → ℝ, ∑ l, c l • a (Fin.castLE hnP l) =
          InnerProductSpace.gramSchmidtNormed ℝ a (Fin.castLE hnP i) := by
        intro i
        rw [← Submodule.mem_span_range_iff_exists_fun]
        have hmem := InnerProductSpace.gramSchmidt_mem_span ℝ a (le_refl (Fin.castLE hnP i))
        have hsub : a '' Set.Iic (Fin.castLE hnP i) ⊆
            Set.range (fun l : Fin (m + 1) => a (Fin.castLE hnP l)) := by
          rintro _ ⟨k, hk, rfl⟩
          have hk' : (k : ℕ) < m + 1 := lt_of_le_of_lt (by simpa [Fin.le_def] using hk) i.isLt
          exact ⟨⟨k, hk'⟩, by simp⟩
        unfold InnerProductSpace.gramSchmidtNormed
        exact Submodule.smul_mem _ _ (Submodule.span_mono hsub hmem)
      choose G hG using h
      exact ⟨G, fun i => (hG i).symm⟩
    -- a coordinate permutation moving the initial segment onto `α`
    have hperm : ∀ α : SimonMultiIndex (m + 1) P, ∃ O : Eucl P ≃ₗᵢ[ℝ] Eucl P,
        ∀ (x : Eucl P) (i : Fin (m + 1)), O x (α i) = x (Fin.castLE hnP i) := by
      intro α
      let e₀ : {x // x ∈ Set.range (Fin.castLE hnP)} ≃ {y // y ∈ Set.range α} :=
        (Equiv.ofInjective _ (Fin.castLE_injective hnP)).symm.trans
          (Equiv.ofInjective α α.injective)
      let σ : Equiv.Perm (Fin P) := e₀.extendSubtype
      have hσ : ∀ i, σ (Fin.castLE hnP i) = α i := by
        intro i
        simp only [σ]
        rw [Equiv.extendSubtype_apply_of_mem e₀ _ ⟨i, rfl⟩]
        simp [e₀]
      refine ⟨LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ, fun x i => ?_⟩
      rw [← hσ i]
      simp [LinearIsometryEquiv.piLpCongrLeft_apply]
    -- the random frame: Lebesgue measure restricted to the independent frames in a ball
    set B : Set (Fin P → Eucl P) := ball 0 2 ∩ {a | LinearIndependent ℝ a} with hB
    set μ : Measure (Fin P → Eucl P) := (volume : Measure (Fin P → Eucl P)).restrict B with hμ
    have hBopen : IsOpen B := isOpen_ball.inter (isOpen_setOfPred_linearIndependent (𝕜 := ℝ))
    have hBm : MeasurableSet B := hBopen.measurableSet
    have hfin : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.mpr ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
    have hμ0 : μ univ ≠ 0 := by
      rw [Measure.restrict_apply_univ]
      refine (hBopen.measure_pos _ ⟨fun i => EuclideanSpace.single i 1, ?_, ?_⟩).ne'
      · rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
        intro i
        simp
      · exact (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).linearIndependent
    have hμinv : ∀ (O : Eucl P ≃ₗᵢ[ℝ] Eucl P) (S' : Set (Fin P → Eucl P)), MeasurableSet S' →
        μ ((fun a i => O (a i)) ⁻¹' S') = μ S' := by
      intro O S' hS'
      have hΨ : MeasurePreserving (fun (a : Fin P → Eucl P) i => O (a i)) volume volume :=
        measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => O.measurePreserving)
      have hBpre : (fun (a : Fin P → Eucl P) i => O (a i)) ⁻¹' B = B := by
        ext a
        simp only [hB, mem_preimage, mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq,
          pi_norm_lt_iff (show (0 : ℝ) < 2 by norm_num), LinearIsometryEquiv.norm_map]
        have : LinearIndependent ℝ (fun i => O (a i)) ↔ LinearIndependent ℝ a :=
          LinearMap.linearIndependent_iff (v := a) O.toLinearEquiv.toLinearMap
            (LinearEquiv.ker O.toLinearEquiv)
        rw [this]
      have hpre : (fun (a : Fin P → Eucl P) i => O (a i)) ⁻¹' S' ∩ B =
          (fun (a : Fin P → Eucl P) i => O (a i)) ⁻¹' (S' ∩ B) := by
        rw [preimage_inter, hBpre]
      rw [Measure.restrict_apply (hΨ.measurable hS'), Measure.restrict_apply hS', hpre,
        hΨ.measure_preimage (hS'.inter hBm).nullMeasurableSet]
    have hμind : ∀ᵐ a ∂μ, LinearIndependent ℝ a := by
      rw [ae_restrict_iff' hBm]
      exact Filter.Eventually.of_forall fun a ha => ha.2
    -- projections of null sets of `(m + 1)`-frames are null
    have hproj : (volume : Measure (Fin P → Eucl P))
        {a | (fun i : Fin (m + 1) => a (Fin.castLE hnP i)) ∈ Z} = 0 := by
      let p : Fin P → Prop := fun k => (k : ℕ) < m + 1
      have hmp := measurePreserving_piEquivPiSubtypeProd
        (fun _ : Fin P => (volume : Measure (Eucl P))) p
      let f : Fin (m + 1) ≃ {k : Fin P // p k} :=
        { toFun := fun i => ⟨Fin.castLE hnP i, i.isLt⟩
          invFun := fun k => ⟨k.1, k.2⟩
          left_inv := fun i => by simp
          right_inv := fun k => by ext; simp }
      have hf := measurePreserving_piCongrLeft
        (fun _ : {k : Fin P // p k} => (volume : Measure (Eucl P))) f
      set Z' : Set ({k : Fin P // p k} → Eucl P) := {w | (fun i : Fin (m + 1) => w (f i)) ∈ Z}
        with hZ'
      have hZ'0 : Measure.pi (fun _ : {k : Fin P // p k} => (volume : Measure (Eucl P))) Z' = 0 := by
        rw [← hf.measure_preimage_equiv Z']
        have hpre : (MeasurableEquiv.piCongrLeft (fun _ => Eucl P) f) ⁻¹' Z' = Z := by
          ext v
          simp only [hZ', mem_preimage, mem_ofPred_eq]
          congr! 1
        rw [hpre]
        exact hZ0
      have hset : {a : Fin P → Eucl P | (fun i : Fin (m + 1) => a (Fin.castLE hnP i)) ∈ Z} =
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => Eucl P) p) ⁻¹' (Z' ×ˢ univ) := by
        ext a
        simp [hZ', f, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
      rw [hset, volume_pi, hmp.measure_preimage_equiv, Measure.prod_prod, hZ'0, zero_mul]
    set GS : (Fin P → Eucl P) → (Fin P → Eucl P) :=
      fun a => InnerProductSpace.gramSchmidtNormed ℝ a with hGS
    have hGSon : ∀ a, LinearIndependent ℝ a → Orthonormal ℝ (GS a) :=
      fun a ha => InnerProductSpace.gramSchmidtNormed_orthonormal ha
    have hGSeq' : ∀ (O : Eucl P ≃ₗᵢ[ℝ] Eucl P) a, GS (fun i => O (a i)) = fun i => O (GS a i) :=
      hGSeq
    have hGSm' : Measurable GS := hGSm
    set T : (Fin P → Eucl P) → (Fin P → Eucl P) :=
      fun b k => (WithLp.toLp 2 (fun i : Fin P => b i k) : Eucl P) with hT
    have hco : ∀ k : Fin P, Continuous fun x : Eucl P => x k := fun k =>
      (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
    have hTc : Continuous T := by
      refine continuous_pi fun k => (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      exact (hco k).comp (continuous_apply i)
    have hTm : Measurable T := hTc.measurable
    -- the law of the Gram-Schmidt frame equals the law of its transpose (Tonelli)
    have hTon := hTonGen μ hfin hμ0 hμinv hμind GS hGSm' hGSeq' hGSon
    -- every coordinate subframe of the Gram-Schmidt frame avoids `Z` almost surely
    have hS : ∀ β : Fin (m + 1) → Fin P,
        MeasurableSet {b : Fin P → Eucl P | (fun i => b (β i)) ∈ Z} :=
      fun β => hZm.preimage (measurable_pi_iff.mpr fun i => measurable_pi_apply (β i))
    have hbad : ∀ α : SimonMultiIndex (m + 1) P, μ {a | (fun i => GS a (α i)) ∈ Z} = 0 := by
      intro α
      obtain ⟨O, hO⟩ := hperm α
      have e1 : μ {a | (fun i => GS a (α i)) ∈ Z} = μ {a | (fun i => T (GS a) (α i)) ∈ Z} :=
        hTon _ (hS α)
      have hX : MeasurableSet {a | (fun i => T (GS a) (α i)) ∈ Z} := (hTm.comp hGSm') (hS α)
      have e2 : μ {a | (fun i => T (GS a) (α i)) ∈ Z} =
          μ {a | (fun i => T (GS a) (Fin.castLE hnP i)) ∈ Z} := by
        rw [← hμinv O _ hX]
        congr 1
        ext a
        simp only [mem_preimage, mem_ofPred_eq]
        rw [hGSeq']
        have : (fun i => T (fun j => O (GS a j)) (α i)) =
            (fun i => T (GS a) (Fin.castLE hnP i)) := by
          funext i; ext j; simp [hT, hO]
        rw [this]
      have e3 : μ {a | (fun i => T (GS a) (Fin.castLE hnP i)) ∈ Z} =
          μ {a | (fun i => GS a (Fin.castLE hnP i)) ∈ Z} :=
        (hTon _ (hS (Fin.castLE hnP))).symm
      have e4 : μ {a | (fun i => GS a (Fin.castLE hnP i)) ∈ Z} ≤
          μ {a | (fun i => a (Fin.castLE hnP i)) ∈ Z} := by
        refine measure_mono fun a ha => ?_
        obtain ⟨G, hG⟩ := hGSspan a
        have h' : (fun i => GS a (Fin.castLE hnP i)) =
            fun i => ∑ l, G i l • a (Fin.castLE hnP l) := funext hG
        exact hZpre G _ (h' ▸ ha)
      have e5 : μ {a | (fun i => a (Fin.castLE hnP i)) ∈ Z} = 0 :=
        le_antisymm ((Measure.restrict_le_self _).trans_eq hproj) zero_le
      rw [e1, e2, e3]
      exact le_antisymm (e4.trans e5.le) zero_le
    have hfinite : Finite (SimonMultiIndex (m + 1) P) :=
      Finite.of_injective (fun f : Fin (m + 1) ↪o Fin P => (f : Fin (m + 1) → Fin P))
        (fun f g h => RelEmbedding.ext (congrFun h))
    have hN : μ ({a | LinearIndependent ℝ a}ᶜ ∪
        ⋃ α : SimonMultiIndex (m + 1) P, {a | (fun i => GS a (α i)) ∈ Z}) = 0 := by
      refine measure_union_null ?_ (measure_iUnion_null hbad)
      rw [Measure.restrict_apply' hBm]
      refine measure_mono_null (fun a ha => ?_) measure_empty
      exact ha.1 ha.2.2
    obtain ⟨a, ha⟩ : ({a | LinearIndependent ℝ a}ᶜ ∪
        ⋃ α : SimonMultiIndex (m + 1) P, {a | (fun i => GS a (α i)) ∈ Z})ᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at h
      rw [h] at hN
      exact hμ0 hN
    simp only [mem_compl_iff, mem_union, not_or, mem_iUnion, not_exists, mem_ofPred_eq,
      not_not] at ha
    obtain ⟨hind, hgood⟩ := ha
    obtain ⟨U, hU⟩ := hUc (GS a) (hGSon a hind)
    refine ⟨U.symm, fun α => ?_⟩
    simp only [LinearIsometryEquiv.symm_symm, hU]
    have hsum : (fun i => ∑ k, (EuclideanSpace.single (α i) (1 : ℝ)) k • GS a k) =
        fun i => GS a (α i) := by
      funext i
      simp [PiLp.single_apply]
    rw [hsum]
    exact hgood α
  -- Step 2: compact, purely unrectifiable pieces of finite measure covering `A` up to a null set.
  obtain ⟨K, hKc, hKfin, hKpu, hnull⟩ : ∃ K : ℕ → Set (Eucl P), (∀ j, IsCompact (K j)) ∧
      (∀ j, (μHE[m + 1] : Measure (Eucl P)) (K j) < ∞) ∧
      (∀ j, Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) (K j)) ∧
      (μHE[m + 1] : Measure (Eucl P)) (A \ ⋃ j, K j) = 0 := by
    obtain ⟨S, hAS, hSfin⟩ := hS
    set μ : Measure (Eucl P) := μHE[m + 1] with hμ
    let A' : ℕ → Set (Eucl P) := fun j => A ∩ S j
    have hA'fin : ∀ j, μ (A' j) ≠ ∞ := fun j =>
      ((measure_mono inter_subset_right).trans_lt (hSfin j)).ne
    let B : ℕ → Set (Eucl P) := fun j => toMeasurable μ (A' j)
    have hBmeas : ∀ j, MeasurableSet (B j) := fun j => measurableSet_toMeasurable _ _
    have hAB : ∀ j, A' j ⊆ B j := fun j => subset_toMeasurable _ _
    have hBfin : ∀ j, μ (B j) < ∞ := fun j => by
      simp only [B, measure_toMeasurable]; exact (hA'fin j).lt_top
    have hBinter : ∀ j F, MeasurableSet F → μ (toMeasurable μ (A' j) ∩ F) = μ (A' j ∩ F) :=
      fun j F hF => Measure.measure_toMeasurable_inter hF (hA'fin j)
    have hBpu : ∀ j, Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) (B j) := by
      intro j
      obtain ⟨R, Pp, hRP, -, hRmeas, -, hRrect, hPpu⟩ :=
        Poincare.SimonGMT.Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition
          (n := m + 1) (hBmeas j).nullMeasurableSet (fun _ => B j)
          (subset_iUnion_of_subset 0 subset_rfl) (fun _ => hBfin j)
      have hRsub : R ⊆ B j := by rw [hRP]; exact subset_union_left
      have hR0 : μ R = 0 := by
        have h1 := hBinter j R hRmeas
        rw [inter_eq_right.mpr hRsub] at h1
        rw [h1]
        exact hA _ (inter_subset_left.trans inter_subset_left) (hRrect.mono inter_subset_right)
      intro T hT hTrect
      have hcov : T ⊆ (T ∩ R) ∪ (T ∩ Pp) := by
        intro x hx
        have hxB := hT hx
        rw [hRP] at hxB
        rcases hxB with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      refine measure_mono_null hcov (measure_union_null (measure_mono_null inter_subset_right hR0) ?_)
      exact hPpu _ inter_subset_right (hTrect.mono inter_subset_left)
    have hcomp : ∀ j, ∃ C : ℕ → Set (Eucl P), (∀ i, IsCompact (C i)) ∧ (∀ i, C i ⊆ B j) ∧
        μ (B j \ ⋃ i, C i) = 0 := by
      intro j
      have : IsFiniteMeasure (μ.restrict (B j)) := isFiniteMeasure_restrict.mpr (hBfin j).ne
      have happrox : ∀ i : ℕ, ∃ C ⊆ B j, IsCompact C ∧
          μ.restrict (B j) (B j \ C) < ((i : ℝ≥0∞) + 1)⁻¹ := fun i =>
        (hBmeas j).exists_isCompact_sdiff_lt (measure_ne_top _ _) (by simp)
      choose C hCsub hCc hCsmall using happrox
      refine ⟨C, hCc, hCsub, ?_⟩
      have hle : ∀ i : ℕ, μ.restrict (B j) (B j \ ⋃ k, C k) ≤ ((i : ℝ≥0∞) + 1)⁻¹ := fun i =>
        ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion C i))).trans (hCsmall i).le)
      have h0 : μ.restrict (B j) (B j \ ⋃ k, C k) = 0 := by
        refine le_antisymm (ENNReal.le_of_forall_pos_le_add ?_) zero_le
        intro ε hε _
        obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
        calc μ.restrict (B j) (B j \ ⋃ k, C k) ≤ ((i : ℝ≥0∞) + 1)⁻¹ := hle i
          _ ≤ (i : ℝ≥0∞)⁻¹ := by gcongr; exact le_self_add
          _ ≤ ε := hi.le
          _ ≤ 0 + ε := by simp
      rwa [Measure.restrict_apply' (hBmeas j), inter_eq_left.mpr sdiff_subset] at h0
    choose C hCc hCsub hCnull using hcomp
    refine ⟨fun k => C (Nat.unpair k).1 (Nat.unpair k).2, fun k => hCc _ _, fun k => ?_,
      fun k => ?_, ?_⟩
    · exact (measure_mono (hCsub _ _)).trans_lt (hBfin _)
    · exact (hBpu _).mono (hCsub _ _)
    · have hsub : A \ ⋃ k, C (Nat.unpair k).1 (Nat.unpair k).2 ⊆ ⋃ j, (B j \ ⋃ i, C j i) := by
        intro x hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hAS hx.1)
        refine mem_iUnion.mpr ⟨j, hAB j ⟨hx.1, hj⟩, ?_⟩
        intro hxC
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxC
        exact hx.2 (mem_iUnion.mpr ⟨Nat.pair j i, by simpa [Nat.unpair_pair] using hi⟩)
      exact measure_mono_null hsub (measure_iUnion_null hCnull)
  -- the row maps `L v x = (⟪v i, x⟫)ᵢ`
  let L : (Fin (m + 1) → Eucl P) → Eucl P → Eucl (m + 1) :=
    fun v x => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))
  -- Step 3(b): `v ↦ Lⁿ(L v '' K)` is measurable for compact `K` (closed graph and Tonelli).
  have hLmeas : ∀ K' : Set (Eucl P), IsCompact K' →
      Measurable (fun v => (volume : Measure (Eucl (m + 1))) (L v '' K')) := by
    intro K' hK'
    let Λ : (Fin (m + 1) → Eucl P) × Eucl P → Eucl (m + 1) := fun p => L p.1 p.2
    have hΛ : Continuous Λ := by
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      exact ((continuous_apply i).comp continuous_fst).inner continuous_snd
    let Γ : Set ((Fin (m + 1) → Eucl P) × Eucl (m + 1)) := {q | ∃ x ∈ K', Λ (q.1, x) = q.2}
    have hΓ : IsClosed Γ := by
      have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
      let C' : Set (((Fin (m + 1) → Eucl P) × Eucl (m + 1)) × K') :=
        {r | Λ (r.1.1, (r.2 : Eucl P)) = r.1.2}
      have hC' : IsClosed C' := isClosed_eq
        (hΛ.comp ((continuous_fst.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)))
        (continuous_snd.comp continuous_fst)
      have himg : Prod.fst '' C' = Γ := by
        ext q
        constructor
        · rintro ⟨r, hr, rfl⟩
          exact ⟨r.2, r.2.2, hr⟩
        · rintro ⟨x, hx, hq⟩
          exact ⟨(q, ⟨x, hx⟩), hq, rfl⟩
      rw [← himg]
      exact isClosedMap_fst_of_compactSpace C' hC'
    have hmeas := measurable_measure_prodMk_left (ν := (volume : Measure (Eucl (m + 1))))
      hΓ.measurableSet
    have hsec : ∀ v : Fin (m + 1) → Eucl P, Prod.mk v ⁻¹' Γ = L v '' K' := by
      intro v
      ext y
      simp only [mem_image, mem_preimage, mem_ofPred_eq, Γ, Λ]
    simp_rw [← hsec]
    exact hmeas
  -- Step 3(c): recombining the rows by a matrix `G` scales `Lⁿ(L v '' S)` by `|det G|`.
  have hLrec : ∀ (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (v : Fin (m + 1) → Eucl P)
      (S' : Set (Eucl P)), (volume : Measure (Eucl (m + 1))) (L (fun i => ∑ l, G i l • v l) '' S') =
        ENNReal.ofReal |G.det| * (volume : Measure (Eucl (m + 1))) (L v '' S') := by
    intro G v S'
    let g : Eucl (m + 1) →ₗ[ℝ] Eucl (m + 1) := Matrix.toEuclideanLin G
    have hcomp : L (fun i => ∑ l, G i l • v l) = g ∘ L v := by
      funext x
      ext i
      simp [L, g, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, sum_inner, inner_smul_left]
    have hdet : LinearMap.det g = G.det := by
      simp only [g, Matrix.toEuclideanLin]
      simp
    rw [hcomp, Set.image_comp, Measure.addHaar_image_linearMap, hdet]
  -- the bad set `Z`
  let Z : Set (Fin (m + 1) → Eucl P) :=
    ⋃ j, {v | 0 < (volume : Measure (Eucl (m + 1))) (L v '' K j)}
  have hZm : MeasurableSet Z :=
    MeasurableSet.iUnion fun j => measurableSet_lt measurable_const (hLmeas (K j) (hKc j))
  -- Step 3(a): `Z` is Lebesgue-null.
  have hZ0 : (volume : Measure (Fin (m + 1) → Eucl P)) Z = 0 := by
    refine measure_iUnion_null fun j => ?_
    have h := bf P m (K j) (hKc j).isClosed.measurableSet (hKfin j) (hKpu j)
    rw [ae_iff] at h
    refine measure_mono_null (fun v hv => ?_) h
    simp only [mem_ofPred_eq] at hv ⊢
    exact hv.ne'
  have hZpre : ∀ (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (w : Fin (m + 1) → Eucl P),
      (fun i => ∑ l, G i l • w l) ∈ Z → w ∈ Z := by
    intro G w hw
    simp only [Z, mem_iUnion, mem_ofPred_eq] at hw ⊢
    obtain ⟨j, hj⟩ := hw
    refine ⟨j, pos_iff_ne_zero.mpr fun h0 => ?_⟩
    rw [hLrec G w (K j), h0, mul_zero] at hj
    exact lt_irrefl _ hj
  obtain ⟨Q, hQ⟩ := hFA Z hZm hZ0 hZpre
  -- Steps 4 and 3(d): conclusion
  refine ⟨Q, fun α => ?_⟩
  set v : Fin (m + 1) → Eucl P := fun i => Q.symm (EuclideanSpace.single (α i) (1 : ℝ)) with hvdef
  have hv : ∀ j, (volume : Measure (Eucl (m + 1))) (L v '' K j) = 0 := by
    intro j
    by_contra hne
    exact hQ α (mem_iUnion.mpr ⟨j, pos_iff_ne_zero.mpr hne⟩)
  have hrows : (fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1)))
      = L v := by
    funext x
    simp only [L, v]
    congr 1
    funext i
    rw [← LinearIsometryEquiv.inner_map_map Q, LinearIsometryEquiv.apply_symm_apply,
      EuclideanSpace.inner_single_left]
    simp
  rw [hrows]
  have hsub : L v '' A ⊆ (⋃ j, L v '' K j) ∪ L v '' (A \ ⋃ j, K j) := by
    rintro y ⟨x, hxA, rfl⟩
    by_cases hx : x ∈ ⋃ j, K j
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact Or.inl (mem_iUnion.mpr ⟨j, mem_image_of_mem _ hj⟩)
    · exact Or.inr (mem_image_of_mem _ ⟨hxA, hx⟩)
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null hv) ?_)
  let ℓ : Eucl P →ₗ[ℝ] Eucl (m + 1) :=
    { toFun := L v
      map_add' := by
        intro x y
        simp only [L]
        ext i
        simp [inner_add_right]
      map_smul' := by
        intro c x
        simp only [L]
        ext i
        simp [inner_smul_right] }
  let f : Eucl P →L[ℝ] Eucl (m + 1) := LinearMap.toContinuousLinearMap ℓ
  have hf : (f : Eucl P → Eucl (m + 1)) = L v := rfl
  have hvol : (volume : Measure (Eucl (m + 1))) = (μHE[m + 1] : Measure (Eucl (m + 1))) := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Eucl (m + 1))
    simpa [finrank_euclideanSpace] using h.symm
  rw [hvol, ← hf]
  have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
    (A := A \ ⋃ j, K j) (m + 1) (f.lipschitzWith.lipschitzOnWith)
  rw [hnull, mul_zero] at hle
  exact le_antisymm hle zero_le

/-- Simon Ch. 6, proof of 8.1, (1)–(8) (pp. 173–174): if `Θ*ⁿ(μ, x) > 0` for `μ`-a.e. `x`, the
mass measure `μ` of `T` is `θ Hⁿ ⌞ M` for a Borel, countably `n`-rectifiable `M ⊆ U` and a Borel
`θ`, positive on `M` and locally `Hⁿ`-integrable in `U`.  A Borel carrier
`B₀ ⊆ U ∩ {Θ*ⁿ(μ, ·) > 0}` of `μ` is `Hⁿ`-σ-finite; in its decomposition `B₀ = R ∪ P'`
(Ch. 3, Lemma 3.2) the purely unrectifiable part `P'` is `μ`-null by the structure theorem and
Remark 2.37(2), hence `Hⁿ`-null; Radon–Nikodym for `μ ≪ Hⁿ ⌞ B₀` then gives `M` and `θ`. -/
theorem Submission.rectifiability_mass_measure_rectifiable : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ μ : Measure (Eucl P), IsMassMeasure T μ → (∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) → ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ), M ⊆ U ∧ MeasurableSet M ∧ CountablyRectifiable (m + 1) M ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) ∧ μ = ((μHE[m + 1] : Measure (Eucl P)).restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) := by
  intro P m U hU T hmass μ hμ hdens
  -- Step 1: an exhaustion `W i ⊂⊂ U` with `μ(W i) = M_{W i}(T) < ∞` and `U ⊆ ⋃ i, W i`, so `μ`
  -- is σ-finite; and `μ ≪ Hⁿ` (Remark 2.37(1)).
  obtain ⟨W, hWU, hWK⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
  have hWo : ∀ i, IsOpen (W i) := fun i => (hWU i).1
  have hWfin : ∀ i, μ (W i) < ∞ := fun i => by
    rw [hμ.2 _ (hWU i)]
    exact le_self_add.trans_lt (hmass _ (hWU i))
  have hUW : U ⊆ ⋃ i, W i := fun x hx => by
    obtain ⟨i, hi⟩ := hWK {x} isCompact_singleton (singleton_subset_iff.2 hx)
    exact mem_iUnion.2 ⟨i, hi (mem_singleton x)⟩
  have hμσ : SigmaFinite μ := by
    refine ⟨⟨⟨fun i => W i ∪ Uᶜ, fun _ => trivial, fun i => ?_, ?_⟩⟩⟩
    · exact (measure_union_le _ _).trans_lt (by rw [hμ.1, add_zero]; exact hWfin i)
    · refine eq_univ_of_forall fun x => ?_
      by_cases hx : x ∈ U
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (hUW hx)
        exact mem_iUnion.2 ⟨i, Or.inl hi⟩
      · exact mem_iUnion.2 ⟨0, Or.inr hx⟩
  have hac := Submission.rectifiability_mass_measure_abs_continuous P m U hU T hmass μ hμ
  -- Step 2: a Borel carrier `B₀ = U ∖ Z` of `μ`, `Z` a Borel `μ`-null hull of
  -- `{x : ¬ Θ*ⁿ(μ, x) > 0}`.
  obtain ⟨B₀, hB₀m, hB₀U, hB₀D, hμB₀⟩ : ∃ B₀ : Set (Eucl P), MeasurableSet B₀ ∧ B₀ ⊆ U ∧
      (∀ x ∈ B₀, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) ∧
      μ B₀ᶜ = 0 := by
    set Z := toMeasurable μ {x | ¬ 0 < dimensionalUpperDensity μ.toOuterMeasure
      ((m + 1 : ℕ) : ℝ) univ x} with hZ
    have hZ0 : μ Z = 0 := by
      rw [hZ, measure_toMeasurable]
      exact ae_iff.1 hdens
    refine ⟨U \ Z, hU.measurableSet.diff (measurableSet_toMeasurable _ _), sdiff_subset,
      fun x hx => ?_, measure_mono_null (fun x hx => ?_) (measure_union_null hμ.1 hZ0)⟩
    · by_contra h
      exact hx.2 (subset_toMeasurable _ _ h)
    · by_cases hxU : x ∈ U
      · exact Or.inr (by_contra fun hxZ => hx ⟨hxU, hxZ⟩)
      · exact Or.inl hxU
  -- Step 3 (printed (1)): `B₀` is covered by countably many sets of finite `Hⁿ`-measure.
  obtain ⟨C, hB₀C, hCfin⟩ := (Submission.rectifiability_positive_density_cover_null P (m + 1) μ W
    B₀ hWo hWfin (hB₀U.trans hUW) hB₀D).1
  -- Step 4: Lemma 3.2 of Ch. 3 gives `B₀ = R ∪ P'` with `R` Borel and countably rectifiable and
  -- `P'` purely unrectifiable.
  obtain ⟨R, P', hRP, -, -, hP'm, hRrect, hP'pure⟩ :=
    Poincare.SimonGMT.Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition
      hB₀m.nullMeasurableSet C hB₀C hCfin
  have hP'B₀ : P' ⊆ B₀ := subset_union_right.trans hRP.symm.subset
  -- `μ(P') = 0`: the structure theorem gives `Q` with `Lⁿ(p_α(Q P')) = 0` for all `α`; Remark
  -- 2.37(2) gives `μ(Bk) = 0` for a Borel kernel `Bk ⊆ P'`, and `μ ≪ Hⁿ` handles `P' ∖ Bk`.
  obtain ⟨Q, hQ⟩ := Submission.rectifiability_structure_projection P m P' hP'pure
    ⟨C, hP'B₀.trans hB₀C, hCfin⟩
  obtain ⟨Bk, hBkP', hBkm, hBkae⟩ := hP'm.exists_measurable_subset_ae_eq
  have hμBk : μ Bk = 0 := Submission.rectifiability_projection_null P m U hU T hmass μ hμ Q Bk
    hBkm fun α => measure_mono_null (image_mono hBkP') (hQ α)
  have hμP' : μ P' = 0 :=
    measure_mono_null (union_sdiff_cancel hBkP').symm.subset
      (measure_union_null hμBk (hac (ae_le_set.1 hBkae.symm.le)))
  -- `Hⁿ(P') = 0` (printed (6)), so `B₀ = R ∪ P'` is countably rectifiable (printed (7)).
  have hP'0 : (μHE[m + 1] : Measure (Eucl P)) P' = 0 :=
    (Submission.rectifiability_positive_density_cover_null P (m + 1) μ W P' hWo hWfin
      (hP'B₀.trans (hB₀U.trans hUW)) fun x hx => hB₀D x (hP'B₀ hx)).2 hμP'
  have hB₀rect : CountablyRectifiable (m + 1) B₀ := by
    have h := Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (n := m + 1) (D := {R, P'})
      ((countable_singleton P').insert R) (by
        rintro S (rfl | rfl)
        exacts [hRrect, Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hP'0])
    rwa [sUnion_pair, ← hRP] at h
  -- Steps 5–6 (printed (8)): Radon–Nikodym for `μ ≪ Hⁿ ⌞ B₀`, with `Hⁿ ⌞ B₀` σ-finite by step 3,
  -- gives `M ⊆ B₀` and `θ > 0` on `M` with `μ = θ Hⁿ ⌞ M`.
  obtain ⟨M, θ, hMB₀, hMm, hθm, hθpos, hθint, hrep⟩ :=
    Submission.rectifiability_rn_positive_real_density (Eucl P) (μHE[m + 1] : Measure (Eucl P)) μ
      B₀ hB₀m (Poincare.SimonGMT.Chapter03.sigmaFinite_restrict_of_hausdorff_finite_cover C hB₀C
        hCfin) hμσ hμB₀ hac
  -- Step 7: a compact `K ⊆ U` lies in some `W i`, so `μ(K) < ∞` and `θ` is integrable on `M ∩ K`.
  refine ⟨M, θ, hMB₀.trans hB₀U, hMm, hB₀rect.mono hMB₀, hθm, hθpos, fun K hK hKU => ?_, hrep⟩
  obtain ⟨i, hi⟩ := hWK K hK hKU
  exact hθint K hK.measurableSet ((measure_mono hi).trans_lt (hWfin i))

/-- **Simon Ch. 6, 8.1 (Rectifiability Theorem, p. 173).**  By (1)–(8) of the printed proof the
mass measure is `μ = θ Hⁿ ⌞ M` with `M` countably `n`-rectifiable and `θ > 0` locally
`Hⁿ`-integrable on `M`; by (2.7)–(2.8) `T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|ξ| = 1` `μ`-a.e., so
`T = τ(M, θ, ξ)` (9); and by (10)–(13) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the
weighted approximate tangent space `TₓM`, for `Hⁿ`-a.e. `x ∈ M`.  (Book `n = m + 1`.) -/
theorem Submission.rectifiability_theorem : RectifiabilityTheorem := by
  intro P m U hU T hT ⟨μ, hμ, hdens⟩
  -- (1)–(8): `μ = θ Hⁿ ⌞ M`.
  obtain ⟨M, θ, hMU, hM, hMrect, hθm, hθpos, hθint, rfl⟩ :=
    Submission.rectifiability_mass_measure_rectifiable P m U hU T hT μ hμ hdens
  -- (2.7)–(2.8), using `M_W(T) ≤ M_W(T) + M_W(∂T)`.
  obtain ⟨ξ, hξm, hξ1, hrep⟩ :=
    (Submission.rectifiability_mass_measure_representation P (m + 1) U hU T fun W hW =>
      (hT W hW).trans_le' le_self_add).2 _ hμ
  -- (9): `T = τ(M, θ, ξ)`, as `θ > 0` on `M`.
  have hτ : ∀ ω : TestFormOn U (m + 1), T ω = tauAction (m + 1) M θ ξ ω := fun ω => by
    rw [(hrep ω).2, integral_withDensity_eq_integral_toReal_smul hθm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), tauAction]
    exact setIntegral_congr_fun hM fun x hx => by
      rw [ENNReal.toReal_ofReal (hθpos x hx).le, smul_eq_mul]
  -- `|ξ| = 1` holds `Hⁿ`-a.e. on `M`, as `θ > 0` on `M`.
  have hξ1' : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
      ∑ α : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) α) ^ 2 = 1 := by
    filter_upwards [(ae_withDensity_iff hθm.ennreal_ofReal).1 hξ1, ae_restrict_mem hM]
      with x hx hxM
    exact hx (ENNReal.ofReal_pos.2 (hθpos x hxM)).ne'
  -- (10)–(13), using `M_W(∂T) ≤ M_W(T) + M_W(∂T)`.
  exact ⟨M, θ, ξ, ⟨hMU, hM.nullMeasurableSet, hMrect, hθpos, hθint, hξm.aestronglyMeasurable,
    Submission.rectifiability_orientation P m U hU T (fun W hW => (hT W hW).trans_le' le_add_self)
      M θ ξ hMU hM.nullMeasurableSet hMrect hθpos hθint hξm.aestronglyMeasurable hξ1' hτ⟩, hτ⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
