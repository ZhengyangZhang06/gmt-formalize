import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter02.AreaCritical
import Poincare.SimonGMT.Chapter02.AreaDomain

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

/-- **Unit bound for the orientation `±τ₁ ∧ ⋯ ∧ τₙ` (Simon Ch. 6, 3.1).**  If `τ` is an
orthonormal family in `ℝ^P` and `w = ±simpleNVector τ`, then `|w(α)| ≤ ‖α‖` for every
`n`-covector `α`: `simpleNVector τ α = α(τ₁, …, τₙ)` and `‖α(τ)‖ ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
(`ContinuousAlternatingMap.le_opNorm`, each `τᵢ` a unit vector). -/
theorem Submission.fiw_ims_tt_unit_bound : ∀ (P n : ℕ) (τ : Fin n → Eucl P) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → ∀ α : Covector (Eucl P) n, |w α| ≤ ‖α‖ := by
  intro P n τ w hτ hw α
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`.
  have h1 : |simpleNVector τ α| ≤ ‖α‖ := by
    rw [simpleNVector_apply, ← Real.norm_eq_abs]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
      _ = ‖α‖ := by simp [hτ.1]
  -- `w = ±simpleNVector τ`, and `|-a| = |a|`.
  rcases hw with rfl | rfl
  · exact h1
  · simpa [abs_neg] using h1
/-- **Null-set consequences of the co-area identity (Simon Ch. 6, proof of 4.5(2)).**  Assume
(CA): for every Borel `g ≥ 0`, `t ↦ ∫_{M ∩ f⁻¹{t}} g dν` is a.e.-measurable and
`∫_ℝ ∫_{M ∩ f⁻¹{t}} g dν dt = ∫_M |G| g dμ`.  Then (i) `G = 0` `μ⌞M`-a.e. on each level set
`{f = c}` (test (CA) with `g = 1_{f = c}`: the slice integrals vanish for `t ≠ c`); and (ii) a
`μ`-null `Z ⊆ M` has `ν`-null slices `Z ∩ f⁻¹{t}` for a.e. `t` (test (CA) with `g = 1_{Z'}`,
`Z' ⊇ Z` a measurable `μ`-null hull). -/
theorem Submission.slicing_im_si_coarea_null_sets : ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P), Measurable f → Measurable G → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂μ) → (∀ c : ℝ, ∀ᵐ x ∂(μ.restrict M), f x = c → G x = 0) ∧ ∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0 := by
  intro P μ ν M f G hf hG CA
  constructor
  · intro c
    have hmc : MeasurableSet (f ⁻¹' {c}) := hf (measurableSet_singleton c)
    obtain ⟨-, hCA⟩ := CA ((f ⁻¹' {c}).indicator 1) (measurable_one.indicator hmc)
    -- The slice integrals `ν(f⁻¹{c} ∩ M ∩ f⁻¹{t})` vanish for `t ≠ c`.
    have hslice : ∀ t, t ≠ c → ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν = 0 := by
      intro t ht
      rw [lintegral_indicator_one hmc, Measure.restrict_apply hmc]
      convert measure_empty (μ := ν)
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hxc _ hxt
      exact ht (hxt.symm.trans hxc)
    -- `{c}` is Lebesgue-null, so the left side of (CA) is `0`.
    have hL : ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν)
        ∂(volume : Measure ℝ) = 0 := by
      have : (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, (f ⁻¹' {c}).indicator 1 x ∂ν) =ᵐ[volume] 0 := by
        have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
          simp [ae_iff, measure_singleton]
        filter_upwards [hne] with t ht
        exact hslice t ht
      rw [lintegral_congr_ae this]
      simp
    -- Hence `|G| 1_{f = c} = 0` `μ⌞M`-a.e.
    rw [hL] at hCA
    have hmeas : AEMeasurable (fun x => ‖G x‖ₑ * (f ⁻¹' {c}).indicator 1 x) (μ.restrict M) :=
      (hG.enorm.mul (measurable_one.indicator hmc)).aemeasurable
    have h0 := (lintegral_eq_zero_iff' hmeas).1 hCA.symm
    filter_upwards [h0] with x hx hfx
    have hxc : x ∈ f ⁻¹' {c} := hfx
    simp only [Pi.zero_apply, indicator_of_mem hxc, Pi.one_apply, mul_one, enorm_eq_zero] at hx
    exact hx
  · intro Z hZM hZ
    -- A measurable `μ`-null hull `Z' = toMeasurable μ Z ⊇ Z`.
    have hZ'm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hZ'0 : μ (toMeasurable μ Z) = 0 := by rw [measure_toMeasurable]; exact hZ
    obtain ⟨hae, hCA⟩ := CA ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZ'm)
    -- The right side of (CA) vanishes, since `1_{Z'} = 0` `μ`-a.e.
    have hR : ∫⁻ x in M, ‖G x‖ₑ * (toMeasurable μ Z).indicator 1 x ∂μ = 0 := by
      have hnull : ∀ᵐ x ∂μ, x ∉ toMeasurable μ Z := measure_eq_zero_iff_ae_notMem.1 hZ'0
      have : (fun x => ‖G x‖ₑ * (toMeasurable μ Z).indicator 1 x) =ᵐ[μ.restrict M] 0 := by
        filter_upwards [ae_restrict_of_ae hnull] with x hx
        simp [indicator_of_notMem hx]
      rw [lintegral_congr_ae this]
      simp
    -- So `ν(Z' ∩ (M ∩ f⁻¹{t})) = 0` for a.e. `t`, and `Z ∩ f⁻¹{t} ⊆ Z' ∩ (M ∩ f⁻¹{t})`.
    rw [hR] at hCA
    have h0 := (lintegral_eq_zero_iff' hae).1 hCA
    filter_upwards [h0] with t ht
    simp only [Pi.zero_apply] at ht
    rw [lintegral_indicator_one hZ'm, Measure.restrict_apply hZ'm] at ht
    refine measure_mono_null (fun x hx => ?_) ht
    exact ⟨subset_toMeasurable μ Z hx.1, hZM hx.1, hx.2⟩

/-- **Borel density for `θ⟨ξ, G♭ ∧ ω⟩` (Simon Ch. 6, Remark 4.2 and proof of 4.5).**  For a
rectifiable triple `(M, θ, ξ)`, a Borel `G`, `ν := |G|⁻¹G` and `ω ∈ 𝒟ᵐ(U)`, there is a Borel
`Hⁿ⌞M`-integrable `g` vanishing on `{G = 0}` with `g = θ⟨ξ⌞ν, ω⟩` where `G ≠ 0` and
`θ⟨ξ, G♭ ∧ ω⟩ = |G| g`, `Hⁿ⌞M`-a.e.: `g := 1_{K ∩ {G ≠ 0}} θ' ξ'(ν♭ ∧ ω)` with `K = tsupport ω`,
Borel versions `θ'` of `θ` on `M ∩ K` and `ξ'` of `ξ` on `M`, dominated by
`(m + 1) sup ‖ω‖ · |1_K θ'|` (unit bound `|ξ(α)| ≤ ‖α‖`). -/
theorem Submission.slicing_im_si_borel_density :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (G : Eucl P → Eucl P) (ω : TestFormOn U m), IsRectifiableTriple U (m + 1) M θ ξ → Measurable G → ∃ g : Eucl P → ℝ, Measurable g ∧ Integrable g ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧ (∀ x, G x = 0 → g x = 0) ∧ ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), (G x ≠ 0 → g x = θ x * (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x)))) ((ω : DifferentialForm (Eucl P) m) x)) ∧ θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))) = ‖G x‖ * g x := by
  have unit_bound := Submission.fiw_ims_tt_unit_bound
  intro P m U M θ ξ G ω hM hG
  have hwc : Continuous (ω : DifferentialForm (Eucl P) m) := ω.2.1.1.continuous
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) m)) := ω.2.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U := ω.2.2
  obtain ⟨K, hK⟩ : ∃ K : Set (Eucl P), K = tsupport (ω : DifferentialForm (Eucl P) m) := ⟨_, rfl⟩
  rw [← hK] at hKc hKU
  have hKm : MeasurableSet K := hK ▸ (isClosed_tsupport _).measurableSet
  have hw0 : ∀ x, x ∉ K → (ω : DifferentialForm (Eucl P) m) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hK ▸ hx)
  obtain ⟨Cw, hCw⟩ := hwc.bounded_above_of_compact_support ω.2.1.2
  -- Borel versions of θ (on M ∩ K) and ξ (on M)
  have hθK : IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P)) := hM.integrableOn K hKc hKU
  obtain ⟨θ', hθ'm, hθθ'⟩ := hθK.aestronglyMeasurable
  obtain ⟨ξ', hξ'm, hξξ'⟩ := hM.aestronglyMeasurable
  -- the covector field β = ν♭ ∧ ω with ν = G/|G|
  have hνm : Measurable (fun x => ‖G x‖⁻¹ • G x) := (hG.norm.inv).smul hG
  have hνle : ∀ x, ‖‖G x‖⁻¹ • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, norm_inv, norm_norm]
    by_cases h : ‖G x‖ = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  obtain ⟨β, hβ⟩ : ∃ β : Eucl P → Covector (Eucl P) (m + 1), β = fun x =>
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := ⟨_, rfl⟩
  have hBc : Continuous (fun p : Eucl P × Covector (Eucl P) m =>
      ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ p.1).smulRight p.2)) := by
    have h2 : Continuous (fun p : Eucl P × Covector (Eucl P) m => (innerSL ℝ p.1).smulRight p.2) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Eucl P) (F := Covector (Eucl P) m)).continuous.comp
        (((innerSL ℝ).continuous.comp continuous_fst).prodMk continuous_snd)
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp h2
  have hβm : StronglyMeasurable β := by
    have h3 : StronglyMeasurable (fun x => ((‖G x‖⁻¹ • G x : Eucl P), (ω : DifferentialForm (Eucl P) m) x)) :=
      hνm.stronglyMeasurable.prodMk hwc.stronglyMeasurable
    have h4 := hBc.comp_stronglyMeasurable h3
    beta_reduce at h4
    rw [hβ]; exact h4
  have hβle : ∀ x, ‖β x‖ ≤ (m + 1) * Cw := by
    intro x
    rw [hβ]
    calc ‖ContinuousAlternatingMap.alternatizeUncurryFin
            ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))‖
        ≤ ((m : ℝ) + 1) * ‖(innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)‖ :=
          ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _
      _ = ((m : ℝ) + 1) * (‖‖G x‖⁻¹ • G x‖ * ‖(ω : DifferentialForm (Eucl P) m) x‖) := by
          rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      _ ≤ ((m : ℝ) + 1) * (1 * Cw) := by
          gcongr
          · exact hνle x
          · exact hCw x
      _ = (m + 1) * Cw := by ring
  have hξβm : StronglyMeasurable (fun x => ξ' x (β x)) := by
    have h4 := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hξ'm.prodMk hβm)
    beta_reduce at h4
    exact h4
  -- the density
  have hSm : MeasurableSet {x | x ∈ K ∧ G x ≠ 0} :=
    hKm.inter (hG (measurableSet_singleton (0 : Eucl P))).compl
  obtain ⟨g, hg⟩ : ∃ g : Eucl P → ℝ,
      g = {x | x ∈ K ∧ G x ≠ 0}.indicator (fun x => θ' x * ξ' x (β x)) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact (hθ'm.measurable.mul hξβm.measurable).indicator hSm
  -- a.e. facts on M
  have hθae : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ K → θ x = θ' x := by
    have : ∀ᵐ x ∂(((μHE[m + 1] : Measure (Eucl P)).restrict M).restrict K), θ x = θ' x := by
      rw [Measure.restrict_restrict hKm, inter_comm]; exact hθθ'
    exact (ae_restrict_iff' hKm).1 this
  have hunit : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) (m + 1), |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, -, hξx⟩ := hx
    exact unit_bound P (m + 1) τ (ξ x) hτ hξx
  refine ⟨g, hgm, ?_, ?_, ?_⟩
  · -- integrability
    have hθ'K : IntegrableOn θ' (M ∩ K) (μHE[m + 1] : Measure (Eucl P)) := hθK.congr_fun_ae hθθ'
    have hind : Integrable (K.indicator θ') ((μHE[m + 1] : Measure (Eucl P)).restrict M) := by
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
      exact hθ'K
    refine Integrable.mono' ((hind.norm).const_mul ((m + 1) * Cw)) hgm.aestronglyMeasurable ?_
    filter_upwards [hξξ', hunit] with x hξx hux
    by_cases hS : x ∈ K ∧ G x ≠ 0
    · rw [hg, indicator_of_mem (show x ∈ {x | x ∈ K ∧ G x ≠ 0} from hS), indicator_of_mem hS.1, norm_mul]
      have : ‖ξ' x (β x)‖ ≤ (m + 1) * Cw := by
        rw [← hξx, Real.norm_eq_abs]; exact (hux (β x)).trans (hβle x)
      calc ‖θ' x‖ * ‖ξ' x (β x)‖ ≤ ‖θ' x‖ * ((m + 1) * Cw) := by gcongr
        _ = (m + 1) * Cw * ‖θ' x‖ := by ring
    · rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from hS), norm_zero]
      have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans (hCw x)
      positivity
  · intro x hx
    rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from fun h => h.2 hx)]
  · filter_upwards [hξξ', hθae] with x hξx hθx
    have hcomp : (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))
          ((ω : DifferentialForm (Eucl P) m) x) = ξ x (β x) := by
      rw [hβ]; rfl
    have part1 : G x ≠ 0 → g x = θ x * ξ x (β x) := by
      intro hG0
      by_cases hxK : x ∈ K
      · rw [hg, indicator_of_mem (show x ∈ {x | x ∈ K ∧ G x ≠ 0} from ⟨hxK, hG0⟩), hθx hxK, hξx]
      · have hβ0 : β x = 0 := by
          have hsr : (innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight (0 : Covector (Eucl P) m) = 0 := by
            ext y; simp
          rw [hβ]
          simp only [hw0 x hxK, hsr]
          exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
        rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from fun h => hxK h.1), hβ0,
          map_zero, mul_zero]
    refine ⟨fun hG0 => by rw [hcomp]; exact part1 hG0, ?_⟩
    by_cases hG0 : G x = 0
    · have h0 : ContinuousAlternatingMap.alternatizeUncurryFin (0 : Eucl P →L[ℝ] Covector (Eucl P) m) = 0 :=
        map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
      simp [hG0, h0]
    · have hGν : G x = ‖G x‖ • (‖G x‖⁻¹ • G x) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0), one_smul]
      have hlin : ∀ (c : ℝ) (v : Eucl P) (α : Covector (Eucl P) m),
          (innerSL ℝ (c • v)).smulRight α = c • (innerSL ℝ v).smulRight α := by
        intro c v α
        ext y; simp [smul_smul]
      have hsm : (innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x) =
          ‖G x‖ • (innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x) := by
        rw [← hlin]
        congr 2
      have hβx : β x = ContinuousAlternatingMap.alternatizeUncurryFin
          ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by rw [hβ]
      rw [hsm, ContinuousAlternatingMap.alternatizeUncurryFin_smul, map_smul, smul_eq_mul, ← hβx,
        part1 hG0]
      ring
/-- Signed co-area identity on a level band (Simon Ch. 6, Remark 4.2): if the co-area formula
`∫ ∫_{M ∩ f⁻¹{t}} h dν dt = ∫_M |G| h dμ` holds for every Borel `h ≥ 0` and `|G| g` is
`μ⌞M`-integrable, then `t ↦ ∫_{M ∩ f⁻¹{t}} g dν` is integrable and
`∫_{M ∩ f⁻¹(a, b)} |G| g dμ = ∫_{(a, b)} ∫_{M ∩ f⁻¹{t}} g dν dt` (split `g = g⁺ - g⁻`). -/
theorem Submission.slicing_im_si_signed_coarea :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (g : Eucl P → ℝ), Measurable f → Measurable G → Measurable g → Integrable (fun x => ‖G x‖ * g x) (μ.restrict M) → (∀ h : Eucl P → ℝ≥0∞, Measurable h → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, h x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * h x ∂μ) → Integrable (fun t : ℝ => ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∀ a b : ℝ, ∫ x in M ∩ f ⁻¹' Ioo a b, ‖G x‖ * g x ∂μ = ∫ t in Ioo a b, (∫ x in M ∩ f ⁻¹' {t}, g x ∂ν) := by
  intro P μ ν M f G g hf hG hg hGg CA
  -- positive and negative parts `g⁺ = ofReal g`, `g⁻ = ofReal (-g)`
  have hgp : Measurable (fun x => ENNReal.ofReal (g x)) := ENNReal.measurable_ofReal.comp hg
  have hgn : Measurable (fun x => ENNReal.ofReal (-g x)) := ENNReal.measurable_ofReal.comp hg.neg
  obtain ⟨hφpm, hφp⟩ := CA _ hgp
  obtain ⟨hφnm, hφn⟩ := CA _ hgn
  have hprod : ∀ x, ‖G x‖ₑ * ENNReal.ofReal (g x) = ENNReal.ofReal (‖G x‖ * g x) := by
    intro x; rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  have hprodn : ∀ x, ‖G x‖ₑ * ENNReal.ofReal (-g x) = ENNReal.ofReal (-(‖G x‖ * g x)) := by
    intro x; rw [← mul_neg, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  -- both slice integrals of the parts have finite total integral, hence are a.e. finite
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
  -- band identity for a nonnegative Borel function: apply (CA) to `1_{f⁻¹(a, b)} h`
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
  -- subtract the finite parts on both sides
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGgE]
  simp_rw [← hprod, ← hprodn]
  rw [hpp, hnn]
  rw [integral_congr_ae (ae_restrict_of_ae hae)]
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hφpm hfinp).restrict
    (integrable_toReal_of_lintegral_ne_top hφnm hfinn).restrict]
  rw [integral_toReal hφpm.restrict (ae_restrict_of_ae hltp),
    integral_toReal hφnm.restrict (ae_restrict_of_ae hltn)]
/-- Transfer of an a.e. identity on `M` to almost every slice: if `μ`-null subsets `Z ⊆ M` have
`ν`-null slices `Z ∩ f⁻¹{t}` for a.e. `t`, `g = 0` off the Borel set `S` and `g = F` on `S`
`μ⌞M`-a.e., then `∫_{M ∩ f⁻¹{t}} g dν = ∫_{{x ∈ M : f x = t, x ∈ S}} F dν` for a.e. `t`
(Simon 4.5, slice identification). -/
theorem Submission.slicing_im_si_slice_ae_transfer :
    ∀ (P : ℕ) (μ ν : Measure (Eucl P)) (M S : Set (Eucl P)) (f g F : Eucl P → ℝ), NullMeasurableSet M μ → MeasurableSet S → Measurable f → (∀ Z : Set (Eucl P), Z ⊆ M → μ Z = 0 → ∀ᵐ t ∂(volume : Measure ℝ), ν (Z ∩ f ⁻¹' {t}) = 0) → (∀ x, x ∉ S → g x = 0) → (∀ᵐ x ∂(μ.restrict M), x ∈ S → g x = F x) → ∀ᵐ t ∂(volume : Measure ℝ), ∫ x in M ∩ f ⁻¹' {t}, g x ∂ν = ∫ x in {x | x ∈ M ∧ f x = t ∧ x ∈ S}, F x ∂ν := by
  intro P μ ν M S f g F hM hS hf hNT hg0 hgF
  -- A Borel `M₁ ⊆ M` with `μ(M \ M₁) = 0`; the bad set `Z₁ ∪ (M \ M₁) ⊆ M` is `μ`-null.
  obtain ⟨M₁, hM₁M, hM₁m, hM₁ae⟩ := hM.exists_measurable_subset_ae_eq
  have hZ₁ : μ ({x | ¬(x ∈ S → g x = F x)} ∩ M) = 0 :=
    le_antisymm ((Measure.le_restrict_apply M _).trans (ae_iff.1 hgF).le) (zero_le)
  have hZ₂ : μ (M \ M₁) = 0 := (ae_eq_set.1 hM₁ae).2
  have hZ : μ (({x | ¬(x ∈ S → g x = F x)} ∩ M) ∪ (M \ M₁)) = 0 := measure_union_null hZ₁ hZ₂
  -- For a.e. `t` the slice of the bad set is `ν`-null.
  filter_upwards [hNT _ (union_subset inter_subset_right sdiff_subset) hZ] with t ht
  have hft : MeasurableSet (f ⁻¹' {t}) := hf (measurableSet_singleton t)
  -- Both domains are `ν`-a.e. equal to Borel sets cut out by `M₁`.
  have hA : (M ∩ f ⁻¹' {t} : Set (Eucl P)) =ᵐ[ν] (M₁ ∩ f ⁻¹' {t} : Set (Eucl P)) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ ht
      intro x hx
      exact ⟨Or.inr ⟨hx.1.1, fun h => hx.2 ⟨h, hx.1.2⟩⟩, hx.1.2⟩
    · rw [sdiff_eq_empty.2 (inter_subset_inter_left _ hM₁M), measure_empty]
  have hB : ({x | x ∈ M ∧ f x = t ∧ x ∈ S} : Set (Eucl P)) =ᵐ[ν] (M₁ ∩ f ⁻¹' {t} ∩ S : Set (Eucl P)) := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ ht
      rintro x ⟨⟨hxM, hxt, hxS⟩, hx⟩
      refine ⟨Or.inr ⟨hxM, fun h => hx ⟨⟨h, hxt⟩, hxS⟩⟩, hxt⟩
    · have : (M₁ ∩ f ⁻¹' {t} ∩ S : Set (Eucl P)) \ {x | x ∈ M ∧ f x = t ∧ x ∈ S} = ∅ := by
        ext x
        simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact h2 (hM₁M h1.1.1) h1.1.2 h1.2
      rw [this, measure_empty]
  rw [Measure.restrict_congr_set hA, Measure.restrict_congr_set hB]
  -- `g = 1_S g`, so the left side is the integral of `g` over `M₁ ∩ f⁻¹{t} ∩ S`.
  have hgS : (fun x => g x) = S.indicator g := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hg0 x hx]
  rw [show (∫ x in M₁ ∩ f ⁻¹' {t}, g x ∂ν) = ∫ x in M₁ ∩ f ⁻¹' {t}, S.indicator g x ∂ν by
    rw [← hgS], setIntegral_indicator hS]
  -- On this Borel set `g = F` off the `ν`-null slice of the bad set.
  apply setIntegral_congr_ae ((hM₁m.inter hft).inter hS)
  rw [ae_iff]
  refine measure_mono_null ?_ ht
  intro x hx
  simp only [mem_ofPred_eq, Classical.not_imp] at hx
  obtain ⟨⟨⟨hxM₁, hxt⟩, hxS⟩, hne⟩ := hx
  exact ⟨Or.inl ⟨fun h => hne (h hxS), hM₁M hxM₁⟩, hxt⟩
/-- One-sided Lebesgue points: for locally integrable `φ : ℝ → ℝ` and a.e. `t`, the left averages
`ε⁻¹ ∫_{(t - ε, t)} φ` tend to `φ t` as `ε → 0+` (Lebesgue differentiation along the Vitali
family of `volume`; Simon Ch. 6, Remark 4.2 and the proof of 4.5(2)). -/
theorem Submission.slicing_im_si_left_lebesgue_point :
    ∀ φ : ℝ → ℝ, LocallyIntegrable φ (volume : Measure ℝ) → ∀ᵐ t ∂(volume : Measure ℝ), Tendsto (fun ε : ℝ => ε⁻¹ * ∫ r in Ioo (t - ε) t, φ r) (𝓝[>] 0) (𝓝 (φ t)) := by
  intro φ hφ
  -- Lebesgue differentiation along the Vitali family of `volume`, restricted to left intervals.
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average hφ]
    with t ht
  have hleft := ht.comp (Real.tendsto_Icc_vitaliFamily_left t)
  -- `ε ↦ t - ε` maps `𝓝[>] 0` to `𝓝[<] t`.
  have hsub : Tendsto (fun ε : ℝ => t - ε) (𝓝[>] 0) (𝓝[<] t) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => t - ε) (𝓝 0) (𝓝 (t - 0)) := tendsto_const_nhds.sub tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp only [mem_Iio]; linarith
  -- For `ε > 0` the average over `Icc (t - ε) t` is `ε⁻¹ ∫_{(t - ε, t)} φ`.
  refine (hleft.comp hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp_apply, average, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioo, show t - (t - ε) = ε by ring,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hε.le, smul_eq_mul]
/-- Tangential gradient of the level cut-off `h_ε = ψ ∘ f`, `ψ(s) = max(0, min(1, (t - s)/ε))`:
`h_ε` is Lipschitz and, wherever `G` is a tangential gradient of `f` vanishing on the level sets
`{f = t - ε}` and `{f = t}`, `G_ε = 1_{t - ε < f < t} · (-ε⁻¹ G)` is a bounded Borel tangential
gradient of `h_ε` (Simon Ch. 6, proof of 4.5(2)). -/
theorem Submission.slicing_im_si_cutoff_tangential_gradient :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (Tan : Eucl P → Submodule ℝ (Eucl P) → Prop) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P) (t ε : ℝ), 0 < ε → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → (∀ᵐ x ∂μ, f x = t - ε → G x = 0) → (∀ᵐ x ∂μ, f x = t → G x = 0) → ∃ K : ℝ≥0, LipschitzWith K (fun x => max 0 (min 1 ((t - f x) / ε))) ∧ Measurable ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) ∧ (∀ x, ‖(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x‖ ≤ K) ∧ ∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → (f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => max 0 (min 1 ((t - f (x + s • u)) / ε))) (inner ℝ ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x) u) 0 := by
  intro P μ Tan f L G t ε hε hf hG hGL hTG h1 h2
  set ψ : ℝ → ℝ := fun s => max 0 (min 1 ((t - s) / ε)) with hψdef
  set Kψ : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.2 hε.le⟩ with hKψ
  -- `ψ` is `ε⁻¹`-Lipschitz: an affine map of slope `-ε⁻¹`, clamped to `[0, 1]`.
  have hψL : LipschitzWith Kψ ψ := by
    have hlin : LipschitzWith Kψ (fun s : ℝ => (t - s) / ε) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, Real.dist_eq, show (t - a) / ε - (t - b) / ε = ε⁻¹ * (b - a) by ring,
        abs_mul, abs_of_pos (inv_pos.2 hε), abs_sub_comm]
      rfl
    exact (hlin.const_min 1).const_max 0
  have hfm : Measurable f := hf.continuous.measurable
  set E : Set (Eucl P) := f ⁻¹' Ioo (t - ε) t with hEdef
  have hE : MeasurableSet E := hfm measurableSet_Ioo
  refine ⟨Kψ * L, hψL.comp hf, (hG.const_smul (-ε⁻¹)).indicator hE, fun x => ?_, ?_⟩
  · -- `‖G_ε x‖ ≤ ε⁻¹ L`
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.2 hε)]
      simp only [hKψ]
      exact mul_le_mul_of_nonneg_left (hGL x) (inv_nonneg.2 hε.le)
    · rw [indicator_of_notMem hx, norm_zero]
      exact NNReal.coe_nonneg _
  · filter_upwards [hTG, h1, h2] with x hx hx1 hx2
    intro Q hQ
    obtain ⟨hGQ, hder⟩ := hx Q hQ
    constructor
    · by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]; exact Q.smul_mem _ hGQ
      · rw [indicator_of_notMem hxE]; exact Q.zero_mem
    intro u hu
    have hd := hder u hu
    have hc : ContinuousAt (fun s : ℝ => f (x + s • u)) 0 := hd.continuousAt
    -- the cut-off composed with the line
    change HasDerivAt (fun s => ψ (f (x + s • u))) _ 0
    -- at points where `G x = 0` the Lipschitz bound gives derivative `0`
    have edge : G x = 0 → HasDerivAt (fun s : ℝ => ψ (f (x + s • u))) 0 (0 : ℝ) := by
      intro hG0
      rw [hG0, inner_zero_left] at hd
      rw [hasDerivAt_iff_isLittleO] at hd ⊢
      simp only [sub_zero, smul_zero] at hd ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
      refine Asymptotics.IsBigO.of_bound (Kψ : ℝ) (Eventually.of_forall fun s => ?_)
      have := hψL.dist_le_mul (f (x + s • u)) (f (x + (0 : ℝ) • u))
      simpa [Real.dist_eq, Real.norm_eq_abs] using this
    -- case analysis on the position of `f x`
    rcases lt_trichotomy (f x) (t - ε) with hlt | heq | hgt
    · -- below the band: locally constant `1`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t - ε := by
        have := hc.eventually_lt (continuousAt_const (y := t - ε)) (by simpa using hlt)
        simpa using this
      apply (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hev] with s hs
      have : 1 ≤ (t - f (x + s • u)) / ε := by rw [le_div_iff₀ hε]; linarith
      simp only [hψdef, min_eq_left this, max_eq_right zero_le_one]
    · -- lower edge: `G x = 0`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      exact edge (hx1 heq)
    · rcases lt_trichotomy (f x) t with hlt' | heq' | hgt'
      · -- inside the band: affine with slope `-1/ε`
        have hxE : x ∈ E := by simp [hEdef]; exact ⟨hgt, hlt'⟩
        rw [indicator_of_mem hxE, real_inner_smul_left]
        have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), t - ε < f (x + s • u) := by
          have := (continuousAt_const (y := t - ε)).eventually_lt hc (by simpa using hgt)
          simpa using this
        have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t := by
          have := hc.eventually_lt (continuousAt_const (y := t)) (by simpa using hlt')
          simpa using this
        have hlin : HasDerivAt (fun s : ℝ => (t - f (x + s • u)) / ε)
            (-ε⁻¹ * inner ℝ (G x) u) 0 := by
          have := (hd.const_sub t).div_const ε
          convert this using 1
          field_simp
        apply hlin.congr_of_eventuallyEq
        filter_upwards [hev1, hev2] with s hs1 hs2
        have ha : (t - f (x + s • u)) / ε ≤ 1 := by rw [div_le_iff₀ hε]; linarith
        have hb : 0 ≤ (t - f (x + s • u)) / ε := div_nonneg (by linarith) hε.le
        simp only [hψdef, min_eq_right ha, max_eq_right hb]
      · -- upper edge: `G x = 0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        exact edge (hx2 heq')
      · -- above the band: locally constant `0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        have hev : ∀ᶠ s in 𝓝 (0 : ℝ), t < f (x + s • u) := by
          have := (continuousAt_const (y := t)).eventually_lt hc (by simpa using hgt')
          simpa using this
        apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hev] with s hs
        have : (t - f (x + s • u)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
        simp only [hψdef, max_eq_left ((min_le_right _ _).trans this)]
/-- Level cut-offs converge to the indicator of `{x ∈ U : f x < t}` under the integral: for
`χ_h = 1` on `(-∞, t - h]`, `χ_h = 0` on `[t, ∞)` and `|χ_h| ≤ 1`,
`∫ χ_h(f) F dν → ∫_{x ∈ U, f x < t} F dν` as `h → 0+` (dominated convergence; Simon 4.11). -/
theorem Submission.slicing_mb_pointwise_cutoff_tendsto :
    ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ (ν : Measure (Eucl P)) (F : Eucl P → ℝ), Integrable F ν → (∀ x, x ∉ U → F x = 0) → ∀ (t : ℝ) (χ : ℝ → ℝ → ℝ), (∀ h : ℝ, 0 < h → Measurable (χ h)) → (∀ h s : ℝ, 0 < h → |χ h s| ≤ 1) → (∀ h s : ℝ, 0 < h → s ≤ t - h → χ h s = 1) → (∀ h s : ℝ, 0 < h → t ≤ s → χ h s = 0) → Tendsto (fun h : ℝ => ∫ x, χ h (f x) * F x ∂ν) (𝓝[>] 0) (𝓝 (∫ x in {x | x ∈ U ∧ f x < t}, F x ∂ν)) := by
  intro P U hU f L hf ν F hF hF0 t χ hχm hχb hχ1 hχ0
  -- McShane extension `g` of `f|U`: globally Lipschitz, hence continuous.
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have hgc : Continuous g := hg.continuous
  -- The limit set `A = U ∩ g⁻¹(-∞, t)` is open, so the set integral is an indicator integral.
  set A : Set (Eucl P) := {x | x ∈ U ∧ f x < t} with hA
  have hAeq : A = U ∩ g ⁻¹' Iio t := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, show g x < t from hfg hx ▸ hfx⟩
    · rintro ⟨hx, hgx⟩
      exact ⟨hx, show f x < t from (hfg hx).symm ▸ hgx⟩
  have hAm : MeasurableSet A := by
    rw [hAeq]
    exact (hU.inter (isOpen_Iio.preimage hgc)).measurableSet
  rw [← integral_indicator hAm]
  -- Off `U` we have `F = 0`, so `f` may be replaced by `g` inside the integrand.
  have hfg' : ∀ h x, χ h (f x) * F x = χ h (g x) * F x := by
    intro h x
    by_cases hx : x ∈ U
    · rw [hfg hx]
    · simp [hF0 x hx]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hF.norm ?_
  · -- measurability for `h > 0`
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    have : (fun x => χ h (f x) * F x) = fun x => χ h (g x) * F x := funext (hfg' h)
    rw [this]
    exact ((hχm h hh).comp hgc.measurable).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · -- domination by `‖F‖` for `h > 0`
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs (χ h (f x))]
    calc |χ h (f x)| * ‖F x‖ ≤ 1 * ‖F x‖ := by gcongr; exact hχb h _ hh
      _ = ‖F x‖ := one_mul _
  · -- pointwise convergence at every `x`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ U
    · by_cases hft : f x < t
      · rw [indicator_of_mem (show x ∈ A from ⟨hx, hft⟩)]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hft)] with h hh
        rw [hχ1 h (f x) hh.1 (by linarith [hh.2]), one_mul]
      · rw [indicator_of_notMem (show x ∉ A from fun h => hft h.2)]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
        rw [hχ0 h (f x) hh (not_lt.mp hft), zero_mul]
    · rw [indicator_of_notMem (show x ∉ A from fun h => hx h.1), hF0 x hx]
      simp
/-- A `C¹` function `h` on `ℝⁿ` is `ε`-Lipschitz on each piece of a countable Borel partition of
a Borel set `E` on which `Dh = 0`.  Continuity of `Dh` gives balls `B(w, r w)`, `w ∈ E`, with
`‖Dh‖₊ < ε`, on which `h` is `ε`-Lipschitz by the mean value inequality; countably many of them
cover `E` (Lindelöf), and `D k = E ∩ disjointed B k` disjointifies this cover. -/
theorem Submission.slicing_im_coarea_cc_small_lip_partition :
    ∀ (n : ℕ) (h : Eucl n → ℝ) (E : Set (Eucl n)) (ε : ℝ≥0), ContDiff ℝ 1 h → MeasurableSet E →
      (∀ w ∈ E, fderiv ℝ h w = 0) → 0 < ε →
      ∃ D : ℕ → Set (Eucl n), (∀ k, MeasurableSet (D k)) ∧ Pairwise (Function.onFun Disjoint D) ∧
        (⋃ k, D k) = E ∧ ∀ k, LipschitzOnWith ε h (D k) := by
  intro n h E ε hh hE hE0 hε
  -- `h` is differentiable and `z ↦ ‖Dh z‖₊` is continuous.
  have hdiff : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hcont : Continuous fun z => ‖fderiv ℝ h z‖₊ := (hh.continuous_fderiv one_ne_zero).nnnorm
  -- Good radii: since `Dh w = 0`, `‖Dh‖₊ < ε` on a ball `B(w, r w)` for every `w ∈ E`.
  have hrad : ∀ w ∈ E, ∃ r > 0, ∀ z ∈ ball w r, ‖fderiv ℝ h z‖₊ < ε := fun w hw =>
    Metric.eventually_nhds_iff_ball.1 <|
      (hcont.tendsto' w 0 (by simp [hE0 w hw])).eventually (gt_mem_nhds hε)
  choose! r hr0 hr using hrad
  -- Mean value inequality on the convex balls: `h` is `ε`-Lipschitz on each of them.
  have hlip : ∀ w ∈ E, LipschitzOnWith ε h (ball w (r w)) := fun w hw =>
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun z _ => hdiff z)
      (fun z hz => (hr w hw z hz).le) (convex_ball w (r w))
  -- Lindelöf: the balls centred at the points of a countable `T ⊆ E` cover `E`.
  obtain ⟨T, hTE, hTc, hET⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun w => ball w (r w)) fun w hw => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds w (hr0 w hw))
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- No ball is needed, so `E = ∅` and `D k = ∅` works.
    have hE' : E = ∅ := by simpa using hET
    exact ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun _ _ _ => disjoint_bot_left,
      by simp [hE'], fun _ => lipschitzOnWith_empty ε h⟩
  · -- Enumerate the balls `B k = B(w k, r (w k))` and set `D k = E ∩ disjointed B k`.
    obtain ⟨w, rfl⟩ := hTc.exists_eq_range hTne
    rw [biUnion_range] at hET
    refine ⟨fun k => E ∩ disjointed (fun j => ball (w j) (r (w j))) k,
      fun k => hE.inter (MeasurableSet.disjointed (fun _ => measurableSet_ball) k),
      (disjoint_disjointed _).mono fun _ _ hij =>
        Disjoint.mono inter_subset_right inter_subset_right hij,
      ?_, fun k => (hlip (w k) (hTE (mem_range_self k))).mono
        (inter_subset_right.trans (disjointed_subset _ k))⟩
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left]
    exact hET
/-- Slices of `S` are `ν`-null for a.e. level if `S` admits countable covers with measurable
majorants of arbitrarily small total integral: if for every `ε > 0` there are `A k` covering `S`
and measurable `φ k` with `ν (A k ∩ f ⁻¹' {t}) ≤ φ k t` and `∑' k, ∫⁻ φ k ≤ ε * M` (`M ≠ ∞`), then
`ν (S ∩ f ⁻¹' {t}) = 0` for a.e. `t`.  For `ε_j = 1 / (j + 1)`, `g = ⨅ j, ∑' k, φ_j k` is a
measurable majorant of `t ↦ ν (S ∩ f ⁻¹' {t})` with `∫⁻ g ≤ ε_j * M → 0`, so `g = 0` a.e. -/
theorem Submission.slicing_im_coarea_cc_null_of_small_majorants :
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (f : X → ℝ) (S : Set X) (M : ℝ≥0∞),
      M ≠ ∞ → (∀ ε : ℝ≥0, 0 < ε → ∃ (A : ℕ → Set X) (φ : ℕ → ℝ → ℝ≥0∞),
        S ⊆ ⋃ k, A k ∧ (∀ k, Measurable (φ k)) ∧ (∀ k t, ν (A k ∩ f ⁻¹' {t}) ≤ φ k t) ∧
          ∑' k, ∫⁻ t, φ k t ≤ (ε : ℝ≥0∞) * M) →
      ∀ᵐ t ∂(volume : Measure ℝ), ν (S ∩ f ⁻¹' {t}) = 0 := by
  intro X _ ν f S M hM h
  -- For `ε_j = 1 / (j + 1)` choose covers `A j k` of `S` and majorants `φ j k`.
  choose A φ hSA hφ hle hsum using fun j : ℕ => h (1 / ((j : ℝ≥0) + 1)) (by positivity)
  -- `ψ_j = ∑' k, φ j k` is measurable and majorizes `t ↦ ν (S ∩ f ⁻¹' {t})` by countable
  -- subadditivity, since `S ∩ f ⁻¹' {t} ⊆ ⋃ k, A j k ∩ f ⁻¹' {t}`.
  have hψ : ∀ j, Measurable fun t => ∑' k, φ j k t := fun j => Measurable.tsum (hφ j)
  have hFψ : ∀ j t, ν (S ∩ f ⁻¹' {t}) ≤ ∑' k, φ j k t := by
    intro j t
    calc ν (S ∩ f ⁻¹' {t}) ≤ ν (⋃ k, A j k ∩ f ⁻¹' {t}) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨k, hk⟩ := mem_iUnion.1 (hSA j hx.1)
          exact mem_iUnion.2 ⟨k, hk, hx.2⟩
      _ ≤ ∑' k, ν (A j k ∩ f ⁻¹' {t}) := measure_iUnion_le _
      _ ≤ ∑' k, φ j k t := ENNReal.tsum_le_tsum fun k => hle j k t
  -- Monotone convergence: `∫⁻ ψ_j = ∑' k, ∫⁻ φ j k ≤ ε_j * M`.
  have hψint : ∀ j, ∫⁻ t, ∑' k, φ j k t ≤ ((1 / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) * M := by
    intro j
    rw [lintegral_tsum fun k => (hφ j k).aemeasurable]
    exact hsum j
  -- `g = ⨅ j, ψ_j` is a measurable majorant with `∫⁻ g ≤ ε_j * M` for every `j`.
  have hg : Measurable fun t => ⨅ i, ∑' k, φ i k t := Measurable.iInf hψ
  have hgint : ∀ j : ℕ, ∫⁻ t, ⨅ i, ∑' k, φ i k t ≤ ((1 / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) * M :=
    fun j => (lintegral_mono fun t => iInf_le _ j).trans (hψint j)
  -- `ε_j * M → 0` because `M ≠ ∞`, so `∫⁻ g = 0`.
  have htend : Tendsto (fun j : ℕ => ((1 / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) * M) atTop (𝓝 0) := by
    have h0 : Tendsto (fun j : ℕ => ((1 / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
      rw [← ENNReal.coe_zero]
      exact ENNReal.tendsto_coe.2 tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const h0 (Or.inr hM)
  have hg0 : ∫⁻ t, ⨅ i, ∑' k, φ i k t = 0 := le_antisymm (ge_of_tendsto' htend hgint) bot_le
  -- Hence `g = 0` a.e., and `ν (S ∩ f ⁻¹' {t}) ≤ g t` gives the claim.
  filter_upwards [(lintegral_eq_zero_iff hg).1 hg0] with t ht
  exact le_antisymm ((le_iInf fun j => hFψ j t).trans_eq ht) bot_le
/-- Near-optimal covers for `μH[d]` (`d ≥ 0`, `μH[d] A < ∞`): for `r, ε > 0`, `A` is covered by
sets `S i ⊆ A` of diameter `≤ r` with `∑ᵢ (diam S i)^d ≤ μH[d] A + ε`, empty pieces counting `0`.
By `hausdorffMeasure_apply` the `r`-content of `A` is `≤ μH[d] A < μH[d] A + ε`, so some cover
`t` beats `μH[d] A + ε`; its traces `t i ∩ A` keep the cover and only shrink diameters. -/
theorem Submission.slicing_im_coarea_eil_near_optimal_cover :
    ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (d : ℝ) (A : Set X) (r ε : ℝ≥0∞), 0 ≤ d → 0 < r → 0 < ε → (μH[d] : Measure X) A ≠ ∞ → ∃ S : ℕ → Set X, (∀ i, S i ⊆ A) ∧ A ⊆ ⋃ i, S i ∧ (∀ i, ediam (S i) ≤ r) ∧ ∑' i, ⨆ (_ : (S i).Nonempty), ediam (S i) ^ d ≤ (μH[d] : Measure X) A + ε := by
  intro X _ _ _ d A r ε hd hr hε hA
  -- The `r`-content of `A` is at most `μH[d] A`, hence strictly below `μH[d] A + ε`.
  have hlt : (⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) < (μH[d] : Measure X) A + ε := by
    refine lt_of_le_of_lt ?_ (ENNReal.lt_add_right hA hε.ne')
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂ (f := fun ρ (_ : 0 < ρ) => ⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n)
      (_ : ∀ n, ediam (t n) ≤ ρ), ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) r hr
  -- So some cover `t` of `A` by sets of diameter `≤ r` has sum below `μH[d] A + ε`.
  simp only [iInf_lt_iff] at hlt
  obtain ⟨t, hAt, htr, hsum⟩ := hlt
  -- Its traces `t i ∩ A` on `A` still cover `A`, have diameter `≤ r` and smaller terms
  -- (`x ↦ x ^ d` is monotone as `d ≥ 0`; an empty trace contributes `0`).
  refine ⟨fun i => t i ∩ A, fun i => inter_subset_right, fun x hx => ?_, fun i => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hAt hx)
    exact mem_iUnion.2 ⟨i, hi, hx⟩
  · exact (ediam_mono inter_subset_left).trans (htr i)
  · refine le_trans (ENNReal.tsum_le_tsum fun i => iSup_le fun hne => ?_) hsum.le
    exact le_iSup_of_le (hne.mono inter_subset_left)
      (ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) hd)
/-- Simon Ch. 6, §4 (Eilenberg's inequality in the coarea step): if for every `k` the sets
`T k i` (`i ∈ ℕ`) cover `s` and have diameter `≤ r k`, where `r k → 0`, then
`μH[d](s) ≤ liminf_k ∑ᵢ (ediam T k i)^d`, empty pieces contributing `0`.  Reindexing the `k`-th
cover by its nonempty pieces `{i // (T k i).Nonempty}` (a countable type) keeps a cover of `s`
with the same diameter bound, so Mathlib's `hausdorffMeasure_le_liminf_tsum` bounds `μH[d](s)` by
the liminf of the reindexed sums; each reindexed sum is at most the sum over all `i`. -/
theorem Submission.slicing_im_coarea_eil_liminf_cover_bound :
    ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (d : ℝ) (s : Set X) (r : ℕ → ℝ≥0∞) (T : ℕ → ℕ → Set X), Tendsto r atTop (𝓝 0) → (∀ k i, ediam (T k i) ≤ r k) → (∀ k, s ⊆ ⋃ i, T k i) → (μH[d] : Measure X) s ≤ liminf (fun k => ∑' i, ⨆ (_ : (T k i).Nonempty), ediam (T k i) ^ d) atTop := by
  intro X _ _ _ d s r T hr hT hs
  calc (μH[d] : Measure X) s
      ≤ liminf (fun k => ∑' j : {i // (T k i).Nonempty}, ediam (T k j) ^ d) atTop :=
        Measure.hausdorffMeasure_le_liminf_tsum (ι := fun k => {i // (T k i).Nonempty}) d s r hr
          (fun k j => T k j) (.of_forall fun k j => hT k j) (.of_forall fun k x hx => by
            -- a piece containing `x` is nonempty
            obtain ⟨i, hi⟩ := mem_iUnion.1 (hs k hx)
            exact mem_iUnion.2 ⟨⟨i, x, hi⟩, hi⟩)
    _ ≤ liminf (fun k => ∑' i, ⨆ (_ : (T k i).Nonempty), ediam (T k i) ^ d) atTop :=
        liminf_le_liminf (.of_forall fun k =>
          (ENNReal.tsum_le_tsum fun j => le_iSup_of_le j.2 le_rfl).trans
            (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
              fun i => ⨆ (_ : (T k i).Nonempty), ediam (T k i) ^ d))
/-- If `f` is `L`-Lipschitz on `A` and `S i ⊆ A`, a Borel `ψ : ℝ → [0, ∞]` majorizes the slice
sums `∑ᵢ (ediam (S i ∩ A ∩ f⁻¹{t}))^m` over nonempty pieces, with
`∫ ψ ≤ 2 L ∑ᵢ (ediam (S i))^(m+1)` (empty `S i` omitted).  Pick `a i = f xᵢ` with `xᵢ ∈ S i`
(any `a i` if `S i = ∅`), so `f (S i) ⊆ Iᵢ := closedEBall (a i) (L · ediam (S i))`, and take
`ψ = ∑ᵢ cᵢ 1_{Iᵢ}`, `cᵢ = (ediam (S i))^m` (`0` if `S i = ∅`): a nonempty piece
`S i ∩ (A ∩ f⁻¹{t}) ∋ y` forces `t = f y ∈ Iᵢ`, and `λ¹(Iᵢ) = 2 L ediam (S i)`
(`Real.volume_closedEBall`). -/
theorem Submission.slicing_im_coarea_eil_cover_majorant :
    ∀ (X : Type) [EMetricSpace X] (m : ℕ) (f : X → ℝ) (L : ℝ≥0) (A : Set X) (S : ℕ → Set X),
      LipschitzOnWith L f A → (∀ i, S i ⊆ A) →
      ∃ ψ : ℝ → ℝ≥0∞, Measurable ψ ∧
        (∀ t : ℝ, ∑' i, ⨆ (_ : (S i ∩ (A ∩ f ⁻¹' {t})).Nonempty),
          ediam (S i ∩ (A ∩ f ⁻¹' {t})) ^ (m : ℝ) ≤ ψ t) ∧
        ∫⁻ t, ψ t ≤ 2 * (L : ℝ≥0∞) *
          ∑' i, ⨆ (_ : (S i).Nonempty), ediam (S i) ^ ((m + 1 : ℕ) : ℝ) := by
  intro X _ m f L A S hf hSA
  -- Centres: `edist (f y) (a i) ≤ L · ediam (S i)` for `y ∈ S i` (`a i = f xᵢ` with `xᵢ ∈ S i`).
  have hcen : ∀ i, ∃ a : ℝ, ∀ y ∈ S i, edist (f y) a ≤ L * ediam (S i) := by
    intro i
    rcases (S i).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · exact ⟨0, by simp [h]⟩
    · exact ⟨f x, fun y hy => (hf (hSA i hy) (hSA i hx)).trans
        (mul_le_mul_right (edist_le_ediam_of_mem hy hx) _)⟩
  choose a ha using hcen
  have hI : ∀ i, MeasurableSet (closedEBall (a i) (L * ediam (S i))) :=
    fun i => isClosed_closedEBall.measurableSet
  refine ⟨fun t => ∑' i, (closedEBall (a i) (L * ediam (S i))).indicator
      (fun _ => ⨆ (_ : (S i).Nonempty), ediam (S i) ^ (m : ℝ)) t,
    Measurable.tsum fun i => measurable_const.indicator (hI i), fun t => ?_, ?_⟩
  · -- A nonempty slice piece `S i ∩ (A ∩ f⁻¹{t}) ∋ y` gives `t = f y ∈ Iᵢ`.
    refine ENNReal.tsum_le_tsum fun i => iSup_le fun ⟨y, hyS, _, hyt⟩ => ?_
    have htI : t ∈ closedEBall (a i) (L * ediam (S i)) := by
      rw [mem_closedEBall, ← show f y = t from hyt]
      exact ha i y hyS
    rw [indicator_of_mem htI]
    exact le_iSup_of_le ⟨y, hyS⟩
      (ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) (Nat.cast_nonneg m))
  · -- `∫ ψ = ∑ᵢ cᵢ λ¹(Iᵢ)` and `cᵢ λ¹(Iᵢ) = 2 L (ediam (S i))^(m+1)` for `S i ≠ ∅`.
    rw [lintegral_tsum fun i => (measurable_const.indicator (hI i)).aemeasurable,
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [lintegral_indicator_const (hI i), Real.volume_closedEBall]
    rcases (S i).eq_empty_or_nonempty with h | h
    · simp [h]
    · simp only [iSup_pos h, ENNReal.rpow_natCast]
      exact le_of_eq (by ring)

/-- Eilenberg's inequality for the unnormalized Hausdorff measures on an extended metric space:
if `f : X → ℝ` is `L`-Lipschitz on `A`, some Borel `ψ` majorizes `t ↦ μH[m](A ∩ f⁻¹{t})` with
`∫ ψ ≤ 2 L μH[m+1](A)`.  For `L = 0` take `∞ · 1_{f(A)}` (`f(A)` has at most one point), and for
`μH[m+1](A) = ∞` the constant `∞`.  Otherwise `ψ = liminf_k ψ_k`, where `ψ_k` is the majorant
(`slicing_im_coarea_eil_cover_majorant`) of a near-optimal cover of `A` at scale `(k + 1)⁻¹`
(`slicing_im_coarea_eil_near_optimal_cover`): the pointwise bound is
`slicing_im_coarea_eil_liminf_cover_bound` and the integral bound is Fatou's lemma. -/
theorem Submission.slicing_im_coarea_eil_unnormalized : ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (f : X → ℝ) (L : ℝ≥0) (A : Set X), LipschitzOnWith L f A → ∃ ψ : ℝ → ℝ≥0∞, Measurable ψ ∧ (∀ t : ℝ, (μH[(m : ℝ)] : Measure X) (A ∩ f ⁻¹' {t}) ≤ ψ t) ∧ ∫⁻ t, ψ t ≤ 2 * (L : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure X) A := by
  intro X _ _ _ m f L A hf
  -- `L = 0`: `f` is constant on `A`, so `∞ · 1_{f(A)}` works (`f(A)` is countable, hence null).
  rcases eq_or_ne L 0 with rfl | hL
  · have hc : (f '' A).Countable := Set.Subsingleton.countable <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa using hf hx hy
    refine ⟨(f '' A).indicator fun _ => ∞, measurable_const.indicator hc.measurableSet,
      fun t => ?_, ?_⟩
    · by_cases ht : t ∈ f '' A
      · simp [indicator_of_mem ht]
      · have h : A ∩ f ⁻¹' {t} = ∅ :=
          eq_empty_of_forall_notMem fun x hx => ht ⟨x, hx.1, hx.2⟩
        simp [h]
    · rw [lintegral_indicator_const hc.measurableSet, hc.measure_zero, mul_zero]
      exact zero_le
  have h2L : 2 * (L : ℝ≥0∞) ≠ 0 := mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.2 hL)
  -- `μH[m+1](A) = ∞`: the constant `∞` works.
  by_cases hA : (μH[((m + 1 : ℕ) : ℝ)] : Measure X) A = ∞
  · refine ⟨fun _ => ∞, measurable_const, fun _ => le_top, ?_⟩
    rw [hA, ENNReal.mul_top h2L]
    exact le_top
  -- Scales `ρ_k = (k + 1)⁻¹ → 0`.
  obtain ⟨ρ, hρpos, hρlim⟩ : ∃ ρ : ℕ → ℝ≥0∞, (∀ k, 0 < ρ k) ∧ Tendsto ρ atTop (𝓝 0) :=
    ⟨fun k => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹, fun k => ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _),
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)⟩
  -- Near-optimal covers `S k` of `A` at scale `ρ k` and their majorants `φ k`.
  choose S hSA hAS hSd hSsum using fun k =>
    Submission.slicing_im_coarea_eil_near_optimal_cover X ((m + 1 : ℕ) : ℝ) A (ρ k) (ρ k)
      (Nat.cast_nonneg _) (hρpos k) (hρpos k) hA
  choose φ hφm hφt hφi using fun k =>
    Submission.slicing_im_coarea_eil_cover_majorant X m f L A (S k) hf (hSA k)
  refine ⟨fun t => liminf (fun k => φ k t) atTop, Measurable.liminf hφm, fun t => ?_, ?_⟩
  · -- The pieces `S k i ∩ (A ∩ f⁻¹{t})` cover the level set at scale `ρ k`.
    calc (μH[(m : ℝ)] : Measure X) (A ∩ f ⁻¹' {t})
        ≤ liminf (fun k => ∑' i, ⨆ (_ : (S k i ∩ (A ∩ f ⁻¹' {t})).Nonempty),
            ediam (S k i ∩ (A ∩ f ⁻¹' {t})) ^ (m : ℝ)) atTop :=
          Submission.slicing_im_coarea_eil_liminf_cover_bound X (m : ℝ) (A ∩ f ⁻¹' {t}) ρ
            (fun k i => S k i ∩ (A ∩ f ⁻¹' {t})) hρlim
            (fun k i => (ediam_mono inter_subset_left).trans (hSd k i))
            (fun k x hx => by
              obtain ⟨i, hi⟩ := mem_iUnion.1 (hAS k hx.1)
              exact mem_iUnion.2 ⟨i, hi, hx⟩)
      _ ≤ liminf (fun k => φ k t) atTop := liminf_le_liminf (.of_forall fun k => hφt k t)
  · -- Fatou, then `2L (μH[m+1](A) + ρ k) → 2L μH[m+1](A)`.
    have hlim : Tendsto (fun k => 2 * (L : ℝ≥0∞) *
        ((μH[((m + 1 : ℕ) : ℝ)] : Measure X) A + ρ k)) atTop
        (𝓝 (2 * (L : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure X) A)) := by
      have h := ENNReal.Tendsto.const_mul (a := 2 * (L : ℝ≥0∞))
        (hρlim.const_add ((μH[((m + 1 : ℕ) : ℝ)] : Measure X) A))
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top))
      rwa [add_zero] at h
    calc ∫⁻ t, liminf (fun k => φ k t) atTop
        ≤ liminf (fun k => ∫⁻ t, φ k t) atTop := lintegral_liminf_le hφm
      _ ≤ liminf (fun k => 2 * (L : ℝ≥0∞) *
            ((μH[((m + 1 : ℕ) : ℝ)] : Measure X) A + ρ k)) atTop :=
          liminf_le_liminf (.of_forall fun k => (hφi k).trans (by gcongr; exact hSsum k))
      _ = 2 * (L : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure X) A := hlim.liminf_eq

/-- Eilenberg's inequality for a real-valued Lipschitz function (Federer 2.10.25 with target `ℝ`),
for the normalized `Hᵏ = μHE[k]`: if `f` is `L`-Lipschitz on `A ⊆ ℝ^P`, some Borel `φ` majorizes
`t ↦ Hᵐ(A ∩ f⁻¹{t})` with `∫ φ ≤ C(m) L Hᵐ⁺¹(A)`.  With `κ_d` the scalar of
`μHE[d] = κ_d • μH[d]` (`euclideanHausdorffMeasure_def`; it does not depend on the space and
`κ_{m+1} ≠ 0`), take `C = 2 κ_m / κ_{m+1}` and `φ = κ_m ψ`, where `ψ` is the majorant for the
unnormalized `μH` with constant `2` (`slicing_im_coarea_eil_unnormalized`). -/
theorem Submission.slicing_im_coarea_eilenberg : ∀ m : ℕ, ∃ C : ℝ≥0, ∀ (P : ℕ) (f : Eucl P → ℝ) (L : ℝ≥0) (A : Set (Eucl P)), LipschitzOnWith L f A → ∃ φ : ℝ → ℝ≥0∞, Measurable φ ∧ (∀ t : ℝ, (μHE[m] : Measure (Eucl P)) (A ∩ f ⁻¹' {t}) ≤ φ t) ∧ ∫⁻ t, φ t ≤ (C : ℝ≥0∞) * (L : ℝ≥0∞) * (μHE[m + 1] : Measure (Eucl P)) A := by
  intro m
  -- `μHE[d] = κ_d • μH[d]` on every space, with `κ_d ∈ ℝ≥0` independent of the space.
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℝ≥0, ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X],
      (μHE[m] : Measure X) = κ₀ • μH[(m : ℝ)] :=
    ⟨_, fun X _ _ _ => Measure.euclideanHausdorffMeasure_def m⟩
  obtain ⟨κ₁, hκ₁0, hκ₁⟩ : ∃ κ₁ : ℝ≥0, κ₁ ≠ 0 ∧
      ∀ (X : Type) [EMetricSpace X] [MeasurableSpace X] [BorelSpace X],
        (μHE[m + 1] : Measure X) = κ₁ • μH[((m + 1 : ℕ) : ℝ)] :=
    ⟨_, Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (m + 1),
      fun X _ _ _ => Measure.euclideanHausdorffMeasure_def (m + 1)⟩
  refine ⟨2 * κ₀ / κ₁, fun P f L A hf => ?_⟩
  -- The unnormalized inequality on `ℝ^P`, rescaled by `κ_m`.
  obtain ⟨ψ, hψm, hψt, hψi⟩ := Submission.slicing_im_coarea_eil_unnormalized (Eucl P) m f L A hf
  refine ⟨fun t => (κ₀ : ℝ≥0∞) * ψ t, hψm.const_mul _, fun t => ?_, ?_⟩
  · rw [hκ₀, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
    dsimp only
    gcongr
    exact hψt t
  · rw [lintegral_const_mul _ hψm, hκ₁, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
    have hC : ((2 * κ₀ / κ₁ : ℝ≥0) : ℝ≥0∞) * κ₁ = 2 * κ₀ := by
      rw [← ENNReal.coe_mul, div_mul_cancel₀ _ hκ₁0, ENNReal.coe_mul, ENNReal.coe_ofNat]
    calc (κ₀ : ℝ≥0∞) * ∫⁻ t, ψ t
        ≤ κ₀ * (2 * L * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl P)) A) := by gcongr
      _ = ((2 * κ₀ / κ₁ : ℝ≥0) : ℝ≥0∞) * κ₁ * L * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl P)) A := by
        rw [hC]; ring
      _ = ((2 * κ₀ / κ₁ : ℝ≥0) : ℝ≥0∞) * L * (κ₁ * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl P)) A) := by
        ring
/-- Countable Lipschitz cover (Lindelöf): if `f` is locally Lipschitz on an arbitrary `U ⊆ ℝ^P`,
then countably many open sets `O i` cover `U` and `f` is `K i`-Lipschitz on each `O i ∩ U`. -/
theorem Submission.lpf_lli_countable_lipschitz_cover : ∀ (P Q : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q), LocallyLipschitzOn U f → ∃ (O : ℕ → Set (Eucl P)) (K : ℕ → ℝ≥0), (∀ i, IsOpen (O i)) ∧ U ⊆ ⋃ i, O i ∧ ∀ i, LipschitzOnWith (K i) f (O i ∩ U) := by
  intro P Q U f hf
  -- Step 1: each `x ∈ U` has an open `o x ∋ x` with `f` `k x`-Lipschitz on `o x ∩ U`.
  have hloc : ∀ x ∈ U, ∃ (o : Set (Eucl P)) (k : ℝ≥0),
      IsOpen o ∧ x ∈ o ∧ LipschitzOnWith k f (o ∩ U) := by
    intro x hx
    obtain ⟨k, t, ht, hft⟩ := hf hx
    obtain ⟨o, ho, hxo, hot⟩ := mem_nhdsWithin.1 ht
    exact ⟨o, k, ho, hxo, hft.mono hot⟩
  choose! o k ho hxo hfo using hloc
  -- Step 2: `ℝ^P` is hereditarily Lindelöf, so countably many `o x` (`x ∈ T ⊆ U`) cover `U`.
  obtain ⟨T, hTc, hTU, hUT⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_nhds_subcover o
    fun x hx => (ho x hx).mem_nhds (hxo x hx)
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- Step 3: `T = ∅` forces `U = ∅`; take empty pieces.
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, fun x hx => ?_, fun _ => ?_⟩
    · simpa using hUT hx
    · simp
  · -- Step 4: enumerate `T = range g` and take `O i = o (g i)`, `K i = k (g i)`.
    obtain ⟨g, rfl⟩ := hTc.exists_eq_range hTne
    refine ⟨fun i => o (g i), fun i => k (g i), fun i => ho _ (hTU _ (mem_range_self i)),
      fun x hx => ?_, fun i => hfo _ (hTU _ (mem_range_self i))⟩
    -- Step 5: the pieces cover `U`.
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.1 (hUT hx)
    exact mem_iUnion.2 ⟨i, hxy⟩

/-- Disjoint Lipschitz pieces: if `u` is locally Lipschitz on an open `Ω ⊆ ℝⁿ` and `D ⊆ Ω` is
`Lⁿ`-null-measurable, then `D` is covered by pairwise disjoint null-measurable `B m ⊆ D ∩ V m`,
where the `V m ⊆ Ω` are open and `u` is `K m`-Lipschitz on `V m`. -/
theorem Submission.lpf_raf_lla_disjoint_lipschitz_pieces : ∀ (n Q : ℕ) (Ω D : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → D ⊆ Ω → NullMeasurableSet D (volume : Measure (Eucl n)) → ∃ (V B : ℕ → Set (Eucl n)) (K : ℕ → ℝ≥0), (∀ m, IsOpen (V m)) ∧ (∀ m, V m ⊆ Ω) ∧ (∀ m, LipschitzOnWith (K m) u (V m)) ∧ (∀ m, B m ⊆ D ∩ V m) ∧ Pairwise (Function.onFun Disjoint B) ∧ (∀ m, NullMeasurableSet (B m) (volume : Measure (Eucl n))) ∧ D ⊆ ⋃ m, B m := by
  intro n Q Ω D u hΩ hu hDΩ hD
  -- Step 1: countable Lipschitz cover: open `O m` cover `Ω`, `u` is `K m`-Lipschitz on `O m ∩ Ω`.
  obtain ⟨O, K, hO, hΩO, hK⟩ := Submission.lpf_lli_countable_lipschitz_cover n Q Ω u hu
  -- Step 2: the open pieces `V m = O m ∩ Ω` lie in `Ω` and cover `Ω`.
  have hVo : ∀ m, IsOpen (O m ∩ Ω) := fun m => (hO m).inter hΩ
  have hΩV : Ω ⊆ ⋃ m, O m ∩ Ω := fun x hx => by
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hΩO hx)
    exact mem_iUnion.2 ⟨m, hm, hx⟩
  -- Steps 3–4: `W m = disjointed V m` and `B m = D ∩ W m`.
  refine ⟨fun m => O m ∩ Ω, fun m => D ∩ disjointed (fun m => O m ∩ Ω) m, K, hVo,
    fun m => inter_subset_right, hK,
    fun m => inter_subset_inter_right D (disjointed_subset (fun m => O m ∩ Ω) m),
    fun i j hij => Disjoint.mono inter_subset_right inter_subset_right
      (disjoint_disjointed (fun m => O m ∩ Ω) hij),
    fun m => hD.inter
      (MeasurableSet.disjointed (fun m => (hVo m).measurableSet) m).nullMeasurableSet,
    fun x hx => ?_⟩
  -- Step 4(d): `x ∈ D ⊆ Ω ⊆ ⋃ V m = ⋃ W m`, so `x ∈ D ∩ W m = B m` for some `m`.
  have hxW : x ∈ ⋃ m, disjointed (fun m => O m ∩ Ω) m := by
    rw [iUnion_disjointed]
    exact hΩV (hDΩ hx)
  obtain ⟨m, hm⟩ := mem_iUnion.1 hxW
  exact mem_iUnion.2 ⟨m, hx, hm⟩
/-- Countable gluing of fibre-sum area identities (Simon Ch. 3, proof of 2.6; used for Ch. 6,
3.9): if `A` is covered, up to a `μ`-null set `Z` with `ν`-null image `f '' Z`, by pairwise
disjoint `μ`-null-measurable pieces `B m ⊆ A`, each satisfying `∫_{B m} F dμ = ∫ N_{B m} dν` with
an a.e.-measurable fibre sum `N_S(y) = ∑_{x ∈ S, f x = y} h x`, then so does `A`. -/
theorem Submission.lpf_raf_fiber_sum_glue : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (f : X → Y) (h F : X → ℝ≥0∞) (A Z : Set X) (B : ℕ → Set X), (∀ m, B m ⊆ A) → Pairwise (Function.onFun Disjoint B) → (∀ m, NullMeasurableSet (B m) μ) → (A ⊆ Z ∪ ⋃ m, B m) → μ Z = 0 → ν (f '' Z) = 0 → (∀ m, AEMeasurable (fun y => ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x) ν ∧ ∫⁻ x in B m, F x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x ∂ν) → AEMeasurable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) ν ∧ ∫⁻ x in A, F x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x ∂ν := by
  intro X Y _ _ μ ν f h F A Z B hBA hdisj hBm hcov hZ hfZ hg
  -- Off `f '' Z`, the `A`-fibre is the disjoint union of the `B m`-fibres, so the sums split.
  have hpt : ∀ y ∉ f '' Z, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x =
      ∑' m, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x := by
    intro y hy
    have he : {x | x ∈ A ∧ f x = y} = ⋃ m, {x | x ∈ B m ∧ f x = y} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxA, rfl⟩
        rcases hcov hxA with hxZ | hxB
        · exact absurd ⟨x, hxZ, rfl⟩ hy
        · obtain ⟨m, hm⟩ := mem_iUnion.mp hxB
          exact ⟨m, hm, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨hBA m hm, rfl⟩
    have hd : univ.PairwiseDisjoint fun m => {x | x ∈ B m ∧ f x = y} :=
      fun i _ j _ hij => (hdisj hij).mono (fun _ hx => hx.1) (fun _ hx => hx.1)
    change ∑' x : ({x | x ∈ A ∧ f x = y} : Set X), h x =
      ∑' m, ∑' x : ({x | x ∈ B m ∧ f x = y} : Set X), h x
    rw [he]
    exact ENNReal.tsum_biUnion hd
  -- As `ν (f '' Z) = 0`, the fibre sums agree `ν`-a.e.; this gives a.e.-measurability.
  have hae : (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) =ᵐ[ν]
      fun y => ∑' m, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfZ] with y hy using hpt y hy
  refine ⟨(AEMeasurable.tsum fun m => (hg m).1).congr hae.symm, ?_⟩
  -- `A` and `⋃ m, B m` differ by a subset of the `μ`-null set `Z`.
  have hAe : A =ᵐ[μ] ⋃ m, B m := by
    refine ae_eq_set.mpr ⟨measure_mono_null ?_ hZ, ?_⟩
    · rintro x ⟨hxA, hxB⟩
      exact (hcov hxA).resolve_right hxB
    · rw [sdiff_eq_empty.mpr (iUnion_subset hBA), measure_empty]
  -- Sum the identities over `m` on both sides.
  rw [Measure.restrict_congr_set hAe, lintegral_iUnion₀ hBm hdisj.aedisjoint F,
    lintegral_congr_ae hae, lintegral_tsum fun m => (hg m).1]
  exact tsum_congr fun m => (hg m).2

/-- Area formula for a map locally Lipschitz on an open set (Simon Ch. 2, (3.5), localized by the
countable decomposition of the proof of Ch. 3, 2.4–2.5; used for Ch. 6, 3.9): if `u` is locally
Lipschitz on open `Ω ⊆ ℝⁿ`, `D ⊆ Ω` is `Lⁿ`-null-measurable and `w ≥ 0` is `Lⁿ ⌞ D`-a.e.
measurable, then the fibre sum `N(y) = ∑_{x ∈ D, u x = y} w x` is `Hⁿ`-a.e. measurable and
`∫_D w Ju dLⁿ = ∫ N dHⁿ`, where `Ju = √det(⟨Du eᵢ, Du eⱼ⟩)`.  Split `D` into disjoint pieces
`B m` inside open `V m ⊆ Ω` on which `u` is Lipschitz, apply SimonGMT's area formula for maps
Lipschitz on a set to each piece (its within-derivative Jacobian is `Ju` a.e. on `B m`, via a
Lipschitz extension of `u|V m`), and glue the pieces. -/
theorem Submission.lpf_raf_local_lipschitz_area : ∀ (n Q : ℕ) (Ω D : Set (Eucl n)) (u : Eucl n → Eucl Q) (w : Eucl n → ℝ≥0∞), IsOpen Ω → LocallyLipschitzOn Ω u → D ⊆ Ω → NullMeasurableSet D (volume : Measure (Eucl n)) → AEMeasurable w ((volume : Measure (Eucl n)).restrict D) → AEMeasurable (fun y => ∑' x : {x : Eucl n // x ∈ D ∧ u x = y}, w x) (μHE[n] : Measure (Eucl Q)) ∧ ∫⁻ x in D, w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1)) (fderiv ℝ u x (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) = ∫⁻ y, ∑' x : {x : Eucl n // x ∈ D ∧ u x = y}, w x ∂(μHE[n] : Measure (Eucl Q)) := by
  intro n Q Ω D u w hΩ hu hDΩ hD hw
  -- Step 1: `normDet T = √det(⟨T eᵢ, T eⱼ⟩)`, the Gram determinant in the orthonormal basis `eᵢ`.
  have hJ : ∀ T : Eucl n →L[ℝ] Eucl Q, (T : Eucl n →ₗ[ℝ] Eucl Q).normDet =
      Real.sqrt (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1))
        (T (EuclideanSpace.single j 1))).det := by
    intro T
    have h := (T : Eucl n →ₗ[ℝ] Eucl Q).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      RCLike.ofReal_real_eq_id, id_eq] at h
    rw [← Real.sqrt_sq (T : Eucl n →ₗ[ℝ] Eucl Q).normDet_nonneg, h]
    rfl
  -- Steps 2–3: pairwise disjoint null-measurable `B m ⊆ D ∩ V m` covering `D`, where `V m` is
  -- open and `u` is `K m`-Lipschitz on `V m`.
  obtain ⟨V, B, K, hVo, -, hK, hBDV, hBd, hBm, hDB⟩ :=
    Submission.lpf_raf_lla_disjoint_lipschitz_pieces n Q Ω D u hΩ hu hDΩ hD
  have hdim : Module.finrank ℝ (Eucl n) = n := finrank_euclideanSpace_fin
  -- Steps 4–5: the area formula on each piece `B m`.
  have hpiece : ∀ m, AEMeasurable (fun y => ∑' x : {x : Eucl n // x ∈ B m ∧ u x = y}, w x)
        (μHE[n] : Measure (Eucl Q)) ∧
      ∫⁻ x in B m, w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j =>
        inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1))
          (fderiv ℝ u x (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) =
        ∫⁻ y, ∑' x : {x : Eucl n // x ∈ B m ∧ u x = y}, w x ∂(μHE[n] : Measure (Eucl Q)) := by
    intro m
    have hBV : B m ⊆ V m := fun x hx => (hBDV m hx).2
    have hL : LipschitzOnWith (K m) u (B m) := (hK m).mono hBV
    have hwm : AEMeasurable w ((volume : Measure (Eucl n)).restrict (B m)) :=
      hw.mono_set fun x hx => (hBDV m hx).1
    -- Step 4: SimonGMT's weighted area formula for `u` Lipschitz on `B m`.
    have hmeas :=
      Poincare.SimonGMT.Chapter02.aemeasurable_weightedAreaFiberSum_lipschitzOn (hBm m) hL hwm
    have harea :=
      Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum (hBm m) hL hwm
    rw [hdim] at hmeas harea
    refine ⟨hmeas, Eq.trans ?_ harea.symm⟩
    -- Step 5: `fderivWithin ℝ u (B m) = fderiv ℝ u` a.e. on `B m`, through a global Lipschitz
    -- extension `g` of `u|V m` (`u = g` near every point of the open `V m ⊇ B m`).
    obtain ⟨g, L, hg, hug⟩ :=
      Poincare.SimonGMT.Chapter02.exists_lipschitz_extension_finiteDimensional (hK m)
    have hder := Poincare.SimonGMT.Chapter02.ae_fderivWithin_eq_of_lipschitz_extension (hBm m) hg
      (hug.mono hBV)
    refine lintegral_congr_ae ?_
    filter_upwards [hder, ae_restrict_mem₀ (hBm m)] with x hx hxB
    have hxg : fderiv ℝ u x = fderiv ℝ g x :=
      (Filter.eventuallyEq_of_mem ((hVo m).mem_nhds (hBV hxB)) hug).fderiv_eq
    rw [Poincare.SimonGMT.Chapter02.areaJacobianWithin, hx, ← hxg, hJ, mul_comm]
  -- Step 6: glue the pieces with `Z = ∅`.
  exact Submission.lpf_raf_fiber_sum_glue (Eucl n) (Eucl Q) volume μHE[n] u w
    (fun x => w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j =>
      inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1))
        (fderiv ℝ u x (EuclideanSpace.single j 1))).det))
    D ∅ B (fun m => (hBDV m).trans inter_subset_left) hBd hBm (hDB.trans subset_union_right)
    measure_empty (by rw [image_empty, measure_empty]) hpiece
/-- Antilipschitz charts pull back `Hⁿ`-null sets to `Lⁿ`-null sets (Simon Ch. 3, proof of 2.6;
used for Ch. 6, 3.9): if `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` on `Ω` with `c > 0`, then `Φ` has a
`c⁻¹`-Lipschitz inverse `Ψ` on `Φ(Ω)` with `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, so `Hⁿ(Z) = 0` gives
`Lⁿ(Ω ∩ Φ⁻¹(Z)) = Hⁿ(Ω ∩ Φ⁻¹(Z)) = 0`. -/
theorem Submission.lpf_raf_chart_preimage_null : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c → (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ Z : Set (Eucl P), (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
  intro P n Φ Ω c hc hΦ Z hZ
  -- `Φ` is injective on `Ω`, so `Ψ := invFunOn Φ Ω` is a left inverse of `Φ` on `Ω`.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  set Ψ := Function.invFunOn Φ Ω
  have hleft : LeftInvOn Ψ Φ Ω := hinj.leftInvOn_invFunOn
  -- `Ψ` is `c⁻¹`-Lipschitz on `Φ '' Ω`.
  have hlip : LipschitzOnWith (Real.toNNReal c⁻¹) Ψ (Φ '' Ω) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    rw [hleft hw, hleft hw', dist_eq_norm, dist_eq_norm,
      Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hΦ w hw w' hw'
  -- `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, and the latter is `Hⁿ`-null by the Lipschitz image bound.
  have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Ψ '' (Φ '' Ω ∩ Z) := by
    rintro w ⟨hw, hwZ⟩
    exact ⟨Φ w, ⟨⟨w, hw, rfl⟩, hwZ⟩, hleft hw⟩
  have himg : (μHE[n] : Measure (Eucl n)) (Ψ '' (Φ '' Ω ∩ Z)) = 0 := by
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (A := Φ '' Ω ∩ Z) n (hlip.mono fun _ hy => hy.1)
    have h2 : (μHE[n] : Measure (Eucl P)) (Φ '' Ω ∩ Z) = 0 :=
      measure_mono_null (fun _ hy => hy.2) hZ
    rw [h2, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  -- On `ℝⁿ`, `Hⁿ = Lⁿ`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact measure_mono_null hsub himg

/-- Change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6 with a weight;
used for Ch. 6, 3.9): if `Φ` is Lipschitz and `c`-antilipschitz on the open set `Ω` and
`A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable, then `D = Ω ∩ Φ⁻¹(A)` is `Lⁿ`-null-measurable, `g ∘ Φ` is
a.e.-measurable on `D`, and `∫_A g dHⁿ = ∫_D g(Φ(w)) JΦ(w) dLⁿ(w)`.  This is the area formula
for `Φ` on `D`, whose fibre sums are `1_A g` because `Φ` is injective on `Ω`. -/
theorem Submission.lpf_raf_chart_change_of_variables : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (g : Eucl P → ℝ≥0∞), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → AEMeasurable g ((μHE[n] : Measure (Eucl P)).restrict A) → NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ AEMeasurable (fun w => g (Φ w)) ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) ∧ ∫⁻ x in A, g x ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ w in Ω ∩ Φ ⁻¹' A, g (Φ w) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) := by
  intro P n Φ Ω A g hΩ ⟨K, hK⟩ ⟨c, hc, hΦ⟩ hAΩ hA hg
  -- `Φ` is injective and continuous on `Ω`.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  have hcont : ContinuousOn Φ Ω := hK.continuousOn
  classical
  -- `Ω ∩ Φ⁻¹(B)` is Borel for Borel `B`: replace `Φ` by its Borel extension `Ω.piecewise Φ 0`.
  have hborel : ∀ B : Set (Eucl P), MeasurableSet B → MeasurableSet (Ω ∩ Φ ⁻¹' B) := by
    intro B hB
    have hm : Measurable (Ω.piecewise Φ (fun _ => (0 : Eucl P))) :=
      hcont.measurable_piecewise continuousOn_const hΩ.measurableSet
    have heq : Ω ∩ Φ ⁻¹' B = Ω ∩ (Ω.piecewise Φ (fun _ => (0 : Eucl P))) ⁻¹' B := by
      ext w
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hw, hwB⟩
        exact ⟨hw, by rwa [Set.piecewise_eq_of_mem _ _ _ hw]⟩
      · rintro ⟨hw, hwB⟩
        exact ⟨hw, by rwa [Set.piecewise_eq_of_mem _ _ _ hw] at hwB⟩
    rw [heq]
    exact hΩ.measurableSet.inter (hm hB)
  -- `D = (Ω ∩ Φ⁻¹(B)) ∪ (Ω ∩ Φ⁻¹(A ∖ B))` with `B ⊆ A` Borel and `Hⁿ(A ∖ B) = 0`, so `D` is
  -- `Lⁿ`-null-measurable.
  obtain ⟨B, hBA, hBm, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have hnull : (μHE[n] : Measure (Eucl P)) (A \ B) = 0 := (ae_eq_set.mp hBae).2
  have hD : NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) := by
    have hsplit : Ω ∩ Φ ⁻¹' A = (Ω ∩ Φ ⁻¹' B) ∪ (Ω ∩ Φ ⁻¹' (A \ B)) := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨hw, hwA⟩
        by_cases hwB : Φ w ∈ B
        · exact Or.inl ⟨hw, hwB⟩
        · exact Or.inr ⟨hw, hwA, hwB⟩
      · rintro (⟨hw, hwB⟩ | ⟨hw, hwA, -⟩)
        · exact ⟨hw, hBA hwB⟩
        · exact ⟨hw, hwA⟩
    rw [hsplit]
    exact (hborel B hBm).nullMeasurableSet.union
      (NullMeasurableSet.of_null (Submission.lpf_raf_chart_preimage_null P n Φ Ω c hc hΦ _ hnull))
  -- `g ∘ Φ = g' ∘ Φ` a.e. on `D` for a measurable `g' = g` (`Hⁿ⌞A`-a.e.), since `Φ` pulls the
  -- `Hⁿ`-null set `{g ≠ g'} ∩ A` back to an `Lⁿ`-null set.
  have hgae : AEMeasurable (fun w => g (Φ w))
      ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) := by
    have hZ : (μHE[n] : Measure (Eucl P)) ({x | g x ≠ hg.mk g x} ∩ A) = 0 := by
      rw [← Measure.restrict_apply₀' hA]
      exact hg.ae_eq_mk
    have hpre := Submission.lpf_raf_chart_preimage_null P n Φ Ω c hc hΦ _ hZ
    have hΦae : AEMeasurable Φ ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) :=
      (hcont.aemeasurable hΩ.measurableSet).mono_measure
        (Measure.restrict_mono inter_subset_left le_rfl)
    refine (hg.measurable_mk.comp_aemeasurable hΦae).congr ?_
    have h1 : ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)),
        w ∈ Ω ∩ Φ ⁻¹' A := ae_restrict_mem₀ hD
    have h2 : ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)),
        w ∉ Ω ∩ Φ ⁻¹' ({x | g x ≠ hg.mk g x} ∩ A) :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hpre)
    filter_upwards [h1, h2] with w hw1 hw2
    simp only [Function.comp_apply]
    by_contra hne
    exact hw2 ⟨hw1.1, Ne.symm hne, hw1.2⟩
  -- The area formula for `Φ` (locally Lipschitz on `Ω`) on `D` with weight `g ∘ Φ`.
  have hloc : LocallyLipschitzOn Ω Φ := fun _ _ => ⟨K, Ω, self_mem_nhdsWithin, hK⟩
  obtain ⟨-, harea⟩ := Submission.lpf_raf_local_lipschitz_area n P Ω (Ω ∩ Φ ⁻¹' A) Φ
    (fun w => g (Φ w)) hΩ hloc inter_subset_left hD hgae
  -- By injectivity, the fibre of `D` over `y` is a singleton for `y ∈ A` and empty otherwise.
  have hfib : ∀ y, (∑' x : {x : Eucl n // x ∈ Ω ∩ Φ ⁻¹' A ∧ Φ x = y}, g (Φ x)) =
      A.indicator g y := by
    intro y
    by_cases hy : y ∈ A
    · obtain ⟨w₀, hw₀, rfl⟩ := hAΩ hy
      rw [indicator_of_mem hy,
        tsum_eq_single (⟨w₀, ⟨hw₀, hy⟩, rfl⟩ : {x : Eucl n // x ∈ Ω ∩ Φ ⁻¹' A ∧ Φ x = Φ w₀})]
      intro b hb
      exact absurd (Subtype.ext (hinj b.2.1.1 hw₀ b.2.2)) hb
    · rw [indicator_of_notMem hy]
      have : IsEmpty {x : Eucl n // x ∈ Ω ∩ Φ ⁻¹' A ∧ Φ x = y} :=
        ⟨fun x => hy (x.2.2 ▸ x.2.1.2)⟩
      exact tsum_empty
  refine ⟨hD, hgae, ?_⟩
  rw [harea, ← lintegral_indicator₀ hA]
  exact lintegral_congr fun y => (hfib y).symm

/-- Area formula through a chart composed with an injective `C¹` change of variables (one
straightened box of the co-area formula, Simon Ch. 3, 2.7–2.9; used for Ch. 6, §4): if `Φ` is
Lipschitz and `c`-antilipschitz on the open set `Ω`, `χ` is `C¹` and injective on the open set
`B` with `χ(B) ⊆ Ω`, `S ⊆ χ(B)` is Borel and `ψ ≥ 0` is Borel, then
`∫_{Φ(S)} ψ dHⁿ = ∫_{B ∩ χ⁻¹(S)} |det Dχ(y)| ψ(Φ(χ y)) JΦ(χ y) dLⁿ(y)`.  Apply the chart change
of variables to `A = Φ(S)` (Borel by Lusin–Souslin, with `Ω ∩ Φ⁻¹(A) = S`), then Mathlib's
change of variables along `χ` on the Borel set `B ∩ χ⁻¹(S)`, whose image is `S`. -/
theorem Submission.slicing_im_creg_box_bulk : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (B : Set (Eucl n)) (χ : Eucl n → Eucl n) (S : Set (Eucl n)) (ψ : Eucl P → ℝ≥0∞), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → IsOpen B → ContDiffOn ℝ 1 χ B → InjOn χ B → χ '' B ⊆ Ω → MeasurableSet S → S ⊆ χ '' B → Measurable ψ → ∫⁻ x in Φ '' S, ψ x ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ y, (B ∩ χ ⁻¹' S).indicator (fun y => ENNReal.ofReal |(fderiv ℝ χ y).det| * (ψ (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ (χ y) (EuclideanSpace.single i 1)) (fderiv ℝ Φ (χ y) (EuclideanSpace.single j 1))).det))) y ∂(volume : Measure (Eucl n)) := by
  intro P n Φ Ω B χ S ψ hΩ ⟨K, hK⟩ ⟨c, hc, hΦ⟩ hB hχ hχinj hχΩ hS hSχ hψ
  -- Step 1: `Φ` is injective and continuous on `Ω`.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  have hcont : ContinuousOn Φ Ω := hK.continuousOn
  -- Step 2: `Φ(S)` is Borel (Lusin–Souslin) and `Ω ∩ Φ⁻¹(Φ(S)) = S`.
  have hSΩ : S ⊆ Ω := hSχ.trans hχΩ
  have hΦS : MeasurableSet (Φ '' S) :=
    hS.image_of_continuousOn_injOn (hcont.mono hSΩ) (hinj.mono hSΩ)
  have hpre : Ω ∩ Φ ⁻¹' (Φ '' S) = S := by
    ext w
    constructor
    · rintro ⟨hw, w', hw'S, hΦw⟩
      rwa [← hinj (hSΩ hw'S) hw hΦw]
    · intro hw
      exact ⟨hSΩ hw, w, hw, rfl⟩
  -- Step 3: the area formula for `Φ` with `A = Φ(S)`.
  obtain ⟨-, -, harea⟩ := Submission.lpf_raf_chart_change_of_variables P n Φ Ω (Φ '' S) ψ hΩ
    ⟨K, hK⟩ ⟨c, hc, hΦ⟩ (image_mono hSΩ) hΦS.nullMeasurableSet hψ.aemeasurable
  rw [hpre] at harea
  -- Step 4: `S' = B ∩ χ⁻¹(S)` is Borel, via the Borel extension `B.piecewise χ 0`.
  classical
  have hS' : MeasurableSet (B ∩ χ ⁻¹' S) := by
    have hm : Measurable (B.piecewise χ (fun _ => (0 : Eucl n))) :=
      hχ.continuousOn.measurable_piecewise continuousOn_const hB.measurableSet
    have heq : B ∩ χ ⁻¹' S = B ∩ (B.piecewise χ (fun _ => (0 : Eucl n))) ⁻¹' S := by
      ext y
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hy, hyS⟩
        exact ⟨hy, by rwa [Set.piecewise_eq_of_mem _ _ _ hy]⟩
      · rintro ⟨hy, hyS⟩
        exact ⟨hy, by rwa [Set.piecewise_eq_of_mem _ _ _ hy] at hyS⟩
    rw [heq]
    exact hB.measurableSet.inter (hm hS)
  -- Step 5: `χ(S') = S`.
  have himg : χ '' (B ∩ χ ⁻¹' S) = S := by
    ext w
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact hy
    · intro hw
      obtain ⟨y, hyB, rfl⟩ := hSχ hw
      exact ⟨y, ⟨hyB, hw⟩, rfl⟩
  -- Step 6: `χ` has derivative `Dχ(y)` at every `y ∈ S' ⊆ B` (`B` is open).
  have hder : ∀ y ∈ B ∩ χ ⁻¹' S, HasFDerivWithinAt χ (fderiv ℝ χ y) (B ∩ χ ⁻¹' S) y := by
    intro y hy
    have hd : DifferentiableAt ℝ χ y :=
      (hχ.differentiableOn one_ne_zero y hy.1).differentiableAt (hB.mem_nhds hy.1)
    exact hd.hasFDerivAt.hasFDerivWithinAt
  -- Step 7: change of variables along `χ` on `S'`.
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (Eucl n)) hS'
    hder (hχinj.mono inter_subset_left) (fun w => ψ (Φ w) * ENNReal.ofReal (Real.sqrt
      (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1))
        (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det))
  rw [himg] at hcov
  -- Step 8: combine and write the set integral over `S'` as an indicator integral.
  rw [harea, hcov, lintegral_indicator hS']
/-- Area formula on the slices `{y₀ = t}` of a straightened chart `(B, χ)` (Simon Ch. 3, 2.6 on
each slice; used for the co-area formula of Ch. 6, 4.1): with `[t, v] = (t, v₀, …, v_{m-1})`, the
slice map `σ_t(v) = Φ(χ[t, v])` is Lipschitz and `c`-antilipschitz on the open slice
`B_t = {v | [t, v] ∈ B}`, so the chart change of variables gives
`∫_{σ_t(S′_t)} g dHᵐ = ∫_{S′_t} g(σ_t(v)) Jσ_t(v) dLᵐ(v)` with `S′ = B ∩ χ⁻¹(S)`, and by the chain
rule `Dσ_t(v) eᵢ = DΦ(χ[t, v]) (Dχ([t, v]) eᵢ₊₁)`, i.e. `Jσ_t(v) = 𝒥([t, v])`. -/
theorem Submission.slicing_im_creg_box_slice_area : ∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)) (S : Set (Eucl (m + 1))) (g : Eucl P → ℝ≥0∞), ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → IsOpen B → ContDiffOn ℝ 1 χ B → χ '' B ⊆ Ω → (∃ Λ : ℝ≥0, LipschitzOnWith Λ χ B) → (∀ (t : ℝ) (v v' : Eucl m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B → (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')) ∈ B → ‖v - v'‖ ≤ ‖χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) - χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')))‖) → MeasurableSet S → Measurable g → ∀ t : ℝ, ∫⁻ x in (fun v : Eucl m => Φ (χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))))) '' {v : Eucl m | (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B ∩ χ ⁻¹' S}, g x ∂(μHE[m] : Measure (Eucl P)) = ∫⁻ v : Eucl m, (B ∩ χ ⁻¹' S).indicator (fun y => g (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1))) (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1)))).det)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) ∂(volume : Measure (Eucl m)) := by
  intro P m Φ Ω B χ S g hΦ ⟨K, hK⟩ ⟨c, hc, hΦc⟩ hB hχ hχΩ ⟨Λ, hΛ⟩ hslice hS hg t
  classical
  -- `ι z = [0, z]` is a linear isometry with `ι eᵢ = eᵢ₊₁`, and `e v = [t, v] = e 0 + ι v`.
  let ιl : Eucl m →ₗ[ℝ] Eucl (m + 1) :=
    { toFun := fun z => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ z))
      map_add' := fun z w => by
        ext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp
      map_smul' := fun a z => by
        ext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp }
  let ι : Eucl m →L[ℝ] Eucl (m + 1) := LinearMap.toContinuousLinearMap ιl
  let e : Eucl m → Eucl (m + 1) := fun v =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))
  have he_split : ∀ v, e v = e 0 + ι v := by
    intro v
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [e, ι, ιl]
  have hι_single : ∀ i : Fin m,
      ι (EuclideanSpace.single i 1) = EuclideanSpace.single i.succ 1 := by
    intro i
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [ι, ιl]
  have hι_norm : ∀ z, ‖ι z‖ = ‖z‖ := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    simp [ι, ιl]
  have he_iso : Isometry e := by
    refine Isometry.of_dist_eq fun v w => ?_
    rw [dist_eq_norm, dist_eq_norm, he_split v, he_split w, add_sub_add_left_eq_sub, ← map_sub,
      hι_norm]
  have he_cont : Continuous e := he_iso.continuous
  have he_d : ∀ v, HasFDerivAt e ι v := fun v =>
    (ι.hasFDerivAt.const_add (e 0)).congr_of_eventuallyEq (Eventually.of_forall he_split)
  -- The slices `B_t = e⁻¹(B)` (open) and `S′_t = e⁻¹(B ∩ χ⁻¹(S)) ⊆ B_t` (Borel: replace `χ` by
  -- its Borel extension `B.piecewise χ 0`).
  let Bt : Set (Eucl m) := e ⁻¹' B
  let St : Set (Eucl m) := {v | e v ∈ B ∩ χ ⁻¹' S}
  have hBt : IsOpen Bt := hB.preimage he_cont
  have hSt_sub : St ⊆ Bt := fun v hv => hv.1
  have hS' : MeasurableSet (B ∩ χ ⁻¹' S) := by
    have hm : Measurable (B.piecewise χ (fun _ => (0 : Eucl (m + 1)))) :=
      hχ.continuousOn.measurable_piecewise continuousOn_const hB.measurableSet
    have heq : B ∩ χ ⁻¹' S = B ∩ (B.piecewise χ (fun _ => (0 : Eucl (m + 1)))) ⁻¹' S := by
      ext y
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hy, hyS⟩
        exact ⟨hy, by rwa [Set.piecewise_eq_of_mem _ _ _ hy]⟩
      · rintro ⟨hy, hyS⟩
        exact ⟨hy, by rwa [Set.piecewise_eq_of_mem _ _ _ hy] at hyS⟩
    rw [heq]
    exact hB.measurableSet.inter (hm hS)
  have hSt : MeasurableSet St := he_cont.measurable hS'
  -- `σ = Φ ∘ χ ∘ e` is `K Λ`-Lipschitz on `B_t`, and `c`-antilipschitz there by the slice
  -- hypothesis and the antilipschitz bound of `Φ` on `χ(B) ⊆ Ω`; hence injective on `B_t`.
  let σ : Eucl m → Eucl P := fun v => Φ (χ (e v))
  have hχe : LipschitzOnWith (Λ * 1) (χ ∘ e) Bt :=
    hΛ.comp he_iso.lipschitzWith.lipschitzOnWith (fun v hv => hv)
  have hσlip : LipschitzOnWith (K * (Λ * 1)) σ Bt :=
    hK.comp hχe (fun v hv => hχΩ ⟨e v, hv, rfl⟩)
  have hσanti : ∀ w ∈ Bt, ∀ w' ∈ Bt, c * ‖w - w'‖ ≤ ‖σ w - σ w'‖ := by
    intro w hw w' hw'
    calc c * ‖w - w'‖ ≤ c * ‖χ (e w) - χ (e w')‖ :=
          mul_le_mul_of_nonneg_left (hslice t w w' hw hw') hc.le
      _ ≤ ‖σ w - σ w'‖ := hΦc _ (hχΩ ⟨e w, hw, rfl⟩) _ (hχΩ ⟨e w', hw', rfl⟩)
  have hinj : InjOn σ Bt := by
    intro w hw w' hw' h
    have h1 := hσanti w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- `σ(S′_t)` is Borel (Lusin–Souslin) and `B_t ∩ σ⁻¹(σ(S′_t)) = S′_t` by injectivity.
  have hAt : MeasurableSet (σ '' St) :=
    hSt.image_of_continuousOn_injOn (hσlip.continuousOn.mono hSt_sub) (hinj.mono hSt_sub)
  have hpre : Bt ∩ σ ⁻¹' (σ '' St) = St := by
    ext v
    constructor
    · rintro ⟨hv, w, hw, hwv⟩
      rwa [← hinj (hSt_sub hw) hv hwv]
    · intro hv
      exact ⟨hSt_sub hv, v, hv, rfl⟩
  -- The chart change of variables for `σ` on `B_t` with `A := σ(S′_t)`.
  obtain ⟨-, -, harea⟩ := Submission.lpf_raf_chart_change_of_variables P m σ Bt (σ '' St) g hBt
    ⟨_, hσlip⟩ ⟨c, hc, hσanti⟩ (image_mono hSt_sub) hAt.nullMeasurableSet hg.aemeasurable
  rw [hpre] at harea
  -- Chain rule: `Dσ(v) = DΦ(χ(e v)) ∘ Dχ(e v) ∘ ι` on `B_t`, so
  -- `Dσ(v) eᵢ = DΦ(χ(e v)) (Dχ(e v) eᵢ₊₁)`.
  have hderiv : ∀ v ∈ Bt, ∀ i : Fin m, fderiv ℝ σ v (EuclideanSpace.single i 1) =
      fderiv ℝ Φ (χ (e v)) (fderiv ℝ χ (e v) (EuclideanSpace.single i.succ 1)) := by
    intro v hv i
    have hev : e v ∈ B := hv
    have hχd : HasFDerivAt χ (fderiv ℝ χ (e v)) (e v) :=
      ((hχ.differentiableOn_one (e v) hev).differentiableAt (hB.mem_nhds hev)).hasFDerivAt
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (χ (e v))) (χ (e v)) :=
      (hΦ.differentiable_one (χ (e v))).hasFDerivAt
    have hσd : HasFDerivAt σ ((fderiv ℝ Φ (χ (e v))).comp ((fderiv ℝ χ (e v)).comp ι)) v :=
      hΦd.comp v (hχd.comp v (he_d v))
    rw [hσd.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hι_single]
  -- Compare the integrands pointwise: both vanish off `S′_t`, and agree on it by `hderiv`.
  show ∫⁻ x in σ '' St, g x ∂(μHE[m] : Measure (Eucl P)) =
    ∫⁻ v, (B ∩ χ ⁻¹' S).indicator _ (e v) ∂(volume : Measure (Eucl m))
  rw [harea, ← lintegral_indicator hSt]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ St
  · have hev : e v ∈ B ∩ χ ⁻¹' S := hv
    rw [indicator_of_mem hv, indicator_of_mem hev]
    show g (Φ (χ (e v))) * _ = _
    simp only [hderiv v hv.1]
  · have hev : e v ∉ B ∩ χ ⁻¹' S := hv
    rw [indicator_of_notMem hv, indicator_of_notMem hev]
/-- Borel measurability of the straightened slice-Jacobian integrand
`F̃ = 1_{S′} · (y ↦ g(Φ(χ y)) · √det(⟨DΦ(χ y)(Dχ(y)e_{i+1}), DΦ(χ y)(Dχ(y)e_{j+1})⟩)_{i,j<m})`,
`S′ = B ∩ χ⁻¹(S)`, for `Φ` of class `C¹`, `χ` of class `C¹` on the open set `B`, `S` and `g`
Borel.  The extension `χ̃ = B.piecewise χ 0` of `χ` is Borel, so `S′ = B ∩ χ̃⁻¹(S)` is Borel, and
on `S′` the outer `χ` may be replaced by `χ̃`.  `y ↦ Dχ(y)v` is measurable for any `χ`, while
`(x, u) ↦ DΦ(x)u`, the inner product and the determinant are continuous. -/
theorem Submission.slicing_im_creg_box_integrand_measurable : (∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)) (S : Set (Eucl (m + 1))) (g : Eucl P → ℝ≥0∞), ContDiff ℝ 1 Φ → IsOpen B → ContDiffOn ℝ 1 χ B → MeasurableSet S → Measurable g → Measurable ((B ∩ χ ⁻¹' S).indicator (fun y => g (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1))) (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1)))).det)))) := by
  intro P m Φ B χ S g hΦ hB hχ hS hg
  classical
  -- `χ̃ = B.piecewise χ 0` is Borel and agrees with `χ` on `B`.
  obtain ⟨χt, hχt, hχtB⟩ : ∃ χt : Eucl (m + 1) → Eucl (m + 1), Measurable χt ∧ EqOn χt χ B :=
    ⟨B.piecewise χ 0, hχ.continuousOn.measurable_piecewise continuousOn_const hB.measurableSet,
      piecewise_eqOn B χ 0⟩
  -- `S′ = B ∩ χ⁻¹(S) = B ∩ χ̃⁻¹(S)` is Borel.
  have hS' : MeasurableSet (B ∩ χ ⁻¹' S) := by
    rw [hχtB.symm.inter_preimage_eq S]
    exact hB.measurableSet.inter (hχt hS)
  -- `y ↦ g(Φ(χ̃ y))` is measurable.
  have h₁ : Measurable fun y => g (Φ (χt y)) := hg.comp (hΦ.continuous.measurable.comp hχt)
  -- `a_k(y) = DΦ(χ̃ y)(Dχ(y)e_k)` is measurable.
  have ha : ∀ k : Fin (m + 1), Measurable fun y =>
      fderiv ℝ Φ (χt y) (fderiv ℝ χ y (EuclideanSpace.single k 1)) := fun k =>
    (hΦ.continuous_fderiv_apply one_ne_zero).measurable.comp
      (hχt.prodMk (measurable_fderiv_apply_const ℝ χ (EuclideanSpace.single k (1 : ℝ))))
  -- The entries `M(y)_{ij} = ⟨a_{i+1}(y), a_{j+1}(y)⟩` are measurable.
  have hM : ∀ i j : Fin m, Measurable fun y =>
      inner ℝ (fderiv ℝ Φ (χt y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1)))
        (fderiv ℝ Φ (χt y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1))) := fun i j =>
    continuous_inner.measurable.comp ((ha i.succ).prodMk (ha j.succ))
  -- `N ↦ det (Matrix.of N)` is continuous on `Fin m → Fin m → ℝ`, so `y ↦ ofReal √det M(y)` is
  -- measurable.
  have hdet : Continuous fun N : Fin m → Fin m → ℝ => (Matrix.of N).det :=
    Continuous.matrix_det (continuous_matrix fun i j => continuous_apply_apply i j)
  have h₂ : Measurable fun y => ENNReal.ofReal (Real.sqrt (Matrix.of fun i j : Fin m =>
      inner ℝ (fderiv ℝ Φ (χt y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1)))
        (fderiv ℝ Φ (χt y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1)))).det) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (hdet.measurable.comp (Measurable.of_eval fun i => Measurable.of_eval fun j => hM i j)))
  -- On `S′` the integrand agrees with the measurable `y ↦ g(Φ(χ̃ y)) · ofReal √det M(y)`.
  convert (h₁.mul h₂).indicator hS' using 1
  exact indicator_congr fun y hy => by simp only [Pi.mul_apply, hχtB hy.1]
/-- Jacobian identity for the slice map, in Gram-determinant form: if `γ ∈ range A` is dual to
the first coordinate, `⟪γ, A (D y)⟫ = y₀`, then with `eᵢ` the standard basis,
`√det(⟪A D e_{i+1}, A D e_{j+1}⟫)_{i,j<m} = ‖γ‖ · √det(⟪A eᵢ, A eⱼ⟫)_{i,j≤m} · |det D|`. -/
theorem Submission.slicing_im_creg_jacobian_identity : ∀ (P m : ℕ) (A : Eucl (m + 1) →L[ℝ] Eucl P) (D : Eucl (m + 1) →L[ℝ] Eucl (m + 1)) (γ : Eucl P), γ ∈ LinearMap.range A.toLinearMap → (∀ y : Eucl (m + 1), inner ℝ γ (A (D y)) = y 0) → Real.sqrt (Matrix.of fun i j : Fin m => inner ℝ (A (D (EuclideanSpace.single i.succ 1))) (A (D (EuclideanSpace.single j.succ 1)))).det = ‖γ‖ * Real.sqrt (Matrix.of fun i j : Fin (m + 1) => inner ℝ (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1))).det * |D.det| := by
  intro P m A D γ hγ hdual
  -- Coordinates: `x = ∑ₖ xₖ eₖ`, so `A (D x) = ∑ₖ xₖ vₖ` with `vₖ = A (D eₖ)`, and
  -- `⟪A x, A y⟫ = ∑ₖ xₖ ∑ₗ ⟪A eₖ, A eₗ⟫ yₗ`.
  have hexp : ∀ x : Eucl (m + 1), ∑ k, x k • EuclideanSpace.single k (1 : ℝ) = x := fun x => by
    simpa using (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr x
  have hAD : ∀ x : Eucl (m + 1),
      A (D x) = ∑ k, x k • A (D (EuclideanSpace.single k 1)) := fun x => by
    conv_lhs => rw [← hexp x]
    simp only [map_sum, map_smul]
  have hgram : ∀ x y : Eucl (m + 1), inner ℝ (A x) (A y) = ∑ k, x k *
      ∑ l, inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)) * y l := by
    intro x y
    conv_lhs => rw [← hexp x, ← hexp y]
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  -- Notation: `G` the Gram matrix of `A`, `Γ` the Gram matrix of the `vⱼ`, `M` the matrix of `D`.
  set G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun i j =>
    inner ℝ (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1))
  set Γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun i j =>
    inner ℝ (A (D (EuclideanSpace.single i 1))) (A (D (EuclideanSpace.single j 1)))
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun k i => D (EuclideanSpace.single i 1) k
  have hMdet : M.det = D.det := by
    have hDM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis D.toLinearMap = M := by
      ext k i
      simp [LinearMap.toMatrix_apply, M]
    rw [← hDM, LinearMap.det_toMatrix]
  -- Step 2: `Γ = Mᵀ G M`, hence `det Γ = (det D)² det G`.
  have hΓM : Γ = M.transpose * (G * M) := by
    ext i j
    simp only [Γ, G, M, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    exact hgram _ _
  have hΓdet : Γ.det = D.det ^ 2 * G.det := by
    rw [hΓM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hMdet]
    ring
  -- Step 3: `det Γ' = ‖γ‖² det Γ`, where `Γ' = Γ.submatrix succ succ` is the left-hand matrix.
  have hclaim : (Γ.submatrix Fin.succ Fin.succ).det = ‖γ‖ ^ 2 * Γ.det := by
    by_cases hD : D.det = 0
    · -- Step 3(a): `D` is singular.  A kernel vector `y ≠ 0` of `D` has `y₀ = ⟪γ, A (D y)⟫ = 0`,
      -- so its tail `z` is a nonzero kernel vector of `Γ'`.
      rw [hΓdet, hD, show ‖γ‖ ^ 2 * ((0 : ℝ) ^ 2 * G.det) = 0 by ring]
      obtain ⟨y, hyker, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hD).ne'
      have hDy : D y = 0 := by simpa using LinearMap.mem_ker.1 hyker
      have hy0 : y 0 = 0 := by rw [← hdual y, hDy, map_zero, inner_zero_right]
      have hsum : ∑ j : Fin m, y j.succ • A (D (EuclideanSpace.single j.succ 1)) = 0 := by
        rw [← map_zero A, ← hDy, hAD y, Fin.sum_univ_succ, hy0, zero_smul, zero_add]
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun i => y i.succ, fun hz => hyne ?_, ?_⟩
      · ext k
        refine Fin.cases ?_ (fun i => ?_) k
        · simpa using hy0
        · simpa using congrFun hz i
      · ext i
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Γ, Matrix.of_apply,
          Pi.zero_apply]
        rw [← inner_zero_right (A (D (EuclideanSpace.single i.succ 1))), ← hsum, inner_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [real_inner_smul_right, mul_comm]
    · -- Step 3(b): `D` is invertible.  Write `γ = A (D c)`; then `Γ c = e₀` and `c₀ = ‖γ‖²`,
      -- and Cramer's rule `adj Γ · Γ = det Γ · 1` gives `det Γ' = (adj Γ)₀₀ = det Γ · c₀`.
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hγ
      obtain ⟨c, hDc⟩ : ∃ c, D c = u :=
        ⟨_, (D.toContinuousLinearEquivOfDetNeZero hD).apply_symm_apply u⟩
      have hγc : A (D c) = γ := by rw [hDc]; simpa using hu
      have hnorm : ‖γ‖ ^ 2 = c 0 := by
        rw [← hdual c, hγc, real_inner_self_eq_norm_sq]
      -- Step 1 (dual relation): `(Γ c)ᵢ = ⟪vᵢ, γ⟫ = (eᵢ)₀ = δᵢ₀`.
      have hΓc : Γ.mulVec (fun j => c j) = Pi.single 0 1 := by
        ext i
        simp only [Matrix.mulVec, dotProduct, Γ, Matrix.of_apply]
        have hi : ∑ j, inner ℝ (A (D (EuclideanSpace.single i 1)))
            (A (D (EuclideanSpace.single j 1))) * c j =
            inner ℝ (A (D (EuclideanSpace.single i 1))) (A (D c)) := by
          rw [hAD c, inner_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [real_inner_smul_right, mul_comm]
        rw [hi, hγc, real_inner_comm, hdual]
        by_cases h0 : i = 0
        · subst h0; simp
        · simp [h0, Ne.symm h0]
      have hadj : Γ.adjugate 0 0 = Γ.det * c 0 := by
        have h1 : Γ.adjugate.mulVec (Γ.mulVec fun j => c j) = Γ.det • fun j => c j := by
          rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        have h2 := congrFun h1 0
        rw [hΓc] at h2
        simpa using h2
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hadj
      simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero] at hadj
      rw [hadj, hnorm, mul_comm]
  -- Steps 4–5: `det Γ' = (‖γ‖ |det D|)² det G`; take square roots.
  have hfinal : (Γ.submatrix Fin.succ Fin.succ).det = (‖γ‖ * |D.det|) ^ 2 * G.det := by
    rw [hclaim, hΓdet, mul_pow, sq_abs]
    ring
  show Real.sqrt (Γ.submatrix Fin.succ Fin.succ).det = ‖γ‖ * Real.sqrt G.det * |D.det|
  rw [hfinal, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (mul_nonneg (norm_nonneg _) (abs_nonneg _))]
  ring
/-- Tonelli in the coordinates `ℝ^{m+1} = ℝ × ℝ^m`: `(t, v) ↦ [t, v]` is the composite of the
volume-preserving maps `id × ofLp`, `(piFinSuccAbove _ 0).symm = Fin.cons` and `toLp`, so
`∫ F = ∫ F ∘ [·,·]` over `ℝ × ℝ^m`, which splits by `lintegral_prod`. -/
theorem Submission.slicing_im_creg_lintegral_cons :
    ∀ (m : ℕ) (F : Eucl (m + 1) → ℝ≥0∞), Measurable F → Measurable (fun t : ℝ => ∫⁻ v : Eucl m, F ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)))) ∧ ∫⁻ y, F y = ∫⁻ t : ℝ, ∫⁻ v : Eucl m, F ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) := by
  intro m F hF
  -- `e (t, v) = [t, v]` is volume preserving from `ℝ × ℝ^m` to `ℝ^{m+1}`.
  set e : ℝ × Eucl m → Eucl (m + 1) := fun p =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin m) ℝ p.2))
  have he : MeasurePreserving e ((volume : Measure ℝ).prod (volume : Measure (Eucl m)))
      (volume : Measure (Eucl (m + 1))) := by
    have h := (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
      (((volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _).comp
        ((MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_ofLp (Fin m))))
    convert h using 1
    funext p
    simp only [e, Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_zero]
    rfl
  have hFe : Measurable fun p : ℝ × Eucl m => F (e p) := hF.comp he.measurable
  exact ⟨hFe.lintegral_prod_right', by
    rw [← he.lintegral_comp hF, lintegral_prod _ hFe.aemeasurable]⟩
/-- Straightening at a regular point (inverse function theorem): if `h` is `C¹` and
`Dh(w₀) ≠ 0`, the local inverse `χ` of `Ψ = [h, π]` (`π` the orthogonal projection onto
`ker Dh(w₀) ≅ ℝ^m`) is a `C¹`, Lipschitz chart on an open `B` with `w₀ ∈ χ(B) ⊆ Ω`,
`h ∘ χ = y ↦ y 0` on `B`, and `|v - v'| ≤ |χ[t,v] - χ[t,v']|` on each slice `{y 0 = t}`, where
`[t,v] = (t, v_0, …, v_{m-1})`. -/
theorem Submission.slicing_im_creg_straightening : ∀ (m : ℕ) (h : Eucl (m + 1) → ℝ) (Ω : Set (Eucl (m + 1))) (w₀ : Eucl (m + 1)), IsOpen Ω → w₀ ∈ Ω → ContDiff ℝ 1 h → fderiv ℝ h w₀ ≠ 0 → ∃ (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)), IsOpen B ∧ ContDiffOn ℝ 1 χ B ∧ IsOpen (χ '' B) ∧ w₀ ∈ χ '' B ∧ χ '' B ⊆ Ω ∧ (∃ Λ : ℝ≥0, LipschitzOnWith Λ χ B) ∧ (∀ y ∈ B, h (χ y) = y 0) ∧ ∀ (t : ℝ) (v v' : Eucl m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B → (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')) ∈ B → ‖v - v'‖ ≤ ‖χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) - χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')))‖ := by
  intro m h Ω w₀ hΩ hw₀ hh hDh
  -- Step 1: the coordinate map `J (a, b) = [a, b]` is continuous linear and injective.
  obtain ⟨J, hJ⟩ : ∃ J : ℝ × Eucl m →L[ℝ] Eucl (m + 1), ∀ a b, J (a, b) =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons a (EuclideanSpace.equiv (Fin m) ℝ b)) := by
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun p => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons p.1 (EuclideanSpace.equiv (Fin m) ℝ p.2))
        map_add' := fun p q => ?_
        map_smul' := fun c p => ?_ }, fun a b => rfl⟩
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hJ0 : ∀ a b, J (a, b) 0 = a := fun a b => by simp [hJ]
  have hJs : ∀ a b (j : Fin m), J (a, b) j.succ = b j := fun a b j => by simp [hJ]
  have hJinj : ∀ a a' b b', J (a, b) = J (a', b') → a = a' ∧ b = b' := fun a a' b b' hab =>
    ⟨by rw [← hJ0 a b, hab, hJ0], by ext j; rw [← hJs a b j, hab, hJs]⟩
  -- Step 2: `pr = ι_K ∘ P_K` (`π` above) for `K = ker Dh(w₀)`, `P_K` the orthogonal projection
  -- and `ι_K : K ≃ ℝ^m` an orthonormal basis: `|pr u| ≤ |u|` and `ker Dh(w₀) ∩ ker pr = 0`.
  obtain ⟨pr, hprn, hprk⟩ : ∃ pr : Eucl (m + 1) →L[ℝ] Eucl m, (∀ u, ‖pr u‖ ≤ ‖u‖) ∧
      ∀ u, fderiv ℝ h w₀ u = 0 → pr u = 0 → u = 0 := by
    let ℓ : Module.Dual ℝ (Eucl (m + 1)) := (fderiv ℝ h w₀ : Eucl (m + 1) →ₗ[ℝ] ℝ)
    have hℓ : ℓ ≠ 0 := fun h0 => hDh (ContinuousLinearMap.ext fun u => LinearMap.congr_fun h0 u)
    have hK : Module.finrank ℝ (LinearMap.ker ℓ) = m := by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
      rw [finrank_euclideanSpace_fin] at this
      omega
    let b := (stdOrthonormalBasis ℝ (LinearMap.ker ℓ)).reindex (finCongr hK)
    refine ⟨b.repr.toLinearIsometry.toContinuousLinearMap ∘L
      (LinearMap.ker ℓ).orthogonalProjectionOnto, fun u => ?_, fun u hu hpu => ?_⟩
    · simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
      exact (LinearMap.ker ℓ).norm_orthogonalProjectionOnto_apply_le u
    · have huK : u ∈ LinearMap.ker ℓ := LinearMap.mem_ker.2 hu
      simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.map_eq_zero_iff,
        Submodule.orthogonalProjectionOnto_eq_zero_iff] at hpu
      simpa using Submodule.inner_right_of_mem_orthogonal huK hpu
  -- Step 3: `Ψ = [h, pr]` is `C¹` with invertible derivative `e₀ = J ∘ (Dh(w₀), pr)` at `w₀`.
  have hΨs : HasStrictFDerivAt (fun w => J (h w, pr w)) (J ∘L ((fderiv ℝ h w₀).prod pr)) w₀ :=
    J.hasStrictFDerivAt.comp w₀
      ((hh.contDiffAt.hasStrictFDerivAt one_ne_zero).prodMk pr.hasStrictFDerivAt)
  have hΨc : ContDiff ℝ 1 (fun w => J (h w, pr w)) := J.contDiff.comp (hh.prodMk pr.contDiff)
  have hLinj : Function.Injective (J ∘L ((fderiv ℝ h w₀).prod pr)) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
    have h1 : J (fderiv ℝ h w₀ u, pr u) = J (0, 0) := by
      rw [Prod.mk_zero_zero, map_zero]
      exact hu
    obtain ⟨h1a, h1b⟩ := hJinj _ _ _ _ h1
    exact hprk u h1a h1b
  let e₀ : Eucl (m + 1) ≃L[ℝ] Eucl (m + 1) :=
    (LinearEquiv.ofInjectiveEndo (J ∘L ((fderiv ℝ h w₀).prod pr) :
      Eucl (m + 1) →ₗ[ℝ] Eucl (m + 1)) hLinj).toContinuousLinearEquiv
  have he₀ : (e₀ : Eucl (m + 1) →L[ℝ] Eucl (m + 1)) = J ∘L ((fderiv ℝ h w₀).prod pr) :=
    ContinuousLinearMap.ext fun u => by simp [e₀, LinearEquiv.coe_ofInjectiveEndo]
  have hΨe : HasStrictFDerivAt (fun w => J (h w, pr w))
      (e₀ : Eucl (m + 1) →L[ℝ] Eucl (m + 1)) w₀ := by
    rw [he₀]
    exact hΨs
  -- Step 4: inverse function theorem; `χ = Φ.symm` is `C¹` at `y₀ = Ψ(w₀)`.
  obtain ⟨Φ, hΦ, hw₀s⟩ : ∃ Φ : OpenPartialHomeomorph (Eucl (m + 1)) (Eucl (m + 1)),
      ⇑Φ = (fun w => J (h w, pr w)) ∧ w₀ ∈ Φ.source :=
    ⟨hΨe.toOpenPartialHomeomorph _, hΨe.toOpenPartialHomeomorph_coe,
      hΨe.mem_toOpenPartialHomeomorph_source⟩
  have hy₀ : Φ w₀ ∈ Φ.target := Φ.map_source hw₀s
  have hχy₀ : Φ.symm (Φ w₀) = w₀ := Φ.left_inv hw₀s
  have hχC : ContDiffAt ℝ 1 Φ.symm (Φ w₀) := by
    refine Φ.contDiffAt_symm (f₀' := e₀) hy₀ ?_ ?_
    · rw [hχy₀, hΦ]
      exact hΨe.hasFDerivAt
    · rw [hχy₀, hΦ]
      exact hΨc.contDiffAt
  -- Step 5: a ball `B` around `y₀` inside the target, on which `χ` is `C¹`, Lipschitz (mean value
  -- inequality near `y₀`) and maps into `Ω`.
  obtain ⟨Λ, T, hT, hΛ⟩ := hχC.exists_lipschitzOnWith
  have hΩ' : Φ.symm ⁻¹' Ω ∈ 𝓝 (Φ w₀) :=
    (Φ.continuousAt_symm hy₀).preimage_mem_nhds (by rw [hχy₀]; exact hΩ.mem_nhds hw₀)
  have hev : ∀ᶠ y in 𝓝 (Φ w₀),
      (y ∈ Φ.target ∧ ContDiffAt ℝ 1 Φ.symm y ∧ Φ.symm y ∈ Ω) ∧ y ∈ T := by
    filter_upwards [Φ.open_target.mem_nhds hy₀, hχC.eventually (by simp), hΩ', hT]
      with y h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  obtain ⟨ε, hε, hεB⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- Step 6: `Ψ ∘ χ = id` on `B`; `B` and `χ(B)` are open, `w₀ = χ(y₀) ∈ χ(B)`.
  have hΨχ : ∀ y ∈ ball (Φ w₀) ε, J (h (Φ.symm y), pr (Φ.symm y)) = y := fun y hy => by
    have h1 := Φ.right_inv (hεB y hy).1.1
    rw [hΦ] at h1
    exact h1
  refine ⟨ball (Φ w₀) ε, Φ.symm, isOpen_ball,
    fun y hy => (hεB y hy).1.2.1.contDiffWithinAt,
    Φ.isOpen_image_symm_of_subset_target isOpen_ball fun y hy => (hεB y hy).1.1,
    ⟨Φ w₀, mem_ball_self hε, hχy₀⟩, ?_, ⟨Λ, hΛ.mono fun y hy => (hεB y hy).2⟩, ?_, ?_⟩
  · -- Step 7: `χ(B) ⊆ Ω`.
    rintro _ ⟨y, hy, rfl⟩
    exact (hεB y hy).1.2.2
  · -- Step 8: `h ∘ χ` is the first coordinate.
    intro y hy
    conv_rhs => rw [← hΨχ y hy]
    exact (hJ0 _ _).symm
  · -- Step 9: on a slice, `pr ∘ χ` recovers `v`, and `|pr| ≤ 1`.
    intro s v v' hv hv'
    simp only [← hJ] at hv hv' ⊢
    have hpv : ∀ v : Eucl m, J (s, v) ∈ ball (Φ w₀) ε → pr (Φ.symm (J (s, v))) = v :=
      fun v hv => (hJinj _ _ _ _ (hΨχ _ hv)).2
    calc ‖v - v'‖ = ‖pr (Φ.symm (J (s, v))) - pr (Φ.symm (J (s, v')))‖ := by
          rw [hpv v hv, hpv v' hv']
      _ = ‖pr (Φ.symm (J (s, v)) - Φ.symm (J (s, v')))‖ := by rw [map_sub]
      _ ≤ ‖Φ.symm (J (s, v)) - Φ.symm (J (s, v'))‖ := hprn _

/-- Co-area formula on one straightened box.  Let `Φ` be a `C¹` Lipschitz, antilipschitz chart on
`Ω`, and let `(B, χ)` straighten `h`: `h (χ y) = y₀` on `B` and `‖v - v'‖ ≤ ‖χ [t, v] - χ [t, v']‖`.
If `S ⊆ χ(B)` is Borel and on `S` we have `f ∘ Φ = h`, `G ∘ Φ ∈ range DΦ` and
`⟪G (Φ w), DΦ(w) u⟫ = Dh(w) u`, then `t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dHᵐ` is a.e.-measurable and
`∫_ℝ ∫_{Φ(S) ∩ f⁻¹{t}} g dHᵐ dt = ∫_{Φ(S)} ‖G‖ g dHᵐ⁺¹`.  Both sides equal `∫ F̃ dLᵐ⁺¹`, where
`F̃ = 1_{B ∩ χ⁻¹(S)} · g(Φ(χ y)) · 𝒥(y)`: the right side by `bulk` and the Jacobian identity, the
left side by Tonelli along `y = [y₀, tail y]` and `slice_area`. -/
theorem Submission.slicing_im_creg_box_coarea : ∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)) (S : Set (Eucl (m + 1))), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ContDiff ℝ 1 h → Measurable G → IsOpen B → ContDiffOn ℝ 1 χ B → χ '' B ⊆ Ω → (∃ Λ : ℝ≥0, LipschitzOnWith Λ χ B) → (∀ y ∈ B, h (χ y) = y 0) → (∀ (t : ℝ) (v v' : Eucl m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B → (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')) ∈ B → ‖v - v'‖ ≤ ‖χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) - χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')))‖) → MeasurableSet S → S ⊆ χ '' B → (∀ w ∈ S, f (Φ w) = h w ∧ G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u, inner ℝ (G (Φ w)) (fderiv ℝ Φ w u) = fderiv ℝ h w u) → ∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in Φ '' S, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P)) := by
  intro P m Φ Ω h f G B χ S hΩ hΦ hK hc hh hG hB hχ hχΩ hΛ hχh hslice hS hSB hpt g hg
  -- Step 1 (coordinates): `[t, v]₀ = t`, and `y = [y₀, tail y]` with `tail y = (y₁, …, y_m)`.
  have hcons0 : ∀ (t : ℝ) (v : Eucl m),
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) 0
        = t := fun t v => by simp
  have hrecon : ∀ y : Eucl (m + 1), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons (y 0)
      (EuclideanSpace.equiv (Fin m) ℝ ((EuclideanSpace.equiv (Fin m) ℝ).symm fun i => y i.succ)))
        = y := by
    intro y
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- Step 2 (injectivity): `χ y = χ y'` forces `y₀ = y'₀` (as `h ∘ χ = y₀`), and then the
  -- slice bound gives `tail y = tail y'`.
  have hinj : InjOn χ B := by
    intro y hy y' hy' hyy
    have h0 : y 0 = y' 0 := by rw [← hχh y hy, ← hχh y' hy', hyy]
    have hy1 := hrecon y
    have hy2 := hrecon y'
    rw [h0] at hy1
    have hle := hslice (y' 0) _ _ (hy1.symm ▸ hy) (hy2.symm ▸ hy')
    rw [hy1, hy2, hyy, sub_self, norm_zero] at hle
    rw [← hy1, sub_eq_zero.mp (norm_le_zero_iff.mp hle), hy2]
  -- Step 3 (derivatives): `h ∘ χ = proj₀` near each `y ∈ B`, so `Dh(χ y) ∘ Dχ(y) = proj₀`.
  have hderiv : ∀ y ∈ B, ∀ z : Eucl (m + 1), fderiv ℝ h (χ y) (fderiv ℝ χ y z) = z 0 := by
    intro y hy z
    have hχd : HasFDerivAt χ (fderiv ℝ χ y) y :=
      ((hχ.differentiableOn one_ne_zero y hy).differentiableAt (hB.mem_nhds hy)).hasFDerivAt
    have hhd : HasFDerivAt h (fderiv ℝ h (χ y)) (χ y) :=
      (hh.differentiable one_ne_zero (χ y)).hasFDerivAt
    have h2 : HasFDerivAt (h ∘ χ) (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m + 1))) y := by
      refine (EuclideanSpace.proj (𝕜 := ℝ) _).hasFDerivAt.congr_of_eventuallyEq ?_
      filter_upwards [hB.mem_nhds hy] with y' hy'
      simp [hχh y' hy']
    have h3 := congrArg (fun L : Eucl (m + 1) →L[ℝ] ℝ => L z) ((hhd.comp y hχd).unique h2)
    simpa using h3
  -- Step 7 (Jacobian identity): on `S' = B ∩ χ⁻¹(S)` the bulk integrand for `ψ = ‖G‖ₑ g` is
  -- `g(Φ(χ y)) · 𝒥(y)`.
  have hJ : ∀ y ∈ B ∩ χ ⁻¹' S, ENNReal.ofReal |(fderiv ℝ χ y).det| *
      (‖G (Φ (χ y))‖ₑ * g (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j =>
        inner ℝ (fderiv ℝ Φ (χ y) (EuclideanSpace.single i 1))
          (fderiv ℝ Φ (χ y) (EuclideanSpace.single j 1))).det)) =
      g (Φ (χ y)) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j : Fin m =>
        inner ℝ (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single i.succ 1)))
          (fderiv ℝ Φ (χ y) (fderiv ℝ χ y (EuclideanSpace.single j.succ 1)))).det) := by
    rintro y ⟨hy, hyS⟩
    obtain ⟨-, hγ, hdual⟩ := hpt (χ y) hyS
    rw [Submission.slicing_im_creg_jacobian_identity P m (fderiv ℝ Φ (χ y)) (fderiv ℝ χ y)
      (G (Φ (χ y))) hγ fun z => (hdual _).trans (hderiv y hy z),
      ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),
      ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    ring
  -- Step 11 (slice sets): `Φ(S) ∩ f⁻¹{t} = σ_t(S'_t)`.
  have hset : ∀ t : ℝ, Φ '' S ∩ f ⁻¹' {t} = (fun v : Eucl m => Φ (χ
      ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)))))
        '' {v : Eucl m | (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B ∩ χ ⁻¹' S} := by
    intro t
    ext x
    constructor
    · rintro ⟨⟨w, hwS, rfl⟩, hft⟩
      obtain ⟨y, hyB, rfl⟩ := hSB hwS
      have ht : y 0 = t := by
        rw [← hχh y hyB, ← (hpt _ hwS).1]
        exact hft
      refine ⟨(EuclideanSpace.equiv (Fin m) ℝ).symm fun i => y i.succ, ?_, ?_⟩
      · rw [mem_ofPred_eq, ← ht, hrecon]
        exact ⟨hyB, hwS⟩
      · simp only
        rw [← ht, hrecon]
    · rintro ⟨v, ⟨hvB, hvS⟩, rfl⟩
      refine ⟨⟨_, hvS, rfl⟩, ?_⟩
      rw [mem_preimage, mem_singleton_iff, (hpt _ hvS).1, hχh _ hvB, hcons0]
  -- Steps 8–9 (measurability and Tonelli): `τ(t) = ∫ F̃([t, v]) dv` is measurable and
  -- `∫ F̃ = ∫ τ`.
  obtain ⟨hτ, hsplit⟩ := Submission.slicing_im_creg_lintegral_cons m _
    (Submission.slicing_im_creg_box_integrand_measurable P m Φ B χ S g hΦ hB hχ hS hg)
  -- Step 10 (slices): `∫_{Φ(S) ∩ f⁻¹{t}} g dHᵐ = τ(t)` for every `t`.
  have hslice_eq := fun t : ℝ => (hset t).symm ▸
    Submission.slicing_im_creg_box_slice_area P m Φ Ω B χ S g hΦ hK hc hB hχ hχΩ hΛ hslice hS hg t
  -- Steps 5–6 (bulk): with `ψ = ‖G‖ₑ g`, `∫_{Φ(S)} ψ dHᵐ⁺¹ = ∫ 1_{S'} |det Dχ| ψ(Φ ∘ χ) JΦ(χ ·)`.
  have hbulk := Submission.slicing_im_creg_box_bulk P (m + 1) Φ Ω B χ S (fun x => ‖G x‖ₑ * g x)
    hΩ hK hc hB hχ hinj hχΩ hS hSB (hG.enorm.mul hg)
  refine ⟨(funext hslice_eq ▸ hτ).aemeasurable, ?_⟩
  -- Step 12: chain the bulk, Jacobian, Tonelli and slice identities.
  rw [lintegral_congr hslice_eq, ← hsplit, hbulk]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ B ∩ χ ⁻¹' S
  · rw [indicator_of_mem hy, indicator_of_mem hy, hJ y hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]
/-- Local-to-global gluing of co-area identities through an injective continuous chart (used for
the co-area formula of Simon Ch. 6, Lemma 4.1, p. 153): if every point of `Ω ∩ Φ⁻¹(W)` has an open
neighbourhood `O` such that for all Borel `S ⊆ O ∩ Ω ∩ Φ⁻¹(W)` the slice function
`t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dν` is a.e.-measurable and
`∫ ∫_{Φ(S) ∩ f⁻¹{t}} g dν dt = ∫_{Φ(S)} J g dμ`, then the same holds with `Φ(S)` replaced by `W`
(Lindelöf, disjointification, Lusin–Souslin and countable additivity). -/
theorem Submission.slicing_im_creg_local_to_global : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (W : Set (Eucl P)) (f : Eucl P → ℝ) (J g : Eucl P → ℝ≥0∞) (μ ν : Measure (Eucl P)), IsOpen Ω → Continuous Φ → InjOn Φ Ω → Measurable f → MeasurableSet W → W ⊆ Φ '' Ω → (∀ w₀ ∈ Ω, Φ w₀ ∈ W → ∃ O : Set (Eucl n), IsOpen O ∧ w₀ ∈ O ∧ ∀ S : Set (Eucl n), MeasurableSet S → S ⊆ O ∩ (Ω ∩ Φ ⁻¹' W) → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in Φ '' S, J x * g x ∂μ) → AEMeasurable (fun t : ℝ => ∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) = ∫⁻ x in W, J x * g x ∂μ := by
  intro P n Φ Ω W f J g μ ν hΩ hΦ hinj hf hW hWΦ hloc
  -- Step 1: `E = Ω ∩ Φ⁻¹(W)` is Borel and `Φ(E) = W`.
  have hEm : MeasurableSet (Ω ∩ Φ ⁻¹' W) := hΩ.measurableSet.inter (hΦ.measurable hW)
  have hΦE : Φ '' (Ω ∩ Φ ⁻¹' W) = W := by
    refine Subset.antisymm (image_subset_iff.2 inter_subset_right) fun x hx => ?_
    obtain ⟨w, hwΩ, rfl⟩ := hWΦ hx
    exact ⟨w, ⟨hwΩ, hx⟩, rfl⟩
  -- Step 2: an open `O w` for every `w` (empty off `E`) such that the identity holds on every
  -- Borel `S ⊆ O w ∩ E`; for `w ∉ E` only `S = ∅` occurs, where both sides vanish.
  have hloc' : ∀ w : Eucl n, ∃ O : Set (Eucl n), IsOpen O ∧ (w ∈ Ω ∩ Φ ⁻¹' W → w ∈ O) ∧
      ∀ S : Set (Eucl n), MeasurableSet S → S ⊆ O ∩ (Ω ∩ Φ ⁻¹' W) →
        AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) =
          ∫⁻ x in Φ '' S, J x * g x ∂μ := by
    intro w
    by_cases hw : w ∈ Ω ∩ Φ ⁻¹' W
    · obtain ⟨O, hO, hwO, hS⟩ := hloc w hw.1 hw.2
      exact ⟨O, hO, fun _ => hwO, hS⟩
    · refine ⟨∅, isOpen_empty, fun h => absurd h hw, fun S _ hS => ?_⟩
      rw [empty_inter, subset_empty_iff] at hS
      subst hS
      simp
  choose O hO hwO hOS using hloc'
  -- Step 3: Lindelöf: `E ⊆ ⋃ w, O w` is covered by countably many `O (e k)`.
  obtain ⟨T, hTc, hTO⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  obtain ⟨e, hTe⟩ := Set.countable_iff_exists_subset_range.1 hTc
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set (Eucl n), ∀ k, A k = (Ω ∩ Φ ⁻¹' W) ∩ O (e k) :=
    ⟨_, fun _ => rfl⟩
  have hAm : ∀ k, MeasurableSet (A k) := fun k => by
    rw [hA k]
    exact hEm.inter (hO (e k)).measurableSet
  have hAU : ⋃ k, A k = Ω ∩ Φ ⁻¹' W := by
    refine Subset.antisymm (iUnion_subset fun k => (hA k).symm ▸ inter_subset_left) fun w hw => ?_
    have hwT : w ∈ ⋃ i ∈ T, O i := by
      rw [hTO]
      exact mem_iUnion.2 ⟨w, hwO w hw⟩
    obtain ⟨i, hiT, hwi⟩ := mem_iUnion₂.1 hwT
    obtain ⟨k, rfl⟩ := hTe hiT
    exact mem_iUnion.2 ⟨k, (hA k).symm ▸ ⟨hw, hwi⟩⟩
  -- Step 4: disjointification `D k = disjointed A k`; each `D k ⊆ O (e k) ∩ E` is Borel.
  have hDm : ∀ k, MeasurableSet (disjointed A k) := MeasurableSet.disjointed hAm
  have hDE : ∀ k, disjointed A k ⊆ O (e k) ∩ (Ω ∩ Φ ⁻¹' W) := fun k w hw => by
    have h := disjointed_subset A k hw
    rw [hA k] at h
    exact ⟨h.2, h.1⟩
  have hDΩ : ∀ k, disjointed A k ⊆ Ω := fun k =>
    (hDE k).trans (inter_subset_right.trans inter_subset_left)
  have hDU : ⋃ k, disjointed A k = Ω ∩ Φ ⁻¹' W := by rw [iUnion_disjointed, hAU]
  have hLP := fun k => hOS (e k) (disjointed A k) (hDm k) (hDE k)
  -- Step 5: the images `Φ(D k)` are Borel (Lusin–Souslin), pairwise disjoint and cover `W`.
  have hWm : ∀ k, MeasurableSet (Φ '' disjointed A k) := fun k =>
    (hDm k).image_of_continuousOn_injOn hΦ.continuousOn (hinj.mono (hDΩ k))
  have hWd : Pairwise (Function.onFun Disjoint fun k => Φ '' disjointed A k) := fun i j hij =>
    Disjoint.image (disjoint_disjointed A hij) hinj (hDΩ i) (hDΩ j)
  have hWU : ⋃ k, Φ '' disjointed A k = W := by rw [← image_iUnion, hDU, hΦE]
  -- Step 6: countable additivity on every slice `W ∩ f⁻¹{t} = ⋃ k, Φ(D k) ∩ f⁻¹{t}`.
  have hslice : (fun t : ℝ => ∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂ν) =
      fun t => ∑' k, ∫⁻ x in Φ '' disjointed A k ∩ f ⁻¹' {t}, g x ∂ν := by
    funext t
    rw [← hWU, iUnion_inter]
    exact lintegral_iUnion (fun k => (hWm k).inter (hf (measurableSet_singleton t)))
      (fun i j hij => (hWd hij).mono inter_subset_left inter_subset_left) _
  -- Steps 7–8: a.e.-measurability of the sum, and the identity by `lintegral_tsum`.
  refine ⟨by rw [hslice]; exact AEMeasurable.tsum fun k => (hLP k).1, ?_⟩
  rw [hslice, lintegral_tsum fun k => (hLP k).1, ← hWU, lintegral_iUnion hWm hWd]
  exact tsum_congr fun k => (hLP k).2
/-- Countable gluing of co-area identities.  Put `Z = M \ ⋃ i, W i`.  For a.e. `t`,
`ν (Z ∩ f⁻¹{t}) = 0`, so `M ∩ f⁻¹{t}` and `⋃ i, (W i ∩ f⁻¹{t})` are `ν`-a.e. equal and the slice
integral over `M` is the sum of the slice integrals over the disjoint pieces `W i ∩ f⁻¹{t}`.
Integrating in `t` (`lintegral_tsum`) and summing the piece identities gives
`∫_{⋃ W i} J g dμ` (`lintegral_iUnion`), which is `∫_M J g dμ` because `J g = 0` a.e. on `Z`. -/
theorem Submission.slicing_im_coarea_glue :
    ∀ (X : Type) [MeasurableSpace X] (μ ν : Measure X) (f : X → ℝ) (J g : X → ℝ≥0∞)
      (M : Set X) (W : ℕ → Set X), Measurable f → (∀ i, MeasurableSet (W i)) →
      (∀ i, W i ⊆ M) → Pairwise (Function.onFun Disjoint W) →
      (∀ᵐ x ∂(μ.restrict (M \ ⋃ i, W i)), J x * g x = 0) →
      (∀ᵐ t ∂(volume : Measure ℝ), ν ((M \ ⋃ i, W i) ∩ f ⁻¹' {t}) = 0) →
      (∀ i, AEMeasurable (fun t : ℝ => ∫⁻ x in W i ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in W i ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) =
          ∫⁻ x in W i, J x * g x ∂μ) →
      AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) ∂(volume : Measure ℝ) =
          ∫⁻ x in M, J x * g x ∂μ := by
  intro X _ μ ν f J g M W hf hW hWM hdisj hZ hslice hpieces
  -- For a.e. `t`, `M ∩ f⁻¹{t}` and `⋃ i, (W i ∩ f⁻¹{t})` differ by the `ν`-null set
  -- `(M \ ⋃ i, W i) ∩ f⁻¹{t}`, so the slice integral over `M` is the sum over the pieces.
  have hsum : (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂ν) =ᵐ[volume]
      fun t => ∑' i, ∫⁻ x in W i ∩ f ⁻¹' {t}, g x ∂ν := by
    filter_upwards [hslice] with t ht
    have hset : M ∩ f ⁻¹' {t} =ᵐ[ν] ⋃ i, W i ∩ f ⁻¹' {t} := by
      rw [← iUnion_inter]
      refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) ht, ?_⟩
      · exact ⟨⟨hx.1.1, fun hxW => hx.2 ⟨hxW, hx.1.2⟩⟩, hx.1.2⟩
      · rw [sdiff_eq_empty.2 (inter_subset_inter_left _ (iUnion_subset hWM)), measure_empty]
    rw [setLIntegral_congr hset]
    exact lintegral_iUnion (fun i => (hW i).inter (hf (measurableSet_singleton t)))
      (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left) g
  -- The remainder `M \ ⋃ i, W i` does not contribute to the weighted integral over `M`.
  have hM : ∫⁻ x in M, J x * g x ∂μ = ∫⁻ x in ⋃ i, W i, J x * g x ∂μ := by
    rw [← lintegral_inter_add_sdiff (fun x => J x * g x) M (MeasurableSet.iUnion hW),
      inter_eq_right.2 (iUnion_subset hWM), lintegral_congr_ae hZ, lintegral_zero, add_zero]
  refine ⟨(AEMeasurable.tsum fun i => (hpieces i).1).congr hsum.symm, ?_⟩
  rw [lintegral_congr_ae hsum, lintegral_tsum fun i => (hpieces i).1, hM,
    lintegral_iUnion hW hdisj]
  exact tsum_congr fun i => (hpieces i).2
/-- Simon Ch. 6, 4.11 (Leibniz rule, pointwise): `d(ψω)(x) = ψ(x) dω(x) + Dψ(x) ∧ ω(x)`, the
wedge `Dψ(x) ∧ ω(x)` being the alternatization of `h ↦ Dψ(x)(h) ω(x)`.  As `d = Alt ∘ D`
(Mathlib's `extDeriv`), this is the product rule `D(ψω)(x) = ψ(x) Dω(x) + Dψ(x) ⊗ ω(x)`
followed by linearity of `alternatizeUncurryFin`. -/
theorem Submission.slicing_mb_lb_extDeriv_smul :
    ∀ (P m : ℕ) (ψ : Eucl P → ℝ) (ω : DifferentialForm (Eucl P) m) (x : Eucl P), DifferentiableAt ℝ ψ x → DifferentiableAt ℝ ω x → exteriorDerivative (fun y => ψ y • ω y : DifferentialForm (Eucl P) m) x = ψ x • exteriorDerivative ω x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight (ω x)) := by
  intro P m ψ ω x hψ hω
  simp only [exteriorDerivative, extDeriv]
  rw [fderiv_fun_smul hψ hω, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- Multiplication by a smooth function `ψ` maps `𝒟ᵏ(U)` into itself: `ψ φ` is smooth, and
`spt (ψ φ) ⊆ spt φ`, which is compact and contained in `U`. -/
theorem Submission.slicing_mb_lb_smul_testForm :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (φ : TestFormOn U k) (ψ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ η : TestFormOn U k, ∀ x, (η : DifferentialForm (Eucl P) k) x =
        ψ x • (φ : DifferentialForm (Eucl P) k) x := by
  intro P k U φ ψ hψ
  obtain ⟨⟨hφ, hφc⟩, hφU⟩ := φ.2
  exact ⟨⟨ψ • (φ : DifferentialForm (Eucl P) k), ⟨hψ.smul hφ, hφc.smul_left⟩,
    (tsupport_smul_subset_right ψ _).trans hφU⟩, fun _ => rfl⟩
/-- The wedge `α ∧ ω` of a `C^∞` field `α` of covectors with a test form `ω ∈ 𝒟ᵐ(U)` is a test
form in `𝒟ᵐ⁺¹(U)`, given pointwise by `alternatizeUncurryFin ((α x).smulRight (ω x))`. -/
theorem Submission.slicing_mb_lb_wedge_testForm :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U m) (α : Eucl P → (Eucl P →L[ℝ] ℝ)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α →
      ∃ η : TestFormOn U (m + 1), ∀ x, (η : DifferentialForm (Eucl P) (m + 1)) x =
        ContinuousAlternatingMap.alternatizeUncurryFin
          ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by
  intro P m U ω α hα
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  -- `η` vanishes wherever `ω` does: `(α x).smulRight 0 = 0` and `alternatizeUncurryFin` is linear.
  have hsupp : Function.support (fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ⊆
      Function.support (ω : DifferentialForm (Eucl P) m) := by
    intro x hx h0
    apply hx
    simp only [h0, ContinuousLinearMap.smulRight_zero]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
  -- Hence `η` has compact support and `tsupport η ⊆ tsupport ω ⊆ U`; the formula holds by `rfl`.
  refine ⟨⟨fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)),
    ⟨?_, hωc.mono hsupp⟩, (closure_mono hsupp).trans hωU⟩, fun x => rfl⟩
  -- Smoothness: `x ↦ (α x).smulRight (ω x)` is `C^∞` (bounded bilinear in `(α x, ω x)`), and
  -- `alternatizeUncurryFin` is the continuous linear map `alternatizeUncurryFinCLM`.
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).contDiff.comp
    (hα.smulRight hωs)
/-- Global smooth approximation of a Lipschitz function by mollification: `g k = ρ_k ⋆ h` with a
normalized smooth bump `ρ_k ≥ 0`, `∫ ρ_k = 1`, supported in `B(0, 1/(k+1))`.  Each `g k` is `C^∞`,
`L`-Lipschitz, and `|g k - h| ≤ L/(k+1)` uniformly. -/
theorem Submission.slicing_im_ll_mollify :
    ∀ (P : ℕ) (h : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L h → ∃ g : ℕ → Eucl P → ℝ,
      (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g k)) ∧ (∀ k, LipschitzWith L (g k)) ∧
        TendstoUniformly g h atTop := by
  intro P h L hL
  -- Step 1: normalized smooth bumps `ρ k ≥ 0` with `∫ ρ k = 1`, supported in `B(0, 1/(k+1))`.
  have hbump : ∀ k : ℕ, ∃ ρ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧
      Function.support ρ ⊆ ball (0 : Eucl P) (1 / ((k : ℝ) + 1)) ∧ ∫ y, ρ y = 1 := by
    intro k
    have hσ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    let φ : ContDiffBump (0 : Eucl P) :=
      ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), half_pos hσ, half_lt_self hσ⟩
    have hint : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have hpos : 0 < ∫ y, φ y := by
      refine (integral_pos_iff_support_of_nonneg φ.nonneg' hint).mpr ?_
      rw [φ.support_eq]
      exact measure_ball_pos _ _ hσ
    have hsupp : Function.support (fun y => φ y / ∫ y, φ y) ⊆ Function.support φ :=
      fun y hy h0 => hy (by simp [h0])
    refine ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
      fun y => div_nonneg φ.nonneg hpos.le, φ.support_eq ▸ hsupp, ?_⟩
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    exact mul_inv_cancel₀ hpos.ne'
  choose ρ hρs hρc hρn hρsupp hρi using hbump
  have hρint : ∀ k, Integrable (ρ k) := fun k => integrable_of_integral_eq_one (hρi k)
  -- Step 2: `g k = ρ k ⋆ h`; the convolution exists everywhere.
  have hex : ∀ k, ConvolutionExists (ρ k) h (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun k =>
    (hρc k).convolutionExists_left _ (hρs k).continuous hL.continuous.locallyIntegrable
  refine ⟨fun k => convolution (ρ k) h (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_⟩
  -- Step 3: smoothness.
  · intro k
    exact (hρc k).contDiff_convolution_left _ (hρs k) hL.continuous.locallyIntegrable
  -- Step 4: the Lipschitz constant is preserved.
  · intro k
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hx := (hex k x).integrable
    have hx' := (hex k x').integrable
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at hx hx' ⊢
    rw [dist_eq_norm, ← integral_sub hx hx']
    refine (norm_integral_le_of_norm_le ((hρint k).mul_const ((L : ℝ) * dist x x'))
      (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hρn k t), ← dist_eq_norm]
      gcongr
      · exact hρn k t
      · calc dist (h (x - t)) (h (x' - t)) ≤ L * dist (x - t) (x' - t) := hL.dist_le_mul _ _
          _ = L * dist x x' := by rw [dist_sub_right]
    · rw [integral_mul_const, hρi k, one_mul]
  -- Steps 5–6: `|g k - h| ≤ L/(k+1)` everywhere, hence uniform convergence.
  · have hbound : ∀ k x, dist (convolution (ρ k) h (ContinuousLinearMap.lsmul ℝ ℝ) volume x) (h x)
        ≤ L * (1 / ((k : ℝ) + 1)) := by
      intro k x
      refine dist_convolution_le (by positivity) (hρsupp k) (hρn k) (hρi k)
        hL.continuous.aestronglyMeasurable fun y hy => ?_
      calc dist (h y) (h x) ≤ L * dist y x := hL.dist_le_mul _ _
        _ ≤ L * (1 / ((k : ℝ) + 1)) := by
          gcongr
          exact (mem_ball.mp hy).le
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hlim : Tendsto (fun k : ℕ => (L : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (L : ℝ)
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk x
    rw [dist_comm]
    exact (hbound k x).trans_lt hk
/-- Continuous multipliers `g k → f` converging uniformly on `ℝ^P`, integrated against a
`ν`-integrable density `F` vanishing off a compact set `K`: `∫ g k F dν → ∫ f F dν`. -/
theorem Submission.slicing_im_ll_multiplier_tendsto :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) (F : Eucl P → ℝ) (K : Set (Eucl P)) (f : Eucl P → ℝ)
      (g : ℕ → Eucl P → ℝ), Integrable F ν → IsCompact K → (∀ x, x ∉ K → F x = 0) →
      Continuous f → (∀ k, Continuous (g k)) → TendstoUniformly g f atTop →
      Tendsto (fun k => ∫ x, g k x * F x ∂ν) atTop (𝓝 (∫ x, f x * F x ∂ν)) := by
  intro P ν F K f g hF hK hFK hf hg hgf
  -- A continuous `φ` is bounded by some `B` on `K` and `F` vanishes off `K`, so
  -- `|φ F| ≤ B |F|` everywhere and `φ F` is integrable.
  have hint : ∀ φ : Eucl P → ℝ, Continuous φ → Integrable (fun x => φ x * F x) ν := by
    intro φ hφ
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
    refine (hF.norm.const_mul B).mono' (hφ.aestronglyMeasurable.mul hF.aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    by_cases hx : x ∈ K
    · exact mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _)
    · simp [hFK x hx]
  -- With `I = ∫ |F| dν`, once `|g k - f| < ε / (I + 1)` everywhere,
  -- `|∫ g k F - ∫ f F| ≤ ∫ |g k - f| |F| ≤ ε I / (I + 1) < ε`.
  set I := ∫ x, ‖F x‖ ∂ν
  have hI : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hgf _ hδ)
  refine ⟨k₀, fun k hk => ?_⟩
  rw [dist_eq_norm, ← integral_sub (hint _ (hg k)) (hint _ hf)]
  calc ‖∫ x, (g k x * F x - f x * F x) ∂ν‖ ≤ ∫ x, ε / (I + 1) * ‖F x‖ ∂ν := by
        refine norm_integral_le_of_norm_le (hF.norm.const_mul _) (ae_of_all _ fun x => ?_)
        rw [← sub_mul, norm_mul, ← dist_eq_norm, dist_comm]
        exact mul_le_mul_of_nonneg_right (hk₀ k hk x).le (norm_nonneg _)
    _ = ε / (I + 1) * I := integral_const_mul _ _
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Simon Ch. 6, proof of 4.5(2), (2), for a `C^∞` multiplier `ψ`: the Leibniz rule
`∂T(ψ ω) = T(ψ dω) + T(Dψ ∧ ω)`, with `∂T` and `T` evaluated through their measure
representations and `T(Dψ ∧ ω) = τ(M, θ, ξ)(Dψ ∧ ω)`. -/
theorem Submission.slicing_im_ll_smooth_leibniz :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ η : TestFormOn U (m + 1), T η = tauAction (m + 1) M θ ξ η) → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)) (μ' : Measure (Eucl P)) (v' : Eucl P → NVector (Eucl P) m), IsMeasureRepresentation T μ v → IsMeasureRepresentation T.boundary μ' v' → ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ∂(μHE[m + 1] : Measure (Eucl P)) = (∫ x, ψ x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') - (∫ x, ψ x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ) := by
  intro P m U M θ ξ T hT μ v μ' v' hv hv' ω ψ hψ
  -- The test forms `η₁ = ψ ω ∈ 𝒟ᵐ(U)`, `η₂ = ψ dω ∈ 𝒟ᵐ⁺¹(U)` and `η₃ = Dψ ∧ ω ∈ 𝒟ᵐ⁺¹(U)`.
  have hdω : ((exteriorDerivativeTestOn U m ω : TestFormOn U (m + 1)) :
      DifferentialForm (Eucl P) (m + 1)) = exteriorDerivative (ω : DifferentialForm (Eucl P) m) :=
    rfl
  obtain ⟨η₁, hη₁⟩ := Submission.slicing_mb_lb_smul_testForm P m U ω ψ hψ
  obtain ⟨η₂, hη₂⟩ :=
    Submission.slicing_mb_lb_smul_testForm P (m + 1) U (exteriorDerivativeTestOn U m ω) ψ hψ
  obtain ⟨η₃, hη₃⟩ :=
    Submission.slicing_mb_lb_wedge_testForm P m U ω (fderiv ℝ ψ) (hψ.fderiv_right (by simp))
  -- Leibniz rule `d(ψ ω) = ψ dω + Dψ ∧ ω`: the exterior derivative of `η₁` is `η₂ + η₃`.
  have hd : exteriorDerivativeTestOn U m η₁ = η₂ + η₃ := by
    have hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) m) := ω.2.1.1
    have h₁ : (η₁ : DifferentialForm (Eucl P) m) =
        fun y => ψ y • (ω : DifferentialForm (Eucl P) m) y := funext hη₁
    apply Subtype.ext
    funext x
    change exteriorDerivative (η₁ : DifferentialForm (Eucl P) m) x =
      (η₂ : DifferentialForm (Eucl P) (m + 1)) x + (η₃ : DifferentialForm (Eucl P) (m + 1)) x
    rw [h₁, hη₂, hη₃, hdω, Submission.slicing_mb_lb_extDeriv_smul P m ψ _ x
      (hψ.differentiable (by simp) x) (hω.differentiable (by simp) x)]
  -- Hence `∂T(η₁) = T(dη₁) = T(η₂) + T(η₃)`.
  have hb : T.boundary η₁ = T η₂ + T η₃ := by
    rw [GeometricCurrentOn.boundary_apply, hd]
    exact map_add T.toCurrent η₂ η₃
  -- `∂T(η₁)` and `T(η₂)` through the measure representations, `T(η₃)` through `τ(M, θ, ξ)`.
  have h₁ : T.boundary η₁ = ∫ x, ψ x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ' := by
    simp only [(hv' η₁).2, hη₁, map_smul, smul_eq_mul]
  have h₂ : T η₂ =
      ∫ x, ψ x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ := by
    simp only [(hv η₂).2, hη₂, hdω, map_smul, smul_eq_mul]
  have h₃ : T η₃ = ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin
      ((fderiv ℝ ψ x).smulRight ((ω : DifferentialForm (Eucl P) m) x)))
      ∂(μHE[m + 1] : Measure (Eucl P)) := by
    simp only [hT η₃, tauAction, hη₃]
  rw [← h₁, ← h₂, ← h₃, hb]
  ring
/-- The tangent vector field dual to `θ ⟨· ∧ ω, ξ⟩` (Simon Ch. 6, proof of Lemma 4.5(2),
(1)–(3)): for a rectifiable triple `(M, θ, ξ)` of dimension `n = m + 1` and `ω ∈ 𝒟ᵐ(U)` there is
`Y : ℝ^P → ℝ^P` with `φ(Y(x)) = θ(x) ⟨φ ∧ ω(x), ξ(x)⟩` for all `x` and all functionals `φ`,
`Y ∈ L¹(Hⁿ ⌞ M)`, and `Y(x)` lies in every weighted approximate tangent plane at `Hⁿ`-a.e.
`x ∈ M`.  Take the Riesz representative `Y(x) = ∑ᵢ θ(x) ⟨eᵢ♭ ∧ ω(x), ξ(x)⟩ eᵢ`.  A.e. on `M`,
`ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|ξ(x)(β)| ≤ ‖β‖` and `|Y| ≤ C |θ| 1_{spt ω}`;
and for `w ⊥ span τ`, `(w♭ ∧ ω(x))(τ) = ∑ᵢ (-1)ⁱ ⟨w, τᵢ⟩ ω(x)(τ without τᵢ) = 0`, so
`Y(x) ∈ (span τ)ᗮᗮ = span τ`, the unique weighted tangent plane (`θ(x) > 0`). -/
theorem Submission.slicing_im_ll_tangent_dual_field :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)),
      IsRectifiableTriple U (m + 1) M θ ξ → ∀ ω : TestFormOn U m,
      ∃ Y : Eucl P → Eucl P, Integrable Y ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧
        (∀ (x : Eucl P) (φ : Eucl P →L[ℝ] ℝ), φ (Y x) = θ x * ξ x
          (ContinuousAlternatingMap.alternatizeUncurryFin
            (φ.smulRight ((ω : DifferentialForm (Eucl P) m) x)))) ∧
        ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
          HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → Y x ∈ Q := by
  intro P m U M θ ξ hT ω
  set f : DifferentialForm (Eucl P) m := (ω : DifferentialForm (Eucl P) m)
  -- `Λ x φ = θ(x) ⟨φ ∧ ω(x), ξ(x)⟩` is a continuous linear functional of `φ`.
  let Λ : Eucl P → (Eucl P →L[ℝ] ℝ) →L[ℝ] ℝ := fun x =>
    θ x • (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
      ((ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)).flip (f x)))
  have hΛ : ∀ x φ, Λ x φ = θ x * ξ x
      (ContinuousAlternatingMap.alternatizeUncurryFin (φ.smulRight (f x))) := fun x φ => rfl
  -- `Y(x) = ∑ᵢ Λ x (eᵢ♭) eᵢ`; every functional is `φ = ∑ᵢ φ(eᵢ) eᵢ♭`, so `φ(Y(x)) = Λ x φ`.
  let b := EuclideanSpace.basisFun (Fin P) ℝ
  let Y : Eucl P → Eucl P := fun x => ∑ i, Λ x (innerSL ℝ (b i)) • b i
  have hdual : ∀ φ : Eucl P →L[ℝ] ℝ, ∑ i, φ (b i) • innerSL ℝ (b i) = φ := by
    intro φ
    ext y
    conv_rhs => rw [← b.sum_repr' y]
    simp [map_sum, map_smul, mul_comm]
  have hY : ∀ x (φ : Eucl P →L[ℝ] ℝ), φ (Y x) = Λ x φ := by
    intro x φ
    conv_rhs => rw [← hdual φ]
    simp [Y, map_sum, map_smul, mul_comm]
  refine ⟨Y, ?_, fun x φ => (hY x φ).trans (hΛ x φ), ?_⟩
  · -- Integrability: each coordinate `x ↦ Λ x (eᵢ♭)` is integrable.
    have hω : IsTestForm f ∧ tsupport f ⊆ U := ω.2
    have hfc : Continuous f := ContDiff.continuous hω.1.1
    have hθK : IntegrableOn θ (tsupport f ∩ M) (μHE[m + 1] : Measure (Eucl P)) := by
      rw [inter_comm]
      exact hT.integrableOn _ hω.1.2 hω.2
    -- A.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|ξ(x)(β)| ≤ ‖β‖`.
    have hξb : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
        ∀ β : Covector (Eucl P) (m + 1), ‖ξ x β‖ ≤ ‖β‖ := by
      filter_upwards [hT.orients] with x hx β
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      have h1 : ‖β τ‖ ≤ ‖β‖ := by
        simpa [hτ.1] using β.le_opNorm τ
      rcases hξ with h | h <;> simpa [h] using h1
    refine integrable_finsetSum _ fun i _ => Integrable.smul_const ?_ (b i)
    -- `βᵢ(x) = eᵢ♭ ∧ ω(x)` is continuous with compact support, hence bounded.
    let β : Eucl P → Covector (Eucl P) (m + 1) := fun x =>
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (b i)))) (f x)
    have hβc : Continuous β := (ContinuousLinearMap.continuous _).comp hfc
    have hβs : HasCompactSupport β := hω.1.2.comp_left (map_zero _)
    obtain ⟨C, hC⟩ := hβc.bounded_above_of_compact_support hβs
    have hΛβ : ∀ x, Λ x (innerSL ℝ (b i)) = θ x * ξ x (β x) := fun x => rfl
    -- The coordinate vanishes off `spt ω`, where `θ` is integrable.
    have hsupp : Function.support (fun x => Λ x (innerSL ℝ (b i))) ⊆ tsupport f := by
      intro x hx
      by_contra hxK
      have h0 : β x = 0 := by
        dsimp only [β]
        rw [image_eq_zero_of_notMem_tsupport hxK, map_zero]
      have h1 : Λ x (innerSL ℝ (b i)) = 0 := by
        rw [hΛβ, h0, map_zero, mul_zero]
      exact hx h1
    rw [← integrableOn_iff_integrable_of_support_subset hsupp, IntegrableOn,
      Measure.restrict_restrict (isClosed_tsupport f).measurableSet]
    have hmono : (μHE[m + 1] : Measure (Eucl P)).restrict (tsupport f ∩ M) ≤
        (μHE[m + 1] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono inter_subset_right le_rfl
    have hg : AEStronglyMeasurable (fun x => ξ x (β x))
        ((μHE[m + 1] : Measure (Eucl P)).restrict M) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hT.aestronglyMeasurable.prodMk hβc.aestronglyMeasurable)
    simp only [hΛβ]
    refine hθK.mul_bdd (hg.mono_measure hmono) (c := C) ?_
    filter_upwards [ae_mono hmono hξb] with x hx
    exact (hx (β x)).trans (hC x)
  · -- Tangency: `⟨u, Y(x)⟩ = θ(x) ⟨u♭ ∧ ω(x), ±τ⟩ = 0` for `u ⊥ span τ`.
    filter_upwards [hT.orients, ae_restrict_mem₀ hT.nullMeasurableSet] with x hx hxM
    obtain ⟨τ, -, hW, hξ⟩ := hx
    intro Q hQ
    rw [HasWeightedApproximateTangentSpaceAt.unique (hT.pos x hxM).ne' hQ hW,
      ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ)), Submodule.mem_orthogonal]
    intro u hu
    have hτu : ∀ i, inner ℝ u (τ i) = 0 := fun i =>
      Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (mem_range_self i)) hu
    rw [← innerSL_apply_apply, hY, hΛ]
    rcases hξ with h | h <;>
      simp [h, ContinuousAlternatingMap.alternatizeUncurryFin_apply, hτu]
/-- Simon Ch. 1, Theorem 1.17 (Lusin), in the form used in the proof of Ch. 2, Theorem 1.5
(p. 44), "which applies to sets of infinite measure for `Lⁿ`": if `S ⊆ ℝⁿ` is Borel and
`f : ℝⁿ → (ℝⁿ)*` is Borel measurable, then for every `ε > 0` there is a closed `C ⊆ S` with
`Lⁿ(S ∖ C) < ε` and `f|C` continuous. -/
theorem Submission.lpf_c1r_lusin_closed :
    ∀ (n : ℕ) (S : Set (Eucl n)) (f : Eucl n → (Eucl n →L[ℝ] ℝ)), MeasurableSet S →
      Measurable f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Eucl n), IsClosed C ∧ C ⊆ S ∧
        (volume : Measure (Eucl n)) (S \ C) < ε ∧ ContinuousOn f C := by
  intro n S f hS hf ε hε
  -- Closed inner approximation of Borel sets of any measure: on the closed annuli
  -- `K j = {j ≤ |x| ≤ j + 1}`, which are bounded and locally finite and cover `ℝⁿ`, choose
  -- closed `F j ⊆ A ∩ K j` with `Lⁿ((A ∩ K j) ∖ F j) < η j`, `∑ η j < δ`; `⋃ j, F j` is closed.
  have hreg : ∀ A : Set (Eucl n), MeasurableSet A → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ A, IsClosed F ∧ (volume : Measure (Eucl n)) (A \ F) < δ := by
    intro A hA δ hδ
    obtain ⟨η, hη0, hηδ⟩ := ENNReal.exists_pos_sum_of_countable hδ ℕ
    set K : ℕ → Set (Eucl n) := fun j => (fun x : Eucl n => ‖x‖) ⁻¹' Icc (j : ℝ) (j + 1)
    have hKc : ∀ j, IsClosed (K j) := fun j => isClosed_Icc.preimage continuous_norm
    have hKb : ∀ j, K j ⊆ closedBall 0 (j + 1) := by
      intro j x hx
      rw [mem_closedBall, dist_zero_right]
      exact hx.2
    have hKcov : ∀ x : Eucl n, x ∈ K ⌊‖x‖⌋₊ := fun x =>
      ⟨Nat.floor_le (norm_nonneg x), (Nat.lt_floor_add_one _).le⟩
    -- `B₁(x)` meets `K j` only if `j ≤ |y| < |x| + 1` for some `y`.
    have hKlf : LocallyFinite K := by
      intro x
      refine ⟨ball x 1, ball_mem_nhds x one_pos, (Set.finite_lt_nat (⌊‖x‖⌋₊ + 2)).subset ?_⟩
      rintro j ⟨y, hyK, hyx⟩
      have h1 : (j : ℝ) ≤ ‖y‖ := hyK.1
      have h2 : ‖y‖ < ‖x‖ + 1 := by
        have hd : ‖y - x‖ < 1 := by rw [← dist_eq_norm]; exact mem_ball.1 hyx
        have := norm_le_norm_add_norm_sub' y x
        linarith [norm_sub_rev y x]
      have h3 : ‖x‖ < ⌊‖x‖⌋₊ + 1 := Nat.lt_floor_add_one _
      have h4 : (j : ℝ) < ((⌊‖x‖⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h4
    have hfin : ∀ j, (volume : Measure (Eucl n)) (A ∩ K j) ≠ ⊤ := fun j =>
      ((measure_mono (inter_subset_right.trans (hKb j))).trans_lt measure_closedBall_lt_top).ne
    choose F hFA hFc hFlt using fun j =>
      (hA.inter (hKc j).measurableSet).exists_isClosed_sdiff_lt (hfin j)
        (ENNReal.coe_ne_zero.2 (hη0 j).ne')
    refine ⟨⋃ j, F j, iUnion_subset fun j => (hFA j).trans inter_subset_left,
      (hKlf.subset fun j => (hFA j).trans inter_subset_right).isClosed_iUnion hFc, ?_⟩
    calc (volume : Measure (Eucl n)) (A \ ⋃ j, F j)
        ≤ volume (⋃ j, (A ∩ K j) \ F j) := by
          refine measure_mono fun x hx => mem_iUnion.2 ⟨⌊‖x‖⌋₊, ⟨hx.1, hKcov x⟩, fun hxF => ?_⟩
          exact hx.2 (mem_iUnion.2 ⟨_, hxF⟩)
      _ ≤ ∑' j, volume ((A ∩ K j) \ F j) := measure_iUnion_le _
      _ ≤ ∑' j, (η j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => (hFlt j).le
      _ < δ := hηδ
  -- Lusin's theorem through a countable basis `(b k)` of the second countable space `(ℝⁿ)*`:
  -- closed `F k ⊆ S ∩ f⁻¹(b k)` and `G k ⊆ S ∖ f⁻¹(b k)` with defects `< η k`, `∑ η k < ε / 2`,
  -- and `C = ⋂ k, (F k ∪ G k)`.
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (Eucl n →L[ℝ] ℝ)
  have hbo : ∀ k, IsOpen (b k) := fun k => hb.isOpen (mem_range_self k)
  obtain ⟨η, hη0, hηε⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε.ne').ne' ℕ
  have hη : ∀ k, ((η k : ℝ≥0) : ℝ≥0∞) ≠ 0 := fun k => ENNReal.coe_ne_zero.2 (hη0 k).ne'
  choose F hFE hFc hFlt using fun k =>
    hreg _ (hS.inter (hf (hbo k).measurableSet)) (η k) (hη k)
  choose G hGE hGc hGlt using fun k =>
    hreg _ (hS.diff (hf (hbo k).measurableSet)) (η k) (hη k)
  refine ⟨⋂ k, (F k ∪ G k), isClosed_iInter fun k => (hFc k).union (hGc k), ?_, ?_, ?_⟩
  · exact (iInter_subset _ 0).trans
      (union_subset ((hFE 0).trans inter_subset_left) ((hGE 0).trans Set.sdiff_subset))
  -- `S ∖ C ⊆ ⋃ k, ((S ∩ f⁻¹(b k)) ∖ F k ∪ (S ∖ f⁻¹(b k)) ∖ G k)`.
  · calc (volume : Measure (Eucl n)) (S \ ⋂ k, (F k ∪ G k))
        ≤ volume (⋃ k, ((S ∩ f ⁻¹' b k) \ F k ∪ (S \ f ⁻¹' b k) \ G k)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨k, hk⟩ : ∃ k, x ∉ F k ∪ G k := by
            by_contra! h
            exact hx.2 (mem_iInter.2 h)
          refine mem_iUnion.2 ⟨k, ?_⟩
          by_cases hxb : f x ∈ b k
          · exact Or.inl ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inl h)⟩
          · exact Or.inr ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inr h)⟩
      _ ≤ ∑' k, volume ((S ∩ f ⁻¹' b k) \ F k ∪ (S \ f ⁻¹' b k) \ G k) := measure_iUnion_le _
      _ ≤ ∑' k, ((η k : ℝ≥0∞) + η k) := ENNReal.tsum_le_tsum fun k =>
          (measure_union_le _ _).trans (add_le_add (hFlt k).le (hGlt k).le)
      _ = ∑' k, (η k : ℝ≥0∞) + ∑' k, (η k : ℝ≥0∞) := ENNReal.tsum_add
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hηε hηε
      _ = ε := ENNReal.add_halves ε
  -- `f⁻¹(b k) ∩ C = (G k)ᶜ ∩ C` is relatively open in `C` for every basic open set `b k`.
  · rw [hb.continuousOn_iff]
    rintro t ⟨k, rfl⟩
    refine ⟨(G k)ᶜ, (hGc k).isOpen_compl, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hxb, hxC⟩
      exact ⟨fun hxG => ((hGE k) hxG).2 hxb, hxC⟩
    · rintro ⟨hxG, hxC⟩
      refine ⟨?_, hxC⟩
      rcases mem_iInter.1 hxC k with hxF | hxG'
      · exact ((hFE k) hxF).2
      · exact absurd hxG' hxG
/-- Closed Egorov theorem on `ℝⁿ` (Simon Ch. 2, proof of Theorem 1.5): if Borel `f k` converge
pointwise on a Borel set `C` to a Borel `g`, then for every `ε > 0` there is a closed `A ⊆ C` with
`Lⁿ(C \ A) < ε` such that `f k → g` uniformly on every bounded part `A ∩ B̄_R(0)`. -/
theorem Submission.lpf_c1r_egoroff_closed : ∀ (n : ℕ) (C : Set (Eucl n)) (f : ℕ → Eucl n → ℝ) (g : Eucl n → ℝ), MeasurableSet C → (∀ k, Measurable (f k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => f k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Eucl n), IsClosed A ∧ A ⊆ C ∧ (volume : Measure (Eucl n)) (C \ A) < ε ∧ ∀ R : ℝ, TendstoUniformlyOn f g atTop (A ∩ closedBall 0 R) := by
  intro n C f g hC hf hg hfg ε hε
  -- Step 1: positive budgets `δ j` with `∑ j, δ j < ε` (this also covers `ε = ∞`).
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  -- Step 2: the bounded annuli `S j = {x : j ≤ ‖x‖ < j + 1}` partition `ℝⁿ`.
  set S : ℕ → Set (Eucl n) := fun j => ball 0 ((j : ℝ) + 1) \ ball 0 j
  have hSle : ∀ j, ∀ x ∈ S j, (j : ℝ) ≤ ‖x‖ := fun j x hx => by
    simpa [mem_ball_zero_iff] using hx.2
  have hScov : ∀ x : Eucl n, x ∈ S ⌊‖x‖⌋₊ := fun x => by
    simp only [S, Set.mem_sdiff, mem_ball_zero_iff, not_lt]
    exact ⟨Nat.lt_floor_add_one _, Nat.floor_le (norm_nonneg x)⟩
  -- Step 3: on each `C ∩ S j` (finite measure), Egorov gives `t` with `Lⁿ(t) ≤ δ j / 2` and
  -- uniform convergence on `(C ∩ S j) \ t`; inner regularity gives a closed `F ⊆ (C ∩ S j) \ t`
  -- with defect `< δ j / 2`.
  have key : ∀ j, ∃ F : Set (Eucl n), F ⊆ C ∩ S j ∧ IsClosed F ∧
      (volume : Measure (Eucl n)) ((C ∩ S j) \ F) < δ j ∧ TendstoUniformlyOn f g atTop F := by
    intro j
    have hm : MeasurableSet (C ∩ S j) := hC.inter (measurableSet_ball.diff measurableSet_ball)
    have hfin : (volume : Measure (Eucl n)) (C ∩ S j) ≠ ∞ :=
      ((measure_mono (inter_subset_right.trans sdiff_subset)).trans_lt measure_ball_lt_top).ne
    have hδ2 : (0 : ℝ≥0∞) < (δ j : ℝ≥0∞) / 2 := ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hδpos j).ne')
    obtain ⟨t, -, htm, htμ, htu⟩ := tendstoUniformlyOn_of_ae_tendsto (μ := volume)
      (fun k => (hf k).stronglyMeasurable) hg.stronglyMeasurable hm hfin
      (Eventually.of_forall fun x hx => hfg x hx.1) hδ2
    obtain ⟨F, hF, hFc, hFμ⟩ := (hm.diff htm).exists_isClosed_sdiff_lt (μ := volume)
      (ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)) hδ2.ne'
    refine ⟨F, hF.trans sdiff_subset, hFc, ?_, htu.mono hF⟩
    calc (volume : Measure (Eucl n)) ((C ∩ S j) \ F)
        ≤ volume (t ∪ ((C ∩ S j) \ t) \ F) := measure_mono fun x hx => by
          by_cases hxt : x ∈ t
          · exact Or.inl hxt
          · exact Or.inr ⟨⟨hx.1, hxt⟩, hx.2⟩
      _ ≤ volume t + volume (((C ∩ S j) \ t) \ F) := measure_union_le _ _
      _ < (δ j : ℝ≥0∞) / 2 + (δ j : ℝ≥0∞) / 2 :=
          (add_le_add htμ le_rfl).trans_lt (ENNReal.add_lt_add_left
            (ENNReal.div_ne_top ENNReal.coe_ne_top two_ne_zero) hFμ)
      _ = δ j := ENNReal.add_halves _
  choose F hFsub hFc hFμ hFu using key
  refine ⟨⋃ j, F j, ?_, iUnion_subset fun j => (hFsub j).trans inter_subset_left, ?_, ?_⟩
  · -- Step 4: `ball x 1` meets `F j ⊆ S j` only for `j < ‖x‖ + 1`, so the family is locally
    -- finite and its union is closed.
    refine LocallyFinite.isClosed_iUnion (fun x => ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩) hFc
    refine (finite_Iio ⌈‖x‖ + 1⌉₊).subset fun j ⟨y, hyF, hyx⟩ => ?_
    have h1 := hSle j y (hFsub j hyF).2
    have h2 := norm_sub_norm_le y x
    have h3 := mem_ball_iff_norm.1 hyx
    exact Nat.lt_ceil.2 (by linarith)
  · -- Step 5: `C \ ⋃ j, F j ⊆ ⋃ j, (C ∩ S j) \ F j`, of measure `≤ ∑ j, δ j < ε`.
    calc (volume : Measure (Eucl n)) (C \ ⋃ j, F j)
        ≤ volume (⋃ j, (C ∩ S j) \ F j) := measure_mono fun x hx =>
          mem_iUnion.2 ⟨⌊‖x‖⌋₊, ⟨hx.1, hScov x⟩, fun h => hx.2 (mem_iUnion.2 ⟨_, h⟩)⟩
      _ ≤ ∑' j, volume ((C ∩ S j) \ F j) := measure_iUnion_le _
      _ ≤ ∑' j, (δ j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => (hFμ j).le
      _ < ε := hδsum
  · -- Step 6: `(⋃ j, F j) ∩ B̄_R(0)` lies in the finite union of `F j`, `j ≤ ⌈R⌉₊`, on each of
    -- which the convergence is uniform.
    intro R u hu
    filter_upwards [(Finset.range (⌈R⌉₊ + 1)).eventually_all.2 fun j _ => hFu j u hu]
      with k hk x hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx.1
    refine hk j (Finset.mem_range.2 (Nat.lt_succ_of_le ?_)) x hj
    have h1 := hSle j x (hFsub j hj).2
    have h2 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx.2
    exact_mod_cast (h1.trans h2).trans (Nat.le_ceil R)

/-- Simon Ch. 2, proof of Theorem 1.5 (C¹ Approximation Theorem, p. 44), the `η_k` step.  Let
`g : ℝⁿ → ℝ` be Lipschitz and `C` closed, with `g` differentiable at every point of `C` and `Dg`
continuous on `C`.  Then there is a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε` on which the remainder
`R(x, y) = (g(y) − g(x) − Dg(x)(y − x)) / |y − x|` tends to `0` as `y → x` in `A`, uniformly for
`x` in each compact `L ⊆ A` (Whitney's condition 1.6 (‡)).  The functions
`η_k(x) = sup ({0} ∪ {|R(x, y)| : y ∈ C, 0 < |y − x| < 1/(k+1)})` (`η_k = 0` off `C`) are Borel
and tend to `0` on `C`, so Egoroff (`lpf_c1r_egoroff_closed`) makes the convergence uniform on the
bounded parts of a closed `A ⊆ C`. -/
theorem Submission.lpf_c1r_uniform_remainder :
    ∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ C : Set (Eucl n), IsClosed C →
      (∀ x ∈ C, DifferentiableAt ℝ g x) → ContinuousOn (fderiv ℝ g) C → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ A : Set (Eucl n), IsClosed A ∧ A ⊆ C ∧ (volume : Measure (Eucl n)) (C \ A) < ε ∧
        ∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ δ * ‖y - x‖ := by
  intro n g K hg C hC hdiff hDg ε hε
  -- `q x y = |R(x, y)|`.
  obtain ⟨q, hq⟩ : ∃ q : Eucl n → Eucl n → ℝ,
      ∀ x y, q x y = ‖g y - g x - fderiv ℝ g x (y - x)‖ / ‖y - x‖ := ⟨_, fun _ _ => rfl⟩
  -- Step 2: `|R(x, y)| ≤ 2K`, as `‖Dg(x)‖ ≤ K`.
  have hq_le : ∀ x y, q x y ≤ 2 * K := by
    intro x y
    have h1 : ‖g y - g x‖ ≤ K * ‖y - x‖ := by simpa only [dist_eq_norm] using hg.dist_le_mul y x
    have h2 : ‖fderiv ℝ g x (y - x)‖ ≤ K * ‖y - x‖ :=
      ((fderiv ℝ g x).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hg) (norm_nonneg _))
    rw [hq]
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖g y - g x - fderiv ℝ g x (y - x)‖ ≤ ‖g y - g x‖ + ‖fderiv ℝ g x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ K * ‖y - x‖ + K * ‖y - x‖ := add_le_add h1 h2
      _ = 2 * K * ‖y - x‖ := by ring
  -- Step 1: `σ r x = sup ({0} ∪ {|R(x, y)| : y ∈ C, 0 < |y − x| < r})`, a real number in
  -- `[0, 2K]`, so that `η_k = 1_C · σ (1/(k+1))`.
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → Eucl n → ℝ, ∀ r x,
      σ r x = sSup (insert 0 (q x '' {y | y ∈ C ∧ 0 < ‖y - x‖ ∧ ‖y - x‖ < r})) :=
    ⟨_, fun _ _ => rfl⟩
  have hbdd : ∀ r x,
      BddAbove (insert (0 : ℝ) (q x '' {y | y ∈ C ∧ 0 < ‖y - x‖ ∧ ‖y - x‖ < r})) := by
    refine fun r x => ⟨2 * (K : ℝ), ?_⟩
    rintro a (rfl | ⟨y, -, rfl⟩)
    · positivity
    · exact hq_le x y
  have hσ_nonneg : ∀ r x, 0 ≤ σ r x := by
    intro r x
    rw [hσ]
    exact le_csSup (hbdd r x) (Set.mem_insert _ _)
  have hσ_ge : ∀ r x y, y ∈ C → 0 < ‖y - x‖ → ‖y - x‖ < r → q x y ≤ σ r x := by
    intro r x y hy h0 hr
    rw [hσ]
    exact le_csSup (hbdd r x) (Or.inr ⟨y, ⟨hy, h0, hr⟩, rfl⟩)
  have hσ_le : ∀ r x c, 0 ≤ c → (∀ y, y ∈ C → 0 < ‖y - x‖ → ‖y - x‖ < r → q x y ≤ c) →
      σ r x ≤ c := by
    intro r x c hc h
    rw [hσ]
    refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
    rintro a (rfl | ⟨y, ⟨hy, h0, hr⟩, rfl⟩)
    · exact hc
    · exact h y hy h0 hr
  have hσ_lt : ∀ r x t, 0 ≤ t → t < σ r x →
      ∃ y, y ∈ C ∧ 0 < ‖y - x‖ ∧ ‖y - x‖ < r ∧ t < q x y := by
    intro r x t ht h
    rw [hσ] at h
    obtain ⟨a, ha, hta⟩ := exists_lt_of_lt_csSup ⟨0, Set.mem_insert _ _⟩ h
    rcases ha with rfl | ⟨y, ⟨hy, h0, hr⟩, rfl⟩
    · exact absurd hta (not_lt.mpr ht)
    · exact ⟨y, hy, h0, hr, hta⟩
  -- Step 3: `σ (1/(k+1)) x → 0` for `x ∈ C`, since `g` is differentiable at `x`.
  have htend : ∀ x ∈ C, Tendsto (fun k : ℕ => σ (1 / ((k : ℝ) + 1)) x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro γ hγ
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp
      (Asymptotics.isLittleO_iff.mp (hdiff x hx).hasFDerivAt.isLittleO (half_pos hγ))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
    have hle : σ (1 / ((k : ℝ) + 1)) x ≤ γ / 2 := by
      refine hσ_le _ x _ (half_pos hγ).le fun y _ _ hr => ?_
      rw [hq]
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos hγ).le
        (hball (by rw [dist_eq_norm]; linarith))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hσ_nonneg _ x)]
    linarith
  -- Step 4 (Route 1): `1_C · σ r` is Borel.  For `t ≥ 0`, `{1_C · σ r > t}` is
  -- `C ∩ ⋃_{y ∈ C} (U_y ∩ O_y)`, where `U_y = {x : 0 < |y − x| < r}` and `O_y` is open with
  -- `O_y ∩ C ∩ U_y = {x ∈ C ∩ U_y : |R(x, y)| > t}`; `O_y` exists because `x ↦ |R(x, y)|` is
  -- continuous on `C ∩ U_y` (`Dg` is continuous on `C`).
  have hmeas : ∀ r, Measurable (C.indicator (σ r)) := by
    intro r
    let U : Eucl n → Set (Eucl n) := fun y => {x | 0 < ‖y - x‖ ∧ ‖y - x‖ < r}
    have hU : ∀ y, IsOpen (U y) := fun y =>
      (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).inter
        (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const)
    have hcont : ∀ y, ContinuousOn (fun x => q x y) (C ∩ U y) := by
      intro y
      simp only [hq]
      refine ContinuousOn.div ?_ (continuous_const.sub continuous_id).norm.continuousOn
        fun x hx => hx.2.1.ne'
      exact ((continuous_const.sub hg.continuous).continuousOn.sub
        ((hDg.mono Set.inter_subset_left).clm_apply
          (continuous_const.sub continuous_id).continuousOn)).norm
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · have huniv : C.indicator (σ r) ⁻¹' Ioi t = univ := Set.eq_univ_of_forall fun x =>
        ht.trans_le (Set.indicator_nonneg (fun x _ => hσ_nonneg r x) x)
      rw [huniv]
      exact MeasurableSet.univ
    · choose O hOo hOeq using fun y => _root_.continuousOn_iff'.mp (hcont y) (Ioi t) isOpen_Ioi
      have hset : C.indicator (σ r) ⁻¹' Ioi t = C ∩ ⋃ y ∈ C, (U y ∩ O y) := by
        ext x
        constructor
        · intro hx
          by_cases hxC : x ∈ C
          · rw [Set.mem_preimage, Set.indicator_of_mem hxC, Set.mem_Ioi] at hx
            obtain ⟨y, hyC, h0, hr, hty⟩ := hσ_lt r x t ht hx
            have hxO : x ∈ (fun x => q x y) ⁻¹' Ioi t ∩ (C ∩ U y) := ⟨hty, hxC, h0, hr⟩
            rw [hOeq y] at hxO
            exact ⟨hxC, Set.mem_biUnion hyC ⟨⟨h0, hr⟩, hxO.1⟩⟩
          · rw [Set.mem_preimage, Set.indicator_of_notMem hxC, Set.mem_Ioi] at hx
            exact absurd hx (not_lt.mpr ht)
        · rintro ⟨hxC, hx⟩
          obtain ⟨y, hyC, hxU, hxO⟩ := Set.mem_iUnion₂.mp hx
          have hxO' : x ∈ O y ∩ (C ∩ U y) := ⟨hxO, hxC, hxU⟩
          rw [← hOeq y] at hxO'
          rw [Set.mem_preimage, Set.indicator_of_mem hxC, Set.mem_Ioi]
          exact hxO'.1.trans_le (hσ_ge r x y hyC hxU.1 hxU.2)
      rw [hset]
      exact hC.measurableSet.inter (isOpen_biUnion fun y _ => (hU y).inter (hOo y)).measurableSet
  -- Step 5: Egoroff on `C` (sibling `egoroff_closed`) for `η_k = 1_C · σ (1/(k+1)) → 0`.
  obtain ⟨η, hη⟩ : ∃ η : ℕ → Eucl n → ℝ, ∀ k, η k = C.indicator (σ (1 / ((k : ℝ) + 1))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hAc, hAC, hCA, hunif⟩ := Submission.lpf_c1r_egoroff_closed n C η 0
    hC.measurableSet (fun k => by rw [hη]; exact hmeas _) measurable_const
    (fun x hx => (htend x hx).congr fun k => by rw [hη, Set.indicator_of_mem hx]) ε hε
  refine ⟨A, hAc, hAC, hCA, fun L hL hLA δ hδ => ?_⟩
  -- Step 6: `L ⊆ A ∩ B̄_R(0)` for some `R`, so `η_k < δ` on `L` for some `k`; take `ρ = 1/(k+1)`.
  obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp
    ((hunif R).mono (fun x hx => ⟨hLA hx, hR hx⟩ : L ⊆ A ∩ closedBall 0 R)) δ hδ).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hxL y hyA hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have hxC : x ∈ C := hAC (hLA hxL)
  have h0 : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hr : ‖y - x‖ < 1 / ((k : ℝ) + 1) := by rwa [← dist_eq_norm, dist_comm]
  have hσδ : σ (1 / ((k : ℝ) + 1)) x < δ := by
    have hkx := hk x hxL
    rw [Pi.zero_apply, hη, Set.indicator_of_mem hxC, dist_zero_left, Real.norm_eq_abs] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hqδ := (hσ_ge _ x y (hAC hyA) h0 hr).trans_lt hσδ
  rw [hq, div_lt_iff₀ h0] at hqδ
  exact hqδ.le
/-- Whitney's `C¹` extension theorem (Simon Ch. 2, Theorem 1.6), with derivatives as continuous
linear maps: if `A ⊆ ℝⁿ` is closed and `f`, `τ` are continuous on `A` with the compact-uniform
Taylor condition, then some `C¹` function `h` agrees with `f` on `A` and has derivative `τ a` at
every `a ∈ A`.  Standard construction (Evans–Gariepy §6.5): Whitney radius
`r = min(1, dist(·, A)) / 100`, a Vitali family of disjoint balls `B(c, r c)` whose fourfold
enlargements cover `ℝⁿ ∖ A`, uniformly bounded overlap, rescaled bumps normalized to a partition
of unity `w_c` with `∑ ‖Dw_c(x)‖ ≤ M / r x`, and `h = ∑ w_c P_{q c}` off `A`, where
`P_b(y) = f b + τ b (y - b)` and `q c ∈ A` is a nearest point.  The steps follow the pinned
SimonGMT proof `Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney` (whose
module is not imported here), inlined. -/
theorem Submission.lpf_c1r_whitney_extension :
    ∀ (n : ℕ) (A : Set (Eucl n)) (f : Eucl n → ℝ) (τ : Eucl n → (Eucl n →L[ℝ] ℝ)),
      IsClosed A → ContinuousOn f A → ContinuousOn τ A →
      (∀ L : Set (Eucl n), IsCompact L → L ⊆ A → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧
        ∀ x ∈ L, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - τ x (y - x)‖ ≤ δ * ‖y - x‖) →
      ∃ h : Eucl n → ℝ, ContDiff ℝ 1 h ∧ ∀ a ∈ A, h a = f a ∧ HasFDerivAt h (τ a) a := by
  intro n A f τ hA _hf hτ hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, fun a ha => absurd ha (notMem_empty a)⟩
  -- Step 1: local uniform Taylor estimate near each point of `A`.
  have hloc : ∀ a ∈ A, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖τ b - τ a‖ ≤ ε) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖f c - f b - τ b (c - b)‖ ≤ ε * ‖c - b‖ := by
    intro a ha ε hε
    obtain ⟨ρ, hρ, hρrem⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left ε hε
    obtain ⟨η, hη, hD⟩ := Metric.continuousWithinAt_iff.mp (hτ a ha) ε hε
    have hδ1 : min 1 (min η (ρ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η (ρ / 3)) ≤ η := (min_le_right _ _).trans (min_le_left _ _)
    have hδρ : min 1 (min η (ρ / 3)) ≤ ρ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η (ρ / 3)), lt_min one_pos (lt_min hη (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      have h1 := hD hb (hba.trans_le hδη)
      rw [dist_eq_norm] at h1
      exact h1.le
    · intro b hb hba c hc hca
      refine hρrem b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc ?_
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- Affine jets `P b y = f b + τ b (y - b)`.
  obtain ⟨P, hPdef⟩ : ∃ P : Eucl n → Eucl n → ℝ, ∀ b y, P b y = f b + τ b (y - b) :=
    ⟨fun b y => f b + τ b (y - b), fun _ _ => rfl⟩
  have P_sub : ∀ a b y, ‖P b y - P a y‖ ≤
      ‖f b - f a - τ a (b - a)‖ + ‖τ b - τ a‖ * ‖y - b‖ := by
    intro a b y
    have hid : P b y - P a y = (f b - f a - τ a (b - a)) + (τ b - τ a) (y - b) := by
      have hy : y - a = (y - b) + (b - a) := by abel
      simp only [hPdef, hy, map_add, sub_apply]
      ring
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((τ b - τ a).le_opNorm (y - b)))
  have P_deriv : ∀ b y, HasFDerivAt (P b) (τ b) y := by
    intro b y
    have e : P b = fun y => f b + (τ b y - τ b b) := by
      funext y
      rw [hPdef, map_sub]
    rw [e]
    exact ((τ b).hasFDerivAt.sub_const (τ b b)).const_add (f b)
  have P_cd : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    have e : P b = fun y => f b + τ b (y - b) := funext (hPdef b)
    rw [e]
    exact contDiff_const.add ((τ b).contDiff.comp (contDiff_id.sub contDiff_const))
  -- Step 2: the Whitney radius `r x = min 1 (dist x A) / 100`.
  obtain ⟨r, hr⟩ : ∃ r : Eucl n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨fun x => min 1 (infDist x A) / 100, fun _ => rfl⟩
  have r_nonneg : ∀ x, 0 ≤ r x := by
    intro x
    rw [hr]
    exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have r_le : ∀ x, r x ≤ 1 / 100 := by
    intro x
    rw [hr]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have r_le_inf : ∀ x, 100 * r x ≤ infDist x A := by
    intro x
    rw [hr]
    linarith [min_le_right (1 : ℝ) (infDist x A)]
  have r_pos : ∀ x, x ∉ A → 0 < r x := by
    intro x hx
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have r_le_add : ∀ x y, r x ≤ r y + dist x y / 100 := by
    intro x y
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [hr, hr]
    linarith
  have r_near : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := r_le_add x c
    have h₂ := r_le_add c x
    rw [dist_comm c x] at h₂
    have hx := r_nonneg x
    have hc := r_nonneg c
    exact ⟨by linarith, by linarith, by linarith⟩
  have r_scale : ∀ x, infDist x A ≤ 1 → infDist x A = 100 * r x := by
    intro x hx
    rw [hr, min_eq_right hx]
    ring
  have notMem_of_near : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA
    have hi := infDist_le_dist_of_mem (x := x) hyA
    rw [dist_comm x y] at hi
    linarith [r_le_inf x, r_nonneg x]
  -- Step 3: Vitali selection of disjoint Whitney balls covering `Aᶜ` fourfold.
  obtain ⟨Z, hZA, hZd, hZc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    Aᶜ (fun x : Eucl n => x) r (1 / 100) (fun x _ => r_le x) 4 (by norm_num)
  have Z_cov : ∀ x, x ∉ A → ∃ c ∈ Z, dist x c < 4 * r c := by
    intro x hx
    obtain ⟨c, hcZ, hxc⟩ := hZc x hx
    exact ⟨c, hcZ, hxc (mem_ball_self (r_pos x hx))⟩
  have Z_sep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      rw [mem_ball, dist_comm]
      exact lt_of_not_ge hlt
    have hdd : d ∈ ball d (r d) := mem_ball_self (r_pos d (hZA hd))
    exact Set.disjoint_left.mp (hZd hc hd hcd) hdc hdd
  -- Step 4: bounded overlap, via a uniform packing bound in `closedBall 0 21`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Eucl n), s ⊆ closedBall 0 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Eucl n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hsep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Eucl n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Function.Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Eucl n) ≠ (y : Eucl n) := fun h => hxy' (Subtype.ext h)
      have hd := hsep x.property y.property hne'
      have htri := dist_triangle (x : Eucl n) (c x : Eucl n) (y : Eucl n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Eucl n) (c x : Eucl n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  have hover : ∀ x, x ∉ A →
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
        {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := r_pos x hx
    let sc : Eucl n → Eucl n := fun c => (r x)⁻¹ • (c - x)
    have hsc : Function.Injective sc := by
      intro c d hcd
      have h := congrArg (fun z : Eucl n => r x • z) hcd
      simpa [sc, smul_smul, hrx.ne'] using h
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖sc c‖ ≤ 21 := by
      intro c hc
      have hd := (r_near x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      dsimp [sc]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep : (sc '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun h => hcd (congrArg sc h)
      have hdist := Z_sep c hc.1 d hd.1 hcd'
      have hrad := (r_near x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        rw [← dist_eq_norm]
        exact hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      dsimp [sc]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : sc '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Eucl n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      exact hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep
    exact ⟨hfin.of_finite_image hsc.injOn, by rwa [Set.ncard_image_of_injective _ hsc] at hcard⟩
  -- The finite sets `S x` of centres near `x`.
  have hSex : ∀ x : Eucl n, ∃ s : Finset Z, x ∉ A →
      (∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun h => absurd hx h⟩
    · obtain ⟨hT, hTN⟩ := hover x hx
      have hU : {c : Z | dist x c ≤ r x + 10 * r c}.Finite :=
        (hT.preimage Subtype.val_injective.injOn).subset (fun c hc => ⟨c.2, hc⟩)
      refine ⟨hU.toFinset, fun _ => ⟨fun c => by simp, ?_⟩⟩
      rw [← Set.ncard_eq_toFinset_card _ hU,
        ← Set.ncard_image_of_injective _ Subtype.val_injective]
      refine le_trans (Set.ncard_le_ncard ?_ hT) hTN
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
  choose S hS using hSex
  -- Step 5: rescaled bumps `bp c y = b0 ((y - c) / r c)`, with `b0 = 1` on `B̄(0, 4)` and
  -- `b0 = 0` off `B(0, 8)`.
  obtain ⟨b0, hb0in, hb0out⟩ : ∃ b0 : ContDiffBump (0 : Eucl n), b0.rIn = 4 ∧ b0.rOut = 8 :=
    ⟨⟨4, 8, by norm_num, by norm_num⟩, rfl, rfl⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport b0.hasCompactSupport
    (b0.contDiff (n := 1)) (by simp)
  obtain ⟨bp, hbp⟩ : ∃ bp : Z → Eucl n → ℝ, ∀ c y, bp c y = b0 ((r c)⁻¹ • (y - c)) :=
    ⟨fun c y => b0 ((r c)⁻¹ • (y - c)), fun _ _ => rfl⟩
  have bp_cd : ∀ c, ContDiff ℝ 1 (bp c) := by
    intro c
    have e : bp c = fun y => b0 ((r c)⁻¹ • (y - c)) := funext (hbp c)
    rw [e]
    exact (b0.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).const_smul _)
  have bp_nonneg : ∀ c y, 0 ≤ bp c y := by
    intro c y
    rw [hbp]
    exact b0.nonneg
  have bp_le_one : ∀ c y, bp c y ≤ 1 := by
    intro c y
    rw [hbp]
    exact b0.le_one
  have bp_one : ∀ (c : Z) (y : Eucl n), dist y c ≤ 4 * r c → bp c y = 1 := by
    intro c y hy
    have hc : 0 < r c := r_pos c (hZA c.2)
    rw [hbp]
    apply b0.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le),
      hb0in]
    rw [dist_eq_norm] at hy
    calc (r c)⁻¹ * ‖y - c‖ ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have bp_zero : ∀ (c : Z) (y : Eucl n), 8 * r c ≤ dist y c → bp c y = 0 := by
    intro c y hy
    have hc : 0 < r c := r_pos c (hZA c.2)
    rw [hbp]
    apply Function.notMem_support.mp
    rw [b0.support_eq, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hc.le), hb0out, not_lt]
    rw [dist_eq_norm] at hy
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * ‖y - c‖ := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, bp_der⟩ : ∃ B : ℝ, 0 < B ∧
      ∀ (c : Z) (y : Eucl n), ‖fderiv ℝ (bp c) y‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c y => ?_⟩
    have hc : 0 < r c := r_pos c (hZA c.2)
    let ρ : ℝ≥0 := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Eucl n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (bp c) := by
      have e : bp c = b0 ∘ (fun y : Eucl n => (r c)⁻¹ • (y - c)) := funext (hbp c)
      rw [e]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := y)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (bp c) y‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- Step 6: the partition of unity `w c = bp c / sm`, `sm = ∑ᶠ c, bp c`, on `Aᶜ`.
  have bp_far : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c : Z, c ∉ S x → bp c y = 0 := by
    intro x hx y hy c hc
    apply bp_zero c y
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun h => hc (((hS x hx).1 c).mpr h)
    have ht := dist_triangle x y (c : Eucl n)
    rw [dist_comm x y] at ht
    have := r_nonneg c
    linarith
  obtain ⟨sm, hsm⟩ : ∃ sm : Eucl n → ℝ, ∀ y, sm y = ∑ᶠ c : Z, bp c y :=
    ⟨fun y => ∑ᶠ c : Z, bp c y, fun _ => rfl⟩
  have sm_eq : ∀ x, x ∉ A → ∀ y, dist y x < r x → sm y = ∑ c ∈ S x, bp c y := by
    intro x hx y hy
    rw [hsm]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra h
    exact hc (bp_far x hx y hy c h)
  have sm_ge : ∀ x, x ∉ A → 1 ≤ sm x := by
    intro x hx
    have hrx := r_pos x hx
    rw [sm_eq x hx x (by rw [dist_self]; exact hrx)]
    obtain ⟨c, hcZ, hxc⟩ := Z_cov x hx
    have hi : (⟨c, hcZ⟩ : Z) ∈ S x := by
      rw [(hS x hx).1]
      have := r_nonneg c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = bp ⟨c, hcZ⟩ x := (bp_one ⟨c, hcZ⟩ x hxc.le).symm
      _ ≤ ∑ c ∈ S x, bp c x :=
          Finset.single_le_sum (f := fun c : Z => bp c x) (fun c _ => bp_nonneg c x) hi
  have sm_cd : ∀ x, x ∉ A → ContDiffAt ℝ 1 sm x := by
    intro x hx
    have hs : ContDiff ℝ 1 (fun y => ∑ c ∈ S x, bp c y) := ContDiff.sum (fun c _ => bp_cd c)
    apply hs.contDiffAt.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
    exact sm_eq x hx y hy
  have sm_fderiv : ∀ x, x ∉ A → fderiv ℝ sm x = ∑ c ∈ S x, fderiv ℝ (bp c) x := by
    intro x hx
    have heq : sm =ᶠ[𝓝 x] (fun y => ∑ c ∈ S x, bp c y) := by
      filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
      exact sm_eq x hx y hy
    rw [heq.fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (bp_cd c).differentiable one_ne_zero x)
  obtain ⟨w, hw⟩ : ∃ w : Z → Eucl n → ℝ, ∀ c y, w c y = bp c y / sm y :=
    ⟨fun c y => bp c y / sm y, fun _ _ => rfl⟩
  have w_cd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    have e : w c = bp c / sm := funext (hw c)
    rw [e]
    exact (bp_cd c).contDiffAt.div (sm_cd x hx) (ne_of_gt (lt_of_lt_of_le one_pos (sm_ge x hx)))
  have w_nonneg : ∀ c x, x ∉ A → 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (bp_nonneg c x) (zero_le_one.trans (sm_ge x hx))
  have w_zero : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c : Z, c ∉ S x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, bp_far x hx y hy c hc, zero_div]
  have w_sum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ S x, w c y = 1 := by
    intro x hx y hy
    have hyA := notMem_of_near x hx y hy
    simp only [hw, ← Finset.sum_div, ← sm_eq x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (sm_ge y hyA)))
  have w_dsum : ∀ x, x ∉ A → ∑ c ∈ S x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ S x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
      exact w_sum x hx y hy
    have hh := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh
    rw [fderiv_fun_sum (fun c _ => (w_cd c x hx).differentiableAt one_ne_zero)] at hh
    exact hh
  -- Step 7: `‖D w_c‖ ≤ ‖D bp_c‖ + ‖D sm‖` and the summed bound `M / r x`.
  have w_der : ∀ c x, x ∉ A →
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (bp c) x‖ + ‖fderiv ℝ sm x‖ := by
    intro c x hx
    have hS1 : 1 ≤ sm x := sm_ge x hx
    have hSpos : 0 < sm x := lt_of_lt_of_le one_pos hS1
    have hSi : (sm x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1
    have hSi2 : (sm x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ sm x ^ 2 by nlinarith)
    have hb := ((bp_cd c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((sm_cd x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x) + (sm x)⁻¹ • fderiv ℝ (bp c) x := by
      have e : w c = fun y => bp c y * ((fun t : ℝ => t⁻¹) ∘ sm) y := by
        funext y
        rw [hw, div_eq_mul_inv]
        rfl
      rw [e]
      exact hprod.fderiv
    rw [hder]
    have hb0 := bp_nonneg c x
    have hb1 := bp_le_one c x
    calc ‖bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x) + (sm x)⁻¹ • fderiv ℝ (bp c) x‖
        ≤ ‖bp c x • (-(sm x ^ 2)⁻¹ • fderiv ℝ sm x)‖ + ‖(sm x)⁻¹ • fderiv ℝ (bp c) x‖ :=
          norm_add_le _ _
      _ = bp c x * ((sm x ^ 2)⁻¹ * ‖fderiv ℝ sm x‖) + (sm x)⁻¹ * ‖fderiv ℝ (bp c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (sm x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (bp c) x‖ + ‖fderiv ℝ sm x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (bp c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ sm x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (sm x))) (norm_nonneg (fderiv ℝ sm x)))
          linarith
  obtain ⟨M, hM, w_dbound⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x, x ∉ A →
      ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := r_pos x hx
    have hT : 0 ≤ 2 * B / r x := by positivity
    have hb' : ∀ c ∈ S x, ‖fderiv ℝ (bp c) x‖ ≤ 2 * B / r x := by
      intro c hc
      have hlow := (r_near x c (((hS x hx).1 c).mp hc)).1
      refine (bp_der c x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = 2 * B / r x := by ring
    have hcard : ((S x).card : ℝ) ≤ N := by exact_mod_cast (hS x hx).2
    have hsum : ‖fderiv ℝ sm x‖ ≤ (N : ℝ) * (2 * B / r x) := by
      rw [sm_fderiv x hx]
      calc ‖∑ c ∈ S x, fderiv ℝ (bp c) x‖ ≤ ∑ c ∈ S x, ‖fderiv ℝ (bp c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ S x, 2 * B / r x := Finset.sum_le_sum hb'
        _ = ((S x).card : ℝ) * (2 * B / r x) := by simp
        _ ≤ (N : ℝ) * (2 * B / r x) := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ S x, ‖fderiv ℝ (w c) x‖ ≤ 2 * B / r x + (N : ℝ) * (2 * B / r x) :=
      fun c hc => (w_der c x hx).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖
        ≤ ∑ _c ∈ S x, (2 * B / r x + (N : ℝ) * (2 * B / r x)) := Finset.sum_le_sum hw'
      _ = ((S x).card : ℝ) * (2 * B / r x + (N : ℝ) * (2 * B / r x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * B / r x + (N : ℝ) * (2 * B / r x)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * (2 * B / r x) := by
          nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by ring
  -- Step 8: nearest-point anchors.
  choose q hqA hqd using fun x => hA.exists_infDist_eq_dist hne x
  have q_le : ∀ x a, a ∈ A → dist x (q x) ≤ dist x a := by
    intro x a ha
    rw [← hqd]
    exact infDist_le_dist_of_mem ha
  have q_pt : ∀ x a, a ∈ A → dist (q x) a ≤ 2 * dist x a := by
    intro x a ha
    have h1 := dist_triangle (q x) x a
    rw [dist_comm (q x) x] at h1
    linarith [q_le x a ha]
  have anchor1 : ∀ x, x ∉ A → ∀ c ∈ S x, dist x (q c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hc' := ((hS x hx).1 c).mp hc
    have hd := (r_near x c hc').2.2
    have hr' := r_le_inf x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Eucl n)) (y := x)
    have ht := dist_triangle x (c : Eucl n) (q c)
    rw [dist_comm (c : Eucl n) x] at hi
    rw [← hqd (c : Eucl n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have anchor2 : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ S x, dist (q c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := anchor1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (q c) x a
    rw [dist_comm (q c) x] at ht
    linarith
  -- Convex combinations of vectors of norm `≤ b` have norm `≤ b`.
  have convex_le : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (s : Finset Z)
      (u : Z → ℝ) (v : Z → F) (b : ℝ), (∀ i ∈ s, 0 ≤ u i) → ∑ i ∈ s, u i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, u i • v i‖ ≤ b := by
    intro F _ _ s u v b hu hs hv
    calc ‖∑ i ∈ s, u i • v i‖ ≤ ∑ i ∈ s, ‖u i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, u i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (hu i hi)]
      _ ≤ ∑ i ∈ s, u i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (hu i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- Step 9: the extension.
  obtain ⟨g, hg⟩ : ∃ g : Eucl n → ℝ,
      ∀ y, g y = if y ∈ A then f y else ∑ᶠ c : Z, w c y * P (q c) y :=
    ⟨fun y => if y ∈ A then f y else ∑ᶠ c : Z, w c y * P (q c) y, fun _ => rfl⟩
  have g_on : ∀ a ∈ A, g a = f a := by
    intro a ha
    rw [hg, ite_eq_left ha]
  have g_near : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ S x, w c y * P (q c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (notMem_of_near x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (q c) y = 0
    rw [w_zero x hx y hy c hc', zero_mul]
  have g_ev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] (fun y => ∑ c ∈ S x, w c y * P (q c) y) := by
    intro x hx
    filter_upwards [ball_mem_nhds x (r_pos x hx)] with y hy
    exact g_near x hx y hy
  have g_cd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ S x, w c y * P (q c) y) x :=
      ContDiffAt.sum (fun c _ => (w_cd c x hx).mul (P_cd _).contDiffAt)
    exact hs.congr_of_eventuallyEq (g_ev x hx)
  have g_fderiv : ∀ x, x ∉ A → fderiv ℝ g x =
      ∑ c ∈ S x, (w c x • τ (q c) + P (q c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(g_ev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((w_cd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (P_deriv _ x)
  have g_sub : ∀ a x, x ∉ A → g x - P a x = ∑ c ∈ S x, w c x * (P (q c) x - P a x) := by
    intro a x hx
    have hx' : dist x x < r x := by
      rw [dist_self]
      exact r_pos x hx
    rw [g_near x hx x hx']
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, w_sum x hx x hx', one_mul]
  -- Step 10: `g` has derivative `τ a` at every `a ∈ A`.
  have g_deriv : ∀ a ∈ A, HasFDerivAt g (τ a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, _hδ1, hD, hR⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by
      rw [dist_self]
      exact hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [g_on a ha]
    by_cases hxA : x ∈ A
    · rw [g_on x hxA]
      have hr' := hR a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hid : g x - f a - τ a (x - a) = g x - P a x := by
        rw [hPdef a x]
        ring
      rw [hid, g_sub a x hxA]
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact r_pos x hxA
      have key := convex_le ℝ (S x) (fun c => w c x) (fun c => P (q c) x - P a x) (ε * ‖x - a‖)
        (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') ?_
      · simpa only [smul_eq_mul] using key
      intro c hc
      have hbA : q c ∈ A := hqA c
      have hba : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
      have hxb : dist x (q c) ≤ 2 * dist x a :=
        (anchor1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (q c) a < δ := by linarith
      have hDb := hD (q c) hbA hbaδ
      have hr' := hR a ha haa (q c) hbA hbaδ
      have hba' : ‖q c - a‖ ≤ 3 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hba
      have hxb' : ‖x - q c‖ ≤ 2 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hxb
      calc ‖P (q c) x - P a x‖
          ≤ ‖f (q c) - f a - τ a (q c - a)‖ + ‖τ (q c) - τ a‖ * ‖x - q c‖ := P_sub a (q c) x
        _ ≤ (ε / 5) * ‖q c - a‖ + (ε / 5) * ‖x - q c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  have g_fderiv_on : ∀ a ∈ A, fderiv ℝ g a = τ a := fun a ha => (g_deriv a ha).fderiv
  -- Step 11: `Dg` is continuous at every `a ∈ A`.
  have g_cont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    have hK : (0 : ℝ) < 1 + 700 * M := by positivity
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by
      rw [hηdef]
      field_simp
    have hηε : η ≤ ε / 2 := by nlinarith
    obtain ⟨δ, hδ, hδ1, hD, hR⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [g_fderiv_on a ha, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [g_fderiv_on x hxA]
      exact (hD x hxA (by linarith)).trans hηε
    · have hrx := r_pos x hxA
      have hbA : q x ∈ A := hqA x
      have hba : dist (q x) a ≤ 2 * dist x a := q_pt x a ha
      have hbaδ : dist (q x) a < δ := by linarith
      have hDb := hD (q x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := r_scale x hdx
      have hD' : ∀ c ∈ S x, ‖τ (q c) - τ a‖ ≤ η := by
        intro c hc
        apply hD _ (hqA c)
        have hi := anchor2 x hxA a ha c hc
        linarith
      have hP' : ∀ c ∈ S x, ‖P (q c) x - P (q x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA : q c ∈ A := hqA c
        have hda : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
        have hdaδ : dist (q c) a < δ := by linarith
        have hxd : dist x (q c) ≤ 2 * infDist x A := anchor1 x hxA c hc
        have hxb : dist x (q x) = infDist x A := (hqd x).symm
        have hdb : dist (q c) (q x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (q c) x (q x)
          rw [dist_comm (q c) x, hxb] at ht
          linarith
        have hDd : ‖τ (q c) - τ (q x)‖ ≤ 2 * η := by
          calc ‖τ (q c) - τ (q x)‖ = ‖(τ (q c) - τ a) - (τ (q x) - τ a)‖ := by
                congr 1
                abel
            _ ≤ ‖τ (q c) - τ a‖ + ‖τ (q x) - τ a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hR (q x) hbA hbaδ (q c) hdA hdaδ
        have hdb' : ‖q c - q x‖ ≤ 3 * infDist x A := by
          rw [← dist_eq_norm]
          exact hdb
        have hxd' : ‖x - q c‖ ≤ 2 * infDist x A := by
          rw [← dist_eq_norm]
          exact hxd
        calc ‖P (q c) x - P (q x) x‖
            ≤ ‖f (q c) - f (q x) - τ (q x) (q c - q x)‖ + ‖τ (q c) - τ (q x)‖ * ‖x - q c‖ :=
              P_sub (q x) (q c) x
          _ ≤ η * ‖q c - q x‖ + (2 * η) * ‖x - q c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by
              rw [hscale]
              ring
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact hrx
      have hdecomp : fderiv ℝ g x - τ a =
          (∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x := by
        rw [g_fderiv x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, w_sum x hxA x hx', w_dsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hdecomp]
      calc ‖(∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ S x, w c x • (τ (q c) - τ a)‖ +
            ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact convex_le _ (S x) (fun c => w c x) (fun c => τ (q c) - τ a) η
                (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') hD'
            · calc ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ S x, ‖(P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_sum_le _ _
                _ ≤ ∑ c ∈ S x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (w_dbound x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by
            field_simp
        _ = ε / 2 := heq
  -- Step 12: conclusion.
  refine ⟨g, ?_, fun a ha => ⟨g_on a ha, g_deriv a ha⟩⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (g_deriv x hx).differentiableAt
    · exact (g_cd x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact g_cont x hx
    · exact (g_cd x hx).continuousAt_fderiv one_ne_zero

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42), in the form established by its
printed proof (p. 44): a Lipschitz `g : ℝⁿ → ℝ` agrees with a `C¹` function `h` on a closed set `A`
with `Lⁿ(ℝⁿ ∖ A) < ε`, and `g` is differentiable on `A` with `Dg = Dh` there.  Rademacher gives a
Borel set `D` of full measure where `g` is differentiable; Lusin gives a closed `C ⊆ D` with `Dg|C`
continuous; the `η_k` step gives a closed `A ⊆ C` satisfying Whitney's condition (‡) (Thm 1.6);
Whitney's extension theorem then gives `h`. -/
theorem Submission.lpf_c1_approximation_real :
    ∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧ (volume : Measure (Eucl n)) Aᶜ < ε ∧
        ContDiff ℝ 1 h ∧ ∀ x ∈ A, g x = h x ∧ HasFDerivAt g (fderiv ℝ h x) x := by
  intro n g K hg ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Rademacher: `g` is differentiable on the Borel set `D`, and `Lⁿ(ℝⁿ ∖ D) = 0`.
  set D : Set (Eucl n) := {x | DifferentiableAt ℝ g x}
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  have hDc : (volume : Measure (Eucl n)) Dᶜ = 0 := ae_iff.1 hg.ae_differentiableAt
  -- Lusin: a closed `C ⊆ D` with `Lⁿ(D ∖ C) < ε / 2` on which `Dg` is continuous.
  obtain ⟨C, hCc, hCD, hDC, hgC⟩ := Submission.lpf_c1r_lusin_closed n D (fderiv ℝ g) hDm
    (measurable_fderiv ℝ g) (ε / 2) hε2
  -- The `η_k` step: a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε / 2` satisfying Whitney's (‡) for
  -- `(g, Dg)`.
  obtain ⟨A, hAc, hAC, hCA, hrem⟩ := Submission.lpf_c1r_uniform_remainder n g K hg C hCc
    (fun x hx => hCD hx) hgC (ε / 2) hε2
  -- Whitney: a `C¹` function `h` with `h = g` and `Dh = Dg` on `A`.
  obtain ⟨h, hh, hhA⟩ := Submission.lpf_c1r_whitney_extension n A g (fderiv ℝ g) hAc
    hg.continuous.continuousOn (hgC.mono hAC) hrem
  refine ⟨A, h, hAc, ?_, hh, fun x hx => ?_⟩
  · -- `ℝⁿ ∖ A ⊆ (ℝⁿ ∖ D) ∪ (D ∖ C) ∪ (C ∖ A)`, so `Lⁿ(ℝⁿ ∖ A) < 0 + ε / 2 + ε / 2 = ε`.
    have hsub : Aᶜ ⊆ Dᶜ ∪ (D \ C) ∪ (C \ A) := by
      intro x hxA
      by_cases hxD : x ∈ D
      · by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        · exact Or.inl (Or.inr ⟨hxD, hxC⟩)
      · exact Or.inl (Or.inl hxD)
    calc (volume : Measure (Eucl n)) Aᶜ ≤ volume (Dᶜ ∪ (D \ C) ∪ (C \ A)) := measure_mono hsub
      _ ≤ volume Dᶜ + volume (D \ C) + volume (C \ A) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = volume (D \ C) + volume (C \ A) := by rw [hDc, zero_add]
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hDC hCA
      _ = ε := ENNReal.add_halves ε
  · -- `Dh(x) = Dg(x)` by uniqueness of the derivative, and `g` is differentiable at `x ∈ A ⊆ D`.
    obtain ⟨hhx, hDhx⟩ := hhA x hx
    rw [hDhx.fderiv]
    exact ⟨hhx.symm, DifferentiableAt.hasFDerivAt (hCD (hAC hx))⟩

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) for `ℝ^Q`-valued maps, applied
componentwise as in the proof of Ch. 6, Lemma 3.9 (p. 148): a Lipschitz `u : ℝⁿ → ℝ^Q` agrees
with a `C¹` map `G`, and has Fréchet derivative `DG(x)`, at every `x` of a closed set `A` with
`Lⁿ(ℝⁿ ∖ A) < ε`. -/
theorem Submission.lpf_c1_approximation_eucl :
    ∀ (n Q : ℕ) (u : Eucl n → Eucl Q) (K : ℝ≥0), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (G : Eucl n → Eucl Q), IsClosed A ∧
        (volume : Measure (Eucl n)) Aᶜ < ε ∧ ContDiff ℝ 1 G ∧
        ∀ x ∈ A, u x = G x ∧ HasFDerivAt u (fderiv ℝ G x) x := by
  intro n Q u K hu ε hε
  -- Split `ε`: `δ > 0` with `Q δ < ε`.
  obtain ⟨δ, hδ, hδQ⟩ := ENNReal.exists_pos_mul_lt (ENNReal.natCast_ne_top Q) hε.ne'
  -- The scalar theorem for each component `u_l = π_l ∘ u`, which is `‖π_l‖ K`-Lipschitz: a closed
  -- `A_l` with `Lⁿ(ℝⁿ ∖ A_l) < δ` and a `C¹` `h_l` with `u_l = h_l`, `Du_l = Dh_l` on `A_l`.
  have hcomp : ∀ l : Fin Q, ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧
      (volume : Measure (Eucl n)) Aᶜ < δ ∧ ContDiff ℝ 1 h ∧
      ∀ x ∈ A, u x l = h x ∧ HasFDerivAt (fun y => u y l) (fderiv ℝ h x) x := fun l =>
    Submission.lpf_c1_approximation_real n (fun y => u y l) _
      ((EuclideanSpace.proj (𝕜 := ℝ) l).lipschitzWith.comp hu) δ hδ
  choose A h hA hAδ hh hAh using hcomp
  -- Every `y ∈ ℝ^Q` is `∑_l y_l e_l`, `e_l = EuclideanSpace.single l 1`.
  have hsum : ∀ y : Eucl Q, ∑ l, y l • EuclideanSpace.single l (1 : ℝ) = y := fun y => by
    have hy := (EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr y
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hy
    exact hy
  -- `A = ⋂_l A_l` and `G = ∑_l h_l e_l`.
  refine ⟨⋂ l, A l, fun x => ∑ l, h l x • EuclideanSpace.single l (1 : ℝ), isClosed_iInter hA,
    ?_, ContDiff.sum fun l _ => (hh l).smul_const _, ?_⟩
  · -- `Lⁿ(ℝⁿ ∖ A) ≤ ∑_l Lⁿ(ℝⁿ ∖ A_l) ≤ Q δ < ε`.
    rw [compl_iInter]
    calc (volume : Measure (Eucl n)) (⋃ l, (A l)ᶜ)
        ≤ ∑ l, (volume : Measure (Eucl n)) (A l)ᶜ := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _l : Fin Q, δ := Finset.sum_le_sum fun l _ => (hAδ l).le
      _ = δ * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ < ε := hδQ
  · intro x hx
    rw [mem_iInter] at hx
    -- `G` and `u = ∑_l u_l e_l` both have derivative `Λ = ∑_l (Dh_l(x)).smulRight e_l` at `x`.
    have hG : HasFDerivAt (fun y => ∑ l, h l y • EuclideanSpace.single l (1 : ℝ))
        (∑ l, (fderiv ℝ (h l) x).smulRight (EuclideanSpace.single l (1 : ℝ))) x :=
      HasFDerivAt.fun_sum fun l _ =>
        ((hh l).differentiable one_ne_zero x).hasFDerivAt.smul_const _
    have hu' : HasFDerivAt (fun y => ∑ l, u y l • EuclideanSpace.single l (1 : ℝ))
        (∑ l, (fderiv ℝ (h l) x).smulRight (EuclideanSpace.single l (1 : ℝ))) x :=
      HasFDerivAt.fun_sum fun l _ => (hAh l x (hx l)).2.smul_const _
    rw [show (fun y => ∑ l, u y l • EuclideanSpace.single l (1 : ℝ)) = u from
      funext fun y => hsum (u y)] at hu'
    refine ⟨?_, ?_⟩
    · rw [← hsum (u x)]
      exact Finset.sum_congr rfl fun l _ => by rw [(hAh l x (hx l)).1]
    · rw [hG.fderiv]
      exact hu'
/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9 (p. 148): the
inverse-function-theorem estimate.  If `G : ℝⁿ → ℝ^Q` is `C¹` and `DG(w)` is injective, then
`c |z − z'| ≤ |G z − G z'|` for all `z, z'` in some ball `B_r(w)`, with `c > 0`. -/
theorem Submission.lpf_c1_local_antilipschitz :
    ∀ (n Q : ℕ) (G : Eucl n → Eucl Q) (w : Eucl n), ContDiff ℝ 1 G →
      Function.Injective (fderiv ℝ G w) →
      ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ ball w r, ∀ z' ∈ ball w r,
        c * ‖z - z'‖ ≤ ‖G z - G z'‖ := by
  intro n Q G w hG hinj
  set A : Eucl n →L[ℝ] Eucl Q := fderiv ℝ G w
  -- `A` is injective on the finite-dimensional `ℝⁿ`, hence antilipschitz: `|v| ≤ K |A v|`,
  -- i.e. `|A v| ≥ m |v|` with `m = K⁻¹ > 0`.
  obtain ⟨K, hKpos, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q)).mp hinj
  have hK0 : (0 : ℝ) < K := hKpos
  have hm : ∀ v : Eucl n, (K : ℝ)⁻¹ * ‖v‖ ≤ ‖A v‖ := by
    intro v
    rw [inv_mul_le_iff₀ hK0]
    exact ZeroHomClass.bound_of_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q) hK v
  -- `c = m / 2`.  `A` is the strict derivative of `G` at `w`, so `G` approximates `A` with
  -- constant `c` on a neighbourhood of `w`, which contains a ball `B_r(w)`.
  set c : ℝ≥0 := K⁻¹ / 2 with hc
  have hc0 : 0 < c := by
    rw [hc]
    exact div_pos (inv_pos.mpr hKpos) two_pos
  have hcK : (c : ℝ) = (K : ℝ)⁻¹ / 2 := by
    rw [hc, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_two]
  have hstrict : HasStrictFDerivAt G A w := hG.hasStrictFDerivAt one_ne_zero
  obtain ⟨s, hs, happrox⟩ := hstrict.approximates_deriv_on_nhds (c := c) (Or.inr hc0)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r, hr, c, hc0, fun z hz z' hz' => ?_⟩
  -- On `B_r(w)`, `|G z − G z' − A (z − z')| ≤ c |z − z'|`; with the triangle inequality,
  -- `m |z − z'| ≤ |A (z − z')| ≤ |G z − G z'| + c |z − z'|`, and `m − c = c`.
  have h1 : ‖G z - G z' - A (z - z')‖ ≤ c * ‖z - z'‖ := happrox z (hrs hz) z' (hrs hz')
  have h2 := hm (z - z')
  have h3 : ‖A (z - z')‖ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := by
    calc ‖A (z - z')‖ = ‖(G z - G z') - (G z - G z' - A (z - z'))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := norm_sub_le _ _
  rw [hcK] at h1 ⊢
  linarith
/-- Countable localization of a locally Lipschitz map: open sets `B m ⊆ Ω` covering `Ω` and
globally Lipschitz maps `v m` agreeing with `u` on `B m` (Lindelöf, then Lipschitz extension). -/
theorem Submission.lpf_lipschitz_localization :
    ∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u →
      ∃ (B : ℕ → Set (Eucl n)) (v : ℕ → Eucl n → Eucl Q), (∀ m, IsOpen (B m)) ∧
        (∀ m, B m ⊆ Ω) ∧ Ω ⊆ ⋃ m, B m ∧ (∀ m, ∃ K : ℝ≥0, LipschitzWith K (v m)) ∧
        ∀ m, EqOn u (v m) (B m) := by
  intro n Q Ω u hΩ hu
  -- Each `w ∈ Ω` has an open neighbourhood `V w ⊆ Ω` on which `u` is Lipschitz.
  have hV : ∀ w : Ω, ∃ V : Set (Eucl n), IsOpen V ∧ V ⊆ Ω ∧ (w : Eucl n) ∈ V ∧
      ∃ K : ℝ≥0, LipschitzOnWith K u V := by
    rintro ⟨w, hw⟩
    obtain ⟨K, t, ht, hK⟩ := hu hw
    obtain ⟨o, ho, hwo, hot⟩ := mem_nhdsWithin.1 ht
    exact ⟨o ∩ Ω, ho.inter hΩ, inter_subset_right, ⟨hwo, hw⟩, K, hK.mono hot⟩
  choose V hVo hVΩ hwV hVK using hV
  -- Lindelöf: countably many `V w` already cover `Ω`.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hΩT : Ω ⊆ ⋃ w ∈ T, V w := fun x hx => hTU ▸ mem_iUnion.2 ⟨⟨x, hx⟩, hwV _⟩
  -- Extend `u` from each `V w` to a globally Lipschitz map `g w`.
  have hext : ∀ w : Ω, ∃ g : Eucl n → Eucl Q, (∃ K : ℝ≥0, LipschitzWith K g) ∧
      EqOn u g (V w) := fun w => by
    obtain ⟨K, hK⟩ := hVK w
    obtain ⟨g, hg, hug⟩ := hK.extend_finite_dimension
    exact ⟨g, ⟨_, hg⟩, hug⟩
  choose g hg hug using hext
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- `T = ∅` forces `Ω = ∅`: take empty sets and the zero map.
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, fun _ => empty_subset _, ?_,
      fun _ => ⟨0, LipschitzWith.const 0⟩, fun _ => eqOn_empty _ _⟩
    simpa [hT] using hΩT
  · -- Enumerate the nonempty countable `T` as `range f`.
    obtain ⟨f, rfl⟩ := hTc.exists_eq_range hT
    refine ⟨fun m => V (f m), fun m => g (f m), fun m => hVo _, fun m => hVΩ _, ?_,
      fun m => hg _, fun m => hug _⟩
    rwa [biUnion_range] at hΩT

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) combined with the
inverse-function-theorem estimate of Ch. 3, Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9
(p. 148).  A map `u : ℝⁿ → ℝ^Q` that is locally Lipschitz on an open `Ω` agrees, together with its
derivative, with `C¹` maps `G_k` on pairwise disjoint Borel sets `E_k ⊆ O_k ∩ Ω`, where `G_k` is
antilipschitz on the open set `O_k`; and `Lⁿ`-a.e. point of `Ω` at which `u` has an injective
derivative lies in `⋃_k E_k`. -/
theorem Submission.lpf_lipschitz_c1_immersion_pieces :
    ∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u →
      ∃ (G : ℕ → Eucl n → Eucl Q) (O E : ℕ → Set (Eucl n)), (∀ k, IsOpen (O k)) ∧
        (∀ k, ContDiff ℝ 1 (G k)) ∧
        (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G k w - G k w'‖) ∧
        (∀ k, MeasurableSet (E k)) ∧ (∀ k, E k ⊆ O k ∩ Ω) ∧
        Pairwise (Function.onFun Disjoint E) ∧
        (∀ k, ∀ w ∈ E k, u w = G k w ∧ HasFDerivAt u (fderiv ℝ (G k) w) w) ∧
        ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω →
          (∃ D : Eucl n →L[ℝ] Eucl Q, HasFDerivAt u D w ∧ Function.Injective D) →
            w ∈ ⋃ k, E k := by
  intro n Q Ω u hΩ hu
  -- Open sets `B m ⊆ Ω` covering `Ω`, and Lipschitz maps `v m` with `u = v m` on `B m`.
  obtain ⟨B, v, hBo, hBΩ, hΩB, hv, huv⟩ := Submission.lpf_lipschitz_localization n Q Ω u hΩ hu
  choose K hK using hv
  -- C¹ approximation of `v m` with `ε = 1 / i`: closed sets `A m i` with `Lⁿ(ℝⁿ ∖ A m i) < 1 / i`
  -- and `C¹` maps `G m i` with `v m = G m i` and `D(v m) = D(G m i)` on `A m i`.
  have happrox : ∀ m i : ℕ, ∃ (A : Set (Eucl n)) (G : Eucl n → Eucl Q), IsClosed A ∧
      (volume : Measure (Eucl n)) Aᶜ < (i : ℝ≥0∞)⁻¹ ∧ ContDiff ℝ 1 G ∧
      ∀ x ∈ A, v m x = G x ∧ HasFDerivAt (v m) (fderiv ℝ G x) x := fun m i =>
    Submission.lpf_c1_approximation_eucl n Q (v m) (K m) (hK m) _
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
  choose A G hAc hA hG hAG using happrox
  -- On `B m ∩ A m i`, `u = G m i` and `Du = D(G m i)`, because `u = v m` on the open set `B m`.
  have huG : ∀ m i, ∀ w ∈ B m ∩ A m i, u w = G m i w ∧ HasFDerivAt u (fderiv ℝ (G m i) w) w := by
    rintro m i w ⟨hwB, hwA⟩
    exact ⟨(huv m hwB).trans (hAG m i w hwA).1, (hAG m i w hwA).2.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem ((hBo m).mem_nhds hwB) (huv m))⟩
  -- A sequence `b j` of open sets forming a basis of the topology of `ℝⁿ`.
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (Eucl n)
  -- Index `k ↔ (m, i, j)`.  The triple is *good* when `b j ⊆ B m` and `G m i` is antilipschitz on
  -- `b j`; then `O k := b j`, otherwise `O k := ∅`.  `E' k := O k ∩ B m ∩ A m i`, and
  -- `E := disjointed E'`.
  classical
  let good : ℕ × ℕ × ℕ → Prop := fun t => b t.2.2 ⊆ B t.1 ∧
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ b t.2.2, ∀ w' ∈ b t.2.2, c * ‖w - w'‖ ≤ ‖G t.1 t.2.1 w - G t.1 t.2.1 w'‖
  let idx : ℕ → ℕ × ℕ × ℕ := fun k => ((Nat.unpair k).1, Nat.unpair (Nat.unpair k).2)
  let O : ℕ → Set (Eucl n) := fun k => if good (idx k) then b (idx k).2.2 else ∅
  let E' : ℕ → Set (Eucl n) := fun k => O k ∩ (B (idx k).1 ∩ A (idx k).1 (idx k).2.1)
  have hOo : ∀ k, IsOpen (O k) := by
    intro k
    by_cases h : good (idx k)
    · simp only [O, ite_eq_left h]
      exact hb.isOpen ⟨_, rfl⟩
    · simp only [O, ite_eq_right h]
      exact isOpen_empty
  have hE' : ∀ k, MeasurableSet (E' k) := fun k =>
    (hOo k).measurableSet.inter ((hBo _).measurableSet.inter (hAc _ _).measurableSet)
  refine ⟨fun k => G (idx k).1 (idx k).2.1, O, disjointed E', hOo, fun k => hG _ _, ?_,
    MeasurableSet.disjointed hE', ?_, disjoint_disjointed E', ?_, ?_⟩
  · -- `G k` is antilipschitz on `O k` (vacuously if `O k = ∅`).
    intro k
    by_cases h : good (idx k)
    · simp only [O, ite_eq_left h]
      exact h.2
    · simp only [O, ite_eq_right h]
      exact ⟨1, one_pos, fun w hw => absurd hw (notMem_empty w)⟩
  · -- `E k ⊆ E' k ⊆ O k ∩ B m ⊆ O k ∩ Ω`.
    intro k w hw
    have hw' : w ∈ E' k := disjointed_subset E' k hw
    exact ⟨hw'.1, hBΩ _ hw'.2.1⟩
  · intro k w hw
    have hw' : w ∈ E' k := disjointed_subset E' k hw
    exact huG _ _ w hw'.2
  · -- For each `m`, the points outside every `A m i` form a null set, as `Lⁿ(ℝⁿ ∖ A m i) < 1 / i`.
    have hnull : ∀ m, (volume : Measure (Eucl n)) (⋂ i, (A m i)ᶜ) = 0 := by
      intro m
      by_contra h
      obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt h
      exact lt_asymm hi ((measure_mono (iInter_subset _ i)).trans_lt (hA m i))
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_iUnion_null hnull)]
      with w hwN hwΩ hDw
    obtain ⟨D, hD, hDinj⟩ := hDw
    obtain ⟨m, hwm⟩ := mem_iUnion.1 (hΩB hwΩ)
    obtain ⟨i, hwi⟩ : ∃ i, w ∈ A m i := by
      by_contra h
      exact hwN (mem_iUnion.2 ⟨m, mem_iInter.2 fun i => mem_compl (not_exists.1 h i)⟩)
    -- `D = D(G m i)(w)` by uniqueness of the derivative, so `D(G m i)(w)` is injective.
    have hDG : D = fderiv ℝ (G m i) w := hD.unique (huG m i w ⟨hwm, hwi⟩).2
    rw [hDG] at hDinj
    -- `G m i` is antilipschitz on a ball `B_r(w)`, hence on a basis set `b j` with
    -- `w ∈ b j ⊆ B_r(w) ∩ B m`; so `(m, i, j)` is good and `w ∈ E' k` for `k ↔ (m, i, j)`.
    obtain ⟨r, hr, c, hc, hcr⟩ :=
      Submission.lpf_c1_local_antilipschitz n Q (G m i) w (hG m i) hDinj
    obtain ⟨_, ⟨j, rfl⟩, hwj, hjs⟩ := hb.exists_subset_of_mem_open
      (show w ∈ ball w r ∩ B m from ⟨mem_ball_self hr, hwm⟩) (isOpen_ball.inter (hBo m))
    have hk : idx (Nat.pair m (Nat.pair i j)) = (m, i, j) := by
      simp only [idx, Nat.unpair_pair]
    have hgood : good (m, i, j) :=
      ⟨fun z hz => (hjs hz).2, c, hc, fun z hz z' hz' => hcr z (hjs hz).1 z' (hjs hz').1⟩
    rw [iUnion_disjointed]
    refine mem_iUnion.2 ⟨Nat.pair m (Nat.pair i j), ?_⟩
    simp only [E', O, hk, ite_eq_left hgood]
    exact ⟨hwj, hwm, hwi⟩

/-- **Simon Ch. 3, Lemma 1.2 ("only if").**  A countably `n`-rectifiable `M ⊆ ℝ^P` is covered,
up to an `Hⁿ`-null set, by the images `Φ_j(Ω_j)` of `C¹` maps `Φ_j : ℝⁿ → ℝ^P` which are
Lipschitz and antilipschitz on open sets `Ω_j ⊆ ℝⁿ`. -/
theorem Submission.lpf_countably_rectifiable_c1_cover : ∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 := by
  intro P n M hM
  -- Ch. 3, 1.1: `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and every `F_j` Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hMsub⟩ := hM
  choose K hK using hF
  -- Step 1: `C¹` maps `G j k`, antilipschitz on open `O j k`, with `F j = G j k` on
  -- `E j k ⊆ O j k`; a.e. point where `F j` has injective derivative lies in some `E j k`.
  choose G O E hO hG hanti _ hEO _ hFG hae using fun j =>
    Submission.lpf_lipschitz_c1_immersion_pieces n P univ (F j) isOpen_univ
      (hK j).locallyLipschitz.locallyLipschitzOn
  -- Step 4, local estimate: if `f` is `t²`-close on `S` to a linear `A` with `A e = 0`, `|e| = 1`,
  -- then compressing `ℝⁿ` by the factor `t` in the direction `e` (`T`, with `Lⁿ(T S) = t Lⁿ(S)`)
  -- makes `f ∘ T⁻¹` `(‖A‖ + t)`-Lipschitz on `T S`, so `Hⁿ(f S) ≤ (‖A‖ + t)ⁿ t Lⁿ(S)`.
  have hpiece : ∀ (f : Eucl n → Eucl P) (A : Eucl n →L[ℝ] Eucl P) (S : Set (Eucl n)) (t : ℝ≥0),
      0 < t → t ≤ 1 → ¬ Function.Injective A → ApproximatesLinearOn f A S (t ^ 2) →
      (μHE[n] : Measure (Eucl P)) (f '' S) ≤
        ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume S) := by
    intro f A S t ht0 ht1 hA happ
    obtain ⟨v, hv0, hAv⟩ : ∃ v, v ≠ 0 ∧ A v = 0 := by
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, A x = A y ∧ x ≠ y := by
        simpa [Function.Injective] using hA
      exact ⟨x - y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩
    set e : Eucl n := ‖v‖⁻¹ • v with he_def
    have he : ‖e‖ = 1 := norm_smul_inv_norm hv0
    have hAe : A e = 0 := by rw [he_def, map_smul, hAv, smul_zero]
    have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    have ht0' : (0 : ℝ) < t := ht0
    have ht1' : (t : ℝ) ≤ 1 := ht1
    set T : Eucl n →L[ℝ] Eucl n :=
      ContinuousLinearMap.id ℝ (Eucl n) + ((t : ℝ) - 1) • (innerSL ℝ e).smulRight e with hT_def
    set T' : Eucl n →L[ℝ] Eucl n :=
      ContinuousLinearMap.id ℝ (Eucl n) + ((t : ℝ)⁻¹ - 1) • (innerSL ℝ e).smulRight e with hT'_def
    have hTx : ∀ x, T x = x + (((t : ℝ) - 1) * inner ℝ e x) • e := by
      intro x
      simp [T, smul_smul]
    have hT'x : ∀ x, T' x = x + (((t : ℝ)⁻¹ - 1) * inner ℝ e x) • e := by
      intro x
      simp [T', smul_smul]
    have hT'T : ∀ x, T' (T x) = x := by
      intro x
      rw [hT'x, hTx, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul]
      have h0 : ((t : ℝ) - 1) * inner ℝ e x +
          ((t : ℝ)⁻¹ - 1) * (inner ℝ e x + ((t : ℝ) - 1) * inner ℝ e x * 1) = 0 := by
        field_simp
        ring
      rw [h0, zero_smul, add_zero]
    -- `det T = 1 + (t - 1) |e|² = t` (matrix determinant lemma in the standard basis).
    have hdet : LinearMap.det (T : Eucl n →ₗ[ℝ] Eucl n) = t := by
      set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      rw [← LinearMap.det_toMatrix b]
      have hmat : LinearMap.toMatrix b b (T : Eucl n →ₗ[ℝ] Eucl n) =
          1 + Matrix.replicateCol Unit (fun i => ((t : ℝ) - 1) * e i) *
            Matrix.replicateRow Unit (fun i => e i) := by
        ext i j
        simp [T, LinearMap.toMatrix_apply, b, Matrix.one_apply, Matrix.mul_apply,
          EuclideanSpace.inner_single_right]
        ring
      rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
      have h2 := EuclideanSpace.real_norm_sq_eq e
      rw [he] at h2
      simp only [dotProduct]
      rw [show (∑ i, e i * (((t : ℝ) - 1) * e i)) = ((t : ℝ) - 1) * ∑ i, e i ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, ← h2]
      ring
    have hvol : (volume : Measure (Eucl n)) (T '' S) = (t : ℝ≥0∞) * volume S := by
      rw [Measure.addHaar_image_continuousLinearMap, hdet, abs_of_pos ht0',
        ENNReal.ofReal_coe_nnreal]
    -- For `x, x' ∈ S`: `A (x - x') = A (T x - T x')` as `A e = 0`, and `|x - x'| ≤ t⁻¹ |T x - T x'|`.
    have hlip : LipschitzOnWith (‖A‖₊ + t) (f ∘ T') (T '' S) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      simp only [Function.comp_apply, hT'T, dist_eq_norm, NNReal.coe_add, coe_nnnorm]
      have h1 : ‖f x - f x' - A (x - x')‖ ≤ (t : ℝ) ^ 2 * ‖x - x'‖ := by
        simpa using happ x hx x' hx'
      have hxx : x - x' = T' (T x - T x') := by rw [map_sub, hT'T, hT'T]
      have h2 : A (x - x') = A (T x - T x') := by
        rw [hxx, hT'x, map_add, map_smul, hAe, smul_zero, add_zero]
      have h3 : ‖x - x'‖ ≤ (t : ℝ)⁻¹ * ‖T x - T x'‖ := by
        rw [hxx, hT'x]
        have hti : 0 ≤ (t : ℝ)⁻¹ - 1 := sub_nonneg.mpr (one_le_inv₀ ht0' |>.mpr ht1')
        calc ‖(T x - T x') + (((t : ℝ)⁻¹ - 1) * inner ℝ e (T x - T x')) • e‖
            ≤ ‖T x - T x'‖ + ‖(((t : ℝ)⁻¹ - 1) * inner ℝ e (T x - T x')) • e‖ :=
              norm_add_le _ _
          _ = ‖T x - T x'‖ + ((t : ℝ)⁻¹ - 1) * |inner ℝ e (T x - T x')| := by
              rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hti]
          _ ≤ ‖T x - T x'‖ + ((t : ℝ)⁻¹ - 1) * ‖T x - T x'‖ := by
              gcongr
              exact (abs_real_inner_le_norm e _).trans (by rw [he, one_mul])
          _ = (t : ℝ)⁻¹ * ‖T x - T x'‖ := by ring
      have h4 : ‖A (T x - T x')‖ ≤ ‖A‖ * ‖T x - T x'‖ := A.le_opNorm _
      calc ‖f x - f x'‖ ≤ ‖A (x - x')‖ + ‖f x - f x' - A (x - x')‖ := norm_le_insert' _ _
        _ ≤ ‖A‖ * ‖T x - T x'‖ + (t : ℝ) ^ 2 * ((t : ℝ)⁻¹ * ‖T x - T x'‖) :=
            add_le_add (by rw [h2]; exact h4) (h1.trans (by gcongr))
        _ = (‖A‖ + t) * ‖T x - T x'‖ := by field_simp
    have himg : f '' S = (f ∘ T') '' (T '' S) := by
      rw [image_image]
      exact image_congr fun x _ => by simp only [Function.comp_apply, hT'T]
    calc (μHE[n] : Measure (Eucl P)) (f '' S)
        = (μHE[n] : Measure (Eucl P)) ((f ∘ T') '' (T '' S)) := by rw [himg]
      _ ≤ ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Eucl n)) (T '' S) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
      _ = ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume S) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvol]
  -- Step 4: the image of the critical set of a Lipschitz map is `Hⁿ`-null.  Split the critical
  -- points in `B_m(0)` into countably many disjoint Borel pieces on which `f` is `t²`-close to
  -- its (non-injective) derivative at some point of the piece; then
  -- `Hⁿ(f(C ∩ B_m)) ≤ (L + 1)ⁿ t Lⁿ(B_m)` for every `t ∈ (0, 1]`.
  have hcrit : ∀ (f : Eucl n → Eucl P) (L : ℝ≥0), LipschitzWith L f →
      (μHE[n] : Measure (Eucl P))
        (f '' {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}) = 0 := by
    intro f L hf
    set C := {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}
    have hCm : ∀ m : ℕ, (μHE[n] : Measure (Eucl P)) (f '' (C ∩ ball 0 m)) = 0 := by
      intro m
      set V := (volume : Measure (Eucl n)) (ball 0 m)
      have hV : V ≠ ∞ := measure_ball_lt_top.ne
      have hbound : ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
          (μHE[n] : Measure (Eucl P)) (f '' (C ∩ ball 0 m)) ≤
            ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * V * t := by
        intro t ht0 ht1
        rcases (C ∩ ball (0 : Eucl n) m).eq_empty_or_nonempty with hs | hs
        · rw [hs, image_empty, measure_empty]
          exact bot_le
        obtain ⟨T, A, hTdisj, hTmeas, hsT, hTapprox, hTA⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (C ∩ ball 0 m)
            (fderiv ℝ f) (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => t ^ 2)
            (fun _ => pow_ne_zero 2 ht0.ne')
        have hpi : ∀ i, (μHE[n] : Measure (Eucl P)) (f '' (C ∩ ball 0 m ∩ T i)) ≤
            ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * t * volume (ball (0 : Eucl n) m ∩ T i) := by
          intro i
          -- `A i = Df(y)` for a critical point `y`, so `A i` is not injective and `‖A i‖ ≤ L`.
          obtain ⟨y, hy, hAy⟩ := hTA hs i
          have hAinj : ¬ Function.Injective (A i) := by
            rw [hAy]
            exact hy.1.2
          have hAn : ‖A i‖₊ ≤ L := by
            rw [hAy, ← NNReal.coe_le_coe, coe_nnnorm]
            exact norm_fderiv_le_of_lipschitz ℝ hf
          calc (μHE[n] : Measure (Eucl P)) (f '' (C ∩ ball 0 m ∩ T i))
              ≤ ((‖A i‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n *
                  ((t : ℝ≥0∞) * volume (C ∩ ball 0 m ∩ T i)) :=
                hpiece f (A i) _ t ht0 ht1 hAinj (hTapprox i)
            _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n *
                  ((t : ℝ≥0∞) * volume (ball (0 : Eucl n) m ∩ T i)) := by
                gcongr
                exact inter_subset_right
            _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * t * volume (ball (0 : Eucl n) m ∩ T i) := by ring
        calc (μHE[n] : Measure (Eucl P)) (f '' (C ∩ ball 0 m))
            ≤ (μHE[n] : Measure (Eucl P)) (⋃ i, f '' (C ∩ ball 0 m ∩ T i)) := by
              refine measure_mono ?_
              rintro _ ⟨x, hx, rfl⟩
              obtain ⟨i, hi⟩ := mem_iUnion.mp (hsT hx)
              exact mem_iUnion.mpr ⟨i, x, ⟨hx, hi⟩, rfl⟩
          _ ≤ ∑' i, (μHE[n] : Measure (Eucl P)) (f '' (C ∩ ball 0 m ∩ T i)) :=
              measure_iUnion_le _
          _ ≤ ∑' i, ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * t * volume (ball (0 : Eucl n) m ∩ T i) :=
              ENNReal.tsum_le_tsum hpi
          _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * t * volume (⋃ i, ball (0 : Eucl n) m ∩ T i) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (hTdisj hij).mono inter_subset_right inter_subset_right
              · exact fun i => measurableSet_ball.inter (hTmeas i)
          _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * t * V := by
              gcongr
              exact measure_mono (iUnion_subset fun i => inter_subset_left)
          _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * V * t := by ring
      -- Let `t = 1 / (k + 1) → 0`.
      have hlim : Tendsto (fun k : ℕ => ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * V * ((k + 1 : ℕ) : ℝ≥0∞)⁻¹)
          atTop (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
          (Or.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hV) :
            (0 : ℝ≥0∞) ≠ 0 ∨ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * V ≠ ∞)
        rw [mul_zero] at h
        exact h
      refine le_antisymm (ge_of_tendsto' hlim fun k => ?_) bot_le
      have hk : ((k + 1 : ℕ) : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr k.succ_ne_zero
      have h := hbound ((k + 1 : ℕ) : ℝ≥0)⁻¹ (inv_pos.mpr (pos_iff_ne_zero.mpr hk))
        (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr k.succ_pos))
      rwa [ENNReal.coe_inv hk, ENNReal.coe_natCast] at h
    refine measure_mono_null ?_ (measure_iUnion_null hCm)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨m, x, ⟨hx, mem_ball_zero_iff.mpr hm⟩, rfl⟩
  -- Steps 2–5: `F j (ℝⁿ)` is covered by the sets `G j k (O j k)` up to an `Hⁿ`-null set.
  have hnull : ∀ j, (μHE[n] : Measure (Eucl P)) (range (F j) \ ⋃ k, G j k '' O j k) = 0 := by
    intro j
    -- Steps 2–3: by Rademacher's theorem and Step 1, `Lⁿ`-a.e. non-critical point lies in
    -- `⋃_k E j k`; as `Hⁿ = Lⁿ` on `ℝⁿ`, the image of the exceptional set `N` is `Hⁿ`-null.
    set N := {w | ¬ (DifferentiableAt ℝ (F j) w ∧ ¬ Function.Injective (fderiv ℝ (F j) w)) ∧
      w ∉ ⋃ k, E j k}
    have hN : (volume : Measure (Eucl n)) N = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp ((hK j).ae_differentiableAt.and (hae j)))
      rintro w ⟨hwC, hwE⟩ ⟨hd, hw⟩
      exact hwE (hw (mem_univ w)
        ⟨fderiv ℝ (F j) w, hd.hasFDerivAt, not_not.mp fun h => hwC ⟨hd, h⟩⟩)
    have h₂ : (μHE[n] : Measure (Eucl P)) (F j '' N) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        ((hK j).lipschitzOnWith (s := N))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, hN, mul_zero] at h
      exact le_antisymm h bot_le
    -- Step 5: `F j = G j k` on `E j k ⊆ O j k`.
    refine measure_mono_null ?_ (measure_union_null (hcrit (F j) (K j) (hK j)) h₂)
    rintro _ ⟨⟨w, rfl⟩, hw⟩
    by_cases hE : w ∈ ⋃ k, E j k
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hE
      exact (hw (mem_iUnion.mpr ⟨k, w, (hEO j k hk).1, (hFG j k w hk).1.symm⟩)).elim
    · by_cases hC : DifferentiableAt ℝ (F j) w ∧ ¬ Function.Injective (fderiv ℝ (F j) w)
      · exact Or.inl ⟨w, hC, rfl⟩
      · exact Or.inr ⟨w, ⟨hC, hE⟩, rfl⟩
  -- Step 6: a `C¹` map is Lipschitz on every ball, by the mean value inequality, since its
  -- derivative is bounded on the compact closed ball.
  have hball : ∀ Ψ : Eucl n → Eucl P, ContDiff ℝ 1 Ψ → ∀ r : ℝ,
      ∃ C : ℝ≥0, LipschitzOnWith C Ψ (ball 0 r) := by
    intro Ψ hΨ r
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Eucl n) r).exists_bound_of_continuousOn
      (hΨ.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨C.toNNReal, (convex_ball (0 : Eucl n) r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hΨ.differentiable one_ne_zero x) fun x hx => ?_⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC x (ball_subset_closedBall hx)).trans (Real.le_coe_toNNReal C)
  -- So we shrink `O j k` to the bounded open sets `O j k ∩ B(0, m)`, on which `G j k` stays
  -- antilipschitz, and enumerate the triples `(j, k, m)`.
  let e : ℕ ≃ ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm
  refine ⟨fun l => G (e l).1 (e l).2.1, fun l => O (e l).1 (e l).2.1 ∩ ball 0 ((e l).2.2 : ℝ),
    fun l => (hO _ _).inter isOpen_ball, fun l => hG _ _, fun l => ?_, fun l => ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hball _ (hG (e l).1 (e l).2.1) ((e l).2.2 : ℝ)
    exact ⟨C, hC.mono inter_subset_right⟩
  · obtain ⟨c, hc, h⟩ := hanti (e l).1 (e l).2.1
    exact ⟨c, hc, fun w hw w' hw' => h w hw.1 w' hw'.1⟩
  -- Step 7: `M ∖ ⋃_l Φ_l(Ω_l) ⊆ M₀ ∪ ⋃_j (F_j(ℝⁿ) ∖ ⋃_k G j k (O j k))`, a countable union
  -- of `Hⁿ`-null sets.
  · refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hnull))
    rintro x ⟨hxM, hxΦ⟩
    refine (hMsub hxM).imp id fun hx => ?_
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨j, hj, fun hcov => hxΦ ?_⟩
    obtain ⟨k, w, hw, rfl⟩ := mem_iUnion.mp hcov
    obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
    refine mem_iUnion.mpr ⟨e.symm (j, k, m), w, ?_, ?_⟩ <;> simp only [Equiv.apply_symm_apply]
    exact ⟨hw, mem_ball_zero_iff.mpr hm⟩
/-- Derivative lower bound (step 1 of the C¹ chart approximate tangent argument for Simon Ch. 6,
3.9): if `c ‖v - v'‖ ≤ ‖Φ v - Φ v'‖` on an open `Ω ∋ w` and `Φ` is differentiable at `w`, then
`c ‖s‖ ≤ ‖DΦ(w) s‖` for every `s` (no sign condition on `c`).  Apply the bound to `v = w + t • s`,
`v' = w`, divide by `t > 0` and let `t → 0⁺`. -/
theorem Submission.lpf_wtc_cat_fderiv_lower_bound :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (c : ℝ) (w : Eucl n), IsOpen Ω → w ∈ Ω → DifferentiableAt ℝ Φ w → (∀ v ∈ Ω, ∀ v' ∈ Ω, c * ‖v - v'‖ ≤ ‖Φ v - Φ v'‖) → ∀ s : Eucl n, c * ‖s‖ ≤ ‖fderiv ℝ Φ w s‖ := by
  intro Q n Φ Ω c w hΩ hw hdiff hanti s
  -- `γ t = Φ (w + t • s)` has derivative `DΦ(w) s` at `0`, so its right slopes converge to it.
  have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
  have hγ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 := by
    have h0 : w + (0 : ℝ) • s = w := by simp
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
  have hnorm : Tendsto (fun t : ℝ => ‖t⁻¹ • (Φ (w + (0 + t) • s) - Φ (w + (0 : ℝ) • s))‖)
      (𝓝[>] 0) (𝓝 ‖fderiv ℝ Φ w s‖) := hγ.tendsto_slope_zero_right.norm
  -- The segment `w + t • s` stays in the open set `Ω` for small `t`.
  have hcont : Continuous (fun t : ℝ => w + t • s) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), w + t • s ∈ Ω := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hw
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c * ‖s‖ ≤ ‖t⁻¹ • (Φ (w + (0 + t) • s) - Φ (w + (0 : ℝ) • s))‖ := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with t ht htpos
    have htpos : (0 : ℝ) < t := htpos
    have h1 := hanti (w + t • s) ht w hw
    simp only [zero_add, zero_smul, add_zero]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), le_inv_mul_iff₀ htpos]
    linarith [h1]
  exact ge_of_tendsto hnorm hev
/-- Rescaled chart integrals converge (Simon Ch. 3, approximate tangent space of a `C¹` chart
image): for `Φ` continuous, differentiable at `w ∈ Ω` and antilipschitz on the open set `Ω`,
`J` continuous and `φ ∈ C_c`, `(rⁿ)⁻¹ ∫_Ω J(v) φ(r⁻¹(Φ v − Φ w)) dv → ∫ J(w) φ(DΦ(w) s) ds`
as `r → 0⁺`.  Substituting `v = w + r s` (Haar scaling and translation invariance) turns the
left side into `∫ F_r`; for `0 < r ≤ 1` the antilipschitz bound confines the support of `F_r`
to `‖s‖ ≤ R / c`, so `F_r` is dominated by a constant on a ball, and `F_r(s) → J(w) φ(DΦ(w) s)`
pointwise by differentiability at `w`; dominated convergence concludes. -/
theorem Submission.lpf_wtc_cat_rescaled_integral_tendsto :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (J : Eucl n → ℝ) (φ : Eucl Q → ℝ)
      (w : Eucl n), IsOpen Ω → w ∈ Ω → Continuous Φ → DifferentiableAt ℝ Φ w →
      (∃ c : ℝ, 0 < c ∧ ∀ v ∈ Ω, ∀ v' ∈ Ω, c * ‖v - v'‖ ≤ ‖Φ v - Φ v'‖) → Continuous J →
      Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ v in Ω, J v * φ (r⁻¹ • (Φ v - Φ w))) (𝓝[>] 0)
        (𝓝 (∫ s, J w * φ (fderiv ℝ Φ w s))) := by
  intro Q n Φ Ω J φ w hΩ hw hΦc hdiff hanti hJ hφ hφc
  obtain ⟨c, hc, hcΩ⟩ := hanti
  -- Constants: `tsupport φ ⊆ B̄_R(0)`, `|φ| ≤ A`, `|J| ≤ B` on `B̄_{R/c}(w)`.
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ tsupport φ ⊆ closedBall (0 : Eucl Q) R :=
    hφc.isCompact.isBounded.subset_closedBall_lt 0 0
  obtain ⟨A, hA⟩ : ∃ A, ∀ x, ‖φ x‖ ≤ A := hφ.bounded_above_of_compact_support hφc
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall w (R / c), ‖J z‖ ≤ B :=
    (isCompact_closedBall w (R / c)).exists_bound_of_continuousOn hJ.continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w (mem_closedBall_self (div_pos hR0 hc).le))
  set F : ℝ → Eucl n → ℝ := fun r s =>
    Ω.indicator (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) (w + r • s) with hF
  -- Change of variables `v = w + r • s`.
  have hcov : ∀ r : ℝ, 0 < r →
      ∫ s, F r s = (r ^ n)⁻¹ * ∫ v in Ω, J v * φ (r⁻¹ • (Φ v - Φ w)) := by
    intro r hr
    rw [← integral_indicator hΩ.measurableSet]
    have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure (Eucl n))
      (fun x => Ω.indicator (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) (w + x)) r (hR := hr.le)
    rw [integral_add_left_eq_self, finrank_euclideanSpace_fin, smul_eq_mul] at h1
    exact h1
  have hmeas : ∀ r : ℝ, AEStronglyMeasurable (F r) volume := by
    intro r
    have hk : Continuous (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) := by
      have h1 : Continuous (fun v => r⁻¹ • (Φ v - Φ w)) :=
        (hΦc.sub continuous_const).const_smul r⁻¹
      exact hJ.mul (hφ.comp h1)
    have hlin : Measurable (fun s : Eucl n => w + r • s) :=
      (continuous_const.add (continuous_id.const_smul r)).measurable
    exact ((hk.measurable.indicator hΩ.measurableSet).comp hlin).aestronglyMeasurable
  -- Domination for `0 < r ≤ 1` by `B * A` on `B̄_{R/c}(0)`.
  set bound : Eucl n → ℝ := (closedBall (0 : Eucl n) (R / c)).indicator (fun _ => B * A)
    with hbound
  have hdom : ∀ r : ℝ, r ∈ Ioc (0 : ℝ) 1 → ∀ s, ‖F r s‖ ≤ bound s := by
    rintro r ⟨hr0, hr1⟩ s
    by_cases hz : F r s = 0
    · rw [hz, norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg hB0 hA0) s
    · have hmemΩ : w + r • s ∈ Ω := by
        by_contra hnot
        exact hz (by simp only [hF, indicator_of_notMem hnot])
      have hFeq : F r s = J (w + r • s) * φ (r⁻¹ • (Φ (w + r • s) - Φ w)) := by
        simp only [hF, indicator_of_mem hmemΩ]
      have hφne : φ (r⁻¹ • (Φ (w + r • s) - Φ w)) ≠ 0 := by
        intro h0; apply hz; rw [hFeq, h0, mul_zero]
      have hinR : ‖r⁻¹ • (Φ (w + r • s) - Φ w)‖ ≤ R := by
        have := hR (subset_tsupport φ hφne)
        simpa [mem_closedBall, dist_zero_right] using this
      have hΦR : ‖Φ (w + r • s) - Φ w‖ ≤ r * R := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), inv_mul_le_iff₀ hr0] at hinR
        exact hinR
      have hant := hcΩ (w + r • s) hmemΩ w hw
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le] at hant
      have hs : ‖s‖ ≤ R / c := by
        rw [le_div_iff₀ hc]
        have : r * (c * ‖s‖) ≤ r * R := by nlinarith
        nlinarith
      have hsball : s ∈ closedBall (0 : Eucl n) (R / c) := by
        simpa [mem_closedBall, dist_zero_right] using hs
      have hwball : w + r • s ∈ closedBall w (R / c) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hr0.le]
        calc r * ‖s‖ ≤ 1 * ‖s‖ := by gcongr
          _ = ‖s‖ := one_mul _
          _ ≤ R / c := hs
      rw [hbound, indicator_of_mem hsball, hFeq, norm_mul]
      exact mul_le_mul (hB _ hwball) (hA _) (norm_nonneg _) hB0
  have hint : Integrable bound volume := by
    rw [hbound]
    exact (integrableOn_const (measure_closedBall_lt_top (x := (0 : Eucl n))
      (r := R / c)).ne).integrable_indicator measurableSet_closedBall
  -- Pointwise limit from differentiability of `Φ` at `w`.
  have hlim : ∀ s, Tendsto (fun r => F r s) (𝓝[>] 0) (𝓝 (J w * φ (fderiv ℝ Φ w s))) := by
    intro s
    have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
    have hγ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 := by
      have h0 : w + (0 : ℝ) • s = w := by simp
      exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
    have hslope : Tendsto (fun t : ℝ => t⁻¹ • (Φ (w + t • s) - Φ w)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ Φ w s)) := by
      simpa using hγ.tendsto_slope_zero_right
    have hcont : Continuous (fun t : ℝ => w + t • s) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hto : Tendsto (fun t : ℝ => w + t • s) (𝓝[>] 0) (𝓝 w) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), w + t • s ∈ Ω := hto (hΩ.mem_nhds hw)
    have hJlim : Tendsto (fun t : ℝ => J (w + t • s)) (𝓝[>] 0) (𝓝 (J w)) :=
      (hJ.tendsto w).comp hto
    have hφlim : Tendsto (fun t : ℝ => φ (t⁻¹ • (Φ (w + t • s) - Φ w))) (𝓝[>] 0)
        (𝓝 (φ (fderiv ℝ Φ w s))) := (hφ.tendsto _).comp hslope
    refine (hJlim.mul hφlim).congr' ?_
    filter_upwards [hmem] with t ht
    simp only [hF, indicator_of_mem ht]
  -- Dominated convergence along `𝓝[>] 0`, then undo the change of variables.
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Eucl n))) (l := 𝓝[>] (0 : ℝ)) (F := F)
    (f := fun s => J w * φ (fderiv ℝ Φ w s)) bound
    (Eventually.of_forall hmeas)
    (by filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with r hr
        exact Eventually.of_forall (hdom r hr))
    hint (Eventually.of_forall hlim)
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hcov r hr
/-- Continuity of the Jacobian `JΦ = √det((DΦ)* DΦ)` (Simon Ch. 2, (3.3)) of a `C¹` map
`Φ : ℝⁿ → ℝ^Q`, written as the Gram determinant `det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)` of the columns of
`DΦ(v)`.  `v ↦ DΦ(v)` is continuous since `Φ` is `C¹`, so are the columns `DΦ(v)eᵢ`, the Gram
entries, the Gram matrix (entrywise), its determinant (a polynomial in the entries) and the
square root. -/
theorem Submission.lpf_wtc_cat_gram_jacobian_continuous :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q), ContDiff ℝ 1 Φ → Continuous (fun v : Eucl n => Real.sqrt (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1)) (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det) := by
  intro Q n Φ hΦ
  have hD : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (hD.clm_apply continuous_const).inner (hD.clm_apply continuous_const)
/-- Splitting of the blown-up weighted integral (Simon Ch. 3, Remark 1.8(1)): for `C ⊆ M` and all
small `t > 0`, `∫_M φ(η_t) θ = θ(y) ∫_C φ(η_t) + ∫_C φ(η_t) (θ − θ(y)) + ∫_{M∖C} φ(η_t) θ`. -/
theorem Submission.lpf_wtc_wtt_blowup_integral_split : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ x in M, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)) = θ y * ∫ x in C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q)) + ∫ x in C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y) ∂(μHE[n] : Measure (Eucl Q)) + ∫ x in M \ C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n M C θ y φ hM hC hCM ⟨r, hr, hCr, hθr⟩
  -- Step 1: `tsupport φ ⊆ B_R(0)` and `|φ| ≤ A`.
  obtain ⟨R, -, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- Step 2: `t R < r` for all sufficiently small `t > 0`; fix such a `t`.
  have hlim : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.mul_const R
  filter_upwards [hlim.eventually (eventually_lt_nhds hr), self_mem_nhdsWithin] with t htR ht
  -- Step 3: `F = φ ∘ η_t` is continuous, bounded by `A`, and vanishes off `B̄_r(y)`.
  have hcont : Continuous fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) :=
    (map_continuous φ).comp ((continuous_id.sub continuous_const).const_smul t⁻¹)
  have hzero : ∀ x ∉ closedBall y r, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro x hx
    by_contra hne
    have hball := hR (subset_tsupport _ (Function.mem_support.2 hne))
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg (le_of_lt ht), inv_mul_lt_iff₀ ht] at hball
    exact hx (mem_closedBall.2 (by rw [dist_eq_norm]; linarith))
  suffices key : ∀ F : Eucl Q → ℝ, Continuous F → (∀ x, ‖F x‖ ≤ A) →
      (∀ x ∉ closedBall y r, F x = 0) →
      ∫ x in M, F x * θ x ∂(μHE[n] : Measure (Eucl Q)) =
        θ y * ∫ x in C, F x ∂(μHE[n] : Measure (Eucl Q)) +
          ∫ x in C, F x * (θ x - θ y) ∂(μHE[n] : Measure (Eucl Q)) +
            ∫ x in M \ C, F x * θ x ∂(μHE[n] : Measure (Eucl Q)) from
    key _ hcont (fun x => hA _) hzero
  intro F hFc hFA hF0
  generalize (μHE[n] : Measure (Eucl Q)) = μ at hM hC hCr hθr ⊢
  -- Step 4: `F θ` is integrable on `M ∩ B̄_r(y)`, and vanishes on the rest of `M`.
  have hFθM : IntegrableOn (fun x => F x * θ x) M μ := by
    refine IntegrableOn.of_ae_sdiff_eq_zero
      (hθr.bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hFA)) hM
      (Eventually.of_forall fun x hx => ?_)
    rw [hF0 x fun h => hx.2 ⟨hx.1, h⟩, zero_mul]
  -- Step 5: `F` is integrable on `C ∩ B̄_r(y)` (finite measure), and vanishes on the rest of `C`.
  have hFC : IntegrableOn F C μ :=
    (Measure.integrableOn_of_bounded hCr.ne hFc.aestronglyMeasurable
      (Eventually.of_forall hFA)).of_ae_sdiff_eq_zero hC
        (Eventually.of_forall fun x hx => hF0 x fun h => hx.2 ⟨hx.1, h⟩)
  -- Step 6: derived integrabilities on `C` and `M \ C`.
  have hFθC : IntegrableOn (fun x => F x * θ x) C μ := hFθM.mono_set hCM
  have hFθMC : IntegrableOn (fun x => F x * θ x) (M \ C) μ := hFθM.mono_set sdiff_subset
  have hθF : IntegrableOn (fun x => θ y * F x) C μ := hFC.const_mul _
  have hFd : IntegrableOn (fun x => F x * (θ x - θ y)) C μ :=
    (hFθC.sub hθF).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  -- Step 7: split `M = C ∪ (M \ C)`.
  have h7 : ∫ x in M, F x * θ x ∂μ = ∫ x in C, F x * θ x ∂μ + ∫ x in M \ C, F x * θ x ∂μ := by
    conv_lhs => rw [← union_sdiff_cancel hCM]
    exact setIntegral_union₀ disjoint_sdiff_right.aedisjoint (hM.diff hC) hFθC hFθMC
  -- Step 8: split the weight on `C`.
  have h8 : ∫ x in C, F x * θ x ∂μ =
      θ y * ∫ x in C, F x ∂μ + ∫ x in C, F x * (θ x - θ y) ∂μ := by
    rw [← integral_const_mul, ← integral_add hθF hFd]
    congr 1
    funext x
    ring
  -- Step 9: combine.
  rw [h7, h8]

/-- If `C` is `Hⁿ`-null-measurable, `θ` is continuous at `y` within `C` and
`Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for small `ρ > 0`, then
`t⁻ⁿ ∫_C φ(η_{y,t}(x)) (θ(x) - θ(y)) dHⁿ(x) → 0` as `t → 0⁺`.  With `tsupport φ ⊆ B_R(0)` and
`|φ| ≤ A`, the integrand vanishes off `B̄_{tR}(y)` and is at most `A ε₁` on `C ∩ B̄_{tR}(y)` once
`tR < δ(ε₁)`, so the integral is at most `A ε₁ K (tR)ⁿ`. -/
theorem Submission.lpf_wtc_wtt_continuity_error_vanishes :
    ∀ (Q n : ℕ) (C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q)
      (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ),
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → ContinuousWithinAt θ C y →
      (∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n)) →
      Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in C,
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y)
          ∂(μHE[n] : Measure (Eucl Q))) (𝓝[>] 0) (𝓝 0) := by
  intro Q n C θ y φ hC hθ hK
  obtain ⟨K, hK⟩ := hK
  -- `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A`.
  obtain ⟨R, hR, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- For `t > 0`, `φ(η_t(x)) = 0` off `B̄_{tR}(y)`.
  have hloc : ∀ t : ℝ, 0 < t → ∀ x, x ∉ closedBall y (t * R) →
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro t ht x hx
    by_contra hne
    have hmem := hRφ (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos ht, inv_mul_lt_iff₀ ht] at hmem
    exact hx (mem_closedBall.2 ((dist_eq_norm x y).trans_le hmem.le))
  -- `tR → 0` within `(0, ∞)`, so the density bound holds at `ρ = tR` for small `t > 0`.
  have hRt : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const R
  have hRt' : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hRt, eventually_nhdsWithin_of_forall fun t ht => mul_pos ht hR⟩
  have hKt := hRt'.eventually hK
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := A * K * R ^ n with hc
  have hc0 : 0 ≤ c := by positivity
  set ε₁ : ℝ := ε / (2 * (c + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ, hθδ⟩ := Metric.continuousWithinAt_iff.1 hθ ε₁ hε₁0
  filter_upwards [hKt, hRt.eventually (Iio_mem_nhds hδ), self_mem_nhdsWithin] with t htK htδ ht
  have ht0 : 0 < t := ht
  set μ : Measure (Eucl Q) := (μHE[n] : Measure (Eucl Q))
  set f : Eucl Q → ℝ := fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y)
    with hf
  set B : Set (Eucl Q) := closedBall y (t * R)
  -- `μ⌞C`-a.e., `|f| ≤ A ε₁ 1_B`.
  have hpt : ∀ᵐ x ∂μ.restrict C, ENNReal.ofReal ‖f x‖ ≤
      B.indicator (fun _ => ENNReal.ofReal (A * ε₁)) x := by
    filter_upwards [ae_restrict_mem₀ hC] with x hxC
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB]
      refine ENNReal.ofReal_le_ofReal ?_
      have hxy : dist x y < δ := (mem_closedBall.1 hxB).trans_lt htδ
      have h1 : ‖θ x - θ y‖ ≤ ε₁ := by
        rw [← dist_eq_norm]; exact (hθδ hxC hxy).le
      simp only [hf, norm_mul]
      exact mul_le_mul (hA _) h1 (norm_nonneg _) hA0
    · rw [indicator_of_notMem hxB]
      simp [hf, hloc t ht0 x hxB]
  -- `∫⁻_C |f| ≤ A ε₁ μ(C ∩ B) ≤ A ε₁ K (tR)ⁿ < ∞`.
  have hlin : ∫⁻ x in C, ENNReal.ofReal ‖f x‖ ∂μ ≤
      ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) := by
    calc ∫⁻ x in C, ENNReal.ofReal ‖f x‖ ∂μ
        ≤ ∫⁻ x in C, B.indicator (fun _ => ENNReal.ofReal (A * ε₁)) x ∂μ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (A * ε₁) * μ (C ∩ B) := by
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, inter_comm]
      _ ≤ ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) := by
        gcongr
  have hfin : ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top)
  -- `|∫_C f| ≤ A ε₁ K (tR)ⁿ`.
  have hnorm : ‖∫ x in C, f x ∂μ‖ ≤ A * ε₁ * (K * (t * R) ^ n) := by
    refine (norm_integral_le_lintegral_norm f).trans ?_
    refine (ENNReal.toReal_mono hfin hlin).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal]
  -- Rescaling: `t⁻ⁿ |∫_C f| ≤ c ε₁ ≤ ε / 2 < ε`.
  rw [dist_zero_right, norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos ht0]
  calc (t ^ n)⁻¹ * ‖∫ x in C, f x ∂μ‖
      ≤ (t ^ n)⁻¹ * (A * ε₁ * (K * (t * R) ^ n)) := by gcongr
    _ = c * ε₁ := by
      rw [hc, mul_pow]
      field_simp
    _ ≤ (c + 1) * ε₁ := by gcongr; linarith
    _ = ε / 2 := by
      rw [hε₁]
      field_simp
    _ < ε := by linarith

/-- Zero `θ`-weighted `n`-density of `D` at `y` kills the blow-up integrals (Simon Ch. 3,
Remark 1.8(1)): if `(∫⁻_{D ∩ B̄_ρ(y)} θ dHⁿ) / ρⁿ → 0` as `ρ ↓ 0`, then for every `φ ∈ C_c(ℝ^Q)`,
`(tⁿ)⁻¹ ∫_D φ(η_{y,t}(x)) θ(x) dHⁿ(x) → 0` as `t ↓ 0`.  No integrability of `θ` is assumed. -/
theorem Submission.lpf_wtc_wtt_remainder_vanishes : ∀ (Q n : ℕ) (D : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ), NullMeasurableSet D (μHE[n] : Measure (Eucl Q)) → (∀ x ∈ D, 0 ≤ θ x) → Tendsto (fun ρ : ℝ => (∫⁻ x in D ∩ closedBall y ρ, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q))) (𝓝[>] 0) (𝓝 0) := by
  intro Q n D θ y φ hD hθ hlim
  set μ : Measure (Eucl Q) := μHE[n]
  -- Step 1: `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A` (so `A ≥ 0`).
  obtain ⟨R, hR, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  obtain ⟨A, hA⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- Step 2: for `t > 0`, `φ (η_t x) = 0` whenever `x ∉ B̄_{tR}(y)`.
  have hloc : ∀ t : ℝ, 0 < t → ∀ x, x ∉ closedBall y (t * R) →
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro t ht x hx
    by_contra hne
    have hmem := hRφ (subset_tsupport φ (Function.mem_support.2 hne))
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg ht.le, inv_mul_lt_iff₀ ht] at hmem
    exact hx (mem_closedBall_iff_norm.2 hmem.le)
  -- Step 3: compose the density hypothesis with `t ↦ tR`, which tends to `0` within `(0, ∞)`.
  have hTR : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun t : ℝ => t * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos ht hR
  have hq := hlim.comp hTR
  -- (a) eventually `q (tR) < ∞`;
  have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal (θ x) ∂μ)
      / ENNReal.ofReal ((t * R) ^ n) < ⊤ :=
    hq.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  -- (b) `b t = A Rⁿ toReal (q (tR)) → 0`.
  have hb : Tendsto (fun t : ℝ => A * R ^ n * ((∫⁻ x in D ∩ closedBall y (t * R),
      ENNReal.ofReal (θ x) ∂μ) / ENNReal.ofReal ((t * R) ^ n)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hq).const_mul (A * R ^ n)
    rw [ENNReal.toReal_zero, mul_zero] at h0
    exact h0
  -- Step 4: squeeze; fix `t > 0` with `q (tR) < ∞`.
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [hfin, self_mem_nhdsWithin] with t hqt ht
  have ht' : (0 : ℝ) < t := ht
  have htR : 0 < t * R := mul_pos ht' hR
  set L := ∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal (θ x) ∂μ
  -- Step 5: `L (tR) < ∞`.
  have hLtop : L ≠ ⊤ := by
    intro hLt
    rw [hLt, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hqt
    exact lt_irrefl _ hqt
  -- Steps 6–7: `∫⁻_D ofReal |φ(η_t x) θ(x)| ≤ ofReal A · L (tR)`.
  have hlint : ∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖
      ∂μ ≤ ENNReal.ofReal A * L := by
    calc ∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖ ∂μ
        ≤ ∫⁻ x in D, (closedBall y (t * R)).indicator
            (fun x => ENNReal.ofReal A * ENNReal.ofReal (θ x)) x ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hD] with x hx
          by_cases hxB : x ∈ closedBall y (t * R)
          · simp only [indicator_of_mem hxB]
            rw [← ENNReal.ofReal_mul hA0, norm_mul, Real.norm_of_nonneg (hθ x hx)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hA _) (hθ x hx))
          · rw [hloc t ht' x hxB, zero_mul, norm_zero, ENNReal.ofReal_zero]
            exact zero_le
      _ = ∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal A * ENNReal.ofReal (θ x) ∂μ := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm (closedBall y (t * R)) D]
      _ = ENNReal.ofReal A * L := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 8: `|∫_D φ(η_t x) θ(x)| ≤ A · toReal (L (tR))`, with no integrability needed.
  have hint : ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
      ≤ A * L.toReal := by
    calc ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
        ≤ (∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖
            ∂μ).toReal := norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal A * L).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop) hlint
      _ = A * L.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0]
  -- Step 9: rescaling, `(tⁿ)⁻¹ A toReal (L (tR)) = A Rⁿ toReal (q (tR))`.
  have htn : 0 < t ^ n := pow_pos ht' n
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [norm_mul, norm_inv, Real.norm_of_nonneg htn.le, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_pos htR n).le, mul_pow]
  calc (t ^ n)⁻¹ * ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
      ≤ (t ^ n)⁻¹ * (A * L.toReal) := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 htn.le)
    _ = A * R ^ n * (L.toReal / (t ^ n * R ^ n)) := by
      field_simp [htn.ne', hRn.ne']

/-- Change of variables for `Hⁿ`-integrals over blow-ups: `η = η_{y,r}`, `η(x) = r⁻¹(x − y)`,
pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so `∫_{η(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η dHⁿ` for every set
`S` and every `g` (both sides are Bochner set integrals). -/
theorem Submission.lpf_wtc_blowup_setIntegral_image :
    ∀ (Q n : ℕ) (y : Eucl Q) (r : ℝ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ), 0 < r →
      ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, g z ∂(μHE[n] : Measure (Eucl Q)) =
        (r ^ n)⁻¹ * ∫ x in S, g (Poincare.SimonGMT.Chapter03.blowUpMap y r x)
          ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n y r S g hr
  -- `η = blowUpMap y r`, `η x = r⁻¹ • (x - y)`, is a homeomorphism of `ℝ^Q`.
  let e : Eucl Q ≃ₜ Eucl Q :=
    (Homeomorph.addRight (-y)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl Q → Eucl Q) = Poincare.SimonGMT.Chapter03.blowUpMap y r := by
    funext x
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = y + r • B`.
  have hmp : MeasurePreserving (Poincare.SimonGMT.Chapter03.blowUpMap y r)
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl Q))) μHE[n] := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap y r ⁻¹' B =
        (fun z => y + z) '' ((fun z => r • z) '' B) := by
      ext x
      simp only [mem_preimage, mem_image, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · intro hx
        exact ⟨r • r⁻¹ • (x - y), ⟨r⁻¹ • (x - y), hx, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left y), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
/-- The image `Φ(Ω)` of an open `Ω ⊆ ℝⁿ` under a `C¹` map `Φ : ℝⁿ → ℝ^Q` with
`c |w - w'| ≤ |Φ w - Φ w'|` on `Ω` is Borel, and `Hⁿ(Φ(Ω) ∩ K) < ∞` for every compact `K`. -/
theorem Submission.lpf_wtc_chart_image_measurable_locally_finite :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen Ω → ContDiff ℝ 1 Φ →
      (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      MeasurableSet (Φ '' Ω) ∧ ∀ K : Set (Eucl Q), IsCompact K →
        (μHE[n] : Measure (Eucl Q)) (Φ '' Ω ∩ K) < ∞ := by
  intro Q n Φ Ω hΩ hΦ ⟨c, hc, hcΦ⟩
  refine ⟨?_, fun K hK => ?_⟩
  · -- `Φ` is injective on `Ω`, so `Φ '' Ω` is Borel by Lusin–Souslin.
    refine hΩ.measurableSet.image_of_continuousOn_injOn hΦ.continuous.continuousOn
      fun w hw w' hw' h => ?_
    have h0 := hcΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h0
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h0 hc))
  · rcases (Φ '' Ω ∩ K).eq_empty_or_nonempty with h | ⟨_, ⟨w₀, hw₀, rfl⟩, hw₀K⟩
    · rw [h, measure_empty]
      exact ENNReal.zero_lt_top
    -- `Ω ∩ Φ⁻¹(K)` lies in the closed ball `B` of radius `D / c` about `w₀`, `D ≥ diam K`.
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hK.isBounded
    have hsub : Φ '' Ω ∩ K ⊆ Φ '' closedBall w₀ (D / c) := by
      rintro _ ⟨⟨v, hv, rfl⟩, hvK⟩
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hc, mul_comm]
      exact (hcΦ v hv w₀ hw₀).trans ((dist_eq_norm (Φ v) (Φ w₀)).symm.trans_le (hD hvK hw₀K))
    -- `DΦ` is bounded on the compact convex ball `B`, so `Φ` is Lipschitz on `B`.
    obtain ⟨C, hC⟩ := (isCompact_closedBall w₀ (D / c)).exists_bound_of_continuousOn
      (hΦ.continuous_fderiv one_ne_zero).continuousOn
    have hLip : LipschitzOnWith (Real.toNNReal C) Φ (closedBall w₀ (D / c)) :=
      (convex_closedBall w₀ (D / c)).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => hΦ.differentiable one_ne_zero x)
        (fun x hx => by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact (hC x hx).trans (Real.le_coe_toNNReal C))
    -- `μHE[n] = κₙ • μH[n]` and `μH[n](Φ(B)) ≤ Λⁿ μH[n](B) < ∞` (`μH[n]` is Haar on `ℝⁿ`).
    refine (measure_mono hsub).trans_lt ?_
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((hLip.hausdorffMeasure_image_le n.cast_nonneg).trans_lt ?_)
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg n.cast_nonneg ENNReal.coe_ne_top)
      (isCompact_closedBall w₀ (D / c)).measure_lt_top
/-- For a `C¹` map `Φ : ℝⁿ → ℝ^Q` with `c |w - w'| ≤ |Φ w - Φ w'|` on an open `Ω ⊆ ℝⁿ` and a
compact `K ⊆ ℝ^Q`, `Ω ∩ Φ⁻¹(K)` lies in a bounded open `s ⊆ Ω` on which `Φ` is Lipschitz. -/
theorem Submission.lpf_wtc_caf_lipschitz_localization :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (K : Set (Eucl Q)), IsOpen Ω →
      ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      IsCompact K → ∃ (s : Set (Eucl n)) (L : ℝ≥0), IsOpen s ∧ s ⊆ Ω ∧ Ω ∩ Φ ⁻¹' K ⊆ s ∧
        Bornology.IsBounded s ∧ LipschitzOnWith L Φ s := by
  intro Q n Φ Ω K hΩ hΦ ⟨c, hc, hcΦ⟩ hK
  rcases (Ω ∩ Φ ⁻¹' K).eq_empty_or_nonempty with h | ⟨w₀, hw₀, hw₀K⟩
  · exact ⟨∅, 0, isOpen_empty, empty_subset Ω, h.subset, Bornology.isBounded_empty,
      lipschitzOnWith_empty 0 Φ⟩
  -- `s = Ω ∩ B_ρ(w₀)` with `ρ = D / c + 1`, `D ≥ diam K`.
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hK.isBounded
  -- `DΦ` is bounded on the compact convex ball `B̄_ρ(w₀)`, so `Φ` is Lipschitz on it.
  obtain ⟨C, hC⟩ := (isCompact_closedBall w₀ (D / c + 1)).exists_bound_of_continuousOn
    (hΦ.continuous_fderiv one_ne_zero).continuousOn
  have hLip : LipschitzOnWith (Real.toNNReal C) Φ (closedBall w₀ (D / c + 1)) :=
    (convex_closedBall w₀ (D / c + 1)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hΦ.differentiable one_ne_zero x)
      (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact (hC x hx).trans (Real.le_coe_toNNReal C))
  refine ⟨Ω ∩ ball w₀ (D / c + 1), Real.toNNReal C, hΩ.inter isOpen_ball, inter_subset_left,
    fun v ⟨hv, hvK⟩ => ⟨hv, ?_⟩, isBounded_ball.subset inter_subset_right,
    hLip.mono (inter_subset_right.trans ball_subset_closedBall)⟩
  -- `c |v - w₀| ≤ |Φ v - Φ w₀| ≤ D`, so `|v - w₀| ≤ D / c < ρ`.
  rw [mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt ?_ (lt_add_one (D / c))
  rw [le_div_iff₀ hc, mul_comm]
  exact (hcΦ v hv w₀ hw₀).trans ((dist_eq_norm (Φ v) (Φ w₀)).symm.trans_le (hD hvK hw₀K))
/-- Signed area formula from the nonnegative one: if `∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s J · (g ∘ Φ) dLⁿ`
for every Borel `g ≥ 0`, then `∫_{Φ(Ω)} h dHⁿ = ∫_Ω J · (h ∘ Φ) dLⁿ` for every continuous
compactly supported `h` with `Ω ∩ Φ⁻¹(spt h) ⊆ s`. -/
theorem Submission.lpf_wtc_caf_signed_of_lintegral :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω s : Set (Eucl n)) (J : Eucl n → ℝ) (h : Eucl Q → ℝ),
      IsOpen Ω → IsOpen s → s ⊆ Ω → Bornology.IsBounded s → Continuous Φ → InjOn Φ Ω →
      Continuous J → (∀ v, 0 ≤ J v) → Continuous h → HasCompactSupport h →
      Ω ∩ Φ ⁻¹' tsupport h ⊆ s →
      (∀ g : Eucl Q → ℝ≥0∞, Measurable g →
        ∫⁻ y in Φ '' s, g y ∂(μHE[n] : Measure (Eucl Q)) =
          ∫⁻ v in s, ENNReal.ofReal (J v) * g (Φ v) ∂(volume : Measure (Eucl n))) →
      ∫ x in Φ '' Ω, h x ∂(μHE[n] : Measure (Eucl Q)) =
        ∫ v in Ω, J v * h (Φ v) ∂(volume : Measure (Eucl n)) := by
  intro Q n Φ Ω s J h hΩ hs hsΩ hsb hΦ hinj hJ hJ0 hh hhc hsupp H
  -- `h ∘ Φ` vanishes on `Ω \ s`.
  have hvan : ∀ v ∈ Ω \ s, h (Φ v) = 0 := fun v hv =>
    image_eq_zero_of_notMem_tsupport fun hK => hv.2 (hsupp ⟨hv.1, hK⟩)
  -- Bounds: `‖J‖ ≤ C` on `s`, `‖h‖ ≤ M`, and `Lⁿ(s) < ∞`.
  obtain ⟨C, hC⟩ := hsb.isCompact_closure.exists_bound_of_continuousOn hJ.continuousOn
  have hJC : ∀ v ∈ s, ‖J v‖ ≤ C := fun v hv => hC v (subset_closure hv)
  obtain ⟨M, hM⟩ := hh.bounded_above_of_compact_support hhc
  have hvol : volume s < ∞ := hsb.measure_lt_top
  -- `Hⁿ(Φ(s)) < ∞`: the identity with `g ≡ 1`.
  have hfin : (μHE[n] : Measure (Eucl Q)) (Φ '' s) < ∞ := by
    have h1 := H (fun _ => 1) measurable_const
    rw [setLIntegral_one] at h1
    rw [h1]
    calc ∫⁻ v in s, ENNReal.ofReal (J v) * 1 ∂volume
        ≤ ∫⁻ _ in s, ENNReal.ofReal C ∂volume :=
          setLIntegral_mono measurable_const fun v hv => by
            rw [mul_one]
            exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hJC v hv))
      _ = ENNReal.ofReal C * volume s := setLIntegral_const s _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol
  -- Integrability of `h` on `Φ(s)` and of `J · (h ∘ Φ)` on `s`.
  have hint₁ : IntegrableOn h (Φ '' s) (μHE[n] : Measure (Eucl Q)) :=
    Measure.integrableOn_of_bounded hfin.ne hh.aestronglyMeasurable (ae_of_all _ hM)
  have hint₂ : IntegrableOn (fun v => J v * h (Φ v)) s volume := by
    refine Measure.integrableOn_of_bounded (M := C * M) hvol.ne
      (hJ.mul (hh.comp hΦ)).aestronglyMeasurable
      (ae_restrict_of_forall_mem hs.measurableSet fun v hv => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg' (hJC v hv) (hM _) (norm_nonneg _)
      ((norm_nonneg _).trans (hJC v hv))
  -- The identity for `ofReal ∘ h` and `ofReal ∘ (-h)`, using `J ≥ 0`.
  have ePos : ∫⁻ y in Φ '' s, ENNReal.ofReal (h y) ∂(μHE[n] : Measure (Eucl Q)) =
      ∫⁻ v in s, ENNReal.ofReal (J v * h (Φ v)) ∂(volume : Measure (Eucl n)) := by
    rw [H (fun y => ENNReal.ofReal (h y)) (ENNReal.measurable_ofReal.comp hh.measurable)]
    exact lintegral_congr fun v => (ENNReal.ofReal_mul (hJ0 v)).symm
  have eNeg : ∫⁻ y in Φ '' s, ENNReal.ofReal (-h y) ∂(μHE[n] : Measure (Eucl Q)) =
      ∫⁻ v in s, ENNReal.ofReal (-(J v * h (Φ v))) ∂(volume : Measure (Eucl n)) := by
    rw [H (fun y => ENNReal.ofReal (-h y)) (ENNReal.measurable_ofReal.comp hh.measurable.neg)]
    exact lintegral_congr fun v => by rw [← mul_neg, ENNReal.ofReal_mul (hJ0 v)]
  -- The signed identity on `s`.
  have key : ∫ x in Φ '' s, h x ∂(μHE[n] : Measure (Eucl Q)) =
      ∫ v in s, J v * h (Φ v) ∂(volume : Measure (Eucl n)) := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint₁,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint₂, ePos, eNeg]
  -- The integrands vanish on `Ω \ s` and `Φ(Ω) \ Φ(s)`; `Φ(Ω)` is Borel by Lusin–Souslin.
  have eΩ : ∫ v in Ω, J v * h (Φ v) ∂(volume : Measure (Eucl n)) =
      ∫ v in s, J v * h (Φ v) ∂(volume : Measure (Eucl n)) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hsΩ fun v hv => by
      rw [hvan v hv, mul_zero]
  have eΦΩ : ∫ x in Φ '' Ω, h x ∂(μHE[n] : Measure (Eucl Q)) =
      ∫ x in Φ '' s, h x ∂(μHE[n] : Measure (Eucl Q)) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hΩ.measurableSet.image_of_continuousOn_injOn hΦ.continuousOn hinj) (image_mono hsΩ) ?_
    rintro _ ⟨⟨v, hv, rfl⟩, hvs⟩
    exact hvan v ⟨hv, fun hvs' => hvs (mem_image_of_mem Φ hvs')⟩
  rw [eΦΩ, eΩ, key]
/-- Injective area formula on a `C¹` antilipschitz chart (Simon Ch. 2, (3.1), (3.2), (3.5)):
if `Φ : ℝⁿ → ℝ^Q` is `C¹`, `Ω ⊆ ℝⁿ` is open and `c |w - w'| ≤ |Φ w - Φ w'|` on `Ω` for some
`c > 0`, then `∫_{Φ(Ω)} h dHⁿ = ∫_Ω JΦ(v) h(Φ(v)) dLⁿ(v)` for every `h ∈ C_c(ℝ^Q, ℝ)`, where
`JΦ(v) = √det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)`.

Proof.  `JΦ(v) = normDet(DΦ(v))` (`LinearMap.normDet_sq_eq_det_gram` for the standard basis), and
`JΦ` is continuous and nonnegative; `Φ` is injective on `Ω`.  Localize to a bounded open
`s ⊆ Ω` containing `Ω ∩ Φ⁻¹(spt h)` on which `Φ` is Lipschitz
(`lpf_wtc_caf_lipschitz_localization`).  As `Φ` is injective on `s`, the fibre sum of the
weighted area formula on `s` (`weighted_area_formula_lipschitzOn_fiberSum`, weight `g ∘ Φ`) is
the indicator of the Borel set `Φ(s)` applied to `g`, and the within Jacobian on the open `s` is
`JΦ`; this gives `∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s JΦ (g ∘ Φ) dLⁿ` for every Borel `g ≥ 0`.  The signed
identity on `Ω` then follows from `lpf_wtc_caf_signed_of_lintegral`. -/
theorem Submission.lpf_wtc_chart_area_formula : ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ h : Eucl Q → ℝ, Continuous h → HasCompactSupport h → ∫ x in Φ '' Ω, h x ∂(μHE[n] : Measure (Eucl Q)) = ∫ v in Ω, Real.sqrt (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1)) (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det * h (Φ v) := by
  intro Q n Φ Ω hΩ hΦ hanti h hh hsupp
  -- The Gram-determinant Jacobian `JΦ(v) = √det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)`.
  set J : Eucl n → ℝ := fun v => Real.sqrt (Matrix.of fun i j : Fin n =>
    inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1))
      (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det with hJ
  -- Step 1: `JΦ(v) = normDet(DΦ(v))`, since `normDet(A)² = det(⟨A eᵢ, A eⱼ⟩)` and `normDet ≥ 0`.
  have hJdet : ∀ v, J v = (fderiv ℝ Φ v).normDet := by
    intro v
    have hgram := LinearMap.normDet_sq_eq_det_gram (fderiv ℝ Φ v).toLinearMap
      (EuclideanSpace.basisFun (Fin n) ℝ)
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe] at hgram
    rw [hJ]
    change Real.sqrt (Matrix.gram ℝ fun i : Fin n =>
      fderiv ℝ Φ v (EuclideanSpace.single i 1)).det = _
    rw [← hgram]
    exact Real.sqrt_sq (LinearMap.normDet_nonneg _)
  -- `JΦ` is continuous (`DΦ` is continuous) and nonnegative.
  have hJcont : Continuous J := by
    have hD : Continuous fun v => fderiv ℝ Φ v := hΦ.continuous_fderiv one_ne_zero
    have hcol : ∀ i : Fin n, Continuous fun v => fderiv ℝ Φ v (EuclideanSpace.single i 1) :=
      fun i => hD.clm_apply continuous_const
    exact Real.continuous_sqrt.comp
      (continuous_matrix fun i j => (hcol i).inner (hcol j)).matrix_det
  have hJnonneg : ∀ v, 0 ≤ J v := fun v => Real.sqrt_nonneg _
  -- `Φ` is injective on `Ω` by the lower bound.
  have hinj : InjOn Φ Ω := by
    obtain ⟨c, hc, hcΦ⟩ := hanti
    intro w hw w' hw' hww'
    have hle := hcΦ w hw w' hw'
    rw [hww', sub_self, norm_zero] at hle
    have h0 : ‖w - w'‖ ≤ 0 := by
      by_contra hpos
      exact absurd hle (not_le.2 (mul_pos hc (lt_of_not_ge hpos)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  -- Step 2: a bounded open `s ⊆ Ω` carrying `Ω ∩ Φ⁻¹(spt h)` on which `Φ` is Lipschitz.
  obtain ⟨s, L, hs, hsΩ, hcover, hsb, hLip⟩ :=
    Submission.lpf_wtc_caf_lipschitz_localization Q n Φ Ω (tsupport h) hΩ hΦ hanti hsupp
  -- Step 3: the nonnegative identity on `s`, from the injective weighted area formula.
  have hlint : ∀ g : Eucl Q → ℝ≥0∞, Measurable g →
      ∫⁻ y in Φ '' s, g y ∂(μHE[n] : Measure (Eucl Q)) =
        ∫⁻ v in s, ENNReal.ofReal (J v) * g (Φ v) ∂(volume : Measure (Eucl n)) := by
    intro g hg
    have hinjs : InjOn Φ s := hinj.mono hsΩ
    have hsm : MeasurableSet s := hs.measurableSet
    have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum
      hsm.nullMeasurableSet hLip (w := fun v => g (Φ v))
      (hg.comp hΦ.continuous.measurable).aemeasurable
    rw [finrank_euclideanSpace_fin] at harea
    -- Injectivity: the fibre sum is the indicator of `Φ(s)` applied to `g`.
    have hfib : ∀ y, Poincare.SimonGMT.Chapter02.weightedAreaFiberSum s Φ (fun v => g (Φ v)) y =
        (Φ '' s).indicator g y := by
      intro y
      unfold Poincare.SimonGMT.Chapter02.weightedAreaFiberSum
        Poincare.SimonGMT.Chapter02.areaFiber
      by_cases hy : y ∈ Φ '' s
      · obtain ⟨x, hx, rfl⟩ := hy
        rw [indicator_of_mem (mem_image_of_mem Φ hx),
          tsum_eq_single (⟨x, hx, rfl⟩ : {x' // x' ∈ s ∧ Φ x' = Φ x})]
        intro z hz
        exact absurd (Subtype.ext (hinjs z.2.1 hx z.2.2)) hz
      · rw [indicator_of_notMem hy]
        have : IsEmpty {x' // x' ∈ s ∧ Φ x' = y} := ⟨fun z => hy ⟨z.1, z.2.1, z.2.2⟩⟩
        exact tsum_empty
    simp_rw [hfib] at harea
    rw [lintegral_indicator (hsm.image_of_continuousOn_injOn hΦ.continuous.continuousOn hinjs)]
      at harea
    rw [harea]
    refine setLIntegral_congr_fun hsm fun v hv => ?_
    simp only [Poincare.SimonGMT.Chapter02.areaJacobianWithin, fderivWithin_of_isOpen hs hv,
      hJdet v]
  -- Steps 4–5: the signed identity, extended from `s, Φ(s)` back to `Ω, Φ(Ω)`.
  exact Submission.lpf_wtc_caf_signed_of_lintegral Q n Φ Ω s J h hΩ hs hsΩ hsb hΦ.continuous
    hinj hJcont hJnonneg hh hsupp hcover hlint

/-- A `C¹` chart that is antilipschitz on the open set `Ω` has, at each `y = Φ(w)` (`w ∈ Ω`),
the approximate tangent space `T = DΦ(w)(ℝⁿ)` (Simon Ch. 3, Def. 1.4) of `N = Φ(Ω)`.  The
blow-up integral `∫_{η_{y,λ}(N)} φ dHⁿ` is `(λⁿ)⁻¹ ∫_Ω JΦ(v) φ(λ⁻¹(Φ(v) − y)) dv` (blow-up change
of variables, then the area formula), which tends to `∫ JΦ(w) φ(DΦ(w)s) ds`; the area formula for
the linear map `DΦ(w)` identifies this limit with `∫_T φ dHⁿ`. -/
theorem Submission.lpf_wtc_chart_approx_tangent :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen Ω → ContDiff ℝ 1 Φ →
      (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      ∀ w ∈ Ω, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (Φ '' Ω) (Φ w)
        (LinearMap.range (fderiv ℝ Φ w).toLinearMap) := by
  intro Q n Φ Ω hΩ hΦ hanti w hw
  obtain ⟨c, hc, hcΩ⟩ := hanti
  have hdiff : DifferentiableAt ℝ Φ w := hΦ.differentiable one_ne_zero w
  -- `c‖s‖ ≤ ‖DΦ(w)s‖`: `DΦ(w)` is injective and `c`-antilipschitz on `ℝⁿ`.
  have hlow : ∀ s : Eucl n, c * ‖s‖ ≤ ‖fderiv ℝ Φ w s‖ :=
    Submission.lpf_wtc_cat_fderiv_lower_bound Q n Φ Ω c w hΩ hw hdiff hcΩ
  have hinj : Function.Injective (fderiv ℝ Φ w) := by
    intro s s' hss'
    have h := hlow (s - s')
    rw [map_sub, hss', sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by nlinarith [norm_nonneg (s - s')]))
  refine ⟨?_, fun f => ?_⟩
  · exact (LinearMap.finrank_range_of_inj (f := (fderiv ℝ Φ w).toLinearMap) hinj).trans
      finrank_euclideanSpace_fin
  -- The area formula for the linear map `DΦ(w)` on `ℝⁿ` evaluates the limit `∫_T φ dHⁿ`.
  have hT : ∫ y in (LinearMap.range (fderiv ℝ Φ w).toLinearMap : Set (Eucl Q)), f y
        ∂(μHE[n] : Measure (Eucl Q)) =
      ∫ s, Real.sqrt (Matrix.of fun i j : Fin n =>
          inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1))
            (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det * f (fderiv ℝ Φ w s) := by
    have h := Submission.lpf_wtc_chart_area_formula Q n (fderiv ℝ Φ w) univ isOpen_univ
      (fderiv ℝ Φ w).contDiff
      ⟨c, hc, fun v _ v' _ => by rw [← map_sub (fderiv ℝ Φ w)]; exact hlow (v - v')⟩
      f f.continuous f.hasCompactSupport
    simp only [image_univ, Measure.restrict_univ, ContinuousLinearMap.fderiv] at h
    rwa [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  rw [hT]
  refine (Submission.lpf_wtc_cat_rescaled_integral_tendsto Q n Φ Ω
    (fun v => Real.sqrt (Matrix.of fun i j : Fin n =>
      inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1))
        (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det) f w hΩ hw hΦ.continuous hdiff
    ⟨c, hc, hcΩ⟩ (Submission.lpf_wtc_cat_gram_jacobian_continuous Q n Φ hΦ) f.continuous
    f.hasCompactSupport).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `η = η_{Φ(w),r}` is a homeomorphism, so `φ ∘ η` is again continuous with compact support.
  let e : Eucl Q ≃ₜ Eucl Q :=
    (Homeomorph.addRight (-Φ w)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl Q → Eucl Q) = Poincare.SimonGMT.Chapter03.blowUpMap (Φ w) r := by
    funext x
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hcont : Continuous fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ w) r x) := by
    rw [← he]
    exact f.continuous.comp e.continuous
  have hsupp : HasCompactSupport fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ w) r x) := by
    rw [← he]
    exact f.hasCompactSupport.comp_homeomorph e
  -- Blow up `Φ(Ω)` at `Φ(w)`, then pull the integral back to `Ω` by the area formula.
  rw [Submission.lpf_wtc_blowup_setIntegral_image Q n (Φ w) r (Φ '' Ω) f hr,
    Submission.lpf_wtc_chart_area_formula Q n Φ Ω hΩ hΦ ⟨c, hc, hcΩ⟩ _ hcont hsupp]
  rfl
/-- Lusin decomposition (Simon Ch. 3, Remark 1.8(1)): a positive weight `θ`, `Hⁿ`-integrable on
`M ∩ K` for compact `K ⊆ V`, is continuous on countably many compact pieces `C k ⊆ M` of finite
`Hⁿ`-measure which cover `M` up to an `Hⁿ`-null set. -/
theorem Submission.lpf_wtc_lusin_compact_pieces :
    ∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ), IsOpen V → M ⊆ V →
      NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
        IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) →
      ∃ C : ℕ → Set (Eucl Q), (∀ k, IsCompact (C k)) ∧ (∀ k, C k ⊆ M) ∧
        (∀ k, ContinuousOn θ (C k)) ∧ (∀ k, (μHE[n] : Measure (Eucl Q)) (C k) < ∞) ∧
        (μHE[n] : Measure (Eucl Q)) (M \ ⋃ k, C k) = 0 := by
  intro Q n V M θ hV hMV hM hθ hint
  set μ : Measure (Eucl Q) := μHE[n]
  -- Compact sets `K i = F i ∩ closedBall 0 i ⊆ V` covering `V`.
  obtain ⟨F, hFc, hFV, hFU, hFmono⟩ := hV.exists_iUnion_isClosed
  set K : ℕ → Set (Eucl Q) := fun i => F i ∩ closedBall 0 i
  have hKc : ∀ i, IsCompact (K i) := fun i => (isCompact_closedBall 0 (i : ℝ)).inter_left (hFc i)
  have hKV : ∀ i, K i ⊆ V := fun i => inter_subset_left.trans (hFV i)
  have hcover : ∀ x ∈ V, ∃ i, x ∈ K i := by
    intro x hx
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    exact ⟨max i j, hFmono (le_max_left i j) hi,
      mem_closedBall_zero_iff.2 (hj.trans (Nat.cast_le.2 (le_max_right i j)))⟩
  -- Lusin's theorem for a Borel set `E` of finite measure and a Borel function `g`.
  have lusin : ∀ (E : Set (Eucl Q)) (g : Eucl Q → ℝ), MeasurableSet E → μ E ≠ ∞ → Measurable g →
      ∃ G : ℕ → Set (Eucl Q), (∀ l, IsClosed (G l)) ∧ (∀ l, G l ⊆ E) ∧
        (∀ l, ContinuousOn g (G l)) ∧ μ (E \ ⋃ l, G l) = 0 := by
    intro E g hE hμE hg
    have : IsFiniteMeasure (μ.restrict E) := isFiniteMeasure_restrict.2 hμE
    -- A measurable `S` is relatively open in some closed `H ⊆ E` with `μ (E \ H) < δ`.
    have step : ∀ S : Set (Eucl Q), MeasurableSet S → ∀ δ : ℝ≥0∞, δ ≠ 0 →
        ∃ H, IsClosed H ∧ H ⊆ E ∧ μ (E \ H) < δ ∧ ∃ O, IsOpen O ∧ S ∩ H = O ∩ H := by
      intro S hS δ hδ
      have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
      obtain ⟨H₁, hH₁S, hH₁c, hH₁⟩ :=
        (hE.inter hS).exists_isClosed_sdiff_lt (μ := μ.restrict E) (measure_ne_top _ _) hδ2
      obtain ⟨H₂, hH₂S, hH₂c, hH₂⟩ :=
        (hE.diff hS).exists_isClosed_sdiff_lt (μ := μ.restrict E) (measure_ne_top _ _) hδ2
      refine ⟨H₁ ∪ H₂, hH₁c.union hH₂c,
        union_subset (hH₁S.trans inter_subset_left) (hH₂S.trans sdiff_subset), ?_,
        H₂ᶜ, hH₂c.isOpen_compl, ?_⟩
      · calc μ (E \ (H₁ ∪ H₂)) ≤ μ ((E ∩ S) \ H₁ ∪ (E \ S) \ H₂) := by
              refine measure_mono fun x hx => ?_
              by_cases hxS : x ∈ S
              · exact Or.inl ⟨⟨hx.1, hxS⟩, fun h => hx.2 (Or.inl h)⟩
              · exact Or.inr ⟨⟨hx.1, hxS⟩, fun h => hx.2 (Or.inr h)⟩
          _ ≤ μ ((E ∩ S) \ H₁) + μ ((E \ S) \ H₂) := measure_union_le _ _
          _ = μ.restrict E ((E ∩ S) \ H₁) + μ.restrict E ((E \ S) \ H₂) := by
              rw [Measure.restrict_eq_self _ (sdiff_subset.trans inter_subset_left),
                Measure.restrict_eq_self _ (sdiff_subset.trans sdiff_subset)]
          _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hH₁ hH₂
          _ = δ := ENNReal.add_halves δ
      · ext x
        constructor
        · rintro ⟨hxS, hxH⟩
          exact ⟨fun h => (hH₂S h).2 hxS, hxH⟩
        · rintro ⟨hxO, hxH | hxH⟩
          · exact ⟨(hH₁S hxH).2, Or.inl hxH⟩
          · exact absurd hxH hxO
    -- Doing this for `g⁻¹(q, ∞)` and `g⁻¹(-∞, q)`, `q ∈ ℚ`, makes `g` continuous on `⋂ H`.
    have piece : ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ H, IsClosed H ∧ H ⊆ E ∧ μ (E \ H) < ε ∧ ContinuousOn g H := by
      intro ε hε
      obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × Bool)
      set S : ℚ × Bool → Set (Eucl Q) := fun p =>
        bif p.2 then g ⁻¹' Ioi (p.1 : ℝ) else g ⁻¹' Iio (p.1 : ℝ)
      have hS : ∀ p, MeasurableSet (S p) := by
        rintro ⟨q, b⟩
        cases b
        · exact hg measurableSet_Iio
        · exact hg measurableSet_Ioi
      choose H hHc hHE hHμ O hOo hSO using fun p =>
        step (S p) (hS p) (δ p) (ENNReal.coe_ne_zero.2 (hδpos p).ne')
      refine ⟨⋂ p, H p, isClosed_iInter hHc, (iInter_subset _ (0, true)).trans (hHE _), ?_, ?_⟩
      · calc μ (E \ ⋂ p, H p) = μ (⋃ p, E \ H p) := by rw [sdiff_iInter]
          _ ≤ ∑' p, μ (E \ H p) := measure_iUnion_le _
          _ ≤ ∑' p, (δ p : ℝ≥0∞) := ENNReal.tsum_le_tsum fun p => (hHμ p).le
          _ < ε := hδsum
      · intro x hx
        have hxH : ∀ p, x ∈ H p := mem_iInter.1 hx
        have key : ∀ p, x ∈ S p → ∀ᶠ y in 𝓝[⋂ p, H p] x, y ∈ S p := by
          intro p hxp
          have hxO : x ∈ O p := ((hSO p).subset ⟨hxp, hxH p⟩).1
          filter_upwards [mem_nhdsWithin_of_mem_nhds ((hOo p).mem_nhds hxO),
            self_mem_nhdsWithin] with y hyO hyH
          exact ((hSO p).symm.subset ⟨hyO, mem_iInter.1 hyH p⟩).1
        refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
        · obtain ⟨q, haq, hqx⟩ := exists_rat_btwn ha
          filter_upwards [key (q, true) hqx] with y hy
          exact haq.trans hy
        · obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn hb
          filter_upwards [key (q, false) hxq] with y hy
          exact lt_trans hy hqb
    choose G hGc hGE hGμ hGcont using fun l : ℕ =>
      piece ((l : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top l))
    refine ⟨G, hGc, hGE, hGcont, ?_⟩
    by_contra h
    obtain ⟨l, hl⟩ := ENNReal.exists_inv_nat_lt h
    exact lt_asymm (hl.trans_le (measure_mono (sdiff_subset_sdiff_right (subset_iUnion G l))))
      (hGμ l)
  -- A Borel representative `g` of `θ` on `M`, and a Borel core `B ⊆ M` on which `θ = g`.
  have hMU : M = ⋃ i, M ∩ K i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hx => (hcover x (hMV hx)).imp fun i hi => ⟨hx, hi⟩, fun ⟨_, hx, _⟩ => hx⟩
  have hθm : AEMeasurable θ (μ.restrict M) := by
    rw [hMU]
    exact aemeasurable_iUnion_iff.2 fun i => Integrable.aemeasurable (hint (K i) (hKc i) (hKV i))
  set g := hθm.mk θ
  have hg : Measurable g := hθm.measurable_mk
  have hbad : μ {x | ¬(x ∈ M → θ x = g x)} = 0 := ae_iff.1 ((ae_restrict_iff'₀ hM).1 hθm.ae_eq_mk)
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null hbad
  obtain ⟨B₀, hB₀M, hB₀m, hB₀ae⟩ := hM.exists_measurable_subset_ae_eq
  set B := B₀ \ Z
  have hBm : MeasurableSet B := hB₀m.diff hZm
  have hBM : B ⊆ M := sdiff_subset.trans hB₀M
  have hθgB : ∀ x ∈ B, θ x = g x := fun x hx => by
    by_contra h
    exact hx.2 (hZsub fun hh => h (hh (hBM hx)))
  have hMB : μ (M \ B) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null (ae_eq_set.1 hB₀ae).2 hZ0)
    by_cases hxB₀ : x ∈ B₀
    · exact Or.inr (by_contra fun hz => hx.2 ⟨hxB₀, hz⟩)
    · exact Or.inl ⟨hx.1, hxB₀⟩
  -- Borel pieces `E i j = B ∩ K i ∩ {g > 1/(j+1)}` of finite measure.
  set E : ℕ → ℕ → Set (Eucl Q) := fun i j => B ∩ K i ∩ g ⁻¹' Ioi ((j : ℝ) + 1)⁻¹
  have hEm : ∀ i j, MeasurableSet (E i j) := fun i j =>
    (hBm.inter (hKc i).isClosed.measurableSet).inter (hg measurableSet_Ioi)
  have hEfin : ∀ i j, μ (E i j) ≠ ∞ := by
    intro i j htop
    have hc : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hle : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ * μ (E i j) ≤ ∫⁻ x in M ∩ K i, ‖θ x‖ₑ ∂μ :=
      calc ENNReal.ofReal ((j : ℝ) + 1)⁻¹ * μ (E i j)
          = ∫⁻ _ in E i j, ENNReal.ofReal ((j : ℝ) + 1)⁻¹ ∂μ := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in E i j, ‖θ x‖ₑ ∂μ := setLIntegral_mono' (hEm i j) fun x hx => by
            rw [Real.enorm_eq_ofReal_abs, hθgB x hx.1.1]
            exact ENNReal.ofReal_le_ofReal (hx.2.le.trans (le_abs_self _))
        _ ≤ ∫⁻ x in M ∩ K i, ‖θ x‖ₑ ∂μ :=
            lintegral_mono_set fun x hx => ⟨hBM hx.1.1, hx.1.2⟩
    have hlt := hle.trans_lt (hint (K i) (hKc i) (hKV i)).2
    rw [htop, ENNReal.mul_top hc] at hlt
    exact lt_irrefl _ hlt
  -- Lusin on each `E i j`; the pieces, enumerated by `Nat.unpair`, are the `C k`.
  choose G hGc hGE hGcont hGnull using fun i j => lusin (E i j) g (hEm i j) (hEfin i j) hg
  refine ⟨fun k => G k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2, fun k => ?_, fun k => ?_,
    fun k => ?_, fun k => ?_, ?_⟩
  · exact (hKc _).of_isClosed_subset (hGc _ _ _)
      ((hGE _ _ _).trans (inter_subset_left.trans inter_subset_right))
  · exact (hGE _ _ _).trans (inter_subset_left.trans (inter_subset_left.trans hBM))
  · exact (hGcont _ _ _).congr fun x hx => hθgB x ((hGE _ _ _) hx).1.1
  · exact (measure_mono (hGE _ _ _)).trans_lt (lt_top_iff_ne_top.2 (hEfin _ _))
  · refine measure_mono_null (fun x hx => ?_) (measure_union_null hMB
      (measure_iUnion_null fun i => measure_iUnion_null fun j => hGnull i j))
    obtain ⟨hxM, hxC⟩ := hx
    by_cases hxB : x ∈ B
    · right
      obtain ⟨i, hi⟩ := hcover x (hMV hxM)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt ((hθgB x hxB) ▸ hθ x hxM)
      refine mem_iUnion₂.2 ⟨i, j, ⟨⟨hxB, hi⟩, by simpa [one_div] using hj⟩, fun hxG => hxC ?_⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hxG
      exact mem_iUnion.2 ⟨Nat.pair i (Nat.pair j l), by simpa [Nat.unpair_pair] using hl⟩
    · exact Or.inl ⟨hxM, hxB⟩
/-- Localized upper density theorem (Simon Ch. 1, 3.6) for `ν = (Hⁿ ⌞ S).withDensity g`: if
`∫⁻_{S ∩ K} g dHⁿ < ∞` for every compact `K ⊆ W`, then `ν(B̄_ρ(y)) / ρⁿ → 0` as `ρ → 0+` for
`Hⁿ`-a.e. `y ∈ W \ S`. -/
theorem Submission.lpf_wtc_ae_zero_density_off_set :
    ∀ (Q n : ℕ) (W S : Set (Eucl Q)) (g : Eucl Q → ℝ≥0∞), IsOpen W →
      NullMeasurableSet S (μHE[n] : Measure (Eucl Q)) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ W →
        ∫⁻ x in S ∩ K, g x ∂(μHE[n] : Measure (Eucl Q)) < ∞) →
      ∀ᵐ y ∂(μHE[n] : Measure (Eucl Q)), y ∈ W → y ∉ S →
        Tendsto (fun ρ : ℝ => (∫⁻ x in S ∩ closedBall y ρ, g x ∂(μHE[n] : Measure (Eucl Q))) /
          ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
  intro Q n W S g hW hS hfin
  set μ : Measure (Eucl Q) := μHE[n] with hμ
  -- Step 1: `ν = (μ ⌞ S).withDensity g`, so `ν B = ∫⁻_{S ∩ B} g dμ` for Borel `B`.
  set ν : Measure (Eucl Q) := (μ.restrict S).withDensity g with hν
  have hνB : ∀ B : Set (Eucl Q), MeasurableSet B → ν B = ∫⁻ x in S ∩ B, g x ∂μ := by
    intro B hB
    rw [hν, withDensity_apply _ hB, Measure.restrict_restrict hB, inter_comm B S]
  -- Step 2: the Borel hull `A ⊇ S` of `S`; `ν` does not charge `Aᶜ`.
  set A : Set (Eucl Q) := toMeasurable μ S
  have hAm : MeasurableSet A := measurableSet_toMeasurable μ S
  have hνA : ν Aᶜ = 0 := by
    rw [hνB _ hAm.compl,
      (disjoint_compl_right_iff_subset.mpr (subset_toMeasurable μ S)).inter_eq,
      Measure.restrict_empty, lintegral_zero_measure]
  -- `diam B̄_s(c) ≤ 2s`.
  have hdiam : ∀ (c : Eucl Q) (s : ℝ), ediam (closedBall c s) ≤ ENNReal.ofReal (2 * s) :=
    fun c s => ediam_le_of_forall_dist_le fun y hy z hz => by
      have := dist_triangle_right y z c
      rw [mem_closedBall] at hy hz
      linarith
  -- Step 4 (Upper Density Theorem, Simon Ch. 1, 3.6): for a finite `m` with `m Aᶜ = 0`, the
  -- points `y ∉ A` of upper density `> ε` form an `Hⁿ`-null set.  Proof: a closed `C ⊆ A`
  -- with `m (A \ C) < k⁻¹`, then a Vitali 5r-covering by disjoint balls of radius `< 1/(k+1)`
  -- missing `C`, whose total `ρⁿ`-cost is at most `k⁻¹ / ε`.
  have hcore : ∀ m : Measure (Eucl Q), m univ ≠ ∞ → m Aᶜ = 0 → ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ∞ →
      μH[n] {y | y ∉ A ∧ ∀ δ > 0, ∃ ρ ∈ Ioo 0 δ,
        ε * ENNReal.ofReal ρ ^ n < m (closedBall y ρ)} = 0 := by
    intro m hm hmA ε hε0 hεtop
    set Z := {y | y ∉ A ∧ ∀ δ > 0, ∃ ρ ∈ Ioo 0 δ,
      ε * ENNReal.ofReal ρ ^ n < m (closedBall y ρ)}
    have : IsFiniteMeasure m := ⟨lt_top_iff_ne_top.mpr hm⟩
    have hstep : ∀ k : ℕ, ∃ u : Set (Eucl Q × ℝ), u.Countable ∧
        (∀ b ∈ u, b.2 ∈ Ioo 0 (1 / ((k : ℝ) + 1))) ∧
        Z ⊆ ⋃ b ∈ u, closedBall b.1 (5 * b.2) ∧
        ε * ∑' b : u, ENNReal.ofReal b.1.2 ^ n ≤ (k : ℝ≥0∞)⁻¹ := by
      intro k
      obtain ⟨C, hCA, hCc, hCm⟩ := hAm.exists_isClosed_sdiff_lt (μ := m) (measure_ne_top m A)
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k))
      let t : Set (Eucl Q × ℝ) := {b | b.1 ∈ Z ∧ b.2 ∈ Ioo 0 (1 / ((k : ℝ) + 1)) ∧
        closedBall b.1 b.2 ⊆ Cᶜ ∧ ε * ENNReal.ofReal b.2 ^ n < m (closedBall b.1 b.2)}
      obtain ⟨u, hut, hudisj, hucov⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall t Prod.fst Prod.snd
          (1 / ((k : ℝ) + 1)) (fun b hb => hb.2.1.2.le) 5 (by norm_num)
      have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb =>
        (nonempty_ball.mpr (hut hb).2.1.1).mono ball_subset_interior_closedBall
      refine ⟨u, hucount, fun b hb => (hut hb).2.1, ?_, ?_⟩
      · -- each `y ∈ Z` lies outside the closed `C ⊆ A`, so it centers small good balls `⊆ Cᶜ`
        intro y hy
        obtain ⟨δ₀, hδ₀, hδ₀C⟩ := Metric.isOpen_iff.mp hCc.isOpen_compl y fun h => hy.1 (hCA h)
        obtain ⟨ρ, hρ, hρm⟩ := hy.2 (min δ₀ (1 / ((k : ℝ) + 1))) (by positivity)
        have hρC : closedBall y ρ ⊆ Cᶜ :=
          (closedBall_subset_ball (hρ.2.trans_le (min_le_left _ _))).trans hδ₀C
        obtain ⟨b, hbu, hb⟩ :=
          hucov (y, ρ) ⟨hy, ⟨hρ.1, hρ.2.trans_le (min_le_right _ _)⟩, hρC, hρm⟩
        exact mem_iUnion₂.mpr ⟨b, hbu, hb (mem_closedBall_self hρ.1.le)⟩
      · have := hucount.to_subtype
        calc ε * ∑' b : u, ENNReal.ofReal b.1.2 ^ n
            = ∑' b : u, ε * ENNReal.ofReal b.1.2 ^ n := ENNReal.tsum_mul_left.symm
          _ ≤ ∑' b : u, m (closedBall b.1.1 b.1.2 ∩ Cᶜ) := ENNReal.tsum_le_tsum fun b => by
              rw [inter_eq_left.mpr (hut b.2).2.2.1]
              exact (hut b.2).2.2.2.le
          _ = m (⋃ b : u, closedBall b.1.1 b.1.2 ∩ Cᶜ) := (measure_iUnion
              (fun i j hij => (hudisj i.2 j.2 (Subtype.coe_ne_coe.mpr hij)).mono
                inter_subset_left inter_subset_left)
              (fun _ => measurableSet_closedBall.inter hCc.isOpen_compl.measurableSet)).symm
          _ ≤ m Cᶜ := measure_mono (iUnion_subset fun _ => inter_subset_right)
          _ ≤ m ((A \ C) ∪ Aᶜ) := measure_mono fun x hx => by
              by_cases h : x ∈ A
              exacts [Or.inl ⟨h, hx⟩, Or.inr h]
          _ ≤ m (A \ C) + m Aᶜ := measure_union_le _ _
          _ ≤ (k : ℝ≥0∞)⁻¹ := by
              rw [hmA, add_zero]
              exact hCm.le
    choose u hucount hurad hucov husum using hstep
    have : ∀ k, Countable (u k) := fun k => (hucount k).to_subtype
    refine le_antisymm ?_ bot_le
    calc μH[n] Z ≤ liminf (fun k => ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ))
          atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) Z
            (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) ?_
            (fun k (b : u k) => closedBall b.1.1 (5 * b.1.2)) ?_ ?_
          · simpa using ENNReal.tendsto_ofReal
              ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10)
          · refine Eventually.of_forall fun k b => (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
            have := (hurad k b.1 b.2).2
            linarith
          · refine Eventually.of_forall fun k y hy => ?_
            obtain ⟨b, hbu, hb⟩ := mem_iUnion₂.mp (hucov k hy)
            exact mem_iUnion.mpr ⟨⟨b, hbu⟩, hb⟩
      _ ≤ liminf (fun k : ℕ => 10 ^ n * ((k : ℝ≥0∞)⁻¹ / ε)) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
          calc ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)
              ≤ ∑' b : u k, 10 ^ n * ENNReal.ofReal b.1.2 ^ n :=
                ENNReal.tsum_le_tsum fun b => by
                  rw [ENNReal.rpow_natCast, ← mul_pow]
                  gcongr
                  refine (hdiam _ _).trans ?_
                  rw [← ENNReal.ofReal_ofNat 10, ← ENNReal.ofReal_mul (by norm_num)]
                  exact ENNReal.ofReal_le_ofReal (by linarith)
            _ = 10 ^ n * ∑' b : u k, ENNReal.ofReal b.1.2 ^ n := ENNReal.tsum_mul_left
            _ ≤ 10 ^ n * ((k : ℝ≥0∞)⁻¹ / ε) := by
                gcongr
                rw [ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop), mul_comm]
                exact husum k
      _ = 0 := by
          refine Tendsto.liminf_eq ?_
          simpa using ENNReal.Tendsto.const_mul
            (ENNReal.Tendsto.div_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hε0))
            (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
  -- Steps 3 and 5: localize to balls `B̄_{2r}(x) ⊆ W` (finite `ν`-mass) around each point of
  -- the exceptional set, and use `μHE[n] = c • μH[n]`.
  have hmain : ∀ᵐ y ∂μ, y ∈ W → y ∉ A →
      Tendsto (fun ρ : ℝ => ν (closedBall y ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    rw [ae_iff]
    apply measure_null_of_locally_null
    intro x hx
    rw [(g_ev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((w_cd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (P_deriv _ x)
  have g_sub : ∀ a x, x ∉ A → g x - P a x = ∑ c ∈ S x, w c x * (P (q c) x - P a x) := by
    intro a x hx
    have hx' : dist x x < r x := by
      rw [dist_self]
      exact r_pos x hx
    rw [g_near x hx x hx']
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, w_sum x hx x hx', one_mul]
  -- Step 10: `g` has derivative `τ a` at every `a ∈ A`.
  have g_deriv : ∀ a ∈ A, HasFDerivAt g (τ a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, _hδ1, hD, hR⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by
      rw [dist_self]
      exact hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [g_on a ha]
    by_cases hxA : x ∈ A
    · rw [g_on x hxA]
      have hr' := hR a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hid : g x - f a - τ a (x - a) = g x - P a x := by
        rw [hPdef a x]
        ring
      rw [hid, g_sub a x hxA]
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact r_pos x hxA
      have key := convex_le ℝ (S x) (fun c => w c x) (fun c => P (q c) x - P a x) (ε * ‖x - a‖)
        (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') ?_
      · simpa only [smul_eq_mul] using key
      intro c hc
      have hbA : q c ∈ A := hqA c
      have hba : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
      have hxb : dist x (q c) ≤ 2 * dist x a :=
        (anchor1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (q c) a < δ := by linarith
      have hDb := hD (q c) hbA hbaδ
      have hr' := hR a ha haa (q c) hbA hbaδ
      have hba' : ‖q c - a‖ ≤ 3 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hba
      have hxb' : ‖x - q c‖ ≤ 2 * ‖x - a‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hxb
      calc ‖P (q c) x - P a x‖
          ≤ ‖f (q c) - f a - τ a (q c - a)‖ + ‖τ (q c) - τ a‖ * ‖x - q c‖ := P_sub a (q c) x
        _ ≤ (ε / 5) * ‖q c - a‖ + (ε / 5) * ‖x - q c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  have g_fderiv_on : ∀ a ∈ A, fderiv ℝ g a = τ a := fun a ha => (g_deriv a ha).fderiv
  -- Step 11: `Dg` is continuous at every `a ∈ A`.
  have g_cont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    have hK : (0 : ℝ) < 1 + 700 * M := by positivity
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by
      rw [hηdef]
      field_simp
    have hηε : η ≤ ε / 2 := by nlinarith
    obtain ⟨δ, hδ, hδ1, hD, hR⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [g_fderiv_on a ha, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [g_fderiv_on x hxA]
      exact (hD x hxA (by linarith)).trans hηε
    · have hrx := r_pos x hxA
      have hbA : q x ∈ A := hqA x
      have hba : dist (q x) a ≤ 2 * dist x a := q_pt x a ha
      have hbaδ : dist (q x) a < δ := by linarith
      have hDb := hD (q x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := r_scale x hdx
      have hD' : ∀ c ∈ S x, ‖τ (q c) - τ a‖ ≤ η := by
        intro c hc
        apply hD _ (hqA c)
        have hi := anchor2 x hxA a ha c hc
        linarith
      have hP' : ∀ c ∈ S x, ‖P (q c) x - P (q x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA : q c ∈ A := hqA c
        have hda : dist (q c) a ≤ 3 * dist x a := anchor2 x hxA a ha c hc
        have hdaδ : dist (q c) a < δ := by linarith
        have hxd : dist x (q c) ≤ 2 * infDist x A := anchor1 x hxA c hc
        have hxb : dist x (q x) = infDist x A := (hqd x).symm
        have hdb : dist (q c) (q x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (q c) x (q x)
          rw [dist_comm (q c) x, hxb] at ht
          linarith
        have hDd : ‖τ (q c) - τ (q x)‖ ≤ 2 * η := by
          calc ‖τ (q c) - τ (q x)‖ = ‖(τ (q c) - τ a) - (τ (q x) - τ a)‖ := by
                congr 1
                abel
            _ ≤ ‖τ (q c) - τ a‖ + ‖τ (q x) - τ a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hR (q x) hbA hbaδ (q c) hdA hdaδ
        have hdb' : ‖q c - q x‖ ≤ 3 * infDist x A := by
          rw [← dist_eq_norm]
          exact hdb
        have hxd' : ‖x - q c‖ ≤ 2 * infDist x A := by
          rw [← dist_eq_norm]
          exact hxd
        calc ‖P (q c) x - P (q x) x‖
            ≤ ‖f (q c) - f (q x) - τ (q x) (q c - q x)‖ + ‖τ (q c) - τ (q x)‖ * ‖x - q c‖ :=
              P_sub (q x) (q c) x
          _ ≤ η * ‖q c - q x‖ + (2 * η) * ‖x - q c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by
              rw [hscale]
              ring
      have hx' : dist x x < r x := by
        rw [dist_self]
        exact hrx
      have hdecomp : fderiv ℝ g x - τ a =
          (∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x := by
        rw [g_fderiv x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, w_sum x hxA x hx', w_dsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hdecomp]
      calc ‖(∑ c ∈ S x, w c x • (τ (q c) - τ a)) +
            ∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ S x, w c x • (τ (q c) - τ a)‖ +
            ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact convex_le _ (S x) (fun c => w c x) (fun c => τ (q c) - τ a) η
                (fun c _ => w_nonneg c x hxA) (w_sum x hxA x hx') hD'
            · calc ‖∑ c ∈ S x, (P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ S x, ‖(P (q c) x - P (q x) x) • fderiv ℝ (w c) x‖ := norm_sum_le _ _
                _ ≤ ∑ c ∈ S x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ S x, ‖fderiv ℝ (w c) x‖ := (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (w_dbound x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by
            field_simp
        _ = ε / 2 := heq
  -- Step 12: conclusion.
  refine ⟨g, ?_, fun a ha => ⟨g_on a ha, g_deriv a ha⟩⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (g_deriv x hx).differentiableAt
    · exact (g_cd x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact g_cont x hx
    · exact (g_cd x hx).continuousAt_fderiv one_ne_zero

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42), in the form established by its
printed proof (p. 44): a Lipschitz `g : ℝⁿ → ℝ` agrees with a `C¹` function `h` on a closed set `A`
with `Lⁿ(ℝⁿ ∖ A) < ε`, and `g` is differentiable on `A` with `Dg = Dh` there.  Rademacher gives a
Borel set `D` of full measure where `g` is differentiable; Lusin gives a closed `C ⊆ D` with `Dg|C`
continuous; the `η_k` step gives a closed `A ⊆ C` satisfying Whitney's condition (‡) (Thm 1.6);
Whitney's extension theorem then gives `h`. -/
theorem Submission.lpf_c1_approximation_real :
    ∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧ (volume : Measure (Eucl n)) Aᶜ < ε ∧
        ContDiff ℝ 1 h ∧ ∀ x ∈ A, g x = h x ∧ HasFDerivAt g (fderiv ℝ h x) x := by
  intro n g K hg ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Rademacher: `g` is differentiable on the Borel set `D`, and `Lⁿ(ℝⁿ ∖ D) = 0`.
  set D : Set (Eucl n) := {x | DifferentiableAt ℝ g x}
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  have hDc : (volume : Measure (Eucl n)) Dᶜ = 0 := ae_iff.1 hg.ae_differentiableAt
  -- Lusin: a closed `C ⊆ D` with `Lⁿ(D ∖ C) < ε / 2` on which `Dg` is continuous.
  obtain ⟨C, hCc, hCD, hDC, hgC⟩ := Submission.lpf_c1r_lusin_closed n D (fderiv ℝ g) hDm
    (measurable_fderiv ℝ g) (ε / 2) hε2
  -- The `η_k` step: a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε / 2` satisfying Whitney's (‡) for
  -- `(g, Dg)`.
  obtain ⟨A, hAc, hAC, hCA, hrem⟩ := Submission.lpf_c1r_uniform_remainder n g K hg C hCc
    (fun x hx => hCD hx) hgC (ε / 2) hε2
  -- Whitney: a `C¹` function `h` with `h = g` and `Dh = Dg` on `A`.
  obtain ⟨h, hh, hhA⟩ := Submission.lpf_c1r_whitney_extension n A g (fderiv ℝ g) hAc
    hg.continuous.continuousOn (hgC.mono hAC) hrem
  refine ⟨A, h, hAc, ?_, hh, fun x hx => ?_⟩
  · -- `ℝⁿ ∖ A ⊆ (ℝⁿ ∖ D) ∪ (D ∖ C) ∪ (C ∖ A)`, so `Lⁿ(ℝⁿ ∖ A) < 0 + ε / 2 + ε / 2 = ε`.
    have hsub : Aᶜ ⊆ Dᶜ ∪ (D \ C) ∪ (C \ A) := by
      intro x hxA
      by_cases hxD : x ∈ D
      · by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        · exact Or.inl (Or.inr ⟨hxD, hxC⟩)
      · exact Or.inl (Or.inl hxD)
    calc (volume : Measure (Eucl n)) Aᶜ ≤ volume (Dᶜ ∪ (D \ C) ∪ (C \ A)) := measure_mono hsub
      _ ≤ volume Dᶜ + volume (D \ C) + volume (C \ A) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = volume (D \ C) + volume (C \ A) := by rw [hDc, zero_add]
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hDC hCA
      _ = ε := ENNReal.add_halves ε
  · -- `Dh(x) = Dg(x)` by uniqueness of the derivative, and `g` is differentiable at `x ∈ A ⊆ D`.
    obtain ⟨hhx, hDhx⟩ := hhA x hx
    rw [hDhx.fderiv]
    exact ⟨hhx.symm, DifferentiableAt.hasFDerivAt (hCD (hAC hx))⟩

/-- Simon Ch. 2, Theorem 1.5 (`C¹` Approximation Theorem), in the form established by its printed
proof (p. 44): a Lipschitz `g : ℝⁿ → ℝ` agrees, together with its derivative, with a `C¹`
function `h` on a closed set `A` with `Lⁿ(ℝⁿ ∖ A) < ε`, and `g` is differentiable on `A`.
Rademacher, then Lusin (`lpf_c1r_lusin_closed`), the uniform remainder estimate
(`lpf_c1r_uniform_remainder`) and Whitney's extension theorem (`lpf_c1r_whitney_extension`). -/
theorem Submission.slicing_im_coarea_c1_approx :
    ∀ (n : ℕ) (g : Eucl n → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧ (volume : Measure (Eucl n)) Aᶜ < ε ∧
        ContDiff ℝ 1 h ∧ ∀ x ∈ A, g x = h x ∧ HasFDerivAt g (fderiv ℝ h x) x := by
  intro n g K hg ε hε
  -- Step 1 (Rademacher): `D = {x : g is differentiable at x}` is Borel and `Lⁿ`-conull, and
  -- `Dg = fderiv ℝ g` is Borel.
  set D : Set (Eucl n) := {x | DifferentiableAt ℝ g x}
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  have hD : (volume : Measure (Eucl n)) Dᶜ = 0 := ae_iff.mp hg.ae_differentiableAt
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Step 2 (Lusin): a closed `C ⊆ D` with `Lⁿ(D ∖ C) < ε/2` and `Dg` continuous on `C`.
  obtain ⟨C, hCc, hCD, hDC, hcont⟩ :=
    Submission.lpf_c1r_lusin_closed n D (fderiv ℝ g) hDm (measurable_fderiv ℝ g) (ε / 2) hε2
  -- Step 3 (uniform remainder): a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε/2` satisfying Whitney's
  -- condition 1.6 (‡) for `g` and `Dg`.
  obtain ⟨A, hAc, hAC, hCA, hrem⟩ := Submission.lpf_c1r_uniform_remainder n g K hg C hCc
    (fun x hx => hCD hx) hcont (ε / 2) hε2
  -- Step 4 (Whitney): a `C¹` function `h` with `h = g` and `Dh = Dg` on `A`.
  obtain ⟨h, hh, hhA⟩ := Submission.lpf_c1r_whitney_extension n A g (fderiv ℝ g) hAc
    hg.continuous.continuousOn (hcont.mono hAC) hrem
  refine ⟨A, h, hAc, ?_, hh, fun x hx => ⟨(hhA x hx).1.symm, ?_⟩⟩
  -- `ℝⁿ ∖ A ⊆ (ℝⁿ ∖ D) ∪ (D ∖ C) ∪ (C ∖ A)`.
  · calc (volume : Measure (Eucl n)) Aᶜ ≤ volume (Dᶜ ∪ (D \ C) ∪ (C \ A)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxC : x ∈ C
          · exact Or.inr ⟨hxC, hx⟩
          · by_cases hxD : x ∈ D
            · exact Or.inl (Or.inr ⟨hxD, hxC⟩)
            · exact Or.inl (Or.inl hxD)
      _ ≤ volume Dᶜ + volume (D \ C) + volume (C \ A) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ = volume (D \ C) + volume (C \ A) := by rw [hD, zero_add]
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hDC hCA
      _ = ε := ENNReal.add_halves ε
  -- `fderiv ℝ h x = Dg(x)` by uniqueness, and `g` is differentiable at `x ∈ A ⊆ C ⊆ D`.
  · rw [(hhA x hx).2.fderiv]
    exact (hCD (hAC hx) : DifferentiableAt ℝ g x).hasFDerivAt

/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) for `ℝ^Q`-valued maps, applied
componentwise as in the proof of Ch. 6, Lemma 3.9 (p. 148): a Lipschitz `u : ℝⁿ → ℝ^Q` agrees
with a `C¹` map `G`, and has Fréchet derivative `DG(x)`, at every `x` of a closed set `A` with
`Lⁿ(ℝⁿ ∖ A) < ε`. -/
theorem Submission.lpf_c1_approximation_eucl :
    ∀ (n Q : ℕ) (u : Eucl n → Eucl Q) (K : ℝ≥0), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (A : Set (Eucl n)) (G : Eucl n → Eucl Q), IsClosed A ∧
        (volume : Measure (Eucl n)) Aᶜ < ε ∧ ContDiff ℝ 1 G ∧
        ∀ x ∈ A, u x = G x ∧ HasFDerivAt u (fderiv ℝ G x) x := by
  intro n Q u K hu ε hε
  -- Split `ε`: `δ > 0` with `Q δ < ε`.
  obtain ⟨δ, hδ, hδQ⟩ := ENNReal.exists_pos_mul_lt (ENNReal.natCast_ne_top Q) hε.ne'
  -- The scalar theorem for each component `u_l = π_l ∘ u`, which is `‖π_l‖ K`-Lipschitz: a closed
  -- `A_l` with `Lⁿ(ℝⁿ ∖ A_l) < δ` and a `C¹` `h_l` with `u_l = h_l`, `Du_l = Dh_l` on `A_l`.
  have hcomp : ∀ l : Fin Q, ∃ (A : Set (Eucl n)) (h : Eucl n → ℝ), IsClosed A ∧
      (volume : Measure (Eucl n)) Aᶜ < δ ∧ ContDiff ℝ 1 h ∧
      ∀ x ∈ A, u x l = h x ∧ HasFDerivAt (fun y => u y l) (fderiv ℝ h x) x := fun l =>
    Submission.lpf_c1_approximation_real n (fun y => u y l) _
      ((EuclideanSpace.proj (𝕜 := ℝ) l).lipschitzWith.comp hu) δ hδ
  choose A h hA hAδ hh hAh using hcomp
  -- Every `y ∈ ℝ^Q` is `∑_l y_l e_l`, `e_l = EuclideanSpace.single l 1`.
  have hsum : ∀ y : Eucl Q, ∑ l, y l • EuclideanSpace.single l (1 : ℝ) = y := fun y => by
    have hy := (EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr y
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hy
    exact hy
  -- `A = ⋂_l A_l` and `G = ∑_l h_l e_l`.
  refine ⟨⋂ l, A l, fun x => ∑ l, h l x • EuclideanSpace.single l (1 : ℝ), isClosed_iInter hA,
    ?_, ContDiff.sum fun l _ => (hh l).smul_const _, ?_⟩
  · -- `Lⁿ(ℝⁿ ∖ A) ≤ ∑_l Lⁿ(ℝⁿ ∖ A_l) ≤ Q δ < ε`.
    rw [compl_iInter]
    calc (volume : Measure (Eucl n)) (⋃ l, (A l)ᶜ)
        ≤ ∑ l, (volume : Measure (Eucl n)) (A l)ᶜ := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _l : Fin Q, δ := Finset.sum_le_sum fun l _ => (hAδ l).le
      _ = δ * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ < ε := hδQ
  · intro x hx
    rw [mem_iInter] at hx
    -- `G` and `u = ∑_l u_l e_l` both have derivative `Λ = ∑_l (Dh_l(x)).smulRight e_l` at `x`.
    have hG : HasFDerivAt (fun y => ∑ l, h l y • EuclideanSpace.single l (1 : ℝ))
        (∑ l, (fderiv ℝ (h l) x).smulRight (EuclideanSpace.single l (1 : ℝ))) x :=
      HasFDerivAt.fun_sum fun l _ =>
        ((hh l).differentiable one_ne_zero x).hasFDerivAt.smul_const _
    have hu' : HasFDerivAt (fun y => ∑ l, u y l • EuclideanSpace.single l (1 : ℝ))
        (∑ l, (fderiv ℝ (h l) x).smulRight (EuclideanSpace.single l (1 : ℝ))) x :=
      HasFDerivAt.fun_sum fun l _ => (hAh l x (hx l)).2.smul_const _
    rw [show (fun y => ∑ l, u y l • EuclideanSpace.single l (1 : ℝ)) = u from
      funext fun y => hsum (u y)] at hu'
    refine ⟨?_, ?_⟩
    · rw [← hsum (u x)]
      exact Finset.sum_congr rfl fun l _ => by rw [(hAh l x (hx l)).1]
    · rw [hG.fderiv]
      exact hu'
/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9 (p. 148): the
inverse-function-theorem estimate.  If `G : ℝⁿ → ℝ^Q` is `C¹` and `DG(w)` is injective, then
`c |z − z'| ≤ |G z − G z'|` for all `z, z'` in some ball `B_r(w)`, with `c > 0`. -/
theorem Submission.lpf_c1_local_antilipschitz :
    ∀ (n Q : ℕ) (G : Eucl n → Eucl Q) (w : Eucl n), ContDiff ℝ 1 G →
      Function.Injective (fderiv ℝ G w) →
      ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ, 0 < c ∧ ∀ z ∈ ball w r, ∀ z' ∈ ball w r,
        c * ‖z - z'‖ ≤ ‖G z - G z'‖ := by
  intro n Q G w hG hinj
  set A : Eucl n →L[ℝ] Eucl Q := fderiv ℝ G w
  -- `A` is injective on the finite-dimensional `ℝⁿ`, hence antilipschitz: `|v| ≤ K |A v|`,
  -- i.e. `|A v| ≥ m |v|` with `m = K⁻¹ > 0`.
  obtain ⟨K, hKpos, hK⟩ :=
    (LinearMap.injective_iff_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q)).mp hinj
  have hK0 : (0 : ℝ) < K := hKpos
  have hm : ∀ v : Eucl n, (K : ℝ)⁻¹ * ‖v‖ ≤ ‖A v‖ := by
    intro v
    rw [inv_mul_le_iff₀ hK0]
    exact ZeroHomClass.bound_of_antilipschitz (A : Eucl n →ₗ[ℝ] Eucl Q) hK v
  -- `c = m / 2`.  `A` is the strict derivative of `G` at `w`, so `G` approximates `A` with
  -- constant `c` on a neighbourhood of `w`, which contains a ball `B_r(w)`.
  set c : ℝ≥0 := K⁻¹ / 2 with hc
  have hc0 : 0 < c := by
    rw [hc]
    exact div_pos (inv_pos.mpr hKpos) two_pos
  have hcK : (c : ℝ) = (K : ℝ)⁻¹ / 2 := by
    rw [hc, NNReal.coe_div, NNReal.coe_inv, NNReal.coe_two]
  have hstrict : HasStrictFDerivAt G A w := hG.hasStrictFDerivAt one_ne_zero
  obtain ⟨s, hs, happrox⟩ := hstrict.approximates_deriv_on_nhds (c := c) (Or.inr hc0)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r, hr, c, hc0, fun z hz z' hz' => ?_⟩
  -- On `B_r(w)`, `|G z − G z' − A (z − z')| ≤ c |z − z'|`; with the triangle inequality,
  -- `m |z − z'| ≤ |A (z − z')| ≤ |G z − G z'| + c |z − z'|`, and `m − c = c`.
  have h1 : ‖G z - G z' - A (z - z')‖ ≤ c * ‖z - z'‖ := happrox z (hrs hz) z' (hrs hz')
  have h2 := hm (z - z')
  have h3 : ‖A (z - z')‖ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := by
    calc ‖A (z - z')‖ = ‖(G z - G z') - (G z - G z' - A (z - z'))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖G z - G z'‖ + ‖G z - G z' - A (z - z')‖ := norm_sub_le _ _
  rw [hcK] at h1 ⊢
  linarith

/-- Simon Ch. 3, Lemma 1.2 ("only if" part, p. 70), with each chart restricted, as in the printed
proof, to a small neighbourhood of a point where its differential is injective, so that it is both
Lipschitz and antilipschitz: a countably `n`-rectifiable `M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null
set, by countably many images `Φ_i(Ω_i)` of open sets `Ω_i ⊆ ℝⁿ` under `C¹` maps `Φ_i` with
`c_i |w − w'| ≤ |Φ_i(w) − Φ_i(w')| ≤ K_i |w − w'|` on `Ω_i`.  The `C¹` Approximation Theorem
(Ch. 2, 1.5) gives `C¹` maps `G_{j,k}` that agree to first order with the Lipschitz
parametrizations `F_j` off sets of measure `< 1/(k+1)`; the area formula makes the image of the
critical set of `F_j` null; near points where `DG_{j,k}` is injective, `G_{j,k}` is a chart on a
small basic open set. -/
theorem Submission.slicing_im_coarea_chart_cover : ∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 := by
  intro P n M hM
  classical
  -- Step 1: `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and `F_j` `Λ_j`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hMsub⟩ := hM
  choose Λ hΛ using hF
  -- Step 2: the `C¹` Approximation Theorem for `F_j` with `ε = (k+1)⁻¹`: a closed `A_{j,k}` with
  -- `Lⁿ(ℝⁿ ∖ A_{j,k}) < (k+1)⁻¹` and a `C¹` map `G_{j,k}` such that `F_j = G_{j,k}` and
  -- `DF_j = DG_{j,k}` on `A_{j,k}`.
  have hε : ∀ k : ℕ, (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ := fun k => ENNReal.inv_pos.2 (by simp)
  choose A G hAc hAm hG hAG using
    fun (j k : ℕ) => Submission.lpf_c1_approximation_eucl n P (F j) (Λ j) (hΛ j) _ (hε k)
  -- Step 4 (Lindelöf): a countable basis `{e p}` of the topology of `ℝⁿ`.
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Eucl n)
  have hbne : b.Nonempty := by
    obtain ⟨s, hs, -, -⟩ := hb.mem_nhds_iff.1 (univ_mem : (univ : Set (Eucl n)) ∈ 𝓝 0)
    exact ⟨s, hs⟩
  obtain ⟨e, rfl⟩ := hbc.exists_eq_range hbne
  -- `s` is a chart domain for `G_{j,k}` if `G_{j,k}` is Lipschitz and antilipschitz on `s`;
  -- `Ω'_{j,k,p}` is the basic set `e p` if it is a chart domain for `G_{j,k}`, and `∅` otherwise.
  let good : ℕ → ℕ → Set (Eucl n) → Prop := fun j k s =>
    (∃ K : ℝ≥0, LipschitzOnWith K (G j k) s) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ w ∈ s, ∀ w' ∈ s, c * ‖w - w'‖ ≤ ‖G j k w - G j k w'‖
  let Ω' : ℕ → ℕ → ℕ → Set (Eucl n) := fun j k p => if good j k (e p) then e p else ∅
  have hΩ'pos : ∀ j k p, good j k (e p) → Ω' j k p = e p := fun j k p h => by
    simp only [Ω', h, ↓reduceIte]
  have hΩ'neg : ∀ j k p, ¬ good j k (e p) → Ω' j k p = ∅ := fun j k p h => by
    simp only [Ω', h, ↓reduceIte]
  have hΩ'open : ∀ j k p, IsOpen (Ω' j k p) := by
    intro j k p
    by_cases h : good j k (e p)
    · rw [hΩ'pos j k p h]; exact hb.isOpen (mem_range_self p)
    · rw [hΩ'neg j k p h]; exact isOpen_empty
  -- The empty set is a chart domain vacuously (`K = 0`, `c = 1`).
  have hΩ'good : ∀ j k p, good j k (Ω' j k p) := by
    intro j k p
    by_cases h : good j k (e p)
    · rw [hΩ'pos j k p h]; exact h
    · rw [hΩ'neg j k p h]
      exact ⟨⟨0, fun x hx => absurd hx (notMem_empty x)⟩, 1, one_pos,
        fun w hw => absurd hw (notMem_empty w)⟩
  -- If `DG_{j,k}(x)` is injective, `G_{j,k}` is antilipschitz on a ball `B_r(x)` (inverse function
  -- estimate) and Lipschitz on a neighbourhood `t` of `x` (it is `C¹`); a basic set
  -- `x ∈ e p ⊆ B_r(x) ∩ t` is then a chart domain, so `x ∈ Ω'_{j,k,p}`.
  have hcover : ∀ j k x, Function.Injective (fderiv ℝ (G j k) x) → ∃ p, x ∈ Ω' j k p := by
    intro j k x hinj
    obtain ⟨r, hr, c, hc, hanti⟩ :=
      Submission.lpf_c1_local_antilipschitz n P (G j k) x (hG j k) hinj
    obtain ⟨K, t, ht, hLip⟩ := ((hG j k).contDiffAt (x := x)).exists_lipschitzOnWith
    have hnhds : ball x r ∩ t ∈ 𝓝 x := inter_mem (ball_mem_nhds x hr) ht
    obtain ⟨s, hs, hxs, hsub⟩ := hb.mem_nhds_iff.1 hnhds
    obtain ⟨p, rfl⟩ := hs
    have hg : good j k (e p) := ⟨⟨K, hLip.mono (hsub.trans inter_subset_right)⟩, c, hc,
      fun w hw w' hw' => hanti w (hsub hw).1 w' (hsub hw').1⟩
    exact ⟨p, by rw [hΩ'pos j k p hg]; exact hxs⟩
  -- Step 5: enumerate `(j, k, p) ∈ ℕ³` by `i ↦ ((unpair i).1, unpair (unpair i).2)` and set
  -- `Φ_i = G_{j,k}`, `Ω_i = Ω'_{j,k,p}`.
  let Φ : ℕ → Eucl n → Eucl P := fun i => G (Nat.unpair i).1 (Nat.unpair (Nat.unpair i).2).1
  let Ω : ℕ → Set (Eucl n) := fun i =>
    Ω' (Nat.unpair i).1 (Nat.unpair (Nat.unpair i).2).1 (Nat.unpair (Nat.unpair i).2).2
  refine ⟨Φ, Ω, fun i => hΩ'open _ _ _, fun i => hG _ _, fun i => (hΩ'good _ _ _).1,
    fun i => (hΩ'good _ _ _).2, ?_⟩
  -- Step 6: `M ∖ ⋃_i Φ_i(Ω_i) ⊆ M₀ ∪ ⋃_j (F_j(N_j) ∪ F_j(C_j))`, where `N_j = ℝⁿ ∖ ⋃_k A_{j,k}`
  -- and `C_j` is the critical set of `F_j`.
  let N : ℕ → Set (Eucl n) := fun j => (⋃ k, A j k)ᶜ
  let C : ℕ → Set (Eucl n) := fun j =>
    {x | DifferentiableAt ℝ (F j) x ∧ ¬ Function.Injective (fderiv ℝ (F j) x)}
  have hsub : M \ ⋃ i, Φ i '' Ω i ⊆ M₀ ∪ ⋃ j, (F j '' N j ∪ F j '' C j) := by
    rintro y ⟨hyM, hyU⟩
    rcases hMsub hyM with hy0 | hy
    · exact Or.inl hy0
    right
    obtain ⟨j, x, rfl⟩ := mem_iUnion.1 hy
    refine mem_iUnion.2 ⟨j, ?_⟩
    by_cases hxN : x ∈ N j
    · exact Or.inl ⟨x, hxN, rfl⟩
    right
    -- `x ∈ A_{j,k}` for some `k`, so `F_j` is differentiable at `x` with `DF_j(x) = DG_{j,k}(x)`;
    -- if this were injective, `F_j(x) = G_{j,k}(x)` would lie in some `Φ_i(Ω_i)`.
    have hxA : x ∈ ⋃ k, A j k := not_not.1 hxN
    obtain ⟨k, hxk⟩ := mem_iUnion.1 hxA
    obtain ⟨hval, hder⟩ := hAG j k x hxk
    refine ⟨x, ⟨hder.differentiableAt, ?_⟩, rfl⟩
    rw [hder.fderiv]
    intro hinj
    obtain ⟨p, hp⟩ := hcover j k x hinj
    apply hyU
    refine mem_iUnion.2 ⟨Nat.pair j (Nat.pair k p), x, ?_, ?_⟩
    · simp only [Ω, Nat.unpair_pair]; exact hp
    · simp only [Φ, Nat.unpair_pair]; exact hval.symm
  apply measure_mono_null hsub
  refine measure_union_null hM₀ (measure_iUnion_null fun j => measure_union_null ?_ ?_)
  · -- Step 3(a): `Lⁿ(N_j) ≤ Lⁿ(ℝⁿ ∖ A_{j,k}) < (k+1)⁻¹` for every `k`, so `Lⁿ(N_j) = 0`, and
    -- `Hⁿ(F_j(N_j)) ≤ Λ_jⁿ Hⁿ(N_j) = Λ_jⁿ Lⁿ(N_j) = 0`.
    have hvol : (volume : Measure (Eucl n)) (N j) = 0 := by
      by_contra hne
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hne
      have h1 : (volume : Measure (Eucl n)) (N j) ≤ volume (A j k)ᶜ :=
        measure_mono (compl_subset_compl.2 (subset_iUnion (A j) k))
      have h2 : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      exact absurd (lt_of_le_of_lt h1 ((hAm j k).trans_le h2)) (not_lt.2 hk.le)
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      ((hΛ j).lipschitzOnWith (s := N j))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvol, mul_zero] at h
    exact nonpos_iff_eq_zero.1 h
  · -- Step 3(b): the image of the critical set is `Hⁿ`-null (area formula).
    have h := Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero (F j)
    rwa [finrank_euclideanSpace_fin] at h
/-- Derivative lower bound (step 1 of the C¹ chart approximate tangent argument for Simon Ch. 6,
3.9): if `c ‖v - v'‖ ≤ ‖Φ v - Φ v'‖` on an open `Ω ∋ w` and `Φ` is differentiable at `w`, then
`c ‖s‖ ≤ ‖DΦ(w) s‖` for every `s` (no sign condition on `c`).  Apply the bound to `v = w + t • s`,
`v' = w`, divide by `t > 0` and let `t → 0⁺`. -/
theorem Submission.lpf_wtc_cat_fderiv_lower_bound :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (c : ℝ) (w : Eucl n), IsOpen Ω → w ∈ Ω → DifferentiableAt ℝ Φ w → (∀ v ∈ Ω, ∀ v' ∈ Ω, c * ‖v - v'‖ ≤ ‖Φ v - Φ v'‖) → ∀ s : Eucl n, c * ‖s‖ ≤ ‖fderiv ℝ Φ w s‖ := by
  intro Q n Φ Ω c w hΩ hw hdiff hanti s
  -- `γ t = Φ (w + t • s)` has derivative `DΦ(w) s` at `0`, so its right slopes converge to it.
  have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
  have hγ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 := by
    have h0 : w + (0 : ℝ) • s = w := by simp
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
  have hnorm : Tendsto (fun t : ℝ => ‖t⁻¹ • (Φ (w + (0 + t) • s) - Φ (w + (0 : ℝ) • s))‖)
      (𝓝[>] 0) (𝓝 ‖fderiv ℝ Φ w s‖) := hγ.tendsto_slope_zero_right.norm
  -- The segment `w + t • s` stays in the open set `Ω` for small `t`.
  have hcont : Continuous (fun t : ℝ => w + t • s) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), w + t • s ∈ Ω := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hw
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      c * ‖s‖ ≤ ‖t⁻¹ • (Φ (w + (0 + t) • s) - Φ (w + (0 : ℝ) • s))‖ := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with t ht htpos
    have htpos : (0 : ℝ) < t := htpos
    have h1 := hanti (w + t • s) ht w hw
    simp only [zero_add, zero_smul, add_zero]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), le_inv_mul_iff₀ htpos]
    linarith [h1]
  exact ge_of_tendsto hnorm hev
/-- Rescaled chart integrals converge (Simon Ch. 3, approximate tangent space of a `C¹` chart
image): for `Φ` continuous, differentiable at `w ∈ Ω` and antilipschitz on the open set `Ω`,
`J` continuous and `φ ∈ C_c`, `(rⁿ)⁻¹ ∫_Ω J(v) φ(r⁻¹(Φ v − Φ w)) dv → ∫ J(w) φ(DΦ(w) s) ds`
as `r → 0⁺`.  Substituting `v = w + r s` (Haar scaling and translation invariance) turns the
left side into `∫ F_r`; for `0 < r ≤ 1` the antilipschitz bound confines the support of `F_r`
to `‖s‖ ≤ R / c`, so `F_r` is dominated by a constant on a ball, and `F_r(s) → J(w) φ(DΦ(w) s)`
pointwise by differentiability at `w`; dominated convergence concludes. -/
theorem Submission.lpf_wtc_cat_rescaled_integral_tendsto :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (J : Eucl n → ℝ) (φ : Eucl Q → ℝ)
      (w : Eucl n), IsOpen Ω → w ∈ Ω → Continuous Φ → DifferentiableAt ℝ Φ w →
      (∃ c : ℝ, 0 < c ∧ ∀ v ∈ Ω, ∀ v' ∈ Ω, c * ‖v - v'‖ ≤ ‖Φ v - Φ v'‖) → Continuous J →
      Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ v in Ω, J v * φ (r⁻¹ • (Φ v - Φ w))) (𝓝[>] 0)
        (𝓝 (∫ s, J w * φ (fderiv ℝ Φ w s))) := by
  intro Q n Φ Ω J φ w hΩ hw hΦc hdiff hanti hJ hφ hφc
  obtain ⟨c, hc, hcΩ⟩ := hanti
  -- Constants: `tsupport φ ⊆ B̄_R(0)`, `|φ| ≤ A`, `|J| ≤ B` on `B̄_{R/c}(w)`.
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ tsupport φ ⊆ closedBall (0 : Eucl Q) R :=
    hφc.isCompact.isBounded.subset_closedBall_lt 0 0
  obtain ⟨A, hA⟩ : ∃ A, ∀ x, ‖φ x‖ ≤ A := hφ.bounded_above_of_compact_support hφc
  obtain ⟨B, hB⟩ : ∃ B, ∀ z ∈ closedBall w (R / c), ‖J z‖ ≤ B :=
    (isCompact_closedBall w (R / c)).exists_bound_of_continuousOn hJ.continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w (mem_closedBall_self (div_pos hR0 hc).le))
  set F : ℝ → Eucl n → ℝ := fun r s =>
    Ω.indicator (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) (w + r • s) with hF
  -- Change of variables `v = w + r • s`.
  have hcov : ∀ r : ℝ, 0 < r →
      ∫ s, F r s = (r ^ n)⁻¹ * ∫ v in Ω, J v * φ (r⁻¹ • (Φ v - Φ w)) := by
    intro r hr
    rw [← integral_indicator hΩ.measurableSet]
    have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure (Eucl n))
      (fun x => Ω.indicator (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) (w + x)) r (hR := hr.le)
    rw [integral_add_left_eq_self, finrank_euclideanSpace_fin, smul_eq_mul] at h1
    exact h1
  have hmeas : ∀ r : ℝ, AEStronglyMeasurable (F r) volume := by
    intro r
    have hk : Continuous (fun v => J v * φ (r⁻¹ • (Φ v - Φ w))) := by
      have h1 : Continuous (fun v => r⁻¹ • (Φ v - Φ w)) :=
        (hΦc.sub continuous_const).const_smul r⁻¹
      exact hJ.mul (hφ.comp h1)
    have hlin : Measurable (fun s : Eucl n => w + r • s) :=
      (continuous_const.add (continuous_id.const_smul r)).measurable
    exact ((hk.measurable.indicator hΩ.measurableSet).comp hlin).aestronglyMeasurable
  -- Domination for `0 < r ≤ 1` by `B * A` on `B̄_{R/c}(0)`.
  set bound : Eucl n → ℝ := (closedBall (0 : Eucl n) (R / c)).indicator (fun _ => B * A)
    with hbound
  have hdom : ∀ r : ℝ, r ∈ Ioc (0 : ℝ) 1 → ∀ s, ‖F r s‖ ≤ bound s := by
    rintro r ⟨hr0, hr1⟩ s
    by_cases hz : F r s = 0
    · rw [hz, norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg hB0 hA0) s
    · have hmemΩ : w + r • s ∈ Ω := by
        by_contra hnot
        exact hz (by simp only [hF, indicator_of_notMem hnot])
      have hFeq : F r s = J (w + r • s) * φ (r⁻¹ • (Φ (w + r • s) - Φ w)) := by
        simp only [hF, indicator_of_mem hmemΩ]
      have hφne : φ (r⁻¹ • (Φ (w + r • s) - Φ w)) ≠ 0 := by
        intro h0; apply hz; rw [hFeq, h0, mul_zero]
      have hinR : ‖r⁻¹ • (Φ (w + r • s) - Φ w)‖ ≤ R := by
        have := hR (subset_tsupport φ hφne)
        simpa [mem_closedBall, dist_zero_right] using this
      have hΦR : ‖Φ (w + r • s) - Φ w‖ ≤ r * R := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le), inv_mul_le_iff₀ hr0] at hinR
        exact hinR
      have hant := hcΩ (w + r • s) hmemΩ w hw
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le] at hant
      have hs : ‖s‖ ≤ R / c := by
        rw [le_div_iff₀ hc]
        have : r * (c * ‖s‖) ≤ r * R := by nlinarith
        nlinarith
      have hsball : s ∈ closedBall (0 : Eucl n) (R / c) := by
        simpa [mem_closedBall, dist_zero_right] using hs
      have hwball : w + r • s ∈ closedBall w (R / c) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg hr0.le]
        calc r * ‖s‖ ≤ 1 * ‖s‖ := by gcongr
          _ = ‖s‖ := one_mul _
          _ ≤ R / c := hs
      rw [hbound, indicator_of_mem hsball, hFeq, norm_mul]
      exact mul_le_mul (hB _ hwball) (hA _) (norm_nonneg _) hB0
  have hint : Integrable bound volume := by
    rw [hbound]
    exact (integrableOn_const (measure_closedBall_lt_top (x := (0 : Eucl n))
      (r := R / c)).ne).integrable_indicator measurableSet_closedBall
  -- Pointwise limit from differentiability of `Φ` at `w`.
  have hlim : ∀ s, Tendsto (fun r => F r s) (𝓝[>] 0) (𝓝 (J w * φ (fderiv ℝ Φ w s))) := by
    intro s
    have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
    have hγ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 := by
      have h0 : w + (0 : ℝ) • s = w := by simp
      exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline h0.symm
    have hslope : Tendsto (fun t : ℝ => t⁻¹ • (Φ (w + t • s) - Φ w)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ Φ w s)) := by
      simpa using hγ.tendsto_slope_zero_right
    have hcont : Continuous (fun t : ℝ => w + t • s) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hto : Tendsto (fun t : ℝ => w + t • s) (𝓝[>] 0) (𝓝 w) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), w + t • s ∈ Ω := hto (hΩ.mem_nhds hw)
    have hJlim : Tendsto (fun t : ℝ => J (w + t • s)) (𝓝[>] 0) (𝓝 (J w)) :=
      (hJ.tendsto w).comp hto
    have hφlim : Tendsto (fun t : ℝ => φ (t⁻¹ • (Φ (w + t • s) - Φ w))) (𝓝[>] 0)
        (𝓝 (φ (fderiv ℝ Φ w s))) := (hφ.tendsto _).comp hslope
    refine (hJlim.mul hφlim).congr' ?_
    filter_upwards [hmem] with t ht
    simp only [hF, indicator_of_mem ht]
  -- Dominated convergence along `𝓝[>] 0`, then undo the change of variables.
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Eucl n))) (l := 𝓝[>] (0 : ℝ)) (F := F)
    (f := fun s => J w * φ (fderiv ℝ Φ w s)) bound
    (Eventually.of_forall hmeas)
    (by filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with r hr
        exact Eventually.of_forall (hdom r hr))
    hint (Eventually.of_forall hlim)
  refine hdct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hcov r hr
/-- Continuity of the Jacobian `JΦ = √det((DΦ)* DΦ)` (Simon Ch. 2, (3.3)) of a `C¹` map
`Φ : ℝⁿ → ℝ^Q`, written as the Gram determinant `det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)` of the columns of
`DΦ(v)`.  `v ↦ DΦ(v)` is continuous since `Φ` is `C¹`, so are the columns `DΦ(v)eᵢ`, the Gram
entries, the Gram matrix (entrywise), its determinant (a polynomial in the entries) and the
square root. -/
theorem Submission.lpf_wtc_cat_gram_jacobian_continuous :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q), ContDiff ℝ 1 Φ → Continuous (fun v : Eucl n => Real.sqrt (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1)) (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det) := by
  intro Q n Φ hΦ
  have hD : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (hD.clm_apply continuous_const).inner (hD.clm_apply continuous_const)
/-- Splitting of the blown-up weighted integral (Simon Ch. 3, Remark 1.8(1)): for `C ⊆ M` and all
small `t > 0`, `∫_M φ(η_t) θ = θ(y) ∫_C φ(η_t) + ∫_C φ(η_t) (θ − θ(y)) + ∫_{M∖C} φ(η_t) θ`. -/
theorem Submission.lpf_wtc_wtt_blowup_integral_split : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ x in M, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)) = θ y * ∫ x in C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q)) + ∫ x in C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y) ∂(μHE[n] : Measure (Eucl Q)) + ∫ x in M \ C, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n M C θ y φ hM hC hCM ⟨r, hr, hCr, hθr⟩
  -- Step 1: `tsupport φ ⊆ B_R(0)` and `|φ| ≤ A`.
  obtain ⟨R, -, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- Step 2: `t R < r` for all sufficiently small `t > 0`; fix such a `t`.
  have hlim : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.mul_const R
  filter_upwards [hlim.eventually (eventually_lt_nhds hr), self_mem_nhdsWithin] with t htR ht
  -- Step 3: `F = φ ∘ η_t` is continuous, bounded by `A`, and vanishes off `B̄_r(y)`.
  have hcont : Continuous fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) :=
    (map_continuous φ).comp ((continuous_id.sub continuous_const).const_smul t⁻¹)
  have hzero : ∀ x ∉ closedBall y r, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro x hx
    by_contra hne
    have hball := hR (subset_tsupport _ (Function.mem_support.2 hne))
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg (le_of_lt ht), inv_mul_lt_iff₀ ht] at hball
    exact hx (mem_closedBall.2 (by rw [dist_eq_norm]; linarith))
  suffices key : ∀ F : Eucl Q → ℝ, Continuous F → (∀ x, ‖F x‖ ≤ A) →
      (∀ x ∉ closedBall y r, F x = 0) →
      ∫ x in M, F x * θ x ∂(μHE[n] : Measure (Eucl Q)) =
        θ y * ∫ x in C, F x ∂(μHE[n] : Measure (Eucl Q)) +
          ∫ x in C, F x * (θ x - θ y) ∂(μHE[n] : Measure (Eucl Q)) +
            ∫ x in M \ C, F x * θ x ∂(μHE[n] : Measure (Eucl Q)) from
    key _ hcont (fun x => hA _) hzero
  intro F hFc hFA hF0
  generalize (μHE[n] : Measure (Eucl Q)) = μ at hM hC hCr hθr ⊢
  -- Step 4: `F θ` is integrable on `M ∩ B̄_r(y)`, and vanishes on the rest of `M`.
  have hFθM : IntegrableOn (fun x => F x * θ x) M μ := by
    refine IntegrableOn.of_ae_sdiff_eq_zero
      (hθr.bdd_mul hFc.aestronglyMeasurable (Eventually.of_forall hFA)) hM
      (Eventually.of_forall fun x hx => ?_)
    rw [hF0 x fun h => hx.2 ⟨hx.1, h⟩, zero_mul]
  -- Step 5: `F` is integrable on `C ∩ B̄_r(y)` (finite measure), and vanishes on the rest of `C`.
  have hFC : IntegrableOn F C μ :=
    (Measure.integrableOn_of_bounded hCr.ne hFc.aestronglyMeasurable
      (Eventually.of_forall hFA)).of_ae_sdiff_eq_zero hC
        (Eventually.of_forall fun x hx => hF0 x fun h => hx.2 ⟨hx.1, h⟩)
  -- Step 6: derived integrabilities on `C` and `M \ C`.
  have hFθC : IntegrableOn (fun x => F x * θ x) C μ := hFθM.mono_set hCM
  have hFθMC : IntegrableOn (fun x => F x * θ x) (M \ C) μ := hFθM.mono_set sdiff_subset
  have hθF : IntegrableOn (fun x => θ y * F x) C μ := hFC.const_mul _
  have hFd : IntegrableOn (fun x => F x * (θ x - θ y)) C μ :=
    (hFθC.sub hθF).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  -- Step 7: split `M = C ∪ (M \ C)`.
  have h7 : ∫ x in M, F x * θ x ∂μ = ∫ x in C, F x * θ x ∂μ + ∫ x in M \ C, F x * θ x ∂μ := by
    conv_lhs => rw [← union_sdiff_cancel hCM]
    exact setIntegral_union₀ disjoint_sdiff_right.aedisjoint (hM.diff hC) hFθC hFθMC
  -- Step 8: split the weight on `C`.
  have h8 : ∫ x in C, F x * θ x ∂μ =
      θ y * ∫ x in C, F x ∂μ + ∫ x in C, F x * (θ x - θ y) ∂μ := by
    rw [← integral_const_mul, ← integral_add hθF hFd]
    congr 1
    funext x
    ring
  -- Step 9: combine.
  rw [h7, h8]

/-- If `C` is `Hⁿ`-null-measurable, `θ` is continuous at `y` within `C` and
`Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for small `ρ > 0`, then
`t⁻ⁿ ∫_C φ(η_{y,t}(x)) (θ(x) - θ(y)) dHⁿ(x) → 0` as `t → 0⁺`.  With `tsupport φ ⊆ B_R(0)` and
`|φ| ≤ A`, the integrand vanishes off `B̄_{tR}(y)` and is at most `A ε₁` on `C ∩ B̄_{tR}(y)` once
`tR < δ(ε₁)`, so the integral is at most `A ε₁ K (tR)ⁿ`. -/
theorem Submission.lpf_wtc_wtt_continuity_error_vanishes :
    ∀ (Q n : ℕ) (C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q)
      (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ),
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → ContinuousWithinAt θ C y →
      (∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n)) →
      Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in C,
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y)
          ∂(μHE[n] : Measure (Eucl Q))) (𝓝[>] 0) (𝓝 0) := by
  intro Q n C θ y φ hC hθ hK
  obtain ⟨K, hK⟩ := hK
  -- `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A`.
  obtain ⟨R, hR, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- For `t > 0`, `φ(η_t(x)) = 0` off `B̄_{tR}(y)`.
  have hloc : ∀ t : ℝ, 0 < t → ∀ x, x ∉ closedBall y (t * R) →
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro t ht x hx
    by_contra hne
    have hmem := hRφ (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos ht, inv_mul_lt_iff₀ ht] at hmem
    exact hx (mem_closedBall.2 ((dist_eq_norm x y).trans_le hmem.le))
  -- `tR → 0` within `(0, ∞)`, so the density bound holds at `ρ = tR` for small `t > 0`.
  have hRt : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const R
  have hRt' : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hRt, eventually_nhdsWithin_of_forall fun t ht => mul_pos ht hR⟩
  have hKt := hRt'.eventually hK
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := A * K * R ^ n with hc
  have hc0 : 0 ≤ c := by positivity
  set ε₁ : ℝ := ε / (2 * (c + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ, hθδ⟩ := Metric.continuousWithinAt_iff.1 hθ ε₁ hε₁0
  filter_upwards [hKt, hRt.eventually (Iio_mem_nhds hδ), self_mem_nhdsWithin] with t htK htδ ht
  have ht0 : 0 < t := ht
  set μ : Measure (Eucl Q) := (μHE[n] : Measure (Eucl Q))
  set f : Eucl Q → ℝ := fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * (θ x - θ y)
    with hf
  set B : Set (Eucl Q) := closedBall y (t * R)
  -- `μ⌞C`-a.e., `|f| ≤ A ε₁ 1_B`.
  have hpt : ∀ᵐ x ∂μ.restrict C, ENNReal.ofReal ‖f x‖ ≤
      B.indicator (fun _ => ENNReal.ofReal (A * ε₁)) x := by
    filter_upwards [ae_restrict_mem₀ hC] with x hxC
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB]
      refine ENNReal.ofReal_le_ofReal ?_
      have hxy : dist x y < δ := (mem_closedBall.1 hxB).trans_lt htδ
      have h1 : ‖θ x - θ y‖ ≤ ε₁ := by
        rw [← dist_eq_norm]; exact (hθδ hxC hxy).le
      simp only [hf, norm_mul]
      exact mul_le_mul (hA _) h1 (norm_nonneg _) hA0
    · rw [indicator_of_notMem hxB]
      simp [hf, hloc t ht0 x hxB]
  -- `∫⁻_C |f| ≤ A ε₁ μ(C ∩ B) ≤ A ε₁ K (tR)ⁿ < ∞`.
  have hlin : ∫⁻ x in C, ENNReal.ofReal ‖f x‖ ∂μ ≤
      ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) := by
    calc ∫⁻ x in C, ENNReal.ofReal ‖f x‖ ∂μ
        ≤ ∫⁻ x in C, B.indicator (fun _ => ENNReal.ofReal (A * ε₁)) x ∂μ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (A * ε₁) * μ (C ∩ B) := by
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, inter_comm]
      _ ≤ ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) := by
        gcongr
  have hfin : ENNReal.ofReal (A * ε₁) * (K * ENNReal.ofReal ((t * R) ^ n)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      ENNReal.ofReal_ne_top)
  -- `|∫_C f| ≤ A ε₁ K (tR)ⁿ`.
  have hnorm : ‖∫ x in C, f x ∂μ‖ ≤ A * ε₁ * (K * (t * R) ^ n) := by
    refine (norm_integral_le_lintegral_norm f).trans ?_
    refine (ENNReal.toReal_mono hfin hlin).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal]
  -- Rescaling: `t⁻ⁿ |∫_C f| ≤ c ε₁ ≤ ε / 2 < ε`.
  rw [dist_zero_right, norm_mul, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos ht0]
  calc (t ^ n)⁻¹ * ‖∫ x in C, f x ∂μ‖
      ≤ (t ^ n)⁻¹ * (A * ε₁ * (K * (t * R) ^ n)) := by gcongr
    _ = c * ε₁ := by
      rw [hc, mul_pow]
      field_simp
    _ ≤ (c + 1) * ε₁ := by gcongr; linarith
    _ = ε / 2 := by
      rw [hε₁]
      field_simp
    _ < ε := by linarith

/-- Zero `θ`-weighted `n`-density of `D` at `y` kills the blow-up integrals (Simon Ch. 3,
Remark 1.8(1)): if `(∫⁻_{D ∩ B̄_ρ(y)} θ dHⁿ) / ρⁿ → 0` as `ρ ↓ 0`, then for every `φ ∈ C_c(ℝ^Q)`,
`(tⁿ)⁻¹ ∫_D φ(η_{y,t}(x)) θ(x) dHⁿ(x) → 0` as `t ↓ 0`.  No integrability of `θ` is assumed. -/
theorem Submission.lpf_wtc_wtt_remainder_vanishes : ∀ (Q n : ℕ) (D : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (φ : CompactlySupportedContinuousMap (Eucl Q) ℝ), NullMeasurableSet D (μHE[n] : Measure (Eucl Q)) → (∀ x ∈ D, 0 ≤ θ x) → Tendsto (fun ρ : ℝ => (∫⁻ x in D ∩ closedBall y ρ, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q))) (𝓝[>] 0) (𝓝 0) := by
  intro Q n D θ y φ hD hθ hlim
  set μ : Measure (Eucl Q) := μHE[n]
  -- Step 1: `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A` (so `A ≥ 0`).
  obtain ⟨R, hR, hRφ⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  obtain ⟨A, hA⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- Step 2: for `t > 0`, `φ (η_t x) = 0` whenever `x ∉ B̄_{tR}(y)`.
  have hloc : ∀ t : ℝ, 0 < t → ∀ x, x ∉ closedBall y (t * R) →
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
    intro t ht x hx
    by_contra hne
    have hmem := hRφ (subset_tsupport φ (Function.mem_support.2 hne))
    rw [mem_ball_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
      Real.norm_of_nonneg ht.le, inv_mul_lt_iff₀ ht] at hmem
    exact hx (mem_closedBall_iff_norm.2 hmem.le)
  -- Step 3: compose the density hypothesis with `t ↦ tR`, which tends to `0` within `(0, ∞)`.
  have hTR : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun t : ℝ => t * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos ht hR
  have hq := hlim.comp hTR
  -- (a) eventually `q (tR) < ∞`;
  have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal (θ x) ∂μ)
      / ENNReal.ofReal ((t * R) ^ n) < ⊤ :=
    hq.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  -- (b) `b t = A Rⁿ toReal (q (tR)) → 0`.
  have hb : Tendsto (fun t : ℝ => A * R ^ n * ((∫⁻ x in D ∩ closedBall y (t * R),
      ENNReal.ofReal (θ x) ∂μ) / ENNReal.ofReal ((t * R) ^ n)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hq).const_mul (A * R ^ n)
    rw [ENNReal.toReal_zero, mul_zero] at h0
    exact h0
  -- Step 4: squeeze; fix `t > 0` with `q (tR) < ∞`.
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [hfin, self_mem_nhdsWithin] with t hqt ht
  have ht' : (0 : ℝ) < t := ht
  have htR : 0 < t * R := mul_pos ht' hR
  set L := ∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal (θ x) ∂μ
  -- Step 5: `L (tR) < ∞`.
  have hLtop : L ≠ ⊤ := by
    intro hLt
    rw [hLt, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hqt
    exact lt_irrefl _ hqt
  -- Steps 6–7: `∫⁻_D ofReal |φ(η_t x) θ(x)| ≤ ofReal A · L (tR)`.
  have hlint : ∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖
      ∂μ ≤ ENNReal.ofReal A * L := by
    calc ∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖ ∂μ
        ≤ ∫⁻ x in D, (closedBall y (t * R)).indicator
            (fun x => ENNReal.ofReal A * ENNReal.ofReal (θ x)) x ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hD] with x hx
          by_cases hxB : x ∈ closedBall y (t * R)
          · simp only [indicator_of_mem hxB]
            rw [← ENNReal.ofReal_mul hA0, norm_mul, Real.norm_of_nonneg (hθ x hx)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hA _) (hθ x hx))
          · rw [hloc t ht' x hxB, zero_mul, norm_zero, ENNReal.ofReal_zero]
            exact zero_le
      _ = ∫⁻ x in D ∩ closedBall y (t * R), ENNReal.ofReal A * ENNReal.ofReal (θ x) ∂μ := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm (closedBall y (t * R)) D]
      _ = ENNReal.ofReal A * L := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 8: `|∫_D φ(η_t x) θ(x)| ≤ A · toReal (L (tR))`, with no integrability needed.
  have hint : ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
      ≤ A * L.toReal := by
    calc ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
        ≤ (∫⁻ x in D, ENNReal.ofReal ‖φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x‖
            ∂μ).toReal := norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal A * L).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop) hlint
      _ = A * L.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0]
  -- Step 9: rescaling, `(tⁿ)⁻¹ A toReal (L (tR)) = A Rⁿ toReal (q (tR))`.
  have htn : 0 < t ^ n := pow_pos ht' n
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [norm_mul, norm_inv, Real.norm_of_nonneg htn.le, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (pow_pos htR n).le, mul_pow]
  calc (t ^ n)⁻¹ * ‖∫ x in D, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂μ‖
      ≤ (t ^ n)⁻¹ * (A * L.toReal) := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 htn.le)
    _ = A * R ^ n * (L.toReal / (t ^ n * R ^ n)) := by
      field_simp [htn.ne', hRn.ne']

/-- Change of variables for `Hⁿ`-integrals over blow-ups: `η = η_{y,r}`, `η(x) = r⁻¹(x − y)`,
pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so `∫_{η(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η dHⁿ` for every set
`S` and every `g` (both sides are Bochner set integrals). -/
theorem Submission.lpf_wtc_blowup_setIntegral_image :
    ∀ (Q n : ℕ) (y : Eucl Q) (r : ℝ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ), 0 < r →
      ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, g z ∂(μHE[n] : Measure (Eucl Q)) =
        (r ^ n)⁻¹ * ∫ x in S, g (Poincare.SimonGMT.Chapter03.blowUpMap y r x)
          ∂(μHE[n] : Measure (Eucl Q)) := by
  intro Q n y r S g hr
  -- `η = blowUpMap y r`, `η x = r⁻¹ • (x - y)`, is a homeomorphism of `ℝ^Q`.
  let e : Eucl Q ≃ₜ Eucl Q :=
    (Homeomorph.addRight (-y)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl Q → Eucl Q) = Poincare.SimonGMT.Chapter03.blowUpMap y r := by
    funext x
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = y + r • B`.
  have hmp : MeasurePreserving (Poincare.SimonGMT.Chapter03.blowUpMap y r)
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl Q))) μHE[n] := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap y r ⁻¹' B =
        (fun z => y + z) '' ((fun z => r • z) '' B) := by
      ext x
      simp only [mem_preimage, mem_image, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · intro hx
        exact ⟨r • r⁻¹ • (x - y), ⟨r⁻¹ • (x - y), hx, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left y), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
/-- The image `Φ(Ω)` of an open `Ω ⊆ ℝⁿ` under a `C¹` map `Φ : ℝⁿ → ℝ^Q` with
`c |w - w'| ≤ |Φ w - Φ w'|` on `Ω` is Borel, and `Hⁿ(Φ(Ω) ∩ K) < ∞` for every compact `K`. -/
theorem Submission.lpf_wtc_chart_image_measurable_locally_finite :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen Ω → ContDiff ℝ 1 Φ →
      (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      MeasurableSet (Φ '' Ω) ∧ ∀ K : Set (Eucl Q), IsCompact K →
        (μHE[n] : Measure (Eucl Q)) (Φ '' Ω ∩ K) < ∞ := by
  intro Q n Φ Ω hΩ hΦ ⟨c, hc, hcΦ⟩
  refine ⟨?_, fun K hK => ?_⟩
  · -- `Φ` is injective on `Ω`, so `Φ '' Ω` is Borel by Lusin–Souslin.
    refine hΩ.measurableSet.image_of_continuousOn_injOn hΦ.continuous.continuousOn
      fun w hw w' hw' h => ?_
    have h0 := hcΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h0
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h0 hc))
  · rcases (Φ '' Ω ∩ K).eq_empty_or_nonempty with h | ⟨_, ⟨w₀, hw₀, rfl⟩, hw₀K⟩
    · rw [h, measure_empty]
      exact ENNReal.zero_lt_top
    -- `Ω ∩ Φ⁻¹(K)` lies in the closed ball `B` of radius `D / c` about `w₀`, `D ≥ diam K`.
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hK.isBounded
    have hsub : Φ '' Ω ∩ K ⊆ Φ '' closedBall w₀ (D / c) := by
      rintro _ ⟨⟨v, hv, rfl⟩, hvK⟩
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hc, mul_comm]
      exact (hcΦ v hv w₀ hw₀).trans ((dist_eq_norm (Φ v) (Φ w₀)).symm.trans_le (hD hvK hw₀K))
    -- `DΦ` is bounded on the compact convex ball `B`, so `Φ` is Lipschitz on `B`.
    obtain ⟨C, hC⟩ := (isCompact_closedBall w₀ (D / c)).exists_bound_of_continuousOn
      (hΦ.continuous_fderiv one_ne_zero).continuousOn
    have hLip : LipschitzOnWith (Real.toNNReal C) Φ (closedBall w₀ (D / c)) :=
      (convex_closedBall w₀ (D / c)).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => hΦ.differentiable one_ne_zero x)
        (fun x hx => by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact (hC x hx).trans (Real.le_coe_toNNReal C))
    -- `μHE[n] = κₙ • μH[n]` and `μH[n](Φ(B)) ≤ Λⁿ μH[n](B) < ∞` (`μH[n]` is Haar on `ℝⁿ`).
    refine (measure_mono hsub).trans_lt ?_
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((hLip.hausdorffMeasure_image_le n.cast_nonneg).trans_lt ?_)
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg n.cast_nonneg ENNReal.coe_ne_top)
      (isCompact_closedBall w₀ (D / c)).measure_lt_top
/-- For a `C¹` map `Φ : ℝⁿ → ℝ^Q` with `c |w - w'| ≤ |Φ w - Φ w'|` on an open `Ω ⊆ ℝⁿ` and a
compact `K ⊆ ℝ^Q`, `Ω ∩ Φ⁻¹(K)` lies in a bounded open `s ⊆ Ω` on which `Φ` is Lipschitz. -/
theorem Submission.lpf_wtc_caf_lipschitz_localization :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (K : Set (Eucl Q)), IsOpen Ω →
      ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      IsCompact K → ∃ (s : Set (Eucl n)) (L : ℝ≥0), IsOpen s ∧ s ⊆ Ω ∧ Ω ∩ Φ ⁻¹' K ⊆ s ∧
        Bornology.IsBounded s ∧ LipschitzOnWith L Φ s := by
  intro Q n Φ Ω K hΩ hΦ ⟨c, hc, hcΦ⟩ hK
  rcases (Ω ∩ Φ ⁻¹' K).eq_empty_or_nonempty with h | ⟨w₀, hw₀, hw₀K⟩
  · exact ⟨∅, 0, isOpen_empty, empty_subset Ω, h.subset, Bornology.isBounded_empty,
      lipschitzOnWith_empty 0 Φ⟩
  -- `s = Ω ∩ B_ρ(w₀)` with `ρ = D / c + 1`, `D ≥ diam K`.
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hK.isBounded
  -- `DΦ` is bounded on the compact convex ball `B̄_ρ(w₀)`, so `Φ` is Lipschitz on it.
  obtain ⟨C, hC⟩ := (isCompact_closedBall w₀ (D / c + 1)).exists_bound_of_continuousOn
    (hΦ.continuous_fderiv one_ne_zero).continuousOn
  have hLip : LipschitzOnWith (Real.toNNReal C) Φ (closedBall w₀ (D / c + 1)) :=
    (convex_closedBall w₀ (D / c + 1)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hΦ.differentiable one_ne_zero x)
      (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact (hC x hx).trans (Real.le_coe_toNNReal C))
  refine ⟨Ω ∩ ball w₀ (D / c + 1), Real.toNNReal C, hΩ.inter isOpen_ball, inter_subset_left,
    fun v ⟨hv, hvK⟩ => ⟨hv, ?_⟩, isBounded_ball.subset inter_subset_right,
    hLip.mono (inter_subset_right.trans ball_subset_closedBall)⟩
  -- `c |v - w₀| ≤ |Φ v - Φ w₀| ≤ D`, so `|v - w₀| ≤ D / c < ρ`.
  rw [mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt ?_ (lt_add_one (D / c))
  rw [le_div_iff₀ hc, mul_comm]
  exact (hcΦ v hv w₀ hw₀).trans ((dist_eq_norm (Φ v) (Φ w₀)).symm.trans_le (hD hvK hw₀K))
/-- Signed area formula from the nonnegative one: if `∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s J · (g ∘ Φ) dLⁿ`
for every Borel `g ≥ 0`, then `∫_{Φ(Ω)} h dHⁿ = ∫_Ω J · (h ∘ Φ) dLⁿ` for every continuous
compactly supported `h` with `Ω ∩ Φ⁻¹(spt h) ⊆ s`. -/
theorem Submission.lpf_wtc_caf_signed_of_lintegral :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω s : Set (Eucl n)) (J : Eucl n → ℝ) (h : Eucl Q → ℝ),
      IsOpen Ω → IsOpen s → s ⊆ Ω → Bornology.IsBounded s → Continuous Φ → InjOn Φ Ω →
      Continuous J → (∀ v, 0 ≤ J v) → Continuous h → HasCompactSupport h →
      Ω ∩ Φ ⁻¹' tsupport h ⊆ s →
      (∀ g : Eucl Q → ℝ≥0∞, Measurable g →
        ∫⁻ y in Φ '' s, g y ∂(μHE[n] : Measure (Eucl Q)) =
          ∫⁻ v in s, ENNReal.ofReal (J v) * g (Φ v) ∂(volume : Measure (Eucl n))) →
      ∫ x in Φ '' Ω, h x ∂(μHE[n] : Measure (Eucl Q)) =
        ∫ v in Ω, J v * h (Φ v) ∂(volume : Measure (Eucl n)) := by
  intro Q n Φ Ω s J h hΩ hs hsΩ hsb hΦ hinj hJ hJ0 hh hhc hsupp H
  -- `h ∘ Φ` vanishes on `Ω \ s`.
  have hvan : ∀ v ∈ Ω \ s, h (Φ v) = 0 := fun v hv =>
    image_eq_zero_of_notMem_tsupport fun hK => hv.2 (hsupp ⟨hv.1, hK⟩)
  -- Bounds: `‖J‖ ≤ C` on `s`, `‖h‖ ≤ M`, and `Lⁿ(s) < ∞`.
  obtain ⟨C, hC⟩ := hsb.isCompact_closure.exists_bound_of_continuousOn hJ.continuousOn
  have hJC : ∀ v ∈ s, ‖J v‖ ≤ C := fun v hv => hC v (subset_closure hv)
  obtain ⟨M, hM⟩ := hh.bounded_above_of_compact_support hhc
  have hvol : volume s < ∞ := hsb.measure_lt_top
  -- `Hⁿ(Φ(s)) < ∞`: the identity with `g ≡ 1`.
  have hfin : (μHE[n] : Measure (Eucl Q)) (Φ '' s) < ∞ := by
    have h1 := H (fun _ => 1) measurable_const
    rw [setLIntegral_one] at h1
    rw [h1]
    calc ∫⁻ v in s, ENNReal.ofReal (J v) * 1 ∂volume
        ≤ ∫⁻ _ in s, ENNReal.ofReal C ∂volume :=
          setLIntegral_mono measurable_const fun v hv => by
            rw [mul_one]
            exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hJC v hv))
      _ = ENNReal.ofReal C * volume s := setLIntegral_const s _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol
  -- Integrability of `h` on `Φ(s)` and of `J · (h ∘ Φ)` on `s`.
  have hint₁ : IntegrableOn h (Φ '' s) (μHE[n] : Measure (Eucl Q)) :=
    Measure.integrableOn_of_bounded hfin.ne hh.aestronglyMeasurable (ae_of_all _ hM)
  have hint₂ : IntegrableOn (fun v => J v * h (Φ v)) s volume := by
    refine Measure.integrableOn_of_bounded (M := C * M) hvol.ne
      (hJ.mul (hh.comp hΦ)).aestronglyMeasurable
      (ae_restrict_of_forall_mem hs.measurableSet fun v hv => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg' (hJC v hv) (hM _) (norm_nonneg _)
      ((norm_nonneg _).trans (hJC v hv))
  -- The identity for `ofReal ∘ h` and `ofReal ∘ (-h)`, using `J ≥ 0`.
  have ePos : ∫⁻ y in Φ '' s, ENNReal.ofReal (h y) ∂(μHE[n] : Measure (Eucl Q)) =
      ∫⁻ v in s, ENNReal.ofReal (J v * h (Φ v)) ∂(volume : Measure (Eucl n)) := by
    rw [H (fun y => ENNReal.ofReal (h y)) (ENNReal.measurable_ofReal.comp hh.measurable)]
    exact lintegral_congr fun v => (ENNReal.ofReal_mul (hJ0 v)).symm
  have eNeg : ∫⁻ y in Φ '' s, ENNReal.ofReal (-h y) ∂(μHE[n] : Measure (Eucl Q)) =
      ∫⁻ v in s, ENNReal.ofReal (-(J v * h (Φ v))) ∂(volume : Measure (Eucl n)) := by
    rw [H (fun y => ENNReal.ofReal (-h y)) (ENNReal.measurable_ofReal.comp hh.measurable.neg)]
    exact lintegral_congr fun v => by rw [← mul_neg, ENNReal.ofReal_mul (hJ0 v)]
  -- The signed identity on `s`.
  have key : ∫ x in Φ '' s, h x ∂(μHE[n] : Measure (Eucl Q)) =
      ∫ v in s, J v * h (Φ v) ∂(volume : Measure (Eucl n)) := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint₁,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint₂, ePos, eNeg]
  -- The integrands vanish on `Ω \ s` and `Φ(Ω) \ Φ(s)`; `Φ(Ω)` is Borel by Lusin–Souslin.
  have eΩ : ∫ v in Ω, J v * h (Φ v) ∂(volume : Measure (Eucl n)) =
      ∫ v in s, J v * h (Φ v) ∂(volume : Measure (Eucl n)) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hsΩ fun v hv => by
      rw [hvan v hv, mul_zero]
  have eΦΩ : ∫ x in Φ '' Ω, h x ∂(μHE[n] : Measure (Eucl Q)) =
      ∫ x in Φ '' s, h x ∂(μHE[n] : Measure (Eucl Q)) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hΩ.measurableSet.image_of_continuousOn_injOn hΦ.continuousOn hinj) (image_mono hsΩ) ?_
    rintro _ ⟨⟨v, hv, rfl⟩, hvs⟩
    exact hvan v ⟨hv, fun hvs' => hvs (mem_image_of_mem Φ hvs')⟩
  rw [eΦΩ, eΩ, key]
/-- Injective area formula on a `C¹` antilipschitz chart (Simon Ch. 2, (3.1), (3.2), (3.5)):
if `Φ : ℝⁿ → ℝ^Q` is `C¹`, `Ω ⊆ ℝⁿ` is open and `c |w - w'| ≤ |Φ w - Φ w'|` on `Ω` for some
`c > 0`, then `∫_{Φ(Ω)} h dHⁿ = ∫_Ω JΦ(v) h(Φ(v)) dLⁿ(v)` for every `h ∈ C_c(ℝ^Q, ℝ)`, where
`JΦ(v) = √det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)`.

Proof.  `JΦ(v) = normDet(DΦ(v))` (`LinearMap.normDet_sq_eq_det_gram` for the standard basis), and
`JΦ` is continuous and nonnegative; `Φ` is injective on `Ω`.  Localize to a bounded open
`s ⊆ Ω` containing `Ω ∩ Φ⁻¹(spt h)` on which `Φ` is Lipschitz
(`lpf_wtc_caf_lipschitz_localization`).  As `Φ` is injective on `s`, the fibre sum of the
weighted area formula on `s` (`weighted_area_formula_lipschitzOn_fiberSum`, weight `g ∘ Φ`) is
the indicator of the Borel set `Φ(s)` applied to `g`, and the within Jacobian on the open `s` is
`JΦ`; this gives `∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s JΦ (g ∘ Φ) dLⁿ` for every Borel `g ≥ 0`.  The signed
identity on `Ω` then follows from `lpf_wtc_caf_signed_of_lintegral`. -/
theorem Submission.lpf_wtc_chart_area_formula : ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ h : Eucl Q → ℝ, Continuous h → HasCompactSupport h → ∫ x in Φ '' Ω, h x ∂(μHE[n] : Measure (Eucl Q)) = ∫ v in Ω, Real.sqrt (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1)) (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det * h (Φ v) := by
  intro Q n Φ Ω hΩ hΦ hanti h hh hsupp
  -- The Gram-determinant Jacobian `JΦ(v) = √det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)`.
  set J : Eucl n → ℝ := fun v => Real.sqrt (Matrix.of fun i j : Fin n =>
    inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1))
      (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det with hJ
  -- Step 1: `JΦ(v) = normDet(DΦ(v))`, since `normDet(A)² = det(⟨A eᵢ, A eⱼ⟩)` and `normDet ≥ 0`.
  have hJdet : ∀ v, J v = (fderiv ℝ Φ v).normDet := by
    intro v
    have hgram := LinearMap.normDet_sq_eq_det_gram (fderiv ℝ Φ v).toLinearMap
      (EuclideanSpace.basisFun (Fin n) ℝ)
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe] at hgram
    rw [hJ]
    change Real.sqrt (Matrix.gram ℝ fun i : Fin n =>
      fderiv ℝ Φ v (EuclideanSpace.single i 1)).det = _
    rw [← hgram]
    exact Real.sqrt_sq (LinearMap.normDet_nonneg _)
  -- `JΦ` is continuous (`DΦ` is continuous) and nonnegative.
  have hJcont : Continuous J := by
    have hD : Continuous fun v => fderiv ℝ Φ v := hΦ.continuous_fderiv one_ne_zero
    have hcol : ∀ i : Fin n, Continuous fun v => fderiv ℝ Φ v (EuclideanSpace.single i 1) :=
      fun i => hD.clm_apply continuous_const
    exact Real.continuous_sqrt.comp
      (continuous_matrix fun i j => (hcol i).inner (hcol j)).matrix_det
  have hJnonneg : ∀ v, 0 ≤ J v := fun v => Real.sqrt_nonneg _
  -- `Φ` is injective on `Ω` by the lower bound.
  have hinj : InjOn Φ Ω := by
    obtain ⟨c, hc, hcΦ⟩ := hanti
    intro w hw w' hw' hww'
    have hle := hcΦ w hw w' hw'
    rw [hww', sub_self, norm_zero] at hle
    have h0 : ‖w - w'‖ ≤ 0 := by
      by_contra hpos
      exact absurd hle (not_le.2 (mul_pos hc (lt_of_not_ge hpos)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  -- Step 2: a bounded open `s ⊆ Ω` carrying `Ω ∩ Φ⁻¹(spt h)` on which `Φ` is Lipschitz.
  obtain ⟨s, L, hs, hsΩ, hcover, hsb, hLip⟩ :=
    Submission.lpf_wtc_caf_lipschitz_localization Q n Φ Ω (tsupport h) hΩ hΦ hanti hsupp
  -- Step 3: the nonnegative identity on `s`, from the injective weighted area formula.
  have hlint : ∀ g : Eucl Q → ℝ≥0∞, Measurable g →
      ∫⁻ y in Φ '' s, g y ∂(μHE[n] : Measure (Eucl Q)) =
        ∫⁻ v in s, ENNReal.ofReal (J v) * g (Φ v) ∂(volume : Measure (Eucl n)) := by
    intro g hg
    have hinjs : InjOn Φ s := hinj.mono hsΩ
    have hsm : MeasurableSet s := hs.measurableSet
    have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum
      hsm.nullMeasurableSet hLip (w := fun v => g (Φ v))
      (hg.comp hΦ.continuous.measurable).aemeasurable
    rw [finrank_euclideanSpace_fin] at harea
    -- Injectivity: the fibre sum is the indicator of `Φ(s)` applied to `g`.
    have hfib : ∀ y, Poincare.SimonGMT.Chapter02.weightedAreaFiberSum s Φ (fun v => g (Φ v)) y =
        (Φ '' s).indicator g y := by
      intro y
      unfold Poincare.SimonGMT.Chapter02.weightedAreaFiberSum
        Poincare.SimonGMT.Chapter02.areaFiber
      by_cases hy : y ∈ Φ '' s
      · obtain ⟨x, hx, rfl⟩ := hy
        rw [indicator_of_mem (mem_image_of_mem Φ hx),
          tsum_eq_single (⟨x, hx, rfl⟩ : {x' // x' ∈ s ∧ Φ x' = Φ x})]
        intro z hz
        exact absurd (Subtype.ext (hinjs z.2.1 hx z.2.2)) hz
      · rw [indicator_of_notMem hy]
        have : IsEmpty {x' // x' ∈ s ∧ Φ x' = y} := ⟨fun z => hy ⟨z.1, z.2.1, z.2.2⟩⟩
        exact tsum_empty
    simp_rw [hfib] at harea
    rw [lintegral_indicator (hsm.image_of_continuousOn_injOn hΦ.continuous.continuousOn hinjs)]
      at harea
    rw [harea]
    refine setLIntegral_congr_fun hsm fun v hv => ?_
    simp only [Poincare.SimonGMT.Chapter02.areaJacobianWithin, fderivWithin_of_isOpen hs hv,
      hJdet v]
  -- Steps 4–5: the signed identity, extended from `s, Φ(s)` back to `Ω, Φ(Ω)`.
  exact Submission.lpf_wtc_caf_signed_of_lintegral Q n Φ Ω s J h hΩ hs hsΩ hsb hΦ.continuous
    hinj hJcont hJnonneg hh hsupp hcover hlint

/-- A `C¹` chart that is antilipschitz on the open set `Ω` has, at each `y = Φ(w)` (`w ∈ Ω`),
the approximate tangent space `T = DΦ(w)(ℝⁿ)` (Simon Ch. 3, Def. 1.4) of `N = Φ(Ω)`.  The
blow-up integral `∫_{η_{y,λ}(N)} φ dHⁿ` is `(λⁿ)⁻¹ ∫_Ω JΦ(v) φ(λ⁻¹(Φ(v) − y)) dv` (blow-up change
of variables, then the area formula), which tends to `∫ JΦ(w) φ(DΦ(w)s) ds`; the area formula for
the linear map `DΦ(w)` identifies this limit with `∫_T φ dHⁿ`. -/
theorem Submission.lpf_wtc_chart_approx_tangent :
    ∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen Ω → ContDiff ℝ 1 Φ →
      (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      ∀ w ∈ Ω, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (Φ '' Ω) (Φ w)
        (LinearMap.range (fderiv ℝ Φ w).toLinearMap) := by
  intro Q n Φ Ω hΩ hΦ hanti w hw
  obtain ⟨c, hc, hcΩ⟩ := hanti
  have hdiff : DifferentiableAt ℝ Φ w := hΦ.differentiable one_ne_zero w
  -- `c‖s‖ ≤ ‖DΦ(w)s‖`: `DΦ(w)` is injective and `c`-antilipschitz on `ℝⁿ`.
  have hlow : ∀ s : Eucl n, c * ‖s‖ ≤ ‖fderiv ℝ Φ w s‖ :=
    Submission.lpf_wtc_cat_fderiv_lower_bound Q n Φ Ω c w hΩ hw hdiff hcΩ
  have hinj : Function.Injective (fderiv ℝ Φ w) := by
    intro s s' hss'
    have h := hlow (s - s')
    rw [map_sub, hss', sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by nlinarith [norm_nonneg (s - s')]))
  refine ⟨?_, fun f => ?_⟩
  · exact (LinearMap.finrank_range_of_inj (f := (fderiv ℝ Φ w).toLinearMap) hinj).trans
      finrank_euclideanSpace_fin
  -- The area formula for the linear map `DΦ(w)` on `ℝⁿ` evaluates the limit `∫_T φ dHⁿ`.
  have hT : ∫ y in (LinearMap.range (fderiv ℝ Φ w).toLinearMap : Set (Eucl Q)), f y
        ∂(μHE[n] : Measure (Eucl Q)) =
      ∫ s, Real.sqrt (Matrix.of fun i j : Fin n =>
          inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1))
            (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det * f (fderiv ℝ Φ w s) := by
    have h := Submission.lpf_wtc_chart_area_formula Q n (fderiv ℝ Φ w) univ isOpen_univ
      (fderiv ℝ Φ w).contDiff
      ⟨c, hc, fun v _ v' _ => by rw [← map_sub (fderiv ℝ Φ w)]; exact hlow (v - v')⟩
      f f.continuous f.hasCompactSupport
    simp only [image_univ, Measure.restrict_univ, ContinuousLinearMap.fderiv] at h
    rwa [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  rw [hT]
  refine (Submission.lpf_wtc_cat_rescaled_integral_tendsto Q n Φ Ω
    (fun v => Real.sqrt (Matrix.of fun i j : Fin n =>
      inner ℝ (fderiv ℝ Φ v (EuclideanSpace.single i 1))
        (fderiv ℝ Φ v (EuclideanSpace.single j 1))).det) f w hΩ hw hΦ.continuous hdiff
    ⟨c, hc, hcΩ⟩ (Submission.lpf_wtc_cat_gram_jacobian_continuous Q n Φ hΦ) f.continuous
    f.hasCompactSupport).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `η = η_{Φ(w),r}` is a homeomorphism, so `φ ∘ η` is again continuous with compact support.
  let e : Eucl Q ≃ₜ Eucl Q :=
    (Homeomorph.addRight (-Φ w)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl Q → Eucl Q) = Poincare.SimonGMT.Chapter03.blowUpMap (Φ w) r := by
    funext x
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hcont : Continuous fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ w) r x) := by
    rw [← he]
    exact f.continuous.comp e.continuous
  have hsupp : HasCompactSupport fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ w) r x) := by
    rw [← he]
    exact f.hasCompactSupport.comp_homeomorph e
  -- Blow up `Φ(Ω)` at `Φ(w)`, then pull the integral back to `Ω` by the area formula.
  rw [Submission.lpf_wtc_blowup_setIntegral_image Q n (Φ w) r (Φ '' Ω) f hr,
    Submission.lpf_wtc_chart_area_formula Q n Φ Ω hΩ hΦ ⟨c, hc, hcΩ⟩ _ hcont hsupp]
  rfl
/-- Lusin decomposition (Simon Ch. 3, Remark 1.8(1)): a positive weight `θ`, `Hⁿ`-integrable on
`M ∩ K` for compact `K ⊆ V`, is continuous on countably many compact pieces `C k ⊆ M` of finite
`Hⁿ`-measure which cover `M` up to an `Hⁿ`-null set. -/
theorem Submission.lpf_wtc_lusin_compact_pieces :
    ∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ), IsOpen V → M ⊆ V →
      NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
        IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) →
      ∃ C : ℕ → Set (Eucl Q), (∀ k, IsCompact (C k)) ∧ (∀ k, C k ⊆ M) ∧
        (∀ k, ContinuousOn θ (C k)) ∧ (∀ k, (μHE[n] : Measure (Eucl Q)) (C k) < ∞) ∧
        (μHE[n] : Measure (Eucl Q)) (M \ ⋃ k, C k) = 0 := by
  intro Q n V M θ hV hMV hM hθ hint
  set μ : Measure (Eucl Q) := μHE[n]
  -- Compact sets `K i = F i ∩ closedBall 0 i ⊆ V` covering `V`.
  obtain ⟨F, hFc, hFV, hFU, hFmono⟩ := hV.exists_iUnion_isClosed
  set K : ℕ → Set (Eucl Q) := fun i => F i ∩ closedBall 0 i
  have hKc : ∀ i, IsCompact (K i) := fun i => (isCompact_closedBall 0 (i : ℝ)).inter_left (hFc i)
  have hKV : ∀ i, K i ⊆ V := fun i => inter_subset_left.trans (hFV i)
  have hcover : ∀ x ∈ V, ∃ i, x ∈ K i := by
    intro x hx
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    exact ⟨max i j, hFmono (le_max_left i j) hi,
      mem_closedBall_zero_iff.2 (hj.trans (Nat.cast_le.2 (le_max_right i j)))⟩
  -- Lusin's theorem for a Borel set `E` of finite measure and a Borel function `g`.
  have lusin : ∀ (E : Set (Eucl Q)) (g : Eucl Q → ℝ), MeasurableSet E → μ E ≠ ∞ → Measurable g →
      ∃ G : ℕ → Set (Eucl Q), (∀ l, IsClosed (G l)) ∧ (∀ l, G l ⊆ E) ∧
        (∀ l, ContinuousOn g (G l)) ∧ μ (E \ ⋃ l, G l) = 0 := by
    intro E g hE hμE hg
    have : IsFiniteMeasure (μ.restrict E) := isFiniteMeasure_restrict.2 hμE
    -- A measurable `S` is relatively open in some closed `H ⊆ E` with `μ (E \ H) < δ`.
    have step : ∀ S : Set (Eucl Q), MeasurableSet S → ∀ δ : ℝ≥0∞, δ ≠ 0 →
        ∃ H, IsClosed H ∧ H ⊆ E ∧ μ (E \ H) < δ ∧ ∃ O, IsOpen O ∧ S ∩ H = O ∩ H := by
      intro S hS δ hδ
      have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
      obtain ⟨H₁, hH₁S, hH₁c, hH₁⟩ :=
        (hE.inter hS).exists_isClosed_sdiff_lt (μ := μ.restrict E) (measure_ne_top _ _) hδ2
      obtain ⟨H₂, hH₂S, hH₂c, hH₂⟩ :=
        (hE.diff hS).exists_isClosed_sdiff_lt (μ := μ.restrict E) (measure_ne_top _ _) hδ2
      refine ⟨H₁ ∪ H₂, hH₁c.union hH₂c,
        union_subset (hH₁S.trans inter_subset_left) (hH₂S.trans sdiff_subset), ?_,
        H₂ᶜ, hH₂c.isOpen_compl, ?_⟩
      · calc μ (E \ (H₁ ∪ H₂)) ≤ μ ((E ∩ S) \ H₁ ∪ (E \ S) \ H₂) := by
              refine measure_mono fun x hx => ?_
              by_cases hxS : x ∈ S
              · exact Or.inl ⟨⟨hx.1, hxS⟩, fun h => hx.2 (Or.inl h)⟩
              · exact Or.inr ⟨⟨hx.1, hxS⟩, fun h => hx.2 (Or.inr h)⟩
          _ ≤ μ ((E ∩ S) \ H₁) + μ ((E \ S) \ H₂) := measure_union_le _ _
          _ = μ.restrict E ((E ∩ S) \ H₁) + μ.restrict E ((E \ S) \ H₂) := by
              rw [Measure.restrict_eq_self _ (sdiff_subset.trans inter_subset_left),
                Measure.restrict_eq_self _ (sdiff_subset.trans sdiff_subset)]
          _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hH₁ hH₂
          _ = δ := ENNReal.add_halves δ
      · ext x
        constructor
        · rintro ⟨hxS, hxH⟩
          exact ⟨fun h => (hH₂S h).2 hxS, hxH⟩
        · rintro ⟨hxO, hxH | hxH⟩
          · exact ⟨(hH₁S hxH).2, Or.inl hxH⟩
          · exact absurd hxH hxO
    -- Doing this for `g⁻¹(q, ∞)` and `g⁻¹(-∞, q)`, `q ∈ ℚ`, makes `g` continuous on `⋂ H`.
    have piece : ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ H, IsClosed H ∧ H ⊆ E ∧ μ (E \ H) < ε ∧ ContinuousOn g H := by
      intro ε hε
      obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε (ℚ × Bool)
      set S : ℚ × Bool → Set (Eucl Q) := fun p =>
        bif p.2 then g ⁻¹' Ioi (p.1 : ℝ) else g ⁻¹' Iio (p.1 : ℝ)
      have hS : ∀ p, MeasurableSet (S p) := by
        rintro ⟨q, b⟩
        cases b
        · exact hg measurableSet_Iio
        · exact hg measurableSet_Ioi
      choose H hHc hHE hHμ O hOo hSO using fun p =>
        step (S p) (hS p) (δ p) (ENNReal.coe_ne_zero.2 (hδpos p).ne')
      refine ⟨⋂ p, H p, isClosed_iInter hHc, (iInter_subset _ (0, true)).trans (hHE _), ?_, ?_⟩
      · calc μ (E \ ⋂ p, H p) = μ (⋃ p, E \ H p) := by rw [sdiff_iInter]
          _ ≤ ∑' p, μ (E \ H p) := measure_iUnion_le _
          _ ≤ ∑' p, (δ p : ℝ≥0∞) := ENNReal.tsum_le_tsum fun p => (hHμ p).le
          _ < ε := hδsum
      · intro x hx
        have hxH : ∀ p, x ∈ H p := mem_iInter.1 hx
        have key : ∀ p, x ∈ S p → ∀ᶠ y in 𝓝[⋂ p, H p] x, y ∈ S p := by
          intro p hxp
          have hxO : x ∈ O p := ((hSO p).subset ⟨hxp, hxH p⟩).1
          filter_upwards [mem_nhdsWithin_of_mem_nhds ((hOo p).mem_nhds hxO),
            self_mem_nhdsWithin] with y hyO hyH
          exact ((hSO p).symm.subset ⟨hyO, mem_iInter.1 hyH p⟩).1
        refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
        · obtain ⟨q, haq, hqx⟩ := exists_rat_btwn ha
          filter_upwards [key (q, true) hqx] with y hy
          exact haq.trans hy
        · obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn hb
          filter_upwards [key (q, false) hxq] with y hy
          exact lt_trans hy hqb
    choose G hGc hGE hGμ hGcont using fun l : ℕ =>
      piece ((l : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top l))
    refine ⟨G, hGc, hGE, hGcont, ?_⟩
    by_contra h
    obtain ⟨l, hl⟩ := ENNReal.exists_inv_nat_lt h
    exact lt_asymm (hl.trans_le (measure_mono (sdiff_subset_sdiff_right (subset_iUnion G l))))
      (hGμ l)
  -- A Borel representative `g` of `θ` on `M`, and a Borel core `B ⊆ M` on which `θ = g`.
  have hMU : M = ⋃ i, M ∩ K i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hx => (hcover x (hMV hx)).imp fun i hi => ⟨hx, hi⟩, fun ⟨_, hx, _⟩ => hx⟩
  have hθm : AEMeasurable θ (μ.restrict M) := by
    rw [hMU]
    exact aemeasurable_iUnion_iff.2 fun i => Integrable.aemeasurable (hint (K i) (hKc i) (hKV i))
  set g := hθm.mk θ
  have hg : Measurable g := hθm.measurable_mk
  have hbad : μ {x | ¬(x ∈ M → θ x = g x)} = 0 := ae_iff.1 ((ae_restrict_iff'₀ hM).1 hθm.ae_eq_mk)
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null hbad
  obtain ⟨B₀, hB₀M, hB₀m, hB₀ae⟩ := hM.exists_measurable_subset_ae_eq
  set B := B₀ \ Z
  have hBm : MeasurableSet B := hB₀m.diff hZm
  have hBM : B ⊆ M := sdiff_subset.trans hB₀M
  have hθgB : ∀ x ∈ B, θ x = g x := fun x hx => by
    by_contra h
    exact hx.2 (hZsub fun hh => h (hh (hBM hx)))
  have hMB : μ (M \ B) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_union_null (ae_eq_set.1 hB₀ae).2 hZ0)
    by_cases hxB₀ : x ∈ B₀
    · exact Or.inr (by_contra fun hz => hx.2 ⟨hxB₀, hz⟩)
    · exact Or.inl ⟨hx.1, hxB₀⟩
  -- Borel pieces `E i j = B ∩ K i ∩ {g > 1/(j+1)}` of finite measure.
  set E : ℕ → ℕ → Set (Eucl Q) := fun i j => B ∩ K i ∩ g ⁻¹' Ioi ((j : ℝ) + 1)⁻¹
  have hEm : ∀ i j, MeasurableSet (E i j) := fun i j =>
    (hBm.inter (hKc i).isClosed.measurableSet).inter (hg measurableSet_Ioi)
  have hEfin : ∀ i j, μ (E i j) ≠ ∞ := by
    intro i j htop
    have hc : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hle : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ * μ (E i j) ≤ ∫⁻ x in M ∩ K i, ‖θ x‖ₑ ∂μ :=
      calc ENNReal.ofReal ((j : ℝ) + 1)⁻¹ * μ (E i j)
          = ∫⁻ _ in E i j, ENNReal.ofReal ((j : ℝ) + 1)⁻¹ ∂μ := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in E i j, ‖θ x‖ₑ ∂μ := setLIntegral_mono' (hEm i j) fun x hx => by
            rw [Real.enorm_eq_ofReal_abs, hθgB x hx.1.1]
            exact ENNReal.ofReal_le_ofReal (hx.2.le.trans (le_abs_self _))
        _ ≤ ∫⁻ x in M ∩ K i, ‖θ x‖ₑ ∂μ :=
            lintegral_mono_set fun x hx => ⟨hBM hx.1.1, hx.1.2⟩
    have hlt := hle.trans_lt (hint (K i) (hKc i) (hKV i)).2
    rw [htop, ENNReal.mul_top hc] at hlt
    exact lt_irrefl _ hlt
  -- Lusin on each `E i j`; the pieces, enumerated by `Nat.unpair`, are the `C k`.
  choose G hGc hGE hGcont hGnull using fun i j => lusin (E i j) g (hEm i j) (hEfin i j) hg
  refine ⟨fun k => G k.unpair.1 k.unpair.2.unpair.1 k.unpair.2.unpair.2, fun k => ?_, fun k => ?_,
    fun k => ?_, fun k => ?_, ?_⟩
  · exact (hKc _).of_isClosed_subset (hGc _ _ _)
      ((hGE _ _ _).trans (inter_subset_left.trans inter_subset_right))
  · exact (hGE _ _ _).trans (inter_subset_left.trans (inter_subset_left.trans hBM))
  · exact (hGcont _ _ _).congr fun x hx => hθgB x ((hGE _ _ _) hx).1.1
  · exact (measure_mono (hGE _ _ _)).trans_lt (lt_top_iff_ne_top.2 (hEfin _ _))
  · refine measure_mono_null (fun x hx => ?_) (measure_union_null hMB
      (measure_iUnion_null fun i => measure_iUnion_null fun j => hGnull i j))
    obtain ⟨hxM, hxC⟩ := hx
    by_cases hxB : x ∈ B
    · right
      obtain ⟨i, hi⟩ := hcover x (hMV hxM)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt ((hθgB x hxB) ▸ hθ x hxM)
      refine mem_iUnion₂.2 ⟨i, j, ⟨⟨hxB, hi⟩, by simpa [one_div] using hj⟩, fun hxG => hxC ?_⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 hxG
      exact mem_iUnion.2 ⟨Nat.pair i (Nat.pair j l), by simpa [Nat.unpair_pair] using hl⟩
    · exact Or.inl ⟨hxM, hxB⟩
/-- Localized upper density theorem (Simon Ch. 1, 3.6) for `ν = (Hⁿ ⌞ S).withDensity g`: if
`∫⁻_{S ∩ K} g dHⁿ < ∞` for every compact `K ⊆ W`, then `ν(B̄_ρ(y)) / ρⁿ → 0` as `ρ → 0+` for
`Hⁿ`-a.e. `y ∈ W \ S`. -/
theorem Submission.lpf_wtc_ae_zero_density_off_set :
    ∀ (Q n : ℕ) (W S : Set (Eucl Q)) (g : Eucl Q → ℝ≥0∞), IsOpen W →
      NullMeasurableSet S (μHE[n] : Measure (Eucl Q)) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ W →
        ∫⁻ x in S ∩ K, g x ∂(μHE[n] : Measure (Eucl Q)) < ∞) →
      ∀ᵐ y ∂(μHE[n] : Measure (Eucl Q)), y ∈ W → y ∉ S →
        Tendsto (fun ρ : ℝ => (∫⁻ x in S ∩ closedBall y ρ, g x ∂(μHE[n] : Measure (Eucl Q))) /
          ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
  intro Q n W S g hW hS hfin
  set μ : Measure (Eucl Q) := μHE[n] with hμ
  -- Step 1: `ν = (μ ⌞ S).withDensity g`, so `ν B = ∫⁻_{S ∩ B} g dμ` for Borel `B`.
  set ν : Measure (Eucl Q) := (μ.restrict S).withDensity g with hν
  have hνB : ∀ B : Set (Eucl Q), MeasurableSet B → ν B = ∫⁻ x in S ∩ B, g x ∂μ := by
    intro B hB
    rw [hν, withDensity_apply _ hB, Measure.restrict_restrict hB, inter_comm B S]
  -- Step 2: the Borel hull `A ⊇ S` of `S`; `ν` does not charge `Aᶜ`.
  set A : Set (Eucl Q) := toMeasurable μ S
  have hAm : MeasurableSet A := measurableSet_toMeasurable μ S
  have hνA : ν Aᶜ = 0 := by
    rw [hνB _ hAm.compl,
      (disjoint_compl_right_iff_subset.mpr (subset_toMeasurable μ S)).inter_eq,
      Measure.restrict_empty, lintegral_zero_measure]
  -- `diam B̄_s(c) ≤ 2s`.
  have hdiam : ∀ (c : Eucl Q) (s : ℝ), ediam (closedBall c s) ≤ ENNReal.ofReal (2 * s) :=
    fun c s => ediam_le_of_forall_dist_le fun y hy z hz => by
      have := dist_triangle_right y z c
      rw [mem_closedBall] at hy hz
      linarith
  -- Step 4 (Upper Density Theorem, Simon Ch. 1, 3.6): for a finite `m` with `m Aᶜ = 0`, the
  -- points `y ∉ A` of upper density `> ε` form an `Hⁿ`-null set.  Proof: a closed `C ⊆ A`
  -- with `m (A \ C) < k⁻¹`, then a Vitali 5r-covering by disjoint balls of radius `< 1/(k+1)`
  -- missing `C`, whose total `ρⁿ`-cost is at most `k⁻¹ / ε`.
  have hcore : ∀ m : Measure (Eucl Q), m univ ≠ ∞ → m Aᶜ = 0 → ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ∞ →
      μH[n] {y | y ∉ A ∧ ∀ δ > 0, ∃ ρ ∈ Ioo 0 δ,
        ε * ENNReal.ofReal ρ ^ n < m (closedBall y ρ)} = 0 := by
    intro m hm hmA ε hε0 hεtop
    set Z := {y | y ∉ A ∧ ∀ δ > 0, ∃ ρ ∈ Ioo 0 δ,
      ε * ENNReal.ofReal ρ ^ n < m (closedBall y ρ)}
    have : IsFiniteMeasure m := ⟨lt_top_iff_ne_top.mpr hm⟩
    have hstep : ∀ k : ℕ, ∃ u : Set (Eucl Q × ℝ), u.Countable ∧
        (∀ b ∈ u, b.2 ∈ Ioo 0 (1 / ((k : ℝ) + 1))) ∧
        Z ⊆ ⋃ b ∈ u, closedBall b.1 (5 * b.2) ∧
        ε * ∑' b : u, ENNReal.ofReal b.1.2 ^ n ≤ (k : ℝ≥0∞)⁻¹ := by
      intro k
      obtain ⟨C, hCA, hCc, hCm⟩ := hAm.exists_isClosed_sdiff_lt (μ := m) (measure_ne_top m A)
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k))
      let t : Set (Eucl Q × ℝ) := {b | b.1 ∈ Z ∧ b.2 ∈ Ioo 0 (1 / ((k : ℝ) + 1)) ∧
        closedBall b.1 b.2 ⊆ Cᶜ ∧ ε * ENNReal.ofReal b.2 ^ n < m (closedBall b.1 b.2)}
      obtain ⟨u, hut, hudisj, hucov⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall t Prod.fst Prod.snd
          (1 / ((k : ℝ) + 1)) (fun b hb => hb.2.1.2.le) 5 (by norm_num)
      have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb =>
        (nonempty_ball.mpr (hut hb).2.1.1).mono ball_subset_interior_closedBall
      refine ⟨u, hucount, fun b hb => (hut hb).2.1, ?_, ?_⟩
      · -- each `y ∈ Z` lies outside the closed `C ⊆ A`, so it centers small good balls `⊆ Cᶜ`
        intro y hy
        obtain ⟨δ₀, hδ₀, hδ₀C⟩ := Metric.isOpen_iff.mp hCc.isOpen_compl y fun h => hy.1 (hCA h)
        obtain ⟨ρ, hρ, hρm⟩ := hy.2 (min δ₀ (1 / ((k : ℝ) + 1))) (by positivity)
        have hρC : closedBall y ρ ⊆ Cᶜ :=
          (closedBall_subset_ball (hρ.2.trans_le (min_le_left _ _))).trans hδ₀C
        obtain ⟨b, hbu, hb⟩ :=
          hucov (y, ρ) ⟨hy, ⟨hρ.1, hρ.2.trans_le (min_le_right _ _)⟩, hρC, hρm⟩
        exact mem_iUnion₂.mpr ⟨b, hbu, hb (mem_closedBall_self hρ.1.le)⟩
      · have := hucount.to_subtype
        calc ε * ∑' b : u, ENNReal.ofReal b.1.2 ^ n
            = ∑' b : u, ε * ENNReal.ofReal b.1.2 ^ n := ENNReal.tsum_mul_left.symm
          _ ≤ ∑' b : u, m (closedBall b.1.1 b.1.2 ∩ Cᶜ) := ENNReal.tsum_le_tsum fun b => by
              rw [inter_eq_left.mpr (hut b.2).2.2.1]
              exact (hut b.2).2.2.2.le
          _ = m (⋃ b : u, closedBall b.1.1 b.1.2 ∩ Cᶜ) := (measure_iUnion
              (fun i j hij => (hudisj i.2 j.2 (Subtype.coe_ne_coe.mpr hij)).mono
                inter_subset_left inter_subset_left)
              (fun _ => measurableSet_closedBall.inter hCc.isOpen_compl.measurableSet)).symm
          _ ≤ m Cᶜ := measure_mono (iUnion_subset fun _ => inter_subset_right)
          _ ≤ m ((A \ C) ∪ Aᶜ) := measure_mono fun x hx => by
              by_cases h : x ∈ A
              exacts [Or.inl ⟨h, hx⟩, Or.inr h]
          _ ≤ m (A \ C) + m Aᶜ := measure_union_le _ _
          _ ≤ (k : ℝ≥0∞)⁻¹ := by
              rw [hmA, add_zero]
              exact hCm.le
    choose u hucount hurad hucov husum using hstep
    have : ∀ k, Countable (u k) := fun k => (hucount k).to_subtype
    refine le_antisymm ?_ bot_le
    calc μH[n] Z ≤ liminf (fun k => ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ))
          atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) Z
            (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) ?_
            (fun k (b : u k) => closedBall b.1.1 (5 * b.1.2)) ?_ ?_
          · simpa using ENNReal.tendsto_ofReal
              ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10)
          · refine Eventually.of_forall fun k b => (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
            have := (hurad k b.1 b.2).2
            linarith
          · refine Eventually.of_forall fun k y hy => ?_
            obtain ⟨b, hbu, hb⟩ := mem_iUnion₂.mp (hucov k hy)
            exact mem_iUnion.mpr ⟨⟨b, hbu⟩, hb⟩
      _ ≤ liminf (fun k : ℕ => 10 ^ n * ((k : ℝ≥0∞)⁻¹ / ε)) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
          calc ∑' b : u k, ediam (closedBall b.1.1 (5 * b.1.2)) ^ (n : ℝ)
              ≤ ∑' b : u k, 10 ^ n * ENNReal.ofReal b.1.2 ^ n :=
                ENNReal.tsum_le_tsum fun b => by
                  rw [ENNReal.rpow_natCast, ← mul_pow]
                  gcongr
                  refine (hdiam _ _).trans ?_
                  rw [← ENNReal.ofReal_ofNat 10, ← ENNReal.ofReal_mul (by norm_num)]
                  exact ENNReal.ofReal_le_ofReal (by linarith)
            _ = 10 ^ n * ∑' b : u k, ENNReal.ofReal b.1.2 ^ n := ENNReal.tsum_mul_left
            _ ≤ 10 ^ n * ((k : ℝ≥0∞)⁻¹ / ε) := by
                gcongr
                rw [ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl hεtop), mul_comm]
                exact husum k
      _ = 0 := by
          refine Tendsto.liminf_eq ?_
          simpa using ENNReal.Tendsto.const_mul
            (ENNReal.Tendsto.div_const ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hε0))
            (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
  -- Steps 3 and 5: localize to balls `B̄_{2r}(x) ⊆ W` (finite `ν`-mass) around each point of
  -- the exceptional set, and use `μHE[n] = c • μH[n]`.
  have hmain : ∀ᵐ y ∂μ, y ∈ W → y ∉ A →
      Tendsto (fun ρ : ℝ => ν (closedBall y ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    rw [ae_iff]
    apply measure_null_of_locally_null
    intro x hx
    simp only [mem_ofPred_eq, not_imp] at hx
    obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.mp hW x hx.1
    have hr : 0 < R / 3 := by positivity
    have hKW : closedBall x (2 * (R / 3)) ⊆ W := (closedBall_subset_ball (by linarith)).trans hRW
    set m := ν.restrict (closedBall x (2 * (R / 3))) with hm_def
    have hm : m univ ≠ ∞ := by
      rw [hm_def, Measure.restrict_apply_univ, hνB _ measurableSet_closedBall]
      exact (hfin _ (isCompact_closedBall x _) hKW).ne
    have hmA : m Aᶜ = 0 := by
      rw [hm_def, Measure.restrict_apply hAm.compl]
      exact measure_mono_null inter_subset_left hνA
    refine ⟨_ ∩ ball x (R / 3), inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
    rw [hμ, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    refine (congrArg _ (measure_mono_null ?_ (measure_iUnion_null fun k : ℕ =>
      hcore m hm hmA ((k : ℝ≥0∞) + 1)⁻¹ (by simp) (by simp)))).trans (smul_zero _)
    -- a non-tending quotient exceeds some `(k + 1)⁻¹` at arbitrarily small radii
    rintro y ⟨hy, hyx⟩
    simp only [mem_ofPred_eq, not_imp] at hy
    obtain ⟨-, hyA, hyT⟩ := hy
    rw [ENNReal.tendsto_nhds_zero] at hyT
    push Not at hyT
    obtain ⟨ε, hε, hfreq⟩ := hyT
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.mpr ⟨k, hyA, fun δ hδ => ?_⟩
    obtain ⟨ρ, hρf, hρ⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hδ hr))).exists
    refine ⟨ρ, ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩, ?_⟩
    have hsub : closedBall y ρ ⊆ closedBall x (2 * (R / 3)) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      rw [mem_ball] at hyx
      linarith [dist_triangle z y x, hρ.2.trans_le (min_le_right δ (R / 3))]
    rw [hm_def, Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hsub,
      ← ENNReal.ofReal_pow hρ.1.le]
    refine ENNReal.mul_lt_of_lt_div (lt_of_le_of_lt ?_ hρf)
    exact (ENNReal.inv_le_inv.mpr (by simp)).trans hk.le
  -- Step 6: transfer from the hull `A` back to `S` (they agree `μ`-a.e.).
  filter_upwards [hmain, hS.toMeasurable_ae_eq] with y hy hyA hyW hyS
  refine (hy hyW fun h => hyS (hyA ▸ h)).congr fun ρ => ?_
  rw [hνB _ measurableSet_closedBall]

/-- Density bound at a tangent point (Simon Ch. 3, Remark 1.5(3), boundedness part): if `T` is
the approximate tangent space (Def. 1.4) of `S` at `y` and `Hⁿ(S ∩ B̄_r(y)) < ∞` for some `r > 0`,
then `Hⁿ(S ∩ B̄_ρ(y)) ≤ K ρⁿ` for all sufficiently small `ρ > 0`. -/
theorem Submission.lpf_wtc_density_bound_of_tangent : ∀ (Q n : ℕ) (S : Set (Eucl Q)) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y T → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y r) < ∞) → ∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n) := by
  intro Q n S y T hT ⟨r, hr, hfin⟩
  -- Step 1: the cut-off `φ₀(z) = min(1, max(0, 2 - |z|))`, an element of `C_c(ℝ^Q, ℝ)` with
  -- `0 ≤ φ₀ ≤ 1`, `φ₀ = 1` on `B̄₁(0)` and `φ₀ = 0` off `B̄₂(0)`.
  have hzero : ∀ z : Eucl Q, 2 ≤ ‖z‖ → min 1 (max 0 (2 - ‖z‖)) = (0 : ℝ) := fun z hz => by
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  let φ₀ : CompactlySupportedContinuousMap (Eucl Q) ℝ :=
    ⟨⟨fun z => min 1 (max 0 (2 - ‖z‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) fun z hz =>
        hzero z (not_le.1 (mt mem_closedBall_zero_iff.2 hz)).le⟩
  have hφ₀ : ∀ z, φ₀ z = min 1 (max 0 (2 - ‖z‖)) := fun _ => rfl
  have hφ₀01 : ∀ z, 0 ≤ φ₀ z ∧ φ₀ z ≤ 1 := fun z => by
    rw [hφ₀]
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hφ₀one : ∀ z, ‖z‖ ≤ 1 → φ₀ z = 1 := fun z hz => by
    rw [hφ₀]
    exact min_eq_left (le_max_of_le_right (by linarith))
  set L₀ : ℝ := ∫ z in (T : Set (Eucl Q)), φ₀ z ∂(μHE[n] : Measure (Eucl Q))
  refine ⟨(L₀ + 1).toNNReal, ?_⟩
  -- Step 2: the blow-up integrals of `φ₀` tend to `L₀`, so they are eventually `≤ L₀ + 1`;
  -- also eventually `0 < ρ < r / 2`.
  filter_upwards [(hT.2 φ₀).eventually (eventually_le_nhds (lt_add_one L₀)),
    Ioo_mem_nhdsGT (half_pos hr)] with ρ hρ ⟨hρ0, hρr⟩
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  have hnorm : ∀ x, ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ = ρ⁻¹ * dist x y := by
    intro x
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hρ0), dist_eq_norm]
  have hcont : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y ρ) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hsub : ∀ s ≤ r, S ∩ closedBall y s ⊆ S ∩ closedBall y r := fun s hs =>
    inter_subset_inter_right _ (closedBall_subset_closedBall hs)
  -- Step 3: `ψ = φ₀ ∘ η_{y,ρ}` is integrable on `S` (it is bounded by `1_{B̄_{2ρ}(y)}` and
  -- `Hⁿ(S ∩ B̄_{2ρ}(y)) < ∞`) and dominates `1_{B̄_ρ(y)}`.
  have hψint : Integrable (fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x))
      ((μHE[n] : Measure (Eucl Q)).restrict S) := by
    refine Integrable.mono' (g := (closedBall y (2 * ρ)).indicator fun _ => (1 : ℝ)) ?_
      (φ₀.continuous.comp hcont).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact ne_top_of_le_ne_top hfin.ne (measure_mono (hsub _ (by linarith)))
    · by_cases hx : x ∈ closedBall y (2 * ρ)
      · rw [indicator_of_mem hx, Real.norm_of_nonneg (hφ₀01 _).1]
        exact (hφ₀01 _).2
      · have h2 : 2 ≤ ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ := by
          rw [mem_closedBall, not_le] at hx
          rw [hnorm, le_inv_mul_iff₀ hρ0]
          linarith
        rw [indicator_of_notMem hx, hφ₀, hzero _ h2, norm_zero]
  have hle : (μHE[n] : Measure (Eucl Q)).real (S ∩ closedBall y ρ) ≤
      ∫ x in S, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x)
        ∂(μHE[n] : Measure (Eucl Q)) := by
    rw [inter_comm, ← measureReal_restrict_apply measurableSet_closedBall,
      ← integral_indicator_one measurableSet_closedBall]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hψint (ae_of_all _ fun x => ?_)
    · exact indicator_nonneg (fun _ _ => zero_le_one) x
    · by_cases hx : x ∈ closedBall y ρ
      · have h1 : ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ ≤ 1 := by
          rw [hnorm, inv_mul_le_iff₀ hρ0, mul_one]
          exact hx
        rw [indicator_of_mem hx, Pi.one_apply]
        exact (hφ₀one _ h1).ge
      · rw [indicator_of_notMem hx]
        exact (hφ₀01 _).1
  -- Step 4: by the blow-up identity, `∫_S ψ = ρⁿ ∫_{η_{y,ρ}(S)} φ₀ ≤ (L₀ + 1) ρⁿ`.
  have hS : ∫ x in S, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x)
        ∂(μHE[n] : Measure (Eucl Q)) =
      ρ ^ n * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y ρ '' S, φ₀ z
        ∂(μHE[n] : Measure (Eucl Q)) := by
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y ρ S φ₀ hρ0,
      mul_inv_cancel_left₀ hρn.ne']
  have hfinρ : (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (measure_mono (hsub _ (by linarith)))
  calc (μHE[n] : Measure (Eucl Q)) (S ∩ closedBall y ρ)
      = ENNReal.ofReal ((μHE[n] : Measure (Eucl Q)).real (S ∩ closedBall y ρ)) :=
        (ofReal_measureReal hfinρ).symm
    _ ≤ ENNReal.ofReal ((L₀ + 1) * ρ ^ n) := by
        refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
        rw [hS, mul_comm]
        exact mul_le_mul_of_nonneg_right hρ hρn.le
    _ = (L₀ + 1).toNNReal * ENNReal.ofReal (ρ ^ n) := ENNReal.ofReal_mul' hρn.le

/-- Transfer of approximate tangent planes (Simon Ch. 3, proof of Theorem 1.6 "⇒", step 2).  If
`T` is the approximate tangent space of `N` at `y`, `Hⁿ(N ∩ B̄_r(y)) < ∞` for some `r > 0` and
`Hⁿ((C ∖ N) ∩ B̄_ρ(y))`, `Hⁿ((N ∖ C) ∩ B̄_ρ(y))` are `o(ρⁿ)`, then `T` is the approximate tangent
space of `C` at `y`.  For `φ ∈ C_c` with `|φ| ≤ A` and `tsupport φ ⊆ B_R(0)`, the blow-up formula
`lpf_wtc_blowup_setIntegral_image` localizes both blow-up integrals to `B = B̄_{λR}(y)`, and
splitting `C ∩ B`, `N ∩ B` along `C ∩ N ∩ B` gives, for small `λ > 0`,
`|∫_{η_{y,λ}(C)} φ - ∫_{η_{y,λ}(N)} φ| ≤ A Rⁿ (q₁(λR) + q₂(λR))`, where `q₁, q₂` are the two
density quotients of the hypotheses. -/
theorem Submission.lpf_wtc_tangent_transfer :
    ∀ (Q n : ℕ) (C N : Set (Eucl Q)) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)),
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) →
      NullMeasurableSet N (μHE[n] : Measure (Eucl Q)) →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n N y T →
      (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (N ∩ closedBall y r) < ∞) →
      Tendsto (fun ρ : ℝ => (μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y ρ) /
        ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun ρ : ℝ => (μHE[n] : Measure (Eucl Q)) ((N \ C) ∩ closedBall y ρ) /
        ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C y T := by
  intro Q n C N y T hC hN hNT hfin hCN hNC
  obtain ⟨r, hr, hNr⟩ := hfin
  -- The dimension condition is inherited from `N`.
  refine ⟨hNT.1, fun φ => ?_⟩
  -- `tsupport φ ⊆ B_R(0)` with `R > 0`, and `|φ| ≤ A`.
  obtain ⟨R, hR, hRsupp⟩ :=
    (HasCompactSupport.isCompact φ.hasCompactSupport).isBounded.subset_ball_lt 0 (0 : Eucl Q)
  obtain ⟨A, hA⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- `t ↦ t * R` maps `𝓝[>] 0` into itself, so `q₁(tR), q₂(tR) → 0`.
  have hmap : Tendsto (fun t : ℝ => t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun t : ℝ => t * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos ht hR
  have hCN' := hCN.comp hmap
  have hNC' := hNC.comp hmap
  -- The error bound `A Rⁿ (q₁(tR) + q₂(tR))` tends to `0`.
  have hbound : Tendsto (fun t : ℝ => A * R ^ n *
      (((μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y (t * R)) /
          ENNReal.ofReal ((t * R) ^ n)).toReal +
        ((μHE[n] : Measure (Eucl Q)) ((N \ C) ∩ closedBall y (t * R)) /
          ENNReal.ofReal ((t * R) ^ n)).toReal)) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hCN'
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hNC'
    simpa using (h1.add h2).const_mul (A * R ^ n)
  -- The blow-up integrals of `C` and `N` are asymptotically equal.
  have key : Tendsto (fun t : ℝ =>
      (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y t '' C, φ z ∂(μHE[n] : Measure (Eucl Q))) -
        ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y t '' N, φ z ∂(μHE[n] : Measure (Eucl Q)))
      (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * R < r :=
      (hmap.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hr)
    have hfin₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y (t * R)) /
          ENNReal.ofReal ((t * R) ^ n) < ∞ :=
      hCN'.eventually (gt_mem_nhds ENNReal.zero_lt_top)
    filter_upwards [self_mem_nhdsWithin, hsmall, hfin₁] with t ht htr htfin
    have ht : 0 < t := ht
    -- Localization: `φ ∘ η_{y,t}` vanishes off `B = B̄_{tR}(y)`.
    have hvan : ∀ x, x ∉ closedBall y (t * R) →
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) = 0 := by
      intro x hx
      by_contra hne
      apply hx
      have h1 : Poincare.SimonGMT.Chapter03.blowUpMap y t x ∈ ball (0 : Eucl Q) R :=
        hRsupp (subset_tsupport _ hne)
      rw [mem_ball, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
        Real.norm_of_nonneg ht.le, inv_mul_lt_iff₀ ht] at h1
      rw [mem_closedBall, dist_eq_norm]
      exact h1.le
    have hloc : ∀ S : Set (Eucl Q),
        ∫ x in S, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q)) =
          ∫ x in S ∩ closedBall y (t * R), φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x)
            ∂(μHE[n] : Measure (Eucl Q)) := by
      intro S
      rw [← setIntegral_indicator measurableSet_closedBall]
      congr 1
      funext x
      by_cases hx : x ∈ closedBall y (t * R)
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hvan x hx]
    -- Finiteness of the pieces: `tR < r` and `q₁(tR) < ∞`.
    have hBr : closedBall y (t * R) ⊆ closedBall y r := closedBall_subset_closedBall htr.le
    have hNB : (μHE[n] : Measure (Eucl Q)) (N ∩ closedBall y (t * R)) < ∞ :=
      (measure_mono (inter_subset_inter_right N hBr)).trans_lt hNr
    have hP₂ : (μHE[n] : Measure (Eucl Q)) ((N \ C) ∩ closedBall y (t * R)) < ∞ :=
      (measure_mono (inter_subset_inter_left _ sdiff_subset)).trans_lt hNB
    have hP₁ : (μHE[n] : Measure (Eucl Q)) ((C \ N) ∩ closedBall y (t * R)) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at htfin
      exact lt_irrefl _ htfin
    have hCB : (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y (t * R)) < ∞ := by
      have hsub : C ∩ closedBall y (t * R) ⊆
          (N ∩ closedBall y (t * R)) ∪ ((C \ N) ∩ closedBall y (t * R)) := by
        rintro x ⟨hxC, hxB⟩
        by_cases hxN : x ∈ N
        · exact Or.inl ⟨hxN, hxB⟩
        · exact Or.inr ⟨⟨hxC, hxN⟩, hxB⟩
      exact (measure_mono hsub).trans_lt
        ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hNB, hP₁⟩))
    -- `φ ∘ η_{y,t}` is continuous and bounded by `A`, hence integrable on finite-measure sets.
    have hcont : Continuous fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) :=
      (map_continuous φ).comp (show Continuous fun x : Eucl Q => t⁻¹ • (x - y) by fun_prop)
    have hint : ∀ S : Set (Eucl Q), (μHE[n] : Measure (Eucl Q)) S < ∞ →
        IntegrableOn (fun x => φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x)) S
          (μHE[n] : Measure (Eucl Q)) := fun S hS =>
      Measure.integrableOn_of_bounded hS.ne hcont.aestronglyMeasurable
        (Eventually.of_forall fun x => hA _)
    have hnorm : ∀ S : Set (Eucl Q), (μHE[n] : Measure (Eucl Q)) S < ∞ →
        ‖∫ x in S, φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x)
          ∂(μHE[n] : Measure (Eucl Q))‖ ≤ A * ((μHE[n] : Measure (Eucl Q)) S).toReal :=
      fun S hS => by
        rw [← measureReal_def]
        exact norm_setIntegral_le_of_norm_le_const hS fun x _ => hA _
    -- Split `C ∩ B` and `N ∩ B` along the common part `C ∩ N ∩ B`.
    have hdC := integral_inter_add_sdiff₀ hN (hint _ hCB)
    have hdN := integral_inter_add_sdiff₀ hC (hint _ hNB)
    have e₀ : C ∩ closedBall y (t * R) ∩ N = N ∩ closedBall y (t * R) ∩ C := by
      ext x; simp only [mem_inter_iff]; tauto
    have e₁ : (C ∩ closedBall y (t * R)) \ N = (C \ N) ∩ closedBall y (t * R) := by
      ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
    have e₂ : (N ∩ closedBall y (t * R)) \ C = (N \ C) ∩ closedBall y (t * R) := by
      ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
    rw [e₀, e₁] at hdC
    rw [e₂] at hdN
    -- `|∫_{η(C)} φ - ∫_{η(N)} φ| = t⁻ⁿ |∫_{P₁} φ ∘ η - ∫_{P₂} φ ∘ η| ≤ t⁻ⁿ A (Hⁿ(P₁) + Hⁿ(P₂))`.
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t C φ ht,
      Submission.lpf_wtc_blowup_setIntegral_image Q n y t N φ ht, ← mul_sub, hloc C, hloc N,
      ← hdC, ← hdN, add_sub_add_left_eq_sub, norm_mul, norm_inv, norm_pow,
      Real.norm_of_nonneg ht.le]
    have hpow : 0 < (t * R) ^ n := pow_pos (mul_pos ht hR) n
    have hle := (norm_sub_le _ _).trans (add_le_add (hnorm _ hP₁) (hnorm _ hP₂))
    refine (mul_le_mul_of_nonneg_left hle (by positivity)).trans_eq ?_
    rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_ofReal hpow.le, mul_pow]
    field_simp
  -- Conclusion: `∫_{η(C)} φ = ∫_{η(N)} φ + (∫_{η(C)} φ - ∫_{η(N)} φ) → ∫_T φ + 0`.
  have h := (hNT.2 φ).add key
  rw [add_zero] at h
  exact h.congr fun t => add_sub_cancel _ _
/-- Simon Ch. 3, Remark 1.8(1): if `T` is the approximate tangent space of `C ⊆ M` at `y ∈ C`
(Definition 1.4), `θ ≥ 0` is `Hⁿ`-integrable on `M` near `y`, `θ|C` is continuous at `y` and
`θ Hⁿ ⌞ (M ∖ C)` has `n`-density `0` at `y`, then `T` is the approximate tangent space of `M` at
`y` with respect to `θ` (Definition 1.7).  After the change of variables `z = η_{y,t}(x)`, the
weighted blow-up integral is `θ(y) ∫_{η_{y,t}(C)} φ`, which tends to `θ(y) ∫_T φ`, plus the
oscillation of `θ` along `C` and the contribution of `M ∖ C`, both of which tend to `0`. -/
theorem Submission.lpf_wtc_weighted_tangent_transfer :
    ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)),
      NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) →
      NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → y ∈ C →
      (∀ x ∈ M, 0 ≤ θ x) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C y T →
      (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧
        IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) →
      ContinuousWithinAt θ C y →
      Tendsto (fun ρ : ℝ => (∫⁻ x in (M \ C) ∩ closedBall y ρ, ENNReal.ofReal (θ x)
        ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      HasWeightedApproximateTangentSpaceAt n M θ y T := by
  intro Q n M C θ y T hM hC hCM _ hθ hT hr hθC hdens
  -- `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all small `ρ > 0`.
  have hK := Submission.lpf_wtc_density_bound_of_tangent Q n C y T hT
    (hr.imp fun _ h => ⟨h.1, h.2.1⟩)
  refine ⟨hT.1, fun φ => ?_⟩
  -- Main term: `(tⁿ)⁻¹ ∫_C φ ∘ η_{y,t} = ∫_{η_{y,t}(C)} φ → ∫_T φ`.
  have h₁ : Tendsto (fun t : ℝ => θ y * ((t ^ n)⁻¹ * ∫ x in C,
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) ∂(μHE[n] : Measure (Eucl Q))))
      (𝓝[>] 0) (𝓝 (θ y * ∫ z in (T : Set (Eucl Q)), φ z ∂(μHE[n] : Measure (Eucl Q)))) := by
    refine ((hT.2 φ).const_mul (θ y)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t C φ ht]
  -- The oscillation of `θ` along `C` and the contribution of `M ∖ C` vanish in the limit.
  have h₂ := Submission.lpf_wtc_wtt_continuity_error_vanishes Q n C θ y φ hC hθC hK
  have h₃ := Submission.lpf_wtc_wtt_remainder_vanishes Q n (M \ C) θ y φ (hM.diff hC)
    (fun x hx => hθ x hx.1) hdens
  have h := (h₁.add h₂).add h₃
  rw [add_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Submission.lpf_wtc_wtt_blowup_integral_split Q n M C θ y φ hM hC hCM hr]
    with t (ht : 0 < t) hsplit
  -- Change of variables `z = η_{y,t}(x)`, under which `y + t • z = x`.
  have hη : ∀ x, y + t • Poincare.SimonGMT.Chapter03.blowUpMap y t x = x := fun x => by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ ht.ne', add_sub_cancel]
  rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t M _ ht]
  simp_rw [hη]
  rw [hsplit]
  ring

/-- Weighted approximate tangent planes along a `C¹` chart (Simon Ch. 3, proof of Theorem 1.6
"⇒" and Remark 1.8(1), for one chart): if `Φ : ℝⁿ → ℝ^Q` is `C¹` and antilipschitz on the open
set `Ω`, then at `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)`, with `y = Φ(w)`, `DΦ(w)(ℝⁿ)` is the approximate tangent
space of `M` with respect to `θ`.  Cover `M` up to a null set by compact pieces `C` with `θ|C`
continuous (`lpf_wtc_lusin_compact_pieces`).  At a.e. `y ∈ C ∩ Φ(Ω)`, the sets `C ∖ Φ(Ω)`,
`Φ(Ω) ∖ C` and the measure `θ Hⁿ ⌞ (M ∖ C)` have zero `n`-density
(`lpf_wtc_ae_zero_density_off_set`); there the tangent plane of `Φ(Ω)`
(`lpf_wtc_chart_approx_tangent`) passes to `C` (`lpf_wtc_tangent_transfer`) and then to the
weighted set `(M, θ)` (`lpf_wtc_weighted_tangent_transfer`). -/
theorem Submission.slicing_im_coarea_chart_tangent : ∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen V → M ⊆ V → NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict (M ∩ Φ '' Ω)), ∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt n M θ y (LinearMap.range (fderiv ℝ Φ w).toLinearMap) := by
  intro Q n V M θ Φ Ω hV hMV hM hθ hint hΩ hΦ hanti
  -- Step 0: `N = Φ(Ω)` is Borel and locally `Hⁿ`-finite.
  obtain ⟨hNm, hNfin⟩ :=
    Submission.lpf_wtc_chart_image_measurable_locally_finite Q n Φ Ω hΩ hΦ hanti
  -- Step 1 (Remark 1.8(1)): compact pieces `C k ⊆ M` of finite measure with `θ|C k` continuous,
  -- covering `M` up to an `Hⁿ`-null set.
  obtain ⟨C, hCc, hCM, hθC, hCfin, hnull⟩ :=
    Submission.lpf_wtc_lusin_compact_pieces Q n V M θ hV hMV hM hθ hint
  -- Steps 2–4 on a fixed piece: the conclusion holds at `Hⁿ`-a.e. point of `C k ∩ Φ(Ω)`.
  have hpiece : ∀ k, ∀ᵐ y ∂(μHE[n] : Measure (Eucl Q)), y ∈ C k → y ∈ Φ '' Ω →
      ∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt n M θ y
        (LinearMap.range (fderiv ℝ Φ w).toLinearMap) := by
    intro k
    have hCm : MeasurableSet (C k) := (hCc k).isClosed.measurableSet
    -- (i) `Hⁿ ⌞ (C k ∖ Φ(Ω))` has zero `n`-density off `C k ∖ Φ(Ω)`.
    have h₁ := Submission.lpf_wtc_ae_zero_density_off_set Q n univ (C k \ Φ '' Ω) (fun _ => 1)
      isOpen_univ (hCm.diff hNm).nullMeasurableSet fun K _ _ => by
        rw [setLIntegral_one]
        exact (measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt (hCfin k)
    -- (ii) `Hⁿ ⌞ (Φ(Ω) ∖ C k)` has zero `n`-density off `Φ(Ω) ∖ C k`.
    have h₂ := Submission.lpf_wtc_ae_zero_density_off_set Q n univ (Φ '' Ω \ C k) (fun _ => 1)
      isOpen_univ (hNm.diff hCm).nullMeasurableSet fun K hK _ => by
        rw [setLIntegral_one]
        exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hNfin K hK)
    -- (iii) `θ Hⁿ ⌞ (M ∖ C k)` has zero `n`-density at a.e. point of `V ∖ (M ∖ C k)`.
    have h₃ := Submission.lpf_wtc_ae_zero_density_off_set Q n V (M \ C k)
      (fun x => ENNReal.ofReal (θ x)) hV (hM.diff hCm.nullMeasurableSet) fun K hK hKV =>
        (lintegral_mono_set (inter_subset_inter_left K sdiff_subset)).trans_lt
          (hint K hK hKV).setLIntegral_lt_top
    filter_upwards [h₁, h₂, h₃] with y hy₁ hy₂ hy₃ hyC hyN w hw hwy
    subst hwy
    simp only [setLIntegral_one] at hy₁ hy₂
    have hyV : Φ w ∈ V := hMV (hCM k hyC)
    -- Step 2: the approximate tangent plane of `Φ(Ω)` at `Φ w` is also that of `C k`.
    have hT := Submission.lpf_wtc_chart_approx_tangent Q n Φ Ω hΩ hΦ hanti w hw
    have hCT := Submission.lpf_wtc_tangent_transfer Q n (C k) (Φ '' Ω) (Φ w) _
      hCm.nullMeasurableSet hNm.nullMeasurableSet hT
      ⟨1, one_pos, hNfin _ (isCompact_closedBall _ _)⟩
      (hy₁ (mem_univ _) fun h => h.2 hyN) (hy₂ (mem_univ _) fun h => h.2 hyC)
    -- Step 4: weighted blow-up on `M`, with `closedBall (Φ w) (ε / 2) ⊆ V`.
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV _ hyV
    exact Submission.lpf_wtc_weighted_tangent_transfer Q n M (C k) θ (Φ w) _ hM
      hCm.nullMeasurableSet (hCM k) hyC (fun x hx => (hθ x hx).le) hCT
      ⟨ε / 2, half_pos hε, (measure_mono inter_subset_left).trans_lt (hCfin k),
        hint _ (isCompact_closedBall _ _)
          ((closedBall_subset_ball (half_lt_self hε)).trans hεV)⟩
      ((hθC k).continuousWithinAt hyC) (hy₃ hyV fun h => h.2 hyC)
  -- Step 5: a.e. point of `M ∩ Φ(Ω)` lies in some piece `C k` and is good for it.
  filter_upwards [ae_restrict_mem₀ (hM.inter hNm.nullMeasurableSet),
    ae_restrict_of_ae (ae_all_iff.2 hpiece),
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)] with y hy hyk hyU
  obtain ⟨k, hk⟩ := mem_iUnion.1 (not_not.1 fun h => hyU ⟨hy.1, h⟩)
  exact hyk k hk hy.2
/-- Simon Ch. 2, 4.7/4.10 (used for the co-area step of Ch. 6, 4.5): if `F : ℝ^P → ℝ` is
`K`-Lipschitz on a neighbourhood `V` of `Φ(w)` and both `Φ` and `F ∘ Φ` are differentiable at `w`,
then `t ↦ F(Φ(w) + t DΦ(w)s)` has derivative `D(F∘Φ)(w)s` at `0`.  For small `t` it differs from
`t ↦ F(Φ(w + ts))` by at most `K ‖Φ(w + ts) - Φ(w) - t DΦ(w)s‖ = o(t)`, and the latter map has
derivative `D(F∘Φ)(w)s`. -/
theorem Submission.slicing_im_coarea_line_deriv : ∀ (n P : ℕ) (F : Eucl P → ℝ) (Φ : Eucl n → Eucl P) (w : Eucl n), (∃ K : ℝ≥0, ∃ V ∈ 𝓝 (Φ w), LipschitzOnWith K F V) → DifferentiableAt ℝ Φ w → DifferentiableAt ℝ (F ∘ Φ) w → ∀ s : Eucl n, HasDerivAt (fun t : ℝ => F (Φ w + t • fderiv ℝ Φ w s)) (fderiv ℝ (F ∘ Φ) w s) 0 := by
  rintro n P F Φ w ⟨K, V, hV, hFV⟩ hΦ hFΦ s
  -- The line `ℓ(t) = w + t s` has derivative `s` at `0`.
  have hℓ : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
  have hℓ0 : w = w + (0 : ℝ) • s := by simp
  -- Chain rule along `ℓ`: `t ↦ Φ(w + t s)` has derivative `DΦ(w)s` and `t ↦ F(Φ(w + t s))` has
  -- derivative `D(F∘Φ)(w)s` at `0`.
  have hφ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0
  have hg : HasDerivAt (fun t : ℝ => F (Φ (w + t • s))) (fderiv ℝ (F ∘ Φ) w s) 0 :=
    hFΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0
  -- `Φ(w + t s) - Φ(w) - t DΦ(w)s = o(t)`.
  have hrem : (fun t : ℝ => Φ (w + t • s) - Φ w - t • fderiv ℝ Φ w s) =o[𝓝 0] fun t : ℝ => t := by
    simpa using hφ.isLittleO
  -- For `t` near `0`, both `Φ(w) + t DΦ(w)s` and `Φ(w + t s)` lie in `V`.
  have h₁ : ∀ᶠ t : ℝ in 𝓝 0, Φ w + t • fderiv ℝ Φ w s ∈ V := by
    have hc : Continuous fun t : ℝ => Φ w + t • fderiv ℝ Φ w s := by fun_prop
    have : Tendsto (fun t : ℝ => Φ w + t • fderiv ℝ Φ w s) (𝓝 0) (𝓝 (Φ w)) := by
      simpa using hc.tendsto 0
    exact this.eventually_mem hV
  have h₂ : ∀ᶠ t : ℝ in 𝓝 0, Φ (w + t • s) ∈ V := by
    have : Tendsto (fun t : ℝ => Φ (w + t • s)) (𝓝 0) (𝓝 (Φ w)) := by
      simpa using hφ.continuousAt.tendsto
    exact this.eventually_mem hV
  -- Hence `q(t) := F(Φ(w) + t DΦ(w)s) - F(Φ(w + t s)) = O(Φ(w + t s) - Φ(w) - t DΦ(w)s) = o(t)`.
  have hO : (fun t : ℝ => F (Φ w + t • fderiv ℝ Φ w s) - F (Φ (w + t • s))) =O[𝓝 0]
      fun t : ℝ => Φ (w + t • s) - Φ w - t • fderiv ℝ Φ w s := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [h₁, h₂] with t ht₁ ht₂
    have hK := hFV.dist_le_mul _ ht₁ _ ht₂
    rw [dist_eq_norm, dist_eq_norm] at hK
    rw [sub_sub, norm_sub_rev (Φ (w + t • s))]
    exact hK
  -- `q(0) = 0`, so `q` has derivative `0` at `0`.
  have hq : HasDerivAt (fun t : ℝ => F (Φ w + t • fderiv ℝ Φ w s) - F (Φ (w + t • s))) 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa using hO.trans_isLittleO hrem
  -- `F(Φ(w) + t DΦ(w)s) = F(Φ(w + t s)) + q(t)`.
  have hsum := hg.add hq
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp

/-- Pieces for the co-area formula (Steps 1–4 of `slicing_im_coarea`; Simon Ch. 2, 1.2 and 1.5,
Ch. 3, 1.2–1.8).  Up to an `Hⁿ`-null set, `M` is the disjoint union of Borel pieces
`W i ⊆ Φ i(Ω i)`, where the `Φ i` are `C¹` antilipschitz charts.  On `Φ i⁻¹(W i)`, `f ∘ Φ i`
agrees with a `C¹` function `h i`, and `Dh i(w) u = ⟨G(Φ i w), DΦ i(w) u⟩`.

The charts come from `slicing_im_coarea_chart_cover`.  The Lipschitz extension of `f ∘ Φ j|Ω j`
is approximated by `slicing_im_coarea_c1_approx` off a set `ℝⁿ ∖ A' j k` of measure `< k⁻¹`.
Off the null sets where `slicing_im_coarea_chart_tangent` or the tangential-gradient hypothesis
fails, `range DΦ j(w)` is a tangent plane at `Φ j w`; `slicing_im_coarea_line_deriv` and
uniqueness of derivatives then give `⟨G, DΦ j(w) u⟩ = Dh(w) u`.  The pieces disjointify
`(B ∩ Φ j(Ω j ∩ A' j k)) ∖ (Z₁ j ∪ Z₂)`, with `B ⊆ M` a Borel kernel. -/
theorem Submission.slicing_im_coarea_pieces :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1))
      (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U →
      IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f →
      (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
          G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) →
      ∃ (Φ : ℕ → Eucl (m + 1) → Eucl P) (Ω : ℕ → Set (Eucl (m + 1)))
        (h : ℕ → Eucl (m + 1) → ℝ) (W : ℕ → Set (Eucl P)),
        (∀ i, IsOpen (Ω i)) ∧ (∀ i, ContDiff ℝ 1 (Φ i)) ∧
        (∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (Φ i) (Ω i)) ∧
        (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω i, ∀ w' ∈ Ω i, c * ‖w - w'‖ ≤ ‖Φ i w - Φ i w'‖) ∧
        (∀ i, ContDiff ℝ 1 (h i)) ∧ (∀ i, MeasurableSet (W i)) ∧ (∀ i, W i ⊆ M) ∧
        (∀ i, W i ⊆ Φ i '' Ω i) ∧ Pairwise (Function.onFun Disjoint W) ∧
        (μHE[m + 1] : Measure (Eucl P)) (M \ ⋃ i, W i) = 0 ∧
        ∀ i, ∀ w ∈ Ω i, Φ i w ∈ W i → f (Φ i w) = h i w ∧
          G (Φ i w) ∈ LinearMap.range (fderiv ℝ (Φ i) w).toLinearMap ∧
          ∀ u, inner ℝ (G (Φ i w)) (fderiv ℝ (Φ i) w u) = fderiv ℝ (h i) w u := by
  intro P m U M θ ξ f L G hU hT hf hTG
  -- Step 1: `C¹` charts `Φ j`, Lipschitz and antilipschitz (hence injective) on the open `Ω j`,
  -- covering `M` up to an `Hⁿ`-null set.
  obtain ⟨Φ, Ω, hΩ, hΦ, hΦK, hΦc, hcov⟩ :=
    Submission.slicing_im_coarea_chart_cover P (m + 1) M hT.countablyRectifiable
  choose K hK using hΦK
  choose c hc0 hc using hΦc
  have hinj : ∀ j, InjOn (Φ j) (Ω j) := by
    intro j w hw w' hw' hww'
    have h1 := hc j w hw w' hw'
    rw [hww', sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra hne
      exact absurd h1 (not_le.mpr (mul_pos (hc0 j) (not_le.mp hne)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- Step 2: the McShane extension `u j` of `f ∘ Φ j|Ω j` agrees, together with its derivative,
  -- with a `C¹` function `H j k` on a closed `A' j k` with `Lⁿ(ℝⁿ ∖ A' j k) < k⁻¹`.
  have hfΦ : ∀ j, LipschitzOnWith (L * K j) (f ∘ Φ j) (Ω j) := fun j =>
    hf.comp_lipschitzOnWith (hK j)
  choose u hu hfu using fun j => (hfΦ j).extend_real
  choose A' H hA' hA'c hH hAH using fun j (k : ℕ) =>
    Submission.slicing_im_coarea_c1_approx (m + 1) (u j) (L * K j) (hu j) ((k : ℝ≥0∞)⁻¹)
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  have hstep2 : ∀ j k, ∀ w ∈ Ω j, w ∈ A' j k →
      f (Φ j w) = H j k w ∧ HasFDerivAt (f ∘ Φ j) (fderiv ℝ (H j k) w) w := by
    intro j k w hw hwA
    obtain ⟨huH, hder⟩ := hAH j k w hwA
    refine ⟨(hfu j hw).trans huH, hder.congr_of_eventuallyEq ?_⟩
    filter_upwards [(hΩ j).mem_nhds hw] with y hy using hfu j hy
  -- Step 3: Borel `Hⁿ`-null sets `Z₁ j` (tangent planes on the chart `Φ j`) and `Z₂`
  -- (tangential gradient) off which the a.e. statements hold, and a Borel kernel `B ⊆ M`.
  have hnull : ∀ (S : Set (Eucl P)) (p : Eucl P → Prop),
      (∀ᵐ y ∂((μHE[m + 1] : Measure (Eucl P)).restrict S), p y) →
      ∃ Z : Set (Eucl P), MeasurableSet Z ∧ (μHE[m + 1] : Measure (Eucl P)) Z = 0 ∧
        ∀ y ∈ S, y ∉ Z → p y := by
    intro S p hp
    refine ⟨toMeasurable (μHE[m + 1] : Measure (Eucl P)) ({y | ¬ p y} ∩ S),
      measurableSet_toMeasurable _ _, ?_, fun y hyS hyZ => ?_⟩
    · rw [measure_toMeasurable]
      exact nonpos_iff_eq_zero.mp
        ((Measure.le_restrict_apply S {y | ¬ p y}).trans (ae_iff.mp hp).le)
    · by_contra hpy
      exact hyZ (subset_toMeasurable _ _ ⟨hpy, hyS⟩)
  choose Z1 hZ1m hZ1 hZ1p using fun j => hnull _ _
    (Submission.slicing_im_coarea_chart_tangent P (m + 1) U M θ (Φ j) (Ω j) hU hT.subset
      hT.nullMeasurableSet hT.pos hT.integrableOn (hΩ j) (hΦ j) ⟨c j, hc0 j, hc j⟩)
  obtain ⟨Z2, hZ2m, hZ2, hZ2p⟩ := hnull _ _ hTG
  obtain ⟨B, hBM, hBm, hBae⟩ := hT.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hMB : (μHE[m + 1] : Measure (Eucl P)) (M \ B) = 0 := (ae_eq_set.mp hBae).2
  -- Step 4: off `Z₁ j ∪ Z₂`, `range DΦ j(w)` is a tangent plane at `Φ j w`, so it contains
  -- `G(Φ j w)`, and the derivatives of `s ↦ f(Φ j w + s DΦ j(w) v)` at `0` give
  -- `⟨G(Φ j w), DΦ j(w) v⟩ = DH j k(w) v`.
  have hgrad : ∀ j k, ∀ w ∈ Ω j, w ∈ A' j k → Φ j w ∈ M → Φ j w ∉ Z1 j → Φ j w ∉ Z2 →
      G (Φ j w) ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap ∧
        ∀ v, inner ℝ (G (Φ j w)) (fderiv ℝ (Φ j) w v) = fderiv ℝ (H j k) w v := by
    intro j k w hw hwA hxM hx1 hx2
    obtain ⟨hGQ, hGd⟩ :=
      hZ2p (Φ j w) hxM hx2 _ (hZ1p j (Φ j w) ⟨hxM, w, hw, rfl⟩ hx1 w hw rfl)
    refine ⟨hGQ, fun v => ?_⟩
    have hder := (hstep2 j k w hw hwA).2
    have hline := Submission.slicing_im_coarea_line_deriv (m + 1) P f (Φ j) w
      ⟨L, univ, univ_mem, hf.lipschitzOnWith⟩ ((hΦ j).differentiable one_ne_zero w)
      hder.differentiableAt v
    rw [hder.fderiv] at hline
    exact (hGd _ (LinearMap.mem_range_self _ v)).unique hline
  -- Step 5: the pieces are the disjointification of `V (j, k)`, enumerated by `Nat.unpair`.
  obtain ⟨V, hV⟩ : ∃ V : ℕ → Set (Eucl P), ∀ i, V i =
      (B ∩ Φ (Nat.unpair i).1 '' (Ω (Nat.unpair i).1 ∩ A' (Nat.unpair i).1 (Nat.unpair i).2)) \
        (Z1 (Nat.unpair i).1 ∪ Z2) := ⟨_, fun _ => rfl⟩
  have hVm : ∀ i, MeasurableSet (V i) := by
    intro i
    rw [hV]
    refine (hBm.inter ?_).diff ((hZ1m _).union hZ2m)
    -- Lusin–Souslin: `Φ j` is continuous and injective on the Borel set `Ω j ∩ A' j k`.
    exact ((hΩ _).measurableSet.inter (hA' _ _).measurableSet).image_of_continuousOn_injOn
      (hΦ _).continuous.continuousOn ((hinj _).mono inter_subset_left)
  refine ⟨fun i => Φ (Nat.unpair i).1, fun i => Ω (Nat.unpair i).1,
    fun i => H (Nat.unpair i).1 (Nat.unpair i).2, disjointed V,
    fun i => hΩ _, fun i => hΦ _, fun i => ⟨K _, hK _⟩, fun i => ⟨c _, hc0 _, hc _⟩,
    fun i => hH _ _, MeasurableSet.disjointed hVm, fun i => ?_, fun i => ?_,
    disjoint_disjointed V, ?_, fun i w hw hwW => ?_⟩
  · refine (disjointed_subset V i).trans fun x hx => ?_
    rw [hV] at hx
    exact hBM hx.1.1
  · refine (disjointed_subset V i).trans fun x hx => ?_
    rw [hV] at hx
    exact image_mono inter_subset_left hx.1.2
  · -- Step 6: `M ∖ ⋃ V` lies in a countable union of `Hⁿ`-null sets.
    rw [iUnion_disjointed]
    refine measure_mono_null (t := (M \ B) ∪ (M \ ⋃ j, Φ j '' Ω j) ∪
      (⋃ j, Φ j '' (Ω j \ ⋃ k, A' j k)) ∪ (⋃ j, Z1 j) ∪ Z2) ?_ ?_
    · rintro x ⟨hxM, hxV⟩
      by_cases hxB : x ∈ B
      swap
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hxM, hxB⟩)))
      by_cases hxΦ : x ∈ ⋃ j, Φ j '' Ω j
      swap
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hxM, hxΦ⟩)))
      obtain ⟨j, w, hw, rfl⟩ := mem_iUnion.mp hxΦ
      by_cases hwA : w ∈ ⋃ k, A' j k
      swap
      · exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨j, w, ⟨hw, hwA⟩, rfl⟩)))
      obtain ⟨k, hk⟩ := mem_iUnion.mp hwA
      by_cases hx1 : Φ j w ∈ Z1 j
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨j, hx1⟩))
      by_cases hx2 : Φ j w ∈ Z2
      · exact Or.inr hx2
      refine absurd (mem_iUnion.mpr ⟨Nat.pair j k, ?_⟩) hxV
      rw [hV, Nat.unpair_pair]
      exact ⟨⟨hxB, w, ⟨hw, hk⟩, rfl⟩, fun h => h.elim hx1 hx2⟩
    · refine measure_union_null (measure_union_null (measure_union_null
        (measure_union_null hMB hcov) (measure_iUnion_null fun j => ?_))
        (measure_iUnion_null hZ1)) hZ2
      -- `Lⁿ(Ω j ∖ ⋃ k, A' j k) ≤ Lⁿ(ℝⁿ ∖ A' j k) < k⁻¹` for every `k`.
      have hvol : (volume : Measure (Eucl (m + 1))) (Ω j \ ⋃ k, A' j k) = 0 := by
        by_contra hne
        obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hne
        have hsub : Ω j \ ⋃ k, A' j k ⊆ (A' j k)ᶜ := fun w hw hwA =>
          hw.2 (mem_iUnion.mpr ⟨k, hwA⟩)
        exact lt_irrefl _ (((measure_mono hsub).trans_lt (hA'c j k)).trans hk)
      -- The Lipschitz image of an `Hⁿ`-null set is `Hⁿ`-null.
      have himg := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
        (m + 1) ((hK j).mono (Set.sdiff_subset : Ω j \ ⋃ k, A' j k ⊆ Ω j))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1), hvol, mul_zero] at himg
      exact nonpos_iff_eq_zero.mp himg
  · -- `w` is the unique preimage in `Ω j` of `Φ j w ∈ V (j, k)`, so `w ∈ A' j k`.
    have hwV := disjointed_subset V i hwW
    rw [hV] at hwV
    obtain ⟨⟨hxB, w', hw'A, hw'w⟩, hZ⟩ := hwV
    obtain rfl : w = w' := (hinj _ hw'A.1 hw hw'w).symm
    exact ⟨(hstep2 _ _ w hw hw'A.2).1,
      hgrad _ _ w hw hw'A.2 (hBM hxB) (fun h => hZ (Or.inl h)) (fun h => hZ (Or.inr h))⟩

/-- Slices of the critical part of a `C¹` chart piece are `Hᵐ`-null for a.e. level (Simon Ch. 2,
6.3–6.4, via Eilenberg's inequality).  Put `E₀ = Ω ∩ Φ⁻¹(W)`, so that `W = Φ(E₀)` and `Dh = 0` on
`E₀`.  For `R ∈ ℕ` and `ε > 0`, `slicing_im_coarea_cc_small_lip_partition` splits
`E₀ ∩ B(0, R)` into disjoint Borel pieces `D k` on which `h` is `ε`-Lipschitz.  As `f ∘ Φ = h` on
`E₀` and `c |w - w'| ≤ |Φ w - Φ w'|`, `f` is `ε c⁻¹`-Lipschitz on `Φ(D k)`, so Eilenberg's
inequality `slicing_im_coarea_eilenberg` dominates the slices of `Φ(D k)` by `φ k` with
`∫ φ k ≤ C ε c⁻¹ Hⁿ(Φ(D k)) ≤ C ε c⁻¹ Kⁿ Lⁿ(D k)`; these sum to at most
`ε · C c⁻¹ Kⁿ Lⁿ(B(0, R))`.  Hence `slicing_im_coarea_cc_null_of_small_majorants` makes the
slices of `Φ(E₀ ∩ B(0, R))` null for a.e. level, and `W = ⋃_R Φ(E₀ ∩ B(0, R))`. -/
theorem Submission.slicing_im_coarea_chart_critical :
    ∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ)
      (f : Eucl P → ℝ) (W : Set (Eucl P)), IsOpen Ω → ContDiff ℝ 1 Φ →
      (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) →
      (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      ContDiff ℝ 1 h → MeasurableSet W → W ⊆ Φ '' Ω →
      (∀ w ∈ Ω, Φ w ∈ W → f (Φ w) = h w ∧ fderiv ℝ h w = 0) →
      ∀ᵐ t ∂(volume : Measure ℝ), (μHE[m] : Measure (Eucl P)) (W ∩ f ⁻¹' {t}) = 0 := by
  rintro P m Φ Ω h f W hΩ hΦ ⟨K, hK⟩ ⟨c, hc0, hc⟩ hh hW hWΦ hfh
  lift c to ℝ≥0 using hc0.le
  obtain ⟨C, hC⟩ := Submission.slicing_im_coarea_eilenberg m
  -- For each radius `R`, the slices of `Φ(E₀ ∩ B(0, R))` are null for a.e. level.
  have hR : ∀ R : ℕ, ∀ᵐ t ∂(volume : Measure ℝ),
      (μHE[m] : Measure (Eucl P)) (Φ '' (Ω ∩ Φ ⁻¹' W ∩ ball 0 R) ∩ f ⁻¹' {t}) = 0 := by
    intro R
    refine Submission.slicing_im_coarea_cc_null_of_small_majorants (Eucl P) μHE[m] f
      (Φ '' (Ω ∩ Φ ⁻¹' W ∩ ball 0 R))
      (((C * c⁻¹ * K ^ (m + 1) : ℝ≥0) : ℝ≥0∞) * volume (ball (0 : Eucl (m + 1)) R))
      (ENNReal.mul_ne_top ENNReal.coe_ne_top measure_ball_lt_top.ne) fun ε hε => ?_
    -- Disjoint Borel pieces `D k` of `E₀ ∩ B(0, R)` on which `h` is `ε`-Lipschitz.
    obtain ⟨D, hDm, hDdisj, hDU, hDlip⟩ :=
      Submission.slicing_im_coarea_cc_small_lip_partition (m + 1) h (Ω ∩ Φ ⁻¹' W ∩ ball 0 R) ε hh
        ((hΩ.measurableSet.inter (hW.preimage hΦ.continuous.measurable)).inter measurableSet_ball)
        (fun w hw => (hfh w hw.1.1 hw.1.2).2) hε
    have hDE : ∀ k, D k ⊆ Ω ∩ Φ ⁻¹' W ∩ ball 0 R := fun k => hDU ▸ subset_iUnion D k
    -- `f = h ∘ Φ⁻¹` is `ε c⁻¹`-Lipschitz on `Φ(D k)`.
    have hflip : ∀ k, LipschitzOnWith (ε * c⁻¹) f (Φ '' D k) := by
      intro k
      refine LipschitzOnWith.of_dist_le_mul ?_
      rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      obtain ⟨⟨hwΩ, hwW⟩, -⟩ := hDE k hw
      obtain ⟨⟨hw'Ω, hw'W⟩, -⟩ := hDE k hw'
      rw [(hfh w hwΩ hwW).1, (hfh w' hw'Ω hw'W).1]
      have hcw : (c : ℝ) * dist w w' ≤ dist (Φ w) (Φ w') := by
        simpa only [dist_eq_norm] using hc w hwΩ w' hw'Ω
      calc dist (h w) (h w') ≤ ε * dist w w' := (hDlip k).dist_le_mul w hw w' hw'
        _ ≤ ε * ((c : ℝ)⁻¹ * dist (Φ w) (Φ w')) := by
          gcongr
          rw [inv_mul_eq_div, le_div_iff₀ hc0, mul_comm]
          exact hcw
        _ = ((ε * c⁻¹ : ℝ≥0) : ℝ) * dist (Φ w) (Φ w') := by push_cast; ring
    -- Eilenberg's inequality on each `Φ(D k)`, and `Hⁿ(Φ(D k)) ≤ Kⁿ Lⁿ(D k)`.
    choose φ hφm hφle hφint using fun k => hC P f (ε * c⁻¹) (Φ '' D k) (hflip k)
    refine ⟨fun k => Φ '' D k, φ, ?_, hφm, hφle, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      rw [← hDU] at hw
      obtain ⟨k, hk⟩ := mem_iUnion.1 hw
      exact mem_iUnion.2 ⟨k, mem_image_of_mem Φ hk⟩
    · calc ∑' k, ∫⁻ t, φ k t
          ≤ ∑' k, (C : ℝ≥0∞) * ((ε * c⁻¹ : ℝ≥0) : ℝ≥0∞) *
              ((K : ℝ≥0∞) ^ (m + 1) * volume (D k)) := by
            refine ENNReal.tsum_le_tsum fun k => (hφint k).trans ?_
            rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
            gcongr
            exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
              (m + 1) (hK.mono fun w hw => (hDE k hw).1.1)
        _ = (C : ℝ≥0∞) * ((ε * c⁻¹ : ℝ≥0) : ℝ≥0∞) * (K : ℝ≥0∞) ^ (m + 1) *
              volume (Ω ∩ Φ ⁻¹' W ∩ ball 0 R) := by
            simp_rw [← mul_assoc]
            rw [ENNReal.tsum_mul_left, ← measure_iUnion hDdisj hDm, hDU]
        _ ≤ (C : ℝ≥0∞) * ((ε * c⁻¹ : ℝ≥0) : ℝ≥0∞) * (K : ℝ≥0∞) ^ (m + 1) *
              volume (ball (0 : Eucl (m + 1)) R) := by
            gcongr
            exact inter_subset_right
        _ = (ε : ℝ≥0∞) *
              (((C * c⁻¹ * K ^ (m + 1) : ℝ≥0) : ℝ≥0∞) * volume (ball (0 : Eucl (m + 1)) R)) := by
            push_cast
            ring
  -- `W = ⋃_R Φ(E₀ ∩ B(0, R))`, so its slices are null for a.e. level.
  filter_upwards [ae_all_iff.2 hR] with t ht
  refine measure_mono_null ?_ (measure_iUnion_null ht)
  rintro _ ⟨hxW, hxt⟩
  obtain ⟨w, hwΩ, rfl⟩ := hWΦ hxW
  obtain ⟨R, hwR⟩ := exists_nat_gt ‖w‖
  exact mem_iUnion.2 ⟨R, ⟨w, ⟨⟨hwΩ, hxW⟩, mem_ball_zero_iff.2 hwR⟩, rfl⟩, hxt⟩

/-- Co-area formula on a regular injective `C¹` chart (Simon Ch. 3, 2.9 for real-valued `f` on
`M = Φ(Ω)`; the last part of Ch. 6, Lemma 4.1): let `Φ` be `C¹`, Lipschitz and antilipschitz on
the open `Ω ⊆ ℝⁿ`, `W ⊆ Φ(Ω)` Borel, and on `Ω ∩ Φ⁻¹(W)` let `G ≠ 0` be the tangential gradient
of `f` along `Φ`: `f ∘ Φ = h`, `G(Φw) ∈ range DΦ(w)` and `⟨G(Φw), DΦ(w)u⟩ = Dh(w)u`.  Then
`t ↦ ∫_{W ∩ f⁻¹{t}} g dH^m` is a.e.-measurable and `∫ ∫_{W ∩ f⁻¹{t}} g dH^m dt = ∫_W |G| g dHⁿ`.
Every `w₀ ∈ Ω ∩ Φ⁻¹(W)` is a regular point of `h`, so `h` is straightened by a chart `χ` with
`w₀ ∈ χ(B)`; on Borel subsets of `χ(B)` the identity holds by the box co-area lemma, and the
local-to-global lemma glues these pieces. -/
theorem Submission.slicing_im_coarea_chart_regular : ∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (W : Set (Eucl P)), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ContDiff ℝ 1 h → Measurable f → Measurable G → MeasurableSet W → W ⊆ Φ '' Ω → (∀ w ∈ Ω, Φ w ∈ W → f (Φ w) = h w ∧ G (Φ w) ≠ 0 ∧ G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u, inner ℝ (G (Φ w)) (fderiv ℝ Φ w u) = fderiv ℝ h w u) → ∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in W ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in W, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P)) := by
  intro P m Φ Ω h f G W hΩ hΦ hK hc hh hf hG hW hWΩ hpt g hg
  -- Step 1: `Φ` is continuous and, being antilipschitz, injective on `Ω`.
  have hinj : InjOn Φ Ω := by
    obtain ⟨c, hc0, hcΦ⟩ := hc
    intro w hw w' hw' heq
    have h1 := hcΦ w hw w' hw'
    rw [heq, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc0 (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- Step 6: by the local-to-global lemma (Lindelöf cover and gluing), it suffices to give every
  -- `w₀ ∈ Ω ∩ Φ⁻¹(W)` an open neighbourhood `O` such that the co-area identity holds for `Φ(S)`,
  -- for every Borel `S ⊆ O ∩ Ω ∩ Φ⁻¹(W)`.
  refine Submission.slicing_im_creg_local_to_global P (m + 1) Φ Ω W f (fun x => ‖G x‖ₑ) g
    (μHE[m + 1] : Measure (Eucl P)) (μHE[m] : Measure (Eucl P)) hΩ hΦ.continuous hinj hf hW hWΩ
    fun w₀ hw₀ hw₀W => ?_
  -- Step 1: `w₀` is a regular point of `h`: writing `G(Φw₀) = DΦ(w₀)u₀`,
  -- `Dh(w₀)u₀ = ⟨G(Φw₀), DΦ(w₀)u₀⟩ = |G(Φw₀)|² ≠ 0`.
  obtain ⟨-, hG0, hrange, hinner⟩ := hpt w₀ hw₀ hw₀W
  obtain ⟨u₀, hu₀⟩ := LinearMap.mem_range.mp hrange
  rw [ContinuousLinearMap.coe_coe] at hu₀
  have hDh : fderiv ℝ h w₀ ≠ 0 := by
    intro h0
    have h1 := hinner u₀
    rw [hu₀, h0] at h1
    exact hG0 (inner_self_eq_zero.mp h1)
  -- Step 2: straighten `h` near `w₀`: a `C¹` chart `χ` on the open `B` with `h (χ y) = y 0`
  -- and `w₀ ∈ χ(B) ⊆ Ω`, `χ(B)` open.
  obtain ⟨B, χ, hB, hχ, hχB, hw₀B, hχΩ, hΛ, hhχ, hslice⟩ :=
    Submission.slicing_im_creg_straightening m h Ω w₀ hΩ hw₀ hh hDh
  -- Steps 3–5: on Borel `S ⊆ χ(B) ∩ Ω ∩ Φ⁻¹(W)` the box co-area identity applies; its pointwise
  -- hypotheses are those of the theorem without `G ≠ 0`.
  refine ⟨χ '' B, hχB, hw₀B, fun S hS hSsub => ?_⟩
  refine Submission.slicing_im_creg_box_coarea P m Φ Ω h f G B χ S hΩ hΦ hK hc hh hG hB hχ hχΩ
    hΛ hhχ hslice hS (fun w hw => (hSsub hw).1) (fun w hw => ?_) g hg
  obtain ⟨hfw, -, hGw, hinw⟩ := hpt w (hSsub hw).2.1 (hSsub hw).2.2
  exact ⟨hfw, hGw, hinw⟩

/-- Simon Ch. 3, (2.8)–(2.9) for a real-valued Lipschitz `f` on the carrier `M` of a rectifiable
triple (`n = m + 1`): if `G` is a Borel tangential gradient of `f` on `M`, then for every Borel
`g ≥ 0` the function `t ↦ ∫_{M ∩ f⁻¹{t}} g dH^m` is a.e.-measurable and
`∫_ℝ ∫_{M ∩ f⁻¹{t}} g dH^m dt = ∫_M |G| g dHⁿ`.

`M` is cut into disjoint Borel chart pieces `W i` (`slicing_im_coarea_pieces`) covering `M` up to
an `Hⁿ`-null set `Z`. The co-area formula holds on the regular parts `W i ∩ {G ≠ 0}`
(`slicing_im_coarea_chart_regular`). The slices of the critical parts `W i ∩ {G = 0}`
(`slicing_im_coarea_chart_critical`) and of `Z` (`slicing_im_coarea_eilenberg`) are `H^m`-null
for a.e. `t`, and `|G| g = 0` on the critical parts, so the regular parts glue to the
statement on `M` (`slicing_im_coarea_glue`). -/
theorem Submission.slicing_im_coarea :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1))
      (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U →
      IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f → Measurable G →
      (∀ x, ‖G x‖ ≤ L) →
      (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
          G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) →
      ∀ g : Eucl P → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
            (volume : Measure ℝ) ∧
          ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
              ∂(volume : Measure ℝ) =
            ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P)) := by
  intro P m U M θ ξ f L G hU hT hf hG _hGL hTG g hg
  have hfm : Measurable f := hf.continuous.measurable
  have hG0 : MeasurableSet {x : Eucl P | G x = 0} := hG (measurableSet_singleton 0)
  -- Steps 1–4: disjoint Borel chart pieces `W i ⊆ M` with `Hⁿ(M \ ⋃ i, W i) = 0`, on which
  -- `f ∘ Φ i = h i` and `G` represents `D(h i)` through `DΦ i`.
  obtain ⟨Φ, Ω, h, W, hΩ, hΦ, hΦL, hΦc, hh, hWm, hWM, hWΦ, hWd, hZ, hW⟩ :=
    Submission.slicing_im_coarea_pieces P m U M θ ξ f L G hU hT hf hTG
  -- Steps 5–7: glue the regular parts `W i ∩ {G ≠ 0}`; the rest of `M` is `Z ∪ ⋃ i, W i ∩ {G = 0}`.
  refine Submission.slicing_im_coarea_glue (Eucl P) (μHE[m + 1] : Measure (Eucl P))
    (μHE[m] : Measure (Eucl P)) f (fun x => ‖G x‖ₑ) g M (fun i => W i ∩ {x | G x ≠ 0}) hfm
    (fun i => (hWm i).inter hG0.compl) (fun i => inter_subset_left.trans (hWM i))
    (fun i j hij => Disjoint.mono inter_subset_left inter_subset_left (hWd hij)) ?_ ?_ ?_
  · -- `|G| g` vanishes off `Z` on the remainder, since there `G = 0`.
    have hmeas : MeasurableSet {x : Eucl P | ¬ (‖G x‖ₑ * g x = 0)} :=
      ((hG.enorm.mul hg) (measurableSet_singleton 0)).compl
    rw [ae_iff, Measure.restrict_apply hmeas]
    refine measure_mono_null ?_ hZ
    rintro x ⟨hx0, hxM, hxW'⟩
    refine ⟨hxM, fun hxW => ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxW
    exact hxW' (mem_iUnion.mpr ⟨i, hi, fun hGx => hx0 (by rw [hGx, enorm_zero, zero_mul])⟩)
  · -- Eilenberg's inequality on the `Hⁿ`-null set `Z = M \ ⋃ i, W i`.
    obtain ⟨C, hC⟩ := Submission.slicing_im_coarea_eilenberg m
    obtain ⟨φ, hφm, hφ, hφi⟩ := hC P f L (M \ ⋃ i, W i) hf.lipschitzOnWith
    have hφ0 : φ =ᵐ[volume] 0 := by
      rw [← lintegral_eq_zero_iff hφm]
      exact nonpos_iff_eq_zero.mp (hφi.trans_eq (by rw [hZ, mul_zero]))
    -- On the critical parts `D(h i) = 0`, because `⟪0, DΦ i w u⟫ = D(h i) w u`.
    have hcrit : ∀ᵐ t ∂(volume : Measure ℝ), ∀ i,
        (μHE[m] : Measure (Eucl P)) ((W i ∩ {x | G x = 0}) ∩ f ⁻¹' {t}) = 0 :=
      ae_all_iff.mpr fun i =>
        Submission.slicing_im_coarea_chart_critical P m (Φ i) (Ω i) (h i) f
          (W i ∩ {x | G x = 0}) (hΩ i) (hΦ i) (hΦL i) (hΦc i) (hh i) ((hWm i).inter hG0)
          (inter_subset_left.trans (hWΦ i)) fun w hw hwW =>
            ⟨(hW i w hw hwW.1).1, ContinuousLinearMap.ext fun u => by
              rw [zero_apply, ← (hW i w hw hwW.1).2.2 u,
                show G (Φ i w) = 0 from hwW.2, inner_zero_left]⟩
    filter_upwards [hφ0, hcrit] with t ht hct
    have hZt : (μHE[m] : Measure (Eucl P)) ((M \ ⋃ i, W i) ∩ f ⁻¹' {t}) = 0 :=
      nonpos_iff_eq_zero.mp ((hφ t).trans_eq ht)
    refine measure_mono_null ?_ (measure_union_null hZt (measure_iUnion_null hct))
    rintro x ⟨⟨hxM, hxW⟩, hxt⟩
    by_cases hx : x ∈ ⋃ i, W i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine Or.inr (mem_iUnion.mpr ⟨i, ⟨hi, ?_⟩, hxt⟩)
      by_contra hGx
      exact hxW (mem_iUnion.mpr ⟨i, hi, hGx⟩)
    · exact Or.inl ⟨⟨hxM, hx⟩, hxt⟩
  · -- Step 6: the co-area formula on every regular part.
    exact fun i => Submission.slicing_im_coarea_chart_regular P m (Φ i) (Ω i) (h i) f G
      (W i ∩ {x | G x ≠ 0}) (hΩ i) (hΦ i) (hΦL i) (hΦc i) (hh i) hfm hG
      ((hWm i).inter hG0.compl) (inter_subset_left.trans (hWΦ i))
      (fun w hw hwW => ⟨(hW i w hw hwW.1).1, hwW.2, (hW i w hw hwW.1).2⟩) g hg

/-- For `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)` and `w ∈ Ω` with `Φ w = y`, `DΦ(w)(ℝⁿ)` is the approximate
tangent space of `M` with multiplicity `θ` at `y` (Simon Ch. 3, proof of 1.6 and Remark 1.8(1),
for one `C¹` chart `Φ` that is antilipschitz on the open set `Ω`). -/
theorem Submission.lpf_weighted_tangent_on_c1_chart :
    ∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)),
      IsOpen V → M ⊆ V → NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) →
      (∀ y ∈ M, 0 < θ y) →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
        IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) →
      IsOpen Ω → ContDiff ℝ 1 Φ →
      (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) →
      ∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict (M ∩ Φ '' Ω)), ∀ w ∈ Ω, Φ w = y →
        HasWeightedApproximateTangentSpaceAt n M θ y
          (LinearMap.range (fderiv ℝ Φ w).toLinearMap) := by
  intro Q n V M θ Φ Ω hV hMV hM hθ hθK hΩ hΦ hanti
  -- `N := Φ(Ω)` is Borel and locally `Hⁿ`-finite.
  obtain ⟨hN, hNK⟩ :=
    Submission.lpf_wtc_chart_image_measurable_locally_finite Q n Φ Ω hΩ hΦ hanti
  -- Compact pieces `C k ⊆ M`, `θ|C k` continuous, `Hⁿ(C k) < ∞`, covering `M` up to a null set.
  obtain ⟨C, hCc, hCM, hθC, hCfin, hMC⟩ :=
    Submission.lpf_wtc_lusin_compact_pieces Q n V M θ hV hMV hM hθ hθK
  have hCm : ∀ k, MeasurableSet (C k) := fun k => (hCc k).isClosed.measurableSet
  -- Zero `n`-density of `Hⁿ ⌞ (C k ∖ N)`, `Hⁿ ⌞ (N ∖ C k)` and `θ Hⁿ ⌞ (M ∖ C k)` off these sets.
  have h₁ := fun k => Submission.lpf_wtc_ae_zero_density_off_set Q n univ (C k \ Φ '' Ω)
    (fun _ => 1) isOpen_univ ((hCm k).diff hN).nullMeasurableSet fun K _ _ => by
      simp only [setLIntegral_one]
      exact (measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt (hCfin k)
  have h₂ := fun k => Submission.lpf_wtc_ae_zero_density_off_set Q n univ (Φ '' Ω \ C k)
    (fun _ => 1) isOpen_univ (hN.diff (hCm k)).nullMeasurableSet fun K hK _ => by
      simp only [setLIntegral_one]
      exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hNK K hK)
  have h₃ := fun k => Submission.lpf_wtc_ae_zero_density_off_set Q n V (M \ C k)
    (fun x => ENNReal.ofReal (θ x)) hV (hM.diff (hCm k).nullMeasurableSet) fun K hK hKV =>
      (lintegral_mono_set (inter_subset_inter_left K sdiff_subset)).trans_lt
        (hθK K hK hKV).setLIntegral_lt_top
  have hall := ae_all_iff.2 fun k => (h₁ k).and ((h₂ k).and (h₃ k))
  rw [ae_restrict_iff'₀ (hM.inter hN.nullMeasurableSet)]
  filter_upwards [hall, measure_eq_zero_iff_ae_notMem.1 hMC] with y hy hyC hyMN w hw hwy
  subst hwy
  obtain ⟨k, hyk⟩ : ∃ k, Φ w ∈ C k := by
    by_contra h
    exact hyC ⟨hyMN.1, fun h' => h (mem_iUnion.1 h')⟩
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy k
  -- `N` has approximate tangent space `T = DΦ(w)(ℝⁿ)` at `Φ w`, and so does `C k`.
  have hCT := Submission.lpf_wtc_tangent_transfer Q n (C k) (Φ '' Ω) (Φ w) _
    (hCm k).nullMeasurableSet hN.nullMeasurableSet
    (Submission.lpf_wtc_chart_approx_tangent Q n Φ Ω hΩ hΦ hanti w hw)
    ⟨1, one_pos, hNK _ (isCompact_closedBall _ _)⟩
    (by simpa only [setLIntegral_one] using hy₁ (mem_univ _) fun h => h.2 hyMN.2)
    (by simpa only [setLIntegral_one] using hy₂ (mem_univ _) fun h => h.2 hyk)
  -- Transfer to `(M, θ)` on a closed ball about `Φ w` inside `V`.
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV _ (hMV hyMN.1)
  exact Submission.lpf_wtc_weighted_tangent_transfer Q n M (C k) θ (Φ w) _ hM
    (hCm k).nullMeasurableSet (hCM k) hyk (fun x hx => (hθ x hx).le) hCT
    ⟨ε / 2, half_pos hε, (measure_mono inter_subset_left).trans_lt (hCfin k),
      hθK _ (isCompact_closedBall _ _) ((closedBall_subset_ball (half_lt_self hε)).trans hεV)⟩
    ((hθC k).continuousWithinAt hyk) (hy₃ (hMV hyMN.1) fun h => h.2 hyk)
/-- Bochner change of variables through a Jacobian-weighted push-forward: if
`∫⁻ g dν = ∫⁻ g(Φ(x)) J(x) dμ(x)` for every measurable `g : Y → [0, ∞]`, then `Φ` pushes the
measure `ρ = J μ` (density `J.toNNReal`) forward to `ν`, so for `ν`-integrable `F`, `J • F ∘ Φ` is
`μ`-integrable and `∫ F dν = ∫ F(Φ(x)) dρ(x) = ∫ J(x) • F(Φ(x)) dμ(x)`.  No σ-finiteness is
needed.  This passes the area formula on a chart from nonnegative to Bochner integrands. -/
theorem Submission.slicing_im_ll_twl_cie_weighted_transfer : ∀ (X Y E : Type) [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (ν : Measure Y) (Φ : X → Y) (J : X → ℝ) (F : Y → E), AEMeasurable Φ μ → AEMeasurable J μ → (∀ x, 0 ≤ J x) → (∀ g : Y → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂ν = ∫⁻ x, g (Φ x) * ENNReal.ofReal (J x) ∂μ) → Integrable F ν → Integrable (fun x => J x • F (Φ x)) μ ∧ ∫ y, F y ∂ν = ∫ x, J x • F (Φ x) ∂μ := by
  intro X Y E _ _ _ _ _ μ ν Φ J F hΦ hJ hJ0 hcv hF
  -- The density `f = J.toNNReal` is a.e.-measurable, and `ρ = μ.withDensity f ≪ μ`, so `Φ` is
  -- `ρ`-a.e.-measurable.
  have hf : AEMeasurable (fun x => (J x).toNNReal) μ := hJ.real_toNNReal
  have hΦρ : AEMeasurable Φ (μ.withDensity fun x => ((J x).toNNReal : ℝ≥0∞)) :=
    hΦ.mono_ac (withDensity_absolutelyContinuous _ _)
  -- `Φ` pushes `ρ` forward to `ν`: test the hypothesis with `g = 1_S` for measurable `S`.
  have hmap : (μ.withDensity fun x => ((J x).toNNReal : ℝ≥0∞)).map Φ = ν := by
    refine Measure.ext fun S hS => ?_
    have hS' : NullMeasurableSet (Φ ⁻¹' S) μ := hΦ.nullMeasurableSet_preimage hS
    rw [Measure.map_apply_of_aemeasurable hΦρ hS, withDensity_apply₀ _ hS',
      ← lintegral_indicator₀ hS', ← lintegral_indicator_one (μ := ν) hS,
      hcv _ (measurable_one.indicator hS)]
    refine lintegral_congr fun x => ?_
    by_cases hx : Φ x ∈ S
    · rw [indicator_of_mem (show x ∈ Φ ⁻¹' S from hx), indicator_of_mem hx, Pi.one_apply, one_mul]
      rfl
    · rw [indicator_of_notMem (show x ∉ Φ ⁻¹' S from hx), indicator_of_notMem hx, zero_mul]
  -- Transfer along `Φ`: `F ∘ Φ` is `ρ`-integrable and `∫ F dν = ∫ F ∘ Φ dρ`.
  have hFmap : Integrable F ((μ.withDensity fun x => ((J x).toNNReal : ℝ≥0∞)).map Φ) := by
    rw [hmap]
    exact hF
  have hFρ : Integrable (fun x => F (Φ x)) (μ.withDensity fun x => ((J x).toNNReal : ℝ≥0∞)) :=
    (integrable_map_measure hFmap.aestronglyMeasurable hΦρ).mp hFmap
  have hint : ∫ y, F y ∂ν = ∫ x, F (Φ x) ∂(μ.withDensity fun x => ((J x).toNNReal : ℝ≥0∞)) := by
    rw [← integral_map hΦρ hFmap.aestronglyMeasurable, hmap]
  -- Remove the density: `f(x) • v = (f(x) : ℝ) • v = J(x) • v` because `J ≥ 0`.
  have hcoe : ∀ x, ((J x).toNNReal : ℝ) • F (Φ x) = J x • F (Φ x) := fun x => by
    rw [Real.coe_toNNReal _ (hJ0 x)]
  refine ⟨((integrable_withDensity_iff_integrable_coe_smul₀ hf).mp hFρ).congr
    (ae_of_all _ hcoe), ?_⟩
  rw [hint, integral_withDensity_eq_integral_smul₀ hf]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [NNReal.smul_def, hcoe]
/-- Measurability of the Gram-determinant Jacobian (step 2 of Simon Ch. 6, 3.9 in charts): for an
arbitrary map `Φ : ℝⁿ → ℝ^P`, `w ↦ √det(⟨DΦ(w)eᵢ, DΦ(w)eⱼ⟩)` is Borel measurable, being the
continuous map `L ↦ √det(⟨Leᵢ, Leⱼ⟩)` on `ℝⁿ →L[ℝ] ℝ^P` composed with the Borel map
`w ↦ fderiv ℝ Φ w`. -/
theorem Submission.slicing_im_ll_twl_cie_jacobian_measurable : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P), Measurable (fun w : Eucl n => Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) := by
  intro P n Φ
  -- The Gram-determinant map is continuous on `ℝⁿ →L[ℝ] ℝ^P`.
  have hG : Continuous fun L : Eucl n →L[ℝ] Eucl P => Real.sqrt (Matrix.of fun i j =>
      inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det := by
    fun_prop
  -- `w ↦ fderiv ℝ Φ w` is Borel measurable for every `Φ`.
  exact hG.measurable.comp (measurable_fderiv ℝ Φ)
/-- Countable Lipschitz cover (Lindelöf): if `f` is locally Lipschitz on an arbitrary `U ⊆ ℝ^P`,
then countably many open sets `O i` cover `U` and `f` is `K i`-Lipschitz on each `O i ∩ U`. -/
theorem Submission.lpf_lli_countable_lipschitz_cover : ∀ (P Q : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q), LocallyLipschitzOn U f → ∃ (O : ℕ → Set (Eucl P)) (K : ℕ → ℝ≥0), (∀ i, IsOpen (O i)) ∧ U ⊆ ⋃ i, O i ∧ ∀ i, LipschitzOnWith (K i) f (O i ∩ U) := by
  intro P Q U f hf
  -- Step 1: each `x ∈ U` has an open `o x ∋ x` with `f` `k x`-Lipschitz on `o x ∩ U`.
  have hloc : ∀ x ∈ U, ∃ (o : Set (Eucl P)) (k : ℝ≥0),
      IsOpen o ∧ x ∈ o ∧ LipschitzOnWith k f (o ∩ U) := by
    intro x hx
    obtain ⟨k, t, ht, hft⟩ := hf hx
    obtain ⟨o, ho, hxo, hot⟩ := mem_nhdsWithin.1 ht
    exact ⟨o, k, ho, hxo, hft.mono hot⟩
  choose! o k ho hxo hfo using hloc
  -- Step 2: `ℝ^P` is hereditarily Lindelöf, so countably many `o x` (`x ∈ T ⊆ U`) cover `U`.
  obtain ⟨T, hTc, hTU, hUT⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_nhds_subcover o
    fun x hx => (ho x hx).mem_nhds (hxo x hx)
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- Step 3: `T = ∅` forces `U = ∅`; take empty pieces.
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, fun x hx => ?_, fun _ => ?_⟩
    · simpa using hUT hx
    · simp
  · -- Step 4: enumerate `T = range g` and take `O i = o (g i)`, `K i = k (g i)`.
    obtain ⟨g, rfl⟩ := hTc.exists_eq_range hTne
    refine ⟨fun i => o (g i), fun i => k (g i), fun i => ho _ (hTU _ (mem_range_self i)),
      fun x hx => ?_, fun i => hfo _ (hTU _ (mem_range_self i))⟩
    -- Step 5: the pieces cover `U`.
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := mem_iUnion₂.1 (hUT hx)
    exact mem_iUnion.2 ⟨i, hxy⟩

/-- Disjoint Lipschitz pieces: if `u` is locally Lipschitz on an open `Ω ⊆ ℝⁿ` and `D ⊆ Ω` is
`Lⁿ`-null-measurable, then `D` is covered by pairwise disjoint null-measurable `B m ⊆ D ∩ V m`,
where the `V m ⊆ Ω` are open and `u` is `K m`-Lipschitz on `V m`. -/
theorem Submission.lpf_raf_lla_disjoint_lipschitz_pieces : ∀ (n Q : ℕ) (Ω D : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → D ⊆ Ω → NullMeasurableSet D (volume : Measure (Eucl n)) → ∃ (V B : ℕ → Set (Eucl n)) (K : ℕ → ℝ≥0), (∀ m, IsOpen (V m)) ∧ (∀ m, V m ⊆ Ω) ∧ (∀ m, LipschitzOnWith (K m) u (V m)) ∧ (∀ m, B m ⊆ D ∩ V m) ∧ Pairwise (Function.onFun Disjoint B) ∧ (∀ m, NullMeasurableSet (B m) (volume : Measure (Eucl n))) ∧ D ⊆ ⋃ m, B m := by
  intro n Q Ω D u hΩ hu hDΩ hD
  -- Step 1: countable Lipschitz cover: open `O m` cover `Ω`, `u` is `K m`-Lipschitz on `O m ∩ Ω`.
  obtain ⟨O, K, hO, hΩO, hK⟩ := Submission.lpf_lli_countable_lipschitz_cover n Q Ω u hu
  -- Step 2: the open pieces `V m = O m ∩ Ω` lie in `Ω` and cover `Ω`.
  have hVo : ∀ m, IsOpen (O m ∩ Ω) := fun m => (hO m).inter hΩ
  have hΩV : Ω ⊆ ⋃ m, O m ∩ Ω := fun x hx => by
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hΩO hx)
    exact mem_iUnion.2 ⟨m, hm, hx⟩
  -- Steps 3–4: `W m = disjointed V m` and `B m = D ∩ W m`.
  refine ⟨fun m => O m ∩ Ω, fun m => D ∩ disjointed (fun m => O m ∩ Ω) m, K, hVo,
    fun m => inter_subset_right, hK,
    fun m => inter_subset_inter_right D (disjointed_subset (fun m => O m ∩ Ω) m),
    fun i j hij => Disjoint.mono inter_subset_right inter_subset_right
      (disjoint_disjointed (fun m => O m ∩ Ω) hij),
    fun m => hD.inter
      (MeasurableSet.disjointed (fun m => (hVo m).measurableSet) m).nullMeasurableSet,
    fun x hx => ?_⟩
  -- Step 4(d): `x ∈ D ⊆ Ω ⊆ ⋃ V m = ⋃ W m`, so `x ∈ D ∩ W m = B m` for some `m`.
  have hxW : x ∈ ⋃ m, disjointed (fun m => O m ∩ Ω) m := by
    rw [iUnion_disjointed]
    exact hΩV (hDΩ hx)
  obtain ⟨m, hm⟩ := mem_iUnion.1 hxW
  exact mem_iUnion.2 ⟨m, hx, hm⟩
/-- Countable gluing of fibre-sum area identities (Simon Ch. 3, proof of 2.6; used for Ch. 6,
3.9): if `A` is covered, up to a `μ`-null set `Z` with `ν`-null image `f '' Z`, by pairwise
disjoint `μ`-null-measurable pieces `B m ⊆ A`, each satisfying `∫_{B m} F dμ = ∫ N_{B m} dν` with
an a.e.-measurable fibre sum `N_S(y) = ∑_{x ∈ S, f x = y} h x`, then so does `A`. -/
theorem Submission.lpf_raf_fiber_sum_glue : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (f : X → Y) (h F : X → ℝ≥0∞) (A Z : Set X) (B : ℕ → Set X), (∀ m, B m ⊆ A) → Pairwise (Function.onFun Disjoint B) → (∀ m, NullMeasurableSet (B m) μ) → (A ⊆ Z ∪ ⋃ m, B m) → μ Z = 0 → ν (f '' Z) = 0 → (∀ m, AEMeasurable (fun y => ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x) ν ∧ ∫⁻ x in B m, F x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x ∂ν) → AEMeasurable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) ν ∧ ∫⁻ x in A, F x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x ∂ν := by
  intro X Y _ _ μ ν f h F A Z B hBA hdisj hBm hcov hZ hfZ hg
  -- Off `f '' Z`, the `A`-fibre is the disjoint union of the `B m`-fibres, so the sums split.
  have hpt : ∀ y ∉ f '' Z, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x =
      ∑' m, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x := by
    intro y hy
    have he : {x | x ∈ A ∧ f x = y} = ⋃ m, {x | x ∈ B m ∧ f x = y} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxA, rfl⟩
        rcases hcov hxA with hxZ | hxB
        · exact absurd ⟨x, hxZ, rfl⟩ hy
        · obtain ⟨m, hm⟩ := mem_iUnion.mp hxB
          exact ⟨m, hm, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨hBA m hm, rfl⟩
    have hd : univ.PairwiseDisjoint fun m => {x | x ∈ B m ∧ f x = y} :=
      fun i _ j _ hij => (hdisj hij).mono (fun _ hx => hx.1) (fun _ hx => hx.1)
    change ∑' x : ({x | x ∈ A ∧ f x = y} : Set X), h x =
      ∑' m, ∑' x : ({x | x ∈ B m ∧ f x = y} : Set X), h x
    rw [he]
    exact ENNReal.tsum_biUnion hd
  -- As `ν (f '' Z) = 0`, the fibre sums agree `ν`-a.e.; this gives a.e.-measurability.
  have hae : (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) =ᵐ[ν]
      fun y => ∑' m, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfZ] with y hy using hpt y hy
  refine ⟨(AEMeasurable.tsum fun m => (hg m).1).congr hae.symm, ?_⟩
  -- `A` and `⋃ m, B m` differ by a subset of the `μ`-null set `Z`.
  have hAe : A =ᵐ[μ] ⋃ m, B m := by
    refine ae_eq_set.mpr ⟨measure_mono_null ?_ hZ, ?_⟩
    · rintro x ⟨hxA, hxB⟩
      exact (hcov hxA).resolve_right hxB
    · rw [sdiff_eq_empty.mpr (iUnion_subset hBA), measure_empty]
  -- Sum the identities over `m` on both sides.
  rw [Measure.restrict_congr_set hAe, lintegral_iUnion₀ hBm hdisj.aedisjoint F,
    lintegral_congr_ae hae, lintegral_tsum fun m => (hg m).1]
  exact tsum_congr fun m => (hg m).2

/-- Area formula for a map locally Lipschitz on an open set (Simon Ch. 2, (3.5), localized by the
countable decomposition of the proof of Ch. 3, 2.4–2.5; used for Ch. 6, 3.9): if `u` is locally
Lipschitz on open `Ω ⊆ ℝⁿ`, `D ⊆ Ω` is `Lⁿ`-null-measurable and `w ≥ 0` is `Lⁿ ⌞ D`-a.e.
measurable, then the fibre sum `N(y) = ∑_{x ∈ D, u x = y} w x` is `Hⁿ`-a.e. measurable and
`∫_D w Ju dLⁿ = ∫ N dHⁿ`, where `Ju = √det(⟨Du eᵢ, Du eⱼ⟩)`.  Split `D` into disjoint pieces
`B m` inside open `V m ⊆ Ω` on which `u` is Lipschitz, apply SimonGMT's area formula for maps
Lipschitz on a set to each piece (its within-derivative Jacobian is `Ju` a.e. on `B m`, via a
Lipschitz extension of `u|V m`), and glue the pieces. -/
theorem Submission.lpf_raf_local_lipschitz_area : ∀ (n Q : ℕ) (Ω D : Set (Eucl n)) (u : Eucl n → Eucl Q) (w : Eucl n → ℝ≥0∞), IsOpen Ω → LocallyLipschitzOn Ω u → D ⊆ Ω → NullMeasurableSet D (volume : Measure (Eucl n)) → AEMeasurable w ((volume : Measure (Eucl n)).restrict D) → AEMeasurable (fun y => ∑' x : {x : Eucl n // x ∈ D ∧ u x = y}, w x) (μHE[n] : Measure (Eucl Q)) ∧ ∫⁻ x in D, w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1)) (fderiv ℝ u x (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) = ∫⁻ y, ∑' x : {x : Eucl n // x ∈ D ∧ u x = y}, w x ∂(μHE[n] : Measure (Eucl Q)) := by
  intro n Q Ω D u w hΩ hu hDΩ hD hw
  -- Step 1: `normDet T = √det(⟨T eᵢ, T eⱼ⟩)`, the Gram determinant in the orthonormal basis `eᵢ`.
  have hJ : ∀ T : Eucl n →L[ℝ] Eucl Q, (T : Eucl n →ₗ[ℝ] Eucl Q).normDet =
      Real.sqrt (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1))
        (T (EuclideanSpace.single j 1))).det := by
    intro T
    have h := (T : Eucl n →ₗ[ℝ] Eucl Q).normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin n) ℝ)
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      RCLike.ofReal_real_eq_id, id_eq] at h
    rw [← Real.sqrt_sq (T : Eucl n →ₗ[ℝ] Eucl Q).normDet_nonneg, h]
    rfl
  -- Steps 2–3: pairwise disjoint null-measurable `B m ⊆ D ∩ V m` covering `D`, where `V m` is
  -- open and `u` is `K m`-Lipschitz on `V m`.
  obtain ⟨V, B, K, hVo, -, hK, hBDV, hBd, hBm, hDB⟩ :=
    Submission.lpf_raf_lla_disjoint_lipschitz_pieces n Q Ω D u hΩ hu hDΩ hD
  have hdim : Module.finrank ℝ (Eucl n) = n := finrank_euclideanSpace_fin
  -- Steps 4–5: the area formula on each piece `B m`.
  have hpiece : ∀ m, AEMeasurable (fun y => ∑' x : {x : Eucl n // x ∈ B m ∧ u x = y}, w x)
        (μHE[n] : Measure (Eucl Q)) ∧
      ∫⁻ x in B m, w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j =>
        inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1))
          (fderiv ℝ u x (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) =
        ∫⁻ y, ∑' x : {x : Eucl n // x ∈ B m ∧ u x = y}, w x ∂(μHE[n] : Measure (Eucl Q)) := by
    intro m
    have hBV : B m ⊆ V m := fun x hx => (hBDV m hx).2
    have hL : LipschitzOnWith (K m) u (B m) := (hK m).mono hBV
    have hwm : AEMeasurable w ((volume : Measure (Eucl n)).restrict (B m)) :=
      hw.mono_set fun x hx => (hBDV m hx).1
    -- Step 4: SimonGMT's weighted area formula for `u` Lipschitz on `B m`.
    have hmeas :=
      Poincare.SimonGMT.Chapter02.aemeasurable_weightedAreaFiberSum_lipschitzOn (hBm m) hL hwm
    have harea :=
      Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitzOn_fiberSum (hBm m) hL hwm
    rw [hdim] at hmeas harea
    refine ⟨hmeas, Eq.trans ?_ harea.symm⟩
    -- Step 5: `fderivWithin ℝ u (B m) = fderiv ℝ u` a.e. on `B m`, through a global Lipschitz
    -- extension `g` of `u|V m` (`u = g` near every point of the open `V m ⊇ B m`).
    obtain ⟨g, L, hg, hug⟩ :=
      Poincare.SimonGMT.Chapter02.exists_lipschitz_extension_finiteDimensional (hK m)
    have hder := Poincare.SimonGMT.Chapter02.ae_fderivWithin_eq_of_lipschitz_extension (hBm m) hg
      (hug.mono hBV)
    refine lintegral_congr_ae ?_
    filter_upwards [hder, ae_restrict_mem₀ (hBm m)] with x hx hxB
    have hxg : fderiv ℝ u x = fderiv ℝ g x :=
      (Filter.eventuallyEq_of_mem ((hVo m).mem_nhds (hBV hxB)) hug).fderiv_eq
    rw [Poincare.SimonGMT.Chapter02.areaJacobianWithin, hx, ← hxg, hJ, mul_comm]
  -- Step 6: glue the pieces with `Z = ∅`.
  exact Submission.lpf_raf_fiber_sum_glue (Eucl n) (Eucl Q) volume μHE[n] u w
    (fun x => w x * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j =>
      inner ℝ (fderiv ℝ u x (EuclideanSpace.single i 1))
        (fderiv ℝ u x (EuclideanSpace.single j 1))).det))
    D ∅ B (fun m => (hBDV m).trans inter_subset_left) hBd hBm (hDB.trans subset_union_right)
    measure_empty (by rw [image_empty, measure_empty]) hpiece
/-- Antilipschitz charts pull back `Hⁿ`-null sets to `Lⁿ`-null sets (Simon Ch. 3, proof of 2.6;
used for Ch. 6, 3.9): if `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` on `Ω` with `c > 0`, then `Φ` has a
`c⁻¹`-Lipschitz inverse `Ψ` on `Φ(Ω)` with `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, so `Hⁿ(Z) = 0` gives
`Lⁿ(Ω ∩ Φ⁻¹(Z)) = Hⁿ(Ω ∩ Φ⁻¹(Z)) = 0`. -/
theorem Submission.lpf_raf_chart_preimage_null : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c → (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ Z : Set (Eucl P), (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
  intro P n Φ Ω c hc hΦ Z hZ
  -- `Φ` is injective on `Ω`, so `Ψ := invFunOn Φ Ω` is a left inverse of `Φ` on `Ω`.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  set Ψ := Function.invFunOn Φ Ω
  have hleft : LeftInvOn Ψ Φ Ω := hinj.leftInvOn_invFunOn
  -- `Ψ` is `c⁻¹`-Lipschitz on `Φ '' Ω`.
  have hlip : LipschitzOnWith (Real.toNNReal c⁻¹) Ψ (Φ '' Ω) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    rw [hleft hw, hleft hw', dist_eq_norm, dist_eq_norm,
      Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hΦ w hw w' hw'
  -- `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, and the latter is `Hⁿ`-null by the Lipschitz image bound.
  have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Ψ '' (Φ '' Ω ∩ Z) := by
    rintro w ⟨hw, hwZ⟩
    exact ⟨Φ w, ⟨⟨w, hw, rfl⟩, hwZ⟩, hleft hw⟩
  have himg : (μHE[n] : Measure (Eucl n)) (Ψ '' (Φ '' Ω ∩ Z)) = 0 := by
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (A := Φ '' Ω ∩ Z) n (hlip.mono fun _ hy => hy.1)
    have h2 : (μHE[n] : Measure (Eucl P)) (Φ '' Ω ∩ Z) = 0 :=
      measure_mono_null (fun _ hy => hy.2) hZ
    rw [h2, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  -- On `ℝⁿ`, `Hⁿ = Lⁿ`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact measure_mono_null hsub himg

/-- Change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6 with a weight;
used for Ch. 6, 3.9): if `Φ` is Lipschitz and `c`-antilipschitz on the open set `Ω` and
`A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable, then `D = Ω ∩ Φ⁻¹(A)` is `Lⁿ`-null-measurable, `g ∘ Φ` is
a.e.-measurable on `D`, and `∫_A g dHⁿ = ∫_D g(Φ(w)) JΦ(w) dLⁿ(w)`.  This is the area formula
for `Φ` on `D`, whose fibre sums are `1_A g` because `Φ` is injective on `Ω`. -/
theorem Submission.lpf_raf_chart_change_of_variables : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (g : Eucl P → ℝ≥0∞), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → AEMeasurable g ((μHE[n] : Measure (Eucl P)).restrict A) → NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ AEMeasurable (fun w => g (Φ w)) ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) ∧ ∫⁻ x in A, g x ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ w in Ω ∩ Φ ⁻¹' A, g (Φ w) * ENNReal.ofReal (Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) ∂(volume : Measure (Eucl n)) := by
  intro P n Φ Ω A g hΩ ⟨K, hK⟩ ⟨c, hc, hΦ⟩ hAΩ hA hg
  -- `Φ` is injective and continuous on `Ω`.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  have hcont : ContinuousOn Φ Ω := hK.continuousOn
  classical
  -- `Ω ∩ Φ⁻¹(B)` is Borel for Borel `B`: replace `Φ` by its Borel extension `Ω.piecewise Φ 0`.
  have hborel : ∀ B : Set (Eucl P), MeasurableSet B → MeasurableSet (Ω ∩ Φ ⁻¹' B) := by
    intro B hB
    have hm : Measurable (Ω.piecewise Φ (fun _ => (0 : Eucl P))) :=
      hcont.measurable_piecewise continuousOn_const hΩ.measurableSet
    have heq : Ω ∩ Φ ⁻¹' B = Ω ∩ (Ω.piecewise Φ (fun _ => (0 : Eucl P))) ⁻¹' B := by
      ext w
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hw, hwB⟩
        exact ⟨hw, by rwa [Set.piecewise_eq_of_mem _ _ _ hw]⟩
      · rintro ⟨hw, hwB⟩
        exact ⟨hw, by rwa [Set.piecewise_eq_of_mem _ _ _ hw] at hwB⟩
    rw [heq]
    exact hΩ.measurableSet.inter (hm hB)
  -- `D = (Ω ∩ Φ⁻¹(B)) ∪ (Ω ∩ Φ⁻¹(A ∖ B))` with `B ⊆ A` Borel and `Hⁿ(A ∖ B) = 0`, so `D` is
  -- `Lⁿ`-null-measurable.
  obtain ⟨B, hBA, hBm, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have hnull : (μHE[n] : Measure (Eucl P)) (A \ B) = 0 := (ae_eq_set.mp hBae).2
  have hD : NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) := by
    have hsplit : Ω ∩ Φ ⁻¹' A = (Ω ∩ Φ ⁻¹' B) ∪ (Ω ∩ Φ ⁻¹' (A \ B)) := by
      ext w
      simp only [mem_inter_iff, mem_preimage, mem_union, Set.mem_sdiff]
      constructor
      · rintro ⟨hw, hwA⟩
        by_cases hwB : Φ w ∈ B
        · exact Or.inl ⟨hw, hwB⟩
        · exact Or.inr ⟨hw, hwA, hwB⟩
      · rintro (⟨hw, hwB⟩ | ⟨hw, hwA, -⟩)
        · exact ⟨hw, hBA hwB⟩
        · exact ⟨hw, hwA⟩
    rw [hsplit]
    exact (hborel B hBm).nullMeasurableSet.union
      (NullMeasurableSet.of_null (Submission.lpf_raf_chart_preimage_null P n Φ Ω c hc hΦ _ hnull))
  -- `g ∘ Φ = g' ∘ Φ` a.e. on `D` for a measurable `g' = g` (`Hⁿ⌞A`-a.e.), since `Φ` pulls the
  -- `Hⁿ`-null set `{g ≠ g'} ∩ A` back to an `Lⁿ`-null set.
  have hgae : AEMeasurable (fun w => g (Φ w))
      ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) := by
    have hZ : (μHE[n] : Measure (Eucl P)) ({x | g x ≠ hg.mk g x} ∩ A) = 0 := by
      rw [← Measure.restrict_apply₀' hA]
      exact hg.ae_eq_mk
    have hpre := Submission.lpf_raf_chart_preimage_null P n Φ Ω c hc hΦ _ hZ
    have hΦae : AEMeasurable Φ ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) :=
      (hcont.aemeasurable hΩ.measurableSet).mono_measure
        (Measure.restrict_mono inter_subset_left le_rfl)
    refine (hg.measurable_mk.comp_aemeasurable hΦae).congr ?_
    have h1 : ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)),
        w ∈ Ω ∩ Φ ⁻¹' A := ae_restrict_mem₀ hD
    have h2 : ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)),
        w ∉ Ω ∩ Φ ⁻¹' ({x | g x ≠ hg.mk g x} ∩ A) :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hpre)
    filter_upwards [h1, h2] with w hw1 hw2
    simp only [Function.comp_apply]
    by_contra hne
    exact hw2 ⟨hw1.1, Ne.symm hne, hw1.2⟩
  -- The area formula for `Φ` (locally Lipschitz on `Ω`) on `D` with weight `g ∘ Φ`.
  have hloc : LocallyLipschitzOn Ω Φ := fun _ _ => ⟨K, Ω, self_mem_nhdsWithin, hK⟩
  obtain ⟨-, harea⟩ := Submission.lpf_raf_local_lipschitz_area n P Ω (Ω ∩ Φ ⁻¹' A) Φ
    (fun w => g (Φ w)) hΩ hloc inter_subset_left hD hgae
  -- By injectivity, the fibre of `D` over `y` is a singleton for `y ∈ A` and empty otherwise.
  have hfib : ∀ y, (∑' x : {x : Eucl n // x ∈ Ω ∩ Φ ⁻¹' A ∧ Φ x = y}, g (Φ x)) =
      A.indicator g y := by
    intro y
    by_cases hy : y ∈ A
    · obtain ⟨w₀, hw₀, rfl⟩ := hAΩ hy
      rw [indicator_of_mem hy,
        tsum_eq_single (⟨w₀, ⟨hw₀, hy⟩, rfl⟩ : {x : Eucl n // x ∈ Ω ∩ Φ ⁻¹' A ∧ Φ x = Φ w₀})]
      intro b hb
      exact absurd (Subtype.ext (hinj b.2.1.1 hw₀ b.2.2)) hb
    · rw [indicator_of_notMem hy]
      have : IsEmpty {x : Eucl n // x ∈ Ω ∩ Φ ⁻¹' A ∧ Φ x = y} :=
        ⟨fun x => hy (x.2.2 ▸ x.2.1.2)⟩
      exact tsum_empty
  refine ⟨hD, hgae, ?_⟩
  rw [harea, ← lintegral_indicator₀ hA]
  exact lintegral_congr fun y => (hfib y).symm
/-- `Hⁿ`-a.e. properties pull back along antilipschitz charts (used for Simon Ch. 6, 3.9): if
`M` is `Hⁿ`-null-measurable, `Ω` and `Φ` are measurable and `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` on `Ω`
with `c > 0`, then `Ω ∩ Φ⁻¹(M)` is `Lⁿ`-null-measurable, and a property holding `Hⁿ`-a.e. on
`M ∩ Φ(Ω)` holds at `Φ w` for `Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`. -/
theorem Submission.lpf_ccr_ae_pullback : ∀ (P n : ℕ) (M : Set (Eucl P)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (p : Eucl P → Prop), MeasurableSet Ω → Measurable Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ Φ '' Ω)), p x) → NullMeasurableSet (Ω ∩ Φ ⁻¹' M) (volume : Measure (Eucl n)) ∧ ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), p (Φ w) := by
  intro P n M Φ Ω p hΩ hΦ ⟨c, hc, hanti⟩ hM hp
  -- `Hⁿ`-null sets of `ℝ^P` pull back to `Lⁿ`-null sets of parameters in `Ω`.
  have hnull := Submission.lpf_raf_chart_preimage_null P n Φ Ω c hc hanti
  -- With `B ⊆ M` measurable and `Hⁿ(M \ B) = 0`, `Ω ∩ Φ⁻¹(M)` is measurable ∪ `Lⁿ`-null.
  obtain ⟨B, hBM, hB, hBae⟩ := hM.exists_measurable_subset_ae_eq
  have hS : Ω ∩ Φ ⁻¹' M = (Ω ∩ Φ ⁻¹' B) ∪ (Ω ∩ Φ ⁻¹' (M \ B)) := by
    ext w
    by_cases hw : Φ w ∈ B
    · simp [hw, hBM hw]
    · simp [hw]
  have hSm : NullMeasurableSet (Ω ∩ Φ ⁻¹' M) (volume : Measure (Eucl n)) := by
    rw [hS]
    exact (hΩ.inter (hΦ hB)).nullMeasurableSet.union_null (hnull _ (ae_eq_set.mp hBae).2)
  refine ⟨hSm, (ae_restrict_iff'₀ hSm).mpr ?_⟩
  -- The exceptional set `{¬p} ∩ (M ∩ Φ(Ω))` is `Hⁿ`-null, so its pullback is `Lⁿ`-null.
  have hZ : (μHE[n] : Measure (Eucl P)) ({x | ¬p x} ∩ (M ∩ Φ '' Ω)) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.le_restrict_apply _ _).trans_eq (ae_iff.mp hp))
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) (hnull _ hZ)
  have hw' : ¬(w ∈ Ω ∩ Φ ⁻¹' M → p (Φ w)) := hw
  obtain ⟨⟨hwΩ, hwM⟩, hwp⟩ := not_imp.mp hw'
  exact ⟨hwΩ, hwp, hwM, mem_image_of_mem Φ hwΩ⟩
/-- Moore–Penrose left inverse (Simon Ch. 3 §2, input to 2.1–2.2): `Λ(A) = (A* A)⁻¹ A*` is
continuous on the injective `A : ℝⁿ → ℝ^P`, `Λ(A) A = id`, and the orthogonal projection
`A Λ(A)` onto `range A` does not increase norms. -/
theorem Submission.lpf_tde_continuous_left_inverse :
    ∀ (n P : ℕ), ∃ Λ : (Eucl n →L[ℝ] Eucl P) → (Eucl P →L[ℝ] Eucl n),
      ContinuousOn Λ {A : Eucl n →L[ℝ] Eucl P | Function.Injective A} ∧
      ∀ A : Eucl n →L[ℝ] Eucl P, Function.Injective A →
        (Λ A).comp A = ContinuousLinearMap.id ℝ (Eucl n) ∧ ∀ v : Eucl P, ‖A (Λ A v)‖ ≤ ‖v‖ := by
  intro n P
  -- `A* A` is a unit of the endomorphism ring when `A` is injective.
  have hunit : ∀ A : Eucl n →L[ℝ] Eucl P, Function.Injective A →
      IsUnit ((ContinuousLinearMap.adjoint A).comp A) := by
    intro A hA
    have hinj : Function.Injective ((ContinuousLinearMap.adjoint A).comp A) :=
      (ContinuousLinearMap.adjoint_comp_self_injective_iff A).2 hA
    exact ContinuousLinearMap.isUnit_iff_bijective.2
      ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  -- `Λ(A) = (A* A)⁻¹ A*`, with `Ring.inverse` (`= 0` off the units).
  refine ⟨fun A => (Ring.inverse ((ContinuousLinearMap.adjoint A).comp A)).comp
    (ContinuousLinearMap.adjoint A), ?_, fun A hA => ?_⟩
  · -- Adjoint, composition and the ring inverse at units are continuous.
    intro A₀ hA₀
    have hadj : Continuous fun A : Eucl n →L[ℝ] Eucl P => ContinuousLinearMap.adjoint A :=
      ContinuousLinearMap.adjoint.continuous
    have hinv : ContinuousAt (fun A : Eucl n →L[ℝ] Eucl P =>
        Ring.inverse ((ContinuousLinearMap.adjoint A).comp A)) A₀ := by
      have h := NormedRing.inverse_continuousAt (hunit A₀ hA₀).unit
      rw [IsUnit.unit_spec] at h
      exact h.comp_of_eq (hadj.clm_comp continuous_id).continuousAt rfl
    exact (hinv.clm_comp hadj.continuousAt).continuousWithinAt
  have hu := hunit A hA
  refine ⟨?_, fun v => ?_⟩
  · -- `Λ(A) A = (A* A)⁻¹ (A* A) = id`.
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def,
      Ring.inverse_mul_cancel _ hu]
    rfl
  · -- `p := A Λ(A) v` satisfies `A* p = A* v`, so `v - p ⊥ p`; Pythagoras.
    beta_reduce
    set p := A ((Ring.inverse ((ContinuousLinearMap.adjoint A).comp A)).comp
      (ContinuousLinearMap.adjoint A) v) with hp
    have hAp : ContinuousLinearMap.adjoint A p = ContinuousLinearMap.adjoint A v := by
      have h := congrArg (fun T : Eucl n →L[ℝ] Eucl n => T (ContinuousLinearMap.adjoint A v))
        (Ring.mul_inverse_cancel _ hu)
      simpa [ContinuousLinearMap.mul_def, hp] using h
    have horth : inner ℝ (v - p) p = 0 := by
      rw [hp, ← ContinuousLinearMap.adjoint_inner_left, ← hp, map_sub, hAp, sub_self,
        inner_zero_left]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [sub_add_cancel] at h
    exact (mul_self_le_mul_self_iff (norm_nonneg p) (norm_nonneg v)).2
      (by nlinarith [mul_self_nonneg ‖v - p‖])
/-- Integrals converge if they converge on every piece of a countable measurable partition, under
integrable domination (step 4 of the tangential weak limit argument).  As `ν` lives on `⋃ⱼ Vⱼ`,
countable additivity gives `∫ H dν = ∑ⱼ ∫_{Vⱼ} H dν` for integrable `H`; the terms for `H = F_k`
are bounded by the summable `∫_{Vⱼ} b dν`, so Tannery's theorem (dominated convergence for series,
the `ε / 3` argument of Mathlib's `tendsto_tsum_of_dominated_convergence`, inlined since that file
is not available here) passes to the limit termwise. -/
theorem Submission.slicing_im_ll_twl_partition_tendsto :
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (V : ℕ → Set X) (b : X → ℝ)
      (F : ℕ → X → ℝ) (Flim : X → ℝ), (∀ j, MeasurableSet (V j)) →
      Pairwise (Function.onFun Disjoint V) → ν (⋃ j, V j)ᶜ = 0 → Integrable b ν →
      (∀ k, Integrable (F k) ν) → (∀ k, ∀ᵐ x ∂ν, ‖F k x‖ ≤ b x) → Integrable Flim ν →
      (∀ j, Tendsto (fun k => ∫ x in V j, F k x ∂ν) atTop (𝓝 (∫ x in V j, Flim x ∂ν))) →
      Tendsto (fun k => ∫ x, F k x ∂ν) atTop (𝓝 (∫ x, Flim x ∂ν)) := by
  intro X _ ν V b F Flim hVm hVd hVc hb hF hFb hFlim hlim
  -- `ν` lives on `⋃ⱼ Vⱼ`, so `∫ H dν = ∑ⱼ ∫_{Vⱼ} H dν` for integrable `H`.
  have hν : ν.restrict (⋃ j, V j) = ν := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hVc)
  have hsum : ∀ H : X → ℝ, Integrable H ν →
      HasSum (fun j => ∫ x in V j, H x ∂ν) (∫ x, H x ∂ν) := fun H hH => by
    simpa only [hν] using hasSum_integral_iUnion hVm hVd hH.integrableOn
  -- The summable majorant: `|∫_{Vⱼ} F_k dν| ≤ ∫_{Vⱼ} b dν`.
  have hbound : ∀ k j, ‖∫ x in V j, F k x ∂ν‖ ≤ ∫ x in V j, b x ∂ν := fun k j =>
    norm_integral_le_of_norm_le hb.integrableOn (ae_restrict_of_ae (hFb k))
  -- Tannery's theorem along `atTop` on `ℕ` (proof of `tendsto_tsum_of_dominated_convergence`).
  have tannery : ∀ (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (bound : ℕ → ℝ), Summable bound →
      (∀ j, Tendsto (f · j) atTop (𝓝 (g j))) → (∀ᶠ n in atTop, ∀ j, ‖f n j‖ ≤ bound j) →
      Tendsto (fun n => ∑' j, f n j) atTop (𝓝 (∑' j, g j)) := by
    intro f g bound h_sum hab h_bound
    have h_g_le (k : ℕ) : ‖g k‖ ≤ bound k :=
      le_of_tendsto (tendsto_norm.comp (hab k)) <| h_bound.mono (fun n h => h k)
    have h_sumg : Summable (‖g ·‖) :=
      h_sum.of_norm_bounded (fun k ↦ (norm_norm (g k)).symm ▸ h_g_le k)
    have h_suma : ∀ᶠ n in atTop, Summable (‖f n ·‖) := by
      filter_upwards [h_bound] with n h
      exact h_sum.of_norm_bounded <| by simpa only [norm_norm] using h
    rw [Metric.tendsto_nhds]
    intro ε hε
    let ⟨S, hS⟩ := h_sum
    obtain ⟨T, hT⟩ : ∃ (T : Finset ℕ), dist (∑ i ∈ T, bound i) S < ε / 3 := by
      rw [HasSum, Metric.tendsto_nhds] at hS
      exact Eventually.exists <| hS _ (by positivity)
    have h1 : ∑' (k : (Tᶜ : Set ℕ)), bound k < ε / 3 := by
      calc _ ≤ ‖∑' (k : (Tᶜ : Set ℕ)), bound k‖ := Real.le_norm_self _
           _ = ‖S - ∑ i ∈ T, bound i‖ := congrArg _ ?_
           _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT
      simpa only [h_sum.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hS.tsum_eq
    have h2 : Tendsto (∑ k ∈ T, f · k) atTop (𝓝 (T.sum g)) :=
      tendsto_finsetSum _ (fun i _ ↦ hab i)
    rw [Metric.tendsto_nhds] at h2
    filter_upwards [h2 (ε / 3) (by positivity), h_suma, h_bound] with n hn h_suma h_bound
    rw [dist_eq_norm, ← h_suma.of_norm.tsum_sub h_sumg.of_norm,
      ← (h_suma.of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T),
      (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
    refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
    · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hn
    · rw [(h_suma.subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
      refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
      · refine ((norm_tsum_le_tsum_norm (h_suma.subtype _)).trans ?_).trans_lt h1
        exact (h_suma.subtype _).tsum_le_tsum (h_bound ·) (h_sum.subtype _)
      · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
        exact (h_sumg.subtype _).tsum_le_tsum (h_g_le ·) (h_sum.subtype _)
  -- Pass to the limit termwise and identify both sums with the full integrals.
  have hlim' := tannery (fun k j => ∫ x in V j, F k x ∂ν) (fun j => ∫ x in V j, Flim x ∂ν)
    (fun j => ∫ x in V j, b x ∂ν) (hsum b hb).summable hlim (Eventually.of_forall hbound)
  rw [← (hsum Flim hFlim).tsum_eq]
  exact hlim'.congr fun k => (hsum (F k) (hF k)).tsum_eq

/-- Bochner change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6 for
integrable integrands; used for Ch. 6, 4.5(2)): if `Φ` is Lipschitz and `κ`-antilipschitz on the
open set `Ω`, `A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable and `F` is Banach-valued and `Hⁿ⌞A`-integrable,
then `D = Ω ∩ Φ⁻¹(A)` is `Lⁿ`-null-measurable, `JΦ · (F ∘ Φ)` is `Lⁿ`-integrable on `D` and
`∫_A F dHⁿ = ∫_D JΦ(w) F(Φ(w)) dLⁿ(w)`.  The nonnegative chart formula, valid for every Borel
`g ≥ 0`, says that `Φ` pushes `JΦ · Lⁿ⌞D` forward to `Hⁿ⌞A`. -/
theorem Submission.slicing_im_ll_twl_chart_integral_eq : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (F : Eucl P → E), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → IntegrableOn F A (μHE[n] : Measure (Eucl P)) → NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ IntegrableOn (fun w => Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • F (Φ w)) (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) ∧ ∫ x in A, F x ∂(μHE[n] : Measure (Eucl P)) = ∫ w in Ω ∩ Φ ⁻¹' A, Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • F (Φ w) ∂(volume : Measure (Eucl n)) := by
  intro E _ _ _ P n Φ Ω A F hΩ hLip hanti hAΩ hA hF
  -- Step 1: the nonnegative chart formula with `g = 0` gives that `D` is null-measurable.
  have hD : NullMeasurableSet (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) :=
    (Submission.lpf_raf_chart_change_of_variables P n Φ Ω A (fun _ => 0) hΩ hLip hanti hAΩ hA
      aemeasurable_const).1
  -- Step 2: `Φ` is continuous on the open set `Ω ⊇ D`, hence a.e.-measurable on `D`.
  obtain ⟨K, hK⟩ := hLip
  have hΦ : AEMeasurable Φ ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) :=
    (hK.continuousOn.aemeasurable hΩ.measurableSet).mono_set inter_subset_left
  -- Steps 3–6: transfer `F` along `Φ` with the weight `JΦ` (Borel, and nonnegative as a square
  -- root), using the nonnegative chart formula for each Borel `g`.
  exact ⟨hD, Submission.slicing_im_ll_twl_cie_weighted_transfer (Eucl n) (Eucl P) E
    ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) ((μHE[n] : Measure (Eucl P)).restrict A)
    Φ (fun w => Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1))
      (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) F hΦ
    (Submission.slicing_im_ll_twl_cie_jacobian_measurable P n Φ).aemeasurable
    (fun _ => Real.sqrt_nonneg _)
    (fun g hg => (Submission.lpf_raf_chart_change_of_variables P n Φ Ω A g hΩ ⟨K, hK⟩ hanti hAΩ
      hA hg.aemeasurable).2.2) hF⟩
/-- Coefficient field on a chart piece (Simon Ch. 6, proof of 4.5(2)): if `Φ` is `C¹`, Lipschitz
and `κ`-antilipschitz on the open `Ω`, `A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable and `Y` is
`Hⁿ ⌞ A`-integrable with `Y(x) ∈ range DΦ(w)` for all `w ∈ Ω ∩ Φ⁻¹(x)`, `Hⁿ`-a.e. `x ∈ A`, then
`c := 1_D Λ(DΦ)(JΦ · Y ∘ Φ)` (`D = Ω ∩ Φ⁻¹(A)`, `Λ` the continuous left inverse) vanishes off
`D`, is `Lⁿ`-integrable (`|c| ≤ κ⁻¹ JΦ |Y ∘ Φ|`) and `DΦ(w) c(w) = JΦ(w) Y(Φ w)` for `Lⁿ`-a.e.
`w ∈ D`. -/
theorem Submission.slicing_im_ll_twl_coefficient_field : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (Y : Eucl P → Eucl P), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → IntegrableOn Y A (μHE[n] : Measure (Eucl P)) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict A), ∀ w ∈ Ω, Φ w = x → Y x ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap) → ∃ c : Eucl n → Eucl n, IntegrableOn c Ω (volume : Measure (Eucl n)) ∧ (∀ w, w ∉ Ω ∩ Φ ⁻¹' A → c w = 0) ∧ ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)), fderiv ℝ Φ w (c w) = Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • Y (Φ w) := by
  intro P n Φ Ω A Y hΩ hΦ hlip hanti hAΩ hA hY htan
  obtain ⟨κ, hκ, hκanti⟩ := hanti
  -- `Λ(B) B = id` and `‖B Λ(B) v‖ ≤ ‖v‖` for injective `B`, and `Λ` is continuous there.
  obtain ⟨Λ, hΛcont, hΛ⟩ := Submission.lpf_tde_continuous_left_inverse n P
  -- On `Ω`, `κ ‖s‖ ≤ ‖DΦ(w) s‖`: `DΦ(w)` is injective and `‖Λ(DΦ(w)) v‖ ≤ κ⁻¹ ‖v‖`.
  have hlow : ∀ w ∈ Ω, ∀ s, κ * ‖s‖ ≤ ‖fderiv ℝ Φ w s‖ := fun w hw =>
    Submission.lpf_wtc_cat_fderiv_lower_bound P n Φ Ω κ w hΩ hw
      (hΦ.differentiable one_ne_zero w) hκanti
  have hinj : ∀ w ∈ Ω, Function.Injective (fderiv ℝ Φ w) := by
    intro w hw s s' h
    have h1 := hlow w hw (s - s')
    rw [map_sub, h, sub_self, norm_zero] at h1
    have h2 : ‖s - s'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hκ (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  have hΛle : ∀ w ∈ Ω, ∀ v, ‖Λ (fderiv ℝ Φ w) v‖ ≤ κ⁻¹ * ‖v‖ := fun w hw v =>
    (le_inv_mul_iff₀ hκ).2
      ((hlow w hw (Λ (fderiv ℝ Φ w) v)).trans ((hΛ _ (hinj w hw)).2 v))
  -- `w ↦ Λ(DΦ(w))` is continuous on `Ω`, hence a.e. strongly measurable on `D = Ω ∩ Φ⁻¹(A)`.
  have hΛm : AEStronglyMeasurable (fun w => Λ (fderiv ℝ Φ w))
      ((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)) :=
    ((hΛcont.comp (hΦ.continuous_fderiv one_ne_zero).continuousOn fun w hw =>
      hinj w hw).aestronglyMeasurable hΩ.measurableSet).mono_set inter_subset_left
  -- The tangency of `Y` holds at `Φ w` for `Lⁿ`-a.e. `w ∈ D`, and `D` is null-measurable.
  obtain ⟨hDm, hpull⟩ := Submission.lpf_ccr_ae_pullback P n A Φ Ω
    (fun x => ∀ w ∈ Ω, Φ w = x → Y x ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap)
    hΩ.measurableSet hΦ.continuous.measurable ⟨κ, hκ, hκanti⟩ hA
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left htan)
  -- An integrable `Z` on `D` with `Z(w) ∈ range DΦ(w)` a.e. lifts to `c := 1_D Λ(DΦ) Z`.
  have key : ∀ Z : Eucl n → Eucl P, IntegrableOn Z (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl n)) →
      (∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)),
        Z w ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap) →
      ∃ c : Eucl n → Eucl n, IntegrableOn c Ω (volume : Measure (Eucl n)) ∧
        (∀ w, w ∉ Ω ∩ Φ ⁻¹' A → c w = 0) ∧
        ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)),
          fderiv ℝ Φ w (c w) = Z w := by
    intro Z hZ hZr
    -- `‖Λ(DΦ(w)) Z(w)‖ ≤ κ⁻¹ ‖Z(w)‖` on `D`.
    have hf : IntegrableOn (fun w => Λ (fderiv ℝ Φ w) (Z w)) (Ω ∩ Φ ⁻¹' A)
        (volume : Measure (Eucl n)) := by
      refine Integrable.mono' ((Integrable.norm hZ).const_mul κ⁻¹)
        ((ContinuousLinearMap.id ℝ (Eucl P →L[ℝ] Eucl n)).aestronglyMeasurable_comp₂ hΛm
          hZ.aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem₀ hDm] with w hw
      exact hΛle w hw.1 (Z w)
    refine ⟨(Ω ∩ Φ ⁻¹' A).indicator fun w => Λ (fderiv ℝ Φ w) (Z w),
      (hf.integrable_indicator₀ hDm).integrableOn, fun w hw => indicator_of_notMem hw _, ?_⟩
    -- `Z(w) = DΦ(w) t` and `Λ(DΦ(w)) DΦ(w) = id` give `DΦ(w) c(w) = Z(w)`.
    filter_upwards [hZr, ae_restrict_mem₀ hDm] with w hw hwD
    obtain ⟨t, ht⟩ := LinearMap.mem_range.1 hw
    have ht' : fderiv ℝ Φ w t = Z w := ht
    rw [indicator_of_mem hwD]
    show fderiv ℝ Φ w (Λ (fderiv ℝ Φ w) (Z w)) = Z w
    rw [← ht', ← ContinuousLinearMap.comp_apply (Λ (fderiv ℝ Φ w)) (fderiv ℝ Φ w),
      (hΛ _ (hinj w hwD.1)).1, ContinuousLinearMap.id_apply]
  -- By the area formula on the chart, `JΦ · Y ∘ Φ` is integrable on `D`; it is tangent like `Y`.
  obtain ⟨-, hZ, -⟩ := Submission.slicing_im_ll_twl_chart_integral_eq (Eucl P) P n Φ Ω A Y hΩ
    hlip ⟨κ, hκ, hκanti⟩ hAΩ hA hY
  refine key _ hZ ?_
  filter_upwards [hpull, ae_restrict_mem₀ hDm] with w hw hwD
  exact Submodule.smul_mem _ _ (hw w hwD.1 rfl)

/-- Chain rule on a `C¹` chart for a Lipschitz function with a tangential gradient (used for
Simon Ch. 6, §4): if `h` is `L`-Lipschitz and, for `Hⁿ`-a.e. `x ∈ A`, `s ↦ h(x + s u)` has
derivative `⟨G(x), u⟩` at `0` for all `u ∈ range DΦ(w)` with `Φ(w) = x`, then Rademacher's theorem
on `Ω` and uniqueness of derivatives give `D(h ∘ Φ)(w) = ⟨G(Φ(w)), DΦ(w) ·⟩` for `Lⁿ`-a.e.
`w ∈ Ω ∩ Φ⁻¹(A)`. -/
theorem Submission.slicing_im_ll_twl_chart_hasFDerivAt : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (h : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → LipschitzWith L h → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict A), ∀ w ∈ Ω, Φ w = x → ∀ u ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)), HasFDerivAt (h ∘ Φ) ((innerSL ℝ (G (Φ w))).comp (fderiv ℝ Φ w)) w := by
  intro P n Φ Ω A h L G hΩ hΦ ⟨K, hK⟩ hanti hA hh hG
  -- The tangential hypothesis at `Φ w` holds for `Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(A)`.
  obtain ⟨hD, hpull⟩ := Submission.lpf_ccr_ae_pullback P n A Φ Ω
    (fun x => ∀ w ∈ Ω, Φ w = x → ∀ u ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap,
      HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0)
    hΩ.measurableSet hΦ.continuous.measurable hanti hA
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hG)
  -- Rademacher: `h ∘ Φ` is Lipschitz on the open set `Ω`, so differentiable a.e. in `Ω`.
  have hrad : ∀ᵐ w ∂(volume : Measure (Eucl n)), w ∈ Ω → DifferentiableWithinAt ℝ (h ∘ Φ) Ω w :=
    (hh.comp_lipschitzOnWith hK).ae_differentiableWithinAt_of_mem
  filter_upwards [hpull, ae_restrict_of_ae hrad, ae_restrict_mem₀ hD] with w hpw hdw hwD
  have hdiff : DifferentiableAt ℝ (h ∘ Φ) w := (hdw hwD.1).differentiableAt (hΩ.mem_nhds hwD.1)
  -- Identify `D(h ∘ Φ)(w) s` with `⟨G(Φ w), DΦ(w) s⟩` for every direction `s`.
  have key : fderiv ℝ (h ∘ Φ) w = (innerSL ℝ (G (Φ w))).comp (fderiv ℝ Φ w) := by
    refine ContinuousLinearMap.ext fun s => ?_
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    have hline : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
    have hΦline : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 :=
      ((hΦ.differentiable one_ne_zero) w).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline
        (by simp)
    have hφ₁ : HasDerivAt (fun t : ℝ => h (Φ (w + t • s))) (fderiv ℝ (h ∘ Φ) w s) 0 :=
      hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    -- The tangential hypothesis, applied at `w` itself in the direction `DΦ(w) s`.
    have h₁ : HasDerivAt (fun t : ℝ => h (Φ w + t • fderiv ℝ Φ w s))
        (inner ℝ (G (Φ w)) (fderiv ℝ Φ w s)) 0 :=
      hpw w hwD.1 rfl _ ⟨s, rfl⟩
    -- `h(Φ w + t DΦ(w) s)` and `h(Φ(w + t s))` differ by at most `L · o(t)`.
    have h₂ : HasDerivAt (fun t : ℝ => h (Φ w + t • fderiv ℝ Φ w s)) (fderiv ℝ (h ∘ Φ) w s) 0 := by
      rw [hasDerivAt_iff_isLittleO] at hΦline hφ₁ ⊢
      have hO : (fun t : ℝ => h (Φ w + t • fderiv ℝ Φ w s) - h (Φ (w + t • s))) =O[𝓝 0]
          (fun t : ℝ => Φ (w + t • s) - Φ (w + (0 : ℝ) • s) - (t - 0) • fderiv ℝ Φ w s) := by
        refine Asymptotics.IsBigO.of_bound (L : ℝ) (Eventually.of_forall fun t => ?_)
        refine (hh.norm_sub_le _ _).trans_eq ?_
        rw [← norm_neg (Φ w + t • fderiv ℝ Φ w s - Φ (w + t • s))]
        congr 2
        simp only [zero_smul, add_zero, sub_zero]
        abel
      refine (hφ₁.add (hO.trans_isLittleO hΦline)).congr_left fun t => ?_
      simp only [zero_smul, add_zero, sub_zero]
      abel
    exact h₂.unique h₁
  rw [← key]
  exact hdiff.hasFDerivAt

/-- Slicing (Simon Ch. 6, §4), tangential weak limit, step (9a)–(9b): over a chart piece
`A ⊆ Φ(Ω)`, tangential integrals are parameter integrals against one field `c`,
`∫_A Df(Y) dHⁿ = ∫_Ω D(f∘Φ)(c)` and `∫_A ⟨G, Y⟩ dHⁿ = ∫_Ω D(h∘Φ)(c)`.  Here `c` is the
coefficient field (`DΦ(w) c(w) = JΦ(w) Y(Φ(w))` a.e. on `Ω ∩ Φ⁻¹(A)`, `c = 0` off it); both
identities are the chart integral formula combined with the chain rule. -/
theorem Submission.slicing_im_ll_twl_chart_representation : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (h : Eucl P → ℝ) (L : ℝ≥0) (G Y : Eucl P → Eucl P), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → LipschitzWith L h → Measurable G → (∀ x, ‖G x‖ ≤ L) → IntegrableOn Y A (μHE[n] : Measure (Eucl P)) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict A), ∀ w ∈ Ω, Φ w = x → Y x ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0) → ∃ c : Eucl n → Eucl n, IntegrableOn c Ω (volume : Measure (Eucl n)) ∧ (∀ (f : Eucl P → ℝ) (K : ℝ≥0), Differentiable ℝ f → LipschitzWith K f → ∫ x in A, fderiv ℝ f x (Y x) ∂(μHE[n] : Measure (Eucl P)) = ∫ w in Ω, fderiv ℝ (f ∘ Φ) w (c w)) ∧ ∫ x in A, inner ℝ (G x) (Y x) ∂(μHE[n] : Measure (Eucl P)) = ∫ w in Ω, fderiv ℝ (h ∘ Φ) w (c w) := by
  intro P n Φ Ω A h L G Y hΩ hΦ hLip hanti hAΦ hA hh hGm hGL hY hae
  -- Step 1: the coefficient field `c`.
  obtain ⟨c, hc, hc0, hcD⟩ := Submission.slicing_im_ll_twl_coefficient_field P n Φ Ω A Y hΩ hΦ
    hLip hanti hAΦ hA hY (hae.mono fun x hx w hw hwx => (hx w hw hwx).1)
  -- Step 2: the differential of `h ∘ Φ` on `Ω ∩ Φ⁻¹(A)`.
  have hhD := Submission.slicing_im_ll_twl_chart_hasFDerivAt P n Φ Ω A h L G hΩ hΦ hLip hanti hA
    hh (hae.mono fun x hx w hw hwx => (hx w hw hwx).2)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable one_ne_zero
  have hY' : Integrable Y ((μHE[n] : Measure (Eucl P)).restrict A) := hY
  -- Step 3: `c` vanishes off `Ω ∩ Φ⁻¹(A)`, so integrals over `Ω` reduce to it.
  have hred : ∀ g : Eucl n → (Eucl n →L[ℝ] ℝ),
      ∫ w in Ω, g w (c w) = ∫ w in Ω ∩ Φ ⁻¹' A, g w (c w) := fun g =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet inter_subset_left
      fun w hw => by rw [hc0 w hw.2, map_zero]
  refine ⟨c, hc, fun f K hf hfK => ?_, ?_⟩
  · -- Step 4: identity (i), with `F = Df(Y)`, `|F| ≤ K |Y|`.
    have hF : IntegrableOn (fun x => fderiv ℝ f x (Y x)) A (μHE[n] : Measure (Eucl P)) := by
      refine Integrable.mono' (hY'.norm.const_mul (K : ℝ))
        ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
          (measurable_fderiv ℝ f).aestronglyMeasurable hY'.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      calc ‖fderiv ℝ f x (Y x)‖ ≤ ‖fderiv ℝ f x‖ * ‖Y x‖ := (fderiv ℝ f x).le_opNorm (Y x)
        _ ≤ K * ‖Y x‖ :=
          mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hfK) (norm_nonneg _)
    rw [(Submission.slicing_im_ll_twl_chart_integral_eq ℝ P n Φ Ω A _ hΩ hLip hanti hAΦ hA
      hF).2.2, hred (fderiv ℝ (f ∘ Φ))]
    refine integral_congr_ae ?_
    filter_upwards [hcD] with w hw
    rw [fderiv_comp w (hf (Φ w)) (hΦd w), ContinuousLinearMap.comp_apply, hw, map_smul]
  · -- Step 5: identity (ii), with `F = ⟨G, Y⟩`, `|F| ≤ L |Y|`.
    have hF : IntegrableOn (fun x => inner ℝ (G x) (Y x)) A (μHE[n] : Measure (Eucl P)) := by
      refine Integrable.mono' (hY'.norm.const_mul (L : ℝ))
        (continuous_inner.comp_aestronglyMeasurable₂ hGm.aestronglyMeasurable
          hY'.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      calc ‖inner ℝ (G x) (Y x)‖ ≤ ‖G x‖ * ‖Y x‖ := norm_inner_le_norm _ _
        _ ≤ L * ‖Y x‖ := mul_le_mul_of_nonneg_right (hGL x) (norm_nonneg _)
    rw [(Submission.slicing_im_ll_twl_chart_integral_eq ℝ P n Φ Ω A _ hΩ hLip hanti hAΦ hA
      hF).2.2, hred (fderiv ℝ (h ∘ Φ))]
    refine integral_congr_ae ?_
    filter_upwards [hcD, hhD] with w hw hw'
    rw [hw'.fderiv, ContinuousLinearMap.comp_apply, hw, innerSL_apply_apply,
      real_inner_smul_right, smul_eq_mul]
/-- **Lipschitz bound, in the field, for the pairing `∫_Ω Df(b)`.**  If `f` is `C`-Lipschitz on
the open set `Ω ⊆ ℝⁿ` and `b, b'` are integrable on `Ω`, then
`|∫_Ω Df(b) − ∫_Ω Df(b')| ≤ C ∫_Ω |b − b'|`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not
differentiable).  On `Ω` we have `‖Df(w)‖ ≤ C`, so `w ↦ Df(w)(v(w))` is dominated by `C |v|`; it
is a.e. strongly measurable because `Df` is Borel, hence integrable for `v = b, b'`, and the
estimate follows by linearity of the integral and of `Df(w)`. -/
theorem Submission.slicing_im_ll_gws_pairing_bound :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (f : Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C f Ω →
      ∀ b b' : Eucl n → Eucl n, IntegrableOn b Ω (volume : Measure (Eucl n)) →
        IntegrableOn b' Ω (volume : Measure (Eucl n)) →
        |(∫ w in Ω, fderiv ℝ f w (b w)) - ∫ w in Ω, fderiv ℝ f w (b' w)| ≤
          C * ∫ w in Ω, ‖b w - b' w‖ := by
  intro n Ω C f hΩ hf b b' hb hb'
  -- `Ω` is a neighbourhood of each of its points, so `‖Df(w)‖ ≤ C` on `Ω`.
  have hD : ∀ w ∈ Ω, ‖fderiv ℝ f w‖ ≤ C := fun w hw =>
    norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hf
  -- Hence `|Df(w)(v(w))| ≤ C |v(w)|` for a.e. `w ∈ Ω`, for every field `v`.
  have hle : ∀ v : Eucl n → Eucl n,
      ∀ᵐ w ∂(volume : Measure (Eucl n)).restrict Ω, ‖fderiv ℝ f w (v w)‖ ≤ C * ‖v w‖ := by
    intro v
    refine (ae_restrict_iff' hΩ.measurableSet).2 (Eventually.of_forall fun w hw => ?_)
    exact (fderiv ℝ f w).le_of_opNorm_le (hD w hw) (v w)
  -- `w ↦ Df(w)(v(w))` is integrable on `Ω` when `v` is: it is a.e. strongly measurable
  -- (`Df` is Borel) and dominated by `C |v|`.
  have hint : ∀ v : Eucl n → Eucl n, IntegrableOn v Ω volume →
      IntegrableOn (fun w => fderiv ℝ f w (v w)) Ω volume := fun v hv =>
    (hv.norm.const_mul C).mono' ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
      hv.aestronglyMeasurable (measurable_fderiv ℝ f).aestronglyMeasurable) (hle v)
  -- Combine the integrals by linearity, then estimate.
  rw [← integral_sub (hint b hb) (hint b' hb')]
  simp_rw [← map_sub]
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((hb.sub hb').norm.const_mul C) (hle (b - b'))
/-- **Integration by parts against a `C¹` field, for functions Lipschitz on `Ω`.**  Let `Ω ⊆ ℝⁿ`
be open and `b : ℝⁿ → ℝⁿ` be `C¹` with compact support and `tsupport b ⊆ Ω`.  The divergence
`g = ∑ᵢ Dbᵢ(·)(eᵢ)` of `b` is integrable, and for every `f` that is `L`-Lipschitz on `Ω`, `f g` is
integrable on `Ω` and `∫_Ω Df(b) = −∫_Ω f g`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not
differentiable).  Extend `f` to an `L`-Lipschitz `F` on `ℝⁿ` (McShane); `DF = Df` on the open set
`Ω` and `b, g` vanish off `Ω`, so both sides are integrals over `ℝⁿ` with `F` in place of `f`.
Expand `b = ∑ᵢ bᵢ eᵢ`: by Rademacher's theorem `DF(w)(eᵢ)` is the line derivative of `F` along
`eᵢ` for a.e. `w`, and integration by parts for Lipschitz functions moves it onto the compactly
supported Lipschitz coordinate `bᵢ`. -/
theorem Submission.slicing_im_ll_gws_lipschitz_ibp :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (b : Eucl n → Eucl n), IsOpen Ω → ContDiff ℝ 1 b →
      HasCompactSupport b → tsupport b ⊆ Ω → ∃ g : Eucl n → ℝ,
        Integrable g (volume : Measure (Eucl n)) ∧
        ∀ (L : ℝ≥0) (f : Eucl n → ℝ), LipschitzOnWith L f Ω →
          IntegrableOn (fun w => f w * g w) Ω (volume : Measure (Eucl n)) ∧
          ∫ w in Ω, fderiv ℝ f w (b w) = -∫ w in Ω, f w * g w := by
  intro n Ω b hΩ hb hbc hbΩ
  classical
  -- Coordinates `bᵢ` of `b`: `C¹` with compact support, hence Lipschitz; `Dbᵢ = 0` off
  -- `tsupport b`.
  let e : Fin n → Eucl n := fun i => EuclideanSpace.single i 1
  let bi : Fin n → Eucl n → ℝ := fun i x => EuclideanSpace.proj i (b x)
  have hbi_cd : ∀ i, ContDiff ℝ 1 (bi i) := fun i =>
    (EuclideanSpace.proj i : StrongDual ℝ (Eucl n)).contDiff.comp hb
  have hbi_cs : ∀ i, HasCompactSupport (bi i) := fun i =>
    hbc.comp_left (g := fun y => EuclideanSpace.proj i y) (map_zero _)
  have hbi_ts : ∀ i, tsupport (bi i) ⊆ tsupport b := fun i =>
    tsupport_comp_subset (g := fun y => EuclideanSpace.proj i y) (map_zero _) b
  have hbi_lip : ∀ i, ∃ D, LipschitzWith D (bi i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hbi_cs i) (hbi_cd i) one_ne_zero
  have hbi_diff : ∀ i, Differentiable ℝ (bi i) := fun i => (hbi_cd i).differentiable one_ne_zero
  have hbi_cfd : ∀ i, Continuous (fderiv ℝ (bi i)) := fun i =>
    (hbi_cd i).continuous_fderiv one_ne_zero
  have hDbi_zero : ∀ i w, w ∉ tsupport b → fderiv ℝ (bi i) w = 0 := fun i w hw =>
    image_eq_zero_of_notMem_tsupport fun h => hw (hbi_ts i (tsupport_fderiv_subset ℝ h))
  -- The divergence `g = ∑ᵢ Dbᵢ(·)(eᵢ)` is continuous and vanishes off `tsupport b`, so it has
  -- compact support and is integrable.  It does not depend on `L` or `f`.
  let g : Eucl n → ℝ := fun w => ∑ i, fderiv ℝ (bi i) w (e i)
  have hg_cont : Continuous g :=
    continuous_finsetSum _ fun i _ => (hbi_cfd i).clm_apply continuous_const
  have hg_zero : ∀ w, w ∉ tsupport b → g w = 0 := fun w hw =>
    Finset.sum_eq_zero fun i _ => by simp [hDbi_zero i w hw]
  have hg_cs : HasCompactSupport g := HasCompactSupport.intro hbc hg_zero
  refine ⟨g, hg_cont.integrable_of_hasCompactSupport hg_cs, fun L f hf => ?_⟩
  -- McShane: `F` is `L`-Lipschitz on `ℝⁿ` and `F = f` on `Ω`, so `DF = Df` on the open set `Ω`.
  obtain ⟨F, hF, hfF⟩ := hf.extend_real
  have hDf : ∀ w ∈ Ω, fderiv ℝ f w = fderiv ℝ F w := fun w hw =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hw) hfF)
  -- (a): `F g` is continuous with compact support, and `f g = F g` on `Ω`.
  have hFg_int : Integrable (fun w => F w * g w) volume :=
    (hF.continuous.mul hg_cont).integrable_of_hasCompactSupport (hg_cs.mul_left (f := F))
  refine ⟨hFg_int.integrableOn.congr_fun (fun w hw => by simp [hfF hw]) hΩ.measurableSet, ?_⟩
  -- (b) reduces to `∫ DF(b) = −∫ F g` over `ℝⁿ`, as `b` and `g` vanish off `Ω`.
  have h1 : ∫ w in Ω, fderiv ℝ f w (b w) = ∫ w, fderiv ℝ F w (b w) := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun w => fderiv ℝ F w (b w))
      (fun w hw => by simp only [hDf w hw])]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
    simp [image_eq_zero_of_notMem_tsupport fun h => hw (hbΩ h)]
  have h2 : ∫ w in Ω, f w * g w = ∫ w, F w * g w := by
    rw [setIntegral_congr_fun hΩ.measurableSet (g := fun w => F w * g w)
      (fun w hw => by simp only [hfF hw])]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
    simp [hg_zero w fun h => hw (hbΩ h)]
  rw [h1, h2]
  -- Expand `b = ∑ᵢ bᵢ eᵢ`; each term `DF(·)(eᵢ) bᵢ` is integrable, as `‖DF‖ ≤ L` and `bᵢ` is
  -- continuous with compact support.
  have hexp : ∀ w, fderiv ℝ F w (b w) = ∑ i, fderiv ℝ F w (e i) * bi i w := by
    intro w
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (b w)]
    simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, mul_comm, e, bi]
  have hterm_int : ∀ i, Integrable (fun w => fderiv ℝ F w (e i) * bi i w) volume := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hbi_cd i).continuous.integrable_of_hasCompactSupport (hbi_cs i))
      (measurable_fderiv_apply_const ℝ F (e i)).aestronglyMeasurable ?_
    filter_upwards with w
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hF) (norm_nonneg _))
  -- Rademacher (`DF(w)(eᵢ) = ∂_{eᵢ}F(w)` a.e.) and integration by parts for Lipschitz functions.
  have hibp : ∀ i, ∫ w, fderiv ℝ F w (e i) * bi i w
      = -∫ w, fderiv ℝ (bi i) w (e i) * F w := by
    intro i
    obtain ⟨D, hD⟩ := hbi_lip i
    have hae : (fun w => fderiv ℝ F w (e i) * bi i w)
        =ᵐ[volume] (fun w => lineDeriv ℝ F w (e i) * bi i w) := by
      filter_upwards [hF.ae_differentiableAt (μ := volume)] with w hw
      rw [hw.lineDeriv_eq_fderiv]
    rw [integral_congr_ae hae, hF.integral_lineDeriv_mul_eq hD (hbi_cs i) (e i), ← integral_neg]
    congr 1
    ext w
    rw [((hbi_diff i) w).lineDeriv_eq_fderiv]
    simp
  -- Sum over `i`; each `Dbᵢ(·)(eᵢ) F` is continuous and vanishes off the compact `tsupport b`.
  have hterm2_int : ∀ i, Integrable (fun w => fderiv ℝ (bi i) w (e i) * F w) volume := by
    intro i
    refine (((hbi_cfd i).clm_apply continuous_const).mul
      hF.continuous).integrable_of_hasCompactSupport (HasCompactSupport.intro hbc fun w hw => ?_)
    simp [hDbi_zero i w hw]
  calc ∫ w, fderiv ℝ F w (b w) = ∫ w, ∑ i, fderiv ℝ F w (e i) * bi i w := by
        simp_rw [hexp]
    _ = ∑ i, ∫ w, fderiv ℝ F w (e i) * bi i w :=
        integral_finsetSum _ fun i _ => hterm_int i
    _ = ∑ i, -∫ w, fderiv ℝ (bi i) w (e i) * F w :=
        Finset.sum_congr rfl fun i _ => hibp i
    _ = -∫ w, ∑ i, fderiv ℝ (bi i) w (e i) * F w := by
        rw [integral_finsetSum _ fun i _ => hterm2_int i, Finset.sum_neg_distrib]
    _ = -∫ w, F w * g w := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp [g, Finset.mul_sum, mul_comm]

/-- Convergence of the gradient pairings against a `C¹` test field: if `u_k → u` uniformly on
the open set `Ω`, all `C`-Lipschitz on `Ω`, and `b` is `C¹` with compact support in `Ω`, then
`∫_Ω Du_k(b) → ∫_Ω Du(b)`.  With the weak divergence `g ∈ L¹` of `b` given by
`slicing_im_ll_gws_lipschitz_ibp`, `∫_Ω Du_k(b) - ∫_Ω Du(b) = ∫_Ω (u - u_k) g`, which is at most
`sup_Ω |u - u_k| · ∫_Ω |g|`. -/
theorem Submission.slicing_im_ll_gws_smooth_tendsto : ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (u : Eucl n → ℝ) (ug : ℕ → Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C u Ω → (∀ k, LipschitzOnWith C (ug k) Ω) → TendstoUniformlyOn ug u atTop Ω → ∀ b : Eucl n → Eucl n, ContDiff ℝ 1 b → HasCompactSupport b → tsupport b ⊆ Ω → Tendsto (fun k => ∫ w in Ω, fderiv ℝ (ug k) w (b w)) atTop (𝓝 (∫ w in Ω, fderiv ℝ u w (b w))) := by
  intro n Ω C u ug hΩ hu hug hconv b hb hbc hbΩ
  -- Step 1: the weak divergence `g` of `b`, applied to `u` and to every `u_k` (all
  -- `C`-Lipschitz on `Ω`).
  obtain ⟨g, hg, hgf⟩ := Submission.slicing_im_ll_gws_lipschitz_ibp n Ω b hΩ hb hbc hbΩ
  obtain ⟨hu_int, hu_eq⟩ := hgf C u hu
  -- Step 2: `∫_Ω Du_k(b) - ∫_Ω Du(b) = -∫_Ω u_k g + ∫_Ω u g = ∫_Ω (u - u_k) g`.
  have hdiff : ∀ k, (∫ w in Ω, fderiv ℝ (ug k) w (b w)) - ∫ w in Ω, fderiv ℝ u w (b w) =
      ∫ w in Ω, (u w - ug k w) * g w := fun k => by
    obtain ⟨hk_int, hk_eq⟩ := hgf C (ug k) (hug k)
    simp only [sub_mul]
    rw [hk_eq, hu_eq, integral_sub hu_int hk_int]
    ring
  -- Step 3: `A = ∫_Ω |g| ≥ 0`, `η = ε / (2 (A + 1))`, and `N` with `|u - u_k| < η` on `Ω` for
  -- all `k ≥ N` (uniform convergence).
  obtain ⟨A, hA⟩ : ∃ A, ∫ w in Ω, |g w| = A := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [← hA]
    exact integral_nonneg fun w => abs_nonneg (g w)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hA1 : 0 < 2 * (A + 1) := by linarith
  have hη : 0 < ε / (2 * (A + 1)) := div_pos hε hA1
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv _ hη)
  refine ⟨N, fun k hk => ?_⟩
  -- Step 4: `|∫_Ω (u - u_k) g| ≤ ∫_Ω η |g| = η A`.
  have hbound : ∀ w ∈ Ω, ‖(u w - ug k w) * g w‖ ≤ ε / (2 * (A + 1)) * |g w| := fun w hw => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← Real.dist_eq]
    exact mul_le_mul_of_nonneg_right (hN k hk w hw).le (abs_nonneg (g w))
  have hest : ‖∫ w in Ω, (u w - ug k w) * g w‖ ≤ ∫ w in Ω, ε / (2 * (A + 1)) * |g w| :=
    norm_integral_le_of_norm_le (hg.integrableOn.abs.const_mul _)
      (ae_restrict_of_forall_mem hΩ.measurableSet hbound)
  rw [integral_const_mul, hA] at hest
  -- Step 5: `η A < η · 2 (A + 1) = ε`.
  rw [Real.dist_eq, hdiff k, ← Real.norm_eq_abs]
  calc ‖∫ w in Ω, (u w - ug k w) * g w‖ ≤ ε / (2 * (A + 1)) * A := hest
    _ < ε / (2 * (A + 1)) * (2 * (A + 1)) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ ε hA1.ne'
/-- `C_c^∞` fields are dense in `L¹(Ω)`: for `Ω ⊆ ℝⁿ` open, `c : ℝⁿ → ℝⁿ` integrable on `Ω` and
`δ > 0` there is a smooth `b` with compact support, `spt b ⊆ Ω` and `∫_Ω |c − b| < δ`.  The
exhaustion `K_j = F_j ∩ B̄(0, j)` of `Ω` gives a compact `K ⊆ Ω` with `∫_{Ω∖K} |c| < δ/2`;
`1_K c` is within `δ/2` in `L¹(ℝⁿ)` of a smooth compactly supported `b₀` (approximate simple
functions, using the regularity of `Lⁿ` and the smooth Urysohn lemma); and `b = χ b₀` for a
smooth cutoff `0 ≤ χ ≤ 1` with `χ = 1` on `K` and `spt χ ⊆ Ω`. -/
theorem Submission.slicing_im_ll_gws_smooth_dense :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (c : Eucl n → Eucl n), IsOpen Ω → IntegrableOn c Ω (volume : Measure (Eucl n)) → ∀ δ : ℝ, 0 < δ → ∃ b : Eucl n → Eucl n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ tsupport b ⊆ Ω ∧ ∫ w in Ω, ‖c w - b w‖ < δ := by
  intro n Ω c hΩ hc δ hδ
  -- Step 1: the compact exhaustion `K j = F j ∩ B̄(0, j)` of `Ω`.
  obtain ⟨F, hFc, hFΩ, hFU, hFm⟩ := hΩ.exists_iUnion_isClosed
  have hKc : ∀ j : ℕ, IsCompact (F j ∩ closedBall 0 j) := fun j =>
    (isCompact_closedBall 0 j).inter_left (hFc j)
  have hKΩ : ∀ j : ℕ, F j ∩ closedBall 0 j ⊆ Ω := fun j => inter_subset_left.trans (hFΩ j)
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Eucl n) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Eucl n) j = Ω := by
    refine Subset.antisymm (iUnion_subset hKΩ) fun w hw => ?_
    rw [← hFU] at hw
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    refine mem_iUnion.2 ⟨max i ⌈‖w‖⌉₊, hFm (le_max_left _ _) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))
  -- Step 2: a compact `K = K j ⊆ Ω` with `∫_{Ω \ K} |c| < δ / 2`.
  have hcn : IntegrableOn (fun w => ‖c w‖) Ω := hc.norm
  obtain ⟨K, hK, hKΩ', htail⟩ : ∃ K : Set (Eucl n), IsCompact K ∧ K ⊆ Ω ∧
      ∫ w in Ω \ K, ‖c w‖ < δ / 2 := by
    have hlim := tendsto_setIntegral_of_monotone (fun j => (hKc j).measurableSet) hKm
      (by rw [hKU]; exact hcn)
    rw [hKU] at hlim
    obtain ⟨j, hj⟩ := ((tendsto_order.1 hlim).1 _ (sub_lt_self _ (half_pos hδ))).exists
    refine ⟨_, hKc j, hKΩ j, ?_⟩
    rw [setIntegral_sdiff (hKc j).measurableSet hcn (hKΩ j)]
    linarith
  -- Step 3: `C_c^∞` is dense in `L¹(ℝⁿ)` (simple functions, regularity and smooth Urysohn).
  have hdense : ∀ f : Eucl n → Eucl n, Integrable f → ∀ ε : ℝ, 0 < ε →
      ∃ g : Eucl n → Eucl n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g ∧
        ∫ w, ‖f w - g w‖ ≤ ε := by
    intro f hf ε hε
    have hind : ∀ (v : Eucl n) ⦃s : Set (Eucl n)⦄, MeasurableSet s → volume s < ∞ →
        ∀ {η : ℝ≥0∞}, η ≠ 0 → ∃ g : Eucl n → Eucl n,
          eLpNorm (g - s.indicator fun _ => v) 1 volume ≤ η ∧
            (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g) := by
      intro v s hs hμs η hη
      obtain ⟨θ, hθ0, hθ⟩ := ENNReal.exists_nnreal_pos_mul_lt
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top : 2 * ‖v‖ₑ ≠ ∞) hη
      have hθ0' : (θ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hθ0.ne'
      obtain ⟨A, hAs, hA, hsA⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hθ0'
      obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hθ0'
      obtain ⟨L, hL, hAL, hLU⟩ := exists_compact_between hA hU (hAs.trans hsU)
      obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) isOpen_interior hA.isClosed hAL
      have hχ0 : ∀ x, x ∉ interior L → χ x = 0 := fun x hx =>
        Function.notMem_support.1 (by rw [hχs]; exact hx)
      refine ⟨fun x => χ x • v, ?_, hχ.smul contDiff_const, ?_⟩
      · calc eLpNorm ((fun x => χ x • v) - s.indicator fun _ => v) 1 volume
            ≤ eLpNorm ((U \ A).indicator fun _ => v) 1 volume := by
              refine eLpNorm_mono ((hχ.continuous.smul continuous_const).aestronglyMeasurable.sub
                (aestronglyMeasurable_const.indicator hs)) fun x => ?_
              rw [Pi.sub_apply]
              by_cases hxA : x ∈ A
              · simp [(hχ1 x).1 hxA, indicator_of_mem (hAs hxA)]
              by_cases hxU : x ∈ U
              · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxA)]
                obtain ⟨h0, h1⟩ := hχr (mem_range_self x)
                by_cases hxs : x ∈ s
                · rw [indicator_of_mem hxs,
                    show χ x • v - v = (χ x - 1) • v by rw [sub_smul, one_smul], norm_smul,
                    Real.norm_eq_abs]
                  calc |χ x - 1| * ‖v‖ ≤ 1 * ‖v‖ := by
                        gcongr; rw [abs_le]; constructor <;> linarith
                    _ = ‖v‖ := one_mul _
                · rw [indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs]
                  calc |χ x| * ‖v‖ ≤ 1 * ‖v‖ := by
                        gcongr; rw [abs_le]; constructor <;> linarith
                    _ = ‖v‖ := one_mul _
              · have hxs : x ∉ s := fun h => hxU (hsU h)
                have hxL : x ∉ interior L := fun h => hxU (hLU (interior_subset h))
                simp [hχ0 x hxL, hxs]
          _ = ‖v‖ₑ * volume (U \ A) := by
              rw [eLpNorm_indicator_const (hU.measurableSet.diff hA.measurableSet).nullMeasurableSet
                one_ne_zero ENNReal.one_ne_top]
              simp
          _ ≤ ‖v‖ₑ * (θ + θ) := by
              gcongr
              calc volume (U \ A) ≤ volume ((U \ s) ∪ (s \ A)) := measure_mono fun x hx => by
                    by_cases hxs : x ∈ s
                    · exact Or.inr ⟨hxs, hx.2⟩
                    · exact Or.inl ⟨hx.1, hxs⟩
                _ ≤ volume (U \ s) + volume (s \ A) := measure_union_le _ _
                _ ≤ θ + θ := add_le_add hUs.le hsA.le
          _ = θ * (2 * ‖v‖ₑ) := by ring
          _ ≤ η := hθ.le
      · exact HasCompactSupport.intro hL fun x hx => by
          simp [hχ0 x fun h => hx (interior_subset h)]
    obtain ⟨g, hfg, hg, hgc⟩ := (memLp_one_iff_integrable.2 hf).induction_dense
      ENNReal.one_ne_top
      (fun g : Eucl n → Eucl n => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g)
      hind (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.2 hε).ne'
    refine ⟨g, hg, hgc, ?_⟩
    have hm : AEStronglyMeasurable (f - g) volume :=
      (hf.sub (hg.continuous.integrable_of_hasCompactSupport hgc)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hm] at hfg
    change ∫ w, ‖(f - g) w‖ ≤ ε
    rw [integral_norm_eq_lintegral_enorm hm]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hfg
  -- Step 3 applied to `1_K c`.
  have hKi : Integrable (K.indicator c) :=
    (integrable_indicator_iff hK.measurableSet).2 (hc.mono_set hKΩ')
  obtain ⟨b₀, hb₀, hb₀c, hb₀K⟩ := hdense _ hKi (δ / 2) (half_pos hδ)
  have hb₀i : Integrable b₀ := hb₀.continuous.integrable_of_hasCompactSupport hb₀c
  -- Step 4: a smooth cutoff `χ`, `χ = 1` exactly on `K`, `0 ≤ χ ≤ 1`, `tsupport χ ⊆ L ⊆ Ω`.
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ'
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) isOpen_interior hK.isClosed hKL
  have hχL : tsupport χ ⊆ L := by
    rw [tsupport, hχs]
    exact closure_minimal interior_subset hL.isClosed
  have hχc : HasCompactSupport χ := hL.of_isClosed_subset (isClosed_tsupport _) hχL
  -- Step 5: `b = χ b₀`.
  have hbc : HasCompactSupport fun w => χ w • b₀ w := hχc.smul_right
  have hbi : Integrable fun w => χ w • b₀ w :=
    (hχ.continuous.smul hb₀.continuous).integrable_of_hasCompactSupport hbc
  refine ⟨fun w => χ w • b₀ w, hχ.smul hb₀, hbc,
    (tsupport_smul_subset_left _ _).trans (hχL.trans hLΩ), ?_⟩
  -- Step 6: `|c - b| ≤ |1_{Kᶜ} c| + |1_K c - b₀|` pointwise.
  have hptw : ∀ w, ‖c w - χ w • b₀ w‖ ≤ ‖Kᶜ.indicator c w‖ + ‖K.indicator c w - b₀ w‖ := by
    intro w
    by_cases hw : w ∈ K
    · simp [(hχ1 w).1 hw, hw]
    · rw [indicator_of_mem (mem_compl hw), indicator_of_notMem hw, zero_sub, norm_neg]
      obtain ⟨h0, h1⟩ := hχr (mem_range_self w)
      calc ‖c w - χ w • b₀ w‖ ≤ ‖c w‖ + ‖χ w • b₀ w‖ := norm_sub_le _ _
        _ ≤ ‖c w‖ + ‖b₀ w‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
          exact mul_le_of_le_one_left (norm_nonneg _) h1
  -- Step 7: integrate over `Ω`.
  have h1 : ∫ w in Ω, ‖Kᶜ.indicator c w‖ < δ / 2 := by
    simp_rw [norm_indicator_eq_indicator_norm]
    rw [setIntegral_indicator hK.measurableSet.compl, ← sdiff_eq]
    exact htail
  have h2 : ∫ w in Ω, ‖K.indicator c w - b₀ w‖ ≤ δ / 2 :=
    (setIntegral_le_integral (hKi.sub hb₀i).norm
      (Eventually.of_forall fun _ => norm_nonneg _)).trans hb₀K
  calc ∫ w in Ω, ‖c w - χ w • b₀ w‖
      ≤ ∫ w in Ω, (‖Kᶜ.indicator c w‖ + ‖K.indicator c w - b₀ w‖) :=
        setIntegral_mono (hc.sub hbi.integrableOn).norm
          ((hc.indicator hK.measurableSet.compl).norm.add (hKi.sub hb₀i).norm.integrableOn) hptw
    _ = (∫ w in Ω, ‖Kᶜ.indicator c w‖) + ∫ w in Ω, ‖K.indicator c w - b₀ w‖ :=
        integral_add (hc.indicator hK.measurableSet.compl).norm (hKi.sub hb₀i).norm.integrableOn
    _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le h1 h2
    _ = δ := add_halves δ

/-- Gradients of functions `u_k → u` that converge uniformly on an open `Ω ⊆ ℝⁿ` and are all
`C`-Lipschitz on `Ω` converge weakly-* on `Ω`: `∫_Ω Du_k(c) → ∫_Ω Du(c)` for every field `c`
integrable on `Ω`. -/
theorem Submission.slicing_im_ll_gradient_weak_star :
    ∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (u : Eucl n → ℝ) (ug : ℕ → Eucl n → ℝ), IsOpen Ω →
      LipschitzOnWith C u Ω → (∀ k, LipschitzOnWith C (ug k) Ω) →
      TendstoUniformlyOn ug u atTop Ω → ∀ c : Eucl n → Eucl n,
      IntegrableOn c Ω (volume : Measure (Eucl n)) →
      Tendsto (fun k => ∫ w in Ω, fderiv ℝ (ug k) w (c w)) atTop
        (𝓝 (∫ w in Ω, fderiv ℝ u w (c w))) := by
  intro n Ω C u ug hΩ hu hug hconv c hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- A smooth field `b` compactly supported in `Ω` with `∫_Ω |c - b| < ε / (3 (C + 1))`,
  -- so that `C ∫_Ω |c - b| < ε / 3`.
  obtain ⟨b, hb, hbc, hbΩ, hcb⟩ := Submission.slicing_im_ll_gws_smooth_dense n Ω c hΩ hc
    (ε / (3 * (C + 1))) (by positivity)
  have hCcb : (C : ℝ) * ∫ w in Ω, ‖c w - b w‖ < ε / 3 := by
    calc (C : ℝ) * ∫ w in Ω, ‖c w - b w‖ ≤ C * (ε / (3 * (C + 1))) :=
          mul_le_mul_of_nonneg_left hcb.le C.coe_nonneg
      _ < ε / 3 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hbi : IntegrableOn b Ω (volume : Measure (Eucl n)) :=
    (hb.continuous.integrable_of_hasCompactSupport hbc).integrableOn
  -- The pairings against the smooth field `b` converge.
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.1
    (Submission.slicing_im_ll_gws_smooth_tendsto n Ω C u ug hΩ hu hug hconv b
      (hb.of_le (by exact_mod_cast le_top)) hbc hbΩ) (ε / 3) (by positivity)
  refine ⟨k₀, fun k hk => ?_⟩
  -- Replacing `c` by `b` moves the pairings with `Du_k` and with `Du` by at most
  -- `C ∫_Ω |c - b| < ε / 3` each.
  have h₁ := Submission.slicing_im_ll_gws_pairing_bound n Ω C (ug k) hΩ (hug k) c b hc hbi
  have h₂ := Submission.slicing_im_ll_gws_pairing_bound n Ω C u hΩ hu c b hc hbi
  have h₃ := hk₀ k hk
  rw [Real.dist_eq] at h₃ ⊢
  have h₄ := abs_sub_le (∫ w in Ω, fderiv ℝ (ug k) w (c w)) (∫ w in Ω, fderiv ℝ (ug k) w (b w))
    (∫ w in Ω, fderiv ℝ u w (c w))
  have h₅ := abs_sub_le (∫ w in Ω, fderiv ℝ (ug k) w (b w)) (∫ w in Ω, fderiv ℝ u w (b w))
    (∫ w in Ω, fderiv ℝ u w (c w))
  rw [abs_sub_comm (∫ w in Ω, fderiv ℝ u w (b w))] at h₅
  linarith

/-- Simon Ch. 6, proof of Lemma 4.5(2), (1): if the differentiable `L`-Lipschitz `g_k` converge
uniformly to `h`, whose tangential gradient on `(M, θ)` is `G`, then `∫_M Dg_k(Y) dHⁿ` tends to
`∫_M ⟨G, Y⟩ dHⁿ` for every integrable tangent field `Y`.  `M` is cut into pieces on disjoint
`C¹` chart images, where `range DΦ` is the weighted tangent plane; on each piece both integrals
are parameter integrals against one integrable field, which converge by the weak-* convergence
of the chart gradients, and dominated convergence sums the pieces. -/
theorem Submission.slicing_im_ll_tangential_weak_limit : ∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsOpen U → IsRectifiableTriple U n M θ ξ → ∀ (h : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), LipschitzWith L h → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0) → ∀ Y : Eucl P → Eucl P, Integrable Y ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → Y x ∈ Q) → ∀ g : ℕ → Eucl P → ℝ, (∀ k, Differentiable ℝ (g k)) → (∀ k, LipschitzWith L (g k)) → TendstoUniformly g h atTop → Tendsto (fun k => ∫ x in M, fderiv ℝ (g k) x (Y x) ∂(μHE[n] : Measure (Eucl P))) atTop (𝓝 (∫ x in M, inner ℝ (G x) (Y x) ∂(μHE[n] : Measure (Eucl P)))) := by
  intro P n U M θ ξ hU hT h L G hh hG hGL hTG Y hY hYtan g hgd hgL hgu
  -- `C¹` charts `Φ j`, Lipschitz and antilipschitz on open `Ω j`, cover `M` up to an
  -- `Hⁿ`-null set (Simon Ch. 3, 1.2).
  obtain ⟨Φ, Ω, hΩ, hΦ, hLip, hanti, hcover⟩ :=
    Submission.lpf_countably_rectifiable_c1_cover P n M hT.countablyRectifiable
  -- Each chart image is Borel: `Φ j` is continuous and injective on the open set `Ω j`.
  have himg : ∀ j, MeasurableSet (Φ j '' Ω j) := by
    intro j
    obtain ⟨κ, hκ, hκΦ⟩ := hanti j
    refine (hΩ j).measurableSet.image_of_continuousOn_injOn (hΦ j).continuous.continuousOn
      fun w hw w' hw' hww' => ?_
    have h₁ := hκΦ w hw w' hw'
    rw [hww', sub_self, norm_zero] at h₁
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h₁ hκ))
  -- Disjoint Borel pieces `V j ⊆ Φ j '' Ω j`; they cover `M` up to an `Hⁿ`-null set.
  set V : ℕ → Set (Eucl P) := disjointed fun j => Φ j '' Ω j with hV
  have hVm : ∀ j, MeasurableSet (V j) := MeasurableSet.disjointed himg
  have hnull : ((μHE[n] : Measure (Eucl P)).restrict M) (⋃ j, V j)ᶜ = 0 := by
    rw [Measure.restrict_apply (MeasurableSet.iUnion hVm).compl, hV, iUnion_disjointed,
      inter_comm, ← sdiff_eq]
    exact hcover
  -- The integrands and their integrable majorant `L |Y|` (`|Dg_k| ≤ L`, `|G| ≤ L`).
  have hb : Integrable (fun x => (L : ℝ) * ‖Y x‖) ((μHE[n] : Measure (Eucl P)).restrict M) :=
    hY.norm.const_mul _
  have hFb : ∀ k x, ‖fderiv ℝ (g k) x (Y x)‖ ≤ (L : ℝ) * ‖Y x‖ := fun k x =>
    ((fderiv ℝ (g k) x).le_opNorm (Y x)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hgL k)) (norm_nonneg _))
  have hF : ∀ k, Integrable (fun x => fderiv ℝ (g k) x (Y x))
      ((μHE[n] : Measure (Eucl P)).restrict M) := fun k =>
    hb.mono' ((ContinuousLinearMap.id ℝ (Eucl P →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      (measurable_fderiv ℝ (g k)).aestronglyMeasurable hY.aestronglyMeasurable)
      (ae_of_all _ (hFb k))
  have hFlim : Integrable (fun x => inner ℝ (G x) (Y x))
      ((μHE[n] : Measure (Eucl P)).restrict M) :=
    hb.mono' (continuous_inner.comp_aestronglyMeasurable₂ (g := fun a b => inner ℝ a b)
      hG.aestronglyMeasurable hY.aestronglyMeasurable) (ae_of_all _ fun x =>
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hGL x) (norm_nonneg _)))
  -- Reduce to the convergence on each piece (dominated convergence for the series).
  refine Submission.slicing_im_ll_twl_partition_tendsto (Eucl P)
    ((μHE[n] : Measure (Eucl P)).restrict M) V (fun x => (L : ℝ) * ‖Y x‖)
    (fun k x => fderiv ℝ (g k) x (Y x)) (fun x => inner ℝ (G x) (Y x)) hVm
    (disjoint_disjointed _) hnull hb hF (fun k => ae_of_all _ (hFb k)) hFlim fun j => ?_
  -- The piece `A := V j ∩ M ⊆ Φ j '' Ω j`.
  rw [Measure.restrict_restrict (hVm j)]
  have hAΦ : V j ∩ M ⊆ Φ j '' Ω j := inter_subset_left.trans (disjointed_subset _ j)
  -- For `Hⁿ`-a.e. `x = Φ j w ∈ A`, `range DΦ j (w)` is the weighted tangent plane of `(M, θ)`,
  -- so it contains `Y x` and `h` has the derivative `⟨G x, u⟩` along each of its vectors `u`.
  have hwtA := ae_restrict_of_ae_restrict_of_subset (subset_inter inter_subset_right hAΦ)
    (Submission.lpf_weighted_tangent_on_c1_chart P n U M θ (Φ j) (Ω j) hU hT.subset
      hT.nullMeasurableSet hT.pos hT.integrableOn (hΩ j) (hΦ j) (hanti j))
  -- Both integrals over `A` as parameter integrals against one integrable field `c`.
  obtain ⟨c, hc, hcf, hch⟩ := Submission.slicing_im_ll_twl_chart_representation P n (Φ j) (Ω j)
    (V j ∩ M) h L G Y (hΩ j) (hΦ j) (hLip j) (hanti j) hAΦ
    ((hVm j).nullMeasurableSet.inter hT.nullMeasurableSet) hh hG hGL
    ((show IntegrableOn Y M (μHE[n] : Measure (Eucl P)) from hY).mono_set inter_subset_right) (by
      filter_upwards [hwtA, ae_restrict_of_ae_restrict_of_subset inter_subset_right hTG,
        ae_restrict_of_ae_restrict_of_subset inter_subset_right hYtan] with x h₁ h₂ h₃ w hw hwx
      exact ⟨h₃ _ (h₁ w hw hwx), (h₂ _ (h₁ w hw hwx)).2⟩)
  -- Weak-* convergence of the chart gradients `D(g_k ∘ Φ j) → D(h ∘ Φ j)` against `c`:
  -- `g_k ∘ Φ j → h ∘ Φ j` uniformly on `Ω j`, all `L K`-Lipschitz there.
  obtain ⟨K, hK⟩ := hLip j
  rw [hch]
  exact (Submission.slicing_im_ll_gradient_weak_star n (Ω j) (L * K) (h ∘ Φ j)
    (fun k => g k ∘ Φ j) (hΩ j) (hh.comp_lipschitzOnWith hK)
    (fun k => (hgL k).comp_lipschitzOnWith hK) (hgu.comp (Φ j)).tendstoUniformlyOn c hc).congr
    fun k => (hcf (g k) L (hgd k) (hgL k)).symm

/-- Simon Ch. 6, proof of Lemma 4.5(2), (1)–(3) (p. 156): Leibniz rule for a Lipschitz `h` with
tangential gradient `G_h` on `M`, `T = τ(M, θ, ξ)`:
`∫ h ⟨ω, v'⟩ dμ' − ∫ h ⟨dω, v⟩ dμ = ∫_M θ ⟨G_h ∧ ω, ξ⟩ dHⁿ`.
For smooth `Lh`-Lipschitz `g_k → h` the smooth identity, rewritten through the tangent field `Y`
with `φ(Y) = θ ⟨φ ∧ ω, ξ⟩`, reads `∫_M Dg_k(Y) dHⁿ = ∫ g_k ⟨ω, v'⟩ dμ' − ∫ g_k ⟨dω, v⟩ dμ`; the
left side tends to `∫_M ⟨G_h, Y⟩ dHⁿ` and the right side to the left side of the claim. -/
theorem Submission.slicing_im_lipschitz_leibniz :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (T : GeometricCurrentOn U (m + 1)), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → (∀ η : TestFormOn U (m + 1), T η = tauAction (m + 1) M θ ξ η) → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)) (μ' : Measure (Eucl P)) (v' : Eucl P → NVector (Eucl P) m), IsMeasureRepresentation T μ v → IsMeasureRepresentation T.boundary μ' v' → ∀ (h : Eucl P → ℝ) (Lh : ℝ≥0) (Gh : Eucl P → Eucl P), LipschitzWith Lh h → Measurable Gh → (∀ x, ‖Gh x‖ ≤ Lh) → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → Gh x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (Gh x) u) 0) → ∀ ω : TestFormOn U m, (∫ x, h x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') - (∫ x, h x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ) = ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (Gh x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ∂(μHE[m + 1] : Measure (Eucl P)) := by
  intro P m U M θ ξ T hU hMθξ hT μ v μ' v' hrep hrep' h Lh Gh hh hGm hGb hTG ω
  obtain ⟨⟨hωs, hωc⟩, -⟩ := ω.2
  -- Smooth `Lh`-Lipschitz `g k → h` uniformly, and the field `Y` dual to `φ ↦ θ ⟨φ ∧ ω, ξ⟩`.
  obtain ⟨g, hg, hgL, hgh⟩ := Submission.slicing_im_ll_mollify P h Lh hh
  obtain ⟨Y, hY, hYφ, hYT⟩ := Submission.slicing_im_ll_tangent_dual_field P m U M θ ξ hMθξ ω
  -- Simon's (2): the smooth identity for `ψ = g k`, with `θ ⟨Dg_k ∧ ω, ξ⟩ = Dg_k(Y)`.
  have hk : ∀ k, ∫ x in M, fderiv ℝ (g k) x (Y x) ∂(μHE[m + 1] : Measure (Eucl P)) =
      (∫ x, g k x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') -
        ∫ x, g k x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ := by
    intro k
    rw [← Submission.slicing_im_ll_smooth_leibniz P m U M θ ξ T hT μ v μ' v' hrep hrep' ω (g k)
      (hg k)]
    exact integral_congr_ae (Eventually.of_forall fun x => hYφ x _)
  -- Representation side: `⟨ω, v'⟩ ∈ L¹(μ')` and `⟨dω, v⟩ ∈ L¹(μ)` vanish off the compact sets
  -- `spt ω` and `spt dω`, so the uniform limit `g k → h` passes inside both integrals.
  have hrhs := (Submission.slicing_im_ll_multiplier_tendsto P μ'
      (fun x => v' x ((ω : DifferentialForm (Eucl P) m) x))
      (tsupport (ω : DifferentialForm (Eucl P) m)) h g (hrep' ω).1 hωc
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) hh.continuous
      (fun k => (hg k).continuous) hgh).sub
    (Submission.slicing_im_ll_multiplier_tendsto P μ
      (fun x => v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x))
      (tsupport (exteriorDerivative (ω : DifferentialForm (Eucl P) m))) h g
      (hrep (exteriorDerivativeTestOn U m ω)).1 (exteriorDerivative_isTestForm ⟨hωs, hωc⟩).2
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) hh.continuous
      (fun k => (hg k).continuous) hgh)
  -- Simon's (1), (3): `∫_M Dg_k(Y) dHⁿ → ∫_M ⟨G_h, Y⟩ dHⁿ`, as `Y` is tangent to `M`.
  have hlhs := Submission.slicing_im_ll_tangential_weak_limit P (m + 1) U M θ ξ hU hMθξ h Lh Gh
    hh hGm hGb hTG Y hY hYT g (fun k => (hg k).differentiable (by simp)) hgL hgh
  have hlim : ∫ x in M, inner ℝ (Gh x) (Y x) ∂(μHE[m + 1] : Measure (Eucl P)) =
      (∫ x, h x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') -
        ∫ x, h x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ :=
    tendsto_nhds_unique hlhs (hrhs.congr fun k => (hk k).symm)
  -- Finally `⟨G_h, Y⟩ = θ ⟨G_h ∧ ω, ξ⟩` pointwise (the dual property with `φ = ⟨G_h, ·⟩`).
  rw [← hlim]
  exact integral_congr_ae (Eventually.of_forall fun x => by
    dsimp only
    rw [← hYφ x (innerSL ℝ (Gh x)), innerSL_apply_apply])

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
