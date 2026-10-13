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

/-- For a.e. `t`, the slice `M ∩ f⁻¹{t}` of an `Hᵐ⁺¹`-null-measurable `M` by a measurable `f`
is `Hᵐ`-null-measurable, given that `Hᵐ⁺¹⌞M`-a.e. properties hold `Hᵐ⌞(M ∩ f⁻¹{t})`-a.e. for
a.e. `t`.  With a Borel `B ⊆ M`, `B = M` `Hᵐ⁺¹`-a.e., the slice is the Borel set `B ∩ f⁻¹{t}`
plus the part outside `B`, which is `Hᵐ`-null for a.e. `t`. -/
theorem Submission.slicing_im_st_mf_slice_null_measurable :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (f : Eucl P → ℝ),
      NullMeasurableSet M (μHE[m + 1] : Measure (Eucl P)) → Measurable f →
      (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) →
      ∀ᵐ t ∂(volume : Measure ℝ),
        NullMeasurableSet (M ∩ f ⁻¹' {t}) (μHE[m] : Measure (Eucl P)) := by
  intro P m M f hM hf hNT
  -- A Borel kernel `B ⊆ M` with `B = M` `Hᵐ⁺¹`-a.e.; then `x ∈ B` for `Hᵐ⁺¹⌞M`-a.e. `x`.
  obtain ⟨B, hBM, hB, hBM_ae⟩ := hM.exists_measurable_subset_ae_eq
  have hmemB : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ B := by
    rw [← Measure.restrict_congr_set hBM_ae]
    exact ae_restrict_mem hB
  filter_upwards [hNT (· ∈ B) hmemB] with t ht
  -- The part of the slice outside `B` is `Hᵐ`-null.
  have hnull : (μHE[m] : Measure (Eucl P)) ({x | x ∉ B} ∩ (M ∩ f ⁻¹' {t})) = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans_eq (ae_iff.1 ht))
  -- `M ∩ f⁻¹{t} = (B ∩ f⁻¹{t}) ∪ ({x ∉ B} ∩ M ∩ f⁻¹{t})`: a Borel set plus a null set.
  have hsplit : M ∩ f ⁻¹' {t} = B ∩ f ⁻¹' {t} ∪ {x | x ∉ B} ∩ (M ∩ f ⁻¹' {t}) := by
    ext x
    by_cases hx : x ∈ B
    · simp [hx, hBM hx]
    · simp [hx]
  rw [hsplit]
  exact (hB.inter (hf (measurableSet_singleton t))).nullMeasurableSet.union_null hnull
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
/-- **Integrability of the integrands of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  For a
rectifiable triple `(M, θ, ξ)` in `U`: (a) `x ↦ θ(x) ⟨b, ξ(x)⟩` is `Hᵏ`-integrable on `M ∩ K` for
every compact `K ⊆ U` and `k`-covector `b`; (b) `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hᵏ`-integrable on `M`
for every continuous compactly supported `ω` with `spt ω ⊆ U`.  Since `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ`
orthonormal, `|⟨α, ξ⟩| ≤ ‖α‖` `Hᵏ⌞M`-a.e.; `θ` is integrable on `M ∩ K`, and the integrand of
(b) vanishes on `M \ spt ω`. -/
theorem Submission.ltg_tau_integrable : ∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ → (∀ (K : Set (Eucl P)) (b : Covector (Eucl P) k), IsCompact K → K ⊆ U → IntegrableOn (fun x => θ x * ξ x b) (M ∩ K) (μHE[k] : Measure (Eucl P))) ∧ ∀ ω : Eucl P → Covector (Eucl P) k, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U → IntegrableOn (fun x => θ x * ξ x (ω x)) M (μHE[k] : Measure (Eucl P)) := by
  intro P k U M θ ξ hT
  -- Step 1: for `Hᵏ⌞M`-a.e. `x`, `|ξ(x)(α)| ≤ ‖α‖` for every covector `α`
  -- (`|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`; the empty product for `k = 0`).
  have hunit : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) k, ‖ξ x α‖ ≤ ‖α‖ := by
    filter_upwards [hT.orients] with x hx α
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hs : ‖simpleNVector τ α‖ ≤ ‖α‖ :=
      calc ‖simpleNVector τ α‖ = ‖α τ‖ := rfl
        _ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h | h
    · rw [h]; exact hs
    · rw [h, neg_apply, norm_neg]; exact hs
  -- Step 2: `x ↦ ξ(x)(ω(x))` is a.e.-strongly measurable for `Hᵏ⌞M` whenever `ω` is
  -- (continuous evaluation `(w, α) ↦ w(α)` composed with `(ξ, ω)`).
  have hmeas : ∀ ω : Eucl P → Covector (Eucl P) k,
      AEStronglyMeasurable ω ((μHE[k] : Measure (Eucl P)).restrict M) →
      AEStronglyMeasurable (fun x => ξ x (ω x)) ((μHE[k] : Measure (Eucl P)).restrict M) := by
    intro ω hω
    have hev : Continuous fun p : NVector (Eucl P) k × Covector (Eucl P) k => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    exact hev.comp_aestronglyMeasurable (hT.aestronglyMeasurable.prodMk hω)
  -- Steps 3–4: for compact `K ⊆ U` and `‖ω‖ ≤ C`, `θ` is integrable on `M ∩ K` and
  -- `ξ(·)(ω(·))` is measurable and a.e. bounded by `C` there, so the product is integrable.
  have hK : ∀ (K : Set (Eucl P)) (ω : Eucl P → Covector (Eucl P) k) (C : ℝ), IsCompact K →
      K ⊆ U → AEStronglyMeasurable ω ((μHE[k] : Measure (Eucl P)).restrict M) →
      (∀ x, ‖ω x‖ ≤ C) →
      IntegrableOn (fun x => θ x * ξ x (ω x)) (M ∩ K) (μHE[k] : Measure (Eucl P)) := by
    intro K ω C hKc hKU hω hC
    have hle : (μHE[k] : Measure (Eucl P)).restrict (M ∩ K) ≤
        (μHE[k] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono Set.inter_subset_left le_rfl
    have hθ : Integrable θ ((μHE[k] : Measure (Eucl P)).restrict (M ∩ K)) :=
      hT.integrableOn K hKc hKU
    refine hθ.mul_bdd (c := C) ((hmeas ω hω).mono_measure hle) ?_
    filter_upwards [ae_mono hle hunit] with x hx
    exact (hx (ω x)).trans (hC x)
  -- Part (a): the constant field `b`, bounded by `‖b‖`.
  refine ⟨fun K b hKc hKU => hK K (fun _ => b) ‖b‖ hKc hKU aestronglyMeasurable_const
    (fun _ => le_rfl), ?_⟩
  -- Part (b): integrable on `M ∩ spt ω` (Step 4) and zero on `M \ spt ω` (Step 5), with `M`
  -- null-measurable.
  intro ω hωc hωs hωU
  obtain ⟨C, hC⟩ := hωc.bounded_above_of_compact_support hωs
  refine (hK (tsupport ω) ω C hωs hωU hωc.aestronglyMeasurable hC).of_ae_sdiff_eq_zero
    hT.nullMeasurableSet (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∉ tsupport ω := fun h => hx.2 ⟨hx.1, h⟩
  rw [image_eq_zero_of_notMem_tsupport hx', map_zero, mul_zero]
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
/-- Passing `ofReal |X_ε(h)| ≤ ofReal ((1 + ε) / h) · LW · a(h)` to the `liminf` as `h → 0+`
and then letting `ε ↓ 0`, in `[0, ∞]`: if for every `ε > 0` some `X_ε(h) → r` as `h → 0+`
satisfies this bound for all `h > 0`, then `ofReal |r| ≤ LW · liminf_{h → 0+} a(h) / ofReal h`.
For fixed `ε`, `ofReal |r|` is the `liminf` of `ofReal |X_ε(h)|`, and
`ofReal ((1 + ε) / h) · LW · a(h) = (ofReal (1 + ε) · LW) · (a(h) / ofReal h)` for `h > 0`;
the finite constant `ofReal (1 + ε) · LW` commutes with the `liminf`, and
`ofReal (1 + ε) → 1` as `ε → 0+`. -/
theorem Submission.slicing_mb_pointwise_liminf_bound :
    ∀ (a : ℝ → ℝ≥0∞) (LW : ℝ≥0) (r : ℝ),
      (∀ ε : ℝ, 0 < ε → ∃ X : ℝ → ℝ, Tendsto X (𝓝[>] 0) (𝓝 r) ∧
        ∀ h : ℝ, 0 < h →
          ENNReal.ofReal |X h| ≤ ENNReal.ofReal ((1 + ε) / h) * (LW : ℝ≥0∞) * a h) →
      ENNReal.ofReal |r| ≤
        (LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0) := by
  intro a LW r hX
  -- For fixed `ε > 0`: `ofReal |r| ≤ ofReal (1 + ε) · (LW · liminf_{h → 0+} a(h) / ofReal h)`.
  have key : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal |r| ≤ ENNReal.ofReal (1 + ε) *
      ((LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0)) := by
    intro ε hε
    obtain ⟨X, hXr, hXb⟩ := hX ε hε
    -- `ofReal |X(h)| → ofReal |r|`, so `ofReal |r|` is the `liminf` of `ofReal |X(h)|`.
    have hlim : Tendsto (fun h => ENNReal.ofReal |X h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |r|)) :=
      ENNReal.tendsto_ofReal hXr.abs
    -- For `h > 0`: `ofReal ((1 + ε) / h) · LW · a(h) = (ofReal (1 + ε) · LW) · (a(h) / ofReal h)`.
    have hle : ∀ᶠ h in 𝓝[>] (0 : ℝ), ENNReal.ofReal |X h| ≤
        ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) * (a h / ENNReal.ofReal h) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      calc ENNReal.ofReal |X h| ≤ ENNReal.ofReal ((1 + ε) / h) * (LW : ℝ≥0∞) * a h := hXb h hh
        _ = ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) * (a h / ENNReal.ofReal h) := by
          rw [ENNReal.ofReal_div_of_pos hh, div_eq_mul_inv, div_eq_mul_inv]
          ring
    -- Monotonicity of the `liminf` and the `liminf` of a finite constant multiple.
    calc ENNReal.ofReal |r| = liminf (fun h => ENNReal.ofReal |X h|) (𝓝[>] 0) :=
          hlim.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) * (a h / ENNReal.ofReal h))
            (𝓝[>] 0) := liminf_le_liminf hle
      _ = ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) *
            liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0) :=
          ENNReal.liminf_const_mul_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.coe_ne_top)
      _ = ENNReal.ofReal (1 + ε) *
            ((LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0)) :=
          mul_assoc _ _ _
  -- `ofReal (1 + ε) · Y → Y` as `ε → 0+` (the limit factor `1` is nonzero), then `ε ↓ 0`.
  have hone : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 (1 + 0)) :=
      ((continuous_const.add continuous_id).tendsto' 0 (1 + 0) rfl).mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [add_zero, ENNReal.ofReal_one] at h2
  have hY := ENNReal.Tendsto.mul_const hone (Or.inl one_ne_zero)
    (b := (LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0))
  rw [one_mul] at hY
  exact ge_of_tendsto hY (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
/-- Sharp smooth cut-off below the level `t` (the cut-off of the proof of Simon Ch. 6, 4.11,
p. 158, with slope bound `(1 + ε)/h`): for `h, ε > 0` there is a `C^∞` function `χ : ℝ → ℝ` with
`0 ≤ χ ≤ 1`, `χ = 1` on `(-∞, t - h]`, `χ = 0` on `[t, ∞)`, `|χ'| ≤ (1 + ε)/h`, and `χ' = 0` off
`(t - h, t)`.  Take `χ = ρ ⋆ λ`: `λ` is the clamped affine profile equal to `1` on
`(-∞, t - h + κ]`, to `0` on `[t - κ, ∞)` and of slope `-(1 + ε)/h` in between
(`κ = εh/(2(1 + ε))`), and `ρ` is a normalized smooth bump supported in `(-κ/2, κ/2)`. -/
theorem Submission.slicing_mb_cutoff : ∀ (t h ε : ℝ), 0 < h → 0 < ε → ∃ χ : ℝ → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ s, 0 ≤ χ s ∧ χ s ≤ 1) ∧
    (∀ s, s ≤ t - h → χ s = 1) ∧ (∀ s, t ≤ s → χ s = 0) ∧
    (∀ s, |deriv χ s| ≤ (1 + ε) / h) ∧ (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) := by
  intro t h ε hh hε
  -- Slope `K = (1 + ε)/h`, `κ = εh/(2(1 + ε))` (so `(h - 2κ) K = 1`), mollification radius `κ/2`.
  set K : ℝ := (1 + ε) / h with hK_def
  have hK : 0 < K := by positivity
  set κ : ℝ := ε * h / (2 * (1 + ε)) with hκ_def
  have hκ : 0 < κ := by positivity
  have hκK : (h - 2 * κ) * K = 1 := by
    rw [hK_def, hκ_def]; field_simp; ring
  set r : ℝ := κ / 2 with hr_def
  have hr : 0 < r := by positivity
  set Kn : ℝ≥0 := ⟨K, hK.le⟩ with hKn_def
  have hKn : (Kn : ℝ) = K := rfl
  -- The profile `λ`: `1` on `(-∞, t - h + κ]`, `0` on `[t - κ, ∞)`, `K`-Lipschitz.
  set lam : ℝ → ℝ := fun u => min (max 0 ((t - κ - u) * K)) 1 with hlam_def
  have haff_lip : LipschitzWith Kn (fun u : ℝ => (t - κ - u) * K) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, hKn,
      show (t - κ - a) * K - (t - κ - b) * K = -((a - b) * K) by ring, abs_neg, abs_mul,
      abs_of_pos hK, mul_comm]
  have hlam_lip : LipschitzWith Kn lam := (haff_lip.const_max 0).min_const 1
  have hlam_cont : Continuous lam := hlam_lip.continuous
  have hlam01 : ∀ u, 0 ≤ lam u ∧ lam u ≤ 1 := fun u =>
    ⟨le_min (le_max_left _ _) zero_le_one, min_le_right _ _⟩
  have hlam_one : ∀ u, u < t - h + κ → lam u = 1 := by
    intro u hu
    have h1 : 1 < (t - κ - u) * K := by
      rw [← hκK]; exact mul_lt_mul_of_pos_right (by linarith) hK
    simp only [hlam_def]
    rw [max_eq_right (by linarith), min_eq_right h1.le]
  have hlam_zero : ∀ u, t - κ < u → lam u = 0 := by
    intro u hu
    have h1 : (t - κ - u) * K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hK.le
    simp only [hlam_def]
    rw [max_eq_left h1, min_eq_left zero_le_one]
  -- The mollifier `ρ = (∫ φ)⁻¹ φ`, `φ` a smooth bump with support `ball 0 r`.
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hφ_int_pos : 0 < ∫ y, φ y := by
    refine φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero φ.hasCompactSupport
      (fun y => φ.nonneg) (x := 0) ?_
    rw [φ.one_of_mem_closedBall (by simp [φ]; positivity)]
    exact one_ne_zero
  set I : ℝ := ∫ y, φ y with hI_def
  set ρ : ℝ → ℝ := fun y => I⁻¹ * φ y with hρ_def
  have hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := contDiff_const.mul φ.contDiff
  have hρ_cs : HasCompactSupport ρ := φ.hasCompactSupport.mul_left
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hρ_nonneg : ∀ y, 0 ≤ ρ y := fun y => mul_nonneg (inv_nonneg.2 hφ_int_pos.le) φ.nonneg
  have hρ_int : Integrable ρ := hρ_cont.integrable_of_hasCompactSupport hρ_cs
  have hρ_one : ∫ y, ρ y = 1 := by
    simp only [hρ_def]; rw [integral_const_mul]; exact inv_mul_cancel₀ hφ_int_pos.ne'
  have hρ_supp : ∀ y, ρ y ≠ 0 → |y| < r := by
    intro y hy
    have hy' : y ∈ Function.support φ := fun h0 => hy (by simp [hρ_def, h0])
    rw [φ.support_eq, mem_ball, Real.dist_eq, sub_zero] at hy'
    exact hy'
  -- `χ = ρ ⋆ λ`.
  set χ : ℝ → ℝ := convolution ρ lam (ContinuousLinearMap.lsmul ℝ ℝ) volume with hχ_def
  have hχ : ∀ s, χ s = ∫ y, ρ y * lam (s - y) := by
    intro s
    simp only [hχ_def, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hint : ∀ s, Integrable (fun y => ρ y * lam (s - y)) := fun s =>
    Continuous.integrable_of_hasCompactSupport
      (hρ_cont.mul (hlam_cont.comp (continuous_const.sub continuous_id))) hρ_cs.mul_right
  -- `χ = 1` on `(-∞, t - h + r)` and `χ = 0` on `(t - r, ∞)`.
  have hχ_one : ∀ s, s < t - h + r → χ s = 1 := by
    intro s hs
    rw [hχ s, ← hρ_one]
    congr 1
    funext y
    by_cases hy : ρ y = 0
    · simp [hy]
    · have := (abs_lt.1 (hρ_supp y hy)).1
      rw [hlam_one (s - y) (by linarith), mul_one]
  have hχ_zero : ∀ s, t - r < s → χ s = 0 := by
    intro s hs
    rw [hχ s]
    have : (fun y => ρ y * lam (s - y)) = fun _ => 0 := by
      funext y
      by_cases hy : ρ y = 0
      · simp [hy]
      · have := (abs_lt.1 (hρ_supp y hy)).2
        rw [hlam_zero (s - y) (by linarith), mul_zero]
    rw [this, integral_zero]
  -- `χ` is `K`-Lipschitz, since `λ` is and `ρ` is a probability density.
  have hχ_lip : LipschitzWith Kn χ := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, hχ a, hχ b, ← integral_sub (hint a) (hint b),
      ← Real.norm_eq_abs]
    calc ‖∫ y, (ρ y * lam (a - y) - ρ y * lam (b - y))‖ ≤ ∫ y, ρ y * (K * |a - b|) := by
          refine norm_integral_le_of_norm_le (hρ_int.mul_const _)
            (Eventually.of_forall fun y => ?_)
          rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hρ_nonneg y)]
          refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg y)
          have := hlam_lip.dist_le_mul (a - y) (b - y)
          rw [Real.dist_eq, Real.dist_eq, hKn, sub_sub_sub_cancel_right] at this
          exact this
      _ = ↑Kn * |a - b| := by rw [integral_mul_const, hρ_one, one_mul, hKn]
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ_cs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ_smooth
      hlam_cont.locallyIntegrable
  · intro s
    rw [hχ s]
    refine ⟨integral_nonneg fun y => mul_nonneg (hρ_nonneg y) (hlam01 _).1, ?_⟩
    calc ∫ y, ρ y * lam (s - y) ≤ ∫ y, ρ y :=
          integral_mono (hint s) hρ_int fun y =>
            mul_le_of_le_one_right (hρ_nonneg y) (hlam01 _).2
      _ = 1 := hρ_one
  · intro s hs
    exact hχ_one s (by linarith)
  · intro s hs
    exact hχ_zero s (by linarith)
  · intro s
    have := norm_deriv_le_of_lipschitz (x₀ := s) hχ_lip
    rwa [Real.norm_eq_abs, hKn] at this
  · intro s hs
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · have hev : χ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show s < t - h + r by linarith)] with u hu
        exact hχ_one u hu
      rw [hev.deriv_eq, deriv_const]
    · have hev : χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (show t - r < s by linarith)] with u hu
        exact hχ_zero u hu
      rw [hev.deriv_eq, deriv_const]
/-- Simon Ch. 6, proof of 4.8–4.9 (p. 158): the integral bounding the right side of 4.11, for a
differentiable approximation `g` of `f` (Simon's `f^{(σ)}`):
`∫ |D(χ ∘ g)| |ω| dμ ≤ c L_W μ(spt ω ∩ {t − h − δ < f < t + δ})` when `|ω| ≤ 1`,
`|g − f| ≤ δ` and `‖Dg‖ ≤ L_W` on `spt ω`, `|χ'| ≤ c` and `χ' = 0` off `(t − h, t)`.
Off `spt ω` the integrand vanishes.  On `spt ω` the chain rule gives
`‖D(χ ∘ g)(x)‖ ≤ |χ'(g x)| ‖Dg(x)‖`; this is `0` unless `t − h < g x < t`, and then
`t − h − δ < f x < t + δ` and the bound is `c L_W`.  Integrate the indicator bound. -/
theorem Submission.slicing_mb_cdb_grad_lintegral_le :
    ∀ (P m : ℕ) (μ : Measure (Eucl P)) (ω : DifferentialForm (Eucl P) m) (f g : Eucl P → ℝ) (LW : ℝ≥0) (χ : ℝ → ℝ) (t h c δ : ℝ), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → Differentiable ℝ g → Differentiable ℝ χ → (∀ x ∈ tsupport ω, |g x - f x| ≤ δ) → (∀ x ∈ tsupport ω, ‖fderiv ℝ g x‖₊ ≤ LW) → (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) → ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) * ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ ≤ ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ)) := by
  intro P m μ ω f g LW χ t h c δ hω hg hχ hgf hDg hc hband
  set E := tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ)
  set a : ℝ≥0∞ := ENNReal.ofReal c * (LW : ℝ≥0∞)
  -- `c ≥ |χ'(0)| ≥ 0`.
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- Pointwise bound of the integrand by `1_E · a`.
  have hpt : ∀ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (covectorEuclideanNorm (ω x)) ≤ E.indicator (fun _ => a) x := by
    intro x
    by_cases hxK : x ∈ tsupport ω
    · -- Chain rule: `D(χ ∘ g)(x) = Dχ(g x) ∘ Dg(x)`.
      have hchain : fderiv ℝ (fun y => χ (g y)) x = (fderiv ℝ χ (g x)).comp (fderiv ℝ g x) :=
        fderiv_fun_comp x (hχ (g x)) (hg x)
      by_cases hgx : g x ∈ Ioo (t - h) t
      · -- `t − h < g x < t` and `|g x − f x| ≤ δ` put `x` in `E`.
        have hxE : x ∈ E := by
          refine ⟨hxK, ?_⟩
          have hab := abs_le.mp (hgf x hxK)
          rw [mem_Ioo] at hgx
          rw [mem_preimage, mem_Ioo]
          constructor <;> linarith [hgx.1, hgx.2, hab.1, hab.2]
        rw [indicator_of_mem hxE]
        have hnorm : ‖fderiv ℝ (fun y => χ (g y)) x‖ ≤ c * LW := by
          rw [hchain]
          calc ‖(fderiv ℝ χ (g x)).comp (fderiv ℝ g x)‖
              ≤ ‖fderiv ℝ χ (g x)‖ * ‖fderiv ℝ g x‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ c * LW := by
              apply mul_le_mul _ _ (norm_nonneg _) hc0
              · rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
                exact hc _
              · exact_mod_cast hDg x hxK
        have h1 : (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) ≤ a := by
          calc (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞)
              = ENNReal.ofReal ‖fderiv ℝ (fun y => χ (g y)) x‖ := (ofReal_norm _).symm
            _ ≤ ENNReal.ofReal (c * LW) := ENNReal.ofReal_le_ofReal hnorm
            _ = a := by rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal]
        have h2 : ENNReal.ofReal (covectorEuclideanNorm (ω x)) ≤ 1 :=
          ENNReal.ofReal_le_one.mpr (hω x)
        calc (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (covectorEuclideanNorm (ω x))
            ≤ a * 1 := mul_le_mul' h1 h2
          _ = a := mul_one _
      · -- `χ'(g x) = 0`, so `Dχ(g x) = 0` and `D(χ ∘ g)(x) = 0`.
        have hfd : fderiv ℝ χ (g x) = 0 := by
          rw [← norm_eq_zero, ← norm_deriv_eq_norm_fderiv, hband _ hgx, norm_zero]
        rw [hchain, hfd]
        simp
    · -- Off `spt ω`, `ω x = 0`.
      have h0 : ω x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0]
  calc ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ
      ≤ ∫⁻ x, E.indicator (fun _ => a) x ∂μ := lintegral_mono hpt
    _ ≤ a * μ E := lintegral_indicator_const_le _ _
/-- Continuity from above for the shrinking level bands (parent proof, Step 6).  With
`δ_j = 1/(j+1)`, the sets `E_j = K ∩ f⁻¹((a − δ_j, b + δ_j))` are Borel (`K` is closed and
`f` is continuous on `K`), decrease in `j`, have intersection `K ∩ f⁻¹([a, b])`, and
`μ(E_0) ≤ μ(K) < ∞`; so `μ(E_j) → μ(K ∩ f⁻¹([a, b]))`. -/
theorem Submission.slicing_mb_cdb_band_measure_tendsto :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (K : Set (Eucl P)) (f : Eucl P → ℝ) (a b : ℝ),
      IsClosed K → ContinuousOn f K → μ K < ∞ →
        Tendsto
          (fun j : ℕ => μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))))
          atTop (𝓝 (μ (K ∩ f ⁻¹' Icc a b))) := by
  intro P μ K f a b hK hf hμK
  -- `E_j = K \ (K ∩ f⁻¹((a − δ_j, b + δ_j)ᶜ))` is Borel.
  have hmeas : ∀ j : ℕ,
      MeasurableSet (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))) := by
    intro j
    have hcl :
        IsClosed (K ∩ f ⁻¹' (Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))ᶜ) :=
      hf.preimage_isClosed_of_isClosed hK isOpen_Ioo.isClosed_compl
    have heq : K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) =
        K \ (K ∩ f ⁻¹' (Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))ᶜ) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [heq]
    exact hK.measurableSet.diff hcl.measurableSet
  -- `δ_j` decreases, so the bands decrease.
  have hanti : Antitone fun j : ℕ =>
      K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) := by
    intro i j hij x hx
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := Nat.one_div_le_one_div hij
    simp only [mem_inter_iff, mem_preimage, mem_Ioo] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  -- `⋂_j E_j = K ∩ f⁻¹([a, b])`.
  have hinter :
      ⋂ j : ℕ, K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) =
        K ∩ f ⁻¹' Icc a b := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Ioo, mem_Icc]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_, ?_⟩
      · by_contra! hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        linarith [(h j).2.1]
      · by_contra! hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        linarith [(h j).2.2]
    · rintro ⟨hxK, hax, hxb⟩ j
      have hδ : 0 < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
      exact ⟨hxK, by linarith, by linarith⟩
  -- `μ(E_0) ≤ μ(K) < ∞`; continuity from above.
  have hfin : ∃ j : ℕ,
      μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))) ≠ ∞ :=
    ⟨0, ((measure_mono inter_subset_left).trans_lt hμK).ne⟩
  have h := tendsto_measure_iInter_atTop (fun j => (hmeas j).nullMeasurableSet) hanti hfin
  rw [hinter] at h
  exact h
/-- Dominated convergence for the bounded continuous multipliers `χ(g_j)` against an integrable
density `F` (the limit `σ ↓ 0` in the cutoff defect bound of the slice mass estimate, Simon Ch. 6,
4.9–4.10): if `F` vanishes off `K` and `g_j → f` on `K`, then `∫ χ(g_j) F dν → ∫ χ(f) F dν`.
The integrands are dominated by `|F|` since `|χ| ≤ 1`, and converge everywhere: on `K` by
continuity of `χ`, off `K` because `F = 0`. -/
theorem Submission.slicing_mb_cdb_multiplier_integral_tendsto :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) (F : Eucl P → ℝ) (K : Set (Eucl P)) (f : Eucl P → ℝ)
      (g : ℕ → Eucl P → ℝ) (χ : ℝ → ℝ), Integrable F ν → (∀ x, x ∉ K → F x = 0) →
      (∀ j, Measurable (g j)) → (∀ x ∈ K, Tendsto (fun j => g j x) atTop (𝓝 (f x))) →
      Continuous χ → (∀ s, |χ s| ≤ 1) →
      Tendsto (fun j => ∫ x, χ (g j x) * F x ∂ν) atTop (𝓝 (∫ x, χ (f x) * F x ∂ν)) := by
  intro P ν F K f g χ hF hFK hg hgf hχ hχ1
  refine tendsto_integral_of_dominated_convergence (fun x => ‖F x‖) (fun j => ?_) hF.norm
    (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · -- `χ ∘ g j` is measurable and `F` is integrable.
    exact (hχ.measurable.comp (hg j)).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · -- `|χ| ≤ 1`.
    rw [norm_mul, Real.norm_eq_abs (χ (g j x))]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 _)
  · -- On `K` by continuity of `χ`; off `K` both sides vanish.
    by_cases hx : x ∈ K
    · exact ((hχ.tendsto (f x)).comp (hgf x hx)).mul_const (F x)
    · simp only [hFK x hx, mul_zero]
      exact tendsto_const_nhds
/-- The mollifier behind Simon's `f^{(σ)}` (Ch. 6, §4, p. 158; parent Step 4): a smooth,
nonnegative, compactly supported `ρ` vanishing off `B(0, σ)` with `∫ ρ = 1`.  Take the bump `φ`
centred at `0` with radii `σ/2 < σ`; then `support φ = B(0, σ)`, so `c = ∫ φ > 0` and
`ρ = c⁻¹ φ` works. -/
theorem Submission.slicing_mb_sa_mollifier_exists :
    ∀ (P : ℕ) (σ : ℝ), 0 < σ → ∃ ρ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧ (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) ∧
      ∫ y, ρ y = 1 := by
  intro P σ hσ
  -- The smooth bump `φ` centred at `0` with `support φ = B(0, σ)`.
  let φ : ContDiffBump (0 : Eucl P) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
  have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  -- Its mass `c = ∫ φ` is positive since `B(0, σ)` has positive Lebesgue measure.
  have hc : 0 < ∫ y, φ y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
    exact measure_ball_pos _ _ hσ
  refine ⟨fun y => (∫ y, φ y)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, fun y => mul_nonneg (inv_nonneg.2 hc.le) φ.nonneg,
    fun y hy => mul_eq_zero_of_right _ (φ.zero_of_le_dist (by rwa [dist_zero_right])), ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hc.ne']
/-- **Uniform error of a mollified Lipschitz function** (Simon Ch. 6, 4.11, p. 158: "use
`f^{(σ)}` in place of `f`").  If `F` is `L`-Lipschitz and `ρ ≥ 0` is continuous with compact
support, `ρ(y) = 0` for `|y| ≥ σ` and `∫ ρ = 1`, then `|∫ ρ(y) F(x − y) dy − F(x)| ≤ L σ`.
As `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`, and pointwise
`|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L |y| ≤ ρ(y) L σ`, since `ρ(y) ≠ 0` forces `|y| < σ`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_close : ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ (ρ : Eucl P → ℝ) (σ : ℝ), Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) → ∫ y, ρ y = 1 → ∀ x : Eucl P, |(∫ y, ρ y * F (x - y)) - F x| ≤ (L : ℝ) * σ := by
  intro P F L hF ρ σ hρc hρs hρ0 hρσ hρ1 x
  -- `ρ` and `y ↦ ρ(y) F(x − y)` are continuous with compact support, hence integrable.
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hgi : Integrable fun y => ρ y * F (x - y) :=
    (hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρs.mul_right
  -- Since `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`.
  have herr : (∫ y, ρ y * F (x - y)) - F x = ∫ y, ρ y * (F (x - y) - F x) := by
    simp_rw [mul_sub]
    rw [integral_sub hgi (hρi.mul_const (F x)), integral_mul_const, hρ1, one_mul]
  -- Pointwise `|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L σ`.
  have hpt : ∀ y, ‖ρ y * (F (x - y) - F x)‖ ≤ ρ y * ((L : ℝ) * σ) := by
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    -- `ρ(y) ≠ 0` forces `|y| < σ`.
    have hyσ : ‖y‖ ≤ σ := (not_le.mp fun h => hy (hρσ y h)).le
    have hlip : |F (x - y) - F x| ≤ (L : ℝ) * σ := by
      rw [← Real.dist_eq]
      calc dist (F (x - y)) (F x) ≤ (L : ℝ) * dist (x - y) x := hF.dist_le_mul _ _
        _ = (L : ℝ) * ‖y‖ := by rw [dist_self_sub_left]
        _ ≤ (L : ℝ) * σ := mul_le_mul_of_nonneg_left hyσ L.coe_nonneg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
    exact mul_le_mul_of_nonneg_left hlip (hρ0 y)
  -- Integrate the pointwise bound, using `∫ ρ = 1` once more.
  rw [herr, ← Real.norm_eq_abs]
  calc ‖∫ y, ρ y * (F (x - y) - F x)‖ ≤ ∫ y, ρ y * ((L : ℝ) * σ) :=
        norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall hpt)
    _ = (L : ℝ) * σ := by rw [integral_mul_const, hρ1, one_mul]
/-- Differentiation under the integral sign for the mollification of a globally Lipschitz `F`
by a continuous compactly supported `ρ`: `D(∫ ρ(y) F(· - y) dy)(x) = ∫ ρ(y) DF(x - y) dy`.
By Rademacher's theorem and the invariance of Lebesgue measure under `y ↦ x - y`, `F` is
differentiable at `x - y` for a.e. `y`; `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz on `ℝ^P`
with integrable majorant `L |ρ|`, so `hasFDerivAt_integral_of_dominated_loc_of_lip` applies
with `s = ℝ^P`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt :
    ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ ρ : Eucl P → ℝ, Continuous ρ →
      HasCompactSupport ρ → ∀ x : Eucl P,
        HasFDerivAt (fun x' : Eucl P => ∫ y, ρ y * F (x' - y))
          (∫ y, ρ y • fderiv ℝ F (x - y)) x := by
  intro P F L hF ρ hρc hρs x
  -- Rademacher, pulled back along the measure-preserving map `y ↦ x - y`.
  have hae : ∀ᵐ y : Eucl P, DifferentiableAt ℝ F (x - y) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      hF.ae_differentiableAt
  -- `y ↦ ρ(y) F(x' - y)` is continuous for every `x'`.
  have hcont : ∀ x' : Eucl P, Continuous fun y : Eucl P => ρ y * F (x' - y) := fun x' =>
    hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))
  -- `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz for every `y`.
  have hlip : ∀ y : Eucl P,
      LipschitzOnWith (Real.nnabs (L * |ρ y|)) (fun x' : Eucl P => ρ y * F (x' - y)) univ := by
    refine fun y => (LipschitzWith.of_dist_le_mul fun a b => ?_).lipschitzOnWith
    calc dist (ρ y * F (a - y)) (ρ y * F (b - y)) = |ρ y| * dist (F (a - y)) (F (b - y)) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      _ ≤ |ρ y| * (L * dist (a - y) (b - y)) := by gcongr; exact hF.dist_le_mul _ _
      _ = Real.nnabs (L * |ρ y|) * dist a b := by
          rw [dist_sub_right, Real.coe_nnabs, abs_mul, abs_abs, NNReal.abs_eq]; ring
  -- For a.e. `y`, the chain rule gives the derivative `ρ(y) DF(x - y)` at `x`.
  have hderiv : ∀ᵐ y : Eucl P,
      HasFDerivAt (fun x' : Eucl P => ρ y * F (x' - y)) (ρ y • fderiv ℝ F (x - y)) x := by
    filter_upwards [hae] with y hy
    have h := hy.hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_mul (ρ y)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip univ_mem
    (Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable)
    ((hcont x).integrable_of_hasCompactSupport hρs.mul_right)
    (hρc.measurable.smul ((measurable_fderiv ℝ F).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall hlip)
    ((hρc.abs.integrable_of_hasCompactSupport hρs.abs).const_mul _) hderiv).2

/-- Simon Ch. 6, 4.11 ("use `f^{(σ)}` in place of `f`") on a compact `K ⊆ W`: if `f` is
`L`-Lipschitz on the open set `W` and `‖Df‖ ≤ LW` a.e. on `W`, then some `C^∞` function `g` is
`δ`-close to `f` on `K` with `‖Dg‖ ≤ LW` on `K`.  Here `g = ρ ⋆ F` mollifies a McShane extension
`F` of `f|W` with a kernel supported in a ball small enough that `x - y ∈ W` whenever `x ∈ K` and
`ρ(y) ≠ 0`. -/
theorem Submission.slicing_mb_smooth_approx :
    ∀ (P : ℕ) (W : Set (Eucl P)), IsOpen W → ∀ (f : Eucl P → ℝ) (L : ℝ≥0),
      LipschitzOnWith L f W → ∀ LW : ℝ≥0,
      (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ W → ∀ δ : ℝ, 0 < δ →
      ∃ g : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∀ x ∈ K, |g x - f x| ≤ δ) ∧
        (∀ x ∈ K, ‖fderiv ℝ g x‖₊ ≤ LW) := by
  intro P W hW f L hf LW hLW K hK hKW δ hδ
  -- The closed `r`-neighbourhood of `K` lies in `W`.
  obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hW hKW
  -- McShane extension: `F` is `L`-Lipschitz on `ℝ^P` and `F = f` on `W`.
  obtain ⟨F, hFL, hfF⟩ := hf.extend_real
  -- The mollification radius: `σ ≤ r` keeps `x - y` in `W`, and `L σ ≤ δ`.
  obtain ⟨σ, hσ, hσr, hσδ⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ r ∧ (L : ℝ) * σ ≤ δ := by
    refine ⟨min r (δ / ((L : ℝ) + 1)), lt_min hr (div_pos hδ (by positivity)), min_le_left _ _, ?_⟩
    calc (L : ℝ) * min r (δ / ((L : ℝ) + 1)) ≤ (L : ℝ) * (δ / ((L : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) L.coe_nonneg
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [L.coe_nonneg]
  obtain ⟨ρ, hρ, hρc, hρ0, hρσ, hρ1⟩ := Submission.slicing_mb_sa_mollifier_exists P σ hσ
  have hρi : Integrable ρ (volume : Measure (Eucl P)) :=
    hρ.continuous.integrable_of_hasCompactSupport hρc
  refine ⟨fun x => ∫ y, ρ y * F (x - y), ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- `g = ρ ⋆ F` is `C^∞`: `ρ` is `C^∞` with compact support and `F` is continuous.
    have hconv : (fun x => ∫ y, ρ y * F (x - y)) =
        convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Eucl P)) := by
      funext x
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [hconv]
    exact hρc.contDiff_convolution_left _ hρ hFL.continuous.locallyIntegrable
  · -- `|g - F| ≤ L σ ≤ δ` everywhere, and `F = f` on `K ⊆ W`.
    rw [hfF (hKW hx)]
    exact (Submission.slicing_mb_sa_mollify_lipschitz_close P F L hFL ρ σ hρ.continuous hρc hρ0
      hρσ hρ1 x).trans hσδ
  · -- `Dg(x) = ∫ ρ(y) DF(x - y) dy`; for a.e. `y` with `ρ(y) ≠ 0`, `x - y ∈ W` and
    -- `‖DF(x - y)‖ = ‖Df(x - y)‖ ≤ LW` (`y ↦ x - y` preserves Lebesgue measure).
    have hDg : fderiv ℝ (fun x => ∫ y, ρ y * F (x - y)) x = ∫ y, ρ y • fderiv ℝ F (x - y) :=
      (Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt P F L hFL ρ hρ.continuous hρc
        x).fderiv
    rw [hDg, ← NNReal.coe_le_coe, coe_nnnorm]
    have hae : ∀ᵐ y ∂(volume : Measure (Eucl P)),
        x - y ∈ W → ‖fderiv ℝ f (x - y)‖₊ ≤ LW :=
      ((volume : Measure (Eucl P)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hLW
    have hbd : ∀ᵐ y ∂(volume : Measure (Eucl P)),
        ‖ρ y • fderiv ℝ F (x - y)‖ ≤ ρ y * LW := by
      filter_upwards [hae] with y hy
      rw [norm_smul, Real.norm_of_nonneg (hρ0 y)]
      rcases eq_or_ne (ρ y) 0 with h0 | h0
      · simp [h0]
      have hyσ : ‖y‖ < σ := not_le.mp fun h => h0 (hρσ y h)
      have hxy : x - y ∈ W := hrW (mem_cthickening_of_dist_le _ x r K hx (by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact hyσ.le.trans hσr))
      have hD : fderiv ℝ F (x - y) = fderiv ℝ f (x - y) :=
        (hfF.symm.eventuallyEq_of_mem (hW.mem_nhds hxy)).fderiv_eq
      rw [hD]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy hxy) (hρ0 y)
    calc ‖∫ y, ρ y • fderiv ℝ F (x - y)‖ ≤ ∫ y, ‖ρ y • fderiv ℝ F (x - y)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, ρ y * (LW : ℝ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hρi.mul_const _) hbd
      _ = LW := by rw [integral_mul_const, hρ1, one_mul]
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

/-- For `L¹`-a.e. `t`, `θ` is `Hᵐ`-integrable on `M ∩ f⁻¹{t} ∩ K` for every compact `K ⊆ U`:
co-area with `g = 1_{Kᵢ} |θ₀|` over a compact exhaustion `Kᵢ` of `U`, `θ₀` a Borel version of
`θ` on `M`, transferred to the slices by the null-transfer hypothesis. -/
theorem Submission.slicing_im_st_mf_slice_integrable :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (f : Eucl P → ℝ) (L : ℝ≥0)
      (G : Eucl P → Eucl P), IsOpen U → M ⊆ U →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) →
      (∀ x, ‖G x‖ ≤ L) →
      (∀ g : Eucl P → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
          (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) =
          ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) →
      (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) →
      ∀ᵐ t ∂(volume : Measure ℝ), ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ (M ∩ f ⁻¹' {t} ∩ K) (μHE[m] : Measure (Eucl P)) := by
  intro P m U M θ f L G hU hMU hθ hG hCA hNT
  -- Compact Borel sets `closure (W i) ⊆ U`; every compact `C ⊆ U` lies in one of them.
  obtain ⟨W, hW, hWK⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
  have hKU : ∀ i, closure (W i) ⊆ U := fun i => (hW i).2.2
  have hKm : ∀ i, MeasurableSet (closure (W i)) := fun _ => isClosed_closure.measurableSet
  have hK : ∀ C : Set (Eucl P), IsCompact C → C ⊆ U → ∃ i, C ⊆ closure (W i) := fun C hC hCU =>
    (hWK C hC hCU).imp fun _ h => h.trans subset_closure
  -- `θ` is a.e. strongly measurable on `M = ⋃ i, M ∩ closure (W i)`; `θ₀` is a Borel version.
  have hM : M = ⋃ i, M ∩ closure (W i) := by
    refine (iUnion_subset fun _ => inter_subset_left).antisymm' fun x hx => ?_
    obtain ⟨i, hi⟩ := hK {x} isCompact_singleton (singleton_subset_iff.2 (hMU hx))
    exact mem_iUnion.2 ⟨i, hx, hi rfl⟩
  have hθm : AEStronglyMeasurable θ ((μHE[m + 1] : Measure (Eucl P)).restrict M) := by
    rw [hM, aestronglyMeasurable_iUnion_iff]
    exact fun i => (hθ _ (hW i).2.1 (hKU i)).aestronglyMeasurable
  obtain ⟨θ₀, hθ₀, hθθ₀⟩ := hθm
  have hGL : ∀ x, ‖G x‖ₑ ≤ (L : ℝ≥0∞) := fun x =>
    enorm_le_coe.2 (NNReal.coe_le_coe.1 (by simpa only [coe_nnnorm] using hG x))
  -- Co-area with `g = 1_{closure (W i)} ‖θ₀‖ₑ`: `∫ J_i dt ≤ L ∫_{M ∩ closure (W i)} ‖θ‖ₑ < ∞`,
  -- so the slice integral `J_i t` is finite for a.e. `t`, simultaneously for all `i`.
  have hfin : ∀ᵐ t ∂(volume : Measure ℝ), ∀ i, ∫⁻ x in M ∩ f ⁻¹' {t},
      (closure (W i)).indicator (fun y => ‖θ₀ y‖ₑ) x ∂(μHE[m] : Measure (Eucl P)) < ∞ := by
    refine ae_all_iff.2 fun i => ?_
    obtain ⟨hJm, hJ⟩ := hCA _ (hθ₀.measurable.enorm.indicator (hKm i))
    refine ae_lt_top' hJm (ne_top_of_le_ne_top ?_ hJ.le)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => mul_le_mul_left (hGL x) _)
    have h₁ : ∫⁻ x in M ∩ closure (W i), ‖θ x‖ₑ ∂(μHE[m + 1] : Measure (Eucl P)) =
        ∫⁻ x in M ∩ closure (W i), ‖θ₀ x‖ₑ ∂(μHE[m + 1] : Measure (Eucl P)) :=
      lintegral_congr_ae ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hθθ₀).mono
        fun x hx => congrArg (‖·‖ₑ) hx)
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_indicator (hKm i),
      Measure.restrict_restrict (hKm i), inter_comm (closure (W i)), ← h₁]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hθ _ (hW i).2.1 (hKU i)).2.ne
  -- For such `t` (with `θ = θ₀` a.e. on the slice), `θ` is integrable on each
  -- `M ∩ f⁻¹{t} ∩ closure (W i)`, hence on `M ∩ f⁻¹{t} ∩ K`.
  filter_upwards [hNT (fun x => θ x = θ₀ x) hθθ₀, hfin] with t ht hti K hKc hKsub
  obtain ⟨i, hi⟩ := hK K hKc hKsub
  have hS : ∀ᵐ x ∂(μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t} ∩ closure (W i)),
      θ x = θ₀ x := ae_restrict_of_ae_restrict_of_subset inter_subset_left ht
  have h₂ : ∫⁻ x in M ∩ f ⁻¹' {t} ∩ closure (W i), ‖θ x‖ₑ ∂(μHE[m] : Measure (Eucl P)) =
      ∫⁻ x in M ∩ f ⁻¹' {t}, (closure (W i)).indicator (fun y => ‖θ₀ y‖ₑ) x
        ∂(μHE[m] : Measure (Eucl P)) := by
    rw [lintegral_indicator (hKm i), Measure.restrict_restrict (hKm i),
      inter_comm (closure (W i))]
    exact lintegral_congr_ae (hS.mono fun x hx => congrArg (‖·‖ₑ) hx)
  have hint : IntegrableOn θ (M ∩ f ⁻¹' {t} ∩ closure (W i)) (μHE[m] : Measure (Eucl P)) :=
    ⟨hθ₀.aestronglyMeasurable.congr (hS.mono fun x hx => hx.symm), h₂.trans_lt (hti i)⟩
  exact hint.mono_set (inter_subset_inter_right _ hi)
/-- Null transfer to slices (Simon Ch. 6, §4; Step 1 of the slice triple): under the co-area
identity for `(M, f, G)`, a property holding `H^{m+1}`-a.e. on `M` holds `H^m`-a.e. on
`M ∩ f⁻¹{t}` for `L¹`-a.e. `t`.  Apply the co-area identity to the indicator of a measurable
null hull `Z` of `{¬p}`: the right side vanishes, so `H^m⌞(M ∩ f⁻¹{t})(Z) = 0` for a.e. `t`. -/
theorem Submission.slicing_im_st_ae_transfer :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (f : Eucl P → ℝ) (G : Eucl P → Eucl P),
      (∀ g : Eucl P → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
          (volume : Measure ℝ) ∧
        ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) =
          ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) →
      ∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x := by
  intro P m M f G hcoarea p hp
  -- A measurable null hull `Z` of the exceptional set `{¬p}` for `H^{m+1}⌞M`.
  set Z := toMeasurable ((μHE[m + 1] : Measure (Eucl P)).restrict M) {x | ¬p x}
  have hZ : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hZ0 : (μHE[m + 1] : Measure (Eucl P)).restrict M Z = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hp
  -- The co-area identity for `g = 1_Z`; its right side vanishes.
  obtain ⟨hmeas, hint⟩ := hcoarea (Z.indicator 1) (measurable_one.indicator hZ)
  have hright : ∫⁻ x in M, ‖G x‖ₑ * Z.indicator 1 x ∂(μHE[m + 1] : Measure (Eucl P)) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ0] with x hx
    simp [hx]
  rw [hright, lintegral_eq_zero_iff' hmeas] at hint
  -- For a.e. `t`, `H^m⌞(M ∩ f⁻¹{t})(Z) = 0`, and `{¬p} ⊆ Z`.
  filter_upwards [hint] with t ht
  rw [Pi.zero_apply, lintegral_indicator_one hZ] at ht
  exact ae_iff.2 (measure_mono_null (subset_toMeasurable _ _) ht)
/-- `v ↦ ι(v)`, `ι(v) α = alternatizeUncurryFin ((innerSL ℝ v).smulRight α) = v♭ ∧ α`, is
`(m + 1)`-Lipschitz from `ℝ^P` to `Λ^m →L Λ^{m+1}` with the operator norm. -/
theorem Submission.slicing_im_st_mf_contraction_lipschitz :
    ∀ (P m : ℕ), LipschitzWith ((m : ℝ≥0) + 1) (fun v : Eucl P =>
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ v))) := by
  intro P m
  let ι : Eucl P → (Covector (Eucl P) m →L[ℝ] Covector (Eucl P) (m + 1)) := fun v =>
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
      (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ v))
  -- Step 1: `ι(v) α = alternatizeUncurryFin ((innerSL ℝ v).smulRight α)` by definition.
  have hform (v : Eucl P) (α : Covector (Eucl P) m) :
      ι v α = ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ v).smulRight α) := rfl
  -- Step 2: `ι(v) - ι(w) = ι(v - w)`, checked at every `α` and `σ = (σ₀, …, σₘ)`.
  have hsub (v w : Eucl P) : ι v - ι w = ι (v - w) := by
    ext α σ
    simp only [_root_.sub_apply, ContinuousAlternatingMap.sub_apply, hform,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousAlternatingMap.smul_apply, innerSL_apply_apply, inner_sub_left, sub_smul,
      smul_sub, Finset.sum_sub_distrib]
  -- Step 3: `‖ι(u)‖ ≤ (m + 1) |u|`.
  have hnorm (u : Eucl P) : ‖ι u‖ ≤ ((m : ℝ) + 1) * ‖u‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
    rw [hform]
    calc ‖ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ u).smulRight α)‖
        ≤ ((m : ℝ) + 1) * ‖(innerSL ℝ u).smulRight α‖ :=
          ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _
      _ = ((m : ℝ) + 1) * ‖u‖ * ‖α‖ := by
          rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_assoc]
  -- Step 4: `dist (ι v) (ι w) = ‖ι (v - w)‖ ≤ (m + 1) dist v w`.
  change LipschitzWith ((m : ℝ≥0) + 1) ι
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [dist_eq_norm, dist_eq_norm, hsub, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  exact hnorm (v - w)

/-- For `L¹`-a.e. `t`, the sliced orientation `x ↦ ξ(x) ∘ ι(|G x|⁻¹ G x)`, where
`ι v = (v♭ ∧ ·) : Λᵐ → Λᵐ⁺¹`, is a.e. strongly measurable for `Hᵐ` on `M ∩ f⁻¹{t}`:
it agrees there with `x ↦ ξ₀(x) ∘ ι(|G x|⁻¹ G x)` for a strongly measurable version `ξ₀` of `ξ`. -/
theorem Submission.slicing_im_st_mf_slice_orientation_aesm :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ)
      (G : Eucl P → Eucl P),
      AEStronglyMeasurable ξ ((μHE[m + 1] : Measure (Eucl P)).restrict M) → Measurable G →
      (∀ p : Eucl P → Prop, (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x) →
        ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})), p x) →
      ∀ᵐ t ∂(volume : Measure ℝ), AEStronglyMeasurable (fun x => (ξ x).comp
        ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
          (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)
            (innerSL ℝ (‖G x‖⁻¹ • G x)))))
        ((μHE[m] : Measure (Eucl P)).restrict (M ∩ f ⁻¹' {t})) := by
  intro P m M ξ f G hξ hG hNT
  -- `x ↦ ι(|G x|⁻¹ G x)` is strongly measurable: `ι` is Lipschitz and `G` is measurable.
  have hν : StronglyMeasurable fun x => ‖G x‖⁻¹ • G x :=
    (hG.norm.inv.smul hG).stronglyMeasurable
  have hιν := (Submission.slicing_im_st_mf_contraction_lipschitz P m).continuous
    |>.comp_stronglyMeasurable hν
  -- With `ξ₀` a strongly measurable version of `ξ`, `F x = ξ₀ x ∘ ι(|G x|⁻¹ G x)` is strongly
  -- measurable, as operator composition is continuous.
  have hF : StronglyMeasurable fun x => (hξ.mk ξ x).comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)
          (innerSL ℝ (‖G x‖⁻¹ • G x)))) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
      (hξ.stronglyMeasurable_mk.prodMk hιν)
  -- Null transfer of `ξ = ξ₀` to the slices; there `F` agrees a.e. with the sliced orientation.
  filter_upwards [hNT (fun x => ξ x = hξ.mk ξ x) hξ.ae_eq_mk] with t ht
  exact hF.aestronglyMeasurable.congr (ht.mono fun x hx => by simp only [hx])

/-- Measure-theoretic fields of the slice triple (Simon Ch. 6, §4; Steps 2, 4, 5 and 6 of the
slice triple): under the co-area identity for `(M, f, G)`, for `L¹`-a.e. `t` the set
`M_t = {x ∈ M : f x = t, G x ≠ 0}` is `H^m`-null-measurable, `θ` is `H^m`-integrable on
`M_t ∩ K` for every compact `K ⊆ U`, and `ξ_t = ξ ∘ ι(|G|⁻¹ G)` is `H^m⌞M_t`-a.e. strongly
measurable.  The null transfer moves the fields of `(M, θ, ξ)` to the whole slice
`M ∩ f⁻¹{t}`, and `M_t = (M ∩ f⁻¹{t}) ∩ G⁻¹{0}ᶜ` inherits them. -/
theorem Submission.slicing_im_st_measure_fields : ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → Measurable f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) → ∀ᵐ t ∂(volume : Measure ℝ), NullMeasurableSet {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} (μHE[m] : Measure (Eucl P)) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ ({x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ∩ K) (μHE[m] : Measure (Eucl P))) ∧ AEStronglyMeasurable (fun x => (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))) ((μHE[m] : Measure (Eucl P)).restrict {x | x ∈ M ∧ f x = t ∧ G x ≠ 0}) := by
  intro P m U M θ ξ f L G hU hT hf hG hGL hcoarea
  -- Null transfer: `H^{m+1}⌞M`-a.e. properties hold `H^m⌞(M ∩ f⁻¹{t})`-a.e. for a.e. `t`.
  have hNT := Submission.slicing_im_st_ae_transfer P m M f G hcoarea
  -- The three fields on the whole slice `M ∩ f⁻¹{t}`, each for a.e. `t`.
  have hnull := Submission.slicing_im_st_mf_slice_null_measurable P m M f hT.nullMeasurableSet
    hf hNT
  have hint := Submission.slicing_im_st_mf_slice_integrable P m U M θ f L G hU hT.subset
    hT.integrableOn hGL hcoarea hNT
  have haesm := Submission.slicing_im_st_mf_slice_orientation_aesm P m M ξ f G
    hT.aestronglyMeasurable hG hNT
  filter_upwards [hnull, hint, haesm] with t hnull_t hint_t haesm_t
  -- `M_t = (M ∩ f⁻¹{t}) ∩ G⁻¹{0}ᶜ`, a subset of the slice.
  have hMt : {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} = M ∩ f ⁻¹' {t} ∩ G ⁻¹' {0}ᶜ :=
    Set.ext fun _ => and_assoc.symm
  have hsub : {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ⊆ M ∩ f ⁻¹' {t} := fun x hx => ⟨hx.1, hx.2.1⟩
  refine ⟨?_, fun K hK hKU => (hint_t K hK hKU).mono_set (inter_subset_inter_left K hsub),
    haesm_t.mono_set hsub⟩
  rw [hMt]
  exact hnull_t.inter (hG (measurableSet_singleton 0).compl).nullMeasurableSet
/-- Compression estimate behind the critical-set step of the area formula (Simon Ch. 2, 3.2–3.4,
pp. 53–54, via the approximation argument of [Har79], [Fed69]).  If `f` is `t²`-close on `S` to a
non-injective linear map `A` (`0 < t ≤ 1`), then `Hⁿ(f(S)) ≤ (‖A‖ + t)ⁿ · t Lⁿ(S)`: for a unit
vector `e ∈ ker A`, the compression `T x = x + (t - 1)⟨e, x⟩ e` has `det T = t`, and `f ∘ T⁻¹` is
`(‖A‖ + t)`-Lipschitz on `T(S)`. -/
theorem Submission.slicing_im_st_cd_c1c_singular_compression :
    ∀ (n P : ℕ) (f : Eucl n → Eucl P) (A : Eucl n →L[ℝ] Eucl P) (S : Set (Eucl n)) (t : ℝ≥0),
      0 < t → t ≤ 1 → ¬ Function.Injective A → ApproximatesLinearOn f A S (t ^ 2) →
        (μHE[n] : Measure (Eucl P)) (f '' S) ≤
          ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * (volume : Measure (Eucl n)) S) := by
  intro n P f A S t ht0 ht1 hA hf
  -- A unit vector `e` with `A e = 0`.
  obtain ⟨e, he1, hAe⟩ : ∃ e : Eucl n, ‖e‖ = 1 ∧ A e = 0 := by
    simp only [Function.Injective, not_forall] at hA
    obtain ⟨x, y, hxy, hne⟩ := hA
    have hv : x - y ≠ 0 := sub_ne_zero.2 hne
    refine ⟨(‖x - y‖⁻¹ : ℝ) • (x - y), norm_smul_inv_norm hv, ?_⟩
    rw [map_smul, map_sub, hxy, sub_self, smul_zero]
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he1, one_pow]
  have ht0' : (0 : ℝ) < t := ht0
  have ht1' : (t : ℝ) ≤ 1 := ht1
  -- The compression `T x = x + (t - 1)⟨e, x⟩ e` and its inverse `T' x = x + (t⁻¹ - 1)⟨e, x⟩ e`.
  let T : Eucl n →ₗ[ℝ] Eucl n := LinearMap.id + ((t : ℝ) - 1) • (innerₛₗ ℝ e).smulRight e
  let T' : Eucl n →ₗ[ℝ] Eucl n := LinearMap.id + ((t : ℝ)⁻¹ - 1) • (innerₛₗ ℝ e).smulRight e
  have hT : ∀ x, T x = x + (((t : ℝ) - 1) * inner ℝ e x) • e := fun x => by
    simp [T, mul_smul]
  have hT' : ∀ x, T' x = x + (((t : ℝ)⁻¹ - 1) * inner ℝ e x) • e := fun x => by
    simp [T', mul_smul]
  have hT'T : ∀ x, T' (T x) = x := fun x => by
    rw [hT', hT, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul]
    convert add_zero x
    convert zero_smul ℝ e
    field_simp
    ring
  -- `det T = t`: in the standard basis, `T` has matrix `1 + u wᵀ` with `u = (t - 1) e`, `w = e`.
  have hdet : LinearMap.det T = t := by
    classical
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    rw [← LinearMap.det_toMatrix b]
    have hM : LinearMap.toMatrix b b T = 1 + Matrix.replicateCol Unit
        (fun i => ((t : ℝ) - 1) * e.ofLp i) * Matrix.replicateRow Unit (fun j => e.ofLp j) := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp [b, T, Matrix.one_apply, Matrix.mul_apply, EuclideanSpace.inner_single_right]
      ring
    have h2 : ∑ i, e.ofLp i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, he1, one_pow]
    rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct]
    calc 1 + ∑ i, e.ofLp i * (((t : ℝ) - 1) * e.ofLp i)
        = 1 + ((t : ℝ) - 1) * ∑ i, e.ofLp i ^ 2 := by
          rw [Finset.mul_sum]
          exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
      _ = t := by rw [h2]; ring
  -- `Lⁿ(T(S)) = t Lⁿ(S)`.
  have hvol : (volume : Measure (Eucl n)) (T '' S) = (t : ℝ≥0∞) * volume S := by
    rw [MeasureTheory.Measure.addHaar_image_linearMap, hdet, abs_of_pos ht0',
      ENNReal.ofReal_coe_nnreal]
  -- `f ∘ T'` is `(‖A‖ + t)`-Lipschitz on `T(S)`: for `x, y ∈ S`, `A (x - y) = A (T x - T y)` and
  -- `‖x - y‖ ≤ t⁻¹ ‖T x - T y‖`.
  have hlip : LipschitzOnWith (‖A‖₊ + t) (f ∘ T') (T '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hT'T, dist_eq_norm]
    have hw : x - y = T' (T x - T y) := by rw [← map_sub, hT'T]
    have hAw : A (x - y) = A (T x - T y) := by
      rw [hw, hT', map_add, map_smul, hAe, smul_zero, add_zero]
    have hxy : ‖x - y‖ ≤ (t : ℝ)⁻¹ * ‖T x - T y‖ := by
      have hc : 0 ≤ (t : ℝ)⁻¹ - 1 := sub_nonneg.2 (one_le_inv_iff₀.2 ⟨ht0', ht1'⟩)
      have hi : |inner ℝ e (T x - T y)| ≤ ‖T x - T y‖ := by
        simpa [he1] using abs_real_inner_le_norm e (T x - T y)
      rw [hw, hT']
      calc ‖(T x - T y) + (((t : ℝ)⁻¹ - 1) * inner ℝ e (T x - T y)) • e‖
          ≤ ‖T x - T y‖ + ‖(((t : ℝ)⁻¹ - 1) * inner ℝ e (T x - T y)) • e‖ := norm_add_le _ _
        _ = ‖T x - T y‖ + ((t : ℝ)⁻¹ - 1) * |inner ℝ e (T x - T y)| := by
          rw [norm_smul, he1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
        _ ≤ ‖T x - T y‖ + ((t : ℝ)⁻¹ - 1) * ‖T x - T y‖ := by gcongr
        _ = (t : ℝ)⁻¹ * ‖T x - T y‖ := by ring
    have happrox : ‖f x - f y - A (x - y)‖ ≤ (t : ℝ) ^ 2 * ‖x - y‖ := by
      simpa using hf x hx y hy
    calc ‖f x - f y‖ = ‖A (x - y) + (f x - f y - A (x - y))‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖A (x - y)‖ + ‖f x - f y - A (x - y)‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖T x - T y‖ + (t : ℝ) ^ 2 * ((t : ℝ)⁻¹ * ‖T x - T y‖) := by
          gcongr
          · rw [hAw]
            exact A.le_opNorm _
          · exact happrox.trans (by gcongr)
      _ = ((‖A‖₊ + t : ℝ≥0) : ℝ) * ‖T x - T y‖ := by
          rw [sq, mul_assoc, mul_inv_cancel_left₀ ht0'.ne', NNReal.coe_add, coe_nnnorm, add_mul]
  -- `f(S) = (f ∘ T')(T(S))`; the Lipschitz image bound and `Hⁿ = Lⁿ` on `ℝⁿ` conclude.
  have himage : f '' S = (f ∘ T') '' (T '' S) := by
    rw [Set.image_image]
    exact (Set.image_congr fun x _ => by simp only [Function.comp_apply, hT'T]).symm
  calc (μHE[n] : Measure (Eucl P)) (f '' S) = μHE[n] ((f ∘ T') '' (T '' S)) := by rw [himage]
    _ ≤ ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (T '' S) :=
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
    _ = ((‖A‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * (volume : Measure (Eucl n)) S) := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvol]

/-- Simon Ch. 2, 3.4 (p. 54) on the critical set, the Sard-type step of the proof of Ch. 3,
Lemma 1.2 (p. 70): the Jacobian `Jf` vanishes where `Df` is not injective, so if `f : ℝⁿ → ℝ^P`
is Lipschitz and `C` is the set of points where `f` is differentiable with non-injective
derivative, then `Hⁿ(f(C)) = 0`.  Proved directly: on pieces where `f` is `t²`-close to a
non-injective `Df(y)`, `Hⁿ(f(·)) ≤ (L + 1)ⁿ · t · Lⁿ(·)`; sum the pieces and let `t → 0`. -/
theorem Submission.slicing_im_st_cd_c1c_critical_image_null :
    ∀ (n P : ℕ) (f : Eucl n → Eucl P) (L : ℝ≥0), LipschitzWith L f →
      (μHE[n] : Measure (Eucl P))
        (f '' {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}) = 0 := by
  intro n P f L hf
  -- Step 2: if `s ⊆ B(0, m)` consists of points where `f` is differentiable with non-injective
  -- derivative, then `Hⁿ(f(s)) ≤ (L + 1)ⁿ · (t · Lⁿ(B(0, m)))` for every `0 < t ≤ 1`.
  have hstep : ∀ (m : ℝ) (s : Set (Eucl n)), s ⊆ ball 0 m →
      (∀ x ∈ s, DifferentiableAt ℝ f x ∧ ¬ Function.Injective (fderiv ℝ f x)) →
      ∀ t : ℝ≥0, 0 < t → t ≤ 1 → (μHE[n] : Measure (Eucl P)) (f '' s) ≤
        ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume (ball (0 : Eucl n) m)) := by
    intro m s hsm hsC t ht0 ht1
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    -- Disjoint measurable `T i` covering `s`, with `f` `t²`-close to `A i = Df(y i)` on `s ∩ T i`.
    obtain ⟨T, A, hTd, hTm, hsT, hTA, hAy⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
        (fun x hx => (hsC x hx).1.hasFDerivAt.hasFDerivWithinAt) (fun _ => t ^ 2)
        (fun _ => pow_ne_zero 2 ht0.ne')
    -- `A i` is not injective and `‖A i‖ ≤ L`, so `singular_compression` bounds `Hⁿ(f(s ∩ T i))`.
    have hpiece : ∀ i, (μHE[n] : Measure (Eucl P)) (f '' (s ∩ T i)) ≤
        ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume (ball (0 : Eucl n) m ∩ T i)) := by
      intro i
      obtain ⟨y, hy, hAi⟩ := hAy hs i
      have hinj : ¬ Function.Injective (A i) := hAi ▸ (hsC y hy).2
      have hnorm : ‖A i‖₊ ≤ L := by
        rw [hAi, ← NNReal.coe_le_coe, coe_nnnorm]
        exact norm_fderiv_le_of_lipschitz ℝ hf
      calc (μHE[n] : Measure (Eucl P)) (f '' (s ∩ T i))
          ≤ ((‖A i‖₊ + t : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume (s ∩ T i)) :=
            Submission.slicing_im_st_cd_c1c_singular_compression n P f (A i) (s ∩ T i) t ht0 ht1
              hinj (hTA i)
        _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume (ball (0 : Eucl n) m ∩ T i)) := by
            -- `gcongr` closes its goals with `hnorm`, `ht1` and `hsm : s ⊆ B(0, m)`.
            gcongr
    -- Sum over the pieces, using that the sets `B(0, m) ∩ T i` are disjoint and measurable.
    calc (μHE[n] : Measure (Eucl P)) (f '' s)
        ≤ (μHE[n] : Measure (Eucl P)) (⋃ i, f '' (s ∩ T i)) := by
          refine measure_mono ?_
          rw [← image_iUnion, ← inter_iUnion]
          exact image_mono (subset_inter subset_rfl hsT)
      _ ≤ ∑' i, (μHE[n] : Measure (Eucl P)) (f '' (s ∩ T i)) := measure_iUnion_le _
      _ ≤ ∑' i, ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n *
            ((t : ℝ≥0∞) * volume (ball (0 : Eucl n) m ∩ T i)) := ENNReal.tsum_le_tsum hpiece
      _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n *
            ((t : ℝ≥0∞) * volume (⋃ i, ball (0 : Eucl n) m ∩ T i)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, measure_iUnion
            (fun i j hij => (hTd hij).mono inter_subset_right inter_subset_right)
            (fun i => measurableSet_ball.inter (hTm i))]
      _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * ((t : ℝ≥0∞) * volume (ball (0 : Eucl n) m)) := by
          gcongr
          exact iUnion_subset fun i => inter_subset_left
  -- Step 3: with `t = (k + 1)⁻¹ → 0` and `Lⁿ(B(0, m)) < ∞`, `Hⁿ(f(s)) = 0` for such `s`.
  have hnull : ∀ (m : ℝ) (s : Set (Eucl n)), s ⊆ ball 0 m →
      (∀ x ∈ s, DifferentiableAt ℝ f x ∧ ¬ Function.Injective (fderiv ℝ f x)) →
      (μHE[n] : Measure (Eucl P)) (f '' s) = 0 := by
    intro m s hsm hsC
    have hinv : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hlim : Tendsto (fun k : ℕ => ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n *
        ((((k + 1 : ℕ) : ℝ≥0∞))⁻¹ * volume (ball (0 : Eucl n) m))) atTop
        (𝓝 (((L + 1 : ℝ≥0) : ℝ≥0∞) ^ n * (0 * volume (ball (0 : Eucl n) m)))) :=
      ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const hinv (Or.inr measure_ball_lt_top.ne))
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    rw [zero_mul, mul_zero] at hlim
    refine le_antisymm (ge_of_tendsto' hlim fun k => ?_) zero_le
    have hk : ((k + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
    have := hstep m s hsm hsC ((k + 1 : ℕ) : ℝ≥0)⁻¹ (inv_pos.2 (by positivity))
      (inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.succ_pos k)))
    rwa [ENNReal.coe_inv hk, ENNReal.coe_natCast] at this
  -- Step 1: `f(C) ⊆ ⋃ₘ f(C ∩ B(0, m))`, a countable union of `Hⁿ`-null sets.
  have hcover : f '' {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)} ⊆
      ⋃ m : ℕ, f '' ({w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)} ∩
        ball 0 m) := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
    exact mem_iUnion.2 ⟨m, w, ⟨hw, mem_ball_zero_iff.2 hm⟩, rfl⟩
  exact measure_mono_null hcover
    (measure_iUnion_null fun m => hnull m _ inter_subset_right fun x hx => hx.1)
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
/-- **Mass estimate from a normalized measure representation** (Simon Ch. 6, (2.7)).  If
`T(η) = ∫ ⟨η, v⟩ dμ` for every test form `η` and `|⟨α, v(x)⟩| ≤ |α|` for every `x` and every
`n`-covector `α` (Euclidean coefficient norm), then `|T(η)| ≤ ∫ |η| dμ` in `[0, ∞]`. -/
theorem Submission.slicing_mb_lb_repr_bound : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → (∀ (x : Eucl P) (α : Covector (Eucl P) n), |v x α| ≤ covectorEuclideanNorm α) → ∀ η : TestFormOn U n, ENNReal.ofReal |T η| ≤ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x)) ∂μ := by
  intro P n U T μ v hrep hv η
  -- Step 1: `T(η) = ∫ ⟨η(x), v(x)⟩ dμ(x)` by the representation (2.7).
  rw [(hrep η).2, ← Real.enorm_eq_ofReal_abs]
  -- Step 2: `‖∫ g dμ‖ₑ ≤ ∫⁻ ‖g‖ₑ dμ`, which needs no integrability hypothesis.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
  -- Steps 3–4: pointwise `‖⟨η(x), v(x)⟩‖ₑ = ofReal |⟨η(x), v(x)⟩| ≤ ofReal |η(x)|`.
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hv x _)
/-- Counting identity: for any family `u` of vectors of `ℝ^P` and any `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = k! ∑_{I strictly increasing} φ(u_{I 0}, …, u_{I (k-1)})²`,
where `I` ranges over all maps `Fin k → Fin P`. -/
theorem Submission.slicing_mb_wn_sq_sum_eq_factorial_mul :
    ∀ (P k : ℕ) (u : Fin P → Eucl P) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        (k.factorial : ℝ) * ∑ I : Fin k → Fin P,
          if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  classical
  set g : (Fin k → Fin P) → ℝ := fun I => (φ (fun i => u (I i))) ^ 2
  -- A non-injective `I` repeats a vector of `u ∘ I`, so `φ (u ∘ I) = 0`.
  have h0 : ∀ I : Fin k → Fin P, ¬Function.Injective I → g I = 0 := by
    intro I hI
    have hv : ¬Function.Injective (fun i => u (I i)) :=
      fun h => hI fun a b hab => h (by simp only [hab])
    simp only [g, φ.map_eq_zero_of_not_injective _ hv, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  -- `φ (u ∘ I ∘ σ) = sign σ • φ (u ∘ I)`, so the square is invariant under permutations.
  have hperm : ∀ (I : Fin k → Fin P) (σ : Equiv.Perm (Fin k)), g (I ∘ σ) = g I := by
    intro I σ
    have h : φ (fun i => u ((I ∘ σ) i)) = Equiv.Perm.sign σ • φ (fun i => u (I i)) :=
      φ.toAlternatingMap.map_perm (fun i => u (I i)) σ
    simp only [g, h]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h' <;> simp [h']
  -- Write both sides as sums over the injective, resp. strictly increasing, maps.
  have hL : ∑ I, g I = ∑ I ∈ Finset.univ.filter Function.Injective, g I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · exact h0 I h
  have hR : (∑ I : Fin k → Fin P, if StrictMono I then g I else 0) =
      ∑ I ∈ Finset.univ.filter StrictMono, g I := (Finset.sum_filter _ _).symm
  -- `(σ, β) ↦ β ∘ σ` is a bijection from permutations × strictly increasing maps onto the
  -- injective maps, with inverse `I ↦ ((sort I)⁻¹, I ∘ sort I)`.
  have hbij : ∑ I ∈ Finset.univ.filter Function.Injective, g I =
      ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))) ×ˢ Finset.univ.filter StrictMono,
        g (p.2 ∘ p.1) := by
    refine Finset.sum_nbij' (fun I => ((Tuple.sort I)⁻¹, I ∘ Tuple.sort I))
      (fun p => p.2 ∘ p.1) ?_ ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
      exact (Tuple.monotone_sort I).strictMono_of_injective (hI.comp (Tuple.sort I).injective)
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.injective.comp σ.injective
    · intro I _
      funext i
      simp
    · rintro ⟨σ, β⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] at hp
      -- sorting `β ∘ σ` recovers the strictly increasing `β`
      have hsorted : (β ∘ σ) ∘ Tuple.sort (β ∘ σ) = β := by
        rw [Tuple.comp_perm_comp_sort_eq_comp_sort,
          (Tuple.sort_eq_refl_iff_monotone).2 hp.monotone]
        rfl
      have hσ : σ * Tuple.sort (β ∘ σ) = 1 := by
        ext i
        have := congrFun hsorted i
        simp only [Function.comp_apply] at this
        simpa using congrArg Fin.val (hp.injective this)
      have hinv : (Tuple.sort (β ∘ σ))⁻¹ = σ := by
        rw [inv_eq_iff_eq_inv]
        exact eq_inv_of_mul_eq_one_right hσ
      simp only [hinv, hsorted]
    · intro I _
      congr 1
      funext i
      simp
  -- Each permutation contributes `∑_β g β`, and there are `k!` permutations.
  rw [hL, hbij, hR, Finset.sum_product]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- Basis independence of the full coefficient sum (Parseval's identity, one slot at a time): for
orthonormal bases `u`, `v` of `ℝ^P` and a `k`-covector `φ`,
`∑_I φ(u_{I 0}, …, u_{I (k-1)})² = ∑_I φ(v_{I 0}, …, v_{I (k-1)})²`, both sums over all index maps
`I : Fin k → Fin P`.  Induction on `k`: write `I = (i, J)` and `φ(w_I) = (φ.curryLeft w_i)(w_J)`,
replace `u` by `v` in the last `k` slots by the induction hypothesis for `φ.curryLeft (u i)`, then
in slot `0` by `OrthonormalBasis.norm_dual` for the functional `z ↦ (φ.curryLeft z)(v_J)`. -/
theorem Submission.slicing_mb_wn_sq_sum_onb_invariant :
    ∀ (P k : ℕ) (u v : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      ∑ I : Fin k → Fin P, (φ (fun i => u (I i))) ^ 2 =
        ∑ I : Fin k → Fin P, (φ (fun i => v (I i))) ^ 2 := by
  intro P k u v
  induction k with
  | zero =>
    -- Both families are the empty tuple.
    intro φ
    exact Fintype.sum_congr _ _ fun I => by
      rw [Subsingleton.elim (fun i => u (I i)) (fun i => v (I i))]
  | succ k ih =>
    intro φ
    -- Split `I = Fin.cons i J`; then `φ(w_I) = (φ.curryLeft w_i)(w_J)`.
    have hsplit : ∀ w : OrthonormalBasis (Fin P) ℝ (Eucl P),
        ∑ I : Fin (k + 1) → Fin P, (φ (fun i => w (I i))) ^ 2 =
          ∑ i : Fin P, ∑ J : Fin k → Fin P, (φ.curryLeft (w i) (fun j => w (J j))) ^ 2 := by
      intro w
      rw [← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Fin P).sum_comp]
      refine Fintype.sum_congr _ _ fun p => ?_
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
          Matrix.cons_val_succ]
    -- Slots `1, …, k`: the induction hypothesis for each `k`-covector `φ.curryLeft (u i)`.
    rw [hsplit u, hsplit v]
    simp_rw [ih]
    -- Slot `0`: for each `J`, Parseval for `ℓ_J z = (φ.curryLeft z)(v_J)` in the bases `u`, `v`.
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun J => ?_
    let ℓ : StrongDual ℝ (Eucl P) :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (fun j => v (J j))).comp φ.curryLeft
    have hu := u.norm_dual ℓ
    have hv := v.norm_dual ℓ
    simp only [ℓ, ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.apply_apply] at hu hv
    rw [← hu, ← hv]

/-- The Euclidean coefficient norm of a `k`-covector can be computed in any orthonormal basis
`u` of `ℝ^P` (Simon Ch. 6, 1.5–1.6 and Remark 2.6): `|φ|² = ∑_{I increasing} φ(u_I)²`.
With `e` the standard basis used by `covectorEuclideanNorm` and `N_w(φ) = ∑_{all I} φ(w_I)²`,
`k! |φ|² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`, and `k! ≠ 0`. -/
theorem Submission.slicing_mb_wn_norm_sq_eq_onb_sum :
    ∀ (P k : ℕ) (u : OrthonormalBasis (Fin P) ℝ (Eucl P)) (φ : Covector (Eucl P) k),
      covectorEuclideanNorm φ ^ 2 =
        ∑ I : Fin k → Fin P, if StrictMono I then (φ (fun i => u (I i))) ^ 2 else 0 := by
  intro P k u φ
  -- `k! ∑_{I increasing} φ(e_I)² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`.
  have key := (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k
      (EuclideanSpace.basisFun (Fin P) ℝ) φ).symm.trans
    ((Submission.slicing_mb_wn_sq_sum_onb_invariant P k
      (EuclideanSpace.basisFun (Fin P) ℝ) u φ).trans
        (Submission.slicing_mb_wn_sq_sum_eq_factorial_mul P k u φ))
  -- `|φ|² = ∑_{I increasing} φ(e_I)²`: the radicand is a sum of squares and zeros.
  rw [covectorEuclideanNorm, Real.sq_sqrt]
  · exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) key
  · exact Finset.sum_nonneg fun I _ => by split_ifs <;> positivity
/-- Every continuous linear functional `α` on `ℝ^P` has an adapted orthonormal basis `u`:
`α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`. -/
theorem Submission.slicing_mb_wn_adapted_onb :
    ∀ (P : ℕ) (α : Eucl P →L[ℝ] ℝ), ∃ u : OrthonormalBasis (Fin P) ℝ (Eucl P),
      ∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then ‖α‖ else 0 := by
  intro P α
  by_cases hα : α = 0
  · -- `α = 0`: the standard basis works, since `‖α‖ = 0`.
    exact ⟨EuclideanSpace.basisFun (Fin P) ℝ, fun j => by simp [hα]⟩
  -- The Riesz vector `a` of `α`: `α z = ⟪a, z⟫` and `‖a‖ = ‖α‖ > 0`.
  set a : Eucl P := (InnerProductSpace.toDual ℝ (Eucl P)).symm α
  have hαa : ∀ z, α z = inner ℝ a z := fun z => InnerProductSpace.toDual_symm_apply.symm
  have hna : ‖a‖ = ‖α‖ := LinearIsometryEquiv.norm_map _ _
  have hpos : 0 < ‖a‖ := hna ▸ norm_pos_iff.mpr hα
  have ha0 : a ≠ 0 := norm_pos_iff.mp hpos
  -- `a ≠ 0` forces `P ≥ 1`, so the index `0` exists.
  have hP : 0 < P := by
    have := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mpr ⟨a, ha0⟩
    rwa [finrank_euclideanSpace_fin] at this
  set i₀ : Fin P := ⟨0, hP⟩
  -- Extend the unit vector `‖a‖⁻¹ • a`, placed at index `i₀`, to an orthonormal basis `u`.
  obtain ⟨u, hu⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := Eucl P) (by simp) (v := fun _ => ‖a‖⁻¹ • a) (s := {i₀})
    (by
      rw [orthonormal_subsingleton_iff]
      intro i
      exact norm_smul_inv_norm ha0)
  have hu₀ : u i₀ = ‖a‖⁻¹ • a := hu i₀ (Set.mem_singleton _)
  have haU : a = ‖a‖ • u i₀ := by rw [hu₀, smul_inv_smul₀ hpos.ne']
  -- `α(uⱼ) = ‖a‖ ⟪u₀, uⱼ⟫`, which is `‖a‖ = ‖α‖` for `j = 0` and `0` otherwise.
  refine ⟨u, fun j => ?_⟩
  rw [hαa, haU, real_inner_smul_left]
  split_ifs with hj
  · have : j = i₀ := Fin.ext hj
    subst this
    rw [real_inner_self_eq_norm_sq, u.orthonormal.norm_eq_one, one_pow, mul_one, hna]
  · have : i₀ ≠ j := fun h => hj (by rw [← h])
    rw [u.orthonormal.inner_eq_zero this, mul_zero]
/-- Coefficient sum of `α ∧ γ` on a family adapted to `α`: if `α (u j)` is `c` for `j = 0` and
`0` otherwise, then `∑_{I increasing} ((α ∧ γ)(u_I))² ≤ c² ∑_{J increasing} γ(u_J)²`, where
`α ∧ γ = alternatizeUncurryFin (α.smulRight γ)`.  The family `u` need not be orthonormal. -/
theorem Submission.slicing_mb_wn_adapted_sum_le :
    ∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m) (u : Fin P → Eucl P) (c : ℝ), (∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then c else 0) → (∑ I : Fin (m + 1) → Fin P, if StrictMono I then (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2 else 0) ≤ c ^ 2 * ∑ I : Fin m → Fin P, if StrictMono I then (γ (fun i => u (I i))) ^ 2 else 0 := by
  intro P m α γ u c hα
  -- Steps 1–2: on a strictly increasing `I`, every term of the wedge formula with `i ≥ 1`
  -- vanishes, because `I i > I 0 ≥ 0` forces `α (u (I i)) = 0`.
  have hval : ∀ I : Fin (m + 1) → Fin P, StrictMono I →
      ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i)) =
        α (u (I 0)) * γ (fun j => u (I j.succ)) := by
    intro I hI
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
      Finset.sum_eq_zero fun i _ => ?_, add_zero]
    · simp only [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero,
        ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rfl
    · have h : ((I 0 : Fin P) : ℕ) < (I i.succ : ℕ) := hI (Fin.succ_pos i)
      have h0 : ((I i.succ : Fin P) : ℕ) ≠ 0 := by omega
      simp [hα, h0]
  -- Step 3: the summands of the left side vanish unless `I` is strictly increasing with
  -- `I 0 = 0`, where they equal `c ^ 2 * γ (u ∘ I ∘ succ) ^ 2`.
  have hL : ∀ I : Fin (m + 1) → Fin P,
      (if StrictMono I then
        (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2
        else 0) =
      if StrictMono I ∧ ((I 0 : Fin P) : ℕ) = 0 then
        c ^ 2 * (γ (fun j => u (I j.succ))) ^ 2 else 0 := by
    intro I
    by_cases hI : StrictMono I
    · rw [hval I hI, hα (I 0)]
      by_cases h0 : ((I 0 : Fin P) : ℕ) = 0 <;> simp [hI, h0, mul_pow]
    · simp [hI]
  rw [Finset.sum_congr rfl fun I _ => hL I, ← Finset.sum_filter, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  -- Steps 4–5: `I ↦ I ∘ succ` is injective on `{I | StrictMono I ∧ I 0 = 0}` and maps it into
  -- the strictly increasing `m`-tuples; the remaining summands are nonnegative squares.
  have hinj : Set.InjOn (fun (I : Fin (m + 1) → Fin P) (j : Fin m) => I j.succ)
      (Finset.univ.filter fun I : Fin (m + 1) → Fin P =>
        StrictMono I ∧ ((I 0 : Fin P) : ℕ) = 0) := by
    intro I hI I' hI' h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hI hI'
    funext i
    refine Fin.cases ?_ (fun j => congrFun h j) i
    exact Fin.ext (hI.2.trans hI'.2.symm)
  rw [← Finset.sum_filter,
    ← Finset.sum_image (f := fun J : Fin m → Fin P => (γ (fun i => u (J i))) ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun J _ _ => sq_nonneg _
  intro J hJ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
  obtain ⟨I, ⟨hI, _⟩, rfl⟩ := hJ
  exact hI.comp Fin.strictMono_succ

/-- The wedge estimate behind the bound on the right side of Simon Ch. 6, 4.11 (proof of 4.8–4.9):
for a covector `α` and an `m`-covector `γ` on `ℝ^P`, the Euclidean coefficient norm of
`α ∧ γ = alternatizeUncurryFin (α.smulRight γ)` is at most `‖α‖ |γ|`.  The coefficient norm can
be computed in any orthonormal basis.  In a basis `u` with `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for
`j ≠ 0`, the coefficients of `α ∧ γ` are `‖α‖` times coefficients of `γ` on pairwise distinct
multi-indices, so `|α ∧ γ|² ≤ ‖α‖² |γ|²`. -/
theorem Submission.slicing_mb_wedge_norm_le :
    ∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m),
      covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ)) ≤
        ‖α‖ * covectorEuclideanNorm γ := by
  intro P m α γ
  -- An orthonormal basis adapted to `α`: `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`.
  obtain ⟨u, hu⟩ := Submission.slicing_mb_wn_adapted_onb P α
  refine (sq_le_sq₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (norm_nonneg α) (covectorEuclideanNorm_nonneg γ))).1 ?_
  -- Both squared norms are sums over increasing multi-indices in `u`, and there
  -- `Σ_{I incr} (α ∧ γ)(u_I)² ≤ ‖α‖² Σ_{J incr} γ(u_J)²`.
  rw [mul_pow, Submission.slicing_mb_wn_norm_sq_eq_onb_sum P (m + 1) u,
    Submission.slicing_mb_wn_norm_sq_eq_onb_sum P m u]
  exact Submission.slicing_mb_wn_adapted_sum_le P m α γ u ‖α‖ hu
/-- **Boundary defect of a smooth multiplier** (Simon Ch. 6, 4.11, with the representation
estimate (2.7) and the wedge bound): if `(μ, v)` represents `T ∈ 𝒟ₘ₊₁(U)` with
`|⟨α, v⟩| ≤ |α|`, `ω ∈ 𝒟ᵐ(U)` and `ψ` is `C^∞`, then `η₁ = ψω` and `η₂ = ψ dω` are test forms
with `|∂T(η₁) − T(η₂)| ≤ ∫ |Dψ| |ω| dμ`.  The Leibniz rule `d(ψω) = ψ dω + Dψ ∧ ω` gives
`∂T(η₁) − T(η₂) = T(Dψ ∧ ω)`, bounded by the representation and `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|`. -/
theorem Submission.slicing_mb_leibniz_bound :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
      (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
      ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ (η₁ : TestFormOn U m) (η₂ : TestFormOn U (m + 1)),
        (∀ x, (η₁ : DifferentialForm (Eucl P) m) x = ψ x • (ω : DifferentialForm (Eucl P) m) x) ∧
        (∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x =
          ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∧
        ENNReal.ofReal |T.boundary η₁ - T η₂| ≤
          ∫⁻ x, (‖fderiv ℝ ψ x‖₊ : ℝ≥0∞) *
            ENNReal.ofReal (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x)) ∂μ := by
  intro P m U T μ v hrep hnorm ω ψ hψ
  -- The test forms `η₁ = ψ ω`, `η₂ = ψ dω` and `η₃ = Dψ ∧ ω` in `U`.
  obtain ⟨η₁, hη₁⟩ := Submission.slicing_mb_lb_smul_testForm P m U ω ψ hψ
  obtain ⟨η₂, hη₂⟩ :=
    Submission.slicing_mb_lb_smul_testForm P (m + 1) U (exteriorDerivativeTestOn U m ω) ψ hψ
  obtain ⟨η₃, hη₃⟩ :=
    Submission.slicing_mb_lb_wedge_testForm P m U ω (fderiv ℝ ψ) (hψ.fderiv_right (by simp))
  have hη₂' : ∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x =
      ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x := hη₂
  refine ⟨η₁, η₂, hη₁, hη₂', ?_⟩
  -- Leibniz rule: `dη₁ = ψ dω + Dψ ∧ ω = η₂ + η₃`.
  have hd : exteriorDerivativeTestOn U m η₁ = η₂ + η₃ := by
    apply Subtype.ext
    funext x
    have h₁ : (η₁ : DifferentialForm (Eucl P) m) =
        fun y => ψ y • (ω : DifferentialForm (Eucl P) m) y := funext hη₁
    change exteriorDerivative (η₁ : DifferentialForm (Eucl P) m) x =
      (η₂ : DifferentialForm (Eucl P) (m + 1)) x + (η₃ : DifferentialForm (Eucl P) (m + 1)) x
    rw [h₁, hη₂', hη₃, Submission.slicing_mb_lb_extDeriv_smul P m ψ
      (ω : DifferentialForm (Eucl P) m) x (hψ.differentiable (by simp) x)
      (ω.2.1.1.differentiable (by simp) x)]
  -- Hence `∂T(η₁) − T(η₂) = T(η₃)`.
  have hb : T.boundary η₁ - T η₂ = T η₃ := by
    rw [GeometricCurrentOn.boundary_apply, hd, map_add, add_sub_cancel_left]
  -- The representation bound for `T(η₃)`, then `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|` pointwise.
  rw [hb]
  refine (Submission.slicing_mb_lb_repr_bound P (m + 1) U T μ v hrep hnorm η₃).trans
    (lintegral_mono fun x => ?_)
  rw [hη₃, ← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Submission.slicing_mb_wedge_norm_le P m _ _)
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

/-- The cut-off defect bound in the proof of Simon Ch. 6, 4.9 for Lipschitz `f` (4.11 and the
bound of its right side, p. 158, with `f^{(σ)}` in place of `f`, then `σ ↓ 0`).  Let
`K = spt ω ⊆ W`, `|ω| ≤ 1`, `|v| ≤ 1` on covectors, `|Df| ≤ L_W` a.e. on the open `W ⊆ U`, and
`|χ| ≤ 1`, `|χ'| ≤ c`, `χ' = 0` off `(t - h, t)`.  Then
`|∫ χ(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ(f) ⟨dω, v₁⟩ dμ₁| ≤ c L_W μ(K ∩ {t - h ≤ f ≤ t})`, i.e.
`∂T(χ(f) ω) - T(χ(f) dω)` computed through the representations of `∂T` and `T`.  For smooth
`g_j` with `|g_j - f| ≤ 1/(j+1)` and `|Dg_j| ≤ L_W` on `K`, 4.11 for `ψ_j = χ ∘ g_j` gives the
bound with the band `K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)}`; let `j → ∞` by dominated
convergence on the left and continuity from above on the right. -/
theorem Submission.slicing_mb_cutoff_defect_bound :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) →
      (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
      ∀ (μ₁ : Measure (Eucl P)) (v₁ : Eucl P → NVector (Eucl P) (m + 1)),
      IsMeasureRepresentation T μ₁ v₁ →
      ∀ (μ₂ : Measure (Eucl P)) (v₂ : Eucl P → NVector (Eucl P) m),
      IsMeasureRepresentation T.boundary μ₂ v₂ →
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
      ∀ W : Set (Eucl P), IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Eucl P) m) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x) ≤ 1) →
      ∀ (χ : ℝ → ℝ) (t h c : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → (∀ s, |χ s| ≤ 1) →
      (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) →
      ENNReal.ofReal |∫ x, χ (f x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ -
        ∫ x, χ (f x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤
      ENNReal.ofReal c * (LW : ℝ≥0∞) *
        μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩ f ⁻¹' Icc (t - h) t) := by
  intro P m U T μ v hμv hμK hv μ₁ v₁ hμ₁ μ₂ v₂ hμ₂ f L hf W hW hWU LW hLW ω hωW hω1 χ t h c hχ
    hχ1 hχc hχ0
  -- `K = spt ω` is compact and `K ⊆ W ⊆ U`.
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) m)) := ω.property.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U := hωW.trans hWU
  -- Smooth `g_j` with `|g_j - f| ≤ 1/(j+1)` and `‖Dg_j‖ ≤ L_W` on `K`.
  choose g hg hgf hgD using fun j : ℕ =>
    Submission.slicing_mb_smooth_approx P W hW f L (hf.mono hWU) LW hLW _ hKc hωW
      (1 / ((j : ℝ) + 1)) (by positivity)
  -- 4.11 for `ψ_j = χ ∘ g_j`, evaluated through the representations of `∂T` and `T`; its right
  -- side is at most `c L_W μ(K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)})`.
  have key : ∀ j : ℕ,
      ENNReal.ofReal |∫ x, χ (g j x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ -
        ∫ x, χ (g j x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤
      ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩
        f ⁻¹' Ioo (t - h - 1 / ((j : ℝ) + 1)) (t + 1 / ((j : ℝ) + 1))) := by
    intro j
    obtain ⟨η₁, η₂, hη₁, hη₂, hle⟩ := Submission.slicing_mb_leibniz_bound P m U T μ v hμv hv ω
      (fun y => χ (g j y)) (hχ.comp (hg j))
    have e₁ : T.boundary η₁ =
        ∫ x, χ (g j x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ := by
      rw [(hμ₂ η₁).2]
      congr 1
      funext x
      rw [hη₁ x, map_smul, smul_eq_mul]
    have e₂ : T η₂ =
        ∫ x, χ (g j x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁ := by
      rw [(hμ₁ η₂).2]
      congr 1
      funext x
      rw [hη₂ x, map_smul, smul_eq_mul]
    rw [← e₁, ← e₂]
    exact hle.trans (Submission.slicing_mb_cdb_grad_lintegral_le P m μ _ f (g j) LW χ t h c
      (1 / ((j : ℝ) + 1)) hω1 ((hg j).differentiable (by simp)) (hχ.differentiable (by simp))
      (hgf j) (hgD j) hχc hχ0)
  -- `g_j → f` pointwise on `K`.
  have hconv : ∀ x ∈ tsupport (ω : DifferentialForm (Eucl P) m),
      Tendsto (fun j => g j x) atTop (𝓝 (f x)) := by
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact hgf j x hx
  -- Left side: dominated convergence in both integrals, whose densities vanish off `K`.
  have hL₂ := Submission.slicing_mb_cdb_multiplier_integral_tendsto P μ₂
    (fun x => v₂ x ((ω : DifferentialForm (Eucl P) m) x)) _ f g χ (hμ₂ ω).1
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun j => (hg j).continuous.measurable) hconv hχ.continuous hχ1
  have hL₁ := Submission.slicing_mb_cdb_multiplier_integral_tendsto P μ₁
    (fun x => v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x)) _ f g χ
    (hμ₁ (exteriorDerivativeTestOn U m ω)).1
    (fun x hx => by
      have hx' : x ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Eucl P) m)) :=
        fun h' => hx (tsupport_exteriorDerivative_subset _ h')
      simp [image_eq_zero_of_notMem_tsupport hx'])
    (fun j => (hg j).continuous.measurable) hconv hχ.continuous hχ1
  -- Right side: continuity from above for the bands, as `μ(K) < ∞`.
  have hR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c * (LW : ℝ≥0∞))
    (Submission.slicing_mb_cdb_band_measure_tendsto P μ _ f (t - h) t (isClosed_tsupport _)
      (hf.continuousOn.mono hKU) (hμK _ hKc hKU))
    (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  exact le_of_tendsto_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp (hL₂.sub hL₁).abs)
    hR key

/-- Simon Ch. 6, 4.9 (p. 158) for the slice `S = ⟨T, f, t₋⟩` of 4.6, `T` represented by `(μ, v)`:
for open `W ⊆ U` with `|Df| ≤ L_W` a.e. on `W`,
`M_W(S) ≤ L_W · liminf_{h ↓ 0} μ(W ∩ {t - h ≤ f ≤ t}) / h`.  For admissible `ω` and the
cut-offs `χ_h` of `slicing_mb_cutoff` (slope at most `(1 + ε)/h`), the defect
`X(h) = ∫ χ_h(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ_h(f) ⟨dω, v₁⟩ dμ₁` of 4.11 tends to `B(ω) - ∂A(ω) = -S(ω)`
as `h ↓ 0` and satisfies `|X(h)| ≤ (1 + ε)/h · L_W · μ(W ∩ {t - h ≤ f ≤ t})`; let `h ↓ 0`,
then `ε ↓ 0`. -/
theorem Submission.slicing_mb_pointwise : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
    (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) →
    (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
    ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
    ∀ (t : ℝ) (S : GeometricCurrentOn U m), IsSlice T f t S →
    ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ LW : ℝ≥0,
    (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
    S.massOn W ≤ (LW : ℝ≥0∞) *
      liminf (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) := by
  intro P m U hU T μ v hT hμ hv f L hf t S hS W hW hWU LW hLW
  -- `S = ∂A - B`, `A = T ⌞ {f < t}` (represented by `μ₁, v₁`), `B = (∂T) ⌞ {f < t}` (`μ₂, v₂`).
  obtain ⟨A, B, ⟨-, μ₁, v₁, hT₁, hA⟩, ⟨-, μ₂, v₂, hT₂, hB⟩, hSAB⟩ := hS
  -- It suffices to bound `S ω` for every `ω` admissible for `M_W`.
  refine sSup_le ?_
  rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  have hSω : S ω = (∫ x in {x | x ∈ U ∧ f x < t},
        v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁) -
      ∫ x in {x | x ∈ U ∧ f x < t}, v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ := by
    have := hSAB ω
    rw [GeometricCurrentOn.boundary_apply, hA, hB] at this
    exact this
  -- The integrands `⟨ω, v₂⟩` and `⟨dω, v₁⟩` are integrable and vanish off `U`.
  have hint₂ : Integrable (fun x => v₂ x ((ω : DifferentialForm (Eucl P) m) x)) μ₂ := (hT₂ ω).1
  have hint₁ : Integrable
      (fun x => v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x)) μ₁ :=
    (hT₁ (exteriorDerivativeTestOn U m ω)).1
  have hvan₂ : ∀ x, x ∉ U → v₂ x ((ω : DifferentialForm (Eucl P) m) x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (ω.property.2 hx'), map_zero]
  have hvan₁ : ∀ x, x ∉ U → v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) = 0 :=
    fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hx' =>
        hx (ω.property.2 (tsupport_exteriorDerivative_subset _ hx')), map_zero]
  calc ENNReal.ofReal (S ω) ≤ ENNReal.ofReal |S ω| := ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal |(∫ x in {x | x ∈ U ∧ f x < t},
          v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂) -
        ∫ x in {x | x ∈ U ∧ f x < t},
          v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| := by
      rw [hSω, abs_sub_comm]
    _ ≤ _ := by
      refine Submission.slicing_mb_pointwise_liminf_bound
        (fun h => μ (W ∩ f ⁻¹' Icc (t - h) t)) LW _ fun ε hε => ?_
      -- The cut-offs `χ_h`, `h > 0`, of slope at most `(1 + ε)/h`.
      choose! χ hχs hχ01 hχ1 hχ0 hχd hχd0 using
        fun h (hh : 0 < h) => Submission.slicing_mb_cutoff t h ε hh hε
      have hχm : ∀ h : ℝ, 0 < h → Measurable (χ h) := fun h hh =>
        (hχs h hh).continuous.measurable
      have hχabs : ∀ h s : ℝ, 0 < h → |χ h s| ≤ 1 := fun h s hh =>
        abs_le.2 ⟨by linarith [(hχ01 h hh s).1], (hχ01 h hh s).2⟩
      refine ⟨fun h => (∫ x, χ h (f x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂) -
          ∫ x, χ h (f x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁,
        ?_, fun h hh => ?_⟩
      · -- `X(h) → B(ω) - ∂A(ω)` as `h ↓ 0`.
        exact (Submission.slicing_mb_pointwise_cutoff_tendsto P U hU f L hf μ₂ _ hint₂ hvan₂ t χ
          hχm hχabs (fun h s hh => hχ1 h hh s) (fun h s hh => hχ0 h hh s)).sub
          (Submission.slicing_mb_pointwise_cutoff_tendsto P U hU f L hf μ₁ _ hint₁ hvan₁ t χ
            hχm hχabs (fun h s hh => hχ1 h hh s) (fun h s hh => hχ0 h hh s))
      · -- `|X(h)| ≤ (1 + ε)/h · L_W · μ(spt ω ∩ {t - h ≤ f ≤ t})`, and `spt ω ⊆ W`.
        refine (Submission.slicing_mb_cutoff_defect_bound P m U T μ v hT hμ hv μ₁ v₁ hT₁ μ₂ v₂
          hT₂ f L hf W hW hWU LW hLW ω hωW hω1 (χ h) t h ((1 + ε) / h) (hχs h hh)
          (fun s => hχabs h s hh) (hχd h hh) (hχd0 h hh)).trans ?_
        gcongr
/-- The distribution function `G(r) = ν((a,b) ∩ (-∞, r])` of a measure `ν` on `ℝ` with
`ν((a,b)) < ∞` is nondecreasing and right-continuous. -/
theorem Submission.slicing_mb_dm_distribution_mono_rightcont :
    ∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ →
      Monotone (fun r : ℝ => (ν (Ioo a b ∩ Iic r)).toReal) ∧
      ∀ s : ℝ, ContinuousWithinAt (fun r : ℝ => (ν (Ioo a b ∩ Iic r)).toReal) (Ici s) s := by
  intro ν a b hab
  -- Each `A_r = (a,b) ∩ (-∞, r]` lies in `(a,b)`, so `ν(A_r) < ∞`.
  have hfin : ∀ r : ℝ, ν (Ioo a b ∩ Iic r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top hab (measure_mono inter_subset_left)
  -- `r ↦ A_r` is monotone, hence so is `G`.
  have hsub : ∀ r r' : ℝ, r ≤ r' → Ioo a b ∩ Iic r ⊆ Ioo a b ∩ Iic r' := fun r r' h =>
    inter_subset_inter_right _ (Iic_subset_Iic.2 h)
  refine ⟨fun r r' h => ENNReal.toReal_mono (hfin r') (measure_mono (hsub r r' h)), fun s => ?_⟩
  -- Continuity within `[s, ∞)` is continuity within `(s, ∞)`.
  rw [← continuousWithinAt_Ioi_iff_Ici]
  -- `⋂_{r > s} A_r = A_s`.
  have hinter : (⋂ r > s, Ioo a b ∩ Iic r) = Ioo a b ∩ Iic s := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_Iic]
    constructor
    · intro h
      exact ⟨(h (s + 1) (by linarith)).1, le_of_forall_gt_imp_ge_of_dense fun r hr => (h r hr).2⟩
    · intro h r hr
      exact ⟨h.1, h.2.trans hr.le⟩
  -- Continuity of `ν` from above along `r ↓ s`, using `ν(A_{s+1}) < ∞`.
  have hlim : Tendsto (fun r => ν (Ioo a b ∩ Iic r)) (𝓝[>] s) (𝓝 (ν (Ioo a b ∩ Iic s))) := by
    rw [← hinter]
    exact tendsto_measure_biInter_gt (s := fun r => Ioo a b ∩ Iic r)
      (fun r _ => (measurableSet_Ioo.inter measurableSet_Iic).nullMeasurableSet)
      (fun i j _ hij => hsub i j hij) ⟨s + 1, by linarith, hfin (s + 1)⟩
  -- `toReal` is continuous at the finite value `ν(A_s)`.
  exact (ENNReal.tendsto_toReal (hfin s)).comp hlim
/-- The lower left Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` of a
nondecreasing right-continuous `G : ℝ → ℝ` is Borel measurable. -/
theorem Submission.slicing_mb_dm_lowerLeftDini_measurable :
    ∀ G : ℝ → ℝ, Monotone G → (∀ s : ℝ, ContinuousWithinAt G (Ici s) s) →
      Measurable (fun t : ℝ => liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k))
        (𝓝[>] 0)) := by
  intro G hG hG_cont
  -- The intervals `(0, 1/(j+1))`, `j ∈ ℕ`, form a basis of `𝓝[>] 0`.
  have hbasis : (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True)
      (fun j => Ioo 0 (1 / ((j : ℝ) + 1))) := by
    refine (nhdsGT_basis (0 : ℝ)).to_hasBasis (fun δ hδ => ?_) (fun j _ => ?_)
    · obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, trivial, Ioo_subset_Ioo_right hj.le⟩
    · exact ⟨1 / ((j : ℝ) + 1), Nat.one_div_pos_of_nat, subset_rfl⟩
  -- Right-continuity of `G` makes `k ↦ F_t(k)` left-continuous at each `k > 0`.
  have hleft : ∀ t k : ℝ, 0 < k → ContinuousWithinAt
      (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (Iio k) k := by
    intro t k hk
    have hGk : ContinuousWithinAt (fun x : ℝ => G (t - x)) (Iio k) k := by
      have h1 : ContinuousWithinAt G (Ioi (t - k)) (t - k) :=
        continuousWithinAt_Ioi_iff_Ici.2 (hG_cont (t - k))
      refine h1.comp (continuous_const.sub continuous_id).continuousWithinAt ?_
      intro x hx
      simp only [mem_Ioi, mem_Iio] at hx ⊢
      linarith
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_const.sub hGk).div continuousWithinAt_id hk.ne')
  -- The infimum over real `k ∈ (0, δ)` equals the infimum over rational `q ∈ (0, δ)`.
  have hrat : ∀ t δ : ℝ, (⨅ k ∈ Ioo 0 δ, ENNReal.ofReal ((G t - G (t - k)) / k)) =
      ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), ENNReal.ofReal ((G t - G (t - q)) / q) := by
    intro t δ
    refine le_antisymm (le_iInf₂ fun q hq => iInf₂_le (q : ℝ) hq) (le_iInf₂ fun k hk => ?_)
    -- Approximate `k` from the left by rationals `q n ∈ (max 0 (k - 1/(n+1)), k)`.
    have hex : ∀ n : ℕ, ∃ q : ℚ, max 0 (k - 1 / ((n : ℝ) + 1)) < q ∧ (q : ℝ) < k := fun n =>
      exists_rat_btwn (max_lt hk.1 (sub_lt_self k Nat.one_div_pos_of_nat))
    choose q hq_lo hq_hi using hex
    have hq_tendsto : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[<] k) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall hq_hi)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => k - 1 / ((n : ℝ) + 1))
        (h := fun _ => k) ?_ tendsto_const_nhds
        (fun n => (le_max_right _ _).trans (hq_lo n).le) (fun n => (hq_hi n).le)
      simpa using (tendsto_const_nhds (f := (atTop : Filter ℕ)) (x := k)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine ge_of_tendsto' ((hleft t k hk.1).tendsto.comp hq_tendsto) fun n => ?_
    exact iInf₂_le (q n) ⟨(le_max_left _ _).trans_lt (hq_lo n), (hq_hi n).trans hk.2⟩
  -- Hence `D(t) = ⨆ j, ⨅ q ∈ ℚ ∩ (0, 1/(j+1)), F_t(q)`, a countable formula.
  have hformula : (fun t : ℝ => liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k))
      (𝓝[>] 0)) = fun t => ⨆ j : ℕ, ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 (1 / ((j : ℝ) + 1))),
        ENNReal.ofReal ((G t - G (t - q)) / q) := by
    funext t
    rw [hbasis.liminf_eq_iSup_iInf]
    simp only [iSup_true]
    exact iSup_congr fun j => hrat t _
  -- `G` is monotone, hence measurable, so each `t ↦ F_t(q)` is measurable.
  rw [hformula]
  have hGm : Measurable G := hG.measurable
  refine Measurable.iSup fun j => Measurable.iInf fun q => Measurable.iInf_Prop _ ?_
  exact ENNReal.measurable_ofReal.comp
    ((hGm.sub (hGm.comp (measurable_id.sub_const _))).div_const _)
/-- For nondecreasing `G : ℝ → ℝ` and `a ≤ b`, the lower integral over `(a, b)` of the lower left
Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` is at most `G b - G a`. -/
theorem Submission.slicing_mb_dm_lintegral_lowerLeftDini_le :
    ∀ G : ℝ → ℝ, Monotone G → ∀ a b : ℝ, a ≤ b →
      ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤
        ENNReal.ofReal (G b - G a) := by
  intro G hG a b hab
  -- Step sizes `δ n = 1/(n+1) → 0+`.
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => Nat.one_div_pos_of_nat
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_tendsto : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ_lim
      (Eventually.of_forall hδ_pos)
  -- Truncated left difference quotients `F n t = 1_{t > a + δ n} ofReal (G t - G (t - δ n)) / δ n`.
  set F : ℕ → ℝ → ℝ≥0∞ := fun n => (Ioi (a + δ n)).indicator
    (fun t => ENNReal.ofReal ((G t - G (t - δ n)) / δ n)) with hF_def
  have hGm : Measurable G := hG.measurable
  have hF_meas : ∀ n, Measurable (F n) := fun n =>
    (ENNReal.measurable_ofReal.comp
      ((hGm.sub (hGm.comp (measurable_id.sub_const _))).div_const _)).indicator measurableSet_Ioi
  -- For `t ∈ (a, b)`: `δ n → 0+`, and `t > a + δ n` eventually, so `D(t) ≤ liminf_n F n t`.
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤
        liminf (fun n => F n t) atTop := by
    intro t ht
    refine hδ_tendsto.liminf_le_liminf_comp.trans_eq (liminf_congr ?_)
    filter_upwards [(tendsto_order.1 hδ_lim).2 _ (sub_pos.2 ht.1)] with n hn
    have hmem : t ∈ Ioi (a + δ n) := by
      simp only [mem_Ioi]
      linarith
    simp only [hF_def, Function.comp_apply, indicator_of_mem hmem]
  -- Each `F n` integrates over `(a, b)` to at most `G b - G a`.
  have hbound : ∀ n, ∫⁻ t in Ioo a b, F n t ≤ ENNReal.ofReal (G b - G a) := by
    intro n
    have hc : 0 < δ n := hδ_pos n
    simp only [hF_def]
    rw [setLIntegral_indicator measurableSet_Ioi, inter_comm, Ioo_inter_Ioi,
      max_eq_right (by linarith : a ≤ a + δ n)]
    rcases le_or_gt b (a + δ n) with hb | hb
    · rw [Ioo_eq_empty (not_lt.2 hb), setLIntegral_empty]
      exact zero_le
    -- On `(a + δ n, b)` the quotient is nonnegative and integrable, and
    -- `∫_{a+δ}^b (G t - G (t - δ)) dt = ∫_{b-δ}^b G - ∫_a^{a+δ} G ≤ δ (G b - G a)`.
    have hGc : Monotone (fun t => G (t - δ n)) := fun x y hxy => hG (by linarith)
    have hint : IntervalIntegrable (fun t => (G t - G (t - δ n)) / δ n) volume (a + δ n) b :=
      (hG.intervalIntegrable.sub hGc.intervalIntegrable).div_const _
    have hintOn : IntegrableOn (fun t => (G t - G (t - δ n)) / δ n) (Ioo (a + δ n) b) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 hint).mono_set Ioo_subset_Ioc_self
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (a + δ n) b)]
        (fun t => (G t - G (t - δ n)) / δ n) :=
      Eventually.of_forall fun t => div_nonneg (sub_nonneg.2 (hG (by linarith))) hc.le
    have hreal : ∫ t in Ioo (a + δ n) b, (G t - G (t - δ n)) / δ n ≤ G b - G a := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.le,
        intervalIntegral.integral_div,
        intervalIntegral.integral_sub hG.intervalIntegrable hGc.intervalIntegrable,
        intervalIntegral.integral_comp_sub_right G (δ n), add_sub_cancel_right, div_le_iff₀ hc]
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (μ := volume) (a := a + δ n) (b := b - δ n))
        (hG.intervalIntegrable (μ := volume) (a := b - δ n) (b := b))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (μ := volume) (a := a) (b := a + δ n))
        (hG.intervalIntegrable (μ := volume) (a := a + δ n) (b := b - δ n))
      have h3 : ∫ x in (b - δ n)..b, G x ≤ δ n * G b := by
        have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : b - δ n ≤ b)
          hG.intervalIntegrable intervalIntegrable_const (fun x hx => hG hx.2)
        simpa [intervalIntegral.integral_const] using this
      have h4 : δ n * G a ≤ ∫ x in a..(a + δ n), G x := by
        have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + δ n)
          intervalIntegrable_const hG.intervalIntegrable (fun x hx => hG hx.1)
        simpa [intervalIntegral.integral_const] using this
      linarith
    calc ∫⁻ t in Ioo (a + δ n) b, ENNReal.ofReal ((G t - G (t - δ n)) / δ n)
        = ENNReal.ofReal (∫ t in Ioo (a + δ n) b, (G t - G (t - δ n)) / δ n) :=
          (ofReal_integral_eq_lintegral_ofReal hintOn hnonneg).symm
      _ ≤ ENNReal.ofReal (G b - G a) := ENNReal.ofReal_le_ofReal hreal
  -- Fatou's lemma.
  calc ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun n => F n t) atTop := setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ liminf (fun n => ∫⁻ t in Ioo a b, F n t) atTop := lintegral_liminf_le hF_meas
    _ ≤ ENNReal.ofReal (G b - G a) := liminf_le_of_frequently_le' (Frequently.of_forall hbound)
/-- **Lower left density versus the lower left Dini derivative** (Simon Ch. 6, p. 158, the step
"4.9 gives 4.10").  Let `ν((a, b)) < ∞`, `G r = ν((a, b) ∩ (-∞, r])` (as a real number) and
`t ∈ (a, b)`.  Then `liminf_{h → 0+} ν([t - h, t]) / h ≤ liminf_{k → 0+} (G t - G (t - k)) / k`.
For `c > 1` and `0 < k < t - a`, `[t - k / c, t] ⊆ (a, b) ∩ (t - k, t]`, a band of mass
`G t - G (t - k)`, so the density at `h = k / c` is at most `c · (G t - G (t - k)) / k`.
Reparametrizing `h = k / c` gives `liminf ≤ c · liminf`, and `c ↓ 1` finishes. -/
theorem Submission.slicing_mb_dm_density_le_lowerLeftDini : ∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ → ∀ t ∈ Ioo a b, liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ liminf (fun k : ℝ => ENNReal.ofReal (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) := by
  intro ν a b hν t ht
  obtain ⟨hat, htb⟩ := ht
  -- Step 1: `A_r = (a, b) ∩ (-∞, r]` has finite measure, so `G r = ν(A_r).toReal` is monotone.
  have hfin : ∀ r : ℝ, ν (Ioo a b ∩ Iic r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top hν (measure_mono inter_subset_left)
  have hmono : ∀ r r' : ℝ, r ≤ r' →
      (ν (Ioo a b ∩ Iic r)).toReal ≤ (ν (Ioo a b ∩ Iic r')).toReal := fun r r' hr =>
    ENNReal.toReal_mono (hfin r') (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hr)))
  -- Step 2: for `s' ≤ s`, `A_s = A_{s'} ⊔ ((a, b) ∩ (s', s])`, so
  -- `ν((a, b) ∩ (s', s]) = G s - G s'`.
  have hincr : ∀ s' s : ℝ, s' ≤ s → ν (Ioo a b ∩ Ioc s' s) =
      ENNReal.ofReal ((ν (Ioo a b ∩ Iic s)).toReal - (ν (Ioo a b ∩ Iic s')).toReal) := by
    intro s' s hs
    have hunion : Ioo a b ∩ Iic s = (Ioo a b ∩ Iic s') ∪ (Ioo a b ∩ Ioc s' s) := by
      ext x
      simp only [mem_inter_iff, mem_union, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨hx, hxs⟩
        by_cases hxs' : x ≤ s'
        · exact Or.inl ⟨hx, hxs'⟩
        · exact Or.inr ⟨hx, lt_of_not_ge hxs', hxs⟩
      · rintro (⟨hx, hxs'⟩ | ⟨hx, -, hxs⟩)
        · exact ⟨hx, hxs'.trans hs⟩
        · exact ⟨hx, hxs⟩
    have hdisj : Disjoint (Ioo a b ∩ Iic s') (Ioo a b ∩ Ioc s' s) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx₁⟩ ⟨-, hx₂, -⟩
      exact absurd hx₁ (not_le.2 hx₂)
    have hB : ν (Ioo a b ∩ Ioc s' s) ≠ ∞ :=
      ne_top_of_le_ne_top hν (measure_mono inter_subset_left)
    have hadd : (ν (Ioo a b ∩ Iic s)).toReal =
        (ν (Ioo a b ∩ Iic s')).toReal + (ν (Ioo a b ∩ Ioc s' s)).toReal := by
      rw [hunion, measure_union hdisj (measurableSet_Ioo.inter measurableSet_Ioc),
        ENNReal.toReal_add (hfin s') hB]
    rw [← ENNReal.ofReal_toReal hB, hadd, add_sub_cancel_left]
  -- Step 3: for `c > 1` and `0 < k < t - a`, `h = k / c` gives `[t - h, t] ⊆ (a, b) ∩ (t - k, t]`,
  -- hence `ν([t - h, t]) / h ≤ c · (G t - G (t - k)) / k`.
  have hband : ∀ c : ℝ, 1 < c → ∀ᶠ k in 𝓝[>] (0 : ℝ),
      ν (Icc (t - k / c) t) / ENNReal.ofReal (k / c) ≤ ENNReal.ofReal c * ENNReal.ofReal
        (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k) := by
    intro c hc
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hat)] with k hk
    obtain ⟨hk0, hkt⟩ := hk
    have hc0 : 0 < c := zero_lt_one.trans hc
    have hhk : k / c < k := div_lt_self hk0 hc
    have hsub : Icc (t - k / c) t ⊆ Ioo a b ∩ Ioc (t - k) t := by
      rintro x ⟨hx₁, hx₂⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, hx₂⟩
    have hΔ0 : 0 ≤ ((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k :=
      div_nonneg (sub_nonneg.2 (hmono _ _ (by linarith))) hk0.le
    apply ENNReal.div_le_of_le_mul
    calc ν (Icc (t - k / c) t) ≤ ν (Ioo a b ∩ Ioc (t - k) t) := measure_mono hsub
      _ = ENNReal.ofReal (c * (((ν (Ioo a b ∩ Iic t)).toReal -
            (ν (Ioo a b ∩ Iic (t - k))).toReal) / k) * (k / c)) := by
        rw [hincr _ _ (by linarith)]
        congr 1
        field_simp
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc0.le hΔ0), ENNReal.ofReal_mul hc0.le]
  -- Steps 4–5: reparametrize `h = k / c` and factor out the constant `ofReal c`.
  have hc_bound : ∀ c : ℝ, 1 < c →
      liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤
        ENNReal.ofReal c * liminf (fun k : ℝ => ENNReal.ofReal
          (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) := by
    intro c hc
    have hc0 : 0 < c := zero_lt_one.trans hc
    have htend : Tendsto (fun k : ℝ => k / c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun k : ℝ => k / c) (𝓝 0) (𝓝 (0 / c)) := tendsto_id.div_const c
        rw [zero_div] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with k hk
        exact div_pos hk hc0
    calc liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0)
        ≤ liminf (fun k : ℝ => ν (Icc (t - k / c) t) / ENNReal.ofReal (k / c)) (𝓝[>] 0) :=
          htend.liminf_le_liminf_comp
      _ ≤ liminf (fun k : ℝ => ENNReal.ofReal c * ENNReal.ofReal
            (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) :=
          liminf_le_liminf (hband c hc)
      _ = _ := ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
  -- Step 6: let `c_n = 1 + 1 / (n + 1) ↓ 1`.
  set D := liminf (fun k : ℝ => ENNReal.ofReal
    (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0)
  rcases eq_or_ne D ∞ with hD | hD
  · rw [hD]
    exact le_top
  · have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * D) atTop (𝓝 D) := by
      simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hD)
    refine ge_of_tendsto h2 (Eventually.of_forall fun n => hc_bound _ ?_)
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The measurable majorant in Simon Ch. 6, 4.10 (`M_W(T ⌞ {f < t})` is increasing in `t`, so
it is differentiable a.e. and its derivative integrates to at most `M_W(T ⌞ {a < f < b})`), for
a Borel measure `ν` on `ℝ`: the lower left density `liminf_{h → 0+} ν([t - h, t]) / h` has a
Borel majorant on `(a, b)` whose integral over `(a, b)` is at most `ν((a, b))`.
If `ν((a, b)) = ∞` the constant `∞` works.  Otherwise the distribution function
`G(r) = ν((a, b) ∩ (-∞, r])` is nondecreasing and right-continuous, and the majorant is `D` on
`(a, b)` and `0` elsewhere, where `D(t) = liminf_{k → 0+} (G(t) - G(t - k)) / k` is the lower
left Dini derivative of `G`: `D` is Borel, it dominates the closed-band density, and by
Lebesgue's theorem for monotone functions `∫_{(a,b)} D ≤ G(b) - G(a) = ν((a, b))`. -/
theorem Submission.slicing_mb_density_majorant :
    ∀ (ν : Measure ℝ) (a b : ℝ), a < b → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧
      (∀ t ∈ Ioo a b,
        liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ g t) ∧
      ∫⁻ t in Ioo a b, g t ≤ ν (Ioo a b) := by
  intro ν a b hab
  -- If `ν((a, b)) = ∞`, take `g ≡ ∞`.
  by_cases hQ : ν (Ioo a b) = ∞
  · exact ⟨fun _ => ∞, measurable_const, fun _ _ => le_top, by rw [hQ]; exact le_top⟩
  obtain ⟨hG_mono, hG_right⟩ := Submission.slicing_mb_dm_distribution_mono_rightcont ν a b hQ
  set G : ℝ → ℝ := fun r => (ν (Ioo a b ∩ Iic r)).toReal
  set D : ℝ → ℝ≥0∞ := fun t =>
    liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0)
  refine ⟨(Ioo a b).indicator D,
    (Submission.slicing_mb_dm_lowerLeftDini_measurable G hG_mono hG_right).indicator
      measurableSet_Ioo, fun t ht => ?_, ?_⟩
  · -- On `(a, b)` the closed-band density is at most `D = g`.
    rw [Set.indicator_of_mem ht]
    exact Submission.slicing_mb_dm_density_le_lowerLeftDini ν a b hQ t ht
  · -- `∫⁻_{(a,b)} g = ∫⁻_{(a,b)} D ≤ G(b) - G(a)`, with `G(a) = 0` and `G(b) = ν((a, b))`.
    have hGa : G a = 0 := by
      have h : Ioo a b ∩ Iic a = ∅ :=
        eq_empty_of_forall_notMem fun x (hx : x ∈ Ioo a b ∩ Iic a) => not_le.2 hx.1.1 hx.2
      simp only [G, h, measure_empty, ENNReal.toReal_zero]
    have hGb : G b = (ν (Ioo a b)).toReal := by
      have h : Ioo a b ∩ Iic b = Ioo a b := inter_eq_left.2 fun x (hx : x ∈ Ioo a b) => hx.2.le
      simp only [G, h]
    rw [setLIntegral_congr_fun measurableSet_Ioo fun t ht => Set.indicator_of_mem ht D]
    calc ∫⁻ t in Ioo a b, D t ≤ ENNReal.ofReal (G b - G a) :=
          Submission.slicing_mb_dm_lintegral_lowerLeftDini_le G hG_mono a b hab.le
      _ = ν (Ioo a b) := by rw [hGa, hGb, sub_zero, ENNReal.ofReal_toReal hQ]
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
/-- Coordinates of a Borel `k`-vector field in an isometric chart `J` of the `k`-covectors:
`u(x) = (v(x)(J⁻¹eᵢ))ᵢ` is Borel, `‖u‖ ≤ 1`, `‖u‖ = 1` `μ`-a.e. and `v(x)(α) = ⟨Jα, u(x)⟩`. -/
theorem Submission.smr_ufd_unit_coord_field :
    ∀ (P k N : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k)
      (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖) →
      (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) →
      (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) →
      (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) →
      ∃ u : Eucl P → EuclideanSpace ℝ (Fin N), Measurable u ∧ (∀ x, ‖u x‖ ≤ 1) ∧
        (∀ᵐ x ∂μ, ‖u x‖ = 1) ∧
        ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x) := by
  intro P k N μ v J hJ hv hmeas hae
  -- Coordinates in the chart `J`: `u(x)ᵢ = v(x)(J⁻¹eᵢ)`.
  let u : Eucl P → EuclideanSpace ℝ (Fin N) := fun x =>
    WithLp.toLp 2 (fun i => v x (J.symm (EuclideanSpace.single i 1)))
  -- Pairing formula `v(x)(α) = ⟨Jα, u(x)⟩`, by expanding `Jα` in the standard basis.
  have hpair : ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x) := by
    intro x α
    have hexp : J α = ∑ i, (J α) i • EuclideanSpace.single i (1 : ℝ) := by
      simpa [EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (J α)).symm
    conv_lhs => rw [← J.symm_apply_apply α, hexp]
    simp [map_sum, map_smul, PiLp.inner_apply, u, mul_comm]
  -- `‖u(x)‖ ≤ 1`: test with `α = J⁻¹u(x)`, so `‖u(x)‖² = v(x)(α) ≤ |α| = ‖u(x)‖`.
  have hle : ∀ x, ‖u x‖ ≤ 1 := by
    intro x
    have h1 : ‖u x‖ ^ 2 ≤ ‖u x‖ := by
      have := hv x (J.symm (u x))
      rw [hpair, hJ, LinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq] at this
      exact (le_abs_self _).trans this
    by_contra h
    nlinarith [norm_nonneg (u x), not_le.mp h]
  refine ⟨u, ?_, hle, ?_, hpair⟩
  · exact (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp (measurable_pi_iff.mpr fun i => hmeas _)
  -- `‖u(x)‖ = 1` a.e.: by Cauchy–Schwarz, `1 = v(x)(α) = ⟨Jα, u(x)⟩ ≤ |α| ‖u(x)‖ ≤ ‖u(x)‖`.
  · filter_upwards [hae] with x ⟨α, hα, hvα⟩
    refine le_antisymm (hle x) ?_
    have h2 : (1 : ℝ) ≤ ‖J α‖ * ‖u x‖ := by
      rw [← hvα, hpair]
      exact real_inner_le_norm _ _
    rw [← hJ] at h2
    nlinarith [norm_nonneg (u x), covectorEuclideanNorm_nonneg α]
/-- Compact inner approximation inside an open `W ⊆ U`: if `μ` is finite on compact subsets of
`U`, `E` is Borel and `c < μ (W ∩ E)`, then some compact `K ⊆ W ∩ E` has `c < μ K`. -/
theorem Submission.smr_ufd_cl_inner_compact : ∀ (P : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → ∀ E : Set (Eucl P), MeasurableSet E → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < μ (W ∩ E) → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ W ∩ E ∧ c < μ K := by
  intro P U μ hfin E hE W hW hWU c hc
  -- Step 1: compact sets `K j = F j ∩ closedBall 0 j ⊆ W`, increasing, with `⋃ j, K j = W`,
  -- where `F j` are closed, increasing and exhaust `W`.
  obtain ⟨F, hFc, hFW, hFU, hFm⟩ := hW.exists_iUnion_isClosed
  set K : ℕ → Set (Eucl P) := fun j => F j ∩ closedBall 0 j
  have hKc : ∀ j, IsCompact (K j) := fun j => (isCompact_closedBall 0 (j : ℝ)).inter_left (hFc j)
  have hKW : ∀ j, K j ⊆ W := fun j => inter_subset_left.trans (hFW j)
  have hKm : Monotone K := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j, K j = W := by
    refine Subset.antisymm (iUnion_subset hKW) fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i n, hFm (le_max_left i n) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hn.trans (Nat.cast_le.2 (le_max_right i n))
  -- Step 2: continuity from below gives `j` with `c < μ (E ∩ K j)`.
  have hlim : Tendsto (fun j => μ (E ∩ K j)) atTop (𝓝 (μ (W ∩ E))) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun j => E ∩ K j)
      (fun i j hij => inter_subset_inter_right E (hKm hij))
    rwa [← inter_iUnion, hKU, inter_comm E W] at h
  obtain ⟨j, hj⟩ := ((tendsto_order.1 hlim).1 c hc).exists
  -- Step 3: `E' = E ∩ K j` is Borel, `E' ⊆ W ∩ E` and `μ E' ≤ μ (K j) < ∞`.
  set E' := E ∩ K j
  have hE'm : MeasurableSet E' := hE.inter (hKc j).isClosed.measurableSet
  have hE'W : E' ⊆ W ∩ E := fun x hx => ⟨hKW j hx.2, hx.1⟩
  have hE'fin : μ E' < ∞ :=
    (measure_mono inter_subset_right).trans_lt (hfin _ (hKc j) ((hKW j).trans hWU))
  -- Step 4: the finite measure `μ ⌞ E'` on `ℝ^P` is inner regular by compact sets.
  have : IsFiniteMeasure (μ.restrict E') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hE'fin⟩
  have hcE' : c < μ.restrict E' E' := by rwa [Measure.restrict_apply_self]
  obtain ⟨L, hLE', hLc, hL⟩ :=
    hE'm.exists_lt_isCompact_of_ne_top (μ := μ.restrict E') (measure_ne_top _ E') hcE'
  -- Step 5: `L` is compact, `L ⊆ E' ⊆ W ∩ E` and `c < μ L`.
  refine ⟨L, hLc, hLE'.trans hE'W, ?_⟩
  rwa [Measure.restrict_eq_self μ hLE'] at hL
/-- Lusin's theorem with compact sets (Simon Ch. 1, 1.17, applied coordinatewise): if `μ` is a
measure on `ℝ^P`, `u : ℝ^P → ℝ^N` is Borel and `A ⊆ ℝ^P` is Borel with `μ(A) < ∞`, then for every
`ε > 0` there is a compact `C ⊆ A` with `μ(A ∖ C) < ε` and `u|C` continuous. -/
theorem Submission.smr_ufd_cl_vector_lusin : ∀ (P N : ℕ) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable u → ∀ A : Set (Eucl P), MeasurableSet A → μ A ≠ ∞ → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ A ∧ μ (A \ C) < ε ∧ ContinuousOn u C := by
  intro P N μ u hu A hA hAfin ε hε
  -- Step 1: every Borel `S` with `μ(S) < ∞` has, for every `δ > 0`, a compact (hence closed)
  -- `F ⊆ S` with `μ(S ∖ F) < δ`: the finite measure `ν = μ ⌞ S` is regular on `ℝ^P`, and
  -- `ν = μ` on subsets of `S`.
  have hreg : ∀ S : Set (Eucl P), MeasurableSet S → μ S ≠ ∞ → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ S, IsCompact F ∧ IsClosed F ∧ μ (S \ F) < δ := by
    intro S hS hSfin δ hδ
    have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
    have : (μ.restrict S).Regular :=
      Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    obtain ⟨F, hFS, hFc, hFcl, hFlt⟩ :=
      hS.exists_isCompact_isClosed_sdiff_lt (μ := μ.restrict S) (measure_ne_top _ _) hδ
    refine ⟨F, hFS, hFc, hFcl, ?_⟩
    rwa [Measure.restrict_apply (hS.diff hFcl.measurableSet), inter_eq_left.2 sdiff_subset]
      at hFlt
  -- Step 2: an error budget `0 < η < ∞` with `(N + 1) η < ε`.
  obtain ⟨η, hη0, hηε⟩ :=
    ENNReal.exists_pos_mul_lt (a := ((N + 1 : ℕ) : ℝ≥0∞)) (ENNReal.natCast_ne_top _) hε
  have hηtop : η ≠ ∞ := by
    rintro rfl
    rw [ENNReal.top_mul (by exact_mod_cast Nat.succ_ne_zero N)] at hηε
    exact not_top_lt hηε
  -- Step 3: the coordinates `u_i = (u ·) i` are Borel.
  have hui : ∀ i : Fin N, Measurable fun x => u x i := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hu
  -- Step 4: Lusin's theorem (Simon Ch. 1, 1.17) on `A` for a Borel `f : ℝ^P → ℝ`, with the
  -- closed regularity of Step 1.  SimonGMT's `Chapter01.Lusin` is outside the frozen imports, so
  -- it is proved here through a countable basis `(b k)` of `ℝ`: closed `G k ⊆ A ∩ f⁻¹(b k)` and
  -- `H k ⊆ A ∖ f⁻¹(b k)` with defects `< δ k`, `∑ δ k < η / 2`, and `F = ⋂ k, (G k ∪ H k)`.
  have hlusin : ∀ f : Eucl P → ℝ, Measurable f →
      ∃ F ⊆ A, IsClosed F ∧ μ (A \ F) < η ∧ ContinuousOn f F := by
    intro f hf
    obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis ℝ
    have hbo : ∀ k, IsOpen (b k) := fun k => hb.isOpen (mem_range_self k)
    obtain ⟨δ, hδ0, hδη⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hη0.ne').ne' ℕ
    have hδ : ∀ k, ((δ k : ℝ≥0) : ℝ≥0∞) ≠ 0 := fun k => ENNReal.coe_ne_zero.2 (hδ0 k).ne'
    choose G hGA hGc hGcl hGlt using fun k =>
      hreg _ (hA.inter (hf (hbo k).measurableSet))
        (ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)) (δ k) (hδ k)
    choose H hHA hHc hHcl hHlt using fun k =>
      hreg _ (hA.diff (hf (hbo k).measurableSet))
        (ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)) (δ k) (hδ k)
    refine ⟨⋂ k, (G k ∪ H k), ?_, isClosed_iInter fun k => (hGcl k).union (hHcl k), ?_, ?_⟩
    · exact (iInter_subset _ 0).trans
        (union_subset ((hGA 0).trans inter_subset_left) ((hHA 0).trans sdiff_subset))
    -- `A ∖ F ⊆ ⋃ k, ((A ∩ f⁻¹(b k)) ∖ G k ∪ (A ∖ f⁻¹(b k)) ∖ H k)`.
    · calc μ (A \ ⋂ k, (G k ∪ H k))
          ≤ μ (⋃ k, ((A ∩ f ⁻¹' b k) \ G k ∪ (A \ f ⁻¹' b k) \ H k)) := by
            refine measure_mono fun x hx => ?_
            obtain ⟨k, hk⟩ : ∃ k, x ∉ G k ∪ H k := by
              by_contra! h
              exact hx.2 (mem_iInter.2 h)
            refine mem_iUnion.2 ⟨k, ?_⟩
            by_cases hxb : f x ∈ b k
            · exact Or.inl ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inr h)⟩
        _ ≤ ∑' k, μ ((A ∩ f ⁻¹' b k) \ G k ∪ (A \ f ⁻¹' b k) \ H k) := measure_iUnion_le _
        _ ≤ ∑' k, ((δ k : ℝ≥0∞) + δ k) := ENNReal.tsum_le_tsum fun k =>
            (measure_union_le _ _).trans (add_le_add (hGlt k).le (hHlt k).le)
        _ = ∑' k, (δ k : ℝ≥0∞) + ∑' k, (δ k : ℝ≥0∞) := ENNReal.tsum_add
        _ < η / 2 + η / 2 := ENNReal.add_lt_add hδη hδη
        _ = η := ENNReal.add_halves η
    -- `f⁻¹(b k) ∩ F = (H k)ᶜ ∩ F` is relatively open in `F` for every basic open set `b k`.
    · rw [hb.continuousOn_iff]
      rintro t ⟨k, rfl⟩
      refine ⟨(H k)ᶜ, (hHcl k).isOpen_compl, ?_⟩
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
      constructor
      · rintro ⟨hxb, hxF⟩
        exact ⟨fun hxH => ((hHA k) hxH).2 hxb, hxF⟩
      · rintro ⟨hxH, hxF⟩
        refine ⟨?_, hxF⟩
        rcases mem_iInter.1 hxF k with hxG | hxH'
        · exact ((hGA k) hxG).2
        · exact absurd hxH' hxH
  -- For each coordinate `i`: a closed `F i ⊆ A` with `μ(A ∖ F i) < η` and `u_i` continuous
  -- on `F i`.
  choose F hFA hFcl hFlt hFcont using fun i => hlusin _ (hui i)
  -- Step 5: a compact `K ⊆ A` with `μ(A ∖ K) < η`.
  obtain ⟨K, hKA, hKc, -, hKlt⟩ := hreg A hA hAfin η hη0.ne'
  -- Step 6: `C = K ∩ ⋂ i, F i` is compact and `C ⊆ K ⊆ A`.
  refine ⟨K ∩ ⋂ i, F i, hKc.inter_right (isClosed_iInter hFcl), inter_subset_left.trans hKA,
    ?_, ?_⟩
  -- Step 8: `A ∖ C ⊆ (A ∖ K) ∪ ⋃ i, (A ∖ F i)`, so `μ(A ∖ C) < η + N η = (N + 1) η < ε`.
  · have hsum : ∑ i, μ (A \ F i) ≤ ∑ _i : Fin N, η :=
      Finset.sum_le_sum fun i _ => (hFlt i).le
    have hsum_ne_top : ∑ i, μ (A \ F i) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun _ _ => hηtop) hsum
    calc μ (A \ (K ∩ ⋂ i, F i))
        ≤ μ ((A \ K) ∪ ⋃ i, (A \ F i)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ K
          · obtain ⟨i, hi⟩ : ∃ i, x ∉ F i := by
              by_contra! h
              exact hx.2 ⟨hxK, mem_iInter.2 h⟩
            exact Or.inr (mem_iUnion.2 ⟨i, hx.1, hi⟩)
          · exact Or.inl ⟨hx.1, hxK⟩
      _ ≤ μ (A \ K) + ∑ i, μ (A \ F i) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
      _ < η + ∑ _i : Fin N, η := ENNReal.add_lt_add_of_lt_of_le hsum_ne_top hKlt hsum
      _ = η * ((N + 1 : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ < ε := hηε
  -- Step 7: every coordinate of `u` is continuous on `C ⊆ F i`, hence so is `u`.
  · have h : ContinuousOn (fun x => WithLp.ofLp (u x)) (K ∩ ⋂ i, F i) :=
      continuousOn_pi.2 fun i => (hFcont i).mono (inter_subset_right.trans (iInter_subset _ i))
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn h

/-- Lusin's theorem with compact sets of large measure (Simon Ch. 1, 1.17, with inner regularity;
used for Ch. 6, 2.7–2.9): let `μ` be finite on compact subsets of `U`, `u : ℝ^P → ℝ^N` Borel,
`E` Borel and `W ⊆ U` open.  If `c < μ(W ∩ E)`, then some compact `C ⊆ W ∩ E` has `c < μ(C)`
and `u|C` continuous. -/
theorem Submission.smr_ufd_compact_lusin_set :
    ∀ (P N : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)),
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → Measurable u →
      ∀ E : Set (Eucl P), MeasurableSet E → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U →
      ∀ c : ℝ≥0∞, c < μ (W ∩ E) →
        ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ W ∩ E ∧ c < μ C ∧ ContinuousOn u C := by
  intro P N U μ u hfin hu E hE W hW hWU c hc
  -- Inner regularity: a compact `C₀ ⊆ W ∩ E` with `c < μ(C₀)`.
  obtain ⟨C₀, hC₀, hC₀WE, hcC₀⟩ :=
    Submission.smr_ufd_cl_inner_compact P U μ hfin E hE W hW hWU c hc
  -- `C₀` is a compact subset of `W ⊆ U`, so `μ(C₀) < ∞`.
  have hC₀fin : μ C₀ ≠ ∞ := (hfin C₀ hC₀ (hC₀WE.trans (inter_subset_left.trans hWU))).ne
  -- Lusin on `C₀` with error `δ = μ(C₀) - c > 0`: a compact `C ⊆ C₀` with `μ(C₀ ∖ C) < δ` on
  -- which `u` is continuous.
  obtain ⟨C, hC, hCC₀, hC₀C, hu_cont⟩ :=
    Submission.smr_ufd_cl_vector_lusin P N μ u hu C₀ hC₀.measurableSet hC₀fin (μ C₀ - c)
      (tsub_pos_iff_lt.2 hcC₀).ne'
  -- `μ(C₀) - μ(C) ≤ μ(C₀ ∖ C) < μ(C₀) - c`, hence `c < μ(C)`.
  exact ⟨C, hC, hCC₀.trans hC₀WE, lt_of_tsub_lt_tsub_left (le_measure_sdiff.trans_lt hC₀C),
    hu_cont⟩
/-- Tietze extension into the closed unit ball of `ℝ^N`: if `u` is continuous on a closed set
`C ⊆ ℝ^P` with `‖u‖ ≤ 1` on `C`, there is a continuous `w : ℝ^P → ℝ^N` with `‖w‖ ≤ 1` and
`w = u` on `C`.  Off `C`, `w` is a continuous selection (partition of unity) of the convex hulls
of the values of `u` on `C ∩ B(y, 3 d(y, C))`, as in Dugundji's extension theorem. -/
theorem Submission.smr_ufd_ball_tietze :
    ∀ (P N : ℕ) (C : Set (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), IsClosed C →
      ContinuousOn u C → (∀ x ∈ C, ‖u x‖ ≤ 1) →
      ∃ w : Eucl P → EuclideanSpace ℝ (Fin N), Continuous w ∧ (∀ x, ‖w x‖ ≤ 1) ∧
        ∀ x ∈ C, w x = u x := by
  intro P N C u hC hu hu1
  -- Empty `C`: take `w = 0`.
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, continuous_const, fun x => by simp, fun x hx => hx.elim⟩
  -- For `y ∉ C`, `t y` is the convex hull of `u (C ∩ B(y, 3 d(y, C)))`.
  set t : (Cᶜ : Set (Eucl P)) → Set (EuclideanSpace ℝ (Fin N)) := fun y =>
    convexHull ℝ (u '' (C ∩ ball (y : Eucl P) (3 * infDist (y : Eucl P) C)))
  have htc : ∀ y, Convex ℝ (t y) := fun y => convex_convexHull ℝ _
  have hpos : ∀ y : (Cᶜ : Set (Eucl P)), 0 < infDist (y : Eucl P) C := fun y =>
    (hC.notMem_iff_infDist_pos hne).1 y.2
  -- Locally constant selections: `u c` for a point `c ∈ C` with `|y - c| < 2 d(y, C)`.
  have hloc : ∀ y : (Cᶜ : Set (Eucl P)), ∃ v, ∀ᶠ z in 𝓝 y, v ∈ t z := by
    intro y
    obtain ⟨c, hcC, hc⟩ := (infDist_lt_iff hne).1
      (by linarith [hpos y] : infDist (y : Eucl P) C < 2 * infDist (y : Eucl P) C)
    refine ⟨u c, ?_⟩
    have h1 : ContinuousAt (fun z : (Cᶜ : Set (Eucl P)) => dist (z : Eucl P) c) y :=
      (continuous_subtype_val.dist continuous_const).continuousAt
    have h2 : ContinuousAt (fun z : (Cᶜ : Set (Eucl P)) => 3 * infDist (z : Eucl P) C) y :=
      (continuous_const.mul ((continuous_infDist_pt C).comp continuous_subtype_val)).continuousAt
    filter_upwards [h1.eventually_lt h2 (by linarith [hpos y])] with z hz
    exact subset_convexHull ℝ _ ⟨c, ⟨hcC, by rw [mem_ball, dist_comm]; exact hz⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const htc hloc
  -- Every `t y` lies in the closed unit ball.
  have htB : ∀ y, t y ⊆ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := fun y =>
    convexHull_min (by rintro _ ⟨c, hc, rfl⟩; simpa using hu1 c hc.1) (convex_closedBall 0 1)
  classical
  refine ⟨fun x => if hx : x ∈ C then u x else g ⟨x, hx⟩, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ C
    · -- At `x ∈ C`: nearby values of `u` on `C` are close to `u x`, and so are their hulls.
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδu⟩ := Metric.continuousOn_iff.1 hu x hx (ε / 2) (half_pos hε)
      filter_upwards [ball_mem_nhds x (by positivity : 0 < δ / 4)] with y hy
      have hyx : dist y x < δ / 4 := mem_ball.1 hy
      rw [dite_eq_left hx]
      by_cases hyC : y ∈ C
      · rw [dite_eq_left hyC]
        exact (hδu y hyC (by linarith)).trans (half_lt_self hε)
      · rw [dite_eq_right hyC]
        have hsub : t ⟨y, hyC⟩ ⊆ closedBall (u x) (ε / 2) := by
          refine convexHull_min ?_ (convex_closedBall _ _)
          rintro _ ⟨c, ⟨hcC, hcy⟩, rfl⟩
          have hcy' : dist c y < 3 * infDist y C := mem_ball.1 hcy
          have hinf : infDist y C ≤ dist y x := infDist_le_dist_of_mem hx
          have hcx : dist c x < δ := by
            calc dist c x ≤ dist c y + dist y x := dist_triangle _ _ _
              _ < δ := by linarith
          exact mem_closedBall.2 (hδu c hcC hcx).le
        exact lt_of_le_of_lt (mem_closedBall.1 (hsub (hg ⟨y, hyC⟩))) (half_lt_self hε)
    · -- Off `C` the glued map is `g` on the open set `Cᶜ`.
      have hcont : ContinuousOn (fun x => if hx : x ∈ C then u x else g ⟨x, hx⟩) Cᶜ := by
        rw [continuousOn_iff_continuous_domRestrict]
        convert g.continuous using 1
        funext y
        have hy : (y : Eucl P) ∉ C := y.2
        simp [hy]
      exact hcont.continuousAt (hC.isOpen_compl.mem_nhds hx)
  · intro x
    dsimp only
    by_cases hx : x ∈ C
    · rw [dite_eq_left hx]
      exact hu1 x hx
    · rw [dite_eq_right hx]
      simpa using htB _ (hg ⟨x, hx⟩)
  · intro x hx
    exact dite_eq_left hx
/-- **Small cutoff (step of Simon Ch. 6, 2.7–2.9, pp. 136–137).**  If `μ` is finite on compact
subsets of `U`, `C` is compact and `W ⊆ U` is open with `C ⊆ W`, then for every `ε > 0` there is
a continuous compactly supported `ψ : ℝ^P → [0, 1]` with `tsupport ψ ⊆ W`, `ψ = 1` on `C` and
`μ(support ψ ∖ C) < ε`.  Choose `r > 0` with the compact `cthickening r C ⊆ W`; the open
thickenings `O j = thickening (r / (j + 1)) C` decrease to `C`, so by continuity from above
`μ(O j ∖ C) < ε` for some `j`, and Urysohn's lemma for `C` and `(O j)ᶜ` gives `ψ`. -/
theorem Submission.smr_ufd_small_cutoff : ∀ (P : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → ∀ C W : Set (Eucl P), IsCompact C → IsOpen W → C ⊆ W → W ⊆ U → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ ψ : Eucl P → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x ∈ C, ψ x = 1) ∧ μ (Function.support ψ \ C) < ε := by
  intro P U μ hfin C W hC hW hCW hWU ε hε
  -- Step 1: a compact closed thickening `cthickening r C ⊆ W ⊆ U`, of finite measure.
  obtain ⟨r, hr, hrW⟩ := hC.exists_cthickening_subset_open hW hCW
  have hKfin : μ (cthickening r C) < ∞ := hfin _ hC.cthickening (hrW.trans hWU)
  -- Step 2: the open thickenings `O j = thickening (r / (j + 1)) C` contain `C`, decrease, lie in
  -- `cthickening r C`, and `⋂ j, O j ⊆ C`.
  set δ : ℕ → ℝ := fun j => r / ((j : ℝ) + 1) with hδ_def
  set O : ℕ → Set (Eucl P) := fun j => thickening (δ j) C with hO_def
  have hδ_pos : ∀ j, 0 < δ j := fun j => div_pos hr (by positivity)
  have hδ_le : ∀ j, δ j ≤ r := fun j =>
    div_le_self hr.le (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hCO : ∀ j, C ⊆ O j := fun j => self_subset_thickening (hδ_pos j) C
  have hOK : ∀ j, closure (O j) ⊆ cthickening r C := fun j =>
    (closure_thickening_subset_cthickening _ _).trans (cthickening_mono (hδ_le j) C)
  have hO_anti : Antitone O := fun i j hij =>
    thickening_mono (div_le_div_of_nonneg_left hr.le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hij)) C
  have hO_inter : (⋂ j, O j) ⊆ C := by
    intro x hx
    rw [← hC.isClosed.closure_eq, closure_eq_iInter_thickening, mem_iInter₂]
    intro t ht
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (div_pos ht hr)
    have hjt : δ j ≤ t := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [one_div, inv_lt_iff_one_lt_mul₀ h1, div_mul_eq_mul_div, one_lt_div hr] at hj
      rw [hδ_def, div_le_iff₀ h1]
      exact hj.le
    exact thickening_mono hjt C (mem_iInter.1 hx j)
  -- Step 3: continuity from above on the halos `O j ∖ C` (open minus closed, decreasing, the
  -- first of finite measure, empty intersection) gives `j` with `μ (O j ∖ C) < ε`.
  have hD_meas : ∀ j, NullMeasurableSet (O j \ C) μ := fun j =>
    (isOpen_thickening.measurableSet.diff hC.isClosed.measurableSet).nullMeasurableSet
  have hD_anti : Antitone fun j => O j \ C := fun i j hij => sdiff_subset_sdiff_left (hO_anti hij)
  have hD_fin : ∃ j, μ (O j \ C) ≠ ∞ :=
    ⟨0, ((measure_mono (sdiff_subset.trans (subset_closure.trans (hOK 0)))).trans_lt hKfin).ne⟩
  have hD_empty : (⋂ j, O j \ C) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    rw [mem_iInter] at hx
    exact (hx 0).2 (hO_inter (mem_iInter.2 fun j => (hx j).1))
  have hT := tendsto_measure_iInter_atTop hD_meas hD_anti hD_fin
  rw [hD_empty, measure_empty] at hT
  obtain ⟨j, hj⟩ := (hT.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  -- Step 4: Urysohn's lemma for the compact `C` and the closed `(O j)ᶜ`, disjoint as `C ⊆ O j`.
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hC
    isOpen_thickening.isClosed_compl (disjoint_compl_right_iff_subset.2 (hCO j))
  -- Step 5: `support f ⊆ O j`, so `tsupport f ⊆ closure (O j) ⊆ cthickening r C ⊆ W` and
  -- `μ (support f ∖ C) ≤ μ (O j ∖ C) < ε`.
  have hsupp : Function.support f ⊆ O j := fun x hx => by
    by_contra h
    exact hx (hf0 h)
  refine ⟨f, f.continuous, hfc, (closure_mono hsupp).trans ((hOK j).trans hrW),
    fun x => hf01 x, fun x hx => hf1 hx, ?_⟩
  exact (measure_mono (sdiff_subset_sdiff_left hsupp)).trans_lt hj
/-- Simon Ch. 6, 2.7–2.9 (the final step of the unit-form density argument): if `|g| ≤ 1`, `g = 1`
on `C ⊆ A`, `g = 0` off `S` with `μ(S) < ∞` and `c + μ(S ∖ C) < μ(C)`, then `c < ∫_A g dμ`.  As
`g = 1` on `C` and `g = 0` off `S`, `C ⊆ S`, so all measures involved are finite, and `|g| ≤ 1_S`
makes `g` integrable.  Then `∫_A g = μ(C) + ∫_{A ∖ C} g` and
`|∫_{A ∖ C} g| = |∫_{(A ∖ C) ∩ S} g| ≤ μ(S ∖ C)`, so `∫_A g ≥ μ(C) − μ(S ∖ C) > c`. -/
theorem Submission.smr_ufd_integral_lower_bound :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (g : Eucl P → ℝ) (A C S : Set (Eucl P)) (c : ℝ≥0∞), MeasurableSet A → MeasurableSet C → MeasurableSet S → C ⊆ A → μ S < ∞ → Measurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ C, g x = 1) → (∀ x, x ∉ S → g x = 0) → c + μ (S \ C) < μ C → c < ENNReal.ofReal (∫ x in A, g x ∂μ) := by
  intro P μ g A C S c hA hC hS hCA hSfin hg hg1 hgC hgS hc
  -- Step 1 (finiteness): `C ⊆ S`, so `μ C ≤ μ S < ∞`, and `c`, `μ (S \ C)` are finite.
  have hCS : C ⊆ S := fun x hx => by
    by_contra hxS
    have h := hgC x hx
    rw [hgS x hxS] at h
    exact zero_ne_one h
  have hCfin : μ C ≠ ∞ := ((measure_mono hCS).trans_lt hSfin).ne
  have hsum : c + μ (S \ C) ≠ ∞ := ne_top_of_lt hc
  have hcfin : c ≠ ∞ := (ENNReal.add_ne_top.1 hsum).1
  have hSCfin : μ (S \ C) ≠ ∞ := (ENNReal.add_ne_top.1 hsum).2
  have hreal : c.toReal + μ.real (S \ C) < μ.real C := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add hcfin hSCfin]
    exact (ENNReal.toReal_lt_toReal hsum hCfin).2 hc
  -- Step 2 (integrability): `|g| ≤ 1_S` and `μ S < ∞`.
  have hgint : Integrable g μ := by
    refine ((integrable_indicator_iff hS).2 (integrableOn_const (C := (1 : ℝ)) hSfin.ne)).mono'
      hg.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · simpa [hx, Real.norm_eq_abs] using hg1 x
    · simp [hx, hgS x hx]
  -- Step 3 (splitting): `∫_A g = ∫_C g + ∫_{A \ C} g = μ(C) + ∫_{A \ C} g`.
  have hsplit : ∫ x in A, g x ∂μ = μ.real C + ∫ x in A \ C, g x ∂μ := by
    have hCint : ∫ x in C, g x ∂μ = ∫ _ in C, (1 : ℝ) ∂μ := setIntegral_congr_fun hC hgC
    rw [← integral_inter_add_sdiff (s := A) hC hgint.integrableOn, inter_eq_right.2 hCA, hCint,
      setIntegral_const, smul_eq_mul, mul_one]
  -- Step 4 (remainder): `|∫_{A \ C} g| ≤ μ((A \ C) ∩ S) ≤ μ(S \ C)`.
  have hsub : (A \ C) ∩ S ⊆ S \ C := fun x hx => ⟨hx.2, hx.1.2⟩
  have hrem : |∫ x in A \ C, g x ∂μ| ≤ μ.real (S \ C) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := (A \ C) ∩ S) (hA.diff hC)
      inter_subset_left fun x hx => hgS x fun hxS => hx.2 ⟨hx.1, hxS⟩]
    have h1 : ‖∫ x in (A \ C) ∩ S, g x ∂μ‖ ≤ 1 * μ.real ((A \ C) ∩ S) :=
      norm_setIntegral_le_of_norm_le_const
        ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.2 hSCfin))
        fun x _ => (Real.norm_eq_abs (g x)).trans_le (hg1 x)
    rw [one_mul, Real.norm_eq_abs] at h1
    exact h1.trans (measureReal_mono hsub hSCfin)
  -- Step 5 (conclusion): `∫_A g ≥ μ(C) − μ(S \ C) > c`.
  rw [ENNReal.lt_ofReal_iff_toReal_lt hcfin, hsplit]
  have := neg_abs_le (∫ x in A \ C, g x ∂μ)
  linarith
/-- The coordinate wedge covectors are dual to the increasing basis tuples: the `J`-th coordinate
of `∑_I c_I dx^I` is `c_J`, i.e. `dx^I(e_{J(0)}, …, e_{J(k-1)}) = δ_{IJ}`. -/
theorem Submission.smr_ci_coord_sum_smul_wedge :
    ∀ (P k : ℕ) (c : SimonMultiIndex k P → ℝ) (J : SimonMultiIndex k P),
      euclideanCovectorCoordinate (∑ I : SimonMultiIndex k P,
        c I • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)) : Covector (Eucl P) k) J = c J := by
  intro P k c J
  classical
  -- Kronecker property: `dx^I (e_J) = δ_{IJ}`.
  have hK : ∀ I : SimonMultiIndex k P, wedgeCovectors k (fun j => EuclideanSpace.proj (I j))
      (fun j => EuclideanSpace.single (J j) (1 : ℝ)) = if I = J then 1 else 0 := by
    intro I
    rw [wedgeCovectors_apply_det]
    split_ifs with hIJ
    · -- the matrix `[δ_{I i, I j}]` is the identity
      subst hIJ
      convert Matrix.det_one (n := Fin k) (R := ℝ)
      ext i j
      simp [Matrix.one_apply, PiLp.single_apply, I.injective.eq_iff]
    · -- some `I i` is not among the `J j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra! h
        apply hIJ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range I ⊆ Set.range J := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range J)
        rw [Set.ncard_range_of_injective J.injective, Set.ncard_range_of_injective I.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  -- Evaluation at `e_J` is linear, so only the term `I = J` survives.
  rw [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
/-- A `k`-covector on `ℝ^P` whose coordinates `α(e_{I(0)}, …, e_{I(k-1)})` vanish for every
increasing multi-index `I` is zero. -/
theorem Submission.smr_ci_covector_eq_zero_of_coord :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k),
      (∀ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I = 0) → α = 0 := by
  intro P k α hα
  classical
  -- By extensionality on the standard basis it suffices to treat injective index tuples `v`.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.toAlternatingMap_zero,
    AlternatingMap.zero_apply]
  -- Sorting `v` gives an increasing multi-index `I` with `e_I = e_v ∘ σ`, `σ := Tuple.sort v`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  have h := hα (OrderEmbedding.ofStrictMono _ hsm)
  have heq : (fun j => EuclideanSpace.single (OrderEmbedding.ofStrictMono _ hsm j) (1 : ℝ)) =
      (fun i => EuclideanSpace.single (v i) (1 : ℝ)) ∘ Tuple.sort v := rfl
  -- `α(e_I) = sign σ • α(e_v)`, and the sign is a unit.
  rw [euclideanCovectorCoordinate, heq, ← ContinuousAlternatingMap.coe_toAlternatingMap α,
    AlternatingMap.map_perm] at h
  exact (smul_eq_zero_iff_eq _).mp h
/-- The Euclidean coefficient norm of a `k`-covector on `ℝ^P` is the `ℓ²`-norm of its coordinates
`α(e_{I(0)}, …, e_{I(k-1)})` over the increasing multi-indices `I : Fin k ↪o Fin P`. -/
theorem Submission.smr_ci_norm_eq_sqrt_sum_coord_sq :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k), covectorEuclideanNorm α =
      Real.sqrt (∑ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I ^ 2) := by
  intro P k α
  unfold covectorEuclideanNorm
  congr 1
  -- Drop the tuples that are not strictly increasing; their terms vanish.
  rw [← Finset.sum_filter]
  -- Reindex the strictly increasing tuples by the order embeddings, `I ↦ ⇑I`.
  symm
  refine Finset.sum_bij' (fun I _ => ⇑I)
    (fun f hf => OrderEmbedding.ofStrictMono f (Finset.mem_filter.1 hf).2)
    (fun I _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, I.strictMono⟩)
    (fun _ _ => Finset.mem_univ _) (fun I _ => ?_) (fun f _ => ?_) (fun I _ => ?_)
  · exact RelEmbedding.ext fun _ => rfl
  · exact OrderEmbedding.coe_ofStrictMono _
  · -- Matching summands: `basisFun i = EuclideanSpace.single i 1`.
    simp only [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]

/-- Simon (6.1.2)–(6.1.5): listing the coefficients `α(e_{I(0)}, …, e_{I(k-1)})` over the
increasing multi-indices `I` is a linear isomorphism `J` of the `k`-covectors on `ℝ^P` onto `ℝ^N`
with `|α| = ‖J α‖` for the Euclidean coefficient norm `|α| = covectorEuclideanNorm α`. -/
theorem Submission.smr_covector_coord_isometry :
    ∀ (P k : ℕ), ∃ (N : ℕ) (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖ := by
  intro P k
  -- Enumerate the increasing multi-indices `I : Fin k ↪o Fin P` by `Fin N`.
  let σ : Fin (Fintype.card (SimonMultiIndex k P)) ≃ SimonMultiIndex k P :=
    (Fintype.equivFin (SimonMultiIndex k P)).symm
  -- The coordinate map `J α = (α(e_{σ n}))_n`, linear because evaluation is.
  obtain ⟨J, hJ⟩ : ∃ J : Covector (Eucl P) k →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (SimonMultiIndex k P))),
      ∀ α n, J α n = euclideanCovectorCoordinate α (σ n) :=
    ⟨{ toFun := fun α => WithLp.toLp 2 fun n => euclideanCovectorCoordinate α (σ n)
       map_add' := fun α β => by
         ext n
         simp [euclideanCovectorCoordinate]
       map_smul' := fun c α => by
         ext n
         simp [euclideanCovectorCoordinate] }, fun _ _ => rfl⟩
  have hbij : Function.Bijective J := by
    refine ⟨(injective_iff_map_eq_zero J).2 fun α hα => ?_, fun y => ?_⟩
    · -- injective: a covector whose coordinates all vanish is zero
      refine Submission.smr_ci_covector_eq_zero_of_coord P k α fun I => ?_
      rw [← σ.apply_symm_apply I, ← hJ, hα, PiLp.zero_apply]
    · -- surjective: `∑_I y_{σ⁻¹ I} dx^I` has coordinates `y`
      refine ⟨∑ I : SimonMultiIndex k P,
        y (σ.symm I) • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)), ?_⟩
      ext n
      rw [hJ, Submission.smr_ci_coord_sum_smul_wedge, σ.symm_apply_apply]
  refine ⟨_, LinearEquiv.ofBijective J hbij, fun α => ?_⟩
  -- Both norms are square roots of the same sum of squares, reindexed along `σ`.
  rw [Submission.smr_ci_norm_eq_sqrt_sum_coord_sq, LinearEquiv.ofBijective_apply,
    EuclideanSpace.norm_eq, ← σ.sum_comp]
  simp only [hJ, Real.norm_eq_abs, sq_abs]
/-- **Mollification step of Simon Ch. 6, 2.7–2.9 (pp. 136–137).**  A continuous compactly
supported `k`-form `φ` with `tsupport φ ⊆ V`, `V` open, is a uniform limit, in the Euclidean
coefficient norm, of test forms supported in `V`.  As `|α| ≤ √M ‖α‖` (`M = #(Fin k → Fin P)`,
`‖α‖` the operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ φ)`:
`ψ ⋆ φ` is the convolution of `φ` with a normalized smooth bump `ψ` supported in a ball whose
radius is a uniform-continuity modulus of `φ`, and `χ` is a smooth cutoff with values in `[0, 1]`,
equal to `1` exactly on `tsupport φ`, whose support `V'` has compact closure in `V`. -/
theorem Submission.smr_exists_testForm_uniform_approx : ∀ (P k : ℕ) (U V : Set (Eucl P)) (φ : Eucl P → Covector (Eucl P) k), IsOpen V → V ⊆ U → Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧ ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ ε := by
  intro P k U V φ hV hVU hφ hφc hφV ε hε
  -- Step 1: `|α| ≤ C ‖α‖` with `C = √M`, since every coefficient satisfies
  -- `|α(e_I)| ≤ ‖α‖ ∏ ‖e_{I j}‖ = ‖α‖`.
  set C : ℝ := Real.sqrt (Fintype.card (Fin k → Fin P)) with hC_def
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hcmp : ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hC_def, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin k → Fin P,
          (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
        ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg α)] using h)
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  have hC1 : 0 < C + 1 := by linarith
  set ε' : ℝ := ε / (C + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε hC1
  -- Step 2: an open `V'` with `tsupport φ ⊆ V'` and `closure V' ⊆ V` compact.
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ :=
    exists_open_between_and_isCompact_closure hφc.isCompact hV hφV
  -- Step 3: a smooth cutoff `χ : ℝ^P → [0, 1]` with `support χ = V'` and `χ = 1` exactly on
  -- `tsupport φ`.
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV'o (isClosed_tsupport φ) hKV'
  -- Step 4: mollification.  `φ` is uniformly continuous with modulus `δ` at accuracy `ε'`; `ψ` is
  -- a smooth bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `g = ψ ⋆ φ` is smooth and
  -- `dist (g x) (φ x) ≤ ε'`.
  obtain ⟨δ, hδ, hφδ⟩ :=
    Metric.uniformContinuous_iff.mp (hφc.uniformContinuous_of_continuous hφ) ε' hε'
  obtain ⟨b, hbs, hbc, hbd, hbr, hb0⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
  have hbnn : ∀ y, 0 ≤ b y := fun y => (hbr (mem_range_self y)).1
  have hbint : 0 < ∫ y, b y :=
    hbd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc (fun y => hbnn y)
      (hb0.symm ▸ one_ne_zero : b 0 ≠ 0)
  set ψ : Eucl P → ℝ := fun y => (∫ z, b z)⁻¹ * b y with hψ_def
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hbd
  have hψc : HasCompactSupport ψ := hbc.mul_left
  have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hbint.le) (hbnn y)
  have hψs : Function.support ψ ⊆ ball 0 δ :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport b).trans hbs)
  have hψ1 : ∫ y, ψ y = 1 := by
    rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hbint.ne']
  obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → Covector (Eucl P) k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (φ x) ≤ ε' :=
    ⟨convolution ψ φ (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      hψc.contDiff_convolution_left _ hψd hφ.locallyIntegrable,
      fun x => dist_convolution_le hε'.le hψs hψnn hψ1 hφ.aestronglyMeasurable
        fun y hy => (hφδ (mem_ball.mp hy)).le⟩
  -- Step 5: `η = χ • g` is a test form with `tsupport η ⊆ closure V' ⊆ V ⊆ U`.
  have hη_supp : tsupport (fun x => χ x • g x) ⊆ closure V' := by
    refine (tsupport_smul_subset_left χ g).trans ?_
    rw [tsupport, hχs]
  have hη_cpt : HasCompactSupport (fun x => χ x • g x) :=
    hV'c.of_isClosed_subset (isClosed_tsupport _) hη_supp
  refine ⟨⟨fun x => χ x • g x, ⟨⟨hχ.smul hg, hη_cpt⟩, hη_supp.trans (hV'V.trans hVU)⟩⟩,
    hη_supp.trans hV'V, fun x => ?_⟩
  -- Step 6: `‖φ x - η x‖ ≤ ε'` (on `tsupport φ`, `η = g`; off it, `φ = 0` and `0 ≤ χ ≤ 1`),
  -- hence `|φ x - η x| ≤ C ε' ≤ ε`.
  have hle : ‖φ x - χ x • g x‖ ≤ ε' := by
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε' := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  calc covectorEuclideanNorm (φ x - χ x • g x) ≤ C * ‖φ x - χ x • g x‖ := hcmp _
    _ ≤ C * ε' := mul_le_mul_of_nonneg_left hle hC
    _ ≤ ε := by
      rw [hε'_def, mul_div_assoc', div_le_iff₀ hC1]
      nlinarith

/-- Continuous extension of a current of locally finite mass (Simon Ch. 6, 2.7, pp. 136–137,
steps P1–P2): there is `L` on continuous forms with `L = X` on test forms, additive and
homogeneous on continuous compactly supported forms in `U`, and with `|L φ|` bounded on each
compact `K ⊆ U` for `|φ| ≤ 1` (Euclidean coefficient norm).  `L φ` is the limit of `X (ζ j)`
along any sequence of test forms `ζ j`, supported in a common `V ⊂⊂ U`, converging to `φ`
uniformly; the limit exists and is unique by the mass estimate `|X ω| ≤ M_V(X) · sup |ω|`. -/
theorem Submission.smr_exists_continuous_extension :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) →
      ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ,
        (∀ ω : TestFormOn U k, L (ω : DifferentialForm (Eucl P) k) = X ω) ∧
        (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          L (φ + ψ) = L φ + L ψ) ∧
        (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → L (c • φ) = c * L φ) ∧
        ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
          ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → tsupport φ ⊆ K →
            (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → |L φ| ≤ B := by
  intro P k U hU X hX
  -- Step 0: the Euclidean coefficient norm is a norm, via the isometry `J` onto `ℝ^N`.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have hle : ∀ α β : Covector (Eucl P) k,
      covectorEuclideanNorm β ≤ covectorEuclideanNorm α + covectorEuclideanNorm (α - β) := by
    intro α β
    simp only [hJ, map_sub]
    exact norm_le_norm_add_norm_sub _ _
  have htri : ∀ α β γ : Covector (Eucl P) k, covectorEuclideanNorm (β - γ) ≤
      covectorEuclideanNorm (α - β) + covectorEuclideanNorm (α - γ) := by
    intro α β γ
    simp only [hJ, map_sub]
    calc ‖J β - J γ‖ ≤ ‖J β - J α‖ + ‖J α - J γ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖J α - J β‖ + ‖J α - J γ‖ := by rw [norm_sub_rev (J β)]
  have hadd : ∀ α β γ δ : Covector (Eucl P) k, covectorEuclideanNorm (α + β - (γ + δ)) ≤
      covectorEuclideanNorm (α - γ) + covectorEuclideanNorm (β - δ) := by
    intro α β γ δ
    rw [add_sub_add_comm]
    simp only [hJ, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hJ, hJ, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 1: compact subsets of `U` lie in some `V ⊂⊂ U`, and `⊂⊂ U` is closed under unions.
  have hnbhd : ∀ K, IsCompact K → K ⊆ U → ∃ V, CompactlyContainedOpen V U ∧ K ⊆ V := by
    intro K hK hKU
    obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨V, ⟨hVo, hVc, hVU⟩, hKV⟩
  have hunion : ∀ V₁ V₂, CompactlyContainedOpen V₁ U → CompactlyContainedOpen V₂ U →
      CompactlyContainedOpen (V₁ ∪ V₂) U := by
    rintro V₁ V₂ ⟨h₁o, h₁c, h₁U⟩ ⟨h₂o, h₂c, h₂U⟩
    refine ⟨h₁o.union h₂o, ?_, ?_⟩ <;> rw [closure_union]
    · exact h₁c.union h₂c
    · exact union_subset h₁U h₂U
  -- Step 2 (P1): `|X ω| ≤ M_V · C` for `ω` supported in `V ⊂⊂ U` with `|ω| ≤ C`.
  have hmass : ∀ V, CompactlyContainedOpen V U → ∀ (ω : TestFormOn U k) (C : ℝ),
      tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ C) →
      |X ω| ≤ (X.massOn V).toReal * C := by
    intro V hV ω C hωV hC
    -- For `s > C`, both `±s⁻¹ ω` are admissible for `M_V(X)`, hence `|X ω| ≤ M_V · s`.
    have key : ∀ s, C < s → |X ω| ≤ (X.massOn V).toReal * s := by
      intro s hs
      have hs0 : 0 < s := ((covectorEuclideanNorm_nonneg _).trans (hC 0)).trans_lt hs
      have hb : ∀ t : ℝ, |t| = s⁻¹ → t * X ω ≤ (X.massOn V).toReal := by
        intro t ht
        have hadm : t • ω ∈ massAdmissibleOn U k V := by
          refine ⟨(tsupport_smul_subset_right (fun _ => t) _).trans hωV, fun x => ?_⟩
          change covectorEuclideanNorm (t • (ω : DifferentialForm (Eucl P) k) x) ≤ 1
          rw [hsmul, ht, inv_mul_le_iff₀ hs0, mul_one]
          exact (hC x).trans hs.le
        have h := (X.le_massOn hadm).trans (ENNReal.ofReal_toReal (hX V hV).ne).ge
        rwa [ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, map_smul, smul_eq_mul] at h
      have h₁ := hb s⁻¹ (abs_of_pos (inv_pos.2 hs0))
      have h₂ := hb (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs0)])
      rw [inv_mul_le_iff₀ hs0, mul_comm] at h₁
      rw [neg_mul_comm, inv_mul_le_iff₀ hs0, mul_comm] at h₂
      exact abs_le.2 ⟨by linarith, h₁⟩
    -- Let `s ↓ C` along `s = C + 1 / (n + 1)`.
    have hlim : Tendsto (fun n : ℕ => (X.massOn V).toReal * (C + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 ((X.massOn V).toReal * C)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add C).const_mul
        (X.massOn V).toReal
    exact ge_of_tendsto' hlim fun n => key _ (lt_add_of_pos_right C Nat.one_div_pos_of_nat)
  -- Test forms supported in `V₁, V₂ ⊂⊂ U` and uniformly close to the same `φ` have close values.
  have hclose : ∀ (φ : Eucl P → Covector (Eucl P) k) V₁ V₂, CompactlyContainedOpen V₁ U →
      CompactlyContainedOpen V₂ U → ∀ (η ζ : TestFormOn U k) (a b : ℝ),
      tsupport (η : DifferentialForm (Eucl P) k) ⊆ V₁ →
      tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ V₂ →
      (∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ a) →
      (∀ x, covectorEuclideanNorm (φ x - (ζ : DifferentialForm (Eucl P) k) x) ≤ b) →
      |X η - X ζ| ≤ (X.massOn (V₁ ∪ V₂)).toReal * (a + b) := by
    intro φ V₁ V₂ hV₁ hV₂ η ζ a b hη hζ ha hb
    rw [← map_sub X.toCurrent η ζ]
    refine hmass _ (hunion V₁ V₂ hV₁ hV₂) (η - ζ) (a + b) ?_ fun x =>
      (htri (φ x) ((η : DifferentialForm (Eucl P) k) x)
        ((ζ : DifferentialForm (Eucl P) k) x)).trans (add_le_add (ha x) (hb x))
    exact (closure_mono (Function.support_sub _ _)).trans
      (closure_union.subset.trans (union_subset_union hη hζ))
  -- Step 4: approximations supported in a common `V ⊂⊂ U` give Cauchy sequences `X (ζ j)`.
  have hconv : ∀ (φ : Eucl P → Covector (Eucl P) k) V, CompactlyContainedOpen V U →
      ∀ (ζ : ℕ → TestFormOn U k) (d : ℕ → ℝ),
      (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) → Tendsto d atTop (𝓝 0) →
      (∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ d j) →
      ∃ r, Tendsto (fun j => X (ζ j)) atTop (𝓝 r) := by
    intro φ V hV ζ d hζV hd hζ
    have hMd : Tendsto (fun j => (X.massOn (V ∪ V)).toReal * d j) atTop (𝓝 0) := by
      simpa using hd.const_mul (X.massOn (V ∪ V)).toReal
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hMd).2 (ε / 2) (half_pos hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    calc |X (ζ n) - X (ζ N)| ≤ (X.massOn (V ∪ V)).toReal * (d n + d N) :=
          hclose φ V V hV hV (ζ n) (ζ N) (d n) (d N) (hζV n) (hζV N) (hζ n) (hζ N)
      _ = (X.massOn (V ∪ V)).toReal * d n + (X.massOn (V ∪ V)).toReal * d N := mul_add _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hN n hn) (hN N le_rfl)
      _ = ε := add_halves ε
  -- `IsLim φ r`: test forms `ζ j`, supported in a common `V ⊂⊂ U`, converge uniformly to `φ`
  -- (errors `d j → 0`) and `X (ζ j) → r`.
  let IsLim : (Eucl P → Covector (Eucl P) k) → ℝ → Prop := fun φ r =>
    ∃ V, CompactlyContainedOpen V U ∧ ∃ (ζ : ℕ → TestFormOn U k) (d : ℕ → ℝ),
      (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) ∧ Tendsto d atTop (𝓝 0) ∧
      (∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ d j) ∧
      Tendsto (fun j => X (ζ j)) atTop (𝓝 r)
  -- Step 5: the limit does not depend on the approximation.
  have huniq : ∀ φ r s, IsLim φ r → IsLim φ s → r = s := by
    rintro φ r s ⟨V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩ ⟨V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩
    have h0 : Tendsto (fun j => X (ζ₁ j) - X (ζ₂ j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans
        (hclose φ V₁ V₂ hV₁ hV₂ (ζ₁ j) (ζ₂ j) (d₁ j) (d₂ j) (hs₁ j) (hs₂ j) (ha₁ j)
          (ha₂ j))) ?_
      simpa using (hd₁.add hd₂).const_mul (X.massOn (V₁ ∪ V₂)).toReal
    exact sub_eq_zero.1 (tendsto_nhds_unique (hl₁.sub hl₂) h0)
  -- Definition of `L`: the common limit of the approximations (arbitrary if there are none).
  obtain ⟨L, hL⟩ : ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ, ∀ φ r, IsLim φ r → L φ = r :=
    ⟨fun φ => Classical.epsilon (IsLim φ), fun φ r hr =>
      huniq φ _ _ (Classical.epsilon_spec ⟨r, hr⟩) hr⟩
  -- Step 3: uniform approximants `|φ - ζ j| ≤ 1 / (j + 1)` supported in `V`.
  have happ : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
      ∀ V, CompactlyContainedOpen V U → tsupport φ ⊆ V →
      ∃ ζ : ℕ → TestFormOn U k, (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) ∧
        ∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤
          1 / ((j : ℝ) + 1) := by
    intro φ hφ hφc V hV hφV
    choose ζ hζV hζ using fun j : ℕ =>
      Submission.smr_exists_testForm_uniform_approx P k U V φ hV.1
        (subset_closure.trans hV.2.2) hφ hφc hφV (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨ζ, hζV, hζ⟩
  -- Every `φ ∈ CF(U)` has an approximation, hence a limit.
  have hexists : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∃ r, IsLim φ r := by
    intro φ hφ hφc hφU
    obtain ⟨V, hV, hφV⟩ := hnbhd _ hφc hφU
    obtain ⟨ζ, hζV, hζ⟩ := happ φ hφ hφc V hV hφV
    obtain ⟨r, hr⟩ := hconv φ V hV ζ _ hζV tendsto_one_div_add_atTop_nhds_zero_nat hζ
    exact ⟨r, V, hV, ζ, _, hζV, tendsto_one_div_add_atTop_nhds_zero_nat, hζ, hr⟩
  refine ⟨L, fun ω => ?_, fun φ ψ hφ hφc hφU hψ hψc hψU => ?_,
    fun c φ hφ hφc hφU => ?_, fun K hK hKU => ?_⟩
  · -- (1) The constant approximation `ζ j = ω`.
    obtain ⟨V, hV, hωV⟩ := hnbhd _ ω.2.1.2 ω.2.2
    exact hL _ _ ⟨V, hV, fun _ => ω, fun _ => 0, fun _ => hωV, tendsto_const_nhds,
      fun _ x => by simp, tendsto_const_nhds⟩
  · -- (2) The sum of approximations of `φ` and `ψ`.
    obtain ⟨r₁, V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩ := hexists φ hφ hφc hφU
    obtain ⟨r₂, V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩ := hexists ψ hψ hψc hψU
    rw [hL φ r₁ ⟨V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩,
      hL ψ r₂ ⟨V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩]
    refine hL _ _ ⟨V₁ ∪ V₂, hunion V₁ V₂ hV₁ hV₂, fun j => ζ₁ j + ζ₂ j,
      fun j => d₁ j + d₂ j, fun j => ?_, by simpa using hd₁.add hd₂, fun j x => ?_, ?_⟩
    · exact (tsupport_add (ζ₁ j : DifferentialForm (Eucl P) k) (ζ₂ j)).trans
        (union_subset_union (hs₁ j) (hs₂ j))
    · exact (hadd (φ x) (ψ x) ((ζ₁ j : DifferentialForm (Eucl P) k) x)
        ((ζ₂ j : DifferentialForm (Eucl P) k) x)).trans (add_le_add (ha₁ j x) (ha₂ j x))
    · simpa only [map_add] using hl₁.add hl₂
  · -- (3) The scalar multiple of an approximation of `φ`.
    obtain ⟨r, V, hV, ζ, d, hs, hd, ha, hl⟩ := hexists φ hφ hφc hφU
    rw [hL φ r ⟨V, hV, ζ, d, hs, hd, ha, hl⟩]
    refine hL _ _ ⟨V, hV, fun j => c • ζ j, fun j => |c| * d j,
      fun j => (tsupport_smul_subset_right (fun _ => c) _).trans (hs j),
      by simpa using hd.const_mul |c|, fun j x => ?_, ?_⟩
    · have e : (c • φ) x - ((c • ζ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x =
          c • (φ x - (ζ j : DifferentialForm (Eucl P) k) x) := (smul_sub c _ _).symm
      rw [e, hsmul]
      exact mul_le_mul_of_nonneg_left (ha j x) (abs_nonneg c)
    · simpa only [map_smul, smul_eq_mul] using hl.const_mul c
  · -- (4) `|L φ| ≤ 2 M_V` for `|φ| ≤ 1` supported in `K ⊆ V ⊂⊂ U`.
    obtain ⟨V, hV, hKV⟩ := hnbhd K hK hKU
    refine ⟨(X.massOn V).toReal * 2, fun φ hφ hφK hφ1 => ?_⟩
    have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hφK
    obtain ⟨ζ, hζV, hζ⟩ := happ φ hφ hφc V hV (hφK.trans hKV)
    obtain ⟨r, hr⟩ := hconv φ V hV ζ _ hζV tendsto_one_div_add_atTop_nhds_zero_nat hζ
    rw [hL φ r ⟨V, hV, ζ, _, hζV, tendsto_one_div_add_atTop_nhds_zero_nat, hζ, hr⟩]
    refine le_of_tendsto' hr.abs fun j => hmass V hV (ζ j) 2 (hζV j) fun x => ?_
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    calc covectorEuclideanNorm ((ζ j : DifferentialForm (Eucl P) k) x)
        ≤ covectorEuclideanNorm (φ x) +
            covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) := hle _ _
      _ ≤ 1 + 1 := add_le_add (hφ1 x) ((hζ j x).trans h1)
      _ = 2 := one_add_one_eq_two
/-- **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6(v) of `slicing_mass_representation`.  If
`S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, where `|⟨α, v(x)⟩| ≤ |α|` and `μ` is finite on
compact subsets of `U`, then `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)` for every continuous compactly supported
`k`-form `φ` with `spt φ ⊆ W ⊆ U`, `W` open, and `|φ| ≤ 1`.

Take an open `V ⊇ spt φ` whose closure is a compact subset of `W`.  The smooth approximants
`η_j ∈ 𝒟ᵏ(U)` of `smr_exists_testForm_uniform_approx` (`spt η_j ⊆ V`, `|φ - η_j| ≤ δ_j → 0`),
rescaled to `ζ_j = (1 + δ_j)⁻¹ η_j`, are admissible for `M_W(S)` and satisfy
`|ζ_j - φ| ≤ 2 δ_j`; the triangle inequality and homogeneity of `|·|` come from
`smr_covector_coord_isometry`.  Dominated convergence on `μ ⌞ A` with the bound `1_{closure V}`
gives `S(ζ_j) → ∫_A ⟨φ, v⟩ dμ`, and `ofReal (S(ζ_j)) ≤ M_W(S)` passes to the limit. -/
theorem Submission.smr_ofReal_integral_le_massOn : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U k), (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ W → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) ≤ S.massOn W := by
  intro P k U μ v hint hfin hv A S hS W hW hWU φ hφc hφs hφW hφ1
  -- `|α| = ‖J α‖` for a linear `J`, so `|·|` is subadditive and absolutely homogeneous.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have hadd : ∀ α β : Covector (Eucl P) k,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hJ, hJ, hJ, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hJ, hJ, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 1: an open `V ⊇ tsupport φ` whose closure is a compact subset of `W ⊆ U`.
  obtain ⟨V, hVo, hφV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hφs hW hφW
  have hKU : closure V ⊆ U := hVW.trans hWU
  have hμK : μ (closure V) < ∞ := hfin _ hVc hKU
  have hVU : V ⊆ U := subset_closure.trans hKU
  -- Step 2: test forms `η j` supported in `V` with `|φ - η j| ≤ δ j → 0`, and
  -- `ζ j = (1 + δ j)⁻¹ • η j`.
  obtain ⟨δ, hδpos, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun j => 1 / ((j : ℝ) + 1), fun j => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  have hη : ∀ j : ℕ, ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧
      ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ δ j := fun j =>
    Submission.smr_exists_testForm_uniform_approx P k U V φ hVo hVU hφc hφs hφV (δ j) (hδpos j)
  choose η hηV hηφ using hη
  obtain ⟨ζ, hζx⟩ : ∃ ζ : ℕ → TestFormOn U k, ∀ j x,
      (ζ j : DifferentialForm (Eucl P) k) x = (1 + δ j)⁻¹ • (η j : DifferentialForm (Eucl P) k) x :=
    ⟨fun j => (1 + δ j)⁻¹ • η j, fun j x => rfl⟩
  have hpos : ∀ j, 0 < 1 + δ j := fun j => by linarith [hδpos j]
  have hηle : ∀ j x, covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x) ≤ 1 + δ j := by
    intro j x
    calc covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
        = covectorEuclideanNorm (φ x + -(φ x - (η j : DifferentialForm (Eucl P) k) x)) := by
          congr 1
          abel
      _ ≤ covectorEuclideanNorm (φ x) +
            covectorEuclideanNorm (-(φ x - (η j : DifferentialForm (Eucl P) k) x)) := hadd _ _
      _ ≤ 1 + δ j := by
          rw [covectorEuclideanNorm_neg]
          exact add_le_add (hφ1 x) (hηφ j x)
  -- Step 3: every `ζ j` is admissible for `M_W(S)`, so `ofReal (S (ζ j)) ≤ M_W(S)`.
  have hadm : ∀ j, ζ j ∈ massAdmissibleOn U k W := by
    intro j
    refine ⟨?_, fun x => ?_⟩
    · have hfun : (ζ j : DifferentialForm (Eucl P) k) =
          fun x => (1 + δ j)⁻¹ • (η j : DifferentialForm (Eucl P) k) x := funext (hζx j)
      rw [hfun]
      exact (tsupport_smul_subset_right (fun _ => (1 + δ j)⁻¹) _).trans
        ((hηV j).trans (subset_closure.trans hVW))
    · rw [hζx, hsmul, abs_of_pos (inv_pos.mpr (hpos j))]
      calc (1 + δ j)⁻¹ * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
          ≤ (1 + δ j)⁻¹ * (1 + δ j) :=
            mul_le_mul_of_nonneg_left (hηle j x) (inv_nonneg.mpr (hpos j).le)
        _ = 1 := inv_mul_cancel₀ (hpos j).ne'
  -- Step 4: `|ζ j - φ| ≤ 2 δ j` everywhere, and `ζ j` vanishes off `V`.
  have hclose : ∀ j x,
      covectorEuclideanNorm ((ζ j : DifferentialForm (Eucl P) k) x - φ x) ≤ 2 * δ j := by
    intro j x
    have e : (ζ j : DifferentialForm (Eucl P) k) x - φ x =
        ((1 + δ j)⁻¹ - 1) • (η j : DifferentialForm (Eucl P) k) x +
          -(φ x - (η j : DifferentialForm (Eucl P) k) x) := by
      rw [hζx]
      module
    have habs : |(1 + δ j)⁻¹ - 1| = δ j / (1 + δ j) := by
      have h : (1 + δ j)⁻¹ - 1 = -(δ j / (1 + δ j)) := by
        linear_combination mul_inv_cancel₀ (hpos j).ne'
      rw [h, abs_neg, abs_of_pos (div_pos (hδpos j) (hpos j))]
    have h2 : δ j / (1 + δ j) * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
        ≤ δ j :=
      calc δ j / (1 + δ j) * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
          ≤ δ j / (1 + δ j) * (1 + δ j) :=
            mul_le_mul_of_nonneg_left (hηle j x) (div_pos (hδpos j) (hpos j)).le
        _ = δ j := div_mul_cancel₀ _ (hpos j).ne'
    rw [e]
    refine (hadd _ _).trans ?_
    rw [covectorEuclideanNorm_neg, hsmul, habs]
    linarith [hηφ j x]
  have hζ0 : ∀ j x, x ∉ V → (ζ j : DifferentialForm (Eucl P) k) x = 0 := fun j x hx => by
    rw [hζx, image_eq_zero_of_notMem_tsupport fun h => hx (hηV j h), smul_zero]
  -- Steps 5–6: dominated convergence on `μ ⌞ A`, with the integrable bound `1_{closure V}`
  -- (`μ (closure V) < ∞`), gives `S (ζ j) → ∫_A ⟨φ, v⟩ dμ`.
  have hlim : Tendsto (fun j => S (ζ j)) atTop (𝓝 (∫ x in A, v x (φ x) ∂μ)) := by
    simp only [hS]
    refine tendsto_integral_of_dominated_convergence
      (F := fun j x => v x ((ζ j : DifferentialForm (Eucl P) k) x)) (f := fun x => v x (φ x))
      ((closure V).indicator fun _ => (1 : ℝ))
      (fun j => (hint (ζ j)).aestronglyMeasurable.restrict)
      ((integrable_indicator_iff isClosed_closure.measurableSet).mpr
        (integrableOn_const ((Measure.restrict_apply_le A (closure V)).trans_lt hμK).ne))
      (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ V
      · rw [indicator_of_mem (subset_closure hx), Real.norm_eq_abs]
        exact (hv x _).trans ((hadm j).2 x)
      · rw [hζ0 j x hx, map_zero, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) x
    · have h2δ : Tendsto (fun j => 2 * δ j) atTop (𝓝 0) := by
        simpa using hδlim.const_mul 2
      have h0 : Tendsto (fun j => v x ((ζ j : DifferentialForm (Eucl P) k) x) - v x (φ x))
          atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun j => ?_) h2δ
        rw [← map_sub, Real.norm_eq_abs]
        exact (hv x _).trans (hclose j x)
      simpa using h0.add_const (v x (φ x))
  -- Step 7: pass to the limit in `ofReal (S (ζ j)) ≤ M_W(S)`.
  exact le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun j => S.le_massOn (hadm j)
/-- Extension by zero from `↥U` to `ℝ^P` transfers a locally bounded functional `L` on
`CF_N(U)` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`, with `L f = L' (f ∘ ι)`
for every `f ∈ CF_N(U)`. -/
theorem Submission.smr_rb_transfer_functional :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ,
      (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        L (f + g) = L f + L g) →
      (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → L (c • f) = c * L f) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K →
          (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) →
      ∃ L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ,
        (∀ K : Set ↥U, IsCompact K → ∃ B : ℝ,
          ∀ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)),
            (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L' g ≤ B) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U →
          ∃ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)),
            (∀ y : ↥U, g y = f ↑y) ∧ L f = L' g := by
  intro P N U hU L hadd hsmul hbd
  -- The zero extension `E g = Function.extend Subtype.val g 0` of `g ∈ C_c(↥U, ℝ^N)`.
  set E : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →
      Eucl P → EuclideanSpace ℝ (Fin N) := fun g => Function.extend Subtype.val (⇑g) 0
  have hEval : ∀ g x (hx : x ∈ U), E g x = g ⟨x, hx⟩ := fun g x hx =>
    Subtype.val_injective.extend_apply (⇑g) 0 ⟨x, hx⟩
  have hEout : ∀ g x, x ∉ U → E g x = 0 := fun g x hx =>
    Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)
  -- `E g ∈ CF_N(U)`, with `tsupport (E g) ⊆ ι(tsupport g)`; continuity uses that `U` is open.
  have hEsupp : ∀ g, tsupport (E g) ⊆ Subtype.val '' tsupport g := fun g =>
    g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val
  have hEU : ∀ g, tsupport (E g) ⊆ U := fun g =>
    (hEsupp g).trans (Subtype.coe_image_subset _ _)
  have hEcpt : ∀ g, HasCompactSupport (E g) := fun g =>
    g.hasCompactSupport.extend_zero continuous_subtype_val
  have hEcont : ∀ g, Continuous (E g) := fun g =>
    HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport
  -- The extension is linear.
  have hEadd : ∀ g h, E (g + h) = E g + E h := by
    intro g h; funext x
    by_cases hx : x ∈ U
    · simp only [Pi.add_apply, hEval _ x hx, CompactlySupportedContinuousMap.add_apply]
    · simp only [Pi.add_apply, hEout _ x hx, add_zero]
  have hEsmul : ∀ (c : ℝ) g, E (c • g) = c • E g := by
    intro c g; funext x
    by_cases hx : x ∈ U
    · simp only [Pi.smul_apply, hEval _ x hx, CompactlySupportedContinuousMap.smul_apply]
    · simp only [Pi.smul_apply, hEout _ x hx, smul_zero]
  -- `L' g = L (E g)` is linear by the additivity and homogeneity of `L` on `CF_N(U)`.
  let L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ :=
    { toFun := fun g => L (E g)
      map_add' := fun g h => by
        show L (E (g + h)) = L (E g) + L (E h)
        rw [hEadd]
        exact hadd _ _ (hEcont g) (hEcpt g) (hEU g) (hEcont h) (hEcpt h) (hEU h)
      map_smul' := fun c g => by
        show L (E (c • g)) = c * L (E g)
        rw [hEsmul]
        exact hsmul c _ (hEcont g) (hEcpt g) (hEU g) }
  refine ⟨L', fun K hK => ?_, fun f hf hfc hfU => ?_⟩
  · -- The bound for the compact set `ι(K) ⊆ U` serves for `L'` on `K`.
    obtain ⟨B, hB⟩ := hbd (Subtype.val '' K) (hK.image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)
    refine ⟨B, fun g hg hgK => hB (E g) (hEcont g) ((hEsupp g).trans (image_mono hgK)) fun x => ?_⟩
    by_cases hx : x ∈ U
    · rw [hEval g x hx]; exact hg _
    · rw [hEout g x hx, norm_zero]; exact zero_le_one
  · -- `g = f ∘ ι` vanishes off the compact set `ι⁻¹(tsupport f)`, and `E g = f`.
    have hcpt : HasCompactSupport (f ∘ Subtype.val : ↥U → EuclideanSpace ℝ (Fin N)) := by
      refine HasCompactSupport.intro (K := Subtype.val ⁻¹' tsupport f) ?_ fun y hy => ?_
      · exact (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (hfU.trans Subtype.range_coe.symm.subset)).2 hfc
      · exact image_eq_zero_of_notMem_tsupport (f := f) hy
    let g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) :=
      ⟨⟨f ∘ Subtype.val, hf.comp continuous_subtype_val⟩, hcpt⟩
    refine ⟨g, fun y => rfl, ?_⟩
    show L f = L (E g)
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hEval g x hx]; rfl
    · rw [hEout g x hx]
      exact image_eq_zero_of_notMem_tsupport fun h => hx (hfU h)
/-- Riesz representation (Simon Ch. 1, 4.14) with Borel data on a σ-compact locally compact
Hausdorff space: a locally bounded functional on `C_c(Y, ℝ^N)` is `g ↦ ∫ ⟨g, ν⟩ dm` for a
measure `m` finite on compacts and a Borel field `ν` with `‖ν‖ ≤ 1`, `‖ν‖ = 1` `m`-a.e. -/
theorem Submission.smr_rb_borel_riesz_sigma_compact : ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (N : ℕ) (L : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ), (∀ K : Set Y, IsCompact K → ∃ B : ℝ, ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L g ≤ B) → ∃ (m : Measure Y) (ν : Y → EuclideanSpace ℝ (Fin N)), (∀ K : Set Y, IsCompact K → m K < ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ ≤ 1) ∧ (∀ᵐ y ∂m, ‖ν y‖ = 1) ∧ ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), L g = ∫ y, inner ℝ (g y) (ν y) ∂m := by
  intro Y _ _ _ _ _ _ N L hL
  -- Step 1: a functional on `C_c(Y, ℝ)` bounded above on each order interval `[0, f]` is
  -- dominated on nonnegative functions by a positive functional (its positive part).
  have key : ∀ ℓ : CompactlySupportedContinuousMap Y ℝ →ₗ[ℝ] ℝ,
      (∀ f : CompactlySupportedContinuousMap Y ℝ≥0, ∃ B : ℝ,
        ∀ φ : CompactlySupportedContinuousMap Y ℝ≥0, φ ≤ f → ℓ φ.toReal ≤ B) →
      ∃ Λ : CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ,
        ∀ f : CompactlySupportedContinuousMap Y ℝ, 0 ≤ f → ℓ f ≤ Λ f := by
    intro ℓ hB
    -- `S f = sup {ℓ φ : φ ≤ f}`, the positive part of `ℓ` on nonnegative functions
    let S : CompactlySupportedContinuousMap Y ℝ≥0 → ℝ := fun f =>
      sSup ((fun φ : CompactlySupportedContinuousMap Y ℝ≥0 => ℓ φ.toReal) '' Set.Iic f)
    have hzero : (0 : CompactlySupportedContinuousMap Y ℝ≥0).toReal = 0 := by ext; simp
    have hle : ∀ f φ, φ ≤ f → ℓ φ.toReal ≤ S f := by
      intro f φ hφ
      obtain ⟨B, hB⟩ := hB f
      exact le_csSup ⟨B, by rintro _ ⟨ψ, hψ, rfl⟩; exact hB ψ hψ⟩ ⟨φ, hφ, rfl⟩
    have hsup : ∀ f c, (∀ φ, φ ≤ f → ℓ φ.toReal ≤ c) → S f ≤ c := by
      intro f c h
      exact csSup_le ⟨_, 0, fun y => zero_le, rfl⟩ (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ)
    have hS0 : ∀ f, 0 ≤ S f := fun f => by
      simpa [hzero] using hle f 0 (fun y => zero_le)
    have hadd : ∀ f g, S (f + g) = S f + S g := by
      intro f g
      refine le_antisymm (hsup _ _ fun φ hφ => ?_) ?_
      · obtain ⟨φ₂, hφ₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le
          (inf_le_left : φ ⊓ f ≤ φ)
        have h2 : φ₂ ≤ g := by
          intro y
          have e := DFunLike.congr_fun hφ₂ y
          have hy := hφ y
          simp only [CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.inf_apply] at e hy
          rcases le_total (φ y) (f y) with h | h
          · rw [inf_eq_left.2 h] at e
            have : φ₂ y = 0 := by simpa using e
            rw [this]; exact zero_le
          · rw [inf_eq_right.2 h] at e
            rw [← e] at hy
            exact le_of_add_le_add_left hy
        calc ℓ φ.toReal = ℓ (φ ⊓ f).toReal + ℓ φ₂.toReal := by
              rw [← map_add, ← CompactlySupportedContinuousMap.toReal_add, hφ₂]
          _ ≤ S f + S g := add_le_add (hle _ _ inf_le_right) (hle _ _ h2)
      · have h1 : ∀ φ, φ ≤ f → ℓ φ.toReal + S g ≤ S (f + g) := by
          intro φ hφ
          have := hsup g (S (f + g) - ℓ φ.toReal) fun ψ hψ => by
            have := hle (f + g) (φ + ψ) fun y => add_le_add (hφ y) (hψ y)
            rw [CompactlySupportedContinuousMap.toReal_add, map_add] at this
            linarith
          linarith
        have := hsup f (S (f + g) - S g) fun φ hφ => by linarith [h1 φ hφ]
        linarith
    have hsmul_le : ∀ (c : ℝ≥0) f, S (c • f) ≤ c * S f := by
      intro c f
      rcases eq_or_ne c 0 with rfl | hc
      · refine hsup _ _ fun φ hφ => ?_
        have : φ = 0 := by
          ext y
          have := hφ y
          simp only [zero_smul, CompactlySupportedContinuousMap.zero_apply] at this
          simpa using le_antisymm this zero_le
        simp [this, hzero]
      · refine hsup _ _ fun φ hφ => ?_
        have h1 : c⁻¹ • φ ≤ f := by
          intro y
          have := hφ y
          simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul] at this ⊢
          rwa [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)]
        have h2 : c • (c⁻¹ • φ) = φ := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        calc ℓ φ.toReal = c * ℓ (c⁻¹ • φ).toReal := by
              conv_lhs => rw [← h2]
              rw [CompactlySupportedContinuousMap.toReal_smul, NNReal.smul_def, map_smul,
                smul_eq_mul]
          _ ≤ c * S f := mul_le_mul_of_nonneg_left (hle _ _ h1) c.2
    have hsmul : ∀ (c : ℝ≥0) f, S (c • f) = c * S f := by
      intro c f
      refine le_antisymm (hsmul_le c f) ?_
      rcases eq_or_ne c 0 with rfl | hc
      · rw [NNReal.coe_zero, zero_mul]; exact hS0 _
      · have := hsmul_le c⁻¹ (c • f)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        calc (c : ℝ) * S f ≤ c * (c⁻¹ * S (c • f)) := mul_le_mul_of_nonneg_left this c.2
          _ = S (c • f) := by
            rw [← mul_assoc, ← NNReal.coe_mul, mul_inv_cancel₀ hc, NNReal.coe_one, one_mul]
    let Λ₀ : CompactlySupportedContinuousMap Y ℝ≥0 →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f => Real.toNNReal (S f)
        map_add' := fun f g => by rw [hadd, Real.toNNReal_add (hS0 f) (hS0 g)]
        map_smul' := fun c f => by
          rw [hsmul, Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe, RingHom.id_apply, smul_eq_mul] }
    refine ⟨CompactlySupportedContinuousMap.toRealPositiveLinear Λ₀, fun f hf => ?_⟩
    have hf' : f.nnrealPart.toReal = f := by
      ext y
      have hfy : 0 ≤ f y := by simpa using hf y
      simp [hfy]
    rw [← hf', CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
    exact (hle _ _ le_rfl).trans (Real.le_coe_toNNReal _)
  -- Step 2: the coordinate functionals `ψ ↦ L(ψ bᵢ)` for the standard orthonormal basis `b`.
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  let mk : CompactlySupportedContinuousMap Y ℝ → EuclideanSpace ℝ (Fin N) →
      CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) := fun ψ v =>
    ψ.compLeft ⟨fun t => t • v, continuous_id.smul continuous_const⟩
  have mk_apply : ∀ ψ v y, mk ψ v y = ψ y • v := fun ψ v y =>
    CompactlySupportedContinuousMap.compLeft_apply (by simp) ψ y
  let ℓ : EuclideanSpace ℝ (Fin N) → CompactlySupportedContinuousMap Y ℝ →ₗ[ℝ] ℝ := fun v =>
    { toFun := fun ψ => L (mk ψ v)
      map_add' := fun ψ φ => by
        rw [← map_add]
        congr 1
        exact CompactlySupportedContinuousMap.ext fun y => by simp [mk_apply, add_smul]
      map_smul' := fun c ψ => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        exact CompactlySupportedContinuousMap.ext fun y => by simp [mk_apply, smul_smul] }
  have hbound : ∀ i, ∀ f : CompactlySupportedContinuousMap Y ℝ≥0, ∃ B : ℝ,
      ∀ φ : CompactlySupportedContinuousMap Y ℝ≥0, φ ≤ f → ℓ (b i) φ.toReal ≤ B := by
    intro i f
    obtain ⟨B, hB⟩ := hL (tsupport f) f.hasCompactSupport
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖f.toReal y‖ ≤ C :=
      (map_continuous f.toReal).bounded_above_of_compact_support f.toReal.hasCompactSupport
    have hc : 0 < |C| + 1 := by positivity
    refine ⟨(|C| + 1) * B, fun φ hφ => ?_⟩
    have hφf : ∀ y, (φ y : ℝ) ≤ |C| + 1 := fun y => by
      have h1 : (φ y : ℝ) ≤ f y := NNReal.coe_le_coe.2 (hφ y)
      have h2 := hC y
      rw [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs] at h2
      linarith [le_abs_self C, le_abs_self (f y : ℝ)]
    have hnorm : ∀ y, ‖mk ((|C| + 1)⁻¹ • φ.toReal) (b i) y‖ ≤ 1 := fun y => by
      rw [mk_apply, norm_smul, hb, mul_one, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      rw [inv_mul_le_iff₀ hc, mul_one]
      exact hφf y
    have hsupp : tsupport (mk ((|C| + 1)⁻¹ • φ.toReal) (b i)) ⊆ tsupport f := by
      refine closure_mono fun y hy => ?_
      rw [Function.mem_support] at hy ⊢
      contrapose! hy
      have : φ y = 0 := le_antisymm ((hφ y).trans hy.le) zero_le
      simp [mk_apply, this]
    have h := hB _ hnorm hsupp
    change ℓ (b i) ((|C| + 1)⁻¹ • φ.toReal) ≤ B at h
    rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hc] at h
    exact h
  -- Step 3: Jordan decomposition `ℓᵢ = Λᵢ - Qᵢ` and the Riesz–Markov–Kakutani measures.
  choose Λ hΛ using fun i => key (ℓ (b i)) (hbound i)
  let Q : Fin N → CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ := fun i =>
    PositiveLinearMap.mk₀ ((Λ i).toLinearMap - ℓ (b i)) fun f hf => by
      simpa using hΛ i f hf
  have hℓ : ∀ i ψ, ℓ (b i) ψ =
      ∫ y, ψ y ∂(RealRMK.rieszMeasure (Λ i)) - ∫ y, ψ y ∂(RealRMK.rieszMeasure (Q i)) := by
    intro i ψ
    rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    change _ = _ - ((Λ i) ψ - ℓ (b i) ψ)
    ring
  -- Step 4: the reference measure `μ₀ = ∑ᵢ (μ_{Λᵢ} + μ_{Qᵢ})` and Radon–Nikodym transfer.
  let μ₀ : Measure Y := ∑ i, (RealRMK.rieszMeasure (Λ i) + RealRMK.rieszMeasure (Q i))
  have hμ₀ : ∀ s, μ₀ s = ∑ i, (RealRMK.rieszMeasure (Λ i) s + RealRMK.rieszMeasure (Q i) s) := by
    intro s
    simp only [μ₀, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_add, Pi.add_apply]
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨fun K hK => by
    rw [hμ₀]
    exact ENNReal.sum_lt_top.2 fun i _ =>
      ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  have hPle : ∀ i, RealRMK.rieszMeasure (Λ i) ≤ μ₀ := fun i => Measure.le_iff'.2 fun s => by
    rw [hμ₀]
    exact le_self_add.trans (Finset.single_le_sum
      (f := fun j => RealRMK.rieszMeasure (Λ j) s + RealRMK.rieszMeasure (Q j) s)
      (fun j _ => zero_le) (Finset.mem_univ i))
  have hQle : ∀ i, RealRMK.rieszMeasure (Q i) ≤ μ₀ := fun i => Measure.le_iff'.2 fun s => by
    rw [hμ₀]
    exact le_add_self.trans (Finset.single_le_sum
      (f := fun j => RealRMK.rieszMeasure (Λ j) s + RealRMK.rieszMeasure (Q j) s)
      (fun j _ => zero_le) (Finset.mem_univ i))
  have transfer : ∀ (μ' : Measure Y) [IsFiniteMeasureOnCompacts μ'], μ' ≤ μ₀ →
      ∀ ψ : CompactlySupportedContinuousMap Y ℝ,
        Integrable (fun y => (μ'.rnDeriv μ₀ y).toReal • ψ y) μ₀ ∧
        ∫ y, ψ y ∂μ' = ∫ y, (μ'.rnDeriv μ₀ y).toReal • ψ y ∂μ₀ := by
    intro μ' _ hle ψ
    have hwd : μ₀.withDensity (μ'.rnDeriv μ₀) = μ' := by
      have h := Measure.rnDeriv_add_singularPart μ' μ₀
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        add_zero] at h
    have hint : Integrable ψ (μ₀.withDensity (μ'.rnDeriv μ₀)) := by
      rw [hwd]
      exact (map_continuous ψ).integrable_of_hasCompactSupport ψ.hasCompactSupport
    refine ⟨(integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).1 hint, ?_⟩
    calc ∫ y, ψ y ∂μ' = ∫ y, ψ y ∂(μ₀.withDensity (μ'.rnDeriv μ₀)) := by rw [hwd]
      _ = _ := integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
          (Measure.rnDeriv_lt_top _ _) _
  -- the vector density `w = ∑ᵢ (dμ_{Λᵢ}/dμ₀ - dμ_{Qᵢ}/dμ₀) bᵢ`
  let a : Fin N → Y → ℝ := fun i y => ((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal -
    ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal
  let w : Y → EuclideanSpace ℝ (Fin N) := fun y => ∑ i, a i y • b i
  have hw : Measurable w := Finset.measurable_sum _ fun i _ =>
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).smul_const _
  -- Step 5: `L g = ∫ ⟨g, w⟩ dμ₀`.
  have hrep : ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)),
      L g = ∫ y, inner ℝ (g y) (w y) ∂μ₀ := by
    intro g
    let gc : Fin N → CompactlySupportedContinuousMap Y ℝ := fun i =>
      g.compLeft ⟨fun v => inner ℝ (b i) v, continuous_const.inner continuous_id⟩
    have gc_apply : ∀ i y, gc i y = inner ℝ (b i) (g y) := fun i y =>
      CompactlySupportedContinuousMap.compLeft_apply (by simp) g y
    have hg : g = ∑ i, mk (gc i) (b i) := by
      refine CompactlySupportedContinuousMap.ext fun y => ?_
      rw [CompactlySupportedContinuousMap.sum_apply]
      simp only [mk_apply, gc_apply]
      exact (b.sum_repr' (g y)).symm
    have hP := fun i => transfer _ (hPle i) (gc i)
    have hQ := fun i => transfer _ (hQle i) (gc i)
    calc L g = ∑ i, ℓ (b i) (gc i) := by
          conv_lhs => rw [hg]
          rw [map_sum]
          rfl
      _ = ∑ i, ∫ y, (((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal • gc i y -
            ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal • gc i y) ∂μ₀ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hℓ, (hP i).2, (hQ i).2, integral_sub (hP i).1 (hQ i).1]
      _ = ∫ y, ∑ i, (((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal • gc i y -
            ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal • gc i y) ∂μ₀ :=
          (integral_finsetSum _ fun i _ => (hP i).1.sub (hQ i).1).symm
      _ = ∫ y, inner ℝ (g y) (w y) ∂μ₀ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [w, a, inner_sum, real_inner_smul_right, gc_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [real_inner_comm]
          ring
  -- Step 6: polar normalization `m = ‖w‖ μ₀`, `ν = ‖w‖⁻¹ w`.
  have hbe : ∀ i, ‖b i‖ₑ = 1 := fun i => by
    rw [← ofReal_norm, hb i, ENNReal.ofReal_one]
  refine ⟨μ₀.withDensity fun y => ‖w y‖ₑ, fun y => ‖w y‖⁻¹ • w y, fun K hK => ?_,
    hw.norm.inv.smul hw, fun y => ?_, ?_, fun g => ?_⟩
  · calc (μ₀.withDensity fun y => ‖w y‖ₑ) K = ∫⁻ y in K, ‖w y‖ₑ ∂μ₀ :=
          withDensity_apply _ hK.isClosed.measurableSet
      _ ≤ ∫⁻ y in K, ∑ i, ((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y +
            (RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y) ∂μ₀ := by
          refine lintegral_mono fun y =>
            (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [enorm_smul, hbe i, mul_one]
          refine enorm_sub_le.trans (add_le_add ?_ ?_) <;>
            rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg] <;> exact ENNReal.ofReal_toReal_le
      _ = ∑ i, (∫⁻ y in K, (RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y ∂μ₀ +
            ∫⁻ y in K, (RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y ∂μ₀) := by
          rw [lintegral_finsetSum']
          · exact Finset.sum_congr rfl fun i _ =>
              lintegral_add_left (Measure.measurable_rnDeriv _ _) _
          · exact fun i _ => ((Measure.measurable_rnDeriv _ _).add
              (Measure.measurable_rnDeriv _ _)).aemeasurable
      _ < ∞ := ENNReal.sum_lt_top.2 fun i _ => ENNReal.add_lt_top.2
          ⟨((withDensity_apply_le _ _).trans (Measure.le_iff'.1
              (Measure.withDensity_rnDeriv_le _ _) K)).trans_lt hK.measure_lt_top,
            ((withDensity_apply_le _ _).trans (Measure.le_iff'.1
              (Measure.withDensity_rnDeriv_le _ _) K)).trans_lt hK.measure_lt_top⟩
  · show ‖‖w y‖⁻¹ • w y‖ ≤ 1
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖w y‖ 0 with h | h
    · rw [h, inv_zero, zero_mul]
      exact zero_le_one
    · rw [inv_mul_cancel₀ h]
  · refine (ae_withDensity_iff hw.enorm).2 (ae_of_all _ fun y hy => ?_)
    show ‖‖w y‖⁻¹ • w y‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (enorm_ne_zero.1 hy))]
  · rw [hrep g, integral_withDensity_eq_integral_toReal_smul hw.enorm
      (ae_of_all _ fun y => enorm_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show inner ℝ (g y) (w y) = (‖w y‖ₑ).toReal • inner ℝ (g y) (‖w y‖⁻¹ • w y)
    rw [toReal_enorm, smul_eq_mul, real_inner_smul_right]
    rcases eq_or_ne ‖w y‖ 0 with h | h
    · rw [norm_eq_zero.1 h, inner_zero_right, mul_zero, mul_zero]
    · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]
/-- Push-forward of Borel representing data from the open subspace `↥U` to `ℝ^P`: `μ = m.map ι`
and the zero extension `ν` of `ν₁` represent the same integrals against every `f ∈ CF_N(U)`. -/
theorem Submission.smr_rb_pushforward_subtype :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (m : Measure ↥U) (ν₁ : ↥U → EuclideanSpace ℝ (Fin N)),
      (∀ K : Set ↥U, IsCompact K → m K < ∞) → Measurable ν₁ → (∀ y, ‖ν₁ y‖ ≤ 1) →
      (∀ᵐ y ∂m, ‖ν₁ y‖ = 1) →
      ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U → Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧
            ∫ x, inner ℝ (f x) (ν x) ∂μ = ∫ y, inner ℝ (f ↑y) (ν₁ y) ∂m := by
  intro P N U hU m ν₁ hm hν₁ hle hae
  -- `ι = Subtype.val : ↥U → ℝ^P` is a measurable embedding since `U` is open.
  have hι : MeasurableEmbedding (Subtype.val : ↥U → Eucl P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  -- The zero extension `ν = Function.extend Subtype.val ν₁ 0` of `ν₁`.
  set ν : Eucl P → EuclideanSpace ℝ (Fin N) := Function.extend Subtype.val ν₁ 0
  have hνval : ∀ y : ↥U, ν y = ν₁ y := fun y => Subtype.val_injective.extend_apply ν₁ 0 y
  have hνout : ∀ x, x ∉ U → ν x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)
  have hνm : Measurable ν := hι.measurable_extend hν₁ measurable_zero
  have hνle : ∀ x, ‖ν x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ U
    · rw [← Subtype.coe_mk x hx, hνval]; exact hle _
    · rw [hνout x hx, norm_zero]; exact zero_le_one
  -- Compact subsets of `U` have finite `m.map ι`-measure.
  have hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → m.map Subtype.val K < ∞ := by
    intro K hK hKU
    rw [hι.map_apply]
    exact hm _ ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (hKU.trans Subtype.range_coe.symm.subset)).2 hK)
  refine ⟨m.map Subtype.val, ν, hνm, ?_, hfin, hνle, ?_, fun f hf hfc hfU => ⟨?_, ?_⟩⟩
  · rw [hι.map_apply, Subtype.preimage_coe_compl, measure_empty]
  · exact hι.ae_map_iff.2 (hae.mono fun y hy => by rw [hνval]; exact hy)
  · -- `⟨f, ν⟩` is measurable, bounded, and vanishes off the compact `tsupport f ⊆ U`.
    have hFm : Measurable fun x => inner ℝ (f x) (ν x) :=
      continuous_inner.measurable.comp (hf.measurable.prodMk hνm)
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
    have hsupp : Function.support (fun x => inner ℝ (f x) (ν x)) ⊆ tsupport f := by
      intro x hx
      by_contra h
      exact hx (by simp only [image_eq_zero_of_notMem_tsupport h, inner_zero_left])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1
      (Measure.integrableOn_of_bounded (hfin _ hfc hfU).ne hFm.aestronglyMeasurable
        (M := C) (ae_of_all _ fun x => ?_))
    calc ‖inner ℝ (f x) (ν x)‖ ≤ ‖f x‖ * ‖ν x‖ := norm_inner_le_norm _ _
      _ ≤ ‖f x‖ := mul_le_of_le_one_right (norm_nonneg _) (hνle x)
      _ ≤ C := hC x
  · -- Change of variables along the measurable embedding `ι`.
    rw [hι.integral_map]
    simp only [hνval]

/-- Riesz representation (Simon Ch. 1, 4.14) for a locally bounded functional `L` on
`CF_N(U) = {f ∈ C_c(ℝ^P, ℝ^N) : tsupport f ⊆ U}`, `U ⊆ ℝ^P` open: there are a Borel measure `μ`
on `ℝ^P` living on `U`, finite on compact subsets of `U`, and a Borel field `ν` with `‖ν‖ ≤ 1`
and `‖ν‖ = 1` `μ`-a.e., such that `L f = ∫ ⟨f, ν⟩ dμ` for every `f ∈ CF_N(U)`. -/
theorem Submission.smr_riesz_borel_euclidean :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ,
      (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        L (f + g) = L f + L g) →
      (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → L (c • f) = c * L f) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K →
          (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) →
      ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U →
          Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧
            L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
  intro P N U hU L hadd hsmul hbd
  -- Transfer `L` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`.
  obtain ⟨L', hL'bd, hL'f⟩ := Submission.smr_rb_transfer_functional P N U hU L hadd hsmul hbd
  -- `↥U` is locally compact (`U` is open), hence σ-compact (second countable); it carries the
  -- subspace Borel σ-algebra.
  have : LocallyCompactSpace ↥U := hU.locallyCompactSpace
  -- Borel Riesz representation of `L'` on `↥U`.
  obtain ⟨m, ν₁, hmK, hν₁, hν₁le, hν₁ae, hrep⟩ :=
    Submission.smr_rb_borel_riesz_sigma_compact ↥U N L' hL'bd
  -- Push the data forward to `ℝ^P`, extending `ν₁` by zero.
  obtain ⟨μ, ν, hν, hμU, hμK, hνle, hνae, hpush⟩ :=
    Submission.smr_rb_pushforward_subtype P N U hU m ν₁ hmK hν₁ hν₁le hν₁ae
  refine ⟨μ, ν, hν, hμU, hμK, hνle, hνae, fun f hf hfc hfU => ?_⟩
  obtain ⟨hint, hμm⟩ := hpush f hf hfc hfU
  obtain ⟨g, hg, hLg⟩ := hL'f f hf hfc hfU
  -- `L f = L' g = ∫ ⟨g, ν₁⟩ dm = ∫ ⟨f ∘ ι, ν₁⟩ dm = ∫ ⟨f, ν⟩ dμ`.
  refine ⟨hint, ?_⟩
  rw [hLg, hrep g, hμm]
  simp only [hg]

/-- Riesz representation of a locally bounded linear functional `L` on the continuous compactly
supported `k`-forms in `U` (Simon Ch. 6, 2.7, from Ch. 1, 4.14): `L(φ) = ∫ ⟨φ, v⟩ dμ` with
`|v(x)(α)| ≤ |α|` and, `μ`-a.e., `v(x)(α) = 1` for some `|α| ≤ 1`.  The isometry
`J : Λᵏ(ℝ^P) ≅ ℝ^N` of `Submission.smr_covector_coord_isometry` (continuous in finite dimension)
transfers `L` to `L_H(f) = L(J⁻¹ ∘ f)` on `ℝ^N`-valued functions;
`Submission.smr_riesz_borel_euclidean` gives `L_H(f) = ∫ ⟨f, ν⟩ dμ` with Borel `ν`, `‖ν‖ ≤ 1`
and `‖ν‖ = 1` `μ`-a.e.; and `v(x)(α) = ⟨ν(x), Jα⟩`, with unit witness `α = J⁻¹(ν(x))`. -/
theorem Submission.smr_riesz_continuous_forms :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → Covector (Eucl P) k) → ℝ,
      (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          L (φ + ψ) = L φ + L ψ) →
      (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → L (c • φ) = c * L φ) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ, ∀ φ : Eucl P → Covector (Eucl P) k,
        Continuous φ → tsupport φ ⊆ K → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → |L φ| ≤ B) →
      ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
        (∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → Integrable (fun x => v x (φ x)) μ ∧ L φ = ∫ x, v x (φ x) ∂μ) ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) ∧
        (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) ∧
        ∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1 := by
  intro P k U hU L hadd hsmul hbd
  -- Step 1: the coordinate isometry `J`; covectors are finite-dimensional, so `J` and `J⁻¹`
  -- are continuous, and `|J⁻¹ h| = ‖h‖`.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have : FiniteDimensional ℝ (Covector (Eucl P) k) := J.symm.finiteDimensional
  let Jc : Covector (Eucl P) k ≃L[ℝ] EuclideanSpace ℝ (Fin N) := J.toContinuousLinearEquiv
  have hJsymm : ∀ h, covectorEuclideanNorm (J.symm h) = ‖h‖ := fun h => by
    rw [hJ, J.apply_symm_apply]
  -- Step 2: `f ↦ J⁻¹ ∘ f` maps `CF_N(U)` into `CF(U)`, so `L_H(f) = L(J⁻¹ ∘ f)` is additive,
  -- homogeneous and bounded above by the bound `B` of `L` on each compact `K ⊆ U`.
  have hcont : ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f →
      Continuous (fun x => J.symm (f x)) := fun f hf => Jc.symm.continuous.comp hf
  have hcpt : ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), HasCompactSupport f →
      HasCompactSupport (fun x => J.symm (f x)) := fun f hf => hf.comp_left (map_zero J.symm)
  have htsupp : ∀ f : Eucl P → EuclideanSpace ℝ (Fin N),
      tsupport (fun x => J.symm (f x)) ⊆ tsupport f := fun f =>
    tsupport_comp_subset (map_zero J.symm) f
  -- Step 3: Riesz for `L_H`.
  obtain ⟨μ, ν, hν, hμU, hμK, hνle, hνone, hrep⟩ :=
    Submission.smr_riesz_borel_euclidean P N U hU (fun f => L (fun x => J.symm (f x)))
      (by
        intro f g hf hfc hfU hg hgc hgU
        have hfg : (fun x => J.symm ((f + g) x)) =
            (fun x => J.symm (f x)) + (fun x => J.symm (g x)) := by
          funext x
          simp
        rw [hfg]
        exact hadd _ _ (hcont f hf) (hcpt f hfc) ((htsupp f).trans hfU)
          (hcont g hg) (hcpt g hgc) ((htsupp g).trans hgU))
      (by
        intro c f hf hfc hfU
        have hcf : (fun x => J.symm ((c • f) x)) = c • (fun x => J.symm (f x)) := by
          funext x
          simp
        rw [hcf]
        exact hsmul c _ (hcont f hf) (hcpt f hfc) ((htsupp f).trans hfU))
      (by
        intro K hK hKU
        obtain ⟨B, hB⟩ := hbd K hK hKU
        refine ⟨B, fun f hf hfK hf1 => ?_⟩
        exact (le_abs_self _).trans (hB _ (hcont f hf) ((htsupp f).trans hfK)
          (fun x => (hJsymm (f x)).le.trans (hf1 x))))
  -- Step 4: the `k`-vector field `v(x)(α) = ⟨ν(x), Jα⟩`.
  let v : Eucl P → NVector (Eucl P) k := fun x =>
    (innerSL ℝ (ν x)).comp (Jc : Covector (Eucl P) k →L[ℝ] EuclideanSpace ℝ (Fin N))
  have hv : ∀ x α, v x α = inner ℝ (ν x) (J α) := fun x α => rfl
  refine ⟨μ, v, ?_, hμU, hμK, ?_, ?_, ?_⟩
  · -- Step 5: representation, via `f = J ∘ φ ∈ CF_N(U)` with `J⁻¹ ∘ f = φ`.
    intro φ hφ hφc hφU
    obtain ⟨hint, hLf⟩ := hrep (fun x => J (φ x)) (Jc.continuous.comp hφ)
      (hφc.comp_left (map_zero J)) ((tsupport_comp_subset (map_zero J) φ).trans hφU)
    have heq : (fun x => inner ℝ (J (φ x)) (ν x)) = fun x => v x (φ x) := by
      funext x
      rw [hv, real_inner_comm]
    have hLφ : (fun x => J.symm (J (φ x))) = φ := by
      funext x
      exact J.symm_apply_apply (φ x)
    rw [heq] at hint hLf
    rw [hLφ] at hLf
    exact ⟨hint, hLf⟩
  · -- (i) Cauchy–Schwarz with `‖ν(x)‖ ≤ 1`: `|v(x)(α)| ≤ ‖Jα‖ = |α|`.
    intro x α
    rw [hv, hJ]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hνle x))
  · -- (ii) `x ↦ ⟨ν(x), Jα⟩` is Borel since `ν` is.
    intro α
    exact ((continuous_id.inner continuous_const).measurable).comp hν
  · -- (iii) Where `‖ν(x)‖ = 1`, `α = J⁻¹(ν(x))` has `|α| = 1` and `v(x)(α) = ‖ν(x)‖² = 1`.
    filter_upwards [hνone] with x hx
    refine ⟨J.symm (ν x), (hJsymm (ν x)).trans_le hx.le, ?_⟩
    rw [hv, J.apply_symm_apply, real_inner_self_eq_norm_sq, hx, one_pow]
/-- **Restriction of a measure representation is a current (Simon Ch. 6, (2.9), p. 136).**  If
`⟨ω, v⟩` is `μ`-integrable for every test form `ω ∈ 𝒟ᵏ(U)`, `μ(K) < ∞` for every compact `K ⊆ U`
and `|⟨α, v(x)⟩| ≤ |α|` for all `x` and all `k`-covectors `α`, then for every set `A`,
`S(ω) = ∫_A ⟨ω, v⟩ dμ` is a current `S ∈ 𝒟ₖ(U)`.  `S` is linear because every integrand is
integrable.  With `M = #(Fin k → Fin P)`, `|α| ≤ √M ‖α‖` for the operator norm; if `ω_j → 0` in
`𝒟ᵏ(U)`, the supports lie in one compact `K ⊆ U` and `ω_j → 0` uniformly on `K`, so
`|S(ω_j)| ≤ √M μ(K) sup_K ‖ω_j‖ → 0`. -/
theorem Submission.smr_restriction_isCurrent : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → ∀ A : Set (Eucl P), ∃ S : GeometricCurrentOn U k, ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ := by
  intro P k U μ v hint hfin hv A
  -- Step 1: `|α| ≤ √M ‖α‖` for the operator norm, `M = #(Fin k → Fin P)`.
  obtain ⟨C, hC0, hcmp⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    refine ⟨Real.sqrt (Fintype.card (Fin k → Fin P)), Real.sqrt_nonneg _, fun α => ?_⟩
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          refine Finset.sum_le_sum fun I _ => ?_
          split_ifs
          · -- `|α(b_{I(0)}, …, b_{I(k-1)})| ≤ ‖α‖` since `‖b_i‖ = 1`
            have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h ⊢
            exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  -- Step 2: `S₀(ω) = ∫_A ⟨ω, v⟩ dμ` is linear, every integrand being `μ⌞A`-integrable.
  let S₀ : TestFormOn U k →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω).restrict (hint η).restrict
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  refine ⟨⟨S₀, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 3: sequential continuity.  The supports of the `ω_j` lie in a compact `K ⊆ U` and
  -- `ω_j → 0` uniformly on `K` (order `0`), while `μ(K) < ∞`.
  obtain ⟨K, hKc, hKU, hsupp, -, hunif⟩ := hconv
  have hKm : MeasurableSet K := hKc.measurableSet
  have hμK : μ K < ∞ := hfin K hKc hKU
  set c : ℝ := C * μ.real K + 1 with hc
  have hc0 : 0 < c := add_pos_of_nonneg_of_pos (mul_nonneg hC0 measureReal_nonneg) one_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j₀, hj₀⟩ :=
    (Metric.tendstoUniformlyOn_iff.mp (hunif 0) (ε / c) (div_pos hε hc0)).exists_forall_of_atTop
  refine ⟨j₀, fun j hj => ?_⟩
  -- `|⟨ω_j(x), v(x)⟩| ≤ C ε / c` on `K`, and `ω_j(x) = 0` off `K`.
  have hbound : ∀ x, ‖v x ((ωs j : DifferentialForm (Eucl P) k) x)‖ ≤
      K.indicator (fun _ => C * (ε / c)) x := by
    intro x
    by_cases hx : x ∈ K
    · have hd := hj₀ j hj x hx
      have h00 : iteratedFDeriv ℝ 0
          ((0 : TestFormOn U k) : DifferentialForm (Eucl P) k) x = 0 := by
        simp
      rw [h00, dist_zero_left, norm_iteratedFDeriv_zero] at hd
      rw [indicator_of_mem hx, Real.norm_eq_abs]
      calc |v x ((ωs j : DifferentialForm (Eucl P) k) x)|
          ≤ covectorEuclideanNorm ((ωs j : DifferentialForm (Eucl P) k) x) := hv x _
        _ ≤ C * ‖(ωs j : DifferentialForm (Eucl P) k) x‖ := hcmp _
        _ ≤ C * (ε / c) := mul_le_mul_of_nonneg_left hd.le hC0
    · have hz : (ωs j : DifferentialForm (Eucl P) k) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h)
      rw [indicator_of_notMem hx, hz, map_zero, norm_zero]
  have hgi : Integrable (K.indicator fun _ => C * (ε / c)) (μ.restrict A) :=
    (integrable_indicator_iff hKm).mpr
      (integrableOn_const ((Measure.restrict_apply_le A K).trans_lt hμK).ne)
  have hI := norm_integral_le_of_norm_le hgi (Eventually.of_forall hbound)
  rw [integral_indicator_const _ hKm, smul_eq_mul] at hI
  have hAK : (μ.restrict A).real K ≤ μ.real K :=
    ENNReal.toReal_mono hμK.ne (Measure.restrict_apply_le A K)
  rw [dist_zero_right]
  calc ‖S₀ (ωs j)‖ ≤ (μ.restrict A).real K * (C * (ε / c)) := hI
    _ ≤ μ.real K * (C * (ε / c)) :=
        mul_le_mul_of_nonneg_right hAK (mul_nonneg hC0 (div_pos hε hc0).le)
    _ = C * μ.real K * ε / c := by ring
    _ < ε := by
        rw [div_lt_iff₀ hc0, hc]
        nlinarith

/-- Simon Ch. 6, 2.8–2.9 (pp. 136–137), the step `μ(W ∩ A) ≤ M_W(T ⌞ A)` of the mass formula
for a restriction: continuous unit forms supported in an open `W ⊆ U` detect `μ(W ∩ A)`.  Write
`v(x)(α) = ⟨Jα, u(x)⟩` for an isometry `J` of `(Λᵏ, |·|)` onto `ℝ^N`, so `‖u‖ ≤ 1` and `‖u‖ = 1`
`μ`-a.e.  Take a compact Lusin set `C ⊆ W ∩ A ∩ {‖u‖ = 1}` of `u` with `c < μ(C)`, a continuous
extension `w` of `u|C` with `‖w‖ ≤ 1` (Tietze) and a cutoff `ψ ∈ [0, 1]`, `ψ = 1` on `C`, with
`tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c` (Urysohn).  Then `φ = J⁻¹(ψ w)` has `|φ| ≤ 1`,
and `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C` and `0` off `support ψ`, so `∫_A ⟨φ, v⟩ dμ > c`. -/
theorem Submission.smr_exists_unit_form_gt : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) → (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < μ (W ∩ A) → ∃ φ : Eucl P → Covector (Eucl P) k, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ W ∧ (∀ x, covectorEuclideanNorm (φ x) ≤ 1) ∧ c < ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) := by
  intro P k U μ v hμK hv hvm hunit A hA W hW hWU c hc
  -- Coordinates `u` of `v` in an isometric chart `J`: `v(x)(α) = ⟨Jα, u(x)⟩`, `‖u‖ = 1` a.e.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  obtain ⟨u, hum, hu1, hu_ae, hvu⟩ :=
    Submission.smr_ufd_unit_coord_field P k N μ v J hJ hv hvm hunit
  -- `{‖u‖ = 1}` is conull, so it does not change `μ(W ∩ A)`; take a compact Lusin set `C` of `u`
  -- inside `W ∩ A ∩ {‖u‖ = 1}` with `c < μ(C)`.
  have hWAG : μ (W ∩ (A ∩ {x | ‖u x‖ = 1})) = μ (W ∩ A) := by
    rw [← Set.inter_assoc]
    exact measure_inter_conull (mem_ae_iff.1 hu_ae)
  obtain ⟨C, hCc, hCsub, hcC, huC⟩ := Submission.smr_ufd_compact_lusin_set P N U μ u hμK hum
    (A ∩ {x | ‖u x‖ = 1}) (hA.inter (measurableSet_eq_fun hum.norm measurable_const)) W hW hWU c
    (by rw [hWAG]; exact hc)
  have hCW : C ⊆ W := hCsub.trans Set.inter_subset_left
  -- Tietze: a continuous `w` with `‖w‖ ≤ 1` and `w = u` on `C`.
  obtain ⟨w, hwc, hw1, hwu⟩ :=
    Submission.smr_ufd_ball_tietze P N C u hCc.isClosed huC fun x _ => hu1 x
  -- Urysohn: `ψ ∈ [0, 1]`, `ψ = 1` on `C`, `tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c`.
  obtain ⟨ψ, hψc, hψcs, hψW, hψ01, hψC, hψS⟩ := Submission.smr_ufd_small_cutoff P U μ hμK C W hCc
    hW hCW hWU (μ C - c) (tsub_pos_of_lt hcC).ne'
  have hψw : ∀ x, ‖ψ x • w x‖ ≤ 1 := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (hψ01 x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hψ01 x).2).trans (hw1 x)
  -- The form `φ = J⁻¹(ψ w)`; `J⁻¹` is continuous since `ℝ^N` is finite-dimensional.
  refine ⟨fun x => J.symm (ψ x • w x),
    (LinearMap.continuous_of_finiteDimensional J.symm.toLinearMap).comp (hψc.smul hwc),
    (hψcs.smul_right (f' := w)).comp_left (map_zero J.symm),
    (tsupport_comp_subset (map_zero J.symm) _).trans ((tsupport_smul_subset_left ψ w).trans hψW),
    fun x => ?_, ?_⟩
  · -- `|φ(x)| = ‖ψ(x) w(x)‖ ≤ 1`.
    change covectorEuclideanNorm (J.symm (ψ x • w x)) ≤ 1
    rw [hJ, LinearEquiv.apply_symm_apply]
    exact hψw x
  · -- `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C ⊆ {‖u‖ = 1}` and `0` off `support ψ`.
    have hg : ∀ x, v x (J.symm (ψ x • w x)) = inner ℝ (ψ x • w x) (u x) := fun x => by
      rw [hvu, LinearEquiv.apply_symm_apply]
    simp only [hg]
    refine Submission.smr_ufd_integral_lower_bound P μ (fun x => inner ℝ (ψ x • w x) (u x)) A C
      (Function.support ψ) c hA hCc.isClosed.measurableSet hψc.isOpen_support.measurableSet
      (fun x hx => (hCsub hx).2.1)
      ((measure_mono (subset_tsupport ψ)).trans_lt (hμK (tsupport ψ) hψcs (hψW.trans hWU)))
      ((continuous_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin N))).measurable.comp
        ((hψc.smul hwc).measurable.prodMk hum))
      (fun x => (abs_real_inner_le_norm _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hψw x)).trans (hu1 x)))
      (fun x hx => ?_) (fun x hx => ?_) (lt_tsub_iff_left.1 hψS)
    · have hx1 : ‖u x‖ = 1 := (hCsub hx).2.2
      simp only [hψC x hx, one_smul, hwu x hx, real_inner_self_eq_norm_sq, hx1, one_pow]
    · simp only [Function.notMem_support.1 hx, zero_smul, inner_zero_left]

/-- **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6 of `slicing_mass_representation`.  Let `μ` be
finite on compact subsets of `U`, `|⟨α, v(x)⟩| ≤ |α|`, `x ↦ ⟨α, v(x)⟩` Borel, and, `μ`-a.e.,
`⟨α, v(x)⟩ = 1` for some `|α| ≤ 1`.  If `S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, `A`
Borel, then `M_W(S) = μ(W ∩ A)` for every open `W ⊆ U`.

`≤`: an admissible `ω` has `‖⟨ω(x), v(x)⟩‖ ≤ 1_{spt ω}(x)`, so
`S(ω) ≤ ∫_A ‖⟨ω, v⟩‖ dμ ≤ μ(spt ω ∩ A) ≤ μ(W ∩ A)`.  `≥`: for `c < μ(W ∩ A)`,
`smr_exists_unit_form_gt` gives a continuous compactly supported `φ` with `spt φ ⊆ W`, `|φ| ≤ 1`
and `c < ∫_A ⟨φ, v⟩ dμ`, and `smr_ofReal_integral_le_massOn` gives `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)`. -/
theorem Submission.smr_restriction_massOn_eq : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) → (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ S : GeometricCurrentOn U k, (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → S.massOn W = μ (W ∩ A) := by
  intro P k U μ v hint hfin hv hmeas hae A hA S hS W hW hWU
  apply le_antisymm
  · -- Step 1 (`≤`): `ofReal (S ω) ≤ μ(W ∩ A)` for every admissible `ω`; take the supremum.
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    have hωm : MeasurableSet (tsupport (ω : DifferentialForm (Eucl P) k)) :=
      (isClosed_tsupport _).measurableSet
    -- Off `spt ω` the form vanishes; on it `|⟨ω(x), v(x)⟩| ≤ |ω(x)| ≤ 1`.
    have hpt : ∀ x, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ≤
        (tsupport (ω : DifferentialForm (Eucl P) k)).indicator 1 x := by
      intro x
      by_cases hx : x ∈ tsupport (ω : DifferentialForm (Eucl P) k)
      · rw [indicator_of_mem hx, Pi.one_apply, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
        exact (hv x _).trans (hω.2 x)
      · refine le_of_eq ?_
        rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
    calc ENNReal.ofReal (S ω)
        = ENNReal.ofReal (∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) := by
          rw [hS]
      _ ≤ ‖∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ‖ₑ := Real.ofReal_le_enorm _
      _ ≤ ∫⁻ x in A, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in A, (tsupport (ω : DifferentialForm (Eucl P) k)).indicator 1 x ∂μ :=
          lintegral_mono hpt
      _ = μ (tsupport (ω : DifferentialForm (Eucl P) k) ∩ A) := by
          rw [lintegral_indicator_one hωm, Measure.restrict_apply hωm]
      _ ≤ μ (W ∩ A) := measure_mono (inter_subset_inter_left _ hω.1)
  · -- Step 2 (`≥`): each `c < μ(W ∩ A)` is below `ofReal (∫_A ⟨φ, v⟩ dμ) ≤ M_W(S)` for a
    -- continuous unit form `φ` supported in `W`.
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨φ, hφc, hφs, hφW, hφ1, hcφ⟩ :=
      Submission.smr_exists_unit_form_gt P k U μ v hfin hv hmeas hae A hA W hW hWU c hc
    exact hcφ.trans_le (Submission.smr_ofReal_integral_le_massOn P k U μ v hint hfin hv A S hS
      W hW hWU φ hφc hφs hφW hφ1)

/-- **Simon Ch. 6, 2.7–2.9 (pp. 136–137).**  A current `X ∈ 𝒟ₖ(U)` with `M_W(X) < ∞` for every
`W ⊂⊂ U` is represented as `X(ω) = ∫ ⟨ω, v⟩ dμ` (2.7) by a Borel measure `μ` living on `U`,
finite on compact subsets of `U`, with `|⟨α, v(x)⟩| ≤ |α|`; the restrictions
`(X ⌞ A)(ω) = ∫_A ⟨ω, v⟩ dμ` to Borel sets `A` are currents (2.9) with
`M_W(X ⌞ A) = μ(W ∩ A)` for every open `W ⊆ U` (2.8).  `X` extends to continuous compactly
supported forms in `U` (`smr_exists_continuous_extension`); the Riesz representation of the
extension (`smr_riesz_continuous_forms`) gives `(μ, v)`, and the restriction statements are
`smr_restriction_isCurrent` and `smr_restriction_massOn_eq`. -/
theorem Submission.slicing_mass_representation :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) →
      ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
        IsMeasureRepresentation X μ v ∧ μ Uᶜ = 0 ∧
        (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) ∧
        (∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U k,
          ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) ∧
        ∀ A : Set (Eucl P), MeasurableSet A → ∀ S : GeometricCurrentOn U k,
          (∀ ω : TestFormOn U k,
            S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) →
          ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → S.massOn W = μ (W ∩ A) := by
  intro P k U hU X hX
  -- Step 2: `X` extends to a linear functional `L` on continuous compactly supported forms in
  -- `U`, bounded on forms with `|φ| ≤ 1` supported in a fixed compact subset of `U`.
  obtain ⟨L, hLX, hLadd, hLsmul, hLbd⟩ :=
    Submission.smr_exists_continuous_extension P k U hU X hX
  -- Steps 3–4: Riesz gives `L φ = ∫ ⟨φ, v⟩ dμ` with (b), (c), (d), Borel coefficients of `v`
  -- and, `μ`-a.e., a covector `α` with `|α| ≤ 1` and `⟨α, v⟩ = 1`.
  obtain ⟨μ, v, hLrep, hμU, hμK, hv, hvmeas, hvunit⟩ :=
    Submission.smr_riesz_continuous_forms P k U hU L hLadd hLsmul hLbd
  -- (a): a test form is a continuous compactly supported form in `U`, on which `L = X`.
  have hrep : IsMeasureRepresentation X μ v := by
    intro ω
    obtain ⟨hint, hL⟩ := hLrep (ω : DifferentialForm (Eucl P) k)
      (ContDiff.continuous ω.property.1.1) ω.property.1.2 ω.property.2
    exact ⟨hint, (hLX ω).symm.trans hL⟩
  have hint : ∀ ω : TestFormOn U k,
      Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ := fun ω => (hrep ω).1
  -- (e): restrictions are currents (Step 5); (f): their mass on open `W ⊆ U` is `μ (W ∩ A)`
  -- (Step 6).
  exact ⟨μ, v, hrep, hμU, hμK, hv,
    fun A _ => Submission.smr_restriction_isCurrent P k U μ v hint hμK hv A,
    fun A hA S hS W hW hWU => Submission.smr_restriction_massOn_eq P k U μ v hint hμK hv hvmeas
      hvunit A hA S hS W hW hWU⟩
/-- **Local integrability from test forms (Simon Ch. 6, (2.7), p. 136).**  If `⟨ω, v⟩` is
`μ`-integrable for every test form `ω ∈ 𝒟ᵏ(U)`, then `⟨c, v⟩` is `μ`-integrable on every compact
`L ⊆ U`, for every constant `k`-covector `c`.  Some closed thickening `cthickening δ L` lies in
`U`; the smooth Urysohn lemma gives a smooth `χ` with values in `[0, 1]`, `support χ =
thickening δ L` and `χ = 1` exactly on `L`.  Then `ω = χ c` is a test form on `U`, so
`χ ⟨c, v⟩ = ⟨ω, v⟩` is `μ`-integrable, and it agrees with `⟨c, v⟩` on the closed set `L`. -/
theorem Submission.slicing_ru_integrableOn_apply : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → ∀ L : Set (Eucl P), IsCompact L → L ⊆ U → ∀ c : Covector (Eucl P) k, IntegrableOn (fun x => v x c) L μ := by
  intro P k U hU μ v hv L hL hLU c
  -- Step 1: room around `L`, `cthickening δ L ⊆ U`.
  obtain ⟨δ, hδ, hδU⟩ := hL.exists_cthickening_subset_open hU hLU
  -- Step 2: a smooth cutoff `χ` with `support χ = thickening δ L` and `χ = 1` exactly on `L`.
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := δ) (E := L)) hL.isClosed (self_subset_thickening hδ L)
  have hχt : tsupport χ ⊆ cthickening δ L := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening δ L
  -- Step 3: `ω = χ c` is a test form on `U`.
  let ω : DifferentialForm (Eucl P) k := fun x => χ x • c
  have hωt : tsupport ω ⊆ tsupport χ := tsupport_smul_subset_left χ fun _ => c
  have hω : ω ∈ TestFormOn U k := by
    refine ⟨⟨hχ.smul contDiff_const, ?_⟩, hωt.trans (hχt.trans hδU)⟩
    exact hL.cthickening.of_isClosed_subset (isClosed_tsupport _) (hωt.trans hχt)
  -- Step 4: by linearity of `v x`, `x ↦ χ x * v x c` is `μ`-integrable.
  have h4 : Integrable (fun x => χ x * v x c) μ := by
    simpa [ω, map_smul, smul_eq_mul] using hv ⟨ω, hω⟩
  -- Step 5: `χ = 1` on the closed set `L`.
  refine (h4.integrableOn (s := L)).congr_fun (fun x hx => ?_) hL.isClosed.measurableSet
  simp [(hχ1 x).1 hx]
/-- **Step 4 of the uniqueness of the representation (2.7), Simon Ch. 6 (p. 136).**  If `g₁ μ₁`
and `g₂ μ₂` (`gᵢ` `μᵢ`-integrable) agree on smooth compactly supported functions `φ` with
`tsupport φ ⊆ O`, `O` open, they agree on continuous compactly supported functions `φ` with
`tsupport φ ⊆ O`.  The approximants are `χ (ψ ⋆ φ)`: `ψ ⋆ φ` is the convolution of `φ` with a
normalized smooth bump `ψ` supported in a ball whose radius is a uniform-continuity modulus of
`φ`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to `1` exactly on `tsupport φ`,
whose support `V` has compact closure in `O`.  Dominated convergence passes to the limit. -/
theorem Submission.slicing_ru_smooth_to_continuous : ∀ (P : ℕ) (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), Integrable g₁ μ₁ → Integrable g₂ μ₂ → ∀ O : Set (Eucl P), IsOpen O → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ O → ∫ x, φ x * g₁ x ∂μ₁ = ∫ x, φ x * g₂ x ∂μ₂) → ∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → ∫ x, φ x * g₁ x ∂μ₁ = ∫ x, φ x * g₂ x ∂μ₂ := by
  intro P μ₁ μ₂ g₁ g₂ hg₁ hg₂ O hO hsmooth φ hφ hφc hφO
  -- Step 1: for every `ε > 0` there is a smooth `η` with compact support, `tsupport η ⊆ O` and
  -- `|η - φ| ≤ ε`.
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ η : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
      HasCompactSupport η ∧ tsupport η ⊆ O ∧ ∀ x, dist (η x) (φ x) ≤ ε := by
    intro ε hε
    -- An open `V` with `tsupport φ ⊆ V` and `closure V ⊆ O` compact, and a smooth cutoff
    -- `χ : ℝ^P → [0, 1]` with `support χ = V` and `χ = 1` exactly on `tsupport φ`.
    obtain ⟨V, hVo, hKV, hVO, hVc⟩ :=
      exists_open_between_and_isCompact_closure hφc.isCompact hO hφO
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo (isClosed_tsupport φ) hKV
    -- Mollification: `φ` is uniformly continuous with modulus `δ` at accuracy `ε`; `ψ` is a smooth
    -- bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `f = ψ ⋆ φ` is smooth and
    -- `dist (f x) (φ x) ≤ ε`.
    obtain ⟨δ, hδ, hφδ⟩ :=
      Metric.uniformContinuous_iff.mp (hφc.uniformContinuous_of_continuous hφ) ε hε
    obtain ⟨ψ₀, hψ₀s, hψ₀c, hψ₀d, hψ₀r, hψ₀0⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
    have hψ₀nn : ∀ y, 0 ≤ ψ₀ y := fun y => (hψ₀r (mem_range_self y)).1
    have hψ₀int : 0 < ∫ y, ψ₀ y :=
      hψ₀d.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hψ₀c (fun y => hψ₀nn y)
        (hψ₀0.symm ▸ one_ne_zero : ψ₀ 0 ≠ 0)
    set ψ : Eucl P → ℝ := fun y => (∫ z, ψ₀ z)⁻¹ * ψ₀ y with hψ_def
    have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hψ₀d
    have hψc : HasCompactSupport ψ := hψ₀c.mul_left
    have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hψ₀int.le) (hψ₀nn y)
    have hψs : Function.support ψ ⊆ ball 0 δ :=
      (Function.support_mul_subset_right _ _).trans ((subset_tsupport ψ₀).trans hψ₀s)
    have hψ1 : ∫ y, ψ y = 1 := by
      rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hψ₀int.ne']
    obtain ⟨f, hf, hfd⟩ : ∃ f : Eucl P → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ ∀ x, dist (f x) (φ x) ≤ ε :=
      ⟨convolution ψ φ (ContinuousLinearMap.lsmul ℝ ℝ) volume,
        hψc.contDiff_convolution_left _ hψd hφ.locallyIntegrable,
        fun x => dist_convolution_le hε.le hψs hψnn hψ1 hφ.aestronglyMeasurable
          fun y hy => (hφδ (mem_ball.mp hy)).le⟩
    -- `η = χ f` is smooth with `tsupport η ⊆ closure V ⊆ O`; on `tsupport φ`, `η = f`, and off
    -- it, `φ = 0` and `0 ≤ χ ≤ 1`.
    have hηs : tsupport (fun x => χ x * f x) ⊆ closure V := by
      refine tsupport_mul_subset_left.trans ?_
      rw [tsupport, hχs]
    refine ⟨fun x => χ x * f x, hχ.mul hf, hVc.of_isClosed_subset (isClosed_tsupport _) hηs,
      hηs.trans hVO, fun x => ?_⟩
    show dist (χ x * f x) (φ x) ≤ ε
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1 x).1 hx, one_mul]
      exact hfd x
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hfx : |f x| ≤ ε := by simpa [h0, Real.dist_eq] using hfd x
      rw [h0, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hχx.2).trans hfx
  -- Step 2: approximants `η n` with `|η n - φ| ≤ 1 / (n + 1)`, and a bound `|φ| ≤ M`.
  choose η hηd hηc hηO hηφ using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  -- Step 3: dominated convergence with bound `(M + 1) |g|`: `∫ η n g dμ → ∫ φ g dμ`.
  have hlim : ∀ (μ : Measure (Eucl P)) (g : Eucl P → ℝ), Integrable g μ →
      Tendsto (fun n => ∫ x, η n x * g x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)) := by
    intro μ g hg
    refine tendsto_integral_of_dominated_convergence (fun x => (M + 1) * ‖g x‖)
      (fun n => (hηd n).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (hg.norm.const_mul _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h1 : dist (η n x) (φ x) ≤ 1 := (hηφ n x).trans <| by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc ‖η n x‖ ≤ ‖φ x‖ + ‖η n x - φ x‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ M + 1 := add_le_add (hM x) (by rwa [← dist_eq_norm])
    · refine Tendsto.mul_const _ (tendsto_iff_dist_tendsto_zero.mpr ?_)
      exact squeeze_zero (fun n => dist_nonneg) (fun n => hηφ n x)
        tendsto_one_div_add_atTop_nhds_zero_nat
  -- Step 4: the two sequences coincide termwise by the smooth hypothesis.
  exact tendsto_nhds_unique
    ((hlim μ₁ g₁ hg₁).congr fun n => hsmooth _ (hηd n) (hηc n) (hηO n)) (hlim μ₂ g₂ hg₂)
/-- Simon Ch. 6, (2.7)–(2.9): uniqueness step for representations of currents.  If `g₁ μ₁` and
`g₂ μ₂` agree on continuous compactly supported functions with support in the open set `O`, then
they agree on bounded Borel functions vanishing off `O`.  With `g⁺ = max g 0`, `g⁻ = max (-g) 0`,
the finite measures `m₁ = g₁⁺ μ₁ + g₂⁻ μ₂`, `m₂ = g₁⁻ μ₁ + g₂⁺ μ₂` satisfy
`∫ f dm₁ - ∫ f dm₂ = ∫ f g₁ dμ₁ - ∫ f g₂ dμ₂` for bounded measurable `f`, so they agree on
`C_c(O)`.  Urysohn functions and inner regularity give `m₁ V = m₂ V` for open `V ⊆ O`; by the
π–λ theorem `m₁ ⌞ O = m₂ ⌞ O`, and the claim follows. -/
theorem Submission.slicing_ru_continuous_to_bounded : ∀ (P : ℕ) (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), Integrable g₁ μ₁ → Integrable g₂ μ₂ → ∀ O : Set (Eucl P), IsOpen O → (∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → ∫ x, φ x * g₁ x ∂μ₁ = ∫ x, φ x * g₂ x ∂μ₂) → ∀ h : Eucl P → ℝ, Measurable h → (∃ C : ℝ, ∀ x, |h x| ≤ C) → (∀ x, x ∉ O → h x = 0) → ∫ x, h x * g₁ x ∂μ₁ = ∫ x, h x * g₂ x ∂μ₂ := by
  intro P μ₁ μ₂ g₁ g₂ hg₁ hg₂ O hO H h hh ⟨C, hC⟩ hhO
  -- Step 1: `∫ f d(g⁺ μ) - ∫ f d(g⁻ μ) = ∫ f g dμ` for bounded measurable `f`.
  have split : ∀ (μ : Measure (Eucl P)) (g : Eucl P → ℝ), Integrable g μ →
      ∀ f : Eucl P → ℝ, Measurable f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (g x)) -
          ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (-g x)) = ∫ x, f x * g x ∂μ := by
    intro μ g hg f hf D hD
    have hb : ∀ {ρ : Measure (Eucl P)}, ∀ᵐ x ∂ρ, ‖f x‖ ≤ D :=
      Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hD x
    have hmax : ∀ t : ℝ, ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
      intro t
      rcases le_total t 0 with ht | ht
      · rw [max_eq_right ht, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos ht]
      · rw [max_eq_left ht]
    have hpos : ∀ u : Eucl P → ℝ, Integrable u μ →
        ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) = ∫ x, max (u x) 0 * f x ∂μ := by
      intro u hu
      have : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (u x)) :=
        isFiniteMeasure_withDensity_ofReal hu.2
      have hρ : AEMeasurable (fun x => ENNReal.ofReal (u x)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable hu.aemeasurable
      have e₁ : ∫⁻ x, ENNReal.ofReal (f x) ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) =
          ∫⁻ x, ENNReal.ofReal (max (u x) 0 * f x) ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul₀ hρ hf.ennreal_ofReal.aemeasurable]
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, ENNReal.ofReal_mul (le_max_right _ _), hmax]
      have e₂ : ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) =
          ∫⁻ x, ENNReal.ofReal (-(max (u x) 0 * f x)) ∂μ := by
        have hnf : AEMeasurable (fun x => ENNReal.ofReal (-f x)) μ :=
          hf.neg.ennreal_ofReal.aemeasurable
        rw [lintegral_withDensity_eq_lintegral_mul₀ hρ hnf]
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, ← mul_neg, ENNReal.ofReal_mul (le_max_right _ _), hmax]
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
          (Integrable.of_bound hf.aestronglyMeasurable D hb),
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part
          (hu.pos_part.mul_bdd hf.aestronglyMeasurable hb), e₁, e₂]
    rw [hpos g hg, hpos (fun x => -g x) hg.neg,
      ← integral_sub (hg.pos_part.mul_bdd hf.aestronglyMeasurable hb)
        (hg.neg_part.mul_bdd hf.aestronglyMeasurable hb)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := max_zero_sub_max_neg_zero_eq_self (g x)
    simp only
    linear_combination (f x) * this
  -- Step 2: the finite measures `m₁ = g₁⁺ μ₁ + g₂⁻ μ₂` and `m₂ = g₁⁻ μ₁ + g₂⁺ μ₂`.
  set m₁ : Measure (Eucl P) := (μ₁.withDensity fun x => ENNReal.ofReal (g₁ x)) +
    μ₂.withDensity fun x => ENNReal.ofReal (-g₂ x) with hm₁
  set m₂ : Measure (Eucl P) := (μ₁.withDensity fun x => ENNReal.ofReal (-g₁ x)) +
    μ₂.withDensity fun x => ENNReal.ofReal (g₂ x) with hm₂
  have : IsFiniteMeasure (μ₁.withDensity fun x => ENNReal.ofReal (g₁ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₁.2
  have : IsFiniteMeasure (μ₁.withDensity fun x => ENNReal.ofReal (-g₁ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₁.neg.2
  have : IsFiniteMeasure (μ₂.withDensity fun x => ENNReal.ofReal (g₂ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₂.2
  have : IsFiniteMeasure (μ₂.withDensity fun x => ENNReal.ofReal (-g₂ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₂.neg.2
  have : IsFiniteMeasure m₁ := by rw [hm₁]; infer_instance
  have : IsFiniteMeasure m₂ := by rw [hm₂]; infer_instance
  -- (★) `∫ f dm₁ - ∫ f dm₂ = ∫ f g₁ dμ₁ - ∫ f g₂ dμ₂` for bounded measurable `f`.
  have star : ∀ f : Eucl P → ℝ, Measurable f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
      ∫ x, f x ∂m₁ - ∫ x, f x ∂m₂ = ∫ x, f x * g₁ x ∂μ₁ - ∫ x, f x * g₂ x ∂μ₂ := by
    intro f hf D hD
    have hb : ∀ {ρ : Measure (Eucl P)}, ∀ᵐ x ∂ρ, ‖f x‖ ≤ D :=
      Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hD x
    have i : ∀ (ρ : Measure (Eucl P)) [IsFiniteMeasure ρ], Integrable f ρ :=
      fun ρ _ => Integrable.of_bound hf.aestronglyMeasurable D hb
    rw [hm₁, hm₂, integral_add_measure (i _) (i _), integral_add_measure (i _) (i _),
      ← split μ₁ g₁ hg₁ f hf D hD, ← split μ₂ g₂ hg₂ f hf D hD]
    ring
  -- Step 3: `m₁` and `m₂` agree on `C_c(O)`.
  have agree : ∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O →
      ∫ x, φ x ∂m₁ = ∫ x, φ x ∂m₂ := by
    intro φ hφ hφc hφO
    obtain ⟨D, hD⟩ := hφ.bounded_above_of_compact_support hφc
    have := star φ hφ.measurable D fun x => by simpa [Real.norm_eq_abs] using hD x
    rw [H φ hφ hφc hφO, sub_self, sub_eq_zero] at this
    exact this
  -- Step 4: finite measures agreeing on `C_c(O)` agree on open subsets of `O`
  -- (inner regularity and Urysohn's lemma).
  have le_of_agree : ∀ (ρ₁ ρ₂ : Measure (Eucl P)) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂],
      (∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O →
        ∫ x, φ x ∂ρ₁ = ∫ x, φ x ∂ρ₂) →
      ∀ V : Set (Eucl P), IsOpen V → V ⊆ O → ρ₁ V ≤ ρ₂ V := by
    intro ρ₁ ρ₂ _ _ hρ V hV hVO
    rw [hV.measure_eq_iSup_isCompact ρ₁]
    refine iSup_le fun K => iSup_le fun hKV => iSup_le fun hK => ?_
    obtain ⟨φ, hφK, hφc, hφV, hφ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
    have hφi : ∀ (ρ : Measure (Eucl P)) [IsFiniteMeasure ρ], Integrable φ ρ := by
      intro ρ _
      refine Integrable.of_bound φ.continuous.aestronglyMeasurable 1
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hφ01 x).1], (hφ01 x).2⟩
    have h₁ : ρ₁.real K ≤ ∫ x, φ x ∂ρ₁ := by
      rw [← integral_indicator_one hK.measurableSet]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator hK.measurableSet) (hφi ρ₁)
        fun x => ?_
      by_cases hx : x ∈ K
      · simp [Set.indicator_of_mem hx, hφK hx]
      · simp [Set.indicator_of_notMem hx, (hφ01 x).1]
    have h₂ : ∫ x, φ x ∂ρ₂ ≤ ρ₂.real V := by
      rw [← integral_indicator_one hV.measurableSet]
      refine integral_mono (hφi ρ₂) ((integrable_const (1 : ℝ)).indicator hV.measurableSet)
        fun x => ?_
      by_cases hx : x ∈ V
      · simp [Set.indicator_of_mem hx, (hφ01 x).2]
      · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => hx (hφV hx')
        simp [Set.indicator_of_notMem hx, this]
    have := h₁.trans ((hρ φ φ.continuous hφc (hφV.trans hVO)).le.trans h₂)
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  have eq_open : ∀ V : Set (Eucl P), IsOpen V → V ⊆ O → m₁ V = m₂ V := fun V hV hVO =>
    le_antisymm (le_of_agree m₁ m₂ agree V hV hVO)
      (le_of_agree m₂ m₁ (fun φ hφ hφc hφO => (agree φ hφ hφc hφO).symm) V hV hVO)
  -- Step 5: π–λ: `m₁ ⌞ O = m₂ ⌞ O`.
  have hrestr : m₁.restrict O = m₂.restrict O := by
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · have hs' : IsOpen s := hs
      rw [Measure.restrict_apply hs'.measurableSet, Measure.restrict_apply hs'.measurableSet]
      exact eq_open _ (hs'.inter hO) inter_subset_right
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact eq_open O hO subset_rfl
  -- Step 6: conclusion.
  have hint : ∫ x, h x ∂m₁ = ∫ x, h x ∂m₂ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := m₁) hhO,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := m₂) hhO, hrestr]
  have := star h hh C hC
  rw [hint, sub_self] at this
  linarith
/-- **Coordinate expansion of covectors, Simon Ch. 6, (1.1)–(1.2) (pp. 131–132).**  Every
`k`-covector `α` on `ℝ^P` is `∑_{β ∈ I(k,P)} α(e_{β(0)}, …, e_{β(k-1)}) dx^β`.  By (1.1),
`dx^β(e_γ) = δ_{βγ}` for increasing `β, γ` (the determinant of the identity matrix if `β = γ`,
of a matrix with a zero column otherwise), so both sides agree on increasing basis tuples;
sorting and the sign rule for alternating maps extend this to all injective basis tuples, and an
alternating map is determined by its values on those. -/
theorem Submission.slicing_ru_covector_expansion : ∀ (P k : ℕ) (α : Covector (Eucl P) k), α = ∑ β : SimonMultiIndex k P, euclideanCovectorCoordinate α β • wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) := by
  intro P k α
  classical
  set e : (Fin k → Fin P) → Fin k → Eucl P := fun v j => EuclideanSpace.single (v j) 1
  set R : Covector (Eucl P) k := ∑ β : SimonMultiIndex k P,
    euclideanCovectorCoordinate α β • wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) with hR
  -- Steps 1–2: Kronecker property `dx^β(e_γ) = δ_{βγ}` on increasing multi-indices.
  have hK : ∀ β γ : SimonMultiIndex k P,
      wedgeCovectors k (fun j => EuclideanSpace.proj (β j)) (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · subst hβγ
      convert Matrix.det_one (n := Fin k) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · -- Some `γ j₀` lies outside `range β`: otherwise the ranges coincide (equal cardinality),
      -- and increasing maps with equal ranges are equal.
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, ∀ i, γ j₀ ≠ β i := by
        by_contra! h
        apply hβγ
        symm
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range γ ⊆ Set.range β := by
          rintro _ ⟨j, rfl⟩
          obtain ⟨i, hi⟩ := h j
          exact ⟨i, hi.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range β)
        rw [Set.ncard_range_of_injective β.injective, Set.ncard_range_of_injective γ.injective]
      exact Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => by
        simp [e, PiLp.single_apply, (hj₀ i).symm]
  -- Step 3: agreement on increasing basis tuples.
  have h1 : ∀ γ : SimonMultiIndex k P, R (e γ) = α (e γ) := by
    intro γ
    rw [hR, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  -- Step 4: agreement on injective basis tuples, by sorting and the sign rule.
  have h2 : ∀ v : Fin k → Fin P, Function.Injective v → R (e v) = α (e v) := by
    intro v hv
    have hsm : StrictMono (v ∘ Tuple.sort v) :=
      (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
    have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
    have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
    rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
      ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
      AlternatingMap.map_perm] at hγ
    exact smul_left_cancel _ hγ
  -- Step 5: an alternating map is determined by its values on injective basis tuples.
  symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  exact h2 v hv

/-- Simon Ch. 6, 2.7–2.9 (uniqueness of the vector measure `v μ` of a representation (2.7)),
localized to an open `W`: if two representations agree on the test forms supported in `W`, their
restrictions to every Borel set `A` agree on those forms. -/
theorem Submission.slicing_representation_unique :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (μ₁ μ₂ : Measure (Eucl P))
      (v₁ v₂ : Eucl P → NVector (Eucl P) k),
      (∀ ω : TestFormOn U k,
        Integrable (fun x => v₁ x ((ω : DifferentialForm (Eucl P) k) x)) μ₁) →
      (∀ ω : TestFormOn U k,
        Integrable (fun x => v₂ x ((ω : DifferentialForm (Eucl P) k) x)) μ₂) →
      ∀ W : Set (Eucl P), IsOpen W →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
        ∫ x, v₁ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₁ =
          ∫ x, v₂ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₂) →
      ∀ A : Set (Eucl P), MeasurableSet A → ∀ ω : TestFormOn U k,
        tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
        ∫ x in A, v₁ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₁ =
          ∫ x in A, v₂ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₂ := by
  intro P k U hU μ₁ μ₂ v₁ v₂ hint₁ hint₂ W hW heq A hA ω hωW
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) :=
    ω.property.1.1
  have hωc : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.property.1.2
  -- Step 1: an open `O ⊇ tsupport ω` whose closure is a compact subset of `U ∩ W`.
  obtain ⟨O, hO, hωO, hOUW, hOc⟩ := exists_open_between_and_isCompact_closure hωc.isCompact
    (hU.inter hW) (subset_inter ω.property.2 hωW)
  have hOU : closure O ⊆ U := hOUW.trans inter_subset_left
  have hOW : closure O ⊆ W := hOUW.trans inter_subset_right
  have hOm : MeasurableSet (closure O) := isClosed_closure.measurableSet
  have hωz : ∀ x, x ∉ O → (ω : DifferentialForm (Eucl P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hωO h)
  -- `dx β = dx^{β₁} ∧ ⋯ ∧ dx^{βₖ}` and `g v β = 1_{closure O} · v(dx β)`.
  let dx : SimonMultiIndex k P → Covector (Eucl P) k :=
    fun β => wedgeCovectors k fun j => EuclideanSpace.proj (β j)
  let g : (Eucl P → NVector (Eucl P) k) → SimonMultiIndex k P → Eucl P → ℝ :=
    fun v β => (closure O).indicator fun x => v x (dx β)
  -- Step 2: `g v β` is integrable, as `v(dx β)` is integrable on the compact `closure O ⊆ U`.
  have hg : ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
      (∀ ω : TestFormOn U k,
        Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) →
      ∀ β, Integrable (g v β) μ := fun μ v hv β =>
    (Submission.slicing_ru_integrableOn_apply P k U hU μ v hv (closure O) hOc hOU
      (dx β)).integrable_indicator hOm
  -- Step 3: agreement against smooth `φ` supported in `O`, testing with the form `φ dx β`.
  have hsmooth : ∀ β, ∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ O →
      ∫ x, φ x * g v₁ β x ∂μ₁ = ∫ x, φ x * g v₂ β x ∂μ₂ := by
    intro β φ hφ hφc hφO
    have hφs : tsupport (fun x => φ x • dx β) ⊆ closure O :=
      (tsupport_smul_subset_left φ fun _ => dx β).trans (hφO.trans subset_closure)
    let η : TestFormOn U k := ⟨fun x => φ x • dx β,
      ⟨⟨hφ.smul contDiff_const, hφc.smul_right⟩, hφs.trans hOU⟩⟩
    have hη : ∀ (v : Eucl P → NVector (Eucl P) k) (x : Eucl P),
        v x ((η : DifferentialForm (Eucl P) k) x) = φ x * g v β x := by
      intro v x
      change v x (φ x • dx β) = φ x * (closure O).indicator (fun x => v x (dx β)) x
      rw [map_smul, smul_eq_mul]
      by_cases hx : x ∈ closure O
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx,
          image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hφO h)), zero_mul,
          mul_zero]
    simp_rw [← hη]
    exact heq η (hφs.trans hOW)
  -- Steps 4–6: continuous `φ`, then bounded Borel `h` vanishing off `O` (π–λ uniqueness).
  have hbdd : ∀ β, ∀ h : Eucl P → ℝ, Measurable h → (∃ C : ℝ, ∀ x, |h x| ≤ C) →
      (∀ x, x ∉ O → h x = 0) → ∫ x, h x * g v₁ β x ∂μ₁ = ∫ x, h x * g v₂ β x ∂μ₂ :=
    fun β => Submission.slicing_ru_continuous_to_bounded P μ₁ μ₂ _ _ (hg μ₁ v₁ hint₁ β)
      (hg μ₂ v₂ hint₂ β) O hO
      (Submission.slicing_ru_smooth_to_continuous P μ₁ μ₂ _ _ (hg μ₁ v₁ hint₁ β)
        (hg μ₂ v₂ hint₂ β) O hO (hsmooth β))
  -- Step 7: the bounded Borel coefficients `a β = 1_A ω(e_β)`, which vanish off `O`.
  let a : SimonMultiIndex k P → Eucl P → ℝ := fun β =>
    A.indicator fun x => euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) k) x) β
  have hac : ∀ β, Continuous fun x =>
      euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) k) x) β := fun β =>
    hωs.continuous.eval_const _
  have ham : ∀ β, Measurable (a β) := fun β => (hac β).measurable.indicator hA
  have hab : ∀ β, ∃ C : ℝ, ∀ x, ‖a β x‖ ≤ C := by
    intro β
    obtain ⟨C, hC⟩ := (hac β).bounded_above_of_compact_support
      (hωc.comp_left (g := fun α => euclideanCovectorCoordinate α β) rfl)
    exact ⟨C, fun x => (norm_indicator_le_norm_self _ x).trans (hC x)⟩
  have ha0 : ∀ β x, x ∉ O → a β x = 0 := by
    intro β x hx
    simp [a, euclideanCovectorCoordinate, hωz x hx]
  -- `1_A v(ω) = ∑_β a β · g v β` pointwise, by the expansion `ω = ∑_β ω(e_β) dx β`.
  have hpt : ∀ (v : Eucl P → NVector (Eucl P) k) (x : Eucl P),
      A.indicator (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) x =
        ∑ β, a β x * g v β x := by
    intro v x
    by_cases hxO : x ∈ closure O
    · by_cases hxA : x ∈ A
      · simp only [a, g, indicator_of_mem hxA, indicator_of_mem hxO]
        conv_lhs => rw [Submission.slicing_ru_covector_expansion P k
          ((ω : DifferentialForm (Eucl P) k) x)]
        simp only [map_sum, map_smul, smul_eq_mul, dx]
      · simp [a, indicator_of_notMem hxA]
    · simp [g, hxO, hωz x fun h => hxO (subset_closure h)]
  have hsum : ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
      (∀ ω : TestFormOn U k,
        Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) →
      ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ =
        ∑ β, ∫ x, a β x * g v β x ∂μ := by
    intro μ v hv
    rw [← integral_indicator hA]
    calc ∫ x, A.indicator (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) x ∂μ
        = ∫ x, ∑ β, a β x * g v β x ∂μ := integral_congr_ae (Eventually.of_forall (hpt v))
      _ = ∑ β, ∫ x, a β x * g v β x ∂μ := integral_finsetSum _ fun β _ => by
          obtain ⟨C, hC⟩ := hab β
          exact (hg μ v hv β).bdd_mul (ham β).aestronglyMeasurable (Eventually.of_forall hC)
  rw [hsum μ₁ v₁ hint₁, hsum μ₂ v₂ hint₂]
  refine Finset.sum_congr rfl fun β _ => hbdd β (a β) (ham β) ?_ (ha0 β)
  obtain ⟨C, hC⟩ := hab β
  exact ⟨C, fun x => (Real.norm_eq_abs (a β x)).symm.le.trans (hC x)⟩

/-- **Simon Ch. 6, 4.6 (p. 157).**  The slice `⟨T, f, t₋⟩ = ∂(T ⌞ A_t) − (∂T) ⌞ A_t` exists for
every level `t`.  `A_t = {x ∈ U | f x < t}` is open, as `f` is continuous on the open set `U`;
the representations of `T` and `∂T` from `slicing_mass_representation` restrict to `A_t`, and
`∂(T ⌞ A_t) − (∂T) ⌞ A_t` is again a sequentially continuous functional. -/
theorem Submission.slicing_exists :
    ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ t : ℝ,
        ∃ S : GeometricCurrentOn U m, IsSlice T f t S := by
  intro P m U hU T hT f L hf t
  -- Step 1: `A_t = U ∩ f⁻¹(-∞, t)` is open, hence Borel.
  have hAt : MeasurableSet {x | x ∈ U ∧ f x < t} :=
    (hf.continuousOn.isOpen_inter_preimage hU isOpen_Iio).measurableSet
  -- Step 2: `T ⌞ A_t`, through a representation `(μ, v)` of `T`.
  obtain ⟨μ, v, hrep, -, -, -, hres, -⟩ :=
    Submission.slicing_mass_representation P (m + 1) U hU T fun W hW => (hT W hW).1
  obtain ⟨A, hA⟩ := hres _ hAt
  -- Step 3: `(∂T) ⌞ A_t`, through a representation `(μ', v')` of `∂T`.
  obtain ⟨μ', v', hrep', -, -, -, hres', -⟩ :=
    Submission.slicing_mass_representation P m U hU T.boundary fun W hW => (hT W hW).2
  obtain ⟨B, hB⟩ := hres' _ hAt
  -- Step 4: `S = ∂A − B` is linear, and continuous as a difference of continuous functionals.
  refine ⟨⟨A.boundary.toCurrent - B.toCurrent, fun ωs hωs => ?_⟩,
    A, B, ⟨hAt, μ, v, hrep, hA⟩, ⟨hAt, μ', v', hrep', hB⟩, fun ω => rfl⟩
  simpa using (A.boundary.continuous' ωs hωs).sub (B.continuous' ωs hωs)
/-- **Simon Ch. 6, 4.8 (p. 157).**  Every slice `S = ⟨T, f, t₋⟩` of (4.6) satisfies
`spt S ⊆ spt T ∩ {f = t}`.  With `A_t = {x ∈ U | f x < t}` and representations `(μ, v)` of `T`
and `(μ', v')` of `∂T`, `S(ω) = ∫_{A_t} ⟨dω, v⟩ dμ − ∫_{A_t} ⟨ω, v'⟩ dμ'`.  Both integrals
vanish for `ω` supported where `T = 0` (`slicing_representation_unique` against the zero
representation) or where `f > t`, and both equal `T(dω)` for `ω` supported where `f < t`. -/
theorem Submission.slicing_support_subset :
    ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
      ∀ (t : ℝ) (S : GeometricCurrentOn U m), IsSlice T f t S →
        S.support ⊆ T.support ∩ {x | f x = t} := by
  intro P m U hU T f L hf t S hS
  -- Step 0: unpack the slice into the formula for `S(ω)` above.
  obtain ⟨A, B, ⟨hAt, μ, v, hrep, hA⟩, ⟨-, μ', v', hrep', hB⟩, hSAB⟩ := hS
  set At : Set (Eucl P) := {x | x ∈ U ∧ f x < t}
  have hS_eq : ∀ ω : TestFormOn U m, S ω =
      (∫ x in At, v x (((exteriorDerivativeTestOn U m ω : TestFormOn U (m + 1)) :
        DifferentialForm (Eucl P) (m + 1)) x) ∂μ) -
      ∫ x in At, v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ' := fun ω => by
    rw [hSAB ω, GeometricCurrentOn.boundary_apply, hA, hB]
  -- Locality: if a represented current vanishes on an open `W`, so does its restriction to
  -- `A_t` (`slicing_representation_unique` against the zero representation).
  have hloc : ∀ {k : ℕ} (X : GeometricCurrentOn U k) (ν : Measure (Eucl P))
      (w : Eucl P → NVector (Eucl P) k), IsMeasureRepresentation X ν w →
      ∀ W : Set (Eucl P), IsOpen W → X.VanishesOn W →
      ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
        ∫ x in At, w x ((ω : DifferentialForm (Eucl P) k) x) ∂ν = 0 := by
    intro k X ν w hX W hW hvan ω hω
    simpa using Submission.slicing_representation_unique P k U hU ν 0 w 0 (fun η => (hX η).1)
      (fun _ => integrable_zero_measure) W hW
      (fun η hη => by rw [← (hX η).2, hvan η hη]; simp) At hAt ω hω
  -- Forms vanish off their topological support, and `tsupport dω ⊆ tsupport ω`.
  have hzero : ∀ {k : ℕ} (w : Eucl P → NVector (Eucl P) k) (η : DifferentialForm (Eucl P) k)
      (y : Eucl P), y ∉ tsupport η → w y (η y) = 0 := fun w η y hy => by
    rw [image_eq_zero_of_notMem_tsupport hy, map_zero]
  have hd : ∀ (ω : TestFormOn U m) (W' : Set (Eucl P)),
      tsupport (ω : DifferentialForm (Eucl P) m) ⊆ W' →
      tsupport (((exteriorDerivativeTestOn U m ω : TestFormOn U (m + 1)) :
        DifferentialForm (Eucl P) (m + 1))) ⊆ W' := fun _ _ hω =>
    (tsupport_exteriorDerivative_subset _).trans hω
  -- Step 1: `x ∈ U`, and `S` vanishes on no open `W' ∋ x` with `closure W'` compact in `U`.
  rintro x ⟨hxU, hxS⟩
  have hS_ne : ∀ W' : Set (Eucl P), IsOpen W' → IsCompact (closure W') → closure W' ⊆ U →
      x ∈ W' → S.VanishesOn W' → False := fun W' h1 h2 h3 hxW hvan =>
    hxS ⟨W', ⟨h1, h2, h3, hvan⟩, hxW⟩
  refine ⟨⟨hxU, ?_⟩, ?_⟩
  · -- Step 2: if `T` vanishes on such a `W' ∋ x`, then so do `∂T` and hence `S`.
    rintro ⟨W', ⟨h1, h2, h3, hTvan⟩, hxW⟩
    apply hS_ne W' h1 h2 h3 hxW
    intro ω hω
    have hbvan : T.boundary.VanishesOn W' := fun η hη => by
      rw [GeometricCurrentOn.boundary_apply]
      exact hTvan _ (hd η W' hη)
    rw [hS_eq ω, hloc T μ v hrep W' h1 hTvan _ (hd ω W' hω),
      hloc T.boundary μ' v' hrep' W' h1 hbvan ω hω, sub_self]
  · -- Step 3: `f x = t`, since otherwise `S` vanishes on a small ball around `x`.
    have hcont : ContinuousAt f x := hf.continuousOn.continuousAt (hU.mem_nhds hxU)
    have hball : ∀ p : Eucl P → Prop, (∀ᶠ y in 𝓝 x, p y) → ∃ W' : Set (Eucl P), IsOpen W' ∧
        IsCompact (closure W') ∧ closure W' ⊆ U ∧ x ∈ W' ∧ ∀ y ∈ W', p y := by
      intro p hp
      obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff_ball.1
        ((show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and hp)
      refine ⟨ball x (r / 2), isOpen_ball, ?_, ?_, mem_ball_self (by linarith), ?_⟩
      · rw [closure_ball x (by positivity)]
        exact isCompact_closedBall x _
      · rw [closure_ball x (by positivity)]
        exact fun y hy => (hr' y (closedBall_subset_ball (by linarith) hy)).1
      · exact fun y hy => (hr' y (ball_subset_ball (by linarith) hy)).2
    rcases lt_trichotomy (f x) t with hlt | heq | hgt
    · -- (a) `f < t` near `x`: both integrals equal `T(dω)`.
      exfalso
      obtain ⟨W', h1, h2, h3, hxW, hW'⟩ :=
        hball (fun y => f y < t) (hcont.eventually (eventually_lt_nhds hlt))
      apply hS_ne W' h1 h2 h3 hxW
      intro ω hω
      have hWA : W' ⊆ At := fun y hy => ⟨h3 (subset_closure hy), hW' y hy⟩
      rw [hS_eq ω, setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => hzero v _ y fun h => hy (hWA (hd ω W' hω h))),
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => hzero v' _ y fun h => hy (hWA (hω h))),
        ← (hrep _).2, ← (hrep' ω).2, GeometricCurrentOn.boundary_apply, sub_self]
    · exact heq
    · -- (b) `f > t` near `x`: both integrals vanish.
      exfalso
      obtain ⟨W', h1, h2, h3, hxW, hW'⟩ :=
        hball (fun y => t < f y) (hcont.eventually (eventually_gt_nhds hgt))
      apply hS_ne W' h1 h2 h3 hxW
      intro ω hω
      have hWA : ∀ y ∈ At, y ∉ W' := fun y hy hyW => lt_asymm hy.2 (hW' y hyW)
      rw [hS_eq ω, setIntegral_eq_zero_of_forall_eq_zero
          (fun y hy => hzero v _ y fun h => hWA y hy (hd ω W' hω h)),
        setIntegral_eq_zero_of_forall_eq_zero
          (fun y hy => hzero v' _ y fun h => hWA y hy (hω h)), sub_self]
/-- **Mass bound for slices (Simon Ch. 6, 4.9–4.10, pp. 157–158).**  For `W ⊆ U` open,
`‖Df‖ ≤ L_W` a.e. on `W` and `a < b`, `t ↦ M_W(⟨T, f, t⟩)` has a measurable majorant `g` on
`(a, b)` with `∫⁻_{(a,b)} g ≤ L_W M_W(T ⌞ {a < f < b})`.  In the normalized representation
`(μ, v)` of `T`, `M_W(T ⌞ {a < f < b}) = μ(W ∩ {a < f < b})`, and (4.9) bounds `M_W(⟨T, f, t⟩)`
by `L_W liminf_{h ↓ 0} h⁻¹ μ(W ∩ f⁻¹[t - h, t])`.  This is `L_W` times the lower left density at
`t` of `ν = f_#(μ ⌞ W)`, which has a measurable majorant with integral `≤ ν(a, b)` (4.10). -/
theorem Submission.slicing_mass_bound : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ S : ℝ → GeometricCurrentOn U m, (∀ t, IsSlice T f t (S t)) → ∀ W, IsOpen W → W ⊆ U → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → ∀ a b : ℝ, a < b → ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W := by
  intro P m U hU T hT f L hf S hS W hW hWU LW hLW a b hab R hR
  -- Step 1: a normalized representation `(μ, v)` of `T`, finite on compact subsets of `U`.
  obtain ⟨μ, v, hrep, -, hfin, hnorm, -, hmass⟩ :=
    Submission.slicing_mass_representation P (m + 1) U hU T fun W' hW' => (hT W' hW').1
  -- Step 2: `R = T ⌞ A` is also computed in `(μ, v)`, hence `M_W(R) = μ(W ∩ A)`.
  obtain ⟨hA, μR, vR, hrepR, hRA⟩ := hR
  have hR' : ∀ ω : TestFormOn U (m + 1), R ω = ∫ x in {x | x ∈ U ∧ a < f x ∧ f x < b},
      v x ((ω : DifferentialForm (Eucl P) (m + 1)) x) ∂μ := by
    intro ω
    rw [hRA ω]
    exact Submission.slicing_representation_unique P (m + 1) U hU μR μ vR v
      (fun ω => (hrepR ω).1) (fun ω => (hrep ω).1) univ isOpen_univ
      (fun ω _ => (hrepR ω).2.symm.trans (hrep ω).2) _ hA ω (subset_univ _)
  have hRmass : R.massOn W = μ (W ∩ {x | x ∈ U ∧ a < f x ∧ f x < b}) :=
    hmass _ hA R hR' W hW hWU
  -- Step 3: `ν = f_#(μ ⌞ W)`, using that `f` is continuous on the open set `W ⊆ U`.
  have hfm : AEMeasurable f (μ.restrict W) :=
    (hf.continuousOn.mono hWU).aemeasurable hW.measurableSet
  have hν : ∀ s : Set ℝ, MeasurableSet s → (μ.restrict W).map f s = μ (W ∩ f ⁻¹' s) := by
    intro s hs
    rw [Measure.map_apply_of_aemeasurable hfm hs, Measure.restrict_apply' hW.measurableSet,
      inter_comm]
  -- Step 4: (4.10) for `ν`: a measurable majorant `g₀` of the lower left densities of `ν`.
  obtain ⟨g₀, hg₀, hg₀le, hg₀int⟩ :=
    Submission.slicing_mb_density_majorant ((μ.restrict W).map f) a b hab
  refine ⟨fun t => (LW : ℝ≥0∞) * g₀ t, hg₀.const_mul _, fun t ht => ?_, ?_⟩
  · -- Step 5: (4.9) gives `M_W(S t) ≤ L_W liminf_{h ↓ 0} h⁻¹ ν[t - h, t] ≤ L_W g₀(t)`.
    have hden : (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) =
        fun h : ℝ => (μ.restrict W).map f (Icc (t - h) t) / ENNReal.ofReal h := by
      funext h
      rw [hν _ measurableSet_Icc]
    calc (S t).massOn W
        ≤ (LW : ℝ≥0∞) *
            liminf (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) :=
          Submission.slicing_mb_pointwise P m U hU T μ v hrep hfin hnorm f L hf t (S t) (hS t)
            W hW hWU LW hLW
      _ ≤ (LW : ℝ≥0∞) * g₀ t := by
          rw [hden]
          exact mul_le_mul_right (hg₀le t ht) _
  · -- Step 6: `∫⁻_{(a,b)} L_W g₀ ≤ L_W ν(a, b) = L_W μ(W ∩ {a < f < b}) = L_W M_W(R)`.
    have hWab : W ∩ f ⁻¹' Ioo a b = W ∩ {x | x ∈ U ∧ a < f x ∧ f x < b} := by
      ext x
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, hWU hx, h⟩
      · rintro ⟨hx, -, h⟩
        exact ⟨hx, h⟩
    calc ∫⁻ t in Ioo a b, (LW : ℝ≥0∞) * g₀ t
        = (LW : ℝ≥0∞) * ∫⁻ t in Ioo a b, g₀ t := lintegral_const_mul _ hg₀
      _ ≤ (LW : ℝ≥0∞) * (μ.restrict W).map f (Ioo a b) := mul_le_mul_right hg₀int _
      _ = (LW : ℝ≥0∞) * R.massOn W := by
          rw [hν _ measurableSet_Ioo, hWab, hRmass]
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

/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70), displays (1)–(2): for a Lipschitz `F : ℝⁿ → ℝ^P`
there are `C¹` maps `G_i : ℝⁿ → ℝ^P` with `F(ℝⁿ) ⊆ F(Z) ∪ ⋃_i G_i(ℝⁿ)` and `Hⁿ(F(Z)) = 0`, where
`F = G_i` off a set of measure `< 1/i` (C¹ Approximation Theorem) and `Lⁿ(Z) = 0`. -/
theorem Submission.slicing_im_tg_cc_lipschitz_range_c1_cover :
    ∀ (n P : ℕ) (F : Eucl n → Eucl P) (K : ℝ≥0), LipschitzWith K F → ∃ G : ℕ → Eucl n → Eucl P,
      (∀ i, ContDiff ℝ 1 (G i)) ∧ (μHE[n] : Measure (Eucl P)) (range F \ ⋃ i, range (G i)) = 0 := by
  intro n P F K hF
  -- `ε_i = i⁻¹ ∈ (0, ∞]` (`ε_0 = ∞`).
  have hε : ∀ i : ℕ, (0 : ℝ≥0∞) < (i : ℝ≥0∞)⁻¹ := fun i =>
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i)
  -- `C¹` approximations: closed `A_i` and `C¹` `G_i` with `F = G_i` on `A_i`, `Lⁿ(ℝⁿ ∖ A_i) < i⁻¹`.
  choose A G hAc hAm hG hAG using fun i : ℕ =>
    Submission.lpf_c1_approximation_eucl n P F K hF _ (hε i)
  refine ⟨G, hG, ?_⟩
  -- `Z = ⋂_i (ℝⁿ ∖ A_i)` is `Lⁿ`-null.
  set Z : Set (Eucl n) := ⋂ i, (A i)ᶜ with hZdef
  have hZ : (volume : Measure (Eucl n)) Z = 0 := by
    refine le_antisymm ?_ bot_le
    refine ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun i => ?_
    exact (measure_mono (iInter_subset _ i)).trans (hAm i).le
  -- `F(Z)` is `Hⁿ`-null: `Hⁿ(F(Z)) ≤ Kⁿ Hⁿ(Z) = Kⁿ Lⁿ(Z) = 0`.
  have hFZ : (μHE[n] : Measure (Eucl P)) (F '' Z) = 0 := by
    refine le_antisymm ?_ bot_le
    calc (μHE[n] : Measure (Eucl P)) (F '' Z)
        ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Eucl n)) Z :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero]
  -- `F(ℝⁿ) ∖ ⋃_i G_i(ℝⁿ) ⊆ F(Z)`: if `F w ∉ ⋃_i G_i(ℝⁿ)`, then `w ∉ A_i` for every `i`.
  refine measure_mono_null ?_ hFZ
  rintro y ⟨⟨w, rfl⟩, hy⟩
  refine ⟨w, ?_, rfl⟩
  rw [hZdef, mem_iInter]
  intro i hwi
  exact hy (mem_iUnion.2 ⟨i, w, ((hAG i w hwi).1).symm⟩)
/-- Simon Ch. 3, proof of Lemma 1.2 (p. 70) and Remark 1.3, for one `C¹` map `G : ℝⁿ → ℝ^P`:
countably many open sets `O k` on each of which `G` is Lipschitz and bi-Lipschitz onto its image
cover `G(ℝⁿ)` up to an `Hⁿ`-null set.  Regular points (`DG(w)` injective) lie in some `O k`;
the image of the critical set is `Hⁿ`-null: near a critical point, `G` composed with a linear map
that shrinks the directions orthogonal to a kernel vector has a small Lipschitz constant. -/
theorem Submission.slicing_im_tg_cc_contDiff_range_chart_cover : ∀ (n P : ℕ) (G : Eucl n → Eucl P), ContDiff ℝ 1 G → ∃ O : ℕ → Set (Eucl n), (∀ k, IsOpen (O k)) ∧ (∀ k, ∃ K : ℝ≥0, LipschitzOnWith K G (O k)) ∧ (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ O k, ∀ w' ∈ O k, c * ‖w - w'‖ ≤ ‖G w - G w'‖) ∧ (μHE[n] : Measure (Eucl P)) (range G \ ⋃ k, G '' O k) = 0 := by
  intro n P G hG
  -- A countable basis `𝔅` of `ℝⁿ`; enumerate `{∅} ∪ {U ∈ 𝔅 : G Lipschitz and antilipschitz on U}`.
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Eucl n)
  set good : Set (Set (Eucl n)) := {U | U ∈ b ∧ (∃ K : ℝ≥0, LipschitzOnWith K G U) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ U, ∀ w' ∈ U, c * ‖w - w'‖ ≤ ‖G w - G w'‖} with hgood
  have hgc : (insert ∅ good).Countable := (hbc.mono fun U hU => hU.1).insert ∅
  obtain ⟨O, hO⟩ := hgc.exists_eq_range (insert_nonempty _ _)
  have hOk : ∀ k, O k = ∅ ∨ O k ∈ good := fun k => by
    have : O k ∈ insert ∅ good := hO ▸ mem_range_self k
    simpa using this
  -- Each `O k` is open, and `G` is Lipschitz and antilipschitz on it.
  refine ⟨O, fun k => ?_, fun k => ?_, fun k => ?_, ?_⟩
  · rcases hOk k with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h.1
  · rcases hOk k with h | h
    · exact ⟨0, by rw [h]; exact lipschitzOnWith_empty _ _⟩
    · exact h.2.1
  · rcases hOk k with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact h.2.2
  · -- A regular point has an antilipschitz ball and a Lipschitz neighbourhood, hence a good
    -- basis set around it.
    have hreg : ∀ w, Function.Injective (fderiv ℝ G w) → ∃ k, w ∈ O k := by
      intro w hw
      obtain ⟨r, hr, c, hc, hcr⟩ := Submission.lpf_c1_local_antilipschitz n P G w hG hw
      obtain ⟨K, t, ht, hKt⟩ := hG.locallyLipschitz w
      have hmem : ball w r ∩ t ∈ 𝓝 w := inter_mem (ball_mem_nhds w hr) ht
      obtain ⟨U, hUb, hwU, hUs⟩ := hb.mem_nhds_iff.1 hmem
      have hUg : U ∈ good := ⟨hUb, ⟨K, hKt.mono fun x hx => (hUs hx).2⟩,
        ⟨c, hc, fun z hz z' hz' => hcr z (hUs hz).1 z' (hUs hz').1⟩⟩
      obtain ⟨k, hk⟩ : U ∈ range O := hO ▸ mem_insert_of_mem _ hUg
      exact ⟨k, hk ▸ hwU⟩
    -- The critical set `C = {w : DG(w) not injective}` has `Hⁿ`-null image, and `G(C)` contains
    -- every uncovered point of `G(ℝⁿ)`.
    set C : Set (Eucl n) := {x | ¬ Function.Injective (fderiv ℝ G x)}
    have hcrit : (μHE[n] : Measure (Eucl P)) (G '' C) = 0 := by
      have hD : ∀ x, HasFDerivAt G (fderiv ℝ G x) x :=
        fun x => ((hG.differentiable one_ne_zero) x).hasFDerivAt
      -- It suffices to treat the bounded pieces `s = C ∩ B_R(0)`.
      have hR : ∀ R : ℕ, (μHE[n] : Measure (Eucl P)) (G '' (C ∩ ball 0 R)) = 0 := by
        intro R
        set s : Set (Eucl n) := C ∩ ball 0 R
        have hsfin : volume s ≠ ∞ :=
          ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        -- Main estimate: `Hⁿ(G(s)) ≤ 2ⁿ ε |s|` for every `0 < ε ≤ 1`.
        have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            (μHE[n] : Measure (Eucl P)) (G '' s) ≤ ENNReal.ofReal (2 ^ n * ε) * volume s := by
          intro ε hε hε1
          rcases s.eq_empty_or_nonempty with hse | hsne
          · rw [hse, image_empty, measure_empty]
            exact zero_le
          -- Partition `s` into measurable pieces `s ∩ t j` on which `G` is approximated by
          -- `A j = DG(y)`, `y ∈ s`, up to `δ = ε / (‖A j‖ + 1)ⁿ`.
          obtain ⟨t, A, htd, htm, hst, hA, hAy⟩ :=
            exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
              (fun x _ => (hD x).hasFDerivWithinAt)
              (fun B => ⟨ε / (‖B‖ + 1) ^ n, by positivity⟩)
              (fun B => ne_of_gt
                (NNReal.coe_pos.1 (show (0 : ℝ) < ε / (‖B‖ + 1) ^ n by positivity)))
          have hpiece : ∀ j, (μHE[n] : Measure (Eucl P)) (G '' (s ∩ t j)) ≤
              ENNReal.ofReal (2 ^ n * ε) * volume (s ∩ t j) := by
            intro j
            obtain ⟨y, hys, hyA⟩ := hAy hsne j
            -- A unit vector `u` in the kernel of `A j = DG(y)`.
            obtain ⟨u, hu1, hAu⟩ : ∃ u : Eucl n, ‖u‖ = 1 ∧ A j u = 0 := by
              have hni : ¬ Function.Injective (A j) := by rw [hyA]; exact hys.1
              obtain ⟨v, hv, hv0⟩ : ∃ v, A j v = 0 ∧ v ≠ 0 := by
                by_contra hcon
                refine hni ((injective_iff_map_eq_zero (A j)).2 fun v hv => ?_)
                by_contra hv0
                exact hcon ⟨v, hv, hv0⟩
              refine ⟨‖v‖⁻¹ • v, ?_, by rw [map_smul, hv, smul_zero]⟩
              rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
            -- `L = ‖A j‖ + 1`, `δ = ε / Lⁿ`, `a = δ / L`; `T = a • id + (1 - a) • ⟪u, ·⟫ u`
            -- shrinks `u⊥` by the factor `a` and fixes `u`.
            set L : ℝ := ‖A j‖ + 1
            have hL1 : 1 ≤ L := le_add_of_nonneg_left (norm_nonneg _)
            have hL0 : 0 < L := by linarith
            set δ : ℝ := ε / L ^ n with hδ
            have hδ0 : 0 < δ := by positivity
            set a : ℝ := δ / L with ha
            have ha0 : 0 < a := by positivity
            have ha1 : a ≤ 1 := by
              rw [ha, hδ, div_div, div_le_one (by positivity)]
              exact hε1.trans (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hL1)
            set T : Eucl n →ₗ[ℝ] Eucl n :=
              a • LinearMap.id + (1 - a) • (innerₛₗ ℝ u).smulRight u with hT
            have hTw : ∀ w, T w = a • w + (1 - a) • (inner ℝ u w • u) := fun w => by
              simp only [hT, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
                LinearMap.smulRight_apply, innerₛₗ_apply_apply]
            have hAT : ∀ w, A j (T w) = a • A j w := fun w => by
              rw [hTw, map_add, map_smul, map_smul, map_smul, hAu, smul_zero, smul_zero, add_zero]
            have hTn : ∀ w, ‖T w‖ ≤ ‖w‖ := fun w => by
              rw [hTw]
              calc ‖a • w + (1 - a) • (inner ℝ u w • u)‖
                  ≤ ‖a • w‖ + ‖(1 - a) • (inner ℝ u w • u)‖ := norm_add_le _ _
                _ = a * ‖w‖ + (1 - a) * (|inner ℝ u w| * ‖u‖) := by
                    rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg ha0.le,
                      Real.norm_of_nonneg (sub_nonneg.2 ha1), Real.norm_eq_abs]
                _ ≤ a * ‖w‖ + (1 - a) * ‖w‖ := by
                    have h1a : 0 ≤ 1 - a := sub_nonneg.2 ha1
                    have hin : |inner ℝ u w| * ‖u‖ ≤ ‖w‖ := by
                      rw [hu1, mul_one]
                      exact (abs_real_inner_le_norm u w).trans (by rw [hu1, one_mul])
                    gcongr
                _ = ‖w‖ := by ring
            -- `det T = aⁿ / a`, computed in the standard basis (matrix determinant lemma).
            have hdet : LinearMap.det T = a ^ n / a := by
              set e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with he
              have hM : LinearMap.toMatrix e e T = a • (1 + Matrix.replicateCol Unit
                  (((1 - a) / a) • fun i => u i) * Matrix.replicateRow Unit (fun i => u i)) := by
                ext i j
                rw [LinearMap.toMatrix_apply]
                simp [he, hT, Matrix.one_apply, Matrix.mul_apply, EuclideanSpace.inner_single_right]
                have h' : a * ((1 - a) / a) = 1 - a := mul_div_cancel₀ _ ha0.ne'
                split_ifs <;> linear_combination (-(u i * u j)) * h'
              have hdot : (fun i => u i) ⬝ᵥ (fun i => u i) = 1 := by
                have h := EuclideanSpace.norm_sq_eq u
                rw [hu1, one_pow] at h
                rw [h, dotProduct]
                simp [sq]
              rw [← LinearMap.det_toMatrix e, hM, Matrix.det_smul,
                Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hdot,
                Fintype.card_fin, smul_eq_mul, mul_one]
              field_simp
              ring
            have hdet0 : LinearMap.det T ≠ 0 := by rw [hdet]; positivity
            have hTs : Function.Surjective T := ((Module.End.isUnit_iff T).1
              ((LinearMap.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet0))).2
            -- `G ∘ T` is `2δ`-Lipschitz on `T⁻¹(s ∩ t j)`.
            have hLip : LipschitzOnWith (2 * δ).toNNReal (G ∘ T) (T ⁻¹' (s ∩ t j)) := by
              refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
              rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
              have h1 : ‖G (T z) - G (T z') - A j (T z - T z')‖ ≤ δ * ‖T z - T z'‖ :=
                hA j (T z) hz (T z') hz'
              have h2 : ‖A j (T z - T z')‖ ≤ δ * ‖z - z'‖ := by
                rw [← map_sub, hAT, norm_smul, Real.norm_of_nonneg ha0.le]
                calc a * ‖A j (z - z')‖ ≤ a * (L * ‖z - z'‖) := by
                      gcongr
                      exact ((A j).le_opNorm _).trans (by gcongr; linarith)
                  _ = δ * ‖z - z'‖ := by rw [ha]; field_simp
              have h3 : ‖T z - T z'‖ ≤ ‖z - z'‖ := by rw [← map_sub]; exact hTn _
              calc ‖(G ∘ T) z - (G ∘ T) z'‖
                  = ‖(G (T z) - G (T z') - A j (T z - T z')) + A j (T z - T z')‖ := by
                    rw [sub_add_cancel]; rfl
                _ ≤ ‖G (T z) - G (T z') - A j (T z - T z')‖ + ‖A j (T z - T z')‖ :=
                    norm_add_le _ _
                _ ≤ δ * ‖z - z'‖ + δ * ‖z - z'‖ := by
                    gcongr
                    exact h1.trans (by gcongr)
                _ = 2 * δ * ‖z - z'‖ := by ring
            -- `Hⁿ(G(s ∩ t j)) ≤ (2δ)ⁿ |T⁻¹(s ∩ t j)| = (2δ)ⁿ a¹⁻ⁿ |s ∩ t j| = 2ⁿ ε L⁻¹ |s ∩ t j|`.
            calc (μHE[n] : Measure (Eucl P)) (G '' (s ∩ t j))
                = (μHE[n] : Measure (Eucl P)) ((G ∘ T) '' (T ⁻¹' (s ∩ t j))) := by
                  rw [image_comp, image_preimage_eq _ hTs]
              _ ≤ ((2 * δ).toNNReal : ℝ≥0∞) ^ n *
                    (μHE[n] : Measure (Eucl n)) (T ⁻¹' (s ∩ t j)) :=
                  Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
                    n hLip
              _ = ENNReal.ofReal ((2 * δ) ^ n * (a / a ^ n)) * volume (s ∩ t j) := by
                  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
                    Measure.addHaar_preimage_linearMap volume hdet0, hdet, inv_div,
                    abs_of_pos (by positivity), ← mul_assoc, ENNReal.ofReal_mul (by positivity),
                    ENNReal.ofReal_pow (by positivity)]
                  rfl
              _ ≤ ENNReal.ofReal (2 ^ n * ε) * volume (s ∩ t j) := by
                  gcongr ENNReal.ofReal ?_ * _
                  have hδa : δ = a * L := by rw [ha]; field_simp
                  have hεδ : ε = δ * L ^ n := by rw [hδ]; field_simp
                  have hval : (2 * δ) ^ n * (a / a ^ n) = 2 ^ n * ε / L := by
                    rw [hεδ, hδa, mul_pow, mul_pow]
                    field_simp
                  rw [hval]
                  exact div_le_self (by positivity) hL1
          calc (μHE[n] : Measure (Eucl P)) (G '' s)
              ≤ (μHE[n] : Measure (Eucl P)) (⋃ j, G '' (s ∩ t j)) := by
                refine measure_mono ?_
                rw [← image_iUnion, ← inter_iUnion]
                exact image_mono (subset_inter subset_rfl hst)
            _ ≤ ∑' j, (μHE[n] : Measure (Eucl P)) (G '' (s ∩ t j)) := measure_iUnion_le _
            _ ≤ ∑' j, ENNReal.ofReal (2 ^ n * ε) * volume (s ∩ t j) :=
                ENNReal.tsum_le_tsum hpiece
            _ = ENNReal.ofReal (2 ^ n * ε) * ∑' j, (volume.restrict s) (t j) := by
                rw [ENNReal.tsum_mul_left]
                congr 1
                refine tsum_congr fun j => ?_
                rw [Measure.restrict_apply (htm j), inter_comm]
            _ = ENNReal.ofReal (2 ^ n * ε) * (volume.restrict s) (⋃ j, t j) := by
                rw [measure_iUnion htd htm]
            _ ≤ ENNReal.ofReal (2 ^ n * ε) * volume s := by
                gcongr _ * ?_
                exact (measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ s)
        -- Let `ε → 0`.
        refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) zero_le
        rw [zero_add]
        have hη' : (0 : ℝ) < η := NNReal.coe_pos.2 hη
        have hV0 : 0 ≤ (volume s).toReal := ENNReal.toReal_nonneg
        have hV1 : 0 < (volume s).toReal + 1 := by linarith
        obtain ⟨ε, hε, hε1, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
            2 ^ n * ε * (volume s).toReal ≤ η := by
          refine ⟨min 1 (η / (2 ^ n * ((volume s).toReal + 1))), lt_min one_pos (by positivity),
            min_le_left _ _, ?_⟩
          calc 2 ^ n * min 1 (η / (2 ^ n * ((volume s).toReal + 1))) * (volume s).toReal
              ≤ 2 ^ n * (η / (2 ^ n * ((volume s).toReal + 1))) * ((volume s).toReal + 1) := by
                gcongr
                · exact min_le_right _ _
                · linarith
            _ = η := by field_simp
        calc (μHE[n] : Measure (Eucl P)) (G '' s) ≤ ENNReal.ofReal (2 ^ n * ε) * volume s :=
              hkey ε hε hε1
          _ = ENNReal.ofReal (2 ^ n * ε * (volume s).toReal) := by
              rw [ENNReal.ofReal_mul' hV0, ENNReal.ofReal_toReal hsfin]
          _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεη
          _ = η := ENNReal.ofReal_coe_nnreal
      refine measure_mono_null ?_ (measure_iUnion_null hR)
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨R, hRx⟩ := exists_nat_gt ‖x‖
      exact mem_iUnion.2 ⟨R, x, ⟨hx, mem_ball_zero_iff.2 hRx⟩, rfl⟩
    refine measure_mono_null ?_ hcrit
    rintro y ⟨⟨w, rfl⟩, hy⟩
    refine ⟨w, fun hinj => ?_, rfl⟩
    obtain ⟨k, hk⟩ := hreg w hinj
    exact hy (mem_iUnion.2 ⟨k, w, hk, rfl⟩)

/-- Simon Ch. 3, Lemma 1.2 ("only if", pp. 69–70) with Remark 1.3 (p. 70), in chart form: a
countably `n`-rectifiable `M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null set, by images `Φ_j(Ω_j)` of
open `Ω_j ⊆ ℝⁿ` under `C¹` maps `Φ_j : ℝⁿ → ℝ^P` that are Lipschitz and antilipschitz on `Ω_j`.
Write `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` (1.1); each `F_j(ℝⁿ)` is covered up to an `Hⁿ`-null set by `C¹`
images `G_{ji}(ℝⁿ)` (display (1)), and each `G_{ji}(ℝⁿ)` by images `G_{ji}(O_{jik})` of open sets
on which `G_{ji}` is Lipschitz and antilipschitz (the area formula at critical points and the
inverse function theorem at regular points); the triples `(j, i, k)` are enumerated by `ℕ`. -/
theorem Submission.slicing_im_tg_c1_chart_cover : ∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 := by
  intro P n M hM
  -- 1.1: `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and `F_j` `K_j`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hM
  choose K hK using hF
  -- `C¹` maps `G_{ji}` with `Hⁿ(F_j(ℝⁿ) ∖ ⋃_i G_{ji}(ℝⁿ)) = 0`.
  choose G hG hGnull using fun j =>
    Submission.slicing_im_tg_cc_lipschitz_range_c1_cover n P (F j) (K j) (hK j)
  -- Open `O_{jik}` on which `G_{ji}` is Lipschitz and antilipschitz, with
  -- `Hⁿ(G_{ji}(ℝⁿ) ∖ ⋃_k G_{ji}(O_{jik})) = 0`.
  choose O hO hOL hOA hOnull using fun j i =>
    Submission.slicing_im_tg_cc_contDiff_range_chart_cover n P (G j i) (hG j i)
  -- The charts `(Φ_m, Ω_m) = (G_{ji}, O_{jik})` for `e m = (j, i, k)`, `e : ℕ ≃ ℕ × ℕ × ℕ`.
  let e : ℕ ≃ ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm
  refine ⟨fun m => G (e m).1 (e m).2.1, fun m => O (e m).1 (e m).2.1 (e m).2.2,
    fun m => hO _ _ _, fun m => hG _ _, fun m => hOL _ _ _, fun m => hOA _ _ _, ?_⟩
  -- `M ∖ ⋃_m Φ_m(Ω_m)` lies in `M₀ ∪ ⋃_j (F_j(ℝⁿ) ∖ ⋃_i G_{ji}(ℝⁿ))` together with
  -- `⋃_{j,i} (G_{ji}(ℝⁿ) ∖ ⋃_k G_{ji}(O_{jik}))`, a countable union of `Hⁿ`-null sets.
  refine measure_mono_null (t := M₀ ∪ (⋃ j, (range (F j) \ ⋃ i, range (G j i))) ∪
    ⋃ j, ⋃ i, (range (G j i) \ ⋃ k, G j i '' O j i k)) ?_
    (measure_union_null (measure_union_null hM₀ (measure_iUnion_null hGnull))
      (measure_iUnion_null fun j => measure_iUnion_null (hOnull j)))
  rintro x ⟨hxM, hxΦ⟩
  rcases hMF hxM with hx0 | hxF
  · exact Or.inl (Or.inl hx0)
  obtain ⟨j, hj⟩ := mem_iUnion.1 hxF
  by_cases hGi : x ∈ ⋃ i, range (G j i)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hGi
    by_cases hOk : x ∈ ⋃ k, G j i '' O j i k
    · -- `x ∈ G_{ji}(O_{jik}) = Φ_m(Ω_m)` for `m = e⁻¹(j, i, k)`, which is excluded.
      obtain ⟨k, hk⟩ := mem_iUnion.1 hOk
      exfalso
      apply hxΦ
      refine mem_iUnion.2 ⟨e.symm (j, i, k), ?_⟩
      simpa only [Equiv.apply_symm_apply] using hk
    · exact Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨i, hi, hOk⟩⟩)
  · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, hj, hGi⟩))
/-- Simon Ch. 3, Lemma 1.2 ("only if", p. 70) and Remark 1.3: a countably `n`-rectifiable
`M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null set, by the images `Φ_j(Ω_j)` of countably many `C¹` maps
`Φ_j : ℝⁿ → ℝ^P` on open sets `Ω_j ⊆ ℝⁿ`, each Lipschitz and antilipschitz on `Ω_j`.  With
`M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` (Ch. 3, 1.1), `lpf_lipschitz_c1_immersion_pieces` for `F_j` gives `C¹` maps
`G_{j,k}`, antilipschitz on open `O_{j,k}`; Rademacher and the critical-image lemma
`slicing_im_st_cd_c1c_critical_image_null` show `Hⁿ(F_j(ℝⁿ) ∖ ⋃_k G_{j,k}(O_{j,k})) = 0`; the
charts are `G_{j,k}` on `O_{j,k} ∩ B_r(0)`, `r ∈ ℕ`. -/
theorem Submission.slicing_im_st_cd_c1_cover : ∀ (P n : ℕ) (M : Set (Eucl P)), CountablyRectifiable n M → ∃ (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧ (∀ j, ∃ K : ℝ≥0, LipschitzOnWith K (Φ j) (Ω j)) ∧ (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧ (μHE[n] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' Ω j) = 0 := by
  intro P n M hM
  -- `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and `F_j` `K_j`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hM
  choose K hK using hF
  -- The sibling lemma with `Ω = ℝⁿ`, `u = F_j`: `C¹` maps `G j k`, antilipschitz on the open
  -- `O j k`, with `F_j = G j k` on `E j k ⊆ O j k`; `Lⁿ`-a.e. point at which `F_j` has an injective
  -- derivative lies in `⋃_k E j k`.
  have hpieces := fun j => Submission.lpf_lipschitz_c1_immersion_pieces n P univ (F j) isOpen_univ
    (hK j).locallyLipschitz.locallyLipschitzOn
  choose G O E hOo hG hGc _ hEO _ hFG hae using hpieces
  -- `Hⁿ(F_j(ℝⁿ) ∖ ⋃_k G j k (O j k)) = 0`.
  have hnull : ∀ j, (μHE[n] : Measure (Eucl P)) (range (F j) \ ⋃ k, G j k '' O j k) = 0 := by
    intro j
    -- An `Lⁿ`-null `N` containing the points where `F_j` is not differentiable (Rademacher) and
    -- those where `F_j` has an injective derivative but which lie in no `E j k`.
    obtain ⟨N, hN0, hNd, hNE⟩ : ∃ N : Set (Eucl n), (volume : Measure (Eucl n)) N = 0 ∧
        (∀ w, ¬ DifferentiableAt ℝ (F j) w → w ∈ N) ∧
        (∀ w, DifferentiableAt ℝ (F j) w → Function.Injective (fderiv ℝ (F j) w) →
          w ∉ ⋃ k, E j k → w ∈ N) :=
      ⟨_, measure_union_null (ae_iff.1 ((hK j).ae_differentiableAt (μ := volume)))
        (ae_iff.1 (hae j)), fun w hw => Or.inl hw,
        fun w hd hi hwE => Or.inr fun h => hwE (h (mem_univ w) ⟨_, hd.hasFDerivAt, hi⟩)⟩
    -- `Hⁿ(F_j(N)) ≤ K_jⁿ Hⁿ(N) = K_jⁿ Lⁿ(N) = 0`.
    have hFN : (μHE[n] : Measure (Eucl P)) (F j '' N) = 0 := by
      refine nonpos_iff_eq_zero.1 ?_
      calc (μHE[n] : Measure (Eucl P)) (F j '' N)
          ≤ (K j : ℝ≥0∞) ^ n * (μHE[n] : Measure (Eucl n)) N :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (hK j).lipschitzOnWith
        _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hN0, mul_zero]
    -- `F_j(ℝⁿ) ∖ ⋃_k G j k (O j k) ⊆ F_j(N) ∪ F_j(C_j)`, `C_j` the critical set of `F_j`, whose
    -- image is `Hⁿ`-null.
    refine measure_mono_null ?_ (measure_union_null hFN
      (Submission.slicing_im_st_cd_c1c_critical_image_null n P (F j) (K j) (hK j)))
    rintro _ ⟨⟨w, rfl⟩, hw⟩
    -- `w ∉ ⋃_k E j k`, since otherwise `F_j(w) = G j k (w) ∈ G j k (O j k)`.
    have hwE : w ∉ ⋃ k, E j k := fun hwE => by
      obtain ⟨k, hk⟩ := mem_iUnion.1 hwE
      exact hw (mem_iUnion.2 ⟨k, w, (hEO j k hk).1, (hFG j k w hk).1.symm⟩)
    by_cases hd : DifferentiableAt ℝ (F j) w
    · by_cases hi : Function.Injective (fderiv ℝ (F j) w)
      · exact Or.inl (mem_image_of_mem _ (hNE w hd hi hwE))
      · exact Or.inr (mem_image_of_mem _ ⟨hd, hi⟩)
    · exact Or.inl (mem_image_of_mem _ (hNd w hd))
  -- The charts: `Φ_l = G j k` on `Ω_l = O j k ∩ B_r(0)` for `l ↔ (j, k, r)`.
  let idx : ℕ → ℕ × ℕ × ℕ := fun l => ((Nat.unpair l).1, Nat.unpair (Nat.unpair l).2)
  refine ⟨fun l => G (idx l).1 (idx l).2.1,
    fun l => O (idx l).1 (idx l).2.1 ∩ ball (0 : Eucl n) ((idx l).2.2 : ℝ),
    fun l => (hOo _ _).inter isOpen_ball, fun l => hG _ _, fun l => ?_, fun l => ?_, ?_⟩
  · -- `G j k` is `C¹`, hence Lipschitz on the compact convex `B̄_r(0) ⊇ Ω_l`.
    obtain ⟨C, hC⟩ := (hG (idx l).1 (idx l).2.1).contDiffOn.exists_lipschitzOnWith
      (s := closedBall (0 : Eucl n) ((idx l).2.2 : ℝ)) one_ne_zero (convex_closedBall _ _)
      (isCompact_closedBall _ _)
    exact ⟨C, hC.mono fun w hw => ball_subset_closedBall hw.2⟩
  · -- `G j k` is antilipschitz on `O j k ⊇ Ω_l`.
    obtain ⟨c, hc, hcO⟩ := hGc (idx l).1 (idx l).2.1
    exact ⟨c, hc, fun w hw w' hw' => hcO w hw.1 w' hw'.1⟩
  · -- `M ∖ ⋃_l Φ_l(Ω_l) ⊆ M₀ ∪ ⋃_j (F_j(ℝⁿ) ∖ ⋃_k G j k (O j k))`, a countable union of null sets.
    refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hnull))
    rintro x ⟨hxM, hx⟩
    rcases hMF hxM with hx0 | hxF
    · exact Or.inl hx0
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hxF
      refine Or.inr (mem_iUnion.2 ⟨j, hj, fun hxG => hx ?_⟩)
      -- `x = G j k (w)` with `w ∈ O j k`; for `r ∈ ℕ` with `|w| < r`, `w ∈ Ω_l`, `l ↔ (j, k, r)`.
      obtain ⟨k, w, hwO, rfl⟩ := mem_iUnion.1 hxG
      obtain ⟨r, hr⟩ := exists_nat_gt ‖w‖
      refine mem_iUnion.2 ⟨Nat.pair j (Nat.pair k r), w, ?_, ?_⟩ <;>
        simp only [idx, Nat.unpair_pair]
      exact ⟨hwO, mem_ball_zero_iff.2 hr⟩
/-- Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem), localized to a real function that is
Lipschitz on an open set `Ω`: McShane-extend `u|Ω` to a Lipschitz `g : ℝⁿ → ℝ`, apply the C¹
approximation theorem to `g` with `ε_k = 1 / (k + 1)` (sets `C_k`, `C¹` functions `h_k`) and take
`A_k = Ω ∩ C_k`.  Since `u = g` on the open set `Ω`, `u` has derivative `Dh_k` on `A_k`, and
`Lⁿ(Ω ∖ ⋃ A_l) ≤ Lⁿ(ℝⁿ ∖ C_k) < 1 / (k + 1)` for every `k`. -/
theorem Submission.slicing_im_st_cd_c1_pieces_of_lipschitzOn : ∀ (n : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → ℝ) (K : ℝ≥0), IsOpen Ω → LipschitzOnWith K u Ω → ∃ (h : ℕ → Eucl n → ℝ) (A : ℕ → Set (Eucl n)), (∀ k, ContDiff ℝ 1 (h k)) ∧ (∀ k, A k ⊆ Ω) ∧ (∀ k, ∀ w ∈ A k, u w = h k w ∧ HasFDerivAt u (fderiv ℝ (h k) w) w) ∧ (volume : Measure (Eucl n)) (Ω \ ⋃ k, A k) = 0 := by
  intro n Ω u K hΩ hu
  -- McShane: a `K`-Lipschitz `g : ℝⁿ → ℝ` with `u = g` on `Ω`.
  obtain ⟨g, hg, hug⟩ := hu.extend_real
  -- C¹ approximation of `g` with `ε_k = 1 / (k + 1)`: sets `C k` with `Lⁿ(ℝⁿ ∖ C k) < ε_k` and
  -- `C¹` functions `h k` with `g = h k` and `Dg = D(h k)` on `C k`.
  choose C h _ hC hh hgh using fun k : ℕ => Submission.lpf_c1_approximation_real n g K hg
    ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _))
  refine ⟨h, fun k => Ω ∩ C k, hh, fun k => inter_subset_left, fun k w hw => ?_, ?_⟩
  · -- On `A k = Ω ∩ C k`, `u = g = h k`; `u = g` near `w` since `Ω` is open, so `Du(w) = Dh_k(w)`.
    obtain ⟨hgw, hDw⟩ := hgh k w hw.2
    exact ⟨(hug hw.1).trans hgw,
      hDw.congr_of_eventuallyEq (hug.eventuallyEq_of_mem (hΩ.mem_nhds hw.1))⟩
  · -- `Ω ∖ ⋃ A ⊆ ℝⁿ ∖ C k`, so `Lⁿ(Ω ∖ ⋃ A) < 1 / (k + 1)` for every `k`; let `k → ∞`.
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto'
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) fun k => ?_)
    have hsub : Ω \ ⋃ l, Ω ∩ C l ⊆ (C k)ᶜ := fun w hw hwC => hw.2 (mem_iUnion.2 ⟨k, hw.1, hwC⟩)
    exact (measure_mono hsub).trans (hC k).le
/-- Simon Ch. 2, 4.7/4.10 (used for Ch. 6, 3.9): if `f` is `K`-Lipschitz on a neighbourhood `V`
of `Φ(w)` and both `Φ` and `f ∘ Φ` are differentiable at `w`, then `t ↦ f(Φ(w) + t DΦ(w)s)` has
derivative `D(f∘Φ)(w)s` at `0`.  For small `t` it differs from `t ↦ f(Φ(w + ts))` by at most
`K ‖Φ(w + ts) - Φ(w) - t DΦ(w)s‖ = o(t)`, and the latter map has derivative `D(f∘Φ)(w)s`. -/
theorem Submission.lpf_ccr_hasDerivAt_line_of_comp : ∀ (n P Q : ℕ) (f : Eucl P → Eucl Q) (Φ : Eucl n → Eucl P) (w : Eucl n), (∃ K : ℝ≥0, ∃ V ∈ 𝓝 (Φ w), LipschitzOnWith K f V) → DifferentiableAt ℝ Φ w → DifferentiableAt ℝ (f ∘ Φ) w → ∀ s : Eucl n, HasDerivAt (fun t : ℝ => f (Φ w + t • fderiv ℝ Φ w s)) (fderiv ℝ (f ∘ Φ) w s) 0 := by
  rintro n P Q f Φ w ⟨K, V, hV, hfV⟩ hΦ hfΦ s
  -- The line `ℓ(t) = w + t s` has derivative `s` at `0`.
  have hℓ : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
  have hℓ0 : w = w + (0 : ℝ) • s := by simp
  -- Chain rule along `ℓ`: `t ↦ Φ(w + t s)` has derivative `DΦ(w)s` and `t ↦ f(Φ(w + t s))` has
  -- derivative `D(f∘Φ)(w)s` at `0`.
  have hφ : HasDerivAt (fun t : ℝ => Φ (w + t • s)) (fderiv ℝ Φ w s) 0 :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0
  have hg : HasDerivAt (fun t : ℝ => f (Φ (w + t • s))) (fderiv ℝ (f ∘ Φ) w s) 0 :=
    hfΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0
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
  -- Hence `h(t) := f(Φ(w) + t DΦ(w)s) - f(Φ(w + t s)) = O(Φ(w + t s) - Φ(w) - t DΦ(w)s) = o(t)`.
  have hO : (fun t : ℝ => f (Φ w + t • fderiv ℝ Φ w s) - f (Φ (w + t • s))) =O[𝓝 0]
      fun t : ℝ => Φ (w + t • s) - Φ w - t • fderiv ℝ Φ w s := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [h₁, h₂] with t ht₁ ht₂
    have hK := hfV.dist_le_mul _ ht₁ _ ht₂
    rw [dist_eq_norm, dist_eq_norm] at hK
    rw [sub_sub, norm_sub_rev (Φ (w + t • s))]
    exact hK
  -- `h(0) = 0`, so `h` has derivative `0` at `0`.
  have hh : HasDerivAt (fun t : ℝ => f (Φ w + t • fderiv ℝ Φ w s) - f (Φ (w + t • s))) 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa using hO.trans_isLittleO hrem
  -- `f(Φ(w) + t DΦ(w)s) = f(Φ(w + t s)) + h(t)`.
  have hsum := hg.add hh
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp
/-- Adapted frame of a nonzero functional (step 1 of the regular level-set charts used for slices
of a rectifiable triple, Simon Ch. 6, 4.1–4.4): for `ℓ ≠ 0` on `ℝ^{m+1}` there are a
norm-preserving `ι : ℝ^m → ℝ^{m+1}` onto `ker ℓ`, a vector `e ⟂ range ι` with `ℓ e = 1`, and `p`
with `ι (p u) + ℓ u • e = u`.  Take `e = ‖a‖⁻² • a` for the Riesz vector `a` of `ℓ`, `ι` from an
orthonormal basis of `ker ℓ` (dimension `m` by rank–nullity) and `p u = ι⁻¹ (u - ℓ u • e)`. -/
theorem Submission.slicing_im_st_lsc_kernel_frame :
    ∀ (m : ℕ) (ℓ : Eucl (m + 1) →L[ℝ] ℝ), ℓ ≠ 0 → ∃ (ι : Eucl m →L[ℝ] Eucl (m + 1)) (p : Eucl (m + 1) →L[ℝ] Eucl m) (e : Eucl (m + 1)), ℓ e = 1 ∧ (∀ v, ‖ι v‖ = ‖v‖) ∧ (∀ v, inner ℝ (ι v) e = 0) ∧ ∀ u, ι (p u) + ℓ u • e = u := by
  intro m ℓ hℓ
  -- Riesz vector `a` of `ℓ` (`ℓ u = ⟪a, u⟫`) and `e := ‖a‖⁻² • a`, so that `ℓ e = 1`.
  set a : Eucl (m + 1) := (InnerProductSpace.toDual ℝ (Eucl (m + 1))).symm ℓ with ha
  have hℓa : ∀ u, ℓ u = inner ℝ a u := fun u => by
    rw [ha, InnerProductSpace.toDual_symm_apply]
  have ha0 : a ≠ 0 := by
    intro h0
    apply hℓ
    ext u
    simp [hℓa, h0]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha0
  set e : Eucl (m + 1) := (‖a‖ ^ 2)⁻¹ • a with he
  have hℓe : ℓ e = 1 := by
    rw [hℓa, he, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  -- `K := ker ℓ` has dimension `m`: `ℓ` maps onto `ℝ`, then rank–nullity.
  set K : Submodule ℝ (Eucl (m + 1)) := LinearMap.ker ℓ.toLinearMap with hKdef
  have htop : LinearMap.range ℓ.toLinearMap = ⊤ := by
    obtain ⟨u, hu⟩ : ∃ u, ℓ u ≠ 0 := by
      by_contra hcon
      apply hℓ
      ext u
      by_contra hu
      exact hcon ⟨u, by simpa using hu⟩
    rw [eq_top_iff]
    rintro y -
    refine ⟨(y / ℓ u) • u, ?_⟩
    simp [hu]
  have hK : Module.finrank ℝ K = m := by
    rw [hKdef]
    have hrn := LinearMap.finrank_range_add_finrank_ker ℓ.toLinearMap
    rw [htop, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hrn
    omega
  -- A linear isometry `J : ℝ^m ≃ K` from an orthonormal basis of `K` indexed by `Fin m`;
  -- `ι := (K ↪ ℝ^{m+1}) ∘ J` and `p u := J⁻¹ (u - ℓ u • e)`.
  let J : Eucl m ≃ₗᵢ[ℝ] K := ((stdOrthonormalBasis ℝ K).reindex (finCongr hK)).repr.symm
  let ι : Eucl m →L[ℝ] Eucl (m + 1) :=
    K.subtypeL.comp J.toContinuousLinearEquiv.toContinuousLinearMap
  have hιK : ∀ v, ι v ∈ K := fun v => (J v).2
  have hmemK : ∀ u, u - ℓ u • e ∈ K := by
    intro u
    simp [hKdef, LinearMap.mem_ker, hℓe]
  let q : Eucl (m + 1) →L[ℝ] K :=
    (ContinuousLinearMap.id ℝ (Eucl (m + 1)) - ℓ.smulRight e).codRestrict K (by
      intro u
      simpa using hmemK u)
  let p : Eucl (m + 1) →L[ℝ] Eucl m :=
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp q
  refine ⟨ι, p, e, hℓe, ?_, ?_, ?_⟩
  · intro v
    show ‖((J v : K) : Eucl (m + 1))‖ = ‖v‖
    rw [Submodule.norm_coe, LinearIsometryEquiv.norm_map]
  · intro v
    have h1 : ℓ (ι v) = 0 := hιK v
    rw [hℓa] at h1
    rw [he, inner_smul_right, real_inner_comm, h1, mul_zero]
  · intro u
    show ((J (J.symm (q u)) : K) : Eucl (m + 1)) + ℓ u • e = u
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp [q]
/-- `C¹` germ extension (steps 1–2 of the level-set chart construction for Simon Ch. 6, 4.6): if
`g` is `C¹` at `x`, then some `g'` that is `C¹` on all of `ℝ^m` agrees with `g` on a ball
`B(x, ρ)`.  Take `ε` with `g` `C¹` on `B(x, ε)`, `ρ = ε / 3`, a bump `χ` with `χ = 1` on
`B̄(x, ρ)` and `χ = 0` off `B(x, 2ρ)`, and `g' = χ g`. -/
theorem Submission.slicing_im_st_lsc_c1_extension :
    ∀ (m : ℕ) (g : Eucl m → ℝ) (x : Eucl m), ContDiffAt ℝ 1 g x → ∃ ρ : ℝ, 0 < ρ ∧ ∃ g' : Eucl m → ℝ, ContDiff ℝ 1 g' ∧ ∀ v ∈ ball x ρ, g' v = g v := by
  intro m g x hg
  -- `g` is `C¹` at every point of some ball `B(x, ε)` (`ContDiffAt.eventually`); `ρ := ε / 3`.
  have hev := hg.eventually (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
  set ρ := ε / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  -- Bump `χ` with `χ = 1` on `closedBall x ρ` and `χ = 0` off `ball x (2ρ)`; `g' := χ * g`.
  let χ : ContDiffBump x := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  refine ⟨ρ, hρ, fun y => χ y * g y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : dist y x < ε
    · exact χ.contDiffAt.mul (hball hy)
    · -- Off `B(x, ε)`, `g'` vanishes on the open neighbourhood `{z | 2ρ < |z - x|}` of `y`.
      have hopen : IsOpen {z : Eucl m | 2 * ρ < dist z x} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hy2 : 2 * ρ < dist y x := by
        have := not_lt.1 hy
        linarith
      have hzero : (fun y => χ y * g y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds hy2] with z hz
        have : χ z = 0 := χ.zero_of_le_dist (le_of_lt hz)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro v hv
    have : χ v = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hv)
    simp [this]
/-- Local graph chart of a regular level set (implicit-function step of the level-set charts used
for integer multiplicity slices, Simon Ch. 6, §4): if `h` is `C¹`, `U` is open, `w₀ ∈ U` and
`Dh(w₀) ≠ 0`, then a `C¹` map `ψ : ℝ^m → ℝ^{m+1}` with `‖v - v'‖ ≤ ‖ψ v - ψ v'‖` maps `B(0, r)`
into `U ∩ {h = h(w₀), Dh ≠ 0}` and onto the level set inside an open `W ∋ w₀`.  With the frame
`(ι, p, e)` of `Dh(w₀)` (`slicing_im_st_lsc_kernel_frame`), `ψ v = w₀ + ι v + g̃ v • e`, where
`g̃` is a `C¹` extension (`slicing_im_st_lsc_c1_extension`) of the implicit function `g` of
`H (v, s) = h (w₀ + ι v + s • e)`, obtained from the inverse function theorem for
`Φ (v, s) = (v, H (v, s))`. -/
theorem Submission.slicing_im_st_lsc_local_graph :
    ∀ (m : ℕ) (h : Eucl (m + 1) → ℝ) (U : Set (Eucl (m + 1))) (w₀ : Eucl (m + 1)), ContDiff ℝ 1 h → IsOpen U → w₀ ∈ U → fderiv ℝ h w₀ ≠ 0 → ∃ (ψ : Eucl m → Eucl (m + 1)) (r : ℝ) (W : Set (Eucl (m + 1))), ContDiff ℝ 1 ψ ∧ 0 < r ∧ IsOpen W ∧ w₀ ∈ W ∧ (∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖) ∧ (∀ v ∈ ball (0 : Eucl m) r, ψ v ∈ U ∧ h (ψ v) = h w₀ ∧ fderiv ℝ h (ψ v) ≠ 0) ∧ ∀ w ∈ W, h w = h w₀ → ∃ v ∈ ball (0 : Eucl m) r, ψ v = w := by
  have hKF := Submission.slicing_im_st_lsc_kernel_frame
  have hC1E := Submission.slicing_im_st_lsc_c1_extension
  intro m h U w₀ hh hU hw₀ hdh
  -- Frame of `ℓ := Dh(w₀)`: `ℓ e = 1`, `ι` isometric, `ι v ⟂ e` and `ι (p u) + ℓ u • e = u`.
  obtain ⟨ι, p, e, hℓe, hιn, hιe, hdec⟩ := hKF m (fderiv ℝ h w₀) hdh
  set ℓ := fderiv ℝ h w₀ with hℓdef
  -- `A (v, s) = w₀ + ι v + s • e` and `H := h ∘ A`, with `DH(0, 0) = ℓ ∘ L`.
  let L : Eucl m × ℝ →L[ℝ] Eucl (m + 1) :=
    ι.comp (ContinuousLinearMap.fst ℝ (Eucl m) ℝ) +
      (ContinuousLinearMap.snd ℝ (Eucl m) ℝ).smulRight e
  let A : Eucl m × ℝ → Eucl (m + 1) := fun q => w₀ + L q
  have hAapp : ∀ q : Eucl m × ℝ, A q = w₀ + ι q.1 + q.2 • e := by
    intro q
    simp [A, L, add_assoc]
  let H : Eucl m × ℝ → ℝ := fun q => h (A q)
  have hAd : ∀ q, HasFDerivAt A L q := fun q => (L.hasFDerivAt).const_add w₀
  have hA0 : A (0, 0) = w₀ := by
    rw [hAapp]
    simp
  have hH : ContDiff ℝ 1 H := hh.comp (contDiff_const.add L.contDiff)
  have hHd : HasFDerivAt H (ℓ.comp L) ((0 : Eucl m), (0 : ℝ)) := by
    have h1 := (hh.differentiable one_ne_zero (A (0, 0))).hasFDerivAt.comp ((0 : Eucl m), (0 : ℝ))
      (hAd (0, 0))
    rw [hA0] at h1
    exact h1
  -- `Φ (v, s) := (v, H (v, s))` has derivative `Φ₀ (v, s) = (v, ℓ (ι v) + s)` at `(0, 0)`, an
  -- equivalence with inverse `Ψ₀ (v, t) = (v, t - ℓ (ι v))`.
  let Φ : Eucl m × ℝ → Eucl m × ℝ := fun q => (q.1, H q)
  have hΦC : ContDiff ℝ 1 Φ := contDiff_fst.prodMk hH
  let Φ₀ : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ :=
    (ContinuousLinearMap.fst ℝ (Eucl m) ℝ).prod (ℓ.comp L)
  let Ψ₀ : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ :=
    (ContinuousLinearMap.fst ℝ (Eucl m) ℝ).prod
      (ContinuousLinearMap.snd ℝ (Eucl m) ℝ - (ℓ.comp ι).comp (ContinuousLinearMap.fst ℝ (Eucl m) ℝ))
  have hleft : Function.LeftInverse Ψ₀ Φ₀ := by
    rintro ⟨v, s⟩
    simp [Φ₀, Ψ₀, L, hℓe]
  have hright : Function.RightInverse Ψ₀ Φ₀ := by
    rintro ⟨v, t⟩
    simp [Φ₀, Ψ₀, L, hℓe]
  let Φ₀e : (Eucl m × ℝ) ≃L[ℝ] Eucl m × ℝ := ContinuousLinearEquiv.equivOfInverse Φ₀ Ψ₀ hleft hright
  have hΦd : HasFDerivAt Φ (Φ₀e : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ) ((0 : Eucl m), (0 : ℝ)) :=
    hasFDerivAt_fst.prodMk hHd
  have hΦs : HasStrictFDerivAt Φ (Φ₀e : (Eucl m × ℝ) →L[ℝ] Eucl m × ℝ) ((0 : Eucl m), (0 : ℝ)) := by
    have h1 := hΦC.contDiffAt.hasStrictFDerivAt (x := ((0 : Eucl m), (0 : ℝ))) one_ne_zero
    rwa [hΦd.fderiv] at h1
  -- Inverse function theorem: `Φ` is a local homeomorphism `T` near `(0, 0)` with `C¹` inverse.
  let T := hΦs.toOpenPartialHomeomorph Φ
  have hsrc : ((0 : Eucl m), (0 : ℝ)) ∈ T.source := hΦs.mem_toOpenPartialHomeomorph_source
  have htgt : ((0 : Eucl m), H ((0 : Eucl m), (0 : ℝ))) ∈ T.target :=
    hΦs.image_mem_toOpenPartialHomeomorph_target
  have hT0 : T.symm ((0 : Eucl m), H ((0 : Eucl m), (0 : ℝ))) = ((0 : Eucl m), (0 : ℝ)) :=
    T.left_inv hsrc
  have hTC : ContDiffAt ℝ 1 T.symm ((0 : Eucl m), H ((0 : Eucl m), (0 : ℝ))) := by
    refine T.contDiffAt_symm (f₀' := Φ₀e) htgt ?_ ?_
    · rw [hT0]
      exact hΦd
    · rw [hT0]
      exact hΦC.contDiffAt
  -- Implicit function `g v := (T⁻¹ (v, H (0, 0))).2`: `g 0 = 0`, `g` is `C¹` at `0` and, near
  -- `(0, 0)`, `H (v, s) = H (0, 0) ↔ g v = s`.
  let g : Eucl m → ℝ := fun v => (T.symm (v, H ((0 : Eucl m), (0 : ℝ)))).2
  have hg0 : g 0 = 0 := by
    simp only [g, hT0]
  have hgC1 : ContDiffAt ℝ 1 g 0 := by
    have hin : ContDiffAt ℝ 1 (fun v : Eucl m => (v, H ((0 : Eucl m), (0 : ℝ)))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    exact contDiffAt_snd.comp (0 : Eucl m)
      (ContDiffAt.comp (f := fun v : Eucl m => (v, H ((0 : Eucl m), (0 : ℝ)))) (0 : Eucl m) hTC hin)
  have hiff : ∀ᶠ q in 𝓝 ((0 : Eucl m), (0 : ℝ)), H q = H ((0 : Eucl m), (0 : ℝ)) ↔ g q.1 = q.2 := by
    have hsrc' : ∀ᶠ q in 𝓝 ((0 : Eucl m), (0 : ℝ)), q ∈ T.source := T.open_source.mem_nhds hsrc
    have htgt' : ∀ᶠ q in 𝓝 ((0 : Eucl m), (0 : ℝ)),
        (q.1, H ((0 : Eucl m), (0 : ℝ))) ∈ T.target :=
      (continuous_fst.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (T.open_target.mem_nhds htgt)
    filter_upwards [hsrc', htgt'] with q hq1 hq2
    constructor
    · intro hq
      have hΦq : T q = (q.1, H ((0 : Eucl m), (0 : ℝ))) := Prod.ext rfl hq
      show (T.symm (q.1, H ((0 : Eucl m), (0 : ℝ)))).2 = q.2
      rw [← hΦq, T.left_inv hq1]
    · intro hq
      have hr : Φ (T.symm (q.1, H ((0 : Eucl m), (0 : ℝ)))) = (q.1, H ((0 : Eucl m), (0 : ℝ))) :=
        T.right_inv hq2
      have hr1 := congrArg Prod.fst hr
      have hr2 := congrArg Prod.snd hr
      have hq' : T.symm (q.1, H ((0 : Eucl m), (0 : ℝ))) = q := Prod.ext hr1 hq
      rw [hq'] at hr2
      exact hr2
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 hiff
  -- `g' = g` on `B(0, ρ)` is `C¹` on `ℝ^m`, and `ψ v := w₀ + ι v + g' v • e`.
  obtain ⟨ρ, hρ, g', hg'C, hg'eq⟩ := hC1E m g 0 hgC1
  let ψ : Eucl m → Eucl (m + 1) := fun v => w₀ + ι v + g' v • e
  have hψC : ContDiff ℝ 1 ψ := (contDiff_const.add ι.contDiff).add (hg'C.smul contDiff_const)
  have hψ0 : ψ 0 = w₀ := by
    simp [ψ, hg'eq 0 (mem_ball_self hρ), hg0]
  -- (i) Pythagoras: `‖ψ v - ψ v'‖² = ‖v - v'‖² + ‖(g' v - g' v') • e‖²`.
  have hanti : ∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖ := by
    intro v v'
    have hdiff : ψ v - ψ v' = ι (v - v') + (g' v - g' v') • e := by
      simp only [ψ, map_sub, sub_smul]
      abel
    have horth : inner ℝ (ι (v - v')) ((g' v - g' v') • e) = 0 := by
      rw [inner_smul_right, hιe, mul_zero]
    have hsq : ‖ψ v - ψ v'‖ ^ 2 = ‖v - v'‖ ^ 2 + ‖(g' v - g' v') • e‖ ^ 2 := by
      rw [hdiff, norm_add_sq_real, horth, hιn]
      ring
    have hle : ‖v - v'‖ ^ 2 ≤ ‖ψ v - ψ v'‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ‖(g' v - g' v') • e‖]
    exact le_of_sq_le_sq hle (norm_nonneg _)
  -- `r := min r₀ (min ρ ε)`, where `ψ (B(0, r₀)) ⊆ U ∩ {Dh ≠ 0}` and `|g| < ε` on `B(0, r₀)`.
  have hopen : IsOpen (U ∩ {w | fderiv ℝ h w ≠ 0}) :=
    hU.inter (isOpen_ne_fun (hh.continuous_fderiv one_ne_zero) continuous_const)
  have h1 : ∀ᶠ v in 𝓝 (0 : Eucl m), ψ v ∈ U ∩ {w | fderiv ℝ h w ≠ 0} := by
    apply hψC.continuous.continuousAt.preimage_mem_nhds
    rw [hψ0]
    exact hopen.mem_nhds ⟨hw₀, hdh⟩
  have h2 : ∀ᶠ v in 𝓝 (0 : Eucl m), g v ∈ ball (0 : ℝ) ε := by
    apply hgC1.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact ball_mem_nhds _ hε
  obtain ⟨r₀, hr₀, hr₀ball⟩ := Metric.mem_nhds_iff.1 (h1.and h2)
  set r := min r₀ (min ρ ε) with hrdef
  have hr : 0 < r := lt_min hr₀ (lt_min hρ hε)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  -- `W := {w | p (w - w₀) ∈ B(0, r), |ℓ (w - w₀)| < ε}`; by the frame,
  -- `A (p (w - w₀), ℓ (w - w₀)) = w`.
  let W : Set (Eucl (m + 1)) := {w | p (w - w₀) ∈ ball (0 : Eucl m) r ∧ ℓ (w - w₀) ∈ ball (0 : ℝ) ε}
  have hWo : IsOpen W := by
    apply IsOpen.inter
    · exact isOpen_ball.preimage (p.continuous.comp (continuous_id.sub continuous_const))
    · exact isOpen_ball.preimage (ℓ.continuous.comp (continuous_id.sub continuous_const))
  have hw₀W : w₀ ∈ W := by
    simp [W, hr, hε]
  refine ⟨ψ, r, W, hψC, hr, hWo, hw₀W, hanti, ?_, ?_⟩
  -- (ii) For `v ∈ B(0, r)`: `(v, g v) ∈ B((0, 0), ε)` and `ψ v = A (v, g v)`.
  · intro v hv
    have hvr₀ : v ∈ ball (0 : Eucl m) r₀ := ball_subset_ball hrr₀ hv
    obtain ⟨⟨hU', hd'⟩, hgv⟩ := hr₀ball hvr₀
    refine ⟨hU', ?_, hd'⟩
    have hvρ : v ∈ ball (0 : Eucl m) ρ := ball_subset_ball hrρ hv
    have hvε : v ∈ ball (0 : Eucl m) ε := ball_subset_ball hrε hv
    have hq : ((v, g v) : Eucl m × ℝ) ∈ ball ((0 : Eucl m), (0 : ℝ)) ε := by
      rw [← ball_prod_same]
      exact ⟨hvε, hgv⟩
    have hHq : H (v, g v) = H ((0 : Eucl m), (0 : ℝ)) := (hεball hq).2 rfl
    have hψv : ψ v = A (v, g v) := by
      rw [hAapp]
      simp [ψ, hg'eq v hvρ]
    rw [hψv]
    simpa [H, hA0] using hHq
  -- (iii) For `w ∈ W` on the level set, `v := p (w - w₀)` has `g v = ℓ (w - w₀)`, so `ψ v = w`.
  · intro w hw hhw
    obtain ⟨hpw, hℓw⟩ := hw
    have hAw : A (p (w - w₀), ℓ (w - w₀)) = w := by
      rw [hAapp]
      have := hdec (w - w₀)
      simp only at this ⊢
      rw [add_assoc, this]
      abel
    have hvε : p (w - w₀) ∈ ball (0 : Eucl m) ε := ball_subset_ball hrε hpw
    have hq : ((p (w - w₀), ℓ (w - w₀)) : Eucl m × ℝ) ∈ ball ((0 : Eucl m), (0 : ℝ)) ε := by
      rw [← ball_prod_same]
      exact ⟨hvε, hℓw⟩
    have hHq : H (p (w - w₀), ℓ (w - w₀)) = H ((0 : Eucl m), (0 : ℝ)) := by
      simp only [H]
      rw [hAw, hA0]
      exact hhw
    have hgs : g (p (w - w₀)) = ℓ (w - w₀) := (hεball hq).1 hHq
    refine ⟨p (w - w₀), hpw, ?_⟩
    have hvρ : p (w - w₀) ∈ ball (0 : Eucl m) ρ := ball_subset_ball hrρ hpw
    calc ψ (p (w - w₀)) = w₀ + ι (p (w - w₀)) + g' (p (w - w₀)) • e := rfl
      _ = w₀ + ι (p (w - w₀)) + ℓ (w - w₀) • e := by rw [hg'eq _ hvρ, hgs]
      _ = A (p (w - w₀), ℓ (w - w₀)) := (hAapp (p (w - w₀), ℓ (w - w₀))).symm
      _ = w := hAw
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

/-- Weighted approximate tangent plane along a `C¹` chart (Simon Ch. 3, proof of 1.6 "⇒",
Remarks 1.5(2) and 1.8(1); used for the tangential gradient in Ch. 6, 4.6–4.7): if `Φ` is `C¹`
and antilipschitz on the open set `Ω`, then for `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)` and `w ∈ Ω` with
`Φ w = y`, `DΦ(w)(ℝⁿ)` is the approximate tangent space of `M` with respect to `θ` at `y`.
Cover `M` up to an `Hⁿ`-null set by compact pieces `C k` on which `θ` is continuous; at
`Hⁿ`-a.e. `y ∈ C k ∩ Φ(Ω)` the sets `C k ∖ Φ(Ω)`, `Φ(Ω) ∖ C k` and the weight `θ` on `M ∖ C k`
have `n`-density `0`, so the tangent plane of `Φ(Ω)` passes to `C k` and then to `(M, θ)`. -/
theorem Submission.slicing_im_tg_weighted_tangent_chart :
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
  -- Off a countable union of null sets, every `y ∈ M ∩ N` lies in some `C k` with all three.
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
  -- Off a countable union of null sets, every `y ∈ M ∩ N` lies in some `C k` with all three.
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
/-- Weighted approximate tangent planes on a `C¹` antilipschitz chart (Simon Ch. 3, proof of 1.6
"⇒" and Remark 1.8(1); used for the tangent planes of `M` and of the level sets `M_t` in Ch. 6,
4.1(2) and 4.4): for `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)` and every `w ∈ Ω` with `Φ w = y`, `DΦ(w)(ℝⁿ)` is
the approximate tangent space of `M` with respect to `θ` at `y`.  Cover `M` up to an `Hⁿ`-null
set by compact pieces `C k` on which `θ` is continuous (Lusin).  At `Hⁿ`-a.e. `y ∈ C k ∩ Φ(Ω)`
the upper density theorem makes `Hⁿ ⌞ (C k ∖ Φ(Ω))`, `Hⁿ ⌞ (Φ(Ω) ∖ C k)` and `θ Hⁿ ⌞ (M ∖ C k)`
of `n`-density `0`, so the tangent plane of the chart image `Φ(Ω)` at `y` passes first to `C k`
and then to `(M, θ)`. -/
theorem Submission.slicing_im_st_weighted_tangent_on_c1_chart :
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
  -- Step 0: the chart image `N = Φ(Ω)` is Borel and locally `Hⁿ`-finite.
  obtain ⟨hNm, hNfin⟩ :=
    Submission.lpf_wtc_chart_image_measurable_locally_finite Q n Φ Ω hΩ hΦ hanti
  -- Step 1: compact pieces `C k ⊆ M` with `θ|C k` continuous and `Hⁿ(C k) < ∞`, covering `M`
  -- up to an `Hⁿ`-null set.
  obtain ⟨C, hCcpt, hCM, hθC, hCfin, hMnull⟩ :=
    Submission.lpf_wtc_lusin_compact_pieces Q n V M θ hV hMV hM hθ hθK
  have hCm : ∀ k, MeasurableSet (C k) := fun k => (hCcpt k).isClosed.measurableSet
  -- Step 2 (i): `Hⁿ ⌞ (C k ∖ N)` has `n`-density `0` at `Hⁿ`-a.e. point outside `C k ∖ N`.
  have hd₁ := fun k => Submission.lpf_wtc_ae_zero_density_off_set Q n univ (C k \ Φ '' Ω)
    (fun _ => 1) isOpen_univ ((hCm k).diff hNm).nullMeasurableSet fun K _ _ => by
      rw [setLIntegral_one]
      exact (measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt (hCfin k)
  -- Step 2 (ii): `Hⁿ ⌞ (N ∖ C k)` has `n`-density `0` at `Hⁿ`-a.e. point outside `N ∖ C k`.
  have hd₂ := fun k => Submission.lpf_wtc_ae_zero_density_off_set Q n univ (Φ '' Ω \ C k)
    (fun _ => 1) isOpen_univ (hNm.diff (hCm k)).nullMeasurableSet fun K hK _ => by
      rw [setLIntegral_one]
      exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hNfin K hK)
  -- Step 3: `θ Hⁿ ⌞ (M ∖ C k)` has `n`-density `0` at `Hⁿ`-a.e. point of `V ∖ (M ∖ C k)`.
  have hd₃ := fun k => Submission.lpf_wtc_ae_zero_density_off_set Q n V (M \ C k)
    (fun x => ENNReal.ofReal (θ x)) hV (hM.diff (hCm k).nullMeasurableSet) fun K hK hKV =>
      (lintegral_mono_set (inter_subset_inter_left K sdiff_subset)).trans_lt
        (hθK K hK hKV).setLIntegral_lt_top
  -- Step 5: the exceptional sets are a countable union of `Hⁿ`-null sets.
  have hgood := ae_all_iff.2 fun k => (hd₁ k).and ((hd₂ k).and (hd₃ k))
  rw [ae_restrict_iff'₀ (hM.inter hNm.nullMeasurableSet)]
  filter_upwards [hgood, measure_eq_zero_iff_ae_notMem.1 hMnull] with y hy hycov hyMN w hw hwy
  subst hwy
  obtain ⟨k, hk⟩ : ∃ k, Φ w ∈ C k := by
    by_contra hnot
    exact hycov ⟨hyMN.1, fun h => hnot (mem_iUnion.1 h)⟩
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy k
  -- Step 2: `N` has approximate tangent space `DΦ(w)(ℝⁿ)` at `Φ w`, hence so does `C k`.
  have hCtan := Submission.lpf_wtc_tangent_transfer Q n (C k) (Φ '' Ω) (Φ w) _
    (hCm k).nullMeasurableSet hNm.nullMeasurableSet
    (Submission.lpf_wtc_chart_approx_tangent Q n Φ Ω hΩ hΦ hanti w hw)
    ⟨1, one_pos, hNfin _ (isCompact_closedBall _ _)⟩
    (by simpa only [setLIntegral_one] using hy₁ (mem_univ _) fun h => h.2 hyMN.2)
    (by simpa only [setLIntegral_one] using hy₂ (mem_univ _) fun h => h.2 hk)
  -- Step 4: weighted blow-up of `(M, θ)` on a closed ball about `Φ w` contained in `V`.
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV _ (hMV hyMN.1)
  exact Submission.lpf_wtc_weighted_tangent_transfer Q n M (C k) θ (Φ w) _ hM
    (hCm k).nullMeasurableSet (hCM k) hk (fun x hx => (hθ x hx).le) hCtan
    ⟨ε / 2, half_pos hε, (measure_mono inter_subset_left).trans_lt (hCfin k),
      hθK _ (isCompact_closedBall _ _) ((closedBall_subset_ball (half_lt_self hε)).trans hεV)⟩
    ((hθC k).continuousWithinAt hk) (hy₃ (hMV hyMN.1) fun h => h.2 hk)
/-- Rademacher on a Lipschitz chart (Simon Ch. 2, 1.4 and 1.8(i)): for `f` locally Lipschitz on
an open `U` and `Φ` `K`-Lipschitz on an open `Ω ⊆ ℝⁿ`, the `Φ`-image of the set of `w ∈ Ω` with
`Φ w ∈ U` at which `f ∘ Φ` is not differentiable is `Hⁿ`-null. -/
theorem Submission.lpf_tde_chart_nondiff_image_null :
    ∀ (P Q n : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q) (Φ : Eucl n → Eucl P)
      (Ω : Set (Eucl n)) (K : ℝ≥0), IsOpen U → LocallyLipschitzOn U f → IsOpen Ω →
      LipschitzOnWith K Φ Ω →
      (μHE[n] : Measure (Eucl P))
        (Φ '' {w | w ∈ Ω ∧ Φ w ∈ U ∧ ¬ DifferentiableAt ℝ (f ∘ Φ) w}) = 0 := by
  intro P Q n U f Φ Ω K hU hf hΩ hΦ
  -- Each `w ∈ Ω ∩ Φ⁻¹(U)` has an open `V ∋ w`, `V ⊆ Ω`, on which `f ∘ Φ` is Lipschitz.
  have hloc : ∀ w ∈ Ω ∩ Φ ⁻¹' U, ∃ V : Set (Eucl n), IsOpen V ∧ w ∈ V ∧ V ⊆ Ω ∧
      ∃ C : ℝ≥0, LipschitzOnWith C (f ∘ Φ) V := by
    rintro w ⟨hwΩ, hwU⟩
    obtain ⟨C, t, ht, hft⟩ := hf hwU
    rw [hU.nhdsWithin_eq hwU] at ht
    have hcont : ContinuousAt Φ w := hΦ.continuousOn.continuousAt (hΩ.mem_nhds hwΩ)
    have hmem : Ω ∩ Φ ⁻¹' t ∈ 𝓝 w := inter_mem (hΩ.mem_nhds hwΩ) (hcont.preimage_mem_nhds ht)
    obtain ⟨V, hVsub, hVo, hwV⟩ := _root_.mem_nhds_iff.1 hmem
    exact ⟨V, hVo, hwV, fun y hy => (hVsub hy).1,
      C * K, hft.comp (hΦ.mono fun y hy => (hVsub hy).1) fun y hy => (hVsub hy).2⟩
  choose! V hVo hwV hVΩ C hC using hloc
  -- Countably many of the `V w` cover `Ω ∩ Φ⁻¹(U)` (Lindelöf).
  obtain ⟨T, hTsub, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable (Ω ∩ Φ ⁻¹' U) V fun w hw => hVo w hw
  -- Rademacher on each `V w`: the non-differentiability set of `f ∘ Φ` is Lebesgue-null.
  have hZ : (volume : Measure (Eucl n))
      {w | w ∈ Ω ∧ Φ w ∈ U ∧ ¬ DifferentiableAt ℝ (f ∘ Φ) w} = 0 := by
    have hcover : {w | w ∈ Ω ∧ Φ w ∈ U ∧ ¬ DifferentiableAt ℝ (f ∘ Φ) w} ⊆
        ⋃ w ∈ T, {y | y ∈ V w ∧ ¬ DifferentiableAt ℝ (f ∘ Φ) y} := by
      rintro y ⟨hyΩ, hyU, hyd⟩
      have hy : y ∈ ⋃ w ∈ T, V w := hTU ▸ mem_biUnion ⟨hyΩ, hyU⟩ (hwV y ⟨hyΩ, hyU⟩)
      obtain ⟨w, hwT, hyV⟩ := mem_iUnion₂.1 hy
      exact mem_biUnion hwT ⟨hyV, hyd⟩
    refine measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 fun w hwT => ?_)
    have hw := hTsub hwT
    have hR := (hC w hw).ae_differentiableWithinAt_of_mem (μ := (volume : Measure (Eucl n)))
    rw [ae_iff] at hR
    refine measure_mono_null (fun y hy => ?_) hR
    obtain ⟨hyV, hyd⟩ := hy
    exact fun h => hyd ((h hyV).differentiableAt ((hVo w hw).mem_nhds hyV))
  -- `μHE[n] = volume` on `ℝⁿ`, and the Lipschitz image bound `Hⁿ(Φ(Z)) ≤ Kⁿ Hⁿ(Z) = 0`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hZ
  have himage := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
    (Y := Eucl P) n (hΦ.mono fun w (hw : w ∈ {w | w ∈ Ω ∧ Φ w ∈ U ∧
      ¬ DifferentiableAt ℝ (f ∘ Φ) w}) => hw.1)
  rw [hZ, mul_zero] at himage
  exact nonpos_iff_eq_zero.1 himage
/-- Gram representative of a differential along a `C¹` chart (chart gradient for the tangential
gradient in the slicing of Simon Ch. 6, §4): if `Φ : ℝⁿ → ℝ^P` is `C¹` and `A_w = DΦ(w)` is
injective on an open `Ω`, then for any `h : ℝⁿ → ℝ` the field `γ(w) = A_w (A_w* A_w)⁻¹ a_w`, with
`a_w` the Riesz vector of `Dh(w)`, extended by `0` off `Ω`, is Borel, lies in `range A_w` and
satisfies `⟨γ(w), A_w u⟩ = Dh(w) u` on `Ω`. -/
theorem Submission.slicing_im_tg_cg_gram_field :
    ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (h : Eucl n → ℝ), IsOpen Ω → ContDiff ℝ 1 Φ → (∀ w ∈ Ω, Function.Injective (fderiv ℝ Φ w)) → ∃ γ : Eucl n → Eucl P, Measurable γ ∧ ∀ w ∈ Ω, γ w ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u : Eucl n, inner ℝ (γ w) (fderiv ℝ Φ w u) = fderiv ℝ h w u := by
  intro P n Φ Ω h hΩ hΦ hinj
  classical
  set A : Eucl n → (Eucl n →L[ℝ] Eucl P) := fderiv ℝ Φ with hA
  have hAc : Continuous A := hΦ.continuous_fderiv one_ne_zero
  -- The Gram operator `G w = A_w* A_w` depends continuously on `w`.
  let G : Eucl n → (Eucl n →L[ℝ] Eucl n) := fun w => (ContinuousLinearMap.adjoint (A w)).comp (A w)
  have hGc : Continuous G := by
    have h1 : Continuous fun w => ContinuousLinearMap.adjoint (A w) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Eucl n) (F := Eucl P)).continuous.comp hAc
    exact h1.clm_comp hAc
  -- On `Ω`, `⟨G w u, u⟩ = ‖A_w u‖²` makes `G w` injective, hence (finite dimension) a unit.
  have hGunit : ∀ w ∈ Ω, IsUnit (G w) := by
    intro w hw
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hi : Function.Injective (G w) := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have h1 : inner ℝ (G w u) u = ‖A w u‖ ^ 2 := by
        simp only [G, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
      rw [hu, inner_zero_left] at h1
      have h2 : A w u = 0 := by
        have h3 : ‖A w u‖ ^ 2 = 0 := h1.symm
        exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
      exact (injective_iff_map_eq_zero _).mp (hinj w hw) u h2
    refine ⟨hi, ?_⟩
    exact (LinearMap.injective_iff_surjective
      (f := ((G w : Eucl n →L[ℝ] Eucl n) : Eucl n →ₗ[ℝ] Eucl n))).mp hi
  -- `B w = A_w (G w)⁻¹` is continuous on `Ω`, since `Ring.inverse` is continuous at units.
  let B : Eucl n → (Eucl n →L[ℝ] Eucl P) := fun w => (A w).comp (Ring.inverse (G w))
  have hBc : ContinuousOn B Ω := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun w => Ring.inverse (G w)) w := by
      obtain ⟨U, hU⟩ := hGunit w hw
      have h2 := NormedRing.inverse_continuousAt U
      rw [hU] at h2
      exact h2.comp hGc.continuousAt
    exact hAc.continuousAt.clm_comp h1
  -- The Riesz vector `a w` of `Dh(w)` is Borel in `w` (`measurable_fderiv`).
  let a : Eucl n → Eucl n := fun w => (InnerProductSpace.toDual ℝ (Eucl n)).symm (fderiv ℝ h w)
  have ham : Measurable a :=
    (InnerProductSpace.toDual ℝ (Eucl n)).symm.continuous.measurable.comp (measurable_fderiv ℝ h)
  -- `B` extended by `0` off the open set `Ω` is Borel, and `γ w = Bt w (a w)`.
  let Bt : Eucl n → (Eucl n →L[ℝ] Eucl P) := Ω.piecewise B 0
  have hBtm : Measurable Bt :=
    ContinuousOn.measurable_piecewise hBc continuousOn_const hΩ.measurableSet
  refine ⟨fun w => Bt w (a w), ?_, ?_⟩
  · exact isBoundedBilinearMap_apply.continuous.measurable2 hBtm ham
  · intro w hw
    have hBt : Bt w = B w := Set.piecewise_eq_of_mem _ _ _ hw
    simp only [hBt]
    refine ⟨LinearMap.mem_range.mpr ⟨Ring.inverse (G w) (a w), rfl⟩, ?_⟩
    intro u
    -- `⟨A_w x, A_w u⟩ = ⟨G w x, u⟩` with `G w x = a w` for `x = (G w)⁻¹ a w`.
    obtain ⟨U, hU⟩ := hGunit w hw
    have hGR : G w (Ring.inverse (G w) (a w)) = a w := by
      rw [← hU, Ring.inverse_unit]
      show ((U : Eucl n →L[ℝ] Eucl n) * ((U⁻¹ : (Eucl n →L[ℝ] Eucl n)ˣ) : Eucl n →L[ℝ] Eucl n)) (a w)
        = a w
      rw [Units.mul_inv]
      rfl
    calc inner ℝ (B w (a w)) (A w u)
        = inner ℝ ((ContinuousLinearMap.adjoint (A w)) (A w (Ring.inverse (G w) (a w)))) u := by
          rw [ContinuousLinearMap.adjoint_inner_left]; rfl
      _ = inner ℝ (G w (Ring.inverse (G w) (a w))) u := rfl
      _ = inner ℝ (a w) u := by rw [hGR]
      _ = fderiv ℝ h w u := InnerProductSpace.toDual_symm_apply
/-- Borel transfer through a chart (Lusin–Souslin, Kechris, *Classical Descriptive Set Theory*,
Thm. 15.1): if `D ⊆ ℝⁿ` is Borel and `Φ` is continuous and injective on `D`, then `Φ|_D` is a
measurable embedding, so a Borel `γ` factors as `γ = g ∘ Φ` on `D` through the Borel map
`g = extend (Φ|_D) (γ|_D) 0`, which vanishes off `Φ(D)`. -/
theorem Submission.slicing_im_tg_cg_borel_transfer :
    ∀ (n P Q : ℕ) (Φ : Eucl n → Eucl P) (D : Set (Eucl n)) (γ : Eucl n → Eucl Q), MeasurableSet D → ContinuousOn Φ D → InjOn Φ D → Measurable γ → ∃ g : Eucl P → Eucl Q, Measurable g ∧ (∀ w ∈ D, g (Φ w) = γ w) ∧ ∀ y, y ∉ Φ '' D → g y = 0 := by
  intro n P Q Φ D γ hD hc hi hγ
  -- Lusin–Souslin: `Φ|_D : D → ℝ^P` is a measurable embedding.
  have hE := hc.measurableEmbedding hD hi
  -- `g = extend (Φ|_D) (γ|_D) 0` is Borel because `γ|_D` and `0` are.
  refine ⟨Function.extend (D.domRestrict Φ) (D.domRestrict γ) 0,
    hE.measurable_extend (hγ.comp measurable_subtype_coe) measurable_const, ?_, ?_⟩
  -- On `Φ(D)`: `g (Φ w) = γ w` since `Φ|_D` is injective.
  · intro w hw
    exact hE.injective.extend_apply (D.domRestrict γ) 0 ⟨w, hw⟩
  -- Off `Φ(D)`: no `w ∈ D` has `Φ w = y`, so `g y = 0`.
  · intro y hy
    rw [Function.extend_apply']
    · rfl
    rintro ⟨⟨w, hw⟩, hwy⟩
    exact hy ⟨w, hw, hwy⟩
/-- Simon Ch. 2, 4.10 (cf. 4.7): if `f` is `L`-Lipschitz and both `Φ` and `f ∘ Φ` are
differentiable at `w`, then `s ↦ f(Φ(w) + s DΦ(w)u)` has derivative `D(f∘Φ)(w)u` at `0`.  It
differs from `s ↦ f(Φ(w + su))` by at most `L ‖Φ(w + su) - Φ(w) - s DΦ(w)u‖ = o(s)`, and the
latter map has derivative `D(f∘Φ)(w)u` by the chain rule. -/
theorem Submission.slicing_im_tg_line_deriv_of_comp : ∀ (n P : ℕ) (f : Eucl P → ℝ) (L : ℝ≥0) (Φ : Eucl n → Eucl P) (w : Eucl n), LipschitzWith L f → DifferentiableAt ℝ Φ w → DifferentiableAt ℝ (f ∘ Φ) w → ∀ u : Eucl n, HasDerivAt (fun s : ℝ => f (Φ w + s • fderiv ℝ Φ w u)) (fderiv ℝ (f ∘ Φ) w u) 0 := by
  intro n P f L Φ w hf hΦ hfΦ u
  -- The line `s ↦ w + s u` has derivative `u` at `0`.
  have hℓ : HasDerivAt (fun s : ℝ => w + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have hℓ0 : w = w + (0 : ℝ) • u := by simp
  -- Chain rule along the line: `s ↦ Φ(w + s u)` has derivative `DΦ(w)u` and
  -- `γ₁(s) = f(Φ(w + s u))` has derivative `D(f∘Φ)(w)u` at `0`.
  have hφ : HasDerivAt (fun s : ℝ => Φ (w + s • u)) (fderiv ℝ Φ w u) 0 :=
    hΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0
  have hγ₁ : HasDerivAt (fun s : ℝ => f (Φ (w + s • u))) (fderiv ℝ (f ∘ Φ) w u) 0 :=
    hfΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓ hℓ0
  -- The two curves are tangent at `0`: `Φ(w + s u) - Φ(w) - s DΦ(w)u = o(s)`.
  have hrem : (fun s : ℝ => Φ (w + s • u) - Φ w - s • fderiv ℝ Φ w u) =o[𝓝 0]
      fun s : ℝ => s := by
    simpa using hφ.isLittleO
  -- Lipschitz transfer: `|γ(s) - γ₁(s)| ≤ L ‖Φ(w + s u) - Φ(w) - s DΦ(w)u‖`.
  have hO : (fun s : ℝ => f (Φ w + s • fderiv ℝ Φ w u) - f (Φ (w + s • u))) =O[𝓝 0]
      fun s : ℝ => Φ (w + s • u) - Φ w - s • fderiv ℝ Φ w u := by
    refine Asymptotics.IsBigO.of_bound L ?_
    filter_upwards with s
    have hL := hf.dist_le_mul (Φ w + s • fderiv ℝ Φ w u) (Φ (w + s • u))
    rw [dist_eq_norm, dist_eq_norm] at hL
    rw [sub_sub, norm_sub_rev (Φ (w + s • u))]
    exact hL
  -- Hence `γ - γ₁`, which vanishes at `0`, has derivative `0` there.
  have hh : HasDerivAt (fun s : ℝ => f (Φ w + s • fderiv ℝ Φ w u) - f (Φ (w + s • u))) 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa using hO.trans_isLittleO hrem
  -- Conclude from `γ = γ₁ + (γ - γ₁)`.
  have hsum := hγ₁.add hh
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

/-- Tangential gradient of a Lipschitz function on a C¹ bi-Lipschitz chart (the gradient `∇ᴹf`
of Simon Ch. 3, 2.1, via Ch. 2, 4.10; used for the slices of Ch. 6, §4): for `f` `L`-Lipschitz and
`Φ` C¹, Lipschitz and antilipschitz on the open `Ω`, there is a Borel `g` with `‖g‖ ≤ L` such that
for `Hⁿ`-a.e. `y = Φ(w) ∈ Φ(Ω)`, `g(y) ∈ DΦ(w)(ℝⁿ)` and `s ↦ f(y + s v)` has derivative
`⟨g(y), v⟩` at `0` for every `v ∈ DΦ(w)(ℝⁿ)`.  Take `g := γ ∘ (Φ|_D)⁻¹` on `Φ(D)` and `0`
elsewhere, where `D` is the Borel set of `w ∈ Ω` at which `f ∘ Φ` is differentiable and
`γ(w) ∈ range DΦ(w)` is the Gram representative of `D(f ∘ Φ)(w)`; the failure set lies in the
`Hⁿ`-null `Φ(Ω ∖ D)`. -/
theorem Submission.slicing_im_tg_chart_gradient : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (f : Eucl P → ℝ) (L : ℝ≥0), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → LipschitzWith L f → ∃ g : Eucl P → Eucl P, Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧ ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict (Φ '' Ω)), ∀ w ∈ Ω, Φ w = y → g y ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ v ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap, HasDerivAt (fun s : ℝ => f (y + s • v)) (inner ℝ (g y) v) 0 := by
  rintro P n Φ Ω f L hΩ hΦ ⟨K, hK⟩ ⟨c, hc, hanti⟩ hf
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable one_ne_zero
  -- Step 1: `c ‖u‖ ≤ ‖DΦ(w) u‖` makes `DΦ(w)` injective for `w ∈ Ω`; `Φ` is injective on `Ω`.
  have hinj : ∀ w ∈ Ω, Function.Injective (fderiv ℝ Φ w) := by
    intro w hw
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h1 := Submission.lpf_wtc_cat_fderiv_lower_bound P n Φ Ω c w hΩ hw (hdiff w) hanti u
    rw [hu, norm_zero] at h1
    exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg u])
  have hΦinj : InjOn Φ Ω := by
    intro w hw w' hw' hww'
    have h1 := hanti w hw w' hw'
    rw [hww', sub_self, norm_zero] at h1
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by nlinarith [norm_nonneg (w - w')]))
  -- Steps 4–5: a Borel Gram representative `γ(w) ∈ range DΦ(w)` of `D(f ∘ Φ)(w)` on `Ω`.
  obtain ⟨γ, hγm, hγ⟩ := Submission.slicing_im_tg_cg_gram_field P n Φ Ω (f ∘ Φ) hΩ hΦ hinj
  -- Step 2: the Borel set `D ⊆ Ω` of differentiability points of `f ∘ Φ`.
  set D : Set (Eucl n) := Ω ∩ {w | DifferentiableAt ℝ (f ∘ Φ) w}
  have hDm : MeasurableSet D :=
    hΩ.measurableSet.inter (measurableSet_of_differentiableAt ℝ (f ∘ Φ))
  -- Step 6: transfer `γ` through `Φ|_D` (Lusin–Souslin); `g = 0` off `Φ(D)`.
  obtain ⟨g, hgm, hgD, hg0⟩ := Submission.slicing_im_tg_cg_borel_transfer n P P Φ D γ hDm
    hdiff.continuous.continuousOn (hΦinj.mono inter_subset_left) hγm
  -- Step 7: the conclusion at `y = Φ w` for `w ∈ D` (line_deriv and the Gram identity).
  have hkey : ∀ w ∈ D, g (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧
      ∀ v ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap,
        HasDerivAt (fun s : ℝ => f (Φ w + s • v)) (inner ℝ (g (Φ w)) v) 0 := by
    intro w hw
    rw [hgD w hw]
    refine ⟨(hγ w hw.1).1, fun v hv => ?_⟩
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    have h1 := Submission.slicing_im_tg_line_deriv_of_comp n P f L Φ w hf (hdiff w) hw.2 u
    rw [← (hγ w hw.1).2 u] at h1
    exact h1
  -- Step 8: `‖g‖ ≤ L` everywhere (converse mean value inequality in the direction `g(y)`).
  have hbound : ∀ x, ‖g x‖ ≤ L := by
    intro x
    by_cases hx : x ∈ Φ '' D
    · obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨hr, hd⟩ := hkey w hw
      have h1 : HasLineDerivAt ℝ f (inner ℝ (g (Φ w)) (g (Φ w))) (Φ w) (g (Φ w)) := hd _ hr
      have h2 := h1.le_of_lipschitz hf
      rw [real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _), sq] at h2
      rcases (norm_nonneg (g (Φ w))).eq_or_lt with h0 | h0
      · rw [← h0]
        exact L.coe_nonneg
      · exact le_of_mul_le_mul_right h2 h0
    · rw [hg0 x hx, norm_zero]
      exact L.coe_nonneg
  refine ⟨g, hgm, hbound, ae_restrict_of_ae ?_⟩
  -- Steps 2–3 and 9: every failure lies in `Φ(Ω ∖ D)`, which is `Hⁿ`-null (Rademacher in the
  -- chart for `e ∘ f : ℝ^P → ℝ¹`, `e : ℝ ≃L ℝ¹`).
  let e : ℝ ≃L[ℝ] Eucl 1 :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm
  have hef : LocallyLipschitzOn univ (e ∘ f) :=
    locallyLipschitzOn_univ.mpr (e.lipschitzWith.comp hf).locallyLipschitz
  have hnull := Submission.lpf_tde_chart_nondiff_image_null P 1 n univ (e ∘ f) Φ Ω K isOpen_univ
    hef hΩ hK
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  rw [mem_ofPred_eq] at hy
  by_contra hy'
  refine hy fun w hw hwy => ?_
  subst hwy
  refine hkey w ⟨hw, ?_⟩
  by_contra hnd
  exact hy' ⟨w, ⟨hw, mem_univ _, fun hd =>
    hnd ((e.comp_differentiableAt_iff (f := f ∘ Φ) (x := w)).mp hd)⟩, rfl⟩

/-- Tangential gradient of a Lipschitz function on a rectifiable carrier (Simon Ch. 3, 2.1, for the
weighted tangent planes of 1.7): for `(M, θ, ξ)` as in 3.1 and `f` `L`-Lipschitz there is a Borel
`G` with `‖G‖ ≤ L` everywhere such that for `Hⁿ`-a.e. `x ∈ M`, `G x` lies in every weighted
approximate tangent plane `Q` of `(M, θ)` at `x` and `⟨G x, u⟩` is the derivative of `f` at `x`
along every `u ∈ Q`.  Cover `M` up to an `Hⁿ`-null set by C¹ bi-Lipschitz charts
`Φ_j : Ω_j → ℝ^P`, let `g_j` be the gradient of `f` along `range DΦ_j` on `Φ_j(Ω_j)`, and put
`G = g_j` on `Φ_j(Ω_j)` for some `j` and `G = 0` off `⋃ j, Φ_j(Ω_j)`.  At `Hⁿ`-a.e.
`x = Φ_j(w) ∈ M`, `range DΦ_j(w)` is a weighted approximate tangent plane, hence the only one as
`θ x > 0`. -/
theorem Submission.slicing_im_tangential_gradient :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1))
      (f : Eucl P → ℝ) (L : ℝ≥0), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ →
      LipschitzWith L f → ∃ G : Eucl P → Eucl P, Measurable G ∧ (∀ x, ‖G x‖ ≤ L) ∧
        ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
          HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → G x ∈ Q ∧
            ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0 := by
  intro P m U M θ ξ f L hU hT hf
  classical
  -- C¹ charts `Φ j`, Lipschitz and antilipschitz on the open sets `Ω j`, cover `M` up to null sets.
  obtain ⟨Φ, Ω, hΩ, hΦ, hΦlip, hΦanti, hcov⟩ :=
    Submission.slicing_im_tg_c1_chart_cover P (m + 1) M hT.countablyRectifiable
  -- `Φ j` is injective on `Ω j`, so the chart images are Borel (Lusin–Souslin).
  have hSm : ∀ j, MeasurableSet (Φ j '' Ω j) := by
    intro j
    obtain ⟨c, hc, hcΦ⟩ := hΦanti j
    refine (hΩ j).measurableSet.image_of_continuousOn_injOn (hΦ j).continuous.continuousOn ?_
    intro w hw w' hw' hww'
    have h := hcΦ w hw w' hw'
    rw [hww', sub_self, norm_zero, ← mul_zero c] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_mul_le_mul_left h hc))
  -- On each chart image, the gradient `g j` of `f` along `range DΦ_j`.
  choose g hgm hgL hg using fun j =>
    Submission.slicing_im_tg_chart_gradient P (m + 1) (Φ j) (Ω j) f L (hΩ j) (hΦ j) (hΦlip j)
      (hΦanti j) hf
  -- Glue: `G = g j` at a point of some `Φ j '' Ω j`, and `G = 0` off all chart images.
  obtain ⟨G, hGm, hG⟩ : ∃ G : Eucl P → Eucl P, Measurable G ∧ ∀ x,
      (x ∉ ⋃ j, Φ j '' Ω j ∧ G x = 0) ∨ ∃ j, x ∈ Φ j '' Ω j ∧ G x = g j x := by
    -- Index `0` is the complement of the chart images, index `j + 1` the image of chart `j`.
    let t : ℕ → Set (Eucl P) := fun
      | 0 => (⋃ j, Φ j '' Ω j)ᶜ
      | j + 1 => Φ j '' Ω j
    let g' : ℕ → Eucl P → Eucl P := fun
      | 0 => 0
      | j + 1 => g j
    have ht : ∀ x, ∃ k, x ∈ t k := by
      intro x
      by_cases hx : x ∈ ⋃ j, Φ j '' Ω j
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact ⟨j + 1, hj⟩
      · exact ⟨0, hx⟩
    refine ⟨fun x => g' (Nat.find (ht x)) x, Measurable.find (fun k => ?_) (fun k => ?_) ht,
      fun x => ?_⟩
    · cases k with
      | zero => exact measurable_const
      | succ j => exact hgm j
    · cases k with
      | zero => exact (MeasurableSet.iUnion hSm).compl
      | succ j => exact hSm j
    · have hx := Nat.find_spec (ht x)
      beta_reduce
      generalize Nat.find (ht x) = k at hx ⊢
      cases k with
      | zero => exact Or.inl ⟨hx, rfl⟩
      | succ j => exact Or.inr ⟨j, hx, rfl⟩
  refine ⟨G, hGm, fun x => ?_, ?_⟩
  · rcases hG x with ⟨-, hx⟩ | ⟨j, -, hx⟩
    · rw [hx, norm_zero]
      exact L.coe_nonneg
    · rw [hx]
      exact hgL j x
  -- `Hⁿ`-a.e. point of `M` lies in a chart image.
  have hcovae : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ ⋃ j, Φ j '' Ω j := by
    rw [ae_restrict_iff'₀ hT.nullMeasurableSet, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hcov
    simp only [mem_ofPred_eq, not_imp] at hx
    exact hx
  -- The chart gradients have the tangential-gradient property a.e. on the chart images.
  have hgae : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ j, x ∈ Φ j '' Ω j →
      ∀ w ∈ Ω j, Φ j w = x → g j x ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap ∧
        ∀ v ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap,
          HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (g j x) v) 0 :=
    ae_all_iff.mpr fun j => ae_restrict_of_ae ((ae_restrict_iff' (hSm j)).mp (hg j))
  -- `range DΦ_j(w)` is a weighted approximate tangent plane at a.e. `x = Φ_j(w) ∈ M`.
  have htae : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ j, x ∈ Φ j '' Ω j →
      ∀ w ∈ Ω j, Φ j w = x → HasWeightedApproximateTangentSpaceAt (m + 1) M θ x
        (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) := by
    refine ae_all_iff.mpr fun j => (ae_restrict_iff' (hSm j)).mp ?_
    rw [Measure.restrict_restrict (hSm j), inter_comm]
    exact Submission.slicing_im_tg_weighted_tangent_chart P (m + 1) U M θ (Φ j) (Ω j) hU
      hT.subset hT.nullMeasurableSet hT.pos hT.integrableOn (hΩ j) (hΦ j) (hΦanti j)
  filter_upwards [ae_restrict_mem₀ hT.nullMeasurableSet, hcovae, hgae, htae] with
    x hxM hxS hgx htx Q hQ
  rcases hG x with ⟨hx, -⟩ | ⟨j, hxj, hGx⟩
  · exact absurd hxS hx
  have hgrad := hgx j hxj
  have htan := htx j hxj
  obtain ⟨w, hw, hwx⟩ := hxj
  -- Weighted approximate tangent planes are unique where `θ ≠ 0`, so `Q = range DΦ_j(w)`.
  obtain rfl : LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap = Q :=
    Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
      (hT.pos x hxM).ne' (htan w hw hwx) hQ
  rw [hGx]
  exact hgrad w hw hwx

/-- Simon Ch. 6, 4.1(2) and 4.4 (Step 7 of the slicing argument for `τ(M, θ, ξ)`, `n = m + 1`):
countably many `C¹` charts `Φ j`, antilipschitz on open `Ω j ⊆ ℝⁿ`, with sets `A j ⊆ Ω j` and `C¹`
functions `h j` such that `f ∘ Φ j = h j` on `A j`, `M ∖ ⋃ j, Φ j (A j)` is `Hⁿ`-null and, at
`Hⁿ`-a.e. `x = Φ j w ∈ M` with `w ∈ A j`, `DΦ j (w)(ℝⁿ)` is the weighted approximate tangent plane
of `(M, θ)` at `x`, contains the tangential gradient `G x` and `⟨G x, DΦ j (w) u⟩ = Dh j (w) u`.
The charts `(Φ' i, Ω' i)` come from Simon Ch. 3, Lemma 1.2, the `C¹` pieces `(h' i k, A' i k)` of
`f ∘ Φ' i` from Ch. 2, Theorem 1.5, and the index pairs `(i, k)` are merged by `Nat.unpair`. -/
theorem Submission.slicing_im_st_chart_data :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1))
      (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U →
      IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f →
      (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
          G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) →
      ∃ (Φ : ℕ → Eucl (m + 1) → Eucl P) (Ω A : ℕ → Set (Eucl (m + 1)))
        (h : ℕ → Eucl (m + 1) → ℝ), (∀ j, IsOpen (Ω j)) ∧ (∀ j, ContDiff ℝ 1 (Φ j)) ∧
        (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) ∧
        (∀ j, A j ⊆ Ω j) ∧ (∀ j, ContDiff ℝ 1 (h j)) ∧ (∀ j, ∀ w ∈ A j, f (Φ j w) = h j w) ∧
        (μHE[m + 1] : Measure (Eucl P)) (M \ ⋃ j, Φ j '' A j) = 0 ∧
        ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ j, ∀ w ∈ A j, Φ j w = x →
          HasWeightedApproximateTangentSpaceAt (m + 1) M θ x
            (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
          G x ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap ∧
          ∀ u : Eucl (m + 1), inner ℝ (G x) (fderiv ℝ (Φ j) w u) = fderiv ℝ (h j) w u := by
  intro P m U M θ ξ f L G hU hT hf hTG
  -- Step 1: `C¹` charts `Φ' i`, Lipschitz and antilipschitz on open sets `Ω' i`, whose images
  -- cover `M` up to an `Hⁿ`-null set.
  obtain ⟨Φ', Ω', hΩ', hΦ', hΦ'L, hΦ'a, hcov⟩ :=
    Submission.slicing_im_st_cd_c1_cover P (m + 1) M hT.countablyRectifiable
  choose K hK using hΦ'L
  -- Step 2: `f ∘ Φ' i` is Lipschitz on `Ω' i`, so it agrees, with its derivative, with `C¹`
  -- functions `h' i k` on sets `A' i k ⊆ Ω' i` that cover `Ω' i` up to an `Lⁿ`-null set.
  choose h' A' hh' hA'Ω hA' hA'null using fun i : ℕ =>
    Submission.slicing_im_st_cd_c1_pieces_of_lipschitzOn (m + 1) (Ω' i) (f ∘ Φ' i) (L * K i)
      (hΩ' i) (hf.comp_lipschitzOnWith (hK i))
  -- Step 5: at `Hⁿ`-a.e. `y ∈ M`, `DΦ' i (w)(ℝⁿ)` is the weighted approximate tangent plane of
  -- `(M, θ)` at `y = Φ' i w`; off the Borel chart image `Φ' i '' Ω' i` this is vacuous.
  have htan : ∀ i, ∀ᵐ y ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ w ∈ Ω' i,
      Φ' i w = y → HasWeightedApproximateTangentSpaceAt (m + 1) M θ y
        (LinearMap.range (fderiv ℝ (Φ' i) w).toLinearMap) := by
    intro i
    -- `Φ' i` is injective on `Ω' i`, so `Φ' i '' Ω' i` is Borel by Lusin–Souslin.
    have hS : MeasurableSet (Φ' i '' Ω' i) := by
      obtain ⟨c, hc, hcΦ⟩ := hΦ'a i
      refine (hΩ' i).measurableSet.image_of_continuousOn_injOn (hΦ' i).continuous.continuousOn
        fun w hw w' hw' hww' => ?_
      have h0 := hcΦ w hw w' hw'
      rw [hww', sub_self, norm_zero] at h0
      exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right h0 hc))
    have h := Submission.slicing_im_st_weighted_tangent_on_c1_chart P (m + 1) U M θ (Φ' i)
      (Ω' i) hU hT.subset hT.nullMeasurableSet hT.pos hT.integrableOn (hΩ' i) (hΦ' i) (hΦ'a i)
    rw [inter_comm M, ← Measure.restrict_restrict hS, ae_restrict_iff' hS] at h
    filter_upwards [h] with y hy w hw hwy
    exact hy ⟨w, hw, hwy⟩ w hw hwy
  -- Step 6 (Simon Ch. 2, 4.10): for `w ∈ A' i k`, `t ↦ f(Φ' i w + t DΦ' i (w) u)` has derivative
  -- `Dh' i k (w) u` at `0`.  Apply the vector-valued statement to `ι ∘ f : ℝ^P → ℝ¹`, `ι r = r e₀`,
  -- and read it off through the coordinate `π`, `π ∘ ι = id`.
  have hline : ∀ i k, ∀ w ∈ A' i k, ∀ u : Eucl (m + 1),
      HasDerivAt (fun t : ℝ => f (Φ' i w + t • fderiv ℝ (Φ' i) w u)) (fderiv ℝ (h' i k) w u) 0 := by
    let ι : ℝ →L[ℝ] Eucl 1 := (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single 0 1)
    let π : Eucl 1 →L[ℝ] ℝ := EuclideanSpace.proj 0
    have hπι : ∀ r, π (ι r) = r := fun r => by simp [π, ι]
    intro i k w hw u
    have hD : HasFDerivAt ((ι ∘ f) ∘ Φ' i) (ι.comp (fderiv ℝ (h' i k) w)) w :=
      ι.hasFDerivAt.comp w (hA' i k w hw).2
    have h := π.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (Submission.lpf_ccr_hasDerivAt_line_of_comp (m + 1) P 1 (ι ∘ f) (Φ' i) w
        ⟨‖ι‖₊ * L, univ, univ_mem, (ι.lipschitzWith.comp hf).lipschitzOnWith⟩
        ((hΦ' i).differentiable one_ne_zero w) hD.differentiableAt u)
    rw [hD.fderiv] at h
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, hπι] using h
  -- Step 3: merge the index pairs `(i, k)` into `j` by `Nat.unpair`.
  refine ⟨fun j => Φ' (Nat.unpair j).1, fun j => Ω' (Nat.unpair j).1,
    fun j => A' (Nat.unpair j).1 (Nat.unpair j).2, fun j => h' (Nat.unpair j).1 (Nat.unpair j).2,
    fun j => hΩ' _, fun j => hΦ' _, fun j => hΦ'a _, fun j => hA'Ω _ _, fun j => hh' _ _,
    fun j w hw => (hA' _ _ w hw).1, ?_, ?_⟩
  · -- Step 4: `M ∖ ⋃ j, Φ j (A j) ⊆ (M ∖ ⋃ i, Φ' i (Ω' i)) ∪ ⋃ i, Φ' i (Ω' i ∖ ⋃ k, A' i k)`;
    -- `Φ' i` is Lipschitz on `Ω' i`, so it maps the `Lⁿ`-null `Ω' i ∖ ⋃ k, A' i k` to an
    -- `Hⁿ`-null set.
    have hsub : M \ ⋃ j, Φ' (Nat.unpair j).1 '' A' (Nat.unpair j).1 (Nat.unpair j).2 ⊆
        (M \ ⋃ i, Φ' i '' Ω' i) ∪ ⋃ i, Φ' i '' (Ω' i \ ⋃ k, A' i k) := by
      rintro x ⟨hxM, hx⟩
      by_cases hxi : x ∈ ⋃ i, Φ' i '' Ω' i
      · obtain ⟨i, w, hw, rfl⟩ := mem_iUnion.1 hxi
        refine mem_union_right _ (mem_iUnion.2 ⟨i, w, ⟨hw, fun hwA => hx ?_⟩, rfl⟩)
        obtain ⟨k, hk⟩ := mem_iUnion.1 hwA
        exact mem_iUnion.2 ⟨Nat.pair i k, w, by simpa only [Nat.unpair_pair] using hk,
          by simp only [Nat.unpair_pair]⟩
      · exact mem_union_left _ ⟨hxM, hxi⟩
    refine measure_mono_null hsub (measure_union_null hcov (measure_iUnion_null fun i => ?_))
    have hle : (μHE[m + 1] : Measure (Eucl P)) (Φ' i '' (Ω' i \ ⋃ k, A' i k)) ≤
        (K i : ℝ≥0∞) ^ (m + 1) * (μHE[m + 1] : Measure (Eucl (m + 1))) (Ω' i \ ⋃ k, A' i k) :=
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (m + 1)
        ((hK i).mono sdiff_subset)
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hA'null i, mul_zero,
      nonpos_iff_eq_zero] at hle
  · -- Steps 5 and 6: `G x ∈ DΦ j (w)(ℝⁿ)` and, by uniqueness of the derivative along
    -- `DΦ j (w) u`, `⟨G x, DΦ j (w) u⟩ = Dh j (w) u`.
    filter_upwards [ae_all_iff.2 htan, hTG] with x hx hxG j w hw hwx
    have hwT := hx (Nat.unpair j).1 w (hA'Ω _ _ hw) hwx
    obtain ⟨hGT, hGd⟩ := hxG _ hwT
    refine ⟨hwT, hGT, fun u => (hGd _ (LinearMap.mem_range.2 ⟨u, rfl⟩)).unique ?_⟩
    subst hwx
    exact hline (Nat.unpair j).1 (Nat.unpair j).2 w hw u
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

/-- Tangent range of a level-set chart (step 7 of the level-set charts for the slicing theorem,
Simon Ch. 6, §4): if `ψ` is differentiable at `v` and `c`-antilipschitz (`c > 0`) on an open
`V ∋ v`, and `h ∘ ψ` is constant on `V` with `Dh(ψ v) ≠ 0`, then
`range D(Φ ∘ ψ)(v) = DΦ(ψ v)(ker Dh(ψ v))`.  By the derivative lower bound `Dψ(v)` is injective,
by the chain rule its range lies in `ker Dh(ψ v)`, and both subspaces have dimension `m`. -/
theorem Submission.slicing_im_st_lsc_tangent_range :
    ∀ (P m : ℕ) (ψ : Eucl m → Eucl (m + 1)) (Φ : Eucl (m + 1) → Eucl P) (h : Eucl (m + 1) → ℝ) (V : Set (Eucl m)) (c : ℝ) (v : Eucl m), IsOpen V → v ∈ V → 0 < c → DifferentiableAt ℝ ψ v → DifferentiableAt ℝ Φ (ψ v) → DifferentiableAt ℝ h (ψ v) → fderiv ℝ h (ψ v) ≠ 0 → (∀ v' ∈ V, ∀ v'' ∈ V, c * ‖v' - v''‖ ≤ ‖ψ v' - ψ v''‖) → (∀ v' ∈ V, h (ψ v') = h (ψ v)) → LinearMap.range (fderiv ℝ (Φ ∘ ψ) v).toLinearMap = Submodule.map (fderiv ℝ Φ (ψ v)).toLinearMap (LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap) := by
  intro P m ψ Φ h V c v hV hv hc hψd hΦd hhd hdh hanti hconst
  -- `c ‖u‖ ≤ ‖Dψ(v) u‖` with `c > 0`, so `Dψ(v)` is injective.
  have hlow := Submission.lpf_wtc_cat_fderiv_lower_bound (m + 1) m ψ V c v hV hv hψd hanti
  have hinj : Function.Injective (fderiv ℝ ψ v) := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  -- `h ∘ ψ` is constant near `v`, so `Dh(ψ v) ∘ Dψ(v) = D(h ∘ ψ)(v) = 0`.
  have hev : (h ∘ ψ) =ᶠ[𝓝 v] fun _ => h (ψ v) := by
    filter_upwards [hV.mem_nhds hv] with v' hv' using hconst v' hv'
  have hzero : fderiv ℝ (h ∘ ψ) v = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  have hcomp : fderiv ℝ (h ∘ ψ) v = (fderiv ℝ h (ψ v)).comp (fderiv ℝ ψ v) :=
    fderiv_comp v hhd hψd
  have hle : LinearMap.range (fderiv ℝ ψ v).toLinearMap ≤
      LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap := by
    rintro _ ⟨u, rfl⟩
    have h3 := congrArg (fun L : Eucl m →L[ℝ] ℝ => L u) (hcomp.symm.trans hzero)
    simpa using h3
  -- Both subspaces have dimension `m`: `Dψ(v)` is injective, and `Dh(ψ v) ≠ 0` maps onto `ℝ`.
  have hrange : Module.finrank ℝ (LinearMap.range (fderiv ℝ ψ v).toLinearMap) = m := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  have htop : LinearMap.range (fderiv ℝ h (ψ v)).toLinearMap = ⊤ := by
    obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ h (ψ v) u ≠ 0 := by
      by_contra hcon
      apply hdh
      ext u
      by_contra hu
      exact hcon ⟨u, by simpa using hu⟩
    rw [eq_top_iff]
    rintro y -
    refine ⟨(y / fderiv ℝ h (ψ v) u) • u, ?_⟩
    simp [hu]
  have hker : Module.finrank ℝ (LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap) = m := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ h (ψ v)).toLinearMap
    rw [htop, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hrn
    omega
  have heq : LinearMap.range (fderiv ℝ ψ v).toLinearMap =
      LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (hrange.trans hker.symm)
  -- Chain rule: `range D(Φ ∘ ψ)(v) = DΦ(ψ v)(range Dψ(v))`.
  rw [fderiv_comp v hΦd hψd]
  show LinearMap.range ((fderiv ℝ Φ (ψ v)).toLinearMap.comp (fderiv ℝ ψ v).toLinearMap) = _
  rw [LinearMap.range_comp, heq]

/-- Level-set charts (implicit-function step of the slice-triple argument for Simon Ch. 6, §4):
the regular points `w ∈ Ω`, `h w = t`, `Dh(w) ≠ 0` of a level set of a `C¹` function are covered,
after applying the `C¹` map `Φ` (antilipschitz on the open set `Ω`), by countably many `C¹`
charts `Ψ i` that are Lipschitz and antilipschitz on open sets `V i`, with tangent range
`DΦ(w)(ker Dh(w))`.  Take the implicit-function chart `ψ x` of `local_graph` at every regular
point `x`, keep countably many of the open sets `W x`, enumerated as `W (xs i)` (second
countability), and set `Ψ i := Φ ∘ ψ (xs i)`, `V i := B(0, r (xs i))`; the tangent range is
`tangent_range` with `c := 1`. -/
theorem Submission.slicing_im_st_level_set_charts :
    ∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ) (t : ℝ), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ContDiff ℝ 1 h → ∃ (Ψ : ℕ → Eucl m → Eucl P) (V : ℕ → Set (Eucl m)), (∀ i, IsOpen (V i)) ∧ (∀ i, ContDiff ℝ 1 (Ψ i)) ∧ (∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (Ψ i) (V i)) ∧ (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ v ∈ V i, ∀ v' ∈ V i, c * ‖v - v'‖ ≤ ‖Ψ i v - Ψ i v'‖) ∧ (∀ w ∈ Ω, h w = t → fderiv ℝ h w ≠ 0 → ∃ i, ∃ v ∈ V i, Ψ i v = Φ w) ∧ ∀ i, ∀ v ∈ V i, ∃ w ∈ Ω, h w = t ∧ Ψ i v = Φ w ∧ LinearMap.range (fderiv ℝ (Ψ i) v).toLinearMap = Submodule.map (fderiv ℝ Φ w).toLinearMap (LinearMap.ker (fderiv ℝ h w).toLinearMap) := by
  have hLG := Submission.slicing_im_st_lsc_local_graph
  have hTR := Submission.slicing_im_st_lsc_tangent_range
  intro P m Φ Ω h t hΩ hΦ hΦanti hh
  obtain ⟨c, hc, hcΦ⟩ := hΦanti
  -- `R` is the type of regular points of the level set `{h = t}` in `Ω`.
  let R := {w : Eucl (m + 1) // w ∈ Ω ∧ h w = t ∧ fderiv ℝ h w ≠ 0}
  rcases isEmpty_or_nonempty R with hR | hR
  · -- No regular point: empty chart domains.
    refine ⟨fun _ _ => 0, fun _ => ∅, fun _ => isOpen_empty, fun _ => contDiff_const,
      fun _ => ⟨0, lipschitzOnWith_empty _ _⟩,
      fun _ => ⟨1, one_pos, fun v hv => absurd hv (notMem_empty v)⟩, ?_,
      fun _ v hv => absurd hv (notMem_empty v)⟩
    intro w hw hhw hdw
    exact hR.elim ⟨w, hw, hhw, hdw⟩
  -- The implicit-function chart `(ψ x, r x, W x)` of `local_graph` at each regular point `x`.
  have hloc : ∀ x : R, ∃ (ψ : Eucl m → Eucl (m + 1)) (r : ℝ) (W : Set (Eucl (m + 1))),
      ContDiff ℝ 1 ψ ∧ 0 < r ∧ IsOpen W ∧ x.1 ∈ W ∧ (∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖) ∧
      (∀ v ∈ ball (0 : Eucl m) r, ψ v ∈ Ω ∧ h (ψ v) = h x.1 ∧ fderiv ℝ h (ψ v) ≠ 0) ∧
      ∀ w ∈ W, h w = h x.1 → ∃ v ∈ ball (0 : Eucl m) r, ψ v = w :=
    fun x => hLG m h Ω x.1 hh hΩ x.2.1 x.2.2.2
  choose ψ r W hψ hr hWo hxW hanti hgood hcover using hloc
  -- Countably many of the open sets `W x` cover all regular points; enumerate them as `W (xs i)`.
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  have hcovT : ∀ x : R, ∃ y ∈ T, x.1 ∈ W y := by
    intro x
    have hx : x.1 ∈ ⋃ y ∈ T, W y := by
      rw [hTU]
      exact mem_iUnion.2 ⟨x, hxW x⟩
    obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 hx
    exact ⟨y, hyT, hxy⟩
  have hTne : T.Nonempty := by
    obtain ⟨y, hyT, -⟩ := hcovT hR.some
    exact ⟨y, hyT⟩
  obtain ⟨xs, hxs⟩ := hTc.exists_eq_range hTne
  refine ⟨fun i => Φ ∘ ψ (xs i), fun i => ball (0 : Eucl m) (r (xs i)), fun _ => isOpen_ball,
    fun i => hΦ.comp (hψ (xs i)), ?_, ?_, ?_, ?_⟩
  · -- Lipschitz on `V i`: `Φ ∘ ψ (xs i)` is `C¹` on the compact convex closed ball.
    intro i
    obtain ⟨K, hK⟩ := ((hΦ.comp (hψ (xs i))).contDiffOn
      (s := closedBall (0 : Eucl m) (r (xs i)))).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall _ _) (isCompact_closedBall _ _)
    exact ⟨K, hK.mono ball_subset_closedBall⟩
  · -- Antilipschitz on `V i`: `ψ (xs i)` is `1`-antilipschitz with values in `Ω`.
    intro i
    refine ⟨c, hc, fun v hv v' hv' => ?_⟩
    calc c * ‖v - v'‖ ≤ c * ‖ψ (xs i) v - ψ (xs i) v'‖ :=
          mul_le_mul_of_nonneg_left (hanti (xs i) v v') hc.le
      _ ≤ ‖Φ (ψ (xs i) v) - Φ (ψ (xs i) v')‖ :=
          hcΦ _ (hgood (xs i) v hv).1 _ (hgood (xs i) v' hv').1
  · -- Covering: a regular point `w` lies in some `W (xs i)`, on which the level set is
    -- `ψ (xs i) (V i)`.
    intro w hw hhw hdw
    obtain ⟨y, hyT, hwy⟩ := hcovT ⟨w, hw, hhw, hdw⟩
    rw [hxs] at hyT
    obtain ⟨i, rfl⟩ := hyT
    obtain ⟨v, hv, hψv⟩ := hcover (xs i) w hwy (hhw.trans (xs i).2.2.1.symm)
    exact ⟨i, v, hv, congrArg Φ hψv⟩
  · -- Tangent range: `tangent_range` on `V i` with `c := 1`.
    intro i v hv
    obtain ⟨hvΩ, hvh, hvd⟩ := hgood (xs i) v hv
    refine ⟨ψ (xs i) v, hvΩ, hvh.trans (xs i).2.2.1, rfl, ?_⟩
    exact hTR P m (ψ (xs i)) Φ h (ball (0 : Eucl m) (r (xs i))) 1 v isOpen_ball hv one_pos
      ((hψ (xs i)).differentiable one_ne_zero v) (hΦ.differentiable one_ne_zero _)
      (hh.differentiable one_ne_zero _) hvd
      (fun v' _ v'' _ => (one_mul ‖v' - v''‖).symm ▸ hanti (xs i) v' v'')
      (fun v' hv' => (hgood (xs i) v' hv').2.1.trans hvh.symm)
/-- Simon Ch. 6, Lemma 4.1 (1)–(2) (p. 154), from Ch. 3, 2.10(2) and 1.6 (`n = m + 1`): for
`L¹`-a.e. `t` the regular level set `M_t = {x ∈ M : f(x) = t, G(x) ≠ 0}` is countably
`m`-rectifiable, and at `H^m`-a.e. `x ∈ M_t` every weighted approximate tangent plane `Q` of
`(M, θ)` gives the weighted approximate tangent plane `Q ∩ G(x)^⊥` of `(M_t, θ)`.

`M` is covered up to an `Hⁿ`-null set by C¹ antilipschitz charts `Φ j` with `f ∘ Φ j = h j` on
`A j`, `h j` C¹, `range DΦ j` the tangent plane, `G ∈ range DΦ j` and `⟪G, DΦ j u⟫ = D(h j) u`
(`slicing_im_st_chart_data`). For a.e. `t` these facts hold at `H^m`-a.e. point of `M_t`
(`slicing_im_st_ae_transfer`), and `M_t` is `H^m`-null-measurable with `θ` locally integrable
(`slicing_im_st_measure_fields`). The level sets `{h j = t}` are covered by C¹ bi-Lipschitz
`m`-charts `Ψ` with `range DΨ = DΦ j (ker D(h j))` (`slicing_im_st_level_set_charts`). At a good
point `G ≠ 0` forces `D(h j) ≠ 0`, and `DΦ j (ker D(h j)) = Q ∩ G^⊥`. Lipschitz extensions of
the `Ψ` cover `M_t` up to an `H^m`-null set, and `slicing_im_st_weighted_tangent_on_c1_chart`
makes each `range DΨ` a weighted approximate tangent plane of `(M_t, θ)`. -/
theorem Submission.slicing_im_st_slice_geometry :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1))
      (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U →
      IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f → Measurable G →
      (∀ x, ‖G x‖ ≤ L) →
      (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
          G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) →
      (∀ g : Eucl P → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t : ℝ => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
            (volume : Measure ℝ) ∧
          ∫⁻ t, (∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)))
              ∂(volume : Measure ℝ) =
            ∫⁻ x in M, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))) →
      ∀ᵐ t ∂(volume : Measure ℝ), CountablyRectifiable m {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ∧
        ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict {x | x ∈ M ∧ f x = t ∧ G x ≠ 0}),
          ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
            HasWeightedApproximateTangentSpaceAt m {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} θ x
              (Q ⊓ (ℝ ∙ G x)ᗮ) := by
  intro P m U M θ ξ f L G hU hT hf hG hGL hTG hCA
  -- Step 1: C¹ antilipschitz charts `Φ j` of `M` with `f ∘ Φ j = h j` on `A j`.
  obtain ⟨Φ, Ω, A, h, hΩ, hΦ, hΦc, hAΩ, hh, hfh, hcover, hchart⟩ :=
    Submission.slicing_im_st_chart_data P m U M θ ξ f L G hU hT hf hTG
  -- Step 2: the good points `p` have full `Hⁿ ⌞ M`-measure; for a.e. `t` they have full
  -- `H^m ⌞ M_t`-measure, `M_t` is `H^m`-null-measurable and `θ` is locally integrable on it.
  set p : Eucl P → Prop := fun x => (x ∈ ⋃ j, Φ j '' A j) ∧
    ∀ j, ∀ w ∈ A j, Φ j w = x →
      HasWeightedApproximateTangentSpaceAt (m + 1) M θ x
          (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
        G x ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap ∧
        ∀ u : Eucl (m + 1), inner ℝ (G x) (fderiv ℝ (Φ j) w u) = fderiv ℝ (h j) w u
  have hcov : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ ⋃ j, Φ j '' A j := by
    rw [ae_restrict_iff'₀ hT.nullMeasurableSet, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hcover
    simp only [Classical.not_imp, Set.mem_ofPred_eq] at hx
    exact hx
  have hp : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), p x := by
    filter_upwards [hcov, hchart] with x hx1 hx2 using ⟨hx1, hx2⟩
  filter_upwards [Submission.slicing_im_st_ae_transfer P m M f G hCA p hp,
    Submission.slicing_im_st_measure_fields P m U M θ ξ f L G hU hT hf.continuous.measurable hG
      hGL hCA] with t hpt hmf
  obtain ⟨hnm, hint, -⟩ := hmf
  set Mt : Set (Eucl P) := {x | x ∈ M ∧ f x = t ∧ G x ≠ 0}
  have hMt : Mt ⊆ M ∩ f ⁻¹' {t} := fun x hx => ⟨hx.1, hx.2.1⟩
  have hp_Mt : ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict Mt), p x :=
    ae_restrict_of_ae_restrict_of_subset hMt hpt
  have hN : (μHE[m] : Measure (Eucl P)) {x | x ∈ Mt ∧ ¬ p x} = 0 := by
    have := (ae_restrict_iff'₀ hnm).1 hp_Mt
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx => ?_) this
    simp only [Classical.not_imp, Set.mem_ofPred_eq]
    exact hx
  -- Step 3: C¹ bi-Lipschitz `m`-charts `Ψ j i` of the level sets `{h j = t}`.
  choose Ψ V hV hΨ hΨL hΨc hΨcover hΨrange using fun j =>
    Submission.slicing_im_st_level_set_charts P m (Φ j) (Ω j) (h j) t (hΩ j) (hΦ j) (hΦc j)
      (hh j)
  -- Step 4: a good point `x ∈ M_t` is `Ψ j i v` with `range DΨ j i v = Q ∩ G(x)^⊥` for every
  -- weighted approximate tangent plane `Q` of `(M, θ)` at `x`.
  have key : ∀ x ∈ Mt, p x → ∃ j i, ∃ v ∈ V j i, Ψ j i v = x ∧
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
        LinearMap.range (fderiv ℝ (Ψ j i) v).toLinearMap = Q ⊓ (ℝ ∙ G x)ᗮ := by
    intro x hx hpx
    obtain ⟨hxU, hpch⟩ := hpx
    obtain ⟨j, w, hwA, hwx⟩ := Set.mem_iUnion.1 hxU
    obtain ⟨hTan, hGmem, hinner⟩ := hpch j w hwA hwx
    -- (a) `h j w = f x = t`.
    have hht : h j w = t := by rw [← hfh j w hwA, hwx, hx.2.1]
    -- (b) `D(h j) w ≠ 0`, as `D(h j) w u₀ = ‖G x‖² ≠ 0` for `DΦ j w u₀ = G x`.
    have hDh : fderiv ℝ (h j) w ≠ 0 := by
      intro h0
      obtain ⟨u₀, hu₀⟩ := hGmem
      have := hinner u₀
      rw [h0] at this
      simp only [zero_apply] at this
      have hu₀' : fderiv ℝ (Φ j) w u₀ = G x := hu₀
      rw [hu₀', real_inner_self_eq_norm_sq] at this
      exact hx.2.2 (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this))
    -- (c) `x = Ψ j i v` for some `i` and `v ∈ V j i`.
    obtain ⟨i, v, hv, hΨv⟩ := hΨcover j w (hAΩ j hwA) hht hDh
    -- (d) The point `w'` attached to `v` is `w`, since `Φ j` is injective on `Ω j`.
    obtain ⟨w', hw', -, hΨw', hrange⟩ := hΨrange j i v hv
    have hww' : w' = w := by
      obtain ⟨c, hc, hcl⟩ := hΦc j
      have h0 := hcl w' hw' w (hAΩ j hwA)
      rw [← hΨw', hΨv, sub_self, norm_zero] at h0
      have : ‖w' - w‖ = 0 := le_antisymm
        (by nlinarith [norm_nonneg (w' - w)]) (norm_nonneg _)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    subst hww'
    refine ⟨j, i, v, hv, hΨv.trans hwx, fun Q hQ => ?_⟩
    -- (e) `Q = range DΦ j w` by uniqueness of the tangent plane, as `θ x > 0`.
    have hQT : Q = LinearMap.range (fderiv ℝ (Φ j) w').toLinearMap :=
      hQ.unique (ne_of_gt (hT.pos x hx.1)) hTan
    -- (f) `DΦ j w (ker D(h j) w) = range DΦ j w ∩ G(x)^⊥`, by `⟪G x, DΦ j w u⟫ = D(h j) w u`.
    rw [hrange, hQT]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, LinearMap.mem_range,
      Submodule.mem_orthogonal_singleton_iff_inner_right, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, rfl⟩, by rw [hinner u, hu]⟩
    · rintro ⟨⟨u, rfl⟩, hy⟩
      exact ⟨u, by rw [← hinner u, hy], rfl⟩
  refine ⟨?_, ?_⟩
  · -- Step 5: Lipschitz extensions of the `Ψ j i` cover `M_t` up to the `H^m`-null set of bad
    -- points (Ch. 3, 2.10(2)).
    have hext : ∀ j i, ∃ F : Eucl m → Eucl P, (∃ K : ℝ≥0, LipschitzWith K F) ∧
        Set.EqOn (Ψ j i) F (V j i) := by
      intro j i
      obtain ⟨K, hK⟩ := hΨL j i
      obtain ⟨F, hF, hEq⟩ := hK.extend_finite_dimension
      exact ⟨F, ⟨_, hF⟩, hEq⟩
    choose F hFL hFeq using hext
    refine ⟨{x | x ∈ Mt ∧ ¬ p x}, hN, fun k => F (Nat.unpair k).1 (Nat.unpair k).2,
      fun k => hFL _ _, fun x hx => ?_⟩
    by_cases hpx : p x
    · obtain ⟨j, i, v, hv, hΨv, -⟩ := key x hx hpx
      refine Or.inr (Set.mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
      simp only [Nat.unpair_pair]
      exact ⟨v, (hFeq j i hv).symm.trans hΨv⟩
    · exact Or.inl ⟨hx, hpx⟩
  · -- Step 6: on every chart, `range DΨ j i` is a weighted approximate tangent plane of
    -- `(M_t, θ)` at `H^m`-a.e. point of `M_t`.
    have htan : ∀ j i, ∀ᵐ y ∂((μHE[m] : Measure (Eucl P)).restrict Mt),
        ∀ v ∈ V j i, Ψ j i v = y →
          HasWeightedApproximateTangentSpaceAt m Mt θ y
            (LinearMap.range (fderiv ℝ (Ψ j i) v).toLinearMap) := by
      intro j i
      have hW := Submission.slicing_im_st_weighted_tangent_on_c1_chart P m U Mt θ (Ψ j i) (V j i)
        hU (fun y hy => hT.subset hy.1) hnm (fun y hy => hT.pos y hy.1) hint (hV j i) (hΨ j i)
        (hΨc j i)
      have hinj : Set.InjOn (Ψ j i) (V j i) := by
        intro a ha b hb hab
        obtain ⟨c, hc, hcl⟩ := hΨc j i
        have h0 := hcl a ha b hb
        rw [hab, sub_self, norm_zero] at h0
        have : ‖a - b‖ = 0 := le_antisymm
          (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
        exact sub_eq_zero.1 (norm_eq_zero.1 this)
      -- `Ψ j i '' V j i` is Borel (Lusin–Souslin), so the chart statement restricts to `M_t`.
      have hS : MeasurableSet (Ψ j i '' V j i) :=
        (hV j i).measurableSet.image_of_continuousOn_injOn (hΨ j i).continuous.continuousOn hinj
      rw [Set.inter_comm, ← Measure.restrict_restrict hS, ae_restrict_iff' hS] at hW
      filter_upwards [hW] with y hy v hv hvy
      exact hy ⟨v, hv, hvy⟩ v hv hvy
    -- Step 7: at a.e. good point of `M_t`, Step 4 identifies `Q ⊓ (ℝ ∙ G x)ᗮ` with a chart plane.
    have hall : ∀ᵐ y ∂((μHE[m] : Measure (Eucl P)).restrict Mt), ∀ j i,
        ∀ v ∈ V j i, Ψ j i v = y →
          HasWeightedApproximateTangentSpaceAt m Mt θ y
            (LinearMap.range (fderiv ℝ (Ψ j i) v).toLinearMap) :=
      ae_all_iff.mpr fun j => ae_all_iff.mpr (htan j)
    filter_upwards [ae_restrict_mem₀ hnm, hp_Mt, hall] with x hxMt hpx hx Q hQ
    obtain ⟨j, i, v, hv, hΨv, hrange⟩ := key x hxMt hpx
    rw [← hrange Q hQ]
    exact hx j i v hv hΨv

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
/-- Orthonormal frames of the same subspace have the same simple `n`-vector up to sign (Simon
Ch. 6, 3.1: `ξ(x) = τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM` is determined by `TₓM` up
to sign).  `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q = span τ = span τ'`.  Restricted to
`Q`, an `n`-covector `ω` is an alternating `n`-form on the `n`-dimensional space `Q`, so
`ω(τ') = b.det(b') ω(τ)` (`AlternatingMap.eq_smul_basis_det`, as in the determinant computation
after (3.4), p. 147), and `b.det(b') = ±1` because the change of basis between orthonormal bases
is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.fiw_ims_frame_sign :
    ∀ (P n : ℕ) (τ τ' : Fin n → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ τ' →
      Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') →
      simpleNVector τ' = simpleNVector τ ∨ simpleNVector τ' = -simpleNVector τ := by
  intro P n τ τ' hτ hτ' hspan
  set Q : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ)
  -- Step 1: `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`.
  let b : Module.Basis (Fin n) ℝ Q := Module.Basis.span hτ.linearIndependent
  let b' : Module.Basis (Fin n) ℝ Q :=
    (Module.Basis.span hτ'.linearIndependent).map (LinearEquiv.ofEq _ _ hspan.symm)
  have hb : Q.subtype ∘ b = τ :=
    funext fun i => Module.Basis.coe_span_apply hτ.linearIndependent i
  have hb' : Q.subtype ∘ b' = τ' := by
    funext i
    simp [b']
  have hbo : Orthonormal ℝ b := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb]
    exact hτ
  have hbo' : Orthonormal ℝ b' := by
    rw [← Q.subtypeₗᵢ.orthonormal_comp_iff, Submodule.coe_subtypeₗᵢ, hb']
    exact hτ'
  -- Step 2: the restriction `f = ω ∘ Q.subtype` of an `n`-covector `ω` is an alternating
  -- `n`-form on `Q`, so `f = f b • b.det`; evaluated at `b'` this is `ω τ' = b.det b' * ω τ`.
  have key : ∀ ω : Covector (Eucl P) n, ω τ' = b.det b' * ω τ := by
    intro ω
    have h := DFunLike.congr_fun
      ((ω.toAlternatingMap.compLinearMap Q.subtype).eq_smul_basis_det b) ⇑b'
    rw [AlternatingMap.smul_apply, smul_eq_mul] at h
    change ω (Q.subtype ∘ b') = ω (Q.subtype ∘ b) * b.det b' at h
    rw [hb, hb'] at h
    rw [h, mul_comm]
  -- Step 3: `b.det b' = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : b.det b' = 1 ∨ b.det b' = -1 := by
    simpa using (b.toOrthonormalBasis hbo).det_to_matrix_orthonormalBasis_real
      (b'.toOrthonormalBasis hbo')
  -- Step 4: extensionality, as `simpleNVector v ω = ω v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key ω, hd, one_mul]
  · right
    refine ContinuousLinearMap.ext fun ω => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key ω, hd, neg_one_mul]

/-- Interior product of a unit simple `(m+1)`-vector with a unit vector of its plane (Simon Ch. 6,
4.3).  Let `τ` be an orthonormal frame of `T = span τ`, `0 ≠ g ∈ T`, `ν = |g|⁻¹ g`, and
`w = ±τ₁ ∧ ⋯ ∧ τₘ₊₁`.  The contraction `w ⌞ ν : α ↦ w(ν♭ ∧ α)`, where
`(ν♭ ∧ α)(v) = ∑ᵢ (-1)ⁱ ⟨ν, vᵢ⟩ α(v₀, …, v̂ᵢ, …, vₘ)` (`alternatizeUncurryFin_apply`), is
`±τ'₁ ∧ ⋯ ∧ τ'ₘ` for an orthonormal basis `τ'` of `S = T ∩ g^⊥`.  Indeed `S` has dimension `m`
(`finrank_add_inf_finrank_orthogonal'`), `σ = (τ', ν)` is an orthonormal basis of `T`, so
`w = ±simpleNVector σ` (`Submission.fiw_ims_frame_sign`), and `(ν♭ ∧ α)(σ) = (-1)^m α(τ')` because
`⟨ν, τ'ₖ⟩ = 0`, `|ν| = 1` and `removeNth (last m) σ = τ'`. -/
theorem Submission.slicing_im_st_interior_product :
    ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (g : Eucl P) (w : NVector (Eucl P) (m + 1)), Orthonormal ℝ τ → g ∈ Submodule.span ℝ (range τ) → g ≠ 0 → (w = simpleNVector τ ∨ w = -simpleNVector τ) → ∃ τ' : Fin m → Eucl P, Orthonormal ℝ τ' ∧ Submodule.span ℝ (range τ') = Submodule.span ℝ (range τ) ⊓ (ℝ ∙ g)ᗮ ∧ (w.comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖g‖⁻¹ • g)))) = simpleNVector τ' ∨ w.comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖g‖⁻¹ • g)))) = -simpleNVector τ') := by
  intro P m τ g w hτ hg hg0 hw
  set T : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ) with hTdef
  set S : Submodule ℝ (Eucl P) := T ⊓ (ℝ ∙ g)ᗮ with hSdef
  set ν : Eucl P := ‖g‖⁻¹ • g with hνdef
  -- Step 1: `S` has dimension `m`, as `ℝ ∙ g ≤ T` has dimension `1` and `T` dimension `m + 1`.
  have hT : Module.finrank ℝ T = m + 1 := by
    rw [hTdef, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  have hgT : (ℝ ∙ g) ≤ T := (Submodule.span_singleton_le_iff_mem g T).2 hg
  have hS : Module.finrank ℝ S = m := by
    rw [hSdef, inf_comm]
    exact Submodule.finrank_add_inf_finrank_orthogonal' hgT
      (by rw [finrank_span_singleton hg0, hT, add_comm])
  -- Step 2: an orthonormal basis `τ'` of `S`, indexed by `Fin m`.
  let b : OrthonormalBasis (Fin m) ℝ S := (stdOrthonormalBasis ℝ S).reindex (finCongr hS)
  let τ' : Fin m → Eucl P := fun i => (b i : Eucl P)
  have hτ' : Orthonormal ℝ τ' := b.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hτ'S : ∀ k, τ' k ∈ S := fun k => (b k).2
  have hspan' : Submodule.span ℝ (range τ') = S := by
    have hr : range τ' = S.subtype '' range b := by
      rw [← range_comp]
      rfl
    have htop : Submodule.span ℝ (range b) = ⊤ := by
      simpa using b.toBasis.span_eq
    rw [hr, Submodule.span_image, htop, Submodule.map_subtype_top]
  -- Step 3: the adapted frame `σ = (τ', ν)` is an orthonormal basis of `T`.
  have hνT : ν ∈ T := T.smul_mem _ hg
  have hν1 : ‖ν‖ = 1 := by
    simpa [hνdef] using norm_smul_inv_norm (𝕜 := ℝ) hg0
  have hτ'ν : ∀ k, inner ℝ (τ' k) ν = 0 := by
    intro k
    have hk : inner ℝ g (τ' k) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hτ'S k).2
    rw [hνdef, inner_smul_right, real_inner_comm, hk, mul_zero]
  have hντ' : ∀ k, inner ℝ ν (τ' k) = 0 := fun k => by
    rw [real_inner_comm]
    exact hτ'ν k
  set σ : Fin (m + 1) → Eucl P := Fin.snoc (α := fun _ => Eucl P) τ' ν with hσdef
  have hσ : Orthonormal ℝ σ := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun c => ?_) j
    · simp [σ, hν1]
    · simp [σ, hντ', (Fin.castSucc_ne_last c).symm]
    · simp [σ, hτ'ν, Fin.castSucc_ne_last a]
    · simp only [σ, Fin.snoc_castSucc, Fin.castSucc_inj]
      exact orthonormal_iff_ite.1 hτ' a c
  have hσT : Submodule.span ℝ (range σ) = T := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun a => ?_) i
      · simpa [σ] using hνT
      · simpa [σ] using (hτ'S a).1
    · rw [finrank_span_eq_card hσ.linearIndependent, Fintype.card_fin, hT]
  -- Step 4: frame sign, `w = ± simpleNVector σ`.
  have hwσ : w = simpleNVector σ ∨ w = -simpleNVector σ := by
    rcases Submission.fiw_ims_frame_sign P (m + 1) τ σ hτ hσ hσT.symm with hs | hs <;>
      rcases hw with rfl | rfl
    · exact Or.inl hs.symm
    · exact Or.inr (by rw [hs])
    · exact Or.inr (by rw [hs]; exact (neg_neg (simpleNVector τ)).symm)
    · exact Or.inl (by rw [hs])
  -- Step 5: evaluation, `(ν♭ ∧ α)(σ) = (-1)^m α(τ')`.
  have hc : (simpleNVector σ).comp
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ ν))) =
      ((-1 : ℝ) ^ m) • simpleNVector τ' := by
    ext α
    simp only [ContinuousLinearMap.comp_apply, simpleNVector_apply, smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    rw [Fin.sum_univ_castSucc]
    simp [σ, Fin.removeNth_last, Fin.init_snoc, hντ', hν1]
  -- Step 6: conclusion, `w ⌞ ν = ± (-1)^m simpleNVector τ'`.
  refine ⟨τ', hτ', hspan', ?_⟩
  rcases neg_one_pow_eq_or ℝ m with hm | hm <;> rcases hwσ with rfl | rfl
  · left
    rw [hc, hm, one_smul]
  · right
    rw [ContinuousLinearMap.neg_comp, hc, hm, one_smul]
  · right
    rw [hc, hm, neg_one_smul ℝ (simpleNVector τ')]
  · left
    rw [ContinuousLinearMap.neg_comp, hc, hm, neg_one_smul ℝ (simpleNVector τ')]
    exact neg_neg (simpleNVector τ')

/-- Slices of a rectifiable triple are rectifiable triples (Simon Ch. 6, 4.1–4.4).  For `L¹`-a.e.
`t`, `M_t = {x ∈ M : f(x) = t, G(x) ≠ 0}` with multiplicity `θ` and orientation
`ξ_t = ξ ⌞ ν`, `ν = |G|⁻¹ G` (`ξ_t(x)(α) = ξ(x)(ν(x)♭ ∧ α)`), is a rectifiable `m`-triple in `U`.
The co-area formula `slicing_im_coarea` for `(M, f, G)` feeds `slicing_im_st_measure_fields`
(null-measurability of `M_t`, local integrability of `θ` on `M_t`, measurability of `ξ_t`),
`slicing_im_st_slice_geometry` (`M_t` is countably `m`-rectifiable with weighted approximate
tangent plane `TₓM ∩ G(x)^⊥`, Simon 4.1(2)) and the null transfer `slicing_im_st_ae_transfer`,
which carries the orientation clause of `(M, θ, ξ)` and the tangential-gradient property to
`Hᵐ`-a.e. point of `M_t`; `subset` and `pos` are inherited from `M_t ⊆ M`.  At such a point,
`ξ(x) = ±τ₁ ∧ ⋯ ∧ τₘ₊₁` with `τ` an orthonormal basis of `TₓM ∋ G(x) ≠ 0`, so
`slicing_im_st_interior_product` gives an orthonormal basis `τ'` of `TₓM ∩ G(x)^⊥` with
`ξ_t(x) = ±τ'₁ ∧ ⋯ ∧ τ'ₘ` (Simon 4.3). -/
theorem Submission.slicing_im_slice_triple :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1))
      (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U →
      IsRectifiableTriple U (m + 1) M θ ξ → LipschitzWith L f → Measurable G →
      (∀ x, ‖G x‖ ≤ L) →
      (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q →
          G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) →
      ∀ᵐ t ∂(volume : Measure ℝ), IsRectifiableTriple U m {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} θ
        (fun x => (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
          (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)
            (innerSL ℝ (‖G x‖⁻¹ • G x))))) := by
  intro P m U M θ ξ f L G hU hT hf hG hGL hTG
  -- The co-area formula for `(M, f, G)`.
  have hCA := Submission.slicing_im_coarea P m U M θ ξ f L G hU hT hf hG hGL hTG
  -- For a.e. `t`: `M_t` is `Hᵐ`-null-measurable, `θ` is locally `Hᵐ`-integrable on `M_t` and
  -- `ξ_t` is `Hᵐ ⌞ M_t`-a.e. strongly measurable.
  have hMF := Submission.slicing_im_st_measure_fields P m U M θ ξ f L G hU hT
    hf.continuous.measurable hG hGL hCA
  -- For a.e. `t`: `M_t` is countably `m`-rectifiable and, `Hᵐ`-a.e. on `M_t`, `TₓM ∩ G(x)^⊥` is
  -- a weighted approximate tangent plane of `(M_t, θ)`.
  have hSG := Submission.slicing_im_st_slice_geometry P m U M θ ξ f L G hU hT hf hG hGL hTG hCA
  -- For a.e. `t`: the orientation clause of `(M, θ, ξ)` and the tangential-gradient property hold
  -- `Hᵐ`-a.e. on `M ∩ f⁻¹{t}`.
  have hNT := Submission.slicing_im_st_ae_transfer P m M f G hCA _ (hT.orients.and hTG)
  filter_upwards [hMF, hSG, hNT] with t ⟨hnm, hint, hasm⟩ ⟨hcr, htan⟩ hp
  have hsub : {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} ⊆ M ∩ f ⁻¹' {t} := fun x hx => ⟨hx.1, hx.2.1⟩
  refine ⟨fun x hx => hT.subset hx.1, hnm, hcr, fun x hx => hT.pos x hx.1, hint, hasm, ?_⟩
  -- Orientation: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₘ₊₁` with `span τ = TₓM ∋ G(x) ≠ 0`, so
  -- `ξ_t(x) = ±τ'₁ ∧ ⋯ ∧ τ'ₘ` with `span τ' = TₓM ∩ G(x)^⊥`, a weighted approximate tangent plane
  -- of `(M_t, θ)` at `x`.
  filter_upwards [ae_restrict_mem₀ hnm, htan, ae_restrict_of_ae_restrict_of_subset hsub hp]
    with x hx hxtan ⟨⟨τ, hτ, hτT, hξ⟩, hxTG⟩
  obtain ⟨τ', hτ', hspan, hξ'⟩ :=
    Submission.slicing_im_st_interior_product P m τ (G x) (ξ x) hτ (hxTG _ hτT).1 hx.2.2 hξ
  refine ⟨τ', hτ', ?_, hξ'⟩
  rw [hspan]
  exact hxtan _ hτT
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

/-- **Slice identity (Simon Ch. 6, Remark 4.2 and the proof of Lemma 4.5(2)).**  For
`T = τ(M, θ, ξ)`, `f` Lipschitz with tangential gradient `G` on `M` and `ω ∈ 𝒟^m(U)`: for a.e. `t`,
every slice `S` of `T` by `f` at `t` has `S(ω) = τ(M_t, θ, ξ_t)(ω)`, where
`M_t = {x ∈ M : f x = t, G x ≠ 0}` and `ξ_t = ξ ⌞ (G/|G|)`.

With `φ(r) = ∫_{M ∩ f⁻¹{r}} g dH^m` (`θ ⟨G♭∧ω, ξ⟩ = |G| g`), the Leibniz identity for the cut-off
`h_ε = ψ_ε ∘ f` (tangential gradient `-ε⁻¹ 1_{t-ε<f<t} G`) and the co-area formula give
`∫ h_ε ⟨ω, v'⟩ dμ' - ∫ h_ε ⟨dω, v⟩ dμ = -ε⁻¹ ∫_{t-ε}^t φ`; let `ε ↓ 0` at a Lebesgue point `t`. -/
theorem Submission.slicing_im_slice_identity : ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → (∀ η : TestFormOn U (m + 1), T η = tauAction (m + 1) M θ ξ η) → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → ∀ ω : TestFormOn U m, ∀ᵐ t ∂(volume : Measure ℝ), ∀ S : GeometricCurrentOn U m, IsSlice T f t S → S ω = tauAction m {x | x ∈ M ∧ f x = t ∧ G x ≠ 0} θ (fun x => (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))) ω := by
  intro P m U M θ ξ T f L G hU hM hT hf hGm hGL hTG ω
  have hfm : Measurable f := hf.continuous.measurable
  -- Co-area formula on `M` for `f` and its tangential gradient `G` (Simon 4.1).
  have hCA := Submission.slicing_im_coarea P m U M θ ξ f L G hU hM hf hGm hGL hTG
  -- `G = 0` a.e. on every level set of `f`, and null subsets of `M` have null slices.
  obtain ⟨hlev, hNT⟩ := Submission.slicing_im_si_coarea_null_sets P
    (μHE[m + 1] : Measure (Eucl P)) (μHE[m] : Measure (Eucl P)) M f G hfm hGm hCA
  -- Borel density `g ∈ L¹(Hⁿ⌞M)`: `θ ⟨G♭∧ω, ξ⟩ = |G| g`, and `g = θ ⟨ω, ξ_t⟩` where `G ≠ 0`.
  obtain ⟨g, hgm, hgi, hg0, hgae⟩ :=
    Submission.slicing_im_si_borel_density P m U M θ ξ G ω hM hGm
  have hGg : Integrable (fun x => ‖G x‖ * g x) ((μHE[m + 1] : Measure (Eucl P)).restrict M) :=
    hgi.bdd_mul (c := (L : ℝ)) hGm.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [norm_norm]; exact hGL x)
  -- Remark 4.2: `φ(r) = ∫_{M ∩ f⁻¹{r}} g dH^m` is integrable and integrates `|G| g` over bands.
  obtain ⟨hφi, hφab⟩ := Submission.slicing_im_si_signed_coarea P
    (μHE[m + 1] : Measure (Eucl P)) (μHE[m] : Measure (Eucl P)) M f G g hfm hGm hgm hGg hCA
  -- For a.e. `t`, `φ(t)` is the action of the slice triple `(M_t, θ, ξ_t)` on `ω`.
  have htr := Submission.slicing_im_si_slice_ae_transfer P (μHE[m + 1] : Measure (Eucl P))
    (μHE[m] : Measure (Eucl P)) M {x | G x ≠ 0} f g
    (fun x => θ x *
      (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m)
          (innerSL ℝ (‖G x‖⁻¹ • G x)))) ((ω : DifferentialForm (Eucl P) m) x))
    hM.nullMeasurableSet (hGm (measurableSet_singleton 0).compl) hfm hNT
    (fun x hx => hg0 x (not_not.mp hx)) (hgae.mono fun x hx hxS => hx.1 hxS)
  -- Almost every `t` is a left Lebesgue point of `φ`.
  have hleb := Submission.slicing_im_si_left_lebesgue_point
    (fun r => ∫ x in M ∩ f ⁻¹' {r}, g x ∂(μHE[m] : Measure (Eucl P))) hφi.locallyIntegrable
  -- The exceptional set depends only on `ω`, not on the slice `S`.
  filter_upwards [htr, hleb] with t ht ht'
  intro S hS
  obtain ⟨A, B, ⟨-, μ₁, v₁, hrep₁, hA⟩, ⟨-, μ₂, v₂, hrep₂, hB⟩, hSAB⟩ := hS
  -- `(c w)♭∧α = c (w♭∧α)`.
  have hsmul : ∀ (c : ℝ) (w : Eucl P) (α : Covector (Eucl P) m),
      ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (c • w)).smulRight α) =
        c • ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ w).smulRight α) := by
    intro c w α
    rw [← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
    congr 1
    ext v u
    simp [mul_assoc]
  -- Leibniz identity for `h_ε = ψ_ε ∘ f`, whose tangential gradient is `-ε⁻¹ 1_{t-ε<f<t} G`
  -- (Simon (2)–(4) in the proof of 4.5(2)).
  have hkey : ∀ ε : ℝ, 0 < ε →
      (∫ x, max 0 (min 1 ((t - f x) / ε)) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂) -
          (∫ x, max 0 (min 1 ((t - f x) / ε)) *
            v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁) =
        -(ε⁻¹ * ∫ r in Ioo (t - ε) t, ∫ x in M ∩ f ⁻¹' {r}, g x ∂(μHE[m] : Measure (Eucl P))) := by
    intro ε hε
    obtain ⟨K, hKlip, hGεm, hGεK, hGεTG⟩ := Submission.slicing_im_si_cutoff_tangential_gradient P
      ((μHE[m + 1] : Measure (Eucl P)).restrict M)
      (HasWeightedApproximateTangentSpaceAt (m + 1) M θ) f L G t ε hε hf hGm hGL hTG
      (hlev (t - ε)) (hlev t)
    rw [Submission.slicing_im_lipschitz_leibniz P m U M θ ξ T hU hM hT μ₁ v₁ μ₂ v₂ hrep₁ hrep₂
      (fun x => max 0 (min 1 ((t - f x) / ε))) K
      ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) hKlip hGεm hGεK hGεTG ω]
    -- On the band `t - ε < f < t` the integrand is `-ε⁻¹ |G| g`; off the band it vanishes.
    have hpt : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
        θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ
          ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x)).smulRight
            ((ω : DifferentialForm (Eucl P) m) x))) =
          (f ⁻¹' Ioo (t - ε) t).indicator (fun y => -ε⁻¹ * (‖G y‖ * g y)) x := by
      filter_upwards [hgae] with x hx
      by_cases hxs : x ∈ f ⁻¹' Ioo (t - ε) t
      · rw [indicator_of_mem hxs, indicator_of_mem hxs, hsmul, ← hx.2, map_smul, smul_eq_mul]
        ring
      · have h0 := hsmul 0 0 ((ω : DifferentialForm (Eucl P) m) x)
        rw [zero_smul, zero_smul] at h0
        rw [indicator_of_notMem hxs, indicator_of_notMem hxs, h0, map_zero, mul_zero]
    rw [integral_congr_ae hpt, setIntegral_indicator (hfm measurableSet_Ioo), integral_const_mul,
      hφab]
    ring
  -- `ψ_ε(s) = max 0 (min 1 ((t - s) / ε))` cuts off `{s < t}`.
  have hχm : ∀ ε : ℝ, 0 < ε → Measurable fun s : ℝ => max 0 (min 1 ((t - s) / ε)) :=
    fun ε _ => by fun_prop
  have hχb : ∀ ε s : ℝ, 0 < ε → |max 0 (min 1 ((t - s) / ε))| ≤ 1 := by
    intro ε s _
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hχ1 : ∀ ε s : ℝ, 0 < ε → s ≤ t - ε → max 0 (min 1 ((t - s) / ε)) = 1 := by
    intro ε s hε hs
    rw [min_eq_left ((one_le_div hε).mpr (by linarith)), max_eq_right zero_le_one]
  have hχ0 : ∀ ε s : ℝ, 0 < ε → t ≤ s → max 0 (min 1 ((t - s) / ε)) = 0 := fun ε s hε hs =>
    max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le))
  -- Dominated convergence for both cut-off integrals (`ω` and `dω` vanish off `U`).
  have hlim₂ := Submission.slicing_mb_pointwise_cutoff_tendsto P U hU f L hf.lipschitzOnWith μ₂
    (fun x => v₂ x ((ω : DifferentialForm (Eucl P) m) x)) (hrep₂ ω).1
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport fun h => hx (ω.property.2 h)])
    t (fun ε s => max 0 (min 1 ((t - s) / ε))) hχm hχb hχ1 hχ0
  have hlim₁ := Submission.slicing_mb_pointwise_cutoff_tendsto P U hU f L hf.lipschitzOnWith μ₁
    (fun x => v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x))
    (hrep₁ (exteriorDerivativeTestOn U m ω)).1
    (fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport fun h =>
        hx (ω.property.2 (tsupport_exteriorDerivative_subset _ h))])
    t (fun ε s => max 0 (min 1 ((t - s) / ε))) hχm hχb hχ1 hχ0
  -- Both sides of the Leibniz identity converge as `ε ↓ 0`; the limits agree.
  have hBA := tendsto_nhds_unique
    ((hlim₂.sub hlim₁).congr' (eventually_nhdsWithin_of_forall (s := Ioi 0) fun ε hε => hkey ε hε))
    ht'.neg
  have hAω : A.boundary ω = ∫ x in {x | x ∈ U ∧ f x < t},
      v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁ :=
    hA (exteriorDerivativeTestOn U m ω)
  have hφt : A.boundary ω - B ω = ∫ x in M ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P)) := by
    rw [hAω, hB ω]
    beta_reduce at hBA
    linarith
  rw [hSAB ω, hφt, ht]
  rfl
/-- **Countable sequential density of test forms supported in a compact `K ⊆ U`** (the
"countable dense set of `ω ∈ 𝒟ⁿ(U)`" of Simon Ch. 6, proof of 4.5, p. 157).  The value spaces
`ℝ^P [×i]→L[ℝ] Λᵏ` of `D^i ω` are second countable (by currying).  For each order `m` and scale
`1/(j+1)`, the forms whose jets `(D^i ω)_{i ≤ m}` oscillate on `K` by less than `1/(m+1)` at
scale `1/(j+1)` are approximated within `3/(m+1)` on `K` through their jets on a finite
`1/(j+1)`-net of `K`.  A choice over the orders `m` gives a sequence whose derivatives of every
order converge uniformly on `K`. -/
theorem Submission.slicing_im_td_countable_seq_dense : ∀ (P k : ℕ) (U K : Set (Eucl P)), IsCompact K → K ⊆ U → ∃ E : Set (TestFormOn U k), E.Countable ∧ ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ K → ∃ e : ℕ → TestFormOn U k, (∀ l, e l ∈ E) ∧ TestFormOnConverges e ω := by
  intro P k U K hK hKU
  -- The value spaces of the iterated derivatives are second countable.
  have hgen : ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [SecondCountableTopology G]
      (i : ℕ), SecondCountableTopology (ContinuousMultilinearMap ℝ (fun _ : Fin i => Eucl P) G) := by
    intro G _ _ _ i
    induction i with
    | zero =>
      exact (continuousMultilinearCurryFin0 ℝ (Eucl P) G).toHomeomorph.secondCountableTopology
    | succ n ih =>
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Eucl P)
        G).toHomeomorph.secondCountableTopology
  have hCov : SecondCountableTopology (Covector (Eucl P) k) := by
    have := hgen ℝ k
    exact ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.isInducing.secondCountableTopology
  have hSC : ∀ i : ℕ, SecondCountableTopology
      (ContinuousMultilinearMap ℝ (fun _ : Fin i => Eucl P) (Covector (Eucl P) k)) :=
    fun i => hgen _ i
  -- The jet of order `m`: `J m ω x = (D^i ω x)_{i ≤ m}`.
  let J : (m : ℕ) → TestFormOn U k → Eucl P → ((i : Fin (m + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin i => Eucl P) (Covector (Eucl P) k)) :=
    fun m ω x i => iteratedFDeriv ℝ i (ω : DifferentialForm (Eucl P) k) x
  have hJcont : ∀ m (ω : TestFormOn U k), Continuous (J m ω) := fun m ω =>
    continuous_pi fun i => ω.2.1.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  let D : Set (TestFormOn U k) := {ω | tsupport (ω : DifferentialForm (Eucl P) k) ⊆ K}
  -- Finite `1/(j+1)`-nets of `K` inside `K`.
  have hnet : ∀ j : ℕ, ∃ t : Finset (Eucl P), (↑t : Set (Eucl P)) ⊆ K ∧
      K ⊆ ⋃ y ∈ t, Metric.ball y (1 / ((j : ℝ) + 1)) := by
    intro j
    obtain ⟨t, htK, ht, hcov⟩ := hK.finite_cover_balls (e := 1 / ((j : ℝ) + 1)) (by positivity)
    exact ⟨ht.toFinset, by simpa using htK, by simpa using hcov⟩
  choose net hnetK hnet using hnet
  -- Order `m`, accuracy `1/(m+1)`, scale `1/(j+1)`: take a countable dense subset of the jets on
  -- the net and choose preimages.
  have key : ∀ m j : ℕ, ∃ E' : Set (TestFormOn U k), E'.Countable ∧ E' ⊆ D ∧
      ∀ ω ∈ D, (∀ x ∈ K, ∀ y ∈ K, dist x y < 1 / ((j : ℝ) + 1) →
          dist (J m ω x) (J m ω y) < 1 / ((m : ℝ) + 1)) →
        ∃ η ∈ E', ∀ x ∈ K, dist (J m ω x) (J m η x) < 3 / ((m : ℝ) + 1) := by
    intro m j
    set r : ℝ := 1 / ((m : ℝ) + 1) with hr_def
    have hr : 0 < r := by positivity
    let Dj : Set (TestFormOn U k) := {ω | ω ∈ D ∧ ∀ x ∈ K, ∀ y ∈ K,
      dist x y < 1 / ((j : ℝ) + 1) → dist (J m ω x) (J m ω y) < r}
    let g : TestFormOn U k → (net j → ((i : Fin (m + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin i => Eucl P) (Covector (Eucl P) k))) :=
      fun ω y => J m ω y
    obtain ⟨S, hSA, hSc, hAS⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace (g '' Dj)).exists_countable_dense_subset
    have hpre : ∀ s : S, ∃ ω ∈ Dj, g ω = s := fun s => hSA s.2
    choose pick hpickD hpickg using hpre
    have : Countable S := hSc.to_subtype
    refine ⟨Set.range pick, Set.countable_range pick, ?_, ?_⟩
    · rintro _ ⟨s, rfl⟩
      exact (hpickD s).1
    · intro ω hωD hωmod
      obtain ⟨s, hsS, hdist⟩ := (Metric.mem_closure_iff (α := net j → (i : Fin (m + 1)) →
          ContinuousMultilinearMap ℝ (fun _ : Fin i => Eucl P) (Covector (Eucl P) k))).mp
        (hAS ⟨ω, ⟨hωD, hωmod⟩, rfl⟩) r hr
      have hηD : pick ⟨s, hsS⟩ ∈ Dj := hpickD ⟨s, hsS⟩
      have hgη : g (pick ⟨s, hsS⟩) = s := hpickg ⟨s, hsS⟩
      refine ⟨pick ⟨s, hsS⟩, ⟨⟨s, hsS⟩, rfl⟩, fun x hx => ?_⟩
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hnet j hx)
      have hyK : y ∈ K := hnetK j hy
      have hxy' : dist x y < 1 / ((j : ℝ) + 1) := Metric.mem_ball.mp hxy
      rw [← hgη] at hdist
      have h1 : dist (J m ω x) (J m ω y) < r := hωmod x hx y hyK hxy'
      have h2 : dist (J m ω y) (J m (pick ⟨s, hsS⟩) y) < r :=
        (dist_le_pi_dist (g ω) (g (pick ⟨s, hsS⟩)) ⟨y, hy⟩).trans_lt hdist
      have h3 : dist (J m (pick ⟨s, hsS⟩) y) (J m (pick ⟨s, hsS⟩) x) < r :=
        hηD.2 y hyK x hx (by rwa [dist_comm])
      have h4 := dist_triangle4 (J m ω x) (J m ω y) (J m (pick ⟨s, hsS⟩) y)
        (J m (pick ⟨s, hsS⟩) x)
      rw [show 3 / ((m : ℝ) + 1) = r + r + r by rw [hr_def]; ring]
      linarith
  choose E' hE'c hE'D hE' using key
  refine ⟨⋃ m, ⋃ j, E' m j,
    Set.countable_iUnion fun m => Set.countable_iUnion fun j => hE'c m j, ?_⟩
  intro ω hω
  -- At order `m`, `J m ω` is uniformly continuous on `K`; choose a scale and an approximant.
  have hlevel : ∀ m : ℕ, ∃ η ∈ ⋃ m', ⋃ j, E' m' j, η ∈ D ∧
      ∀ x ∈ K, dist (J m ω x) (J m η x) < 3 / ((m : ℝ) + 1) := by
    intro m
    have huc : UniformContinuousOn (J m ω) K :=
      hK.uniformContinuousOn_of_continuous (hJcont m ω).continuousOn
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuousOn_iff (α := Eucl P) (β := (i : Fin (m + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin i => Eucl P) (Covector (Eucl P) k))).mp huc
      (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    obtain ⟨η, hηE, hη⟩ := hE' m j ω hω fun x hx y hy hxy => hδ' x hx y hy (hxy.trans hj)
    exact ⟨η, Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨j, hηE⟩⟩, hE'D m j hηE, hη⟩
  choose e heE heD he using hlevel
  -- `K' := K`; for `m ≥ i` the `i`-th derivatives of `e m` are within `3/(m+1)` of those of `ω`.
  refine ⟨e, heE, K, hK, hKU, heD, hω, fun i => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (3 / ε)
  filter_upwards [eventually_ge_atTop (max i m₀)] with m hm x hx
  have him : i < m + 1 := Nat.lt_succ_of_le ((le_max_left i m₀).trans hm)
  have h3 : 3 / ((m : ℝ) + 1) < ε := by
    have hm' : (m₀ : ℝ) ≤ m := by exact_mod_cast (le_max_right i m₀).trans hm
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hm₀
    nlinarith
  exact (dist_le_pi_dist (J m ω x) (J m (e m) x) ⟨i, him⟩).trans_lt ((he m x hx).trans h3)
/-- Simon's currents are sequentially continuous at every test form: if `e l → ω` in `𝒟ᵏ(U)`,
then `S (e l) → S ω`.  The differences `e l - ω` converge to `0` on the same compact set, so
continuity of `S` at `0` (`GeometricCurrentOn.continuous'`) and linearity give the limit. -/
theorem Submission.slicing_im_td_current_tendsto :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (S : GeometricCurrentOn U k) (e : ℕ → TestFormOn U k)
      (ω : TestFormOn U k), TestFormOnConverges e ω →
        Tendsto (fun l => S (e l)) atTop (𝓝 (S ω)) := by
  intro P k U S e ω ⟨K, hK, hKU, he, hω, hd⟩
  -- `e l - ω → 0` on the same compact `K ⊆ U`.
  have hconv : TestFormOnConverges (fun l => e l - ω) 0 := by
    refine ⟨K, hK, hKU, fun l => (tsupport_sub _ _).trans (union_subset (he l) hω), by simp,
      fun i => Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
    -- The `i`-th derivatives of the smooth forms `e l` and `ω` subtract.
    have hsub : ∀ l x, iteratedFDeriv ℝ i
        ((e l : DifferentialForm (Eucl P) k) - (ω : DifferentialForm (Eucl P) k)) x =
          iteratedFDeriv ℝ i (e l : DifferentialForm (Eucl P) k) x -
            iteratedFDeriv ℝ i (ω : DifferentialForm (Eucl P) k) x := fun l x =>
      iteratedFDeriv_sub_apply ((e l).property.1.1.of_le (by exact_mod_cast le_top)).contDiffAt
        (ω.property.1.1.of_le (by exact_mod_cast le_top)).contDiffAt
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hd i) ε hε] with l hl x hx
    simpa [hsub, dist_eq_norm, norm_sub_rev] using hl x hx
  -- Continuity of `S` at `0`, then linearity: `S (e l) = S (e l - ω) + S ω`.
  have hlim := (S.continuous' _ hconv).add_const (S ω)
  rw [zero_add] at hlim
  refine hlim.congr fun l => ?_
  rw [S.toCurrent.map_sub (e l) ω, sub_add_cancel]

/-- A countable family of test forms determines currents (the "countable dense set of
`ω ∈ 𝒟ⁿ(U)`" in the proof of Simon Ch. 6, 4.5(2)): for open `U ⊆ ℝ^P` there is a countable
`E ⊆ 𝒟ᵏ(U)` such that two currents in `𝒟ₖ(U)` agreeing on `E` are equal. -/
theorem Submission.slicing_im_testform_determining :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ E : Set (TestFormOn U k), E.Countable ∧
      ∀ S R : GeometricCurrentOn U k, (∀ e ∈ E, S e = R e) → S = R := by
  intro P k U hU
  -- Exhaust `U` by the compact sets `closure (W i) ⊆ U` and take, for each `i`, a countable
  -- family `E i` approximating every form supported in `closure (W i)`.
  obtain ⟨W, hW, hWK⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
  choose E hE hEω using fun i => Submission.slicing_im_td_countable_seq_dense P k U
    (closure (W i)) (hW i).2.1 (hW i).2.2
  refine ⟨⋃ i, E i, countable_iUnion hE, fun S R hSR => GeometricCurrentOn.ext fun ω => ?_⟩
  -- `tsupport ω` is a compact subset of `U`, hence lies in some `W i`.
  obtain ⟨i, hi⟩ := hWK _ ω.2.1.2 ω.2.2
  obtain ⟨e, heE, he⟩ := hEω i ω (hi.trans subset_closure)
  -- `S (e l) = R (e l)` for every `l`, while `S (e l) → S ω` and `R (e l) → R ω`.
  refine tendsto_nhds_unique (Submission.slicing_im_td_current_tendsto P k U S e ω he) ?_
  exact (Submission.slicing_im_td_current_tendsto P k U R e ω he).congr fun l =>
    (hSR (e l) (mem_iUnion.2 ⟨i, heE l⟩)).symm

/-- **A rectifiable triple defines a current `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  For a
rectifiable triple `(M, θ, ξ)` in `U`, `ω ↦ ∫_M θ(x) ⟨ω(x), ξ(x)⟩ dHᵏ(x)` is a sequentially
continuous linear functional on `𝒟ᵏ(U)`.  The integrand is integrable (`ltg_tau_integrable`) and
linear in `ω`.  If `ω_j → 0` in `𝒟ᵏ(U)`, all `ω_j` are supported in one compact `K ⊆ U` and
`ω_j → 0` uniformly; as `|⟨α, ξ⟩| ≤ ‖α‖` `Hᵏ⌞M`-a.e. (`fiw_ims_tt_unit_bound`), eventually
`|θ ⟨ω_j, ξ⟩| ≤ |θ| 1_K ∈ L¹(Hᵏ⌞M)`, and dominated convergence gives `τ(M, θ, ξ)(ω_j) → 0`. -/
theorem Submission.slicing_im_tau_current : ∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple U k M θ ξ → ∃ R : GeometricCurrentOn U k, ∀ ω : TestFormOn U k, R ω = tauAction k M θ ξ ω := by
  intro P k U M θ ξ hT
  -- Step 1: for a test form `ω`, `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hᵏ`-integrable on `M`.
  have hI : ∀ ω : TestFormOn U k, IntegrableOn
      (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)) M (μHE[k] : Measure (Eucl P)) :=
    fun ω => (Submission.ltg_tau_integrable P k U M θ ξ hT).2 _
      (ContDiff.continuous ω.property.1.1) ω.property.1.2 ω.property.2
  -- Unit orientation: `|⟨α, ξ(x)⟩| ≤ ‖α‖` for `Hᵏ⌞M`-a.e. `x`.
  have hunit : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) k, |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hT.orients] with x hx α
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    exact Submission.fiw_ims_tt_unit_bound P k τ (ξ x) hτ hξ α
  refine ⟨⟨{ toFun := fun ω => tauAction k M θ ξ ω
             map_add' := fun ω η => ?_
             map_smul' := fun c ω => ?_ }, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  · -- Step 2 (additivity): `θ ⟨ω + η, ξ⟩ = θ ⟨ω, ξ⟩ + θ ⟨η, ξ⟩`, both integrable.
    simp only [tauAction, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
    exact integral_add (hI ω) (hI η)
  · -- Step 2 (homogeneity): `θ ⟨c ω, ξ⟩ = c θ ⟨ω, ξ⟩`.
    simp only [tauAction, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
      RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · -- Step 3 (continuity): `ω_j → 0` in `𝒟ᵏ(U)`, all supported in a compact `K ⊆ U`.
    show Tendsto (fun j => tauAction k M θ ξ (ωs j)) atTop (𝓝 0)
    obtain ⟨K, hKc, hKU, hsupp, -, hderiv⟩ := hconv
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    -- `sup_x ‖ω_j(x)‖ → 0`: zeroth derivatives converge uniformly on `K`, and `ω_j = 0` off `K`.
    have hsmall : ∀ ε > 0, ∀ᶠ j in atTop, ∀ x, ‖(ωs j : DifferentialForm (Eucl P) k) x‖ < ε := by
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hderiv 0) ε hε] with j hj x
      by_cases hx : x ∈ K
      · simpa using hj x hx
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
        exact hε
    -- Dominated convergence on `Hᵏ⌞M` with the integrable bound `|θ| 1_K`.
    have key := tendsto_integral_filter_of_dominated_convergence
      (μ := (μHE[k] : Measure (Eucl P)).restrict M) (l := atTop)
      (F := fun j x => θ x * ξ x ((ωs j : DifferentialForm (Eucl P) k) x))
      (f := fun _ => (0 : ℝ)) (K.indicator fun x => |θ x|)
      (Eventually.of_forall fun j => (hI (ωs j)).aestronglyMeasurable)
      ?_ ?_ ?_
    · simp only [integral_zero] at key
      exact key
    · -- Domination: once `‖ω_j‖ < 1`, `|θ ⟨ω_j, ξ⟩| ≤ |θ| 1_K` `Hᵏ⌞M`-a.e.
      filter_upwards [hsmall 1 one_pos] with j hj
      filter_upwards [hunit] with x hx
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |θ x| * |ξ x ((ωs j : DifferentialForm (Eucl P) k) x)| ≤ |θ x| * 1 :=
              mul_le_mul_of_nonneg_left ((hx _).trans (hj x).le) (abs_nonneg _)
          _ = |θ x| := mul_one _
      · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h)),
          map_zero, mul_zero, norm_zero]
    · -- `|θ| 1_K` is integrable on `M`: `θ` is integrable on `M ∩ K`.
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
      exact (hT.integrableOn K hKc hKU).abs
    · -- Pointwise limit: `ω_j(x) → 0`, so `θ(x) ⟨ω_j(x), ξ(x)⟩ → 0`.
      refine Eventually.of_forall fun x => ?_
      have h0 : Tendsto (fun j => (ωs j : DifferentialForm (Eucl P) k) x) atTop (𝓝 0) :=
        Metric.tendsto_nhds.mpr fun ε hε => (hsmall ε hε).mono fun j hj => by
          rw [dist_zero_right]; exact hj x
      have h1 := ((ξ x).continuous.tendsto 0).comp h0
      rw [map_zero] at h1
      simpa using (tendsto_const_nhds (x := θ x)).mul h1

/-- Simon Ch. 6, 4.4–4.5(2) (pp. 155–157): if `T` is integer multiplicity, with `M_W(T)` and
`M_W(∂T)` finite for every `W ⊂⊂ U`, and `f` is `L`-Lipschitz on `U`, then for `L¹`-a.e. `t` every
slice `S` with `IsSlice T f t S` is integer multiplicity.  Write `T = τ(M, θ, ξ)` and let `g` be
a McShane extension of `f`.  `IsSlice` only sees `f` on `U`, so slices of `T` by `f` and by `g`
coincide.  Let `G` be a tangential gradient of `g` on `M` and `E` a countable family of test forms
determining currents.  For a.e. `t`, the triple `(M_t, θ, ξ⌞(G/|G|))` with
`M_t = {x ∈ M : g(x) = t, G(x) ≠ 0}` is rectifiable, and every slice agrees on each `e ∈ E` with
the current `τ(M_t, θ, ξ⌞(G/|G|))`, hence equals it; `θ` is integer-valued on `M_t ⊆ M`. -/
theorem Submission.slicing_integer_multiplicity_ae : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → IsIntegerMultiplicity T → ∀ᵐ t ∂(volume : Measure ℝ), ∀ S : GeometricCurrentOn U m, IsSlice T f t S → IsIntegerMultiplicity S := by
  intro P m U hU T _hmass f L hf hT
  obtain ⟨M, θ, ξ, hMθξ, hθ, hTM⟩ := hT
  -- Step 1: a McShane extension `g` of `f`; the sets `{f < t}` and `{g < t}` agree inside `U`.
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have hslice : ∀ t (S : GeometricCurrentOn U m), IsSlice T f t S → IsSlice T g t S := by
    intro t S hS
    have hA : {x | x ∈ U ∧ f x < t} = {x | x ∈ U ∧ g x < t} :=
      Set.ext fun x => and_congr_right fun hx => by rw [hfg hx]
    unfold IsSlice at hS ⊢
    rwa [← hA]
  -- Step 2: a tangential gradient `G` of `g` on `M`, and a countable determining family `E`.
  obtain ⟨G, hGm, hGL, hG⟩ := Submission.slicing_im_tangential_gradient P m U M θ ξ g L hU hMθξ hg
  obtain ⟨E, hEc, hE⟩ := Submission.slicing_im_testform_determining P m U hU
  -- Step 3: for a.e. `t` the slice triple is rectifiable and every slice agrees with its current
  -- on each of the countably many `e ∈ E`.
  filter_upwards [Submission.slicing_im_slice_triple P m U M θ ξ g L G hU hMθξ hg hGm hGL hG,
    (ae_ball_iff hEc).2 fun e (_ : e ∈ E) =>
      Submission.slicing_im_slice_identity P m U M θ ξ T g L G hU hMθξ hTM hg hGm hGL hG e]
    with t ht hSE
  intro S hS
  -- Step 4: `S` equals the current `τ(M_t, θ, ξ⌞(G/|G|))`, whose multiplicity is `θ`.
  obtain ⟨R, hR⟩ := Submission.slicing_im_tau_current P m U _ θ _ ht
  have hSR : S = R := hE S R fun e he => (hSE e he S (hslice t S hS)).trans (hR e).symm
  refine ⟨_, θ, _, ht, fun x hx => hθ x hx.1, fun ω => ?_⟩
  rw [hSR, hR]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
