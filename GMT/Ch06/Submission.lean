import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation

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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
