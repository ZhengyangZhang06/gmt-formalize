import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
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

/-- Mollifying a Lipschitz map, as for Simon's `f^{(σ)} = f ∗ φ^{(σ)}` (Ch. 6, 2.29, p. 141): for
an `L`-Lipschitz `F : ℝ^m → ℝ^{m'}`, `F_σ(x) = ∫ ρ(w) F(x - w) dw`, with `ρ` the mollifier of
`slicing_mb_sa_mollifier_exists` at radius `σ/2`, is smooth, `L`-Lipschitz and `Lσ`-close to `F`.
If `F` is `Λ'`-Lipschitz on `B(x, 2σ)`, then `F_σ` is `Λ'`-Lipschitz on `B(x, σ)`,
`‖DF_σ(x)‖ ≤ Λ'` and `|F_σ(x) - F(x)| ≤ Λ'σ`; a coordinate of `F` constant on `B(x, σ)` keeps
its value at `x`. -/
theorem Submission.dph_sa_mollify_lipschitz :
    ∀ (m m' : ℕ) (F : Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L F → ∀ σ : ℝ, 0 < σ →
      ∃ Fs : Eucl m → Eucl m', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs ∧ LipschitzWith L Fs ∧
        (∀ x, ‖Fs x - F x‖ ≤ (L : ℝ) * σ) ∧
        (∀ (x : Eucl m) (Λ' : ℝ≥0), LipschitzOnWith Λ' F (ball x (2 * σ)) →
          LipschitzOnWith Λ' Fs (ball x σ) ∧ ‖fderiv ℝ Fs x‖ ≤ (Λ' : ℝ) ∧
            ‖Fs x - F x‖ ≤ (Λ' : ℝ) * σ) ∧
        ∀ (x : Eucl m) (i : Fin m') (c : ℝ), (∀ y ∈ ball x σ, F y i = c) → Fs x i = c := by
  intro m m' F L hF σ hσ
  -- The mollifier `ρ ≥ 0`, `∫ ρ = 1`, vanishing off `B(0, σ/2)`.
  obtain ⟨ρ, hρs, hρc, hρ0, hρz, hρ1⟩ :=
    Submission.slicing_mb_sa_mollifier_exists m (σ / 2) (half_pos hσ)
  have hρi : Integrable ρ := hρs.continuous.integrable_of_hasCompactSupport hρc
  -- `F_σ(x) = ∫ ρ(w) • F(x - w) dw`; each integrand is continuous with compact support.
  let Fs : Eucl m → Eucl m' := fun x => ∫ w, ρ w • F (x - w)
  have hint : ∀ x, Integrable (fun w => ρ w • F (x - w)) := fun x =>
    (hρs.continuous.smul (hF.continuous.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport hρc.smul_right
  -- `|∫ ρ • G| ≤ B` once `|G| ≤ B` on `B(0, σ/2)`, outside of which `ρ = 0`.
  have hbound : ∀ (G : Eucl m → Eucl m') (B : ℝ), (∀ w : Eucl m, ‖w‖ < σ / 2 → ‖G w‖ ≤ B) →
      ‖∫ w, ρ w • G w‖ ≤ B := by
    intro G B hG
    calc ‖∫ w, ρ w • G w‖ ≤ ∫ w, ρ w * B := by
          refine norm_integral_le_of_norm_le (hρi.mul_const B) (Eventually.of_forall fun w => ?_)
          by_cases hw : ‖w‖ < σ / 2
          · rw [norm_smul, Real.norm_of_nonneg (hρ0 w)]
            exact mul_le_mul_of_nonneg_left (hG w hw) (hρ0 w)
          · rw [hρz w (not_lt.1 hw), zero_smul, norm_zero, zero_mul]
      _ = B := by rw [integral_mul_const, hρ1, one_mul]
  -- Smoothness: `F_σ = ρ ⋆ F`.
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs := by
    have : Fs = convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext x
      rw [convolution_lsmul]
    rw [this]
    exact hρc.contDiff_convolution_left _ hρs hF.continuous.locallyIntegrable
  -- (E) `|F_σ(y) - F_σ(y')| ≤ Λ'|y - y'|` if `F` is `Λ'`-Lipschitz on a `U` containing
  -- `y - w` and `y' - w` for all `|w| < σ/2`.
  have hE : ∀ (U : Set (Eucl m)) (Λ' : ℝ≥0), LipschitzOnWith Λ' F U → ∀ y y' : Eucl m,
      (∀ w : Eucl m, ‖w‖ < σ / 2 → y - w ∈ U ∧ y' - w ∈ U) →
        ‖Fs y - Fs y'‖ ≤ Λ' * ‖y - y'‖ := by
    intro U Λ' hU y y' hyy'
    have : Fs y - Fs y' = ∫ w, ρ w • (F (y - w) - F (y' - w)) := by
      simp only [Fs, smul_sub]
      rw [integral_sub (hint y) (hint y')]
    rw [this]
    refine hbound _ _ fun w hw => ?_
    obtain ⟨h1, h2⟩ := hyy' w hw
    calc ‖F (y - w) - F (y' - w)‖ ≤ Λ' * ‖(y - w) - (y' - w)‖ := hU.norm_sub_le h1 h2
      _ = Λ' * ‖y - y'‖ := by rw [sub_sub_sub_cancel_right]
  -- (C) `|F_σ(x) - F(x)| ≤ Λ'σ` if `F` is `Λ'`-Lipschitz on a `U` containing `x` and `x - w`
  -- for all `|w| < σ/2`.
  have hC : ∀ (U : Set (Eucl m)) (Λ' : ℝ≥0), LipschitzOnWith Λ' F U → ∀ x : Eucl m, x ∈ U →
      (∀ w : Eucl m, ‖w‖ < σ / 2 → x - w ∈ U) → ‖Fs x - F x‖ ≤ Λ' * σ := by
    intro U Λ' hU x hx hxw
    have h1 : ∫ w, ρ w • F x = F x := by rw [integral_smul_const, hρ1, one_smul]
    have : Fs x - F x = ∫ w, ρ w • (F (x - w) - F x) := by
      simp only [Fs, smul_sub]
      rw [integral_sub (hint x) (hρi.smul_const (F x)), h1]
    rw [this]
    refine hbound _ _ fun w hw => ?_
    calc ‖F (x - w) - F x‖ ≤ Λ' * ‖(x - w) - x‖ := hU.norm_sub_le (hxw w hw) hx
      _ = Λ' * ‖w‖ := by rw [sub_sub_cancel_left, norm_neg]
      _ ≤ Λ' * σ := by gcongr; linarith
  refine ⟨Fs, hsmooth, ?_, ?_, ?_, ?_⟩
  -- Global bounds: `U = ℝ^m`, `Λ' = L`.
  · refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hE univ L hF.lipschitzOnWith y y' fun w _ => ⟨mem_univ _, mem_univ _⟩
  · exact fun x => hC univ L hF.lipschitzOnWith x (mem_univ _) fun w _ => mem_univ _
  -- Local bounds: `U = B(x, 2σ)` contains `y - w` for `y ∈ B(x, σ)`, `|w| < σ/2`.
  · intro x Λ' hΛ
    have hmem : ∀ y ∈ ball x σ, ∀ w : Eucl m, ‖w‖ < σ / 2 → y - w ∈ ball x (2 * σ) := by
      intro y hy w hw
      rw [mem_ball, dist_eq_norm] at hy ⊢
      calc ‖y - w - x‖ = ‖(y - x) - w‖ := by rw [sub_right_comm]
        _ ≤ ‖y - x‖ + ‖w‖ := norm_sub_le _ _
        _ < 2 * σ := by linarith
    have hLoc : LipschitzOnWith Λ' Fs (ball x σ) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      exact hE _ Λ' hΛ y y' fun w hw => ⟨hmem y hy w hw, hmem y' hy' w hw⟩
    refine ⟨hLoc, norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hσ) hLoc, ?_⟩
    exact hC _ Λ' hΛ x (mem_ball_self (by linarith)) (hmem x (mem_ball_self hσ))
  -- Locality of coordinates: `F_σ(x)_i = ∫ ρ(w) F(x - w)_i dw = c ∫ ρ = c`.
  · intro x i c hc
    have h1 : Fs x i = ∫ w, ρ w * F (x - w) i := by
      have := (EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ).integral_comp_comm (hint x)
      simpa [Fs] using this.symm
    rw [h1]
    have h2 : ∀ w, ρ w * F (x - w) i = ρ w * c := by
      intro w
      by_cases hw : ‖w‖ < σ / 2
      · rw [hc (x - w) (by rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; linarith)]
      · rw [hρz w (not_lt.1 hw), zero_mul, zero_mul]
    simp_rw [h2]
    rw [integral_mul_const, hρ1, one_mul]
/-- Multilinear-algebra step of the smoothing argument in the proof of the Deformation Theorem
(Simon Ch. 6, §5): a `k`-covector `γ` on `ℝ^{m'}` with `γ(e_{α(0)}, …, e_{α(k-1)}) = 0` pulls back
to `0` under every linear `T` with image in `span {e_{α(q)}}`.  With `S c = ∑_q c_q e_{α(q)}` on
`ℝ^k`, `T v = S ((T v)_{α(q)})_q`, and the alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes because
its value on the standard basis is `γ(e_{α(0)}, …, e_{α(k-1)}) = 0`. -/
theorem Submission.dph_sa_covector_comp_eq_zero :
    ∀ (m m' k : ℕ) (α : SimonMultiIndex k m') (γ : Eucl m' [⋀^Fin k]→L[ℝ] ℝ) (T : Eucl m →L[ℝ] Eucl m'), γ (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0 → (∀ (v : Eucl m) (i : Fin m'), i ∉ range α → T v i = 0) → γ.compContinuousLinearMap T = 0 := by
  intro m m' k α γ T hγ hT
  -- `S c = ∑_q c_q e_{α(q)}` on `ℝ^k`.
  let S : (Fin k → ℝ) →ₗ[ℝ] Eucl m' :=
    Fintype.linearCombination ℝ fun q => EuclideanSpace.single (α q) (1 : ℝ)
  -- `T` factors through `S`: coordinates in `range α` agree as `α` is injective, the others vanish.
  have hfac : ∀ v, T v = S fun q => T v (α q) := by
    intro v
    refine PiLp.ext fun i => ?_
    simp only [S, Fintype.linearCombination_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ range α
    · obtain ⟨q₀, rfl⟩ := hi
      simp [α.injective.eq_iff]
    · rw [hT v i hi, Finset.sum_eq_zero fun q _ => ite_eq_right fun h => hi ⟨q, h.symm⟩]
  -- The alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes on the standard basis, hence is `0`.
  have h0 : γ.toAlternatingMap.compLinearMap S = 0 := by
    have hb : (fun q => S (Pi.basisFun ℝ (Fin k) q)) =
        fun j => EuclideanSpace.single (α j) (1 : ℝ) := by
      funext q
      simp [S]
    rw [← AlternatingMap.map_basis_eq_zero_iff (Pi.basisFun ℝ (Fin k)),
      AlternatingMap.compLinearMap_apply, ContinuousAlternatingMap.coe_toAlternatingMap, hb]
    exact hγ
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rw [show ⇑T ∘ v = fun p => S fun q => T (v p) (α q) from funext fun p => hfac (v p)]
  exact AlternatingMap.congr_fun h0 fun p q => T (v p) (α q)

/-- The smoothings `f_σ = f ∗ φ_σ` of Simon Ch. 6, 2.29 (p. 141), for the Lipschitz push-forward
homotopy of the deformation theorem (§5): extend `G` from `A_δ = thickening δ A` to a Lipschitz
`G'` on `ℝ^m` (McShane) and mollify it at the scales `σ_j = (δ / 8) / (j + 1)`.  The
`2σ_j`-balls about points of `A_{δ/2}` stay in `A_δ`, where `G' = G` is `Λ`-Lipschitz, so
`‖D(Gj j)‖ ≤ Λ` there.  Near `A`, wherever `Gj j` meets `spt ω` the normal coordinates
`i ∉ range α` of `G` equal `z i` on a `2σ_j`-ball, so those of `Gj j` are locally constant,
`D(Gj j)` maps into `span e_α`, and `ω` without `e_α`-component pulls back to `0`. -/
theorem Submission.dph_lipschitz_smooth_approx :
    ∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ →
      LipschitzOnWith Λ G (thickening δ A) →
      ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0),
        LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧
        (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧
        TendstoUniformly Gj G' atTop ∧
        (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧
        ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m')
          (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε →
          (∀ x ∈ thickening ε A,
            G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) →
              ∀ i, i ∉ range α → G x i = z i) →
          (∀ y, (ω : DifferentialForm (Eucl m') k) y
            (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) →
          ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A,
            ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap
              (fderiv ℝ (Gj j) x) = 0 := by
  intro m m' G Λ A δ hδ hG
  -- Step 1 (McShane): a global Lipschitz extension `G'` of `G|A_δ`.
  obtain ⟨G', L, hG'L, hG'⟩ : ∃ (G' : Eucl m → Eucl m') (L : ℝ≥0),
      LipschitzWith L G' ∧ EqOn G' G (thickening δ A) :=
    let ⟨G', hG'L, hGG'⟩ := hG.extend_finite_dimension
    ⟨G', _, hG'L, hGG'.symm⟩
  -- The scales `σ_j = (δ / 8) / (j + 1)`: positive, at most `δ / 8`, tending to `0`.
  obtain ⟨σ, hσ, hσδ, hσ0⟩ : ∃ σ : ℕ → ℝ, (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ δ / 8) ∧
      Tendsto σ atTop (𝓝 0) := by
    refine ⟨fun j => δ / 8 * (1 / ((j : ℝ) + 1)), fun j => by positivity, fun j => ?_, ?_⟩
    · dsimp only
      rw [mul_one_div]
      exact div_le_self (by positivity) (by linarith [j.cast_nonneg (α := ℝ)])
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 8)
  -- Step 2: `Gj j` is the mollification of `G'` at scale `σ j`.
  choose Gj hGj hGjL hGjG' hGjloc hGjc using fun j =>
    Submission.dph_sa_mollify_lipschitz m m' G' L hG'L (σ j) (hσ j)
  -- For `x ∈ A_{δ/2}` the ball `B(x, 2σ_j)` lies in `A_δ`, where `G' = G` is `Λ`-Lipschitz.
  have hball : ∀ j, ∀ x ∈ thickening (δ / 2) A, ball x (2 * σ j) ⊆ thickening δ A :=
    fun j x hx => (ball_subset_thickening hx (2 * σ j)).trans
      ((thickening_thickening_subset (2 * σ j) (δ / 2) A).trans
        (thickening_mono (by linarith [hσδ j]) A))
  have hlocal : ∀ j, ∀ x ∈ thickening (δ / 2) A, LipschitzOnWith Λ G' (ball x (2 * σ j)) :=
    fun j x hx => LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => by
      rw [hG' (hball j x hx hy), hG' (hball j x hx hy')]
      exact hG.dist_le_mul y (hball j x hx hy) y' (hball j x hx hy')
  refine ⟨G', Gj, L, hG'L, hG', hGj, hGjL, ?_,
    fun j x hx => (hGjloc j x Λ (hlocal j x hx)).2.1, ?_⟩
  · -- Step 3: `‖Gj j - G'‖ ≤ L σ_j → 0`.
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    have hL := hσ0.const_mul (L : ℝ)
    rw [mul_zero] at hL
    filter_upwards [hL.eventually_lt_const hη] with j hj x
    rw [dist_comm, dist_eq_norm]
    exact (hGjG' j x).trans_lt hj
  -- Step 4 (tangential vanishing) on `A_{μ/4}`, `μ = min ε δ`, once `σ_j < μ / 8` and
  -- `(4Λ + 4) σ_j < ε`.
  intro k α z ω ε hε hH1 hH2
  obtain ⟨μ, hμ, hμε, hμδ⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ ε ∧ μ ≤ δ :=
    ⟨min ε δ, lt_min hε hδ, min_le_left _ _, min_le_right _ _⟩
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  refine ⟨μ / 4, by positivity, ?_⟩
  have hc : 0 < min (μ / 8) (ε / (4 * Λ + 4)) := lt_min (by positivity) (by positivity)
  filter_upwards [hσ0.eventually_lt_const hc] with j hj x hx
  have hj1 : σ j < μ / 8 := hj.trans_le (min_le_left _ _)
  have hj2 : σ j * (4 * Λ + 4) < ε :=
    (lt_div_iff₀ (by positivity)).1 (hj.trans_le (min_le_right _ _))
  have hx2 : x ∈ thickening (δ / 2) A := thickening_mono (by linarith) A hx
  have hxδ : x ∈ thickening δ A := thickening_mono (by linarith) A hx
  by_cases hsupp : Gj j x ∈ tsupport (ω : DifferentialForm (Eucl m') k)
  · refine Submission.dph_sa_covector_comp_eq_zero m m' k α _ _ (hH2 _) fun v i hi => ?_
    -- On `B(x, 2σ_j)` the normal coordinates of `G' = G` are those of `z`: such `y` lie in
    -- `A_ε ∩ A_δ`, and `|G y - Gj j x| ≤ 2Λσ_j + Λσ_j < ε` with `Gj j x ∈ spt ω`.
    have hnormal : ∀ y ∈ ball x (2 * σ j), G' y i = z i := by
      intro y hy
      have hyA : y ∈ thickening (2 * σ j + μ / 4) A :=
        thickening_thickening_subset (2 * σ j) (μ / 4) A (ball_subset_thickening hx _ hy)
      have hyδ : y ∈ thickening δ A := thickening_mono (by linarith) A hyA
      rw [hG' hyδ]
      refine hH1 y (thickening_mono (by linarith) A hyA) ?_ i hi
      refine mem_thickening_iff.2 ⟨Gj j x, hsupp, ?_⟩
      have h1 : dist (G y) (G x) ≤ Λ * dist y x := hG.dist_le_mul y hyδ x hxδ
      have h2 : ‖Gj j x - G' x‖ ≤ Λ * σ j := (hGjloc j x Λ (hlocal j x hx2)).2.2
      rw [hG' hxδ, ← dist_eq_norm] at h2
      have h3 : dist y x < 2 * σ j := hy
      calc dist (G y) (Gj j x) ≤ dist (G y) (G x) + dist (Gj j x) (G x) :=
            dist_triangle_right _ _ _
        _ ≤ Λ * (2 * σ j) + Λ * σ j :=
            add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3.le hΛ)) h2
        _ < ε := by nlinarith [mul_nonneg hΛ (hσ j).le, hσ j]
    -- Hence the `i`-th coordinate of `Gj j` is `z i` on `B(x, σ_j)` and `D(Gj j)(x)` has
    -- vanishing `i`-th coordinate.
    have hconst : (EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ) ∘ Gj j =ᶠ[𝓝 x] fun _ => z i :=
      Filter.mem_of_superset (ball_mem_nhds x (hσ j)) fun x' hx' =>
        hGjc j x' i (z i) fun y hy => hnormal y (by
          rw [mem_ball] at hx' hy ⊢
          linarith [dist_triangle y x' x])
    have hD := ((EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ).hasFDerivAt.comp x
      (((hGj j).differentiable (by simp)).differentiableAt.hasFDerivAt)).unique
      ((hasFDerivAt_const (z i) x).congr_of_eventuallyEq hconst)
    simpa using congrArg (fun T : Eucl m →L[ℝ] ℝ => T v) hD
  · -- Off `spt ω` the covector `ω (Gj j x)` is already `0`.
    rw [image_eq_zero_of_notMem_tsupport hsupp]
    ext v
    simp
/-- **Product formula in measure form (Federer 3.2.23; Simon Ch. 6, 3.2(2)).**  Write
`π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`.  If `Hᵐ(A ∩ K) < ∞` for every
compact `K ⊆ ℝ^P` and `∫⁻_{π⁻¹(A)} g dH^{m+1} = ∫⁻_ℝ ∫⁻_A g(Φ(s, x)) dHᵐ(x) ds` for every Borel
`g ≥ 0`, then `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ × Hᵐ⌞A)`.  Testing the formula with `g = 1_B` gives
`(H^{m+1}⌞π⁻¹(A))(B) = ∫⁻_ℝ (Hᵐ⌞A){x : Φ(s, x) ∈ B} ds = (L¹ × Hᵐ⌞A)(Φ⁻¹(B))` for Borel `B`;
`Hᵐ⌞A` is finite on compact sets, hence σ-finite, so the product measure is given by sections. -/
theorem Submission.iwl_cr_ip_restrict_preimage_eq_map : ∀ (P m : ℕ) (A : Set (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A)) := by
  intro P m A hfin hPF
  -- Step 1: `ν := Hᵐ⌞A` is finite on compact sets (compact sets are closed, hence Borel), so it
  -- is σ-finite on the σ-compact space `ℝ^P`; in particular `Measure.prod_apply` applies to `L¹ × ν`.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hfin K hK⟩
  -- Step 2: `Φ(s, x) = (s, x)` is continuous, hence Borel measurable.
  have hΦ : Measurable (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := by
    refine ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_).measurable
    exact Continuous.finCons continuous_fst
      ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
  -- Steps 3-7: the two measures agree on every Borel set `B`.  The left side is
  -- `∫⁻_{π⁻¹(A)} 1_B dH^{m+1} = ∫⁻_ℝ ∫⁻_A 1_B(Φ(s, x)) dHᵐ(x) ds` (the hypothesis with `g = 1_B`),
  -- the right side is `∫⁻_ℝ ν({x : Φ(s, x) ∈ B}) ds` (`Measure.map_apply`, `Measure.prod_apply`),
  -- and `1_B(Φ(s, x)) = 1_{{x : Φ(s, x) ∈ B}}(x)`.
  ext B hB
  rw [Measure.map_apply hΦ hB, Measure.prod_apply (hΦ hB), ← lintegral_indicator_one hB,
    hPF (B.indicator 1) (measurable_one.indicator hB)]
  refine lintegral_congr fun s => ?_
  rw [← lintegral_indicator_one (measurable_prodMk_left (hΦ hB))]
  rfl
/-- Measure identity on the slab over `A` (fact (D2) in the proof of the product triple): for
`Φ(s, x) = (s, x₁, …, x_P)` and `π(y) = (y₁, …, y_P)`, the cylinder identity
`Hᵐ⁺¹ ⌞ {π ∈ A} = Φ_#(L¹ × Hᵐ ⌞ A)` restricts to the slab `{π ∈ A, 0 < y₀ < 1}`.  Restricting
both sides to the Borel set `{0 < y₀ < 1}`, whose `Φ`-preimage is `(0, 1) × ℝ^P`, gives
`Φ_#((L¹ ⌞ (0, 1)) × Hᵐ ⌞ A)`; `Hᵐ ⌞ A` is finite on compact sets, hence s-finite. -/
theorem Submission.iwl_cr_ip_pt_slab_restrict_eq_map :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) →
      CountablyRectifiable m A →
      (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) →
      (μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} =
        Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
          ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) →
    ∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) →
      CountablyRectifiable m A →
      (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) →
      (μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧
            EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
        Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
          (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
            ((μHE[m] : Measure (Eucl P)).restrict A)) := by
  intro P m hMP A hA hArect hAfin
  -- `Hᵐ ⌞ A` is finite on compact sets, hence σ-finite (`ℝ^P` is σ-compact).
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hAfin K hK⟩
  -- `Φ` is continuous and `O = {0 < y₀ < 1}` is open, so both are Borel.
  have hΦ : Measurable (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) :=
    ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp (Continuous.finCons
      continuous_fst ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))).measurable
  have hO : MeasurableSet
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage
      ((continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous).measurable
  -- `Φ(s, x)₀ = s`, so `Φ⁻¹(O) = (0, 1) × ℝ^P`.
  have hpre : (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ⁻¹'
        {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      Ioo (0 : ℝ) 1 ×ˢ univ := by
    ext ⟨s, x⟩
    simp only [mem_preimage, mem_ofPred_eq, ContinuousLinearEquiv.apply_symm_apply,
      Fin.cons_zero, mem_prod, mem_univ, and_true]
  -- The slab is `O ∩ {π ∈ A}`.
  have hslab : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} ∩
        {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} := by
    ext y
    exact and_comm
  rw [hslab, ← Measure.restrict_restrict hO, hMP A hA hArect hAfin, Measure.restrict_map hΦ hO,
    hpre, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Integrability and a.e. strong measurability pass from `A ⊆ ℝ^P` to the slab
`S_A = {y | π y ∈ A ∧ y₀ ∈ (0, 1)}`, `π y = (y₁, …, y_P)`.  By `slab_restrict_eq_map`,
`H^{m+1} ⌞ S_A = Φ'_# ((L¹ ⌞ (0, 1)) ⊗ (Hᵐ ⌞ A))` for `Φ'(s, x) = (s, x₁, …, x_P)`, a
homeomorphism (hence a measurable embedding) with `π ∘ Φ' = Prod.snd`.  So (a) is integrability
of `f ∘ Prod.snd` for the product of the finite measure `L¹ ⌞ (0, 1)` with `Hᵐ ⌞ A`, and (b) is
a.e. strong measurability of `g ∘ Prod.snd`, `Prod.snd` being quasi-measure-preserving onto
`Hᵐ ⌞ A`. -/
theorem Submission.iwl_cr_ip_pt_slab_transfer : ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (∀ f : Eucl P → ℝ, IntegrableOn f A (μHE[m] : Measure (Eucl P)) → IntegrableOn (fun y : Eucl (P + 1) => f ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (μHE[m + 1] : Measure (Eucl (P + 1)))) ∧ ∀ g : Eucl P → NVector (Eucl P) m, AEStronglyMeasurable g ((μHE[m] : Measure (Eucl P)).restrict A) → AEStronglyMeasurable (fun y : Eucl (P + 1) => g ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ((μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}) := by
  intro P m hMP A hA hArect hAfin
  -- `H^{m+1} ⌞ S_A = Φ'_# ((L¹ ⌞ (0, 1)) ⊗ (Hᵐ ⌞ A))`.
  have hD := Submission.iwl_cr_ip_pt_slab_restrict_eq_map P m hMP A hA hArect hAfin
  -- `Hᵐ ⌞ A` is finite on compact sets, hence σ-finite, as `Integrable.comp_snd` needs.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hAfin K hK⟩
  -- `Φ'` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}` with inverse `y ↦ (y₀, π y)`.
  let Φh : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0,
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      left_inv := fun p => by
        rcases p with ⟨s, x⟩
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
          ContinuousLinearEquiv.symm_apply_apply]
      continuous_toFun := by
        refine (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_
        exact Continuous.finCons continuous_fst
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ ?_
        · exact (continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
        · refine (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_
          exact continuous_pi fun i =>
            (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous }
  have hΦ : MeasurableEmbedding (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := Φh.measurableEmbedding
  -- `π ∘ Φ' = Prod.snd`.
  have hπΦ : ∀ p : ℝ × Eucl P, (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))))) = p.2 := by
    intro p
    simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · -- (a) `f ∘ Prod.snd` is integrable for the product, `L¹ ⌞ (0, 1)` being finite.
    rw [IntegrableOn, hD, hΦ.integrable_map_iff]
    refine (Integrable.comp_snd hf ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hπΦ]
  · -- (b) `Prod.snd` is quasi-measure-preserving from the product onto `Hᵐ ⌞ A`.
    rw [hD, hΦ.aestronglyMeasurable_map_iff]
    refine (hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, hπΦ]
/-- **Slice formula for the product `[[(0, 1)]] × τ(M, θ, ξ)` (Simon Ch. 6, 2.17 and 3.2(2),
pp. 138, 146).**  Write `Φ(s, x) = (s, x) ∈ ℝ^{P+1}` and `π(y) = (y₁, …, y_P)`, and assume the
product formula `H^{m+1}⌞{π ∈ A} = Φ_#(L¹ × Hᵐ⌞A)` for every `Hᵐ`-measurable, countably
`m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for all compact `K`.  Let `(M, θ, ξ)` be a
rectifiable triple in `ℝ^P` with `θ ≥ 1` on `M`, and let `⟨α, ξ'(s, x)⟩ = ⟨β, ξ(x)⟩` whenever
`β(v) = α(e₀, (0, v₁), …, (0, vₘ))`.  If `θ(π y) ⟨η(y), ξ'(y)⟩` is `H^{m+1}`-integrable on
`M̃ = {y : π y ∈ M, y₀ ∈ (0, 1)}` and `φ(s)(x)(v) = η(s, x)(e₀, (0, v₁), …, (0, vₘ))` for
`s ∈ [0, 1]`, then `τ(M̃, θ ∘ π, ξ')(η) = ∫₀¹ τ(M, θ, ξ)(φ(s)) ds`.  As `θ ≥ 1`, `M` has locally
finite `Hᵐ`-measure, so `H^{m+1}⌞M̃ = Φ_#(L¹⌞(0, 1) × Hᵐ⌞M)` and Fubini applies. -/
theorem Submission.iwl_cr_ip_slice_formula : ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m) (ξ' : Eucl (P + 1) → NVector (Eucl (P + 1)) (m + 1)), IsRectifiableTriple (univ : Set (Eucl P)) m M θ ξ → (∀ x ∈ M, 1 ≤ θ x) → (∀ (s : ℝ) (x : Eucl P) (α : Covector (Eucl (P + 1)) (m + 1)) (β : Covector (Eucl P) m), (∀ v : Fin m → Eucl P, β v = α (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → ξ' ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) α = ξ x β) → ∀ (η : DifferentialForm (Eucl (P + 1)) (m + 1)) (φ : ℝ → DifferentialForm (Eucl P) m), IntegrableOn (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) * ξ' y (η y)) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (μHE[m + 1] : Measure (Eucl (P + 1))) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), φ s x v = η ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → tauAction (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ξ' η = ∫ s in (0 : ℝ)..1, tauAction m M θ ξ (φ s) := by
  intro P m hMP M θ ξ ξ' hT hθ1 hchar η φ hint hφ
  -- Step 1: `Hᵐ(M ∩ K) ≤ ∫_{M ∩ K} |θ| dHᵐ < ∞` for every compact `K`, since `θ ≥ 1` on `M`.
  have hlf : ∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞ := by
    intro K hK
    have hI := hT.integrableOn K hK (subset_univ K)
    have hnm : NullMeasurableSet (M ∩ K) (μHE[m] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet
    calc (μHE[m] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, 1 ∂(μHE[m] : Measure (Eucl P)) := by
          rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[m] : Measure (Eucl P)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hnm] with x hx
          rw [← ofReal_norm, ENNReal.one_le_ofReal, Real.norm_eq_abs]
          exact (hθ1 x hx.1).trans (le_abs_self _)
      _ < ∞ := hI.2
  -- So the product formula applies to `M`, and `Hᵐ⌞M` is finite on compacts, hence σ-finite.
  have hS := hMP M hT.nullMeasurableSet hT.countablyRectifiable hlf
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hlf K hK⟩
  -- `Φ(s, x) = (s, x)` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}` with inverse `y ↦ (y₀, π y)`,
  -- hence a measurable embedding.
  let Φh : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0,
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      left_inv := fun p => by
        rcases p with ⟨s, x⟩
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
          ContinuousLinearEquiv.symm_apply_apply]
      continuous_toFun := by
        refine (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_
        exact Continuous.finCons continuous_fst
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ ?_
        · exact (continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
        · refine (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_
          exact continuous_pi fun i =>
            (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous }
  have hΦm : MeasurableEmbedding (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := Φh.measurableEmbedding
  -- Step 2: `H^{m+1}⌞M̃ = Φ_#(L¹⌞(0, 1) × Hᵐ⌞M)`, restricting the product formula for `M` to the
  -- open slab `{y₀ ∈ (0, 1)}`, whose preimage under `Φ` is `(0, 1) × ℝ^P`.
  have hOm : MeasurableSet {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage
      ((continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous).measurable
  have hpre : (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ⁻¹'
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} = Ioo (0 : ℝ) 1 ×ˢ univ := by
    ext ⟨s, x⟩
    simp only [mem_preimage, Set.mem_ofPred_eq, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero,
      mem_prod, mem_univ, and_true]
  have hset : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
      EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} ∩
        {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M} := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_inter_iff]
    exact and_comm
  have hMt : (μHE[m + 1] : Measure (Eucl (P + 1))).restrict
      {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
        (((volume : Measure ℝ).restrict (Ioo 0 1)).prod ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    rw [hset, ← Measure.restrict_restrict hOm, hS, Measure.restrict_map hΦm.measurable hOm, hpre,
      ← Measure.prod_restrict, Measure.restrict_univ]
  -- Step 4: the integrand composed with `Φ` is integrable for `L¹⌞(0, 1) × Hᵐ⌞M`.
  have hint' := hint
  rw [IntegrableOn, hMt, hΦm.integrable_map_iff] at hint'
  -- Steps 3, 5 and 7: transport the integral along `Φ`, apply Fubini, and write `∫₀¹` as the
  -- set integral over `(0, 1]`, equivalently over `(0, 1)`.
  simp only [tauAction]
  rw [hMt, hΦm.integral_map, integral_prod, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  · -- Step 6: for `s ∈ (0, 1)`, `π(Φ(s, x)) = x` and `⟨η(Φ(s, x)), ξ'(Φ(s, x))⟩ = ⟨φ(s)(x), ξ(x)⟩`.
    refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [hchar s x _ _ (fun v => hφ s (Ioo_subset_Icc_self hs) x v)]
  · exact hint'
/-- Cylinders over null-measurable sets: let `π(y) = (y_1, …, y_P)` for `y ∈ ℝ^{P+1}`.  If
`π⁻¹(N)` is `H^{m+1}`-null for every `Hᵐ`-null `N ⊆ ℝ^P`, then `π⁻¹(M)` is `H^{m+1}`-null-measurable
for every `Hᵐ`-null-measurable `M ⊆ ℝ^P`.  `π` is continuous, hence Borel, and the hypothesis makes
it quasi-measure-preserving from `H^{m+1}` to `Hᵐ`. -/
theorem Submission.iwl_cr_ip_pt_cylinder_nullMeasurableSet :
    ∀ (P m : ℕ), (∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) →
      ∀ M : Set (Eucl P), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) →
        NullMeasurableSet {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M}
          (μHE[m + 1] : Measure (Eucl (P + 1))) := by
  intro P m hNT M hM
  -- `π = equiv_P⁻¹ ∘ Fin.tail ∘ equiv_{P+1}` is continuous, hence measurable.
  have hπm : Measurable (fun y : Eucl (P + 1) =>
      (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) := by
    refine ((EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_).measurable
    exact continuous_pi fun i =>
      (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
  -- The hypothesis on measurable null sets gives `π_* H^{m+1} ≪ Hᵐ`.
  have hq : Measure.QuasiMeasurePreserving (fun y : Eucl (P + 1) =>
      (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      (μHE[m + 1] : Measure (Eucl (P + 1))) (μHE[m] : Measure (Eucl P)) := by
    refine ⟨hπm, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
    rw [Measure.map_apply hπm hs]
    exact hNT s hs0
  exact hM.preimage hq
/-- Cylinders over countably `m`-rectifiable sets: if `π(y) = (y_1, …, y_P)` pulls
`Hᵐ`-null sets of `ℝ^P` back to `H^{m+1}`-null sets of `ℝ^{P+1}`, then for countably
`m`-rectifiable `M ⊆ ℝ^P` the cylinder `{y : π(y) ∈ M}` is countably `(m+1)`-rectifiable,
parametrized by `G_j(u) = (u_0, F_j(u_1, …, u_m))`. -/
theorem Submission.iwl_cr_ip_pt_cylinder_countablyRectifiable : ∀ (P m : ℕ), (∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) → ∀ M : Set (Eucl P), CountablyRectifiable m M → CountablyRectifiable (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M} := by
  intro P m hNT M hM
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 1: the continuous linear maps `hd u = u_0`, `tl u = (u_1, …, u_m)` and
  -- `Ψ (a, x) = (a, x_1, …, x_P)`.
  let hd : Eucl (m + 1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) 0).comp
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  let tl : Eucl (m + 1) →L[ℝ] Eucl m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.pi fun i : Fin m =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i.succ).comp
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap)
  let Ψ : ℝ × Eucl P →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun p => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))
      map_add' := by
        intro p q
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearEquiv.apply_symm_apply]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := by
        intro c p
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearEquiv.apply_symm_apply,
          RingHom.id_apply]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  -- Step 2: the exceptional set is the cylinder over `M₀` (null by `hNT`) and
  -- `G_j = Ψ ∘ (hd, F_j ∘ tl)` is Lipschitz.
  refine ⟨{y | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M₀},
    hNT M₀ hM₀, fun j u => Ψ (hd u, F j (tl u)), fun j => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hF j
    exact ⟨_, Ψ.lipschitzWith.comp (hd.lipschitzWith.prodMk (hK.comp tl.lipschitzWith))⟩
  -- Step 3: if `π(y) = F_j(w)` then `G_j(y_0, w) = (y_0, π(y)) = y`.
  · intro y hy
    rcases hcover hy with h0 | h1
    · exact Or.inl h0
    · right
      obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
      refine mem_iUnion.mpr ⟨j, (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0) (EuclideanSpace.equiv (Fin m) ℝ w)), ?_⟩
      have h1' : hd ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0) (EuclideanSpace.equiv (Fin m) ℝ w))) =
          EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 := by
        simp [hd]
      have h2' : tl ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0) (EuclideanSpace.equiv (Fin m) ℝ w))) = w := by
        apply (EuclideanSpace.equiv (Fin m) ℝ).injective
        ext i
        simp [tl]
      show Ψ (hd _, F j (tl _)) = y
      rw [h1', h2', hw]
      show (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
        (EuclideanSpace.equiv (Fin P) ℝ ((EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))))) = y
      simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
        ContinuousLinearEquiv.symm_apply_apply]
/-- Orienting frame of the product triple `(0, 1) × M` (Simon Ch. 6, 3.2(2), used in the proof
of 8.2): if `τ₁, …, τₘ` is orthonormal in `ℝ^P`, then `(e₀, ιτ₁, …, ιτₘ)` is orthonormal in
`ℝ^{P+1}`, `ι v = (0, v)`.  In coordinates `⟨(a, u), (b, w)⟩ = a b + ⟨u, w⟩` and `e₀ = (1, 0)`. -/
theorem Submission.iwl_cr_ip_pt_frame_orthonormal :
    ∀ (P m : ℕ) (τ : Fin m → Eucl P), Orthonormal ℝ τ →
      Orthonormal ℝ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1))
        (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) := by
  intro P m τ hτ
  rw [orthonormal_iff_ite] at hτ ⊢
  -- `⟨(a, u), (b, w)⟩ = a b + ⟨u, w⟩`: split off the coordinate `0` of the sum.
  have hinner : ∀ (a b : ℝ) (u w : Eucl P),
      inner ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons a (EuclideanSpace.equiv (Fin P) ℝ u)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons b (EuclideanSpace.equiv (Fin P) ℝ w))) = a * b + inner ℝ u w := by
    intro a b u w
    rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  -- `e₀ = (1, 0)`, compared coordinatewise.
  have he : (EuclideanSpace.single 0 1 : Eucl (P + 1)) =
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 1 (EuclideanSpace.equiv (Fin P) ℝ 0)) := by
    apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, he, hinner]
    simp
  · simp only [Fin.cons_zero, Fin.cons_succ, he, hinner]
    simp [(Fin.succ_ne_zero j).symm]
  · simp only [Fin.cons_zero, Fin.cons_succ, he, hinner]
    simp [Fin.succ_ne_zero i]
  · -- `⟨ιτᵢ, ιτⱼ⟩ = ⟨τᵢ, τⱼ⟩` and `i.succ = j.succ ↔ i = j`.
    simp only [Fin.cons_succ, hinner, zero_mul, zero_add, Fin.succ_inj]
    exact hτ i j
/-- The product frame of `(0, 1) × M` (Simon Ch. 6, Remark 3.2(2), for `[[(0, 1)]] × τ(M, θ, ξ)`).
Write `ℝ^{P+1} = ℝ × ℝ^P` with `Φ(s, u) = (s, u₁, …, u_P)` and `π(z) = (z₁, …, z_P)`.  If `τ` is an
orthonormal family in `ℝ^P`, then `τ̃ = (e₀, Φ(0, τ₁), …, Φ(0, τ_m))` is orthonormal, its span `Q`
has dimension `m + 1`, and `Q = π⁻¹(span τ)` as sets.  In coordinates
`⟨Φ(a, u), Φ(b, w)⟩ = ab + ⟨u, w⟩` and `e₀ = Φ(1, 0)`; the generators of `Q` project into `span τ`,
and conversely `z = z₀ e₀ + ∑ᵢ cᵢ Φ(0, τᵢ)` whenever `π z = ∑ᵢ cᵢ τᵢ`. -/
theorem Submission.iwl_cr_ip_wt_product_plane :
    ∀ (P m : ℕ) (τ : Fin m → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) ∧ Module.finrank ℝ (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)))) = m + 1 ∧ ((Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1))) : Submodule ℝ (Eucl (P + 1))) : Set (Eucl (P + 1))) = {z : Eucl (P + 1) | ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z))) ∈ Submodule.span ℝ (range τ)} := by
  intro P m τ hτ
  -- Coordinates: `Φ(s, u) = (s, u₁, …, u_P)`, `e₀ = Φ(1, 0)`, `⟨Φ(a, u), Φ(b, w)⟩ = ab + ⟨u, w⟩`.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  have he₀ : (EuclideanSpace.single 0 1 : Eucl (P + 1)) = Φ 1 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Φ]
    · simp [Φ, Fin.succ_ne_zero]
  have hinner : ∀ (a b : ℝ) (u w : Eucl P), inner ℝ (Φ a u) (Φ b w) = a * b + inner ℝ u w := by
    intro a b u w
    simp only [Φ, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  set v : Fin (m + 1) → Eucl (P + 1) := (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1))
    (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) with hv
  have hv0 : v 0 = Φ 1 0 := by rw [hv, Fin.cons_zero, he₀]
  have hvs : ∀ i : Fin m, v i.succ = Φ 0 (τ i) := fun i => by rw [hv, Fin.cons_succ]
  -- `τ̃ = (Φ(1, 0), Φ(0, τ₁), …, Φ(0, τ_m))` is orthonormal, hence linearly independent.
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · rw [hv0, hinner]; simp
    · rw [hv0, hvs, hinner]; simp [(Fin.succ_ne_zero j').symm]
    · rw [hv0, hvs, hinner]; simp [Fin.succ_ne_zero i']
    · rw [hvs, hvs, hinner, (orthonormal_iff_ite.1 hτ) i' j']
      simp [Fin.succ_inj]
  refine ⟨hon, ?_, ?_⟩
  · rw [finrank_span_eq_card hon.linearIndependent, Fintype.card_fin]
  · -- The projection `π` as a linear map; `span τ̃ = π⁻¹(span τ)`.
    let πₗ : Eucl (P + 1) →ₗ[ℝ] Eucl P :=
      (EuclideanSpace.equiv (Fin P) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.funLeft ℝ ℝ Fin.succ ∘ₗ (EuclideanSpace.equiv (Fin (P + 1)) ℝ).toLinearMap)
    have hπ : ∀ z, πₗ z = (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z)) := fun z => rfl
    have hπΦ : ∀ s u, πₗ (Φ s u) = u := by
      intro s u
      rw [hπ]
      simp only [Φ, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
        ContinuousLinearEquiv.symm_apply_apply]
    have hspan : Submodule.span ℝ (range v) = (Submodule.span ℝ (range τ)).comap πₗ := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [SetLike.mem_coe, Submodule.mem_comap, hv0, hπΦ]
          exact Submodule.zero_mem _
        · simp only [SetLike.mem_coe, Submodule.mem_comap, hvs, hπΦ]
          exact Submodule.subset_span ⟨i', rfl⟩
      · intro z hz
        rw [Submodule.mem_comap, Submodule.mem_span_range_iff_exists_fun] at hz
        obtain ⟨c, hc⟩ := hz
        -- `z = Φ(z₀, π z)` and `Φ` is linear, so `z = z₀ e₀ + ∑ᵢ cᵢ Φ(0, τᵢ)`.
        have hz' : z = (EuclideanSpace.equiv (Fin (P + 1)) ℝ z 0) • v 0 +
            ∑ i, c i • v i.succ := by
          have hdecomp : z = Φ (EuclideanSpace.equiv (Fin (P + 1)) ℝ z 0) (πₗ z) := by
            apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
            simp only [Φ, hπ, ContinuousLinearEquiv.apply_symm_apply]
            exact (Fin.cons_self_tail _).symm
          have hlin : ∀ (a b : ℝ) (u w : Eucl P), Φ a u + Φ b w = Φ (a + b) (u + w) := by
            intro a b u w
            simp only [Φ, ← map_add]
            congr 1
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsmul : ∀ (c : ℝ) (a : ℝ) (u : Eucl P), c • Φ a u = Φ (c * a) (c • u) := by
            intro c a u
            simp only [Φ, ← map_smul]
            congr 1
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsum : ∀ (s : Finset (Fin m)) (a : Fin m → ℝ) (u : Fin m → Eucl P),
              ∑ i ∈ s, Φ (a i) (u i) = Φ (∑ i ∈ s, a i) (∑ i ∈ s, u i) := by
            intro s a u
            induction s using Finset.induction_on with
            | empty =>
              have h00 : Φ 0 0 = 0 := by
                apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
                simp only [Φ, ContinuousLinearEquiv.apply_symm_apply, map_zero]
                ext i
                refine Fin.cases ?_ (fun j => ?_) i <;> simp
              simp [h00]
            | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj,
                Finset.sum_insert hj, ih, hlin]
          rw [hv0]
          simp_rw [hvs, hsmul, hsum, hlin, mul_zero, Finset.sum_const_zero, mul_one, smul_zero,
            zero_add, add_zero, hc]
          exact hdecomp
        rw [hz']
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, rfl⟩))
    rw [hspan]
    rfl
/-- Fubini on the product plane `π⁻¹(T)`, `T = span τ`, for compactly supported continuous `f`
(Simon Ch. 6, 3.2(2), product with an interval).  Write `Φ′(s, u) = (s, u) ∈ ℝ^{P+1}` and
`π(y) = (y₁, …, y_P)`, and assume the product formula (MP) `H^{m+1} ⌞ π⁻¹(A) = Φ′_#(L¹ × Hᵐ ⌞ A)`
for every `Hᵐ`-measurable, countably `m`-rectifiable, locally `Hᵐ`-finite `A ⊆ ℝ^P`.  Then for an
orthonormal `τ`, `∫_{π⁻¹(T)} f dH^{m+1} = ∫_ℝ ∫_T f(Φ′(σ, w)) dHᵐ(w) dσ`.
`T` is closed, has dimension `m`, is the range of the Lipschitz map `u ↦ ∑ uᵢ τᵢ`, and `Hᵐ ⌞ T` is
regular, so (MP) applies to `A = T`.  Change variables along the homeomorphism
`Φ′ : ℝ × ℝ^P ≃ ℝ^{P+1}` and apply Fubini to the compactly supported continuous `f ∘ Φ′`. -/
theorem Submission.iwl_cr_ip_wt_plane_fubini :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ τ : Fin m → Eucl P, Orthonormal ℝ τ → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∫ z in {z : Eucl (P + 1) | ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z))) ∈ Submodule.span ℝ (range τ)}, f z ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫ σ : ℝ, ∫ w in (Submodule.span ℝ (range τ) : Set (Eucl P)), f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) ∂(μHE[m] : Measure (Eucl P)) := by
  intro P m hMP τ hτ f hfc hfcs
  -- Coordinates `Φ(s, u) = (s, u)` and `π(y) = (y₁, …, y_P)`.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- `Φ′ = Φ.uncurry` is a homeomorphism `ℝ × ℝ^P ≃ ℝ^{P+1}` with inverse `y ↦ (y₀, π y)`.
  let e : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => Φ p.1 p.2
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0, π y)
      left_inv := fun p => by
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply]
        exact Fin.cons_self_tail _
      continuous_toFun := hΦc
      continuous_invFun := by
        refine Continuous.prodMk ((continuous_apply 0).comp
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) ?_
        exact (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp
          (continuous_pi fun i : Fin P => (continuous_apply i.succ).comp
            (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) }
  have hemb : MeasurableEmbedding (fun p : ℝ × Eucl P => Φ p.1 p.2) := e.measurableEmbedding
  -- The plane `T = span τ` is `Hᵐ`-measurable, countably `m`-rectifiable and locally `Hᵐ`-finite.
  set T : Submodule ℝ (Eucl P) := Submodule.span ℝ (range τ) with hT
  have hfinT : Module.finrank ℝ T = m := by
    rw [hT, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  have hTmeas : MeasurableSet (T : Set (Eucl P)) := T.closed_of_finiteDimensional.measurableSet
  have hTrect : CountablyRectifiable m (T : Set (Eucl P)) := by
    let Λₗ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] Eucl P :=
      Fintype.linearCombination ℝ τ ∘ₗ (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap
    let Λ : EuclideanSpace ℝ (Fin m) →L[ℝ] Eucl P := LinearMap.toContinuousLinearMap Λₗ
    have hrange : range Λ = (T : Set (Eucl P)) := by
      ext v
      simp only [Λ, LinearMap.coe_toContinuousLinearMap', mem_range, SetLike.mem_coe, hT,
        Submodule.mem_span_range_iff_exists_fun]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨fun i => u i, by simp [Λₗ, Fintype.linearCombination_apply]⟩
      · rintro ⟨c, rfl⟩
        exact ⟨(EuclideanSpace.equiv (Fin m) ℝ).symm c, by
          simp [Λₗ, Fintype.linearCombination_apply]⟩
    rw [← hrange]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range Λ.lipschitzWith
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Eucl P) hfinT
  have hTfin : ∀ K : Set (Eucl P), IsCompact K →
      (μHE[m] : Measure (Eucl P)) ((T : Set (Eucl P)) ∩ K) < ∞ := by
    intro K hK
    rw [inter_comm, ← Measure.restrict_apply hK.measurableSet]
    exact hK.measure_lt_top
  -- (MP) for `A = T`.
  have hMPT : (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {z | π z ∈ T} =
      Measure.map (fun p : ℝ × Eucl P => Φ p.1 p.2)
        ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict (T : Set (Eucl P)))) :=
    hMP (T : Set (Eucl P)) hTmeas.nullMeasurableSet hTrect hTfin
  -- Change of variables along `Φ′`, then Fubini for the integrable `f ∘ Φ′`.
  have hint : Integrable (fun p : ℝ × Eucl P => f (Φ p.1 p.2))
      ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict (T : Set (Eucl P)))) :=
    (hfc.comp e.continuous).integrable_of_hasCompactSupport (hfcs.comp_homeomorph e)
  show ∫ z, f z ∂((μHE[m + 1] : Measure (Eucl (P + 1))).restrict {z | π z ∈ T}) = _
  rw [hMPT, hemb.integral_map, integral_prod _ hint]
/-- Simon Ch. 6, 3.2(2) (product with an interval), Hausdorff measure on `(0,1) × M`.  Write
`Φ(s, u) = (s, u)`, `π(y) = (y₁, …, y_P)` and assume `(MP)`: `H^{m+1} ⌞ π⁻¹(A) = Φ_# (L¹ ⊗ Hᵐ ⌞ A)`
for every `Hᵐ`-measurable, countably `m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for compact
`K`.  Then every such `M` has `H^{m+1} ⌞ {π(y) ∈ M, y₀ ∈ (0,1)} = Φ_# ((L¹ ⌞ (0,1)) ⊗ Hᵐ ⌞ M)`:
restrict `(MP)` for `A = M` to the open slab `O = {y₀ ∈ (0,1)}`, use `Φ⁻¹(O) = (0,1) × ℝ^P`, and
split the restricted product, `Hᵐ ⌞ M` being finite on compact sets, hence σ-finite. -/
theorem Submission.iwl_cr_ip_wt_product_measure :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ M : Set (Eucl P), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} = Measure.map (fun p : ℝ × Eucl P => ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))) (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod ((μHE[m] : Measure (Eucl P)).restrict M)) := by
  intro P m hMP M hMmeas hMrect hMfin
  -- `Φ′(s, u) = (s, u)` is continuous, hence measurable.
  have hΦc : Continuous fun p : ℝ × Eucl P =>
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)) :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- The open slab `O = {y₀ ∈ (0,1)}`: `M̃ = O ∩ π⁻¹(M)` and `Φ′⁻¹(O) = (0,1) × ℝ^P`.
  let O : Set (Eucl (P + 1)) := {y | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}
  have hO : MeasurableSet O :=
    (isOpen_Ioo.preimage ((continuous_apply 0).comp
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous)).measurableSet
  have hset : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} =
      O ∩ {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M} := by
    ext y
    exact and_comm
  have hpre : (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ⁻¹' O =
      Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Eucl P)) := by
    ext p
    simp [O]
  -- `Hᵐ ⌞ M` is finite on compact sets, hence σ-finite.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hMfin K hK⟩
  -- Restrict `(MP)` for `A = M` to `O`, pull back along `Φ′` and split the restricted product.
  rw [hset, ← Measure.restrict_restrict hO, hMP M hMmeas hMrect hMfin,
    Measure.restrict_map hΦc.measurable hO, hpre, ← Measure.prod_restrict, Measure.restrict_univ]
/-- Change of variables under Simon's blow-up `η = η_{x,r}`, `η(z) = r⁻¹(z − x)` (Ch. 3, §1, p. 71),
as used for the locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)): for
`r > 0`, every set `S` and every real function `g`, `∫_{η(S)} g dHⁿ = r⁻ⁿ ∫_S g ∘ η dHⁿ`.
`η` is a homeomorphism (inverse `w ↦ x + r w`) and `η⁻¹(F) = x + r F`, so `Hⁿ(η⁻¹ F) = rⁿ Hⁿ(F)`
by translation invariance and `n`-homogeneity of `Hⁿ`.  Hence `η_# Hⁿ = rⁿ Hⁿ`, and the change of
variables along the measurable embedding `η` needs no integrability. -/
theorem Submission.fiw_tl_blowup_setIntegral :
    ∀ (P n : ℕ) (x : Eucl P) (r : ℝ) (S : Set (Eucl P)) (g : Eucl P → ℝ), 0 < r → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, g y ∂(μHE[n] : Measure (Eucl P)) = (r ^ n)⁻¹ * ∫ z in S, g (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[n] : Measure (Eucl P)) := by
  intro P n x r S g hr
  set η : Eucl P → Eucl P := Poincare.SimonGMT.Chapter03.blowUpMap x r
  have hηapp : ∀ z, η z = r⁻¹ • (z - x) := fun _ => rfl
  -- `η` is a homeomorphism with inverse `w ↦ x + r • w`.
  let e : Eucl P ≃ₜ Eucl P :=
    { toFun := η
      invFun := fun w => x + r • w
      left_inv := fun z => by simp [hηapp, smul_smul, hr.ne']
      right_inv := fun w => by simp [hηapp, smul_smul, hr.ne']
      continuous_toFun := by
        show Continuous fun z : Eucl P => r⁻¹ • (z - x)
        fun_prop
      continuous_invFun := by fun_prop }
  have hemb : MeasurableEmbedding η := e.measurableEmbedding
  have hinj : Function.Injective η := e.injective
  -- `η⁻¹(F) = x + r • F`, so `Hⁿ(η⁻¹ F) = ‖r‖₊ⁿ Hⁿ(F)` for every set `F`.
  have hpre : ∀ F : Set (Eucl P), (μHE[n] : Measure (Eucl P)) (η ⁻¹' F) =
      ‖r‖₊ ^ n • (μHE[n] : Measure (Eucl P)) F := by
    intro F
    have hF : η ⁻¹' F = (fun z => z + -x) ⁻¹' ((fun w => r⁻¹ • w) ⁻¹' F) := by
      ext z
      simp only [mem_preimage, hηapp, sub_eq_add_neg]
    rw [hF, measure_preimage_add_right, preimage_smul_inv₀ hr.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne']
  -- Push-forward: `η_# Hⁿ = ‖r‖₊ⁿ Hⁿ`.
  have hmap : Measure.map η (μHE[n] : Measure (Eucl P)) =
      (‖r‖₊ ^ n) • (μHE[n] : Measure (Eucl P)) := by
    ext F hF
    rw [Measure.map_apply hemb.measurable hF, Measure.smul_apply, hpre]
  -- Change of variables along the measurable embedding `η` (no integrability needed).
  have h := hemb.setIntegral_map (μ := (μHE[n] : Measure (Eucl P))) g (η '' S)
  rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure, preimage_image_eq S hinj,
    NNReal.smul_def, smul_eq_mul] at h
  have hc : ((‖r‖₊ ^ n : ℝ≥0) : ℝ) = r ^ n := by
    rw [NNReal.coe_pow, coe_nnnorm, Real.norm_of_nonneg hr.le]
  rw [hc] at h
  rw [← h, inv_mul_cancel_left₀ (pow_ne_zero n hr.ne')]

/-- Uniform mass bound for the blow-ups `η_r(M)`, `η_r = η_{x,r}` (Ch. 3, §1, p. 71), at a point `x`
with a weighted approximate tangent plane `T` (Ch. 3, 1.7), as used for the product with an interval
(Ch. 6, 3.2(2)): for every `R` there is `B` such that for all small `r > 0`, every `g` with `|g| ≤ C`
vanishing off `B̄(0, R)` satisfies `|∫_{η_r(M)} g(w) θ(x + r w) dHᵐ(w)| ≤ C B`.  Compare with the
cut-off `g₀ = max(0, min(1, R + 1 − ‖w‖)) ∈ C_c`: `|g| ≤ C g₀`, `θ ≥ 0` on `M`, and by the change of
variables `fiw_tl_blowup_setIntegral` the `g₀`-integral tends to `θ(x) ∫_T g₀ dHᵐ < B`. -/
theorem Submission.iwl_cr_ip_wt_blowup_mass_bound :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (T : Submodule ℝ (Eucl P)), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → HasWeightedApproximateTangentSpaceAt m M θ x T → ∀ R : ℝ, ∃ B : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (C : ℝ) (g : Eucl P → ℝ), (∀ w, |g w| ≤ C) → (∀ w, R < ‖w‖ → g w = 0) → |∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, g w * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))| ≤ C * B := by
  intro P m M θ x T hMmeas hθnn hθint hTan R
  -- The cut-off `g₀ = max 0 (min 1 (R + 1 - ‖w‖))`.
  let g₀ : Eucl P → ℝ := fun w => max 0 (min 1 (R + 1 - ‖w‖))
  have hg₀c : Continuous g₀ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hg₀0 : ∀ w, R + 1 < ‖w‖ → g₀ w = 0 := by
    intro w hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  have hg₀cs : HasCompactSupport g₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) (R + 1)) (fun w hw => ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hw
    exact hg₀0 w hw
  have hg₀nn : ∀ w, 0 ≤ g₀ w := fun w => le_max_left _ _
  have hg₀le : ∀ w, g₀ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hg₀1 : ∀ w, ‖w‖ ≤ R → g₀ w = 1 := by
    intro w hw
    show max 0 (min 1 (R + 1 - ‖w‖)) = 1
    rw [min_eq_left (by linarith)]
    exact max_eq_right zero_le_one
  let G₀ : CompactlySupportedContinuousMap (Eucl P) ℝ := ⟨⟨g₀, hg₀c⟩, hg₀cs⟩
  have hlim := hTan.2 G₀
  refine ⟨θ x * ∫ y in (T : Set (Eucl P)), g₀ y ∂(μHE[m] : Measure (Eucl P)) + 1, ?_⟩
  filter_upwards [hlim.eventually_lt_const (lt_add_one _), self_mem_nhdsWithin] with r hrB hr C g hgC hg0
  have hr0 : (0 : ℝ) < r := hr
  -- `θ` is a.e. strongly measurable and a.e. nonnegative for `Hᵐ ⌞ M`.
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  have hθpos : ∀ᵐ u ∂((μHE[m] : Measure (Eucl P)).restrict M), 0 ≤ θ u :=
    (ae_restrict_mem₀ hMmeas).mono fun u hu => hθnn u hu
  -- Undo the blow-up for any integrand.
  have hcov : ∀ h : Eucl P → ℝ, ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      h w * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)) = (r ^ m)⁻¹ * ∫ u in M,
        h (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u ∂(μHE[m] : Measure (Eucl P)) := by
    intro h
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => h w * θ (x + r • w)) hr0]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul,
      add_sub_cancel]
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  have hηnorm : ∀ u, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r u‖ = r⁻¹ * ‖u - x‖ := by
    intro u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr0]
  -- Integrability of `u ↦ g₀(η u) θ(u)` on `M`.
  have hint₀ : Integrable (fun u => g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u)
      ((μHE[m] : Measure (Eucl P)).restrict M) := by
    refine Integrable.mono' (g := (closedBall x (r * (R + 1))).indicator fun u => |θ u|) ?_
      ((hg₀c.comp hηc).aestronglyMeasurable.mul hθae) (Filter.Eventually.of_forall fun u => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact (hθint _ (isCompact_closedBall x (r * (R + 1)))).norm.congr
        (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
    · by_cases hu : u ∈ closedBall x (r * (R + 1))
      · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ u), Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _)
          ((abs_of_nonneg (hg₀nn _)).trans_le (hg₀le _))
      · rw [indicator_of_notMem hu, hg₀0, zero_mul, norm_zero]
        rw [mem_closedBall, dist_eq_norm, not_le] at hu
        rw [hηnorm, lt_inv_mul_iff₀ hr0]
        exact hu
  -- `C ≥ 0`, and `|g(η u)| θ(u) ≤ C g₀(η u) θ(u)` on `M`.
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have hpt : ∀ w, |g w| ≤ C * g₀ w := by
    intro w
    by_cases hw : ‖w‖ ≤ R
    · rw [hg₀1 w hw, mul_one]
      exact hgC w
    · rw [hg0 w (not_le.1 hw), abs_zero]
      exact mul_nonneg hC (hg₀nn w)
  have hkey : |∫ u in M, g (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
      ∂(μHE[m] : Measure (Eucl P))| ≤
      C * ∫ u in M, g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P)) := by
    rw [← integral_const_mul]
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
      (hint₀.const_mul C) ?_
    filter_upwards [hθpos] with u hu
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hpt _) hu
  rw [hcov g, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr0 m))]
  have hb := hcov g₀
  calc (r ^ m)⁻¹ * |∫ u in M, g (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P))|
      ≤ (r ^ m)⁻¹ * (C * ∫ u in M, g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P))) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 (pow_nonneg hr0.le m))
    _ = C * ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, g₀ w * θ (x + r • w)
        ∂(μHE[m] : Measure (Eucl P)) := by rw [hb]; ring
    _ ≤ C * (θ x * ∫ y in (T : Set (Eucl P)), g₀ y ∂(μHE[m] : Measure (Eucl P)) + 1) :=
        mul_le_mul_of_nonneg_left hrB.le hC
/-- Blow-ups of the product `(0, 1) × M ⊆ ℝ^{P+1}` slice into blow-ups of `M` (Simon Ch. 6, 3.2(2)).
With `Φ(s, u) = (s, u)`, `π(y) = (y₁, …, y_P)`, `y* = Φ(s₀, x)` and `r > 0`, and assuming the
product formula `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)` for countably `m`-rectifiable `A`:
`∫_{η_{y*,r}((0,1) × M)} f(z) θ(π(y* + r z)) dH^{m+1}(z)
  = ∫_{(−s₀/r, (1−s₀)/r]} ∫_{η_{x,r}(M)} f(Φ(σ, w)) θ(x + r w) dHᵐ(w) dσ`.
Undo both blow-ups (`fiw_tl_blowup_setIntegral`), pass to `(L¹⌞(0,1)) ⊗ Hᵐ⌞M`
(`iwl_cr_ip_wt_product_measure`), apply Fubini and substitute `s = s₀ + r σ`. -/
theorem Submission.iwl_cr_ip_wt_slice_identity :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (s₀ : ℝ), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) r '' {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}, f z * θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ (((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) + r • z)))) ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫ σ : ℝ, (Ioc (-s₀ / r) ((1 - s₀) / r)).indicator (fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))) σ := by
  intro P m hMP M θ x s₀ hMmeas hMrect hMfin hθint f hfc hfcs r hr
  -- Coordinates.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hπΦ : ∀ s u, π (Φ s u) = u := by
    intro s u
    simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  have hΦsub : ∀ s u s' u', Φ s u - Φ s' u' = Φ (s - s') (u - u') := by
    intro s u s' u'
    simp only [Φ, ← map_sub]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hΦsmul : ∀ (c s : ℝ) (u : Eucl P), c • Φ s u = Φ (c * s) (c • u) := by
    intro c s u
    simp only [Φ, ← map_smul]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hnorm : ∀ (s : ℝ) (u : Eucl P), ‖u‖ ≤ ‖Φ s u‖ := by
    intro s u
    have h : ‖Φ s u‖ ^ 2 = s ^ 2 + ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    exact le_of_sq_le_sq (by rw [h]; nlinarith [sq_nonneg s]) (norm_nonneg _)
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  let e : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => Φ p.1 p.2
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0, π y)
      left_inv := fun p => by
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply]
        exact Fin.cons_self_tail _
      continuous_toFun := hΦc
      continuous_invFun := by
        refine Continuous.prodMk ((continuous_apply 0).comp
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) ?_
        exact (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp
          (continuous_pi fun i : Fin P => (continuous_apply i.succ).comp
            (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) }
  have hemb : MeasurableEmbedding (fun p : ℝ × Eucl P => Φ p.1 p.2) := e.measurableEmbedding
  -- Support radius and sup bound of `f`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : Eucl (P + 1), f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz => ?_⟩
    simpa using hR (subset_tsupport _ hz)
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C := hfc.bounded_above_of_compact_support hfcs
  -- `ν = Hᵐ ⌞ M` is finite on compacts (so σ-finite) and `θ` is a.e. strongly measurable for it.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hMfin K hK⟩
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  -- Blow-up maps.
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  have hηnorm : ∀ u, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r u‖ = r⁻¹ * ‖u - x‖ := by
    intro u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr]
  -- Blow-ups of the product are products of blow-ups.
  have hprod : ∀ s u, Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ s u) =
      Φ (r⁻¹ * (s - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r u) := by
    intro s u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, hΦsub, hΦsmul]
  -- The integrand on the product and its integrability.
  let G : ℝ × Eucl P → ℝ := fun p =>
    f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) * θ p.2
  have hGint : Integrable G (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
      ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    have hbint : Integrable ((closedBall x (r * R)).indicator fun u => Cf * |θ u|)
        ((μHE[m] : Measure (Eucl P)).restrict M) := by
      rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact ((hθint _ (isCompact_closedBall x (r * R))).norm.const_mul Cf).congr
        (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
    refine Integrable.mono' (hbint.comp_snd _) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul ?_ hθae.comp_snd
      refine Continuous.aestronglyMeasurable ?_
      exact hfc.comp (hΦc.comp
        ((continuous_const.mul (continuous_fst.sub continuous_const)).prodMk
          (hηc.comp continuous_snd)))
    · show ‖G p‖ ≤ (closedBall x (r * R)).indicator (fun u => Cf * |θ u|) p.2
      by_cases hu : p.2 ∈ closedBall x (r * R)
      · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ p.2)]
        exact mul_le_mul_of_nonneg_right (hCf _) (abs_nonneg _)
      · rw [indicator_of_notMem hu]
        have hf0 :
            f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) = 0 := by
          by_contra h
          apply hu
          have h1 := (hnorm _ _).trans (hR _ h)
          rw [hηnorm, inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          exact h1
        show ‖f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) * θ p.2‖ ≤ 0
        rw [hf0, zero_mul, norm_zero]
  -- Undo the blow-up in `ℝ^{P+1}` and pass to the product measure.
  have hL1 : ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r ''
        {y : Eucl (P + 1) | π y ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1},
        f z * θ (π (Φ s₀ x + r • z)) ∂(μHE[m + 1] : Measure (Eucl (P + 1))) =
      (r ^ (m + 1))⁻¹ * ∫ p, G p ∂(((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
        ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    rw [Submission.fiw_tl_blowup_setIntegral (P + 1) (m + 1) (Φ s₀ x) r _
      (fun z => f z * θ (π (Φ s₀ x + r • z))) hr]
    congr 1
    have hmeas := Submission.iwl_cr_ip_wt_product_measure P m hMP M hMmeas hMrect hMfin
    show ∫ w, f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w) *
        θ (π (Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w))
        ∂((μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y : Eucl (P + 1) | π y ∈ M ∧
            EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}) = _
    rw [hmeas, hemb.integral_map]
    have hback : ∀ w, Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w = w := by
      intro w
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
        one_smul, add_sub_cancel]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ p.1 p.2)) *
      θ (π (Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ p.1 p.2))) = G p
    rw [hback, hπΦ, hprod]
  -- Fubini and the interval.
  let H : ℝ → ℝ := fun s => ∫ u in M, G (s, u) ∂(μHE[m] : Measure (Eucl P))
  have hL2 : ∫ p, G p ∂(((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
        ((μHE[m] : Measure (Eucl P)).restrict M)) = ∫ s in (0 : ℝ)..1, H s := by
    rw [integral_prod _ hGint, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  -- Substitution `s = r σ + s₀`.
  have hsub : ∫ σ in (-s₀ / r)..((1 - s₀) / r), H (r * σ + s₀) = r⁻¹ * ∫ s in (0 : ℝ)..1, H s := by
    rw [intervalIntegral.integral_comp_mul_add H hr.ne' s₀, smul_eq_mul]
    congr 3
    · field_simp
      ring
    · field_simp
      ring
  -- The slices: `H (r σ + s₀) = rᵐ · a σ`.
  have hslice : ∀ σ : ℝ, H (r * σ + s₀) =
      r ^ m * ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
        f (Φ σ w) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)) := by
    intro σ
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => f (Φ σ w) * θ (x + r • w)) hr,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hr.ne'), one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hσ : r⁻¹ * (r * σ + s₀ - s₀) = σ := by
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    simp only [G, hσ, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
      one_smul, add_sub_cancel]
  -- Assemble.
  have hab : -s₀ / r ≤ (1 - s₀) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  rw [hL1, hL2, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hab]
  have hsub' := hsub
  simp only [hslice, intervalIntegral.integral_const_mul] at hsub'
  -- `hsub' : r ^ m * ∫ a = r⁻¹ * ∫₀¹ H`
  have hrm : (r ^ (m + 1))⁻¹ = (r ^ m)⁻¹ * r⁻¹ := by rw [pow_succ, mul_inv]
  rw [hrm, mul_assoc, ← hsub', ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hr.ne'), one_mul]
/-- Continuity in `σ` of the blown-up slice integrals (Simon Ch. 6, 3.2(2), product with an
interval): if `θ` is `Hᵐ`-integrable on `M ∩ K` for every compact `K`, `f ∈ C_c(ℝ^{P+1})` and
`r > 0`, then `σ ↦ ∫_{η(M)} f(σ, w) θ(x + r w) dHᵐ(w)` is continuous, `η = η_{x,r}`.  Undoing the
blow-up (`fiw_tl_blowup_setIntegral`) gives `r⁻ᵐ ∫_M f(σ, η u) θ(u) dHᵐ(u)`, continuous by dominated
convergence with the `σ`-independent bound `sup |f| · |θ| · 1_{B̄(x, r R)}`, `spt f ⊆ B̄(0, R)`. -/
theorem Submission.iwl_cr_ip_wt_slice_continuous :
    ∀ (P m : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P), (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))) := by
  intro P m M θ x hθint f hfc hfcs r hr
  -- Coordinates `Φ(s, u) = (s, u₁, …, u_P)`, with `‖u‖ ≤ ‖Φ(s, u)‖`.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  have hnorm : ∀ (s : ℝ) (u : Eucl P), ‖u‖ ≤ ‖Φ s u‖ := by
    intro s u
    have h : ‖Φ s u‖ ^ 2 = s ^ 2 + ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    exact le_of_sq_le_sq (by rw [h]; nlinarith [sq_nonneg s]) (norm_nonneg _)
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  -- Support radius and sup bound of `f`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : Eucl (P + 1), f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz => ?_⟩
    simpa using hR (subset_tsupport _ hz)
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C := hfc.bounded_above_of_compact_support hfcs
  -- `θ` is a.e. strongly measurable for `Hᵐ ⌞ M` (exhaust `M` by the compact balls `B̄(0, n)`).
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  -- Undo the blow-up: the slice integral is `r⁻ᵐ ∫_M f(Φ(σ, η u)) θ(u) dHᵐ(u)`.
  have hcov : ∀ σ : ℝ, ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f (Φ σ w) * θ (x + r • w)
      ∂(μHE[m] : Measure (Eucl P)) = (r ^ m)⁻¹ * ∫ u in M,
        f (Φ σ (Poincare.SimonGMT.Chapter03.blowUpMap x r u)) * θ u ∂(μHE[m] : Measure (Eucl P)) := by
    intro σ
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => f (Φ σ w) * θ (x + r • w)) hr]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
      add_sub_cancel]
  show Continuous fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
    f (Φ σ w) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))
  simp_rw [hcov]
  refine continuous_const.mul ?_
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  -- Dominated convergence with the `σ`-independent bound `1_{B̄(x, r R)} · Cf · |θ|`.
  refine continuous_of_dominated
    (bound := (closedBall x (r * R)).indicator fun u => Cf * |θ u|) (fun σ => ?_) (fun σ => ?_) ?_ ?_
  · exact ((hfc.comp (hΦc.comp (continuous_const.prodMk hηc))).aestronglyMeasurable).mul hθae
  · refine Filter.Eventually.of_forall fun u => ?_
    by_cases hu : u ∈ closedBall x (r * R)
    · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ u)]
      exact mul_le_mul_of_nonneg_right (hCf _) (abs_nonneg _)
    · rw [indicator_of_notMem hu]
      have hf0 : f (Φ σ (Poincare.SimonGMT.Chapter03.blowUpMap x r u)) = 0 := by
        by_contra h
        apply hu
        have h1 := (hnorm σ _).trans (hR _ h)
        rw [mem_closedBall, dist_eq_norm]
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hr] at h1
        rw [inv_mul_le_iff₀ hr] at h1
        exact h1
      rw [hf0, zero_mul, norm_zero]
  · rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact ((hθint _ (isCompact_closedBall x (r * R))).norm.const_mul Cf).congr
      (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (hfc.comp (hΦc.comp (continuous_id.prodMk continuous_const))).mul continuous_const

/-- Simon Ch. 3, 1.7 for the product of the unit interval with `(M, θ)`: if `span τ` is a weighted
approximate tangent space of `(M, θ)` at `x`, then `span (e₀, ιτ)` is one of
`(M̃, θ ∘ π)`, `M̃ = {y : π y ∈ M, y₀ ∈ (0, 1)}`, at `Φ(s₀, x)` for `0 < s₀ < 1`.
By the slice identity the blow-up integrals at `Φ(s₀, x)` are
`∫_ℝ 1_{(-s₀/r, (1-s₀)/r]}(σ) a_r(σ) dσ`, where `a_r(σ)` is the blow-up integral of `(M, θ)` at `x`
against `f(Φ(σ, ·))`.  Dominated convergence in `σ` (uniform blow-up mass bound, continuity in
`σ`) and Fubini on the plane `π⁻¹(span τ) = span (e₀, ιτ)` give the limit
`θ(x) ∫_{span (e₀, ιτ)} f dH^{m+1}`. -/
theorem Submission.iwl_cr_ip_product_weighted_tangent :
    ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (τ : Fin m → Eucl P) (s₀ : ℝ), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → Orthonormal ℝ τ → HasWeightedApproximateTangentSpaceAt m M θ x (Submodule.span ℝ (range τ)) → s₀ ∈ Ioo (0 : ℝ) 1 → HasWeightedApproximateTangentSpaceAt (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)))) := by
  have h_plane := Submission.iwl_cr_ip_wt_product_plane
  have h_fubini := Submission.iwl_cr_ip_wt_plane_fubini
  have h_bound := Submission.iwl_cr_ip_wt_blowup_mass_bound
  have h_slice := Submission.iwl_cr_ip_wt_slice_identity
  have h_cont := Submission.iwl_cr_ip_wt_slice_continuous
  intro P m hMP M θ x τ s₀ hMmeas hMrect hMfin hθnn hθint hτ hT hs₀
  -- Steps 1–2 (`product_plane`): `finrank Q = m + 1` and `Q = π⁻¹(span τ)` as sets.
  obtain ⟨-, hQrank, hQset⟩ := h_plane P m τ hτ
  refine And.intro hQrank (fun f => ?_)
  have hfc : Continuous f := f.continuous
  have hfs : HasCompactSupport f := f.hasCompactSupport
  -- Coordinates: `‖Φ(σ, w)‖² = σ² + ‖w‖²`, hence `|σ| ≤ ‖Φ(σ, w)‖` and `‖w‖ ≤ ‖Φ(σ, w)‖`.
  have hnsq : ∀ (σ : ℝ) (w : Eucl P), ‖(EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))‖ ^ 2 = σ ^ 2 + ‖w‖ ^ 2 := by
    intro σ w
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp
  have hN0 : ∀ (σ : ℝ) (w : Eucl P), |σ| ≤ ‖(EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))‖ := fun σ w =>
    le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
      (by rw [hnsq, sq_abs]; nlinarith [sq_nonneg ‖w‖])
  have hN1 : ∀ (σ : ℝ) (w : Eucl P), ‖w‖ ≤ ‖(EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))‖ := fun σ w =>
    le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (by rw [hnsq]; nlinarith [sq_nonneg σ])
  -- Step 5: `f` vanishes outside `B̄(0, R)` and `|f| ≤ C`.
  obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall (0 : Eucl (P + 1))
  have hfz : ∀ z : Eucl (P + 1), R < ‖z‖ → f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => (not_le.2 hz) (mem_closedBall_zero_iff.1 (hR h))
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfs
  -- Step 15: the limit is `θ(x) ∫_ℝ ∫_{span τ} f(Φ(σ, w)) dHᵐ(w) dσ`, since
  -- `θ̃(Φ(s₀, x)) = θ(x)`, `Q = π⁻¹(span τ)` and by `plane_fubini`.
  have hθc : θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ
      ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x)))))) = θ x := by
    rw [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  beta_reduce
  rw [hθc, hQset, h_fubini P m hMP τ hτ f hfc hfs, ← integral_const_mul]
  -- Steps 7–10 (`slice_identity`): for `r > 0` the blow-up integral equals
  -- `∫_ℝ 1_{(-s₀/r, (1-s₀)/r]}(σ) a_r(σ) dσ`.
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun r : ℝ => ∫ σ : ℝ,
    (Ioc (-s₀ / r) ((1 - s₀) / r)).indicator (fun σ : ℝ =>
      ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
        f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) *
          θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))) σ) (𝓝[>] 0) _)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (h_slice P m hMP M θ x s₀ hMmeas hMrect hMfin hθint f hfc hfs r hr).symm
  -- Step 14: dominated convergence in the interval variable.
  obtain ⟨B, hB⟩ := h_bound P m M θ x (Submodule.span ℝ (range τ)) hMmeas hθnn hθint hT R
  refine tendsto_integral_filter_of_dominated_convergence
    (fun σ => (Icc (-R) R).indicator (fun _ => C * B) σ) ?_ ?_ ?_ ?_
  · -- Step 13 (`slice_continuous`): measurability in `σ`.
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (h_cont P m M θ x hθint f hfc hfs r hr).aestronglyMeasurable.indicator measurableSet_Ioc
  · -- Step 12 (`blowup_mass_bound`): `|a_r(σ)| ≤ C B`, and `a_r(σ) = 0` for `|σ| > R`.
    filter_upwards [hB] with r hr
    refine ae_of_all _ fun σ => (norm_indicator_le_norm_self _ _).trans ?_
    rw [Real.norm_eq_abs]
    by_cases hσ : σ ∈ Icc (-R) R
    · rw [indicator_of_mem hσ]
      exact hr C (fun w => f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))))
        (fun w => by rw [← Real.norm_eq_abs]; exact hC _)
        (fun w hw => hfz _ (hw.trans_le (hN1 σ w)))
    · rw [indicator_of_notMem hσ]
      have hRσ : R < |σ| := not_le.1 fun h => hσ (abs_le.1 h)
      have h0 : ∀ w : Eucl P, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) = 0 :=
        fun w => hfz _ (hRσ.trans_le (hN0 σ w))
      simpa using hr 0 (fun w => f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))))
        (fun w => by rw [h0]; simp) (fun w _ => h0 w)
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · -- Step 11: pointwise convergence from the tangent hypothesis for `f(Φ(σ, ·))`.
    refine ae_of_all _ fun σ => ?_
    have hmem : ∀ᶠ r in 𝓝[>] (0 : ℝ), σ ∈ Ioc (-s₀ / r) ((1 - s₀) / r) := by
      have hε : 0 < min s₀ (1 - s₀) / (|σ| + 1) :=
        div_pos (lt_min hs₀.1 (sub_pos.2 hs₀.2)) (by positivity)
      filter_upwards [Ioo_mem_nhdsGT hε] with r hr
      obtain ⟨hr0, hrε⟩ := hr
      have h1 : r * (|σ| + 1) < min s₀ (1 - s₀) := (lt_div_iff₀ (by positivity)).1 hrε
      have h2 := min_le_left s₀ (1 - s₀)
      have h3 := min_le_right s₀ (1 - s₀)
      constructor
      · rw [div_lt_iff₀ hr0]
        nlinarith [neg_abs_le σ, abs_nonneg σ]
      · rw [le_div_iff₀ hr0]
        nlinarith [le_abs_self σ, abs_nonneg σ]
    let fσ : CompactlySupportedContinuousMap (Eucl P) ℝ :=
      ⟨⟨fun w => f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))), by fun_prop⟩,
        HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) R) fun w hw =>
          hfz _ ((not_le.1 fun h => hw (mem_closedBall_zero_iff.2 h)).trans_le (hN1 σ w))⟩
    refine (hT.2 fσ).congr' ?_
    filter_upwards [hmem] with r hr
    refine Eq.symm ?_
    exact indicator_of_mem hr _

/-- **The product triple `(0, 1) × (M, θ, ξ)` (Simon Ch. 6, 3.2(2)).**  Write
`Φ(s, x) = (s, x)`, `π(y) = (y₁, …, y_P)`, `e₀ = (1, 0)` and `ι(v) = Φ(0, v)`, and assume the
product formula (MP) `H^{m+1}⌞{π ∈ A} = Φ_*(L¹ ⊗ Hᵐ⌞A)` for every `Hᵐ`-measurable countably
`m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for compact `K`.  If `(M, θ, ξ)` is a rectifiable
`m`-triple in `ℝ^P` with `θ ≥ 1` on `M`, then `((0, 1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` is a rectifiable
`(m + 1)`-triple in `ℝ^{P+1}`; here `e₀ ∧ ξ ∘ π` is characterized by
`⟨α, ξ′(Φ(s, x))⟩ = ⟨β, ξ(x)⟩` whenever `β(v) = α(e₀, ιv₁, …, ιvₘ)`. -/
theorem Submission.iwl_cr_ip_product_triple : ∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m), IsRectifiableTriple (univ : Set (Eucl P)) m M θ ξ → (∀ x ∈ M, 1 ≤ θ x) → ∃ ξ' : Eucl (P + 1) → NVector (Eucl (P + 1)) (m + 1), IsRectifiableTriple (univ : Set (Eucl (P + 1))) (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ξ' ∧ ∀ (s : ℝ) (x : Eucl P) (α : Covector (Eucl (P + 1)) (m + 1)) (β : Covector (Eucl P) m), (∀ v : Fin m → Eucl P, β v = α (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → ξ' ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) α = ξ x β := by
  intro P m hMP M θ ξ hT hθ1
  -- (D1): cylinders over `Hᵐ`-null sets are `H^{m+1}`-null ((MP) with `Hᵐ⌞N = 0`).
  have hNT : ∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1)))
        {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 := by
    intro N hN
    have h := hMP N (NullMeasurableSet.of_null hN)
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hN)
      (fun K _ => (measure_mono_null inter_subset_left hN).trans_lt ENNReal.zero_lt_top)
    rw [Measure.restrict_eq_zero.mpr hN, Measure.prod_zero, Measure.map_zero] at h
    exact Measure.restrict_eq_zero.mp h
  -- Step 1: `Hᵐ(M ∩ K) ≤ ∫_{M ∩ K} |θ| dHᵐ < ∞` for compact `K`, since `θ ≥ 1` on `M`.
  have hlf : ∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞ := by
    intro K hK
    have hI := hT.integrableOn K hK (subset_univ K)
    have hnm : NullMeasurableSet (M ∩ K) (μHE[m] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet
    calc (μHE[m] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, 1 ∂(μHE[m] : Measure (Eucl P)) := by
          rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[m] : Measure (Eucl P)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hnm] with x hx
          rw [← ofReal_norm, ENNReal.one_le_ofReal, Real.norm_eq_abs]
          exact (hθ1 x hx.1).trans (le_abs_self _)
      _ < ∞ := hI.2
  -- Step 2: the contraction `ℒ α = α(e₀, ι ·)`, a continuous linear map `Λ^{m+1} → Λ^m`.
  obtain ⟨L, hL⟩ : ∃ L : Covector (Eucl (P + 1)) (m + 1) →L[ℝ] Covector (Eucl P) m,
      ∀ (α : Covector (Eucl (P + 1)) (m + 1)) (v : Fin m → Eucl P),
        L α v = α (Fin.cons (EuclideanSpace.single 0 1) fun i =>
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) := by
    let ι : Eucl P →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
      { toFun := fun v => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ v))
        map_add' := by
          intro v w
          apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
          simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := by
          intro c v
          apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
          simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    exact ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM ι).comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single 0 1 : Eucl (P + 1))).comp
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl (P + 1)) (F := ℝ)
          (n := m)).toContinuousLinearMap), fun α v => rfl⟩
  -- `ξ′(y) := ξ(π y) ∘ ℒ`, i.e. `⟨α, ξ′(y)⟩ = ⟨ℒ α, ξ(π y)⟩`.
  refine ⟨fun y => (ξ ((EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))).comp L, ?_, ?_⟩
  swap
  · -- Step 3: `ξ′(Φ(s, x))(α) = ξ(x)(ℒ α) = ξ(x)(β)`, as `π(Φ(s, x)) = x` and `ℒ α = β`.
    intro s x α β hβ
    have hLβ : L α = β := by
      ext v
      rw [hL α v, hβ v]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
      Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply, hLβ]
  -- The slab `O = {y₀ ∈ (0, 1)}` is Borel, `π` is continuous, and `M̃ = {π ∈ M} ∩ O` is
  -- `H^{m+1}`-null-measurable (Step 5, child `cylinder_null_measurable`).
  have hOm : MeasurableSet
      {y : Eucl (P + 1) | EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage
      ((continuous_apply 0).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous).measurable
  have hπc : Continuous (fun y : Eucl (P + 1) => (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) := by
    refine (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp ?_
    exact continuous_pi fun i =>
      (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
  have hMt_nm : NullMeasurableSet {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}
      (μHE[m + 1] : Measure (Eucl (P + 1))) :=
    (Submission.iwl_cr_ip_pt_cylinder_nullMeasurableSet P m hNT M hT.nullMeasurableSet).inter
      hOm.nullMeasurableSet
  -- Step 4 (`subset`) and Step 5 (`nullMeasurableSet`).
  refine ⟨subset_univ _, hMt_nm, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 6: `M̃ ⊆ {π ∈ M}`, countably `(m + 1)`-rectifiable (child `cylinder_rectifiable`).
    exact (Submission.iwl_cr_ip_pt_cylinder_countablyRectifiable P m hNT M
      hT.countablyRectifiable).mono (fun y hy => hy.1)
  · -- Step 7: `θ̃(y) = θ(π y) > 0` on `M̃`.
    exact fun y hy => hT.pos _ hy.1
  · -- Step 8: `M̃ ∩ K′` lies in the slab over `M ∩ π(K′)`, on which `θ ∘ π` is integrable
    -- (child `slab_transfer` (a); `π(K′)` is compact).
    intro K' hK' _
    have hK : IsCompact ((fun y : Eucl (P + 1) => (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) '' K') := hK'.image hπc
    have hA := (Submission.iwl_cr_ip_pt_slab_transfer P m hMP (M ∩ _)
      (hT.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet)
      (hT.countablyRectifiable.mono inter_subset_left)
      (fun K'' hK'' => (measure_mono (inter_subset_inter_left _ inter_subset_left)).trans_lt
        (hlf K'' hK''))).1 θ (hT.integrableOn _ hK (subset_univ _))
    refine hA.mono_set ?_
    rintro y ⟨⟨hyM, hy0⟩, hyK'⟩
    exact ⟨⟨hyM, ⟨y, hyK', rfl⟩⟩, hy0⟩
  · -- Step 9: `ξ ∘ π` is a.e. strongly measurable on `M̃` (child `slab_transfer` (b)), and
    -- `T ↦ T ∘ ℒ` is continuous.
    have hξ := (Submission.iwl_cr_ip_pt_slab_transfer P m hMP M hT.nullMeasurableSet
      hT.countablyRectifiable hlf).2 ξ hT.aestronglyMeasurable
    exact (continuous_id.clm_comp continuous_const).comp_aestronglyMeasurable hξ
  · -- Step 10: the orientation fails at most on the cylinder over the `Hᵐ`-null set `N` of bad
    -- points of `M`, which is `H^{m+1}`-null by (D1).
    have hgood := hT.orients
    rw [ae_iff, Measure.restrict_apply₀' hT.nullMeasurableSet] at hgood
    have hNπ := hNT _ hgood
    rw [ae_iff, Measure.restrict_apply₀' hMt_nm]
    refine measure_mono_null ?_ hNπ
    rintro y ⟨hyQ, hyM, hy0⟩
    refine ⟨fun hgx => hyQ ?_, hyM⟩
    obtain ⟨τ, hτ, htan, hsign⟩ := hgx
    -- `y = Φ(y₀, π y)` with `y₀ ∈ (0, 1)`; the frame `τ̃ = (e₀, ιτ₁, …, ιτₘ)` is orthonormal
    -- (child `frame_orthonormal`) and spans the weighted tangent plane of `(M̃, θ̃)` at `y`
    -- (sibling `product_tangent`).
    have hy : (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin P) ℝ ((EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))))) = y := by
      simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
        ContinuousLinearEquiv.symm_apply_apply]
    have htan' := Submission.iwl_cr_ip_product_weighted_tangent P m hMP M θ _ τ _
      hT.nullMeasurableSet hT.countablyRectifiable hlf (fun z hz => (hT.pos z hz).le)
      (fun K hK => hT.integrableOn K hK (subset_univ K)) hτ htan hy0
    rw [hy] at htan'
    -- `(τ₁ ∧ ⋯ ∧ τₘ) ∘ ℒ = e₀ ∧ ιτ₁ ∧ ⋯ ∧ ιτₘ`, so `ξ′(y) = ±τ̃₀ ∧ ⋯ ∧ τ̃ₘ`.
    have hsimple : (simpleNVector τ).comp L = simpleNVector
        (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i =>
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) := by
      ext α
      simp only [ContinuousLinearMap.comp_apply, simpleNVector_apply]
      exact hL α τ
    refine ⟨_, Submission.iwl_cr_ip_pt_frame_orthonormal P m τ hτ, htan', ?_⟩
    rcases hsign with h | h
    · left
      rw [h, hsimple]
    · right
      rw [h, ContinuousLinearMap.neg_comp, hsimple]
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

/-- **`τ(M, θ, ξ)` is a current (Simon Ch. 6, 3.1, p. 146).**  For a rectifiable triple `(M, θ, ξ)`
in `V` (`V` need not be open), `ω ↦ τ(M, θ, ξ)(ω) = ∫_M θ(x) ⟨ω(x), ξ(x)⟩ dHⁿ(x)` is a current
`X ∈ 𝒟ₙ(V)`.  It is linear since the integrands are `Hⁿ`-integrable on `M` (`ltg_tau_integrable`).
It is sequentially continuous: if `ω_j → 0` in `𝒟ⁿ(V)`, all supports lie in one compact `K ⊆ V`
and `sup_K ‖ω_j‖ → 0`; as `|⟨α, ξ(x)⟩| ≤ ‖α‖` for `Hⁿ⌞M`-a.e. `x` (`fiw_ims_tt_unit_bound`) and
`θ > 0` on `M`, `|τ(ω_j)| ≤ (sup_K ‖ω_j‖) ∫_{M ∩ K} θ dHⁿ → 0`. -/
theorem Submission.br_loc_tauAction_current : ∀ (P n : ℕ) (V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple V n M θ ξ → ∃ X : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, X ω = tauAction n M θ ξ ω := by
  intro P n V M θ ξ hTr
  -- Step 1: for every test form `ω` (smooth, hence continuous, with compact support in `V`),
  -- `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hⁿ`-integrable on `M`.
  have hint : ∀ ω : TestFormOn V n, IntegrableOn
      (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)) M (μHE[n] : Measure (Eucl P)) :=
    fun ω => (Submission.ltg_tau_integrable P n V M θ ξ hTr).2 _
      ω.property.1.1.continuous ω.property.1.2 ω.property.2
  -- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨α, ξ(x)⟩| ≤ ‖α‖` for every
  -- covector `α`, for `Hⁿ⌞M`-a.e. `x`.
  have hub : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) n, |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hTr.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    exact Submission.fiw_ims_tt_unit_bound P n τ (ξ x) hτ hξ
  -- Step 3: `ω ↦ τ(M, θ, ξ)(ω)` is linear (additivity of the integral of integrable functions;
  -- constants factor out of the integral).
  let L : CurrentOn V n :=
    { toFun := fun ω => tauAction n M θ ξ ω
      map_add' := by
        intro ω η
        simp only [tauAction]
        rw [← integral_add (hint ω) (hint η)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add]
      map_smul' := by
        intro c ω
        simp only [tauAction, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- Sequential continuity: let `ω_j → 0` in `𝒟ⁿ(V)`, all supported in the compact `K ⊆ V`.
  intro ωs hconv
  obtain ⟨K, hK, hKV, hsupp, -, hderiv⟩ := hconv
  -- Step 4: `sup_K ‖ω_j‖ → 0` (uniform convergence of order `0`, `‖D⁰ω(x)‖ = ‖ω(x)‖`).
  have hsmall : ∀ δ > 0, ∀ᶠ j in atTop, ∀ x ∈ K,
      ‖(ωs j : DifferentialForm (Eucl P) n) x‖ < δ := by
    intro δ hδ
    have h0 := (Metric.tendstoUniformlyOn_iff.mp (hderiv 0)) δ hδ
    filter_upwards [h0] with j hj x hx
    have := hj x hx
    rw [dist_comm, dist_eq_norm] at this
    simpa [norm_iteratedFDeriv_zero] using this
  -- Step 5: the majorant `1_K θ` is `Hⁿ⌞M`-integrable, with integral `C = ∫_{M ∩ K} θ dHⁿ`.
  have hIK : IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    hTr.integrableOn K hK hKV
  set C : ℝ := ∫ x in M ∩ K, θ x ∂(μHE[n] : Measure (Eucl P))
  have hgint : Integrable (K.indicator θ) ((μHE[n] : Measure (Eucl P)).restrict M) := by
    rw [integrable_indicator_iff hK.measurableSet, IntegrableOn,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact hIK
  have hgC : ∫ x, K.indicator θ x ∂((μHE[n] : Measure (Eucl P)).restrict M) = C := by
    rw [integral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_comm]
  -- Step 6: with `δ = ε / (|C| + 1)` and `j` large, `|θ ⟨ω_j, ξ⟩| ≤ δ 1_K θ` `Hⁿ⌞M`-a.e. (on `K`
  -- by Steps 2 and 4 and `θ > 0` on `M`; off `K` since `ω_j = 0` there), so
  -- `|τ(ω_j)| ≤ δ C ≤ δ |C| < ε`.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (|C| + 1) := by positivity
  filter_upwards [hsmall _ hδ] with j hj
  rw [Real.dist_eq, sub_zero]
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      ‖θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
        (ε / (|C| + 1)) * K.indicator θ x := by
    filter_upwards [hub, ae_restrict_mem₀ hTr.nullMeasurableSet] with x hx hxM
    have hθ := hTr.pos x hxM
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs, abs_mul, abs_of_pos hθ]
      calc θ x * |ξ x ((ωs j : DifferentialForm (Eucl P) n) x)|
          ≤ θ x * ‖(ωs j : DifferentialForm (Eucl P) n) x‖ :=
            mul_le_mul_of_nonneg_left (hx _) hθ.le
        _ ≤ θ x * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left (hj x hxK).le hθ.le
        _ = ε / (|C| + 1) * θ x := mul_comm _ _
    · have hz : (ωs j : DifferentialForm (Eucl P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      rw [indicator_of_notMem hxK, hz, map_zero, mul_zero, norm_zero, mul_zero]
  have hle := norm_integral_le_of_norm_le (hgint.const_mul (ε / (|C| + 1))) hbound
  rw [integral_const_mul, hgC, Real.norm_eq_abs] at hle
  change |∫ x in M, θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)
    ∂(μHE[n] : Measure (Eucl P))| < ε
  calc _ ≤ ε / (|C| + 1) * C := hle
    _ ≤ ε / (|C| + 1) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hδ.le
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]
/-- Cylinders over `Hᵐ`-null sets are `Hᵐ⁺¹`-null: if `N ⊆ ℝ^P` has `μHE[m] N = 0`, then the
cylinder `{y ∈ ℝ^{P+1} | π y ∈ N} = ℝ × N`, `π y = (y₁, …, y_P)`, has `μHE[m + 1]`-measure zero.
For `m = 0` the set `N` is empty.  For `m ≥ 1`, each strip `{y | π y ∈ N, a ≤ y₀ ≤ a + 1}`
(`a ∈ ℤ`) is covered by the boxes `{y | π y ∈ C i, a + j dᵢ ≤ y₀ ≤ a + (j + 1) dᵢ}`,
`j ≤ ⌊1 / dᵢ⌋₊`, where the `C i` cover `N` with `∑ ediam (C i) ^ m` small and
`dᵢ ≥ ediam (C i)` is slightly inflated.  The boxes have diameter `≤ 2 dᵢ`, so the sum of
`ediam ^ (m + 1)` over them is at most `2 ^ (m + 2) ∑ dᵢ ^ m`, which is arbitrarily small. -/
theorem Submission.iwl_cr_hp_cylinder_null : ∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 := by
  intro P m N hN
  have hE : ∀ (k : ℕ) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      [MeasurableSpace X] [BorelSpace X] (S : Set X), (μHE[k] : Measure X) S =
        (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin k))) μH[k] : ℝ≥0∞) *
          μH[k] S := by
    intro k X _ _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: a `μH[0]`-null set is empty
    have hNe : N = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
      have h1 : μH[0] ({x} : Set (Eucl P)) ≤ μH[0] N := measure_mono (singleton_subset_iff.mpr hx)
      rw [Measure.hausdorffMeasure_zero_singleton] at h1
      rw [Measure.euclideanHausdorffMeasure_zero] at hN
      rw [hN] at h1
      exact absurd h1 (by simp)
    subst hNe
    simp
  · have hcm : (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin m)))
        μH[m] : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero m
    have hNm : μH[(m : ℝ)] N = 0 := by
      rw [hE m N] at hN
      exact (mul_eq_zero.mp hN).resolve_left hcm
    rw [hE (m + 1)]
    suffices h : μH[((m + 1 : ℕ) : ℝ)] {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0 by rw [h, mul_zero]
    have hsub : {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} ⊆ ⋃ a : ℤ, {y : Eucl (P + 1) |
          (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N ∧
          (a : ℝ) ≤ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∧
          EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ≤ a + 1} := by
      intro y hy
      exact mem_iUnion.2 ⟨⌊EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0⌋, hy, Int.floor_le _,
        (Int.lt_floor_add_one _).le⟩
    have hstrip : ∀ a : ℤ, μH[((m + 1 : ℕ) : ℝ)] {y : Eucl (P + 1) |
        (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N ∧
        (a : ℝ) ≤ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∧
        EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ≤ a + 1} = 0 := by
      intro a
      set π : Eucl (P + 1) → Eucl P := fun y =>
        (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
        with hπdef
      set y0 : Eucl (P + 1) → ℝ := fun y => EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 with hy0def
      have hdist : ∀ y y' : Eucl (P + 1),
          dist y y' ^ 2 = (y0 y - y0 y') ^ 2 + dist (π y) (π y') ^ 2 := by
        intro y y'
        rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity),
          Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
        simp [hπdef, hy0def, Fin.tail, Real.dist_eq, sq_abs]
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      apply le_antisymm _ zero_le
      rw [Measure.hausdorffMeasure_apply]
      refine iSup₂_le fun r hr => ?_
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      rw [zero_add]
      -- the radius
      obtain ⟨δ, hδ0, hδ1, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ENNReal.ofReal δ ≤ r := by
        rcases eq_or_ne r ⊤ with rfl | hrt
        · exact ⟨1 / 2, by norm_num, le_rfl, le_top⟩
        · have hr' : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrt
          refine ⟨min (1 / 2) (r.toReal / 2), by positivity, min_le_left _ _, ?_⟩
          calc ENNReal.ofReal (min (1 / 2) (r.toReal / 2)) ≤ ENNReal.ofReal r.toReal :=
                ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (by linarith))
            _ = r := ENNReal.ofReal_toReal hrt
      -- the smallness parameter
      have hη0 : (0 : ℝ) < η := hη
      set ε : ℝ := min ((δ / 2) ^ m / 2) (η / 2 ^ (m + 3)) with hεdef
      have hε0 : 0 < ε := by positivity
      have hεδ : ε < (δ / 2) ^ m := by
        have : 0 < (δ / 2) ^ m := by positivity
        exact (min_le_left _ _).trans_lt (by linarith)
      have hεη : 2 ^ (m + 3) * ε ≤ η := by
        have h := min_le_right ((δ / 2) ^ m / 2) (η / 2 ^ (m + 3))
        rw [← hεdef] at h
        have h2 : (0 : ℝ) < 2 ^ (m + 3) := by positivity
        calc 2 ^ (m + 3) * ε ≤ 2 ^ (m + 3) * (η / 2 ^ (m + 3)) := by gcongr
          _ = η := by field_simp
      -- a cover of `N`
      have hNa := hNm
      rw [Measure.hausdorffMeasure_apply] at hNa
      have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (by positivity)
      have hF := (iSup₂_eq_bot.mp hNa) (ENNReal.ofReal (δ / 2)) hδ2
      have hlt : (⨅ (t : ℕ → Set (Eucl P)) (_ : N ⊆ ⋃ n, t n)
          (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal (δ / 2)),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (m : ℝ)) < ENNReal.ofReal ε := by
        rw [hF]; exact ENNReal.ofReal_pos.mpr hε0
      obtain ⟨C, hC⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hCcov, hC⟩ := iInf_lt_iff.mp hC
      obtain ⟨hCdiam, hCsum⟩ := iInf_lt_iff.mp hC
      have hCsum' : ∑' i, ediam (C i) ^ m < ENNReal.ofReal ε := by
        refine lt_of_le_of_lt (le_of_eq ?_) hCsum
        refine tsum_congr fun i => ?_
        rcases (C i).eq_empty_or_nonempty with he | hne
        · have : ¬ (C i).Nonempty := by rw [he]; exact not_nonempty_empty
          rw [iSup_neg this, he, ediam_empty, zero_pow (by omega)]
          rfl
        · rw [iSup_pos hne, ENNReal.rpow_natCast]
      -- real diameters
      set D : ℕ → ℝ := fun i => (ediam (C i)).toReal with hDdef
      have hCfin : ∀ i, ediam (C i) ≠ ⊤ := fun i =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCdiam i)
      have hCeq : ∀ i, ediam (C i) = ENNReal.ofReal (D i) := fun i =>
        (ENNReal.ofReal_toReal (hCfin i)).symm
      have hD0 : ∀ i, 0 ≤ D i := fun i => ENNReal.toReal_nonneg
      have hDδ : ∀ i, D i ≤ δ / 2 := fun i =>
        ENNReal.toReal_le_of_le_ofReal (by positivity) (hCdiam i)
      have hCdist : ∀ i, ∀ x ∈ C i, ∀ x' ∈ C i, dist x x' ≤ D i := by
        intro i x hx x' hx'
        have h := edist_le_ediam_of_mem hx hx'
        rw [hCeq i, edist_dist] at h
        exact (ENNReal.ofReal_le_ofReal_iff (hD0 i)).mp h
      -- inflated diameters
      set lam : ℕ → ℝ := fun i => ε / 2 / 2 ^ i / (δ / 2) ^ m with hlamdef
      have hδm : 0 < (δ / 2) ^ m := by positivity
      have hlam0 : ∀ i, 0 < lam i := fun i => by positivity
      have hlam1 : ∀ i, lam i ≤ 1 := by
        intro i
        rw [hlamdef, div_le_one hδm]
        have h1 : ε / 2 / 2 ^ i ≤ ε := by
          rw [div_div]
          exact div_le_self hε0.le (by
            have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
            linarith)
        linarith
      set ρ : ℕ → ℝ := fun i => δ / 2 * lam i with hρdef
      have hρ0 : ∀ i, 0 < ρ i := fun i => mul_pos (by positivity) (hlam0 i)
      have hρδ : ∀ i, ρ i ≤ δ / 2 := fun i => by
        have := hlam1 i
        have h2 : 0 < δ / 2 := by positivity
        calc ρ i = δ / 2 * lam i := rfl
          _ ≤ δ / 2 * 1 := by gcongr
          _ = δ / 2 := mul_one _
      have hρm : ∀ i, ρ i ^ m ≤ ε / 2 / 2 ^ i := by
        intro i
        have hl := pow_le_of_le_one (hlam0 i).le (hlam1 i) (by omega : m ≠ 0)
        calc ρ i ^ m = (δ / 2) ^ m * lam i ^ m := by rw [hρdef, mul_pow]
          _ ≤ (δ / 2) ^ m * lam i := by gcongr
          _ = ε / 2 / 2 ^ i := by rw [hlamdef]; field_simp
      set d : ℕ → ℝ := fun i => max (D i) (ρ i) with hddef
      have hd0 : ∀ i, 0 < d i := fun i => lt_max_of_lt_right (hρ0 i)
      have hdδ : ∀ i, d i ≤ δ / 2 := fun i => max_le (hDδ i) (hρδ i)
      have hd1 : ∀ i, d i ≤ 1 := fun i => (hdδ i).trans (by linarith)
      have hDd : ∀ i, D i ≤ d i := fun i => le_max_left _ _
      have hdm : ∀ i, d i ^ m ≤ D i ^ m + ε / 2 / 2 ^ i := by
        intro i
        rcases le_total (D i) (ρ i) with h | h
        · rw [hddef]; simp only [max_eq_right h]
          have := hρm i
          have : 0 ≤ D i ^ m := pow_nonneg (hD0 i) m
          linarith
        · rw [hddef]; simp only [max_eq_left h]
          have : 0 ≤ ε / 2 / 2 ^ i := by positivity
          linarith
      -- number of intervals
      set k : ℕ → ℕ := fun i => ⌊1 / d i⌋₊ + 1 with hkdef
      have hk : ∀ i, (k i : ℝ) ≤ 2 / d i := by
        intro i
        have h1 : (⌊1 / d i⌋₊ : ℝ) ≤ 1 / d i := Nat.floor_le (by have := hd0 i; positivity)
        have h2 : (1 : ℝ) ≤ 1 / d i := by rw [le_div_iff₀ (hd0 i)]; linarith [hd1 i]
        simp only [hkdef, Nat.cast_add, Nat.cast_one]
        calc (⌊1 / d i⌋₊ : ℝ) + 1 ≤ 1 / d i + 1 / d i := by linarith
          _ = 2 / d i := by ring
      -- the boxes
      set Q : ℕ → ℕ → Set (Eucl (P + 1)) := fun i j =>
        {y | π y ∈ C i ∧ (a : ℝ) + j * d i ≤ y0 y ∧ y0 y ≤ a + (j + 1) * d i} with hQdef
      have hQdiam : ∀ i j, ediam (Q i j) ≤ ENNReal.ofReal (2 * d i) := by
        intro i j
        refine ediam_le_of_forall_dist_le fun y hy y' hy' => ?_
        have h1 : |y0 y - y0 y'| ≤ d i := by
          rw [abs_le]; constructor <;> nlinarith [hy.2.1, hy.2.2, hy'.2.1, hy'.2.2]
        have h2 : dist (π y) (π y') ≤ d i := (hCdist i _ hy.1 _ hy'.1).trans (hDd i)
        have h3 : dist y y' ^ 2 ≤ (2 * d i) ^ 2 := by
          rw [hdist]
          have : (y0 y - y0 y') ^ 2 ≤ d i ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          have : dist (π y) (π y') ^ 2 ≤ d i ^ 2 := pow_le_pow_left₀ dist_nonneg h2 2
          nlinarith
        have h4 : 0 ≤ 2 * d i := by have := hd0 i; positivity
        exact (pow_le_pow_iff_left₀ dist_nonneg h4 two_ne_zero).mp h3
      -- the indexed cover
      set t : ℕ → Set (Eucl (P + 1)) := fun n =>
        if n.unpair.2 < k n.unpair.1 then Q n.unpair.1 n.unpair.2 else ∅ with htdef
      have htpair : ∀ i j, t (Nat.pair i j) = if j < k i then Q i j else ∅ := by
        intro i j; simp only [htdef, Nat.unpair_pair]
      have htcov : {y : Eucl (P + 1) | π y ∈ N ∧ (a : ℝ) ≤ y0 y ∧ y0 y ≤ a + 1} ⊆ ⋃ n, t n := by
        intro y hy
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hCcov hy.1)
        set u : ℝ := (y0 y - a) / d i with hudef
        have hu0 : 0 ≤ u := div_nonneg (by linarith [hy.2.1]) (hd0 i).le
        have hu1 : u ≤ 1 / d i := div_le_div_of_nonneg_right (by linarith [hy.2.2]) (hd0 i).le
        set j := ⌊u⌋₊ with hjdef
        have hjk : j < k i := by
          have : ⌊u⌋₊ ≤ ⌊1 / d i⌋₊ := Nat.floor_le_floor hu1
          simp only [hkdef]; omega
        refine mem_iUnion.mpr ⟨Nat.pair i j, ?_⟩
        rw [htpair, ite_eq_left hjk]
        refine ⟨hi, ?_, ?_⟩
        · have h1 : (j : ℝ) ≤ u := Nat.floor_le hu0
          have h2 : (j : ℝ) * d i ≤ y0 y - a := by
            rw [hudef, le_div_iff₀ (hd0 i)] at h1; exact h1
          linarith
        · have h1 : u < j + 1 := Nat.lt_floor_add_one u
          have h2 : y0 y - a < (j + 1) * d i := by
            rw [hudef, div_lt_iff₀ (hd0 i)] at h1; exact h1
          linarith
      have htdiam : ∀ n, ediam (t n) ≤ r := by
        intro n
        simp only [htdef]
        split_ifs
        · exact (hQdiam _ _).trans
            ((ENNReal.ofReal_le_ofReal (by linarith [hdδ n.unpair.1])).trans hδr)
        · rw [ediam_empty]; exact zero_le
      refine iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htdiam ?_))
      -- the sum estimate
      have hterm : ∀ n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ((m + 1 : ℕ) : ℝ)) ≤
          ediam (t n) ^ (m + 1) := fun n => by
        rw [ENNReal.rpow_natCast]; exact iSup_le fun _ => le_rfl
      have hinner : ∀ i, ∑' j, ediam (t (Nat.pair i j)) ^ (m + 1) ≤
          ENNReal.ofReal (2 ^ (m + 2)) * (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
        intro i
        have hsupp : ∀ j ∉ Finset.range (k i), ediam (t (Nat.pair i j)) ^ (m + 1) = 0 := by
          intro j hj
          rw [Finset.mem_range, not_lt] at hj
          rw [htpair, ite_eq_right (by omega), ediam_empty, zero_pow (by omega)]
        rw [tsum_eq_sum hsupp]
        calc ∑ j ∈ Finset.range (k i), ediam (t (Nat.pair i j)) ^ (m + 1)
            ≤ ∑ j ∈ Finset.range (k i), ENNReal.ofReal (2 * d i) ^ (m + 1) := by
              refine Finset.sum_le_sum fun j hj => ?_
              rw [Finset.mem_range] at hj
              rw [htpair, ite_eq_left hj]
              exact pow_le_pow_left₀ zero_le (hQdiam i j) _
          _ = ENNReal.ofReal ((k i : ℝ) * (2 * d i) ^ (m + 1)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
                ENNReal.ofReal_pow (by have := hd0 i; positivity)]
          _ ≤ ENNReal.ofReal (2 ^ (m + 2) * (D i ^ m + ε / 2 / 2 ^ i)) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hdi := hd0 i
              calc (k i : ℝ) * (2 * d i) ^ (m + 1) ≤ 2 / d i * (2 * d i) ^ (m + 1) := by
                    gcongr; exact hk i
                _ = 2 ^ (m + 2) * d i ^ m := by
                    field_simp; ring
                _ ≤ 2 ^ (m + 2) * (D i ^ m + ε / 2 / 2 ^ i) := by gcongr; exact hdm i
          _ = ENNReal.ofReal (2 ^ (m + 2)) *
                (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
              rw [ENNReal.ofReal_mul (by positivity), hCeq i,
                ← ENNReal.ofReal_pow (hD0 i), ← ENNReal.ofReal_add (pow_nonneg (hD0 i) _)
                  (by positivity)]
      have hgeom : ∑' i : ℕ, ENNReal.ofReal (ε / 2 / 2 ^ i) = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) (summable_geometric_two' ε),
          tsum_geometric_two']
      calc ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ((m + 1 : ℕ) : ℝ))
          ≤ ∑' n, ediam (t n) ^ (m + 1) := ENNReal.tsum_le_tsum hterm
        _ = ∑' p : ℕ × ℕ, ediam (t (Nat.pair p.1 p.2)) ^ (m + 1) :=
            (Nat.pairEquiv.tsum_eq (fun n => ediam (t n) ^ (m + 1))).symm
        _ = ∑' i, ∑' j, ediam (t (Nat.pair i j)) ^ (m + 1) :=
            ENNReal.tsum_prod (f := fun i j => ediam (t (Nat.pair i j)) ^ (m + 1))
        _ ≤ ∑' i, ENNReal.ofReal (2 ^ (m + 2)) *
              (ediam (C i) ^ m + ENNReal.ofReal (ε / 2 / 2 ^ i)) :=
            ENNReal.tsum_le_tsum hinner
        _ = ENNReal.ofReal (2 ^ (m + 2)) * (∑' i, ediam (C i) ^ m +
              ∑' i : ℕ, ENNReal.ofReal (ε / 2 / 2 ^ i)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ ≤ ENNReal.ofReal (2 ^ (m + 2)) * (ENNReal.ofReal ε + ENNReal.ofReal ε) := by
            rw [hgeom]; gcongr
        _ = ENNReal.ofReal (2 ^ (m + 3) * ε) := by
            rw [← ENNReal.ofReal_add hε0.le hε0.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεη
        _ = (η : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    exact measure_mono_null hsub (measure_iUnion_null hstrip)
theorem Submission.iwl_cr_hp_injective_pieces : ∀ (P m : ℕ) (A : Set (Eucl P)), MeasurableSet A → CountablyRectifiable m A → ∃ (G : ℕ → Eucl m → Eucl P) (B : ℕ → Set (Eucl m)), (∀ p, ∃ K : ℝ≥0, LipschitzWith K (G p)) ∧ (∀ p, MeasurableSet (B p)) ∧ (∀ p, InjOn (G p) (B p)) ∧ (∀ p, ∀ b ∈ B p, DifferentiableAt ℝ (G p) b) ∧ (∀ p, G p '' B p ⊆ A) ∧ (∀ p, MeasurableSet (G p '' B p)) ∧ Pairwise (Function.onFun Disjoint fun p => G p '' B p) ∧ (μHE[m] : Measure (Eucl P)) (A \ ⋃ p, G p '' B p) = 0 := by
  intro P m A hA hM
  -- Step 1: `A ⊆ M₀ ∪ ⋃_j F_j(ℝᵐ)` with `Hᵐ(M₀) = 0` and every `F_j` Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 2: lower-bound constants for injective linear maps.
  have hchoice : ∀ L : Eucl m →L[ℝ] Eucl P, ∃ δ : ℝ≥0, 0 < δ ∧ ∃ k : ℝ, 0 < k ∧
      (Function.Injective L → ∀ (t : Set (Eucl m)) (g : Eucl m → Eucl P),
        ApproximatesLinearOn g L t δ → ∀ b ∈ t, ∀ b' ∈ t, k * ‖b - b'‖ ≤ ‖g b - g b'‖) := by
    intro L
    by_cases hL : Function.Injective L
    · obtain ⟨K, hKpos, hK⟩ := (L : Eucl m →ₗ[ℝ] Eucl P).exists_antilipschitzWith
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
  -- Step 3: the regular set `R_j` of `F_j` (differentiability points with injective derivative)
  -- is Borel, as injective linear maps form an open set; partition it into injective pieces.
  set R : ℕ → Set (Eucl m) :=
    fun j => {b | DifferentiableAt ℝ (F j) b ∧ Function.Injective (fderiv ℝ (F j) b)} with hRdef
  have hRmeas : ∀ j, MeasurableSet (R j) := fun j =>
    (measurableSet_of_differentiableAt ℝ (F j)).inter
      (ContinuousLinearMap.isOpen_injective.measurableSet.preimage (measurable_fderiv ℝ (F j)))
  have hpart : ∀ j, ∃ (t : ℕ → Set (Eucl m)),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ R j) ∧ R j ⊆ ⋃ i, t i ∧
      ∀ i, InjOn (F j) (t i) := by
    intro j
    rcases eq_empty_or_nonempty (R j) with hR | hR
    · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun _ => empty_subset _,
        by rw [hR]; exact empty_subset _, fun i => injOn_empty _⟩
    obtain ⟨t, Al, -, ht, hcov, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) (R j) (fderiv ℝ (F j))
        (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) δ (fun L => (hδpos L).ne')
    refine ⟨fun i => R j ∩ t i, fun i => (hRmeas j).inter (ht i), fun i => inter_subset_left,
      ?_, ?_⟩
    · intro b hb
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hb)
      exact mem_iUnion.2 ⟨i, hb, hi⟩
    · intro i b hb b' hb' hbb
      obtain ⟨y, hy, hAy⟩ := hactual hR i
      have hlow := hk (Al i) (hAy ▸ hy.2) (R j ∩ t i) (F j) (happrox i) b hb b' hb'
      rw [hbb, sub_self, norm_zero] at hlow
      have h0 : ‖b - b'‖ ≤ 0 := by
        have := hkpos (Al i)
        nlinarith [norm_nonneg (b - b')]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  choose t ht_meas ht_sub ht_cov ht_inj using hpart
  -- Step 4: enumeration of the pieces by `Nat.unpair`.
  set Gp : ℕ → Eucl m → Eucl P := fun p => F p.unpair.1 with hGpdef
  set Sp : ℕ → Set (Eucl m) := fun p => t p.unpair.1 p.unpair.2 with hSpdef
  have hGpL : ∀ p, ∃ K : ℝ≥0, LipschitzWith K (Gp p) := fun p => hF _
  have hSpm : ∀ p, MeasurableSet (Sp p) := fun p => ht_meas _ _
  have hSpinj : ∀ p, InjOn (Gp p) (Sp p) := fun p => ht_inj _ _
  have hSpdiff : ∀ p, ∀ b ∈ Sp p, DifferentiableAt ℝ (Gp p) b := fun p b hb =>
    (ht_sub _ _ hb).1
  have hGpc : ∀ p, Continuous (Gp p) := fun p => by
    obtain ⟨K, hK⟩ := hGpL p; exact hK.continuous
  have himgm : ∀ p, MeasurableSet (Gp p '' Sp p) := fun p =>
    (hSpm p).image_of_continuousOn_injOn (hGpc p).continuousOn (hSpinj p)
  -- Step 5: the exceptional set `N = M₀ ∪ ⋃_j F_j(ℝᵐ ∖ R_j)` is `Hᵐ`-null.
  -- Local estimate: if `f` is `s²`-close on `S` to a linear `Λ` with `Λ e = 0`, `|e| = 1`, then
  -- compressing `ℝᵐ` by the factor `s` in the direction `e` (`T`, with `Lᵐ(T S) = s Lᵐ(S)`)
  -- makes `f ∘ T⁻¹` `(‖Λ‖ + s)`-Lipschitz on `T S`, so `Hᵐ(f S) ≤ (‖Λ‖ + s)ᵐ s Lᵐ(S)`.
  have hpiece : ∀ (f : Eucl m → Eucl P) (Λ : Eucl m →L[ℝ] Eucl P) (S : Set (Eucl m)) (s : ℝ≥0),
      0 < s → s ≤ 1 → ¬ Function.Injective Λ → ApproximatesLinearOn f Λ S (s ^ 2) →
      (μHE[m] : Measure (Eucl P)) (f '' S) ≤
        ((‖Λ‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m * ((s : ℝ≥0∞) * volume S) := by
    intro f Λ S s hs0 hs1 hΛ happ
    obtain ⟨v, hv0, hΛv⟩ : ∃ v, v ≠ 0 ∧ Λ v = 0 := by
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, Λ x = Λ y ∧ x ≠ y := by
        simpa [Function.Injective] using hΛ
      exact ⟨x - y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩
    set e : Eucl m := ‖v‖⁻¹ • v with he_def
    have he : ‖e‖ = 1 := norm_smul_inv_norm hv0
    have hΛe : Λ e = 0 := by rw [he_def, map_smul, hΛv, smul_zero]
    have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
    have hs0' : (0 : ℝ) < s := hs0
    have hs1' : (s : ℝ) ≤ 1 := hs1
    set T : Eucl m →L[ℝ] Eucl m :=
      ContinuousLinearMap.id ℝ (Eucl m) + ((s : ℝ) - 1) • (innerSL ℝ e).smulRight e with hT_def
    set T' : Eucl m →L[ℝ] Eucl m :=
      ContinuousLinearMap.id ℝ (Eucl m) + ((s : ℝ)⁻¹ - 1) • (innerSL ℝ e).smulRight e
      with hT'_def
    have hTx : ∀ x, T x = x + (((s : ℝ) - 1) * inner ℝ e x) • e := by
      intro x
      simp [T, smul_smul]
    have hT'x : ∀ x, T' x = x + (((s : ℝ)⁻¹ - 1) * inner ℝ e x) • e := by
      intro x
      simp [T', smul_smul]
    have hT'T : ∀ x, T' (T x) = x := by
      intro x
      rw [hT'x, hTx, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul]
      have h0 : ((s : ℝ) - 1) * inner ℝ e x +
          ((s : ℝ)⁻¹ - 1) * (inner ℝ e x + ((s : ℝ) - 1) * inner ℝ e x * 1) = 0 := by
        field_simp
        ring
      rw [h0, zero_smul, add_zero]
    -- `det T = 1 + (s - 1) |e|² = s` (matrix determinant lemma in the standard basis).
    have hdet : LinearMap.det (T : Eucl m →ₗ[ℝ] Eucl m) = s := by
      set b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      rw [← LinearMap.det_toMatrix b]
      have hmat : LinearMap.toMatrix b b (T : Eucl m →ₗ[ℝ] Eucl m) =
          1 + Matrix.replicateCol Unit (fun i => ((s : ℝ) - 1) * e i) *
            Matrix.replicateRow Unit (fun i => e i) := by
        ext i j
        simp [T, LinearMap.toMatrix_apply, b, Matrix.one_apply, Matrix.mul_apply,
          EuclideanSpace.inner_single_right]
        ring
      rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
      have h2 := EuclideanSpace.real_norm_sq_eq e
      rw [he] at h2
      simp only [dotProduct]
      rw [show (∑ i, e i * (((s : ℝ) - 1) * e i)) = ((s : ℝ) - 1) * ∑ i, e i ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, ← h2]
      ring
    have hvol : (volume : Measure (Eucl m)) (T '' S) = (s : ℝ≥0∞) * volume S := by
      rw [Measure.addHaar_image_continuousLinearMap, hdet, abs_of_pos hs0',
        ENNReal.ofReal_coe_nnreal]
    -- For `x, x' ∈ S`: `Λ (x - x') = Λ (T x - T x')` as `Λ e = 0`, and
    -- `|x - x'| ≤ s⁻¹ |T x - T x'|`.
    have hlip : LipschitzOnWith (‖Λ‖₊ + s) (f ∘ T') (T '' S) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      simp only [Function.comp_apply, hT'T, dist_eq_norm, NNReal.coe_add, coe_nnnorm]
      have h1 : ‖f x - f x' - Λ (x - x')‖ ≤ (s : ℝ) ^ 2 * ‖x - x'‖ := by
        simpa using happ x hx x' hx'
      have hxx : x - x' = T' (T x - T x') := by rw [map_sub, hT'T, hT'T]
      have h2 : Λ (x - x') = Λ (T x - T x') := by
        rw [hxx, hT'x, map_add, map_smul, hΛe, smul_zero, add_zero]
      have h3 : ‖x - x'‖ ≤ (s : ℝ)⁻¹ * ‖T x - T x'‖ := by
        rw [hxx, hT'x]
        have hsi : 0 ≤ (s : ℝ)⁻¹ - 1 := sub_nonneg.mpr (one_le_inv₀ hs0' |>.mpr hs1')
        calc ‖(T x - T x') + (((s : ℝ)⁻¹ - 1) * inner ℝ e (T x - T x')) • e‖
            ≤ ‖T x - T x'‖ + ‖(((s : ℝ)⁻¹ - 1) * inner ℝ e (T x - T x')) • e‖ :=
              norm_add_le _ _
          _ = ‖T x - T x'‖ + ((s : ℝ)⁻¹ - 1) * |inner ℝ e (T x - T x')| := by
              rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hsi]
          _ ≤ ‖T x - T x'‖ + ((s : ℝ)⁻¹ - 1) * ‖T x - T x'‖ := by
              gcongr
              exact (abs_real_inner_le_norm e _).trans (by rw [he, one_mul])
          _ = (s : ℝ)⁻¹ * ‖T x - T x'‖ := by ring
      have h4 : ‖Λ (T x - T x')‖ ≤ ‖Λ‖ * ‖T x - T x'‖ := Λ.le_opNorm _
      calc ‖f x - f x'‖ ≤ ‖Λ (x - x')‖ + ‖f x - f x' - Λ (x - x')‖ := norm_le_insert' _ _
        _ ≤ ‖Λ‖ * ‖T x - T x'‖ + (s : ℝ) ^ 2 * ((s : ℝ)⁻¹ * ‖T x - T x'‖) :=
            add_le_add (by rw [h2]; exact h4) (h1.trans (by gcongr))
        _ = (‖Λ‖ + s) * ‖T x - T x'‖ := by field_simp
    have himg : f '' S = (f ∘ T') '' (T '' S) := by
      rw [image_image]
      exact image_congr fun x _ => by simp only [Function.comp_apply, hT'T]
    calc (μHE[m] : Measure (Eucl P)) (f '' S)
        = (μHE[m] : Measure (Eucl P)) ((f ∘ T') '' (T '' S)) := by rw [himg]
      _ ≤ ((‖Λ‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m * (μHE[m] : Measure (Eucl m)) (T '' S) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hlip
      _ = ((‖Λ‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m * ((s : ℝ≥0∞) * volume S) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hvol]
  -- The image of the critical set of a Lipschitz map is `Hᵐ`-null: split the critical points
  -- in `B_r(0)` into countably many disjoint Borel pieces on which `f` is `s²`-close to its
  -- (non-injective) derivative at some point of the piece; then
  -- `Hᵐ(f(C ∩ B_r)) ≤ (L + 1)ᵐ s Lᵐ(B_r)` for every `s ∈ (0, 1]`.
  have hcrit : ∀ (f : Eucl m → Eucl P) (L : ℝ≥0), LipschitzWith L f →
      (μHE[m] : Measure (Eucl P))
        (f '' {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}) = 0 := by
    intro f L hf
    set C := {w | DifferentiableAt ℝ f w ∧ ¬ Function.Injective (fderiv ℝ f w)}
    have hCr : ∀ r : ℕ, (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r)) = 0 := by
      intro r
      set V := (volume : Measure (Eucl m)) (ball 0 r)
      have hV : V ≠ ∞ := measure_ball_lt_top.ne
      have hbound : ∀ s : ℝ≥0, 0 < s → s ≤ 1 →
          (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r)) ≤
            ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V * s := by
        intro s hs0 hs1
        rcases (C ∩ ball (0 : Eucl m) r).eq_empty_or_nonempty with hC | hC
        · rw [hC, image_empty, measure_empty]
          exact bot_le
        obtain ⟨T, Λ, hTdisj, hTmeas, hCT, hTapprox, hTΛ⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (C ∩ ball 0 r)
            (fderiv ℝ f) (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => s ^ 2)
            (fun _ => pow_ne_zero 2 hs0.ne')
        have hpi : ∀ i, (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r ∩ T i)) ≤
            ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (ball (0 : Eucl m) r ∩ T i) := by
          intro i
          -- `Λ i = Df(y)` for a critical point `y`, so `Λ i` is not injective and `‖Λ i‖ ≤ L`.
          obtain ⟨y, hy, hΛy⟩ := hTΛ hC i
          have hΛinj : ¬ Function.Injective (Λ i) := by
            rw [hΛy]
            exact hy.1.2
          have hΛn : ‖Λ i‖₊ ≤ L := by
            rw [hΛy, ← NNReal.coe_le_coe, coe_nnnorm]
            exact norm_fderiv_le_of_lipschitz ℝ hf
          calc (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r ∩ T i))
              ≤ ((‖Λ i‖₊ + s : ℝ≥0) : ℝ≥0∞) ^ m *
                  ((s : ℝ≥0∞) * volume (C ∩ ball 0 r ∩ T i)) :=
                hpiece f (Λ i) _ s hs0 hs1 hΛinj (hTapprox i)
            _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m *
                  ((s : ℝ≥0∞) * volume (ball (0 : Eucl m) r ∩ T i)) := by
                gcongr
                exact inter_subset_right
            _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (ball (0 : Eucl m) r ∩ T i) := by
                ring
        calc (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r))
            ≤ (μHE[m] : Measure (Eucl P)) (⋃ i, f '' (C ∩ ball 0 r ∩ T i)) := by
              refine measure_mono ?_
              rintro _ ⟨x, hx, rfl⟩
              obtain ⟨i, hi⟩ := mem_iUnion.mp (hCT hx)
              exact mem_iUnion.mpr ⟨i, x, ⟨hx, hi⟩, rfl⟩
          _ ≤ ∑' i, (μHE[m] : Measure (Eucl P)) (f '' (C ∩ ball 0 r ∩ T i)) :=
              measure_iUnion_le _
          _ ≤ ∑' i, ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (ball (0 : Eucl m) r ∩ T i) :=
              ENNReal.tsum_le_tsum hpi
          _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * volume (⋃ i, ball (0 : Eucl m) r ∩ T i) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (hTdisj hij).mono inter_subset_right inter_subset_right
              · exact fun i => measurableSet_ball.inter (hTmeas i)
          _ ≤ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * s * V := by
              gcongr
              exact measure_mono (iUnion_subset fun i => inter_subset_left)
          _ = ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V * s := by ring
      -- Let `s = 1 / (l + 1) → 0`.
      have hlim : Tendsto (fun l : ℕ => ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V * ((l + 1 : ℕ) : ℝ≥0∞)⁻¹)
          atTop (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
          (Or.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hV) :
            (0 : ℝ≥0∞) ≠ 0 ∨ ((L + 1 : ℝ≥0) : ℝ≥0∞) ^ m * V ≠ ∞)
        rw [mul_zero] at h
        exact h
      refine le_antisymm (ge_of_tendsto' hlim fun l => ?_) bot_le
      have hl : ((l + 1 : ℕ) : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr l.succ_ne_zero
      have h := hbound ((l + 1 : ℕ) : ℝ≥0)⁻¹ (inv_pos.mpr (pos_iff_ne_zero.mpr hl))
        (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr l.succ_pos))
      rwa [ENNReal.coe_inv hl, ENNReal.coe_natCast] at h
    refine measure_mono_null ?_ (measure_iUnion_null hCr)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨r, x, ⟨hx, mem_ball_zero_iff.mpr hr⟩, rfl⟩
  set N := M₀ ∪ ⋃ j, F j '' (univ \ R j) with hNdef
  have hN : (μHE[m] : Measure (Eucl P)) N = 0 := by
    refine measure_union_null hM₀ (measure_iUnion_null fun j => ?_)
    obtain ⟨K, hK⟩ := hF j
    -- By Rademacher's theorem the non-differentiability set is `Lᵐ`-null, and `Hᵐ = Lᵐ` on
    -- `ℝᵐ`, so its image under the Lipschitz map `F_j` is `Hᵐ`-null.
    have hND : (volume : Measure (Eucl m)) {w | ¬ DifferentiableAt ℝ (F j) w} = 0 :=
      ae_iff.mp (hK.ae_differentiableAt (μ := volume))
    have hNDimg : (μHE[m] : Measure (Eucl P)) (F j '' {w | ¬ DifferentiableAt ℝ (F j) w}) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
        (hK.lipschitzOnWith (s := {w | ¬ DifferentiableAt ℝ (F j) w}))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m, hND, mul_zero] at h
      exact le_antisymm h bot_le
    refine measure_mono_null ?_ (measure_union_null (hcrit (F j) K hK) hNDimg)
    rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F j) w
    · exact Or.inl ⟨w, ⟨hd, fun hinj => hw ⟨hd, hinj⟩⟩, rfl⟩
    · exact Or.inr ⟨w, hd, rfl⟩
  -- Step 6: covering, `A ⊆ N ∪ ⋃_p G_p(S_p)`.
  have hcov2 : A ⊆ N ∪ ⋃ p, Gp p '' Sp p := by
    intro x hx
    rcases hcover hx with h0 | h1
    · exact Or.inl (Or.inl h0)
    · obtain ⟨j, b, rfl⟩ := mem_iUnion.1 h1
      by_cases hb : b ∈ R j
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (ht_cov j hb)
        refine Or.inr (mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
        simp only [hGpdef, hSpdef, Nat.unpair_pair]
        exact ⟨b, hi, rfl⟩
      · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, hb⟩, rfl⟩))
  -- Steps 7–8: disjointification and null remainder.
  set Ap : ℕ → Set (Eucl P) := disjointed fun p => A ∩ Gp p '' Sp p with hApdef
  set Bp : ℕ → Set (Eucl m) := fun p => Sp p ∩ Gp p ⁻¹' Ap p with hBpdef
  have hApm : ∀ p, MeasurableSet (Ap p) :=
    MeasurableSet.disjointed fun p => hA.inter (himgm p)
  have hApsub : ∀ p, Ap p ⊆ A ∩ Gp p '' Sp p := fun p => disjointed_subset _ p
  have himgB : ∀ p, Gp p '' Bp p = Ap p := by
    intro p
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb.2
    · intro hx
      obtain ⟨b, hb, rfl⟩ := ((hApsub p) hx).2
      exact ⟨b, ⟨hb, hx⟩, rfl⟩
  refine ⟨Gp, Bp, hGpL, fun p => (hSpm p).inter ((hApm p).preimage (hGpc p).measurable),
    fun p => (hSpinj p).mono inter_subset_left,
    fun p b hb => hSpdiff p b hb.1, fun p => by rw [himgB p]; exact fun x hx => ((hApsub p) hx).1,
    fun p => by rw [himgB p]; exact hApm p, ?_, ?_⟩
  · intro p q hpq
    simp only [Function.onFun, himgB]
    exact disjoint_disjointed _ hpq
  · simp only [himgB]
    rw [hApdef, iUnion_disjointed]
    refine measure_mono_null ?_ hN
    intro x ⟨hxA, hxU⟩
    rcases hcov2 hxA with hxN | hxG
    · exact hxN
    · exfalso
      obtain ⟨p, hp⟩ := mem_iUnion.1 hxG
      exact hxU (mem_iUnion.2 ⟨p, hxA, hp⟩)
/-- Gram determinant of the cylinder lift `G̃(v) = (v₀, G(v₁, …, v_m))` (the Jacobian step of the
Hausdorff product formula).  With `Λ(s, x) = (s, x)`, `pr₀ v = v₀` and `tl v = (v₁, …, v_m)`,
the chain rule gives `DG̃(w) = Λ ∘ (pr₀, DG(b) ∘ tl)`; as `⟨Λ(s, x), Λ(s', x')⟩ = s s' + ⟨x, x'⟩`,
the Gram matrix of `DG̃(w)` on the standard basis is `diag(1, Gram(DG(b)))`, and Laplace
expansion along row `0` gives `det Gram(DG̃(w)) = det Gram(DG(b))`. -/
theorem Submission.iwl_cr_hp_lift_gram_det : ∀ (P m : ℕ) (G : Eucl m → Eucl P) (Gt : Eucl (m + 1) → Eucl (P + 1)) (w : Eucl (m + 1)) (b : Eucl m), (∀ v : Eucl (m + 1), Gt v = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons (EuclideanSpace.equiv (Fin (m + 1)) ℝ v 0) (EuclideanSpace.equiv (Fin P) ℝ (G ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))))))) → b = (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ w)) → DifferentiableAt ℝ G b → (Matrix.of fun i j : Fin (m + 1) => inner ℝ (fderiv ℝ Gt w (EuclideanSpace.single i 1)) (fderiv ℝ Gt w (EuclideanSpace.single j 1))).det = (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G b (EuclideanSpace.single i 1)) (fderiv ℝ G b (EuclideanSpace.single j 1))).det := by
  intro P m G Gt w b hGt hb hd
  -- the linear lift `Λ(s, x) = (s, x₁, …, x_P)` and the tail map, as continuous linear maps
  let Λ : (ℝ × Eucl P) →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun q => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2))
      map_add' := by
        intro q q'
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp
      map_smul' := by
        intro c q
        ext k
        refine Fin.cases ?_ (fun j => ?_) k <;> simp }
  have hΛ : ∀ (s : ℝ) (x : Eucl P), Λ (s, x) = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) := fun s x => rfl
  have hinnerΛ : ∀ (s s' : ℝ) (x x' : Eucl P),
      inner ℝ (Λ (s, x)) (Λ (s', x')) = s * s' + inner ℝ x x' := by
    intro s s' x x'
    rw [hΛ, hΛ]
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fin.sum_univ_succ, mul_comm]
  let tl : Eucl (m + 1) →L[ℝ] Eucl m := LinearMap.toContinuousLinearMap
    { toFun := fun v => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))
      map_add' := by intro v v'; ext k; simp [Fin.tail]
      map_smul' := by intro c v; ext k; simp [Fin.tail] }
  have htl : ∀ v : Eucl (m + 1), tl v = (EuclideanSpace.equiv (Fin m) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v)) := fun v => rfl
  set L := fderiv ℝ G b with hLdef
  set pr0 : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (m + 1)) with hpr0
  have hGt' : Gt = fun v => Λ (pr0 v, G (tl v)) := by
    funext v; rw [hGt]; rfl
  have hb' : tl w = b := by rw [hb]; rfl
  -- the derivative of the lift
  have hinner : HasFDerivAt (fun v => (pr0 v, G (tl v))) (pr0.prod (L.comp tl)) w := by
    refine pr0.hasFDerivAt.prodMk ?_
    have hG : HasFDerivAt G L (tl w) := by rw [hb']; exact hd.hasFDerivAt
    exact hG.comp w tl.hasFDerivAt
  have hD : fderiv ℝ Gt w = Λ.comp (pr0.prod (L.comp tl)) := by
    rw [hGt']
    exact (Λ.hasFDerivAt.comp w hinner).fderiv
  rw [hD]
  -- values on the standard basis
  have hpr0_zero : pr0 (EuclideanSpace.single 0 1) = 1 := by simp [hpr0]
  have hpr0_succ : ∀ j : Fin m, pr0 (EuclideanSpace.single j.succ 1) = 0 := by
    intro j; simp [hpr0, Fin.succ_ne_zero]
  have htl_zero : tl (EuclideanSpace.single 0 1) = 0 := by
    ext k; simp [htl, Fin.tail, Fin.succ_ne_zero]
  have htl_succ : ∀ j : Fin m, tl (EuclideanSpace.single j.succ 1) = EuclideanSpace.single j 1 := by
    intro j; ext k
    rw [htl]
    by_cases hk : k = j
    · subst hk; simp [Fin.tail]
    · simp [Fin.tail, hk]
  have hentry : ∀ i j : Fin (m + 1),
      inner ℝ ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single i 1))
        ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)) =
      pr0 (EuclideanSpace.single i 1) * pr0 (EuclideanSpace.single j 1) +
        inner ℝ (L (tl (EuclideanSpace.single i 1))) (L (tl (EuclideanSpace.single j 1))) := by
    intro i j
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply]
    exact hinnerΛ _ _ _ _
  -- Laplace expansion along the first row of the block-diagonal Gram matrix
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hrest : ∀ k : Fin m, (-1 : ℝ) ^ (k.succ : ℕ) *
      (Matrix.of fun i j : Fin (m + 1) => inner ℝ ((Λ.comp (pr0.prod (L.comp tl)))
        (EuclideanSpace.single i 1)) ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)))
        0 k.succ *
      ((Matrix.of fun i j : Fin (m + 1) => inner ℝ ((Λ.comp (pr0.prod (L.comp tl)))
        (EuclideanSpace.single i 1)) ((Λ.comp (pr0.prod (L.comp tl))) (EuclideanSpace.single j 1)))
        |>.submatrix Fin.succ k.succ.succAbove).det = 0 := by
    intro k
    rw [Matrix.of_apply, hentry, hpr0_zero, hpr0_succ, htl_zero, map_zero, inner_zero_left]
    ring
  rw [Finset.sum_eq_zero (fun k _ => hrest k), add_zero]
  rw [Matrix.of_apply, hentry, hpr0_zero, htl_zero, map_zero, inner_zero_left, Fin.succAbove_zero]
  simp only [pow_zero, Fin.val_zero, mul_one, add_zero, one_mul]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hentry, hpr0_succ, hpr0_succ, htl_succ, htl_succ]
  ring

/-- Product formula `Hᵐ⁺¹ ⌞ (ℝ × G(B)) = L¹ ⊗ Hᵐ ⌞ G(B)` for one injective Lipschitz piece
`G : ℝᵐ → ℝ^P` on a Borel set `B`, with `Φ(s, x) = (s, x)` and `π(s, x) = x`: for Borel `g ≥ 0`,
`φ(s) = ∫_{G(B)} g(Φ(s, x)) dHᵐ(x)` is measurable and `∫_{π⁻¹(G(B))} g dHᵐ⁺¹ = ∫_ℝ φ(s) ds`.
Both sides come from the injective area formula `∫_{f(S)} u dHᵏ = ∫_S J(Df) · u ∘ f` (proved
inline: partition `S` into pieces where `f` is almost linear, compare with the linear area
formula `Hᵏ(L E) = J(L) |E|`, `J(L) = √det ⟨L eᵢ, L eⱼ⟩`, and let the error go to `0`): in
dimension `m` for `G` on `B`, and in dimension `m + 1` for the lift `G̃(v) = Φ(v₀, G(v₁, …, v_m))`
on `ℝ × B`, whose Jacobian equals that of `G` (`iwl_cr_hp_lift_gram_det`); Tonelli in
`v = (v₀, (v₁, …, v_m))` finishes. -/
theorem Submission.iwl_cr_hp_piece_product :
    ∀ (P m : ℕ) (G : Eucl m → Eucl P) (K : ℝ≥0) (B : Set (Eucl m)), LipschitzWith K G →
      MeasurableSet B → InjOn G B → (∀ b ∈ B, DifferentiableAt ℝ G b) →
      ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g →
        Measurable (fun s : ℝ => ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) ∧
        ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B},
            g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) =
          ∫⁻ s : ℝ, ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) := by
  -- the area Jacobian `J L = √(det Gram(L))` of a linear map `L : ℝᵏ → ℝ^Q`
  obtain ⟨J, hJ⟩ : ∃ J : ∀ k Q : ℕ, (Eucl k →L[ℝ] Eucl Q) → ℝ, ∀ k Q L, J k Q L =
      Real.sqrt (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det :=
    ⟨fun k Q L => Real.sqrt (Matrix.of fun i j : Fin k =>
          inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det, fun _ _ _ => rfl⟩
  -- the Jacobian `J L = √det ⟨L eᵢ, L eⱼ⟩` is continuous in `L`
  have hJc :
      ∀ k Q : ℕ, Continuous (J k Q) := by
    intro k Q
    have hJk : J k Q = fun L => Real.sqrt (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det :=
      funext (hJ k Q)
    rw [hJk]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.of_apply]
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- `J L = 0` when `L` is not injective
  have hJ0 :
      ∀ (k Q : ℕ) (L : Eucl k →L[ℝ] Eucl Q), ¬ Function.Injective L → J k Q L = 0 := by
    intro k Q L hL
    obtain ⟨u, hu0, hLu⟩ : ∃ u : Eucl k, u ≠ 0 ∧ L u = 0 := by
      simp only [Function.Injective, not_forall] at hL
      obtain ⟨a, b, hab, hne⟩ := hL
      exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩
    rw [hJ]
    have hdet : (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨u.ofLp, ?_, ?_⟩
      · intro h
        apply hu0
        ext i
        simp [h]
      · ext i
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        have hsum : u = ∑ j, u.ofLp j • EuclideanSpace.single j (1 : ℝ) := by
          conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr u]
          simp
        have : inner ℝ (L (EuclideanSpace.single i 1)) (L u) = 0 := by rw [hLu, inner_zero_right]
        rw [hsum, map_sum, inner_sum] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, inner_smul_right, mul_comm]
    rw [hdet, Real.sqrt_zero]
  -- linear area formula: `Hᵏ(L E) = J L · |E|` (factor `L` through a linear isometry)
  have hLAF :
      ∀ (k Q : ℕ) (L : Eucl k →L[ℝ] Eucl Q), Function.Injective L →
      ∀ E : Set (Eucl k), (μHE[k] : Measure (Eucl Q)) (L '' E) = ENNReal.ofReal (J k Q L) * volume E := by
    intro k Q L hL E
    set V := LinearMap.range (L : Eucl k →ₗ[ℝ] Eucl Q) with hVdef
    have hV : Module.finrank ℝ V = k := by
      rw [LinearMap.finrank_range_of_inj (f := (L : Eucl k →ₗ[ℝ] Eucl Q)) hL]
      exact finrank_euclideanSpace_fin
    let b : OrthonormalBasis (Fin k) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
    let e : V ≃ₗᵢ[ℝ] Eucl k := b.repr
    let M : Eucl k →ₗ[ℝ] Eucl k :=
      e.toLinearEquiv.toLinearMap ∘ₗ (L : Eucl k →ₗ[ℝ] Eucl Q).rangeRestrict
    let ι : Eucl k →ₗᵢ[ℝ] Eucl Q := V.subtypeₗᵢ.comp e.symm.toLinearIsometry
    have hfac : ∀ x, L x = ι (M x) := by
      intro x
      simp [ι, M]
    have himg : L '' E = ι '' (M '' E) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hfac x)
    rw [himg, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
    congr 2
    rw [hJ]
    set bE := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis with hbE
    have hgram : (Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))) =
        (LinearMap.toMatrix bE bE M).transpose * LinearMap.toMatrix bE bE M := by
      ext i j
      rw [Matrix.of_apply, hfac, hfac, LinearIsometry.inner_map_map, Matrix.mul_apply,
        EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Matrix.transpose_apply, LinearMap.toMatrix_apply, star_trivial]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [bE, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
      ring
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, ← sq,
      Real.sqrt_sq_eq_abs]
  -- the lift `L_η x = (L x, η x)`: `|L_η v| ≥ |L v|, η |v|` and `J L_η → J L` as `η → 0`
  have hlift :
      ∀ (k Q : ℕ) (L : Eucl k →L[ℝ] Eucl Q) (κ : ℝ), 0 < κ → ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ Lη : Eucl k →L[ℝ] Eucl (Q + k),
        (∀ v, ‖L v‖ ≤ ‖Lη v‖) ∧ (∀ v, η * ‖v‖ ≤ ‖Lη v‖) ∧ J k (Q + k) Lη ≤ J k Q L + κ := by
    intro k Q L κ hκ
    let lift : ℝ → (Eucl k →L[ℝ] Eucl (Q + k)) := fun η => LinearMap.toContinuousLinearMap
      { toFun := fun x => (EuclideanSpace.equiv (Fin (Q + k)) ℝ).symm
          (Fin.append (EuclideanSpace.equiv (Fin Q) ℝ (L x)) (η • EuclideanSpace.equiv (Fin k) ℝ x))
        map_add' := by
          intro x y
          ext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
        map_smul' := by
          intro c x
          ext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [mul_left_comm] }
    have hlift : ∀ η x, lift η x = (EuclideanSpace.equiv (Fin (Q + k)) ℝ).symm
        (Fin.append (EuclideanSpace.equiv (Fin Q) ℝ (L x)) (η • EuclideanSpace.equiv (Fin k) ℝ x)) :=
      fun η x => rfl
    have hinner : ∀ η x y, inner ℝ (lift η x) (lift η y) =
        inner ℝ (L x) (L y) + η ^ 2 * inner ℝ x y := by
      intro η x y
      rw [hlift, hlift]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_add]
      simp [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hnorm : ∀ η x, ‖lift η x‖ ^ 2 = ‖L x‖ ^ 2 + η ^ 2 * ‖x‖ ^ 2 := by
      intro η x
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, hinner]
    set G0 : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j : Fin k =>
        inner ℝ (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1)) with hG0
    have hgram : ∀ η : ℝ, (Matrix.of fun i j : Fin k => inner ℝ (lift η (EuclideanSpace.single i 1))
        (lift η (EuclideanSpace.single j 1))) = Matrix.of fun i j => G0 i j +
          η ^ 2 * (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
      intro η
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, hinner, EuclideanSpace.inner_single_left]
      by_cases hij : i = j
      · subst hij
        simp [hG0]
      · simp [hG0, hij]
    set F : ℝ → ℝ := fun η => (Matrix.of fun i j => G0 i j +
        η ^ 2 * (1 : Matrix (Fin k) (Fin k) ℝ) i j).det with hF
    have hFc : Continuous F := by
      refine Continuous.matrix_det ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.of_apply]
      fun_prop
    have hF0 : F 0 = G0.det := by
      simp only [hF]
      congr 1
      ext i j
      simp
    have hcont : Continuous fun η => Real.sqrt (F η) := Real.continuous_sqrt.comp hFc
    obtain ⟨η₀, hη₀, hη₀'⟩ := Metric.continuous_iff.mp hcont 0 κ hκ
    refine ⟨η₀, hη₀, fun η hη hηlt => ⟨lift η, ?_, ?_, ?_⟩⟩
    · intro v
      have h := hnorm η v
      have : ‖L v‖ ^ 2 ≤ ‖lift η v‖ ^ 2 := by
        rw [h]
        have : 0 ≤ η ^ 2 * ‖v‖ ^ 2 := by positivity
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    · intro v
      have h := hnorm η v
      have : (η * ‖v‖) ^ 2 ≤ ‖lift η v‖ ^ 2 := by
        rw [h, mul_pow]
        have : 0 ≤ ‖L v‖ ^ 2 := by positivity
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this
    · rw [hJ, hJ, hgram, ← hG0]
      have h := hη₀' η (by rw [Real.dist_eq, sub_zero, abs_of_pos hη]; exact hηlt)
      rw [Real.dist_eq] at h
      have h' : Real.sqrt (F η) - Real.sqrt (F 0) < κ := lt_of_abs_lt h
      rw [hF0] at h'
      simp only [hF] at h'
      linarith
  -- Lipschitz comparison of images: `Hᵏ(g₂ S) ≤ cᵏ Hᵏ(g₁ S)` when `|Δg₂| ≤ c |Δg₁|` on `S`
  have hcomp :
      ∀ (k Q₁ Q₂ : ℕ) (g₁ : Eucl k → Eucl Q₁) (g₂ : Eucl k → Eucl Q₂)
      (S : Set (Eucl k)) (c : ℝ≥0), InjOn g₁ S →
      (∀ x ∈ S, ∀ x' ∈ S, ‖g₂ x - g₂ x'‖ ≤ c * ‖g₁ x - g₁ x'‖) →
      (μHE[k] : Measure (Eucl Q₂)) (g₂ '' S) ≤
        (c : ℝ≥0∞) ^ k * (μHE[k] : Measure (Eucl Q₁)) (g₁ '' S) := by
    intro k Q₁ Q₂ g₁ g₂ S c hinj hle
    set h : Eucl Q₁ → Eucl Q₂ := fun y => g₂ (Function.invFunOn g₁ S y) with hhdef
    have hh : ∀ x ∈ S, h (g₁ x) = g₂ x := fun x hx => by
      simp only [hhdef]
      rw [hinj.leftInvOn_invFunOn hx]
    have himg : h '' (g₁ '' S) = g₂ '' S := by
      rw [image_image]
      exact image_congr hh
    have hlip : LipschitzOnWith c h (g₁ '' S) := by
      refine LipschitzOnWith.of_dist_le_mul ?_
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      rw [hh x hx, hh x' hx', dist_eq_norm, dist_eq_norm]
      exact hle x hx x' hx'
    have hH := hlip.hausdorffMeasure_image_le (d := (k : ℝ)) (Nat.cast_nonneg k)
    rw [ENNReal.rpow_natCast, himg] at hH
    rw [Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
    exact mul_le_mul_right hH _
  -- the two-sided estimate on a partition into almost-linear pieces
  have hkey :
      ∀ (k Q : ℕ) (f : Eucl k → Eucl Q) (K : ℝ≥0) (S : Set (Eucl k)), LipschitzWith K f →
      MeasurableSet S → InjOn f S → (∀ x ∈ S, DifferentiableAt ℝ f x) →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ κ : ℝ, 0 < κ →
        (μHE[k] : Measure (Eucl Q)) (f '' S) ≤ ENNReal.ofReal (1 + δ) ^ k *
          ((∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x))) + 2 * ENNReal.ofReal κ * volume S) ∧
        (∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x))) ≤
          ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' S) +
            ENNReal.ofReal κ * volume S := by
    intro k Q f K S hf hS hinj hdiff δ hδ hδ2 κ hκ
    -- uniform continuity of `J` on the ball of radius `K`
    obtain ⟨ρ0, hρ0, hρ0'⟩ : ∃ ρ0 > 0, ∀ L ∈ closedBall (0 : Eucl k →L[ℝ] Eucl Q) K,
        ∀ L' ∈ closedBall (0 : Eucl k →L[ℝ] Eucl Q) K, dist L L' < ρ0 →
          dist (J k Q L) (J k Q L') < κ :=
      Metric.uniformContinuousOn_iff.mp ((isCompact_closedBall _ _).uniformContinuousOn_of_continuous
        (hJc k Q).continuousOn) κ hκ
    have hDf : ∀ x, fderiv ℝ f x ∈ closedBall (0 : Eucl k →L[ℝ] Eucl Q) K := fun x => by
      rw [mem_closedBall, dist_zero_right]
      exact norm_fderiv_le_of_lipschitz ℝ hf
    -- a dense sequence of linear maps, and the pre-pieces
    obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq (Eucl k →L[ℝ] Eucl Q)
    set P : ℕ → Set (Eucl k) := fun n => S ∩ fderiv ℝ f ⁻¹' ball (D n) (ρ0 / 2) with hPdef
    have hPm : ∀ n, MeasurableSet (P n) := fun n =>
      hS.inter (measurable_fderiv ℝ f measurableSet_ball)
    have hPcov : S ⊆ ⋃ n, P n := by
      intro x hx
      obtain ⟨n, hn⟩ := (Metric.denseRange_iff.mp hD) (fderiv ℝ f x) (ρ0 / 2) (by positivity)
      exact mem_iUnion.mpr ⟨n, hx, by rw [mem_preimage, mem_ball]; exact hn⟩
    set P' : ℕ → Set (Eucl k) := disjointed P with hP'eq
    have hP'm : ∀ n, MeasurableSet (P' n) := MeasurableSet.disjointed hPm
    have hP'P : ∀ n, P' n ⊆ P n := disjointed_subset P
    have hP'S : ∀ n, P' n ⊆ S := fun n => (hP'P n).trans inter_subset_left
    have hP'cov : S ⊆ ⋃ n, P' n := by rw [hP'eq, iUnion_disjointed]; exact hPcov
    have hP'disj : Pairwise (Function.onFun Disjoint P') := disjoint_disjointed P
    -- the scale `ρ A` attached to each linear map
    have hρex : ∀ A : Eucl k →L[ℝ] Eucl Q, ∃ ρ : ℝ, 0 < ρ ∧
        (Function.Injective A → ∀ v, ρ * ‖v‖ ≤ ‖A v‖) ∧
        ∃ Aρ : Eucl k →L[ℝ] Eucl (Q + k), (∀ v, ‖A v‖ ≤ ‖Aρ v‖) ∧ (∀ v, ρ * ‖v‖ ≤ ‖Aρ v‖) ∧
          J k (Q + k) Aρ ≤ J k Q A + κ := by
      intro A
      obtain ⟨η₀, hη₀, hη₀'⟩ := hlift k Q A κ hκ
      by_cases hA : Function.Injective A
      · obtain ⟨C, hC, hCA⟩ := (A : Eucl k →ₗ[ℝ] Eucl Q).exists_antilipschitzWith
          (LinearMap.ker_eq_bot.mpr hA)
        have hCpos : (0 : ℝ) < C := hC
        set ρ := min (η₀ / 2) (1 / (C : ℝ)) with hρ
        have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
        obtain ⟨Aρ, h1, h2, h3⟩ := hη₀' ρ hρpos (lt_of_le_of_lt (min_le_left _ _) (by linarith))
        refine ⟨ρ, hρpos, fun _ v => ?_, Aρ, h1, h2, h3⟩
        have hv : ‖v‖ ≤ C * ‖A v‖ := by
          have := hCA.le_mul_dist v 0
          simpa [dist_zero_right] using this
        calc ρ * ‖v‖ ≤ (1 / C) * ‖v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
          _ ≤ (1 / C) * (C * ‖A v‖) := mul_le_mul_of_nonneg_left hv (by positivity)
          _ = ‖A v‖ := by field_simp
      · obtain ⟨Aρ, h1, h2, h3⟩ := hη₀' (η₀ / 2) (by positivity) (by linarith)
        exact ⟨η₀ / 2, by positivity, fun h => absurd h hA, Aρ, h1, h2, h3⟩
    choose ρ hρpos hρinj Aρ hAρ1 hAρ2 hAρJ using hρex
    set r : (Eucl k →L[ℝ] Eucl Q) → ℝ≥0 := fun A => Real.toNNReal (δ * ρ A) with hrdef
    have hrpos : ∀ A, r A ≠ 0 := fun A => by
      simp only [hrdef, ne_eq, Real.toNNReal_eq_zero, not_le]
      exact mul_pos hδ (hρpos A)
    have hr : ∀ A, (r A : ℝ) = δ * ρ A := fun A => Real.coe_toNNReal _ (mul_pos hδ (hρpos A)).le
    -- the partition of each pre-piece
    have hpart : ∀ n, ∃ (t : ℕ → Set (Eucl k)) (A : ℕ → (Eucl k →L[ℝ] Eucl Q)),
        Pairwise (Function.onFun Disjoint t) ∧ (∀ j, MeasurableSet (t j)) ∧ P' n ⊆ ⋃ j, t j ∧
        (∀ j, ApproximatesLinearOn f (A j) (P' n ∩ t j) (r (A j))) ∧
        ((P' n).Nonempty → ∀ j, ∃ y ∈ P' n, A j = fderiv ℝ f y) := fun n =>
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f (P' n) (fderiv ℝ f)
        (fun x hx => (hdiff x (hP'S n hx)).hasFDerivAt.hasFDerivWithinAt) r hrpos
    choose t A ht_disj ht_meas ht_cov ht_approx ht_der using hpart
    -- the pieces
    set Sp : ℕ × ℕ → Set (Eucl k) := fun p => P' p.1 ∩ t p.1 p.2 with hSpdef
    have hSpm : ∀ p, MeasurableSet (Sp p) := fun p => (hP'm p.1).inter (ht_meas p.1 p.2)
    have hSpS : ∀ p, Sp p ⊆ S := fun p => inter_subset_left.trans (hP'S p.1)
    have hSpdisj : Pairwise (Function.onFun Disjoint Sp) := by
      rintro ⟨n, j⟩ ⟨n', j'⟩ hne
      by_cases hn : n = n'
      · subst hn
        have hj : j ≠ j' := fun h => hne (by rw [h])
        exact Disjoint.mono inter_subset_right inter_subset_right (ht_disj n hj)
      · exact Disjoint.mono inter_subset_left inter_subset_left (hP'disj hn)
    have hSpcov : S = ⋃ p, Sp p := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp (hP'cov hx)
        obtain ⟨j, hj⟩ := mem_iUnion.mp (ht_cov n hn)
        exact mem_iUnion.mpr ⟨(n, j), hn, hj⟩
      · exact iUnion_subset hSpS
    -- the three quantities as sums over the pieces
    have hXsum : (μHE[k] : Measure (Eucl Q)) (f '' S) =
        ∑' p, (μHE[k] : Measure (Eucl Q)) (f '' Sp p) := by
      conv_lhs => rw [hSpcov, image_iUnion]
      refine measure_iUnion ?_ ?_
      · intro p q hpq
        refine Set.disjoint_left.mpr ?_
        rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
        have : x' = x := hinj (hSpS q hx') (hSpS p hx) hxx'
        subst this
        exact Set.disjoint_left.mp (hSpdisj hpq) hx hx'
      · intro p
        exact (hSpm p).image_of_continuousOn_injOn hf.continuous.continuousOn (hinj.mono (hSpS p))
    have hYsum : ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) =
        ∑' p, ∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
      conv_lhs => rw [hSpcov]
      exact lintegral_iUnion hSpm hSpdisj _
    have hVsum : volume S = ∑' p, volume (Sp p) := by
      conv_lhs => rw [hSpcov]
      exact measure_iUnion hSpdisj hSpm
    -- the estimates on one piece
    have hpiece : ∀ p, (μHE[k] : Measure (Eucl Q)) (f '' Sp p) ≤ ENNReal.ofReal (1 + δ) ^ k *
          ((∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
            2 * ENNReal.ofReal κ * volume (Sp p)) ∧
        (∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))) ≤
          ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' Sp p) +
            ENNReal.ofReal κ * volume (Sp p) := by
      rintro ⟨n, j⟩
      rcases (Sp (n, j)).eq_empty_or_nonempty with hemp | hne
      · simp [hemp]
      obtain ⟨y, hyP, hAy⟩ := ht_der n ⟨hne.some, hne.some_mem.1⟩ j
      have happ := ht_approx n j
      generalize A n j = A0 at happ hAy
      have hJclose : ∀ x ∈ Sp (n, j), dist (J k Q (fderiv ℝ f x)) (J k Q A0) < κ := by
        intro x hx
        refine hρ0' _ (hDf x) _ (by rw [hAy]; exact hDf y) ?_
        have hx1 : dist (fderiv ℝ f x) (D n) < ρ0 / 2 := (hP'P n hx.1).2
        have hy1 : dist (fderiv ℝ f y) (D n) < ρ0 / 2 := (hP'P n hyP).2
        rw [hAy]
        calc dist (fderiv ℝ f x) (fderiv ℝ f y)
            ≤ dist (fderiv ℝ f x) (D n) + dist (D n) (fderiv ℝ f y) := dist_triangle _ _ _
          _ < ρ0 / 2 + ρ0 / 2 := by rw [dist_comm (D n)]; exact add_lt_add hx1 hy1
          _ = ρ0 := by ring
      have happ' : ∀ x ∈ Sp (n, j), ∀ x' ∈ Sp (n, j),
          ‖f x - f x' - A0 (x - x')‖ ≤ δ * ρ A0 * ‖x - x'‖ := by
        intro x hx x' hx'
        have := happ x hx x' hx'
        rwa [hr] at this
      -- upper bound through the lift `Aρ A0`
      have hup : ∀ x ∈ Sp (n, j), ∀ x' ∈ Sp (n, j),
          ‖f x - f x'‖ ≤ (Real.toNNReal (1 + δ) : ℝ) * ‖Aρ A0 x - Aρ A0 x'‖ := by
        intro x hx x' hx'
        rw [Real.coe_toNNReal _ (by linarith), ← map_sub]
        have h1 := happ' x hx x' hx'
        have h2 := hAρ1 A0 (x - x')
        have h3 := hAρ2 A0 (x - x')
        calc ‖f x - f x'‖ = ‖(f x - f x' - A0 (x - x')) + A0 (x - x')‖ := by congr 1; abel
          _ ≤ ‖f x - f x' - A0 (x - x')‖ + ‖A0 (x - x')‖ := norm_add_le _ _
          _ ≤ δ * ρ A0 * ‖x - x'‖ + ‖Aρ A0 (x - x')‖ := add_le_add h1 h2
          _ ≤ δ * ‖Aρ A0 (x - x')‖ + ‖Aρ A0 (x - x')‖ := by nlinarith
          _ = (1 + δ) * ‖Aρ A0 (x - x')‖ := by ring
      have hAρinj : Function.Injective (Aρ A0) := by
        intro v w hvw
        have h := hAρ2 A0 (v - w)
        rw [map_sub, hvw, sub_self, norm_zero] at h
        have h' : ‖v - w‖ = 0 :=
          le_antisymm (by nlinarith [hρpos A0, norm_nonneg (v - w)]) (norm_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp h')
      have hX_le : (μHE[k] : Measure (Eucl Q)) (f '' Sp (n, j)) ≤ ENNReal.ofReal (1 + δ) ^ k *
          (ENNReal.ofReal (J k (Q + k) (Aρ A0)) * volume (Sp (n, j))) := by
        have := hcomp k (Q + k) Q (Aρ A0) f (Sp (n, j)) (Real.toNNReal (1 + δ)) hAρinj.injOn hup
        rwa [hLAF k (Q + k) (Aρ A0) hAρinj] at this
      -- comparison of `J (Df x)` with `J A0` on the piece
      have hJx_le : ∀ x ∈ Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x)) ≤
          ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ := by
        intro x hx
        have h := hJclose x hx
        rw [Real.dist_eq] at h
        exact (ENNReal.ofReal_le_ofReal (by linarith [abs_lt.mp h])).trans ENNReal.ofReal_add_le
      have hA_le : ∀ x ∈ Sp (n, j), ENNReal.ofReal (J k Q A0) ≤
          ENNReal.ofReal (J k Q (fderiv ℝ f x)) + ENNReal.ofReal κ := by
        intro x hx
        have h := hJclose x hx
        rw [Real.dist_eq] at h
        exact (ENNReal.ofReal_le_ofReal (by linarith [abs_lt.mp h])).trans ENNReal.ofReal_add_le
      have hY_le : ∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x)) ≤
          (ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) * volume (Sp (n, j)) := by
        calc _ ≤ ∫⁻ x in Sp (n, j), (ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) :=
              setLIntegral_mono' (hSpm _) (fun x hx => hJx_le x hx)
          _ = _ := setLIntegral_const _ _
      have hA_int : ENNReal.ofReal (J k Q A0) * volume (Sp (n, j)) ≤
          (∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
            ENNReal.ofReal κ * volume (Sp (n, j)) := by
        calc ENNReal.ofReal (J k Q A0) * volume (Sp (n, j))
            = ∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q A0) := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in Sp (n, j), (ENNReal.ofReal (J k Q (fderiv ℝ f x)) + ENNReal.ofReal κ) :=
              setLIntegral_mono' (hSpm _) (fun x hx => hA_le x hx)
          _ = _ := by rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      -- lower bound through `A0` itself
      have hlow : ENNReal.ofReal (J k Q A0) * volume (Sp (n, j)) ≤
          ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' Sp (n, j)) := by
        by_cases hinjA : Function.Injective A0
        · rw [← hLAF k Q A0 hinjA]
          refine hcomp k Q Q f A0 (Sp (n, j)) (Real.toNNReal (1 - δ)⁻¹) (hinj.mono (hSpS _)) ?_
          intro x hx x' hx'
          have h1δ : 0 < 1 - δ := by linarith
          rw [Real.coe_toNNReal _ (by positivity), ← map_sub]
          have h1 := happ' x hx x' hx'
          have h2 := hρinj A0 hinjA (x - x')
          have h3 : ‖A0 (x - x')‖ ≤ ‖f x - f x'‖ + δ * ‖A0 (x - x')‖ := by
            calc ‖A0 (x - x')‖ = ‖(f x - f x') - (f x - f x' - A0 (x - x'))‖ := by
                  congr 1; abel
              _ ≤ ‖f x - f x'‖ + ‖f x - f x' - A0 (x - x')‖ := norm_sub_le _ _
              _ ≤ ‖f x - f x'‖ + δ * ρ A0 * ‖x - x'‖ := by linarith
              _ ≤ ‖f x - f x'‖ + δ * ‖A0 (x - x')‖ := by nlinarith
          rw [inv_mul_eq_div, le_div_iff₀ h1δ]
          linarith
        · rw [hJ0 k Q A0 hinjA, ENNReal.ofReal_zero, zero_mul]
          exact bot_le
      constructor
      · calc (μHE[k] : Measure (Eucl Q)) (f '' Sp (n, j))
            ≤ ENNReal.ofReal (1 + δ) ^ k *
                (ENNReal.ofReal (J k (Q + k) (Aρ A0)) * volume (Sp (n, j))) := hX_le
          _ ≤ ENNReal.ofReal (1 + δ) ^ k *
                ((ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) * volume (Sp (n, j))) := by
            gcongr
            exact (ENNReal.ofReal_le_ofReal (hAρJ A0)).trans ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal (1 + δ) ^ k *
                ((∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
                  2 * ENNReal.ofReal κ * volume (Sp (n, j))) := by
            gcongr
            rw [add_mul]
            calc _ ≤ ((∫⁻ x in Sp (n, j), ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
                    ENNReal.ofReal κ * volume (Sp (n, j))) +
                    ENNReal.ofReal κ * volume (Sp (n, j)) := add_le_add hA_int le_rfl
              _ = _ := by ring
      · calc _ ≤ (ENNReal.ofReal (J k Q A0) + ENNReal.ofReal κ) * volume (Sp (n, j)) := hY_le
          _ = ENNReal.ofReal (J k Q A0) * volume (Sp (n, j)) +
                ENNReal.ofReal κ * volume (Sp (n, j)) := add_mul _ _ _
          _ ≤ _ := add_le_add hlow le_rfl
    -- summing over the pieces
    constructor
    · rw [hXsum, hYsum, hVsum]
      calc ∑' p, (μHE[k] : Measure (Eucl Q)) (f '' Sp p)
          ≤ ∑' p, ENNReal.ofReal (1 + δ) ^ k *
              ((∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))) +
                2 * ENNReal.ofReal κ * volume (Sp p)) := ENNReal.tsum_le_tsum fun p => (hpiece p).1
        _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    · rw [hXsum, hYsum, hVsum]
      calc ∑' p, ∫⁻ x in Sp p, ENNReal.ofReal (J k Q (fderiv ℝ f x))
          ≤ ∑' p, (ENNReal.ofReal (1 - δ)⁻¹ ^ k * (μHE[k] : Measure (Eucl Q)) (f '' Sp p) +
              ENNReal.ofReal κ * volume (Sp p)) := ENNReal.tsum_le_tsum fun p => (hpiece p).2
        _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  -- injective area formula for sets: `Hᵏ(f S) = ∫_S J(Df)`
  have hC7 :
      ∀ (k Q : ℕ) (f : Eucl k → Eucl Q) (K : ℝ≥0) (S : Set (Eucl k)), LipschitzWith K f →
      MeasurableSet S → InjOn f S → (∀ x ∈ S, DifferentiableAt ℝ f x) →
      (μHE[k] : Measure (Eucl Q)) (f '' S) = ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
    intro k Q f K S hf hS hinj hdiff
    -- the finite-volume case
    have hfin : ∀ T ⊆ S, MeasurableSet T → volume T < ∞ →
        (μHE[k] : Measure (Eucl Q)) (f '' T) = ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
      intro T hTS hT hTfin
      have hkeyT := hkey k Q f K T hf hT (hinj.mono hTS) (fun x hx => hdiff x (hTS hx))
      have hXfin : (μHE[k] : Measure (Eucl Q)) (f '' T) < ∞ := by
        have h := hcomp k k Q id f T K (injOn_id T) (fun x _ x' _ => by
          simpa [dist_eq_norm] using hf.dist_le_mul x x')
        rw [image_id, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
        exact h.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hTfin)
      have hVne : volume T ≠ ∞ := hTfin.ne
      -- `X ≤ Y`
      have hle1 : (μHE[k] : Measure (Eucl Q)) (f '' T) ≤
          ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
        set Y := ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) with hY
        have ha : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 + δ) ^ k) (𝓝 0) (𝓝 1) := by
          have : Continuous (fun δ : ℝ => ENNReal.ofReal (1 + δ) ^ k) :=
            (ENNReal.continuous_pow k).comp
              (ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id))
          simpa using this.tendsto 0
        have hb : Tendsto (fun δ : ℝ => Y + 2 * ENNReal.ofReal δ * volume T) (𝓝 0) (𝓝 Y) := by
          have : Continuous (fun δ : ℝ => Y + 2 * ENNReal.ofReal δ * volume T) :=
            continuous_const.add ((ENNReal.continuous_mul_const hVne).comp
              ((ENNReal.continuous_const_mul (by simp)).comp ENNReal.continuous_ofReal))
          simpa using this.tendsto 0
        have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 + δ) ^ k *
            (Y + 2 * ENNReal.ofReal δ * volume T)) (𝓝[>] 0) (𝓝 Y) := by
          have := ENNReal.Tendsto.mul ha (Or.inl one_ne_zero) hb (Or.inr ENNReal.one_ne_top)
          rw [one_mul] at this
          exact this.mono_left nhdsWithin_le_nhds
        refine ge_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
        exact (hkeyT δ hδ.1 hδ.2 δ hδ.1).1
      -- `Y ≤ X`
      have hle2 : ∫⁻ x in T, ENNReal.ofReal (J k Q (fderiv ℝ f x)) ≤
          (μHE[k] : Measure (Eucl Q)) (f '' T) := by
        set X := (μHE[k] : Measure (Eucl Q)) (f '' T) with hX
        have ha : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 - δ)⁻¹ ^ k) (𝓝 0) (𝓝 1) := by
          have h1 : ContinuousAt (fun δ : ℝ => (1 - δ)⁻¹) 0 :=
            (continuous_const.sub continuous_id).continuousAt.inv₀ (by norm_num)
          have h2 : ContinuousAt (fun δ : ℝ => ENNReal.ofReal (1 - δ)⁻¹ ^ k) 0 :=
            (ENNReal.continuous_pow k).continuousAt.comp
              (ENNReal.continuous_ofReal.continuousAt.comp h1)
          simpa using h2.tendsto
        have hb : Tendsto (fun δ : ℝ => ENNReal.ofReal δ * volume T) (𝓝 0) (𝓝 0) := by
          have : Continuous (fun δ : ℝ => ENNReal.ofReal δ * volume T) :=
            (ENNReal.continuous_mul_const hVne).comp ENNReal.continuous_ofReal
          simpa using this.tendsto 0
        have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (1 - δ)⁻¹ ^ k * X +
            ENNReal.ofReal δ * volume T) (𝓝[>] 0) (𝓝 X) := by
          have h1 := ENNReal.Tendsto.mul_const ha (Or.inr hXfin.ne)
          have := h1.add hb
          rw [one_mul, add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        refine ge_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
        exact (hkeyT δ hδ.1 hδ.2 δ hδ.1).2
      exact le_antisymm hle1 hle2
    -- exhaustion by balls
    set T : ℕ → Set (Eucl k) := fun j => S ∩ closedBall 0 j with hTdef
    have hTmono : Monotone T := fun a b hab =>
      inter_subset_inter_right _ (closedBall_subset_closedBall (by exact_mod_cast hab))
    have hTU : S = ⋃ j, T j := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
        exact mem_iUnion.mpr ⟨j, hx, by rw [mem_closedBall, dist_zero_right]; exact hj⟩
      · exact iUnion_subset fun j => inter_subset_left
    have hTm : ∀ j, MeasurableSet (T j) := fun j => hS.inter measurableSet_closedBall
    calc (μHE[k] : Measure (Eucl Q)) (f '' S)
        = ⨆ j, (μHE[k] : Measure (Eucl Q)) (f '' T j) := by
          rw [hTU, image_iUnion]
          exact Monotone.measure_iUnion (fun a b hab => image_mono (hTmono hab))
      _ = ⨆ j, ∫⁻ x in T j, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
          refine iSup_congr fun j => hfin (T j) inter_subset_left (hTm j) ?_
          exact (measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top
      _ = ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) := by
          rw [hTU]
          simp_rw [← withDensity_apply _ (hTm _)]
          rw [← withDensity_apply _ (MeasurableSet.iUnion hTm)]
          exact (Monotone.measure_iUnion hTmono).symm
  -- injective area formula for nonnegative weights
  have hAF :
      ∀ (k Q : ℕ) (f : Eucl k → Eucl Q) (K : ℝ≥0) (S : Set (Eucl k)), LipschitzWith K f →
      MeasurableSet S → InjOn f S → (∀ x ∈ S, DifferentiableAt ℝ f x) →
      ∀ u : Eucl Q → ℝ≥0∞, Measurable u →
        ∫⁻ y in f '' S, u y ∂(μHE[k] : Measure (Eucl Q)) =
          ∫⁻ x in S, ENNReal.ofReal (J k Q (fderiv ℝ f x)) * u (f x) := by
    intro k Q f K S hf hS hinj hdiff u hu
    have hφm : Measurable fun x => ENNReal.ofReal (J k Q (fderiv ℝ f x)) :=
      ENNReal.measurable_ofReal.comp ((hJc k Q).measurable.comp (measurable_fderiv ℝ f))
    have hfm : Measurable f := hf.continuous.measurable
    have hmeas : (μHE[k] : Measure (Eucl Q)).restrict (f '' S) =
        ((volume.restrict S).withDensity fun x => ENNReal.ofReal (J k Q (fderiv ℝ f x))).map f := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.map_apply hfm hT, withDensity_apply _ (hfm hT),
        Measure.restrict_restrict (hfm hT), inter_comm T, ← image_inter_preimage,
        inter_comm (f ⁻¹' T)]
      exact hC7 k Q f K (S ∩ f ⁻¹' T) hf (hS.inter (hfm hT)) (hinj.mono inter_subset_left)
        (fun x hx => hdiff x hx.1)
    rw [hmeas, lintegral_map hu hfm]
    exact lintegral_withDensity_eq_lintegral_mul (volume.restrict S) hφm (hu.comp hfm)
  intro P m G K B hG hB hinj hdiff g hg
  -- notation
  set Φ : ℝ → Eucl P → Eucl (P + 1) := fun s x =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))
    with hΦdef
  have hΦc : Continuous fun q : ℝ × Eucl P => Φ q.1 q.2 := by
    have : Continuous fun q : ℝ × Eucl P =>
        (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2) : Fin (P + 1) → ℝ) := by
      refine continuous_pi fun k => ?_
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
    exact (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp this
  -- (8.1): the area formula in dimension `m`
  set Jm : Eucl m → ℝ≥0∞ := fun b => ENNReal.ofReal (J m P (fderiv ℝ G b)) with hJmdef
  have hJmm : Measurable Jm :=
    ENNReal.measurable_ofReal.comp ((hJc m P).measurable.comp (measurable_fderiv ℝ G))
  set H : ℝ × Eucl m → ℝ≥0∞ := fun q => Jm q.2 * g (Φ q.1 (G q.2)) with hHdef
  have hHm : Measurable H := by
    refine (hJmm.comp measurable_snd).mul (hg.comp ?_)
    exact (hΦc.comp (continuous_fst.prodMk (hG.continuous.comp continuous_snd))).measurable
  have hinner : ∀ s : ℝ, ∫⁻ b in B, H (s, b) =
      ∫⁻ x in G '' B, g (Φ s x) ∂(μHE[m] : Measure (Eucl P)) := fun s =>
    (hAF m P G K B hG hB hinj hdiff (fun x => g (Φ s x))
      (hg.comp (hΦc.comp (continuous_const.prodMk continuous_id)).measurable)).symm
  refine ⟨?_, ?_⟩
  · -- measurability of the inner integral
    have hmeas : Measurable fun s : ℝ => ∫⁻ b, H (s, b) ∂((volume : Measure (Eucl m)).restrict B) :=
      hHm.lintegral_prod_right'
    have heq : (fun s : ℝ => ∫⁻ b, H (s, b) ∂((volume : Measure (Eucl m)).restrict B)) =
        fun s => ∫⁻ x in G '' B, g (Φ s x) ∂(μHE[m] : Measure (Eucl P)) := funext hinner
    rw [heq] at hmeas
    exact hmeas
  · -- the lift
    set e1 := EuclideanSpace.equiv (Fin (m + 1)) ℝ with he1
    set tl : Eucl (m + 1) → Eucl m := fun v =>
      (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (e1 v)) with htldef
    have htlc : Continuous tl := by
      have : Continuous fun v : Eucl (m + 1) => Fin.tail (e1 v) :=
        continuous_pi fun i => (continuous_apply i.succ).comp e1.continuous
      exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp this
    set Gt : Eucl (m + 1) → Eucl (P + 1) := fun v => Φ (e1 v 0) (G (tl v)) with hGtdef
    set Bt : Set (Eucl (m + 1)) := tl ⁻¹' B with hBtdef
    have hBt : MeasurableSet Bt := hB.preimage htlc.measurable
    -- norm identities
    have hnormΦ : ∀ (s : ℝ) (x : Eucl P), ‖Φ s x‖ ^ 2 = s ^ 2 + ‖x‖ ^ 2 := by
      intro s x
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp [hΦdef]
    have hΦsub : ∀ (s s' : ℝ) (x x' : Eucl P), Φ s x - Φ s' x' = Φ (s - s') (x - x') := by
      intro s s' x x'
      ext k
      refine Fin.cases ?_ (fun j => ?_) k <;> simp [hΦdef]
    have hnormw : ∀ v : Eucl (m + 1), ‖v‖ ^ 2 = (e1 v 0) ^ 2 + ‖tl v‖ ^ 2 := by
      intro v
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp [htldef, he1, Fin.tail]
    have htlsub : ∀ v v' : Eucl (m + 1), tl v - tl v' = tl (v - v') := by
      intro v v'; ext k; simp [htldef, he1, Fin.tail]
    -- (i) Lipschitz
    have hGtL : LipschitzWith (max 1 K) Gt := by
      refine LipschitzWith.of_dist_le_mul fun v v' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : ‖Gt v - Gt v'‖ ^ 2 ≤ ((max 1 K : ℝ≥0) * ‖v - v'‖) ^ 2 := by
        simp only [hGtdef]
        rw [hΦsub, hnormΦ, mul_pow, hnormw (v - v')]
        have hK : ‖G (tl v) - G (tl v')‖ ≤ K * ‖tl v - tl v'‖ := by
          have := hG.dist_le_mul (tl v) (tl v')
          rwa [dist_eq_norm, dist_eq_norm] at this
        have hKm : (K : ℝ) ≤ (max 1 K : ℝ≥0) := by exact_mod_cast le_max_right 1 K
        have h1m : (1 : ℝ) ≤ (max 1 K : ℝ≥0) := by exact_mod_cast le_max_left 1 K
        have he0 : e1 v 0 - e1 v' 0 = e1 (v - v') 0 := by simp
        rw [he0, ← htlsub]
        have hA : (e1 (v - v') 0) ^ 2 ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 * (e1 (v - v') 0) ^ 2 := by
          have : (1 : ℝ) ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 := by nlinarith
          nlinarith [sq_nonneg (e1 (v - v') 0)]
        have hB2 : ‖G (tl v) - G (tl v')‖ ^ 2 ≤
            ((max 1 K : ℝ≥0) : ℝ) ^ 2 * ‖tl v - tl v'‖ ^ 2 := by
          have h0 : 0 ≤ ‖G (tl v) - G (tl v')‖ := norm_nonneg _
          have h2 : ‖G (tl v) - G (tl v')‖ ≤ ((max 1 K : ℝ≥0) : ℝ) * ‖tl v - tl v'‖ :=
            hK.trans (mul_le_mul_of_nonneg_right hKm (norm_nonneg _))
          calc ‖G (tl v) - G (tl v')‖ ^ 2 ≤ (((max 1 K : ℝ≥0) : ℝ) * ‖tl v - tl v'‖) ^ 2 :=
                pow_le_pow_left₀ h0 h2 2
            _ = _ := by ring
        nlinarith
      have h0 : 0 ≤ ((max 1 K : ℝ≥0) : ℝ) * ‖v - v'‖ := by positivity
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp h1
    -- coordinates of `Gt`
    have hπGt : ∀ v, (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ (Gt v))) = G (tl v) := by
      intro v; ext k; simp [hGtdef, hΦdef, Fin.tail]
    -- (ii) injectivity
    have hinjt : InjOn Gt Bt := by
      intro v hv v' hv' hvv
      have h0 : e1 v 0 = e1 v' 0 := by
        have := congrArg (fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ) y 0) hvv
        simpa [hGtdef, hΦdef] using this
      have htl : tl v = tl v' := by
        have := congrArg (fun y => (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) hvv
        simp only [hπGt] at this
        exact hinj hv hv' this
      ext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa [he1] using h0
      · have := congrArg (fun z => z j) htl
        simpa [htldef, he1, Fin.tail] using this
    -- (iii) image
    have himg : Gt '' Bt = {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B} := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        simp only [mem_ofPred_eq, hπGt]
        exact ⟨tl v, hv, rfl⟩
      · rintro ⟨b, hb, hby⟩
        refine ⟨e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin m) ℝ b)), ?_, ?_⟩
        · have : tl (e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
              (EuclideanSpace.equiv (Fin m) ℝ b))) = b := by
            ext k; simp [htldef, he1, Fin.tail]
          simp only [hBtdef, mem_preimage, this]
          exact hb
        · have htlb : tl (e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
              (EuclideanSpace.equiv (Fin m) ℝ b))) = b := by
            ext k; simp [htldef, he1, Fin.tail]
          simp only [hGtdef, htlb, hby]
          ext k
          refine Fin.cases ?_ (fun j => ?_) k
          · simp [hΦdef, he1]
          · simp [hΦdef, Fin.tail]
    -- differentiability of the lift on `Bt`
    have hdiffGt : ∀ v ∈ Bt, DifferentiableAt ℝ Gt v := by
      let Λ : (ℝ × Eucl P) →L[ℝ] Eucl (P + 1) := LinearMap.toContinuousLinearMap
        { toFun := fun q => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
            (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2))
          map_add' := by
            intro q q'
            ext k
            refine Fin.cases ?_ (fun j => ?_) k <;> simp
          map_smul' := by
            intro c q
            ext k
            refine Fin.cases ?_ (fun j => ?_) k <;> simp }
      let tlL : Eucl (m + 1) →L[ℝ] Eucl m := LinearMap.toContinuousLinearMap
        { toFun := fun v => (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ v))
          map_add' := by intro v v'; ext k; simp [Fin.tail]
          map_smul' := by intro c v; ext k; simp [Fin.tail] }
      let pr0 : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (m + 1))
      have hGt' : Gt = fun v => Λ (pr0 v, G (tlL v)) := by
        funext v
        rfl
      intro v hv
      rw [hGt']
      exact Λ.differentiableAt.comp v
        (pr0.differentiableAt.prodMk ((hdiff (tl v) hv).comp v tlL.differentiableAt))
    -- (iv) Jacobians
    have hjac : ∀ v ∈ Bt, J (m + 1) (P + 1) (fderiv ℝ Gt v) = J m P (fderiv ℝ G (tl v)) := by
      intro v hv
      rw [hJ, hJ,
        Submission.iwl_cr_hp_lift_gram_det P m G Gt v (tl v) (fun v => rfl) rfl (hdiff _ hv)]
    -- area formula in dimension `m + 1`
    have harea1 := hAF (m + 1) (P + 1) Gt (max 1 K) Bt hGtL hBt hinjt hdiffGt g hg
    rw [himg] at harea1
    rw [harea1]
    have hcongr : ∫⁻ v in Bt, ENNReal.ofReal (J (m + 1) (P + 1) (fderiv ℝ Gt v)) * g (Gt v) =
        ∫⁻ v in Bt, H (e1 v 0, tl v) := by
      refine setLIntegral_congr_fun hBt (fun v hv => ?_)
      rw [hjac v hv]
    rw [hcongr]
    -- the coordinate split
    set Ψ : Eucl (m + 1) → ℝ × Eucl m := fun v => (e1 v 0, tl v) with hΨdef
    have hΨ : MeasurePreserving Ψ (volume : Measure (Eucl (m + 1)))
        ((volume : Measure ℝ).prod (volume : Measure (Eucl m))) := by
      have h1 := PiLp.volume_preserving_ofLp (ι := Fin (m + 1))
      have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0
      have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_toLp (ι := Fin m))
      have h := h3.comp (h2.comp h1)
      convert h using 1
      funext v
      simp only [Function.comp_apply, hΨdef, htldef, he1]
      ext <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    have hpre : Bt = Ψ ⁻¹' (univ ×ˢ B) := by
      ext v; simp [hBtdef, hΨdef]
    rw [hpre, hΨ.setLIntegral_comp_preimage (MeasurableSet.univ.prod hB) hHm,
      ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod H hHm.aemeasurable]
    exact lintegral_congr fun s => hinner s

/-- Product formula for Hausdorff measure on rectifiable sets (Federer 3.2.23), with
`π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`, so `{y : π y ∈ S} = Φ(ℝ × S)`:
(a) if `Hᵐ(N) = 0` then `Hᵐ⁺¹(ℝ × N) = 0`; (b) if `A ⊆ ℝ^P` is `Hᵐ`-measurable and countably
`m`-rectifiable, then `∫_{ℝ × A} g dHᵐ⁺¹ = ∫_ℝ ∫_A g(Φ(s, x)) dHᵐ(x) ds` for Borel `g ≥ 0`, i.e.
`Hᵐ⁺¹ ⌞ (ℝ × A) = L¹ ⊗ Hᵐ ⌞ A`.  (a) is `iwl_cr_hp_cylinder_null`.  For (b), `A` is replaced by a
Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`, which by (a) changes neither side.  Up to an `Hᵐ`-null set,
`A₀` is the disjoint union of the Borel pieces `G p '' B p` with `G p` Lipschitz and injective on
`B p` (`iwl_cr_hp_injective_pieces`); the formula holds on each piece
(`iwl_cr_hp_piece_product`), and both sides are countably additive over the pieces, the cylinder
over the remainder being `Hᵐ⁺¹`-null by (a).  The local finiteness of `Hᵐ ⌞ A` is not needed. -/
theorem Submission.iwl_cr_hausdorff_product_formula : (∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) ∧ (∀ (P m : ℕ) (A : Set (Eucl P)), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) := by
  refine ⟨Submission.iwl_cr_hp_cylinder_null, ?_⟩
  intro P m A hA hrect _hfin g hg
  -- `pr y = (y₁, …, y_P)`, so the cylinder `ℝ × S` over `S ⊆ ℝ^P` is `pr ⁻¹' S`
  set pr : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hpr : Measurable pr := by
    have : Continuous fun y : Eucl (P + 1) => Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y) :=
      continuous_pi fun i => (continuous_apply i.succ).comp
        (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
    exact ((EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp this).measurable
  have hcyl : ∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1))) (pr ⁻¹' N) = 0 :=
    Submission.iwl_cr_hp_cylinder_null P m
  show ∫⁻ y in pr ⁻¹' A, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = _
  -- (1) a Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`; by (a) neither side changes
  obtain ⟨A₀, hA₀A, hA₀m, hA₀ae⟩ := hA.exists_measurable_subset_ae_eq
  have hL₀ : pr ⁻¹' A =ᵐ[(μHE[m + 1] : Measure (Eucl (P + 1)))] pr ⁻¹' A₀ :=
    ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy) (hcyl (A \ A₀) (ae_eq_set.1 hA₀ae).2),
      measure_mono_null (fun y hy => (hy.2 (hA₀A hy.1)).elim) measure_empty⟩
  -- (2) disjoint Borel pieces `G p '' B p` of `A₀`, Lipschitz and injective, up to a null set
  obtain ⟨G, B, hGL, hBm, hinj, hdiff, hsub, hGBm, hdisj, hrest⟩ :=
    Submission.iwl_cr_hp_injective_pieces P m A₀ hA₀m (hrect.mono hA₀A)
  choose K hK using hGL
  have hpiece := fun p => Submission.iwl_cr_hp_piece_product P m (G p) (K p) (B p) (hK p)
    (hBm p) (hinj p) (hdiff p) g hg
  have hU : A₀ =ᵐ[(μHE[m] : Measure (Eucl P))] ⋃ p, G p '' B p :=
    ae_eq_set.2 ⟨hrest,
      measure_mono_null (fun x hx => (hx.2 (iUnion_subset hsub hx.1)).elim) measure_empty⟩
  have hÛ : pr ⁻¹' A₀ =ᵐ[(μHE[m + 1] : Measure (Eucl (P + 1)))] ⋃ p, pr ⁻¹' (G p '' B p) := by
    rw [← preimage_iUnion]
    exact ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy) (hcyl (A₀ \ ⋃ p, G p '' B p) hrest),
      measure_mono_null (fun y hy => (hy.2 (iUnion_subset hsub hy.1)).elim) measure_empty⟩
  -- (3) both sides are countably additive over the pieces, and agree on each piece
  have hR : ∀ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) =
      ∑' p, ∫⁻ x in G p '' B p, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) := by
    intro s
    rw [setLIntegral_congr hA₀ae.symm, setLIntegral_congr hU, lintegral_iUnion hGBm hdisj]
  rw [setLIntegral_congr hL₀, setLIntegral_congr hÛ,
    lintegral_iUnion (fun p => hpr (hGBm p)) (fun p q hpq => (hdisj hpq).preimage pr),
    lintegral_congr hR, lintegral_tsum fun p => (hpiece p).1.aemeasurable]
  exact tsum_congr fun p => (hpiece p).2
/-- Product formula for Hausdorff measure on rectifiable sets (Federer 3.2.23), with
`π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`, so `{y : π y ∈ S} = Φ(ℝ × S)`:
(a) if `Hᵐ(N) = 0` then `Hᵐ⁺¹(ℝ × N) = 0`; (b) if `A ⊆ ℝ^P` is `Hᵐ`-measurable and countably
`m`-rectifiable, then `∫_{ℝ × A} g dHᵐ⁺¹ = ∫_ℝ ∫_A g(Φ(s, x)) dHᵐ(x) ds` for Borel `g ≥ 0`, i.e.
`Hᵐ⁺¹ ⌞ (ℝ × A) = L¹ ⊗ Hᵐ ⌞ A`.  (a) is `iwl_cr_hp_cylinder_null`.  For (b), `A` is replaced by a
Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`, which by (a) changes neither side.  Up to an `Hᵐ`-null set,
`A₀` is the disjoint union of the Borel pieces `G p '' B p` with `G p` Lipschitz and injective on
`B p` (`iwl_cr_hp_injective_pieces`); the formula holds on each piece
(`iwl_cr_hp_piece_product`), and both sides are countably additive over the pieces, the cylinder
over the remainder being `Hᵐ⁺¹`-null by (a).  The local finiteness of `Hᵐ ⌞ A` is not needed. -/
theorem Submission.dph_hausdorff_product_formula : (∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) ∧ (∀ (P m : ℕ) (A : Set (Eucl P)), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) := by
  refine ⟨Submission.iwl_cr_hp_cylinder_null, ?_⟩
  intro P m A hA hrect _hfin g hg
  -- `pr y = (y₁, …, y_P)`, so the cylinder `ℝ × S` over `S ⊆ ℝ^P` is `pr ⁻¹' S`
  set pr : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hpr : Measurable pr := by
    have : Continuous fun y : Eucl (P + 1) => Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y) :=
      continuous_pi fun i => (continuous_apply i.succ).comp
        (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous
    exact ((EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp this).measurable
  have hcyl : ∀ N : Set (Eucl P), (μHE[m] : Measure (Eucl P)) N = 0 →
      (μHE[m + 1] : Measure (Eucl (P + 1))) (pr ⁻¹' N) = 0 :=
    Submission.iwl_cr_hp_cylinder_null P m
  show ∫⁻ y in pr ⁻¹' A, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = _
  -- (1) a Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`; by (a) neither side changes
  obtain ⟨A₀, hA₀A, hA₀m, hA₀ae⟩ := hA.exists_measurable_subset_ae_eq
  have hL₀ : pr ⁻¹' A =ᵐ[(μHE[m + 1] : Measure (Eucl (P + 1)))] pr ⁻¹' A₀ :=
    ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy) (hcyl (A \ A₀) (ae_eq_set.1 hA₀ae).2),
      measure_mono_null (fun y hy => (hy.2 (hA₀A hy.1)).elim) measure_empty⟩
  -- (2) disjoint Borel pieces `G p '' B p` of `A₀`, Lipschitz and injective, up to a null set
  obtain ⟨G, B, hGL, hBm, hinj, hdiff, hsub, hGBm, hdisj, hrest⟩ :=
    Submission.iwl_cr_hp_injective_pieces P m A₀ hA₀m (hrect.mono hA₀A)
  choose K hK using hGL
  have hpiece := fun p => Submission.iwl_cr_hp_piece_product P m (G p) (K p) (B p) (hK p)
    (hBm p) (hinj p) (hdiff p) g hg
  have hU : A₀ =ᵐ[(μHE[m] : Measure (Eucl P))] ⋃ p, G p '' B p :=
    ae_eq_set.2 ⟨hrest,
      measure_mono_null (fun x hx => (hx.2 (iUnion_subset hsub hx.1)).elim) measure_empty⟩
  have hÛ : pr ⁻¹' A₀ =ᵐ[(μHE[m + 1] : Measure (Eucl (P + 1)))] ⋃ p, pr ⁻¹' (G p '' B p) := by
    rw [← preimage_iUnion]
    exact ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy) (hcyl (A₀ \ ⋃ p, G p '' B p) hrest),
      measure_mono_null (fun y hy => (hy.2 (iUnion_subset hsub hy.1)).elim) measure_empty⟩
  -- (3) both sides are countably additive over the pieces, and agree on each piece
  have hR : ∀ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) =
      ∑' p, ∫⁻ x in G p '' B p, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) := by
    intro s
    rw [setLIntegral_congr hA₀ae.symm, setLIntegral_congr hU, lintegral_iUnion hGBm hdisj]
  rw [setLIntegral_congr hL₀, setLIntegral_congr hÛ,
    lintegral_iUnion (fun p => hpr (hGBm p)) (fun p q hpq => (hdisj hpq).preimage pr),
    lintegral_congr hR, lintegral_tsum fun p => (hpiece p).1.aemeasurable]
  exact tsum_congr fun p => (hpiece p).2

/-- **The product `[[(0,1)]] × X` of an integer multiplicity current (Simon Ch. 6, 3.2(2)).**
Write `Φ(s, x) = (s, x)`, `π(Φ(s, x)) = x`, `e₀ = Φ(1, 0)` and `X = τ(M, θ, ξ)` with `θ ∈ ℕ` on
`M`, so `θ ≥ 1` on `M`.  The product formula for Hausdorff measure (Federer 3.2.23), in the
measure form `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)`, makes `((0,1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` a
rectifiable triple; `Z := τ((0,1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` is a current (integrable,
sequentially continuous), integer multiplicity since `θ ∘ π ∈ ℕ`, and Fubini gives
`Z(η) = ∫₀¹ τ(M, θ, ξ)(φ(s)) ds = ∫₀¹ X(φ(s)) ds`. -/
theorem Submission.iwl_cr_interval_product_im : ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m), IsIntegerMultiplicity X → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1), IsIntegerMultiplicity Z ∧ ∀ (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), (φ s : DifferentialForm (Eucl P) m) x v = (η : DifferentialForm (Eucl (P + 1)) (m + 1)) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s) := by
  intro P m X hX
  -- Step 1: `X = τ(M, θ, ξ)` with `θ` positive and integer-valued on `M`, hence `θ ≥ 1` on `M`.
  obtain ⟨M, θ, ξ, hT, hθN, hXτ⟩ := hX
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθN x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hpos)
  -- Step 2: the product formula in measure form, `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)` for every
  -- `Hᵐ`-measurable, countably `m`-rectifiable `A` with `Hᵐ⌞A` locally finite.
  have hMP : ∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) →
      CountablyRectifiable m A →
      (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) →
      (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} =
      Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))
        ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A)) :=
    fun A hA hAr hAK => Submission.iwl_cr_ip_restrict_preimage_eq_map P m A hAK
      (Submission.iwl_cr_hausdorff_product_formula.2 P m A hA hAr hAK)
  -- Step 3: the product triple `((0,1) × M, θ ∘ π, ξ')`, with `ξ'(Φ(s, x))(α) = ξ(x)(ℒα)` for
  -- the contraction `ℒα = α(e₀, ι ·)`.
  obtain ⟨ξ', hT', hξ'⟩ := Submission.iwl_cr_ip_product_triple P m hMP M θ ξ hT hθ1
  -- Step 4: `Z := τ((0,1) × M, θ ∘ π, ξ')` is a current.
  obtain ⟨Z, hZ⟩ := Submission.br_loc_tauAction_current (P + 1) (m + 1) univ _ _ ξ' hT'
  -- Step 5: `Z` is integer multiplicity, since `θ(π y) ∈ ℕ` for `y ∈ (0,1) × M`.
  refine ⟨Z, ⟨_, _, ξ', hT', fun y hy => hθN _ hy.1, hZ⟩, ?_⟩
  -- Step 6: the slice formula (Fubini for `H^{m+1}⌞((0,1) × M) = Φ_#(L¹⌞(0,1) ⊗ Hᵐ⌞M)`), whose
  -- integrability hypothesis holds as `η` is continuous with compact support; then use
  -- `X = τ(M, θ, ξ)`.
  intro η φ hφ
  have hint := (Submission.ltg_tau_integrable (P + 1) (m + 1) univ _ _ ξ' hT').2
    (η : DifferentialForm (Eucl (P + 1)) (m + 1)) η.property.1.1.continuous η.property.1.2
    η.property.2
  rw [hZ η, Submission.iwl_cr_ip_slice_formula P m hMP M θ ξ ξ' hT hθ1 hξ' η
    (fun s => (φ s : DifferentialForm (Eucl P) m)) hint hφ]
  exact intervalIntegral.integral_congr fun s _ => (hXτ (φ s)).symm
/-- Properness transfer (fact (P)); "proper on `F`" means `f⁻¹(K) ∩ F` is compact for every
compact `K`.  (a) If `G` is proper on the closed set `F` and the continuous map `g` is `d`-close
to `G` on `F`, then `g⁻¹(K) ∩ F` is a closed subset of the compact set
`G⁻¹(cthickening d K) ∩ F`.  (b) The affine homotopy `H(y) = F₀(x) + s • (F₁(x) − F₀(x))`,
`y = (s, x)`, of two such maps stays in the closed `d`-ball about `G(x)` by convexity, so
`H⁻¹(K) ∩ ([0,1] × F)` is a closed subset of the image of the compact set
`[0,1] × (G⁻¹(cthickening d K) ∩ F)` under the continuous chart `(s, x) ↦ y`. -/
theorem Submission.dph_lpf_proper_transfer :
    (∀ (m m' : ℕ) (G g : Eucl m → Eucl m') (F : Set (Eucl m)) (d : ℝ), IsClosed F → Continuous g → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → (∀ x ∈ F, dist (g x) (G x) ≤ d) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact (g ⁻¹' K ∩ F)) ∧ (∀ (m m' : ℕ) (G F₀ F₁ : Eucl m → Eucl m') (F : Set (Eucl m)) (d : ℝ), IsClosed F → Continuous F₀ → Continuous F₁ → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → (∀ x ∈ F, dist (F₀ x) (G x) ≤ d) → (∀ x ∈ F, dist (F₁ x) (G x) ≤ d) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ F})) := by
  refine ⟨?_, ?_⟩
  · intro m m' G g F d hF hg hG hd K hK
    refine (hG _ (hK.cthickening (r := d))).of_isClosed_subset
      ((hK.isClosed.preimage hg).inter hF) ?_
    rintro x ⟨hxK, hxF⟩
    exact ⟨mem_cthickening_of_dist_le (G x) (g x) d K hxK ((dist_comm _ _).trans_le (hd x hxF)),
      hxF⟩
  · intro m m' G F₀ F₁ F d hF hF₀ hF₁ hG hd₀ hd₁ K hK
    set e := EuclideanSpace.equiv (Fin (m + 1)) ℝ
    set e' := EuclideanSpace.equiv (Fin m) ℝ
    -- The coordinates `s = t(y)`, `x = tl(y)` and the homotopy `H` are continuous.
    have ht : Continuous fun y : Eucl (m + 1) => e y 0 := (continuous_apply 0).comp e.continuous
    have htl : Continuous fun y : Eucl (m + 1) => e'.symm (Fin.tail (e y)) :=
      e'.symm.continuous.comp (continuous_pi fun i => (continuous_apply i.succ).comp e.continuous)
    have hH : Continuous fun y : Eucl (m + 1) => F₀ (e'.symm (Fin.tail (e y))) +
        e y 0 • (F₁ (e'.symm (Fin.tail (e y))) - F₀ (e'.symm (Fin.tail (e y)))) :=
      (hF₀.comp htl).add (ht.smul ((hF₁.comp htl).sub (hF₀.comp htl)))
    -- The inverse chart `(s, x) ↦ y` is continuous.
    have hc : Continuous fun p : ℝ × Eucl m => e.symm (Fin.cons p.1 (e' p.2) : Fin (m + 1) → ℝ) :=
      e.symm.continuous.comp
        (continuous_fst.finCons (A := fun _ => ℝ) (e'.continuous.comp continuous_snd))
    -- `H⁻¹(K) ∩ cyl(F)` is closed and lies in the chart image of
    -- `[0,1] × (G⁻¹(cthickening d K) ∩ F)`, which is compact.
    refine (((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
        (hG _ (hK.cthickening (r := d)))).image hc).of_isClosed_subset
      ((hK.isClosed.preimage hH).inter ((isClosed_Icc.preimage ht).inter (hF.preimage htl))) ?_
    rintro y ⟨hyK, hyt, hyF⟩
    refine ⟨(e y 0, e'.symm (Fin.tail (e y))), ⟨hyt, ?_, hyF⟩, ?_⟩
    · -- `H(y)` lies in the closed `d`-ball about `G(x)`, so `G(x) ∈ cthickening d K`.
      have hmem := (convex_closedBall (G (e'.symm (Fin.tail (e y)))) d).add_smul_sub_mem
        (mem_closedBall.2 (hd₀ _ hyF)) (mem_closedBall.2 (hd₁ _ hyF)) hyt
      exact mem_cthickening_of_dist_le _ _ d K hyK
        ((dist_comm _ _).trans_le (mem_closedBall.1 hmem))
    · show e.symm (Fin.cons (e y 0) (e' (e'.symm (Fin.tail (e y))))) = y
      rw [e'.apply_symm_apply, Fin.cons_self_tail, e.symm_apply_apply]

/-- **Reference smooth approximations near a closed set** (Simon Ch. 6, 2.28–2.29; Step 2 of the
Lipschitz push-forward).  Assume the smooth approximation statement (SA) of
`dph_lipschitz_smooth_approx`.  If `F` is closed, `G` is `Λ`-Lipschitz on `F_r` (`r > 0`) and
proper on `F`, (SA) with `A := F`, `δ := r` gives `C^∞` maps `Gₙ` with `‖DGₙ‖ ≤ Λ` on `F_(r/2)`
and `Gₙ → Ĝ` uniformly, where `Ĝ = G` on `F_r ⊇ F_(r/2)`.  So `Gₙ → G` uniformly on `F_(r/2)`,
eventually `dist (Gₙ x) (G x) ≤ 1` on `F`, and `dph_lpf_proper_transfer` (a) makes `Gₙ` proper
on `F`. -/
theorem Submission.dph_lpf_reference_sequence : (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ → LipschitzOnWith Λ G (thickening δ A) → ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧ (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧ TendstoUniformly Gj G' atTop ∧ (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧ ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m') (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε → (∀ x ∈ thickening ε A, G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) → ∀ i, i ∉ range α → G x i = z i) → (∀ y, (ω : DifferentialForm (Eucl m') k) y (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) → ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A, ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap (fderiv ℝ (Gj j) x) = 0) → (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) := by
  intro hSA m m' G Λ r F hr hF hG hprop
  -- 1. (SA) with `A := F`, `δ := r`.
  obtain ⟨G', Gj, L, -, hG'G, hsmooth, -, hconv, hderiv, -⟩ := hSA m m' G Λ F r hr hG
  -- 2. `F_(r/2) ⊆ F_r`, where `G' = G`, so `Gj → G` uniformly on `F_(r/2)`.
  have hsub : thickening (r / 2) F ⊆ thickening r F := thickening_mono (half_le_self hr.le) F
  have hconvG : TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) :=
    hconv.tendstoUniformlyOn.congr_right (hG'G.mono hsub)
  refine ⟨Gj, hsmooth, hderiv, hconvG, ?_⟩
  -- 3. Eventually `dist (G x) (Gj n x) < 1` on `F_(r/2) ⊇ F`.
  have hFsub : F ⊆ thickening (r / 2) F := self_subset_thickening (half_pos hr) F
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconvG 1 one_pos] with n hn
  -- 4. `Gj n` is continuous and `1`-close to `G` on `F`, hence proper on `F`.
  exact Submission.dph_lpf_proper_transfer.1 m m' G (Gj n) F 1 hF (hsmooth n).continuous hprop
    fun x hx => by
      rw [dist_comm]
      exact (hn x (hFsub hx)).le
/-- **The affine homotopy restricts to its ends and is smooth** (Simon Ch. 6, (2.26), p. 140:
`h(t, x) = f(x) + t (g(x) − f(x))`).  On `ℝ^{m+1}` write `t(y) = y₀` and `tl(y) = (y₁, …, y_m)`;
`G = F₀ ∘ tl + t • (F₁ ∘ tl − F₀ ∘ tl)`.  For `y = cons(s, x)`, `t(y) = s` and `tl(y) = x` hold
definitionally, so `G(cons(0, x)) = F₀(x)` and `G(cons(1, x)) = F₁(x)`.  The maps `t` and `tl` are
coordinate projections composed with continuous linear equivalences, hence `C^∞`, so `G` is `C^∞`
when `F₀` and `F₁` are. -/
theorem Submission.dph_lpf_cmp_affine_homotopy : ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m') (G : Eucl (m + 1) → Eucl m'), G = (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) → (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) = F₀ ∧ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) = F₁ ∧ (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) := by
  intro m m' F₀ F₁ G hG
  subst hG
  refine ⟨funext fun x => ?_, funext fun x => ?_, fun h₀ h₁ => ?_⟩
  -- `t(cons(0, x)) = 0` and `tl(cons(0, x)) = x` definitionally (`simp` does not see through
  -- `EuclideanSpace.equiv`, so restate the goal by `change`).
  · change F₀ x + (0 : ℝ) • (F₁ x - F₀ x) = F₀ x
    rw [zero_smul, add_zero]
  -- Likewise `t(cons(1, x)) = 1` and `tl(cons(1, x)) = x`.
  · change F₀ x + (1 : ℝ) • (F₁ x - F₀ x) = F₁ x
    rw [one_smul, add_sub_cancel]
  -- `Fin.tail` is `C^∞`: each of its coordinates `q ↦ q i.succ` is.
  · have htail : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) :=
      contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ
    -- `tl` is `C^∞`: compose with the continuous linear equivalences.
    have htl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Eucl (m + 1) =>
        (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) :=
      (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.comp
        (htail.comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).contDiff)
    -- `t` is `C^∞`: the coordinate `q ↦ q 0` composed with a continuous linear equivalence.
    have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Eucl (m + 1) =>
        EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 :=
      (contDiff_apply ℝ ℝ (0 : Fin (m + 1))).comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).contDiff
    exact (h₀.comp htl).add (ht.smul ((h₁.comp htl).sub (h₀.comp htl)))
/-- The straight-line homotopy `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`, `t(y) = y₀`,
`tl(y) = (y₁, …, yₘ)`, is built from the continuous linear maps `t`, `tl` and the smooth `F₀`, `F₁`,
hence smooth.  By the chain and product rules
`DG(y)(w) = DF₀(tl y)(tl w) + t(y) • (DF₁(tl y)(tl w) - DF₀(tl y)(tl w)) + t(w) • (F₁ - F₀)(tl y)`,
so at `y = (s, x)` the derivative maps `e₀ ↦ F₁(x) - F₀(x)` and `ι(v) = (0, v) ↦
DF₀(x)(v) + s • (DF₁(x)(v) - DF₀(x)(v)) = (1 - s) • DF₀(x)(v) + s • DF₁(x)(v)`. -/
theorem Submission.dph_sh_ae_affine_homotopy_contDiff_fderiv :
    ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m'), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ∧ ∀ (s : ℝ) (x : Eucl m), fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (EuclideanSpace.single 0 1) = F₁ x - F₀ x ∧ ∀ v : Eucl m, fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v))) = (1 - s) • fderiv ℝ F₀ x v + s • fderiv ℝ F₁ x v := by
  intro m m' F₀ F₁ hF₀ hF₁
  -- `t(y) = y₀` and `tl(y) = (y₁, …, yₘ)` are continuous linear maps, and
  -- `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`.
  let tL : Eucl (m + 1) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj 0 ∘L (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  let tlL : Eucl (m + 1) →L[ℝ] Eucl m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j : Fin m => ContinuousLinearMap.proj j.succ) ∘L
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  have hG : (fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) =
      fun y => F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)) := rfl
  -- Values: `t(cons(τ, z)) = τ`, `tl(cons(τ, z)) = z`, `t(e₀) = 1` and `tl(e₀) = 0`.
  have htL : ∀ (τ : ℝ) (z : Eucl m), tL ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons τ (EuclideanSpace.equiv (Fin m) ℝ z))) = τ := fun τ z => rfl
  have htlL : ∀ (τ : ℝ) (z : Eucl m), tlL ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons τ (EuclideanSpace.equiv (Fin m) ℝ z))) = z := fun τ z => rfl
  have htL₀ : tL (EuclideanSpace.single 0 1) = 1 := by simp [tL]
  have htlL₀ : tlL (EuclideanSpace.single 0 1) = 0 := by
    ext j
    simp [tlL, Fin.succ_ne_zero]
  clear_value tL tlL
  -- Chain and product rules: `DG(y) = DF₀(tl y) ∘ tl + t(y) • (DF₁(tl y) ∘ tl - DF₀(tl y) ∘ tl)
  -- + t.smulRight ((F₁ - F₀)(tl y))`.
  have hD : ∀ y : Eucl (m + 1), HasFDerivAt (fun y => F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)))
      ((fderiv ℝ F₀ (tlL y)).comp tlL + (tL y • ((fderiv ℝ F₁ (tlL y)).comp tlL -
        (fderiv ℝ F₀ (tlL y)).comp tlL) + tL.smulRight (F₁ (tlL y) - F₀ (tlL y)))) y := by
    intro y
    have h₀ : HasFDerivAt (fun y => F₀ (tlL y)) ((fderiv ℝ F₀ (tlL y)).comp tlL) y :=
      ((hF₀.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y tlL.hasFDerivAt
    have h₁ : HasFDerivAt (fun y => F₁ (tlL y)) ((fderiv ℝ F₁ (tlL y)).comp tlL) y :=
      ((hF₁.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y tlL.hasFDerivAt
    exact h₀.add (tL.hasFDerivAt.smul (h₁.sub h₀))
  refine ⟨?_, fun s x => ⟨?_, fun v => ?_⟩⟩
  · rw [hG]
    exact (hF₀.comp tlL.contDiff).add
      (tL.contDiff.smul ((hF₁.comp tlL.contDiff).sub (hF₀.comp tlL.contDiff)))
  · -- `DG(cons(s, x)) e₀ = DF₀(x) 0 + s • (DF₁(x) 0 - DF₀(x) 0) + 1 • (F₁(x) - F₀(x))`.
    rw [hG, (hD _).fderiv, htlL, htL, add_apply, add_apply, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, htL₀, htlL₀, map_zero, map_zero, sub_zero, smul_zero,
      one_smul, zero_add, zero_add]
  · -- `DG(cons(s, x)) (ι v) = DF₀(x) v + s • (DF₁(x) v - DF₀(x) v) + 0 • (F₁(x) - F₀(x))`.
    rw [hG, (hD _).fderiv, htlL, htL, add_apply, add_apply, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, htlL, htL, zero_smul, add_zero, smul_sub, sub_smul,
      one_smul]
    abel
/-- The straight-line homotopy `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`, `t(y) = y₀`,
`tl(y) = (y₁, …, yₘ)`, is proper on the cylinder `cyl(S) = {t ∈ [0,1], tl ∈ S}`.  `G` is continuous
and `cyl(S)` is closed, so `G⁻¹(K) ∩ cyl(S)` is closed.  For `y` in it,
`dist(F₀(tl y), G y) = t(y) · dist(F₁(tl y), F₀(tl y)) ≤ s`, so `F₀(tl y) ∈ cthickening s K` and
`y = (t y, tl y)` lies in the compact image of `[0,1] × (F₀⁻¹(cthickening s K) ∩ S)`. -/
theorem Submission.dph_sh_ae_affine_homotopy_isCompact_preimage_cyl :
    ∀ (m m' : ℕ) (F₀ F₁ : Eucl m → Eucl m') (S : Set (Eucl m)) (s : ℝ), Continuous F₀ → Continuous F₁ → IsClosed S → (∀ x ∈ S, dist (F₁ x) (F₀ x) ≤ s) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ S)) → ∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ S}) := by
  intro m m' F₀ F₁ S s hF₀ hF₁ hS hs hprop K hK
  -- `t(y) = y₀` and `tl(y) = (y₁, …, yₘ)` are continuous linear maps.
  let tL : Eucl (m + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  let tlL : Eucl (m + 1) →L[ℝ] Eucl m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j : Fin m => ContinuousLinearMap.proj j.succ) ∘L
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toContinuousLinearMap
  -- `Φ(τ, x) = (τ, x)` is continuous, so `Q = Φ([0,1] × (F₀⁻¹(cthickening s K) ∩ S))` is compact.
  let Φ : ℝ × Eucl m → Eucl (m + 1) := fun p =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin m) ℝ p.2))
  have hΦ : Continuous Φ :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin m) ℝ).continuous.comp continuous_snd))
  have hQ : IsCompact (Φ '' (Icc (0 : ℝ) 1 ×ˢ (F₀ ⁻¹' cthickening s K ∩ S))) :=
    (isCompact_Icc.prod (hprop _ (hK.cthickening (r := s)))).image hΦ
  refine hQ.of_isClosed_subset ?_ ?_
  · -- `G` is continuous and `cyl(S) = t⁻¹[0,1] ∩ tl⁻¹(S)` is closed.
    have hG : Continuous fun y => F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)) :=
      (hF₀.comp tlL.continuous).add (tL.continuous.smul
        ((hF₁.comp tlL.continuous).sub (hF₀.comp tlL.continuous)))
    exact (hK.isClosed.preimage hG).inter
      ((isClosed_Icc.preimage tL.continuous).inter (hS.preimage tlL.continuous))
  · rintro y ⟨hyK, hy01, hyS⟩
    have hGy : F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y)) ∈ K := hyK
    have hτ : tL y ∈ Icc (0 : ℝ) 1 := hy01
    have hx : tlL y ∈ S := hyS
    -- `dist(F₀(tl y), G y) = t(y) · dist(F₁(tl y), F₀(tl y)) ≤ s`.
    have hdist : dist (F₀ (tlL y)) (F₀ (tlL y) + tL y • (F₁ (tlL y) - F₀ (tlL y))) ≤ s := by
      rw [dist_self_add_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1, ← dist_eq_norm]
      exact (mul_le_of_le_one_left dist_nonneg hτ.2).trans (hs _ hx)
    -- `Φ(t y, tl y) = y`.
    have hΦy : Φ (tL y, tlL y) = y := by
      change (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin m) ℝ ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) = y
      rw [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_self_tail,
        ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨(tL y, tlL y), ⟨hτ, mem_cthickening_of_dist_le _ _ s K hGy hdist, hx⟩, hΦy⟩
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
/-- Simon Ch. 6, 2.23 (p. 139), cut-off construction: if `f` is `C^∞` and proper on `A ⊆ U`, every
`ω ∈ 𝒟ʲ(V)` has a pull-back `η = ζ f^#ω ∈ 𝒟ʲ(U)` with `0 ≤ ζ ≤ 1`, `η = f^#ω` on an open
`N ⊇ A`, and `spt η ⊆ f⁻¹(spt ω)`. -/
theorem Submission.iwl_sp_exists_compatible_testForm :
    ∀ (P Q j : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (A : Set (Eucl P)) (f : Eucl P → Eucl Q),
      IsOpen U → A ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ A)) →
      ∀ ω : TestFormOn V j, ∃ (η : TestFormOn U j) (ζ : Eucl P → ℝ) (N : Set (Eucl P)),
        IsOpen N ∧ A ⊆ N ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
        (∀ x, (η : DifferentialForm (Eucl P) j) x =
          ζ x • ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap
            (fderiv ℝ f x)) ∧
        (∀ x ∈ N, (η : DifferentialForm (Eucl P) j) x =
          ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∧
        tsupport (η : DifferentialForm (Eucl P) j) ⊆
          f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) := by
  intro P Q j U V A f hU hAU hf hprop ω
  obtain ⟨⟨hωs, hωc⟩, hωV⟩ := ω.property
  have hωs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl Q) j) := hωs
  -- 1. `K = f⁻¹(spt ω) ∩ A` is compact, by properness.
  have hK : IsCompact (f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) ∩ A) :=
    hprop _ hωc.isCompact hωV
  set K := f ⁻¹' tsupport (ω : DifferentialForm (Eucl Q) j) ∩ A
  -- 2. A closed `δ`-thickening of `K` lies in `U`.
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU fun x hx => hAU hx.2
  -- 3. Smooth Urysohn: `support ζ = thickening δ K`, and `ζ = 1` exactly on `cthickening (δ/2) K`.
  obtain ⟨ζ, hζs, hζr, hζsupp, hζone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  have hζt : tsupport ζ ⊆ cthickening δ K := by
    rw [tsupport, hζsupp]
    exact closure_thickening_subset_cthickening δ K
  -- 4. The pull-back `p = f^# ω` is smooth, since `B ↦ B^#` is analytic.
  set p : DifferentialForm (Eucl P) j := fun x =>
    ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p := by
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin j) (F := ℝ)
          (fderiv ℝ f x)) :=
      (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff.comp hD
    exact hC.clm_apply (hωs'.comp hf)
  -- `p` vanishes wherever `ω ∘ f` does.
  have hp0 : ∀ x, f x ∉ tsupport (ω : DifferentialForm (Eucl Q) j) → p x = 0 := by
    intro x hx
    show ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x) = 0
    rw [image_eq_zero_of_notMem_tsupport hx,
      ← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, map_zero]
  -- 5. The test form `η = ζ p`.
  have hηs : IsSmoothForm (fun x => ζ x • p x) := hζs.smul hp
  have hηt : tsupport (fun x => ζ x • p x) ⊆ U :=
    (tsupport_smul_subset_left ζ p).trans (hζt.trans hδU)
  have hηc : HasCompactSupport (fun x => ζ x • p x) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_smul_subset_left ζ p).trans hζt)
  let η : TestFormOn U j := ⟨fun x => ζ x • p x, ⟨hηs, hηc⟩, hηt⟩
  refine ⟨η, ζ, thickening (δ / 2) K ∪ f ⁻¹' (tsupport (ω : DifferentialForm (Eucl Q) j))ᶜ,
    isOpen_thickening.union ((isClosed_tsupport _).isOpen_compl.preimage hf.continuous), ?_,
    fun x => hζr (mem_range_self x), fun x => rfl, ?_, ?_⟩
  · -- 7. `A ⊆ N`.
    intro x hx
    by_cases hfx : f x ∈ tsupport (ω : DifferentialForm (Eucl Q) j)
    · exact Or.inl (self_subset_thickening (half_pos hδ) K ⟨hfx, hx⟩)
    · exact Or.inr hfx
  · -- 8. `η = p` on `N`.
    rintro x (hx | hx)
    · have h1 : ζ x = 1 := (hζone x).1 (thickening_subset_cthickening _ _ hx)
      show ζ x • p x = p x
      rw [h1, one_smul]
    · show ζ x • p x = p x
      rw [hp0 x hx, smul_zero]
  · -- 6. `spt η ⊆ f⁻¹(spt ω)`, a closed set.
    refine closure_minimal ?_ ((isClosed_tsupport _).preimage hf.continuous)
    intro x hx
    by_contra hfx
    exact hx (show ζ x • p x = 0 by rw [hp0 x hfx, smul_zero])
/-- A current kills every test form whose support misses `spt T`: `tsupport ω` is a compact subset
of the zero region, so finitely many open `W ⊂⊂ U` on which `T` vanishes cover it, and a smooth
partition of unity `ψᵢ` on `tsupport ω` subordinate to them splits `ω = ∑ᵢ ψᵢ ω` into test forms
supported in those `W`. -/
theorem Submission.isoperimetric_apply_eq_zero_of_disjoint_support :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n),
      Disjoint (tsupport (ω : DifferentialForm (Eucl P) n)) T.support → T ω = 0 := by
  intro P n U T ω hdisj
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) n)) := ω.property.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) n) ⊆ U := ω.property.2
  -- `tsupport ω` lies in the zero region: the union of the open `W ⊂⊂ U` on which `T` vanishes.
  have hKZ : tsupport (ω : DifferentialForm (Eucl P) n) ⊆
      ⋃ W : {W : Set (Eucl P) // IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧
        T.VanishesOn W}, (W : Set (Eucl P)) := by
    intro x hx
    have hxZ : x ∈ T.zeroRegion := by
      by_contra h
      exact Set.disjoint_left.1 hdisj hx ⟨hKU hx, h⟩
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 hxZ
    exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hxW⟩
  -- A finite subcover, indexed by the finset `t`.
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover _ (fun W => W.2.1) hKZ
  have hcov : tsupport (ω : DifferentialForm (Eucl P) n) ⊆
      ⋃ i : t, ((i : {W : Set (Eucl P) // IsOpen W ∧ IsCompact (closure W) ∧
        closure W ⊆ U ∧ T.VanishesOn W}) : Set (Eucl P)) := by
    intro x hx
    obtain ⟨W, hWt, hxW⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Set.mem_iUnion.2 ⟨⟨W, hWt⟩, hxW⟩
  -- A smooth partition of unity `f i` on `tsupport ω` with `tsupport (f i) ⊆ W i`.
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Eucl P)) hKc.isClosed _ (fun i => i.1.2.1) hcov
  -- `η i = f i • ω` is a test form in `U` supported in `W i`, hence `T (η i) = 0`.
  have hfs : ∀ i, ContDiff ℝ _ (f i : Eucl P → ℝ) :=
    fun i => contMDiff_iff_contDiff.1 (f i).contMDiff
  have hsm : ∀ i, ContDiff ℝ _ (fun x => f i x • (ω : DifferentialForm (Eucl P) n) x) :=
    fun i => (hfs i).smul ω.property.1.1
  have hcs : ∀ i, HasCompactSupport (fun x => f i x • (ω : DifferentialForm (Eucl P) n) x) :=
    fun i => hKc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_smul_subset_right (fun x => f i x) _)
  have hsU : ∀ i, tsupport (fun x => f i x • (ω : DifferentialForm (Eucl P) n) x) ⊆ U :=
    fun i => (tsupport_smul_subset_right (fun x => f i x) _).trans hKU
  let η : t → TestFormOn U n := fun i =>
    ⟨fun x => f i x • (ω : DifferentialForm (Eucl P) n) x, ⟨⟨hsm i, hcs i⟩, hsU i⟩⟩
  have hη : ∀ i, T (η i) = 0 := fun i =>
    i.1.2.2.2.2 (η i) ((tsupport_smul_subset_left (fun x => f i x) _).trans (hf i))
  -- `ω = ∑ i, η i`: `∑ i, f i = 1` on `tsupport ω`, and `ω = 0` off it.
  have hsum : ω = ∑ i, η i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Eucl P) n) x =
      ∑ i, f i x • (ω : DifferentialForm (Eucl P) n) x
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ tsupport (ω : DifferentialForm (Eucl P) n)
    · rw [← finsum_eq_sum_of_fintype, f.sum_eq_one hx, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  change T.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => hη i

/-- Supports of boundaries, weak limits and linear combinations: `spt ∂Z ⊆ spt Z`; a weak limit of
currents supported in a closed `K` is supported in `K`; `spt Z ⊆ spt Z₁ ∪ spt Z₂` when
`Z = a Z₁ + b Z₂`.  In each case a point outside the claimed support lies in an open `W ⊂⊂ U` on
which the current vanishes, i.e. in its zero region. -/
theorem Submission.iwl_cr_support_lemmas :
    (∀ (P m : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (m + 1)),
      Z.boundary.support ⊆ Z.support) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P))
      (Zj : ℕ → GeometricCurrentOn U n) (Z : GeometricCurrentOn U n), IsClosed K →
      (∀ j, (Zj j).support ⊆ K) → WeaklyConvergesOn Zj Z → Z.support ⊆ K) ∧
    (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Z₁ Z₂ Z : GeometricCurrentOn U n) (a b : ℝ),
      (∀ ω : TestFormOn U n, Z ω = a * Z₁ ω + b * Z₂ ω) →
      Z.support ⊆ Z₁.support ∪ Z₂.support) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) If `Z` vanishes on an admissible `W`, so does `∂Z`: `∂Z φ = Z (dφ)` and
    -- `tsupport dφ ⊆ tsupport φ ⊆ W`.
    intro P m U Z x hx
    refine ⟨hx.1, fun hxZ => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
    refine Set.mem_sUnion.2 ⟨W, ⟨hWo, hWc, hWU, fun φ hφ => ?_⟩, hxW⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset _).trans hφ)
  · -- (2) For `x ∈ spt Z \ K`, the ball `W = B(x, ε/2)` has `closure W ⊆ U \ K`.  A test form
    -- supported in `W` misses `K ⊇ spt (Zj j)`, so every `Zj j` kills it, and so does the limit.
    intro P n U hU K Zj Z hK hZj hconv x hx
    by_contra hxK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.sdiff hK) x ⟨hx.1, hxK⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ U \ K := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans sdiff_subset, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have h0 : ∀ j, Zj j ω = 0 := fun j =>
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U (Zj j) ω
          (Set.disjoint_left.2 fun y hy hyS => (hcl (subset_closure (hω hy))).2 (hZj j hyS))
      have hlim := hconv ω
      simp only [h0] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- (3) For `x ∈ spt Z` outside `spt Z₁ ∪ spt Z₂`, the ball `W = B(x, ε/2)` has `closure W`
    -- inside both zero regions and `U`, so `Z₁`, `Z₂` and hence `Z = a Z₁ + b Z₂` vanish on `W`.
    intro P n U hU Z₁ Z₂ Z a b hZ x hx
    by_contra hx12
    have h1 : x ∈ Z₁.zeroRegion := by
      by_contra h
      exact hx12 (Or.inl ⟨hx.1, h⟩)
    have h2 : x ∈ Z₂.zeroRegion := by
      by_contra h
      exact hx12 (Or.inr ⟨hx.1, h⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((Z₁.isOpen_zeroRegion.inter Z₂.isOpen_zeroRegion).inter hU) x ⟨⟨h1, h2⟩, hx.1⟩
    have hr : 0 < ε / 2 := half_pos hε
    have hcl : closure (ball x (ε / 2)) ⊆ Z₁.zeroRegion ∩ Z₂.zeroRegion ∩ U := by
      rw [closure_ball x hr.ne']
      exact (closedBall_subset_ball (half_lt_self hε)).trans hball
    refine hx.2 (Set.mem_sUnion.2 ⟨ball x (ε / 2), ⟨isOpen_ball, ?_,
      hcl.trans inter_subset_right, fun ω hω => ?_⟩, mem_ball_self hr⟩)
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · have e1 : Z₁ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₁ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.1)
      have e2 : Z₂ ω = 0 :=
        Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U Z₂ ω
          (Set.disjoint_left.2 fun y hy hyS => hyS.2 (hcl (subset_closure (hω hy))).1.2)
      rw [hZ ω, e1, e2]
      ring
/-- **Test forms have bounded Euclidean coefficient norm** (the finiteness of `sup_x |ω(x)|` behind
"Evidently (1), (2) give `P_k(ω) → T(ω)`" in the proof of Simon Ch. 6, 6.2, p. 169).
`x ↦ |ω(x)|` is continuous, since `α ↦ |α|` is the square root of a finite sum of squares of
evaluations, and has compact support, since `|0| = 0`.  A continuous compactly supported real
function is bounded by some `C₀ ≥ 0`, and `C = C₀ + 1` is positive. -/
theorem Submission.br_la_testForm_covectorNorm_bounded : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U n), ∃ C : ℝ, 0 < C ∧ ∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C := by
  intro P n U ω
  -- `ω` is smooth, hence continuous.
  have hω : Continuous (ω : DifferentialForm (Eucl P) n) := ω.property.1.1.continuous
  -- `x ↦ |ω(x)|` is continuous: a square root of a finite sum of squares of evaluations.
  have hcont : Continuous fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (hω.eval_const _).pow 2
    · exact continuous_const
  -- `|ω(x)| = 0` wherever `ω(x) = 0`, so `x ↦ |ω(x)|` inherits the compact support of `ω`.
  have hsupp : HasCompactSupport fun x =>
      covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) := by
    refine ω.property.1.2.mono' fun x hx => subset_tsupport _ fun h => hx ?_
    simp [h]
  -- A continuous compactly supported function is bounded by some `C₀ ≥ |f(0)| ≥ 0`.
  obtain ⟨C₀, hC₀⟩ := hcont.bounded_above_of_compact_support hsupp
  refine ⟨C₀ + 1, by linarith [(norm_nonneg _).trans (hC₀ 0)], fun x => ?_⟩
  linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x)),
    (Real.norm_eq_abs _).symm.trans_le (hC₀ x)]
/-- **Core estimate of the comparison lemma** (Simon Ch. 6, proof of 2.29, p. 141: the homotopy
formula 2.25 for the affine homotopy 2.26 and the mass bound 2.27 give
`|f_ε# T(ω) − f_δ# T(ω)| ≤ C sup |f_ε − f_δ| (Lip f)ⁿ`).  Assume the interval product (Prod) and
the homotopy formulas (E0), (E1) with the affine estimate (Aff).  For `X` with `M(X) < ∞` (and
`M(∂X) < ∞` if `k ≥ 1`), `ω` and `L ≥ 0`, everything entering `C₀` is chosen before the maps: `Z`
with `ProdChar(X, Z)`, the constant `c` of (Aff), `C₁ ≥ |dω|` and `B = M(X)`; for `k = j + 1` also
`Z′` with `ProdChar(∂X, Z′)`, `c′`, `C₂ ≥ |ω|` and `B′ = M(∂X)`.  For the affine homotopy
`H = H[F₀, F₁]`, the pull-backs `η′ = H^# dω`, `θ′ = H^# ω` near `[0, 1] × spt X` turn the homotopy
formula into `X(η₁) − X(η₀) = Z(η′) (+ Z′(θ′))`, and (Aff) bounds each term by
`c s L^k M(·) sup |·|`. -/
theorem Submission.dph_lpf_cmp_core_estimate : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (L : ℝ), 0 ≤ L → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s : ℝ) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → 0 ≤ s → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (F₀ x)).compContinuousLinearMap (fderiv ℝ F₀ x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (F₁ x)).compContinuousLinearMap (fderiv ℝ F₁ x)) → |X η₁ - X η₀| ≤ C₀ * s := by
  intro hProd hSH m m' k X hXm hbd ω L hL
  obtain ⟨hE0, hE1, hAff⟩ := hSH
  -- 1. Data that do not depend on the maps: `Z` with `ProdChar(X, Z)`, the constant `c` of (Aff),
  -- a bound `C₁` for `|dω|` and `B = M(X)`.
  obtain ⟨Z, hZ⟩ := hProd m k X hXm
  obtain ⟨c, hc0, hc⟩ := hAff m m' k
  obtain ⟨C₁, hC₁0, hC₁⟩ := Submission.br_la_testForm_covectorNorm_bounded m' (k + 1) univ
    (exteriorDerivativeTestOn univ k ω)
  obtain ⟨B, hB0, hXB⟩ : ∃ B : ℝ, 0 ≤ B ∧ X.mass ≤ ENNReal.ofReal B :=
    ⟨X.mass.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hXm.ne).ge⟩
  cases k with
  | zero =>
    -- 2. `k = 0`: `C₀ = c B C₁`.
    refine ⟨c * B * C₁, mul_nonneg (mul_nonneg hc0 hB0) hC₁0.le, ?_⟩
    intro F₀ F₁ O s η₀ η₁ hF₀ hF₁ hO hXO hs hdist hD₀ hD₁ hF₀p hHp hη₀ hη₁
    -- (i) The affine homotopy `H = H[F₀, F₁]` has ends `F₀`, `F₁` and is `C^∞`.
    set H : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))) with hH
    obtain ⟨hH₀, hH₁, hHs⟩ := Submission.dph_lpf_cmp_affine_homotopy m m' F₀ F₁ H hH
    have hHsm := hHs hF₀ hF₁
    -- (ii) `η′ = H^# dω` near `[0, 1] × spt X`, as `H` is proper there.
    obtain ⟨η', -, N, hN, hXN, -, -, hη', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (0 + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) (exteriorDerivativeTestOn univ 0 ω)
    -- (iii) The homotopy formula (E0), its end conditions rewritten by (i):
    -- `X(η₁) − X(η₀) = Z(η′)`.
    rw [hE0 m m' X Z H hXm hZ hHsm hHp ω η₀ η₁ η' (by rw [hH₀]; exact hη₀)
      (by rw [hH₁]; exact hη₁) ⟨N, hN, hXN, hη'⟩]
    -- (iv)–(v) The affine estimate (Aff) with `ψ = dω`: `|Z(η′)| ≤ c s L⁰ B C₁ = C₀ s`.
    calc |Z η'| ≤ c * s * L ^ 0 * B * C₁ :=
          hc X Z F₀ F₁ O s L B hs hL hB0 hXB hZ hF₀ hF₁ hO hXO hdist hD₀ hD₁ hF₀p
            (exteriorDerivativeTestOn univ 0 ω) C₁ η' hC₁ ⟨N, hN, hXN, hη'⟩
      _ = c * B * C₁ * s := by ring
  | succ j =>
    -- 3. `k = j + 1`, further data that do not depend on the maps: `B′ = M(∂X) < ∞`, `Z′` with
    -- `ProdChar(∂X, Z′)`, the constant `c′` of (Aff) in degree `j`, a bound `C₂` for `|ω|`, and
    -- `spt ∂X ⊆ spt X` with `spt ∂X` closed.
    have hbm : X.boundary.mass < ∞ := hbd j X rfl HEq.rfl
    obtain ⟨B', hB'0, hXB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧ X.boundary.mass ≤ ENNReal.ofReal B' :=
      ⟨X.boundary.mass.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hbm.ne).ge⟩
    obtain ⟨Z', hZ'⟩ := hProd m j X.boundary hbm
    obtain ⟨c', hc'0, hc'⟩ := hAff m m' j
    obtain ⟨C₂, hC₂0, hC₂⟩ := Submission.br_la_testForm_covectorNorm_bounded m' (j + 1) univ ω
    have hsub : X.boundary.support ⊆ X.support := Submission.iwl_cr_support_lemmas.1 m j univ X
    have hcl : IsClosed X.boundary.support := isClosed_univ.sdiff X.boundary.isOpen_zeroRegion
    refine ⟨c * L ^ (j + 1) * B * C₁ + c' * L ^ j * B' * C₂,
      add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (pow_nonneg hL _)) hB0) hC₁0.le)
        (mul_nonneg (mul_nonneg (mul_nonneg hc'0 (pow_nonneg hL _)) hB'0) hC₂0.le), ?_⟩
    intro F₀ F₁ O s η₀ η₁ hF₀ hF₁ hO hXO hs hdist hD₀ hD₁ hF₀p hHp hη₀ hη₁
    -- 4. The affine homotopy `H = H[F₀, F₁]`, as in 2(i).
    set H : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
      F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
          (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
            F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))) with hH
    obtain ⟨hH₀, hH₁, hHs⟩ := Submission.dph_lpf_cmp_affine_homotopy m m' F₀ F₁ H hH
    have hHsm := hHs hF₀ hF₁
    -- (i) `η′ = H^# dω` and `θ′ = H^# ω` near `[0, 1] × spt X`.
    obtain ⟨η', -, N, hN, hXN, -, -, hη', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (j + 1 + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) (exteriorDerivativeTestOn univ (j + 1) ω)
    obtain ⟨θ', -, N', hN', hXN', -, -, hθ', -⟩ := Submission.iwl_sp_exists_compatible_testForm
      (m + 1) m' (j + 1) univ univ _ H isOpen_univ (subset_univ _) hHsm
      (fun K hK _ => hHp K hK) ω
    -- (ii) The homotopy formula (E1): `X(η₁) − X(η₀) = Z(η′) + Z′(θ′)`.
    rw [hE1 m m' j X Z Z' H hXm hZ hZ' hHsm hHp ω η₀ η₁ η' θ' (by rw [hH₀]; exact hη₀)
      (by rw [hH₁]; exact hη₁) ⟨N, hN, hXN, hη'⟩ ⟨N', hN', hXN', hθ'⟩]
    -- (iii) (Aff) for `X` with `ψ = dω`: `|Z(η′)| ≤ c s L^(j+1) B C₁`.
    have hest : |Z η'| ≤ c * s * L ^ (j + 1) * B * C₁ :=
      hc X Z F₀ F₁ O s L B hs hL hB0 hXB hZ hF₀ hF₁ hO hXO hdist hD₀ hD₁ hF₀p
        (exteriorDerivativeTestOn univ (j + 1) ω) C₁ η' hC₁ ⟨N, hN, hXN, hη'⟩
    -- (iv) `F₀` is proper on the closed subset `spt ∂X` of `spt X`.
    have hF₀p' : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.boundary.support) := by
      intro K hK
      have h := (hF₀p K hK).inter_right hcl
      rwa [inter_assoc, inter_eq_right.mpr hsub] at h
    -- (v) (Aff) for `∂X` with `ψ = ω`, as `[0, 1] × spt ∂X ⊆ [0, 1] × spt X ⊆ N′`:
    -- `|Z′(θ′)| ≤ c′ s L^j B′ C₂`.
    have hest' : |Z' θ'| ≤ c' * s * L ^ j * B' * C₂ :=
      hc' X.boundary Z' F₀ F₁ O s L B' hs hL hB'0 hXB' hZ' hF₀ hF₁ hO (hsub.trans hXO) hdist hD₀
        hD₁ hF₀p' ω C₂ θ' hC₂ ⟨N', hN', fun y hy => hXN' ⟨hy.1, hsub hy.2⟩, hθ'⟩
    -- (vi) Sum the two estimates.
    calc |Z η' + Z' θ'| ≤ |Z η'| + |Z' θ'| := abs_add_le _ _
      _ ≤ c * s * L ^ (j + 1) * B * C₁ + c' * s * L ^ j * B' * C₂ := add_le_add hest hest'
      _ = (c * L ^ (j + 1) * B * C₁ + c' * L ^ j * B' * C₂) * s := by ring
/-- Comparison lemma (Step 1 of the Lipschitz push-forward): if `C^∞` maps `Gₙ`, `G'ₙ` with
eventual derivative bounds `L`, `L'` near `spt X` both converge uniformly to a map `G` proper on
`spt X`, then pull-backs `ηₙ`, `η'ₙ` of `ω` compatible with `Gₙ`, `G'ₙ` near `spt X` satisfy
`X(η'ₙ) − X(ηₙ) → 0`.  For `ε > 0`, eventually `Gₙ` and `G'ₙ` are `ε`-close to `G` on
`O ∩ O' ⊇ spt X`; so `Gₙ` is proper on `spt X` and the affine homotopy between `Gₙ` and `G'ₙ` is
proper on `[0,1] × spt X` (properness transfer), `dist(G'ₙ, Gₙ) ≤ 2ε` on `O ∩ O'`, and the core
estimate gives `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε`, which is `< δ` for `ε = δ/(2C₀ + 1)`. -/
theorem Submission.dph_lpf_comparison : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) := by
  intro hProd hSH m m' k X G hXm hbd hG Gj Gj' O O' L L' hO hXO hGj hGjL hGjU hO' hXO' hGj'
    hGjL' hGjU' ω ηj ηj' hηj hηj'
  -- Step 1 (core estimate), with the common derivative bound `L'' = max (max L L') 0`: a
  -- constant `C₀ ≥ 0` that does not depend on the maps.
  obtain ⟨C₀, hC₀, hcore⟩ := Submission.dph_lpf_cmp_core_estimate hProd hSH m m' k X hXm hbd ω
    (max (max L L') 0) (le_max_right _ _)
  -- `spt X = univ \ zeroRegion X` is closed.
  have hXc : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- Step 4: `ε = δ / (2C₀ + 1)`.
  have hpos : 0 < 2 * C₀ + 1 := by linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (2 * C₀ + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := hε ▸ div_pos hδ hpos
  -- Step 2: eventually the derivative bounds, `ε`-closeness to `G` and the compatibilities hold.
  filter_upwards [hGjL, hGjL', Metric.tendstoUniformlyOn_iff.1 hGjU ε hε0,
    Metric.tendstoUniformlyOn_iff.1 hGjU' ε hε0, hηj, hηj'] with n hL hL' hd hd' hc hc'
  -- Step 3: `Gₙ` and `G'ₙ` are `ε`-close to `G` on `spt X`, so properness transfers to `Gₙ` on
  -- `spt X` and to the affine homotopy between them on `cyl(spt X)`.
  have hd₀ : ∀ x ∈ X.support, dist (Gj n x) (G x) ≤ ε := fun x hx =>
    (dist_comm _ _).trans_le (hd x (hXO hx)).le
  have hd₁ : ∀ x ∈ X.support, dist (Gj' n x) (G x) ≤ ε := fun x hx =>
    (dist_comm _ _).trans_le (hd' x (hXO' hx)).le
  have hest : |X (ηj' n) - X (ηj n)| ≤ C₀ * (2 * ε) :=
    hcore (Gj n) (Gj' n) (O ∩ O') (2 * ε) (ηj n) (ηj' n) (hGj n) (hGj' n) (hO.inter hO')
      (subset_inter hXO hXO') (by linarith)
      (fun x hx => by
        linarith [dist_triangle (Gj' n x) (G x) (Gj n x), dist_comm (Gj' n x) (G x),
          hd x hx.1, hd' x hx.2])
      (fun x hx => (hL x hx.1).trans ((le_max_left L L').trans (le_max_left _ 0)))
      (fun x hx => (hL' x hx.2).trans ((le_max_right L L').trans (le_max_left _ 0)))
      (Submission.dph_lpf_proper_transfer.1 m m' G (Gj n) X.support ε hXc (hGj n).continuous
        hG hd₀)
      (Submission.dph_lpf_proper_transfer.2 m m' G (Gj n) (Gj' n) X.support ε hXc
        (hGj n).continuous (hGj' n).continuous hG hd₀ hd₁)
      hc hc'
  -- `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε = δ · 2C₀/(2C₀ + 1) < δ`.
  rw [Real.dist_eq, sub_zero]
  calc |X (ηj' n) - X (ηj n)| ≤ C₀ * (2 * ε) := hest
    _ = 2 * C₀ * δ / (2 * C₀ + 1) := by rw [hε]; ring
    _ < δ := by
      rw [div_lt_iff₀ hpos]
      linarith
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

/-- **A null sequence of test forms is uniformly small (Simon Ch. 6, 2.1).**  If `ω_q → 0` in
`𝒟ⁿ(U)`, then all `ω_q` are supported in one compact `K ⊆ U` and, for every `ε > 0`, eventually
`|ω_q(x)| ≤ ε` for every `x`, in the Euclidean coefficient norm of Remark 2.6.  The `k = 0` part
of the convergence makes the operator norm `‖ω_q(x)‖` uniformly small on `K`, and `ω_q = 0` off
`K`; `Submission.fiw_ims_sc_covectorNorm_le_opNorm` gives `|α| ≤ √(P^n) ‖α‖`. -/
theorem Submission.fiw_ims_sc_converges_zero_small : ∀ (P n : ℕ) (U : Set (Eucl P)) (ω : ℕ → TestFormOn U n), TestFormOnConverges ω 0 → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ U ∧ (∀ q, tsupport ((ω q : DifferentialForm (Eucl P) n)) ⊆ K) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop, ∀ x, covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x) ≤ ε := by
  intro P n U ω hω
  obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hω
  refine ⟨K, hK, hKU, hsupp, fun ε hε => ?_⟩
  set D := Real.sqrt ((P : ℝ) ^ n)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hδ : 0 < ε / (D + 1) := by positivity
  -- `k = 0`: eventually `‖ω_q(x) - 0‖ < ε / (D + 1)` for all `x ∈ K`.
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv 0) _ hδ] with q hq x
  have hx : ‖(ω q : DifferentialForm (Eucl P) n) x‖ ≤ ε / (D + 1) := by
    by_cases hxK : x ∈ K
    · have h := hq x hxK
      rw [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
        norm_iteratedFDeriv_zero] at h
      exact h.le
    · -- off `K ⊇ tsupport ω_q` the form vanishes
      rw [image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp q h), norm_zero]
      exact hδ.le
  calc covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x)
      ≤ D * ‖(ω q : DifferentialForm (Eucl P) n) x‖ :=
        Submission.fiw_ims_sc_covectorNorm_le_opNorm P n _
    _ ≤ D * (ε / (D + 1)) := mul_le_mul_of_nonneg_left hx hD
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **Continuity criterion on `𝒟ⁿ(U)`** (the topology of Simon Ch. 6, §1, p. 134, and the
continuity required in 2.1): if for each compact `K ⊆ U` there is `A` with `|L(ω)| ≤ A·C`
whenever `spt ω ⊆ K` and `|ω(x)| ≤ C` for all `x` (the Euclidean coefficient norm of 1.15), then
`L(ω_q) → 0` for every null sequence `ω_q → 0` of test forms.  By
`fiw_ims_sc_converges_zero_small` all `spt ω_q` lie in one compact `K ⊆ U` and
`sup_x |ω_q(x)| → 0`; for `ε > 0` and `δ = ε / (|A| + 1)`, eventually
`|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.  Neither linearity of `L` nor a sign of `A` is used. -/
theorem Submission.fiw_ims_sc_continuous_of_bound : ∀ (P n : ℕ) (U : Set (Eucl P)) (L : TestFormOn U n → ℝ), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ A : ℝ, ∀ (ω : TestFormOn U n) (C : ℝ), 0 < C → tsupport ((ω : DifferentialForm (Eucl P) n)) ⊆ K → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) → |L ω| ≤ A * C) → ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 → Tendsto (fun q => L (ωs q)) atTop (𝓝 0) := by
  intro P n U L hL ωs hωs
  -- One compact `K ⊆ U` carries every `spt ω_q`, and `sup_x |ω_q(x)| → 0`.
  obtain ⟨K, hK, hKU, hsupp, hsmall⟩ :=
    Submission.fiw_ims_sc_converges_zero_small P n U ωs hωs
  -- The hypothesis on `K`: `|L(ω)| ≤ A·C` whenever `spt ω ⊆ K` and `|ω| ≤ C`.
  obtain ⟨A, hA⟩ := hL K hK hKU
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA1 : 0 < |A| + 1 := by positivity
  have hδ : 0 < ε / (|A| + 1) := div_pos hε hA1
  -- Eventually `|ω_q| ≤ δ = ε / (|A| + 1)`, hence `|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.
  filter_upwards [hsmall _ hδ] with q hq
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs q)| ≤ A * (ε / (|A| + 1)) := hA (ωs q) _ hδ (hsupp q) hq
    _ ≤ |A| * (ε / (|A| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self A) hδ.le
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hA1]
      nlinarith [abs_nonneg A]

/-- **A bounded linear functional on `𝒟ⁿ(U)` is a current of mass at most `B`** (Simon Ch. 6,
2.1 and 2.4; fact (F5/F6) for the Lipschitz push-forward).  If `T₀` is additive and homogeneous
and `|T₀(ω)| ≤ B·C` whenever `|ω(y)| ≤ C` for all `y`, then `T₀` is a current `S`: its
sequential continuity is `fiw_ims_sc_continuous_of_bound` with `A := B` on every compact
`K ⊆ U`, and every mass-admissible `ω` (`|ω| ≤ 1`) has `S(ω) ≤ |T₀(ω)| ≤ B·1`, so the
supremum `M(S)` is at most `B`. -/
theorem Submission.dph_lpf_current_of_bounded_functional : ∀ (P n : ℕ) (U : Set (Eucl P)) (T₀ : TestFormOn U n → ℝ) (B : ℝ), (∀ ω η : TestFormOn U n, T₀ (ω + η) = T₀ ω + T₀ η) → (∀ (c : ℝ) (ω : TestFormOn U n), T₀ (c • ω) = c * T₀ ω) → (∀ (ω : TestFormOn U n) (C : ℝ), (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) y) ≤ C) → |T₀ ω| ≤ B * C) → ∃ S : GeometricCurrentOn U n, (∀ ω, S ω = T₀ ω) ∧ S.mass ≤ ENNReal.ofReal B := by
  intro P n U T₀ B hadd hsmul hbound
  -- Additivity and homogeneity make `T₀` an `ℝ`-linear map on `𝒟ⁿ(U)`.
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := T₀
      map_add' := hadd
      map_smul' := fun c ω => by rw [RingHom.id_apply, smul_eq_mul]; exact hsmul c ω }
  -- Continuity: on every compact `K ⊆ U` the bound holds with `A := B`.
  refine ⟨⟨L, fun ωs hωs => Submission.fiw_ims_sc_continuous_of_bound P n U T₀
    (fun _ _ _ => ⟨B, fun ω C _ _ hω => hbound ω C hω⟩) ωs hωs⟩, fun _ => rfl, ?_⟩
  -- Mass: an admissible `ω` has `|ω| ≤ 1`, so `S(ω) ≤ |T₀(ω)| ≤ B · 1 = B`.
  apply sSup_le
  rintro _ ⟨ω, hω, rfl⟩
  exact ENNReal.ofReal_le_ofReal
    ((le_abs_self _).trans ((hbound ω 1 hω.2).trans_eq (mul_one B)))
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
/-- Slices of a test form `η` on `ℝ^{P+1} = ℝ × ℝ^P` across the first coordinate: with
`e₀ = (1, 0)` and `ι w = (0, w)`, the form `φ s x = η(s, x)(e₀, ι ·)` is the continuous linear
contraction `α ↦ α(e₀, ι ·)` applied to `η` along the affine map `x ↦ (s, x) = s • e₀ + ι x`, hence
smooth; it vanishes off the preimage of `tsupport η`, which is compact as `‖x‖ ≤ ‖(s, x)‖`; and it
depends jointly continuously on `(s, x)`. -/
theorem Submission.iwl_cr_ci_slice_testForm :
    ∀ (P m : ℕ) (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)),
      ∃ φ : ℝ → TestFormOn (univ : Set (Eucl P)) m,
        Continuous (fun p : ℝ × Eucl P => (φ p.1 : DifferentialForm (Eucl P) m) p.2) ∧
        ∀ (s : ℝ) (x : Eucl P) (v : Fin m → Eucl P),
          (φ s : DifferentialForm (Eucl P) m) x v =
            (η : DifferentialForm (Eucl (P + 1)) (m + 1))
              ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) := by
  intro P m η
  -- The linear inclusion `ι w = (0, w)`, the splitting `(s, x) = s • e₀ + ι x`, and
  -- `‖x‖ ≤ ‖(s, x)‖`.
  obtain ⟨ι, hι⟩ : ∃ ι : Eucl P →L[ℝ] Eucl (P + 1), ∀ w : Eucl P,
      ι w = (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ w)) := by
    let ιₗ : Eucl P →ₗ[ℝ] Eucl (P + 1) :=
      { toFun := fun w => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ w))
        map_add' := fun a b => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun c a => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    exact ⟨LinearMap.toContinuousLinearMap ιₗ, fun w => rfl⟩
  have hΦ : ∀ (s : ℝ) (x : Eucl P),
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))
        = s • (EuclideanSpace.single 0 1 : Eucl (P + 1)) + ι x := by
    intro s x
    rw [hι]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  have hnorm : ∀ (s : ℝ) (x : Eucl P),
      ‖x‖ ≤ ‖s • (EuclideanSpace.single 0 1 : Eucl (P + 1)) + ι x‖ := by
    intro s x
    rw [← hΦ, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    apply Real.sqrt_le_sqrt
    simp only [PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply, Fin.cons_zero,
      Fin.cons_succ, PiLp.continuousLinearEquiv_apply]
    exact le_add_of_nonneg_left (sq_nonneg _)
  set e₀ : Eucl (P + 1) := EuclideanSpace.single 0 1
  -- The continuous linear contraction `L α = α(e₀, ι ·)` of covectors.
  obtain ⟨L, hL⟩ : ∃ L : Covector (Eucl (P + 1)) (m + 1) →L[ℝ] Covector (Eucl P) m,
      ∀ (α : Covector (Eucl (P + 1)) (m + 1)) (v : Fin m → Eucl P),
        L α v = α (Fin.cons e₀ fun i => ι (v i)) := by
    refine ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM ι).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Eucl (P + 1)) m) e₀).comp
        (ContinuousAlternatingMap.curryLeftLI :
          Covector (Eucl (P + 1)) (m + 1) →ₗᵢ[ℝ] _).toContinuousLinearMap), ?_⟩
    intro α v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, ContinuousAlternatingMap.curryLeftLI_apply,
      ContinuousLinearMap.apply_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    rfl
  have hηs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (η : DifferentialForm (Eucl (P + 1)) (m + 1)) :=
    η.2.1.1
  have hηc : HasCompactSupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)) := η.2.1.2
  have hΦc : ∀ s : ℝ, Continuous fun x : Eucl P => s • e₀ + ι x := fun s =>
    continuous_const.add ι.continuous
  -- Each slice `x ↦ L (η (s • e₀ + ι x))` is a test form on `ℝ^P`.
  have htest : ∀ s : ℝ, (fun x : Eucl P => L ((η : DifferentialForm (Eucl (P + 1)) (m + 1))
      (s • e₀ + ι x))) ∈ TestFormOn (univ : Set (Eucl P)) m := by
    intro s
    refine ⟨⟨?_, ?_⟩, subset_univ _⟩
    · exact L.contDiff.comp (hηs.comp (contDiff_const.add ι.contDiff))
    · obtain ⟨ρ, hρ⟩ := hηc.isCompact.isBounded.subset_closedBall 0
      have hK : IsCompact ((fun x : Eucl P => s • e₀ + ι x) ⁻¹'
          tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1))) := by
        refine (isCompact_closedBall (0 : Eucl P) ρ).of_isClosed_subset
          ((isClosed_tsupport _).preimage (hΦc s)) ?_
        intro x hx
        have hx' := hρ hx
        rw [mem_closedBall, dist_zero_right] at hx' ⊢
        exact (hnorm s x).trans hx'
      refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
      exact (tsupport_comp_subset (g := L) (map_zero L) _).trans
        (tsupport_comp_subset_preimage _ (hΦc s))
  refine ⟨fun s => ⟨_, htest s⟩, ?_, ?_⟩
  · change Continuous fun p : ℝ × Eucl P =>
      L ((η : DifferentialForm (Eucl (P + 1)) (m + 1)) (p.1 • e₀ + ι p.2))
    exact L.continuous.comp (hηs.continuous.comp
      ((continuous_fst.smul continuous_const).add (ι.continuous.comp continuous_snd)))
  · intro s x v
    change L ((η : DifferentialForm (Eucl (P + 1)) (m + 1)) (s • e₀ + ι x)) v = _
    rw [hL, hΦ s x]
    simp only [hι]
/-- Horizontal slices for the product `[[0,1]] × X`: for `ψ ∈ 𝒟^q(ℝ^{m+1})` and `s ∈ ℝ`, the
pull-backs `j_s^# ψ` and `j_s^# ∂_s ψ` along `j_s(x) = (s, x)`, i.e. `x ↦ ψ(s, x)(ι ·)` and
`x ↦ Dψ(s, x)(e₀)(ι ·)` with `ι v = (0, v)`, are test forms in `𝒟^q(ℝ^m)`. -/
theorem Submission.dph_iprod_horizontal_slices :
    ∀ (m q : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) q),
      ∃ Ψ Ψ' : ℝ → TestFormOn (univ : Set (Eucl m)) q,
        (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m),
          (Ψ s : DifferentialForm (Eucl m) q) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) q)
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
        ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m),
          (Ψ' s : DifferentialForm (Eucl m) q) x v =
            fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q)
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (EuclideanSpace.single 0 1)
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
  have hCF := Submission.iwl_sp_exists_compatible_testForm
  intro m q ψ
  -- 1. `ι v = (0, v)` is a continuous linear map `ℝ^m → ℝ^{m+1}`.
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    { toFun := fun w => Fin.cons 0 w
      map_add' := by
        intro a b; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro c a; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let ι : Eucl m →L[ℝ] Eucl (m + 1) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
      LinearMap.toContinuousLinearMap L ∘L (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap
  have hιv : ∀ v : Eucl m, ι v = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ v)) :=
    fun v => rfl
  -- 2. `j_s(x) = (s, 0) + ι x` is affine, so smooth with derivative `ι`.
  have hj : ∀ s : ℝ, (fun x : Eucl m =>
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) =
      fun x => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s 0) + ι x := by
    intro s
    funext x
    rw [hιv]
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- 3. `‖x‖ ≤ ‖j_s(x)‖`, so `j_s` is proper.
  have hnorm : ∀ (s : ℝ) (x : Eucl m), ‖x‖ ≤ ‖(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))‖ := by
    intro s x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    apply Real.sqrt_le_sqrt
    simp
    positivity
  -- 4. Slices of any test form, by the cut-off pull-back along `j_s` (proper on `A = univ`).
  have hslice : ∀ (ω : TestFormOn (univ : Set (Eucl (m + 1))) q) (s : ℝ),
      ∃ η : TestFormOn (univ : Set (Eucl m)) q, ∀ (x : Eucl m) (v : Fin q → Eucl m),
        (η : DifferentialForm (Eucl m) q) x v = (ω : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => ι (v i)) := by
    intro ω s
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl m =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) := by
      rw [hj s]
      exact contDiff_const.add ι.contDiff
    have hfd : ∀ x, fderiv ℝ (fun x : Eucl m =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) x = ι := by
      intro x
      rw [hj s]
      exact ((ι.hasFDerivAt).const_add _).fderiv
    have hpr : ∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ univ →
        IsCompact ((fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ⁻¹' K ∩ univ) := by
      intro K hK _
      rw [inter_univ]
      apply Metric.isCompact_of_isClosed_isBounded
      · exact hK.isClosed.preimage hsm.continuous
      · obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
        refine (Metric.isBounded_closedBall (x := (0 : Eucl m)) (r := R)).subset ?_
        intro x hx
        have := hR hx
        rw [mem_closedBall, dist_zero_right] at this ⊢
        exact (hnorm s x).trans this
    obtain ⟨η, ζ, N, -, hAN, -, -, hη2, -⟩ := hCF m (m + 1) q univ univ univ _ isOpen_univ
      (subset_univ _) hsm hpr ω
    refine ⟨η, fun x v => ?_⟩
    rw [hη2 x (hAN (mem_univ x)), hfd x]
    rfl
  -- 5. `ψ' = Dψ(·)(e₀)` is a test form.
  have hψ' : ∃ ψ' : TestFormOn (univ : Set (Eucl (m + 1))) q, ∀ y,
      (ψ' : DifferentialForm (Eucl (m + 1)) q) y =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y (EuclideanSpace.single 0 1) := by
    refine ⟨⟨fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y
        (EuclideanSpace.single 0 1), ⟨⟨?_, ?_⟩, subset_univ _⟩⟩, fun y => rfl⟩
    · exact (ψ.property.1.1.fderiv_right (by simp)).clm_apply contDiff_const
    · exact (ψ.property.1.2.fderiv ℝ).comp_left (g := fun L => L (EuclideanSpace.single 0 1)) rfl
  -- 6. Choose the slices of `ψ` and `ψ'` for every `s`.
  obtain ⟨ψ', hψ'⟩ := hψ'
  choose Ψ hΨ using fun s => hslice ψ s
  choose Ψ' hΨ' using fun s => hslice ψ' s
  refine ⟨Ψ, Ψ', fun s x v => ?_, fun s x v => ?_⟩
  · rw [hΨ s x v]
    rfl
  · rw [hΨ' s x v, hψ']
    rfl
/-- Euclidean coefficient norms `|γ| = covectorEuclideanNorm γ` of slices of covectors, with
`ι(v) = (0, v) ∈ ℝ^{m+1}` and `e₀ = EuclideanSpace.single 0 1`: (C1) if `γ'(v) = γ(e₀, ι ∘ v)`
then `|γ'| ≤ |γ|`; (C2) if `γ'(v) = γ(ι ∘ v)` then `|γ'| ≤ |γ|`; (C3) `|α| ≤ √(P^n) · ‖α‖`.
For (C1) and (C2), `e₀ = b_0` and `ι(b_j) = b_{j+1}` for the standard bases `b`, so the
coefficients of `γ'` are coefficients of `γ` on distinct strictly increasing multi-indices; for
(C3), each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` is at most
`‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`. -/
theorem Submission.dph_iprod_slice_covector_norm_le :
    (∀ (m k : ℕ) (γ : Covector (Eucl (m + 1)) (k + 1)) (γ' : Covector (Eucl m) k),
      (∀ v : Fin k → Eucl m, γ' v = γ (Fin.cons (EuclideanSpace.single 0 1) fun i =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      covectorEuclideanNorm γ' ≤ covectorEuclideanNorm γ) ∧
    (∀ (m q : ℕ) (γ : Covector (Eucl (m + 1)) q) (γ' : Covector (Eucl m) q),
      (∀ v : Fin q → Eucl m, γ' v = γ (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      covectorEuclideanNorm γ' ≤ covectorEuclideanNorm γ) ∧
    (∀ (P n : ℕ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ n) * ‖α‖) := by
  -- `e₀` is the first standard basis vector of `ℝ^{m+1}`.
  have hb0 : ∀ m : ℕ, (EuclideanSpace.single 0 1 : Eucl (m + 1)) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0 := by
    intro m; simp [EuclideanSpace.basisFun_apply]
  -- `ι` maps the `j`-th standard basis vector of `ℝ^m` to the `(j+1)`-st one of `ℝ^{m+1}`.
  have hbι : ∀ (m : ℕ) (j : Fin m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (EuclideanSpace.basisFun (Fin m) ℝ j))) =
      EuclideanSpace.basisFun (Fin (m + 1)) ℝ j.succ := by
    intro m j
    apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [EuclideanSpace.basisFun_apply]
  -- A sum dominated termwise, along an injection, by nonnegative terms is at most the full sum.
  have key : ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (g : A → B),
      Function.Injective g → ∀ (F : B → ℝ) (G : A → ℝ), (∀ b, 0 ≤ F b) →
      (∀ a, G a ≤ F (g a)) → ∑ a, G a ≤ ∑ b, F b := by
    intro A B _ _ _ g hg F G hF hG
    calc ∑ a, G a ≤ ∑ a, F (g a) := Finset.sum_le_sum (fun a _ => hG a)
      _ = ∑ b ∈ Finset.univ.image g, F b := (Finset.sum_image (fun a _ b _ h => hg h)).symm
      _ ≤ ∑ b, F b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hF b)
  refine ⟨?_, ?_, ?_⟩
  · -- (C1): compare along `I ↦ (0, I + 1)`.
    intro m k γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin k → Fin m =>
      (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i.succ
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (Fin.cons 0 (fun i => (I i).succ) : Fin (k + 1) → Fin (m + 1)) := by
          intro a b hab
          induction a using Fin.cases with
          | zero =>
            induction b using Fin.cases with
            | zero => exact absurd hab (lt_irrefl _)
            | succ j => simp [Fin.succ_pos]
          | succ i =>
            induction b using Fin.cases with
            | zero => exact absurd hab (Fin.not_lt_zero _)
            | succ j =>
              simp only [Fin.cons_succ, Fin.succ_lt_succ_iff] at hab ⊢
              exact h1 hab
        rw [ite_eq_left h1, ite_eq_left h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.cons_zero]
          exact hb0 m
        · simp only [Fin.cons_succ]
          exact hbι m (I i)
      · rw [ite_eq_right h1]
        split_ifs <;> positivity
  · -- (C2): compare along `I ↦ I + 1`.
    intro m q γ γ' hγ'
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply key (fun I : Fin q → Fin m => (fun i => (I i).succ : Fin q → Fin (m + 1)))
    · intro I I' h
      funext i
      have := congrFun h i
      simpa using this
    · intro J; split_ifs <;> positivity
    · intro I
      by_cases h1 : StrictMono I
      · have h2 : StrictMono (fun i => (I i).succ : Fin q → Fin (m + 1)) :=
          fun a b hab => Fin.succ_lt_succ_iff.mpr (h1 hab)
        rw [ite_eq_left h1, ite_eq_left h2, hγ']
        apply le_of_eq
        congr 2
        funext i
        exact hbι m (I i)
      · rw [ite_eq_right h1]
        split_ifs <;> positivity
  · -- (C3): every coefficient is at most `‖α‖`, and there are `P ^ n` of them.
    intro P n α
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

/-- Full tuple sum of squared coefficients in the standard basis `e` of `ℝ^m`: for a `j`-covector
`γ`, `∑_i γ(e_{i 0}, …, e_{i (j-1)})² = j! |γ|²`, the sum over all index maps `i : Fin j → Fin m`.
The counting identity turns the left side into `j! ∑_{I increasing} γ(e_I)²`, and the
orthonormal-basis formula for `|γ|²`, applied to `e` itself, identifies that sum with `|γ|²`. -/
theorem Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul :
    ∀ (m j : ℕ) (γ : Covector (Eucl m) j),
      ∑ i : Fin j → Fin m, (γ (fun k => EuclideanSpace.basisFun (Fin m) ℝ (i k))) ^ 2 =
        (j.factorial : ℝ) * covectorEuclideanNorm γ ^ 2 := by
  intro m j γ
  rw [Submission.slicing_mb_wn_norm_sq_eq_onb_sum m j (EuclideanSpace.basisFun (Fin m) ℝ) γ]
  exact Submission.slicing_mb_wn_sq_sum_eq_factorial_mul m j (EuclideanSpace.basisFun (Fin m) ℝ) γ
/-- One-slot bound: for `L : ℝ^P → ℝ^Q` and a linear functional `f` on `ℝ^Q`,
`∑_a f(L e_a)² ≤ ‖L‖² ∑_b f(e′_b)²`.  The Riesz vector `g = (f(e′_b))_b` gives `f = ⟨g, ·⟩`
and the test vector `u = (f(L e_a))_a` has `f(L u) = |u|²`, so Cauchy–Schwarz and the operator
norm give `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`; cancel `|u|` and square. -/
theorem Submission.iwl_sp_pn_sum_sq_comp_basis_le : ∀ (P Q : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (f : Eucl Q →ₗ[ℝ] ℝ), ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 ≤ ‖L‖ ^ 2 * ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 := by
  intro P Q L f
  -- The Riesz vector `g` of `f`: `f y = ⟨g, y⟩` and `|g|² = ∑_b f(e′_b)²`.
  set g : Eucl Q := WithLp.toLp 2 (fun b => f (EuclideanSpace.basisFun (Fin Q) ℝ b)) with hg_def
  have hf : ∀ y : Eucl Q, f y = inner ℝ g y := by
    intro y
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin Q) ℝ).sum_repr y]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hg_def]
  have hg : ‖g‖ ^ 2 = ∑ b : Fin Q, (f (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  -- The test vector `u`: `|u|² = ∑_a f(L e_a)²` and `f(L u) = |u|²`.
  set u : Eucl P := WithLp.toLp 2 (fun a => f (L (EuclideanSpace.basisFun (Fin P) ℝ a)))
    with hu_def
  have hu : ‖u‖ ^ 2 = ∑ a : Fin P, (f (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  have hfLu : f (L u) = ‖u‖ ^ 2 := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr u]
    rw [map_sum, map_sum, hu]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hu_def, sq]
  -- Cauchy–Schwarz and the operator norm: `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`.
  have key : ‖u‖ ^ 2 ≤ ‖g‖ * (‖L‖ * ‖u‖) := by
    rw [← hfLu, hf]
    calc inner ℝ g (L u) ≤ ‖g‖ * ‖L u‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * (‖L‖ * ‖u‖) := mul_le_mul_of_nonneg_left (L.le_opNorm u) (norm_nonneg _)
  -- Cancel `|u|` (trivial if `|u| = 0`), then square.
  have hle : ‖u‖ ≤ ‖L‖ * ‖g‖ := by
    rcases (norm_nonneg u).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · have : ‖u‖ * ‖u‖ ≤ (‖L‖ * ‖g‖) * ‖u‖ := by nlinarith [key]
      exact le_of_mul_le_mul_right this hpos
  rw [← hu, ← hg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Multilinear tensor-power bound: for every continuous linear `L : ℝ^P → ℝ^Q` and every
`j`-multilinear `β : (ℝ^Q)^j → ℝ` (not necessarily alternating or continuous),
`∑_{i : Fin j → Fin P} β(L e_{i(1)}, …, L e_{i(j)})²`
`≤ (‖L‖²)^j ∑_{i : Fin j → Fin Q} β(e′_{i(1)}, …, e′_{i(j)})²`,
with `e`, `e′` the standard bases.  Induction on `j`, generalizing `β`: split the sums over
`Fin (j + 1) → Fin n` along `Fin.cons`, apply the inductive hypothesis to `β.curryLeft (L e_a)`,
exchange the sums and bound each slot functional `y ↦ β(Fin.cons y (e′ ∘ i″))` by the one-slot
estimate `Submission.iwl_sp_pn_sum_sq_comp_basis_le`. -/
theorem Submission.iwl_sp_pn_multilinear_sum_sq_le :
    ∀ (P Q j : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (β : MultilinearMap ℝ (fun _ : Fin j => Eucl Q) ℝ),
      ∑ i : Fin j → Fin P, (β (fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i k)))) ^ 2 ≤
        (‖L‖ ^ 2) ^ j *
          ∑ i : Fin j → Fin Q, (β (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k))) ^ 2 := by
  intro P Q j L
  induction j with
  | zero =>
    -- Both sums have the single empty tuple as index, and both arguments of `β` are empty.
    intro β
    rw [Fintype.sum_unique, Fintype.sum_unique, pow_zero, one_mul]
    exact (congrArg (fun v => β v ^ 2) (Subsingleton.elim _ _)).le
  | succ j ih =>
    intro β
    -- Sums over `Fin (j + 1) → Fin n` split along `Fin.cons` (`Fin.consEquiv`).
    have split : ∀ (n : ℕ) (G : (Fin (j + 1) → Fin n) → ℝ),
        ∑ i, G i = ∑ a : Fin n, ∑ i' : Fin j → Fin n, G (Fin.cons a i') := by
      intro n G
      rw [← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin n) _ _ fun _ => rfl).symm
    -- The slot functionals `y ↦ β (Fin.cons y w)` are linear.
    let slot : (Fin j → Eucl Q) → Eucl Q →ₗ[ℝ] ℝ := fun w =>
      { toFun := fun y => β (Fin.cons y w)
        map_add' := fun x y => β.cons_add w x y
        map_smul' := fun c x => β.cons_smul w c x }
    calc ∑ i : Fin (j + 1) → Fin P, (β fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i k))) ^ 2
        = ∑ a : Fin P, ∑ i' : Fin j → Fin P,
            (β.curryLeft (L (EuclideanSpace.basisFun (Fin P) ℝ a))
              fun k => L (EuclideanSpace.basisFun (Fin P) ℝ (i' k))) ^ 2 := by
          rw [split P]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ =>
            congrArg (fun v => β v ^ 2)
              (Fin.comp_cons (fun p => L (EuclideanSpace.basisFun (Fin P) ℝ p)) a i')
      -- the inductive hypothesis for `β.curryLeft (L e_a)`
      _ ≤ ∑ a : Fin P, (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q,
            (β.curryLeft (L (EuclideanSpace.basisFun (Fin P) ℝ a))
              fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k)) ^ 2 :=
          Finset.sum_le_sum fun a _ => ih _
      _ = (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q, ∑ a : Fin P,
            (slot (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))
              (L (EuclideanSpace.basisFun (Fin P) ℝ a))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          rfl
      -- the one-slot bound for each slot functional
      _ ≤ (‖L‖ ^ 2) ^ j * ∑ i'' : Fin j → Fin Q, ‖L‖ ^ 2 * ∑ b : Fin Q,
            (slot (fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))
              (EuclideanSpace.basisFun (Fin Q) ℝ b)) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i'' _ => Submission.iwl_sp_pn_sum_sq_comp_basis_le P Q L _)
            (by positivity)
      _ = (‖L‖ ^ 2) ^ (j + 1) * ∑ b : Fin Q, ∑ i'' : Fin j → Fin Q,
            (β (Fin.cons (EuclideanSpace.basisFun (Fin Q) ℝ b)
              fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i'' k))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm, pow_succ (‖L‖ ^ 2) j, mul_assoc]
          rfl
      _ = (‖L‖ ^ 2) ^ (j + 1) * ∑ i : Fin (j + 1) → Fin Q,
            (β fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k)) ^ 2 := by
          rw [split Q]
          exact congrArg _ (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i'' _ =>
            congrArg (fun v => β v ^ 2)
              (Fin.comp_cons (fun p => EuclideanSpace.basisFun (Fin Q) ℝ p) b i'').symm)

/-- Pullback bound for the Euclidean covector norm: for `L : ℝ^P → ℝ^Q` and a `j`-covector `α`
on `ℝ^Q`, `|L^#α| ≤ ‖L‖^j |α|`.  The multilinear bound
`Submission.iwl_sp_pn_multilinear_sum_sq_le` for `β := α` gives
`∑_i α(L e∘i)² ≤ (‖L‖²)^j ∑_i α(e′∘i)²`, and `α(L e∘i) = (L^#α)(e∘i)` by definition.  By
`Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul` the two sums over all index tuples are
`j! |L^#α|²` and `j! |α|²`; cancel `j! > 0` and take square roots. -/
theorem Submission.iwl_sp_covectorEuclideanNorm_pullback_le : ∀ (P Q j : ℕ) (L : Eucl P →L[ℝ] Eucl Q) (α : Covector (Eucl Q) j), covectorEuclideanNorm (α.compContinuousLinearMap L) ≤ ‖L‖ ^ j * covectorEuclideanNorm α := by
  intro P Q j L α
  -- Sums over all index tuples: `j! |L^#α|²` on `ℝ^P` and `j! |α|²` on `ℝ^Q`.
  have hP := Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul P j (α.compContinuousLinearMap L)
  have hQ := Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul Q j α
  -- The multilinear bound for `β := α`.
  have hβ := Submission.iwl_sp_pn_multilinear_sum_sq_le P Q j L α.toMultilinearMap
  have key : (j.factorial : ℝ) * covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2 ≤
      (j.factorial : ℝ) * (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 :=
    calc (j.factorial : ℝ) * covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2
        = ∑ i : Fin j → Fin P,
            (α.compContinuousLinearMap L fun k => EuclideanSpace.basisFun (Fin P) ℝ (i k)) ^ 2 :=
          hP.symm
      -- `(L^#α)(e∘i) = α(L e∘i)` holds by definition (`compContinuousLinearMap_apply`).
      _ ≤ (‖L‖ ^ 2) ^ j * ∑ i : Fin j → Fin Q,
            (α fun k => EuclideanSpace.basisFun (Fin Q) ℝ (i k)) ^ 2 := hβ
      _ = (j.factorial : ℝ) * (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 := by
          rw [hQ]
          ring
  -- Cancel `j! > 0`, then take square roots of nonnegative quantities.
  have hsq : covectorEuclideanNorm (α.compContinuousLinearMap L) ^ 2 ≤
      (‖L‖ ^ j * covectorEuclideanNorm α) ^ 2 :=
    le_of_mul_le_mul_left key (by exact_mod_cast j.factorial_pos)
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg (norm_nonneg L) j) (covectorEuclideanNorm_nonneg α))

/-- Bounded compatible pull-back forms (Steps 2–3 of the Lipschitz push-forward construction): if
`f` is `C^∞`, proper on `A`, and `‖Df‖ ≤ Λ` on an open `O ⊇ A`, every `ω ∈ 𝒟ᵏ(ℝ^{m′})` has a
pull-back `η ∈ 𝒟ᵏ(ℝ^m)` with `η = f^#ω` on an open `N ⊇ A` and `|η(x)| ≤ Λ^k C` whenever
`|ω| ≤ C`.  The cut-off pull-back `η = ζ f^#ω ∈ 𝒟ᵏ(O)` of
`Submission.iwl_sp_exists_compatible_testForm` is also a test form on `ℝ^m`; on `O`,
`|ζ f^#ω| = ζ |f^#ω| ≤ ‖Df‖^k |ω ∘ f| ≤ Λ^k C` by
`Submission.iwl_sp_covectorEuclideanNorm_pullback_le`, and off `O ⊇ spt η` it vanishes. -/
theorem Submission.dph_lpfex_bounded_compatible_form :
    ∀ (m m' k : ℕ) (f : Eucl m → Eucl m') (A O : Set (Eucl m)) (Λ : ℝ≥0), IsOpen O → A ⊆ O →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ x ∈ O, ‖fderiv ℝ f x‖ ≤ Λ) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (f ⁻¹' K ∩ A)) →
      ∀ ω : TestFormOn (univ : Set (Eucl m')) k, ∃ η : TestFormOn (univ : Set (Eucl m)) k,
        (∃ N : Set (Eucl m), IsOpen N ∧ A ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl m) k) x =
          ((ω : DifferentialForm (Eucl m') k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∧
        ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
          ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C := by
  intro m m' k f A O Λ hO hAO hf hDf hprop ω
  -- 1. The cut-off pull-back `η₀ = ζ f^#ω ∈ 𝒟ᵏ(O)` with `0 ≤ ζ ≤ 1`, equal to `f^#ω` on `N ⊇ A`.
  obtain ⟨η₀, ζ, N, hN, hAN, hζ, hη₀, hη₀N, -⟩ :=
    Submission.iwl_sp_exists_compatible_testForm m m' k O univ A f hO hAO hf
      (fun K hK _ => hprop K hK) ω
  obtain ⟨hη₀test, hη₀O⟩ := η₀.property
  -- 2. `spt η₀ ⊆ O ⊆ ℝ^m`, so the same form is a test form on `ℝ^m`.
  refine ⟨⟨(η₀ : DifferentialForm (Eucl m) k), hη₀test, subset_univ _⟩, ⟨N, hN, hAN, hη₀N⟩,
    fun C hC x => ?_⟩
  show covectorEuclideanNorm ((η₀ : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C
  -- 3. Homogeneity `|c γ| = |c| |γ|`: every squared coefficient scales by `c²`.
  have hsmul : ∀ (c : ℝ) (γ : Covector (Eucl m) k),
      covectorEuclideanNorm (c • γ) = |c| * covectorEuclideanNorm γ := by
    intro c γ
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  -- 4. `C ≥ |ω(0)| ≥ 0`.
  have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
  by_cases hx : x ∈ O
  · -- On `O`: `|ζ f^#ω| = ζ |f^#ω| ≤ |f^#ω| ≤ ‖Df‖^k |ω ∘ f| ≤ Λ^k C`.
    rw [hη₀ x, hsmul, abs_of_nonneg (hζ x).1]
    calc _ ≤ covectorEuclideanNorm
          (((ω : DifferentialForm (Eucl m') k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hζ x).2
      _ ≤ ‖fderiv ℝ f x‖ ^ k * covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) (f x)) :=
          Submission.iwl_sp_covectorEuclideanNorm_pullback_le m m' k _ _
      _ ≤ (Λ : ℝ) ^ k * C :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDf x hx) k) (hC _)
            (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.coe_nonneg k)
  · -- Off `O ⊇ spt η₀` the form vanishes.
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hη₀O h), covectorEuclideanNorm_zero]
    exact mul_nonneg (pow_nonneg Λ.coe_nonneg k) hC0
/-- Simon Ch. 6, 3.6–3.9 (Lipschitz push-forward, existence), the Cauchy argument of Step 6: a
real sequence `a` converges if `a (q i) - a (p i) → 0` for all index maps `p, q → ∞`. -/
theorem Submission.dph_lpfex_tendsto_of_index_maps :
    ∀ a : ℕ → ℝ, (∀ p q : ℕ → ℕ, Tendsto p atTop atTop → Tendsto q atTop atTop →
      Tendsto (fun i => a (q i) - a (p i)) atTop (𝓝 0)) → ∃ s : ℝ, Tendsto a atTop (𝓝 s) := by
  intro a ha
  -- 1. `a` is Cauchy; otherwise some `ε > 0` has `ε ≤ |a m - a n|` for some `m, n ≥ N`, every `N`.
  have hcauchy : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    by_contra hne
    push Not at hne
    obtain ⟨ε, hε, hgap⟩ := hne
    -- 2. Index maps `p N, q N ≥ N` with `ε ≤ |a (p N) - a (q N)|`; both tend to infinity.
    choose p hp q hq hpq using hgap
    have hpt : Tendsto p atTop atTop := tendsto_atTop_mono hp tendsto_id
    have hqt : Tendsto q atTop atTop := tendsto_atTop_mono hq tendsto_id
    -- 3. The hypothesis gives `|a (q i) - a (p i)| < ε` for some `i`, contradicting the gap.
    obtain ⟨i, hi⟩ := (Metric.tendsto_nhds.1 (ha p q hpt hqt) ε hε).exists
    have hgap_i := hpq i
    rw [Real.dist_eq, sub_zero] at hi
    rw [Real.dist_eq, abs_sub_comm] at hgap_i
    exact lt_irrefl ε (hgap_i.trans_lt hi)
  -- 4. `ℝ` is complete.
  exact cauchySeq_tendsto_of_complete hcauchy
/-- Support of a push-forward (Simon Ch. 6, 2.23 and 3.6, pp. 139, 147): if `S ω` is the limit of
`X` on forms equal to the pull-back of `ω` by continuous `G_n` near `spt X`, and `G_n → G`
uniformly on `spt X`, then `spt S ⊆ closure (G(spt X))`. -/
theorem Submission.dph_lpfex_support_subset_closure_image :
    ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k)
      (S : GeometricCurrentOn (univ : Set (Eucl m')) k) (G : Eucl m → Eucl m')
      (Gj : ℕ → Eucl m → Eucl m'),
      (∀ n, Continuous (Gj n)) → TendstoUniformlyOn Gj G atTop X.support →
      (∀ (ω : TestFormOn (univ : Set (Eucl m')) k)
          (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧
          ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x)) →
        Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) →
      S.support ⊆ closure (G '' X.support) := by
  intro m m' k X S G Gj hGj hunif hchar y hy
  by_contra hyc
  -- 1. A ball `B(y, ε)` misses `closure (G(spt X))`, so `ε ≤ dist (G x) y` on `spt X`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl y hyc
  have hfar : ∀ x ∈ X.support, ε ≤ dist (G x) y := by
    intro x hx
    by_contra hlt
    exact hball (mem_ball.mpr (not_le.mp hlt)) (subset_closure (mem_image_of_mem G hx))
  have hρ : 0 < ε / 3 := by positivity
  -- 2. `S` vanishes on `B(y, ε/3)`: the zero forms are eventually compatible with `ω`.
  have hvan : S.VanishesOn (ball y (ε / 3)) := by
    intro ω hω
    have hT := hchar ω (fun _ => 0) <| by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (ε / 3) hρ] with n hn
      refine ⟨Gj n ⁻¹' (tsupport (ω : DifferentialForm (Eucl m') k))ᶜ,
        (isClosed_tsupport _).isOpen_compl.preimage (hGj n), ?_, ?_⟩
      · -- `spt X ⊆ G_n⁻¹((spt ω)ᶜ)`, by the triangle inequality.
        intro x hx hmem
        have h1 : dist (Gj n x) y < ε / 3 := mem_ball.mp (hω hmem)
        linarith [hfar x hx, hn x hx, dist_triangle (G x) (Gj n x) y]
      · -- There `ω(G_n x) = 0`, so its pull-back is `0`.
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx]
        ext v
        simp
    simp only [map_zero] at hT
    exact (tendsto_nhds_unique tendsto_const_nhds hT).symm
  -- 3. `B(y, ε/3)` is open with compact closure, so `y ∈ S.zeroRegion`, i.e. `y ∉ spt S`.
  exact hy.2 (mem_sUnion.mpr ⟨ball y (ε / 3), ⟨isOpen_ball,
    (isCompact_closedBall y (ε / 3)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _, hvan⟩, mem_ball_self hρ⟩)
/-- **Lipschitz push-forward, existence** (Simon Ch. 6, 2.29, p. 141; supplied Steps 1–12).  Assume
the reference-sequence statement (RS) and the comparison statement (CL).  Let `M(X) < ∞`, let
`G` be `Λ`-Lipschitz on `(spt X)_r` and proper on `spt X`.  (RS) with `F := spt X` gives `C^∞`
maps `G_n` with `‖DG_n‖ ≤ Λ` on `O₀ := (spt X)_{r/2}`, `G_n → G` uniformly there and `G_n` proper
on `spt X` for `n ≥ n₀`.  `Submission.dph_lpfex_bounded_compatible_form` gives forms `η_n(ω)`,
compatible with `(G_n, ω)` near `spt X` for `n ≥ n₀` (`η_n(ω) := 0` for `n < n₀`), with
`|η_n(ω)| ≤ Λ^k C` whenever `|ω| ≤ C`; the mass bound gives `|X(η_n(ω))| ≤ M(X) Λ^k C`.
(CL) along pairs of reindexings and `Submission.dph_lpfex_tendsto_of_index_maps` give a limit
`S₀(ω) = lim X(η_n(ω))`, and (CL) against `η_n(ω)` shows that every admissible approximation
computes `S₀(ω)`; this makes `S₀` linear.  `Submission.dph_lpf_current_of_bounded_functional`
turns `S₀` into a current `S` with `M(S) ≤ Λ^k M(X)`; uniqueness is uniqueness of limits, and
`Submission.dph_lpfex_support_subset_closure_image` gives `spt S ⊆ closure (G(spt X))`. -/
theorem Submission.dph_lpf_existence : (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r → IsClosed F → LipschitzOnWith Λ G (thickening r F) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) → ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧ (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧ TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧ ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧ (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧ S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support)) := by
  intro hRS hCL m m' k X G Λ r hXm hXb hr hLip hprop
  -- 1. Reference sequence: (RS) with the closed set `F := spt X`, on `O₀ := (spt X)_{r/2}`.
  have hXc : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  obtain ⟨Gs, hGs, hGsd, hGsu, hGsp⟩ := hRS m m' G Λ r X.support hr hXc hLip hprop
  set O₀ := thickening (r / 2) X.support
  have hO₀ : IsOpen O₀ := isOpen_thickening
  have hXO₀ : X.support ⊆ O₀ := self_subset_thickening (half_pos hr) _
  have hGsd' : ∀ᶠ n in atTop, ∀ x ∈ O₀, ‖fderiv ℝ (Gs n) x‖ ≤ (Λ : ℝ) :=
    Eventually.of_forall hGsd
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hGsp
  -- 3. Forms `η n ω`, compatible with `(G_n, ω)` near `spt X` for `n ≥ n₀`, with
  -- `|η n ω| ≤ Λ^k C` whenever `|ω| ≤ C`; `η n ω := 0` for `n < n₀`.
  have hη : ∀ (n : ℕ) (ω : TestFormOn (univ : Set (Eucl m')) k),
      ∃ η : TestFormOn (univ : Set (Eucl m)) k,
        (n₀ ≤ n → ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (η : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gs n x)).compContinuousLinearMap
              (fderiv ℝ (Gs n) x)) ∧
        ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
          ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl m) k) x) ≤ (Λ : ℝ) ^ k * C := by
    intro n ω
    by_cases hn : n₀ ≤ n
    · obtain ⟨η, hc, hb⟩ := Submission.dph_lpfex_bounded_compatible_form m m' k (Gs n) X.support
        O₀ Λ hO₀ hXO₀ (hGs n) (hGsd n) (hn₀ n hn) ω
      exact ⟨η, fun _ => hc, hb⟩
    · refine ⟨0, fun h => absurd h hn, fun C hC x => ?_⟩
      have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
      rw [Submodule.coe_zero, Pi.zero_apply, covectorEuclideanNorm_zero]
      positivity
  choose η hηc hηb using hη
  have hηc0 : ∀ ω, ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
      (η n ω : DifferentialForm (Eucl m) k) x =
        ((ω : DifferentialForm (Eucl m') k) (Gs n x)).compContinuousLinearMap
          (fderiv ℝ (Gs n) x) :=
    fun ω => (eventually_ge_atTop n₀).mono fun n hn => hηc n ω hn
  -- 5. Reindexing along `p → ∞` keeps the reference sequence and the compatibility.
  have hGsu' : ∀ p : ℕ → ℕ, Tendsto p atTop atTop →
      TendstoUniformlyOn (fun i => Gs (p i)) G atTop O₀ :=
    fun p hp u hu => hp.eventually (hGsu u hu)
  have hηc' : ∀ p : ℕ → ℕ, Tendsto p atTop atTop → ∀ ω, ∀ᶠ i in atTop, ∃ N : Set (Eucl m),
      IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η (p i) ω : DifferentialForm (Eucl m) k) x =
        ((ω : DifferentialForm (Eucl m') k) (Gs (p i) x)).compContinuousLinearMap
          (fderiv ℝ (Gs (p i)) x) :=
    fun p hp ω => (hp.eventually_ge_atTop n₀).mono fun i hi => hηc (p i) ω hi
  -- 6. (CL) along any two reindexings: `X (η n ω)` converges, to `S₀ ω` say.
  have hlim : ∀ ω, ∃ s, Tendsto (fun n => X (η n ω)) atTop (𝓝 s) := by
    intro ω
    refine Submission.dph_lpfex_tendsto_of_index_maps _ fun p q hp hq => ?_
    exact hCL m m' k X G hXm hXb hprop (fun i => Gs (p i)) (fun i => Gs (q i)) O₀ O₀ Λ Λ
      hO₀ hXO₀ (fun i => hGs (p i)) (Eventually.of_forall fun i => hGsd (p i)) (hGsu' p hp)
      hO₀ hXO₀ (fun i => hGs (q i)) (Eventually.of_forall fun i => hGsd (q i)) (hGsu' q hq)
      ω (fun i => η (p i) ω) (fun i => η (q i) ω) (hηc' p hp ω) (hηc' q hq ω)
  choose S₀ hS₀ using hlim
  -- 9. (CL) against `η n ω`: every admissible approximation computes `S₀ ω`.
  have hconv : ∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O →
      X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
      (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
      ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (ηj n : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x)) →
        Tendsto (fun n => X (ηj n)) atTop (𝓝 (S₀ ω)) := by
    intro Gj O L hO hXO hGj hGjd hGju ω ηj hηj
    have h := hCL m m' k X G hXm hXb hprop Gs Gj O₀ O Λ L hO₀ hXO₀ hGs hGsd' hGsu hO hXO hGj
      hGjd hGju ω (fun n => η n ω) ηj (hηc0 ω) hηj
    simpa using h.add (hS₀ ω)
  -- 7. Linearity of `S₀`: the sums and multiples of the `η n ω` are again compatible.
  have hadd : ∀ ω ω' : TestFormOn (univ : Set (Eucl m')) k, S₀ (ω + ω') = S₀ ω + S₀ ω' := by
    intro ω ω'
    have hc : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        ((η n ω + η n ω' : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x =
          (((ω + ω' : TestFormOn (univ : Set (Eucl m')) k) : DifferentialForm (Eucl m') k)
            (Gs n x)).compContinuousLinearMap (fderiv ℝ (Gs n) x) := by
      filter_upwards [hηc0 ω, hηc0 ω'] with n ⟨N, hN, hXN, hNe⟩ ⟨N', hN', hXN', hNe'⟩
      refine ⟨N ∩ N', hN.inter hN', subset_inter hXN hXN', fun x hx => ?_⟩
      rw [Submodule.coe_add, Pi.add_apply, hNe x hx.1, hNe' x hx.2, Submodule.coe_add,
        Pi.add_apply]
      ext v
      simp
    exact tendsto_nhds_unique (hconv Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu _ _ hc)
      (((hS₀ ω).add (hS₀ ω')).congr fun n => (map_add X.toCurrent (η n ω) (η n ω')).symm)
  have hsmul : ∀ (c : ℝ) (ω : TestFormOn (univ : Set (Eucl m')) k), S₀ (c • ω) = c * S₀ ω := by
    intro c ω
    have hc : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        ((c • η n ω : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x =
          (((c • ω : TestFormOn (univ : Set (Eucl m')) k) : DifferentialForm (Eucl m') k)
            (Gs n x)).compContinuousLinearMap (fderiv ℝ (Gs n) x) := by
      filter_upwards [hηc0 ω] with n ⟨N, hN, hXN, hNe⟩
      refine ⟨N, hN, hXN, fun x hx => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hNe x hx, Submodule.coe_smul, Pi.smul_apply]
      ext v
      simp
    exact tendsto_nhds_unique (hconv Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu _ _ hc)
      (((hS₀ ω).const_mul c).congr fun n => (by rw [map_smul, smul_eq_mul]))
  -- 4 and 8. `|X (η n ω)| ≤ M(X) Λ^k C`, hence `|S₀ ω| ≤ Λ^k M(X) C`, whenever `|ω| ≤ C`.
  have hXη : ∀ (n : ℕ) (ω : TestFormOn (univ : Set (Eucl m')) k) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
        |X (η n ω)| ≤ X.mass.toReal * ((Λ : ℝ) ^ k * C) :=
    fun n ω C hC => Submission.cmb_abs_apply_le_of_massOn_le m k univ univ X (η n ω) _ _
      ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hXm.ne).ge (subset_univ _) (hηb n ω C hC)
  have hS₀b : ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m') k) y) ≤ C) →
        |S₀ ω| ≤ ((Λ : ℝ) ^ k * X.mass.toReal) * C := by
    intro ω C hC
    calc |S₀ ω| ≤ X.mass.toReal * ((Λ : ℝ) ^ k * C) :=
          le_of_tendsto' (hS₀ ω).abs fun n => hXη n ω C hC
      _ = ((Λ : ℝ) ^ k * X.mass.toReal) * C := by ring
  -- 8. `S₀` is a current `S` with `M(S) ≤ Λ^k M(X)`.
  obtain ⟨S, hSS₀, hSm⟩ := Submission.dph_lpf_current_of_bounded_functional m' k univ S₀
    ((Λ : ℝ) ^ k * X.mass.toReal) hadd hsmul hS₀b
  have hS : ∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O →
      X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
      (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
      ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (ηj n : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x)) →
        Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω)) := by
    intro Gj O L hO hXO hGj hGjd hGju ω ηj hηj
    rw [hSS₀ ω]
    exact hconv Gj O L hO hXO hGj hGjd hGju ω ηj hηj
  refine ⟨S, hS, fun S' hS' => ?_, ?_, ?_⟩
  · -- 10. Uniqueness: test `S'` against the reference sequence and `η n ω`.
    ext ω
    exact tendsto_nhds_unique (hS' Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu ω _ (hηc0 ω))
      (hS Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu ω _ (hηc0 ω))
  · -- 8. `ofReal (Λ^k M(X)) = Λ^k M(X)`, as `M(X) < ∞`.
    refine hSm.trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (NNReal.coe_nonneg Λ),
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXm.ne]
  · -- 11. Support, from the characterization of `S` along the reference sequence.
    exact Submission.dph_lpfex_support_subset_closure_image m m' k X S G Gs
      (fun n => (hGs n).continuous) (hGsu.mono hXO₀) (hS Gs O₀ Λ hO₀ hXO₀ hGs hGsd' hGsu)

/-- Part (II) of the Lipschitz push-forward: if `S` is the Lipschitz push-forward of `X`, with
`M(X), M(∂X) < ∞`, then `∂S` is that of `∂X`.  Part (I) applied to `∂X` gives a push-forward `S_∂`
of `∂X`.  For a reference sequence `Gₙ` of (RS) on `(spt X)_{r/2}` and forms `θₙ` compatible with
`(Gₙ, φ)` near `spt X`, `dθₙ` is compatible with `(Gₙ, dφ)` since `d` commutes with pull-back, so
`S_∂(φ) = lim ∂X(θₙ) = lim X(dθₙ) = S(dφ) = ∂S(φ)`. -/
theorem Submission.dph_lpf_boundary :
    (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r →
      IsClosed F → LipschitzOnWith Λ G (thickening r F) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) →
      ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧
        (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧
        TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧
        ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) →
    (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m')
      (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ →
      (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X →
        Y.boundary.mass < ∞) →
      0 < r → LipschitzOnWith Λ G (thickening r X.support) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) →
      ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k,
        (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
          (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
          (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
          ∀ (ω : TestFormOn (univ : Set (Eucl m')) k)
            (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
            (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
              (ηj n : DifferentialForm (Eucl m) k) x =
                ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                  (fderiv ℝ (Gj n) x)) →
            Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧
        (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k,
          (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
            (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
            (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
            ∀ (ω : TestFormOn (univ : Set (Eucl m')) k)
              (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
              (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
                (ηj n : DifferentialForm (Eucl m) k) x =
                  ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                    (fderiv ℝ (Gj n) x)) →
              Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧
        S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support)) →
    (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1))
      (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ)
      (S : GeometricCurrentOn (univ : Set (Eucl m')) (j + 1)),
      X.mass < ∞ → X.boundary.mass < ∞ → 0 < r → LipschitzOnWith Λ G (thickening r X.support) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1))
          (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) (j + 1)),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) (j + 1)) x =
              ((ω : DifferentialForm (Eucl m') (j + 1)) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O →
        X.boundary.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) j)
          (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) j),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.boundary.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) j) x =
              ((ω : DifferentialForm (Eucl m') j) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X.boundary (ηj n)) atTop (𝓝 (S.boundary ω)))) := by
  intro hRS hI m m' j X G Λ r S _ hXbm hr hLip hprop hS Gj O L hO hXO hGj hL hGjG ω ηj hη
  -- 1. `spt ∂X ⊆ spt X`; supports of currents on `univ` are closed.
  have hsub : X.boundary.support ⊆ X.support := Submission.iwl_cr_support_lemmas.1 m j univ X
  have hcl : ∀ {k : ℕ} (Z : GeometricCurrentOn (univ : Set (Eucl m)) k), IsClosed Z.support :=
    fun Z => isClosed_univ.sdiff Z.isOpen_zeroRegion
  -- 2. Part (I) applied to `∂X` (`∂∂X = 0` has mass `0`) gives a push-forward `Sb` of `∂X`.
  obtain ⟨Sb, hSb, -⟩ := hI m m' j X.boundary G Λ r hXbm (by
      intro j' Y hj hY
      subst hj
      obtain rfl := eq_of_heq hY
      rw [GeometricCurrentOn.boundary_boundary]
      refine lt_of_le_of_lt (sSup_le ?_) ENNReal.zero_lt_top
      rintro _ ⟨φ, -, rfl⟩
      simp) hr (hLip.mono (thickening_subset_of_subset r hsub)) fun K hK => by
    have h := (hprop K hK).inter_right (hcl X.boundary)
    rwa [inter_assoc, inter_eq_right.2 hsub] at h
  -- It remains to identify `Sb ω` with `∂S ω = S (dω)`.
  suffices key : Sb ω = S.boundary ω by
    rw [← key]
    exact hSb Gj O L hO hXO hGj hL hGjG ω ηj hη
  -- 3. A reference sequence `Gn` for `F = spt X` on `O₀ = (spt X)_{r/2}`, and forms `θ n`
  -- compatible with `(Gn n, ω)` near `spt X` whenever `Gn n` is proper on `spt X`.
  obtain ⟨Gn, hGns, hGnd, hGnu, hGnp⟩ := hRS m m' G Λ r X.support hr (hcl X) hLip hprop
  have hXO₀ : X.support ⊆ thickening (r / 2) X.support := self_subset_thickening (half_pos hr) _
  have hθ : ∀ n, ∃ θ : TestFormOn (univ : Set (Eucl m)) j,
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gn n ⁻¹' K ∩ X.support)) →
      ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        (θ : DifferentialForm (Eucl m) j) x =
          ((ω : DifferentialForm (Eucl m') j) (Gn n x)).compContinuousLinearMap
            (fderiv ℝ (Gn n) x) := by
    intro n
    by_cases hp : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gn n ⁻¹' K ∩ X.support)
    · obtain ⟨θ, -, N, hN, hXN, -, -, hθN, -⟩ := Submission.iwl_sp_exists_compatible_testForm
        m m' j univ univ X.support (Gn n) isOpen_univ (subset_univ _) (hGns n)
        (fun K hK _ => hp K hK) ω
      exact ⟨θ, fun _ => ⟨N, hN, hXN, hθN⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose θ hθ using hθ
  -- 4. `∂X (θ n) → Sb ω`.
  have h1 : Tendsto (fun n => X.boundary (θ n)) atTop (𝓝 (Sb ω)) :=
    hSb Gn (thickening (r / 2) X.support) Λ isOpen_thickening (hsub.trans hXO₀) hGns
      (Eventually.of_forall hGnd) hGnu ω θ (hGnp.mono fun n hn => by
        obtain ⟨N, hN, hXN, hθN⟩ := hθ n hn
        exact ⟨N, hN, hsub.trans hXN, hθN⟩)
  -- 5–6. `dθ n` is compatible with `(Gn n, dω)` near `spt X` (`d` commutes with pull-back), so
  -- `X (dθ n) → S (dω)`.
  have h2 : Tendsto (fun n => X (exteriorDerivativeTestOn univ j (θ n))) atTop
      (𝓝 (S (exteriorDerivativeTestOn univ j ω))) :=
    hS Gn (thickening (r / 2) X.support) Λ isOpen_thickening hXO₀ hGns
      (Eventually.of_forall hGnd) hGnu (exteriorDerivativeTestOn univ j ω)
      (fun n => exteriorDerivativeTestOn univ j (θ n)) (hGnp.mono fun n hn => by
        obtain ⟨N, hN, hXN, hθN⟩ := hθ n hn
        refine ⟨N, hN, hXN, fun x hx => ?_⟩
        have hev : (θ n : DifferentialForm (Eucl m) j) =ᶠ[𝓝 x] fun y =>
            ((ω : DifferentialForm (Eucl m') j) (Gn n y)).compContinuousLinearMap
              (fderiv ℝ (Gn n) y) :=
          eventually_of_mem (hN.mem_nhds hx) hθN
        change extDeriv (θ n : DifferentialForm (Eucl m) j) x =
          (extDeriv (ω : DifferentialForm (Eucl m') j) (Gn n x)).compContinuousLinearMap
            (fderiv ℝ (Gn n) x)
        rw [hev.extDeriv_eq]
        exact extDeriv_pullback ((ω.property.1.1.differentiable (by simp)).differentiableAt)
          (hGns n).contDiffAt (by simp))
  -- 7. `∂X (θ n) = X (dθ n)`, so the two limits agree.
  exact tendsto_nhds_unique h1 h2

/-- Linearity of the Lipschitz push-forward in the current (Part (III)).  With
`F = spt X ∪ spt X₁ ⊇ spt X₂`, one reference sequence `G_n` for `F` (with `O = F_{r/2}`, `L = Λ`)
and one sequence `η_n`, compatible with `(G_n, ω)` near `F` once `G_n` is proper on `F`, are
admissible for all three push-forwards; so `X₂(η_n) = a X(η_n) + a₁ X₁(η_n)` tends both to
`S₂(ω)` and to `a S(ω) + a₁ S₁(ω)`. -/
theorem Submission.dph_lpf_linearity :
    (∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (F : Set (Eucl m)), 0 < r →
      IsClosed F → LipschitzOnWith Λ G (thickening r F) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ F)) →
      ∃ Gj : ℕ → Eucl m → Eucl m', (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) ∧
        (∀ n, ∀ x ∈ thickening (r / 2) F, ‖fderiv ℝ (Gj n) x‖ ≤ Λ) ∧
        TendstoUniformlyOn Gj G atTop (thickening (r / 2) F) ∧
        ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ F)) →
    (∀ (m m' k : ℕ) (X X₁ X₂ : GeometricCurrentOn (univ : Set (Eucl m)) k)
      (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ)
      (S S₁ S₂ : GeometricCurrentOn (univ : Set (Eucl m')) k) (a a₁ : ℝ),
      0 < r → LipschitzOnWith Λ G (thickening r (X.support ∪ X₁.support)) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ (X.support ∪ X₁.support))) →
      (∀ ω, X₂ ω = a * X ω + a₁ * X₁ ω) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) k) x =
              ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₁.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₁.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) k) x =
              ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X₁ (ηj n)) atTop (𝓝 (S₁ ω))) →
      (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₂.support ⊆ O →
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) →
        (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O →
        ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₂.support ⊆ N ∧ ∀ x ∈ N,
            (ηj n : DifferentialForm (Eucl m) k) x =
              ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
                (fderiv ℝ (Gj n) x)) →
          Tendsto (fun n => X₂ (ηj n)) atTop (𝓝 (S₂ ω))) →
      ∀ ω, S₂ ω = a * S ω + a₁ * S₁ ω) := by
  intro hRS m m' k X X₁ X₂ G Λ r S S₁ S₂ a a₁ hr hLip hprop hX₂ hS hS₁ hS₂ ω
  -- 1. `F = spt X ∪ spt X₁` is closed (supports in `univ` are closed) and contains `spt X₂`.
  have hFc : IsClosed (X.support ∪ X₁.support) :=
    (isClosed_univ.sdiff X.isOpen_zeroRegion).union (isClosed_univ.sdiff X₁.isOpen_zeroRegion)
  have hX₂F : X₂.support ⊆ X.support ∪ X₁.support :=
    Submission.iwl_cr_support_lemmas.2.2 m k univ isOpen_univ X X₁ X₂ a a₁ hX₂
  -- 2. One reference sequence `G_n`, admissible on the open `O = F_{r/2} ⊇ F` with `L = Λ`.
  obtain ⟨Gj, hGs, hGd, hGu, hGp⟩ := hRS m m' G Λ r _ hr hFc hLip hprop
  have hO : IsOpen (thickening (r / 2) (X.support ∪ X₁.support)) := isOpen_thickening
  have hFO : X.support ∪ X₁.support ⊆ thickening (r / 2) (X.support ∪ X₁.support) :=
    self_subset_thickening (half_pos hr) _
  have hdb : ∀ᶠ n in atTop, ∀ x ∈ thickening (r / 2) (X.support ∪ X₁.support),
      ‖fderiv ℝ (Gj n) x‖ ≤ (Λ : ℝ) :=
    Eventually.of_forall hGd
  -- 3. Test forms `η_n` compatible with `(G_n, ω)` near `F` whenever `G_n` is proper on `F`
  -- (the cut-off pull-back), and `η_n = 0` otherwise.
  have hη : ∀ n, ∃ η : TestFormOn (univ : Set (Eucl m)) k,
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ (X.support ∪ X₁.support))) →
      ∃ N : Set (Eucl m), IsOpen N ∧ X.support ∪ X₁.support ⊆ N ∧ ∀ x ∈ N,
        (η : DifferentialForm (Eucl m) k) x =
          ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
            (fderiv ℝ (Gj n) x) := by
    intro n
    by_cases hpn : ∀ K : Set (Eucl m'), IsCompact K →
        IsCompact (Gj n ⁻¹' K ∩ (X.support ∪ X₁.support))
    · obtain ⟨η, _, N, hN, hFN, _, _, hηN, _⟩ :=
        Submission.iwl_sp_exists_compatible_testForm m m' k univ univ _ (Gj n) isOpen_univ
          (subset_univ _) (hGs n) (fun K hK _ => hpn K hK) ω
      exact ⟨η, fun _ => ⟨N, hN, hFN, hηN⟩⟩
    · exact ⟨0, fun h => absurd h hpn⟩
  choose ηj hηj using hη
  have hcomp : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ∪ X₁.support ⊆ N ∧
      ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x =
        ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
          (fderiv ℝ (Gj n) x) :=
    hGp.mono fun n hn => hηj n hn
  -- 4. The three push-forward limits; `X₂(η_n) = a X(η_n) + a₁ X₁(η_n)` and uniqueness of limits.
  have h₀ := hS Gj _ Λ hO (subset_union_left.trans hFO) hGs hdb hGu ω ηj
    (hcomp.mono fun n ⟨N, hN, hFN, hηN⟩ => ⟨N, hN, subset_union_left.trans hFN, hηN⟩)
  have h₁ := hS₁ Gj _ Λ hO (subset_union_right.trans hFO) hGs hdb hGu ω ηj
    (hcomp.mono fun n ⟨N, hN, hFN, hηN⟩ => ⟨N, hN, subset_union_right.trans hFN, hηN⟩)
  have h₂ := hS₂ Gj _ Λ hO (hX₂F.trans hFO) hGs hdb hGu ω ηj
    (hcomp.mono fun n ⟨N, hN, hFN, hηN⟩ => ⟨N, hN, hX₂F.trans hFN, hηN⟩)
  exact tendsto_nhds_unique h₂
    (((h₀.const_mul a).add (h₁.const_mul a₁)).congr fun n => (hX₂ (ηj n)).symm)
/-- Locality of currents: test forms that agree on an open neighbourhood `N` of `spt T` have the
same value, since `ψ - φ` vanishes on `N`, so its support lies in the closed set `Nᶜ`, which misses
`spt T`. -/
theorem Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (ψ φ : TestFormOn U n)
      (N : Set (Eucl P)), IsOpen N → T.support ⊆ N →
      (∀ x ∈ N, (ψ : DifferentialForm (Eucl P) n) x = (φ : DifferentialForm (Eucl P) n) x) →
      T ψ = T φ := by
  intro P n U T ψ φ N hN hTN hψφ
  -- `ψ - φ` vanishes on the open set `N`, so `tsupport (ψ - φ) ⊆ Nᶜ`.
  have hsupp : tsupport ((ψ - φ : TestFormOn U n) : DifferentialForm (Eucl P) n) ⊆ Nᶜ := by
    refine closure_minimal ?_ hN.isClosed_compl
    intro x hx hxN
    apply hx
    rw [Submodule.coe_sub, Pi.sub_apply, hψφ x hxN, sub_self]
  -- `Nᶜ` misses `spt T ⊆ N`, so `T (ψ - φ) = 0`.
  have hzero : T (ψ - φ) = 0 :=
    Submission.isoperimetric_apply_eq_zero_of_disjoint_support P n U T (ψ - φ)
      (Set.disjoint_of_subset_left hsupp (Set.disjoint_compl_left_iff_subset.2 hTN))
  have hsub : T.toCurrent (ψ - φ) = T.toCurrent ψ - T.toCurrent φ := map_sub T.toCurrent ψ φ
  change T.toCurrent ψ = T.toCurrent φ
  rw [← sub_eq_zero, ← hsub]
  exact hzero

/-- Locality of an interval product: if `Z η = ∫₀¹ X (φ s) ds` for the slices
`φ s x = η(s, x)(e₀, ι ·)` of every `η`, then `Z η = Z η'` whenever `η = η'` on an open
`N ⊇ [0, 1] × spt X`, since for `s ∈ [0, 1]` the slices of `η` and `η'` agree on the open
neighbourhood `j_s⁻¹ N` of `spt X`, where `j_s x = (s, x)`, so locality of `X` makes the two
integrands agree on `[0, 1]`. -/
theorem Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl :
    ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q)
      (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (q + 1)),
      (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (q + 1))
        (φ : ℝ → TestFormOn (univ : Set (Eucl m)) q),
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin q → Eucl m),
          (φ s : DifferentialForm (Eucl m) q) x v =
            (η : DifferentialForm (Eucl (m + 1)) (q + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
      ∀ (η η' : TestFormOn (univ : Set (Eucl (m + 1))) (q + 1)) (N : Set (Eucl (m + 1))),
        IsOpen N →
        {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
          (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N →
        (∀ y ∈ N, (η : DifferentialForm (Eucl (m + 1)) (q + 1)) y =
          (η' : DifferentialForm (Eucl (m + 1)) (q + 1)) y) →
        Z η = Z η' := by
  intro m q X Z hZ η η' N hN hcyl hηη'
  -- Slice families `φ s x = η(s, x)(e₀, ι ·)` and `φ' s x = η'(s, x)(e₀, ι ·)`, and the
  -- product characterization of `Z`.
  obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm m q η
  obtain ⟨φ', -, hφ'⟩ := Submission.iwl_cr_ci_slice_testForm m q η'
  rw [hZ η φ fun s _ => hφ s, hZ η' φ' fun s _ => hφ' s]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  -- The slice map `j_s x = (s, x)` is continuous and sends `spt X` into the cylinder, so
  -- `j_s⁻¹ N` is an open neighbourhood of `spt X` on which `φ s = φ' s`.
  have hj : Continuous fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
      (continuous_const.finCons (EuclideanSpace.equiv (Fin m) ℝ).continuous)
  refine Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support m q univ X (φ s) (φ' s) _
    (hN.preimage hj) (fun x hx => hcyl ?_) fun x hx => ?_
  · simp only [mem_ofPred_eq, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero,
      Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨hs, hx⟩
  · ext v
    rw [hφ, hφ', hηη' _ hx]
/-- Horizontal slices of a compatible form: for `j_s(x) = (s, x)`, the slice `θ_s = j_s^# θ` is a
test form on `ℝ^m` with `θ_s(x)(v) = θ(s, x)((0, v₁), …, (0, v_q))`, and `θ_s = (G ∘ j_s)^# ω`
at every `x` with `(s, x) ∈ N` whenever `θ = G^# ω` on `N` (chain rule). -/
theorem Submission.dph_sh_slice_compatible_testForm :
    ∀ (m m' q : ℕ) (G : Eucl (m + 1) → Eucl m') (ω : DifferentialForm (Eucl m') q)
      (θ : TestFormOn (univ : Set (Eucl (m + 1))) q) (N : Set (Eucl (m + 1))) (s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G →
      (∀ y ∈ N, (θ : DifferentialForm (Eucl (m + 1)) q) y =
        (ω (G y)).compContinuousLinearMap (fderiv ℝ G y)) →
      ∃ θs : TestFormOn (univ : Set (Eucl m)) q,
        (∀ (x : Eucl m) (v : Fin q → Eucl m), (θs : DifferentialForm (Eucl m) q) x v =
          (θ : DifferentialForm (Eucl (m + 1)) q)
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
        ∀ x : Eucl m, (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ N →
          (θs : DifferentialForm (Eucl m) q) x =
            (ω ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap
              (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x) := by
  intro m m' q G ω θ N s hG hθN
  -- 1. `j_s x = (s, x)` has derivative `L v = (0, v)` everywhere, so it is `C^∞`.
  let L : Eucl m →L[ℝ] Eucl (m + 1) :=
    ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm : (Fin (m + 1) → ℝ) →L[ℝ] Eucl (m + 1)).comp
      ((0 : Eucl m →L[ℝ] ℝ).finCons
        (EuclideanSpace.equiv (Fin m) ℝ : Eucl m →L[ℝ] (Fin m → ℝ)))
  let j : Eucl m → Eucl (m + 1) := fun x =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))
  have hjd : ∀ x, HasFDerivAt j L x := fun x =>
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.hasFDerivAt.comp x
      ((hasFDerivAt_const s x).finCons (EuclideanSpace.equiv (Fin m) ℝ).hasFDerivAt)
  have hjs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) j := by
    refine contDiff_infty_iff_fderiv.2 ⟨fun x => (hjd x).differentiableAt, ?_⟩
    rw [show fderiv ℝ j = fun _ => L from funext fun x => (hjd x).fderiv]
    exact contDiff_const
  -- 2. `j_s` is proper: the continuous map `tl (y₀, y') = y'` is a left inverse.
  let tl : Eucl (m + 1) → Eucl m := fun y =>
    (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))
  have htl : Continuous tl :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp <| continuous_pi fun i : Fin m =>
      (continuous_apply i.succ).comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).continuous
  have htlj : ∀ x, tl (j x) = x := fun x => by
    simp only [tl, j, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  have hprop : ∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ univ →
      IsCompact (j ⁻¹' K ∩ univ) := fun K hK _ => by
    rw [inter_univ]
    exact (hK.image htl).of_isClosed_subset (hK.isClosed.preimage hjs.continuous)
      fun x hx => ⟨j x, hx, htlj x⟩
  -- 3. The slice `θ_s = j_s^# θ ∈ 𝒟^q(ℝ^m)`; it equals `θ(j_s x) ∘ L` everywhere.
  obtain ⟨θs, -, N₀, -, hN₀, -, -, hθsN, -⟩ :=
    Submission.iwl_sp_exists_compatible_testForm m (m + 1) q univ univ univ j isOpen_univ
      subset_rfl hjs hprop θ
  have hθs : ∀ x, (θs : DifferentialForm (Eucl m) q) x =
      ((θ : DifferentialForm (Eucl (m + 1)) q) (j x)).compContinuousLinearMap L := fun x => by
    rw [hθsN x (hN₀ (mem_univ x)), (hjd x).fderiv]
  refine ⟨θs, fun x v => by rw [hθs x]; rfl, fun x hx => ?_⟩
  -- 4. Chain rule `D(G ∘ j_s)(x) = DG(j_s x) ∘ L`, and `θ = G^# ω` at `j_s x ∈ N`.
  have hGj : HasFDerivAt (fun x : Eucl m => G (j x)) ((fderiv ℝ G (j x)).comp L) x :=
    ((hG.differentiable (by simp)) (j x)).hasFDerivAt.comp x (hjd x)
  rw [hθs x, hGj.fderiv, hθN (j x) hx]
  ext v
  rfl
/-- Exterior differentiation commutes with pull-back, locally (Simon Ch. 6, §1, (1.14)): if `θ`
agrees with the pull-back `G^#ω` of a `C^∞` form `ω` by a `C^∞` map `G` on an open set `N`, then
`dθ = G^#(dω)` on `N`.  `dθ(x)` only depends on the germ of `θ` at `x`. -/
theorem Submission.dph_sh_extDeriv_compatible : ∀ (P Q j : ℕ) (G : Eucl P → Eucl Q) (ω : DifferentialForm (Eucl Q) j) (θ : DifferentialForm (Eucl P) j) (N : Set (Eucl P)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → IsOpen N → (∀ x ∈ N, θ x = (ω (G x)).compContinuousLinearMap (fderiv ℝ G x)) → ∀ x ∈ N, exteriorDerivative θ x = ((exteriorDerivative ω) (G x)).compContinuousLinearMap (fderiv ℝ G x) := by
  intro P Q j G ω θ N hG hω hN hθ x hx
  -- `θ` agrees with the pull-back `G^#ω` on the open neighbourhood `N` of `x`.
  have hloc : θ =ᶠ[𝓝 x] fun y => (ω (G y)).compContinuousLinearMap (fderiv ℝ G y) :=
    Filter.eventually_of_mem (hN.mem_nhds hx) hθ
  -- Locality of `d`, then `d` commutes with pull-back by the `C^∞` map `G`.
  exact hloc.extDeriv_eq.trans
    (extDeriv_pullback ((hω.differentiable (by simp)).differentiableAt) hG.contDiffAt (by simp))
/-- Homogeneity of the Euclidean coefficient norm (Simon Ch. 6, 1.15, 2.4–2.5):
`|c α| = |c| |α|`.  Every coefficient of `c • α` on an increasing tuple of basis vectors is
`c` times that of `α`, so each squared coefficient gains the factor `c²`; pull `c²` out of the
finite sum and use `√(c² s) = √(c²) √s = |c| √s`. -/
theorem Submission.fiw_tb_ext_covectorNorm_smul : ∀ (P q : ℕ) (c : ℝ) (α : Covector (Eucl P) q), covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
  intro P q c α
  unfold covectorEuclideanNorm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs
  · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
  · simp
/-- A linear functional `T₀` on `𝒟^q(U)` with `|T₀(ω)| ≤ B · sup_x |ω(x)|` (Euclidean coefficient
norm) is a current of mass at most `B`: test-form convergence makes `sup_x |ω_j(x)| → 0`, since
`|α| ≤ √(P^q) ‖α‖` (conjunct (C3) of `Submission.dph_iprod_slice_covector_norm_le`), and every
mass-admissible `ω` has `T(ω) ≤ |T₀(ω)| ≤ B`. -/
theorem Submission.dph_iprod_current_of_bound :
    ∀ (P q : ℕ) (U : Set (Eucl P)) (T₀ : TestFormOn U q →ₗ[ℝ] ℝ) (B : ℝ), 0 ≤ B →
      (∀ (ω : TestFormOn U q) (C : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) q) x) ≤ C) →
          |T₀ ω| ≤ B * C) →
      ∃ T : GeometricCurrentOn U q, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal B := by
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  intro P q U T₀ B hB hbd
  -- (C3): the coefficient norm is at most `c = √(P^q)` times the operator norm.
  have hC3 : ∀ α : Covector (Eucl P) q,
      covectorEuclideanNorm α ≤ Real.sqrt ((P : ℝ) ^ q) * ‖α‖ :=
    fun α => hSN.2.2 P q α
  set c := Real.sqrt ((P : ℝ) ^ q)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  refine ⟨⟨T₀, ?_⟩, fun ω => rfl, ?_⟩
  · -- Sequential continuity at `0`: the order-`0` uniform convergence on the common compact
    -- support `K` gives `|ω_j(x)| ≤ c δ` for all `x` and large `j`, so `|T₀(ω_j)| ≤ B c δ < ε`.
    intro ωs hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := hunif 0
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ > 0, B * c * δ < ε := by
      refine ⟨ε / (B * c + 1), by positivity, ?_⟩
      have hpos : 0 < B * c + 1 := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hpos]
      nlinarith [mul_nonneg hB hc0]
    rw [Metric.tendstoUniformlyOn_iff] at h0
    filter_upwards [h0 δ hδ] with n hn
    have hpt : ∀ x, covectorEuclideanNorm ((ωs n : DifferentialForm (Eucl P) q) x) ≤ c * δ := by
      intro x
      by_cases hx : x ∈ K
      · have h1 := hn x hx
        rw [dist_comm, dist_eq_norm] at h1
        have h2 : iteratedFDeriv ℝ 0
            (((0 : TestFormOn U q) : DifferentialForm (Eucl P) q)) x = 0 := by
          simp
        rw [h2, sub_zero, norm_iteratedFDeriv_zero] at h1
        calc covectorEuclideanNorm ((ωs n : DifferentialForm (Eucl P) q) x)
            ≤ c * ‖(ωs n : DifferentialForm (Eucl P) q) x‖ := hC3 _
          _ ≤ c * δ := mul_le_mul_of_nonneg_left h1.le hc0
      · -- Off `K`, `ω_j` vanishes.
        have h3 : (ωs n : DifferentialForm (Eucl P) q) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp n h))
        rw [h3, covectorEuclideanNorm_zero]
        positivity
    have h4 := hbd (ωs n) (c * δ) hpt
    rw [Real.dist_eq, sub_zero]
    calc |T₀ (ωs n)| ≤ B * (c * δ) := h4
      _ = B * c * δ := by ring
      _ < ε := hδε
  · -- Mass: a mass-admissible `ω` has `|ω(x)| ≤ 1` everywhere, so `T(ω) ≤ |T₀(ω)| ≤ B`.
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    have h5 := hbd ω 1 hω.2
    have h6 : T₀ ω ≤ |T₀ ω| := le_abs_self _
    show T₀ ω ≤ B
    linarith

/-- **Continuity along slices** (step 3 of the interval product).  Let `X` be a current in `ℝ^m`
with `M(X) < ∞`; write `(s, x) ∈ ℝ^{m+1}` for `Fin.cons s x`, `ι(w) = (0, w)`, `e₀ = (1, 0)`.
(D1) If `X ∈ 𝒟_k`, `η ∈ 𝒟^{k+1}(ℝ^{m+1})` and `φ(s)(x)(v) = η(s, x)(e₀, ι ∘ v)` for
`s ∈ [0, 1]`, then `s ↦ X(φ(s))` is continuous on `[0, 1]` and `|X(φ(s))| ≤ M(X) · sup |η|`.
(D2) If `X ∈ 𝒟_q`, `ω` is a continuous compactly supported `q`-form on `ℝ^{m+1}` and
`Ψ(s)(x)(v) = ω(s, x)(ι ∘ v)` for all `s`, then `s ↦ X(Ψ(s))` is continuous and
`|X(Ψ(s))| ≤ M(X) · sup |ω|`.  By the mass bound, `X` is `M(X)`-Lipschitz for the sup of the
Euclidean covector norm; slices are bounded by the sliced covector
(`dph_iprod_slice_covector_norm_le`), and `η`, `ω` are uniformly continuous. -/
theorem Submission.dph_iprod_slice_continuity : (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → ContinuousOn (fun s => X (φ s)) (Icc (0 : ℝ) 1) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm ((η : DifferentialForm (Eucl (m + 1)) (k + 1)) y) ≤ C) → ∀ s ∈ Icc (0 : ℝ) 1, |X (φ s)| ≤ X.mass.toReal * C) ∧ (∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ → ∀ (ω : DifferentialForm (Eucl (m + 1)) q) (Ψ : ℝ → TestFormOn (univ : Set (Eucl m)) q), Continuous ω → HasCompactSupport ω → (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v = ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Continuous (fun s => X (Ψ s)) ∧ ∀ C : ℝ, (∀ y, covectorEuclideanNorm (ω y) ≤ C) → ∀ s : ℝ, |X (Ψ s)| ≤ X.mass.toReal * C) := by
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  -- (MB) If `|ω(x)| ≤ C` for all `x`, then `|X(ω)| ≤ M(X) · C` (mass bound with `U = W = univ`).
  have hMB : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ →
      ∀ (ω : TestFormOn (univ : Set (Eucl m)) q) (C : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl m) q) x) ≤ C) →
          |X ω| ≤ X.mass.toReal * C := by
    intro m q X hX ω C hC
    refine Submission.cmb_abs_apply_le_of_massOn_le m q univ univ X ω X.mass.toReal C
      ENNReal.toReal_nonneg ?_ (subset_univ _) hC
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  -- If `F(s) - F(s₀)` is uniformly small for close `s, s₀ ∈ S`, then `s ↦ X(F(s))` is
  -- continuous on `S`, by (MB) and linearity of `X`.
  have hcont : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q), X.mass < ∞ →
      ∀ (F : ℝ → TestFormOn (univ : Set (Eucl m)) q) (S : Set ℝ),
        (∀ ε > 0, ∃ δ > 0, ∀ s ∈ S, ∀ s₀ ∈ S, |s - s₀| < δ → ∀ x,
          covectorEuclideanNorm (((F s - F s₀ : TestFormOn (univ : Set (Eucl m)) q) :
            DifferentialForm (Eucl m) q) x) ≤ ε) →
        ContinuousOn (fun s => X (F s)) S := by
    intro m q X hX F S hF s₀ hs₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hB : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hB1 : 0 < X.mass.toReal + 1 := by linarith
    obtain ⟨δ, hδ, hFδ⟩ := hF (ε / (X.mass.toReal + 1)) (div_pos hε hB1)
    refine ⟨δ, hδ, fun {s} hs hss₀ => ?_⟩
    rw [Real.dist_eq] at hss₀ ⊢
    have hsub : X (F s - F s₀) = X (F s) - X (F s₀) := map_sub X.toCurrent _ _
    rw [← hsub]
    calc |X (F s - F s₀)| ≤ X.mass.toReal * (ε / (X.mass.toReal + 1)) :=
          hMB m q X hX _ _ (hFδ s hs s₀ hs₀ hss₀)
      _ < (X.mass.toReal + 1) * (ε / (X.mass.toReal + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) (div_pos hε hB1)
      _ = ε := by field_simp
  -- `dist ((s, x), (s₀, x)) = |s - s₀|`: only the `0`-th coordinates differ.
  have hdist : ∀ (m : ℕ) (s s₀ : ℝ) (x : Eucl m),
      dist ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))) = |s - s₀| := by
    intro m s s₀ x
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_succ]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hfrac : ∀ c ε : ℝ, 0 ≤ c → 0 < ε → c * (ε / (c + 1)) ≤ ε := by
    intro c ε hc hε
    have hc1 : 0 < c + 1 := by linarith
    calc c * (ε / (c + 1)) ≤ (c + 1) * (ε / (c + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_pos hε hc1).le
      _ = ε := by field_simp
  refine ⟨?_, ?_⟩
  · -- (D1) `dt`-slices of `η`: (C1) and (C3).
    intro m k X hX η φ hφ
    have hC1 := hSN.1 m k
    have hC3 := hSN.2.2 (m + 1) (k + 1)
    have hc0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ (k + 1)) := Real.sqrt_nonneg _
    have huc : UniformContinuous (η : DifferentialForm (Eucl (m + 1)) (k + 1)) :=
      η.property.1.2.uniformContinuous_of_continuous η.property.1.1.continuous
    refine ⟨hcont m k X hX φ (Icc 0 1) fun ε hε => ?_, fun C hC s hs =>
      hMB m k X hX (φ s) C fun x => (hC1 _ _ fun v => hφ s hs x v).trans (hC _)⟩
    obtain ⟨δ, hδ, hηδ⟩ := Metric.uniformContinuous_iff.mp huc
      (ε / (Real.sqrt (((m + 1 : ℕ) : ℝ) ^ (k + 1)) + 1)) (by positivity)
    refine ⟨δ, hδ, fun s hs s₀ hs₀ hss₀ x => ?_⟩
    -- `(φ s - φ s₀)(x)` is the `dt`-slice of `η(s, x) - η(s₀, x)`.
    have h1 := hC1 ((η : DifferentialForm (Eucl (m + 1)) (k + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
      (η : DifferentialForm (Eucl (m + 1)) (k + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
      (((φ s - φ s₀ : TestFormOn (univ : Set (Eucl m)) k) : DifferentialForm (Eucl m) k) x) (by
        intro v
        show ((φ s : DifferentialForm (Eucl m) k) - (φ s₀ : DifferentialForm (Eucl m) k)) x v = _
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hφ s hs x v, hφ s₀ hs₀ x v]
        rfl)
    refine h1.trans ((hC3 _).trans ((mul_le_mul_of_nonneg_left ?_ hc0).trans (hfrac _ ε hc0 hε)))
    rw [← dist_eq_norm]
    exact (hηδ (by rwa [hdist])).le
  · -- (D2) horizontal slices of `ω`: (C2) and (C3).
    intro m q X hX ω Ψ hωc hωs hΨ
    have hC2 := hSN.2.1 m q
    have hC3 := hSN.2.2 (m + 1) q
    have hc0 : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) ^ q) := Real.sqrt_nonneg _
    have huc : UniformContinuous ω := hωs.uniformContinuous_of_continuous hωc
    refine ⟨continuousOn_univ.mp (hcont m q X hX Ψ univ fun ε hε => ?_), fun C hC s =>
      hMB m q X hX (Ψ s) C fun x => (hC2 _ _ fun v => hΨ s x v).trans (hC _)⟩
    obtain ⟨δ, hδ, hωδ⟩ := Metric.uniformContinuous_iff.mp huc
      (ε / (Real.sqrt (((m + 1 : ℕ) : ℝ) ^ q) + 1)) (by positivity)
    refine ⟨δ, hδ, fun s _ s₀ _ hss₀ x => ?_⟩
    -- `(Ψ s - Ψ s₀)(x)` is the horizontal slice of `ω(s, x) - ω(s₀, x)`.
    have h1 := hC2
      (ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) -
        ω ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))
      (((Ψ s - Ψ s₀ : TestFormOn (univ : Set (Eucl m)) q) : DifferentialForm (Eucl m) q) x) (by
        intro v
        show ((Ψ s : DifferentialForm (Eucl m) q) - (Ψ s₀ : DifferentialForm (Eucl m) q)) x v = _
        rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hΨ s x v, hΨ s₀ x v]
        rfl)
    refine h1.trans ((hC3 _).trans ((mul_le_mul_of_nonneg_left ?_ hc0).trans (hfrac _ ε hc0 hε)))
    rw [← dist_eq_norm]
    exact (hωδ (by rwa [hdist])).le
/-- The `dt`-slice of `dψ` (`e₀ = EuclideanSpace.single 0 1`, `ι(w) = (0, w)`, `(s, x)` the point
of `ℝ^{m+1}` with first coordinate `s`): for a `0`-form `ψ`, `dψ(y)(e₀) = Dψ(y)(e₀)`; for a
`(j+1)`-form `ψ` whose slice at `s` is `φ(x)(w) = ψ(s, x)(e₀, ι ∘ w)`,
`dψ(s, x)(e₀, ι ∘ v) = Dψ(s, x)(e₀)(ι ∘ v) − dφ(x)(v)`.
Both exterior derivatives are alternating sums of directional derivatives; by the chain rule
along `x ↦ (s, x)` (derivative `ι`), the `l`-th term of `dφ(x)(v)` is the `(l+1)`-st term of
`dψ(s, x)(e₀, ι ∘ v)` with the opposite sign, and the `0`-th term is `Dψ(s, x)(e₀)(ι ∘ v)`. -/
theorem Submission.dph_iprod_slice_extDeriv :
    (∀ (m : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0) (y : Eucl (m + 1))
      (v : Fin 0 → Eucl m),
      ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) 0 ψ :
        TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) : DifferentialForm (Eucl (m + 1)) (0 + 1))
        y (Fin.cons (EuclideanSpace.single 0 1) fun i =>
          (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) =
      fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) 0) y (EuclideanSpace.single 0 1)
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
    (∀ (m j : ℕ) (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1))
      (φ : TestFormOn (univ : Set (Eucl m)) j) (s : ℝ),
      (∀ (x : Eucl m) (w : Fin j → Eucl m), (φ : DifferentialForm (Eucl m) j) x w =
        (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (Fin.cons (EuclideanSpace.single 0 1) fun i =>
            (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (w i))))) →
      ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
        ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) (j + 1) ψ :
          TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) :
            DifferentialForm (Eucl (m + 1)) (j + 1 + 1))
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (Fin.cons (EuclideanSpace.single 0 1) fun i =>
            (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (EuclideanSpace.single 0 1)
          (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) -
        ((exteriorDerivativeTestOn (univ : Set (Eucl m)) j φ :
          TestFormOn (univ : Set (Eucl m)) (j + 1)) : DifferentialForm (Eucl m) (j + 1)) x v) := by
  refine ⟨?_, ?_⟩
  · -- `dψ(y)(e₀)` is the one-term alternating sum `Dψ(y)(e₀)`.
    intro m ψ y v
    have hd : DifferentiableAt ℝ (ψ : DifferentialForm (Eucl (m + 1)) 0) y :=
      ψ.property.1.1.differentiable (by simp) y
    show exteriorDerivative (ψ : DifferentialForm (Eucl (m + 1)) 0) y _ = _
    rw [exteriorDerivative_apply hd, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
    rw [fderiv_continuousAlternatingMap_apply_const_apply hd]
    congr 1
  · intro m j ψ φ s hφ x v
    -- `ι(w) = (0, w)` is a continuous linear map `ℝ^m → ℝ^{m+1}`.
    obtain ⟨ι, hιv⟩ : ∃ ι : Eucl m →L[ℝ] Eucl (m + 1), ∀ w : Eucl m,
        ι w = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ w)) := by
      let L : (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
        { toFun := fun w => Fin.cons 0 w
          map_add' := by
            intro a b; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
          map_smul' := by
            intro c a; funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
      exact ⟨(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
        LinearMap.toContinuousLinearMap L ∘L
          (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap, fun w => rfl⟩
    -- The slice `x ↦ (s, x) = (s, 0) + ι x` has derivative `ι`.
    have hslice : HasFDerivAt (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ι x := by
      have heq : (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) =
          fun x => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s 0) + ι x := by
        funext x
        rw [hιv]
        apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).injective
        simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [heq]
      exact ι.hasFDerivAt.const_add _
    have hd : DifferentiableAt ℝ (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) :=
      ψ.property.1.1.differentiable (by simp) _
    have hdφ : DifferentiableAt ℝ (φ : DifferentialForm (Eucl m) j) x :=
      φ.property.1.1.differentiable (by simp) x
    -- Chain rule: `D(φ(·)(w))(x) = D(ψ(·)(e₀, ι ∘ w))(s, x) ∘ ι`.
    have hchain : ∀ w : Fin j → Eucl m,
        fderiv ℝ (fun x' => (φ : DifferentialForm (Eucl m) j) x' w) x =
          (fderiv ℝ (fun z => (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) z
            (Fin.cons (EuclideanSpace.single 0 1) fun i => ι (w i)))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))).comp ι := by
      intro w
      have hfun : (fun x' => (φ : DifferentialForm (Eucl m) j) x' w) =
          (fun z => (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) z
            (Fin.cons (EuclideanSpace.single 0 1) fun i => ι (w i))) ∘
          (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) := by
        funext x'
        simp only [Function.comp_apply, hφ x' w, hιv]
      rw [hfun]
      exact ((hd.continuousAlternatingMap_apply_const _).hasFDerivAt.comp x hslice).fderiv
    show exteriorDerivative (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) _ _ =
      _ - exteriorDerivative (φ : DifferentialForm (Eucl m) j) x v
    -- Split off the `0`-th term of `dψ`; the remaining terms are those of `-dφ`.
    rw [exteriorDerivative_apply hd, exteriorDerivative_apply hdφ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero,
      Fin.tail_cons]
    rw [fderiv_continuousAlternatingMap_apply_const_apply hd, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hchain, ContinuousLinearMap.comp_apply,
      fderiv_continuousAlternatingMap_apply_const_apply hd,
      fderiv_continuousAlternatingMap_apply_const_apply hd]
    -- Removing the `(l+1)`-st entry of `(e₀, ι ∘ v)` gives `(e₀, ι ∘ removeNth l v)`.
    have hrm : Fin.removeNth l.succ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (m + 1))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) :
            Fin (j + 1 + 1) → Eucl (m + 1)) =
        (Fin.cons (EuclideanSpace.single 0 1 : Eucl (m + 1)) (fun i => ι (Fin.removeNth l v i)) :
          Fin (j + 1) → Eucl (m + 1)) := by
      show (Fin.cons (EuclideanSpace.single 0 1 : Eucl (m + 1))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) :
            Fin (j + 1 + 1) → Eucl (m + 1)) ∘ (l.succ).succAbove = _
      rw [Fin.cons_comp_succ_succAbove]
      congr 1
      funext i
      simp only [Fin.removeNth, hιv]
    rw [hrm, Fin.cons_succ, hιv, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]

/-- Fundamental theorem of calculus along horizontal slices: for `M(X) < ∞`, the slices
`Ψ(s) = ψ(s, ·)` and `Ψ'(s) = ∂ₛψ(s, ·)` of `ψ ∈ 𝒟^q(ℝ^{m+1})` (tested on horizontal vectors)
satisfy `d/ds X(Ψ(s)) = X(Ψ'(s))`, with `s ↦ X(Ψ'(s))` continuous and
`∫₀¹ X(Ψ'(s)) ds = X(Ψ(1)) - X(Ψ(0))`. -/
theorem Submission.dph_iprod_horizontal_ftc :
    ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q)
      (ψ : TestFormOn (univ : Set (Eucl (m + 1))) q) (Ψ Ψ' : ℝ → TestFormOn (univ : Set (Eucl m)) q),
      X.mass < ∞ →
      (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ s : DifferentialForm (Eucl m) q) x v =
        (ψ : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      (∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v =
        fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q)
          ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
          (EuclideanSpace.single 0 1)
          (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      Continuous (fun s => X (Ψ' s)) ∧ (∀ s : ℝ, HasDerivAt (fun t => X (Ψ t)) (X (Ψ' s)) s) ∧
        ∫ s in (0 : ℝ)..1, X (Ψ' s) = X (Ψ 1) - X (Ψ 0) := by
  have hMB := Submission.cmb_abs_apply_le_of_massOn_le
  have hSN := Submission.dph_iprod_slice_covector_norm_le
  have hC := Submission.dph_iprod_slice_continuity
  intro m q X ψ Ψ Ψ' hX hΨ hΨ'
  -- Mass estimate `|X(ω)| ≤ M(X) · sup |ω|`, from `M(X) < ∞`.
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  have hmb : X.massOn univ ≤ ENNReal.ofReal X.mass.toReal := by
    rw [ENNReal.ofReal_toReal hX.ne]
    exact le_rfl
  -- Restriction to horizontal vectors and comparison with the operator norm.
  have hC2 := hSN.2.1 m q
  have hC3 := hSN.2.2 (m + 1) q
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.sqrt ((((m + 1 : ℕ)) : ℝ) ^ q) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ Real.sqrt_nonneg _
  -- The form `ψ' = Dψ(·)(e₀)` is continuous with compact support.
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Eucl (m + 1), e₀ = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'eq⟩ : ∃ ψ' : Eucl (m + 1) → Covector (Eucl (m + 1)) q,
      ψ' = fun y => fderiv ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) y e₀ := ⟨_, rfl⟩
  have hψd : Differentiable ℝ (ψ : DifferentialForm (Eucl (m + 1)) q) :=
    ψ.property.1.1.differentiable (by simp)
  have hψ'c : Continuous ψ' := by
    rw [hψ'eq]
    exact (ψ.property.1.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ's : HasCompactSupport ψ' := by
    rw [hψ'eq]
    exact (ψ.property.1.2.fderiv ℝ).comp_left
      (g := fun L : Eucl (m + 1) →L[ℝ] Covector (Eucl (m + 1)) q => L e₀) rfl
  have hΨ'2 : ∀ (s : ℝ) (x : Eucl m) (v : Fin q → Eucl m), (Ψ' s : DifferentialForm (Eucl m) q) x v =
      ψ' ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
        (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
          (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
    intro s x v
    rw [hΨ' s x v, hψ'eq, he₀]
  -- Continuity of `s ↦ X(Ψ'(s))`.
  have hcont := (hC.2 m q X hX ψ' Ψ' hψ'c hψ's hΨ'2).1
  -- Lines in the time direction: `cons(s + τ, x) = cons(s, x) + τ e₀`.
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
  -- Differentiability: `|X(Ψ(s+h)) - X(Ψ(s)) - h X(Ψ'(s))| ≤ ε |h|` for small `h`, by the mean
  -- value inequality and the uniform continuity of `ψ'`.
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
          rw [hψ'eq]
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
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he₀, PiLp.norm_single, norm_one, mul_one,
          Real.norm_eq_abs]
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
  -- Fundamental theorem of calculus.
  refine ⟨hcont, hderiv, ?_⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcont.intervalIntegrable 0 1)

/-- Contraction bound for the Euclidean coefficient norm: if the `k`-covector `δ` is the
contraction `γ(w, ·)` of a `(k+1)`-covector `γ` with `w ∈ ℝ^p`, then `|δ| ≤ √(k+1) ‖w‖ |γ|`.
Expand `w = ∑_b w_b e_b` in the first slot, so `δ(e_J) = ∑_b w_b γ(e_{(b, J)})`; Cauchy–Schwarz
gives `δ(e_J)² ≤ ‖w‖² ∑_b γ(e_{(b, J)})²`.  Summing over all `J` and reindexing `(b, J) ↦ I`
yields `k! |δ|² ≤ ‖w‖² (k+1)! |γ|²` by the all-tuples identity; cancel `k!` and take roots. -/
theorem Submission.dph_sh_ib_covectorEuclideanNorm_contract_le :
    ∀ (p k : ℕ) (γ : Covector (Eucl p) (k + 1)) (w : Eucl p) (δ : Covector (Eucl p) k),
      (∀ u : Fin k → Eucl p, δ u = γ (Fin.cons w u)) →
        covectorEuclideanNorm δ ≤ Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ := by
  intro p k γ w δ hδ
  set e := EuclideanSpace.basisFun (Fin p) ℝ with he
  -- Linearity in the first slot: `δ(e_J) = ∑_b w_b γ(e_{(b, J)})`.
  have hexp : ∀ J : Fin k → Fin p, δ (fun i => e (J i)) =
      ∑ b : Fin p, w b * γ (fun i => e ((Fin.cons b J : Fin (k + 1) → Fin p) i)) := by
    intro J
    have hw : ∑ b : Fin p, w b • e b = w := by
      simpa only [he, EuclideanSpace.basisFun_repr] using e.sum_repr w
    have hc : δ (fun i => e (J i)) = γ.curryLeft w (fun i => e (J i)) := hδ _
    rw [hc]
    conv_lhs => rw [← hw]
    rw [map_sum, ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  -- Cauchy–Schwarz in `b`.
  have hcs : ∀ J : Fin k → Fin p, δ (fun i => e (J i)) ^ 2 ≤
      ‖w‖ ^ 2 * ∑ b : Fin p, γ (fun i => e ((Fin.cons b J : Fin (k + 1) → Fin p) i)) ^ 2 := by
    intro J
    rw [hexp J, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- `(b, J) ↦ Fin.cons b J` enumerates all index maps `Fin (k + 1) → Fin p`.
  have hre : ∑ J : Fin k → Fin p, ∑ b : Fin p,
      γ (fun i => e ((Fin.cons b J : Fin (k + 1) → Fin p) i)) ^ 2 =
        ∑ I : Fin (k + 1) → Fin p, γ (fun i => e (I i)) ^ 2 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type', ← (Fin.consEquiv fun _ => Fin p).sum_comp]
    rfl
  -- `k! |δ|² ≤ ‖w‖² (k+1)! |γ|²`.
  have hsum : (k.factorial : ℝ) * covectorEuclideanNorm δ ^ 2 ≤
      ‖w‖ ^ 2 * (((k + 1).factorial : ℝ) * covectorEuclideanNorm γ ^ 2) := by
    rw [← Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul p k δ,
      ← Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul p (k + 1) γ, ← hre, Finset.mul_sum]
    exact Finset.sum_le_sum fun J _ => hcs J
  -- Cancel `k! > 0`, using `(k+1)! = (k+1) k!`.
  have hsq : covectorEuclideanNorm δ ^ 2 ≤
      ((k : ℝ) + 1) * ‖w‖ ^ 2 * covectorEuclideanNorm γ ^ 2 := by
    have hpos : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    refine le_of_mul_le_mul_left ?_ hpos
    calc (k.factorial : ℝ) * covectorEuclideanNorm δ ^ 2
        ≤ ‖w‖ ^ 2 * (((k + 1).factorial : ℝ) * covectorEuclideanNorm γ ^ 2) := hsum
      _ = (k.factorial : ℝ) * (((k : ℝ) + 1) * ‖w‖ ^ 2 * covectorEuclideanNorm γ ^ 2) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
        ring
  -- Take nonnegative square roots.
  have hnn : 0 ≤ Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg w)) (covectorEuclideanNorm_nonneg γ)
  refine (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg δ) hnn two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  exact hsq

/-- Interior-product bound for the Euclidean coefficient norm: if
`β(v₁, …, v_k) = a γ(w, T v₁, …, T v_k)` for a `(k+1)`-covector `γ` on `ℝ^{m′}`, `w ∈ ℝ^{m′}` and
`T : ℝ^m → ℝ^{m′}`, then `|β| ≤ |a| √(k+1) ‖w‖ ‖T‖^k |γ|`.  With the contraction
`δ := γ(w, ·) = γ.curryLeft w` we have `β = a • T^#δ`, so homogeneity
`Submission.fiw_tb_ext_covectorNorm_smul`, the pull-back bound
`Submission.iwl_sp_covectorEuclideanNorm_pullback_le` and the contraction bound
`Submission.dph_sh_ib_covectorEuclideanNorm_contract_le` give
`|β| = |a| |T^#δ| ≤ |a| ‖T‖^k |δ| ≤ |a| ‖T‖^k √(k+1) ‖w‖ |γ|`. -/
theorem Submission.dph_sh_covectorEuclideanNorm_interior_le : ∀ (m m' k : ℕ) (γ : Covector (Eucl m') (k + 1)) (w : Eucl m') (T : Eucl m →L[ℝ] Eucl m') (a : ℝ) (β : Covector (Eucl m) k), (∀ v : Fin k → Eucl m, β v = a * γ (Fin.cons w (fun i => T (v i)))) → covectorEuclideanNorm β ≤ |a| * Real.sqrt ((k : ℝ) + 1) * ‖w‖ * ‖T‖ ^ k * covectorEuclideanNorm γ := by
  intro m m' k γ w T a β hβ
  -- The contraction `δ := γ(w, ·)`: `δ u = γ (Fin.cons w u)` holds by definition.
  have hδ := Submission.dph_sh_ib_covectorEuclideanNorm_contract_le m' k γ w (γ.curryLeft w)
    fun u => ContinuousAlternatingMap.curryLeft_apply_apply γ w u
  -- `β = a • T^#δ`: both sides send `v` to `a γ(w, T v₁, …, T v_k)`.
  have hβδ : β = a • (γ.curryLeft w).compContinuousLinearMap T :=
    ContinuousAlternatingMap.ext fun v => hβ v
  -- Homogeneity, then the pull-back bound for `T` and the contraction bound for `δ`.
  rw [hβδ, Submission.fiw_tb_ext_covectorNorm_smul]
  calc |a| * covectorEuclideanNorm ((γ.curryLeft w).compContinuousLinearMap T)
      ≤ |a| * (‖T‖ ^ k * covectorEuclideanNorm (γ.curryLeft w)) :=
        mul_le_mul_of_nonneg_left
          (Submission.iwl_sp_covectorEuclideanNorm_pullback_le m m' k T (γ.curryLeft w))
          (abs_nonneg a)
    _ ≤ |a| * (‖T‖ ^ k * (Real.sqrt ((k : ℝ) + 1) * ‖w‖ * covectorEuclideanNorm γ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hδ (pow_nonneg (norm_nonneg T) k)) (abs_nonneg a)
    _ = |a| * Real.sqrt ((k : ℝ) + 1) * ‖w‖ * ‖T‖ ^ k * covectorEuclideanNorm γ := by ring

/-- Simon Ch. 6, 2.27 (p. 140), affine homotopy estimate: let `Z = [[0,1]] × X` (characterized
through `dt`-slices) and `G(t, x) = F₀(x) + t (F₁(x) - F₀(x))`, with `|F₁ - F₀| ≤ s` and
`|DF₀|, |DF₁| ≤ L` on an open `O ⊇ spt X`.  If `η'` equals `G^#ψ` near `[0,1] × spt X`, then
`|Z(η')| ≤ c s L^k B C` whenever `M(X) ≤ B` and `|ψ| ≤ C`, with `c = √(k+1)`. -/
theorem Submission.dph_sh_affine_estimate :
    ∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k)
      (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m')
      (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B →
      (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
        (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
          (φ s : DifferentialForm (Eucl m) k) x v =
            (η : DifferentialForm (Eucl (m + 1)) (k + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ →
      IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) →
      (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) →
      (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) →
      ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ)
        (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)),
        (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) →
        (∃ N : Set (Eucl (m + 1)), IsOpen N ∧
          {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
            (EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧
          ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x =
            ((ψ : DifferentialForm (Eucl m') (k + 1))
              ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                  (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
                  (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
                    F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)))))
                x)).compContinuousLinearMap
              (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                  (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
                  (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
                    F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
                      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) →
        |Z η'| ≤ c * s * L ^ k * B * C := by
  intro m m' k
  refine ⟨Real.sqrt ((k : ℝ) + 1), Real.sqrt_nonneg _, ?_⟩
  intro X Z F₀ F₁ O s L B hs hL hB hXB hZ hF₀ hF₁ hO hXO hdist hDF₀ hDF₁ hprop ψ C η' hψC hη'
  obtain ⟨N', hN', hAN', hη'N'⟩ := hη'
  -- `spt X = ℝ^m \ zeroRegion X` is closed.
  have hXcl : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  -- 1. `G` is smooth, `DG(s₀, x) e₀ = F₁ x - F₀ x`, `DG(s₀, x) (0, v) = (1 - s₀) DF₀(x) v +
  -- s₀ DF₁(x) v`, and `G` is proper on the cylinder `cyl(spt X) = [0,1] × spt X`.
  obtain ⟨hG, hGd⟩ :=
    Submission.dph_sh_ae_affine_homotopy_contDiff_fderiv m m' F₀ F₁ hF₀ hF₁
  have hGprop := Submission.dph_sh_ae_affine_homotopy_isCompact_preimage_cyl m m' F₀ F₁
    X.support s hF₀.continuous hF₁.continuous hXcl (fun x hx => hdist x (hXO hx)) hprop
  set G : Eucl (m + 1) → Eucl m' := fun y : Eucl (m + 1) =>
    F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) +
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) •
        (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) -
          F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))
  -- The tail projection `tl` is continuous, and `tl(s₀, x) = x`.
  have htail : Continuous (Fin.tail : (Fin (m + 1) → ℝ) → Fin m → ℝ) :=
    continuous_pi fun i => continuous_apply i.succ
  have htl : Continuous fun y : Eucl (m + 1) =>
      (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp
      (htail.comp (EuclideanSpace.equiv (Fin (m + 1)) ℝ).continuous)
  have htl_cons : ∀ (s₀ : ℝ) (x : Eucl m), (EuclideanSpace.equiv (Fin m) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x))))) = x := by
    intro s₀ x
    rw [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  -- 2. Cut-off: `η = ζ G^#ψ` with `0 ≤ ζ ≤ 1`, `η = G^#ψ` near `cyl(spt X)` and
  -- `spt η ⊆ tl⁻¹(O)`; it is also a test form `η₁` on all of `ℝ^{m+1}`.
  obtain ⟨η, ζ, N, hN, hAN, hζ, hη, hηN, -⟩ :=
    Submission.iwl_sp_exists_compatible_testForm (m + 1) m' (k + 1)
      ((fun y : Eucl (m + 1) => (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) ⁻¹' O) univ
      {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
        (EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support}
      G (hO.preimage htl) (fun y hy => hXO hy.2) hG (fun K hK _ => hGprop K hK) ψ
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1),
      (η₁ : DifferentialForm (Eucl (m + 1)) (k + 1)) = η :=
    ⟨⟨η, η.2.1, subset_univ _⟩, rfl⟩
  -- 3. `Z(η') = Z(η₁)`: both forms equal `G^#ψ` on the open set `N' ∩ N ⊇ cyl(spt X)`.
  have hZη : Z η' = Z η₁ :=
    Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl m k X Z hZ η' η₁ (N' ∩ N) (hN'.inter hN)
      (subset_inter hAN' hAN) fun y hy => by rw [hη₁, hη'N' y hy.1, hηN y hy.2]
  -- 4. The `dt`-slices `φ` of `η₁`, and `Z(η₁) = ∫₀¹ X(φ(s₀)) ds₀`.
  obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm m k η₁
  have hZφ : Z η₁ = ∫ s₀ in (0 : ℝ)..1, X (φ s₀) := hZ η₁ φ fun s₀ _ x v => hφ s₀ x v
  have hC : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hψC 0)
  -- 5. Pointwise bound `|φ(s₀)(x)| ≤ √(k+1) s L^k C` for `s₀ ∈ [0,1]`.
  have hbound : ∀ s₀ ∈ Icc (0 : ℝ) 1, ∀ x, covectorEuclideanNorm
      ((φ s₀ : DifferentialForm (Eucl m) k) x) ≤ Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C := by
    intro s₀ hs₀ x
    have hφx := hφ s₀ x
    obtain ⟨hGe₀, hGι₀⟩ := hGd s₀ x
    have htl₀ := htl_cons s₀ x
    generalize (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (Fin.cons s₀ (EuclideanSpace.equiv (Fin m) ℝ x)) = y at hφx hGe₀ hGι₀ htl₀
    rw [hη₁] at hφx
    by_cases hx : x ∈ O
    · -- Over `O`: `φ(s₀)(x)(v) = ζ(y) ψ(G y)(F₁ x - F₀ x, T v₁, …, T v_k)`, where
      -- `T = (1 - s₀) DF₀(x) + s₀ DF₁(x)` has `‖T‖ ≤ L`.
      have hβ : ∀ v : Fin k → Eucl m, (φ s₀ : DifferentialForm (Eucl m) k) x v =
          ζ y * (ψ : DifferentialForm (Eucl m') (k + 1)) (G y) (Fin.cons (F₁ x - F₀ x)
            fun i => ((1 - s₀) • fderiv ℝ F₀ x + s₀ • fderiv ℝ F₁ x) (v i)) := by
        intro v
        rw [hφx, hη y, ContinuousAlternatingMap.smul_apply,
          ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul, Fin.comp_cons,
          hGe₀]
        congr 3
        funext i
        exact hGι₀ (v i)
      have hT : ‖(1 - s₀) • fderiv ℝ F₀ x + s₀ • fderiv ℝ F₁ x‖ ≤ L := by
        calc _ ≤ ‖(1 - s₀) • fderiv ℝ F₀ x‖ + ‖s₀ • fderiv ℝ F₁ x‖ := norm_add_le _ _
          _ = (1 - s₀) * ‖fderiv ℝ F₀ x‖ + s₀ * ‖fderiv ℝ F₁ x‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hs₀.2),
              Real.norm_of_nonneg hs₀.1]
          _ ≤ (1 - s₀) * L + s₀ * L :=
            add_le_add (mul_le_mul_of_nonneg_left (hDF₀ x hx) (sub_nonneg.2 hs₀.2))
              (mul_le_mul_of_nonneg_left (hDF₁ x hx) hs₀.1)
          _ = L := by ring
      have hw : ‖F₁ x - F₀ x‖ ≤ s := by
        rw [← dist_eq_norm]
        exact hdist x hx
      have hζy : |ζ y| ≤ 1 := by
        rw [abs_of_nonneg (hζ y).1]
        exact (hζ y).2
      have hψy := covectorEuclideanNorm_nonneg ((ψ : DifferentialForm (Eucl m') (k + 1)) (G y))
      calc covectorEuclideanNorm ((φ s₀ : DifferentialForm (Eucl m) k) x)
          ≤ |ζ y| * Real.sqrt ((k : ℝ) + 1) * ‖F₁ x - F₀ x‖ *
              ‖(1 - s₀) • fderiv ℝ F₀ x + s₀ • fderiv ℝ F₁ x‖ ^ k *
              covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) (G y)) :=
            Submission.dph_sh_covectorEuclideanNorm_interior_le m m' k _ _ _ _ _ hβ
        _ ≤ 1 * Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C := by
            gcongr
            exact hψC (G y)
        _ = Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C := by ring
    · -- Off `O`: `y ∉ tl⁻¹(O) ⊇ spt η`, so `φ(s₀)(x) = 0`.
      have hy : y ∉ tsupport (η : DifferentialForm (Eucl (m + 1)) (k + 1)) := by
        intro hy
        have hyO : (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ O := η.2.2 hy
        rw [htl₀] at hyO
        exact hx hyO
      have h0 : (φ s₀ : DifferentialForm (Eucl m) k) x = 0 := by
        ext v
        simp only [hφx, image_eq_zero_of_notMem_tsupport hy, ContinuousAlternatingMap.coe_zero,
          Pi.zero_apply]
      rw [h0, covectorEuclideanNorm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs) (pow_nonneg hL k)) hC
  -- 6. Mass bound for each slice, then the interval-integral bound.
  have hint : ‖∫ s₀ in (0 : ℝ)..1, X (φ s₀)‖ ≤
      B * (Real.sqrt ((k : ℝ) + 1) * s * L ^ k * C) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s₀ hs₀ => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs₀
    rw [Real.norm_eq_abs]
    exact Submission.cmb_abs_apply_le_of_massOn_le m k univ univ X (φ s₀) B _ hB hXB
      (subset_univ _) (hbound s₀ (Ioc_subset_Icc_self hs₀))
  rw [hZη, hZφ, ← Real.norm_eq_abs]
  calc _ ≤ _ := hint
    _ = Real.sqrt ((k : ℝ) + 1) * s * L ^ k * B * C := by
      rw [sub_zero, abs_one, mul_one]
      ring
/-- The product `[[0, 1]] × X` of a finite-mass current `X` on `ℝ^m`: with chosen `dt`-slices
`φ^η s x = η(s, x)(e₀, ι ·)`, the functional `η ↦ ∫₀¹ X(φ^η s) ds` is linear and bounded by
`M(X) · sup |η|`, hence a current `Z` with `M(Z) ≤ M(X)`; the integral does not depend on the
slice family, which gives the characterization and uniqueness; and `Z` vanishes on every ball
missing the closed cylinder `[0, 1] × spt X`, since there every slice `φ^η s` misses `spt X`. -/
theorem Submission.dph_iprod_exists :
    ∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ →
      ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1),
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
            (φ s : DifferentialForm (Eucl m) k) x v =
              (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          Z η = ∫ s in (0 : ℝ)..1, X (φ s)) ∧
        (∀ Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1),
          (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
              (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
              (φ s : DifferentialForm (Eucl m) k) x v =
                (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z' η = ∫ s in (0 : ℝ)..1, X (φ s)) → Z' = Z) ∧
        Z.mass ≤ X.mass ∧
        Z.support ⊆ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
          (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈
            X.support} := by
  have hSF := Submission.iwl_cr_ci_slice_testForm
  have hVS := Submission.isoperimetric_apply_eq_zero_of_disjoint_support
  have hCC := Submission.dph_iprod_current_of_bound
  have hC := Submission.dph_iprod_slice_continuity
  intro m k X hX
  -- A chosen slice family `φ η` of every `η`.
  choose φ hφc hφ using fun η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1) => hSF m k η
  have hB0 : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
  -- Any slice family of `η` on `[0, 1]` agrees with `φ η` there, so has the same integral.
  have hcongr : ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
      (ψ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
        (ψ s : DifferentialForm (Eucl m) k) x v =
          (η : DifferentialForm (Eucl (m + 1)) (k + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
      ∫ s in (0 : ℝ)..1, X (ψ s) = ∫ s in (0 : ℝ)..1, X (φ η s) := by
    intro η ψ hψ
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have : ψ s = φ η s := by
      apply Subtype.ext; funext x; ext v; rw [hψ s hs x v, hφ η s x v]
    simp only [this]
  have hint : ∀ η, IntervalIntegrable (fun s => X (φ η s)) MeasureTheory.volume 0 1 := by
    intro η
    exact ((hC.1 m k X hX η (φ η) (fun s _ x v => hφ η s x v)).1).intervalIntegrable_of_Icc
      zero_le_one
  -- The linear functional `T₀ η = ∫₀¹ X(φ η s) ds`.
  let T₀ : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun η => ∫ s in (0 : ℝ)..1, X (φ η s)
      map_add' := by
        intro η η'
        have h := hcongr (η + η') (fun s => φ η s + φ η' s) (by
          intro s _ x v
          show ((φ η s : DifferentialForm (Eucl m) k) +
            (φ η' s : DifferentialForm (Eucl m) k)) x v = _
          rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, hφ η s x v, hφ η' s x v]
          rfl)
        rw [← h]
        have : (fun s => X (φ η s + φ η' s)) = fun s => X (φ η s) + X (φ η' s) := by
          funext s; exact map_add X.toCurrent _ _
        rw [this, intervalIntegral.integral_add (hint η) (hint η')]
      map_smul' := by
        intro c η
        have h := hcongr (c • η) (fun s => c • φ η s) (by
          intro s _ x v
          show (c • (φ η s : DifferentialForm (Eucl m) k)) x v = _
          rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, hφ η s x v]
          rfl)
        rw [← h]
        have : (fun s => X (c • φ η s)) = fun s => c * X (φ η s) := by
          funext s; exact map_smul X.toCurrent c _
        rw [this, intervalIntegral.integral_const_mul]
        rfl }
  have hT₀ : ∀ η, T₀ η = ∫ s in (0 : ℝ)..1, X (φ η s) := fun η => rfl
  -- `|T₀ η| ≤ M(X) · C` whenever `|η| ≤ C` pointwise.
  have hbound : ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((η : DifferentialForm (Eucl (m + 1)) (k + 1)) y) ≤ C) →
      |T₀ η| ≤ X.mass.toReal * C := by
    intro η C hηC
    have hb := (hC.1 m k X hX η (φ η) (fun s _ x v => hφ η s x v)).2 C hηC
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := X.mass.toReal * C) (f := fun s => X (φ η s)) (by
        intro s hs
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs]
        exact hb s ⟨hs.1.le, hs.2⟩)
    rw [hT₀]
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using this
  obtain ⟨Z, hZ, hZm⟩ := hCC (m + 1) (k + 1) univ T₀ X.mass.toReal hB0 hbound
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro η ψ hψ
    rw [hZ η, hT₀, hcongr η ψ hψ]
  · intro Z' hZ'
    ext η
    rw [hZ' η (φ η) (fun s _ x v => hφ η s x v), hZ η, hT₀]
  · calc Z.mass ≤ ENNReal.ofReal X.mass.toReal := hZm
      _ = X.mass := ENNReal.ofReal_toReal hX.ne
  · -- A point off the closed cylinder `[0, 1] × spt X` has a ball around it missing the
    -- cylinder; `Z` vanishes there, so the point lies in the zero region of `Z`.
    intro y₀ hy₀
    by_contra hcyl
    have hsuppX : IsClosed X.support := by
      have : X.support = (X.zeroRegion)ᶜ := by
        ext y; simp [GeometricCurrentOn.support]
      rw [this]; exact X.isOpen_zeroRegion.isClosed_compl
    have hclosed : IsClosed {y : Eucl (m + 1) |
        EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
          (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} := by
      apply IsClosed.inter
      · exact isClosed_Icc.preimage (by fun_prop)
      · exact hsuppX.preimage (by fun_prop)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl y₀ hcyl
    have hvan : Z.VanishesOn (ball y₀ ρ) := by
      intro η hη
      rw [hZ η, hT₀]
      -- For `s ∈ [0, 1]`, the slice `φ η s` is supported in `{x | (s, x) ∈ tsupport η}`,
      -- which misses `spt X`.
      have h0 : ∀ s ∈ Set.uIcc (0 : ℝ) 1, X (φ η s) = 0 := by
        intro s hs
        rw [Set.uIcc_of_le zero_le_one] at hs
        apply hVS
        rw [Set.disjoint_left]
        intro x hx hxX
        have hsub : tsupport (φ η s : DifferentialForm (Eucl m) k) ⊆
            (fun x : Eucl m => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) ⁻¹'
              tsupport (η : DifferentialForm (Eucl (m + 1)) (k + 1)) := by
          apply closure_minimal _ ((isClosed_tsupport _).preimage (by fun_prop))
          intro x' hx'
          by_contra hn
          apply hx'
          ext v
          rw [hφ η s x' v, image_eq_zero_of_notMem_tsupport hn]
          rfl
        have h2 := hη (hsub hx)
        apply hball h2
        refine ⟨?_, ?_⟩
        · simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero]
          exact hs
        · simp only [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
            ContinuousLinearEquiv.symm_apply_apply]
          exact hxX
      rw [intervalIntegral.integral_congr h0]
      simp
    have hW : ball y₀ ρ ⊆ Z.zeroRegion := by
      intro y hy
      refine Set.mem_sUnion.mpr ⟨ball y₀ ρ, ⟨isOpen_ball, ?_, subset_univ _, hvan⟩, hy⟩
      exact (isCompact_closedBall y₀ ρ).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    exact hy₀.2 (hW (mem_ball_self hρ))

/-- Boundary of a current `Z` with the product characterization `ProdChar(X, Z)` of
`[[0,1]] × X`: `Z(η) = ∫₀¹ X(φ(s)) ds` whenever `φ(s)(x)(v) = η((s, x))(e₀, ι ∘ v)` on `[0,1]`.
With `ψᵢ(x)(v) = ψ((i, x))(ι ∘ v)` and `φ(s)(x)(v) = ψ((s, x))(e₀, ι ∘ v)`:
(II) `∂Z(ψ) = X(ψ₁) − X(ψ₀)` in degree `0`; (III) `∂Z(ψ) = X(ψ₁) − X(ψ₀) − ∫₀¹ ∂X(φ(s)) ds` in
positive degree; (N) `M(∂Z) ≤ 2 M(X) + M(∂X) < ∞` (no `M(∂X)` term in degree `0`). -/
theorem Submission.dph_iprod_boundary :
    (∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0)
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)), X.mass < ∞ →
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m),
              (φ s : DifferentialForm (Eucl m) 0) x v =
                (η : DifferentialForm (Eucl (m + 1)) (0 + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
        ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0)
          (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) 0),
          (∀ (x : Eucl m) (v : Fin 0 → Eucl m),
            (ψ₀ : DifferentialForm (Eucl m) 0) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) 0)
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          (∀ (x : Eucl m) (v : Fin 0 → Eucl m),
            (ψ₁ : DifferentialForm (Eucl m) 0) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) 0)
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          Z.boundary ψ = X ψ₁ - X ψ₀) ∧
    (∀ (m j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1))
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)), X.mass < ∞ →
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
              (φ s : DifferentialForm (Eucl m) (j + 1)) x v =
                (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
        ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1))
          (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) (j + 1))
          (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j),
          (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
            (ψ₀ : DifferentialForm (Eucl m) (j + 1)) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
            (ψ₁ : DifferentialForm (Eucl m) (j + 1)) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))
                (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m),
            (φ s : DifferentialForm (Eucl m) j) x v =
              (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          Z.boundary ψ = X ψ₁ - X ψ₀ - ∫ s in (0 : ℝ)..1, X.boundary (φ s)) ∧
    (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k)
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)), X.mass < ∞ →
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
              (φ s : DifferentialForm (Eucl m) k) x v =
                (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
        ((∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 →
            HEq Y X → Y.boundary.mass < ∞) →
          Z.boundary.mass < ∞)) := by
  have hSF := Submission.iwl_cr_ci_slice_testForm
  have hHS := Submission.dph_iprod_horizontal_slices
  have hC := Submission.dph_iprod_slice_continuity
  have hD := Submission.dph_iprod_slice_extDeriv
  have hF := Submission.dph_iprod_horizontal_ftc
  -- (N) uses (II) and (III): prove the conjunction in the form `A`, `B`, `A → B → C`.
  have key : ∀ {A B C : Prop}, A → B → (A → B → C) → A ∧ B ∧ C :=
    fun a b h => ⟨a, b, h a b⟩
  refine key ?_ ?_ ?_
  · -- (II): the `e₀`-derivative slices `Ψ'` are `dt`-slices of `dψ`, so
    -- `∂Z(ψ) = Z(dψ) = ∫₀¹ X(Ψ'(s)) ds = X(Ψ(1)) − X(Ψ(0))`.
    intro m X Z hX hZ ψ ψ₀ ψ₁ h₀ h₁
    obtain ⟨Ψ, Ψ', hΨ, hΨ'⟩ := hHS m 0 ψ
    have hftc := hF m 0 X ψ Ψ Ψ' hX hΨ hΨ'
    have hslice : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m),
        (Ψ' s : DifferentialForm (Eucl m) 0) x v =
          ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) 0 ψ :
              TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) :
            DifferentialForm (Eucl (m + 1)) (0 + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
      intro s _ x v
      rw [hΨ' s x v, hD.1 m ψ _ v]
    have e0 : ψ₀ = Ψ 0 := by
      apply Subtype.ext; funext x; ext v; rw [h₀ x v, hΨ 0 x v]
    have e1 : ψ₁ = Ψ 1 := by
      apply Subtype.ext; funext x; ext v; rw [h₁ x v, hΨ 1 x v]
    rw [GeometricCurrentOn.boundary_apply, hZ _ Ψ' hslice, hftc.2.2, e0, e1]
  · -- (III): `F(s) = Ψ'(s) − dφ(s)` are `dt`-slices of `dψ` on `[0,1]`, so
    -- `∂Z(ψ) = ∫₀¹ X(F(s)) ds = ∫₀¹ X(Ψ'(s)) ds − ∫₀¹ ∂X(φ(s)) ds`, both integrands being
    -- continuous on `[0,1]`.
    intro m j X Z hX hZ ψ ψ₀ ψ₁ φ h₀ h₁ hφ
    obtain ⟨Ψ, Ψ', hΨ, hΨ'⟩ := hHS m (j + 1) ψ
    have hftc := hF m (j + 1) X ψ Ψ Ψ' hX hΨ hΨ'
    let F : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1) :=
      fun s => Ψ' s - exteriorDerivativeTestOn univ j (φ s)
    have hslice : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
        (F s : DifferentialForm (Eucl m) (j + 1)) x v =
          ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) (j + 1) ψ :
              TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) :
            DifferentialForm (Eucl (m + 1)) (j + 1 + 1))
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i)))) := by
      intro s hs x v
      rw [hD.2 m j ψ (φ s) s (fun x w => hφ s hs x w) x v, ← hΨ' s x v]
      rfl
    have hXF : ∀ s, X (F s) = X (Ψ' s) - X.boundary (φ s) := fun s =>
      map_sub X.toCurrent (Ψ' s) (exteriorDerivativeTestOn univ j (φ s))
    have hcont := (hC.1 m (j + 1) X hX _ F hslice).1
    have hI₁ : IntervalIntegrable (fun s => X (Ψ' s)) volume 0 1 :=
      hftc.1.intervalIntegrable 0 1
    have hI₂ : IntervalIntegrable (fun s => X.boundary (φ s)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
      refine (hftc.1.continuousOn.sub hcont).congr fun s _ => ?_
      simp only [Pi.sub_apply, hXF s]
      ring
    have e0 : ψ₀ = Ψ 0 := by
      apply Subtype.ext; funext x; ext v; rw [h₀ x v, hΨ 0 x v]
    have e1 : ψ₁ = Ψ 1 := by
      apply Subtype.ext; funext x; ext v; rw [h₁ x v, hΨ 1 x v]
    rw [GeometricCurrentOn.boundary_apply, hZ _ F hslice]
    simp only [hXF]
    rw [intervalIntegral.integral_sub hI₁ hI₂, hftc.2.2, e0, e1]
  · -- (N): bound `∂Z(ψ)` uniformly over the mass-admissible `ψ` by (II), resp. (III), and the
    -- slice bounds `|X(Ψ(s))| ≤ M(X)`, `|∂X(φ(s))| ≤ M(∂X)`.
    intro hII hIII m k X Z hX hZ hN
    have hmass : ∀ A : ℝ, (∀ ψ ∈ massAdmissibleOn (univ : Set (Eucl (m + 1))) k univ,
        Z.boundary ψ ≤ A) → Z.boundary.mass < ∞ := by
      intro A hA
      have hle : Z.boundary.mass ≤ ENNReal.ofReal A := by
        apply sSup_le
        rintro _ ⟨ψ, hψ, rfl⟩
        exact ENNReal.ofReal_le_ofReal (hA ψ hψ)
      exact hle.trans_lt ENNReal.ofReal_lt_top
    cases k with
    | zero =>
      refine hmass (2 * X.mass.toReal) fun ψ hψ => ?_
      obtain ⟨Ψ, Ψ', hΨ, -⟩ := hHS m 0 ψ
      have hb := hII m X Z hX hZ ψ (Ψ 0) (Ψ 1) (hΨ 0) (hΨ 1)
      have hB := (hC.2 m 0 X hX (ψ : DifferentialForm (Eucl (m + 1)) 0) Ψ
        ψ.2.1.1.continuous ψ.2.1.2 hΨ).2 1 hψ.2
      have h0 := abs_le.mp (hB 0)
      have h1 := abs_le.mp (hB 1)
      rw [hb]
      linarith [h0.1, h1.2]
    | succ j =>
      have hXb : X.boundary.mass < ∞ := hN j X rfl HEq.rfl
      refine hmass (2 * X.mass.toReal + X.boundary.mass.toReal) fun ψ hψ => ?_
      obtain ⟨Ψ, Ψ', hΨ, -⟩ := hHS m (j + 1) ψ
      obtain ⟨φ, -, hφ⟩ := hSF m j ψ
      have hb := hIII m j X Z hX hZ ψ (Ψ 0) (Ψ 1) φ (hΨ 0) (hΨ 1) fun s _ => hφ s
      have hB := (hC.2 m (j + 1) X hX (ψ : DifferentialForm (Eucl (m + 1)) (j + 1)) Ψ
        ψ.2.1.1.continuous ψ.2.1.2 hΨ).2 1 hψ.2
      have hB' := (hC.1 m j X.boundary hXb ψ φ fun s _ => hφ s).2 1 hψ.2
      have hI : ‖∫ s in (0 : ℝ)..1, X.boundary (φ s)‖ ≤
          X.boundary.mass.toReal * 1 * |1 - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
        rw [uIoc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs]
        exact hB' s (Ioc_subset_Icc_self hs)
      rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one, mul_one] at hI
      have h0 := abs_le.mp (hB 0)
      have h1 := abs_le.mp (hB 1)
      have h2 := abs_le.mp hI
      rw [hb]
      linarith [h0.1, h1.2, h2.1]
/-- If `M ⊆ U` is `μ`-null on every open `W ⊂⊂ U` on which `T` vanishes, then `μ(M ∖ spt T) = 0`:
`M ∖ spt T` lies in the zero region (Simon 2.11), a countable union of such `W` (Lindelöf). -/
theorem Submission.lpf_rsn_null_diff_support_of_local_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0 := by
  intro P n U T M μ hMU hloc
  -- Countably many of the open sets whose union is `T.zeroRegion` already cover it.
  obtain ⟨S, hSc, hSsub, hSeq⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Eucl P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- As `M ⊆ U`, every point of `M ∖ spt T` lies in `T.zeroRegion = ⋃₀ S`.
  have hsub : M \ T.support ⊆ ⋃ W ∈ S, M ∩ W := by
    rintro x ⟨hxM, hxs⟩
    have hxZ : x ∈ ⋃₀ S := by
      rw [hSeq]
      by_contra hxZ
      exact hxs ⟨hMU hxM, hxZ⟩
    obtain ⟨W, hWS, hxW⟩ := hxZ
    exact mem_biUnion hWS ⟨hxM, hxW⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hSc).2 fun W hWS => ?_)
  obtain ⟨hWo, hWc, hWU, hWv⟩ := hSsub hWS
  exact hloc W hWo hWc hWU hWv
/-- Finitely many `n`-covectors separate `n`-vectors (Simon Ch. 6, §1; used for Lemma 3.9 to show
that a representation `τ(M, θ, ξ)` of `T` lives on `spt T` up to an `Hⁿ`-null set).  Evaluation on
tuples of standard basis vectors, `Φ(α)(r) = α(e_{r(1)}, …, e_{r(n)})`, embeds `Λⁿ(ℝ^P)` linearly
into `ℝ^(Fin n → Fin P)`, since a multilinear map is determined by its values on basis vectors.
So `Λⁿ(ℝ^P)` is finite-dimensional, and an `n`-vector vanishing on a basis `b₁, …, b_N` is zero. -/
theorem Submission.lpf_rsn_covector_separating_family : ∀ (P n : ℕ), ∃ (N : ℕ) (b : Fin N → Covector (Eucl P) n), ∀ w : NVector (Eucl P) n, (∀ i, w (b i) = 0) → w = 0 := by
  intro P n
  -- Step 1: evaluation on `n`-tuples of standard basis vectors of `ℝ^P` is linear.
  let e : Module.Basis (Fin P) ℝ (Eucl P) := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  let Φ : Covector (Eucl P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α r => α (fun i => e (r i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Step 2: `Φ` is injective, as a multilinear map is determined by its values on basis vectors.
  have hΦ : Function.Injective Φ := by
    intro α β h
    have hm : α.toContinuousMultilinearMap.toMultilinearMap =
        β.toContinuousMultilinearMap.toMultilinearMap :=
      Module.Basis.ext_multilinear (fun _ => e) (fun r => congrFun h r)
    ext v
    exact congrArg (fun m : MultilinearMap ℝ (fun _ : Fin n => Eucl P) ℝ => m v) hm
  -- Step 3: hence `Λⁿ(ℝ^P)` is finite-dimensional; take a basis `b₁, …, b_N`.
  have : FiniteDimensional ℝ (Covector (Eucl P) n) := FiniteDimensional.of_injective Φ hΦ
  let b := Module.finBasis ℝ (Covector (Eucl P) n)
  refine ⟨Module.finrank ℝ (Covector (Eucl P) n), b, ?_⟩
  -- Step 4: a linear functional vanishing on a basis is zero.
  intro w hw
  have hlin : (w : Covector (Eucl P) n →ₗ[ℝ] ℝ) = 0 := b.ext (fun i => by simpa using hw i)
  ext α
  simpa using congrArg (fun l : Covector (Eucl P) n →ₗ[ℝ] ℝ => l α) hlin
/-- If `M ⊆ U` is `μ`-null on every open `W ⊂⊂ U` on which `T` vanishes, then `μ(M ∖ spt T) = 0`:
`M ∖ spt T` lies in the zero region (Simon 2.11), a countable union of such `W` (Lindelöf). -/
theorem Submission.iwl_sp_sn_null_diff_support_of_local_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0 := by
  intro P n U T M μ hMU hloc
  -- As `M ⊆ U` and `spt T = U ∖ T.zeroRegion`, `M ∖ spt T ⊆ T.zeroRegion`.
  have hzero : M \ T.support ⊆ T.zeroRegion := by
    rintro x ⟨hxM, hxs⟩
    by_contra hxZ
    exact hxs ⟨hMU hxM, hxZ⟩
  -- Lindelöf: countably many of the open sets whose union is `T.zeroRegion` have the same union.
  obtain ⟨S, hSc, hSsub, hSeq⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Eucl P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  have hsub : M \ T.support ⊆ ⋃ W ∈ S, M ∩ W := by
    intro x hx
    have hxS : x ∈ ⋃₀ S := by
      rw [hSeq]
      exact hzero hx
    obtain ⟨W, hWS, hxW⟩ := hxS
    exact mem_biUnion hWS ⟨hx.1, hxW⟩
  -- Each `M ∩ W` with `W ∈ S` is `μ`-null, so their countable union is `μ`-null.
  refine measure_mono_null hsub ((measure_biUnion_null_iff hSc).2 fun W hWS => ?_)
  obtain ⟨hWo, hWc, hWU, hWv⟩ := hSsub hWS
  exact hloc W hWo hWc hWU hWv
/-- Finitely many `n`-covectors separate `n`-vectors (Simon Ch. 6, §1; used for Theorem 8.2 to
show that a representation `τ(M, θ, ξ)` of `T` lives on `spt T` up to an `Hⁿ`-null set).
Evaluation on tuples of standard basis vectors, `Φ(α)(r) = α(e_{r(1)}, …, e_{r(n)})`, embeds
`Λⁿ(ℝ^P)` linearly into `ℝ^(Fin n → Fin P)`, since a multilinear map is determined by its values
on basis vectors.  So `Λⁿ(ℝ^P)` is finite-dimensional, and an `n`-vector vanishing on a basis
`b₁, …, b_N` is zero. -/
theorem Submission.iwl_sp_sn_covector_separating_family : ∀ (P n : ℕ), ∃ (N : ℕ) (b : Fin N → Covector (Eucl P) n), ∀ w : NVector (Eucl P) n, (∀ i, w (b i) = 0) → w = 0 := by
  intro P n
  -- Step 1: evaluation on `n`-tuples of standard basis vectors of `ℝ^P` is linear.
  let e : Module.Basis (Fin P) ℝ (Eucl P) := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  let Φ : Covector (Eucl P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α r => α (fun i => e (r i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Step 2: `Φ` is injective, as a multilinear map is determined by its values on basis vectors.
  have hΦ : Function.Injective Φ := by
    intro α β h
    have hm : α.toContinuousMultilinearMap.toMultilinearMap =
        β.toContinuousMultilinearMap.toMultilinearMap :=
      Module.Basis.ext_multilinear (fun _ => e) (fun r => congrFun h r)
    ext v
    exact congrArg (fun m : MultilinearMap ℝ (fun _ : Fin n => Eucl P) ℝ => m v) hm
  -- Step 3: hence `Λⁿ(ℝ^P)` is finite-dimensional; take a basis `b₁, …, b_N`.
  have : FiniteDimensional ℝ (Covector (Eucl P) n) := FiniteDimensional.of_injective Φ hΦ
  let b := Module.finBasis ℝ (Covector (Eucl P) n)
  refine ⟨Module.finrank ℝ (Covector (Eucl P) n), b, ?_⟩
  -- Step 4: a linear functional vanishing on a basis is zero.
  intro w hw
  have hlin : (w : Covector (Eucl P) n →ₗ[ℝ] ℝ) = 0 := b.ext (fun i => by simpa using hw i)
  ext α
  simpa using congrArg (fun l : Covector (Eucl P) n →ₗ[ℝ] ℝ => l α) hlin
/-- **Fundamental lemma of the calculus of variations with a positive weight** (a step of the
proof that a rectifiable `τ(M, θ, ξ)` lives on its support, Simon Ch. 6, 3.9).  If `θ > 0` on `M`,
`θ` is `μ`-integrable on `M ∩ W` with `W` open, `g` is a.e.-strongly measurable and a.e. bounded
for `μ ⌞ M`, and `∫_M θ φ g dμ = 0` for every smooth compactly supported `φ` with
`tsupport φ ⊆ W`, then `g = 0` `μ ⌞ M`-a.e. on `W`.  Mathlib's fundamental lemma applied to `θ g`,
which is integrable on `W` for `μ ⌞ M`, gives `θ g = 0` there; divide by `θ`. -/
theorem Submission.lpf_rsn_weighted_fundamental_lemma : ∀ (P : ℕ) (μ : Measure (Eucl P)) (M W : Set (Eucl P)) (θ g : Eucl P → ℝ) (C : ℝ), IsOpen W → NullMeasurableSet M μ → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) μ → AEStronglyMeasurable g (μ.restrict M) → (∀ᵐ x ∂(μ.restrict M), |g x| ≤ C) → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W → ∫ x in M, θ x * (φ x * g x) ∂μ = 0) → ∀ᵐ x ∂(μ.restrict M), x ∈ W → g x = 0 := by
  intro P μ M W θ g C hW hM hpos hθ hg hgC hint
  -- Step 1: `θ g` is integrable on `W` for `μ ⌞ M`, as `(μ ⌞ M) ⌞ W = μ ⌞ (M ∩ W)`.
  have hfint : IntegrableOn (fun x => θ x * g x) W (μ.restrict M) := by
    rw [IntegrableOn, Measure.restrict_restrict hW.measurableSet, Set.inter_comm]
    have hθ' : Integrable θ (μ.restrict (M ∩ W)) := hθ
    have hg' : AEStronglyMeasurable g (μ.restrict (M ∩ W)) :=
      hg.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hgC' : ∀ᵐ x ∂(μ.restrict (M ∩ W)), ‖g x‖ ≤ C := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hgC] with x hx
      simpa [Real.norm_eq_abs] using hx
    exact hθ'.mul_bdd hg' hgC'
  -- Steps 2–3: the tests `∫ φ • (θ g) d(μ ⌞ M)` vanish, so `θ g = 0` `μ ⌞ M`-a.e. on `W`.
  have hzero := hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint.locallyIntegrableOn
    (fun φ hφ hφc hφW => by
      rw [← hint φ hφ hφc hφW]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring)
  -- Step 4: `μ ⌞ M`-a.e. point lies in `M`, where `θ > 0`.
  filter_upwards [hzero, ae_restrict_mem₀ hM] with x hx hxM hxW
  rcases mul_eq_zero.mp (hx hxW) with h | h
  · exact absurd h (hpos x hxM).ne'
  · exact h
/-- A signed simple `n`-vector `w = ±τ₁ ∧ ⋯ ∧ τₙ` of an orthonormal frame `τ` (the orientations
`ξ(x)` of Simon Ch. 6, 3.1) has `|⟨b, w⟩| ≤ ‖b‖` for every `n`-covector `b` and is nonzero:
`|⟨b, w⟩| = |b(τ)| ≤ ‖b‖ ∏ ‖τᵢ‖ = ‖b‖`, and the covector `b_τ = ⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τₙ, ·⟩` has
`b_τ(τ) = det(⟨τᵢ, τⱼ⟩) = det 1 = 1` (1.1). -/
theorem Submission.iwl_sp_sn_signed_simpleNVector_bound_ne_zero : ∀ (P n : ℕ) (τ : Fin n → Eucl P) (w : NVector (Eucl P) n), Orthonormal ℝ τ → (w = simpleNVector τ ∨ w = -simpleNVector τ) → (∀ b : Covector (Eucl P) n, |w b| ≤ ‖b‖) ∧ w ≠ 0 := by
  intro P n τ w hτ hw
  -- Whatever the sign, `|⟨b, w⟩| = |b(τ₁, …, τₙ)|`.
  have habs : ∀ b : Covector (Eucl P) n, |w b| = |b τ| := by
    intro b
    rcases hw with rfl | rfl
    · simp only [simpleNVector_apply]
    · simp only [neg_apply, simpleNVector_apply, abs_neg]
  -- `|b(τ)| ≤ ‖b‖ ∏ ‖τᵢ‖ = ‖b‖`, as the frame vectors are unit vectors.
  have hbound : ∀ b : Covector (Eucl P) n, |b τ| ≤ ‖b‖ := by
    intro b
    have h1 := b.le_opNorm τ
    have hprod : ∏ i, ‖τ i‖ = 1 := Finset.prod_eq_one (fun i _ => hτ.1 i)
    rw [hprod, mul_one, Real.norm_eq_abs] at h1
    exact h1
  refine ⟨fun b => (habs b).trans_le (hbound b), ?_⟩
  -- `b_τ(τ) = det(⟨τᵢ, τⱼ⟩) = det 1 = 1`, so `w = 0` would give `0 = |w(b_τ)| = 1`.
  intro h0
  have hdet : wedgeCovectors n (fun i => innerSL ℝ (τ i)) τ = 1 := by
    rw [wedgeCovectors_apply_det]
    have hm : (Matrix.of fun i j => (innerSL ℝ (τ i)) (τ j)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      rw [Matrix.of_apply, innerSL_apply_apply, orthonormal_iff_ite.mp hτ i j, Matrix.one_apply]
    rw [hm, Matrix.det_one]
  have h1 := habs (wedgeCovectors n (fun i => innerSL ℝ (τ i)))
  rw [h0, hdet] at h1
  simp only [zero_apply, abs_zero, abs_one, zero_ne_one] at h1
/-- **Fundamental lemma of the calculus of variations with a positive weight** (a step of the
proof that a rectifiable representation `T = τ(M, θ, ξ)` has `Hⁿ(M ∖ spt T) = 0`, used for the
smooth push-forward in Simon Ch. 6, 8.2).  If `θ > 0` on `M`, `θ` is `μ`-integrable on `M ∩ W`
with `W` open, `g` is a.e.-strongly measurable and a.e. bounded for `μ ⌞ M`, and
`∫_M θ φ g dμ = 0` for every smooth compactly supported `φ` with `tsupport φ ⊆ W`, then `g = 0`
`μ ⌞ M`-a.e. on `W`.  Mathlib's fundamental lemma applied to `θ g`, which is integrable on `W`
for `μ ⌞ M`, gives `θ g = 0` there; divide by `θ`. -/
theorem Submission.iwl_sp_sn_weighted_fundamental_lemma : ∀ (P : ℕ) (μ : Measure (Eucl P)) (M W : Set (Eucl P)) (θ g : Eucl P → ℝ) (C : ℝ), IsOpen W → NullMeasurableSet M μ → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) μ → AEStronglyMeasurable g (μ.restrict M) → (∀ᵐ x ∂(μ.restrict M), |g x| ≤ C) → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W → ∫ x in M, θ x * (φ x * g x) ∂μ = 0) → ∀ᵐ x ∂(μ.restrict M), x ∈ W → g x = 0 := by
  intro P μ M W θ g C hW hM hpos hθ hg hgC hint
  -- Step 1: `θ g` is integrable on `W` for `μ ⌞ M`, as `(μ ⌞ M) ⌞ W = μ ⌞ (M ∩ W)`.
  have hfint : IntegrableOn (fun x => θ x * g x) W (μ.restrict M) := by
    rw [IntegrableOn, Measure.restrict_restrict hW.measurableSet, Set.inter_comm]
    have hθ' : Integrable θ (μ.restrict (M ∩ W)) := hθ
    have hg' : AEStronglyMeasurable g (μ.restrict (M ∩ W)) :=
      hg.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hgC' : ∀ᵐ x ∂(μ.restrict (M ∩ W)), ‖g x‖ ≤ C := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hgC] with x hx
      simpa [Real.norm_eq_abs] using hx
    exact hθ'.mul_bdd hg' hgC'
  -- Steps 2–3: the tests `∫ φ • (θ g) d(μ ⌞ M)` vanish, so `θ g = 0` `μ ⌞ M`-a.e. on `W`.
  have hzero := hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint.locallyIntegrableOn
    (fun φ hφ hφc hφW => by
      rw [← hint φ hφ hφc hφW]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring)
  -- Step 4: `μ ⌞ M`-a.e. point lies in `M`, where `θ > 0`; divide by `θ`.
  filter_upwards [hzero, ae_restrict_mem₀ hM] with x hx hxM hxW
  rcases mul_eq_zero.mp (hx hxW) with h | h
  · exact absurd h (hpos x hxM).ne'
  · exact h

/-- **A representation is null where the current vanishes (steps 5–8 of (P2) in Simon Ch. 6,
Lemma 3.9).**  If `T = τ(M, θ, ξ)` with `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`, `T` vanishes on the open set
`W ⊆ U` and `θ` is integrable on `M ∩ W`, then `Hⁿ(M ∩ W) = 0`.  Testing `T` with `φ α`
(`φ ∈ C_c^∞(W)`, `α` an `n`-covector) gives `∫_M θ φ ⟨α, ξ⟩ dHⁿ = 0`, so `⟨α, ξ⟩ = 0` a.e. on
`M ∩ W` (`lpf_rsn_weighted_fundamental_lemma`).  Finitely many covectors separate `n`-vectors
(`lpf_rsn_covector_separating_family`), so `ξ = 0` a.e. on `M ∩ W`; as `‖ξ‖ = 1` a.e. on `M`,
the set `M ∩ W` is null. -/
theorem Submission.lpf_rsn_local_null : ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsOpen W → W ⊆ U → T.VanishesOn W → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M, 0 < θ x) → IntegrableOn θ (M ∩ W) (μHE[n] : Measure (Eucl P)) → AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ = 1) → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M ∩ W) = 0 := by
  intro P n U W T M θ ξ hW hWU hvan hM hpos hθ hξm hξ1 hrep
  -- Each coordinate `x ↦ ξ x α` is bounded by `‖α‖` and vanishes a.e. on `M ∩ W`.
  have key : ∀ α : Covector (Eucl P) n,
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ W → ξ x α = 0 := by
    intro α
    refine Submission.lpf_rsn_weighted_fundamental_lemma P (μHE[n] : Measure (Eucl P)) M W θ
      (fun x => ξ x α) ‖α‖ hW hM hpos hθ ?_ ?_ ?_
    · exact (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable hξm
    · filter_upwards [hξ1] with x hx
      calc |ξ x α| = ‖ξ x α‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ξ x‖ * ‖α‖ := (ξ x).le_opNorm α
        _ = ‖α‖ := by rw [hx, one_mul]
    · -- `ω = φ α` is a test form supported in `W`, so `T ω = 0`.
      intro φ hφ hφc hφW
      let ω : DifferentialForm (Eucl P) n := fun x => φ x • α
      have hωs : IsSmoothForm ω := hφ.smul contDiff_const
      have hωc : HasCompactSupport ω := hφc.smul_right
      have hωW : tsupport ω ⊆ W := (tsupport_smul_subset_left φ (fun _ => α)).trans hφW
      let ωU : TestFormOn U n := ⟨ω, ⟨hωs, hωc⟩, hωW.trans hWU⟩
      have h0 : T ωU = 0 := hvan ωU hωW
      rw [hrep ωU] at h0
      simpa [tauAction, ωU, ω, map_smul, smul_eq_mul] using h0
  -- A finite separating family of covectors gives `ξ = 0` a.e. on `M ∩ W`, where `‖ξ‖ = 1`.
  obtain ⟨N, b, hb⟩ := Submission.lpf_rsn_covector_separating_family P n
  have hall : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ i, x ∈ W → ξ x (b i) = 0 :=
    ae_all_iff.mpr fun i => key (b i)
  have hnotW : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∉ W := by
    filter_upwards [hall, hξ1] with x hx h1 hxW
    rw [hb (ξ x) fun i => hx i hxW, ContinuousLinearMap.opNorm_zero] at h1
    exact zero_ne_one h1
  have hres : (μHE[n] : Measure (Eucl P)).restrict M W = 0 := by
    rw [ae_iff] at hnotW
    simpa using hnotW
  rwa [Measure.restrict_apply hW.measurableSet, Set.inter_comm] at hres
/-- **A rectifiable representation is null where the current vanishes (a step of the proof that
`τ(M, θ, ξ)` lives on `spt T`, used for Simon Ch. 6, Theorem 8.2).**  If `T = τ(M, θ, ξ)` and `T`
vanishes on an open `W` with `closure W` a compact subset of `U`, then `Hⁿ(M ∩ W) = 0`.  Testing
`T` with `φ α` (`φ ∈ C_c^∞(W)`, `α` an `n`-covector) gives `∫_M θ φ ⟨α, ξ⟩ dHⁿ = 0`, so
`⟨α, ξ⟩ = 0` a.e. on `M ∩ W` (`iwl_sp_sn_weighted_fundamental_lemma`; `|⟨α, ξ⟩| ≤ ‖α‖` by
`iwl_sp_sn_signed_simpleNVector_bound_ne_zero`).  Finitely many covectors separate `n`-vectors
(`iwl_sp_sn_covector_separating_family`), so `ξ = 0` a.e. on `M ∩ W`, while `ξ ≠ 0` a.e. on `M`. -/
theorem Submission.iwl_sp_sn_local_null : ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → (μHE[n] : Measure (Eucl P)) (M ∩ W) = 0 := by
  intro P n U W T M θ ξ h hrep hWo hWc hWU hvan
  have hWU' : W ⊆ U := subset_closure.trans hWU
  -- `θ` is integrable on `M ∩ W ⊆ M ∩ closure W`, as `closure W` is a compact subset of `U`.
  have hθ : IntegrableOn θ (M ∩ W) (μHE[n] : Measure (Eucl P)) :=
    (h.integrableOn (closure W) hWc hWU).mono_set (Set.inter_subset_inter_right M subset_closure)
  -- Step 1: `ξ x = ±simpleNVector τ` with `τ` orthonormal, so `|ξ x b| ≤ ‖b‖` and `ξ x ≠ 0`.
  have hgood : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      (∀ b : Covector (Eucl P) n, |ξ x b| ≤ ‖b‖) ∧ ξ x ≠ 0 := by
    filter_upwards [h.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    exact Submission.iwl_sp_sn_signed_simpleNVector_bound_ne_zero P n τ (ξ x) hτ hξ
  -- Steps 3–5: each coefficient `x ↦ ξ x α` vanishes a.e. on `M ∩ W`.
  have key : ∀ α : Covector (Eucl P) n,
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ W → ξ x α = 0 := by
    intro α
    refine Submission.iwl_sp_sn_weighted_fundamental_lemma P (μHE[n] : Measure (Eucl P)) M W θ
      (fun x => ξ x α) ‖α‖ hWo h.nullMeasurableSet h.pos hθ ?_ ?_ ?_
    · exact (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        h.aestronglyMeasurable
    · filter_upwards [hgood] with x hx
      exact hx.1 α
    · -- `ω = φ α` is a test form supported in `W`, so `T ω = 0`.
      intro φ hφ hφc hφW
      let ω : DifferentialForm (Eucl P) n := fun x => φ x • α
      have hωs : IsSmoothForm ω := hφ.smul contDiff_const
      have hωc : HasCompactSupport ω := hφc.smul_right
      have hωW : tsupport ω ⊆ W := (tsupport_smul_subset_left φ (fun _ => α)).trans hφW
      let ωU : TestFormOn U n := ⟨ω, ⟨hωs, hωc⟩, hωW.trans hWU'⟩
      have h0 : T ωU = 0 := hvan ωU hωW
      rw [hrep ωU] at h0
      simpa [tauAction, ωU, ω, map_smul, smul_eq_mul] using h0
  -- Steps 6–7: finitely many covectors separate `n`-vectors, so `ξ = 0` a.e. on `M ∩ W`,
  -- contradicting `ξ ≠ 0`.
  obtain ⟨N, b, hb⟩ := Submission.iwl_sp_sn_covector_separating_family P n
  have hall : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ i, x ∈ W → ξ x (b i) = 0 :=
    ae_all_iff.mpr fun i => key (b i)
  have hnotW : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∉ W := by
    filter_upwards [hall, hgood] with x hx hg hxW
    exact hg.2 (hb (ξ x) fun i => hx i hxW)
  -- Step 8: `(Hⁿ ⌞ M)(W) = Hⁿ(M ∩ W)`, as `W` is open.
  have hres : (μHE[n] : Measure (Eucl P)).restrict M W = 0 := by
    rw [ae_iff] at hnotW
    simpa using hnotW
  rwa [Measure.restrict_apply hWo.measurableSet, Set.inter_comm] at hres
/-- **Simple `n`-vectors (step (P1) of Simon Ch. 6, Lemma 3.9).**  The operator norm of
`v₁ ∧ ⋯ ∧ vₙ = simpleNVector v` is the square root of the Gram determinant `det (⟪vᵢ, vⱼ⟫)`, and a
change of frame `τ ↦ Bτ` multiplies `simpleNVector τ` by `det B`.  The second identity is the
uniqueness of alternating forms on `ℝⁿ` (`AlternatingMap.eq_smul_basis_det`).  A dependent `v`
makes both sides of the first vanish.  An independent `v` is `Bτ` for an orthonormal basis `τ` of
`span v`, so `G(v) = B Bᵀ`; `|α τ| ≤ ‖α‖` and the covector `u ↦ det (⟪τᵢ, uⱼ⟫)` (norm `≤ 1` by
Hadamard's and Bessel's inequalities, value `1` at `τ`) give `‖simpleNVector v‖ = |det B|`. -/
theorem Submission.lpf_simple_nvector_algebra : (∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
  -- Change of frame: `α(Bτ) = det B · α(τ)` for every `n`-covector `α`, since
  -- `B ↦ α(Bτ)` is alternating in the rows of `B` (`AlternatingMap.eq_smul_basis_det`).
  have hframe : ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
      simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
    intro P n B τ
    ext α
    simp only [simpleNVector_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    set f : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ :=
      α.toAlternatingMap.compLinearMap (Fintype.linearCombination ℝ τ) with hf
    have h1 : f (fun i j => B i j) = α (fun i => ∑ j, B i j • τ j) := by
      simp [hf, Fintype.linearCombination_apply]
    have h2 : f (Pi.basisFun ℝ (Fin n)) = α τ := by
      simp [hf, Fintype.linearCombination_apply_single]
    rw [← h1, AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) f,
      AlternatingMap.smul_apply, h2, Pi.basisFun_det, smul_eq_mul, mul_comm]
    rfl
  refine ⟨fun P n v => ?_, hframe⟩
  by_cases hv : LinearIndependent ℝ v
  · -- Independent family: `v = Bτ` for an orthonormal basis `τ` of `W = span v`,
    -- `B i j = ⟪v i, τ j⟫`, so `G(v) = B Bᵀ` and `simpleNVector v = det B • simpleNVector τ`.
    set W := Submodule.span ℝ (Set.range v) with hW_def
    have hW : Module.finrank ℝ W = n := by rw [finrank_span_eq_card hv, Fintype.card_fin]
    set b : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
    set τ : Fin n → Eucl P := fun j => (b j : Eucl P) with hτ_def
    have hτ : Orthonormal ℝ τ := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hvW : ∀ i, v i ∈ W := fun i => Submodule.subset_span (Set.mem_range_self i)
    set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => inner ℝ (v i) (τ j) with hB_def
    have hvB : (fun i => ∑ j, B i j • τ j) = v := by
      funext i
      have h := congrArg Subtype.val (b.sum_repr' ⟨v i, hvW i⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
      simpa [hB_def, hτ_def, real_inner_comm] using h
    have hgram : (Matrix.of fun i j => inner ℝ (v i) (v j)) = B * B.transpose := by
      ext i k
      have h := b.sum_inner_mul_inner ⟨v i, hvW i⟩ ⟨v k, hvW k⟩
      simp only [Submodule.coe_inner] at h
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hB_def]
      rw [← h]
      simp [hτ_def, real_inner_comm]
    have hsv : ∀ α : Covector (Eucl P) n, simpleNVector v α = B.det * α τ := by
      intro α
      rw [← hvB, hframe]
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, simpleNVector_apply]
    -- Upper bound: `|α τ| ≤ ‖α‖ ∏ ‖τ i‖ = ‖α‖`.
    have hup : ∀ α : Covector (Eucl P) n, |α τ| ≤ ‖α‖ := by
      intro α
      have h := α.le_opNorm τ
      simp only [hτ.1, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    -- Lower bound: the calibrating covector `α₀(u) = det (⟪τ i, u j⟫)` has `α₀ τ = 1` and
    -- `‖α₀‖ ≤ 1` by Hadamard's inequality for the columns `c j = (⟪τ i, u j⟫)ᵢ` together with
    -- Bessel's inequality `‖c j‖ ≤ ‖u j‖`.
    set α₀ : Covector (Eucl P) n := wedgeCovectors n fun i => innerSL ℝ (τ i) with hα₀_def
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀_def, wedgeCovectors_apply_det]
      have h : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) = 1 := by
        ext i j
        simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
      rw [h, Matrix.det_one]
    have hα₀ : ‖α₀‖ ≤ 1 := by
      refine ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one fun u => ?_
      rw [one_mul, hα₀_def, wedgeCovectors_apply_det, Real.norm_eq_abs]
      set c : Fin n → EuclideanSpace ℝ (Fin n) :=
        fun j => WithLp.toLp 2 fun i => inner ℝ (τ i) (u j) with hc
      set e := EuclideanSpace.basisFun (Fin n) ℝ
      have hdet : (Matrix.of fun i j => innerSL ℝ (τ i) (u j)).det = e.toBasis.det c := by
        rw [Module.Basis.det_apply]
        congr 1
      have hHad : |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := by
        have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
          ⟨finrank_euclideanSpace_fin⟩
        rw [← e.toBasis.orientation.volumeForm_robust' e c]
        exact e.toBasis.orientation.abs_volumeForm_apply_le c
      have hBessel : ∀ j, ‖c j‖ ≤ ‖u j‖ := by
        intro j
        rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (u j))]
        apply Real.sqrt_le_sqrt
        simpa [hc] using hτ.sum_inner_products_le (u j) (s := Finset.univ)
      rw [hdet]
      calc |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := hHad
        _ ≤ ∏ j, ‖u j‖ := by gcongr with j; exact hBessel j
    -- Hence `‖simpleNVector v‖ = |det B|`.
    have hnorm : ‖simpleNVector v‖ = |B.det| := by
      apply le_antisymm
      · refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun α => ?_
        rw [hsv, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hup α) (abs_nonneg _)
      · calc |B.det| = ‖simpleNVector v α₀‖ := by rw [hsv, hα₀τ, mul_one, Real.norm_eq_abs]
          _ ≤ ‖simpleNVector v‖ * ‖α₀‖ := (simpleNVector v).le_opNorm α₀
          _ ≤ ‖simpleNVector v‖ * 1 :=
            mul_le_mul_of_nonneg_left hα₀ (ContinuousLinearMap.opNorm_nonneg _)
          _ = ‖simpleNVector v‖ := mul_one _
    rw [hnorm, hgram, Matrix.det_mul, Matrix.det_transpose, sq_abs, sq]
  · -- Dependent family: every alternating map vanishes on `v`, and `G(v) g = 0` for a
    -- nontrivial relation `∑ g j • v j = 0`, so both sides vanish.
    have h0 : ‖simpleNVector v‖ = 0 := by
      refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun α => ?_)
        (ContinuousLinearMap.opNorm_nonneg _)
      have hα : α v = 0 := α.toAlternatingMap.map_linearDependent v hv
      rw [simpleNVector_apply, hα, norm_zero, zero_mul]
    obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hv
    have hdet : (Matrix.of fun i j => inner ℝ (v i) (v j)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨g, fun h => hi₀ (congrFun h i₀), ?_⟩
      funext i
      have h := congrArg (inner ℝ (v i)) hg
      simp only [inner_sum, inner_smul_right, inner_zero_right] at h
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
    rw [h0, hdet, sq, mul_zero]

/-- **A rectifiable representation lives on the support (step (P2) of Simon Ch. 6, Lemma 3.9).**
If `T = τ(M, θ, ξ)` then `Hⁿ(M \ spt T) = 0`.  An orthonormal frame `τ` has Gram matrix `1`, so
`‖simpleNVector τ‖ = 1` by `lpf_simple_nvector_algebra` and `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`
(`orients`).  Hence `Hⁿ(M ∩ W) = 0` for every open `W ⊂⊂ U` on which `T` vanishes
(`lpf_rsn_local_null`), and countably many such `W` cover the zero region of `T`
(`lpf_rsn_null_diff_support_of_local_null`). -/
theorem Submission.lpf_rectifiable_support_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := by
  intro P n U T M θ ξ hM hT
  -- Unit norm: `ξ x = ±simpleNVector τ` with `τ` orthonormal for `Hⁿ`-a.e. `x ∈ M`, and
  -- `‖simpleNVector τ‖ ^ 2 = det (⟪τᵢ, τⱼ⟫) = det 1 = 1`.
  have hξ : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ = 1 := by
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, -, hξx⟩ := hx
    have hgram : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = 1 := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
    have hτ1 : ‖simpleNVector τ‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (ContinuousLinearMap.opNorm_nonneg _) two_ne_zero).mp ?_
      rw [Submission.lpf_simple_nvector_algebra.1, hgram, Matrix.det_one]
    rcases hξx with h | h
    · rw [h, hτ1]
    · rw [h, ContinuousLinearMap.opNorm_neg, hτ1]
  -- It suffices that `Hⁿ(M ∩ W) = 0` for each open `W ⊂⊂ U` on which `T` vanishes; there `θ` is
  -- integrable on `M ∩ W ⊆ M ∩ closure W`.
  refine Submission.lpf_rsn_null_diff_support_of_local_null P n U T M _ hM.subset
    fun W hW hWc hWU hTW => ?_
  exact Submission.lpf_rsn_local_null P n U W T M θ ξ hW (subset_closure.trans hWU) hTW
    hM.nullMeasurableSet hM.pos
    ((hM.integrableOn _ hWc hWU).mono_set (Set.inter_subset_inter_right M subset_closure))
    hM.aestronglyMeasurable hξ hT

/-- Simon Ch. 6, 2.17–2.22 (pp. 138–139): the product `[[0,1]] × X` of a finite-mass current
`X ∈ 𝒟ₖ(ℝ^m)`, `([[0,1]] × X)(η) = ∫₀¹ X(φ_s) ds`, where `φ_s(x) = η(s, x)(e₀, ι ·)` is the
`dt`-slice of `η` at time `s` (`e₀ = (1, 0)`, `ι w = (0, w)`).  (I) It exists and is the unique
current with this formula, `M([[0,1]] × X) ≤ M(X)`, `spt([[0,1]] × X) ⊆ [0,1] × spt X`, the
integrand `s ↦ X(φ_s)` is continuous on `[0,1]`, and `[[0,1]] × X` is normal when `X` is.
(II), (III) Every current `Z` with this formula satisfies the boundary formula
`∂Z = {1} × X − {0} × X − [[0,1]] × ∂X` (without the last term for `0`-currents). -/
theorem Submission.dph_interval_product :
    (∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ →
      ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1),
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
            (φ s : DifferentialForm (Eucl m) k) x v =
              (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          Z η = ∫ s in (0 : ℝ)..1, X (φ s)) ∧
        (∀ Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1),
          (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
              (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
              (φ s : DifferentialForm (Eucl m) k) x v =
                (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                  ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                  (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
            Z' η = ∫ s in (0 : ℝ)..1, X (φ s)) → Z' = Z) ∧
        Z.mass ≤ X.mass ∧
        Z.support ⊆ {y : Eucl (m + 1) |
          EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
            (EuclideanSpace.equiv (Fin m) ℝ).symm
                (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ∧
        (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1))
            (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k),
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m),
            (φ s : DifferentialForm (Eucl m) k) x v =
              (η : DifferentialForm (Eucl (m + 1)) (k + 1))
                ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
                (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                    (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
          ContinuousOn (fun s => X (φ s)) (Icc (0 : ℝ) 1)) ∧
        ((∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 →
            HEq Y X → Y.boundary.mass < ∞) →
          Z.boundary.mass < ∞)) ∧
    (∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0)
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)), X.mass < ∞ →
      (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1))
          (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0),
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m),
          (φ s : DifferentialForm (Eucl m) 0) x v =
            (η : DifferentialForm (Eucl (m + 1)) (0 + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
      ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) 0)
        (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) 0),
        (∀ (x : Eucl m) (v : Fin 0 → Eucl m),
          (ψ₀ : DifferentialForm (Eucl m) 0) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) 0)
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        (∀ (x : Eucl m) (v : Fin 0 → Eucl m),
          (ψ₁ : DifferentialForm (Eucl m) 0) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) 0)
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z.boundary ψ = X ψ₁ - X ψ₀) ∧
    (∀ (m j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1))
        (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)), X.mass < ∞ →
      (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1))
          (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)),
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
          (φ s : DifferentialForm (Eucl m) (j + 1)) x v =
            (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z η = ∫ s in (0 : ℝ)..1, X (φ s)) →
      ∀ (ψ : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1))
        (ψ₀ ψ₁ : TestFormOn (univ : Set (Eucl m)) (j + 1))
        (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j),
        (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
          (ψ₀ : DifferentialForm (Eucl m) (j + 1)) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        (∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m),
          (ψ₁ : DifferentialForm (Eucl m) (j + 1)) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m),
          (φ s : DifferentialForm (Eucl m) j) x v =
            (ψ : DifferentialForm (Eucl (m + 1)) (j + 1))
              ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
              (Fin.cons (EuclideanSpace.single 0 1) fun i =>
                (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                  (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) →
        Z.boundary ψ = X ψ₁ - X ψ₀ - ∫ s in (0 : ℝ)..1, X.boundary (φ s)) := by
  -- (II) and (III) are the first two conjuncts of `product_boundary`.
  refine ⟨?_, Submission.dph_iprod_boundary.1, Submission.dph_iprod_boundary.2.1⟩
  -- (I): `product_exists` gives the characterization, uniqueness, mass bound and support of `Z`;
  -- continuity of `s ↦ X(φ_s)` is the first half of (D1) in `slice_continuity`, and normality
  -- is the conjunct (N) of `product_boundary`, applied to this `Z` and its characterization.
  intro m k X hX
  obtain ⟨Z, hZ, huniq, hmass, hsupp⟩ := Submission.dph_iprod_exists m k X hX
  exact ⟨Z, hZ, huniq, hmass, hsupp,
    fun η φ hφ => (Submission.dph_iprod_slice_continuity.1 m k X hX η φ hφ).1,
    Submission.dph_iprod_boundary.2.2 m k X Z hX hZ⟩
/-- Simon Ch. 6, 2.25–2.27: the homotopy formula `(E0)`/`(E1)` and the affine-homotopy estimate
`(Aff)`, for `Z = [[0,1]] × X` given by its slice characterization and with push-forwards written as
evaluation on compatible forms.  For `(E0)`/`(E1)`, pick a test form `θ = G^#ω` near
`[0,1] × spt X` (2.23).  Then `dθ = G^#(dω)` (2.5), so `Z(dθ) = Z η'`; the end slices satisfy
`θᵢ = (G ∘ jᵢ)^#ω` near `spt X`, so `X θᵢ = X ηᵢ`; and the boundary formula for `[[0,1]] × X`
gives `X θ₁ - X θ₀ = Z(dθ) (+ Z' θ)`, with `Z' θ = Z' θ'` by locality. -/
theorem Submission.dph_smooth_homotopy : (∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C) := by
  -- `j_s x = (s, x)` is continuous, and `(s, x)` lies over `[0,1] × spt X` when `s ∈ [0,1]` and
  -- `x ∈ spt X`, since `t (s, x) = s` and `tl (s, x) = x`.
  have hcons : ∀ (m : ℕ) (s : ℝ), Continuous fun x : Eucl m =>
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) :=
    fun m s => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
      (continuous_const.finCons (EuclideanSpace.equiv (Fin m) ℝ).continuous)
  have hcyl : ∀ (m q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q) (s : ℝ),
      s ∈ Icc (0 : ℝ) 1 → ∀ x ∈ X.support,
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈
          {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
            (EuclideanSpace.equiv (Fin m) ℝ).symm
              (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} := by
    intro m q X s hs x hx
    refine ⟨?_, ?_⟩
    · rw [ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero]
      exact hs
    · rw [ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
        ContinuousLinearEquiv.symm_apply_apply]
      exact hx
  -- End slices (1c): if `θ = G^#ω` on an open `N ⊇ [0,1] × spt X` and `η` is compatible with
  -- `(G ∘ j_s, ω)` near `spt X`, then the horizontal slice `θ_s` of `θ` has `X θ_s = X η`.
  have hend : ∀ (m m' q : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) q)
      (G : Eucl (m + 1) → Eucl m') (ω : DifferentialForm (Eucl m') q)
      (θ : TestFormOn (univ : Set (Eucl (m + 1))) q) (N : Set (Eucl (m + 1))) (s : ℝ)
      (η : TestFormOn (univ : Set (Eucl m)) q),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → IsOpen N → s ∈ Icc (0 : ℝ) 1 →
      {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧
        (EuclideanSpace.equiv (Fin m) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N →
      (∀ y ∈ N, (θ : DifferentialForm (Eucl (m + 1)) q) y =
        (ω (G y)).compContinuousLinearMap (fderiv ℝ G y)) →
      (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        (η : DifferentialForm (Eucl m) q) x =
          (ω ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
            (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap
            (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) →
      ∃ θs : TestFormOn (univ : Set (Eucl m)) q,
        (∀ (x : Eucl m) (v : Fin q → Eucl m), (θs : DifferentialForm (Eucl m) q) x v =
          (θ : DifferentialForm (Eucl (m + 1)) q)
            ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)))
            (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) ∧
        X θs = X η := by
    rintro m m' q X G ω θ N s η hG hN hs hAN hθ ⟨N₀, hN₀, hXN₀, hη⟩
    -- `θ_s = (G ∘ j_s)^#ω` wherever `j_s x ∈ N`, so `θ_s = η` on `N₀ ∩ j_s⁻¹(N) ⊇ spt X`.
    obtain ⟨θs, hθs, hθsN⟩ := Submission.dph_sh_slice_compatible_testForm m m' q G ω θ N s hG hθ
    exact ⟨θs, hθs, Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support m q univ X θs η _
      (hN₀.inter (hN.preimage (hcons m s)))
      (fun x hx => ⟨hXN₀ hx, hAN (hcyl m q X s hs x hx)⟩)
      fun x hx => (hθsN x hx.2).trans (hη x hx.1).symm⟩
  refine ⟨?_, ?_, Submission.dph_sh_affine_estimate⟩
  · -- (E0)
    rintro m m' X Z G hX hZ hG hprop ω η₀ η₁ η' h₀ h₁ ⟨N', hN', hAN', h'⟩
    -- (1a) `θ ∈ 𝒟⁰(ℝ^{m+1})` with `θ = G^#ω` on an open `N ⊇ [0,1] × spt X`.
    obtain ⟨θ, _, N, hN, hAN, -, -, hθ, -⟩ :=
      Submission.iwl_sp_exists_compatible_testForm (m + 1) m' 0 univ univ _ G isOpen_univ
        (subset_univ _) hG (fun K hK _ => hprop K hK) ω
    -- (1b) `dθ = G^#(dω)` on `N`, and `η' = G^#(dω)` on `N'`, so `∂Z θ = Z(dθ) = Z η'`.
    have hdθ := Submission.dph_sh_extDeriv_compatible (m + 1) m' 0 G ω θ N hG ω.property.1.1 hN hθ
    have hZθ : Z.boundary θ = Z η' := by
      rw [GeometricCurrentOn.boundary_apply]
      exact Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl m 0 X Z hZ _ η' (N ∩ N') (hN.inter hN')
        (subset_inter hAN hAN') fun y hy => (hdθ y hy.1).trans (h' y hy.2).symm
    -- (1c) The end slices `θ₀, θ₁` have `X θᵢ = X ηᵢ`.
    obtain ⟨θ₀, hθ₀, hX₀⟩ := hend m m' 0 X G ω θ N 0 η₀ hG hN
      (left_mem_Icc.2 zero_le_one) hAN hθ h₀
    obtain ⟨θ₁, hθ₁, hX₁⟩ := hend m m' 0 X G ω θ N 1 η₁ hG hN
      (right_mem_Icc.2 zero_le_one) hAN hθ h₁
    -- (1d) The boundary formula `∂([[0,1]] × X) θ = X θ₁ - X θ₀`.
    rw [← hX₀, ← hX₁, ← hZθ]
    exact (Submission.dph_interval_product.2.1 m X Z hX hZ θ θ₀ θ₁ hθ₀ hθ₁).symm
  · -- (E1)
    rintro m m' j X Z Z' G hX hZ hZ' hG hprop ω η₀ η₁ η' θ' h₀ h₁ ⟨N', hN', hAN', h'⟩
      ⟨N'', hN'', hAN'', hθ'⟩
    -- (1a) `θ ∈ 𝒟^{j+1}(ℝ^{m+1})` with `θ = G^#ω` on an open `N ⊇ [0,1] × spt X`.
    obtain ⟨θ, _, N, hN, hAN, -, -, hθ, -⟩ :=
      Submission.iwl_sp_exists_compatible_testForm (m + 1) m' (j + 1) univ univ _ G isOpen_univ
        (subset_univ _) hG (fun K hK _ => hprop K hK) ω
    -- (1b) `∂Z θ = Z(dθ) = Z η'`.
    have hdθ := Submission.dph_sh_extDeriv_compatible (m + 1) m' (j + 1) G ω θ N hG
      ω.property.1.1 hN hθ
    have hZθ : Z.boundary θ = Z η' := by
      rw [GeometricCurrentOn.boundary_apply]
      exact Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl m (j + 1) X Z hZ _ η' (N ∩ N')
        (hN.inter hN') (subset_inter hAN hAN') fun y hy => (hdθ y hy.1).trans (h' y hy.2).symm
    -- (1c) The end slices `θ₀, θ₁` have `X θᵢ = X ηᵢ`.
    obtain ⟨θ₀, hθ₀, hX₀⟩ := hend m m' (j + 1) X G ω θ N 0 η₀ hG hN
      (left_mem_Icc.2 zero_le_one) hAN hθ h₀
    obtain ⟨θ₁, hθ₁, hX₁⟩ := hend m m' (j + 1) X G ω θ N 1 η₁ hG hN
      (right_mem_Icc.2 zero_le_one) hAN hθ h₁
    -- (1e) With the `dt`-slices `φ` of `θ`, `∫₀¹ ∂X(φ_s) ds = Z' θ`; and `θ = θ' = G^#ω` on
    -- `N ∩ N'' ⊇ [0,1] × spt X ⊇ [0,1] × spt ∂X`, so `Z' θ = Z' θ'`.
    obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm m j θ
    have hZ'θ : Z' θ = ∫ s in (0 : ℝ)..1, X.boundary (φ s) := hZ' θ φ fun s _ x v => hφ s x v
    have hspt : X.boundary.support ⊆ X.support := Submission.iwl_cr_support_lemmas.1 m j univ X
    have hZ'θ' : Z' θ = Z' θ' :=
      Submission.dph_sh_apply_eq_of_eqOn_nhds_cyl m j X.boundary Z' hZ' θ θ' (N ∩ N'')
        (hN.inter hN'') (fun y hy => ⟨hAN ⟨hy.1, hspt hy.2⟩, hAN'' ⟨hy.1, hspt hy.2⟩⟩)
        fun y hy => (hθ y hy.1).trans (hθ' y hy.2).symm
    -- The boundary formula `∂([[0,1]] × X) θ = X θ₁ - X θ₀ - ∫₀¹ ∂X(φ_s) ds`.
    have hb := Submission.dph_interval_product.2.2 m j X Z hX hZ θ θ₀ θ₁ φ hθ₀ hθ₁
      fun s _ x v => hφ s x v
    rw [← hX₀, ← hX₁, ← hZθ, ← hZ'θ', hZ'θ, hb, sub_add_cancel]

/-- **Products with `[[0,1]]` of integer multiplicity currents are integer multiplicity
(Simon Ch. 6, 3.2(2)).**  By `iwl_cr_interval_product_im` there is an integer multiplicity
`Z' = τ(M̃, θ̃, ξ̃)` with the same product characterization `Z'(η) = ∫₀¹ X(φ(s)) ds`.  For a test
form `η`, `iwl_cr_ci_slice_testForm` gives a `dt`-slice family `φ` of `η` on all of `ℝ`, so both
characterizations apply and `Z(η) = ∫₀¹ X(φ(s)) ds = Z'(η)`.  Hence `Z = τ(M̃, θ̃, ξ̃)` on every
test form, and the triple of `Z'` shows that `Z` is integer multiplicity. -/
theorem Submission.dph_interval_product_im : ∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)), IsIntegerMultiplicity X → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → IsIntegerMultiplicity Z := by
  intro m k X Z hX hZ
  -- The product current `Z' = [[(0,1)]] × X` exists and is integer multiplicity.
  obtain ⟨Z', hZ'IM, hZ'⟩ := Submission.iwl_cr_interval_product_im m k X hX
  -- `Z` and `Z'` agree on every test form: test both characterizations with a slice family.
  have hEq : ∀ η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1), Z η = Z' η := by
    intro η
    obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm m k η
    rw [hZ η φ (fun s _ x v => hφ s x v), hZ' η φ (fun s _ x v => hφ s x v)]
  obtain ⟨M, θ, ξ, hT, hN, hτ⟩ := hZ'IM
  exact ⟨M, θ, ξ, hT, hN, fun ω => (hEq ω).trans (hτ ω)⟩
/-- **Lipschitz push-forward of normal currents (Simon Ch. 6, 2.28–2.29).**  (I) the limit `S` of
the push-forwards `X(η_n)` along locally admissible smooth approximations `G_n → G` exists, is
unique, and has `M(S) ≤ Λ^k M(X)` and `spt S ⊆ closure (G(spt X))`; (II) it commutes with `∂`;
(III) it is linear in `X`.  `Submission.dph_lipschitz_smooth_approx` gives the reference sequences
(`Submission.dph_lpf_reference_sequence`); the product `[[0,1]] × X` of
`Submission.dph_interval_product` and the homotopy formulas `Submission.dph_smooth_homotopy` give
the comparison lemma `Submission.dph_lpf_comparison`, from which `Submission.dph_lpf_existence`
builds (I); (II) and (III) are `Submission.dph_lpf_boundary` and `Submission.dph_lpf_linearity`. -/
theorem Submission.dph_lipschitz_pushforward : (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) ∧ (∀ S' : GeometricCurrentOn (univ : Set (Eucl m')) k, (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S' ω))) → S' = S) ∧ S.mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ S.support ⊆ closure (G '' X.support)) ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (S : GeometricCurrentOn (univ : Set (Eucl m')) (j + 1)), X.mass < ∞ → X.boundary.mass < ∞ → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.boundary.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) j) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) j), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.boundary.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) j) x = ((ω : DifferentialForm (Eucl m') j) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X.boundary (ηj n)) atTop (𝓝 (S.boundary ω)))) ∧ (∀ (m m' k : ℕ) (X X₁ X₂ : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (S S₁ S₂ : GeometricCurrentOn (univ : Set (Eucl m')) k) (a a₁ : ℝ), 0 < r → LipschitzOnWith Λ G (thickening r (X.support ∪ X₁.support)) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ (X.support ∪ X₁.support))) → (∀ ω, X₂ ω = a * X ω + a₁ * X₁ ω) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₁.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₁.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X₁ (ηj n)) atTop (𝓝 (S₁ ω))) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X₂.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X₂.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X₂ (ηj n)) atTop (𝓝 (S₂ ω))) → ∀ ω, S₂ ω = a * S ω + a₁ * S₁ ω) := by
  -- Reference smooth approximations with `‖DG_n‖ ≤ Λ` on `(spt X)_{r/2}` (proof, Step 2).
  have hRef := Submission.dph_lpf_reference_sequence Submission.dph_lipschitz_smooth_approx
  -- Comparison lemma (Step 1); it only uses the characterization of the product `[[0,1]] × X`.
  have hCmp := Submission.dph_lpf_comparison
    (fun m k X hX => (Submission.dph_interval_product.1 m k X hX).imp fun _ hZ => hZ.1)
    Submission.dph_smooth_homotopy
  -- (I): existence, uniqueness, mass and support (Steps 3–6).
  have hI := Submission.dph_lpf_existence hRef hCmp
  -- (II) boundary (Step 7) and (III) linearity (Step 8).
  exact ⟨hI, Submission.dph_lpf_boundary hRef hI, Submission.dph_lpf_linearity hRef⟩

/-- **A rectifiable representation carries no `Hⁿ`-measure off the support** (step 3 of the
smooth push-forward argument; cf. Simon Ch. 6, 2.11 and Lemma 3.9).  If `T = τ(M, θ, ξ)` then
`Hⁿ(M ∖ spt T) = 0`.  Testing `T` with `φ b` (`φ ∈ C_c^∞(W)`, `b` an `n`-covector) shows
`Hⁿ(M ∩ W) = 0` for every open `W ⊂⊂ U` on which `T` vanishes (`iwl_sp_sn_local_null`).  As
`M ⊆ U`, countably many such `W` cover `M ∖ spt T`
(`iwl_sp_sn_null_diff_support_of_local_null`). -/
theorem Submission.iwl_sp_rectifiable_support_null : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := by
  intro P n U T M θ ξ hM hT
  -- Step 8: since `M ⊆ U`, it suffices that `Hⁿ(M ∩ W) = 0` for each open `W ⊂⊂ U` on which
  -- `T` vanishes; steps 1–7 give exactly that.
  exact Submission.iwl_sp_sn_null_diff_support_of_local_null P n U T M
    (μHE[n] : Measure (Eucl P)) hM.subset fun W hW hWc hWU hTW =>
      Submission.iwl_sp_sn_local_null P n U W T M θ ξ hM hT hW hWc hWU hTW

/-- **Integrality of the Lipschitz push-forward defined by smooth approximation** (step 5.9 of the
push-forward homotopy argument; Simon Ch. 6, 2.29 and Lemma 3.9).  Assume (S5′): `g_# X` is an
integer multiplicity `S'` with `∫_M θ ⟨ω(g_j x), (Dg_j)_# ξ⟩ dHᵏ → S'(ω)` along `C¹` maps
`g_j → g`.  If `S` is the limit of `X(η_n)` for forms `η_n` compatible with smooth approximations
`G_n → G` near `spt X`, then `S` is integer multiplicity.  Take `G_n → Ĝ` from
`dph_lipschitz_smooth_approx` and `η_n` from `iwl_sp_exists_compatible_testForm`.  As
`Hᵏ(M ∖ spt X) = 0` (`iwl_sp_rectifiable_support_null`), `X(η_n)` is the integral for `g_j = G_n`,
so `S = S'`. -/
theorem Submission.dph_lipschitz_pushforward_im : (∀ (P Q k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → (∀ x ∈ M, ∃ j : ℕ, θ x = j) → (∀ ω : TestFormOn (univ : Set (Eucl P)) k, X ω = tauAction k M θ ξ ω) → ∀ (g : Eucl P → Eucl Q) (Λ : ℝ≥0), LipschitzWith Λ g → (∀ K : Set (Eucl Q), IsCompact K → IsCompact (g ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl Q)) k, IsLipschitzPushforward X g S ∧ IsIntegerMultiplicity S ∧ ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : TestFormOn (univ : Set (Eucl Q)) k, Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) ((ω : DifferentialForm (Eucl Q) k) (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (S ω))) → ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (S : GeometricCurrentOn (univ : Set (Eucl m')) k), IsIntegerMultiplicity X → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) → IsIntegerMultiplicity S := by
  intro hS5 m m' k X G Λ r S hX hr hGLip hGprop hLipPF
  -- 1. `X = τ(M, θ, ξ)` with `θ` integer-valued.
  obtain ⟨M, θ, ξ, hT, hθ, hXτ⟩ := hX
  -- 2. `Ĝ = G'` is Lipschitz with `Ĝ = G` on `(spt X)_r`; the `C^∞` maps `G_n` are `L`-Lipschitz,
  -- `G_n → Ĝ` uniformly and `‖DG_n‖ ≤ Λ` on `O₀ = (spt X)_{r/2}`, where `G_n → G` uniformly.
  obtain ⟨G', Gj, L, hG'Lip, hG'eq, hGjsmooth, hGjLip, hGjconv, hGjderiv, -⟩ :=
    Submission.dph_lipschitz_smooth_approx m m' G Λ X.support r hr hGLip
  have hsptO : X.support ⊆ thickening (r / 2) X.support := self_subset_thickening (half_pos hr) _
  have hOr : thickening (r / 2) X.support ⊆ thickening r X.support :=
    thickening_mono (half_le_self hr.le) _
  have hsptr : X.support ⊆ thickening r X.support := self_subset_thickening hr _
  have hconvO : TendstoUniformlyOn Gj G atTop (thickening (r / 2) X.support) :=
    hGjconv.tendstoUniformlyOn.congr_right (hG'eq.mono hOr)
  -- 3. `Ĝ` is proper on `spt X` (it equals `G` there), so (S5′) gives an integer multiplicity `S'`
  -- with `I_n(ω) = ∫_M θ ⟨ω(G_n x), (DG_n)_# ξ⟩ dHᵏ → S'(ω)`.
  have hG'prop : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (G' ⁻¹' K ∩ X.support) := by
    intro K hK
    have hEq : G' ⁻¹' K ∩ X.support = G ⁻¹' K ∩ X.support := by
      ext x
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hx, hxs⟩
        exact ⟨hG'eq (hsptr hxs) ▸ hx, hxs⟩
      · rintro ⟨hx, hxs⟩
        exact ⟨(hG'eq (hsptr hxs)).symm ▸ hx, hxs⟩
    rw [hEq]
    exact hGprop K hK
  obtain ⟨S', -, hS'im, hS'lim⟩ := hS5 m m' k X M θ ξ hT hθ hXτ G' L hG'Lip hG'prop
  -- 4. Eventually `dist (G x) (G_n x) < 1` on `spt X`, so `G_n` is proper on the closed `spt X`:
  -- `G_n⁻¹(K) ∩ spt X` is a closed subset of the compact `G⁻¹(cthickening 1 K) ∩ spt X`.
  have hsptClosed : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  have hprop_ev : ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K →
      IsCompact (Gj n ⁻¹' K ∩ X.support) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconvO.mono hsptO) 1 one_pos] with n hn
    intro K hK
    refine (hGprop (cthickening 1 K) hK.cthickening).of_isClosed_subset
      ((hK.isClosed.preimage (hGjsmooth n).continuous).inter hsptClosed) ?_
    rintro x ⟨hxK, hxs⟩
    exact ⟨Metric.mem_cthickening_of_dist_le (G x) (Gj n x) 1 K hxK (hn x hxs).le, hxs⟩
  -- `Hᵏ(M ∖ spt X) = 0`: `Hᵏ`-a.e. point of `M` lies in `spt X`.
  have hnull := Submission.iwl_sp_rectifiable_support_null m k univ X M θ ξ hT hXτ
  have hspt : ∀ᵐ x ∂((μHE[k] : Measure (Eucl m)).restrict M), x ∈ X.support := by
    rw [ae_restrict_iff'₀ hT.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    by_contra hxX
    exact hx ⟨hxM, hxX⟩
  -- 5. `S(ω) = S'(ω)`: both are limits of `X(η_n) = I_n(ω)`.
  have hSeq : ∀ ω, S ω = S' ω := by
    intro ω
    -- `η_n` is compatible with `(G_n, ω)` near `spt X` whenever `G_n` is proper on `spt X`.
    have hex : ∀ n, ∃ η : TestFormOn (univ : Set (Eucl m)) k,
        (∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ X.support)) →
        ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (η : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x) := by
      intro n
      by_cases hp : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ X.support)
      · obtain ⟨η, _ζ, N, hN, hAN, -, -, hηN, -⟩ :=
          Submission.iwl_sp_exists_compatible_testForm m m' k univ univ X.support (Gj n)
            isOpen_univ (subset_univ _) (hGjsmooth n) (fun K hK _ => hp K hK) ω
        exact ⟨η, fun _ => ⟨N, hN, hAN, hηN⟩⟩
      · exact ⟨0, fun h => absurd h hp⟩
    choose ηj hηj using hex
    have hcompat : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        (ηj n : DifferentialForm (Eucl m) k) x =
          ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
            (fderiv ℝ (Gj n) x) :=
      hprop_ev.mono fun n hn => hηj n hn
    -- `LipPF(X, G, S)` for the admissible `(G_n, O₀, Λ)`: `X(η_n) → S(ω)`.
    have hlim1 : Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω)) :=
      hLipPF Gj (thickening (r / 2) X.support) (Λ : ℝ) isOpen_thickening hsptO hGjsmooth
        (Eventually.of_forall fun n x hx => hGjderiv n x hx) hconvO ω ηj hcompat
    -- Step 3 with `g_n = G_n` (`C^∞` maps are `C¹`): `I_n(ω) → S'(ω)`.
    have hlim2 := hS'lim Gj L (fun n => (hGjsmooth n).of_le (by exact_mod_cast le_top))
      hGjLip hGjconv ω
    -- Eventually `X(η_n) = I_n(ω)`: `η_n = (ω ∘ G_n) ∘ DG_n` on `N ⊇ spt X`, which carries
    -- `Hᵏ ⌞ M`, and `⟨(ω ∘ G_n) ∘ DG_n, ξ⟩ = ⟨ω ∘ G_n, (DG_n)_# ξ⟩` by definition.
    have hevEq : ∀ᶠ n in atTop, X (ηj n) = ∫ x in M, θ x * nVectorPushforward k
        (fderiv ℝ (Gj n) x) (ξ x) ((ω : DifferentialForm (Eucl m') k) (Gj n x))
          ∂(μHE[k] : Measure (Eucl m)) := by
      filter_upwards [hcompat] with n hn
      obtain ⟨N, -, hXN, hηN⟩ := hn
      rw [hXτ, tauAction]
      refine integral_congr_ae ?_
      filter_upwards [hspt] with x hxX
      rw [hηN x (hXN hxX)]
      rfl
    exact tendsto_nhds_unique hlim1 (hlim2.congr' (hevEq.mono fun n h => h.symm))
  -- `S` inherits the integer multiplicity representation of `S'`.
  obtain ⟨M', θ', ξ', hT', hθ', hS'τ⟩ := hS'im
  exact ⟨M', θ', ξ', hT', hθ', fun ω => (hSeq ω).trans (hS'τ ω)⟩
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
/-- Simon Ch. 6, proof of Lemma 5.4 (pointwise bounds integrate along segments): if every point
of `[0, 1]` has pointwise upper Lipschitz constant at most `K` for `γ`, then `‖γ 1 - γ 0‖ ≤ K`.
For `ε > 0`, continuous induction shows `‖γ s - γ 0‖ ≤ (K + ε) s` on `[0, 1]`. -/
theorem Submission.deformation_retraction_dini_segment : ∀ (N : ℕ) (γ : ℝ → Eucl N) (K : ℝ), (∀ s ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s' ∈ Icc (0 : ℝ) 1, |s' - s| < δ → ‖γ s' - γ s‖ ≤ (K + ε) * |s' - s|) → ‖γ 1 - γ 0‖ ≤ K := by
  intro N γ K h
  -- Step 1: the estimate with `ε = 1` makes `γ` continuous on `[0, 1]`.
  have hcont : ContinuousOn γ (Icc 0 1) := by
    intro s hs
    obtain ⟨δ, hδ, hδs⟩ := h s hs 1 one_pos
    rw [Metric.continuousWithinAt_iff]
    intro e he
    have hc : 0 < |K + 1| + 1 := by positivity
    refine ⟨min δ (e / (|K + 1| + 1)), lt_min hδ (div_pos he hc), fun x hx hxs => ?_⟩
    rw [Real.dist_eq] at hxs
    rw [dist_eq_norm]
    have h2 : |x - s| * (|K + 1| + 1) < e :=
      (lt_div_iff₀ hc).1 (lt_of_lt_of_le hxs (min_le_right _ _))
    calc ‖γ x - γ s‖ ≤ (K + 1) * |x - s| := hδs x hx (lt_of_lt_of_le hxs (min_le_left _ _))
      _ ≤ |K + 1| * |x - s| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      _ < e := by nlinarith [abs_nonneg (x - s)]
  -- Steps 2–3: for fixed `ε > 0`, continuous induction on
  -- `S = {x | ‖γ x - γ 0‖ ≤ (K + ε) x}` gives `[0, 1] ⊆ S`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set S : Set ℝ := {x | ‖γ x - γ 0‖ ≤ (K + ε) * x} with hS
  have hclosed : IsClosed (S ∩ Icc 0 1) := by
    have hpair : ContinuousOn (fun x => (‖γ x - γ 0‖, (K + ε) * x)) (Icc 0 1) :=
      (hcont.sub continuousOn_const).norm.prodMk (continuousOn_const.mul continuousOn_id)
    rw [inter_comm]
    exact hpair.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have h0 : (0 : ℝ) ∈ S := by simp [hS]
  have hsub : Icc (0 : ℝ) 1 ⊆ S := by
    refine hclosed.Icc_subset_of_forall_exists_gt h0 ?_
    rintro x ⟨hxS, hx0, hx1⟩ y hy
    obtain ⟨δ, hδ, hδx⟩ := h x ⟨hx0, hx1.le⟩ ε hε
    -- Step 3: `z = min (min y 1) (x + δ / 2)` lies in `S ∩ (x, y]`.
    set z := min (min y 1) (x + δ / 2) with hz
    have hxz : x < z := lt_min (lt_min hy hx1) (by linarith)
    have hzy : z ≤ y := (min_le_left _ _).trans (min_le_left _ _)
    have hz1 : z ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
    have hzx : z ≤ x + δ / 2 := min_le_right _ _
    have habs : |z - x| = z - x := abs_of_pos (sub_pos.2 hxz)
    have hzx' : |z - x| < δ := by rw [habs]; linarith
    have hstep := hδx z ⟨hx0.trans hxz.le, hz1⟩ hzx'
    rw [habs] at hstep
    refine ⟨z, ?_, hxz, hzy⟩
    show ‖γ z - γ 0‖ ≤ (K + ε) * z
    calc ‖γ z - γ 0‖ ≤ ‖γ z - γ x‖ + ‖γ x - γ 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (K + ε) * (z - x) + (K + ε) * x := add_le_add hstep hxS
      _ = (K + ε) * z := by ring
  -- Step 4 is `le_of_forall_pos_le_add`; here we read off the bound at `x = 1`.
  have h1 : ‖γ 1 - γ 0‖ ≤ (K + ε) * 1 := hsub ⟨zero_le_one, le_rfl⟩
  linarith
/-- Simon Ch. 6, §5: a point of `ℝ^{(m+1)+ℓ}` with `ℓ` integer coordinates lies on the lattice
`(m+1)`-skeleton.  It lies in the face `⌊x⌋ + F_α`, where `α` enumerates the other `m + 1`
coordinates increasingly. -/
theorem Submission.deformation_retraction_skeleton_mem : ∀ (m ℓ : ℕ) (x : Eucl (m + 1 + ℓ)), (∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ∃ k : ℤ, x i = k) → x ∈ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F := by
  rintro m ℓ x ⟨I, hIcard, hI⟩
  -- `Iᶜ` has `m + 1` elements; `α` is its increasing enumeration.
  have hc : Iᶜ.card = m + 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hIcard, Nat.add_sub_cancel]
  refine mem_iUnion.2 ⟨(fun i => ⌊x i⌋, Iᶜ.orderEmbOfFin hc), fun i => ⟨fun _ => ?_, fun hi => ?_⟩⟩
  · simp only [one_mul]
    exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  · -- Outside the range of `α` we are in `I`, where `x i` is an integer.
    have hiI : i ∈ I := by
      by_contra h
      exact hi (by simpa [Finset.range_orderEmbOfFin] using h)
    obtain ⟨k, hk⟩ := hI i hiI
    simp only [one_mul, hk, Int.floor_intCast]
/-- Simon Ch. 6, Lemma 5.4, proof p. 163 ("by (7), (8) and the chain rule"), pointwise form:
if `f` is `K₁`-Lipschitz at `x` within `A`, `f` maps `A` into `B`, and `g` is `K₂`-Lipschitz at
`f x` within `B`, then `g ∘ f` is `K₁ K₂`-Lipschitz at `x` within `A`.  With
`η = min{1, ε/(K₁ + K₂ + 1)}` and `δ = min{δ₁, δ₂/(K₁ + η)}` one gets
`(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + ε`. -/
theorem Submission.dr_cc_lip_at_comp : ∀ (X Y Z : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z] (f : X → Y) (g : Y → Z) (A : Set X) (B : Set Y) (x : X) (K₁ K₂ : ℝ), 0 ≤ K₁ → 0 ≤ K₂ → MapsTo f A B → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (f x') (f x) ≤ (K₁ + ε) * dist x' x) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' (f x) < δ → dist (g y') (g (f x)) ≤ (K₂ + ε) * dist y' (f x)) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ A, dist x' x < δ → dist (g (f x')) (g (f x)) ≤ (K₁ * K₂ + ε) * dist x' x := by
  intro X Y Z _ _ _ f g A B x K₁ K₂ hK₁ hK₂ hfAB hf hg ε hε
  -- The auxiliary level `η = min{1, ε/(K₁ + K₂ + 1)}`: `0 < η ≤ 1` and `η(K₁ + K₂ + 1) ≤ ε`.
  have hS : 0 < K₁ + K₂ + 1 := by linarith
  obtain ⟨η, hη, hη1, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η * (K₁ + K₂ + 1) ≤ ε :=
    ⟨min 1 (ε / (K₁ + K₂ + 1)), lt_min one_pos (div_pos hε hS), min_le_left _ _,
      (le_div_iff₀ hS).1 (min_le_right _ _)⟩
  -- `δ₁` for `f` and `δ₂` for `g` at level `η`; then `δ = min{δ₁, δ₂/(K₁ + η)}`.
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf η hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg η hη
  have hL : 0 < K₁ + η := by linarith
  refine ⟨min δ₁ (δ₂ / (K₁ + η)), lt_min hδ₁ (div_pos hδ₂ hL), fun x' hx' hd => ?_⟩
  -- `d(f x', f x) ≤ (K₁ + η) d(x', x) < δ₂`, and `f x' ∈ B`, so the bound for `g` applies.
  have hfx : dist (f x') (f x) ≤ (K₁ + η) * dist x' x := h₁ x' hx' (hd.trans_le (min_le_left _ _))
  have hd₂ : (K₁ + η) * dist x' x < δ₂ := by
    rw [← lt_div_iff₀' hL]
    exact hd.trans_le (min_le_right _ _)
  have hgx := h₂ (f x') (hfAB hx') (hfx.trans_lt hd₂)
  -- `(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + η(K₁ + K₂ + 1) ≤ K₁K₂ + ε`.
  have hη2 : η * (K₁ + K₂ + η) ≤ η * (K₁ + K₂ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  calc dist (g (f x')) (g (f x)) ≤ (K₂ + η) * dist (f x') (f x) := hgx
    _ ≤ (K₂ + η) * ((K₁ + η) * dist x' x) := mul_le_mul_of_nonneg_left hfx (by linarith)
    _ = (K₁ * K₂ + η * (K₁ + K₂ + η)) * dist x' x := by ring
    _ ≤ (K₁ * K₂ + ε) * dist x' x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
/-- Union rule for pointwise upper Lipschitz bounds (used for Simon Ch. 6, Lemma 5.4, p. 162,
where `y` may lie on several closed faces): if `g` is `K`-Lipschitz at `y` within `G k ∩ B` for
every closed piece `G k ∋ y`, and `B ⊆ ⋃ k, G k` with finitely many pieces, then `g` is
`K`-Lipschitz at `y` within `B`.  Pieces missing `y` stay a positive distance away from `y`, and
the minimum of finitely many radii is a common radius. -/
theorem Submission.dr_cc_lip_at_union : ∀ (X Y : Type) [PseudoMetricSpace X] [PseudoMetricSpace Y] (ι : Type) [Finite ι] (G : ι → Set X) (B : Set X) (g : X → Y) (y : X) (K : ℝ), (∀ k, IsClosed (G k)) → B ⊆ ⋃ k, G k → (∀ k, y ∈ G k → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ G k ∩ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ B, dist y' y < δ → dist (g y') (g y) ≤ (K + ε) * dist y' y := by
  intro X Y _ _ ι _ G B g y K hG hB hloc ε hε
  -- A radius `r k > 0` for each piece: from the hypothesis if `y ∈ G k`, and otherwise a ball
  -- around `y` missing the closed set `G k` (the bound then holds vacuously).
  have hr : ∀ k, ∃ r : ℝ, 0 < r ∧
      ∀ y' ∈ G k ∩ B, dist y' y < r → dist (g y') (g y) ≤ (K + ε) * dist y' y := by
    intro k
    by_cases hyk : y ∈ G k
    · exact hloc k hyk ε hε
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hG k).isOpen_compl y hyk
      exact ⟨r, hr, fun y' hy' hdist => absurd hy'.1 (hball (Metric.mem_ball.2 hdist))⟩
  choose r hr0 hrb using hr
  -- A common radius `δ ≤ r k`: the minimum over the finite index type (`1` if `ι` is empty).
  obtain ⟨δ, hδ, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ r k := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun k => isEmptyElim k⟩
    · obtain ⟨k₀, hk₀⟩ := Finite.exists_min r
      exact ⟨r k₀, hr0 k₀, hk₀⟩
  -- A point `y' ∈ B` lies in some piece `G k`, and `dist y' y < δ ≤ r k`.
  refine ⟨δ, hδ, fun y' hy' hdist => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hB hy')
  exact hrb k y' ⟨hk, hy'⟩ (hdist.trans_le (hδr k))
/-- Simon Ch. 6, Lemma 5.4, proof p. 161, displays (1) and (2): elementary facts on the dual
skeleton `La = {y : y_i − a_i ∈ ℤ for m + 2 indices i}` of a point `a ∈ (1/4, 3/4)^d`.
`La` is a finite union of finite intersections of the closed sets `{y : y_i − a_i ∈ ℤ}`, hence
closed; a point agreeing with `a` on `m + 2` coordinates lies in `La`; and if `y ∈ La ∩ [0,1]^d`
lies on the ray from the centre `c` of a face of `[0,1]^d` (free coordinates `J`) through `x`,
then each witness coordinate `i` of `y` has `y_i − a_i ∈ (−1, 1) ∩ ℤ = {0}`, so `i ∈ J` (else
`a_i = y_i = c_i ∈ {0, 1}`) and `x_i = a_i` as `s > 0`. -/
theorem Submission.dr_cc_skeleton_facts :
    ∀ (m ℓ : ℕ) (a : Eucl (m + 1 + ℓ)), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → IsClosed La ∧ (∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)), m + 2 ≤ J.card → (∀ i ∈ J, c i = a i) → c ∈ La) ∧ ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s → (∀ i, y i - c i = s * (x i - c i)) → y ∈ La → x ∈ La := by
  intro m ℓ a ha La hLa
  refine ⟨?_, ?_, ?_⟩
  · -- `La = ⋃_{|J| = m+2} ⋂_{i ∈ J} {y : y_i − a_i ∈ ℤ}`, a finite union of closed sets.
    have hLa' : La = ⋃ J ∈ {J : Finset (Fin (m + 1 + ℓ)) | J.card = m + 2},
        ⋂ i ∈ J, (fun y : Eucl (m + 1 + ℓ) => y i - a i) ⁻¹' range ((↑) : ℤ → ℝ) := by
      rw [hLa]
      ext y
      simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_preimage, mem_range, exists_prop]
      exact exists_congr fun J => and_congr_right fun _ =>
        forall₂_congr fun i _ => exists_congr fun k => eq_comm
    rw [hLa']
    refine (toFinite _).isClosed_biUnion fun J _ => isClosed_biInter fun i _ => ?_
    exact Real.isClosed_range_intCast.preimage (by fun_prop)
  · -- Face centres: any `m + 2` of the coordinates where `c = a` witness `c ∈ La`.
    intro J c hJ hc
    obtain ⟨J', hJ'J, hJ'⟩ := Finset.exists_subset_card_eq hJ
    rw [hLa]
    exact ⟨J', hJ', fun i hi => ⟨0, by rw [hc i (hJ'J hi), sub_self, Int.cast_zero]⟩⟩
  · -- Cone property: every witness coordinate of `y` is free and has `x_i = y_i = a_i`.
    intro J c x y s hcJ hc01 hxc hy hs hyx hyLa
    rw [hLa] at hyLa ⊢
    obtain ⟨J', hJ', hyJ'⟩ := hyLa
    refine ⟨J', hJ', fun i hi => ⟨0, ?_⟩⟩
    obtain ⟨k, hk⟩ := hyJ' i hi
    obtain ⟨ha1, ha2⟩ := ha i
    obtain ⟨hy0, hy1⟩ := hy i
    -- `y_i − a_i ∈ (−1, 1)` is an integer, hence `0`.
    have hk0 : k = 0 := by
      have h1 : (-1 : ℝ) < k := by linarith
      have h2 : (k : ℝ) < 1 := by linarith
      have h1' : -1 < k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    rw [hk0, Int.cast_zero] at hk
    rw [Int.cast_zero]
    have h := hyx i
    by_cases hiJ : i ∈ J
    · rw [hcJ i hiJ, hk] at h
      exact (mul_eq_zero.1 h.symm).resolve_left hs.ne'
    · -- A fixed coordinate would give `a_i = y_i = c_i ∈ {0, 1}`.
      rw [hxc i hiJ, sub_self, mul_zero] at h
      rcases hc01 i hiJ with h0 | h0 <;> linarith
/-- Simon Ch. 6, Lemma 5.4, displays (4)–(7) (corrected similarity bound): if `y ∈ [0,1]^d` lies
on the ray `y = c + s(x - c)` from a face centre `c` (with `c_i = a_i` on `J`, `c_i ∈ {0,1}`
and `x_i = c_i` off `J`), then `min{1/4, s·dist(x, La)} ≤ dist(y, La)`.  A point `w ∈ La` either
has a witness coordinate where `y_i ∈ [0,1]` is `1/4`-far from `a_i + ℤ`, or all its witness
coordinates are free with zero shift, and then `w' = c + s⁻¹(w - c) ∈ La` and
`y - w = s(x - w')`. -/
theorem Submission.dr_cc_similarity_bound : ∀ (m ℓ : ℕ) (a : Eucl (m + 1 + ℓ)), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s → (∀ i, y i - c i = s * (x i - c i)) → min (1 / 4) (s * infDist x La) ≤ infDist y La := by
  intro m ℓ a ha La hLa J c x y s hcJ hcJc hxJc hy hs hrel
  -- `La = ∅` is trivial; otherwise it suffices to bound `dist y w` for each `w ∈ La`.
  rcases La.eq_empty_or_nonempty with hE | hne
  · simp [hE]
  rw [Metric.le_infDist hne]
  intro w hw
  -- The witness set `J'` (of `m + 2` indices) and the integers `k_i` for `w ∈ La`.
  rw [hLa, Set.mem_ofPred_eq] at hw
  obtain ⟨J', hJ'card, hJ'⟩ := hw
  -- `|y_i - w_i| ≤ |y - w|`, so a coordinate gap of `1/4` gives the bound.
  have hcoord : ∀ i, 1 / 4 ≤ |y i - w i| → min (1 / 4) (s * infDist x La) ≤ dist y w := by
    intro i hi
    have hi' := PiLp.dist_apply_le y w i
    rw [Real.dist_eq] at hi'
    exact (min_le_left _ _).trans (hi.trans hi')
  by_cases h1 : ∃ i ∈ J', i ∉ J
  · -- Case 1: a witness index `i ∉ J`, where `y_i = c_i ∈ {0, 1}`.
    obtain ⟨i, hiJ', hiJ⟩ := h1
    obtain ⟨k, hk⟩ := hJ' i hiJ'
    obtain ⟨ha1, ha2⟩ := ha i
    have hyi : y i = c i := by
      have hri := hrel i
      rw [hxJc i hiJ, sub_self, mul_zero, sub_eq_zero] at hri
      exact hri
    refine hcoord i ?_
    rcases hcJc i hiJ with hc | hc
    · have hk' : (k : ℝ) ≤ -1 ∨ (0 : ℝ) ≤ k := by
        rcases le_or_gt 0 k with h | h
        · right; exact_mod_cast h
        · left; exact_mod_cast (show k ≤ -1 by omega)
      rcases hk' with hk1 | hk1
      · exact (show (1 : ℝ) / 4 ≤ y i - w i by linarith).trans (le_abs_self _)
      · exact (show (1 : ℝ) / 4 ≤ -(y i - w i) by linarith).trans (neg_le_abs _)
    · have hk' : (k : ℝ) ≤ 0 ∨ (1 : ℝ) ≤ k := by
        rcases le_or_gt 1 k with h | h
        · right; exact_mod_cast h
        · left; exact_mod_cast (show k ≤ 0 by omega)
      rcases hk' with hk1 | hk1
      · exact (show (1 : ℝ) / 4 ≤ y i - w i by linarith).trans (le_abs_self _)
      · exact (show (1 : ℝ) / 4 ≤ -(y i - w i) by linarith).trans (neg_le_abs _)
  push Not at h1
  by_cases h2 : ∃ i ∈ J', w i ≠ a i
  · -- Case 2: a nonzero shift `k_i` at a witness index, where `y_i ∈ [0, 1]`.
    obtain ⟨i, hiJ', hwi⟩ := h2
    obtain ⟨k, hk⟩ := hJ' i hiJ'
    obtain ⟨ha1, ha2⟩ := ha i
    obtain ⟨hy0, hy1⟩ := hy i
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Int.cast_zero, sub_eq_zero] at hk
      exact hwi hk
    have hk' : (k : ℝ) ≤ -1 ∨ (1 : ℝ) ≤ k := by
      rcases le_or_gt 1 k with h | h
      · right; exact_mod_cast h
      · left; exact_mod_cast (show k ≤ -1 by omega)
    refine hcoord i ?_
    rcases hk' with hk1 | hk1
    · exact (show (1 : ℝ) / 4 ≤ y i - w i by linarith).trans (le_abs_self _)
    · exact (show (1 : ℝ) / 4 ≤ -(y i - w i) by linarith).trans (neg_le_abs _)
  -- Case 3: all witness indices lie in `J` with zero shifts; `w' = c + s⁻¹(w - c) ∈ La`.
  push Not at h2
  have hw' : c + s⁻¹ • (w - c) ∈ La := by
    rw [hLa, Set.mem_ofPred_eq]
    refine ⟨J', hJ'card, fun i hi => ⟨0, ?_⟩⟩
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, h2 i hi,
      hcJ i (h1 i hi), sub_self, mul_zero, add_zero, Int.cast_zero]
  have hyw : y - w = s • (x - (c + s⁻¹ • (w - c))) := by
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    calc y i - w i = (y i - c i) - (w i - c i) := by ring
      _ = s * (x i - c i) - s * s⁻¹ * (w i - c i) := by rw [hrel i, mul_inv_cancel₀ hs.ne', one_mul]
      _ = s * (x i - (c i + s⁻¹ * (w i - c i))) := by ring
  have hdist : dist y w = s * dist x (c + s⁻¹ • (w - c)) := by
    rw [dist_eq_norm, dist_eq_norm, hyw, norm_smul, Real.norm_of_nonneg hs.le]
  rw [hdist]
  exact (min_le_right _ _).trans
    (mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem hw') hs.le)
/-- Simon Ch. 6, proof of Lemma 5.4: the radial retraction `ψ_F` with origin `c` (p. 161) of
`F = {x ∈ [0,1]^D : xᵢ = cᵢ (i ∉ J)}` onto its relative boundary, with its pointwise Lipschitz
bound (printed (8), p. 163).  Here `g(x) = c + N(x - c)⁻¹ • (x - c)` for the gauge
`N(v) = max_{i ∈ J} max (vᵢ/(1 - aᵢ)) (-vᵢ/aᵢ)`, and `s = N(x - c)⁻¹`. -/
theorem Submission.dr_cc_radial_map : ∀ (D : ℕ) (a : Eucl D), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ (J : Finset (Fin D)) (c : Eucl D), (∀ i ∈ J, c i = a i) → ∃ g : Eucl D → Eucl D, ∀ x : Eucl D, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i ∉ J, x i = c i) → x ≠ c → (∀ i, 0 ≤ g x i ∧ g x i ≤ 1) ∧ (∃ i ∈ J, g x i = 0 ∨ g x i = 1) ∧ ∃ s : ℝ, 0 < s ∧ (∀ i, g x i - c i = s * (x i - c i)) ∧ s * dist x c ≤ Real.sqrt (D : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl D, (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) → dist x' x < δ → dist (g x') (g x) ≤ ((1 + 4 * Real.sqrt (D : ℝ)) * s + ε) * dist x' x := by
  intro D a ha J c hcJ
  -- Step 1: for `J = ∅` the face is `{c}`, so no `x` is admissible.
  rcases J.eq_empty_or_nonempty with hJ | hJ
  · refine ⟨id, fun x _ hxJ hxc => absurd ?_ hxc⟩
    ext i
    exact hxJ i (by simp [hJ])
  -- Step 0: `aᵢ, 1 - aᵢ > 1/4`, coordinates are bounded by the norm, `diam [0,1]^D ≤ √D`.
  have ha0 : ∀ i, 0 < a i := fun i => by linarith [(ha i).1]
  have ha1 : ∀ i, 0 < 1 - a i := fun i => by linarith [(ha i).2]
  have hcoord : ∀ (v : Eucl D) (i : Fin D), |v i| ≤ ‖v‖ := by
    intro v i
    have h := PiLp.norm_apply_le v i
    rwa [Real.norm_eq_abs] at h
  have hdiam : ∀ p q : Eucl D, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → (∀ i, 0 ≤ q i ∧ q i ≤ 1) →
      dist p q ≤ Real.sqrt D := by
    intro p q hp hq
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (p i) (q i) ^ 2 ≤ ∑ _i : Fin D, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : 0 ≤ 1 - p i + q i := by linarith [(hp i).2, (hq i).1]
          have h2 : 0 ≤ 1 + p i - q i := by linarith [(hp i).1, (hq i).2]
          rw [Real.dist_eq, sq_abs]
          nlinarith [mul_nonneg h1 h2]
      _ = D := by simp
  -- Step 2: the gauge `N(v) = max_{i ∈ J} fᵢ(v)`, `fᵢ(v) = max (vᵢ/(1 - aᵢ)) (-vᵢ/aᵢ)`.
  obtain ⟨f, hf⟩ : ∃ f : Eucl D → Fin D → ℝ,
      ∀ v i, f v i = max (v i / (1 - a i)) (-v i / a i) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Eucl D → ℝ, ∀ v, N v = J.sup' hJ (f v) := ⟨_, fun _ => rfl⟩
  have hfN : ∀ v, ∀ i ∈ J, f v i ≤ N v := by
    intro v i hi
    rw [hN]
    exact Finset.le_sup' (f v) hi
  have hNatt : ∀ v, ∃ i ∈ J, N v = f v i := by
    intro v
    obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup' hJ (f v)
    exact ⟨i, hi, (hN v).trans h⟩
  -- (N2): each `fᵢ`, hence `N`, is `4`-Lipschitz.
  have hfLip : ∀ v w : Eucl D, ∀ i, f w i ≤ f v i + 4 * ‖w - v‖ := by
    intro v w i
    have hwv : |w i - v i| ≤ ‖w - v‖ := hcoord (w - v) i
    have e1 : |w i / (1 - a i) - v i / (1 - a i)| ≤ 4 * |w i - v i| := by
      rw [← sub_div, abs_div, abs_of_pos (ha1 i), div_le_iff₀ (ha1 i)]
      nlinarith [abs_nonneg (w i - v i), (ha i).2]
    have e2 : |-w i / a i - -v i / a i| ≤ 4 * |w i - v i| := by
      rw [← sub_div, abs_div, abs_of_pos (ha0 i), div_le_iff₀ (ha0 i), neg_sub_neg,
        abs_sub_comm (v i) (w i)]
      nlinarith [abs_nonneg (w i - v i), (ha i).1]
    have e3 := (abs_le.mp (abs_max_sub_max_le_max (w i / (1 - a i)) (-w i / a i)
      (v i / (1 - a i)) (-v i / a i))).2
    have e4 := max_le e1 e2
    rw [hf, hf]
    linarith
  have hNle : ∀ v w : Eucl D, N w ≤ N v + 4 * ‖w - v‖ := by
    intro v w
    rw [hN w]
    exact Finset.sup'_le hJ (f w) fun i hi => (hfLip v w i).trans (by linarith [hfN v i hi])
  have hNlip : ∀ v w : Eucl D, |N w - N v| ≤ 4 * ‖w - v‖ := by
    intro v w
    rw [abs_le]
    constructor
    · have h := hNle w v
      rw [norm_sub_rev] at h
      linarith
    · linarith [hNle v w]
  -- Step 8 (core): the estimate `|u w - t v| ≤ ((1 + 4√D) t + ε) |w - v|` for `t = N(v)⁻¹`,
  -- `u = N(w)⁻¹`, written with `W = w - v`, `V = v`, `ν = N(v)`, `μ = N(w)`, `ρ = |w - v|`.
  have key : ∀ (ν μ ρ ε : ℝ) (V W : Eucl D), 0 < ν → ‖W‖ = ρ → |μ - ν| ≤ 4 * ρ →
      ν⁻¹ * ‖V‖ ≤ Real.sqrt D → ρ < ν / 8 → ρ < ε * ν ^ 2 / (8 * (1 + 4 * Real.sqrt D)) →
      ‖μ⁻¹ • W + (μ⁻¹ - ν⁻¹) • V‖ ≤ ((1 + 4 * Real.sqrt D) * ν⁻¹ + ε) * ρ := by
    intro ν μ ρ ε V W hν hW hμν hV hρ1 hρ2
    have hβ : 0 < 1 + 4 * Real.sqrt D := by positivity
    have hρ0 : 0 ≤ ρ := hW ▸ norm_nonneg W
    have hμ : ν / 2 < μ := by linarith [(abs_le.mp hμν).1]
    have hμ0 : 0 < μ := by linarith
    have ht : 0 < ν⁻¹ := inv_pos.mpr hν
    have hu : 0 < μ⁻¹ := inv_pos.mpr hμ0
    have htν : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν.ne'
    have huμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0.ne'
    generalize ν⁻¹ = t at ht htν hV ⊢
    generalize μ⁻¹ = u at hu huμ ⊢
    -- (b): `u - t = u t (ν - μ)`, so `|u - t| ≤ 4 u t ρ`; and `u < 2 t`.
    have hut : u - t = u * t * (ν - μ) := by linear_combination (-u) * htν + t * huμ
    have habs : |u - t| ≤ 4 * u * t * ρ := by
      rw [hut, abs_mul, abs_of_pos (mul_pos hu ht), abs_sub_comm ν μ]
      have h := mul_le_mul_of_nonneg_left hμν (mul_pos hu ht).le
      linarith
    have hu2t : u < 2 * t := by
      have h1 : u * (μ * ν) = ν := by rw [← mul_assoc, huμ, one_mul]
      have h2 : 2 * t * (μ * ν) = 2 * μ := by
        have h : 2 * t * (μ * ν) = 2 * μ * (t * ν) := by ring
        rw [h, htν, mul_one]
      have h3 : u * (μ * ν) < 2 * t * (μ * ν) := by rw [h1, h2]; linarith
      exact lt_of_mul_lt_mul_right h3 (mul_pos hμ0 hν).le
    -- (d): `u ≤ t + 8 t² ρ` and `8 (1 + 4√D) t² ρ ≤ ε`.
    have hu_le : u ≤ t + 8 * t ^ 2 * ρ := by
      have h1 : u - t ≤ 4 * u * t * ρ := (le_abs_self _).trans habs
      have h2 := mul_le_mul_of_nonneg_right hu2t.le (by positivity : (0 : ℝ) ≤ 4 * t * ρ)
      nlinarith
    have h8 : 8 * (1 + 4 * Real.sqrt D) * t ^ 2 * ρ ≤ ε := by
      have h1 : ρ * (8 * (1 + 4 * Real.sqrt D)) < ε * ν ^ 2 := by
        rwa [lt_div_iff₀ (by positivity)] at hρ2
      calc 8 * (1 + 4 * Real.sqrt D) * t ^ 2 * ρ
          = t ^ 2 * (ρ * (8 * (1 + 4 * Real.sqrt D))) := by ring
        _ ≤ t ^ 2 * (ε * ν ^ 2) := mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = ε * (t * ν) ^ 2 := by ring
        _ = ε := by rw [htν, one_pow, mul_one]
    -- (a), (c), (e).
    calc ‖u • W + (u - t) • V‖ ≤ ‖u • W‖ + ‖(u - t) • V‖ := norm_add_le _ _
      _ = u * ρ + |u - t| * ‖V‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu, hW]
      _ ≤ u * ρ + 4 * u * t * ρ * ‖V‖ := by
          have h := mul_le_mul_of_nonneg_right habs (norm_nonneg V)
          linarith
      _ = u * ρ * (1 + 4 * (t * ‖V‖)) := by ring
      _ ≤ u * ρ * (1 + 4 * Real.sqrt D) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hu.le hρ0)
          linarith
      _ = (1 + 4 * Real.sqrt D) * u * ρ := by ring
      _ ≤ (1 + 4 * Real.sqrt D) * (t + 8 * t ^ 2 * ρ) * ρ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu_le hβ.le) hρ0
      _ = ((1 + 4 * Real.sqrt D) * t + 8 * (1 + 4 * Real.sqrt D) * t ^ 2 * ρ) * ρ := by ring
      _ ≤ ((1 + 4 * Real.sqrt D) * t + ε) * ρ := by
          refine mul_le_mul_of_nonneg_right ?_ hρ0
          linarith
  -- Step 3: the map `g(y) = c + N(y - c)⁻¹ (y - c)`.
  obtain ⟨g, hg⟩ : ∃ g : Eucl D → Eucl D, ∀ y, g y = c + (N (y - c))⁻¹ • (y - c) :=
    ⟨_, fun _ => rfl⟩
  have hgi : ∀ y i, g y i = c i + (N (y - c))⁻¹ * (y i - c i) := by
    intro y i
    rw [hg]
    rfl
  refine ⟨g, fun x hx hxJ hxc => ?_⟩
  -- Step 4: `ν = N(x - c) > 0` (N3); `s = ν⁻¹`.
  have hxc_i : ∀ i, (x - c) i = x i - c i := fun i => rfl
  have hν : 0 < N (x - c) := by
    by_contra hle
    rw [not_lt] at hle
    apply hxc
    ext i
    by_cases hi : i ∈ J
    · have h := (hfN (x - c) i hi).trans hle
      rw [hf, max_le_iff, div_le_iff₀ (ha1 i), div_le_iff₀ (ha0 i), zero_mul, zero_mul,
        hxc_i] at h
      linarith [h.1, h.2]
    · exact hxJ i hi
  -- Step 5: `g(x) ∈ [0,1]^D` (printed (R1)).
  have hgx_cube : ∀ i, 0 ≤ g x i ∧ g x i ≤ 1 := by
    intro i
    rw [hgi]
    by_cases hi : i ∈ J
    · have h := hfN (x - c) i hi
      rw [hf, max_le_iff, div_le_iff₀ (ha1 i), div_le_iff₀ (ha0 i), hxc_i] at h
      have k1 : (N (x - c))⁻¹ * (x i - c i) ≤ 1 - a i := by
        rw [inv_mul_le_iff₀ hν]
        exact h.1
      have k2 : -((N (x - c))⁻¹ * (x i - c i)) ≤ a i := by
        rw [← mul_neg, inv_mul_le_iff₀ hν]
        exact h.2
      constructor <;> linarith [hcJ i hi]
    · rw [← hxJ i hi, sub_self, mul_zero, add_zero]
      exact hx i
  -- Step 7: `s |x - c| = |g(x) - c| ≤ √D` (printed (R5)), as `c ∈ [0,1]^D`.
  have hc_cube : ∀ i, 0 ≤ c i ∧ c i ≤ 1 := by
    intro i
    by_cases hi : i ∈ J
    · rw [hcJ i hi]
      exact ⟨(ha0 i).le, by linarith [ha1 i]⟩
    · rw [← hxJ i hi]
      exact hx i
  have hR5 : (N (x - c))⁻¹ * ‖x - c‖ ≤ Real.sqrt D := by
    have h := hdiam (g x) c hgx_cube hc_cube
    rwa [hg, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hν)] at h
  refine ⟨hgx_cube, ?_, (N (x - c))⁻¹, inv_pos.mpr hν, fun i => by rw [hgi]; ring,
    by rw [dist_eq_norm]; exact hR5, ?_⟩
  · -- Step 6: a coordinate `i₀ ∈ J` realizing the maximum is sent to `0` or `1`.
    obtain ⟨i₀, hi₀, hmax⟩ := hNatt (x - c)
    refine ⟨i₀, hi₀, ?_⟩
    rw [hgi, hcJ i₀ hi₀]
    rw [hf, hxc_i, hcJ i₀ hi₀] at hmax
    rcases le_total (-(x i₀ - a i₀) / a i₀) ((x i₀ - a i₀) / (1 - a i₀)) with h | h
    · right
      rw [max_eq_left h] at hmax
      have e : x i₀ - a i₀ = N (x - c) * (1 - a i₀) := by
        rw [hmax, div_mul_cancel₀ _ (ha1 i₀).ne']
      rw [e, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      ring
    · left
      rw [max_eq_right h] at hmax
      have e : x i₀ - a i₀ = -(N (x - c) * a i₀) := by
        rw [hmax, div_mul_cancel₀ _ (ha0 i₀).ne', neg_neg]
      rw [e, mul_neg, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      ring
  · -- Step 8: the pointwise estimate (printed (8)), with `δ = min (ν/8) (εν²/(8(1 + 4√D)))`.
    intro ε hε
    refine ⟨min (N (x - c) / 8) (ε * N (x - c) ^ 2 / (8 * (1 + 4 * Real.sqrt D))),
      lt_min (by linarith) (div_pos (mul_pos hε (pow_pos hν 2)) (by positivity)), ?_⟩
    intro x' _ _ hx'
    have hid : g x' - g x = (N (x' - c))⁻¹ • ((x' - c) - (x - c)) +
        ((N (x' - c))⁻¹ - (N (x - c))⁻¹) • (x - c) := by
      rw [hg, hg]
      module
    have hwv : ‖(x' - c) - (x - c)‖ = dist x' x := by
      rw [sub_sub_sub_cancel_right, dist_eq_norm]
    have hμν : |N (x' - c) - N (x - c)| ≤ 4 * dist x' x := by
      have h := hNlip (x - c) (x' - c)
      rwa [hwv] at h
    rw [dist_eq_norm (g x') (g x), hid]
    exact key (N (x - c)) (N (x' - c)) (dist x' x) ε (x - c) ((x' - c) - (x - c)) hν hwv hμν hR5
      (hx'.trans_le (min_le_left _ _)) (hx'.trans_le (min_le_right _ _))

/-- Simon Ch. 6, Lemma 5.4, printed proof p. 161 (book `n = m + 1`), in the one-step form
`ψ₀ = R^ℓ`.  A point `y ∈ C ∖ La` whose carrier `J(y) = {i : 0 < yᵢ < 1}` has at least `m + 2`
elements is pushed radially from the centre `a_F` of its carrier face `F` onto `∂F`,
`R(y)ᵢ = aᵢ + (yᵢ - aᵢ) / N(y)` on `J(y)`, with the gauge
`N(y) = max_{i ∈ J(y)} max ((yᵢ - aᵢ) / (1 - aᵢ), (aᵢ - yᵢ) / aᵢ)`; `R` fixes every other point.
Each step stays in `C ∖ La` (cone property of `dr_cc_skeleton_facts`) and lowers `|J(y)|`, so
`R^ℓ` maps `C ∖ La` into the `(m+1)`-skeleton (α) and fixes the `(m+1)`-skeleton (S1); `R`
commutes with integer translations (β); and the exit point `y` of the ray from `a_F` through
`x ∈ F ∖ La` is `R(x)` or `x` itself (S2). -/
theorem Submission.dr_cc_construction :
    ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ a : Eucl (m + 1 + ℓ), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) →
      ∀ La : Set (Eucl (m + 1 + ℓ)),
        La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧
          ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} →
        ∃ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
          (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
            (∀ i, 0 ≤ ψ₀ x i ∧ ψ₀ x i ≤ 1) ∧
              ∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ψ₀ x i = 0 ∨ ψ₀ x i = 1) ∧
          (∀ x x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
            (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → (∀ i, ∃ k : ℤ, x' i - x i = k) →
              ∀ i, ψ₀ x' i - ψ₀ x i = x' i - x i) ∧
          (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
            (∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, x i = 0 ∨ x i = 1) →
              ψ₀ x = x) ∧
          ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), m + 2 ≤ J.card →
            (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
            x ∉ La → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s →
            (∀ i, y i - c i = s * (x i - c i)) → (∃ i ∈ J, y i = 0 ∨ y i = 1) → ψ₀ y = ψ₀ x := by
  intro m ℓ _ a ha La hLa
  classical
  -- Cone property: if `y ∈ C ∩ La` lies on the ray from the face centre `c` through `x`
  -- (`y - c = s • (x - c)`, `s > 0`), then `x ∈ La`.
  obtain ⟨-, -, hcone⟩ := Submission.dr_cc_skeleton_facts m ℓ a ha La hLa
  have ha1 : ∀ i, 0 < a i := fun i => by linarith [(ha i).1]
  have ha2 : ∀ i, 0 < 1 - a i := fun i => by linarith [(ha i).2]
  -- The carrier `J(y) = {i : 0 < yᵢ < 1}`.
  obtain ⟨Jx, hJx⟩ : ∃ Jx : Eucl (m + 1 + ℓ) → Finset (Fin (m + 1 + ℓ)),
      ∀ y i, i ∈ Jx y ↔ (0 < y i ∧ y i < 1) :=
    ⟨fun y => Finset.univ.filter (fun i => 0 < y i ∧ y i < 1), fun y i => by simp⟩
  have hoff01 : ∀ y : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → ∀ i, i ∉ Jx y →
      y i = 0 ∨ y i = 1 := by
    intro y hy i hi
    rw [hJx] at hi
    rcases (hy i).1.lt_or_eq with h0 | h0
    · exact Or.inr (le_antisymm (hy i).2 (not_lt.1 fun h1 => hi ⟨h0, h1⟩))
    · exact Or.inl h0.symm
  -- The gauge `N(y) = max_{i ∈ J(y)} max ((yᵢ - aᵢ) / (1 - aᵢ), (aᵢ - yᵢ) / aᵢ)`.
  obtain ⟨N, hNle, hNex⟩ : ∃ N : Eucl (m + 1 + ℓ) → ℝ,
      (∀ y, ∀ i ∈ Jx y, max ((y i - a i) / (1 - a i)) ((a i - y i) / a i) ≤ N y) ∧
      (∀ y, (Jx y).Nonempty → ∃ i ∈ Jx y,
        N y = max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) := by
    refine ⟨fun y => if h : (Jx y).Nonempty then
      (Jx y).sup' h (fun i => max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) else 0, ?_, ?_⟩
    · intro y i hi
      have h : (Jx y).Nonempty := ⟨i, hi⟩
      simp only [dite_eq_left h]
      exact Finset.le_sup' (fun i => max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) hi
    · intro y h
      obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' h
        (fun i => max ((y i - a i) / (1 - a i)) ((a i - y i) / a i))
      exact ⟨i, hi, by simp only [dite_eq_left h]; exact he⟩
  -- `y` is *active* if `y ∈ C ∖ La` and `|J(y)| ≥ m + 2`.  `R` retracts an active `y` radially
  -- from the centre of its carrier face onto the boundary of that face and fixes all other points.
  obtain ⟨R, hRa, hRn⟩ : ∃ R : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
      (∀ y, ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) →
        ∀ i, R y i = if i ∈ Jx y then a i + (y i - a i) / N y else y i) ∧
      (∀ y, ¬((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) → R y = y) := by
    refine ⟨fun y => if ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) then
      WithLp.toLp 2 (fun i => if i ∈ Jx y then a i + (y i - a i) / N y else y i) else y, ?_, ?_⟩
    · intro y hy i
      dsimp only
      rw [ite_eq_left hy]
    · intro y hy
      dsimp only
      rw [ite_eq_right hy]
  -- One step: for active `y`, `N(y) > 0`, `R(y) ∈ C ∖ La` and `|J(R y)| < |J(y)|`.
  have step : ∀ y, ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card) →
      0 < N y ∧ (∀ i, 0 ≤ R y i ∧ R y i ≤ 1) ∧ R y ∉ La ∧ (Jx (R y)).card + 1 ≤ (Jx y).card := by
    intro y hact
    have hRi := hRa y hact
    obtain ⟨hyC, hyL, hyJ⟩ := hact
    -- `N(y) ≤ 0` would force `y = a` on `J(y)`, hence `y ∈ La`.
    have hNpos : 0 < N y := by
      by_contra hle
      rw [not_lt] at hle
      apply hyL
      rw [hLa]
      obtain ⟨J', hJ'sub, hJ'card⟩ := Finset.exists_subset_card_eq hyJ
      refine ⟨J', hJ'card, fun i hi => ⟨0, ?_⟩⟩
      have hi' := hJ'sub hi
      have h := (hNle y i hi').trans hle
      have h1 : (y i - a i) / (1 - a i) ≤ 0 := (le_max_left _ _).trans h
      have h2 : (a i - y i) / a i ≤ 0 := (le_max_right _ _).trans h
      rw [div_le_iff₀ (ha2 i), zero_mul] at h1
      rw [div_le_iff₀ (ha1 i), zero_mul] at h2
      simp only [Int.cast_zero]
      linarith
    have hbd : ∀ i ∈ Jx y, 0 ≤ a i + (y i - a i) / N y ∧ a i + (y i - a i) / N y ≤ 1 := by
      intro i hi
      have h := hNle y i hi
      have h1 : (y i - a i) / (1 - a i) ≤ N y := (le_max_left _ _).trans h
      have h2 : (a i - y i) / a i ≤ N y := (le_max_right _ _).trans h
      rw [div_le_iff₀ (ha2 i)] at h1
      rw [div_le_iff₀ (ha1 i)] at h2
      constructor
      · have h3 : (a i - y i) / N y ≤ a i := by rw [div_le_iff₀ hNpos]; linarith
        have e : (y i - a i) / N y = -((a i - y i) / N y) := by ring
        linarith
      · have h3 : (y i - a i) / N y ≤ 1 - a i := by rw [div_le_iff₀ hNpos]; linarith
        linarith
    have hRC : ∀ i, 0 ≤ R y i ∧ R y i ≤ 1 := by
      intro i
      rw [hRi]
      split_ifs with hi
      · exact hbd i hi
      · exact hyC i
    -- A maximising coordinate `i₀` of the gauge is sent to `0` or `1`.
    have hne : (Jx y).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨i₀, hi₀, hNi₀⟩ := hNex y hne
    have hext : R y i₀ = 0 ∨ R y i₀ = 1 := by
      rw [hRi, ite_eq_left hi₀]
      rcases max_cases ((y i₀ - a i₀) / (1 - a i₀)) ((a i₀ - y i₀) / a i₀) with ⟨hm, _⟩ | ⟨hm, _⟩
      · right
        rw [hm] at hNi₀
        have h4 : (y i₀ - a i₀) / N y = 1 - a i₀ := by
          rw [div_eq_iff hNpos.ne', hNi₀, mul_comm, div_mul_cancel₀ _ (ha2 i₀).ne']
        linarith
      · left
        rw [hm] at hNi₀
        have h4 : (a i₀ - y i₀) / N y = a i₀ := by
          rw [div_eq_iff hNpos.ne', hNi₀, mul_comm, div_mul_cancel₀ _ (ha1 i₀).ne']
        have e : (y i₀ - a i₀) / N y = -((a i₀ - y i₀) / N y) := by ring
        linarith
    have hsub : Jx (R y) ⊆ (Jx y).erase i₀ := by
      intro i hi
      rw [hJx] at hi
      rw [Finset.mem_erase]
      constructor
      · rintro rfl
        rcases hext with h | h <;> rw [h] at hi <;> linarith [hi.1, hi.2]
      · by_contra hni
        rw [hRi, ite_eq_right hni] at hi
        exact hni ((hJx y i).2 hi)
    have hcard : (Jx (R y)).card + 1 ≤ (Jx y).card := by
      have h5 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi₀] at h5
      have : 0 < (Jx y).card := Finset.card_pos.2 hne
      omega
    -- `R(y) - c = N(y)⁻¹ (y - c)` for the centre `c` of the carrier face, so `R(y) ∉ La`.
    have hRL : R y ∉ La := by
      intro hRyL
      apply hyL
      let c : Eucl (m + 1 + ℓ) := WithLp.toLp 2 (fun i => if i ∈ Jx y then a i else y i)
      have hc : ∀ i, c i = if i ∈ Jx y then a i else y i := fun i => rfl
      refine hcone (Jx y) c y (R y) (N y)⁻¹ (fun i hi => by rw [hc, ite_eq_left hi])
        (fun i hi => by rw [hc, ite_eq_right hi]; exact hoff01 y hyC i hi)
        (fun i hi => by rw [hc, ite_eq_right hi]) hRC (inv_pos.2 hNpos) (fun i => ?_) hRyL
      rw [hRi, hc]
      split_ifs with hi
      · ring
      · ring
    exact ⟨hNpos, hRC, hRL, hcard⟩
  -- Iteration: `R^k` stays in `C ∖ La`, and `|J(R^k y)| ≤ m + 1` or `|J(R^k y)| + k ≤ |J(y)|`.
  have iter : ∀ k : ℕ, ∀ y : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → y ∉ La →
      (∀ i, 0 ≤ R^[k] y i ∧ R^[k] y i ≤ 1) ∧ R^[k] y ∉ La ∧
        ((Jx (R^[k] y)).card ≤ m + 1 ∨ (Jx (R^[k] y)).card + k ≤ (Jx y).card) := by
    intro k
    induction k with
    | zero => intro y hyC hyL; exact ⟨hyC, hyL, Or.inr (by simp)⟩
    | succ k ih =>
      intro y hyC hyL
      obtain ⟨hzC, hzL, hzJ⟩ := ih y hyC hyL
      rw [Function.iterate_succ_apply']
      by_cases hact : ((∀ i, 0 ≤ R^[k] y i ∧ R^[k] y i ≤ 1) ∧ R^[k] y ∉ La ∧
          m + 2 ≤ (Jx (R^[k] y)).card)
      · obtain ⟨-, hC', hL', hJ'⟩ := step _ hact
        refine ⟨hC', hL', ?_⟩
        have := hact.2.2
        omega
      · rw [hRn _ hact]
        refine ⟨hzC, hzL, Or.inl ?_⟩
        by_contra h
        exact hact ⟨hzC, hzL, by omega⟩
  -- After `ℓ` steps the carrier has at most `m + 1` elements, as `|J(y)| ≤ m + 1 + ℓ`.
  have hfinal : ∀ y : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → y ∉ La →
      (Jx (R^[ℓ] y)).card ≤ m + 1 := by
    intro y hyC hyL
    obtain ⟨-, -, h⟩ := iter ℓ y hyC hyL
    have := Finset.card_le_univ (Jx y)
    rw [Fintype.card_fin] at this
    omega
  refine ⟨R^[ℓ], ?_, ?_, ?_, ?_⟩
  · -- (α): at least `ℓ` coordinates of `R^ℓ x` lie outside the carrier, i.e. in `{0, 1}`.
    intro x hx hxL
    obtain ⟨hC, -, -⟩ := iter ℓ x hx hxL
    have hc := hfinal x hx hxL
    refine ⟨hC, ?_⟩
    have hcompl : ℓ ≤ (Finset.univ \ Jx (R^[ℓ] x)).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_fin]; omega
    obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hcompl
    exact ⟨I, hIcard, fun i hi => hoff01 _ hC i (Finset.mem_sdiff.1 (hIsub hi)).2⟩
  · -- (β): `R` commutes with integer translations inside `C ∖ La` (same carrier, same gauge).
    have stepT : ∀ y y' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → y ∉ La →
        (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → y' ∉ La → (∀ i, ∃ k : ℤ, y' i - y i = k) →
        ∀ i, R y' i - R y i = y' i - y i := by
      intro y y' hyC hyL hy'C hy'L hz
      have hsame : ∀ i, (0 < y i ∧ y i < 1) ∨ (0 < y' i ∧ y' i < 1) → y' i = y i := by
        intro i hi
        obtain ⟨k, hk⟩ := hz i
        have hk0 : k = 0 := by
          have hb : (-1 : ℝ) < k ∧ (k : ℝ) < 1 := by
            rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · constructor <;> linarith [(hy'C i).1, (hy'C i).2]
            · constructor <;> linarith [(hyC i).1, (hyC i).2]
          have h1 : (-1 : ℤ) < k := by exact_mod_cast hb.1
          have h2 : k < 1 := by exact_mod_cast hb.2
          omega
        rw [hk0, Int.cast_zero] at hk
        linarith
      have hJeq : Jx y' = Jx y := by
        ext i
        rw [hJx, hJx]
        constructor
        · intro h; rw [← hsame i (Or.inr h)]; exact h
        · intro h; rw [hsame i (Or.inl h)]; exact h
      by_cases hact : ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ y ∉ La ∧ m + 2 ≤ (Jx y).card)
      · have hact' : ((∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ y' ∉ La ∧ m + 2 ≤ (Jx y').card) :=
          ⟨hy'C, hy'L, by rw [hJeq]; exact hact.2.2⟩
        have hterm : ∀ i ∈ Jx y, max ((y' i - a i) / (1 - a i)) ((a i - y' i) / a i) =
            max ((y i - a i) / (1 - a i)) ((a i - y i) / a i) := by
          intro i hi
          rw [hsame i (Or.inl ((hJx y i).1 hi))]
        have hNeq : N y' = N y := by
          have hne : (Jx y).Nonempty := Finset.card_pos.1 (by have := hact.2.2; omega)
          obtain ⟨i₀, hi₀, h₀⟩ := hNex y hne
          obtain ⟨i₁, hi₁, h₁⟩ := hNex y' (by rw [hJeq]; exact hne)
          rw [hJeq] at hi₁
          apply le_antisymm
          · rw [h₁, hterm i₁ hi₁]; exact hNle y i₁ hi₁
          · rw [h₀, ← hterm i₀ hi₀]; exact hNle y' i₀ (by rw [hJeq]; exact hi₀)
        intro i
        rw [hRa y' hact' i, hRa y hact i, hJeq, hNeq]
        split_ifs with hi
        · rw [hsame i (Or.inl ((hJx y i).1 hi))]; ring
        · ring
      · have hact' : ¬((∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ y' ∉ La ∧ m + 2 ≤ (Jx y').card) := by
          rintro ⟨-, -, h⟩
          exact hact ⟨hyC, hyL, by rw [← hJeq]; exact h⟩
        intro i
        rw [hRn y hact, hRn y' hact']
    intro x x' hx hxL hx' hx'L hz
    have hk : ∀ k : ℕ, ∀ i, R^[k] x' i - R^[k] x i = x' i - x i := by
      intro k
      induction k with
      | zero => intro i; rfl
      | succ k ih =>
        intro i
        obtain ⟨hC, hL, -⟩ := iter k x hx hxL
        obtain ⟨hC', hL', -⟩ := iter k x' hx' hx'L
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hz' : ∀ j, ∃ k' : ℤ, R^[k] x' j - R^[k] x j = k' := fun j => by
          rw [ih j]; exact hz j
        rw [stepT _ _ hC hL hC' hL' hz' i, ih i]
    exact hk ℓ
  · -- (S1): `ℓ` coordinates in `{0, 1}` leave a carrier of size `≤ m + 1`, so `R` fixes `x`.
    rintro x hx hxL ⟨I, hIcard, hI⟩
    have hsub : Jx x ⊆ Finset.univ \ I := by
      intro i hi
      rw [hJx] at hi
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hiI => ?_⟩
      rcases hI i hiI with h | h <;> rw [h] at hi <;> linarith [hi.1, hi.2]
    have hc : (Jx x).card ≤ m + 1 := by
      have h5 := Finset.card_le_card hsub
      rw [Finset.card_univ_sdiff, Fintype.card_fin, hIcard] at h5
      omega
    have hR : R x = x := hRn x (fun h => by have := h.2.2; omega)
    exact Function.iterate_fixed hR ℓ
  · -- (S2): the exit point `y` of the ray from the face centre `c` through `x` is `R(x)` or `x`.
    intro J c x y s hJ hcJ hc01 hx hxL hxc hy hs hray hext
    have hyoff : ∀ i ∉ J, y i = c i := fun i hi => by
      have := hray i
      rw [hxc i hi, sub_self, mul_zero] at this
      linarith
    by_cases hint : ∀ i ∈ J, 0 < x i ∧ x i < 1
    · -- Case A: `x` lies in the relative interior of the face, so `J(x) = J`, `N(x) = s⁻¹` and
      -- `y = R(x)`; then `R^ℓ y = R (R^ℓ x) = R^ℓ x`.
      have hJeq : Jx x = J := by
        ext i
        rw [hJx]
        constructor
        · intro h
          by_contra hiJ
          rw [hxc i hiJ] at h
          rcases hc01 i hiJ with h0 | h0 <;> rw [h0] at h <;> linarith [h.1, h.2]
        · exact hint i
      have hact : ((∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x ∉ La ∧ m + 2 ≤ (Jx x).card) :=
        ⟨hx, hxL, by rw [hJeq]; exact hJ⟩
      have hterm_le : ∀ i ∈ J, max ((x i - a i) / (1 - a i)) ((a i - x i) / a i) ≤ s⁻¹ := by
        intro i hi
        have hyi := hy i
        have hr := hray i
        rw [hcJ i hi] at hr
        apply max_le
        · rw [div_le_iff₀ (ha2 i)]
          have h6 : s * (x i - a i) ≤ 1 - a i := by linarith [hyi.2]
          calc x i - a i = s⁻¹ * (s * (x i - a i)) := by field_simp
            _ ≤ s⁻¹ * (1 - a i) := mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hs.le)
        · rw [div_le_iff₀ (ha1 i)]
          have h6 : s * (a i - x i) ≤ a i := by linarith [hyi.1]
          calc a i - x i = s⁻¹ * (s * (a i - x i)) := by field_simp
            _ ≤ s⁻¹ * a i := mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hs.le)
      have hNx : N x = s⁻¹ := by
        apply le_antisymm
        · obtain ⟨i₀, hi₀, h₀⟩ := hNex x (Finset.card_pos.1 (by rw [hJeq]; omega))
          rw [h₀]
          rw [hJeq] at hi₀
          exact hterm_le i₀ hi₀
        · obtain ⟨i₁, hi₁J, hi₁⟩ := hext
          have hle := hNle x i₁ (by rw [hJeq]; exact hi₁J)
          have hr := hray i₁
          rw [hcJ i₁ hi₁J] at hr
          rcases hi₁ with h0 | h1
          · have h7 : (a i₁ - x i₁) / a i₁ = s⁻¹ := by
              rw [div_eq_iff (ha1 i₁).ne']
              rw [h0] at hr
              field_simp
              linarith
            rw [← h7]
            exact (le_max_right _ _).trans hle
          · have h7 : (x i₁ - a i₁) / (1 - a i₁) = s⁻¹ := by
              rw [div_eq_iff (ha2 i₁).ne']
              rw [h1] at hr
              field_simp
              linarith
            rw [← h7]
            exact (le_max_left _ _).trans hle
      have hRx : R x = y := by
        ext i
        rw [hRa x hact i, hJeq]
        split_ifs with hi
        · rw [hNx]
          have hr := hray i
          rw [hcJ i hi] at hr
          rw [div_inv_eq_mul]
          linarith
        · rw [hyoff i hi, hxc i hi]
      rw [← hRx, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
      have hc := hfinal x hx hxL
      exact hRn _ (fun h => by have := h.2.2; omega)
    · -- Case B: `x` lies on the relative boundary of the face; then `s = 1` and `y = x`.
      push Not at hint
      obtain ⟨i₂, hi₂J, hi₂⟩ := hint
      have hx01 : x i₂ = 0 ∨ x i₂ = 1 := by
        rcases (hx i₂).1.lt_or_eq with h0 | h0
        · right; exact le_antisymm (hx i₂).2 (hi₂ h0)
        · left; exact h0.symm
      have hs1 : s ≤ 1 := by
        have hr := hray i₂
        rw [hcJ i₂ hi₂J] at hr
        have hyi := hy i₂
        have hai1 := ha1 i₂
        have hai2 := ha2 i₂
        rcases hx01 with h0 | h1
        · rw [h0] at hr
          nlinarith
        · rw [h1] at hr
          nlinarith
      have hs1' : 1 ≤ s := by
        obtain ⟨i₁, hi₁J, hi₁⟩ := hext
        have hr := hray i₁
        rw [hcJ i₁ hi₁J] at hr
        have hxi := hx i₁
        have hai1 := ha1 i₁
        have hai2 := ha2 i₁
        rcases hi₁ with h0 | h1
        · rw [h0] at hr
          nlinarith [mul_nonneg hs.le hxi.1]
        · rw [h1] at hr
          nlinarith [mul_le_mul_of_nonneg_left hxi.2 hs.le]
      have hyx : y = x := by
        ext i
        have := hray i
        rw [le_antisymm hs1 hs1', one_mul] at this
        linarith
      rw [hyx]
/-- Simon Ch. 6, Lemma 5.4, claim (3) (pp. 162–163), as a pointwise upper Lipschitz bound.  Let
`ψ₀` satisfy (S1) (`ψ₀ x = x` on `C ∖ La` where `ℓ` coordinates lie in `{0, 1}`) and (S2) (on each
face of dimension `≥ m + 2`, `ψ₀` is constant along the rays from its centre `c` up to its
boundary).  Then near `x ∈ C ∖ La`, `|ψ₀ x' - ψ₀ x| ≤ (c₁ / dist(x, La) + ε) |x' - x|`.

Induction on the dimension `j` of the faces `F` of `C = [0,1]^d`, with
`c₁(j) = β r q^(j - (m + 2))`, `r = √d`, `β = 1 + 4r`, `q = 4rβ`.  On `F ∖ La`, `ψ₀ = ψ₀ ∘ g` for
the radial projection `g` from `c` onto `∂F` (S2).  For `j = m + 2`, `ψ₀ = g` there (S1).  For
`j + 1`, the bound at `g x` on the facets through `g x` glues to `∂F ∖ La` and composes with that
of `g`.  Finally `dist(g x, La) ≥ min(1/4, s dist(x, La))` turns `β s c₁(j) / dist(g x, La)` into
`c₁(j + 1) / dist(x, La)`. -/
theorem Submission.dr_cc_pointwise_lip :
    ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ a : Eucl (m + 1 + ℓ), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) →
      ∀ La : Set (Eucl (m + 1 + ℓ)),
        La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧
          ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} →
      ∀ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
        (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La →
          (∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, x i = 0 ∨ x i = 1) → ψ₀ x = x) →
        (∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), m + 2 ≤ J.card →
          (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
          x ∉ La → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s →
          (∀ i, y i - c i = s * (x i - c i)) → (∃ i ∈ J, y i = 0 ∨ y i = 1) → ψ₀ y = ψ₀ x) →
        ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La →
            dist x' x < δ → dist (ψ₀ x') (ψ₀ x) ≤ (c₁ / infDist x La + ε) * dist x' x := by
  intro m ℓ hℓ
  -- Constants: `r = √d ≥ 1`, `β = 1 + 4r ≤ q = 4rβ`, `c₁(j) = β r q^(j - (m + 2))`, `c₁ = c₁(d)`.
  obtain ⟨r, hr⟩ : ∃ r : ℝ, Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [← hr, Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ m + 1 + ℓ by omega)
  have hr0 : 0 ≤ r := by linarith
  have hβ : 0 < 1 + 4 * r := by linarith
  have hq : 0 < 4 * r * (1 + 4 * r) := mul_pos (by linarith) hβ
  have hβq : 1 + 4 * r ≤ 4 * r * (1 + 4 * r) := by nlinarith
  refine ⟨(1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (m + 1 + ℓ - (m + 2)), by positivity, ?_⟩
  intro a ha La hLa ψ₀ hS1 hS2
  -- `La` is closed, contains the centre of every face of dimension `≥ m + 2` (so `a ∈ La`), and
  -- has the cone property; so `dist(z, La) > 0` for `z ∉ La`.
  obtain ⟨hLac, hcLa, hcone⟩ := Submission.dr_cc_skeleton_facts m ℓ a ha La hLa
  have hLane : La.Nonempty :=
    ⟨a, hcLa Finset.univ a (by rw [Finset.card_univ, Fintype.card_fin]; omega) fun i _ => rfl⟩
  have hdpos : ∀ z, z ∉ La → 0 < infDist z La := fun z hz =>
    (hLac.notMem_iff_infDist_pos hLane).1 hz
  -- A face `(J, c)` (`c i = a i` on `J`, `c i ∈ {0, 1}` off `J`) has point set
  -- `F = {x ∈ C : x i = c i for i ∉ J}`.  For `|J| ≥ m + 2`, the radial map `g` from `c ∈ La`
  -- sends `F ∖ La` into `∂F ∖ La` with `ψ₀ ∘ g = ψ₀` there (S2), and is `β s`-Lipschitz at `x`.
  have setup : ∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)), m + 2 ≤ J.card →
      (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) →
      ∃ g : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ),
        (∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) →
          x' ∉ La → (∀ i, 0 ≤ g x' i ∧ g x' i ≤ 1) ∧ (∀ i ∉ J, g x' i = c i) ∧
            (∃ i ∈ J, g x' i = 0 ∨ g x' i = 1) ∧ g x' ∉ La ∧ ψ₀ (g x') = ψ₀ x') ∧
        ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i ∉ J, x i = c i) → x ∉ La →
          ∃ s : ℝ, 0 < s ∧ (∀ i, g x i - c i = s * (x i - c i)) ∧ s * infDist x La ≤ r ∧
            ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ),
              (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) → dist x' x < δ →
              dist (g x') (g x) ≤ ((1 + 4 * r) * s + ε) * dist x' x := by
    intro J c hJ hcJ hcJc
    obtain ⟨g, hg⟩ := Submission.dr_cc_radial_map (m + 1 + ℓ) a ha J c hcJ
    have hc : c ∈ La := hcLa J c hJ hcJ
    refine ⟨g, fun x' hx'C hx'F hx'La => ?_, fun x hxC hxF hxLa => ?_⟩
    · obtain ⟨hgC, hgJ, s', hs', hscale, -⟩ := hg x' hx'C hx'F fun h => hx'La (h ▸ hc)
      have hgF : ∀ i ∉ J, g x' i = c i := fun i hi => by
        have h := hscale i
        rwa [hx'F i hi, sub_self, mul_zero, sub_eq_zero] at h
      exact ⟨hgC, hgF, hgJ, fun h => hx'La (hcone J c x' (g x') s' hcJ hcJc hx'F hgC hs' hscale h),
        hS2 J c x' (g x') s' hJ hcJ hcJc hx'C hx'La hx'F hgC hs' hscale hgJ⟩
    · obtain ⟨-, -, s, hs, hscale, hsr, hlip⟩ := hg x hxC hxF fun h => hxLa (h ▸ hc)
      rw [hr] at hsr hlip
      exact ⟨s, hs, hscale,
        (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem hc) hs.le).trans hsr, hlip⟩
  -- Claim `P(j)`: on every face of dimension `j ≥ m + 2`, `ψ₀` is `c₁(j) / dist(x, La)`-Lipschitz
  -- at every `x ∈ F ∖ La` within `F ∖ La`.
  have key : ∀ j : ℕ, m + 2 ≤ j → ∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)),
      J.card = j → (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) →
      ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → (∀ i ∉ J, x i = c i) → x ∉ La →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ),
        (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → (∀ i ∉ J, x' i = c i) → x' ∉ La → dist x' x < δ →
        dist (ψ₀ x') (ψ₀ x) ≤
          ((1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) / infDist x La + ε) *
            dist x' x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      -- `|J| = m + 2`: `g` lands where `ℓ` coordinates lie in `{0, 1}`, so `ψ₀ = g` on `F ∖ La`
      -- by (S1), and `β s ≤ β r / dist(x, La)` as `s dist(x, La) ≤ s |x - c| ≤ r`.
      intro J c hJc hcJ hcJc x hxC hxF hxLa ε hε
      obtain ⟨g, hgA, hgx⟩ := setup J c hJc.ge hcJ hcJc
      have hψg : ∀ z : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ z i ∧ z i ≤ 1) → (∀ i ∉ J, z i = c i) →
          z ∉ La → ψ₀ z = g z := by
        intro z hzC hzF hzLa
        obtain ⟨hgzC, hgzF, ⟨i, hiJ, hi⟩, hgzLa, hψ⟩ := hgA z hzC hzF hzLa
        rw [← hψ]
        refine hS1 (g z) hgzC hgzLa ⟨insert i (Finset.univ \ J), ?_, fun k hk => ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hiJ]), Finset.card_univ_sdiff,
            Fintype.card_fin, hJc]
          omega
        · rcases Finset.mem_insert.1 hk with rfl | hk
          · exact hi
          · have hkJ : k ∉ J := (Finset.mem_sdiff.1 hk).2
            rw [hgzF k hkJ]
            exact hcJc k hkJ
      obtain ⟨s, hs, -, hsr, hlip⟩ := hgx x hxC hxF hxLa
      obtain ⟨δ, hδ, hδlip⟩ := hlip ε hε
      refine ⟨δ, hδ, fun x' hx'C hx'F hx'La hx'x => ?_⟩
      rw [hψg x' hx'C hx'F hx'La, hψg x hxC hxF hxLa]
      refine (hδlip x' hx'C hx'F hx'x).trans
        (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) dist_nonneg)
      rw [Nat.sub_self, pow_zero, mul_one, le_div_iff₀ (hdpos x hxLa)]
      nlinarith [mul_le_mul_of_nonneg_left hsr hβ.le]
    | succ j hj ih =>
      intro J c hJc hcJ hcJc x hxC hxF hxLa
      obtain ⟨g, hgA, hgx⟩ := setup J c (by omega) hcJ hcJc
      obtain ⟨s, hs, hscale, hsr, hlip⟩ := hgx x hxC hxF hxLa
      obtain ⟨hyC, hyF, -, hyLa, hψy⟩ := hgA x hxC hxF hxLa
      have hdx := hdpos x hxLa
      have hdy := hdpos (g x) hyLa
      -- `ψ₀` is `c₁(j) / dist(g x, La)`-Lipschitz at `g x` within `∂F ∖ La`: `P(j)` on each facet
      -- `F ∩ {y i = b}` (`i ∈ J`, `b ∈ {0, 1}`) through `g x`, glued over the finitely many facets.
      have hψB : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' ∈ {y' : Eucl (m + 1 + ℓ) |
          (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ (∀ i ∉ J, y' i = c i) ∧ (∃ i ∈ J, y' i = 0 ∨ y' i = 1) ∧
            y' ∉ La}, dist y' (g x) < δ → dist (ψ₀ y') (ψ₀ (g x)) ≤
          ((1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) / infDist (g x) La + ε) *
            dist y' (g x) := by
        have hcoord : ∀ k : Fin (m + 1 + ℓ), Continuous fun y' : Eucl (m + 1 + ℓ) => y' k :=
          fun k => PiLp.continuous_apply 2 _ k
        refine Submission.dr_cc_lip_at_union (Eucl (m + 1 + ℓ)) (Eucl (m + 1 + ℓ))
          (Fin (m + 1 + ℓ) × Bool) (fun p => {y' : Eucl (m + 1 + ℓ) | (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧
            (∀ i ∉ J, y' i = c i) ∧ p.1 ∈ J ∧ y' p.1 = if p.2 then 1 else 0}) _ ψ₀ (g x) _
          (fun p => ?_) ?_ ?_
        · -- Each facet is closed.
          have h1 : IsClosed {y' : Eucl (m + 1 + ℓ) | ∀ i, 0 ≤ y' i ∧ y' i ≤ 1} := by
            simp only [Set.ofPred_forall]
            exact isClosed_iInter fun i => (isClosed_le continuous_const (hcoord i)).inter
              (isClosed_le (hcoord i) continuous_const)
          have h2 : IsClosed {y' : Eucl (m + 1 + ℓ) | ∀ i ∉ J, y' i = c i} := by
            simp only [Set.ofPred_forall]
            exact isClosed_iInter fun i =>
              isClosed_iInter fun _ => isClosed_eq (hcoord i) continuous_const
          exact h1.inter (h2.inter
            (isClosed_const.inter (isClosed_eq (hcoord p.1) continuous_const)))
        · -- The facets cover `∂F ∖ La`.
          rintro y' ⟨hy'C, hy'F, ⟨i, hiJ, hi | hi⟩, -⟩
          · exact Set.mem_iUnion.2 ⟨(i, false), hy'C, hy'F, hiJ, by simp [hi]⟩
          · exact Set.mem_iUnion.2 ⟨(i, true), hy'C, hy'F, hiJ, by simp [hi]⟩
        · -- The facet through `g x` is the face `(J.erase i, c')`, `c' i = b`, of dimension `j`.
          rintro ⟨i, b⟩ hy ε hε
          obtain ⟨-, -, hiJ, hyi⟩ : (∀ k, 0 ≤ g x k ∧ g x k ≤ 1) ∧ (∀ k ∉ J, g x k = c k) ∧
              i ∈ J ∧ g x i = if b then 1 else 0 := hy
          obtain ⟨c', hc'i, hc'k⟩ : ∃ c' : Eucl (m + 1 + ℓ),
              c' i = (if b then 1 else 0) ∧ ∀ k ≠ i, c' k = c k :=
            ⟨WithLp.toLp 2 fun k => if k = i then (if b then 1 else 0) else c k, by simp,
              fun k hk => by simp [hk]⟩
          have hF' : ∀ z : Eucl (m + 1 + ℓ), (∀ k ∉ J, z k = c k) →
              z i = (if b then 1 else 0) → ∀ k ∉ J.erase i, z k = c' k := by
            intro z hzF hzi k hk
            by_cases hki : k = i
            · rw [hki, hzi, hc'i]
            · rw [hzF k fun h => hk (Finset.mem_erase.2 ⟨hki, h⟩), hc'k k hki]
          obtain ⟨δ, hδ, hδlip⟩ := ih (J.erase i) c'
            (by rw [Finset.card_erase_of_mem hiJ, hJc, Nat.add_sub_cancel])
            (fun k hk => by
              obtain ⟨hki, hkJ⟩ := Finset.mem_erase.1 hk
              rw [hc'k k hki]
              exact hcJ k hkJ)
            (fun k hk => by
              by_cases hki : k = i
              · rw [hki, hc'i]
                cases b <;> simp
              · rw [hc'k k hki]
                exact hcJc k fun h => hk (Finset.mem_erase.2 ⟨hki, h⟩))
            (g x) hyC (hF' (g x) hyF hyi) hyLa ε hε
          refine ⟨δ, hδ, fun y' hy' hy'y => ?_⟩
          obtain ⟨⟨hy'C, hy'F, -, hy'i⟩, -, -, -, hy'La⟩ := hy'
          exact hδlip y' hy'C (hF' y' hy'F hy'i) hy'La hy'y
      -- Chain rule for `ψ₀ ∘ g`, which equals `ψ₀` on `F ∖ La`.
      have hcomp := Submission.dr_cc_lip_at_comp (Eucl (m + 1 + ℓ)) (Eucl (m + 1 + ℓ))
        (Eucl (m + 1 + ℓ)) g ψ₀
        {x' : Eucl (m + 1 + ℓ) | (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) ∧ (∀ i ∉ J, x' i = c i) ∧ x' ∉ La}
        {y' : Eucl (m + 1 + ℓ) | (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) ∧ (∀ i ∉ J, y' i = c i) ∧
          (∃ i ∈ J, y' i = 0 ∨ y' i = 1) ∧ y' ∉ La}
        x ((1 + 4 * r) * s)
        ((1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) / infDist (g x) La)
        (by positivity) (by positivity)
        (fun x' hx' => by
          obtain ⟨hx'C, hx'F, hx'La⟩ := hx'
          obtain ⟨h1, h2, h3, h4, -⟩ := hgA x' hx'C hx'F hx'La
          exact ⟨h1, h2, h3, h4⟩)
        (fun ε hε => by
          obtain ⟨δ, hδ, h⟩ := hlip ε hε
          exact ⟨δ, hδ, fun x' hx' hx'x => h x' hx'.1 hx'.2.1 hx'x⟩)
        hψB
      -- The constant: `β s c₁(j) / dist(g x, La) ≤ q c₁(j) / dist(x, La) = c₁(j + 1) / dist(x, La)`
      -- by `dist(g x, La) ≥ min(1/4, s dist(x, La))` and `s dist(x, La) ≤ r`.
      have hsim := Submission.dr_cc_similarity_bound m ℓ a ha La hLa J c x (g x) s hcJ hcJc hxF
        hyC hs hscale
      have hkey : (1 + 4 * r) * s * infDist x La ≤ 4 * r * (1 + 4 * r) * infDist (g x) La := by
        rcases le_total (1 / 4) (s * infDist x La) with h14 | h14
        · rw [min_eq_left h14] at hsim
          nlinarith [mul_le_mul_of_nonneg_left hsr hβ.le, mul_le_mul_of_nonneg_left hsim hq.le]
        · rw [min_eq_right h14] at hsim
          nlinarith [mul_le_mul_of_nonneg_left hsim hq.le,
            mul_le_mul_of_nonneg_right hβq (mul_nonneg hs.le hdx.le)]
      have hQ : 0 ≤ (1 + 4 * r) * r * (4 * r * (1 + 4 * r)) ^ (j - (m + 2)) := by positivity
      intro ε hε
      obtain ⟨δ, hδ, hδlip⟩ := hcomp ε hε
      refine ⟨δ, hδ, fun x' hx'C hx'F hx'La hx'x => ?_⟩
      have h := hδlip x' ⟨hx'C, hx'F, hx'La⟩ hx'x
      rw [(hgA x' hx'C hx'F hx'La).2.2.2.2, hψy] at h
      refine h.trans (mul_le_mul_of_nonneg_right (add_le_add ?_ le_rfl) dist_nonneg)
      rw [show j + 1 - (m + 2) = j - (m + 2) + 1 by omega, pow_succ, mul_div_assoc',
        div_le_div_iff₀ hdy hdx]
      nlinarith [mul_le_mul_of_nonneg_left hkey hQ]
  -- `P(d)` on the face `C` itself (`J` = all indices, `c = a`) is the claim.
  intro x hxC hxLa ε hε
  obtain ⟨δ, hδ, h⟩ := key (m + 1 + ℓ) (by omega) Finset.univ a
    (by rw [Finset.card_univ, Fintype.card_fin]) (fun i _ => rfl)
    (fun i hi => absurd (Finset.mem_univ i) hi) x hxC (fun i hi => absurd (Finset.mem_univ i) hi)
    hxLa ε hε
  exact ⟨δ, hδ, fun x' hx'C hx'La hx'x =>
    h x' hx'C (fun i hi => absurd (Finset.mem_univ i) hi) hx'La hx'x⟩

/-- **Simon Ch. 6, Lemma 5.4, printed proof pp. 161–163: the radial retraction of the unit cube.**
For `1/4 < aᵢ < 3/4` there is `ψ₀` mapping `C ∖ L_{ℓ−1}(a)`, `C = [0, 1]^d`, into `C` with `ℓ`
coordinates in `{0, 1}` (α), compatible with integer translations inside `C` (β), and
`c₁ / dist(x, L_{ℓ−1}(a))`-Lipschitz at every `x` within `C ∖ L_{ℓ−1}(a)` (γ, claim (3)), with
`c₁ = c₁(m, ℓ)` chosen before `a`.  `ψ₀ = ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(d)}` is the composite of the radial
retractions `ψ_F` of the faces of `C`; claim (3) holds for every map with its structural properties
(S1) (`ψ₀` fixes the points of `C ∖ L_{ℓ−1}(a)` with `ℓ` coordinates in `{0, 1}`) and (S2)
(`ψ₀ = ψ₀ ∘ ψ_F` on `F ∖ L_{ℓ−1}(a)` for every face `F` of dimension `≥ m + 2`). -/
theorem Submission.deformation_retraction_cube_core : ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ a : Eucl (m + 1 + ℓ), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∃ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ), (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → (∀ i, 0 ≤ ψ₀ x i ∧ ψ₀ x i ≤ 1) ∧ ∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ψ₀ x i = 0 ∨ ψ₀ x i = 1) ∧ (∀ x x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → (∀ i, ∃ k : ℤ, x' i - x i = k) → ∀ i, ψ₀ x' i - ψ₀ x i = x' i - x i) ∧ ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → dist x' x < δ → dist (ψ₀ x') (ψ₀ x) ≤ (c₁ / infDist x La + ε) * dist x' x := by
  intro m ℓ hℓ
  -- Step 6.6: `c₁ = c₁(m, ℓ)` of claim (3) is chosen before `a`.
  obtain ⟨c₁, hc₁, hlip⟩ := Submission.dr_cc_pointwise_lip m ℓ hℓ
  refine ⟨c₁, hc₁, fun a ha La hLa => ?_⟩
  -- Steps 3–5: the composite `ψ₀` with (α), (β), (S1) and (S2).
  obtain ⟨ψ₀, hα, hβ, hS1, hS2⟩ := Submission.dr_cc_construction m ℓ hℓ a ha La hLa
  -- Step 6: (γ) is claim (3) for this `ψ₀`.
  exact ⟨ψ₀, hα, hβ, hlip a ha La hLa ψ₀ hS1 hS2⟩
/-- Simon Ch. 6, proof of Lemma 5.4 (p. 161): the periodic extension `ψ(z + x) = z + ψ₀(x)` of a
map `ψ₀` on `C ∖ La`, `C = [0,1]^d`, satisfying (α) `ψ₀(C ∖ La) ⊆ C` with `ℓ` coordinates in
`{0, 1}`, (β) `ψ₀(x') − ψ₀(x) = x' − x` for `x' − x ∈ ℤ^d`, and (γ) the pointwise bound
`|ψ₀(x') − ψ₀(x)| ≤ (c₁ / dist(x, La) + ε)|x' − x|` near `x`.  Here
`ψ(x) = ⌊x⌋ + ψ₀(x − ⌊x⌋)`; by (β), `ψ = z + ψ₀(· − z)` on each cube `(z + C) ∖ La`, and as `La`
is `ℤ^d`-periodic, `dist(x − z, La) = dist(x, La)` transports (γ) to every unit cube. -/
theorem Submission.deformation_retraction_periodic_extension : ∀ (m ℓ : ℕ) (c₁ : ℝ) (a : Eucl (m + 1 + ℓ)) (La : Set (Eucl (m + 1 + ℓ))), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∀ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ), (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → (∀ i, 0 ≤ ψ₀ x i ∧ ψ₀ x i ≤ 1) ∧ ∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ψ₀ x i = 0 ∨ ψ₀ x i = 1) → (∀ x x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → (∀ i, ∃ k : ℤ, x' i - x i = k) → ∀ i, ψ₀ x' i - ψ₀ x i = x' i - x i) → (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → dist x' x < δ → dist (ψ₀ x') (ψ₀ x) ≤ (c₁ / infDist x La + ε) * dist x' x) → ∃ ψ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ), (∀ x, x ∉ La → ∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ∃ k : ℤ, ψ x i = k) ∧ (∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)), x ∉ La → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, (z i : ℝ) ≤ ψ x i ∧ ψ x i ≤ z i + 1) ∧ ∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)), x ∉ La → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ), x' ∉ La → (∀ i, (z i : ℝ) ≤ x' i ∧ x' i ≤ z i + 1) → dist x' x < δ → dist (ψ x') (ψ x) ≤ (c₁ / infDist x La + ε) * dist x' x := by
  intro m ℓ c₁ a La hLa ψ₀ hα hβ hγ
  -- Step 1: `La` is invariant under integral displacements.
  have hper : ∀ y y' : Eucl (m + 1 + ℓ), (∀ i, ∃ k : ℤ, y' i - y i = k) → y ∈ La → y' ∈ La := by
    intro y y' hyy' hy
    rw [hLa] at hy ⊢
    obtain ⟨J, hJ, hJk⟩ := hy
    refine ⟨J, hJ, fun i hi => ?_⟩
    obtain ⟨k, hk⟩ := hJk i hi
    obtain ⟨k', hk'⟩ := hyy' i
    exact ⟨k + k', by push_cast; linarith⟩
  -- The lattice point `z ∈ ℤ^d` as a vector of `ℝ^d`.
  let zv : (Fin (m + 1 + ℓ) → ℤ) → Eucl (m + 1 + ℓ) := fun z => WithLp.toLp 2 (fun i => (z i : ℝ))
  have zv_apply : ∀ z i, zv z i = (z i : ℝ) := fun z i => rfl
  have hsub_notin : ∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)), x ∉ La → x - zv z ∉ La := by
    intro z x hx hxz
    refine hx (hper (x - zv z) x (fun i => ⟨z i, ?_⟩) hxz)
    simp [PiLp.sub_apply, zv_apply]
  -- Step 2: `dist(x − z, La) = dist(x, La)`, as `w ↦ w − z` is an isometry mapping `La` onto `La`.
  have hdist : ∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)),
      infDist (x - zv z) La = infDist x La := by
    intro z x
    have himg : (IsometryEquiv.subRight (zv z)) '' La = La := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine hper v _ (fun i => ⟨-z i, ?_⟩) hv
        simp [PiLp.sub_apply, zv_apply]
      · intro hw
        refine ⟨w + zv z, hper w _ (fun i => ⟨z i, ?_⟩) hw, ?_⟩
        · simp [PiLp.add_apply, zv_apply]
        · simp
    have := Metric.infDist_image (x := x) (t := La) (IsometryEquiv.subRight (zv z)).isometry
    rw [himg] at this
    simpa using this
  -- Step 3: `ψ(x) = ⌊x⌋ + ψ₀(x − ⌊x⌋)`.
  let fl : Eucl (m + 1 + ℓ) → (Fin (m + 1 + ℓ) → ℤ) := fun x i => ⌊x i⌋
  let ψ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ) := fun x => zv (fl x) + ψ₀ (x - zv (fl x))
  have hflC : ∀ x : Eucl (m + 1 + ℓ), ∀ i, 0 ≤ (x - zv (fl x)) i ∧ (x - zv (fl x)) i ≤ 1 := by
    intro x i
    simp only [PiLp.sub_apply, zv_apply, fl]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  have hzC : ∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)),
      (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, 0 ≤ (x - zv z) i ∧ (x - zv z) i ≤ 1 := by
    intro z x hx i
    simp only [PiLp.sub_apply, zv_apply]
    constructor <;> linarith [(hx i).1, (hx i).2]
  -- Step 4: on `(z + C) ∖ La`, `ψ = z + ψ₀(· − z)`, by (β).
  have hkey : ∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)), x ∉ La →
      (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, ψ x i = z i + ψ₀ (x - zv z) i := by
    intro z x hx hxz i
    have hb := hβ (x - zv z) (x - zv (fl x)) (hzC z x hxz) (hsub_notin z x hx) (hflC x)
      (hsub_notin (fl x) x hx) (fun j => ⟨z j - fl x j, by simp [PiLp.sub_apply, zv_apply]⟩) i
    simp only [PiLp.sub_apply, zv_apply] at hb
    simp only [ψ, PiLp.add_apply, zv_apply]
    linarith
  refine ⟨ψ, ?_, ?_, ?_⟩
  · -- Step 5 (i′): `ℓ` integer coordinates, from (α) at `x − ⌊x⌋`.
    intro x hx
    obtain ⟨_, I, hI, hI01⟩ := hα (x - zv (fl x)) (hflC x) (hsub_notin (fl x) x hx)
    refine ⟨I, hI, fun i hi => ?_⟩
    rcases hI01 i hi with h | h
    · exact ⟨fl x i, by simp only [ψ, PiLp.add_apply, zv_apply, h, add_zero]⟩
    · exact ⟨fl x i + 1, by simp only [ψ, PiLp.add_apply, zv_apply, h]; push_cast; ring⟩
  · -- Step 6 (ii): `ψ` maps `(z + C) ∖ La` into `z + C`.
    intro z x hx hxz i
    rw [hkey z x hx hxz i]
    have := ((hα (x - zv z) (hzC z x hxz) (hsub_notin z x hx)).1 i)
    constructor <;> linarith [this.1, this.2]
  · -- Step 7 (iii′): transport (γ) at `x − z` through `hkey` and `hdist`.
    intro z x hx hxz ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hγ (x - zv z) (hzC z x hxz) (hsub_notin z x hx) ε hε
    refine ⟨δ, hδ, fun x' hx' hx'z hxx' => ?_⟩
    have hdd : dist (x' - zv z) (x - zv z) = dist x' x := dist_sub_right _ _ _
    have hψ : ψ x' - ψ x = ψ₀ (x' - zv z) - ψ₀ (x - zv z) := by
      ext i
      simp only [PiLp.sub_apply]
      rw [hkey z x' hx' hx'z i, hkey z x hx hxz i]
      ring
    have h1 := hδ' (x' - zv z) (hzC z x' hx'z) (hsub_notin z x' hx') (by rw [hdd]; exact hxx')
    rw [hdd, hdist z x] at h1
    rw [dist_eq_norm, hψ, ← dist_eq_norm]
    exact h1

/-- Simon Ch. 6, proof of Lemma 5.4 (local to global Lipschitz bounds): if `ψ` maps each closed
unit cube `z + [0, 1]^N` into itself off `L` and has pointwise Lipschitz constant `c₁ / dist(x, L)`
inside each such cube, then `ψ` is `c / σ`-Lipschitz on `{x | σ ≤ dist(x, L)}` for `0 < σ ≤ 1/4`,
with `c = max (2 c₁) (1/4 + 4 √N)`.  Far pairs use `|ψ y - y| ≤ √N`; for near pairs the segment
stays in `{σ / 2 < dist(·, L)}` and `deformation_retraction_dini_segment` integrates the bound. -/
theorem Submission.deformation_retraction_globalize : ∀ (N : ℕ) (c₁ : ℝ), 0 ≤ c₁ → ∃ c : ℝ≥0, ∀ (L : Set (Eucl N)) (ψ : Eucl N → Eucl N), (∀ (z : Fin N → ℤ) (x : Eucl N), x ∉ L → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, (z i : ℝ) ≤ ψ x i ∧ ψ x i ≤ z i + 1) → (∀ (z : Fin N → ℤ) (x : Eucl N), x ∉ L → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl N, x' ∉ L → (∀ i, (z i : ℝ) ≤ x' i ∧ x' i ≤ z i + 1) → dist x' x < δ → dist (ψ x') (ψ x) ≤ (c₁ / infDist x L + ε) * dist x' x) → ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 → LipschitzOnWith (c / Real.toNNReal σ) ψ {x | σ ≤ infDist x L} := by
  intro N c₁ hc₁
  -- Step 5(b): from `p` in direction `v`, the points `p + t • v`, `0 ≤ t < τ`, stay in one closed
  -- unit cube `z + Q` (`zᵢ = ⌊pᵢ⌋` if `0 ≤ vᵢ`, `zᵢ = ⌈pᵢ⌉ - 1` if `vᵢ < 0`); `-v` gives `z⁻`.
  have cube_ray : ∀ p v : Eucl N, ∃ z : Fin N → ℤ, ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 ≤ t → t < τ →
      ∀ i, (z i : ℝ) ≤ p i + t * v i ∧ p i + t * v i ≤ z i + 1 := by
    intro p v
    classical
    let z : Fin N → ℤ := fun i => if 0 ≤ v i then ⌊p i⌋ else ⌈p i⌉ - 1
    have hev : ∀ i, ∀ᶠ t in 𝓝[≥] (0 : ℝ),
        (z i : ℝ) ≤ p i + t * v i ∧ p i + t * v i ≤ z i + 1 := by
      intro i
      have hlim : Tendsto (fun t : ℝ => p i + t * v i) (𝓝 0) (𝓝 (p i)) := by
        have hcont : Continuous fun t : ℝ => p i + t * v i := by fun_prop
        simpa using hcont.tendsto 0
      by_cases hvi : 0 ≤ v i
      · have hz : z i = ⌊p i⌋ := by simp [z, hvi]
        have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), p i + t * v i < (⌊p i⌋ : ℝ) + 1 :=
          hlim.eventually (eventually_lt_nhds (Int.lt_floor_add_one (p i)))
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht ht0
        have ht0' : (0 : ℝ) ≤ t := ht0
        have htv : 0 ≤ t * v i := mul_nonneg ht0' hvi
        rw [hz]
        exact ⟨by linarith [Int.floor_le (p i)], ht.le⟩
      · have hz : z i = ⌈p i⌉ - 1 := by simp [z, hvi]
        have hlt : (⌈p i⌉ : ℝ) - 1 < p i := by linarith [Int.ceil_lt_add_one (p i)]
        have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), (⌈p i⌉ : ℝ) - 1 < p i + t * v i :=
          hlim.eventually (eventually_gt_nhds hlt)
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht ht0
        have ht0' : (0 : ℝ) ≤ t := ht0
        have htv : t * v i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0' (le_of_not_ge hvi)
        rw [hz]
        push_cast
        exact ⟨ht.le, by linarith [Int.le_ceil (p i)]⟩
    obtain ⟨τ, hτ, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (Filter.eventually_all.2 hev)
    exact ⟨z, τ, hτ, fun t ht htτ => hsub ⟨ht, htτ⟩⟩
  -- Step 1: the constant `c = max (2 c₁) (1/4 + 4 √N)`, chosen before `L` and `ψ`.
  have hsqrt : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  refine ⟨.mk (max (2 * c₁) (1 / 4 + 4 * Real.sqrt N)) (le_max_of_le_left (by linarith)), ?_⟩
  intro L ψ H1 H2 σ hσ hσ4
  -- Step 2: a point at positive distance from `L` is not in `L`.
  have notL : ∀ w : Eucl N, 0 < infDist w L → w ∉ L := fun w hw hwL => by
    rw [infDist_zero_of_mem hwL] at hw
    exact lt_irrefl 0 hw
  -- Step 3: `|ψ y - y| ≤ √N` for `y ∉ L`, since `y, ψ y ∈ ⌊y⌋ + Q` by (H1).
  have displacement : ∀ y : Eucl N, y ∉ L → dist (ψ y) y ≤ Real.sqrt N := by
    intro y hy
    have hy' : ∀ i, ((fun i => ⌊y i⌋ : Fin N → ℤ) i : ℝ) ≤ y i ∧
        y i ≤ ((fun i => ⌊y i⌋ : Fin N → ℤ) i : ℝ) + 1 :=
      fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    have hψ := H1 (fun i => ⌊y i⌋) y hy hy'
    rw [EuclideanSpace.dist_eq]
    apply Real.sqrt_le_sqrt
    have hle : ∀ i, dist (ψ y i) (y i) ^ 2 ≤ 1 := by
      intro i
      obtain ⟨a1, a2⟩ := hψ i
      obtain ⟨b1, b2⟩ := hy' i
      rw [Real.dist_eq]
      have h : |ψ y i - y i| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      have h0 := abs_nonneg (ψ y i - y i)
      nlinarith
    calc ∑ i, dist (ψ y i) (y i) ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = N := by simp
  -- Step 5(c): if the segment `x + s • v` (`s ∈ [0, 1]`) avoids `L` with `c₁ / dist(·, L) ≤ K`,
  -- then `s ↦ ψ (x + s • v)` satisfies the hypothesis of `deformation_retraction_dini_segment`
  -- with constant `K ‖v‖`: apply (H2) at `x + s • v` on the cubes `z⁺` (`s ≤ s'`), `z⁻` (`s' < s`).
  have segment_slope : ∀ (K : ℝ) (x v : Eucl N),
      (∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∉ L ∧ c₁ / infDist (x + s • v) L ≤ K) →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s' ∈ Icc (0 : ℝ) 1,
        |s' - s| < δ → ‖ψ (x + s' • v) - ψ (x + s • v)‖ ≤ (K * ‖v‖ + ε) * |s' - s| := by
    intro K x v hseg s hs ε hε
    by_cases hv : v = 0
    · refine ⟨1, one_pos, fun s' _ _ => ?_⟩
      subst hv
      simp only [smul_zero, add_zero, sub_self, norm_zero, mul_zero, zero_add]
      positivity
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    obtain ⟨hpL, hpK⟩ := hseg s hs
    obtain ⟨zp, τp, hτp, hzp⟩ := cube_ray (x + s • v) v
    obtain ⟨zm, τm, hτm, hzm⟩ := cube_ray (x + s • v) (-v)
    have hpzp : ∀ i, (zp i : ℝ) ≤ (x + s • v) i ∧ (x + s • v) i ≤ zp i + 1 := by
      intro i
      simpa using hzp 0 le_rfl hτp i
    have hpzm : ∀ i, (zm i : ℝ) ≤ (x + s • v) i ∧ (x + s • v) i ≤ zm i + 1 := by
      intro i
      simpa using hzm 0 le_rfl hτm i
    have hε' : 0 < ε / ‖v‖ := div_pos hε hvpos
    obtain ⟨δp, hδp, hp2⟩ := H2 zp (x + s • v) hpL hpzp (ε / ‖v‖) hε'
    obtain ⟨δm, hδm, hm2⟩ := H2 zm (x + s • v) hpL hpzm (ε / ‖v‖) hε'
    refine ⟨min (min τp τm) (min (δp / ‖v‖) (δm / ‖v‖)), by positivity, ?_⟩
    intro s' hs' hss'
    have hτp' : |s' - s| < τp := lt_of_lt_of_le hss' ((min_le_left _ _).trans (min_le_left _ _))
    have hτm' : |s' - s| < τm := lt_of_lt_of_le hss' ((min_le_left _ _).trans (min_le_right _ _))
    have hδp' : |s' - s| < δp / ‖v‖ :=
      lt_of_lt_of_le hss' ((min_le_right _ _).trans (min_le_left _ _))
    have hδm' : |s' - s| < δm / ‖v‖ :=
      lt_of_lt_of_le hss' ((min_le_right _ _).trans (min_le_right _ _))
    have hq : x + s' • v = (x + s • v) + (s' - s) • v := by rw [sub_smul]; abel
    have hqL : x + s' • v ∉ L := (hseg s' hs').1
    have hdist : dist (x + s' • v) (x + s • v) = |s' - s| * ‖v‖ := by
      rw [hq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    -- (H2) on a cube `z` containing `x + s' • v` gives the bound, via `c₁ / dist(·, L) ≤ K`.
    have key : ∀ (z : Fin N → ℤ) (δ' : ℝ), (∀ x' : Eucl N, x' ∉ L →
        (∀ i, (z i : ℝ) ≤ x' i ∧ x' i ≤ z i + 1) → dist x' (x + s • v) < δ' →
        dist (ψ x') (ψ (x + s • v)) ≤
          (c₁ / infDist (x + s • v) L + ε / ‖v‖) * dist x' (x + s • v)) →
        |s' - s| < δ' / ‖v‖ → (∀ i, (z i : ℝ) ≤ (x + s' • v) i ∧ (x + s' • v) i ≤ z i + 1) →
        ‖ψ (x + s' • v) - ψ (x + s • v)‖ ≤ (K * ‖v‖ + ε) * |s' - s| := by
      intro z δ' h2 hlt hmem
      have hd : dist (x + s' • v) (x + s • v) < δ' := by
        rw [hdist]
        rwa [lt_div_iff₀ hvpos] at hlt
      rw [← dist_eq_norm]
      calc dist (ψ (x + s' • v)) (ψ (x + s • v))
          ≤ (c₁ / infDist (x + s • v) L + ε / ‖v‖) * dist (x + s' • v) (x + s • v) :=
            h2 _ hqL hmem hd
        _ ≤ (K + ε / ‖v‖) * dist (x + s' • v) (x + s • v) := by gcongr
        _ = (K * ‖v‖ + ε) * |s' - s| := by rw [hdist]; field_simp
    rcases le_or_gt s s' with hle | hlt
    · refine key zp δp hp2 hδp' fun i => ?_
      have hts : 0 ≤ s' - s := sub_nonneg.2 hle
      have h := hzp (s' - s) hts (by rwa [abs_of_nonneg hts] at hτp') i
      have hcoord : (x + s' • v) i = (x + s • v) i + (s' - s) * v i := by
        rw [hq]
        simp
      rw [hcoord]
      exact h
    · refine key zm δm hm2 hδm' fun i => ?_
      have hts : 0 ≤ s - s' := by linarith
      have h := hzm (s - s') hts (by rw [abs_sub_comm, abs_of_nonneg hts] at hτm'; exact hτm') i
      have hcoord : (x + s' • v) i = (x + s • v) i + (s - s') * (-v) i := by
        rw [hq]
        simp
        ring
      rw [hcoord]
      exact h
  -- Step 1 (cont.): it suffices that `dist (ψ x) (ψ x') ≤ (c / σ) * dist x x'` on
  -- `A = {σ ≤ dist(·, L)}`, as `Real.toNNReal σ = σ`.
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx x' hx'
  have hx0 : σ ≤ infDist x L := hx
  have hx0' : σ ≤ infDist x' L := hx'
  rw [NNReal.coe_div, NNReal.coe_mk, Real.coe_toNNReal σ hσ.le]
  set c : ℝ := max (2 * c₁) (1 / 4 + 4 * Real.sqrt N) with hc
  have hc1 : 2 * c₁ ≤ c := le_max_left _ _
  have hc2 : 1 / 4 + 4 * Real.sqrt N ≤ c := le_max_right _ _
  have hxL : x ∉ L := notL x (lt_of_lt_of_le hσ hx0)
  have hx'L : x' ∉ L := notL x' (lt_of_lt_of_le hσ hx0')
  have hd0 : 0 ≤ dist x x' := dist_nonneg
  rcases le_or_gt (σ / 2) (dist x x') with hfar | hnear
  · -- Step 4: far pairs, `σ / 2 ≤ |x - x'|`, by Step 3 and the triangle inequality.
    have d1 := displacement x hxL
    have d2 := displacement x' hx'L
    have tri : dist (ψ x) (ψ x') ≤ dist x x' + 2 * Real.sqrt N := by
      calc dist (ψ x) (ψ x') ≤ dist (ψ x) x + dist x x' + dist x' (ψ x') :=
            dist_triangle4 _ _ _ _
        _ ≤ Real.sqrt N + dist x x' + Real.sqrt N := by rw [dist_comm x' (ψ x')]; gcongr
        _ = dist x x' + 2 * Real.sqrt N := by ring
    refine tri.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hσ]
    have e1 : dist x x' * σ ≤ dist x x' * (1 / 4) := mul_le_mul_of_nonneg_left hσ4 hd0
    have e2 : Real.sqrt N * σ ≤ Real.sqrt N * (2 * dist x x') :=
      mul_le_mul_of_nonneg_left (by linarith) hsqrt
    have e3 : (1 / 4 + 4 * Real.sqrt N) * dist x x' ≤ c * dist x x' :=
      mul_le_mul_of_nonneg_right hc2 hd0
    nlinarith
  · -- Step 5: near pairs, `|x - x'| < σ / 2`; put `v = x' - x`.
    set v := x' - x with hv
    have hnv : ‖v‖ = dist x x' := by rw [hv, ← dist_eq_norm, dist_comm]
    -- Step 5(a): `σ / 2 < dist(x + s • v, L)` on `[0, 1]`, so the segment avoids `L` and
    -- `c₁ / dist(x + s • v, L) ≤ 2 c₁ / σ`.
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1,
        x + s • v ∉ L ∧ c₁ / infDist (x + s • v) L ≤ 2 * c₁ / σ := by
      intro s hs
      have hdist : dist x (x + s • v) = s * dist x x' := by
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hs.1, hnv]
      have h1 := infDist_le_infDist_add_dist (x := x) (y := x + s • v) (s := L)
      rw [hdist] at h1
      have h2 : s * dist x x' ≤ dist x x' := by nlinarith [hs.2]
      have hlow : σ / 2 < infDist (x + s • v) L := by linarith
      have hpos : 0 < infDist (x + s • v) L := by linarith
      refine ⟨notL _ hpos, ?_⟩
      calc c₁ / infDist (x + s • v) L ≤ c₁ / (σ / 2) :=
            div_le_div_of_nonneg_left hc₁ (by positivity) hlow.le
        _ = 2 * c₁ / σ := by field_simp
    -- Step 5(d): `deformation_retraction_dini_segment` for `γ s = ψ (x + s • v)`,
    -- `K = (2 c₁ / σ) ‖v‖`.
    have hd := Submission.deformation_retraction_dini_segment N (fun s => ψ (x + s • v))
      (2 * c₁ / σ * ‖v‖) (segment_slope (2 * c₁ / σ) x v hseg)
    simp only [one_smul, zero_smul, add_zero] at hd
    have hxv : x + v = x' := by rw [hv]; abel
    rw [hxv, hnv] at hd
    rw [dist_comm, dist_eq_norm]
    calc ‖ψ x' - ψ x‖ ≤ 2 * c₁ / σ * dist x x' := hd
      _ ≤ c / σ * dist x x' := by gcongr

/-- **Simon Ch. 6, Lemma 5.4 (p. 160).**  For `a ∈ B_{1/4}(q)`, `q = (1/2, …, 1/2)`, there is
`ψ : ℝ^d → ℝ^d` mapping `ℝ^d ∖ L_{ℓ−1}(a)` into the lattice `(m+1)`-skeleton and every closed unit
cube `z + [0, 1]^d` into itself off `L_{ℓ−1}(a)`, which is `c / σ`-Lipschitz on
`{dist(·, L_{ℓ−1}(a)) ≥ σ}` for `0 < σ ≤ 1/4`.  Printed proof (pp. 161–163): the radial retraction
`ψ₀` of `[0, 1]^d ∖ L_{ℓ−1}(a)` with pointwise Lipschitz constant `c₁ / dist(x, L_{ℓ−1}(a))`
(claim (3)), its periodic extension `ψ(z + x) = z + ψ₀(x)`, and the passage from pointwise to
Lipschitz bounds. -/
theorem Submission.deformation_retraction : ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ a : Eucl (m + 1 + ℓ), ∑ i, (a i - 1 / 2) ^ 2 < 1 / 16 → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∃ ψ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ), (∀ x, x ∉ La → ψ x ∈ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F) ∧ (∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)), x ∉ La → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, (z i : ℝ) ≤ ψ x i ∧ ψ x i ≤ z i + 1) ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 → LipschitzOnWith (c / Real.toNNReal σ) ψ {x | σ ≤ infDist x La} := by
  intro m ℓ hℓ
  -- Step 1: `c₁ = c₁(m, ℓ)` of claim (3) and `c = max (2 c₁) (1/4 + 4 √d)`, both chosen before `a`.
  obtain ⟨c₁, hc₁, hcore⟩ := Submission.deformation_retraction_cube_core m ℓ hℓ
  obtain ⟨c, hc⟩ := Submission.deformation_retraction_globalize (m + 1 + ℓ) c₁ hc₁
  refine ⟨c, fun a ha La hLa => ?_⟩
  -- Step 2: `|a - q| < 1/4` gives `1/4 < aᵢ < 3/4`, as `(aᵢ - 1/2)² ≤ ∑ⱼ (aⱼ - 1/2)²`.
  have ha' : ∀ i, 1 / 4 < a i ∧ a i < 3 / 4 := by
    intro i
    have hi : (a i - 1 / 2) ^ 2 < (1 / 4) ^ 2 :=
      calc (a i - 1 / 2) ^ 2 ≤ ∑ j, (a j - 1 / 2) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg (a j - 1 / 2)) (Finset.mem_univ i)
        _ < 1 / 16 := ha
        _ = (1 / 4) ^ 2 := by norm_num
    obtain ⟨h1, h2⟩ := abs_lt_of_sq_lt_sq' hi (by norm_num)
    constructor <;> linarith
  -- Step 3: the radial retraction `ψ₀` of `C ∖ La` and its periodic extension `ψ`.
  obtain ⟨ψ₀, hα, hβ, hγ⟩ := hcore a ha' La hLa
  obtain ⟨ψ, hskel, hcube, hloc⟩ :=
    Submission.deformation_retraction_periodic_extension m ℓ c₁ a La hLa ψ₀ hα hβ hγ
  -- Step 4: (i) as `ψ x` has `ℓ` integer coordinates, (ii), and (iii) by globalizing the
  -- cube-wise pointwise bounds.
  exact ⟨ψ, fun x hx => Submission.deformation_retraction_skeleton_mem m ℓ (ψ x) (hskel x hx),
    hcube, hc La ψ hcube hloc⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
