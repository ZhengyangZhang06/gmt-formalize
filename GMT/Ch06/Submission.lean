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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
