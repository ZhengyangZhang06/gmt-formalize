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
/-- Rademacher for `f ∘ Φ`: if `f` is locally Lipschitz on an open `U ⊆ ℝ^P` and `Φ : ℝⁿ → ℝ^P`
is `C¹`, then `f ∘ Φ` is differentiable at `Lⁿ`-a.e. `w` with `Φ w ∈ U`. -/
theorem Submission.lpf_ccr_ae_differentiableAt_comp : ∀ (P Q n : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q) (Φ : Eucl n → Eucl P), IsOpen U → LocallyLipschitzOn U f → ContDiff ℝ 1 Φ → ∀ᵐ w ∂(volume : Measure (Eucl n)), Φ w ∈ U → DifferentiableAt ℝ (f ∘ Φ) w := by
  intro P Q n U f Φ hU hf hΦ
  -- Step 1: `O = Φ⁻¹(U)` is open.
  have hO : IsOpen (Φ ⁻¹' U) := hU.preimage hΦ.continuous
  -- Step 2: `f ∘ Φ` is locally Lipschitz on `O`: compose a Lipschitz neighbourhood of `f` at
  -- `Φ w` (a full neighbourhood, as `U` is open) with one of the `C¹` map `Φ` at `w`.
  have hloc : LocallyLipschitzOn (Φ ⁻¹' U) (f ∘ Φ) := by
    intro w hw
    obtain ⟨K₁, t₁, ht₁, hft₁⟩ := hf hw
    rw [hU.nhdsWithin_eq hw] at ht₁
    obtain ⟨K₂, t₂, ht₂, hΦt₂⟩ := hΦ.locallyLipschitz w
    refine ⟨K₁ * K₂, t₂ ∩ Φ ⁻¹' t₁, mem_nhdsWithin_of_mem_nhds
      (inter_mem ht₂ (hΦ.continuous.continuousAt.preimage_mem_nhds ht₁)), ?_⟩
    exact hft₁.comp (hΦt₂.mono inter_subset_left) fun y hy => hy.2
  -- Step 3: countable Lipschitz cover of `O` (accepted sibling).
  obtain ⟨O, K, hOo, hcov, hlip⟩ :=
    Submission.lpf_lli_countable_lipschitz_cover n Q (Φ ⁻¹' U) (f ∘ Φ) hloc
  -- Step 4: Rademacher on each piece `O i ∩ O`; it is open, so differentiability within it is
  -- differentiability.
  have hpiece : ∀ i, ∀ᵐ w ∂(volume : Measure (Eucl n)),
      w ∈ O i ∩ Φ ⁻¹' U → DifferentiableAt ℝ (f ∘ Φ) w := fun i => by
    filter_upwards [(hlip i).ae_differentiableWithinAt_of_mem
      (μ := (volume : Measure (Eucl n)))] with w hw hws
    exact (hw hws).differentiableAt (((hOo i).inter hO).mem_nhds hws)
  -- Step 5: countably many null sets; every `w` with `Φ w ∈ U` lies in some piece.
  filter_upwards [ae_all_iff.2 hpiece] with w hw hwU
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hwU)
  exact hw i ⟨hi, hwU⟩
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


/-- Chain rule on a `C¹` antilipschitz chart (Simon Ch. 6, proof of 3.9, steps 2 and 5.2): for
`Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`, `DΦ(w)(ℝⁿ)` is the weighted approximate tangent space of `(M, θ)` at
`Φ(w)` and `D(f∘Φ)(w) = L(Φ w) ∘ DΦ(w)`.  The tangent identification and the derivative clause
for `L` hold `Hⁿ`-a.e. on `M`, hence at `Φ w` for a.e. parameter; `f∘Φ` is differentiable a.e.
(Rademacher); and along each `DΦ(w)s ∈ TₓM` both `L(Φ w)` and `D(f∘Φ)(w)` give the derivative of
`t ↦ f(Φ(w) + t DΦ(w)s)` at `0`. -/
theorem Submission.lpf_chart_chain_rule : ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)), IsOpen U → IsRectifiableTriple U n M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' M)), HasWeightedApproximateTangentSpaceAt n M θ (Φ w) (LinearMap.range (fderiv ℝ Φ w).toLinearMap) ∧ HasFDerivAt (f ∘ Φ) ((L (Φ w)).comp (fderiv ℝ Φ w)) w := by
  intro P Q n U M θ ξ f L Φ Ω hU hT hf hL hΩ hΦ hanti
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hΦm : Measurable Φ := hΦ.continuous.measurable
  -- Step 2: tangent identification `T_{Φ w}(M, θ) = DΦ(w)(ℝⁿ)` (sibling lemma), pulled back to
  -- a.e. parameter; this also gives the null-measurability of `Ω ∩ Φ⁻¹(M)`.
  obtain ⟨hSm, h₁⟩ := Submission.lpf_ccr_ae_pullback P n M Φ Ω _ hΩm hΦm hanti
    hT.nullMeasurableSet
    (Submission.lpf_weighted_tangent_on_c1_chart P n U M θ Φ Ω hU hT.subset
      hT.nullMeasurableSet hT.pos hT.integrableOn hΩ hΦ hanti)
  -- Step 3: the derivative clause for `L` holds at `Φ w` for a.e. parameter.
  have h₂ := (Submission.lpf_ccr_ae_pullback P n M Φ Ω _ hΩm hΦm hanti hT.nullMeasurableSet
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hL)).2
  -- Step 4: Rademacher for `f ∘ Φ` on `Φ⁻¹(U) ⊇ Ω ∩ Φ⁻¹(M)`.
  have h₃ := ae_restrict_of_ae (s := Ω ∩ Φ ⁻¹' M)
    (Submission.lpf_ccr_ae_differentiableAt_comp P Q n U f Φ hU hf hΦ)
  filter_upwards [h₁, h₂, h₃, ae_restrict_mem₀ hSm] with w hw₁ hw₂ hw₃ hwS
  have hwU : Φ w ∈ U := hT.subset hwS.2
  have hTw := hw₁ w hwS.1 rfl
  refine ⟨hTw, ?_⟩
  have hdiff : DifferentiableAt ℝ (f ∘ Φ) w := hw₃ hwU
  -- Step 5: `f` is Lipschitz on a neighbourhood of `Φ w` (`U` is open), so along `DΦ(w)s` the
  -- derivative of `t ↦ f(Φ w + t DΦ(w)s)` at `0` is both `D(f∘Φ)(w)s` and `L(Φ w)(DΦ(w)s)`.
  have hlip : ∃ K : ℝ≥0, ∃ V ∈ 𝓝 (Φ w), LipschitzOnWith K f V := by
    obtain ⟨K, V, hV, hfV⟩ := hf hwU
    exact ⟨K, V, hU.nhdsWithin_eq hwU ▸ hV, hfV⟩
  have hline := Submission.lpf_ccr_hasDerivAt_line_of_comp n P Q f Φ w hlip
    (hΦ.differentiable one_ne_zero w) hdiff
  have heq : fderiv ℝ (f ∘ Φ) w = (L (Φ w)).comp (fderiv ℝ Φ w) := by
    ext1 s
    exact (hline s).unique (hw₂ _ hTw _ (LinearMap.mem_range_self _ s))
  exact heq ▸ hdiff.hasFDerivAt

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

/-- Measurable tangential differential on a single `C¹` chart (for the push-forward in Simon
Ch. 6, 3.9): let `Φ` be `C¹` with `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` (`c > 0`) on the open set `Ω`, and
let `Λ A` be a left inverse of each injective `A` with `‖A (Λ A v)‖ ≤ ‖v‖`, `Λ` continuous on the
injective maps.  With `Ψ` the inverse of `Φ` on `S = Φ(Ω)`, the map
`G x = D(f ∘ Φ)(Ψ x) ∘ Λ(DΦ(Ψ x))` on `S` (`0` elsewhere) is Borel: `S` is Borel by
Lusin–Souslin, `Ψ` is `c⁻¹`-Lipschitz on `S`, `DΦ(w)` is injective by
`lpf_wtc_cat_fderiv_lower_bound`, and `D(f ∘ Φ)` is Borel. -/
theorem Submission.lpf_tde_mcd_single_chart :
    ∀ (P Q n : ℕ) (Λ : (Eucl n →L[ℝ] Eucl P) → (Eucl P →L[ℝ] Eucl n)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (f : Eucl P → Eucl Q), ContinuousOn Λ {A : Eucl n →L[ℝ] Eucl P | Function.Injective A} → (∀ A : Eucl n →L[ℝ] Eucl P, Function.Injective A → (Λ A).comp A = ContinuousLinearMap.id ℝ (Eucl n) ∧ ∀ v : Eucl P, ‖A (Λ A v)‖ ≤ ‖v‖) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∃ G : Eucl P → (Eucl P →L[ℝ] Eucl Q), Measurable G ∧ MeasurableSet (Φ '' Ω) ∧ ∀ x ∈ Φ '' Ω, ∃ w ∈ Ω, Φ w = x ∧ (∀ s : Eucl n, G x (fderiv ℝ Φ w s) = fderiv ℝ (f ∘ Φ) w s) ∧ ∀ v : Eucl P, ∃ s : Eucl n, ‖fderiv ℝ Φ w s‖ ≤ ‖v‖ ∧ G x v = fderiv ℝ (f ∘ Φ) w s := by
  classical
  intro P Q n Λ Φ Ω f hΛc hΛ hΩ hΦ hc
  obtain ⟨c, hcpos, hanti⟩ := hc
  -- `c ‖a‖ ≤ 0` with `c > 0` forces `a = 0`.
  have hzero : ∀ a : Eucl n, c * ‖a‖ ≤ 0 → a = 0 := fun a ha =>
    norm_le_zero_iff.mp (by nlinarith [norm_nonneg a])
  -- `Φ` is injective on `Ω`, so `S = Φ(Ω)` is Borel by the Lusin–Souslin theorem.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hanti w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    exact sub_eq_zero.mp (hzero _ h1)
  have hS : MeasurableSet (Φ '' Ω) :=
    hΩ.measurableSet.image_of_continuousOn_injOn hΦ.continuous.continuousOn hinj
  -- The inverse chart `Ψ` maps `S` into `Ω`, inverts `Φ` there and is `c⁻¹`-Lipschitz on `S`.
  obtain ⟨Ψ, hΨmem, hΨeq⟩ : ∃ Ψ : Eucl P → Eucl n,
      (∀ x ∈ Φ '' Ω, Ψ x ∈ Ω) ∧ ∀ x ∈ Φ '' Ω, Φ (Ψ x) = x :=
    ⟨Function.invFunOn Φ Ω, fun _ hx => Function.invFunOn_mem hx,
      fun _ hx => Function.invFunOn_eq hx⟩
  have hΨcont : ContinuousOn Ψ (Φ '' Ω) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal c⁻¹)
      fun x hx x' hx' => ?_).continuousOn
    have h1 := hanti (Ψ x) (hΨmem x hx) (Ψ x') (hΨmem x' hx')
    rw [hΨeq x hx, hΨeq x' hx'] at h1
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hcpos.le),
      inv_mul_eq_div, le_div_iff₀ hcpos]
    linarith
  -- `DΦ(w)` is injective for `w ∈ Ω` by the lower bound `c ‖s‖ ≤ ‖DΦ(w) s‖`.
  have hDinj : ∀ w ∈ Ω, Function.Injective (fderiv ℝ Φ w) := by
    intro w hw s t hst
    have h1 := Submission.lpf_wtc_cat_fderiv_lower_bound P n Φ Ω c w hΩ hw
      (hΦ.differentiable one_ne_zero w) hanti (s - t)
    rw [map_sub, hst, sub_self, norm_zero] at h1
    exact sub_eq_zero.mp (hzero _ h1)
  -- `Ψ` and `x ↦ Λ(DΦ(Ψ x))`, extended by `0` off `S`, are Borel, and so is `D(f ∘ Φ)`.
  have hΨm : Measurable ((Φ '' Ω).piecewise Ψ fun _ => 0) :=
    hΨcont.measurable_piecewise continuousOn_const hS
  have hΛm : Measurable ((Φ '' Ω).piecewise (fun x => Λ (fderiv ℝ Φ (Ψ x))) fun _ => 0) := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hS
    exact hΛc.comp ((hΦ.continuous_fderiv one_ne_zero).comp_continuousOn hΨcont)
      fun x hx => hDinj (Ψ x) (hΨmem x hx)
  have hBm := (measurable_fderiv ℝ (f ∘ Φ)).comp hΨm
  -- `G x = D(f ∘ Φ)(Ψ x) ∘ Λ(DΦ(Ψ x))` on `S`; composition of linear maps is continuous.
  refine ⟨fun x => (fderiv ℝ (f ∘ Φ) ((Φ '' Ω).piecewise Ψ (fun _ => 0) x)).comp
      ((Φ '' Ω).piecewise (fun x => Λ (fderiv ℝ Φ (Ψ x))) (fun _ => 0) x),
    isBoundedBilinearMap_comp.continuous.measurable2 hBm hΛm, hS, fun x hx => ?_⟩
  have hA := hΛ _ (hDinj (Ψ x) (hΨmem x hx))
  refine ⟨Ψ x, hΨmem x hx, hΨeq x hx, fun s => ?_,
    fun v => ⟨Λ (fderiv ℝ Φ (Ψ x)) v, hA.2 v, ?_⟩⟩
  · simp only [Set.piecewise_eq_of_mem _ _ _ hx, ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.comp_apply (Λ _), hA.1, ContinuousLinearMap.id_apply]
  · simp only [Set.piecewise_eq_of_mem _ _ _ hx, ContinuousLinearMap.comp_apply]
/-- Countable measurable gluing by the first index: for measurable sets `S j` and measurable
maps `G j : X → Y` there is a measurable `L : X → Y` vanishing off `⋃ j, S j` and agreeing at each
`x ∈ ⋃ j, S j` with some `G j` such that `x ∈ S j`.  Take `L x = G'_{j(x)} x` with
`G'_j = (S j).piecewise (G j) 0` and `j(x)` the least `j` with `x ∈ S j ∨ x ∉ ⋃ i, S i`;
`L` is measurable by `Measurable.find`. -/
theorem Submission.lpf_tde_mcd_countable_glue :
    ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] [Zero Y] (S : ℕ → Set X)
      (G : ℕ → X → Y), (∀ j, MeasurableSet (S j)) → (∀ j, Measurable (G j)) →
      ∃ L : X → Y, Measurable L ∧ (∀ x, x ∉ (⋃ j, S j) → L x = 0) ∧
        ∀ x ∈ (⋃ j, S j), ∃ j, x ∈ S j ∧ L x = G j x := by
  intro X Y _ _ _ S G hS hG
  classical
  -- Every `x` satisfies `x ∈ S j ∨ x ∉ ⋃ i, S i` for some `j`.
  have h : ∀ x, ∃ j, x ∈ S j ∨ x ∉ ⋃ i, S i := fun x => by
    by_cases hx : x ∈ ⋃ i, S i
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hx⟩
  -- `L x = G'_{j(x)} x` with `G'_j = (S j).piecewise (G j) 0` and `j(x)` the least such `j`.
  refine ⟨fun x => (S (Nat.find (h x))).piecewise (G (Nat.find (h x))) 0 x, ?_, ?_, ?_⟩
  · exact Measurable.find (p := fun j x => x ∈ S j ∨ x ∉ ⋃ i, S i)
      (fun j => (hG j).piecewise (hS j) measurable_const)
      (fun j => (hS j).union (MeasurableSet.iUnion hS).compl) h
  · intro x hx
    have hxS : x ∉ S (Nat.find (h x)) := fun hxS => hx (mem_iUnion.2 ⟨_, hxS⟩)
    simp only [piecewise_eq_of_notMem _ _ _ hxS, Pi.zero_apply]
  · intro x hx
    have hxS : x ∈ S (Nat.find (h x)) := (Nat.find_spec (h x)).resolve_right (not_not.2 hx)
    exact ⟨Nat.find (h x), hxS, piecewise_eq_of_mem _ _ _ hxS⟩
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

/-- Borel chartwise tangential differential (Simon Ch. 3 §2, 2.1–2.2, for Ch. 6, 3.6): for C¹
charts `Φ j` antilipschitz on open `Ω j` and any `f`, glue the Borel pieces
`x = Φ j w ↦ D(f ∘ Φ j)(w) ∘ Λ(DΦ j(w))` along the first chart through `x`, and `0` off the
charts; `Λ` is the continuous left inverse of `lpf_tde_continuous_left_inverse`. -/
theorem Submission.lpf_tde_measurable_chart_differential :
    ∀ (P Q n : ℕ) (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)) (f : Eucl P → Eucl Q), (∀ j, IsOpen (Ω j)) → (∀ j, ContDiff ℝ 1 (Φ j)) → (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) → ∃ L : Eucl P → (Eucl P →L[ℝ] Eucl Q), StronglyMeasurable L ∧ (∀ x, x ∉ (⋃ j, Φ j '' Ω j) → L x = 0) ∧ ∀ x ∈ (⋃ j, Φ j '' Ω j), ∃ j, ∃ w ∈ Ω j, Φ j w = x ∧ (∀ s : Eucl n, L x (fderiv ℝ (Φ j) w s) = fderiv ℝ (f ∘ Φ j) w s) ∧ ∀ v : Eucl P, ∃ s : Eucl n, ‖fderiv ℝ (Φ j) w s‖ ≤ ‖v‖ ∧ L x v = fderiv ℝ (f ∘ Φ j) w s := by
  intro P Q n Φ Ω f hΩ hΦ hanti
  -- Step 0: the continuous left inverse `Λ` on the injective maps.
  obtain ⟨Λ, hΛc, hΛ⟩ := Submission.lpf_tde_continuous_left_inverse n P
  -- Steps 1–5, chart by chart: a Borel piece `G j` on the Borel image `Φ j '' Ω j`.
  choose G hGm hSm hG using fun j =>
    Submission.lpf_tde_mcd_single_chart P Q n Λ (Φ j) (Ω j) f hΛc hΛ (hΩ j) (hΦ j) (hanti j)
  -- Steps 6–7: glue the pieces along the first chart containing `x`, `0` off the charts.
  obtain ⟨L, hLm, hL0, hL⟩ := Submission.lpf_tde_mcd_countable_glue (Eucl P)
    (Eucl P →L[ℝ] Eucl Q) (fun j => Φ j '' Ω j) G hSm hGm
  refine ⟨L, hLm.stronglyMeasurable, hL0, fun x hx => ?_⟩
  -- Step 8: `L x` is the piece of a chart `j` through `x`, so the chart identities transfer.
  obtain ⟨j, hxj, hLx⟩ := hL x hx
  obtain ⟨w, hw, hΦw, hA, hv⟩ := hG j x hxj
  refine ⟨j, w, hw, hΦw, fun s => by rw [hLx]; exact hA s, fun v => ?_⟩
  obtain ⟨s, hs, hGs⟩ := hv v
  exact ⟨s, hs, by rw [hLx]; exact hGs⟩
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
/-- Finitely many covectors separate `k`-vectors (Simon Ch. 6, §1): `Λᵏ(ℝ^P)` is
finite-dimensional, and `k`-vectors (continuous linear functionals on it) agreeing on a basis
agree.  Evaluation on tuples of standard basis vectors embeds `Λᵏ(ℝ^P)` linearly into
`ℝ^(Fin k → Fin P)` (a multilinear map is determined by its values on basis vectors). -/
theorem Submission.ltg_covector_separating :
    ∀ (P k : ℕ), ∃ (L : ℕ) (b : Fin L → Covector (Eucl P) k),
      ∀ w w' : NVector (Eucl P) k, (∀ l, w (b l) = w' (b l)) → w = w' := by
  intro P k
  -- Evaluation on `k`-tuples of standard basis vectors of `ℝ^P`.
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  let ev : Covector (Eucl P) k →ₗ[ℝ] (Fin k → Fin P) → ℝ :=
    { toFun := fun α I => α fun j => e (I j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- `ev` is injective, so `Λᵏ(ℝ^P)` is finite-dimensional.
  have hinj : Function.Injective ev := fun α β h =>
    ContinuousAlternatingMap.toAlternatingMap_injective <|
      Module.Basis.ext_alternating e fun v _ => congrFun h v
  have : FiniteDimensional ℝ (Covector (Eucl P) k) := FiniteDimensional.of_injective ev hinj
  -- Linear functionals agreeing on a basis are equal.
  let b := Module.finBasis ℝ (Covector (Eucl P) k)
  exact ⟨Module.finrank ℝ (Covector (Eucl P) k), b, fun w w' h =>
    ContinuousLinearMap.coe_injective (b.ext h)⟩
/-- Nonnegative multiples of unit simple `k`-vectors are rigid (the orientations
`ξ = ±τ₁ ∧ ⋯ ∧ τₖ` of Simon Ch. 6, 3.1): if `τ, τ'` are orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₖ`,
`w' = ±τ'₁ ∧ ⋯ ∧ τ'ₖ`, `a, a' ≥ 0` and `a w = a' w'`, then `a = a'`, and `w = w'` when `a ≠ 0`.
Evaluate on the dual covectors `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩`, `α_σ(v) = det(⟨σᵢ, vⱼ⟩)` (1.1):
with `d = det(⟨τᵢ, τ'ⱼ⟩)`, `α_τ(τ) = α_τ'(τ') = 1` and `α_τ(τ') = α_τ'(τ) = d` give
`a = a' |d|` and `a |d| = a'`. -/
theorem Submission.ltg_simple_unit_rigidity :
    ∀ (P k : ℕ) (τ τ' : Fin k → Eucl P) (w w' : NVector (Eucl P) k) (a a' : ℝ),
      Orthonormal ℝ τ → Orthonormal ℝ τ' → (w = simpleNVector τ ∨ w = -simpleNVector τ) →
      (w' = simpleNVector τ' ∨ w' = -simpleNVector τ') → 0 ≤ a → 0 ≤ a' → a • w = a' • w' →
      a = a' ∧ (a ≠ 0 → w = w') := by
  intro P k τ τ' w w' a a' hτ hτ' hw hw' ha ha' h
  -- The dual covector `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩` evaluates as `det(⟨σᵢ, vⱼ⟩)`.
  let α : (Fin k → Eucl P) → Covector (Eucl P) k :=
    fun σ => wedgeCovectors k fun i => innerSL ℝ (σ i)
  have hα : ∀ σ v : Fin k → Eucl P,
      α σ v = (Matrix.of fun i j => inner ℝ (σ i) (v j)).det := fun σ v => by
    simp only [α, wedgeCovectors_apply_det, innerSL_apply_apply]
  -- `α_σ(σ) = det 1 = 1` for orthonormal `σ`, and `α_τ'(τ) = α_τ(τ')` by transposition.
  have hone : ∀ σ : Fin k → Eucl P, Orthonormal ℝ σ → α σ σ = 1 := fun σ hσ => by
    have h1 : (Matrix.of fun i j => inner ℝ (σ i) (σ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [orthonormal_iff_ite.mp hσ, Matrix.one_apply]
    rw [hα, h1, Matrix.det_one]
  have hswap : α τ' τ = α τ τ' := by
    rw [hα, hα, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact real_inner_comm _ _
  -- Signs: `w = s • simpleNVector τ` and `w' = s' • simpleNVector τ'` with `|s| = |s'| = 1`.
  have hsign : ∀ (σ : Fin k → Eucl P) (v : NVector (Eucl P) k),
      (v = simpleNVector σ ∨ v = -simpleNVector σ) →
        ∃ s : ℝ, |s| = 1 ∧ v = s • simpleNVector σ := by
    rintro σ v (rfl | rfl)
    · exact ⟨1, abs_one, (one_smul ℝ _).symm⟩
    · refine ⟨-1, by simp, ?_⟩
      ext β
      simp
  obtain ⟨s, hs, rfl⟩ := hsign τ w hw
  obtain ⟨s', hs', rfl⟩ := hsign τ' w' hw'
  -- Evaluate `a • w = a' • w'` at `α_τ` and `α_τ'` and take absolute values:
  -- `a = a' |d|` and `a |d| = a'`, where `d = α_τ(τ')`.
  have e1 := congrArg (fun v : NVector (Eucl P) k => |v (α τ)|) h
  have e2 := congrArg (fun v : NVector (Eucl P) k => |v (α τ')|) h
  simp only [smul_apply, simpleNVector_apply, smul_eq_mul, hone τ hτ, hone τ' hτ', hswap,
    abs_mul, abs_of_nonneg ha, abs_of_nonneg ha', hs, hs', mul_one, one_mul] at e1 e2
  -- `a = a'`: trivial if `a = 0`; otherwise `a |d|² = a` forces `|d| = 1`.
  have haa : a = a' := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [← e2, ha0, zero_mul]
    · have hd : |α τ τ'| * |α τ τ'| = 1 :=
        mul_left_cancel₀ ha0 (by rw [← mul_assoc, e2, ← e1, mul_one])
      have hd' : |α τ τ'| = 1 := by nlinarith [abs_nonneg (α τ τ')]
      rw [← e2, hd', mul_one]
  -- `w = w'`: cancel the nonzero scalar `a` in `a • w = a • w'`.
  refine ⟨haa, fun ha0 => ?_⟩
  rw [← haa] at h
  exact smul_right_injective _ ha0 h

/-- Uniqueness of `τ(M, θ, ξ)` on an open set (Simon Ch. 6, 3.1): if two rectifiable triples
define the same current on test forms supported in an open `O ⊆ U`, then
`Hᵏ((M₁ Δ M₂) ∩ O) = 0`, and `θ₁ = θ₂`, `ξ₁ = ξ₂` `Hᵏ`-a.e. on `M₁ ∩ O`.  For a covector `b`,
testing with `φ b` and the fundamental lemma give `1_{M₁} θ₁ ξ₁(b) = 1_{M₂} θ₂ ξ₂(b)` a.e. on
`O`; finitely many separating covectors upgrade this to `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂`, and
rigidity of nonnegative multiples of unit simple `k`-vectors concludes. -/
theorem Submission.ltg_tau_unique_on_open :
    ∀ (P k : ℕ) (U O : Set (Eucl P)), IsOpen O → O ⊆ U →
      ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ) (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M₁ θ₁ ξ₁ → IsRectifiableTriple U k M₂ θ₂ ξ₂ →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M₁ θ₁ ξ₁ ω = tauAction k M₂ θ₂ ξ₂ ω) →
      (μHE[k] : Measure (Eucl P)) (symmDiff M₁ M₂ ∩ O) = 0 ∧
        ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ O)), θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x := by
  intro P k U O hO hOU M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ hT₁ hT₂ hτ
  -- The scalar density `g^b = 1_M θ ξ(b)` of a triple is locally integrable on `O`, and
  -- `∫ φ g^b dHᵏ = τ(M, θ, ξ)(φ b)` for smooth `φ` with compact support in `O`.
  have key : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ → ∀ b : Covector (Eucl P) k,
      LocallyIntegrableOn (M.indicator fun y => θ y * ξ y b) O (μHE[k] : Measure (Eucl P)) ∧
      ∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ O →
        Integrable (fun x => φ x • M.indicator (fun y => θ y * ξ y b) x)
          (μHE[k] : Measure (Eucl P)) ∧
        ∫ x, φ x • M.indicator (fun y => θ y * ξ y b) x ∂(μHE[k] : Measure (Eucl P)) =
          tauAction k M θ ξ (fun x => φ x • b) := by
    intro M θ ξ hT b
    have hI := Submission.ltg_tau_integrable P k U M θ ξ hT
    refine ⟨?_, fun φ hφ hφc hφO => ?_⟩
    · rw [locallyIntegrableOn_iff hO.isLocallyClosed]
      intro K hKO hK
      exact (integrableOn_indicator_iff hT.nullMeasurableSet).2 (hI.1 K b hK (hKO.trans hOU))
    · have hint := hI.2 (fun x => φ x • b) (hφ.continuous.smul continuous_const)
        hφc.smul_right ((tsupport_smul_subset_left φ fun _ => b).trans (hφO.trans hOU))
      have heq : (fun x => φ x • M.indicator (fun y => θ y * ξ y b) x) =
          M.indicator fun x => θ x * ξ x (φ x • b) := by
        funext x
        by_cases hx : x ∈ M
        · simp only [Set.indicator_of_mem hx, map_smul, smul_eq_mul]
          ring
        · simp [Set.indicator_of_notMem hx]
      rw [heq]
      exact ⟨(integrable_indicator_iff₀ hT.nullMeasurableSet).2 hint,
        integral_indicator₀ hT.nullMeasurableSet⟩
  -- Fundamental lemma: for each covector `b`, `g₁^b = g₂^b` a.e. on `O`.
  have hG : ∀ b : Covector (Eucl P) k, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      M₁.indicator (fun y => θ₁ y * ξ₁ y b) x - M₂.indicator (fun y => θ₂ y * ξ₂ y b) x = 0 := by
    intro b
    obtain ⟨hl₁, hi₁⟩ := key M₁ θ₁ ξ₁ hT₁ b
    obtain ⟨hl₂, hi₂⟩ := key M₂ θ₂ ξ₂ hT₂ b
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hl₁.sub hl₂) fun φ hφ hφc hφO => ?_
    obtain ⟨hint₁, he₁⟩ := hi₁ φ hφ hφc hφO
    obtain ⟨hint₂, he₂⟩ := hi₂ φ hφ hφc hφO
    -- The test form `φ b ∈ 𝒟ᵏ(U)`, supported in `O`.
    have hsmooth : IsSmoothForm (fun x => φ x • b : DifferentialForm (Eucl P) k) := by
      unfold IsSmoothForm
      exact hφ.smul contDiff_const
    have hts : tsupport (fun x => φ x • b : DifferentialForm (Eucl P) k) ⊆ O :=
      (tsupport_smul_subset_left φ fun _ => b).trans hφO
    let ω : TestFormOn U k := ⟨fun x => φ x • b, ⟨hsmooth, hφc.smul_right⟩, hts.trans hOU⟩
    simp_rw [smul_sub]
    rw [integral_sub hint₁ hint₂, he₁, he₂]
    exact sub_eq_zero.2 (hτ ω hts)
  -- Finitely many covectors separate `k`-vectors: `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` a.e. on `O`.
  obtain ⟨L, bs, hsep⟩ := Submission.ltg_covector_separating P k
  have hind : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k)
      (x : Eucl P) (b : Covector (Eucl P) k),
      (M.indicator θ x • ξ x) b = M.indicator (fun y => θ y * ξ y b) x := by
    intro M θ ξ x b
    by_cases hx : x ∈ M <;> simp [hx]
  have hW : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      M₁.indicator θ₁ x • ξ₁ x = M₂.indicator θ₂ x • ξ₂ x := by
    have hall : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), ∀ l, x ∈ O →
        M₁.indicator (fun y => θ₁ y * ξ₁ y (bs l)) x -
          M₂.indicator (fun y => θ₂ y * ξ₂ y (bs l)) x = 0 :=
      ae_all_iff.2 fun l => hG (bs l)
    filter_upwards [hall] with x hx hxO
    refine hsep _ _ fun l => ?_
    rw [hind, hind]
    exact sub_eq_zero.1 (hx l hxO)
  -- `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` for an orthonormal frame `τ`, a.e. on `M`.
  have hor : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ M →
        ∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
          (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
    intro M θ ξ hT
    filter_upwards [(ae_restrict_iff'₀ hT.nullMeasurableSet).1 hT.orients] with x hx hxM
    obtain ⟨τ, hτo, -, hξ⟩ := hx hxM
    exact ⟨τ, hτo, hξ⟩
  -- Pointwise rigidity, using `θᵢ > 0` on `Mᵢ`: a.e. on `O`, `x ∈ M₁ ↔ x ∈ M₂`, and on `M₁`
  -- `θ₁ = θ₂`, `ξ₁ = ξ₂`.
  have hpt : ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
      (x ∈ M₁ ↔ x ∈ M₂) ∧ (x ∈ M₁ → θ₁ x = θ₂ x ∧ ξ₁ x = ξ₂ x) := by
    filter_upwards [hW, hor M₁ θ₁ ξ₁ hT₁, hor M₂ θ₂ ξ₂ hT₂] with x hWx h1x h2x hxO
    have hW' := hWx hxO
    by_cases h1 : x ∈ M₁ <;> by_cases h2 : x ∈ M₂
    · obtain ⟨τ, hτo, hξτ⟩ := h1x h1
      obtain ⟨τ', hτo', hξτ'⟩ := h2x h2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2] at hW'
      obtain ⟨hθ, hξ⟩ := Submission.ltg_simple_unit_rigidity P k τ τ' (ξ₁ x) (ξ₂ x) (θ₁ x)
        (θ₂ x) hτo hτo' hξτ hξτ' (hT₁.pos x h1).le (hT₂.pos x h2).le hW'
      exact ⟨iff_of_true h1 h2, fun _ => ⟨hθ, hξ (hT₁.pos x h1).ne'⟩⟩
    · -- On `M₁ \ M₂`, `θ₁ ξ₁ = 0 = 0 ξ₁` would force `θ₁ = 0`.
      obtain ⟨τ, hτo, hξτ⟩ := h1x h1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, zero_smul] at hW'
      exact absurd (Submission.ltg_simple_unit_rigidity P k τ τ (ξ₁ x) (ξ₁ x) (θ₁ x) 0 hτo hτo
        hξτ hξτ (hT₁.pos x h1).le le_rfl (by rw [hW', zero_smul])).1 (hT₁.pos x h1).ne'
    · obtain ⟨τ, hτo, hξτ⟩ := h2x h2
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_smul] at hW'
      exact absurd (Submission.ltg_simple_unit_rigidity P k τ τ (ξ₂ x) (ξ₂ x) (θ₂ x) 0 hτo hτo
        hξτ hξτ (hT₂.pos x h2).le le_rfl (by rw [← hW', zero_smul])).1 (hT₂.pos x h2).ne'
    · exact ⟨iff_of_false h1 h2, fun h => absurd h h1⟩
  refine ⟨?_, ?_⟩
  · -- `(M₁ Δ M₂) ∩ O` lies in the exceptional null set.
    rw [ae_iff] at hpt
    refine measure_mono_null ?_ hpt
    rintro x ⟨hxs, hxO⟩ hcon
    rcases Set.mem_symmDiff.1 hxs with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact h2 ((hcon hxO).1.1 h1)
    · exact h1 ((hcon hxO).1.2 h2)
  · rw [ae_restrict_iff'₀ (hT₁.nullMeasurableSet.inter hO.measurableSet.nullMeasurableSet)]
    filter_upwards [hpt] with x hx hxMO
    exact (hx hxMO.2).2 hxMO.1

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

/-- `C_c^∞(Ω)` is dense in `L¹(Ω)` for real functions: for `Ω ⊆ ℝᵏ` open, `η` integrable on `Ω`
and `ε > 0` there is a smooth `φ` with compact support, `spt φ ⊆ Ω` and `∫_Ω |η − φ| < ε`.  For
`k = 0` the space is a point, so `Ω = ∅` (take `φ = 0`) or `Ω = ℝ⁰` (take `φ = η`, a constant).
For `k ≥ 1` the field `c = η e₀` is approximated by `b` (`slicing_im_ll_gws_smooth_dense`) and
`φ = b₀` is its first coordinate, so `|η − φ| = |(c − b)₀| ≤ |c − b|`. -/
theorem Submission.deformation_ipl_mwc_td_scalar_smooth_dense :
    ∀ (k : ℕ) (Ω : Set (Eucl k)) (η : Eucl k → ℝ), IsOpen Ω → IntegrableOn η Ω (volume : Measure (Eucl k)) → ∀ ε : ℝ, 0 < ε → ∃ φ : Eucl k → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧ ∫ w in Ω, |η w - φ w| ∂(volume : Measure (Eucl k)) < ε := by
  intro k Ω η hΩ hη ε hε
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: `Eucl 0` is a single point, so `Ω = ∅` or `Ω = univ`.
    by_cases hΩe : Ω = ∅
    · subst hΩe
      exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simpa using hε⟩
    · have hΩu : Ω = univ := by
        obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hΩe
        exact eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      have hconst : η = fun _ => η 0 := funext fun x => congrArg η (Subsingleton.elim x 0)
      refine ⟨η, ?_, ?_, by simp [hΩu], by simpa using hε⟩
      · rw [hconst]
        exact contDiff_const
      · exact subsingleton_of_subsingleton.isCompact.of_isClosed_subset (isClosed_tsupport _)
          (subset_univ _)
  · -- `k ≥ 1`: carry `η` as the first coordinate of a vector field and project back.
    let i₀ : Fin k := ⟨0, hk⟩
    let e : Eucl k := EuclideanSpace.single i₀ (1 : ℝ)
    have he : e i₀ = 1 := by simp [e]
    have hc : IntegrableOn (fun w => η w • e) Ω := hη.smul_const e
    obtain ⟨b, hb, hbc, hbΩ, hbε⟩ :=
      Submission.slicing_im_ll_gws_smooth_dense k Ω (fun w => η w • e) hΩ hc ε hε
    let p : Eucl k →L[ℝ] ℝ := EuclideanSpace.proj i₀
    have hp : ∀ v : Eucl k, p v = v i₀ := fun v => rfl
    have hp0 : p 0 = 0 := map_zero p
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (p ∘ b) := p.contDiff.comp hb
    have hφc : HasCompactSupport (p ∘ b) := hbc.comp_left hp0
    refine ⟨p ∘ b, hφ, hφc, (tsupport_comp_subset hp0 b).trans hbΩ, ?_⟩
    have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbc
    have hφi : Integrable (p ∘ b) := hφ.continuous.integrable_of_hasCompactSupport hφc
    -- `|η − φ| = |(c − b)₀| ≤ ‖c − b‖` pointwise, and both sides are integrable on `Ω`.
    have hptw : ∀ w, |η w - (p ∘ b) w| ≤ ‖η w • e - b w‖ := fun w => by
      have h1 : (η w • e - b w) i₀ = η w - (p ∘ b) w := by
        simp [Function.comp, hp, he]
      rw [← h1, ← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ _
    calc ∫ w in Ω, |η w - (p ∘ b) w| ≤ ∫ w in Ω, ‖η w • e - b w‖ :=
          setIntegral_mono (hη.sub hφi.integrableOn).abs (hc.sub hbi.integrableOn).norm hptw
      _ < ε := hbε
/-- Leibniz bound for determinants: if every entry of a real `n × n` matrix satisfies
`|A i j| ≤ c`, then `|det A| ≤ n! · cⁿ`.  Expand `det A = ∑_σ sgn(σ) • ∏_i A (σ i) i`, apply the
triangle inequality, drop the sign `±1`, bound each product of `n` entries by `cⁿ`, and count the
`n!` permutations of `Fin n`. -/
theorem Submission.deformation_ipl_mwc_mil_abs_det_le :
    ∀ (n : ℕ) (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, |A i j| ≤ c) →
      |Matrix.det A| ≤ (n.factorial : ℝ) * c ^ n := by
  intro n c A hA
  rw [Matrix.det_apply]
  calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, |A (σ i) i| := by
        -- `sgn σ = ±1`, and `|·|` is multiplicative on finite products.
        refine Finset.sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
          simp [h, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
        refine Finset.sum_le_sum fun σ _ => ?_
        calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c :=
              Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA _ _)
          _ = c ^ n := by simp
    _ = (n.factorial : ℝ) * c ^ n := by
        simp [Fintype.card_perm]

/-- **Dominated convergence for `h_m · det A_m`.**  If the entries of `A_m(x)` are bounded by
`C`, `|h_m| ≤ H` with `H` integrable for all large `m`, and `h_m → h₀`, `A_m → A₀` entrywise
`μ`-a.e., then `∫ h_m det A_m dμ → ∫ h₀ det A₀ dμ`.  Dominated convergence with the bound
`H · n! Cⁿ` (`deformation_ipl_mwc_mil_abs_det_le`); `det A_m` is a.e.-strongly measurable by
the Leibniz formula and `det` is continuous in the entries. -/
theorem Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (n : ℕ) (C : ℝ) (A : ℕ → Fin n → Fin n → α → ℝ) (A₀ : Fin n → Fin n → α → ℝ) (h : ℕ → α → ℝ) (h₀ H : α → ℝ), (∀ m t s, AEStronglyMeasurable (A m t s) μ) → (∀ m, AEStronglyMeasurable (h m) μ) → Integrable H μ → (∀ m t s x, |A m t s x| ≤ C) → (∀ᶠ m in atTop, ∀ x, |h m x| ≤ H x) → (∀ᵐ x ∂μ, Tendsto (fun m => h m x) atTop (𝓝 (h₀ x))) → (∀ᵐ x ∂μ, ∀ t s, Tendsto (fun m => A m t s x) atTop (𝓝 (A₀ t s x))) → Tendsto (fun m => ∫ x, h m x * Matrix.det (Matrix.of fun t s => A m t s x) ∂μ) atTop (𝓝 (∫ x, h₀ x * Matrix.det (Matrix.of fun t s => A₀ t s x) ∂μ)) := by
  intro α _ μ n C A A₀ h h₀ H hAm hhm hH hAb hhb hhl hAl
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => H x * ((n.factorial : ℝ) * C ^ n)) ?_ ?_ (hH.mul_const _) ?_
  · -- Leibniz: `det A_m(x) = ∑_σ sgn σ ∏_i A_m(σ i, i, x)`, finite sums and products of
    -- a.e.-strongly measurable functions.
    refine Eventually.of_forall fun m => (hhm m).mul ?_
    have hdet : (fun x => Matrix.det (Matrix.of fun t s => A m t s x)) =
        fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A m (σ i) i x := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [hdet]
    refine Finset.aestronglyMeasurable_fun_sum _ fun σ _ => ?_
    exact aestronglyMeasurable_const.mul
      (Finset.aestronglyMeasurable_fun_prod _ fun i _ => hAm m _ _)
  · -- `|h_m(x) det A_m(x)| ≤ H(x) · n! Cⁿ` for every `x`, once `|h_m| ≤ H`.
    filter_upwards [hhb] with m hm
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hm x)
      (Submission.deformation_ipl_mwc_mil_abs_det_le n C _ fun t s => hAb m t s x)
      (abs_nonneg _) ((abs_nonneg _).trans (hm x))
  · -- Entrywise convergence gives `A_m(x) → A₀(x)` in the product topology; `det` is continuous.
    filter_upwards [hhl, hAl] with x hx1 hx2
    refine hx1.mul ?_
    have hc : Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := continuous_id.matrix_det
    exact (hc.tendsto _).comp (tendsto_pi_nhds.2 fun t => tendsto_pi_nhds.2 fun s => hx2 t s)
/-- A.e. derivative of a coordinate of a Lipschitz map (the Rademacher step of the Lipschitz
minor integration by parts in the proof of Simon Ch. 6, 3.9): if `v : ℝᵏ → ℝ^Q` is `C`-Lipschitz
on an open `Ω` and `g = v^c := proj_c ∘ v` on `Ω`, then for Lebesgue-a.e. `w ∈ Ω`,
`Dg(w) x = proj_c (Dv(w) x)` for every `x`.  By Rademacher's theorem `v` is differentiable within
`Ω` at a.e. `w ∈ Ω`, hence at `w` as `Ω` is open; `g` and `v^c` agree near `w`, so they have the
same `fderiv`, which is `proj_c ∘L Dv(w)` by the chain rule.  No regularity of `g` is needed. -/
theorem Submission.deformation_ipl_mwc_mil_ae_fderiv_eq_proj :
    ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : Eucl k → Eucl Q) (c : Fin Q)
      (g : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω →
      EqOn g (fun w => EuclideanSpace.proj c (v w)) Ω →
      ∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → ∀ x : Eucl k,
        fderiv ℝ g w x = EuclideanSpace.proj c (fderiv ℝ v w x) := by
  intro k Q Ω C v c g hΩ hv hg
  -- Rademacher's theorem on `Ω`: `v` is differentiable within `Ω` at a.e. `w ∈ Ω`.
  filter_upwards [hv.ae_differentiableWithinAt_of_mem (μ := volume)] with w hw hwΩ x
  -- `Ω` is a neighbourhood of `w`, so `v` is differentiable at `w` and `g = proj_c ∘ v` near `w`.
  have hd : DifferentiableAt ℝ v w := (hw hwΩ).differentiableAt (hΩ.mem_nhds hwΩ)
  have heq : g =ᶠ[𝓝 w] (fun w => EuclideanSpace.proj c (v w)) :=
    eventuallyEq_of_mem (hΩ.mem_nhds hwΩ) hg
  -- Chain rule for the continuous linear map `proj_c`.
  have hcomp : HasFDerivAt (fun w => EuclideanSpace.proj c (v w))
      ((EuclideanSpace.proj c).comp (fderiv ℝ v w)) w :=
    (EuclideanSpace.proj c : Eucl Q →L[ℝ] ℝ).hasFDerivAt.comp w hd.hasFDerivAt
  -- Locality of `fderiv`: `Dg(w) = D(proj_c ∘ v)(w) = proj_c ∘L Dv(w)`.
  rw [heq.fderiv_eq, hcomp.fderiv]
  rfl
/-- **A directional derivative of a compactly supported `C¹` function has integral `0`.**  For
`h : ℝᵏ → ℝ` of class `C¹` with compact support and `e ∈ ℝᵏ`, `∫ Dh(w)(e) dw = 0`, where
`Dh(w) = fderiv ℝ h w`.  `h` is Lipschitz, so integration by parts for Lipschitz functions against
the constant function `1` gives `∫ ∂ₑ1 · h = ∫ ∂₋ₑh · 1`.  The left side vanishes and, `h` being
differentiable, `∂₋ₑh(w) = Dh(w)(-e) = -Dh(w)(e)`, so the right side is `-∫ Dh(w)(e) dw`. -/
theorem Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero :
    ∀ (k : ℕ) (h : Eucl k → ℝ) (e : Eucl k), ContDiff ℝ 1 h → HasCompactSupport h →
      ∫ w, fderiv ℝ h w e ∂(volume : Measure (Eucl k)) = 0 := by
  intro k h e hh hcs
  -- `h` is Lipschitz; integrate by parts against the constant function `1`.
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hh one_ne_zero
  have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Eucl k)))
    (LipschitzWith.const (α := Eucl k) (1 : ℝ)) hD hcs e
  -- Both functions are differentiable, so their line derivatives are Fréchet derivatives.
  have h1 : ∀ w, lineDeriv ℝ (fun _ : Eucl k => (1 : ℝ)) w e = 0 := fun w => by
    rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
    simp
  have h2 : ∀ w, lineDeriv ℝ h w (-e) = -fderiv ℝ h w e := fun w => by
    rw [((hh.differentiable one_ne_zero) w).lineDeriv_eq_fderiv]
    simp
  simp only [h1, h2, zero_mul, integral_zero, mul_one, integral_neg] at key
  linarith
/-- **The determinant of a matrix of `C^m` functions is `C^m`.**  Let `M t s : ℝᵏ → ℝ`
(`t, s : Fin n`) be `C^m` for some `m : WithTop ℕ∞` (finite, `∞` or `ω`).  Then
`w ↦ det (M t s w)ₜₛ` is `C^m`.  By the Leibniz formula `det A = ∑_σ sign σ · ∏ᵢ A (σ i) i`, this
function is a finite sum, over the permutations `σ` of `Fin n`, of constant multiples of finite
products of entries (for `n = 0` it is the constant `1`). -/
theorem Submission.deformation_ipl_mwc_mis_det_contDiff :
    ∀ (k n : ℕ) (m : WithTop ℕ∞) (M : Fin n → Fin n → Eucl k → ℝ),
      (∀ t s, ContDiff ℝ m (M t s)) →
        ContDiff ℝ m (fun w => Matrix.det (Matrix.of fun t s : Fin n => M t s w)) := by
  intro k n m M hM
  -- Leibniz formula: `det (M t s w)ₜₛ = ∑_σ sign σ * ∏ᵢ M (σ i) i w`.
  simp only [Matrix.det_apply', Matrix.of_apply]
  -- Each summand is a constant times a finite product of `C^m` entries.
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hM _ _
/-- Signed first-row cofactors as restricted Leibniz sums: `(-1)^q` times the minor of the
`r × (r + 1)` array `N` with column `q` deleted is the sum of `sgn σ * ∏ t, N t (σ t.succ)` over
the permutations `σ` of `Fin (r + 1)` with `σ 0 = q`.  Both sides are the determinant of the
matrix with row `0` equal to `Pi.single q 1` and row `t.succ` equal to `N t`. -/
theorem Submission.deformation_ipl_mwc_pi_cofactor_leibniz : ∀ (r : ℕ) (N : Fin r → Fin (r + 1) → ℝ) (q : Fin (r + 1)), (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) = ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
  intro r N q
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := Matrix.of (Matrix.vecCons (Pi.single q 1) N)
  -- Laplace expansion along row `0`: only the column `j = q` survives.
  have h1 : A.det = (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) := by
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single q]
    · have hsub : A.submatrix Fin.succ q.succAbove =
          Matrix.of fun t s : Fin r => N t (q.succAbove s) := by
        ext t s
        simp [A]
      rw [hsub]
      simp [A]
    · intro j _ hj
      simp [A, hj]
    · intro h
      exact absurd (Finset.mem_univ q) h
  -- Leibniz formula for `Aᵀ`: the row-`0` factor `Pi.single q 1 (σ 0)` selects `σ 0 = q`.
  have h2 : A.det = ∑ σ : Equiv.Perm (Fin (r + 1)),
      (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [A, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Pi.single_apply]
    split_ifs <;> ring
  rw [← h1, h2]
/-- Schwarz symmetry of mixed directional second derivatives of a `C²` function on `ℝ^k`:
`∂_v (∂_u f)(x) = ∂_u (∂_v f)(x)`. -/
theorem Submission.deformation_ipl_mwc_pi_hessian_symm :
    ∀ (k : ℕ) (f : Eucl k → ℝ), ContDiff ℝ 2 f → ∀ x u v : Eucl k,
      fderiv ℝ (fun y : Eucl k => fderiv ℝ f y u) x v =
        fderiv ℝ (fun y : Eucl k => fderiv ℝ f y v) x u := by
  intro k f hf x u v
  -- `Df` is `C¹`, hence differentiable at `x`; by Schwarz, `D²f(x)` is symmetric.
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := (h1.differentiable (by norm_num)) x
  have hs : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  -- Differentiating `y ↦ Df(y) u` at `x` in direction `v` gives `D²f(x) v u`.
  rw [fderiv_clm_apply hd (differentiableAt_const u),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa using hs v u
/-- Product rule for a weighted sum of finite products: if every `g i t` is differentiable at
`w`, the derivative of `x ↦ ∑ i, a i * ∏ t, g i t x` at `w` in direction `v` is
`∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ≠ u, g i t w`. -/
theorem Submission.deformation_ipl_mwc_pi_fderiv_sum_prod : ∀ (k r : ℕ) (ι : Type) [Fintype ι] (a : ι → ℝ) (g : ι → Fin r → Eucl k → ℝ) (w v : Eucl k), (∀ i t, DifferentiableAt ℝ (g i t) w) → fderiv ℝ (fun x : Eucl k => ∑ i, a i * ∏ t, g i t x) w v = ∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ∈ Finset.univ.erase u, g i t w := by
  intro k r ι _ a g w v hg
  -- Product rule for each `∏ t, g i t`, then the constant factor `a i` and the sum over `ι`.
  have hs : HasFDerivAt (fun x => ∑ i, a i * ∏ t, g i t x)
      (∑ i, a i • ∑ u, (∏ t ∈ Finset.univ.erase u, g i t w) • fderiv ℝ (g i u) w) w :=
    HasFDerivAt.fun_sum fun i _ =>
      (HasFDerivAt.finsetProd fun t _ => (hg i t).hasFDerivAt).const_mul (a i)
  -- Evaluate the derivative at `v` termwise and commute the real factors.
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  ring
/-- Algebraic core of the Piola identity: an alternating sum over permutations against a kernel
`H u` symmetric in its two arguments vanishes, since `σ ↦ σ * swap 0 u.succ` reverses the sign,
exchanges the two arguments of `H u` and fixes every other factor. -/
theorem Submission.deformation_ipl_mwc_pi_swap_cancel : ∀ (r : ℕ) (H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ) (N : Fin r → Fin (r + 1) → ℝ), (∀ u i j, H u i j = H u j i) → ∑ σ : Equiv.Perm (Fin (r + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ u : Fin r, H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) = 0 := by
  intro r H N hH
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  -- Pair `σ` with `σ * τ`, `τ = (0 u.succ)`; the terms `T σ` and `T (σ * τ)` cancel.
  let τ : Equiv.Perm (Fin (r + 1)) := Equiv.swap 0 u.succ
  have hτne : (0 : Fin (r + 1)) ≠ u.succ := (Fin.succ_ne_zero u).symm
  let T : Equiv.Perm (Fin (r + 1)) → ℝ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * (H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ))
  have hT : ∀ σ : Equiv.Perm (Fin (r + 1)), T (σ * τ) = - T σ := by
    intro σ
    have h0 : (σ * τ) 0 = σ u.succ := by simp [τ, Equiv.Perm.mul_apply]
    have h1 : (σ * τ) u.succ = σ 0 := by simp [τ, Equiv.Perm.mul_apply]
    have hprod : ∏ t ∈ Finset.univ.erase u, N t ((σ * τ) t.succ) =
        ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) := by
      refine Finset.prod_congr rfl (fun t ht => ?_)
      have htu : t ≠ u := Finset.ne_of_mem_erase ht
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero t)
        (fun h => htu (Fin.succ_injective _ h))]
    have hsign : ((Equiv.Perm.sign (σ * τ) : ℤ) : ℝ) = - ((Equiv.Perm.sign σ : ℤ) : ℝ) := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hτne]
      push_cast
      ring
    simp only [T]
    rw [h0, h1, hprod, hsign, hH u (σ u.succ) (σ 0)]
    ring
  have hS : ∑ σ, T σ = - ∑ σ, T σ :=
    calc ∑ σ, T σ = ∑ σ, T (σ * τ) := (Equiv.sum_comp (Equiv.mulRight τ) T).symm
      _ = ∑ σ, - T σ := Finset.sum_congr rfl (fun σ _ => hT σ)
      _ = - ∑ σ, T σ := Finset.sum_neg_distrib _
  linarith

/-- Piola identity (step (3.2)(i) of the proof of `minor_weak_continuity`; Evans, PDE, §8.1.4(b),
Lemma 1): for `C²` functions `W_0, …, W_{r-1}` on `ℝ^k` and `b : Fin (r + 1) → Fin k`, the signed
minors `c_q = (-1)^q det (∂_{b (q.succAbove s)} W_t)_{t,s}` satisfy `∑_q ∂_{b q} c_q = 0`.
By the cofactor formula `c_q = ∑_{σ 0 = q} sgn σ ∏_t ∂_{b (σ t.succ)} W_t` and the product rule,
`∑_q ∂_{b q} c_q = ∑_σ sgn σ ∑_u H_u(σ 0, σ u.succ) ∏_{t ≠ u} ∂_{b (σ t.succ)} W_t` with
`H_u(i, j) = ∂_{b i} ∂_{b j} W_u`; this vanishes since `H_u` is symmetric (Schwarz) and
`σ ↦ σ * swap 0 u.succ` changes the sign. -/
theorem Submission.deformation_ipl_mwc_piola_identity :
    ∀ (k r : ℕ) (W : Fin r → Eucl k → ℝ) (b : Fin (r + 1) → Fin k), (∀ t, ContDiff ℝ 2 (W t)) →
      ∀ w : Eucl k, ∑ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w
          (EuclideanSpace.single (b q) 1) = 0 := by
  intro k r W b hW w
  -- `D t i x = ∂_{b i} W_t (x)`, the entries of the minors; `C¹` since `W_t` is `C²`.
  let D : Fin r → Fin (r + 1) → Eucl k → ℝ := fun t i x =>
    fderiv ℝ (W t) x (EuclideanSpace.single (b i) 1)
  have hD : ∀ t i, DifferentiableAt ℝ (D t i) w := fun t i =>
    (((hW t).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero w).clm_apply
      (differentiableAt_const _)
  -- `H u i j = ∂_{b i} ∂_{b j} W_u (w)` is symmetric in `(i, j)`.
  let H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ := fun u i j =>
    fderiv ℝ (D u j) w (EuclideanSpace.single (b i) 1)
  have hH : ∀ u i j, H u i j = H u j i := fun u i j =>
    Submission.deformation_ipl_mwc_pi_hessian_symm k (W u) (hW u) w
      (EuclideanSpace.single (b j) 1) (EuclideanSpace.single (b i) 1)
  -- Cofactor formula and product rule: `∂_{b q} c_q = ∑_{σ 0 = q} sgn σ ∂_{b q} ∏_t D t (σ t.succ)`
  have hc : ∀ q : Fin (r + 1), fderiv ℝ (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) w
        (EuclideanSpace.single (b q) 1) =
      ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) *
        ∑ u : Fin r, H u q (σ u.succ) * ∏ t ∈ Finset.univ.erase u, D t (σ t.succ) w := by
    intro q
    have hcof : (fun x : Eucl k => (-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (W t) x (EuclideanSpace.single (b (q.succAbove s)) 1))) =
        fun x => ∑ σ : Equiv.Perm (Fin (r + 1)),
          (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, D t (σ t.succ) x :=
      funext fun x => Submission.deformation_ipl_mwc_pi_cofactor_leibniz r (fun t i => D t i x) q
    rw [hcof]
    exact Submission.deformation_ipl_mwc_pi_fderiv_sum_prod k r (Equiv.Perm (Fin (r + 1)))
      (fun σ => if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0)
      (fun σ t => D t (σ t.succ)) w _ fun σ t => hD t (σ t.succ)
  -- Sum over `q`: only `q = σ 0` survives, and the sum cancels in pairs `σ, σ * swap 0 u.succ`.
  refine Eq.trans ?_
    (Submission.deformation_ipl_mwc_pi_swap_cancel r H (fun t i => D t i w) hH)
  rw [Fintype.sum_congr _ _ hc, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun σ => ?_
  rw [Finset.sum_eq_single (σ 0) (fun q _ hq => by rw [ite_eq_right (Ne.symm hq), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- Integration by parts for Jacobian minors of `C²` functions (step (3.2)(ii) of the weak
continuity of Jacobian minors behind the Lipschitz push-forward limits in the proof of the
Deformation Theorem, Simon Ch. 6, 5.1): for `C²` functions `V₀, …, V_r : ℝᵏ → ℝ`, directions
`b : Fin (r + 1) → Fin k` and `φ ∈ C¹_c(ℝᵏ)`, with
`A = (∂_{b(s)} V_t)_{t,s}` and the signed first-row cofactors
`C_q = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1})_{t,s}`, `∫ φ det A = -∑_q ∫ V₀ C_q ∂_{b(q)} φ`.
Laplace expansion along row `0` gives `det A = ∑_q ∂_{b(q)} V₀ · C_q`.  The directional derivative
`∂_{b(q)}(V₀ φ C_q)` of the compactly supported `C¹` function `V₀ φ C_q` has integral `0`, and the
product rule turns this into `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`.
Summing over `q`, the last terms cancel by the Piola identity `∑_q ∂_{b(q)} C_q = 0`. -/
theorem Submission.deformation_ipl_mwc_minor_ibp_smooth :
    ∀ (k r : ℕ) (V : Fin (r + 1) → Eucl k → ℝ) (b : Fin (r + 1) → Fin k) (φ : Eucl k → ℝ),
      (∀ t, ContDiff ℝ 2 (V t)) → ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
          fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k)) =
        -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) *
          Matrix.det (Matrix.of fun t s : Fin r =>
            fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
          fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
  intro k r V b φ hV hφ hφc
  -- `C q w = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1}(w))_{t,s}`: the signed first-row cofactors.
  obtain ⟨C, hC⟩ : ∃ C : Fin (r + 1) → Eucl k → ℝ, ∀ q w, C q w = (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1)) :=
    ⟨_, fun _ _ => rfl⟩
  have hCf : ∀ q, C q = fun w => (-1 : ℝ) ^ (q : ℕ) *
      Matrix.det (Matrix.of fun t s : Fin r =>
        fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1)) :=
    fun q => funext (hC q)
  -- Step 1 (Laplace expansion along row `0`): `det A = ∑_q ∂_{b(q)} V₀ · C_q`.
  have hLap : ∀ w, Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
      fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) =
      ∑ q, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * C q w := by
    intro w
    rw [Matrix.det_succ_row_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hC q w, Matrix.of_apply]
    have hsub : (Matrix.of fun t s : Fin (r + 1) =>
        fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)).submatrix Fin.succ q.succAbove =
        Matrix.of fun t s : Fin r =>
          fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1) := rfl
    rw [hsub]
    ring
  -- Step 2 (regularity): the entries `∂_i V_t` and, by the Leibniz formula, the cofactors `C_q`
  -- are `C¹`.
  have hDV : ∀ t i, ContDiff ℝ 1 fun w => fderiv ℝ (V t) w (EuclideanSpace.single i 1) :=
    fun t i => ((hV t).fderiv_right (m := 1) one_add_one_eq_two.le).clm_apply contDiff_const
  have hV0 : ContDiff ℝ 1 (V 0) := (hV 0).of_le one_le_two
  have hCd : ∀ q, ContDiff ℝ 1 (C q) := by
    intro q
    rw [hCf q]
    exact contDiff_const.mul (Submission.deformation_ipl_mwc_mis_det_contDiff k r 1
      (fun t s w => fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      fun t s => hDV t.succ _)
  -- Step 3 (supports and integrability): `φ` and `Dφ` vanish off the compact set `tsupport φ`,
  -- so every continuous integrand below with a factor `φ` or `∂_i φ` is integrable.
  have hφ0 : ∀ w, w ∉ tsupport φ → φ w = 0 := fun w hw => image_eq_zero_of_notMem_tsupport hw
  have hdφ0 : ∀ w, w ∉ tsupport φ → fderiv ℝ φ w = 0 :=
    fun w hw => fderiv_of_notMem_tsupport ℝ hw
  have hcs : ∀ g : Eucl k → ℝ, (∀ w, w ∉ tsupport φ → g w = 0) → HasCompactSupport g := by
    intro g hg0
    refine hφc.mono' fun w hw => ?_
    by_contra hw'
    exact (Function.mem_support.mp hw) (hg0 w hw')
  have hint : ∀ g : Eucl k → ℝ, Continuous g → (∀ w, w ∉ tsupport φ → g w = 0) →
      Integrable g (volume : Measure (Eucl k)) :=
    fun g hg hg0 => hg.integrable_of_hasCompactSupport (hcs g hg0)
  have hcDφ : ∀ i, Continuous fun w => fderiv ℝ φ w (EuclideanSpace.single i 1) :=
    fun i => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDC : ∀ q i, Continuous fun w => fderiv ℝ (C q) w (EuclideanSpace.single i 1) :=
    fun q i => ((hCd q).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hT1 : ∀ q, Integrable (fun w => fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) *
      φ w * C q w) (volume : Measure (Eucl k)) := fun q =>
    hint _ (((hDV 0 _).continuous.mul hφ.continuous).mul (hCd q).continuous)
      fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul]
  have hT2 : ∀ q, Integrable (fun w => V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) *
      C q w) (volume : Measure (Eucl k)) := fun q =>
    hint _ ((hV0.continuous.mul (hcDφ _)).mul (hCd q).continuous)
      fun w hw => by rw [hdφ0 w hw, zero_apply, mul_zero, zero_mul]
  have hT3 : ∀ q, Integrable (fun w => V 0 w * φ w *
      fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1)) (volume : Measure (Eucl k)) := fun q =>
    hint _ ((hV0.continuous.mul hφ.continuous).mul (hcDC q _))
      fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul]
  -- Product rule for `V₀ φ C_q` in the direction `e_{b(q)}`.
  have hprod : ∀ q w, fderiv ℝ (fun y => V 0 y * φ y * C q y) w (EuclideanSpace.single (b q) 1) =
      fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w +
        V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w +
        V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
    intro q w
    have hd : HasFDerivAt (fun y => V 0 y * φ y * C q y)
        ((V 0 w * φ w) • fderiv ℝ (C q) w +
          C q w • (V 0 w • fderiv ℝ φ w + φ w • fderiv ℝ (V 0) w)) w :=
      ((hV0.differentiable one_ne_zero w).hasFDerivAt.mul
        (hφ.differentiable one_ne_zero w).hasFDerivAt).mul
        ((hCd q).differentiable one_ne_zero w).hasFDerivAt
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- Steps 4–5 (one integration by parts for each `q`): `∫ ∂_{b(q)}(V₀ φ C_q) = 0`, so
  -- `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`.
  have hq : ∀ q, ∫ w, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w =
      -(∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
        ∫ w, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
    intro q
    have h0 := Submission.deformation_ipl_mwc_mis_integral_fderiv_eq_zero k
      (fun y => V 0 y * φ y * C q y) (EuclideanSpace.single (b q) 1) ((hV0.mul hφ).mul (hCd q))
      (hcs _ fun w hw => by rw [hφ0 w hw, mul_zero, zero_mul])
    simp only [hprod q] at h0
    have h12 : Integrable (fun w => fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w +
        V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w)
        (volume : Measure (Eucl k)) := (hT1 q).add (hT2 q)
    rw [integral_add h12 (hT3 q), integral_add (hT1 q) (hT2 q)] at h0
    linarith
  -- Step 6 (Piola identity for the rows `W_t = V_{t+1}`): `∑_q ∂_{b(q)} C_q = 0`.
  have hdivC : ∀ w, ∑ q, fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) = 0 := by
    intro w
    simp only [hCf]
    exact Submission.deformation_ipl_mwc_piola_identity k r (fun t => V t.succ) b
      (fun t => hV t.succ) w
  calc ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
          fderiv ℝ (V t) w (EuclideanSpace.single (b s) 1)) ∂(volume : Measure (Eucl k))
      = ∫ w, ∑ q, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w := by
        refine integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [hLap w, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ q, ∫ w, fderiv ℝ (V 0) w (EuclideanSpace.single (b q) 1) * φ w * C q w :=
        integral_finsetSum _ fun q _ => hT1 q
    _ = ∑ q, (-(∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
          ∫ w, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1)) :=
        Finset.sum_congr rfl fun q _ => hq q
    _ = -(∑ q, ∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w) -
          ∫ w, ∑ q, V 0 w * φ w * fderiv ℝ (C q) w (EuclideanSpace.single (b q) 1) := by
        rw [integral_finsetSum _ fun q _ => hT3 q, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    _ = -∑ q, ∫ w, V 0 w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) * C q w := by
        simp only [← Finset.mul_sum, hdivC, mul_zero, integral_zero, sub_zero]
    _ = -∑ q : Fin (r + 1), ∫ w, V 0 w * ((-1 : ℝ) ^ (q : ℕ) *
          Matrix.det (Matrix.of fun t s : Fin r =>
            fderiv ℝ (V t.succ) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
          fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
        congr 1
        refine Finset.sum_congr rfl fun q _ => integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [hC q w]
        ring
/-- A smooth approximate identity on `ℝⁿ` (Simon Ch. 6, proof of 2.34, p. 143; Ch. 2, §2):
`ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)` for a smooth bump `0 ≤ h ≤ 1` with `h(0) = 1`,
`spt h ⊆ B_1(0)` and `I = ∫ h > 0`.  Each `ψ_k` is `C^∞`, nonnegative, of integral `1` and
supported in `B̄_{1/(k+1)}(0)`, and `0 ≤ ψ_k ≤ (k+1)ⁿ I⁻¹`.  For locally integrable `g` and every
Lebesgue point `x` of `g` (Simon Ch. 1, 3.17), `|(g ∗ ψ_k)(x) − g(x)| ≤ I⁻¹ Lⁿ(B_1(0)) ·
⨍_{B̄_{1/(k+1)}(x)} |g − g(x)| → 0`, so `g ∗ ψ_k → g` almost everywhere. -/
theorem Submission.constancy_mdc_smooth_approx_identity_ae_tendsto :
    ∀ n : ℕ, ∃ ψ : ℕ → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k)) ∧
      (∀ k, HasCompactSupport (ψ k)) ∧
      (∀ k : ℕ, tsupport (ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1))) ∧ (∀ k y, 0 ≤ ψ k y) ∧
      (∀ k, ∫ y, ψ k y ∂volume = 1) ∧
      ∀ g : Eucl n → ℝ, LocallyIntegrable g volume → ∀ᵐ x ∂volume,
        Tendsto (fun k => convolution g (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop
          (𝓝 (g x)) := by
  intro n
  -- A smooth bump `h` with `0 ≤ h ≤ 1`, `h 0 = 1` and `spt h ⊆ B_1(0)`; `I = ∫ h > 0`.
  obtain ⟨h, hts, hhc, hhs, hrange, h0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ball_mem_nhds (0 : Eucl n) one_pos)
  have hh0 : ∀ y, 0 ≤ h y := fun y => (hrange ⟨y, rfl⟩).1
  have hh1 : ∀ y, h y ≤ 1 := fun y => (hrange ⟨y, rfl⟩).2
  have hhcont : Continuous h := hhs.continuous
  have hhint : Integrable h volume := hhcont.integrable_of_hasCompactSupport hhc
  have hIpos : 0 < ∫ y, h y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => hh0 y) hhint]
    exact hhcont.isOpen_support.measure_pos volume ⟨0, by simp [Function.mem_support, h0]⟩
  set I := ∫ y, h y with hI
  have hzero : ∀ y : Eucl n, 1 ≤ ‖y‖ → h y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have := hts hy'
    rw [mem_ball, dist_zero_right] at this
    linarith
  -- The kernels `ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)`.
  have hs : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  set Ψ : ℕ → Eucl n → ℝ := fun k y => ((k : ℝ) + 1) ^ n * (I⁻¹ * h (((k : ℝ) + 1) • y))
    with hΨ
  have hΨsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ k) := fun k =>
    contDiff_const.mul (contDiff_const.mul (hhs.comp (contDiff_const_smul _)))
  have hΨzero : ∀ (k : ℕ) (y : Eucl n), 1 / ((k : ℝ) + 1) ≤ ‖y‖ → Ψ k y = 0 := by
    intro k y hy
    have h1 : 1 ≤ ‖((k : ℝ) + 1) • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hs k).le]
      rw [div_le_iff₀ (hs k)] at hy
      linarith
    simp only [hΨ, hzero _ h1, mul_zero]
  have hΨsupp : ∀ k : ℕ, tsupport (Ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1)) := by
    intro k
    refine closure_minimal ?_ isClosed_closedBall
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    exact hy (hΨzero k y hlt.le)
  have hΨc : ∀ k, HasCompactSupport (Ψ k) := fun k =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport _).trans (hΨsupp k))
  have hΨnn : ∀ k y, 0 ≤ Ψ k y := fun k y => by
    have := hh0 (((k : ℝ) + 1) • y)
    have := (hs k).le
    have := inv_nonneg.2 hIpos.le
    simp only [hΨ]
    positivity
  have hΨle : ∀ k y, Ψ k y ≤ ((k : ℝ) + 1) ^ n * I⁻¹ := fun k y => by
    simp only [hΨ]
    have hp : 0 ≤ ((k : ℝ) + 1) ^ n := by positivity
    have hIi : 0 ≤ I⁻¹ := inv_nonneg.2 hIpos.le
    have := hh1 (((k : ℝ) + 1) • y)
    calc ((k : ℝ) + 1) ^ n * (I⁻¹ * h (((k : ℝ) + 1) • y))
        ≤ ((k : ℝ) + 1) ^ n * (I⁻¹ * 1) := by gcongr
      _ = _ := by ring
  have hΨint : ∀ k, Integrable (Ψ k) volume := fun k =>
    (hΨsmooth k).continuous.integrable_of_hasCompactSupport (hΨc k)
  -- `∫ ψ_k = (k+1)ⁿ I⁻¹ (k+1)⁻ⁿ ∫ h = 1` by the linear change of variables `y ↦ (k+1) y`.
  have hΨone : ∀ k, ∫ y, Ψ k y = 1 := by
    intro k
    simp only [hΨ]
    rw [integral_const_mul, integral_const_mul, Measure.integral_comp_smul,
      finrank_euclideanSpace_fin]
    rw [smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < (((k : ℝ) + 1) ^ n)⁻¹), ← hI]
    field_simp
  refine ⟨Ψ, hΨsmooth, hΨc, hΨsupp, hΨnn, hΨone, ?_⟩
  intro g hg
  -- Lebesgue points: `⨍_{B̄_r(x)} |g − g(x)| → 0` as `r ↓ 0`, for a.e. `x`.
  have hleb :=
    IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Eucl n)) hg 1
  filter_upwards [hleb] with x hx
  set r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k, 0 < r k := fun k => by simp only [hr]; positivity
  have hrlim : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => hrpos k⟩
  have havg := hx (fun _ => x) r hrlim (Eventually.of_forall fun k => by
    rw [one_mul]; exact mem_closedBall_self (hrpos k).le)
  set ω := (volume : Measure (Eucl n)).real (ball 0 1) with hω
  have hωpos : 0 < ω := by
    rw [hω, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set C := I⁻¹ * ω with hC
  -- `|(g ∗ ψ_k)(x) − g(x)| ≤ C ⨍_{B̄_{1/(k+1)}(x)} |g − g(x)|` with `C = I⁻¹ Lⁿ(B_1(0))`.
  have hbound : ∀ k, ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ ≤
      C * ⨍ y in closedBall x (r k), ‖g y - g x‖ := by
    intro k
    set K := closedBall x (r k) with hK
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hconv : Integrable (fun t => g t * Ψ k (x - t)) volume := by
      have := (hΨc k).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hg
        (hΨsmooth k).continuous x
      simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using this
    have hconst : Integrable (fun t => g x * Ψ k (x - t)) volume :=
      ((hΨint k).comp_sub_left x).const_mul (g x)
    have hgx : g x = ∫ t, g x * Ψ k (x - t) := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun y => Ψ k y) volume x, hΨone k,
        mul_one]
    have hdiff : convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x =
        ∫ t, (g t - g x) * Ψ k (x - t) := by
      rw [convolution_def]
      conv_lhs => rw [hgx]
      rw [← integral_sub _ hconst]
      · congr 1
        funext t
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        ring
      · simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hconv
    have hoff : ∀ t, t ∉ K → ‖g t - g x‖ * Ψ k (x - t) = 0 := by
      intro t ht
      rw [hK, mem_closedBall, not_le, dist_eq_norm, ← norm_neg, neg_sub] at ht
      rw [hΨzero k (x - t) ht.le, mul_zero]
    have hgK : IntegrableOn g K volume := hg.integrableOn_isCompact hKc
    have hgxK : IntegrableOn (fun t => ‖g t - g x‖) K volume :=
      (hgK.sub (integrableOn_const (hKc.measure_lt_top.ne))).norm
    calc ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖
        = ‖∫ t, (g t - g x) * Ψ k (x - t)‖ := by rw [hdiff]
      _ ≤ ∫ t, ‖(g t - g x) * Ψ k (x - t)‖ := norm_integral_le_integral_norm _
      _ = ∫ t, ‖g t - g x‖ * Ψ k (x - t) := by
          congr 1
          funext t
          rw [norm_mul, Real.norm_of_nonneg (hΨnn k _)]
      _ = ∫ t in K, ‖g t - g x‖ * Ψ k (x - t) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
      _ ≤ ∫ t in K, ‖g t - g x‖ * (((k : ℝ) + 1) ^ n * I⁻¹) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hgxK.mul_const _)
            (Eventually.of_forall fun t => ?_)
          · exact mul_nonneg (norm_nonneg _) (hΨnn k _)
          · exact mul_le_mul_of_nonneg_left (hΨle k _) (norm_nonneg _)
      _ = (∫ t in K, ‖g t - g x‖) * (((k : ℝ) + 1) ^ n * I⁻¹) := integral_mul_const _ _
      _ = C * ⨍ y in K, ‖g y - g x‖ := by
          rw [setAverage_eq, smul_eq_mul, hC]
          have hKvol : (volume : Measure (Eucl n)).real K = r k ^ n * ω := by
            rw [measureReal_def, hK, Measure.addHaar_closedBall _ _ (hrpos k).le,
              finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
              hω, measureReal_def]
          rw [hKvol]
          simp only [hr]
          field_simp
          rw [mul_assoc, ← mul_pow, mul_one_div_cancel (hs k).ne', one_pow, mul_one]
  -- Squeeze: `0 ≤ |(g ∗ ψ_k)(x) − g(x)| ≤ C ⨍ … → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  simpa using havg.const_mul C
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
/-- **Smooth approximation of a Lipschitz function with a.e. convergent derivatives**
(mollification).  Let `ψ_m` be the kernels of `constancy_mdc_smooth_approx_identity_ae_tendsto`
and `G_m(x) = ∫ ψ_m(y) g(x − y) dy = (ψ_m ⋆ g)(x)`.  Then `G_m` is `C^∞`, `L`-Lipschitz (an
average of translates of `g`), and `|G_m − g| ≤ 2L/(m+1)` by
`slicing_mb_sa_mollify_lipschitz_close`.  Differentiating under the integral sign
(`slicing_mb_sa_mollify_lipschitz_hasFDerivAt`), `DG_m(x) e_b = (∂_b g ∗ ψ_m)(x)`, which tends to
`∂_b g(x)` for a.e. `x` because `∂_b g` is bounded and measurable; as `‖T‖ ≤ Σ_b |T e_b|` for
`T : ℝ^k →L[ℝ] ℝ`, `DG_m(x) → Dg(x)` for a.e. `x`. -/
theorem Submission.deformation_ipl_mwc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : ℝ≥0) (g : Eucl k → ℝ), LipschitzWith L g → ∃ G : ℕ → Eucl k → ℝ, (∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G m)) ∧ (∀ m, LipschitzWith L (G m)) ∧ TendstoUniformly G g atTop ∧ ∀ᵐ w ∂(volume : Measure (Eucl k)), Tendsto (fun m => fderiv ℝ (G m) w) atTop (𝓝 (fderiv ℝ g w)) := by
  intro k L g hg
  -- The kernels `ψ_m`: `C^∞`, `≥ 0`, `∫ ψ_m = 1`, `spt ψ_m ⊆ B̄_{1/(m+1)}(0)`.
  obtain ⟨ψ, hψs, hψc, hψsupp, hψnn, hψone, hψae⟩ :=
    Submission.constancy_mdc_smooth_approx_identity_ae_tendsto k
  have hψcont : ∀ m, Continuous (ψ m) := fun m => (hψs m).continuous
  have hψint : ∀ m, Integrable (ψ m) volume := fun m =>
    (hψcont m).integrable_of_hasCompactSupport (hψc m)
  -- `ψ_m(y) = 0` for `|y| ≥ 2/(m+1)`.
  have hψzero : ∀ (m : ℕ) (y : Eucl k), 2 / ((m : ℝ) + 1) ≤ ‖y‖ → ψ m y = 0 := by
    intro m y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have h1 := hψsupp m hy'
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : 1 / ((m : ℝ) + 1) < 2 / ((m : ℝ) + 1) :=
      div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith
  -- `G_m(x) = ∫ ψ_m(y) g(x − y) dy`.
  set G : ℕ → Eucl k → ℝ := fun m x => ∫ y, ψ m y * g (x - y) with hG
  refine ⟨G, fun m => ?_, fun m => ?_, ?_, ?_⟩
  · -- `G_m = ψ_m ⋆ g` is `C^∞`.
    have hconv : convolution (ψ m) g (ContinuousLinearMap.lsmul ℝ ℝ) volume = G m := by
      funext x
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hG]
    rw [← hconv]
    exact (hψc m).contDiff_convolution_left _ (hψs m) hg.continuous.locallyIntegrable
  · -- `|G_m(x) − G_m(x')| ≤ ∫ ψ_m(y) |g(x − y) − g(x' − y)| dy ≤ L |x − x'|`.
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hi : ∀ z, Integrable (fun y => ψ m y * g (z - y)) volume := fun z =>
      Continuous.integrable_of_hasCompactSupport
        ((hψcont m).mul (hg.continuous.comp (continuous_const.sub continuous_id))) (hψc m).mul_right
    have hpt : ∀ y, ‖ψ m y * g (x - y) - ψ m y * g (x' - y)‖ ≤ ψ m y * ((L : ℝ) * dist x x') := by
      intro y
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψnn m y)]
      refine mul_le_mul_of_nonneg_left ?_ (hψnn m y)
      rw [← Real.dist_eq]
      calc dist (g (x - y)) (g (x' - y)) ≤ L * dist (x - y) (x' - y) := hg.dist_le_mul _ _
        _ = L * dist x x' := by rw [dist_sub_right]
    rw [Real.dist_eq]
    simp only [hG]
    rw [← integral_sub (hi x) (hi x'), ← Real.norm_eq_abs]
    calc ‖∫ y, ψ m y * g (x - y) - ψ m y * g (x' - y)‖ ≤ ∫ y, ψ m y * ((L : ℝ) * dist x x') :=
          norm_integral_le_of_norm_le ((hψint m).mul_const _) (Eventually.of_forall hpt)
      _ = L * dist x x' := by rw [integral_mul_const, hψone m, one_mul]
  · -- `|G_m − g| ≤ 2L/(m+1) → 0`.
    have hclose : ∀ m x, |G m x - g x| ≤ (L : ℝ) * (2 / ((m : ℝ) + 1)) := fun m x =>
      Submission.slicing_mb_sa_mollify_lipschitz_close k g L hg (ψ m) (2 / ((m : ℝ) + 1))
        (hψcont m) (hψc m) (hψnn m) (hψzero m) (hψone m) x
    have hlim : Tendsto (fun m : ℕ => (L : ℝ) * (2 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (L : ℝ))
      rw [mul_zero] at this
      exact this.congr fun m => by ring
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hlim).2 ε hε] with m hm x
    rw [dist_comm, Real.dist_eq]
    exact (hclose m x).trans_lt hm
  · set e : Fin k → Eucl k := fun b => EuclideanSpace.basisFun (Fin k) ℝ b with he
    have hDg : ∀ z, ‖fderiv ℝ g z‖ ≤ L := fun z => norm_fderiv_le_of_lipschitz ℝ hg
    -- `DG_m(x) = ∫ ψ_m(y) Dg(x − y) dy`, a Bochner integral of an integrable integrand.
    have hfd : ∀ m x, fderiv ℝ (G m) x = ∫ y, ψ m y • fderiv ℝ g (x - y) := fun m x =>
      (Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt k g L hg (ψ m) (hψcont m)
        (hψc m) x).fderiv
    have hint : ∀ m x, Integrable (fun y => ψ m y • fderiv ℝ g (x - y)) volume := by
      intro m x
      refine ((hψint m).mul_const (L : ℝ)).mono' ?_ (Eventually.of_forall fun y => ?_)
      · exact ((hψcont m).measurable.smul ((measurable_fderiv ℝ g).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
      · rw [norm_smul, Real.norm_of_nonneg (hψnn m y)]
        exact mul_le_mul_of_nonneg_left (hDg _) (hψnn m y)
    -- Hence `DG_m(x) v = (Dg(·) v ∗ ψ_m)(x)`.
    have happly : ∀ m x v, fderiv ℝ (G m) x v =
        convolution (fun t => fderiv ℝ g t v) (ψ m) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro m x v
      rw [hfd, ContinuousLinearMap.integral_apply (hint m x), convolution_lsmul_swap]
      congr 1
      funext t
      simp only [smul_apply, smul_eq_mul, mul_comm]
    -- `Dg(·) v` is measurable and bounded by `L |v|`, hence locally integrable.
    have hloc : ∀ v, LocallyIntegrable (fun t => fderiv ℝ g t v) volume := by
      intro v
      refine (locallyIntegrable_const ((L : ℝ) * ‖v‖)).mono
        (measurable_fderiv_apply_const ℝ g v).aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg L.coe_nonneg (norm_nonneg v))]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDg t) (norm_nonneg _))
    -- For a.e. `x`: `DG_m(x) e_b → Dg(x) e_b` for every `b`.
    have hae : ∀ᵐ x ∂(volume : Measure (Eucl k)), ∀ b,
        Tendsto (fun m => fderiv ℝ (G m) x (e b)) atTop (𝓝 (fderiv ℝ g x (e b))) := by
      rw [ae_all_iff]
      intro b
      filter_upwards [hψae _ (hloc (e b))] with x hx
      simp_rw [happly]
      exact hx
    -- `‖T‖ ≤ Σ_b |T e_b|`, writing `z = Σ_b z_b e_b` with `|z_b| ≤ |z|`.
    have hnorm : ∀ T : Eucl k →L[ℝ] ℝ, ‖T‖ ≤ ∑ b, |T (e b)| := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound _
        (Finset.sum_nonneg fun b _ => abs_nonneg _) fun z => ?_
      have hz : z = ∑ b, z b • e b := by
        simpa [he] using ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr z).symm
      calc ‖T z‖ = ‖∑ b, z b * T (e b)‖ := by
            conv_lhs => rw [hz]
            simp [map_sum, map_smul]
        _ ≤ ∑ b, ‖z b * T (e b)‖ := norm_sum_le _ _
        _ = ∑ b, ‖z b‖ * |T (e b)| := by simp [norm_mul]
        _ ≤ ∑ b, ‖z‖ * |T (e b)| := Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z b) (abs_nonneg _)
        _ = (∑ b, |T (e b)|) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
    -- Squeeze: `‖DG_m(x) − Dg(x)‖ ≤ Σ_b |DG_m(x) e_b − Dg(x) e_b| → 0`.
    filter_upwards [hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => hnorm _) ?_
    have hsum : Tendsto (fun m => ∑ b, |(fderiv ℝ (G m) x - fderiv ℝ g x) (e b)|) atTop
        (𝓝 (∑ b, |fderiv ℝ g x (e b) - fderiv ℝ g x (e b)|)) := by
      refine tendsto_finsetSum _ fun b _ => ?_
      simp only [sub_apply]
      exact ((hx b).sub_const _).abs
    simpa using hsum

/-- **Integration by parts for the Jacobian minors of a Lipschitz map** (the divergence form of
the minors; cf. J. M. Ball, ARMA 63 (1977)).  Let `v` be `C`-Lipschitz on the open set `Ω`,
`φ ∈ C¹_c(Ω)`, `M = det (∂_{b s} v^{a t})_{t,s}` the `(r+1) × (r+1)` minor with rows `a` and
columns `b`, and `C_q = (-1)^q det (∂_{b (q.succAbove s)} v^{a t.succ})_{t,s}` its cofactors
along the first row.  Then `∫_Ω φ M = -∑_q ∫_Ω v^{a 0} C_q ∂_{b q} φ`.

Extend each coordinate `v^c|_Ω` to a `C`-Lipschitz `ṽ^c` on `ℝ^k` (McShane) and mollify it
(`lipschitz_smooth_approx`): `G^c_m` is `C^∞` and `C`-Lipschitz, `G^c_m → ṽ^c` uniformly and
`DG^c_m → Dṽ^c` a.e.  The identity holds on `ℝ^k` for the rows `G^{a t}_m` (`minor_ibp_smooth`);
the matrix entries are bounded by `C` and converge a.e., and the scalar factors are dominated by
`|φ|` resp. `(|ṽ^{a 0}| + 1) |∂_{b q} φ|` for large `m`, so it passes to the limit
(`mil_tendsto_integral_mul_det`).  Finally `Dṽ^c = proj_c ∘ Dv` a.e. on `Ω`
(`mil_ae_fderiv_eq_proj`), `ṽ^c = v^c` on `Ω`, and every integrand vanishes off
`tsupport φ ⊆ Ω`. -/
theorem Submission.deformation_ipl_mwc_minor_ibp_lipschitz : ∀ (k Q r : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (a : Fin (r + 1) → Fin Q) (b : Fin (r + 1) → Fin k) (v : Eucl k → Eucl Q) (φ : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → ∫ w in Ω, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) => EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k)) = -∑ q : Fin (r + 1), ∫ w in Ω, EuclideanSpace.proj (a 0) (v w) * ((-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ) (fderiv ℝ v w (EuclideanSpace.single (b (q.succAbove s)) 1)))) * fderiv ℝ φ w (EuclideanSpace.single (b q) 1) ∂(volume : Measure (Eucl k)) := by
  intro k Q r Ω C a b v φ hΩ hv hφ hφc hφΩ
  -- Step 1 (McShane): `v^c = proj_c ∘ v` is `C`-Lipschitz on `Ω`, so it extends to a
  -- `C`-Lipschitz `ṽ^c` on `ℝ^k` with `ṽ^c = v^c` on `Ω`.
  have hvc : ∀ c : Fin Q, LipschitzOnWith C (fun w => EuclideanSpace.proj c (v w)) Ω := by
    intro c
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    calc dist (EuclideanSpace.proj c (v x)) (EuclideanSpace.proj c (v y))
          = ‖(v x - v y) c‖ := by simp [dist_eq_norm]
      _ ≤ ‖v x - v y‖ := PiLp.norm_apply_le _ _
      _ = dist (v x) (v y) := (dist_eq_norm _ _).symm
      _ ≤ C * dist x y := hv.dist_le_mul x hx y hy
  choose vt hvtl hvteq using fun c => (hvc c).extend_real
  -- Step 2: `C^∞`, `C`-Lipschitz `G^c_m → ṽ^c` uniformly, with `DG^c_m → Dṽ^c` a.e.
  choose G hGs hGl hGu hGd using fun c =>
    Submission.deformation_ipl_mwc_lipschitz_smooth_approx k C (vt c) (hvtl c)
  -- Step 3: the smooth identity `(S_m)` for the rows `V^m_t = G^{a t}_m`.
  have hS : ∀ m : ℕ, ∫ w, φ w * Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
        fderiv ℝ (G (a t) m) w (EuclideanSpace.single (b s) 1)) =
      -∑ q : Fin (r + 1), ∫ w, G (a 0) m w * ((-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (G (a t.succ) m) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1) := fun m =>
    Submission.deformation_ipl_mwc_minor_ibp_smooth k r (fun t => G (a t) m) b φ
      (fun t => (hGs (a t) m).of_le (WithTop.coe_le_coe.2 le_top)) hφ hφc
  -- Step 4: the entries `∂_i g` of a `C`-Lipschitz `g` are bounded by `C`, and those of `G^c_m`
  -- converge a.e. to those of `ṽ^c`.
  have hent : ∀ g : Eucl k → ℝ, LipschitzWith C g → ∀ (i : Fin k) (w : Eucl k),
      |fderiv ℝ g w (EuclideanSpace.single i 1)| ≤ C := by
    intro g hg i w
    calc |fderiv ℝ g w (EuclideanSpace.single i 1)|
        ≤ ‖fderiv ℝ g w‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          (fderiv ℝ g w).le_opNorm _
      _ ≤ C := by simpa using norm_fderiv_le_of_lipschitz ℝ hg (x₀ := w)
  have hconv : ∀ᵐ w ∂(volume : Measure (Eucl k)), ∀ (c : Fin Q) (i : Fin k),
      Tendsto (fun m => fderiv ℝ (G c m) w (EuclideanSpace.single i 1)) atTop
        (𝓝 (fderiv ℝ (vt c) w (EuclideanSpace.single i 1))) := by
    filter_upwards [ae_all_iff.2 hGd] with w hw c i
    exact ((continuous_id.clm_apply continuous_const).tendsto _).comp (hw c)
  -- Step 5: dominated convergence on both sides of `(S_m)`.
  have hφcont : Continuous φ := hφ.continuous
  have hL := Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det (Eucl k) volume (r + 1)
    C (fun m t s w => fderiv ℝ (G (a t) m) w (EuclideanSpace.single (b s) 1))
    (fun t s w => fderiv ℝ (vt (a t)) w (EuclideanSpace.single (b s) 1)) (fun _ => φ) φ
    (fun w => |φ w|) (fun m t s => (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable)
    (fun _ => hφcont.aestronglyMeasurable) (hφcont.integrable_of_hasCompactSupport hφc).abs
    (fun m t s w => hent _ (hGl _ m) _ w) (Eventually.of_forall fun _ _ => le_rfl)
    (ae_of_all _ fun _ => tendsto_const_nhds) (hconv.mono fun w hw t s => hw _ _)
  have hR : ∀ q : Fin (r + 1), Tendsto (fun m => ∫ w, G (a 0) m w * ((-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (G (a t.succ) m) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1)) atTop
      (𝓝 (∫ w, vt (a 0) w * ((-1 : ℝ) ^ (q : ℕ) *
        Matrix.det (Matrix.of fun t s : Fin r =>
          fderiv ℝ (vt (a t.succ)) w (EuclideanSpace.single (b (q.succAbove s)) 1))) *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1))) := by
    intro q
    have hdφ : Continuous fun w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdφs : HasCompactSupport fun w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1) :=
      hφc.fderiv_apply ℝ _
    -- The majorant `(|ṽ^{a 0}| + 1) |∂_{b q} φ|` is continuous with compact support.
    have hH : Integrable (fun w => (|vt (a 0) w| + 1) *
        |fderiv ℝ φ w (EuclideanSpace.single (b q) 1)|) (volume : Measure (Eucl k)) :=
      (((hvtl (a 0)).continuous.abs.add continuous_const).mul
        hdφ.abs).integrable_of_hasCompactSupport hdφs.abs.mul_left
    -- `|G^{a 0}_m| ≤ |ṽ^{a 0}| + 1` as soon as `sup |G^{a 0}_m − ṽ^{a 0}| < 1`.
    have hbd : ∀ᶠ m in atTop, ∀ w, |(-1 : ℝ) ^ (q : ℕ) * G (a 0) m w *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1)| ≤
        (|vt (a 0) w| + 1) * |fderiv ℝ φ w (EuclideanSpace.single (b q) 1)| := by
      filter_upwards [Metric.tendstoUniformly_iff.1 (hGu (a 0)) 1 one_pos] with m hm w
      have hd := hm w
      rw [Real.dist_eq, abs_sub_comm] at hd
      have h1 : |G (a 0) m w| ≤ |vt (a 0) w| + 1 := by
        linarith [abs_sub_abs_le_abs_sub (G (a 0) m w) (vt (a 0) w)]
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have key := Submission.deformation_ipl_mwc_mil_tendsto_integral_mul_det (Eucl k) volume r C
      (fun m t s w => fderiv ℝ (G (a t.succ) m) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      (fun t s w => fderiv ℝ (vt (a t.succ)) w (EuclideanSpace.single (b (q.succAbove s)) 1))
      (fun m w => (-1 : ℝ) ^ (q : ℕ) * G (a 0) m w *
        fderiv ℝ φ w (EuclideanSpace.single (b q) 1))
      (fun w => (-1 : ℝ) ^ (q : ℕ) * vt (a 0) w * fderiv ℝ φ w (EuclideanSpace.single (b q) 1))
      _ (fun m t s => (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable)
      (fun m => ((continuous_const.mul (hGs (a 0) m).continuous).mul hdφ).aestronglyMeasurable)
      hH (fun m t s w => hent _ (hGl _ m) _ w) hbd
      (ae_of_all _ fun w => (tendsto_const_nhds.mul ((hGu (a 0)).tendsto_at w)).mul
        tendsto_const_nhds)
      (hconv.mono fun w hw t s => hw _ _)
    convert key using 2 with m <;>
      exact integral_congr_ae (Eventually.of_forall fun w => by beta_reduce; ring)
  -- `(S)`: by uniqueness of limits, `(S_m)` passes to the limit `m → ∞`.
  have hlim := tendsto_nhds_unique hL
    (((tendsto_finsetSum _ fun q _ => hR q).neg).congr fun m => (hS m).symm)
  -- Step 6: back to `v` on `Ω`.  For a.e. `w ∈ Ω`, `Dṽ^c(w) = proj_c ∘ Dv(w)`.
  have hae : ∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → ∀ (c : Fin Q) (x : Eucl k),
      fderiv ℝ (vt c) w x = EuclideanSpace.proj c (fderiv ℝ v w x) := by
    filter_upwards [ae_all_iff.2 fun c => Submission.deformation_ipl_mwc_mil_ae_fderiv_eq_proj
      k Q Ω C v c (vt c) hΩ hv (hvteq c).symm] with w hw hwΩ c x
    exact hw c hwΩ x
  -- `φ` and `Dφ` vanish off `tsupport φ ⊆ Ω`, so the integrals over `ℝ^k` are over `Ω`.
  have hφ0 : ∀ w, w ∉ Ω → φ w = 0 := fun w hw =>
    image_eq_zero_of_notMem_tsupport fun h => hw (hφΩ h)
  have hdφ0 : ∀ w, w ∉ Ω → fderiv ℝ φ w = 0 := fun w hw =>
    fderiv_of_notMem_tsupport ℝ fun h => hw (hφΩ h)
  have hΩint : ∀ F F' : Eucl k → ℝ, (∀ w, w ∉ Ω → F' w = 0) →
      (∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → F w = F' w) → ∫ w in Ω, F w = ∫ w, F' w :=
    fun F F' h0 hFF' => (setIntegral_congr_ae hΩ.measurableSet hFF').trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero h0)
  refine (hΩint _ _ (fun w hw => ?_) ?_).trans (hlim.trans ?_)
  · simp [hφ0 w hw]
  · filter_upwards [hae] with w hw hwΩ
    simp only [hw hwΩ]
  · congr 1
    refine Finset.sum_congr rfl fun q _ => (hΩint _ _ (fun w hw => ?_) ?_).symm
    · simp [hdφ0 w hw]
    · filter_upwards [hae] with w hw hwΩ
      have h0 : vt (a 0) w = EuclideanSpace.proj (a 0) (v w) := (hvteq (a 0) hwΩ).symm
      simp only [hw hwΩ, h0]

/-- Smooth test functions suffice (step (3.0) of the proof of `minor_weak_continuity`): if
`Ω ⊆ ℝᵏ` is open, `|f_j|, |f₀| ≤ B` on `Ω` and `∫_Ω φ f_j → ∫_Ω φ f₀` for every `φ ∈ C¹_c(Ω)`, then
`∫_Ω η f_j → ∫_Ω η f₀` for every `η ∈ L¹(Ω)`.  Given `δ > 0`, choose `ε > 0` with
`2 |B| ε ≤ δ / 2` and, by `scalar_smooth_dense`, `φ ∈ C_c^∞(Ω)` with `∫_Ω |η − φ| < ε`.  Then
`|∫_Ω η g − ∫_Ω φ g| ≤ |B| ∫_Ω |η − φ| ≤ |B| ε` for `g = f_j, f₀`, so for large `j`
`|∫_Ω η f_j − ∫_Ω η f₀| ≤ |B| ε + |∫_Ω φ f_j − ∫_Ω φ f₀| + |B| ε < δ`. -/
theorem Submission.deformation_ipl_mwc_test_density : ∀ (k : ℕ) (Ω : Set (Eucl k)) (B : ℝ) (f : ℕ → Eucl k → ℝ) (f₀ : Eucl k → ℝ), IsOpen Ω → (∀ j, AEStronglyMeasurable (f j) ((volume : Measure (Eucl k)).restrict Ω)) → AEStronglyMeasurable f₀ ((volume : Measure (Eucl k)).restrict Ω) → (∀ j, ∀ w ∈ Ω, |f j w| ≤ B) → (∀ w ∈ Ω, |f₀ w| ≤ B) → (∀ φ : Eucl k → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → Tendsto (fun j => ∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k))))) → ∀ η : Eucl k → ℝ, IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k)))) := by
  intro k Ω B f f₀ hΩ hfm hf₀m hfB hf₀B hφ η hη
  -- Step 2: `ζ g ∈ L¹(Ω)` for `ζ ∈ L¹(Ω)` and `g` bounded by `B` (hence by `|B|`) on `Ω`.
  have hint : ∀ ζ g : Eucl k → ℝ, IntegrableOn ζ Ω (volume : Measure (Eucl k)) →
      AEStronglyMeasurable g ((volume : Measure (Eucl k)).restrict Ω) → (∀ w ∈ Ω, |g w| ≤ B) →
      IntegrableOn (fun w => ζ w * g w) Ω (volume : Measure (Eucl k)) := fun ζ g hζ hg hgB =>
    Integrable.mul_bdd hζ hg (ae_restrict_of_forall_mem hΩ.measurableSet fun w hw =>
      (hgB w hw).trans (le_abs_self B))
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Step 3: `ε > 0` with `2 |B| ε ≤ δ / 2` (`|B|` avoids the case split `Ω = ∅`).
  obtain ⟨ε, hε0, hBε⟩ : ∃ ε : ℝ, 0 < ε ∧ |B| * ε ≤ δ / 4 := by
    refine ⟨δ / (4 * (|B| + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg B]
  -- Step 1 (the sibling `scalar_smooth_dense`): `φ ∈ C_c^∞(Ω)` with `∫_Ω |η − φ| < ε`.
  obtain ⟨φ, hφs, hφc, hφΩ, hηφ⟩ :=
    Submission.deformation_ipl_mwc_td_scalar_smooth_dense k Ω η hΩ hη ε hε0
  have hφi : IntegrableOn φ Ω (volume : Measure (Eucl k)) :=
    (hφs.continuous.integrable_of_hasCompactSupport hφc).integrableOn
  -- `|∫_Ω η g − ∫_Ω φ g| ≤ |B| ∫_Ω |η − φ| ≤ |B| ε` for `g` bounded by `B` on `Ω`.
  have happrox : ∀ g : Eucl k → ℝ,
      AEStronglyMeasurable g ((volume : Measure (Eucl k)).restrict Ω) → (∀ w ∈ Ω, |g w| ≤ B) →
      dist (∫ w in Ω, η w * g w ∂(volume : Measure (Eucl k)))
        (∫ w in Ω, φ w * g w ∂(volume : Measure (Eucl k))) ≤ |B| * ε := by
    intro g hg hgB
    rw [dist_eq_norm, ← integral_sub (hint η g hη hg hgB) (hint φ g hφi hg hgB)]
    calc ‖∫ w in Ω, η w * g w - φ w * g w ∂(volume : Measure (Eucl k))‖
        ≤ ∫ w in Ω, |B| * |η w - φ w| ∂(volume : Measure (Eucl k)) := by
          refine norm_integral_le_of_norm_le ((hη.sub hφi).abs.const_mul |B|)
            (ae_restrict_of_forall_mem hΩ.measurableSet fun w hw => ?_)
          rw [← sub_mul, Real.norm_eq_abs, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right ((hgB w hw).trans (le_abs_self B)) (abs_nonneg _)
      _ = |B| * ∫ w in Ω, |η w - φ w| ∂(volume : Measure (Eucl k)) := integral_const_mul _ _
      _ ≤ |B| * ε := mul_le_mul_of_nonneg_left hηφ.le (abs_nonneg B)
  -- The hypothesis for `φ ∈ C¹_c(Ω)`, then the `ε/3` estimate.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (hφ φ (hφs.of_le (WithTop.coe_le_coe.2 le_top)) hφc hφΩ) (δ / 2) (half_pos hδ)
  refine ⟨N, fun j hj => ?_⟩
  have h₁ := happrox (f j) (hfm j) (hfB j)
  have h₂ := hN j hj
  have h₃ := happrox f₀ hf₀m hf₀B
  rw [dist_comm] at h₃
  linarith [dist_triangle4 (∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k)))
    (∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k)))
    (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k)))
    (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k)))]

/-- Weak-* continuity of the Jacobian minors (step 3 of the proof of `minor_weak_continuity`;
J. M. Ball, ARMA 63 (1977); Fonseca–Leoni–Malý, ARMA 178 (2005)).  Let `v_j, v₀` be
`C`-Lipschitz on the open set `Ω` with `v_j → v₀` uniformly on `Ω`, and let
`M_{a,b}(u) = det (⟨e_{a t}, Du (e_{b s})⟩)_{t,s}` be the `r × r` minor with rows `a` and
columns `b`.  Then `∫_Ω η M_{a,b}(v_j) → ∫_Ω η M_{a,b}(v₀)` for every `η ∈ L¹(Ω)`.

Induction on `r`; for `r = 0` both sides equal `∫_Ω η`.  For `r + 1`, `‖Du‖ ≤ C` on `Ω` gives
`|M_{a,b}(u)| ≤ (r+1)! C^{r+1}` there, so by `test_density` it suffices to test against
`φ ∈ C¹_c(Ω)`.  By `minor_ibp_lipschitz`,
`∫_Ω φ M_{a,b}(u) = -∑_q ∫_Ω u^{a 0} (-1)^q M_{a',b^{(q)}}(u) ∂_{b q} φ` with `a' = a ∘ succ`,
`b^{(q)} = b ∘ q.succAbove`.  In each term the part carrying `v_j^{a 0} - v₀^{a 0} → 0`
(uniformly on `Ω`, while `|M_{a',b^{(q)}}| ≤ r! C^r`) tends to `0`, and the induction hypothesis
applies to the rest, tested against `η_q = v₀^{a 0} ∂_{b q} φ ∈ L¹(Ω)`. -/
theorem Submission.deformation_ipl_mwc_minor_weak_star :
    ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q),
      IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω →
      TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k)
      (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) →
      Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k))) atTop
        (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k)))) := by
  intro k Q Ω C v v₀ hΩ hv hv₀ hconv r
  /- Step 0: bounds and measurability.  Leibniz formula: `|det A| ≤ n! c^n` if all
  `|A t s| ≤ c` (`Matrix.det_le` is not imported). -/
  have abs_det_le : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ),
      (∀ t s, |A t s| ≤ c) → |A.det| ≤ (Nat.factorial n : ℝ) * c ^ n := by
    intro n A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), c ^ n := by
          gcongr with σ
          have hσ : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [hσ, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ n := by simp
      _ = (Nat.factorial n : ℝ) * c ^ n := by simp [Fintype.card_perm]
  -- If `u` is `C`-Lipschitz on `Ω`, then `‖Du‖ ≤ C` on `Ω`, so every entry of a minor is
  -- bounded by `C` and `|M_{a,b}(u)| ≤ n! C^n` on `Ω`; every minor is Borel measurable.
  have minor_facts : ∀ {n : ℕ} (a : Fin n → Fin Q) (b : Fin n → Fin k) (u : Eucl k → Eucl Q),
      LipschitzOnWith C u Ω →
      (∀ w ∈ Ω, |Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))| ≤ (Nat.factorial n : ℝ) * (C : ℝ) ^ n) ∧
      Measurable (fun w => Matrix.det (Matrix.of fun t s : Fin n => EuclideanSpace.proj (a t)
          (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))) := by
    intro n a b u hu
    constructor
    · intro w hw
      refine abs_det_le _ C fun t s => ?_
      have hDu : ‖fderiv ℝ u w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hu
      calc |EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1))|
          = ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1) (a t)‖ := by simp [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ u w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖fderiv ℝ u w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ :=
          (fderiv ℝ u w).le_opNorm _
        _ ≤ C := by simpa using hDu
    · have hdet : Continuous fun A : Fin n → Fin n → ℝ => (Matrix.of A).det :=
        Continuous.matrix_det continuous_id
      have hent : ∀ t s : Fin n, Measurable fun w =>
          EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)) := fun t s =>
        (EuclideanSpace.proj (a t)).continuous.measurable.comp
          (measurable_fderiv_apply_const ℝ u _)
      exact hdet.measurable.comp
        (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => hent t s)
  induction r with
  | zero =>
    -- Step 1: a `0 × 0` determinant is `1`, so the sequence is constant.
    intro a b η hη
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro a b η hη
    -- `M u = M_{a,b}(u)`, the `(r + 1) × (r + 1)` minor.
    let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w =>
      Matrix.det (Matrix.of fun t s : Fin (r + 1) =>
        EuclideanSpace.proj (a t) (fderiv ℝ u w (EuclideanSpace.single (b s) 1)))
    -- Step 2: by `test_density` (bound `(r+1)! C^{r+1}`) it suffices to test against
    -- `φ ∈ C¹_c(Ω)`.
    refine Submission.deformation_ipl_mwc_test_density k Ω
      ((Nat.factorial (r + 1) : ℝ) * (C : ℝ) ^ (r + 1)) (fun j => M (v j)) (M v₀) hΩ
      (fun j => (minor_facts a b (v j) (hv j)).2.aestronglyMeasurable)
      (minor_facts a b v₀ hv₀).2.aestronglyMeasurable
      (fun j => (minor_facts a b (v j) (hv j)).1) (minor_facts a b v₀ hv₀).1 ?_ η hη
    intro φ hφ hφc hφΩ
    -- `M' q u = M_{a',b^{(q)}}(u)`, `dφ q = ∂_{b q} φ` and `p u = u^{a 0}`.
    let M' : Fin (r + 1) → (Eucl k → Eucl Q) → Eucl k → ℝ := fun q u w =>
      Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t.succ)
        (fderiv ℝ u w (EuclideanSpace.single (b (q.succAbove s)) 1)))
    let dφ : Fin (r + 1) → Eucl k → ℝ := fun q w => fderiv ℝ φ w (EuclideanSpace.single (b q) 1)
    let p : (Eucl k → Eucl Q) → Eucl k → ℝ := fun u w => EuclideanSpace.proj (a 0) (u w)
    -- Step 3: integration by parts (`minor_ibp_lipschitz`) for `u = v_j` and `u = v₀`.
    have hDu : ∀ u, LipschitzOnWith C u Ω →
        ∫ w in Ω, φ w * M u w ∂(volume : Measure (Eucl k)) =
          -∑ q : Fin (r + 1), ∫ w in Ω, p u w * ((-1 : ℝ) ^ (q : ℕ) * M' q u w) * dφ q w
            ∂(volume : Measure (Eucl k)) := fun u hu =>
      Submission.deformation_ipl_mwc_minor_ibp_lipschitz k Q r Ω C a b u φ hΩ hu hφ hφc hφΩ
    have hfun : (fun j => ∫ w in Ω, φ w * M (v j) w ∂(volume : Measure (Eucl k))) = fun j =>
        -∑ q : Fin (r + 1), ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
          ∂(volume : Measure (Eucl k)) := funext fun j => hDu _ (hv j)
    rw [hfun, hDu v₀ hv₀]
    refine (tendsto_finsetSum _ fun q _ => ?_).neg
    -- `dφ q` is continuous, vanishes off the compact `K = tsupport φ ⊆ Ω` and is integrable.
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
    -- `p u` is bounded on `K` and measurable on `Ω`; `|M' q u| ≤ B' = r! C^r` on `Ω`.
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
      ((EuclideanSpace.proj (a 0)).continuous.comp_continuousOn
        hu.continuousOn).aestronglyMeasurable hΩ.measurableSet
    have hM'b : ∀ u, LipschitzOnWith C u Ω →
        ∀ w ∈ Ω, |M' q u w| ≤ (Nat.factorial r : ℝ) * (C : ℝ) ^ r :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).1
    have hM'm : ∀ u, LipschitzOnWith C u Ω → Measurable (M' q u) :=
      fun u hu => (minor_facts (fun t => a t.succ) (fun s => b (q.succAbove s)) u hu).2
    set B' : ℝ := (Nat.factorial r : ℝ) * (C : ℝ) ^ r with hB'
    have hB'0 : 0 ≤ B' := by positivity
    -- Step 4: anything a.e.-measurable on `Ω` and bounded by `c |dφ q|` there is integrable.
    have hint : ∀ (F : Eucl k → ℝ) (c : ℝ),
        AEStronglyMeasurable F ((volume : Measure (Eucl k)).restrict Ω) →
        (∀ w ∈ Ω, |F w| ≤ c * |dφ q w|) → IntegrableOn F Ω (volume : Measure (Eucl k)) := by
      intro F c hFm hFb
      refine Integrable.mono' ((hdφint.abs.const_mul c).integrableOn) hFm ?_
      exact (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
        simpa [Real.norm_eq_abs] using hFb w hw)
    let ηq : Eucl k → ℝ := fun w => p v₀ w * dφ q w
    obtain ⟨P0, hP00, hP0⟩ := hpbd v₀ hv₀
    have hηq : IntegrableOn ηq Ω (volume : Measure (Eucl k)) := by
      refine hint ηq P0 ((hpm v₀ hv₀).mul hdφc.aestronglyMeasurable.restrict) fun w hw => ?_
      by_cases hwK : w ∈ K
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hP0 w hwK) (abs_nonneg _)
      · simp [ηq, hdφ0 w hwK]
    have hI1 : ∀ j, IntegrableOn (fun w => (p (v j) w - p v₀ w) *
        ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w) Ω (volume : Measure (Eucl k)) := by
      intro j
      obtain ⟨Pj, hPj0, hPj⟩ := hpbd (v j) (hv j)
      refine hint _ ((Pj + P0) * B') ((((hpm _ (hv j)).sub (hpm _ hv₀)).mul
        ((hM'm _ (hv j)).aestronglyMeasurable.const_mul _)).mul
          hdφc.aestronglyMeasurable.restrict) ?_
      intro w hw
      by_cases hwK : w ∈ K
      · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        gcongr
        · exact (abs_sub _ _).trans (add_le_add (hPj w hwK) (hP0 w hwK))
        · exact hM'b _ (hv j) w hw
      · simp [hdφ0 w hwK]
    have hI2 : ∀ u, LipschitzOnWith C u Ω →
        IntegrableOn (fun w => ηq w * M' q u w) Ω (volume : Measure (Eucl k)) := by
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
    -- Step 5: `I_j = ∫_Ω (v_j^{a 0} - v₀^{a 0}) (-1)^q M'_j dφ + (-1)^q ∫_Ω η_q M'_j`.
    have hsplit : ∀ j, ∫ w in Ω, p (v j) w * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
        ∂(volume : Measure (Eucl k)) =
        (∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
          ∂(volume : Measure (Eucl k))) +
          (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q (v j) w ∂(volume : Measure (Eucl k)) := by
      intro j
      rw [← integral_const_mul, ← integral_add (hI1 j) ((hI2 _ (hv j)).const_mul _)]
      congr 1; funext w; simp only [ηq]; ring
    have hlim : ∫ w in Ω, p v₀ w * ((-1 : ℝ) ^ (q : ℕ) * M' q v₀ w) * dφ q w
        ∂(volume : Measure (Eucl k)) =
        0 + (-1 : ℝ) ^ (q : ℕ) * ∫ w in Ω, ηq w * M' q v₀ w ∂(volume : Measure (Eucl k)) := by
      rw [zero_add, ← integral_const_mul]
      congr 1; funext w; simp only [ηq]; ring
    -- Step 6: the first term tends to `0`, as `p (v j) → p v₀` uniformly on `Ω`.
    have h1 : Tendsto (fun j => ∫ w in Ω, (p (v j) w - p v₀ w) *
        ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w ∂(volume : Measure (Eucl k))) atTop
        (𝓝 0) := by
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
          ‖(p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w‖ ≤
            δ * B' * |dφ q w| := by
        refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
        have e1 : |p (v j) w - p v₀ w| ≤ δ := by
          have h' := (hN j hj w hw).le
          rw [dist_comm, dist_eq_norm] at h'
          calc |p (v j) w - p v₀ w| = |EuclideanSpace.proj (a 0) (v j w - v₀ w)| := by
                simp [p]
            _ = ‖(v j w - v₀ w) (a 0)‖ := by simp [Real.norm_eq_abs]
            _ ≤ ‖v j w - v₀ w‖ := PiLp.norm_apply_le _ _
            _ ≤ δ := h'
        have e2 := hM'b _ (hv j) w hw
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
          one_mul]
        gcongr
      calc ‖∫ w in Ω, (p (v j) w - p v₀ w) * ((-1 : ℝ) ^ (q : ℕ) * M' q (v j) w) * dφ q w
            ∂(volume : Measure (Eucl k))‖
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
    -- Steps 7–8: the induction hypothesis, tested against `η_q ∈ L¹(Ω)`, handles the second
    -- term; multiplying by `(-1)^q` and adding the first term gives `I_j → I_0`.
    have hih := ih (fun t => a t.succ) (fun s => b (q.succAbove s)) ηq hηq
    rw [hlim]
    exact (h1.add (hih.const_mul _)).congr fun j => (hsplit j).symm

/-- Weak continuity of the Jacobian minors `M_{a,b}(u) = det (⟨e_{a t}, Du (e_{b s})⟩)_{t,s}`
against a coefficient `ψ (g ∘ u)`, `ψ ∈ L¹(Ω)`, `g ∈ C_c(ℝ^Q)` (step 2 of the proof of
`minor_weak_continuity`).  With `η = ψ (g ∘ u₀) ∈ L¹(Ω)`,
`∫_Ω ψ (g ∘ u_j) M_{a,b}(u_j) = ∫_Ω ψ (g ∘ u_j - g ∘ u₀) M_{a,b}(u_j) + ∫_Ω η M_{a,b}(u_j)`; the
first term tends to `0` because `|M_{a,b}(u_j)| ≤ r! C^r` on `Ω` and `g ∘ u_j → g ∘ u₀`
uniformly on `Ω`, the second tends to `∫_Ω η M_{a,b}(u₀)` by `minor_weak_star`. -/
theorem Submission.deformation_ipl_mwc_coeff_minor_continuity :
    ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (ψ : Eucl k → ℝ) (g : Eucl Q → ℝ) (C : ℝ≥0)
      (u : ℕ → Eucl k → Eucl Q) (u₀ : Eucl k → Eucl Q) (r : ℕ) (a : Fin r → Fin Q)
      (b : Fin r → Fin k), IsOpen Ω → IntegrableOn ψ Ω (volume : Measure (Eucl k)) →
      Continuous g → HasCompactSupport g → (∀ j, LipschitzOnWith C (u j) Ω) →
      LipschitzOnWith C u₀ Ω → TendstoUniformlyOn u u₀ atTop Ω →
      Tendsto (fun j => ∫ w in Ω, ψ w * g (u j w) * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ (u j) w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k))) atTop
        (𝓝 (∫ w in Ω, ψ w * g (u₀ w) * Matrix.det (Matrix.of fun t s : Fin r =>
          EuclideanSpace.proj (a t) (fderiv ℝ u₀ w (EuclideanSpace.single (b s) 1)))
            ∂(volume : Measure (Eucl k)))) := by
  intro k Q Ω ψ g C u u₀ r a b hΩ hψ hg hgc hu hu₀ hconv
  -- `M v w = M_{a,b}(v)(w)`, the `(a, b)` minor of `Dv(w)`.
  let M : (Eucl k → Eucl Q) → Eucl k → ℝ := fun v w => Matrix.det (Matrix.of fun t s : Fin r =>
    EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1)))
  /- Step 1: bounds and measurability.  Leibniz formula: `|det A| ≤ r! c^r` if all
  `|A t s| ≤ c` (`Matrix.det_le` is not imported). -/
  have abs_det_le : ∀ (A : Matrix (Fin r) (Fin r) ℝ) (c : ℝ), (∀ t s, |A t s| ≤ c) →
      |A.det| ≤ (Nat.factorial r : ℝ) * c ^ r := by
    intro A c hA
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ • ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin r), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), c ^ r := by
          gcongr with σ
          have hσ : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [hσ, Finset.abs_prod]
          calc ∏ i, |A (σ i) i| ≤ ∏ _i : Fin r, c := by
                gcongr with i
                exact hA _ _
            _ = c ^ r := by simp
      _ = (Nat.factorial r : ℝ) * c ^ r := by simp [Fintype.card_perm]
  -- On `Ω`, `‖Dv‖ ≤ C` for `v` `C`-Lipschitz on `Ω`, so every entry of the minor is `≤ C`.
  obtain ⟨B, hB0, hMb⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ v, LipschitzOnWith C v Ω → ∀ w ∈ Ω, |M v w| ≤ B := by
    refine ⟨(Nat.factorial r : ℝ) * (C : ℝ) ^ r, by positivity, fun v hv w hw => ?_⟩
    refine abs_det_le _ C fun t s => ?_
    have hD : ‖fderiv ℝ v w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hv
    calc |EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1))|
        = ‖fderiv ℝ v w (EuclideanSpace.single (b s) 1) (a t)‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ v w (EuclideanSpace.single (b s) 1)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ v w‖ * ‖EuclideanSpace.single (b s) (1 : ℝ)‖ := (fderiv ℝ v w).le_opNorm _
      _ ≤ C := by simpa using hD
  have hMm : ∀ v, Measurable (M v) := by
    intro v
    have hdet : Continuous fun A : Fin r → Fin r → ℝ => (Matrix.of A).det :=
      Continuous.matrix_det continuous_id
    have hent : ∀ t s : Fin r, Measurable fun w =>
        EuclideanSpace.proj (a t) (fderiv ℝ v w (EuclideanSpace.single (b s) 1)) := fun t s =>
      (EuclideanSpace.proj (a t)).continuous.measurable.comp (measurable_fderiv_apply_const ℝ v _)
    exact hdet.measurable.comp (measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun s => hent t s)
  have hMbd : ∀ j, ∀ᵐ w ∂(volume : Measure (Eucl k)).restrict Ω, ‖M (u j) w‖ ≤ B := fun j =>
    (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => by
      simpa [Real.norm_eq_abs] using hMb _ (hu j) w hw)
  obtain ⟨G, hG⟩ := hg.bounded_above_of_compact_support hgc
  have hgm : ∀ v, LipschitzOnWith C v Ω →
      AEStronglyMeasurable (fun w => g (v w)) ((volume : Measure (Eucl k)).restrict Ω) :=
    fun v hv => (hg.comp_continuousOn hv.continuousOn).aestronglyMeasurable hΩ.measurableSet
  -- Step 2: integrability.
  let η : Eucl k → ℝ := fun w => ψ w * g (u₀ w)
  have hη : IntegrableOn η Ω (volume : Measure (Eucl k)) :=
    Integrable.mul_bdd hψ (hgm u₀ hu₀) (ae_of_all _ fun w => hG _)
  have hint₁ : ∀ j, IntegrableOn (fun w => ψ w * (g (u j w) - g (u₀ w)) * M (u j) w) Ω
      (volume : Measure (Eucl k)) := fun j =>
    Integrable.mul_bdd (Integrable.mul_bdd (c := G + G) hψ ((hgm _ (hu j)).sub (hgm _ hu₀))
      (ae_of_all _ fun w => (norm_sub_le _ _).trans (add_le_add (hG _) (hG _))))
      (hMm _).aestronglyMeasurable (hMbd j)
  have hint₂ : ∀ j, IntegrableOn (fun w => η w * M (u j) w) Ω (volume : Measure (Eucl k)) :=
    fun j => Integrable.mul_bdd hη (hMm _).aestronglyMeasurable (hMbd j)
  -- Step 3: `∫_Ω ψ (g ∘ u_j) M_j = D₁(j) + ∫_Ω η M_j`.
  have hsplit : ∀ j, ∫ w in Ω, ψ w * g (u j w) * M (u j) w ∂(volume : Measure (Eucl k)) =
      (∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w ∂(volume : Measure (Eucl k))) +
        ∫ w in Ω, η w * M (u j) w ∂(volume : Measure (Eucl k)) := by
    intro j
    rw [← integral_add (hint₁ j) (hint₂ j)]
    congr 1
    funext w
    simp only [η]
    ring
  -- Step 4: `D₁(j) → 0`, as `g ∘ u_j → g ∘ u₀` uniformly on `Ω` and `|M_j| ≤ B` there.
  have hunif : TendstoUniformlyOn (fun j w => g (u j w)) (fun w => g (u₀ w)) atTop Ω :=
    (hgc.uniformContinuous_of_continuous hg).comp_tendstoUniformlyOn hconv
  obtain ⟨I, hI0, hI⟩ : ∃ I : ℝ, 0 ≤ I ∧ ∫ w in Ω, |ψ w| ∂(volume : Measure (Eucl k)) = I :=
    ⟨_, integral_nonneg fun w => abs_nonneg _, rfl⟩
  have hD₁ : Tendsto (fun j => ∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w
      ∂(volume : Measure (Eucl k))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hBI : 0 < B * I + 1 := by positivity
    obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * (B * I + 1) = ε :=
      ⟨ε / (B * I + 1), div_pos hε hBI, div_mul_cancel₀ ε hBI.ne'⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif δ hδ0)
    refine ⟨N, fun j hj => ?_⟩
    have hbound : ∀ᵐ w ∂(volume : Measure (Eucl k)).restrict Ω,
        ‖ψ w * (g (u j w) - g (u₀ w)) * M (u j) w‖ ≤ δ * B * |ψ w| := by
      refine (ae_restrict_iff' hΩ.measurableSet).2 (ae_of_all _ fun w hw => ?_)
      have e₁ : |g (u j w) - g (u₀ w)| ≤ δ := by
        rw [← Real.dist_eq, dist_comm]
        exact (hN j hj w hw).le
      have e₂ := hMb _ (hu j) w hw
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |ψ w| * |g (u j w) - g (u₀ w)| * |M (u j) w| ≤ |ψ w| * δ * B := by gcongr
        _ = δ * B * |ψ w| := by ring
    rw [dist_zero_right]
    calc ‖∫ w in Ω, ψ w * (g (u j w) - g (u₀ w)) * M (u j) w ∂(volume : Measure (Eucl k))‖
        ≤ ∫ w in Ω, δ * B * |ψ w| ∂(volume : Measure (Eucl k)) :=
          norm_integral_le_of_norm_le (hψ.abs.const_mul _) hbound
      _ = δ * (B * I) := by rw [integral_const_mul, hI]; ring
      _ < δ * (B * I + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ0
      _ = ε := hδε
  -- Step 5: the sibling `minor_weak_star` tested against `η ∈ L¹(Ω)`.
  have hη₂ :=
    Submission.deformation_ipl_mwc_minor_weak_star k Q Ω C u u₀ hΩ hu hu₀ hconv r a b η hη
  -- Step 6: conclusion.
  have hlim := hD₁.add hη₂
  rw [zero_add] at hlim
  exact hlim.congr fun j => (hsplit j).symm

/-- **Weak continuity of `ψ · α(u)(∂₀u, …, ∂_{k−1}u)`** (weak continuity of Jacobian minors;
used for Lipschitz push-forwards as limits of C¹ push-forwards in the proof of Simon Ch. 6, 5.1,
remark after (21)).  By the covector expansion and `wedgeCovectors_apply_det`,
`α(y)(∂₀u, …, ∂_{k−1}u) = ∑_γ α_γ(y) M_γ(Du)` with `α_γ = euclideanCovectorCoordinate (α ·) γ`
and `M_γ(Du) = det(∂_s u^{γ t})`.  Each summand `ψ (α_γ ∘ u) M_γ(Du)` is integrable on `Ω`:
`α_γ` is continuous with compact support, and `‖Du‖ ≤ C` on the open set `Ω` gives
`|M_γ(Du)| = |dy^γ(Du e₀, …, Du e_{k−1})| ≤ ‖dy^γ‖ Cᵏ` there.  Each summand converges by
`deformation_ipl_mwc_coeff_minor_continuity` with `g = α_γ`, `r = k`, `a = γ`, `b = id`. -/
theorem Submission.deformation_ipl_minor_weak_continuity : ∀ (k Q : ℕ) (Ω : Set (Eucl k)) (ψ : Eucl k → ℝ) (α : Eucl Q → Covector (Eucl Q) k) (C : ℝ≥0) (u : ℕ → Eucl k → Eucl Q) (u₀ : Eucl k → Eucl Q), IsOpen Ω → IntegrableOn ψ Ω (volume : Measure (Eucl k)) → Continuous α → HasCompactSupport α → (∀ j, LipschitzOnWith C (u j) Ω) → LipschitzOnWith C u₀ Ω → TendstoUniformlyOn u u₀ atTop Ω → Tendsto (fun j => ∫ w in Ω, ψ w * α (u j w) (fun b => fderiv ℝ (u j) w (EuclideanSpace.single b 1)) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, ψ w * α (u₀ w) (fun b => fderiv ℝ u₀ w (EuclideanSpace.single b 1)) ∂(volume : Measure (Eucl k)))) := by
  intro k Q Ω ψ α C u u₀ hΩ hψ hαc hαs hu hu₀ hlim
  -- Coordinate expansion: `α(y)(x) = ∑_γ α_γ(y) det(x_s^{γ t})`.
  have hexp : ∀ (y : Eucl Q) (x : Fin k → Eucl Q), α y x = ∑ γ : SimonMultiIndex k Q,
      euclideanCovectorCoordinate (α y) γ *
        Matrix.det (Matrix.of fun t s : Fin k => EuclideanSpace.proj (γ t) (x s)) := by
    intro y x
    conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge Q k (α y)]
    rw [ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_det, smul_eq_mul]
  -- The coefficients `α_γ` are continuous with compact support.
  have hgc : ∀ γ : SimonMultiIndex k Q, Continuous fun y => euclideanCovectorCoordinate (α y) γ :=
    fun γ => hαc.eval_const _
  have hgs : ∀ γ : SimonMultiIndex k Q,
      HasCompactSupport fun y => euclideanCovectorCoordinate (α y) γ := by
    intro γ
    refine hαs.mono fun y hy => ?_
    rw [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    simp [euclideanCovectorCoordinate, h0]
  -- The minors of a map `C`-Lipschitz on `Ω` are measurable, and bounded on `Ω` by
  -- `‖dy^γ‖ Cᵏ` since `‖Dv‖ ≤ C` on the open set `Ω`.
  have hminor : ∀ v : Eucl k → Eucl Q, LipschitzOnWith C v Ω → ∀ γ : SimonMultiIndex k Q,
      AEStronglyMeasurable (fun w => Matrix.det (Matrix.of fun t s : Fin k =>
          EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1))))
          ((volume : Measure (Eucl k)).restrict Ω) ∧
        ∀ w ∈ Ω, ‖Matrix.det (Matrix.of fun t s : Fin k =>
            EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1)))‖ ≤
          ‖wedgeCovectors k (fun t => EuclideanSpace.proj (γ t))‖ * (C : ℝ) ^ k := by
    intro v hv γ
    set ω : Covector (Eucl Q) k := wedgeCovectors k (fun t => EuclideanSpace.proj (γ t)) with hω
    -- `M_γ(v)(w) = dy^γ(Dv(w) e₀, …, Dv(w) e_{k−1})`.
    have hM : ∀ w, Matrix.det (Matrix.of fun t s : Fin k =>
        EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1))) =
          ω (fun s => fderiv ℝ v w (EuclideanSpace.single s 1)) := by
      intro w
      rw [hω, wedgeCovectors_apply_det]
    simp only [hM]
    refine ⟨?_, fun w hw => ?_⟩
    · have hcont : Continuous fun L : Eucl k →L[ℝ] Eucl Q =>
          ω (fun s => L (EuclideanSpace.single s 1)) :=
        ω.coe_continuous.comp (continuous_pi fun s => continuous_id.clm_apply continuous_const)
      exact (hcont.measurable.comp (measurable_fderiv ℝ v)).aestronglyMeasurable
    · have hD : ‖fderiv ℝ v w‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) hv
      calc ‖ω (fun s => fderiv ℝ v w (EuclideanSpace.single s 1))‖
          ≤ ‖ω‖ * ∏ s, ‖fderiv ℝ v w (EuclideanSpace.single s 1)‖ := ω.le_opNorm _
        _ ≤ ‖ω‖ * ∏ _s : Fin k, (C : ℝ) := by
            gcongr with s
            calc ‖fderiv ℝ v w (EuclideanSpace.single s 1)‖
                ≤ ‖fderiv ℝ v w‖ * ‖(EuclideanSpace.single s (1 : ℝ) : Eucl k)‖ :=
                  (fderiv ℝ v w).le_opNorm _
              _ = ‖fderiv ℝ v w‖ := by simp
              _ ≤ C := hD
        _ = ‖ω‖ * (C : ℝ) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Each summand `ψ (α_γ ∘ v) M_γ(v)` is integrable on `Ω`.
  have hint : ∀ v : Eucl k → Eucl Q, LipschitzOnWith C v Ω → ∀ γ : SimonMultiIndex k Q,
      IntegrableOn (fun w => ψ w * euclideanCovectorCoordinate (α (v w)) γ *
        Matrix.det (Matrix.of fun t s : Fin k =>
          EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1))))
        Ω (volume : Measure (Eucl k)) := by
    intro v hv γ
    obtain ⟨B, hB⟩ := (hgc γ).bounded_above_of_compact_support (hgs γ)
    obtain ⟨hmeas, hbd⟩ := hminor v hv γ
    have hgm : AEStronglyMeasurable (fun w => euclideanCovectorCoordinate (α (v w)) γ)
        ((volume : Measure (Eucl k)).restrict Ω) :=
      ((hgc γ).comp_continuousOn hv.continuousOn).aestronglyMeasurable hΩ.measurableSet
    have hm : AEStronglyMeasurable (fun w => euclideanCovectorCoordinate (α (v w)) γ *
        Matrix.det (Matrix.of fun t s : Fin k =>
          EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1))))
        ((volume : Measure (Eucl k)).restrict Ω) := hgm.mul hmeas
    have hb : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict Ω),
        ‖euclideanCovectorCoordinate (α (v w)) γ * Matrix.det (Matrix.of fun t s : Fin k =>
          EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1)))‖ ≤
          B * (‖wedgeCovectors k (fun t => EuclideanSpace.proj (γ t))‖ * (C : ℝ) ^ k) := by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with w hw
      rw [norm_mul]
      exact mul_le_mul (hB _) (hbd w hw) (norm_nonneg _) ((norm_nonneg _).trans (hB (v w)))
    exact (Integrable.mul_bdd hψ hm hb).congr
      (Eventually.of_forall fun w => (mul_assoc _ _ _).symm)
  -- Both integrals are finite sums over `γ` of such summands.
  have hrw : ∀ v : Eucl k → Eucl Q, LipschitzOnWith C v Ω →
      ∫ w in Ω, ψ w * α (v w) (fun b => fderiv ℝ v w (EuclideanSpace.single b 1))
          ∂(volume : Measure (Eucl k)) =
        ∑ γ : SimonMultiIndex k Q, ∫ w in Ω, ψ w * euclideanCovectorCoordinate (α (v w)) γ *
          Matrix.det (Matrix.of fun t s : Fin k =>
            EuclideanSpace.proj (γ t) (fderiv ℝ v w (EuclideanSpace.single s 1)))
          ∂(volume : Measure (Eucl k)) := by
    intro v hv
    rw [← integral_finsetSum _ fun γ _ => hint v hv γ]
    congr 1
    funext w
    rw [hexp (v w), Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => (mul_assoc _ _ _).symm
  rw [hrw u₀ hu₀]
  refine Tendsto.congr (fun j => (hrw (u j) (hu j)).symm) ?_
  -- Each summand converges: coefficient–minor continuity with `r = k`, `a = γ`, `b = id`.
  exact tendsto_finsetSum _ fun γ _ =>
    Submission.deformation_ipl_mwc_coeff_minor_continuity k Q Ω ψ
      (fun y => euclideanCovectorCoordinate (α y) γ) C u u₀ k γ (fun s => s)
      hΩ hψ (hgc γ) (hgs γ) hu hu₀ hlim

/-- Measurability of the push-forward `k`-vector field (Simon Ch. 6, (3.6), p. 147, as needed in
the proof of the Deformation Theorem, §5, p. 166): for a rectifiable triple `(M, θ, ξ)` in an open
`U`, a locally Lipschitz `f` and any `L` with `L(x)v = d/dt f(x + tv)|₀` on the weighted
approximate tangent spaces `TₓM`, `x ↦ L(x)_# ξ(x)` is `Hᵏ⌞M`-a.e. strongly measurable.  Off an
`Hᵏ`-null set, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₖ` with `span τ = TₓM = DΦ_j(w)(ℝᵏ)` for a `C¹` chart
`Φ_j(w) = x` (uniqueness of `TₓM`, `θ x > 0`), so `L x` agrees on `τ` with the Borel chartwise
differential `L'` of `lpf_tde_measurable_chart_differential`. -/
theorem Submission.deformation_ipl_tangential_pushforward_aestronglyMeasurable : ∀ (P Q k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U k M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → AEStronglyMeasurable (fun x => nVectorPushforward k (L x) (ξ x)) ((μHE[k] : Measure (Eucl P)).restrict M) := by
  intro P Q k U M θ ξ f L hU hT hf hL
  -- Step 1: `C¹` charts `Φ j`, Lipschitz and antilipschitz on open `Ω j`, cover `M` up to an
  -- `Hᵏ`-null set.
  obtain ⟨Φ, Ω, hΩ, hΦ, hLip, hanti, hcover⟩ :=
    Submission.lpf_countably_rectifiable_c1_cover P k M hT.countablyRectifiable
  -- Step 2: a strongly measurable `L'` with `L'(x) ∘ DΦ_j(w) = D(f ∘ Φ_j)(w)` at a chart
  -- preimage `w` of every covered point `x`.
  obtain ⟨L', hL'm, -, hL'⟩ :=
    Submission.lpf_tde_measurable_chart_differential P Q k Φ Ω f hΩ hΦ hanti
  -- Step 3: on each chart, the tangent identification and the chain rule hold off an `Lᵏ`-null
  -- set `E j ⊆ Ω j` of parameters.
  have hgood : ∀ j, ∃ E : Set (Eucl k), E ⊆ Ω j ∧ (volume : Measure (Eucl k)) E = 0 ∧
      ∀ w ∈ Ω j, Φ j w ∈ M → w ∉ E →
        HasWeightedApproximateTangentSpaceAt k M θ (Φ j w)
            (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
          HasFDerivAt (f ∘ Φ j) ((L (Φ j w)).comp (fderiv ℝ (Φ j) w)) w := by
    intro j
    have h := Submission.lpf_chart_chain_rule P Q k U M θ ξ f L (Φ j) (Ω j) hU hT hf hL (hΩ j)
      (hΦ j) (hanti j)
    refine ⟨{w | ¬ (HasWeightedApproximateTangentSpaceAt k M θ (Φ j w)
        (LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap) ∧
          HasFDerivAt (f ∘ Φ j) ((L (Φ j w)).comp (fderiv ℝ (Φ j) w)) w)} ∩ (Ω j ∩ Φ j ⁻¹' M),
      fun w hw => hw.2.1,
      nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans_eq (ae_iff.1 h)), ?_⟩
    intro w hw hwM hwE
    by_contra hcon
    exact hwE ⟨hcon, hw, hwM⟩
  choose E hEΩ hE0 hEgood using hgood
  -- Step 4: `Φ j (E j)` is `Hᵏ`-null, as `Φ j` is Lipschitz on `E j ⊆ Ω j` and `Hᵏ = Lᵏ` on `ℝᵏ`.
  have hΦE : ∀ j, (μHE[k] : Measure (Eucl P)) (Φ j '' E j) = 0 := by
    intro j
    obtain ⟨K, hK⟩ := hLip j
    refine nonpos_iff_eq_zero.1
      ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
        (hK.mono (hEΩ j))).trans ?_)
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hE0 j, mul_zero]
  have hcov : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), x ∈ ⋃ j, Φ j '' Ω j := by
    rw [ae_iff, Measure.restrict_apply₀' hT.nullMeasurableSet]
    refine measure_mono_null ?_ hcover
    intro x hx
    exact ⟨hx.2, hx.1⟩
  have hnot : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ j, x ∉ Φ j '' E j :=
    ae_all_iff.2 fun j => ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hΦE j))
  -- Step 5: off an `Hᵏ`-null set, `ξ x = ±τ₁ ∧ ⋯ ∧ τₖ` with `span τ = DΦ_j(w)(ℝᵏ)` (uniqueness of
  -- weighted approximate tangent spaces, `θ x > 0`), so `L' x ∘ τ = L x ∘ τ`.
  have heq : (fun x => nVectorPushforward k (L' x) (ξ x)) =ᵐ[(μHE[k] : Measure (Eucl P)).restrict M]
      fun x => nVectorPushforward k (L x) (ξ x) := by
    filter_upwards [ae_restrict_mem₀ hT.nullMeasurableSet, hcov, hnot, hT.orients]
      with x hxM hxc hxE hor
    obtain ⟨τ, -, hτ, hξ⟩ := hor
    obtain ⟨j, w, hw, hΦw, hA, -⟩ := hL' x hxc
    have hwM : Φ j w ∈ M := by rw [hΦw]; exact hxM
    have hwE : w ∉ E j := fun hwE => hxE j ⟨w, hwE, hΦw⟩
    obtain ⟨hW, hD⟩ := hEgood j w hw hwM hwE
    rw [hΦw] at hW hD
    have hspan := HasWeightedApproximateTangentSpaceAt.unique (hT.pos x hxM).ne' hτ hW
    have hcomp : L' x ∘ τ = L x ∘ τ := by
      funext a
      obtain ⟨s, hs⟩ : τ a ∈ LinearMap.range (fderiv ℝ (Φ j) w).toLinearMap :=
        hspan ▸ Submodule.subset_span (mem_range_self a)
      have hs' : fderiv ℝ (Φ j) w s = τ a := hs
      rw [Function.comp_apply, Function.comp_apply, ← hs', hA s, hD.fderiv,
        ContinuousLinearMap.comp_apply]
    rcases hξ with hξ | hξ
    · rw [hξ, nVectorPushforward_simple, nVectorPushforward_simple, hcomp]
    · ext ω
      simp only [nVectorPushforward, hξ, ContinuousLinearMap.comp_apply,
        neg_apply, simpleNVector_apply, covectorPullback_apply, hcomp]
  -- Step 6: `(A, w) ↦ A_# w = w ∘ A^#` is continuous, so `x ↦ L'(x)_# ξ(x)` is `Hᵏ⌞M`-a.e.
  -- strongly measurable, and it agrees a.e. with `x ↦ L(x)_# ξ(x)`.
  have hcont : Continuous fun p : (Eucl P →L[ℝ] Eucl Q) × NVector (Eucl P) k =>
      nVectorPushforward k p.1 p.2 :=
    continuous_snd.clm_comp
      (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp continuous_fst)
  exact (hcont.comp_aestronglyMeasurable
    (hL'm.aestronglyMeasurable.prodMk hT.aestronglyMeasurable)).congr heq

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
