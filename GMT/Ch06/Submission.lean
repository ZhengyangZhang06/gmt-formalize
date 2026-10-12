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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
