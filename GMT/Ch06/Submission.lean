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
