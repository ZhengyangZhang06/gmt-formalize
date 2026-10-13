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

/-- Gram-determinant lower bound (the Jacobian bound of step 6a): if `0 ≤ c` and `c‖s‖ ≤ ‖T s‖`
for all `s ∈ ℝᵏ`, then `cᵏ ≤ √det (⟪T eᵢ, T eⱼ⟫)ᵢⱼ`.  The Gram matrix is the matrix of the
symmetric operator `S = T† T` in the standard basis; on an orthonormal eigenbasis `uᵢ` of `S` the
eigenvalues are `⟪S uᵢ, uᵢ⟫ = ‖T uᵢ‖² ≥ c²`, and `det S` is their product. -/
theorem Submission.deformation_ipl_cc_gram_det_lower_bound : ∀ (P k : ℕ) (T : Eucl k →L[ℝ] Eucl P) (c : ℝ), 0 ≤ c → (∀ s : Eucl k, c * ‖s‖ ≤ ‖T s‖) → c ^ k ≤ Real.sqrt (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1))).det := by
  intro P k T c hc hT
  -- `S = T† T` on `ℝᵏ`, with `⟪S x, y⟫ = ⟪T x, T y⟫`
  set S : Eucl k →ₗ[ℝ] Eucl k :=
    ((ContinuousLinearMap.adjoint T).comp T : Eucl k →L[ℝ] Eucl k).toLinearMap with hS
  have hSin : ∀ x y : Eucl k, inner ℝ (S x) y = inner ℝ (T x) (T y) := by
    intro x y
    simp only [hS, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_left T y (T x)
  -- Step 1: `S` is symmetric
  have hsymm : S.IsSymmetric := by
    intro x y
    rw [hSin, real_inner_comm (S y) x, hSin, real_inner_comm]
  have hn : Module.finrank ℝ (Eucl k) = k := finrank_euclideanSpace_fin
  -- Step 2: the Gram matrix is the matrix of `S` in the standard basis, so `det G = det S`
  have hmat : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis S = Matrix.of fun i j =>
        inner ℝ (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, Matrix.of_apply, ← hSin,
      hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      EuclideanSpace.inner_single_left]
    simp
  have hdet : (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1))
      (T (EuclideanSpace.single j 1))).det = LinearMap.det S := by
    rw [← hmat, LinearMap.det_toMatrix]
  -- Step 3: every eigenvalue `λᵢ = ⟪S uᵢ, uᵢ⟫ = ‖T uᵢ‖²` is at least `c²`
  have heig : ∀ i, c ^ 2 ≤ hsymm.eigenvalues hn i := by
    intro i
    have hun : ‖hsymm.eigenvectorBasis hn i‖ = 1 := (hsymm.eigenvectorBasis hn).orthonormal.1 i
    have h1 := hSin (hsymm.eigenvectorBasis hn i) (hsymm.eigenvectorBasis hn i)
    rw [hsymm.apply_eigenvectorBasis hn i, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hun] at h1
    have h2 := hT (hsymm.eigenvectorBasis hn i)
    rw [hun, mul_one] at h2
    have h3 : hsymm.eigenvalues hn i = ‖T (hsymm.eigenvectorBasis hn i)‖ ^ 2 := by
      simpa using h1
    rw [h3]
    nlinarith [norm_nonneg (T (hsymm.eigenvectorBasis hn i))]
  -- Step 4: `det G = ∏ λᵢ ≥ (c²)ᵏ`
  have hprod : (c ^ 2) ^ k ≤ (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1))
      (T (EuclideanSpace.single j 1))).det := by
    rw [hdet, hsymm.det_eq_prod_eigenvalues hn]
    calc (c ^ 2) ^ k = ∏ _i : Fin k, c ^ 2 := by simp
      _ ≤ ∏ i, hsymm.eigenvalues hn i :=
          Finset.prod_le_prod₀ (fun _ _ => sq_nonneg c) (fun i _ => heig i)
  -- Step 5: `cᵏ = √((c²)ᵏ) ≤ √det G`
  calc c ^ k = Real.sqrt ((c ^ k) ^ 2) := (Real.sqrt_sq (pow_nonneg hc k)).symm
    _ = Real.sqrt ((c ^ 2) ^ k) := by ring_nf
    _ ≤ _ := Real.sqrt_le_sqrt hprod
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
/-- Gram-determinant lower bound (the Jacobian bound of step 6a): if `0 ≤ c` and `c‖s‖ ≤ ‖T s‖`
for all `s ∈ ℝᵏ`, then `cᵏ ≤ √det (⟪T eᵢ, T eⱼ⟫)ᵢⱼ`.  The Gram matrix is the matrix of the
symmetric operator `S = T† T` in the standard basis; on an orthonormal eigenbasis `uᵢ` of `S` the
eigenvalues are `⟪S uᵢ, uᵢ⟫ = ‖T uᵢ‖² ≥ c²`, and `det S` is their product. -/
theorem Submission.deformation_ipl_cc_gram_det_lower_bound : ∀ (P k : ℕ) (T : Eucl k →L[ℝ] Eucl P) (c : ℝ), 0 ≤ c → (∀ s : Eucl k, c * ‖s‖ ≤ ‖T s‖) → c ^ k ≤ Real.sqrt (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1))).det := by
  intro P k T c hc hT
  -- `S = T† T` on `ℝᵏ`, with `⟪S x, y⟫ = ⟪T x, T y⟫`
  set S : Eucl k →ₗ[ℝ] Eucl k :=
    ((ContinuousLinearMap.adjoint T).comp T : Eucl k →L[ℝ] Eucl k).toLinearMap with hS
  have hSin : ∀ x y : Eucl k, inner ℝ (S x) y = inner ℝ (T x) (T y) := by
    intro x y
    simp only [hS, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_left T y (T x)
  -- Step 1: `S` is symmetric
  have hsymm : S.IsSymmetric := by
    intro x y
    rw [hSin, real_inner_comm (S y) x, hSin, real_inner_comm]
  have hn : Module.finrank ℝ (Eucl k) = k := finrank_euclideanSpace_fin
  -- Step 2: the Gram matrix is the matrix of `S` in the standard basis, so `det G = det S`
  have hmat : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis S = Matrix.of fun i j =>
        inner ℝ (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, Matrix.of_apply, ← hSin,
      hsymm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),
      EuclideanSpace.inner_single_left]
    simp
  have hdet : (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1))
      (T (EuclideanSpace.single j 1))).det = LinearMap.det S := by
    rw [← hmat, LinearMap.det_toMatrix]
  -- Step 3: every eigenvalue `λᵢ = ⟪S uᵢ, uᵢ⟫ = ‖T uᵢ‖²` is at least `c²`
  have heig : ∀ i, c ^ 2 ≤ hsymm.eigenvalues hn i := by
    intro i
    have hun : ‖hsymm.eigenvectorBasis hn i‖ = 1 := (hsymm.eigenvectorBasis hn).orthonormal.1 i
    have h1 := hSin (hsymm.eigenvectorBasis hn i) (hsymm.eigenvectorBasis hn i)
    rw [hsymm.apply_eigenvectorBasis hn i, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hun] at h1
    have h2 := hT (hsymm.eigenvectorBasis hn i)
    rw [hun, mul_one] at h2
    have h3 : hsymm.eigenvalues hn i = ‖T (hsymm.eigenvectorBasis hn i)‖ ^ 2 := by
      simpa using h1
    rw [h3]
    nlinarith [norm_nonneg (T (hsymm.eigenvectorBasis hn i))]
  -- Step 4: `det G = ∏ λᵢ ≥ (c²)ᵏ`
  have hprod : (c ^ 2) ^ k ≤ (Matrix.of fun i j => inner ℝ (T (EuclideanSpace.single i 1))
      (T (EuclideanSpace.single j 1))).det := by
    rw [hdet, hsymm.det_eq_prod_eigenvalues hn]
    calc (c ^ 2) ^ k = ∏ _i : Fin k, c ^ 2 := by simp
      _ ≤ ∏ i, hsymm.eigenvalues hn i :=
          Finset.prod_le_prod₀ (fun _ _ => sq_nonneg c) (fun i _ => heig i)
  -- Step 5: `cᵏ = √((c²)ᵏ) ≤ √det G`
  calc c ^ k = Real.sqrt ((c ^ k) ^ 2) := (Real.sqrt_sq (pow_nonneg hc k)).symm
    _ = Real.sqrt ((c ^ 2) ^ k) := by ring_nf
    _ ≤ _ := Real.sqrt_le_sqrt hprod

/-- Signed change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6; used for
Ch. 6, 3.9): if `Φ` is Lipschitz and `c`-antilipschitz on the open set `Ω`, `A ⊆ Φ(Ω)` is
`Hᵏ`-null-measurable and `h` is `Hᵏ`-integrable on `A`, then `h(Φ(w)) JΦ(w)` is `Lᵏ`-integrable
on `D = Ω ∩ Φ⁻¹(A)` and `∫_A h dHᵏ = ∫_D h(Φ(w)) JΦ(w) dLᵏ(w)`.  This is the `[0, ∞]`-valued
change of variables applied to the positive and negative parts of `h` and to `|h|`. -/
theorem Submission.deformation_ipl_cc_signed_change_of_variables : ∀ (P k : ℕ) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)) (A : Set (Eucl P)) (h : Eucl P → ℝ), IsOpen Ω → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[k] : Measure (Eucl P)) → IntegrableOn h A (μHE[k] : Measure (Eucl P)) → IntegrableOn (fun w => h (Φ w) * Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det) (Ω ∩ Φ ⁻¹' A) (volume : Measure (Eucl k)) ∧ ∫ x in A, h x ∂(μHE[k] : Measure (Eucl P)) = ∫ w in Ω ∩ Φ ⁻¹' A, h (Φ w) * Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det ∂(volume : Measure (Eucl k)) := by
  intro P k Φ Ω A h hΩ hΦLip hΦanti hAΦ hAm hh
  set J : Eucl k → ℝ := fun w => Real.sqrt (Matrix.of fun i j => inner ℝ
    (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det
  set D : Set (Eucl k) := Ω ∩ Φ ⁻¹' A
  -- The Jacobian `J = JΦ` is nonnegative and Borel: `fderiv ℝ Φ` is Borel, and `J` is a
  -- continuous function of its columns `DΦ(w) eᵢ`.
  have hJ0 : ∀ w, 0 ≤ J w := fun w => Real.sqrt_nonneg _
  have hJm : Measurable J := by
    have hfd : Measurable (fderiv ℝ Φ) := measurable_fderiv ℝ Φ
    have hcol : ∀ i : Fin k, Measurable (fun w => fderiv ℝ Φ w (EuclideanSpace.single i 1)) :=
      fun i => (ContinuousLinearMap.apply ℝ (Eucl P)
        (EuclideanSpace.single i 1)).continuous.measurable.comp hfd
    have hmat : Measurable (fun w => (fun i j => inner ℝ
        (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1)) :
          Fin k → Fin k → ℝ)) := by
      refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
      exact continuous_inner.measurable.comp ((hcol i).prodMk (hcol j))
    have hdet : Continuous (fun f : Fin k → Fin k → ℝ => (Matrix.of f).det) :=
      (show Continuous (fun f : Fin k → Fin k → ℝ => Matrix.of f) from continuous_id).matrix_det
    exact Real.continuous_sqrt.measurable.comp (hdet.measurable.comp hmat)
  -- The `[0, ∞]`-valued change of variables for `h⁺`, `h⁻` and `|h|`.
  obtain ⟨-, hposm, hposeq⟩ := Submission.lpf_raf_chart_change_of_variables P k Φ Ω A
    (fun x => ENNReal.ofReal (h x)) hΩ hΦLip hΦanti hAΦ hAm hh.aemeasurable.ennreal_ofReal
  obtain ⟨-, hnegm, hnegeq⟩ := Submission.lpf_raf_chart_change_of_variables P k Φ Ω A
    (fun x => ENNReal.ofReal (-h x)) hΩ hΦLip hΦanti hAΦ hAm hh.neg.aemeasurable.ennreal_ofReal
  obtain ⟨-, -, habseq⟩ := Submission.lpf_raf_chart_change_of_variables P k Φ Ω A
    (fun x => ‖h x‖ₑ) hΩ hΦLip hΦanti hAΦ hAm hh.aemeasurable.enorm
  -- `h ∘ Φ = (h⁺ ∘ Φ) - (h⁻ ∘ Φ)` is a.e.-measurable on `D`.
  have hhΦ : AEMeasurable (fun w => h (Φ w)) ((volume : Measure (Eucl k)).restrict D) := by
    refine (hposm.ennreal_toReal.sub hnegm.ennreal_toReal).congr
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply]
    rcases le_total 0 (h (Φ w)) with hw | hw
    · rw [ENNReal.toReal_ofReal hw, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero,
        sub_zero]
    · rw [ENNReal.ofReal_of_nonpos hw, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_zero]
      ring
  -- Integrability on `D`: `∫⁻_D ‖h(Φ(w)) J(w)‖ₑ dw = ∫⁻_A ‖h‖ₑ dHᵏ < ∞`.
  have hFint : IntegrableOn (fun w => h (Φ w) * J w) D (volume : Measure (Eucl k)) := by
    refine ⟨(hhΦ.mul hJm.aemeasurable).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have : ∫⁻ w in D, ‖h (Φ w) * J w‖ₑ = ∫⁻ x in A, ‖h x‖ₑ ∂(μHE[k] : Measure (Eucl P)) := by
      rw [habseq]
      refine lintegral_congr fun w => ?_
      rw [enorm_mul, Real.enorm_eq_ofReal_abs (J w), abs_of_nonneg (hJ0 w)]
    rw [this]
    exact hh.2
  refine ⟨hFint, ?_⟩
  -- The signed identity: `∫ f = (∫⁻ f⁺) - (∫⁻ f⁻)` on both sides, and
  -- `ofReal (±h(Φ(w))) * ofReal (J w) = ofReal (±h(Φ(w)) * J w)` as `J ≥ 0`.
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hFint, hposeq, hnegeq]
  congr 2
  · refine lintegral_congr fun w => ?_
    rw [← ENNReal.ofReal_mul' (hJ0 w)]
  · refine lintegral_congr fun w => ?_
    rw [← ENNReal.ofReal_mul' (hJ0 w), neg_mul]
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

/-- Measurable relative orientation on a `C¹` antilipschitz chart (Simon Ch. 6, proof of 3.9,
step (6c)): for a rectifiable triple `(M, θ, ξ)` and a `C¹` map `Φ` that is antilipschitz on the
open set `Ω`, there is a sign `σ = ±1`, a.e.-strongly measurable for `Lᵏ ⌞ (Ω ∩ Φ⁻¹(M))`, with
`JΦ(w) ξ(Φ(w)) = σ(w) ∂₁Φ(w) ∧ ⋯ ∧ ∂ₖΦ(w)` for `Lᵏ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`.  The sign is that of
`⟨ξ(Φ(w)), β_w⟩` for the covector `β_w(u) = det (⟪∂ₐΦ(w), u_b⟫)`, continuous in `w`. -/
theorem Submission.deformation_ipl_cc_chart_orientation_sign : ∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)), IsOpen U → IsRectifiableTriple U k M θ ξ → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∃ σ : Eucl k → ℝ, AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) ∧ ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)), (σ w = 1 ∨ σ w = -1) ∧ Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • ξ (Φ w) = σ w • simpleNVector (fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1)) := by
  intro P k U M θ ξ Φ Ω hU hT hΩ hΦC1 hΦanti
  have hΦc : Continuous Φ := hΦC1.continuous
  have hΦm : Measurable Φ := hΦc.measurable
  -- A strongly measurable representative `ξt` of `ξ`.
  set ξt := hT.aestronglyMeasurable.mk ξ with hξt
  have hξtm : StronglyMeasurable ξt := hT.aestronglyMeasurable.stronglyMeasurable_mk
  have hξeq : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ξ x = ξt x :=
    hT.aestronglyMeasurable.ae_eq_mk
  -- Good points of `M ∩ Φ(Ω)`: tangent spaces from the chart and the orientation, `ξ = ξt`.
  have hgoodH : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ Φ '' Ω)),
      (∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt k M θ y
          (LinearMap.range (fderiv ℝ Φ w).toLinearMap)) ∧
      (∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt k M θ y (Submodule.span ℝ (range τ)) ∧
        (ξ y = simpleNVector τ ∨ ξ y = -simpleNVector τ)) ∧
      ξ y = ξt y := by
    have h1 := Submission.lpf_weighted_tangent_on_c1_chart P k U M θ Φ Ω hU hT.subset
      hT.nullMeasurableSet hT.pos hT.integrableOn hΩ hΦC1 hΦanti
    have h2 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M ∩ Φ '' Ω ⊆ M) hT.orients
    have h3 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M ∩ Φ '' Ω ⊆ M) hξeq
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  -- Pull the good points back to parameters.
  obtain ⟨hSm, hgood⟩ := Submission.lpf_ccr_ae_pullback P k M Φ Ω _ hΩ.measurableSet hΦm hΦanti
    hT.nullMeasurableSet hgoodH
  have hmemS : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)), w ∈ Ω ∩ Φ ⁻¹' M :=
    ae_restrict_mem₀ hSm
  set v : Eucl k → Fin k → Eucl P := fun w b => fderiv ℝ Φ w (EuclideanSpace.single b 1) with hv
  set J : Eucl k → ℝ := fun w => Real.sqrt (Matrix.of fun i j => inner ℝ
    (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det
    with hJdef
  -- The test covector `β w = covectorPullback (DΦ(w)†) β₀`, `β w u = det (⟪∂ₐΦ(w), u_b⟫)`.
  set β₀ : Covector (Eucl k) k := wedgeCovectors k (fun a => (EuclideanSpace.proj a : Eucl k →L[ℝ] ℝ))
    with hβ₀
  set β : Eucl k → Covector (Eucl P) k :=
    fun w => covectorPullback k (ContinuousLinearMap.adjoint (fderiv ℝ Φ w)) β₀ with hβdef
  have hβv : ∀ w, β w (v w) = (Matrix.of fun i j => inner ℝ (v w i) (v w j)).det := by
    intro w
    simp only [hβdef, covectorPullback_apply, hβ₀, wedgeCovectors_apply_det]
    congr 1
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply]
    have h1 := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ)
      (ContinuousLinearMap.adjoint (fderiv ℝ Φ w) (v w j))
    rw [ContinuousLinearMap.adjoint_inner_right] at h1
    simp only [map_one, one_mul] at h1
    rw [h1]
    rfl
  have hβc : Continuous β := by
    have hfd : Continuous (fderiv ℝ Φ) := hΦC1.continuous_fderiv one_ne_zero
    have hadj : Continuous (fun w => ContinuousLinearMap.adjoint (fderiv ℝ Φ w)) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Eucl k) (F := Eucl P)).continuous.comp hfd
    have hcomp : Continuous (fun A : Eucl P →L[ℝ] Eucl k =>
        (covectorPullback k A : Covector (Eucl k) k →L[ℝ] Covector (Eucl P) k)) :=
      ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM
    exact (hcomp.comp hadj).clm_apply continuous_const
  -- The sign `σ` of the pairing `p w = ⟨ξ(Φ(w)), β w⟩`, and its measurability.
  set p : Eucl k → ℝ := fun w => ξ (Φ w) (β w) with hp
  set σ : Eucl k → ℝ := fun w => if 0 ≤ p w then 1 else -1 with hσdef
  have hpm : AEStronglyMeasurable p ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) := by
    have hξΦ : AEStronglyMeasurable (fun w => ξ (Φ w))
        ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) := by
      refine (hξtm.comp_measurable hΦm).aestronglyMeasurable.congr ?_
      filter_upwards [hgood] with w hw
      exact hw.2.2.symm
    have hpair : Continuous (fun q : NVector (Eucl P) k × Covector (Eucl P) k => q.1 q.2) :=
      isBoundedBilinearMap_apply.continuous
    exact hpair.comp_aestronglyMeasurable (hξΦ.prodMk hβc.aestronglyMeasurable)
  have hσm : AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' M)) := by
    have hs : Measurable (fun t : ℝ => if 0 ≤ t then (1 : ℝ) else -1) :=
      Measurable.ite measurableSet_Ici measurable_const measurable_const
    exact (hs.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  refine ⟨σ, hσm, ?_⟩
  filter_upwards [hgood, hmemS] with w hw hwS
  obtain ⟨hw1, ⟨τ, hτ, hτT, hξτ⟩, -⟩ := hw
  -- `range DΦ(w) = span τ` by uniqueness of the weighted approximate tangent space (`θ > 0`).
  have hθpos : 0 < θ (Φ w) := hT.pos _ hwS.2
  have hrange : LinearMap.range (fderiv ℝ Φ w).toLinearMap = Submodule.span ℝ (range τ) :=
    HasWeightedApproximateTangentSpaceAt.unique hθpos.ne' (hw1 w hwS.1 rfl) hτT
  have hσval : σ w = 1 ∨ σ w = -1 := by
    simp only [hσdef]; split_ifs <;> simp
  refine ⟨hσval, ?_⟩
  -- `∂Φ(w) = B τ` with `B_{ba} = ⟪τ_a, ∂_bΦ(w)⟫`, so `simpleNVector ∂Φ(w) = det B • simpleNVector τ`.
  have hvmem : ∀ b, v w b ∈ Submodule.span ℝ (range τ) := by
    intro b; rw [← hrange]; exact LinearMap.mem_range_self _ _
  have hvexp : ∀ b, (∑ a, inner ℝ (τ a) (v w b) • τ a) = v w b := by
    intro b
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hvmem b)
    have hc : ∀ a, inner ℝ (τ a) (v w b) = cf a := by
      intro a; rw [← hcf]; exact hτ.inner_right_fintype cf a
    simp_rw [hc]; exact hcf
  set B : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun b a => inner ℝ (τ a) (v w b) with hB
  have hS : simpleNVector (v w) = B.det • simpleNVector τ := by
    rw [← Submission.lpf_simple_nvector_algebra.2 P k B τ]
    congr 1
    funext b
    simp only [hB, Matrix.of_apply]
    exact (hvexp b).symm
  -- Norms: `‖simpleNVector τ‖ = 1`, `JΦ(w) = |det B|` and `β w (∂Φ(w)) = (det B)²`.
  have hsτ : ‖simpleNVector τ‖ = 1 := by
    have h := Submission.lpf_simple_nvector_algebra.1 P k τ
    have hG : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ]
    rw [hG, Matrix.det_one] at h
    have h0 : 0 ≤ ‖simpleNVector τ‖ := ContinuousLinearMap.opNorm_nonneg _
    nlinarith [h]
  have hnsmul : ∀ (d : ℝ) (s : NVector (Eucl P) k), ‖d • s‖ = |d| * ‖s‖ := by
    intro d s
    apply le_antisymm
    · simpa [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le d s
    · by_cases hd : d = 0
      · simp only [hd, abs_zero, zero_mul]; exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le d⁻¹ (d • s)
        rw [smul_smul, inv_mul_cancel₀ hd, one_smul, Real.norm_eq_abs, abs_inv] at h
        have hpos : 0 < |d| := abs_pos.mpr hd
        calc |d| * ‖s‖ ≤ |d| * (|d|⁻¹ * ‖d • s‖) := by gcongr
          _ = ‖d • s‖ := by field_simp
  have hnormS : ‖simpleNVector (v w)‖ = |B.det| := by
    rw [hS, hnsmul, hsτ, mul_one]
  have hJ : J w = |B.det| := by
    have h := Submission.lpf_simple_nvector_algebra.1 P k (v w)
    show Real.sqrt (Matrix.of fun i j => inner ℝ (v w i) (v w j)).det = |B.det|
    rw [← h, Real.sqrt_sq (ContinuousLinearMap.opNorm_nonneg _), hnormS]
  have hSβ : simpleNVector (v w) (β w) = B.det ^ 2 := by
    rw [simpleNVector_apply, hβv, ← Submission.lpf_simple_nvector_algebra.1 P k (v w), hnormS,
      sq_abs]
  -- Case analysis on `det B` and on the orientation `ξ(Φ(w)) = ±simpleNVector τ`.
  by_cases hd : B.det = 0
  · have hJ0 : J w = 0 := by rw [hJ, hd, abs_zero]
    have hS0 : simpleNVector (v w) = 0 := by rw [hS, hd, zero_smul]
    show J w • ξ (Φ w) = σ w • simpleNVector (v w)
    rw [hJ0, zero_smul, hS0, smul_zero]
  · have hs : simpleNVector τ (β w) = B.det := by
      have h1 : B.det * simpleNVector τ (β w) = B.det * B.det := by
        have := hSβ
        rw [hS, smul_apply, smul_eq_mul] at this
        rw [this]; ring
      exact mul_left_cancel₀ hd h1
    show J w • ξ (Φ w) = σ w • simpleNVector (v w)
    rw [hJ, hS, smul_smul]
    rcases hξτ with h | h
    · have hp' : p w = B.det := by
        show ξ (Φ w) (β w) = B.det
        rw [h, hs]
      rw [h]
      congr 1
      simp only [hσdef, hp']
      split_ifs with h0
      · rw [abs_of_nonneg h0]; ring
      · rw [abs_of_neg (lt_of_not_ge h0)]; ring
    · have hp' : p w = -B.det := by
        show ξ (Φ w) (β w) = -B.det
        rw [h, neg_apply, hs]
      rw [h]
      have hcoef : -|B.det| = σ w * B.det := by
        simp only [hσdef, hp']
        split_ifs with h0
        · have hneg : B.det < 0 := lt_of_le_of_ne (by linarith) hd
          rw [abs_of_neg hneg]; ring
        · have hpos : 0 < B.det := by linarith
          rw [abs_of_pos hpos]; ring
      ext γ
      simp only [smul_apply, neg_apply, smul_eq_mul]
      rw [← hcoef]; ring

/-- Chart representation of push-forward integrals (steps (6a)–(6d) of the chart convergence in
the C¹ push-forward limit behind the proof of Simon Ch. 6, 5.1): let `Φ` be C¹, Lipschitz and
`c`-antilipschitz (`c > 0`) on the open `Ω ⊆ ℝᵏ`, and let `G ⊆ M ∩ Φ(Ω)` be `Hᵏ`-null-measurable
with `θ ∈ L¹(Hᵏ ⌞ G)`.  With `D = Ω ∩ Φ⁻¹(G)` and the chart orientation sign `σ = ±1`, the weight
`ψ = 1_D (θ ∘ Φ) σ` is in `L¹(Ω)` (as `JΦ ≥ cᵏ` and `∫_D (θ ∘ Φ) JΦ = ∫_G θ`), and
`∫_G θ ⟨α(f), A_# ξ⟩ dHᵏ = ∫_Ω ψ ⟨α(f(Φ)), ∂₀(f ∘ Φ) ∧ ⋯ ∧ ∂ₖ₋₁(f ∘ Φ)⟩ dLᵏ` whenever
`D(f ∘ Φ)(w) = A(Φ w) ∘ DΦ(w)` a.e. on `D` and the left integrand is integrable: by the signed
change of variables, `JΦ(w) ξ(Φ w) = σ(w) ∂₀Φ(w) ∧ ⋯ ∧ ∂ₖ₋₁Φ(w)` and `A(Φ w) ∂_bΦ = ∂_b(f ∘ Φ)`. -/
theorem Submission.deformation_ipl_cc_chart_integral_representation : ∀ (P Q k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)) (G : Set (Eucl P)), IsOpen U → IsRectifiableTriple U k M θ ξ → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → G ⊆ M → G ⊆ Φ '' Ω → NullMeasurableSet G (μHE[k] : Measure (Eucl P)) → IntegrableOn θ G (μHE[k] : Measure (Eucl P)) → ∃ ψ : Eucl k → ℝ, IntegrableOn ψ Ω (volume : Measure (Eucl k)) ∧ ∀ (f : Eucl P → Eucl Q) (A : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (α : Eucl Q → Covector (Eucl Q) k), (∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' G)), HasFDerivAt (f ∘ Φ) ((A (Φ w)).comp (fderiv ℝ Φ w)) w) → IntegrableOn (fun x => θ x * nVectorPushforward k (A x) (ξ x) (α (f x))) G (μHE[k] : Measure (Eucl P)) → ∫ x in G, θ x * nVectorPushforward k (A x) (ξ x) (α (f x)) ∂(μHE[k] : Measure (Eucl P)) = ∫ w in Ω, ψ w * α (f (Φ w)) (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) ∂(volume : Measure (Eucl k)) := by
  intro P Q k U M θ ξ Φ Ω G hU hT hΩ hΦC1 hΦLip hΦanti hGM hGΦ hGm hθG
  obtain ⟨c, hc, hcanti⟩ := hΦanti
  set J : Eucl k → ℝ := fun w => Real.sqrt (Matrix.of fun i j => inner ℝ
    (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det
    with hJdef
  set D : Set (Eucl k) := Ω ∩ Φ ⁻¹' G with hDdef
  have hDΩ : D ⊆ Ω := inter_subset_left
  have hDM : D ⊆ Ω ∩ Φ ⁻¹' M := fun w hw => ⟨hw.1, hGM hw.2⟩
  -- (6a) `c ‖s‖ ≤ ‖DΦ(w) s‖` on `Ω`, hence `cᵏ ≤ JΦ(w)` by the Gram determinant bound.
  have hJlow : ∀ w ∈ Ω, c ^ k ≤ J w := fun w hw =>
    Submission.deformation_ipl_cc_gram_det_lower_bound P k (fderiv ℝ Φ w) c hc.le
      (Submission.lpf_wtc_cat_fderiv_lower_bound P k Φ Ω c w hΩ hw
        ((hΦC1.differentiable one_ne_zero) w) hcanti)
  -- (6c) The orientation sign `σ = ±1` with `JΦ ξ(Φ) = σ ∂₀Φ ∧ ⋯ ∧ ∂ₖ₋₁Φ`, restricted to `D`.
  obtain ⟨σ, hσm, hσ⟩ := Submission.deformation_ipl_cc_chart_orientation_sign P k U M θ ξ Φ Ω
    hU hT hΩ hΦC1 ⟨c, hc, hcanti⟩
  have hσD : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict D), (σ w = 1 ∨ σ w = -1) ∧
      J w • ξ (Φ w) = σ w • simpleNVector (fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1)) :=
    ae_restrict_of_ae_restrict_of_subset hDM hσ
  -- (6b) Change of variables for `θ`: `D` is null-measurable, `θ ∘ Φ` is a.e.-measurable on `D`
  -- and `∫_G θ dHᵏ = ∫_D (θ ∘ Φ) JΦ dLᵏ` (in `ℝ≥0∞`).
  have hθae : AEMeasurable (fun x => ENNReal.ofReal (θ x))
      ((μHE[k] : Measure (Eucl P)).restrict G) := hθG.aemeasurable.ennreal_ofReal
  obtain ⟨hDm, hθΦm, hθCoV⟩ := Submission.lpf_raf_chart_change_of_variables P k Φ Ω G
    (fun x => ENNReal.ofReal (θ x)) hΩ hΦLip ⟨c, hc, hcanti⟩ hGΦ hGm hθae
  have hmemD : ∀ᵐ w ∂((volume : Measure (Eucl k)).restrict D), w ∈ D := ae_restrict_mem₀ hDm
  have hθΦpos : ∀ w ∈ D, 0 < θ (Φ w) := fun w hw => hT.pos _ (hGM hw.2)
  have hθΦae : AEMeasurable (fun w => θ (Φ w)) ((volume : Measure (Eucl k)).restrict D) := by
    refine hθΦm.ennreal_toReal.congr ?_
    filter_upwards [hmemD] with w hw
    exact ENNReal.toReal_ofReal (hθΦpos w hw).le
  have hσDm : AEStronglyMeasurable σ ((volume : Measure (Eucl k)).restrict D) :=
    hσm.mono_measure (Measure.restrict_mono hDM le_rfl)
  have hDmΩ : NullMeasurableSet D ((volume : Measure (Eucl k)).restrict Ω) :=
    hDm.mono_ac Measure.restrict_le_self.absolutelyContinuous
  have hrestrDΩ : ((volume : Measure (Eucl k)).restrict Ω).restrict D =
      (volume : Measure (Eucl k)).restrict D := by
    rw [Measure.restrict_restrict₀ hDmΩ, inter_eq_left.mpr hDΩ]
  -- The weight `ψ = 1_D F₁`, `F₁ = (θ ∘ Φ) σ`, is a.e.-strongly measurable on `Ω`.
  set F₁ : Eucl k → ℝ := fun w => θ (Φ w) * σ w with hF₁
  set ψ : Eucl k → ℝ := D.indicator F₁ with hψdef
  have hF₁m : AEStronglyMeasurable F₁ ((volume : Measure (Eucl k)).restrict D) :=
    hθΦae.aestronglyMeasurable.mul hσDm
  have hψm : AEStronglyMeasurable ψ ((volume : Measure (Eucl k)).restrict Ω) := by
    rw [hψdef, aestronglyMeasurable_indicator_iff₀ hDmΩ, hrestrDΩ]
    exact hF₁m
  have hck : 0 < c ^ k := pow_pos hc k
  have hck0 : ENNReal.ofReal (c ^ k) ≠ 0 := by simpa using hck
  refine ⟨ψ, ?_, ?_⟩
  · -- (6d) `∫_Ω |ψ| = ∫_D θ ∘ Φ ≤ c⁻ᵏ ∫_D (θ ∘ Φ) JΦ = c⁻ᵏ ∫_G θ < ∞`.
    refine ⟨hψm, ?_⟩
    rw [HasFiniteIntegral]
    have h1 : ∫⁻ w in Ω, ‖ψ w‖ₑ = ∫⁻ w in D, ‖F₁ w‖ₑ := by
      have : (fun w => ‖ψ w‖ₑ) = D.indicator (fun w => ‖F₁ w‖ₑ) := by
        funext w
        by_cases hw : w ∈ D
        · simp [hψdef, hw]
        · simp [hψdef, hw]
      rw [this, lintegral_indicator₀ hDmΩ, hrestrDΩ]
    rw [h1]
    have h2 : ∫⁻ w in D, ‖F₁ w‖ₑ ≤ ∫⁻ w in D,
        (ENNReal.ofReal (c ^ k))⁻¹ * (ENNReal.ofReal (θ (Φ w)) * ENNReal.ofReal (J w)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [hσD, hmemD] with w hw hwD
      have hθp := hθΦpos w hwD
      have hσ1 : |σ w| = 1 := by rcases hw.1 with h | h <;> simp [h]
      have hle : c ^ k ≤ J w := hJlow w hwD.1
      calc ‖F₁ w‖ₑ = ENNReal.ofReal (θ (Φ w)) := by
            rw [hF₁, Real.enorm_eq_ofReal_abs, abs_mul, hσ1, abs_of_pos hθp, mul_one]
        _ = (ENNReal.ofReal (c ^ k))⁻¹ * (ENNReal.ofReal (θ (Φ w)) * ENNReal.ofReal (c ^ k)) := by
            rw [mul_comm (ENNReal.ofReal (θ (Φ w))), ← mul_assoc,
              ENNReal.inv_mul_cancel hck0 ENNReal.ofReal_ne_top, one_mul]
        _ ≤ (ENNReal.ofReal (c ^ k))⁻¹ * (ENNReal.ofReal (θ (Φ w)) * ENNReal.ofReal (J w)) := by
            gcongr
    refine lt_of_le_of_lt h2 ?_
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hck0), ← hθCoV]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by simpa using hck)) ?_
    refine lt_of_le_of_lt ?_ hθG.2
    refine lintegral_mono fun x => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · -- (7) `∫_G h dHᵏ = ∫_D h(Φ) JΦ dLᵏ` by the signed change of variables, and pointwise on `D`
    -- `h(Φ w) JΦ(w) = F₁(w) α(f(Φ w))(∂(f ∘ Φ)(w))`.
    intro f A α hfd hint
    obtain ⟨-, hcov⟩ := Submission.deformation_ipl_cc_signed_change_of_variables P k Φ Ω G
      (fun x => θ x * nVectorPushforward k (A x) (ξ x) (α (f x)))
      hΩ hΦLip ⟨c, hc, hcanti⟩ hGΦ hGm hint
    rw [hcov]
    have hR : ∫ w in Ω, ψ w * α (f (Φ w))
          (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) =
        ∫ w in D, F₁ w * α (f (Φ w))
          (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) := by
      have : (fun w => ψ w * α (f (Φ w))
            (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1))) =
          D.indicator (fun w => F₁ w * α (f (Φ w))
            (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1))) := by
        funext w
        by_cases hw : w ∈ D
        · simp [hψdef, hw]
        · simp [hψdef, hw]
      rw [this, integral_indicator₀ hDmΩ, hrestrDΩ]
    rw [hR]
    refine setIntegral_congr_ae₀ hDm ?_
    have hgood := (ae_restrict_iff'₀ hDm).mp (hσD.and hfd)
    filter_upwards [hgood] with w hw hwD
    obtain ⟨⟨-, hJξ⟩, hder⟩ := hw hwD
    set v : Fin k → Eucl P := fun b => fderiv ℝ Φ w (EuclideanSpace.single b 1) with hv
    set β : Covector (Eucl P) k := covectorPullback k (A (Φ w)) (α (f (Φ w))) with hβ
    -- Evaluate `JΦ ξ(Φ w) = σ v₀ ∧ ⋯ ∧ vₖ₋₁` at `β = A(Φ w)^# α(f(Φ w))`.
    have key : ξ (Φ w) β * J w = σ w * β v := by
      have := congrArg (fun T : NVector (Eucl P) k => T β) hJξ
      simp only [smul_apply, smul_eq_mul, simpleNVector_apply] at this
      linarith [this]
    -- The chain rule: `∂_b(f ∘ Φ)(w) = A(Φ w) v_b`.
    have hfv : (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) =
        (A (Φ w)) ∘ v := by
      funext b
      rw [hder.fderiv]
      rfl
    have hβv : β v = α (f (Φ w)) ((A (Φ w)) ∘ v) := by
      rw [hβ, covectorPullback_apply]
    show θ (Φ w) * nVectorPushforward k (A (Φ w)) (ξ (Φ w)) (α (f (Φ w))) * J w =
      F₁ w * α (f (Φ w)) (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1))
    have hpush : nVectorPushforward k (A (Φ w)) (ξ (Φ w)) (α (f (Φ w))) = ξ (Φ w) β := rfl
    rw [hpush, mul_assoc, key, hβv, hfv, hF₁]
    ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
