import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral
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
/-- The triangle inequality for the Euclidean coefficient norm of covectors (Simon Ch. 6, 1.15):
`|α + γ| ≤ |α| + |γ|`.  `|a|` is the Euclidean norm of the coefficient vector
`c(a)_I = [I strictly increasing] · a(b_{I(0)}, …, b_{I(n-1)})` in `ℝ^(Fin n → Fin P)`, and `c` is
additive, so this is `norm_add_le` in that Euclidean space. -/
theorem Submission.cmb_rb_covectorEuclideanNorm_add_le :
    ∀ (P n : ℕ) (α γ : Covector (Eucl P) n),
      covectorEuclideanNorm (α + γ) ≤ covectorEuclideanNorm α + covectorEuclideanNorm γ := by
  intro P n α γ
  -- The coefficient vector `c(a)_I = [I strictly increasing] · a(b_{I(0)}, …, b_{I(n-1)})`.
  let c : Covector (Eucl P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun a =>
    WithLp.toLp 2 fun I =>
      if StrictMono I then a (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) else 0
  have hc : ∀ a, covectorEuclideanNorm a = ‖c a‖ := by
    intro a
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [c, Real.norm_eq_abs, sq_abs]
    split_ifs <;> simp
  have hadd : c (α + γ) = c α + c γ := by
    ext I
    simp only [c, PiLp.add_apply, ContinuousAlternatingMap.add_apply]
    split_ifs <;> simp
  rw [hc, hc, hc, hadd]
  exact norm_add_le _ _
/-- Coefficients of a measure representation (2.7) are integrable on compact sets (Simon Ch. 6,
p. 136): for compact `K ⊆ W ⊆ U`, `W` open, test with `ψ = χ dx^β`, where the smooth cutoff `χ`
equals `1` exactly on `K` and has compact support in `W`.  Then `⟨ψ, v⟩` is `μ`-integrable and
agrees on `K` with the coefficient `⟨dx^β, v⟩`. -/
theorem Submission.cmb_rb_measureRepresentation_integrableOn_coeff :
    ∀ (P n : ℕ) (U W : Set (Eucl P)), IsOpen W → W ⊆ U → ∀ (T : GeometricCurrentOn U n)
      (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v →
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ W → ∀ β : SimonMultiIndex n P,
        IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) K μ := by
  intro P n U W hW hWU T μ v hrep K hK hKW β
  -- An open `V` with `K ⊆ V` and `closure V` compact inside `W`.
  obtain ⟨V, hVo, hKV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  -- A smooth cutoff `χ` with `support χ = V` and `χ x = 1 ↔ x ∈ K`.
  obtain ⟨χ, hχs, -, hχV, hχK⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hVo hK.isClosed hKV
  -- The test form `ψ = χ dx^β`.
  let c : Covector (Eucl P) n := wedgeCovectors n (fun j => EuclideanSpace.proj (β j))
  let ψ : DifferentialForm (Eucl P) n := fun x => χ x • c
  have hψV : tsupport ψ ⊆ closure V := by
    simpa [tsupport, hχV] using tsupport_smul_subset_left χ (fun _ => c)
  have hψ : ψ ∈ TestFormOn U n :=
    ⟨⟨hχs.smul contDiff_const, hVc.of_isClosed_subset (isClosed_tsupport _) hψV⟩,
      hψV.trans (hVW.trans hWU)⟩
  -- `⟨ψ, v⟩` is `μ`-integrable and equals the coefficient on the closed set `K`.
  refine (hrep ⟨ψ, hψ⟩).1.integrableOn.congr_fun (fun x hx => ?_) hK.isClosed.measurableSet
  simp [ψ, c, (hχK x).1 hx, euclideanNVectorCoordinate]

/-- **Coordinate pairing estimate, the step "by (2.7)" in the proof of Simon Ch. 6, Lemma 2.15
(p. 137).**  Let the coefficients `v^β = ⟨dx^β, v⟩` of `v` be `μ`-integrable on a measurable set
`K`, and let `θ` be a continuous `n`-form vanishing off `K` with `|θ| ≤ D` (Euclidean coefficient
norm).  Then `f = ∑_β θ(e_β) v^β` is `μ`-integrable and `|∫ f dμ| ≤ D ∑_β ∫_K |v^β| dμ`.  Each
coefficient `θ(e_β)` is continuous with `|θ(e_β)| ≤ |θ| ≤ D`, so `f` is integrable on `K`; it
vanishes off `K`; and `|f| ≤ ∑_β D |v^β|` pointwise. -/
theorem Submission.cmb_rb_integral_coeff_pairing_bound : ∀ (P n : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) (K : Set (Eucl P)), MeasurableSet K → (∀ β : SimonMultiIndex n P, IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) K μ) → ∀ (θ : Eucl P → Covector (Eucl P) n) (D : ℝ), Continuous θ → (∀ x, x ∉ K → θ x = 0) → (∀ x, covectorEuclideanNorm (θ x) ≤ D) → Integrable (fun x => ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β) μ ∧ |∫ x, ∑ β : SimonMultiIndex n P, euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β ∂μ| ≤ D * ∑ β : SimonMultiIndex n P, ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ := by
  intro P n μ v K _hK hv θ D hθ hθK hθD
  -- Step 1: every coefficient is bounded, `|θ(x)(e_β)| ≤ |θ(x)| ≤ D`.
  have hcD : ∀ (β : SimonMultiIndex n P) (x : Eucl P),
      |euclideanCovectorCoordinate (θ x) β| ≤ D := fun β x =>
    (Submission.cmb_rb_abs_euclideanCovectorCoordinate_le P n (θ x) β).trans (hθD x)
  -- Step 2: `x ↦ θ(x)(e_β)` is continuous, as evaluation at `e_β` is continuous.
  have hcc : ∀ β : SimonMultiIndex n P,
      Continuous fun x => euclideanCovectorCoordinate (θ x) β := fun β =>
    hθ.eval_const _
  -- Step 3: each `θ(e_β) v^β`, hence `f`, is `μ`-integrable on `K`.
  have hfK : IntegrableOn (fun x => ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β) K μ :=
    integrable_finsetSum _ fun β _ => Integrable.bdd_mul (hv β) (hcc β).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hcD β x))
  -- Step 4: `f = 0` off `K`, so `f` is `μ`-integrable and `∫ f dμ = ∫_K f dμ`.
  have hf0 : ∀ x, x ∉ K → ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β = 0 := by
    intro x hx
    simp [euclideanCovectorCoordinate, hθK x hx]
  refine ⟨(integrableOn_iff_integrable_of_support_subset
    (Function.support_subset_iff'.2 hf0)).1 hfK, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf0]
  -- Steps 5–6: `|f| ≤ ∑_β D |v^β|` pointwise; integrate over `K`.
  have hg : ∀ β ∈ (Finset.univ : Finset (SimonMultiIndex n P)),
      IntegrableOn (fun x => D * |euclideanNVectorCoordinate (v x) β|) K μ := fun β _ =>
    (hv β).abs.const_mul D
  calc |∫ x in K, ∑ β : SimonMultiIndex n P,
          euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β ∂μ|
      ≤ ∫ x in K, |∑ β : SimonMultiIndex n P,
          euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in K, ∑ β : SimonMultiIndex n P, D * |euclideanNVectorCoordinate (v x) β| ∂μ :=
        integral_mono hfK.abs (integrable_finsetSum _ hg) fun x =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun β _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hcD β x) (abs_nonneg _))
    _ = ∑ β : SimonMultiIndex n P, D * ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ := by
        rw [integral_finsetSum _ hg]
        simp only [integral_const_mul]
    _ = D * ∑ β : SimonMultiIndex n P, ∫ x in K, |euclideanNVectorCoordinate (v x) β| ∂μ :=
        (Finset.mul_sum _ _ _).symm
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
/-- Simon Ch. 6, §5, proof of 5.1 (p. 164), the inclusion `⊆` of the identity printed after (5):
the `σ`-neighbourhood of `L(a)` lies in the union of the periodic coordinate cylinders
`p_J⁻¹(B_σ(p_J(a) + z))`, `|J| = k`, `z ∈ ℤ^J`.  `L(a)` contains `a` (as `k ≤ d`), so
`dist(x, L(a)) < σ` gives `y ∈ L(a)` with `|x − y| < σ`; for the `J` and the integers
`z_i = y_i − a_i` (`i ∈ J`) witnessing `y ∈ L(a)`,
`∑_{i∈J} (x_i − a_i − z_i)² = ∑_{i∈J} (x_i − y_i)² ≤ |x − y|² < σ²`. -/
theorem Submission.dgc_tube_cover :
    ∀ (d k : ℕ), k ≤ d → ∀ (a : Eucl d) (La : Set (Eucl d)), La = {y | ∃ J : Finset (Fin d), J.card = k ∧ ∀ i ∈ J, ∃ n : ℤ, y i - a i = n} → ∀ (σ : ℝ) (x : Eucl d), infDist x La < σ → ∃ J : Finset (Fin d), J.card = k ∧ ∃ z : J → ℤ, ∑ i : J, (x i - a i - z i) ^ 2 < σ ^ 2 := by
  classical
  intro d k hkd a La hLa σ x hx
  subst hLa
  -- `L(a)` is nonempty: `a ∈ L(a)` for any `k` of the `d` coordinates.
  have hne : {y : Eucl d | ∃ J : Finset (Fin d), J.card = k ∧
      ∀ i ∈ J, ∃ n : ℤ, y i - a i = n}.Nonempty := by
    obtain ⟨J₀, -, hJ₀⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin d))) (by simpa using hkd)
    exact ⟨a, J₀, hJ₀, fun i _ => ⟨0, by simp⟩⟩
  -- A point `y ∈ L(a)` with `|x − y| < σ`, and its lattice coordinates `z_i = y_i − a_i`.
  obtain ⟨y, ⟨J, hJ, hy⟩, hxy⟩ := (infDist_lt_iff hne).1 hx
  choose n hn using hy
  refine ⟨J, hJ, fun i => n i.1 i.2, ?_⟩
  calc ∑ i : J, (x i - a i - (n i.1 i.2 : ℝ)) ^ 2 = ∑ i ∈ J, (x i - y i) ^ 2 := by
        rw [← Finset.sum_coe_sort J]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hn i.1 i.2]
        ring
    _ ≤ ∑ i, (x i - y i) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg fun i => sq_nonneg _
    _ = dist x y ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq]
        simp [Real.dist_eq, sq_abs]
    _ < σ ^ 2 := by gcongr
/-- Ball-volume bound used in step 8 of the proof of Simon Ch. 6, 5.1 (pp. 163–164), with the
erratum `ω_k ≤ 2^k`: a closed Euclidean ball of radius `r ≥ 0` in `ℝ^ι` has Lebesgue measure at
most `(2r)^k`, `k = card ι`.  Each coordinate is `1`-Lipschitz, so `B̄_r(c)` lies in the preimage
under the measure-preserving coordinate map `ofLp` of the sup-metric cube `∏_i [c_i - r, c_i + r]`,
whose volume is `(2r)^k`. -/
theorem Submission.dgc_pm_ball_volume_le :
    ∀ (ι : Type) [Fintype ι] (c : EuclideanSpace ℝ ι) (r : ℝ), 0 ≤ r →
      volume (closedBall c r) ≤ ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  intro ι _ c r hr
  -- `|w_i - c_i| ≤ |w - c| ≤ r`, so `B̄_r(c) ⊆ ofLp⁻¹(Q)`, `Q` the sup-metric ball about `ofLp c`.
  have hsub : closedBall c r ⊆ WithLp.ofLp ⁻¹' closedBall (WithLp.ofLp c) r := fun w hw =>
    (dist_pi_le_iff hr).2 fun i => (PiLp.dist_apply_le w c i).trans (mem_closedBall.1 hw)
  -- `ofLp` is measure preserving and `Q` is closed, so `L^k(ofLp⁻¹(Q)) = volume(Q) = (2r)^k`.
  calc volume (closedBall c r)
      ≤ volume (WithLp.ofLp ⁻¹' closedBall (WithLp.ofLp c) r) := measure_mono hsub
    _ = volume (closedBall (WithLp.ofLp c) r) :=
        (PiLp.volume_preserving_ofLp ι).measure_preimage measurableSet_closedBall.nullMeasurableSet
    _ = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := Real.volume_pi_closedBall _ hr
/-- Simon Ch. 6, proof of 5.1 (p. 164): `{p_j⁻¹ B_{σ_ℓ}(b_ℓ + z)}_{ℓ = 1, 2, …, z ∈ ℤ^{n+ℓ} ∩ S_j}`
is a pairwise disjoint collection.  Stated for the periodic open sets before pulling back by `p_j`:
if `|b - g₀|, |b' - g₀| < 1/4`, `0 < σ, σ' < 1/4` and `B̄_σ(b) ∩ B̄_σ'(b') = ∅`, then
`⋃_{z ∈ ℤ^ι} B_σ(b + z)` and `⋃_{z ∈ ℤ^ι} B_σ'(b' + z)` are disjoint. -/
theorem Submission.dgc_pm_lattice_tubes_disjoint :
    ∀ (ι : Type) [Fintype ι] (g₀ b b' : EuclideanSpace ℝ ι) (σ σ' : ℝ), dist b g₀ < 1 / 4 → dist b' g₀ < 1 / 4 → 0 < σ → σ < 1 / 4 → 0 < σ' → σ' < 1 / 4 → Disjoint (closedBall b σ) (closedBall b' σ') → Disjoint {y : EuclideanSpace ℝ ι | ∃ z : ι → ℤ, ∑ i, (y i - b i - z i) ^ 2 < σ ^ 2} {y : EuclideanSpace ℝ ι | ∃ z : ι → ℤ, ∑ i, (y i - b' i - z i) ^ 2 < σ' ^ 2} := by
  intro ι _ g₀ b b' σ σ' hb hb' hσ hσ4 hσ' hσ'4 hbb'
  rw [Set.disjoint_left]
  rintro y ⟨z, hz⟩ ⟨z', hz'⟩
  -- The translate `w z = y - z` of `y` by a lattice point `z ∈ ℤ^ι`.
  obtain ⟨w, hw⟩ : ∃ w : (ι → ℤ) → EuclideanSpace ℝ ι, ∀ z i, w z i = y i - z i :=
    ⟨fun z => WithLp.toLp 2 fun i => y i - z i, fun _ _ => rfl⟩
  -- `|(y - z) - c|² = ∑ᵢ (yᵢ - cᵢ - zᵢ)²`, so the defining inequality gives `|(y - z) - c| < τ`.
  have hdist : ∀ (c : EuclideanSpace ℝ ι) (z : ι → ℤ) (τ : ℝ), 0 < τ →
      ∑ i, (y i - c i - z i) ^ 2 < τ ^ 2 → dist (w z) c < τ := by
    intro c z τ hτ h
    refine lt_of_pow_lt_pow_left₀ 2 hτ.le ?_
    rw [EuclideanSpace.dist_sq_eq]
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun i _ => ?_) h
    rw [Real.dist_eq, sq_abs, hw]
    ring
  have h1 := hdist b z σ hσ hz
  have h2 := hdist b' z' σ' hσ' hz'
  by_cases hzz : z = z'
  · -- If `z = z'`, then `y - z ∈ B̄_σ(b) ∩ B̄_σ'(b')`.
    subst hzz
    exact Set.disjoint_left.1 hbb' (mem_closedBall.2 h1.le) (mem_closedBall.2 h2.le)
  · -- If `z ≠ z'`, then `|z - z'| < 1` (both `y - z` and `y - z'` are `1/2`-close to `g₀`),
    -- while `|zⱼ - z'ⱼ| ≥ 1` for some `j`.
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hzz
    have hint : (1 : ℝ) ≤ |(z j : ℝ) - z' j| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hj)
    have hcoord : |(z j : ℝ) - z' j| ≤ dist (w z') (w z) := by
      have h := PiLp.dist_apply_le (w z') (w z) j
      rw [Real.dist_eq, hw, hw] at h
      convert h using 2
      ring
    have hg : dist (w z) g₀ < 1 / 2 := by
      calc dist (w z) g₀ ≤ dist (w z) b + dist b g₀ := dist_triangle _ _ _
        _ < 1 / 4 + 1 / 4 := add_lt_add (h1.trans hσ4) hb
        _ = 1 / 2 := by norm_num
    have hg' : dist (w z') g₀ < 1 / 2 := by
      calc dist (w z') g₀ ≤ dist (w z') b' + dist b' g₀ := dist_triangle _ _ _
        _ < 1 / 4 + 1 / 4 := add_lt_add (h2.trans hσ'4) hb'
        _ = 1 / 2 := by norm_num
    have hzz' : dist (w z') (w z) < 1 := by
      calc dist (w z') (w z) ≤ dist (w z') g₀ + dist (w z) g₀ := dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add hg' hg
        _ = 1 := by norm_num
    linarith

/-- Vitali volume bound (Simon Ch. 6, §5, proof of 5.1, printed (4), pp. 163–164): if
`0 < r(b) ≤ R` on `S ⊆ ℝᵏ` and every `u ⊆ S` with pairwise disjoint closed balls
`B̄_{r(b)}(b)` is countable with `∑_{b ∈ u} r(b)ᵏ ≤ M`, then `Lᵏ(S) ≤ 10ᵏ M`.
The 5-times covering lemma (closed balls, `τ = 5`) gives such a `u` with
`S ⊆ ⋃_{b ∈ u} B̄_{5r(b)}(b)`, and `Lᵏ(B̄_{5r(b)}(b)) ≤ (10 r(b))ᵏ`.  Only monotonicity and
countable subadditivity of the outer measure are used, so `S` need not be measurable. -/
theorem Submission.dgc_pm_vitali_volume_bound :
    ∀ (ι : Type) [Fintype ι] (S : Set (EuclideanSpace ℝ ι)) (r : EuclideanSpace ℝ ι → ℝ)
      (R M : ℝ), (∀ b ∈ S, 0 < r b ∧ r b ≤ R) →
      (∀ u ⊆ S, u.PairwiseDisjoint (fun b => closedBall b (r b)) →
        u.Countable ∧ ∑' b : u, ENNReal.ofReal (r b ^ Fintype.card ι) ≤ ENNReal.ofReal M) →
      volume S ≤ ENNReal.ofReal (10 ^ Fintype.card ι * M) := by
  intro ι _ S r R M hr hpack
  -- 5-times covering: a disjoint subfamily `u ⊆ S` whose enlargements `B̄_{5r(b)}(b)` cover `S`.
  obtain ⟨u, huS, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S (fun b => b) r R
      (fun a ha => (hr a ha).2) 5 (by norm_num)
  obtain ⟨hcount, hsum⟩ := hpack u huS hdisj
  have hSsub : S ⊆ ⋃ b ∈ u, closedBall b (5 * r b) := by
    intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov a ha
    exact mem_biUnion hb (hsub (mem_closedBall_self (hr a ha).1.le))
  -- `Lᵏ(B̄_{5r(b)}(b)) ≤ (2 · 5r(b))ᵏ = 10ᵏ r(b)ᵏ`.
  have hball : ∀ b ∈ u, volume (closedBall b (5 * r b)) ≤
      ENNReal.ofReal (10 ^ Fintype.card ι) * ENNReal.ofReal (r b ^ Fintype.card ι) := by
    intro b hb
    have hrb := (hr b (huS hb)).1
    calc volume (closedBall b (5 * r b))
        ≤ ENNReal.ofReal ((2 * (5 * r b)) ^ Fintype.card ι) :=
          Submission.dgc_pm_ball_volume_le ι b _ (by positivity)
      _ = ENNReal.ofReal (10 ^ Fintype.card ι) * ENNReal.ofReal (r b ^ Fintype.card ι) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
        ring_nf
  calc volume S ≤ volume (⋃ b ∈ u, closedBall b (5 * r b)) := measure_mono hSsub
    _ ≤ ∑' b : u, volume (closedBall (b : EuclideanSpace ℝ ι) (5 * r b)) :=
        measure_biUnion_le _ hcount _
    _ ≤ ∑' b : u, ENNReal.ofReal (10 ^ Fintype.card ι) * ENNReal.ofReal (r b ^ Fintype.card ι) :=
        ENNReal.tsum_le_tsum fun b => hball b b.2
    _ = ENNReal.ofReal (10 ^ Fintype.card ι) * ∑' b : u, ENNReal.ofReal (r b ^ Fintype.card ι) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (10 ^ Fintype.card ι) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (10 ^ Fintype.card ι * M) := (ENNReal.ofReal_mul (by positivity)).symm

/-- Periodic maximal estimate (Simon Ch. 6, §5, proof of the Deformation Theorem, printed (3),
(4) and `L^{n+1}(B_j) ≤ β⁻¹5^{n+1}ω_{n+1}`, pp. 163–164), for a finite measure `μ` on `X` and a
measurable `p : X → ℝ^ι`, `k = card ι`: the centres `g` with `|g − g₀| < 1/4` at which some
`σ ∈ (0, 1/4)` has `μ(p⁻¹ ⋃_{z ∈ ℤ^ι} B_σ(g + z)) > βσ^k μ(X)` have outer Lebesgue measure at
most `10^k/β`.  Choosing such a `σ_b` for every bad centre `b`, the periodic tubes of a subfamily
with disjoint balls `B̄_{σ_b}(b)` are disjoint, so the subfamily is countable and
`Σ σ_b^k ≤ 1/β`; the `5`-times covering bound then gives `10^k/β`. -/
theorem Submission.dgc_periodic_maximal :
    ∀ (ι : Type) [Fintype ι] (X : Type) [MeasurableSpace X] (μ : Measure X), IsFiniteMeasure μ →
      ∀ p : X → EuclideanSpace ℝ ι, Measurable p → ∀ (g₀ : EuclideanSpace ℝ ι) (β : ℝ), 0 < β →
        volume {g : EuclideanSpace ℝ ι | dist g g₀ < 1 / 4 ∧ ∃ σ : ℝ, 0 < σ ∧ σ < 1 / 4 ∧
          ENNReal.ofReal (β * σ ^ Fintype.card ι) * μ univ <
            μ {x | ∃ z : ι → ℤ, ∑ i, (p x i - g i - z i) ^ 2 < σ ^ 2}} ≤
          ENNReal.ofReal (10 ^ Fintype.card ι / β) := by
  intro ι _ X _ μ hμ p hp g₀ β hβ
  set Bad := {g : EuclideanSpace ℝ ι | dist g g₀ < 1 / 4 ∧ ∃ σ : ℝ, 0 < σ ∧ σ < 1 / 4 ∧
    ENNReal.ofReal (β * σ ^ Fintype.card ι) * μ univ <
      μ {x | ∃ z : ι → ℤ, ∑ i, (p x i - g i - z i) ^ 2 < σ ^ 2}}
  -- The tubes `T(g, σ) = p⁻¹ ⋃_z B_σ(g + z)` are measurable.
  have hmeas : ∀ (g : EuclideanSpace ℝ ι) (σ : ℝ),
      MeasurableSet {x | ∃ z : ι → ℤ, ∑ i, (p x i - g i - z i) ^ 2 < σ ^ 2} := by
    intro g σ
    have hopen : IsOpen
        {y : EuclideanSpace ℝ ι | ∃ z : ι → ℤ, ∑ i, (y i - g i - z i) ^ 2 < σ ^ 2} := by
      simp only [ofPred_exists]
      exact isOpen_iUnion fun z => isOpen_lt (continuous_finsetSum _ fun i _ =>
        (((PiLp.continuous_apply 2 _ i).sub continuous_const).sub continuous_const).pow 2)
        continuous_const
    exact hp hopen.measurableSet
  -- If `μ(X) = 0`, no centre is bad.
  rcases eq_or_ne (μ univ) 0 with h0 | h0
  · have hempty : Bad = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun g hg => ?_
      obtain ⟨σ, -, -, hlt⟩ := hg.2
      rw [h0, mul_zero] at hlt
      exact hlt.ne' (measure_mono_null (subset_univ _) h0)
    rw [hempty, measure_empty]
    exact zero_le
  -- Choose a radius `σ_b` for every bad centre `b` (printed (3)).
  have hex : ∀ b : EuclideanSpace ℝ ι, ∃ σ : ℝ, b ∈ Bad → 0 < σ ∧ σ < 1 / 4 ∧
      ENNReal.ofReal (β * σ ^ Fintype.card ι) * μ univ <
        μ {x | ∃ z : ι → ℤ, ∑ i, (p x i - b i - z i) ^ 2 < σ ^ 2} := by
    intro b
    by_cases hb : b ∈ Bad
    · obtain ⟨σ, hσ⟩ := hb.2
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose r hr using hex
  have key := Submission.dgc_pm_vitali_volume_bound ι Bad r (1 / 4) (1 / β)
    (fun b hb => ⟨(hr b hb).1, (hr b hb).2.1.le⟩) ?_
  · rwa [mul_one_div] at key
  -- Packing: a subfamily `u` with disjoint balls `B̄_{σ_b}(b)` has disjoint tubes.
  intro u hu hdisj
  set A : u → Set X := fun b =>
    {x | ∃ z : ι → ℤ, ∑ i, (p x i - (b : EuclideanSpace ℝ ι) i - z i) ^ 2 < r b ^ 2}
  have hAm : ∀ b, MeasurableSet (A b) := fun b => hmeas _ _
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro b b' hne
    exact (Submission.dgc_pm_lattice_tubes_disjoint ι g₀ b b' (r b) (r b') (hu b.2).1 (hu b'.2).1
      (hr b (hu b.2)).1 (hr b (hu b.2)).2.1 (hr b' (hu b'.2)).1 (hr b' (hu b'.2)).2.1
      (hdisj b.2 b'.2 (Subtype.coe_injective.ne hne))).preimage p
  have hApos : ∀ b : u, 0 < μ (A b) := fun b => zero_le.trans_lt (hr b (hu b.2)).2.2
  -- Disjoint sets of positive measure: `u` is countable.
  have hcount : u.Countable := by
    have h : (univ : Set u).Countable :=
      (Measure.countable_meas_pos_of_disjoint_iUnion hAm hAd).mono fun b _ => hApos b
    exact countable_coe_iff.1 (countable_univ_iff.1 h)
  refine ⟨hcount, ?_⟩
  -- Summing (3): `β Σ σ_b^k μ(X) ≤ Σ μ(T(b, σ_b)) ≤ μ(X)`.
  have hsum : (∑' b : u, ENNReal.ofReal (β * r b ^ Fintype.card ι)) * μ univ ≤ 1 * μ univ := by
    rw [← ENNReal.tsum_mul_right, one_mul]
    calc ∑' b : u, ENNReal.ofReal (β * r b ^ Fintype.card ι) * μ univ
        ≤ ∑' b : u, μ (A b) := ENNReal.tsum_le_tsum fun b => (hr b (hu b.2)).2.2.le
      _ ≤ μ (⋃ b, A b) := tsum_meas_le_meas_iUnion_of_disjoint μ hAm hAd
      _ ≤ μ univ := measure_mono (subset_univ _)
  have h1 := (ENNReal.mul_le_mul_iff_left h0 (measure_ne_top μ univ)).1 hsum
  simp_rw [ENNReal.ofReal_mul hβ.le, ENNReal.tsum_mul_left] at h1
  rw [one_div, ENNReal.ofReal_inv_of_pos hβ, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact h1
/-- Fubini bound for the cylinder over a set of centres (corrected (5) in the proof of Simon
Ch. 6, 5.1): for `J ⊆ ι` and any `B ⊆ ℝ^J`,
`L^ι({a ∈ [0,1]^ι : (a_i)_{i ∈ J} ∈ B}) ≤ L^J(B)`.  The set lies in the preimage of
`B × [0,1]^{ι∖J}` under the measure-preserving equivalence `ℝ^ι ≃ ℝ^J × ℝ^{ι∖J}`, and the
product measure of a rectangle of arbitrary sets is the product of the measures. -/
theorem Submission.dgc_cylinder_volume :
    ∀ (ι : Type) [Fintype ι] (J : Finset ι) (B : Set (EuclideanSpace ℝ J)),
      volume {a : EuclideanSpace ℝ ι | (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
        WithLp.toLp 2 (fun i : J => a i) ∈ B} ≤ volume B := by
  intro ι _ J B
  classical
  -- `e : E_ι → ℝ^J × ℝ^{ι∖J}` (coordinates, then restriction to `J` and to `ι∖J`) is a
  -- measure-preserving measurable equivalence.  (`convert` identifies the two `Fintype ↥J`
  -- instances underlying the product measures.)
  let e := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J))
  have he : MeasurePreserving e := by
    convert (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).trans
      (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ∈ J))
  -- The set lies in `e⁻¹(B' × C)`, `B'` the coordinate copy of `B` and `C = [0,1]^{ι∖J}`.
  let B' : Set (J → ℝ) := MeasurableEquiv.toLp 2 (J → ℝ) ⁻¹' B
  let C : Set ({i // i ∉ J} → ℝ) := univ.pi fun _ => Icc 0 1
  have hsub : {a : EuclideanSpace ℝ ι | (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
      WithLp.toLp 2 (fun i : J => a i) ∈ B} ⊆ e ⁻¹' (B' ×ˢ C) :=
    fun a ha => ⟨ha.2, fun i _ => ha.1 i⟩
  -- The two factors: `L^J(B') = L^J(B)` and `L^{ι∖J}(C) = ∏ L¹([0,1]) = 1`.
  have hB' : volume B' = volume B :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp J).symm.measure_preimage_equiv B
  have hC : volume C = 1 := by
    simp only [C, volume_pi_pi, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      Finset.prod_const_one]
  -- Monotonicity and the rectangle formula for product measures.
  calc volume {a : EuclideanSpace ℝ ι | (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧
        WithLp.toLp 2 (fun i : J => a i) ∈ B}
      ≤ volume (e ⁻¹' (B' ×ˢ C)) := measure_mono hsub
    _ = volume B' * volume C := by
      rw [he.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
    _ = volume B := by rw [hB', hC, mul_one]
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
/-- **Continuous forms against a measure representation: the step "by (2.7)" in the proof of
Simon Ch. 6, Lemma 2.15 (p. 137).**  Let `(μ, v)` represent `T` as in (2.7), `W ⊂⊂ U` and
`M_W(T) ≤ B`.  If `ω` is a continuous `n`-form with `tsupport ω ⊆ W` and `|ω(x)| ≤ C` everywhere
(Euclidean coefficient norm), then `⟨ω, v⟩` is `μ`-integrable and `|∫ ⟨ω, v⟩ dμ| ≤ B · C`.
Choose `V` open with `tsupport ω ⊆ V` and `closure V ⊆ W` compact.  The coefficients `v_β` of `v`
are `μ`-integrable on `closure V`, so for every continuous `θ` vanishing off `closure V` with
`|θ| ≤ D`, `⟨θ, v⟩ = ∑_β θ(e_β) v_β` is integrable and `|∫ ⟨θ, v⟩ dμ| ≤ D · G`, where
`G = ∑_β ∫_{closure V} |v_β| dμ`.  For a test form `η` supported in `V` with `|ω - η| ≤ ε`, the
mass bound gives `|∫ ⟨ω, v⟩ dμ| ≤ |T(η)| + ε G ≤ B (C + ε) + ε G`; let `ε → 0`. -/
theorem Submission.cmb_measureRepresentation_continuous_bound : ∀ (P n : ℕ) (U W : Set (Eucl P)), CompactlyContainedOpen W U → ∀ (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → ∀ (B C : ℝ), 0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → tsupport ω ⊆ W → (∀ x, covectorEuclideanNorm (ω x) ≤ C) → Integrable (fun x => v x (ω x)) μ ∧ |∫ x, v x (ω x) ∂μ| ≤ B * C := by
  intro P n U W hWU T μ v hT B C hB hM ω hω hωW hωC
  obtain ⟨hWo, hWc, hWU'⟩ := hWU
  have hWU₀ : W ⊆ U := subset_closure.trans hWU'
  -- Step 1: `tsupport ω` is compact; choose `V` open with `tsupport ω ⊆ V`, `closure V ⊆ W`
  -- compact.
  have hωc : HasCompactSupport ω :=
    hWc.of_isClosed_subset (isClosed_tsupport ω) (hωW.trans subset_closure)
  obtain ⟨V, hVo, hωV, hVW, hVc⟩ :=
    exists_open_between_and_isCompact_closure hωc.isCompact hWo hωW
  have hVU : V ⊆ U := subset_closure.trans (hVW.trans hWU₀)
  -- Step 2: the coefficients `v_β` of `v` are `μ`-integrable on `closure V`.
  have hcoef : ∀ β : SimonMultiIndex n P,
      IntegrableOn (fun x => euclideanNVectorCoordinate (v x) β) (closure V) μ :=
    Submission.cmb_rb_measureRepresentation_integrableOn_coeff P n U W hWo hWU₀ T μ v hT
      (closure V) hVc hVW
  set G : ℝ := ∑ β : SimonMultiIndex n P,
    ∫ x in closure V, |euclideanNVectorCoordinate (v x) β| ∂μ
  have hG : 0 ≤ G := Finset.sum_nonneg fun β _ => integral_nonneg fun x => abs_nonneg _
  -- Step 3: coordinate expansion `v(x)(α) = ∑_β α(e_β) v_β(x)`.
  have hexp : ∀ (x : Eucl P) (α : Covector (Eucl P) n), v x α = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β * euclideanNVectorCoordinate (v x) β := by
    intro x α
    conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P n α]
    simp only [map_sum, map_smul, smul_eq_mul, euclideanNVectorCoordinate]
  -- Step 4: pairings with continuous forms vanishing off `closure V` are integrable, and
  -- `|∫ ⟨θ, v⟩ dμ| ≤ D G` when `|θ| ≤ D`.
  have hpair : ∀ (θ : Eucl P → Covector (Eucl P) n) (D : ℝ), Continuous θ →
      (∀ x, x ∉ closure V → θ x = 0) → (∀ x, covectorEuclideanNorm (θ x) ≤ D) →
      Integrable (fun x => v x (θ x)) μ ∧ |∫ x, v x (θ x) ∂μ| ≤ D * G := by
    intro θ D hθ hθV hθD
    have hfun : (fun x => v x (θ x)) = fun x => ∑ β : SimonMultiIndex n P,
        euclideanCovectorCoordinate (θ x) β * euclideanNVectorCoordinate (v x) β :=
      funext fun x => hexp x (θ x)
    rw [hfun]
    exact Submission.cmb_rb_integral_coeff_pairing_bound P n μ v (closure V)
      isClosed_closure.measurableSet hcoef θ D hθ hθV hθD
  have hωV' : ∀ x, x ∉ closure V → ω x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hωV h))
  refine ⟨(hpair ω C hω hωV' hωC).1, ?_⟩
  -- Step 5: compare with a test form `η` supported in `V`, `|ω - η| ≤ ε`.
  have key : ∀ ε : ℝ, 0 < ε → |∫ x, v x (ω x) ∂μ| ≤ B * (C + ε) + ε * G := by
    intro ε hε
    obtain ⟨η, hηV, hηω⟩ :=
      Submission.cmb_exists_testForm_uniform_approx P n U V ω hVo hVU hω hωc hωV ε hε
    -- `|η| ≤ C + ε`, hence `|T(η)| ≤ B (C + ε)` by the mass bound.
    have hηC : ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x) ≤ C + ε := by
      intro x
      have h := Submission.cmb_rb_covectorEuclideanNorm_add_le P n (ω x)
        (-(ω x - (η : DifferentialForm (Eucl P) n) x))
      have heq : ω x + -(ω x - (η : DifferentialForm (Eucl P) n) x) =
          (η : DifferentialForm (Eucl P) n) x := by abel
      rw [heq, covectorEuclideanNorm_neg] at h
      linarith [hωC x, hηω x]
    have hTη : |T η| ≤ B * (C + ε) :=
      Submission.cmb_abs_apply_le_of_massOn_le P n U W T η B (C + ε) hB hM
        (hηV.trans (subset_closure.trans hVW)) hηC
    -- `θ = ω - η` is continuous, vanishes off `closure V` and `|θ| ≤ ε`.
    have hηc : Continuous (η : DifferentialForm (Eucl P) n) := ContDiff.continuous η.property.1.1
    have hθV : ∀ x, x ∉ closure V → ω x - (η : DifferentialForm (Eucl P) n) x = 0 := by
      intro x hx
      rw [hωV' x hx, image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hηV h)),
        sub_zero]
    obtain ⟨hθi, hθb⟩ :
        Integrable (fun x => v x (ω x - (η : DifferentialForm (Eucl P) n) x)) μ ∧
          |∫ x, v x (ω x - (η : DifferentialForm (Eucl P) n) x) ∂μ| ≤ ε * G :=
      hpair (fun x => ω x - (η : DifferentialForm (Eucl P) n) x) ε (hω.sub hηc) hθV hηω
    -- `∫ ⟨ω, v⟩ dμ = T(η) + ∫ ⟨ω - η, v⟩ dμ`.
    obtain ⟨hηi, hηT⟩ := hT η
    have hsplit : ∫ x, v x (ω x) ∂μ =
        T η + ∫ x, v x (ω x - (η : DifferentialForm (Eucl P) n) x) ∂μ := by
      rw [hηT, ← integral_add hηi hθi]
      congr 1
      funext x
      rw [← map_add, add_sub_cancel]
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hTη hθb)
  -- Step 6: let `ε → 0`, with `ε = ε₀ / (B + G + 1)`.
  refine le_of_forall_pos_le_add fun ε₀ hε₀ => ?_
  have hBG : 0 < B + G + 1 := by linarith
  have hε : 0 < ε₀ / (B + G + 1) := div_pos hε₀ hBG
  have hεε₀ : ε₀ / (B + G + 1) * (B + G + 1) = ε₀ := div_mul_cancel₀ ε₀ hBG.ne'
  have h := key _ hε
  nlinarith
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
/-- **`L¹` density of continuous compactly supported maps for a finite measure on `ℝ^N`.**  For a
finite Borel measure `ν` on `ℝ^N` and `f ∈ L¹(ν)` with values in a real normed space `E`, every
`ε ≠ 0` admits a continuous compactly supported `g ∈ L¹(ν)` with `‖f - g‖_{L¹(ν)} ≤ ε` (the case
`p = 1` of Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, whose file is not imported
here; its proof is reproduced).  Urysohn's lemma and outer regularity approximate `c • 1_s` (`s`
closed, `s ⊆ u` open, `ν s < ∞`) by a continuous `L¹` map supported in `u`; inner regularity by
compact closed sets treats `c • 1_t` for measurable `t` with `ν t < ∞`; and `MemLp.induction_dense`
(density of simple functions) extends this to all of `L¹(ν)`, the class being closed under `+`. -/
theorem Submission.imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le : ∀ (N : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure (Eucl N)) [IsFiniteMeasure ν] (f : Eucl N → E), MemLp f 1 ν → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ g : Eucl N → E, HasCompactSupport g ∧ eLpNorm (f - g) 1 ν ≤ ε ∧ Continuous g ∧ MemLp g 1 ν := by
  intro N E _ _ ν _ f hf ε hε
  -- Urysohn approximation of `c • 1_s` for `s` closed, `s ⊆ u` open, `ν s < ∞` (Mathlib's
  -- `exists_continuous_eLpNorm_sub_le_of_closed` with `p = 1`).
  have hury : ∀ {s u : Set (Eucl N)}, IsClosed s → IsOpen u → s ⊆ u → ν s ≠ ∞ →
      ∀ (c : E) {δ : ℝ≥0∞}, δ ≠ 0 → ∃ h : Eucl N → E,
        Continuous h ∧ eLpNorm (fun x => h x - s.indicator (fun _y => c) x) 1 ν ≤ δ ∧
          (∀ x, ‖h x‖ ≤ ‖c‖) ∧ Function.support h ⊆ u ∧ MemLp h 1 ν := by
    intro s u s_closed u_open hsu hs c δ hδ
    -- `‖c • 1_r‖₁ ≤ δ` whenever `ν r ≤ η`.
    obtain ⟨η, η_pos, hη⟩ :
        ∃ η : ℝ≥0, 0 < η ∧ ∀ r : Set (Eucl N), ν r ≤ η → NullMeasurableSet r ν →
            eLpNorm (r.indicator fun _x => c) 1 ν ≤ δ :=
      exists_eLpNorm_indicator_le ENNReal.one_ne_top c hδ
    have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
    -- Outer regularity: an open `V ⊇ s` with `ν (V \ s) < η`.
    obtain ⟨V, sV, V_open, h'V, hV⟩ :
        ∃ (V : Set (Eucl N)), V ⊇ s ∧ IsOpen V ∧ ν V < ∞ ∧ ν (V \ s) < η :=
      s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
    let v := u ∩ V
    have hsv : s ⊆ v := subset_inter hsu sV
    have hνv : ν v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
    -- Urysohn's lemma: `φ = 0` off `v`, `φ = 1` on `s`, `0 ≤ φ ≤ 1`.
    obtain ⟨φ, hφv, hφs, hφ_range⟩ :=
      exists_continuous_zero_one_of_isClosed (u_open.inter V_open).isClosed_compl s_closed
        (disjoint_compl_left_iff.2 hsv)
    have φ_norm : ∀ x, ‖φ x‖ = φ x := fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ_range x).1]
    have φc_bd0 : ∀ x, ‖φ x • c‖ ≤ ‖c‖ := by
      intro x
      simp only [norm_smul, φ_norm x]
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact (hφ_range x).2
    -- Pointwise `‖φ c - c 1_s‖ ≤ ‖c 1_{v \ s}‖`.
    have φc_bd :
        ∀ x, ‖φ x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
      intro x
      by_cases hv : x ∈ v
      · rw [← Set.sdiff_union_of_subset hsv] at hv
        rcases hv with hxvs | hxs
        · simpa only [hxvs.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hxvs,
            Set.indicator_of_mem] using φc_bd0 x
        · simp [hφs hxs, hxs]
      · simp [hφv hv, show x ∉ s from fun h => hv (hsv h)]
    have φc_support : (Function.support fun x : Eucl N => φ x • c) ⊆ v := by
      refine Function.support_subset_iff'.2 fun x hx => ?_
      simp only [hφv hx, Pi.zero_apply, zero_smul]
    -- `φ c ∈ L¹(ν)`: `φ ≤ 1_v` and `ν v < ∞`.
    have φc_mem : MemLp (fun x => φ x • c) 1 ν := by
      refine MemLp.smul ?_ (memLp_top_const (μ := ν) c) (p := 1) (q := ∞) (r := 1)
      have hv : MeasurableSet v := u_open.measurableSet.inter V_open.measurableSet
      have : eLpNorm (v.indicator fun _x => (1 : ℝ)) 1 ν < ∞ :=
        (eLpNorm_indicator_const_le _ _ hv.nullMeasurableSet).trans_lt <| by
          simp [lt_top_iff_ne_top, hνv.ne]
      refine (eLpNorm_mono φ.continuous.aestronglyMeasurable fun x => ?_).trans_lt this
      by_cases hx : x ∈ v
      · simp only [hx, abs_of_nonneg (hφ_range x).1, (hφ_range x).2, Real.norm_eq_abs,
          indicator_of_mem, CStarRing.norm_one]
      · simp only [hφv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
    refine ⟨fun x ↦ φ x • c, by fun_prop,
      (eLpNorm_mono (φc_mem.aestronglyMeasurable.sub
        (aestronglyMeasurable_const.indicator s_closed.measurableSet)) φc_bd).trans ?_, φc_bd0,
        φc_support.trans inter_subset_left, φc_mem⟩
    exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)
      ((u_open.measurableSet.inter V_open.measurableSet).diff
        s_closed.measurableSet).nullMeasurableSet
  suffices hex : ∃ g : Eucl N → E,
      eLpNorm (f - g) 1 ν ≤ ε ∧ Continuous g ∧ MemLp g 1 ν ∧ HasCompactSupport g by
    rcases hex with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  -- Density of simple functions: approximate indicator-constants, and close under addition.
  apply hf.induction_dense ENNReal.one_ne_top _ _ _ hε
  rotate_left
  · rintro g₁ g₂ ⟨g₁_cont, g₁_mem, hg₁⟩ ⟨g₂_cont, g₂_mem, hg₂⟩
    exact ⟨g₁_cont.add g₂_cont, g₁_mem.add g₂_mem, hg₁.add hg₂⟩
  intro c t ht htν δ hδ
  rcases exists_Lp_half E ν 1 hδ with ⟨δ', δ'pos, hδ'⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ r : Set (Eucl N), ν r ≤ η → NullMeasurableSet r ν →
          eLpNorm (r.indicator fun _x => c) 1 ν ≤ δ' :=
    exists_eLpNorm_indicator_le ENNReal.one_ne_top c δ'pos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  -- Inner regularity: a compact closed `s ⊆ t` with `ν (t \ s) < η`.
  obtain ⟨s, st, s_compact, s_closed, νs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ ν (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htν.ne hη_pos'.ne'
  have hsν : ν s < ∞ := (measure_mono st).trans_lt htν
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) 1 ν ≤ δ' := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ νs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  -- A compact `k` with `s ⊆ interior k`, and the Urysohn approximation for `(s, interior k)`.
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set (Eucl N), IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases hury s_closed isOpen_interior sk hsν.ne c δ'pos.ne'
    with ⟨h, h_cont, I2, _h_bound, h_support, h_mem⟩
  have I3 : eLpNorm (h - t.indicator fun _y => c) 1 ν ≤ δ := by
    convert (hδ' _ _ I2 I1).le using 2
    ext x
    simp
  refine ⟨h, I3, h_cont, h_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (h_support hx)

/-- **Polar field (Simon Ch. 6, 2.7–2.8; Steps 3, 5 and 6 of the mass lower bound).**  If `g` is
`μ`-integrable on `B = B_R(0)` with values in a real inner product space, then for every `ε > 0`
there is a continuous `F` with `tsupport F ⊆ B` and `‖F‖ ≤ 1` such that `⟨F, g⟩` is
`μ`-integrable and `∫_B ‖g‖ dμ ≤ ∫ ⟨F, g⟩ dμ + ε`.  With `ρ = ‖g‖`, the polar field `u = g / ρ`
and the finite measure `ν = ρ μ⌞B`, approximate `u` in `L¹(ν)` by a continuous compactly
supported `g₀` (sibling `l1_density`) and take `F = χ · π(g₀)`, where `χ` cuts off near `∂B` and
`π(a) = a / max(1, ‖a‖)` is the radial retraction onto the closed unit ball. -/
theorem Submission.imc_mlb_exists_unit_field_integral_ge : ∀ (N : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure (Eucl N)) (R : ℝ) (g : Eucl N → E), IntegrableOn g (ball (0 : Eucl N) R) μ → ∀ ε : ℝ, 0 < ε → ∃ F : Eucl N → E, Continuous F ∧ tsupport F ⊆ ball (0 : Eucl N) R ∧ (∀ x, ‖F x‖ ≤ 1) ∧ Integrable (fun x => inner ℝ (F x) (g x)) μ ∧ ∫ x in ball (0 : Eucl N) R, ‖g x‖ ∂μ ≤ ∫ x, inner ℝ (F x) (g x) ∂μ + ε := by
  intro N E _ _ μ R g hg ε hε
  -- Step 0: a continuous `F` with `‖F‖ ≤ 1` vanishing off `B` pairs integrably with `g`, and
  -- `∫ ⟨F, g⟩ dμ = ∫_B ⟨F, g⟩ dμ`.
  have hpair : ∀ F : Eucl N → E, Continuous F → tsupport F ⊆ ball (0 : Eucl N) R →
      (∀ x, ‖F x‖ ≤ 1) → Integrable (fun x => inner ℝ (F x) (g x)) μ ∧
        ∫ x, inner ℝ (F x) (g x) ∂μ = ∫ x in ball (0 : Eucl N) R, inner ℝ (F x) (g x) ∂μ := by
    intro F hFc hFs hF1
    have hzero : ∀ x, x ∉ ball (0 : Eucl N) R → inner ℝ (F x) (g x) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (hFs h), inner_zero_left]
    have hint : IntegrableOn (fun x => inner ℝ (F x) (g x)) (ball (0 : Eucl N) R) μ :=
      (Integrable.norm hg).mono' (continuous_inner.comp_aestronglyMeasurable
        (hFc.aestronglyMeasurable.prodMk hg.aestronglyMeasurable))
        (Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hF1 x)))
    exact ⟨(integrableOn_iff_integrable_of_support_subset fun x hx =>
      not_not.mp fun h => hx (hzero x h)).mp hint,
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm⟩
  -- Step 1: if `R ≤ 0` then `B = ∅` and `F = 0` works.
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨0, continuous_const, by rw [tsupport_zero]; exact empty_subset _, fun x => by simp,
      by simp, ?_⟩
    rw [ball_eq_empty.mpr hR]
    simp [hε.le]
  -- Step 2: a strongly measurable `g' = g` `μ⌞B`-a.e.; `ρ = ‖g'‖` and `u = ρ⁻¹ g'`, so that
  -- `‖u‖ ≤ 1`, `‖u‖ = 1` where `g' ≠ 0`, and `g' = ρ u`.
  obtain ⟨g', hg'm, hgg'⟩ := hg.aestronglyMeasurable
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Eucl N → ℝ, ρ = fun x => ‖g' x‖ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Eucl N → E, u = fun x => (ρ x)⁻¹ • g' x := ⟨_, rfl⟩
  have hρx : ∀ x, ρ x = ‖g' x‖ := fun x => by rw [hρ]
  have hux : ∀ x, u x = (ρ x)⁻¹ • g' x := fun x => by rw [hu]
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => by rw [hρx]; exact norm_nonneg _
  have hρm : StronglyMeasurable ρ := by rw [hρ]; exact hg'm.norm
  have hum : StronglyMeasurable u := by
    rw [hu]; exact hρm.measurable.inv.stronglyMeasurable.smul hg'm
  have hgρu : ∀ x, g' x = ρ x • u x := by
    intro x
    rw [hux, smul_smul]
    rcases eq_or_ne (g' x) 0 with h | h
    · rw [h, smul_zero]
    · rw [mul_inv_cancel₀ (by rw [hρx]; exact norm_ne_zero_iff.mpr h), one_smul]
  have hu1 : ∀ x, ‖u x‖ ≤ 1 := by
    intro x
    rw [hux, norm_smul, norm_inv, Real.norm_of_nonneg (hρ0 x), hρx]
    rcases eq_or_ne ‖g' x‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hu1' : ∀ x, g' x ≠ 0 → ‖u x‖ = 1 := by
    intro x hx
    rw [hux, norm_smul, norm_inv, Real.norm_of_nonneg (hρ0 x), hρx,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hgρ : (fun x => ‖g x‖) =ᵐ[μ.restrict (ball (0 : Eucl N) R)] ρ :=
    hgg'.mono fun x hx => by simp only [hρx, hx]
  have hρi : Integrable ρ (μ.restrict (ball (0 : Eucl N) R)) := (Integrable.norm hg).congr hgρ
  have hρ_eq : ∫ x in ball (0 : Eucl N) R, ‖g x‖ ∂μ = ∫ x in ball (0 : Eucl N) R, ρ x ∂μ :=
    integral_congr_ae hgρ
  -- Step 3: the finite measure `ν = ρ μ⌞B`, with `ν(S) = ∫_S ρ dμ` for measurable `S ⊆ B`;
  -- `u ∈ L¹(ν)`.
  have hρmeas : Measurable fun x => ENNReal.ofReal (ρ x) := hρm.measurable.ennreal_ofReal
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Eucl N),
      ν = (μ.restrict (ball (0 : Eucl N) R)).withDensity fun x => ENNReal.ofReal (ρ x) :=
    ⟨_, rfl⟩
  have : IsFiniteMeasure ν := by
    rw [hν]
    refine isFiniteMeasure_withDensity ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0)]
    exact ENNReal.ofReal_ne_top
  have hνS : ∀ S, MeasurableSet S → S ⊆ ball (0 : Eucl N) R →
      ν S = ENNReal.ofReal (∫ x in S, ρ x ∂μ) := by
    intro S hS hSB
    rw [hν, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.mpr hSB,
      ofReal_integral_eq_lintegral_ofReal (IntegrableOn.mono_set hρi hSB)
        (Eventually.of_forall hρ0)]
  have huL1 : MemLp u 1 ν := MemLp.of_bound hum.aestronglyMeasurable 1 (Eventually.of_forall hu1)
  -- Step 4: continuity from above of `ν` gives `0 < R' < R` with `ν(B ∖ B̄_{R'}) < ε/4`.
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  obtain ⟨R', hR'0, hR'R, hνR'⟩ : ∃ R', 0 < R' ∧ R' < R ∧
      ν (ball (0 : Eucl N) R \ closedBall 0 R') < ENNReal.ofReal (ε / 4) := by
    have hanti : Antitone fun n : ℕ => ball (0 : Eucl N) R \ closedBall 0 (R - R / (n + 2)) := by
      intro m n hmn
      refine sdiff_subset_sdiff_right (closedBall_subset_closedBall ?_)
      have : R / (n + 2) ≤ R / (m + 2) := div_le_div_of_nonneg_left hR.le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hmn 2)
      linarith
    have hempty : (⋂ n : ℕ, ball (0 : Eucl N) R \ closedBall 0 (R - R / (n + 2))) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      rw [mem_iInter] at hx
      have hxR : ‖x‖ < R := mem_ball_zero_iff.mp (hx 0).1
      obtain ⟨n, hn⟩ := exists_nat_gt (R / (R - ‖x‖))
      have hpos : 0 < R - ‖x‖ := sub_pos.mpr hxR
      have hlt : R / (n + 2) < R - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn
        nlinarith
      exact (hx n).2 (mem_closedBall_zero_iff.mpr (by linarith))
    have htend := tendsto_measure_iInter_atTop (μ := ν)
      (fun n => (measurableSet_ball.diff measurableSet_closedBall).nullMeasurableSet) hanti
      ⟨0, measure_ne_top ν _⟩
    rw [hempty, measure_empty] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε4))).exists
    refine ⟨R - R / (n + 2), ?_, ?_, hn⟩
    · have : R / (n + 2) < R := div_lt_self hR (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
      linarith
    · have : 0 < R / (n + 2) := by positivity
      linarith
  -- Step 5 (sibling `l1_density`): a continuous compactly supported `g₀` with
  -- `∫⁻_B ρ ‖g₀ - u‖ dμ = ‖u - g₀‖_{L¹(ν)} ≤ ε/4`; `g₀` is bounded.
  obtain ⟨g₀, hg₀s, hg₀L1, hg₀c, -⟩ :=
    Submission.imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le N E ν u huL1
      (ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.mpr hε4).ne'
  obtain ⟨C₀, hC₀⟩ := hg₀c.bounded_above_of_compact_support hg₀s
  have h51 : ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (ρ x * ‖g₀ x - u x‖) ∂μ ≤
      ENNReal.ofReal (ε / 4) :=
    calc ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (ρ x * ‖g₀ x - u x‖) ∂μ
        = ∫⁻ x in ball (0 : Eucl N) R,
            ((fun x => ENNReal.ofReal (ρ x)) * fun x => ‖(u - g₀) x‖ₑ) x ∂μ := by
          refine lintegral_congr fun x => ?_
          show ENNReal.ofReal (ρ x * ‖g₀ x - u x‖) = ENNReal.ofReal (ρ x) * ‖u x - g₀ x‖ₑ
          rw [ENNReal.ofReal_mul (hρ0 x), ofReal_norm, enorm_sub_rev]
      _ = ∫⁻ x, ‖(u - g₀) x‖ₑ ∂ν := by
          rw [hν, lintegral_withDensity_eq_lintegral_mul _ hρmeas
            (hum.sub hg₀c.stronglyMeasurable).enorm]
      _ ≤ eLpNorm (u - g₀) 1 ν := lintegral_enorm_le_eLpNorm_one
      _ ≤ ENNReal.ofReal (ε / 4) := hg₀L1
  -- Step 6: the cut-off `χ`, equal to `1` on `B̄_{R'}` and to `0` off `B_{R''}`,
  -- `R'' = (R + R')/2`; `tsupport χ ⊆ B̄_{R''} ⊆ B`.
  obtain ⟨R'', hR''⟩ : ∃ R'' : ℝ, R'' = (R + R') / 2 := ⟨_, rfl⟩
  have hR'R'' : R' < R'' := by rw [hR'']; linarith
  have hR''R : R'' < R := by rw [hR'']; linarith
  obtain ⟨χ, hχ⟩ : ∃ χ : Eucl N → ℝ, χ = fun x => min 1 (max 0 ((R'' - ‖x‖) / (R'' - R'))) :=
    ⟨_, rfl⟩
  have hχx : ∀ x, χ x = min 1 (max 0 ((R'' - ‖x‖) / (R'' - R'))) := fun x => by rw [hχ]
  have hχc : Continuous χ := by
    rw [hχ]
    exact continuous_const.min (continuous_const.max
      ((continuous_const.sub continuous_norm).div_const _))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => by rw [hχx]; exact le_min zero_le_one (le_max_left _ _)
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => by rw [hχx]; exact min_le_left _ _
  have hχin : ∀ x, ‖x‖ ≤ R' → χ x = 1 := by
    intro x hx
    rw [hχx, min_eq_left]
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hχout : ∀ x, R'' ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    rw [hχx, max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)),
      min_eq_right zero_le_one]
  have hχs : tsupport χ ⊆ ball (0 : Eucl N) R := by
    have hsupp : Function.support χ ⊆ ball (0 : Eucl N) R'' := fun x hx =>
      mem_ball_zero_iff.mpr (not_le.mp fun h => hx (hχout x h))
    exact (closure_mono hsupp).trans
      (closure_ball_subset_closedBall.trans (closedBall_subset_ball hR''R))
  -- Step 7: the radial retraction `pr a = a / max(1, ‖a‖)`: continuous, `‖pr a‖ ≤ 1`, and
  -- `‖pr a - b‖ ≤ 2 ‖a - b‖` whenever `‖b‖ ≤ 1`.
  have hmax : ∀ a : E, 0 < max 1 ‖a‖ := fun a => zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨pr, hpr⟩ : ∃ pr : E → E, pr = fun a => (max 1 ‖a‖)⁻¹ • a := ⟨_, rfl⟩
  have hprx : ∀ a, pr a = (max 1 ‖a‖)⁻¹ • a := fun a => by rw [hpr]
  have hprc : Continuous pr := by
    rw [hpr]
    exact ((continuous_const.max continuous_norm).inv₀ fun a => (hmax a).ne').smul continuous_id
  have hpr1 : ∀ a, ‖pr a‖ ≤ 1 := by
    intro a
    rw [hprx, norm_smul, norm_inv, Real.norm_of_nonneg (hmax a).le, inv_mul_le_iff₀ (hmax a),
      mul_one]
    exact le_max_right _ _
  have hpr2 : ∀ a b : E, ‖b‖ ≤ 1 → ‖pr a - b‖ ≤ 2 * ‖a - b‖ := by
    intro a b hb
    rcases le_or_gt ‖a‖ 1 with ha | ha
    · rw [hprx, max_eq_left ha, inv_one, one_smul]
      linarith [norm_nonneg (a - b)]
    · have ha0 : 0 < ‖a‖ := zero_lt_one.trans ha
      have h1 : ‖pr a - a‖ = ‖a‖ - 1 := by
        rw [hprx, max_eq_right ha.le,
          show ‖a‖⁻¹ • a - a = (‖a‖⁻¹ - 1) • a by rw [sub_smul, one_smul], norm_smul,
          Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (inv_le_one_of_one_le₀ ha.le)),
          neg_sub, sub_mul, one_mul, inv_mul_cancel₀ ha0.ne']
      have h2 : ‖a‖ - 1 ≤ ‖a - b‖ := by linarith [norm_sub_norm_le a b]
      calc ‖pr a - b‖ = ‖(pr a - a) + (a - b)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖pr a - a‖ + ‖a - b‖ := norm_add_le _ _
        _ ≤ 2 * ‖a - b‖ := by linarith
  -- Step 8: the competitor `F = χ · pr ∘ g₀`.
  obtain ⟨F, hF⟩ : ∃ F : Eucl N → E, F = fun x => χ x • pr (g₀ x) := ⟨_, rfl⟩
  have hFx : ∀ x, F x = χ x • pr (g₀ x) := fun x => by rw [hF]
  have hFc : Continuous F := by rw [hF]; exact hχc.smul (hprc.comp hg₀c)
  have hFs : tsupport F ⊆ ball (0 : Eucl N) R := by
    rw [hF]; exact (tsupport_smul_subset_left _ _).trans hχs
  have hF1 : ∀ x, ‖F x‖ ≤ 1 := by
    intro x
    rw [hFx, norm_smul, Real.norm_of_nonneg (hχ0 x)]
    nlinarith [hχ0 x, hχ1 x, hpr1 (g₀ x), norm_nonneg (pr (g₀ x))]
  obtain ⟨hFi, hFeq⟩ := hpair F hFc hFs hF1
  refine ⟨F, hFc, hFs, hF1, hFi, ?_⟩
  -- Step 9: pointwise, `⟨F, g'⟩ = χρ⟨pr g₀, u⟩ ≥ ρ - ρ(1 - χ) - 2ρ‖g₀ - u‖`.
  have h9 : ∀ x, ρ x - ρ x * (1 - χ x) - 2 * (ρ x * ‖g₀ x - u x‖) ≤ inner ℝ (F x) (g' x) := by
    intro x
    have hinner : inner ℝ (F x) (g' x) = χ x * ρ x * inner ℝ (pr (g₀ x)) (u x) := by
      rw [hFx, hgρu x, real_inner_smul_left, real_inner_smul_right]; ring
    rw [hinner]
    rcases eq_or_ne (g' x) 0 with h0 | h0
    · have : ρ x = 0 := by rw [hρx, h0, norm_zero]
      rw [this]; simp
    · have hux1 : ‖u x‖ = 1 := hu1' x h0
      have hlow : 1 - 2 * ‖g₀ x - u x‖ ≤ inner ℝ (pr (g₀ x)) (u x) := by
        have e1 : inner ℝ (pr (g₀ x)) (u x) = 1 + inner ℝ (pr (g₀ x) - u x) (u x) := by
          rw [inner_sub_left, real_inner_self_eq_norm_sq, hux1]; ring
        have e2 := abs_real_inner_le_norm (pr (g₀ x) - u x) (u x)
        have e3 := hpr2 (g₀ x) (u x) (hu1 x)
        rw [hux1, mul_one] at e2
        rw [e1]
        linarith [neg_abs_le (inner ℝ (pr (g₀ x) - u x) (u x))]
      have hd0 : 0 ≤ ‖g₀ x - u x‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hlow (mul_nonneg (hχ0 x) (hρ0 x)),
        mul_nonneg (sub_nonneg.mpr (hχ1 x)) (mul_nonneg (hρ0 x) hd0)]
  -- Step 10: integrability on `B` of `ρ(1 - χ)`, `ρ‖g₀ - u‖` and `⟨F, g'⟩`.
  have hi2 : Integrable (fun x => ρ x * (1 - χ x)) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.mul_bdd (c := 1) (continuous_const.sub hχc).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sub_nonneg.mpr (hχ1 x))]; linarith [hχ0 x])
  have hi3 : Integrable (fun x => ρ x * ‖g₀ x - u x‖) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.mul_bdd (c := C₀ + 1) (hg₀c.stronglyMeasurable.sub hum).norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hC₀ x) (hu1 x)))
  have hi4 : Integrable (fun x => inner ℝ (F x) (g' x)) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.mono' (continuous_inner.comp_aestronglyMeasurable
      (hFc.aestronglyMeasurable.prodMk hg'm.aestronglyMeasurable))
      (Eventually.of_forall fun x => (norm_inner_le_norm _ _).trans (by
        rw [hρx]; exact mul_le_of_le_one_left (norm_nonneg _) (hF1 x)))
  -- Step 11(a): `∫_B ρ(1 - χ) dμ ≤ ∫_{B ∖ B̄_{R'}} ρ dμ < ε/4`.
  have hAm : MeasurableSet (ball (0 : Eucl N) R \ closedBall 0 R') :=
    measurableSet_ball.diff measurableSet_closedBall
  have h11a : ∫ x in ball (0 : Eucl N) R, ρ x * (1 - χ x) ∂μ ≤ ε / 4 := by
    have hle : ∫ x in ball (0 : Eucl N) R, ρ x * (1 - χ x) ∂μ ≤
        ∫ x in ball (0 : Eucl N) R,
          (ball (0 : Eucl N) R \ closedBall 0 R').indicator ρ x ∂μ := by
      refine setIntegral_mono_on hi2 (hρi.indicator hAm) measurableSet_ball fun x hx => ?_
      by_cases hxA : x ∈ ball (0 : Eucl N) R \ closedBall 0 R'
      · rw [indicator_of_mem hxA]
        nlinarith [hρ0 x, hχ0 x]
      · have hxR' : ‖x‖ ≤ R' := by
          by_contra h
          exact hxA ⟨hx, fun h' => h (mem_closedBall_zero_iff.mp h')⟩
        rw [indicator_of_notMem hxA, hχin x hxR', sub_self, mul_zero]
    have heq : ∫ x in ball (0 : Eucl N) R,
          (ball (0 : Eucl N) R \ closedBall 0 R').indicator ρ x ∂μ =
        ∫ x in ball (0 : Eucl N) R \ closedBall 0 R', ρ x ∂μ := by
      rw [setIntegral_indicator hAm, inter_eq_right.mpr sdiff_subset]
    have hlt : ∫ x in ball (0 : Eucl N) R \ closedBall 0 R', ρ x ∂μ < ε / 4 := by
      rw [← ENNReal.ofReal_lt_ofReal_iff hε4, ← hνS _ hAm sdiff_subset]
      exact hνR'
    linarith
  -- Step 11(b): `∫_B ρ‖g₀ - u‖ dμ ≤ ε/4` by (5.1).
  have h11b : ∫ x in ball (0 : Eucl N) R, ρ x * ‖g₀ x - u x‖ ∂μ ≤ ε / 4 := by
    rw [← ENNReal.ofReal_le_ofReal_iff hε4.le, ofReal_integral_eq_lintegral_ofReal hi3
      (Eventually.of_forall fun x => mul_nonneg (hρ0 x) (norm_nonneg _))]
    exact h51
  -- Step 12: integrate the pointwise estimate over `B`.
  have hiA : Integrable (fun x => ρ x - ρ x * (1 - χ x)) (μ.restrict (ball (0 : Eucl N) R)) :=
    hρi.sub hi2
  have hiB : Integrable (fun x => ρ x - ρ x * (1 - χ x) - 2 * (ρ x * ‖g₀ x - u x‖))
      (μ.restrict (ball (0 : Eucl N) R)) := hiA.sub (hi3.const_mul 2)
  have h12 := integral_mono hiB hi4 h9
  rw [integral_sub hiA (hi3.const_mul 2), integral_sub hρi hi2, integral_const_mul] at h12
  have hFg : ∫ x in ball (0 : Eucl N) R, inner ℝ (F x) (g x) ∂μ =
      ∫ x in ball (0 : Eucl N) R, inner ℝ (F x) (g' x) ∂μ :=
    integral_congr_ae (hgg'.mono fun x hx => by simp only [hx])
  rw [hρ_eq, hFeq, hFg]
  linarith
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
/-- **Local integrability of `⟨c, v⟩` from test forms (Simon Ch. 6, (2.7), p. 136).**  If
`⟨ω, v⟩` is `μ`-integrable for every test form `ω ∈ 𝒟ⁿ(U)`, then `⟨c, v⟩` is `μ`-integrable on
every compact `K ⊆ U`, for every constant `n`-covector `c`.  With `cthickening δ K ⊆ U` and
`r = δ / 2`, the smooth Urysohn lemma gives a smooth `χ` with `χ = 0` off `thickening r K` and
`χ = 1` on `K`; its support lies in the compact `cthickening r K ⊆ U`, so `ω_K = χ c` is a test
form on `U`, and `⟨ω_K, v⟩ = χ ⟨c, v⟩` agrees with `⟨c, v⟩` on the closed set `K`. -/
theorem Submission.polyhedral_approx_rt_integrableOn_apply : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), (∀ ω : TestFormOn U n, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) n) x)) μ) → ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∀ c : Covector (Eucl P) n, IntegrableOn (fun x => v x c) K μ := by
  intro P n U hU μ v hv K hK hKU c
  -- Step 1: a radius `r = δ / 2 > 0` with `cthickening r K ⊆ cthickening δ K ⊆ U`.
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hr : 0 < δ / 2 := half_pos hδ
  have hrU : cthickening (δ / 2) K ⊆ U := (cthickening_mono (half_le_self hδ.le) K).trans hδU
  -- Step 2: smooth Urysohn for the disjoint closed sets `(thickening r K)ᶜ` and `K`.
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ (Eucl P)) (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := δ / 2) (E := K)).isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.mpr (self_subset_thickening hr K))
  have hχd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := contMDiff_iff_contDiff.mp χ.contMDiff
  -- Step 3: `tsupport χ ⊆ cthickening r K ⊆ U`, a compact set, so `χ` has compact support.
  have hχs : Function.support χ ⊆ thickening (δ / 2) K := fun x hx => by
    by_contra h
    exact hx (hχ0 h)
  have hχt : tsupport χ ⊆ cthickening (δ / 2) K :=
    (closure_mono hχs).trans (closure_thickening_subset_cthickening _ _)
  have hχc : HasCompactSupport χ := hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hχt
  -- Step 4: `ω_K = χ c` is a test form on `U`.
  let ω : DifferentialForm (Eucl P) n := fun x => χ x • c
  have hω : ω ∈ TestFormOn U n :=
    ⟨⟨hχd.smul contDiff_const, hχc.smul_right (f' := fun _ => c)⟩,
      (tsupport_smul_subset_left (fun x => χ x) fun _ => c).trans (hχt.trans hrU)⟩
  -- Step 5: by linearity of `v x`, `x ↦ v x (ω_K x) = χ x * v x c` is `μ`-integrable.
  have h5 : Integrable (fun x => χ x * v x c) μ := by
    simpa [ω, map_smul, smul_eq_mul] using hv ⟨ω, hω⟩
  -- Step 6: `χ = 1` on the closed, hence measurable, set `K`.
  refine (h5.integrableOn (s := K)).congr_fun (fun x hx => ?_) hK.isClosed.measurableSet
  simp [hχ1 hx]
/-- **Local integrability of `θ ⟨c, ξ⟩` for `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  If
`(M, θ, ξ)` is a rectifiable triple in `U`, then `x ↦ θ(x) ⟨c, ξ(x)⟩` is `Hⁿ⌞M`-integrable on
every compact `K ⊆ U`, for every `n`-covector `c`.  For orthonormal `τ`,
`‖±τ₁ ∧ ⋯ ∧ τₙ‖ ≤ ∏ᵢ ‖τᵢ‖ = 1`, so `|⟨c, ξ⟩| ≤ ‖c‖` `Hⁿ⌞M`-a.e.; `(Hⁿ⌞M)⌞K = Hⁿ⌞(M ∩ K)`, on
which `θ` is integrable, and an integrable function times an a.e.-bounded one is integrable. -/
theorem Submission.polyhedral_approx_rt_tau_integrableOn : ∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∀ c : Covector (Eucl P) n, IntegrableOn (fun x => θ x * ξ x c) K ((μHE[n] : Measure (Eucl P)).restrict M) := by
  intro P n U M θ ξ hT K hK hKU c
  -- Step 1: `‖simpleNVector τ‖ ≤ ∏ᵢ ‖τᵢ‖ = 1` for orthonormal `τ` (the `mkContinuous` bound).
  have hunit : ∀ τ : Fin n → Eucl P, Orthonormal ℝ τ → ‖simpleNVector τ‖ ≤ 1 := by
    intro τ hτ
    have h1 : ‖simpleNVector τ‖ ≤ ∏ i, ‖τ i‖ :=
      LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun i _ => norm_nonneg _) _
    simpa [hτ.norm_eq_one] using h1
  -- Step 2: `ξ = ±simpleNVector τ` gives `|ξ(x)(c)| ≤ ‖c‖` for `Hⁿ⌞M`-a.e. `x`.
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x c‖ ≤ ‖c‖ := by
    filter_upwards [hT.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hs : ‖simpleNVector τ c‖ ≤ ‖c‖ :=
      calc ‖simpleNVector τ c‖ ≤ ‖simpleNVector τ‖ * ‖c‖ := (simpleNVector τ).le_opNorm c
        _ ≤ 1 * ‖c‖ := by gcongr; exact hunit τ hτ
        _ = ‖c‖ := one_mul _
    rcases hξ with h | h
    · rw [h]; exact hs
    · rw [h, neg_apply, norm_neg]; exact hs
  -- Step 3: `K` is closed, so `(Hⁿ⌞M)⌞K = Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`.
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [IntegrableOn, Measure.restrict_restrict hKm, Set.inter_comm]
  have hle : (μHE[n] : Measure (Eucl P)).restrict (M ∩ K) ≤
      (μHE[n] : Measure (Eucl P)).restrict M :=
    Measure.restrict_mono Set.inter_subset_left le_rfl
  -- Step 4: `θ` is `Hⁿ⌞(M ∩ K)`-integrable (the `integrableOn` field).
  have hθ : Integrable θ ((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)) :=
    hT.integrableOn K hK hKU
  -- Step 5: `ξ(·)(c)` is a.e.-strongly measurable and a.e. bounded by `‖c‖` for `Hⁿ⌞(M ∩ K)`.
  have hmeas : AEStronglyMeasurable (fun x => ξ x c)
      ((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)) :=
    ((ContinuousLinearMap.apply ℝ ℝ c).continuous.comp_aestronglyMeasurable
      hT.aestronglyMeasurable).mono_measure hle
  have hbd : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)), ‖ξ x c‖ ≤ ‖c‖ :=
    ae_mono hle hbound
  -- Step 6: integrable times a.e.-bounded is integrable.
  exact hθ.mul_bdd hmeas hbd
/-- **Polar test form for a `k`-vector field** (Simon Ch. 6, 2.6–2.8).  If the coordinates
`κ^γ = κ(dx^γ)` of `κ : ℝ^N → Λ_k(ℝ^N)` are `μ`-integrable on `B = B_R(0)`, then for every `ε > 0`
there is a continuous `k`-form `ω` with `tsupport ω ⊆ B` and `|ω| ≤ 1` such that
`∫_B |κ| dμ ≤ ∫ κ(ω) dμ + ε`, where `|κ| = (∑_γ (κ^γ)²)^{1/2}`.  Apply
`imc_mlb_exists_unit_field_integral_ge` to the coefficient field `c = (κ^γ)_γ ∈ ℝ^I` and put
`ω = ∑_γ F^γ dx^γ`, so that `|ω| = |F| ≤ 1` and `κ(ω) = ⟨F, c⟩`. -/
theorem Submission.imc_mlb_exists_form_lintegral_coordNorm_le : ∀ (N k : ℕ) (μ : Measure (Eucl N)) (κ : Eucl N → NVector (Eucl N) k) (R : ℝ), (∀ γ : SimonMultiIndex k N, IntegrableOn (fun x => euclideanNVectorCoordinate (κ x) γ) (ball (0 : Eucl N) R) μ) → ∀ ε : ℝ, 0 < ε → ∃ ω : Eucl N → Covector (Eucl N) k, Continuous ω ∧ tsupport ω ⊆ ball (0 : Eucl N) R ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ Integrable (fun x => κ x (ω x)) μ ∧ ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ ENNReal.ofReal (∫ x, κ x (ω x) ∂μ + ε) := by
  intro N k μ κ R hκ ε hε
  classical
  -- Step 1: the coefficient field `c(x) = (κ^γ(x))_γ = ∑_γ κ^γ(x) e_γ` in `ℝ^I`.
  obtain ⟨c, hc_apply⟩ : ∃ c : Eucl N → EuclideanSpace ℝ (SimonMultiIndex k N),
      ∀ x γ, c x γ = euclideanNVectorCoordinate (κ x) γ :=
    ⟨fun x => WithLp.toLp 2 fun γ => euclideanNVectorCoordinate (κ x) γ, fun _ _ => rfl⟩
  have hc_sum : c = fun x => ∑ γ : SimonMultiIndex k N,
      euclideanNVectorCoordinate (κ x) γ • EuclideanSpace.single γ (1 : ℝ) := by
    funext x
    ext β
    simp [hc_apply, Pi.single_apply, mul_ite]
  -- Step 2: `c` is `μ`-integrable on `B`.
  have hc : IntegrableOn c (ball (0 : Eucl N) R) μ := by
    rw [hc_sum]
    exact integrable_finsetSum _ fun γ _ => (hκ γ).smul_const _
  -- Step 3: `|c(x)| = (∑_γ κ^γ(x)²)^{1/2}`.
  have hc_norm : ∀ x, ‖c x‖ =
      Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2) := by
    intro x
    simp [EuclideanSpace.norm_eq, hc_apply]
  -- Step 4: a continuous unit field `F` nearly attaining `∫_B |c| dμ`.
  obtain ⟨F, hF, hFB, hF1, hFi, hFle⟩ := Submission.imc_mlb_exists_unit_field_integral_ge N
    (EuclideanSpace ℝ (SimonMultiIndex k N)) μ R c hc ε hε
  -- Step 5: the test form `ω = ∑_γ F^γ dx^γ`.
  obtain ⟨ω, hω⟩ : ∃ ω : Eucl N → Covector (Eucl N) k, ∀ x, ω x = ∑ γ : SimonMultiIndex k N,
      F x γ • wedgeCovectors k (fun j => EuclideanSpace.proj (γ j)) :=
    ⟨_, fun _ => rfl⟩
  -- Step 5(d): `κ(x)(ω(x)) = ∑_γ F^γ(x) κ^γ(x) = ⟨F(x), c(x)⟩`.
  have hpair : (fun x => κ x (ω x)) = fun x => inner ℝ (F x) (c x) := by
    funext x
    simp only [hω, map_sum, map_smul, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, hc_apply, euclideanNVectorCoordinate, mul_comm]
  refine ⟨ω, ?_, ?_, fun x => ?_, ?_, ?_⟩
  · -- Step 5(a): `ω` is continuous.
    rw [show ω = _ from funext hω]
    fun_prop
  · -- Step 5(b): `support ω ⊆ support F`, so `tsupport ω ⊆ tsupport F ⊆ B`.
    refine (closure_mono (Function.support_subset_iff'.2 fun x hx => ?_)).trans hFB
    rw [Function.notMem_support] at hx
    simp [hω, hx]
  · -- Step 5(c): the coordinates of `ω(x)` are `F^β(x)`, so `|ω(x)| = |F(x)| ≤ 1`.
    have hcoord : ∀ β, euclideanCovectorCoordinate (ω x) β = F x β := by
      intro β
      rw [hω]
      exact Submission.smr_ci_coord_sum_smul_wedge N k (fun γ => F x γ) β
    calc covectorEuclideanNorm (ω x)
        = Real.sqrt (∑ β : SimonMultiIndex k N, (F x β) ^ 2) := by
          rw [Submission.smr_ci_norm_eq_sqrt_sum_coord_sq]
          simp only [hcoord]
      _ = ‖F x‖ := by simp [EuclideanSpace.norm_eq]
      _ ≤ 1 := hF1 x
  · -- Step 6: `κ(ω) = ⟨F, c⟩` is `μ`-integrable.
    rw [hpair]
    exact hFi
  · -- Step 7: `∫⁻_B |κ| dμ = ofReal (∫_B |c| dμ) ≤ ofReal (∫ ⟨F, c⟩ dμ + ε)`.
    rw [hpair]
    calc ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
          (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ
        = ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal ‖c x‖ ∂μ := by simp only [hc_norm]
      _ = ENNReal.ofReal (∫ x in ball (0 : Eucl N) R, ‖c x‖ ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (Integrable.norm hc)
          (Eventually.of_forall fun x => norm_nonneg (c x))).symm
      _ ≤ ENNReal.ofReal (∫ x, inner ℝ (F x) (c x) ∂μ + ε) := ENNReal.ofReal_le_ofReal hFle
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
/-- **Coordinate bound** (for the pairing expansion in the proof of Simon Ch. 6, 6.2, p. 169).
Each increasing coordinate `c_I = c(e_{I(1)}, …, e_{I(n)})` of an `n`-covector `c` is bounded in
absolute value by the Euclidean coefficient norm `|c|` of Remark 2.6.  Here `|c|² = ∑_J t_J`, with
`t_J = c(e_{J(1)}, …, e_{J(n)})²` for strictly increasing `J : Fin n → Fin P` and `t_J = 0`
otherwise.  Every `t_J ≥ 0` and `t_I = c_I²`, so `c_I² ≤ |c|²`. -/
theorem Submission.polyhedral_approx_pairing_coordinate_bound : ∀ (P n : ℕ) (c : Covector (Eucl P) n) (I : SimonMultiIndex n P), |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c := by
  intro P n c I
  -- `|c| = √(∑_J t_J)`, the sum over all `J : Fin n → Fin P`.
  set t : (Fin n → Fin P) → ℝ := fun J =>
    if StrictMono J then (c fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) ^ 2 else 0 with ht
  -- Each `t_J` is a square or `0`.
  have ht0 : ∀ J ∈ Finset.univ, 0 ≤ t J := fun J _ => by
    simp only [ht]
    split_ifs <;> positivity
  -- `⇑I` is strictly increasing and `basisFun (I i) = e_{I(i)}`, so `t_I = c_I²`.
  have htI : t I = euclideanCovectorCoordinate c I ^ 2 := by
    simp only [ht, I.strictMono, ite_true, EuclideanSpace.basisFun_apply, euclideanCovectorCoordinate]
  -- `|c_I| = √(c_I²) = √(t_I) ≤ √(∑_J t_J) = |c|`.
  calc |euclideanCovectorCoordinate c I| = √(euclideanCovectorCoordinate c I ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(∑ J, t J) := by
        rw [← htI]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum ht0 (Finset.mem_univ _))
    _ = covectorEuclideanNorm c := rfl
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

/-- **Restriction theory, Simon Ch. 6, (2.7)–(2.9) (p. 136).**
(R0) A current with a measure representation (2.7) has locally finite mass: `M_W(X)` is bounded by
the `μ`-integrals of the coefficients `v(dx^I)` over `closure W`.
(R1) Restrictions `X ⌞ A` (2.9) do not depend on the representation: the coefficient densities of
two representations agree on `C_c^∞`, hence on `C_c` and on bounded Borel functions.
(R2) If `M_W(X) < ∞` for all `W ⊂⊂ U`, the vector Riesz theorem (Ch. 1, 4.14, SimonGMT) applied on
`U` to the extension of `X` to continuous compactly supported forms gives the mass measure `μ` and
a density `v` with `|v| ≤ 1`, `μ(W) = M_W(X)` by the envelope identity. Then `S_A(ω) = ∫_A ⟨ω, v⟩ dμ`
is the restriction, and `M_W(S) = μ(W ∩ A)`: `≤` from `|v| ≤ 1`, `≥` from
`X = S_A + S_{Aᶜ}` and inner approximation by compact sets. -/
theorem Submission.iwl_restriction_theory : (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X : GeometricCurrentOn U k) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), IsMeasureRepresentation X μ v → ∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) ∧ (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X : GeometricCurrentOn U k) (A : Set (Eucl P)) (S₁ S₂ : GeometricCurrentOn U k), IsRestriction X A S₁ → IsRestriction X A S₂ → S₁ = S₂) ∧ (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k, (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) → ∃ μ : Measure (Eucl P), IsMassMeasure X μ ∧ (∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U k, IsRestriction X A S) ∧ ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U k), IsRestriction X A S → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → S.massOn W = μ (W ∩ A)) := by
  classical
  -- Coefficient vectors `cv α = (α(e_J))_J` and the inverse expansion `emb c = Σ_I c_I dx^I`.
  have coeff : ∀ (P k : ℕ), ∃ (cv : Covector (Eucl P) k →L[ℝ] EuclideanSpace ℝ (Fin k → Fin P))
      (emb : EuclideanSpace ℝ (Fin k → Fin P) →L[ℝ] Covector (Eucl P) k),
      (∀ α, ‖cv α‖ = covectorEuclideanNorm α) ∧ (∀ α, emb (cv α) = α) ∧
      (∀ c, covectorEuclideanNorm (emb c) ≤ ‖c‖) := by
    intro P k
    classical
    obtain ⟨cv, hcv⟩ : ∃ cv : Covector (Eucl P) k →L[ℝ] EuclideanSpace ℝ (Fin k → Fin P),
        ∀ α J, cv α J = if StrictMono J then
          α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) else 0 := by
      refine ⟨(EuclideanSpace.equiv (Fin k → Fin P) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun J => if StrictMono J then
          simpleNVector (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) else 0), fun α J => ?_⟩
      by_cases hJ : StrictMono J <;> simp [hJ]
    have hcvn : ∀ α, ‖cv α‖ = covectorEuclideanNorm α := by
      intro α
      rw [EuclideanSpace.norm_eq]
      unfold covectorEuclideanNorm
      congr 1
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [hcv]
      by_cases hJ : StrictMono J <;> simp [hJ]
    -- Kronecker property `dx^β (e_γ) = δ_{βγ}`.
    have hK : ∀ β γ : SimonMultiIndex k P,
        wedgeCovectors k (fun j => EuclideanSpace.proj (β j))
          (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) = if β = γ then 1 else 0 := by
      intro β γ
      rw [wedgeCovectors_apply_det]
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
    obtain ⟨emb, hemb⟩ : ∃ emb : EuclideanSpace ℝ (Fin k → Fin P) →L[ℝ] Covector (Eucl P) k,
        ∀ c, emb c = ∑ I : SimonMultiIndex k P,
          c (⇑I) • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)) :=
      ⟨∑ I : SimonMultiIndex k P, (EuclideanSpace.proj (⇑I : Fin k → Fin P)).smulRight
          (wedgeCovectors k (fun j => EuclideanSpace.proj (I j))), fun c => by simp⟩
    refine ⟨cv, emb, hcvn, fun α => ?_, fun c => ?_⟩
    · rw [hemb]
      conv_rhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P k α]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [hcv, if_pos I.strictMono]
      simp [euclideanCovectorCoordinate, EuclideanSpace.basisFun_apply]
    · rw [← hcvn, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro J _
      rw [hcv]
      split_ifs with hJ
      · have hγ : (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) =
            fun j => EuclideanSpace.single ((OrderEmbedding.ofStrictMono J hJ) j) (1 : ℝ) := by
          funext i
          simp [EuclideanSpace.basisFun_apply]
        have hval : emb c (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) = c J := by
          rw [hγ, hemb, ContinuousAlternatingMap.sum_apply]
          simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          rfl
        exact le_of_eq (by rw [hval])
      · have h := sq_nonneg ‖c J‖
        simpa using h
  -- Coefficient functions of a measure representation are locally integrable.
  have intOn : ∀ {P k : ℕ} {U : Set (Eucl P)} (hU : IsOpen U)
      {X : GeometricCurrentOn U k} {μ : Measure (Eucl P)} {v : Eucl P → NVector (Eucl P) k}
      (hrep : IsMeasureRepresentation X μ v) {K : Set (Eucl P)} (hK : IsCompact K) (hKU : K ⊆ U)
      (α : Covector (Eucl P) k), IntegrableOn (fun x => v x α) K μ := by
    intro P k U hU X μ v hrep K hK hKU α
    obtain ⟨W, hW, hcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
    obtain ⟨i, hKi⟩ := hcov K hK hKU
    obtain ⟨hWo, hWc, hWU⟩ := hW i
    obtain ⟨χ, hχs, -, hχsupp, hχ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hWo hK.isClosed hKi
    let ω : DifferentialForm (Eucl P) k := fun x => χ x • α
    have hωsmooth : IsSmoothForm ω := hχs.smul contDiff_const
    have hsuppω : Function.support ω ⊆ W i := by
      intro x hx
      rw [← hχsupp]
      intro h0
      apply hx
      simp [ω, h0]
    have htsupp : tsupport ω ⊆ closure (W i) := closure_mono hsuppω
    have hcpt : HasCompactSupport ω := hWc.of_isClosed_subset (isClosed_tsupport _) htsupp
    have hmem : ω ∈ TestFormOn U k := ⟨⟨hωsmooth, hcpt⟩, htsupp.trans hWU⟩
    have hint := (hrep ⟨ω, hmem⟩).1
    have hfun : (fun x => v x (((⟨ω, hmem⟩ : TestFormOn U k) : DifferentialForm (Eucl P) k) x)) =
        fun x => χ x * v x α := by
      funext x
      change v x (χ x • α) = χ x * v x α
      rw [map_smul, smul_eq_mul]
    rw [hfun] at hint
    refine hint.integrableOn.congr_fun ?_ hK.measurableSet
    intro x hx
    simp [(hχ1 x).1 hx]
  -- (R0): a measure representation forces locally finite mass.
  have R0 : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X : GeometricCurrentOn U k)
      (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), IsMeasureRepresentation X μ v →
      ∀ W, CompactlyContainedOpen W U → X.massOn W < ∞ := by
    intro P k U hU X μ v hrep W hW
    obtain ⟨hWo, hWc, hWU⟩ := hW
    let d : SimonMultiIndex k P → Covector (Eucl P) k :=
      fun I => wedgeCovectors k (fun j => EuclideanSpace.proj (I j))
    have hint : ∀ I, IntegrableOn (fun x => v x (d I)) (closure W) μ :=
      fun I => intOn hU hrep hWc hWU (d I)
    set C : ℝ := ∑ I, ∫ x in closure W, |v x (d I)| ∂μ with hC
    have key : ∀ ω ∈ massAdmissibleOn U k W, X ω ≤ C := by
      intro ω hω
      obtain ⟨hωW, hω1⟩ := hω
      rw [(hrep ω).2]
      have hpt : ∀ x, v x ((ω : DifferentialForm (Eucl P) k) x) ≤
          (closure W).indicator (fun x => ∑ I, |v x (d I)|) x := by
        intro x
        by_cases hx : x ∈ closure W
        · rw [indicator_of_mem hx]
          rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P k
            ((ω : DifferentialForm (Eucl P) k) x), map_sum]
          apply Finset.sum_le_sum
          intro I _
          rw [map_smul, smul_eq_mul]
          calc euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) k) x) I * v x (d I)
              ≤ |euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) k) x) I * v x (d I)| :=
                le_abs_self _
            _ = |euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) k) x) I| * |v x (d I)| :=
                abs_mul _ _
            _ ≤ 1 * |v x (d I)| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact (Submission.polyhedral_approx_pairing_coordinate_bound P k _ I).trans (hω1 x)
            _ = |v x (d I)| := one_mul _
        · have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hωW h)))
          simp [h0, indicator_of_notMem hx]
      have hintS : Integrable (fun x => ∑ I, |v x (d I)|) (μ.restrict (closure W)) :=
        integrable_finsetSum _ (fun I _ => (hint I).abs)
      calc ∫ x, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ
          ≤ ∫ x, (closure W).indicator (fun x => ∑ I, |v x (d I)|) x ∂μ :=
            integral_mono (hrep ω).1 ((integrable_indicator_iff isClosed_closure.measurableSet).2 hintS) hpt
        _ = ∫ x in closure W, ∑ I, |v x (d I)| ∂μ := integral_indicator isClosed_closure.measurableSet
        _ = C := integral_finsetSum _ (fun I _ => (hint I).abs)
    have hle : X.massOn W ≤ ENNReal.ofReal C := by
      apply sSup_le
      rintro r ⟨ω, hω, rfl⟩
      exact ENNReal.ofReal_le_ofReal (key ω hω)
    exact hle.trans_lt ENNReal.ofReal_lt_top
  -- Two representations give the same set integrals of every test form.
  have setInt : ∀ {P k : ℕ} {U : Set (Eucl P)} (hU : IsOpen U)
      {X : GeometricCurrentOn U k} {μ₁ μ₂ : Measure (Eucl P)} {v₁ v₂ : Eucl P → NVector (Eucl P) k}
      (hrep₁ : IsMeasureRepresentation X μ₁ v₁) (hrep₂ : IsMeasureRepresentation X μ₂ v₂)
      {A : Set (Eucl P)} (hA : MeasurableSet A) (ω : TestFormOn U k),
      ∫ x in A, v₁ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₁ =
        ∫ x in A, v₂ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₂ := by
    intro P k U hU X μ₁ μ₂ v₁ v₂ hrep₁ hrep₂ A hA ω
    have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) k)) := ω.2.1.2
    have hKU : tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U := ω.2.2
    obtain ⟨W, hW, hcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
    obtain ⟨i, hKi⟩ := hcov _ hKc hKU
    obtain ⟨hWo, hWc, hWU⟩ := hW i
    set O := W i with hO
    have hLm : MeasurableSet (closure O) := isClosed_closure.measurableSet
    let d : SimonMultiIndex k P → Covector (Eucl P) k :=
      fun I => wedgeCovectors k (fun j => EuclideanSpace.proj (I j))
    let c : SimonMultiIndex k P → Eucl P → ℝ :=
      fun I x => euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) k) x) I
    have hcont_c : ∀ I, Continuous (c I) := by
      intro I
      have hω : Continuous (ω : DifferentialForm (Eucl P) k) := ω.2.1.1.continuous
      exact (continuous_eval_const (fun j => EuclideanSpace.single (I j) (1 : ℝ))).comp hω
    have hc0 : ∀ I x, x ∉ O → c I x = 0 := by
      intro I x hx
      have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hKi h))
      simp [c, h0, euclideanCovectorCoordinate]
    have hbdd : ∀ I, ∃ B : ℝ, ∀ x, |A.indicator (c I) x| ≤ B := by
      intro I
      have hcs : HasCompactSupport (c I) := by
        apply HasCompactSupport.intro hKc
        intro x hx
        have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [c, h0, euclideanCovectorCoordinate]
      obtain ⟨B, hB⟩ := (hcs.isCompact_range (hcont_c I)).isBounded.exists_norm_le
      refine ⟨max B 0, fun x => ?_⟩
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx]
        exact (hB _ (mem_range_self x)).trans (le_max_left _ _)
      · rw [indicator_of_notMem hx]; simp
    -- one coefficient
    have hcoord : ∀ I, ∫ x, A.indicator (c I) x * v₁ x (d I) ∂(μ₁.restrict (closure O)) =
        ∫ x, A.indicator (c I) x * v₂ x (d I) ∂(μ₂.restrict (closure O)) := by
      intro I
      have hg₁ : Integrable (fun x => v₁ x (d I)) (μ₁.restrict (closure O)) :=
        intOn hU hrep₁ hWc hWU (d I)
      have hg₂ : Integrable (fun x => v₂ x (d I)) (μ₂.restrict (closure O)) :=
        intOn hU hrep₂ hWc hWU (d I)
      have hsmooth : ∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ O → ∫ x, ψ x * v₁ x (d I) ∂(μ₁.restrict (closure O)) =
            ∫ x, ψ x * v₂ x (d I) ∂(μ₂.restrict (closure O)) := by
        intro ψ hψ hψc hψO
        let η : DifferentialForm (Eucl P) k := fun x => ψ x • d I
        have hηt : tsupport η ⊆ tsupport ψ := tsupport_smul_subset_left _ _
        have hmem : η ∈ TestFormOn U k :=
          ⟨⟨hψ.smul contDiff_const, hψc.smul_right⟩, hηt.trans (hψO.trans (subset_closure.trans hWU))⟩
        have e₁ := (hrep₁ ⟨η, hmem⟩).2
        have e₂ := (hrep₂ ⟨η, hmem⟩).2
        have hv : ∀ (v : Eucl P → NVector (Eucl P) k) (x : Eucl P),
            v x (((⟨η, hmem⟩ : TestFormOn U k) : DifferentialForm (Eucl P) k) x) = ψ x * v x (d I) := by
          intro v x
          change v x (ψ x • d I) = ψ x * v x (d I)
          rw [map_smul, smul_eq_mul]
        simp only [hv] at e₁ e₂
        have hoff : ∀ (v : Eucl P → NVector (Eucl P) k) (μ : Measure (Eucl P)),
            ∫ x, ψ x * v x (d I) ∂(μ.restrict (closure O)) = ∫ x, ψ x * v x (d I) ∂μ := by
          intro v μ
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hψO h)))
          simp [this]
        rw [hoff v₁ μ₁, hoff v₂ μ₂, ← e₁, ← e₂]
      have hcont := Submission.slicing_ru_smooth_to_continuous P (μ₁.restrict (closure O))
        (μ₂.restrict (closure O)) _ _ hg₁ hg₂ O hWo hsmooth
      refine Submission.slicing_ru_continuous_to_bounded P (μ₁.restrict (closure O))
        (μ₂.restrict (closure O)) _ _ hg₁ hg₂ O hWo hcont (A.indicator (c I))
        (((hcont_c I).measurable).indicator hA) (hbdd I) ?_
      intro x hx
      by_cases hxA : x ∈ A
      · rw [indicator_of_mem hxA]; exact hc0 I x hx
      · rw [indicator_of_notMem hxA]
    -- expansion of the set integral
    have hexp : ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
        IsMeasureRepresentation X μ v →
        ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ =
          ∑ I, ∫ x, A.indicator (c I) x * v x (d I) ∂(μ.restrict (closure O)) := by
      intro μ v hrep
      have hpt : ∀ x, A.indicator (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) x =
          ∑ I, A.indicator (c I) x * v x (d I) := by
        intro x
        by_cases hxA : x ∈ A
        · rw [indicator_of_mem hxA]
          conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge P k
            ((ω : DifferentialForm (Eucl P) k) x), map_sum]
          refine Finset.sum_congr rfl (fun I _ => ?_)
          rw [indicator_of_mem hxA, map_smul, smul_eq_mul]
        · rw [indicator_of_notMem hxA]
          simp [indicator_of_notMem hxA]
      have hterm : ∀ I, Integrable (fun x => A.indicator (c I) x * v x (d I)) (μ.restrict (closure O)) := by
        intro I
        obtain ⟨B, hB⟩ := hbdd I
        have hg : Integrable (fun x => v x (d I)) (μ.restrict (closure O)) :=
          intOn hU hrep hWc hWU (d I)
        refine hg.bdd_mul (c := B) ?_ ?_
        · exact (((hcont_c I).measurable).indicator hA).aestronglyMeasurable
        · exact Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hB x)
      rw [← integral_indicator hA]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closure O)]
      · simp_rw [hpt]
        exact integral_finsetSum _ (fun I _ => hterm I)
      · intro x hx
        have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hKi h)))
        simp [h0]
    rw [hexp μ₁ v₁ hrep₁, hexp μ₂ v₂ hrep₂]
    exact Finset.sum_congr rfl (fun I _ => hcoord I)
  -- (R1): restrictions are unique.
  have R1 : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X : GeometricCurrentOn U k)
      (A : Set (Eucl P)) (S₁ S₂ : GeometricCurrentOn U k), IsRestriction X A S₁ →
      IsRestriction X A S₂ → S₁ = S₂ := by
    intro P k U hU X A S₁ S₂ h₁ h₂
    obtain ⟨hA, μ₁, v₁, hrep₁, hS₁⟩ := h₁
    obtain ⟨-, μ₂, v₂, hrep₂, hS₂⟩ := h₂
    apply GeometricCurrentOn.ext
    intro ω
    rw [hS₁, hS₂]
    exact setInt hU hrep₁ hrep₂ hA ω
  -- `|α| ≤ √N ‖α‖`.
  have euclNormLe : ∀ {P k : ℕ} (α : Covector (Eucl P) k),
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin k → Fin P)) * ‖α‖ := by
    intro P k α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin k → Fin P, (if StrictMono I then
          (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
            simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one] at h
            have h' : |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ ‖α‖ := by
              simpa [Real.norm_eq_abs] using h
            have := sq_le_sq' (neg_le_of_abs_le h') (le_of_abs_le h')
            simpa using this
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  -- `S_A(ω) = ∫_A ⟨ω, v⟩ dμ` is a current when `|v| ≤ 1` and `μ` is finite on compacts.
  have restrCur : ∀ {P k : ℕ} {U : Set (Eucl P)} (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) k)
      (hint : ∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ)
      (hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞)
      (hv : ∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α)
      (A : Set (Eucl P)), ∃ S : GeometricCurrentOn U k, ∀ ω : TestFormOn U k,
        S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ := by
    intro P k U μ v hint hfin hv A
    let T : CurrentOn U k :=
      { toFun := fun ω => ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ
        map_add' := by
          intro ω η
          simp only [Submodule.coe_add, Pi.add_apply, map_add]
          exact integral_add (hint ω).integrableOn (hint η).integrableOn
        map_smul' := by
          intro c ω
          simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
          exact integral_const_mul c _ }
    refine ⟨⟨T, ?_⟩, fun ω => rfl⟩
    intro ωs hconv
    obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
    set c : ℝ := Real.sqrt (Fintype.card (Fin k → Fin P)) with hc
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hμK : μ K < ∞ := hfin K hK hKU
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ : ℝ := ε / ((c + 1) * (μ.real K + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (hunif 0) δ hδpos)
    refine ⟨N, fun j hj => ?_⟩
    have hb : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Eucl P) k) x‖ < δ := by
      intro x hx
      have h := hN j hj x hx
      simpa [dist_eq_norm, norm_iteratedFDeriv_zero] using h
    have hpt : ∀ x, ‖v x ((ωs j : DifferentialForm (Eucl P) k) x)‖ ≤ K.indicator (fun _ => c * δ) x := by
      intro x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        calc |v x ((ωs j : DifferentialForm (Eucl P) k) x)|
            ≤ covectorEuclideanNorm ((ωs j : DifferentialForm (Eucl P) k) x) := hv x _
          _ ≤ c * ‖(ωs j : DifferentialForm (Eucl P) k) x‖ := euclNormLe _
          _ ≤ c * δ := mul_le_mul_of_nonneg_left (hb x hx).le hc0
      · have h0 : (ωs j : DifferentialForm (Eucl P) k) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h))
        rw [indicator_of_notMem hx, h0, map_zero, norm_zero]
    have hgi : Integrable (K.indicator (fun _ : Eucl P => c * δ)) μ :=
      (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hμK.ne)
    have hbound : ‖T (ωs j)‖ ≤ c * δ * μ.real K := by
      calc ‖T (ωs j)‖ = ‖∫ x in A, v x ((ωs j : DifferentialForm (Eucl P) k) x) ∂μ‖ := rfl
        _ ≤ ∫ x in A, K.indicator (fun _ => c * δ) x ∂μ :=
            norm_integral_le_of_norm_le hgi.integrableOn (Eventually.of_forall hpt)
        _ ≤ ∫ x, K.indicator (fun _ => c * δ) x ∂μ :=
            setIntegral_le_integral hgi (Eventually.of_forall (fun x =>
              indicator_nonneg (fun _ _ => mul_nonneg hc0 hδpos.le) x))
        _ = c * δ * μ.real K := by
            rw [integral_indicator hK.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    rw [dist_zero_right]
    calc ‖T (ωs j)‖ ≤ c * δ * μ.real K := hbound
      _ < ε := by
        have hμr : 0 ≤ μ.real K := measureReal_nonneg
        rw [hδ]
        have hden : 0 < (c + 1) * (μ.real K + 1) := by positivity
        rw [show c * (ε / ((c + 1) * (μ.real K + 1))) * μ.real K =
            ε * (c * μ.real K / ((c + 1) * (μ.real K + 1))) by ring]
        have hlt : c * μ.real K / ((c + 1) * (μ.real K + 1)) < 1 := by
          rw [div_lt_one hden]; nlinarith
        calc ε * (c * μ.real K / ((c + 1) * (μ.real K + 1))) < ε * 1 :=
              mul_lt_mul_of_pos_left hlt hε
          _ = ε := mul_one ε
  -- `M_W(S_A) ≤ μ(W ∩ A)`.
  have massLe : ∀ {P k : ℕ} {U : Set (Eucl P)} {μ : Measure (Eucl P)}
      {v : Eucl P → NVector (Eucl P) k}
      (hv : ∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α)
      {A : Set (Eucl P)} (S : GeometricCurrentOn U k)
      (hS : ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ)
      {W : Set (Eucl P)} (hW : MeasurableSet W), S.massOn W ≤ μ (W ∩ A) := by
    intro P k U μ v hv A S hS W hW
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    dsimp only
    rw [hS ω]
    have hpt : ∀ x, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ≤ W.indicator 1 x := by
      intro x
      by_cases hx : x ∈ W
      · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_one.2 ((hv x _).trans (hω1 x))
      · have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hωW h))
        simp [h0]
    calc ENNReal.ofReal (∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ)
        ≤ ‖∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ‖ₑ := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in A, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in A, W.indicator 1 x ∂μ := lintegral_mono hpt
      _ = μ (W ∩ A) := by rw [lintegral_indicator_one hW, Measure.restrict_apply hW]
  -- Mass identity `M_W(S_A) = μ(W ∩ A)` for the mass measure `μ`.
  have massEq : ∀ {P k : ℕ} {U : Set (Eucl P)} (hU : IsOpen U) {X : GeometricCurrentOn U k}
      {μ : Measure (Eucl P)} {v : Eucl P → NVector (Eucl P) k}
      (hmass : IsMassMeasure X μ) (hrep : IsMeasureRepresentation X μ v)
      (hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞)
      (hv : ∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α)
      {A : Set (Eucl P)} (hA : MeasurableSet A) (S : GeometricCurrentOn U k)
      (hS : ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ)
      {W : Set (Eucl P)} (hW : IsOpen W) (hWU : W ⊆ U), S.massOn W = μ (W ∩ A) := by
    intro P k U hU X μ v hmass hrep hfin hv A hA S hS W hW hWU
    apply le_antisymm (massLe hv S hS hW.measurableSet)
    obtain ⟨S', hS'⟩ := restrCur μ v (fun ω => (hrep ω).1) hfin hv Aᶜ
    have hV : ∀ V, CompactlyContainedOpen V U → μ (V ∩ A) ≤ S.massOn V := by
      intro V hVc
      have hX : X.massOn V ≤ S.massOn V + S'.massOn V := by
        apply sSup_le
        rintro r ⟨ω, hω, rfl⟩
        dsimp only
        have hsum : X ω = S ω + S' ω := by
          rw [hS, hS', (hrep ω).2, integral_add_compl hA (hrep ω).1]
        rw [hsum]
        exact ENNReal.ofReal_add_le.trans (add_le_add (S.le_massOn hω) (S'.le_massOn hω))
      have h1 : S'.massOn V ≤ μ (V ∩ Aᶜ) := massLe hv S' hS' hVc.1.measurableSet
      have hfinV : μ (V ∩ Aᶜ) ≠ ⊤ :=
        ne_top_of_le_ne_top (hfin _ hVc.2.1 hVc.2.2).ne
          (measure_mono (inter_subset_left.trans subset_closure))
      apply ENNReal.le_of_add_le_add_right hfinV
      calc μ (V ∩ A) + μ (V ∩ Aᶜ) = μ V := by
            rw [← sdiff_eq, measure_inter_add_sdiff V hA]
        _ = X.massOn V := hmass.2 V hVc
        _ ≤ S.massOn V + S'.massOn V := hX
        _ ≤ S.massOn V + μ (V ∩ Aᶜ) := add_le_add_right h1 _
    obtain ⟨Wi, hWi, hcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
    have hσ : SigmaFinite (μ.restrict (W ∩ A)) := by
      refine Measure.FiniteSpanningSetsIn.sigmaFinite (C := {s | MeasurableSet s})
        ⟨fun i => Wi i ∪ Uᶜ, fun i => ((hWi i).1.measurableSet.union hU.measurableSet.compl),
          fun i => ?_, ?_⟩
      · rw [Measure.restrict_apply ((hWi i).1.measurableSet.union hU.measurableSet.compl)]
        calc μ ((Wi i ∪ Uᶜ) ∩ (W ∩ A)) ≤ μ (closure (Wi i)) := measure_mono (by
                rintro x ⟨hx1 | hx1, hx2, -⟩
                · exact subset_closure hx1
                · exact absurd (hWU hx2) hx1)
          _ < ∞ := hfin _ (hWi i).2.1 (hWi i).2.2
      · ext x
        simp only [mem_iUnion, mem_univ, iff_true, mem_union, mem_compl_iff]
        by_cases hx : x ∈ U
        · obtain ⟨i, hi⟩ := hcov {x} isCompact_singleton (singleton_subset_iff.2 hx)
          exact ⟨i, Or.inl (hi rfl)⟩
        · exact ⟨0, Or.inr hx⟩
    obtain ⟨C, hCc, hCsub, hnull⟩ := Submission.lpf_lli_inner_compact_approx P μ (W ∩ A)
      (hW.measurableSet.inter hA).nullMeasurableSet hσ
    have hle1 : μ (W ∩ A) ≤ μ (⋃ j, C j) := by
      calc μ (W ∩ A) ≤ μ ((W ∩ A) ∩ ⋃ j, C j) + μ ((W ∩ A) \ ⋃ j, C j) :=
            measure_le_inter_add_sdiff μ _ _
        _ = μ ((W ∩ A) ∩ ⋃ j, C j) := by rw [hnull, add_zero]
        _ ≤ μ (⋃ j, C j) := measure_mono inter_subset_right
    rw [measure_iUnion_eq_iSup_accumulate] at hle1
    refine hle1.trans (iSup_le fun n => ?_)
    have hDc : IsCompact (Set.accumulate C n) := by
      rw [Set.accumulate_def]
      exact (Set.finite_Iic n).isCompact_biUnion (fun j _ => hCc j)
    have hDsub : Set.accumulate C n ⊆ W ∩ A := by
      rw [Set.accumulate_def]
      exact iUnion₂_subset (fun j _ => hCsub j)
    obtain ⟨i, hi⟩ := hcov _ hDc (hDsub.trans (inter_subset_left.trans hWU))
    have hVc : CompactlyContainedOpen (W ∩ Wi i) U :=
      ⟨hW.inter (hWi i).1,
        (hWi i).2.1.of_isClosed_subset isClosed_closure (closure_mono inter_subset_right),
        (closure_mono inter_subset_right).trans (hWi i).2.2⟩
    calc μ (Set.accumulate C n) ≤ μ ((W ∩ Wi i) ∩ A) := measure_mono (fun x hx =>
            ⟨⟨(hDsub hx).1, hi hx⟩, (hDsub hx).2⟩)
      _ ≤ S.massOn (W ∩ Wi i) := hV _ hVc
      _ ≤ S.massOn W := S.massOn_mono inter_subset_left
  -- Extension of `X` (locally finite mass) to continuous compactly supported forms.
  have extL : ∀ {P k : ℕ} {U : Set (Eucl P)} (hU : IsOpen U) (X : GeometricCurrentOn U k)
      (hX : ∀ W, CompactlyContainedOpen W U → X.massOn W < ∞),
      ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ,
        (∀ ω : TestFormOn U k, L (ω : DifferentialForm (Eucl P) k) = X ω) ∧
        (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
          Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U → L (φ + ψ) = L φ + L ψ) ∧
        (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → L (c • φ) = c * L φ) ∧
        (∀ (V : Set (Eucl P)) (φ : Eucl P → Covector (Eucl P) k), IsOpen V → V ⊆ U → Continuous φ →
          HasCompactSupport φ → tsupport φ ⊆ V → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) →
          ENNReal.ofReal (L φ) ≤ X.massOn V) := by
    intro P k U hU X hX
    classical
    obtain ⟨cv, emb, hcvn, -, -⟩ := coeff P k
    -- the Euclidean coefficient norm is a norm
    have hN_sub : ∀ α β γ : Covector (Eucl P) k, covectorEuclideanNorm (α - β) ≤
        covectorEuclideanNorm (α - γ) + covectorEuclideanNorm (γ - β) := by
      intro α β γ
      rw [← hcvn, ← hcvn, ← hcvn, map_sub, map_sub, map_sub]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hN_comm : ∀ α β : Covector (Eucl P) k,
        covectorEuclideanNorm (α - β) = covectorEuclideanNorm (β - α) := by
      intro α β
      rw [← hcvn, ← hcvn, map_sub, map_sub, norm_sub_rev]
    have hN_smul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
        covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
      intro c α
      rw [← hcvn, ← hcvn, map_smul, norm_smul, Real.norm_eq_abs]
    have hN_add : ∀ α β : Covector (Eucl P) k,
        covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
      intro α β
      rw [← hcvn, ← hcvn, ← hcvn, map_add]
      exact norm_add_le _ _
    -- exhaustion and unions of compactly contained sets
    obtain ⟨Wx, hWx, hcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
    have hccU : ∀ V₁ V₂ : Set (Eucl P), CompactlyContainedOpen V₁ U → CompactlyContainedOpen V₂ U →
        CompactlyContainedOpen (V₁ ∪ V₂) U := by
      rintro V₁ V₂ ⟨h1o, h1c, h1U⟩ ⟨h2o, h2c, h2U⟩
      refine ⟨h1o.union h2o, ?_, ?_⟩
      · rw [closure_union]; exact h1c.union h2c
      · rw [closure_union]; exact union_subset h1U h2U
    -- (F1) with an explicit bound
    have hF1 : ∀ V : Set (Eucl P), CompactlyContainedOpen V U → ∀ (ω : TestFormOn U k) (C : ℝ),
        tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V →
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ C) →
        |X ω| ≤ (X.massOn V).toReal * C := by
      intro V hV ω C hωV hC
      exact Submission.cmb_abs_apply_le_of_massOn_le P k U V X ω _ C ENNReal.toReal_nonneg
        (by rw [ENNReal.ofReal_toReal (hX V hV).ne]) hωV hC
    have hcoe_sub : ∀ a b : TestFormOn U k, ((a - b : TestFormOn U k) : DifferentialForm (Eucl P) k) =
        (a : DifferentialForm (Eucl P) k) - (b : DifferentialForm (Eucl P) k) := fun a b => rfl
    -- two uniformly close sequences supported in a fixed `V ⊂⊂ U` have close values
    have hclose : ∀ V : Set (Eucl P), CompactlyContainedOpen V U →
        ∀ (η η' : ℕ → TestFormOn U k) (δ : ℕ → ℝ),
        (∀ j, tsupport (η j : DifferentialForm (Eucl P) k) ⊆ V) →
        (∀ j, tsupport (η' j : DifferentialForm (Eucl P) k) ⊆ V) →
        (∀ j x, covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x -
          (η' j : DifferentialForm (Eucl P) k) x) ≤ δ j) →
        Tendsto δ atTop (𝓝 0) → Tendsto (fun j => X (η j) - X (η' j)) atTop (𝓝 0) := by
      intro V hV η η' δ hη hη' hδ hδ0
      have hbd : ∀ j, |X (η j) - X (η' j)| ≤ (X.massOn V).toReal * δ j := by
        intro j
        have hsub : X (η j) - X (η' j) = X (η j - η' j) := (map_sub X.toCurrent _ _).symm
        rw [hsub]
        refine hF1 V hV (η j - η' j) (δ j) ?_ (fun x => ?_)
        · rw [hcoe_sub]
          exact (tsupport_sub _ _).trans (union_subset (hη j) (hη' j))
        · rw [hcoe_sub, Pi.sub_apply]
          exact hδ j x
      have h2 : Tendsto (fun j => (X.massOn V).toReal * δ j) atTop (𝓝 0) := by
        simpa using hδ0.const_mul (X.massOn V).toReal
      exact squeeze_zero_norm (fun j => by rw [Real.norm_eq_abs]; exact hbd j) h2
    -- approximating sequences
    have hseq : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → ∃ V : Set (Eucl P), CompactlyContainedOpen V U ∧
          ∃ η : ℕ → TestFormOn U k, (∀ j, tsupport (η j : DifferentialForm (Eucl P) k) ⊆ V) ∧
          ∀ (j : ℕ) x, covectorEuclideanNorm (φ x - (η j : DifferentialForm (Eucl P) k) x) ≤
            1 / ((j : ℝ) + 1) := by
      intro φ hφ hφc hφU
      obtain ⟨i, hi⟩ := hcov _ hφc hφU
      refine ⟨Wx i, hWx i, ?_⟩
      choose η hηV hηφ using fun j : ℕ => Submission.cmb_exists_testForm_uniform_approx P k U (Wx i) φ
        (hWx i).1 (subset_closure.trans (hWx i).2.2) hφ hφc hi (1 / ((j : ℝ) + 1))
        Nat.one_div_pos_of_nat
      exact ⟨η, hηV, hηφ⟩
    -- the limit, characterized by every approximating sequence
    have hlim : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → ∃ l : ℝ, ∀ V : Set (Eucl P), CompactlyContainedOpen V U →
          ∀ (η : ℕ → TestFormOn U k) (δ : ℕ → ℝ),
          (∀ j, tsupport (η j : DifferentialForm (Eucl P) k) ⊆ V) →
          (∀ j x, covectorEuclideanNorm (φ x - (η j : DifferentialForm (Eucl P) k) x) ≤ δ j) →
          Tendsto δ atTop (𝓝 0) → Tendsto (fun j => X (η j)) atTop (𝓝 l) := by
      intro φ hφ hφc hφU
      obtain ⟨V₀, hV₀, η₀, hη₀V, hη₀φ⟩ := hseq φ hφ hφc hφU
      have htri : ∀ (η η' : ℕ → TestFormOn U k) (δ δ' : ℕ → ℝ),
          (∀ j x, covectorEuclideanNorm (φ x - (η j : DifferentialForm (Eucl P) k) x) ≤ δ j) →
          (∀ j x, covectorEuclideanNorm (φ x - (η' j : DifferentialForm (Eucl P) k) x) ≤ δ' j) →
          ∀ j x, covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x -
            (η' j : DifferentialForm (Eucl P) k) x) ≤ δ j + δ' j := by
        intro η η' δ δ' hη hη' j x
        calc covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x -
              (η' j : DifferentialForm (Eucl P) k) x)
            ≤ covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x - φ x) +
              covectorEuclideanNorm (φ x - (η' j : DifferentialForm (Eucl P) k) x) := hN_sub _ _ _
          _ = covectorEuclideanNorm (φ x - (η j : DifferentialForm (Eucl P) k) x) +
              covectorEuclideanNorm (φ x - (η' j : DifferentialForm (Eucl P) k) x) := by
            rw [hN_comm ((η j : DifferentialForm (Eucl P) k) x) (φ x)]
          _ ≤ δ j + δ' j := add_le_add (hη j x) (hη' j x)
      have hcauchy : CauchySeq (fun j => X (η₀ j)) := by
        refine cauchySeq_of_le_tendsto_0
          (fun N : ℕ => (X.massOn V₀).toReal * (2 / ((N : ℝ) + 1))) (fun n m N hn hm => ?_) ?_
        · rw [Real.dist_eq]
          have hsub : X (η₀ n) - X (η₀ m) = X (η₀ n - η₀ m) := (map_sub X.toCurrent _ _).symm
          rw [hsub]
          refine (hF1 V₀ hV₀ (η₀ n - η₀ m) (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) ?_ ?_).trans ?_
          · rw [hcoe_sub]
            exact (tsupport_sub _ _).trans (union_subset (hη₀V n) (hη₀V m))
          · intro x
            rw [hcoe_sub, Pi.sub_apply]
            exact htri (fun _ => η₀ n) (fun _ => η₀ m) (fun _ => 1 / ((n : ℝ) + 1))
              (fun _ => 1 / ((m : ℝ) + 1)) (fun _ x => hη₀φ n x) (fun _ x => hη₀φ m x) 0 x
          · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            have hn' : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn
            have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
            have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
              one_div_le_one_div_of_le (by positivity) hn'
            have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
              one_div_le_one_div_of_le (by positivity) hm'
            have h3 : (2 : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
            linarith
        · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).const_mul
            (X.massOn V₀).toReal
          simp only [mul_zero] at h
          refine h.congr fun N => ?_
          ring
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
      refine ⟨l, fun V hV η δ hηV hηδ hδ => ?_⟩
      have h0 := hclose (V ∪ V₀) (hccU _ _ hV hV₀) η η₀ (fun j => δ j + 1 / ((j : ℝ) + 1))
        (fun j => (hηV j).trans subset_union_left) (fun j => (hη₀V j).trans subset_union_right)
        (htri η η₀ δ (fun j => 1 / ((j : ℝ) + 1)) hηδ hη₀φ)
        (by simpa using hδ.add tendsto_one_div_add_atTop_nhds_zero_nat)
      have := h0.add hl
      simpa using this
    choose Lg hLg using hlim
    -- the total functional
    set L : (Eucl P → Covector (Eucl P) k) → ℝ := fun φ =>
      if h : Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U then Lg φ h.1 h.2.1 h.2.2 else 0
      with hL
    have hconv : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → ∀ V : Set (Eucl P), CompactlyContainedOpen V U →
          ∀ (η : ℕ → TestFormOn U k) (δ : ℕ → ℝ),
          (∀ j, tsupport (η j : DifferentialForm (Eucl P) k) ⊆ V) →
          (∀ j x, covectorEuclideanNorm (φ x - (η j : DifferentialForm (Eucl P) k) x) ≤ δ j) →
          Tendsto δ atTop (𝓝 0) → Tendsto (fun j => X (η j)) atTop (𝓝 (L φ)) := by
      intro φ hφ hφc hφU
      have : L φ = Lg φ hφ hφc hφU := by
        rw [hL]
        exact dif_pos ⟨hφ, hφc, hφU⟩
      rw [this]
      exact hLg φ hφ hφc hφU
    -- coercions of test-form operations
    have hcoe_add : ∀ a b : TestFormOn U k, ((a + b : TestFormOn U k) : DifferentialForm (Eucl P) k) =
        (a : DifferentialForm (Eucl P) k) + (b : DifferentialForm (Eucl P) k) := fun a b => rfl
    have hcoe_smul : ∀ (c : ℝ) (a : TestFormOn U k),
        ((c • a : TestFormOn U k) : DifferentialForm (Eucl P) k) = c • (a : DifferentialForm (Eucl P) k) :=
      fun c a => rfl
    refine ⟨L, fun ω => ?_, fun φ ψ hφ hφc hφU hψ hψc hψU => ?_, fun c φ hφ hφc hφU => ?_,
      fun V φ hV hVU hφ hφc hφV hφ1 => ?_⟩
    · -- `L` extends `X`
      have hω : Continuous (ω : DifferentialForm (Eucl P) k) := ω.2.1.1.continuous
      obtain ⟨i, hi⟩ := hcov _ ω.2.1.2 ω.2.2
      have hb : ∀ (j : ℕ) x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x -
          (ω : DifferentialForm (Eucl P) k) x) ≤ (0 : ℝ) := fun j x => by simp
      have h := hconv _ hω ω.2.1.2 ω.2.2 (Wx i) (hWx i) (fun _ => ω) (fun _ => 0) (fun _ => hi)
        hb tendsto_const_nhds
      exact tendsto_nhds_unique h tendsto_const_nhds
    · -- additivity
      obtain ⟨V₁, hV₁, η₁, hη₁V, hη₁φ⟩ := hseq φ hφ hφc hφU
      obtain ⟨V₂, hV₂, η₂, hη₂V, hη₂ψ⟩ := hseq ψ hψ hψc hψU
      have hsupp : ∀ j, tsupport ((η₁ j + η₂ j : TestFormOn U k) : DifferentialForm (Eucl P) k) ⊆
          V₁ ∪ V₂ := by
        intro j
        rw [hcoe_add]
        exact (tsupport_add _ _).trans (union_subset_union (hη₁V j) (hη₂V j))
      have hb : ∀ (j : ℕ) x, covectorEuclideanNorm ((φ + ψ) x -
          ((η₁ j + η₂ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x) ≤
          1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) := by
        intro j x
        have e : (φ + ψ) x - ((η₁ j + η₂ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x =
            (φ x - (η₁ j : DifferentialForm (Eucl P) k) x) +
              (ψ x - (η₂ j : DifferentialForm (Eucl P) k) x) := by
          rw [hcoe_add, Pi.add_apply, Pi.add_apply]
          abel
        rw [e]
        exact (hN_add _ _).trans (add_le_add (hη₁φ j x) (hη₂ψ j x))
      have hδ : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
        have h1n : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using h1n.add h1n
      have hsum := hconv (φ + ψ) (hφ.add hψ) (hφc.add hψc)
        ((tsupport_add _ _).trans (union_subset hφU hψU)) (V₁ ∪ V₂) (hccU _ _ hV₁ hV₂)
        (fun j => η₁ j + η₂ j) _ hsupp hb hδ
      have h1 := hconv φ hφ hφc hφU V₁ hV₁ η₁ _ hη₁V hη₁φ tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := hconv ψ hψ hψc hψU V₂ hV₂ η₂ _ hη₂V hη₂ψ tendsto_one_div_add_atTop_nhds_zero_nat
      refine tendsto_nhds_unique hsum ?_
      refine (h1.add h2).congr fun j => ?_
      exact (map_add X.toCurrent _ _).symm
    · -- homogeneity
      obtain ⟨V₁, hV₁, η₁, hη₁V, hη₁φ⟩ := hseq φ hφ hφc hφU
      have hcs : tsupport (c • φ) ⊆ U := (tsupport_smul_subset_right (fun _ => c) φ).trans hφU
      have hsupp : ∀ j, tsupport ((c • η₁ j : TestFormOn U k) : DifferentialForm (Eucl P) k) ⊆ V₁ := by
        intro j
        rw [hcoe_smul]
        exact (tsupport_smul_subset_right (fun _ => c) _).trans (hη₁V j)
      have hb : ∀ (j : ℕ) x, covectorEuclideanNorm ((c • φ) x -
          ((c • η₁ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x) ≤ |c| * (1 / ((j : ℝ) + 1)) := by
        intro j x
        have e : (c • φ) x - ((c • η₁ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x =
            c • (φ x - (η₁ j : DifferentialForm (Eucl P) k) x) := by
          rw [hcoe_smul, Pi.smul_apply, Pi.smul_apply, smul_sub]
        rw [e, hN_smul]
        exact mul_le_mul_of_nonneg_left (hη₁φ j x) (abs_nonneg c)
      have hδ : Tendsto (fun j : ℕ => |c| * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |c|
      have hsm := hconv (c • φ) (hφ.const_smul c) hφc.smul_left hcs V₁ hV₁ (fun j => c • η₁ j) _
        hsupp hb hδ
      have h1 := hconv φ hφ hφc hφU V₁ hV₁ η₁ _ hη₁V hη₁φ tendsto_one_div_add_atTop_nhds_zero_nat
      refine tendsto_nhds_unique hsm ?_
      refine (h1.const_mul c).congr fun j => ?_
      show c * X (η₁ j) = X (c • η₁ j)
      rw [map_smul, smul_eq_mul]
    · -- mass bound
      obtain ⟨i, hi⟩ := hcov _ hφc (hφV.trans hVU)
      choose η hηV hηφ using fun j : ℕ => Submission.cmb_exists_testForm_uniform_approx P k U
        (V ∩ Wx i) φ (hV.inter (hWx i).1) (inter_subset_left.trans hVU) hφ hφc
        (subset_inter hφV hi) (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
      have hlimη := hconv φ hφ hφc (hφV.trans hVU) (Wx i) (hWx i) η _
        (fun j => (hηV j).trans inter_subset_right) hηφ tendsto_one_div_add_atTop_nhds_zero_nat
      obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ j, s j = (1 + 1 / ((j : ℝ) + 1))⁻¹ := ⟨_, fun j => rfl⟩
      have hs0 : ∀ j, 0 < s j := fun j => by rw [hs]; positivity
      have hslim : Tendsto s atTop (𝓝 1) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)).inv₀ (by norm_num)
        rw [show s = fun j : ℕ => (1 + 1 / ((j : ℝ) + 1))⁻¹ from funext hs]
        simpa using h
      have hadm : ∀ j, s j • η j ∈ massAdmissibleOn U k V := by
        intro j
        refine ⟨?_, fun x => ?_⟩
        · rw [hcoe_smul]
          exact (tsupport_smul_subset_right (fun _ => s j) _).trans ((hηV j).trans inter_subset_left)
        · rw [hcoe_smul, Pi.smul_apply, hN_smul, abs_of_pos (hs0 j)]
          have hle : covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x) ≤
              1 + 1 / ((j : ℝ) + 1) := by
            have h := hN_sub ((η j : DifferentialForm (Eucl P) k) x) 0 (φ x)
            simp only [sub_zero] at h
            rw [hN_comm] at h
            linarith [hφ1 x, hηφ j x]
          calc s j * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
              ≤ s j * (1 + 1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left hle (hs0 j).le
            _ = 1 := by rw [hs]; exact inv_mul_cancel₀ (by positivity)
      have hval : Tendsto (fun j => X (s j • η j)) atTop (𝓝 (L φ)) := by
        have h := hslim.mul hlimη
        rw [one_mul] at h
        refine h.congr fun j => ?_
        show s j * X (η j) = X (s j • η j)
        rw [map_smul, smul_eq_mul]
      exact le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp hval)
        fun j => X.le_massOn (hadm j)
  -- Vector Riesz step: the mass measure `μ` and a density `v` with `|v| ≤ 1`.
  have core : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) →
      ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), IsMassMeasure X μ ∧
        IsMeasureRepresentation X μ v ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        ∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α := by
    intro P k U hU X hX
    classical
    obtain ⟨cv, emb, hcvn, hembcv, hembn⟩ := coeff P k
    obtain ⟨L, hLX, hLadd, hLsmul, hLbd⟩ := extL hU X hX
    obtain ⟨Wx, hWx, hcov⟩ := Submission.cmb_exists_compactly_contained_exhaustion P U hU
    haveI : LocallyCompactSpace U := hU.locallyCompactSpace
    -- zero extension from `U` of compactly supported continuous coefficient vectors
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin k → Fin P)) →
        Eucl P → Covector (Eucl P) k,
        ∀ f x, Φ f x = emb (if hx : x ∈ U then f ⟨x, hx⟩ else 0) :=
      ⟨fun f x => emb (if hx : x ∈ U then f ⟨x, hx⟩ else 0), fun _ _ => rfl⟩
    have hΦprop : ∀ f : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin k → Fin P)),
        Continuous (Φ f) ∧ HasCompactSupport (Φ f) ∧ tsupport (Φ f) ⊆ Subtype.val '' tsupport f := by
      intro f
      have hKc : IsCompact (Subtype.val '' tsupport f) :=
        f.hasCompactSupport.image continuous_subtype_val
      have hsupp : tsupport (fun x : Eucl P => if hx : x ∈ U then f ⟨x, hx⟩ else 0) ⊆
          Subtype.val '' tsupport f := by
        refine closure_minimal (fun x hx => ?_) hKc.isClosed
        by_cases hxU : x ∈ U
        · refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
          have hx' : f ⟨x, hxU⟩ ≠ 0 := by simpa [Function.mem_support, hxU] using hx
          exact Function.mem_support.2 hx'
        · simp [hxU] at hx
      have hcont : Continuous (fun x : Eucl P => if hx : x ∈ U then f ⟨x, hx⟩ else 0) := by
        refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
          (hsupp.trans (Subtype.coe_image_subset _ _))
        rw [continuousOn_iff_continuous_restrict]
        convert f.continuous using 1
        funext y
        simp [Set.restrict_apply, y.2]
      have e : Φ f = fun x => emb (if hx : x ∈ U then f ⟨x, hx⟩ else 0) := funext (hΦdef f)
      have ht : tsupport (Φ f) ⊆ Subtype.val '' tsupport f := by
        rw [e]
        exact (tsupport_comp_subset (map_zero emb) _).trans hsupp
      refine ⟨?_, hKc.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩
      rw [e]
      exact emb.continuous.comp hcont
    have hΦU : ∀ f, tsupport (Φ f) ⊆ U := fun f => (hΦprop f).2.2.trans (Subtype.coe_image_subset _ _)
    have hΦadd : ∀ f g, Φ (f + g) = Φ f + Φ g := by
      intro f g
      funext x
      simp only [hΦdef, Pi.add_apply]
      by_cases hx : x ∈ U <;> simp [hx]
    have hΦsmul : ∀ (c : ℝ) f, Φ (c • f) = c • Φ f := by
      intro c f
      funext x
      simp only [hΦdef, Pi.smul_apply]
      by_cases hx : x ∈ U <;> simp [hx]
    have hΦnorm : ∀ f (C : ℝ), 0 ≤ C → (∀ y, ‖f y‖ ≤ C) → ∀ x, covectorEuclideanNorm (Φ f x) ≤ C := by
      intro f C hC hf x
      rw [hΦdef]
      refine (hembn _).trans ?_
      by_cases hx : x ∈ U
      · rw [dif_pos hx]; exact hf _
      · rw [dif_neg hx, norm_zero]; exact hC
    -- the vector functional on `C_c(U; ℝ^N)`
    obtain ⟨Lc, hLc⟩ : ∃ Lc : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin k → Fin P)) →ₗ[ℝ] ℝ,
        ∀ f, Lc f = L (Φ f) :=
      ⟨{ toFun := fun f => L (Φ f)
         map_add' := fun f g => by
           show L (Φ (f + g)) = L (Φ f) + L (Φ g)
           rw [hΦadd]
           exact hLadd _ _ (hΦprop f).1 (hΦprop f).2.1 (hΦU f) (hΦprop g).1 (hΦprop g).2.1 (hΦU g)
         map_smul' := fun c f => by
           show L (Φ (c • f)) = (RingHom.id ℝ) c • L (Φ f)
           rw [hΦsmul, RingHom.id_apply, smul_eq_mul]
           exact hLsmul c _ (hΦprop f).1 (hΦprop f).2.1 (hΦU f) }, fun f => rfl⟩
    have hLcb : Poincare.SimonGMT.Chapter01.IsLocallyBoundedCcFunctional Lc := by
      intro K hK
      obtain ⟨i, hi⟩ := hcov _ (hK.image continuous_subtype_val) (Subtype.coe_image_subset _ _)
      refine ⟨(X.massOn (Wx i)).toReal, ?_⟩
      rintro _ ⟨f, ⟨hf1, hfK⟩, rfl⟩
      rw [hLc]
      have h := hLbd (Wx i) (Φ f) (hWx i).1 (subset_closure.trans (hWx i).2.2) (hΦprop f).1
        (hΦprop f).2.1 ((hΦprop f).2.2.trans ((image_mono hfK).trans hi))
        (hΦnorm f 1 zero_le_one hf1)
      exact (ENNReal.ofReal_le_iff_le_toReal (hX _ (hWx i)).ne).1 h
    -- the envelope (mass) measure on `U` and the `L¹` extension
    set μ₀ : Measure U := Poincare.SimonGMT.Chapter01.vectorFunctionalEnvelopeMeasure Lc hLcb with hμ₀
    haveI : μ₀.Regular := Poincare.SimonGMT.Chapter01.vectorFunctionalEnvelopeMeasure_regular Lc hLcb
    obtain ⟨Lbar, hLbar1, hLbarext⟩ :=
      Poincare.SimonGMT.Chapter01.simon_theorem_4_14_l1_extension Lc hLcb
    -- a bounded Borel density, glued from the compact dual fields
    have hKc : ∀ n, IsCompact (compactCovering U n) := isCompact_compactCovering U
    have hKex : ∀ y : U, ∃ n, y ∈ compactCovering U n := fun y => by
      have hy : y ∈ ⋃ n, compactCovering U n := by rw [iUnion_compactCovering]; exact mem_univ y
      simpa using hy
    obtain ⟨ν, hνm, hνeq⟩ : ∃ ν : U → EuclideanSpace ℝ (Fin k → Fin P), Measurable ν ∧
        ∀ y, ∃ n, y ∈ compactCovering U n ∧ ν y =
          Poincare.SimonGMT.Chapter01.compactL1DualField μ₀ (compactCovering U n) (hKc n) Lbar hLbar1 y :=
      ⟨_, Measurable.find (p := fun n y => y ∈ compactCovering U n)
        (fun n => (Poincare.SimonGMT.Chapter01.compactL1DualField_stronglyMeasurable μ₀ _ (hKc n)
          Lbar hLbar1).measurable) (fun n => (hKc n).measurableSet) hKex,
        fun y => ⟨_, Nat.find_spec (hKex y), rfl⟩⟩
    have hν1 : ∀ y, ‖ν y‖ ≤ 1 := by
      intro y
      obtain ⟨n, -, hn⟩ := hνeq y
      rw [hn]
      exact Poincare.SimonGMT.Chapter01.compactL1DualField_norm_le_one μ₀ _ (hKc n) Lbar hLbar1 y
    have hrep : ∀ f : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin k → Fin P)),
        Lc f = ∫ y, inner ℝ (f y) (ν y) ∂μ₀ := by
      intro f
      rw [← hLbarext f, Poincare.SimonGMT.Chapter01.compactL1DualField_represents_test μ₀ Lbar hLbar1 f]
      have hae : ∀ᵐ y ∂(μ₀.restrict (tsupport f)),
          Poincare.SimonGMT.Chapter01.compactL1DualField μ₀ (tsupport f) f.hasCompactSupport Lbar
            hLbar1 y = ν y := by
        have h1 : ∀ n, ∀ᵐ y ∂(μ₀.restrict (tsupport f)), y ∈ compactCovering U n →
            Poincare.SimonGMT.Chapter01.compactL1DualField μ₀ (tsupport f) f.hasCompactSupport Lbar
              hLbar1 y =
            Poincare.SimonGMT.Chapter01.compactL1DualField μ₀ (compactCovering U n) (hKc n) Lbar
              hLbar1 y := by
          intro n
          have h := Poincare.SimonGMT.Chapter01.compactL1DualField_ae_eq_inter μ₀ (tsupport f)
            f.hasCompactSupport (compactCovering U n) (hKc n) Lbar hLbar1
          rw [inter_comm, ← Measure.restrict_restrict (hKc n).measurableSet] at h
          exact (ae_restrict_iff' (hKc n).measurableSet).1 h
        filter_upwards [ae_all_iff.2 h1] with y hy
        obtain ⟨n, hn, hνn⟩ := hνeq y
        rw [hνn]
        exact hy n hn
      calc ∫ y in tsupport f, inner ℝ (f y)
            (Poincare.SimonGMT.Chapter01.compactL1DualField μ₀ (tsupport f) f.hasCompactSupport Lbar
              hLbar1 y) ∂μ₀
          = ∫ y in tsupport f, inner ℝ (f y) (ν y) ∂μ₀ :=
            integral_congr_ae (hae.mono fun y hy => by simp only [hy])
        _ = ∫ y, inner ℝ (f y) (ν y) ∂μ₀ :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
              rw [image_eq_zero_of_notMem_tsupport hy, inner_zero_left]
    -- coefficient functions of test forms
    have hfω : ∀ ω : TestFormOn U k, ∃ f : CompactlySupportedContinuousMap U
        (EuclideanSpace ℝ (Fin k → Fin P)), ∀ y, f y = cv ((ω : DifferentialForm (Eucl P) k) y) := by
      intro ω
      have hc : Continuous (fun y : U => cv ((ω : DifferentialForm (Eucl P) k) y)) :=
        cv.continuous.comp (ω.2.1.1.continuous.comp continuous_subtype_val)
      have hpre : IsCompact (Subtype.val ⁻¹' tsupport (ω : DifferentialForm (Eucl P) k) : Set U) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 ω.2.2]
        exact ω.2.1.2
      have hcs : HasCompactSupport (fun y : U => cv ((ω : DifferentialForm (Eucl P) k) y)) := by
        refine hpre.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun y hy => ?_)
          ((isClosed_tsupport _).preimage continuous_subtype_val))
        show (y : Eucl P) ∈ tsupport (ω : DifferentialForm (Eucl P) k)
        apply subset_tsupport
        intro h0
        apply hy
        simp [h0]
      exact ⟨⟨⟨_, hc⟩, hcs⟩, fun y => rfl⟩
    have hΦω : ∀ (ω : TestFormOn U k) (f : CompactlySupportedContinuousMap U
        (EuclideanSpace ℝ (Fin k → Fin P))), (∀ y, f y = cv ((ω : DifferentialForm (Eucl P) k) y)) →
        Φ f = (ω : DifferentialForm (Eucl P) k) := by
      intro ω f hf
      funext x
      rw [hΦdef]
      by_cases hx : x ∈ U
      · rw [dif_pos hx, hf, hembcv]
      · rw [dif_neg hx, map_zero]
        exact (image_eq_zero_of_notMem_tsupport (fun h => hx (ω.2.2 h))).symm
    -- the density on `ℝ^P`
    obtain ⟨v, hvU, hvn⟩ : ∃ v : Eucl P → NVector (Eucl P) k,
        (∀ x (hx : x ∈ U) α, v x α = inner ℝ (ν ⟨x, hx⟩) (cv α)) ∧ ∀ x, x ∉ U → v x = 0 :=
      ⟨fun x => if hx : x ∈ U then (innerSL ℝ (ν ⟨x, hx⟩)).comp cv else 0,
        fun x hx α => by simp [hx], fun x hx => by simp [hx]⟩
    have hvb : ∀ x α, |v x α| ≤ covectorEuclideanNorm α := by
      intro x α
      by_cases hx : x ∈ U
      · rw [hvU x hx]
        calc |inner ℝ (ν ⟨x, hx⟩) (cv α)| ≤ ‖ν ⟨x, hx⟩‖ * ‖cv α‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * ‖cv α‖ := mul_le_mul_of_nonneg_right (hν1 _) (norm_nonneg _)
          _ = covectorEuclideanNorm α := by rw [one_mul, hcvn]
      · rw [hvn x hx, ContinuousLinearMap.zero_apply, abs_zero]
        exact covectorEuclideanNorm_nonneg α
    have hme : MeasurableEmbedding (Subtype.val : U → Eucl P) :=
      MeasurableEmbedding.subtype_coe hU.measurableSet
    have hrepX : IsMeasureRepresentation X (μ₀.map Subtype.val) v := by
      intro ω
      obtain ⟨f, hf⟩ := hfω ω
      have hcomp : (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) ∘ Subtype.val =
          fun y => inner ℝ (f y) (ν y) := by
        funext y
        simp only [Function.comp_apply]
        rw [hvU y y.2, hf, real_inner_comm]
      have hfint : Integrable (fun y => inner ℝ (f y) (ν y)) μ₀ := by
        refine Integrable.mono' (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm
          (f.continuous.aestronglyMeasurable.inner hνm.aestronglyMeasurable)
          (Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs]
        calc |inner ℝ (f y) (ν y)| ≤ ‖f y‖ * ‖ν y‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖f y‖ * 1 := mul_le_mul_of_nonneg_left (hν1 y) (norm_nonneg _)
          _ = ‖f y‖ := mul_one _
      refine ⟨?_, ?_⟩
      · rw [hme.integrable_map_iff, hcomp]
        exact hfint
      · rw [hme.integral_map]
        calc X ω = Lc f := by rw [hLc, hΦω ω f hf, hLX]
          _ = ∫ y, inner ℝ (f y) (ν y) ∂μ₀ := hrep f
          _ = ∫ y, v (y : Eucl P) ((ω : DifferentialForm (Eucl P) k) y) ∂μ₀ :=
            (congrArg (fun g => ∫ y, g y ∂μ₀) hcomp).symm
    have hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ₀.map Subtype.val K < ∞ := by
      intro K hK hKU
      rw [hme.map_apply]
      have hpre : IsCompact (Subtype.val ⁻¹' K : Set U) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]
        exact hK
      exact hpre.measure_lt_top
    have hmass : IsMassMeasure X (μ₀.map Subtype.val) := by
      refine ⟨?_, fun W hW => le_antisymm ?_ ?_⟩
      · rw [hme.map_apply]
        have : (Subtype.val ⁻¹' Uᶜ : Set U) = ∅ := by
          ext y
          simp [y.2]
        rw [this, measure_empty]
      · -- `μ(W) ≤ M_W(X)`: inner regularity, Urysohn, the envelope identity and the mass bound
        rw [hme.map_apply]
        have hWo : IsOpen (Subtype.val ⁻¹' W : Set U) := hW.1.preimage continuous_subtype_val
        rw [hWo.measure_eq_iSup_isCompact μ₀]
        refine iSup_le fun K => iSup_le fun hKW => iSup_le fun hK => ?_
        obtain ⟨g, hg1, hgc, hgW, hg01⟩ :=
          exists_continuousMap_one_of_isCompact_subset_isOpen hK hWo hKW
        let gN : CompactlySupportedContinuousMap U ℝ≥0 :=
          { toFun := fun y => Real.toNNReal (g y)
            continuous_toFun := continuous_real_toNNReal.comp g.continuous
            hasCompactSupport' := HasCompactSupport.comp_left (g := Real.toNNReal) hgc
              Real.toNNReal_zero }
        have hgN : ∀ y, (gN y : ℝ) = g y := fun y => Real.coe_toNNReal _ (hg01 y).1
        have hgi : Integrable (fun y => (gN y : ℝ)) μ₀ :=
          (NNReal.continuous_coe.comp gN.continuous).integrable_of_hasCompactSupport
            (gN.hasCompactSupport.comp_left NNReal.coe_zero)
        have h1 : μ₀ K ≤ ENNReal.ofReal (∫ y, (gN y : ℝ) ∂μ₀) := by
          rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => NNReal.coe_nonneg _),
            ← lintegral_indicator_one hK.measurableSet]
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ K
          · rw [Set.indicator_of_mem hy, hgN, hg1 hy]
            simp
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
        have h2 : sSup (Lc '' {f | ∀ y, ‖f y‖ ≤ (gN y : ℝ)}) ≤ (X.massOn W).toReal := by
          refine csSup_le ⟨0, 0, fun y => by simp, map_zero Lc⟩ ?_
          rintro _ ⟨f, hf, rfl⟩
          rw [hLc]
          have htsf : tsupport f ⊆ tsupport g := by
            refine closure_mono fun y hy => ?_
            intro hg0
            apply hy
            have := hf y
            rw [hgN, hg0] at this
            exact norm_le_zero_iff.1 this
          have h := hLbd W (Φ f) hW.1 (subset_closure.trans hW.2.2) (hΦprop f).1 (hΦprop f).2.1
            ((hΦprop f).2.2.trans (by rintro _ ⟨y, hy, rfl⟩; exact hgW (htsf hy)))
            (hΦnorm f 1 zero_le_one fun y => (hf y).trans (by rw [hgN]; exact (hg01 y).2))
          exact (ENNReal.ofReal_le_iff_le_toReal (hX W hW).ne).1 h
        calc μ₀ K ≤ ENNReal.ofReal (∫ y, (gN y : ℝ) ∂μ₀) := h1
          _ = ENNReal.ofReal (sSup (Lc '' {f | ∀ y, ‖f y‖ ≤ (gN y : ℝ)})) := by
            rw [Poincare.SimonGMT.Chapter01.simon_theorem_4_14_positive_envelope Lc hLcb gN]
          _ ≤ ENNReal.ofReal (X.massOn W).toReal := ENNReal.ofReal_le_ofReal h2
          _ = X.massOn W := ENNReal.ofReal_toReal (hX W hW).ne
      · -- `M_W(X) ≤ μ(W)`: the representation and `|v| ≤ 1`
        apply sSup_le
        rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
        dsimp only
        rw [(hrepX ω).2]
        have hpt : ∀ x, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ≤ W.indicator 1 x := by
          intro x
          by_cases hx : x ∈ W
          · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_one.2 ((hvb x _).trans (hω1 x))
          · have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => hx (hωW h))
            simp [h0]
        calc ENNReal.ofReal (∫ x, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₀.map Subtype.val)
            ≤ ‖∫ x, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₀.map Subtype.val‖ₑ := by
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (le_abs_self _)
          _ ≤ ∫⁻ x, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ∂μ₀.map Subtype.val :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ x, W.indicator 1 x ∂μ₀.map Subtype.val := lintegral_mono hpt
          _ = μ₀.map Subtype.val W := lintegral_indicator_one hW.1.measurableSet
    exact ⟨μ₀.map Subtype.val, v, hmass, hrepX, hfin, hvb⟩
  -- (R2): mass measure, existence of restrictions, mass identity.
  refine ⟨R0, R1, fun P k U hU X hX => ?_⟩
  obtain ⟨μ, v, hmass, hrep, hfin, hv⟩ := core P k U hU X hX
  refine ⟨μ, hmass, fun A hA => ?_, fun A S hres W hW hWU => ?_⟩
  · obtain ⟨S, hS⟩ := restrCur μ v (fun ω => (hrep ω).1) hfin hv A
    exact ⟨S, hA, μ, v, hrep, hS⟩
  · obtain ⟨hA, μ', v', hrep', hS⟩ := hres
    have hS2 : ∀ ω : TestFormOn U k,
        S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ :=
      fun ω => (hS ω).trans (setInt hU hrep' hrep hA ω)
    exact massEq hU hmass hrep hfin hv hA S hS2 hW hWU
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

/-- **Pairing expansion** (Simon Ch. 6, 1.2 and 1.7, pp. 132–133; used for 6.2, p. 169).  For an
`n`-vector `w` and an `n`-covector `c` on `ℝ^P`, `w(c) = ∑_I c_I · w(dx^I)`, the sum over the
increasing multi-indices `I`, where `c_I = c(e_{I(1)}, …, e_{I(n)})` and
`dx^I = dx^{I(1)} ∧ ⋯ ∧ dx^{I(n)}`; moreover `|c_I| ≤ |c|`.  Since `dx^I(e_J) = δ_{IJ}` on
increasing multi-indices, `c` and `∑_I c_I dx^I` have the same increasing coordinates, hence are
equal (1.2), and `w` is linear. -/
theorem Submission.polyhedral_approx_pairing_expansion : ∀ (P n : ℕ) (w : NVector (Eucl P) n) (c : Covector (Eucl P) n), w c = ∑ I : SimonMultiIndex n P, euclideanCovectorCoordinate c I * w (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) ∧ ∀ I : SimonMultiIndex n P, |euclideanCovectorCoordinate c I| ≤ covectorEuclideanNorm c := by
  intro P n w c
  refine ⟨?_, Submission.polyhedral_approx_pairing_coordinate_bound P n c⟩
  -- `c = ∑_I c_I • dx^I`: both sides have the same increasing coordinates.
  have hc : c = ∑ I : SimonMultiIndex n P,
      euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) := by
    refine Submission.polyhedral_approx_pairing_covector_ext P n _ _ fun J => ?_
    -- The `J`-th coordinate of the sum is `∑_I c_I · dx^I(e_J)`.
    have hsum : euclideanCovectorCoordinate (∑ I : SimonMultiIndex n P,
          euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J =
        ∑ I : SimonMultiIndex n P, euclideanCovectorCoordinate c I *
          euclideanCovectorCoordinate (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) J := by
      simp only [euclideanCovectorCoordinate, ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    -- Only `I = J` contributes, since `dx^I(e_J) = δ_{IJ}`.
    rw [hsum, Finset.sum_eq_single J]
    · rw [(Submission.polyhedral_approx_pairing_wedge_kronecker P n J).1, mul_one]
    · intro I _ hIJ
      rw [(Submission.polyhedral_approx_pairing_wedge_kronecker P n I).2 J (Ne.symm hIJ), mul_zero]
    · intro hJ
      exact absurd (Finset.mem_univ J) hJ
  -- `w(∑_I c_I • dx^I) = ∑_I c_I · w(dx^I)` by linearity.
  calc w c = w (∑ I : SimonMultiIndex n P,
        euclideanCovectorCoordinate c I • wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) :=
        congrArg w hc
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
/-- An integrable density is a difference of two finite measures (used for the uniqueness of the
vector measure in Simon Ch. 6, (2.7)–(2.9), p. 136): `ν^± = μ.withDensity (ofReal ∘ (±g))` are
finite and `∫ b dν⁺ − ∫ b dν⁻ = ∫ b g dμ` for every bounded Borel `b`. -/
theorem Submission.polyhedral_approx_density_split :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (g : Eucl P → ℝ), Integrable g μ →
      ∃ νpos νneg : Measure (Eucl P), IsFiniteMeasure νpos ∧ IsFiniteMeasure νneg ∧
        ∀ b : Eucl P → ℝ, Measurable b → (∃ C : ℝ, ∀ x, |b x| ≤ C) →
          ∫ x, b x ∂νpos - ∫ x, b x ∂νneg = ∫ x, b x * g x ∂μ := by
  intro P μ g hg
  have hg' : Integrable (fun x => -g x) μ := hg.neg
  refine ⟨μ.withDensity fun x => ENNReal.ofReal (g x),
    μ.withDensity fun x => ENNReal.ofReal (-g x),
    isFiniteMeasure_withDensity_ofReal hg.2, isFiniteMeasure_withDensity_ofReal hg'.2, ?_⟩
  rintro b hb ⟨C, hC⟩
  -- `∫ b d(μ.withDensity (ofReal ∘ f)) = ∫ f⁺ b dμ`, since `(ofReal r).toReal = r⁺`.
  have hwd : ∀ f : Eucl P → ℝ, Integrable f μ →
      ∫ x, b x ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) = ∫ x, max (f x) 0 * b x ∂μ := by
    intro f hf
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.1.aemeasurable.ennreal_ofReal
      (ae_of_all μ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  -- `f⁺ b` is integrable: `f⁺` is integrable and `b` is measurable and bounded.
  have hint : ∀ f : Eucl P → ℝ, Integrable f μ → Integrable (fun x => max (f x) 0 * b x) μ :=
    fun f hf => hf.pos_part.mul_bdd hb.aestronglyMeasurable
      (ae_of_all μ fun x => (Real.norm_eq_abs (b x)).le.trans (hC x))
  rw [hwd g hg, hwd (fun x => -g x) hg', ← integral_sub (hint g hg) (hint (fun x => -g x) hg')]
  -- `g⁺ − (−g)⁺ = g`.
  congr 1
  ext x
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
/-- Finite measures `ν₁, ν₂` on `ℝ^P` that agree on every `C^∞` function with compact support in
an open set `O` agree on every function `b` vanishing outside `O` (the uniqueness behind Simon
Ch. 6, (2.7)–(2.9), p. 136).  For `ν = ν₁ + ν₂` and the real densities `fᵢ = (dνᵢ/dν).toReal`,
the Lebesgue decomposition gives `∫ c dνᵢ = ∫ fᵢ c dν` for every `c`; the fundamental lemma of
the calculus of variations gives `f₁ = f₂` `ν`-a.e. on `O`, hence `f₁ b = f₂ b` `ν`-a.e. -/
theorem Submission.polyhedral_approx_finite_smooth_ext :
    ∀ (P : ℕ) (ν₁ ν₂ : Measure (Eucl P)), IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
      ∀ O : Set (Eucl P), IsOpen O →
      (∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ O → ∫ x, ψ x ∂ν₁ = ∫ x, ψ x ∂ν₂) →
      ∀ b : Eucl P → ℝ, (∀ x, x ∉ O → b x = 0) → ∫ x, b x ∂ν₁ = ∫ x, b x ∂ν₂ := by
  intro P ν₁ ν₂ h₁ h₂ O hO hψ b hb
  -- Step 1: `ν = ν₁ + ν₂` is finite and dominates `ν₁` and `ν₂`.
  set ν : Measure (Eucl P) := ν₁ + ν₂
  have hac₁ : ν₁ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right ν₂
  have hac₂ : ν₂ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' ν₁
  -- Steps 2–4: for finite `μ ≪ ν` the singular part vanishes, so `μ = ν.withDensity (dμ/dν)`;
  -- hence `∫ c dμ = ∫ (dμ/dν).toReal * c dν` for every `c`, and `(dμ/dν).toReal` is
  -- `ν`-integrable.
  have key : ∀ μ : Measure (Eucl P), IsFiniteMeasure μ → μ ≪ ν →
      Integrable (fun x => (μ.rnDeriv ν x).toReal) ν ∧
      ∀ c : Eucl P → ℝ, ∫ x, c x ∂μ = ∫ x, (μ.rnDeriv ν x).toReal * c x ∂ν := by
    intro μ hμ hac
    have hdec : μ = ν.withDensity (μ.rnDeriv ν) := by
      have h := Measure.haveLebesgueDecomposition_add μ ν
      rwa [Measure.singularPart_eq_zero_of_ac hac, zero_add] at h
    refine ⟨integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv μ ν).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top μ ν).ne, fun c => ?_⟩
    calc ∫ x, c x ∂μ = ∫ x, c x ∂(ν.withDensity (μ.rnDeriv ν)) := by
          conv_lhs => rw [hdec]
      _ = ∫ x, (μ.rnDeriv ν x).toReal • c x ∂ν :=
          integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv μ ν)
            (Measure.rnDeriv_lt_top μ ν) c
      _ = ∫ x, (μ.rnDeriv ν x).toReal * c x ∂ν := by simp only [smul_eq_mul]
  obtain ⟨hi₁, e₁⟩ := key ν₁ h₁ hac₁
  obtain ⟨hi₂, e₂⟩ := key ν₂ h₂ hac₂
  -- Steps 5–6: `f₁ - f₂` annihilates every smooth test function supported in `O`, so it
  -- vanishes `ν`-a.e. on `O`.
  have hF : ∀ᵐ x ∂ν, x ∈ O → (ν₁.rnDeriv ν x).toReal - (ν₂.rnDeriv ν x).toReal = 0 := by
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hi₁.sub hi₂).locallyIntegrable.locallyIntegrableOn O) ?_
    intro g hg hgc hgO
    have i₁ : Integrable (fun x => g x • (ν₁.rnDeriv ν x).toReal) ν :=
      hi₁.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    have i₂ : Integrable (fun x => g x • (ν₂.rnDeriv ν x).toReal) ν :=
      hi₂.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    have hg' := hψ g hg hgc hgO
    rw [e₁ g, e₂ g] at hg'
    simp only [smul_sub]
    rw [integral_sub i₁ i₂, sub_eq_zero]
    simpa only [smul_eq_mul, mul_comm] using hg'
  -- Step 7: `f₁ b = f₂ b` `ν`-a.e.: on `O` by steps 5–6, off `O` because `b = 0` there.
  rw [e₁ b, e₂ b]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  by_cases hxO : x ∈ O
  · rw [sub_eq_zero.mp (hx hxO)]
  · simp [hb x hxO]

/-- Integrable densities `g₁ μ₁`, `g₂ μ₂` that agree on every `C^∞` function with compact support
in an open set `O` agree on every bounded Borel `b` vanishing outside `O` (the uniqueness behind
Simon Ch. 6, (2.7)–(2.9), p. 136).  Split `gᵢ μᵢ = pᵢ − nᵢ` into finite measures
(`polyhedral_approx_density_split`).  The finite measures `λ₁ = p₁ + n₂`, `λ₂ = p₂ + n₁` satisfy
`∫ c dλ₁ − ∫ c dλ₂ = ∫ c g₁ dμ₁ − ∫ c g₂ dμ₂` for bounded Borel `c` (★), so they agree on smooth
tests in `O`, hence on `b` (`polyhedral_approx_finite_smooth_ext`); (★) with `c = b` concludes. -/
theorem Submission.polyhedral_approx_integrable_smooth_ext :
    ∀ (P : ℕ) (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), Integrable g₁ μ₁ →
      Integrable g₂ μ₂ → ∀ O : Set (Eucl P), IsOpen O →
      (∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ O → ∫ x, ψ x * g₁ x ∂μ₁ = ∫ x, ψ x * g₂ x ∂μ₂) →
      ∀ b : Eucl P → ℝ, Measurable b → (∃ C : ℝ, ∀ x, |b x| ≤ C) → (∀ x, x ∉ O → b x = 0) →
        ∫ x, b x * g₁ x ∂μ₁ = ∫ x, b x * g₂ x ∂μ₂ := by
  intro P μ₁ μ₂ g₁ g₂ hg₁ hg₂ O hO hψ b hb hbC hbO
  -- Step 1: `gᵢ μᵢ = pᵢ − nᵢ` with `pᵢ`, `nᵢ` finite.
  obtain ⟨p₁, n₁, hp₁, hn₁, h₁⟩ := Submission.polyhedral_approx_density_split P μ₁ g₁ hg₁
  obtain ⟨p₂, n₂, hp₂, hn₂, h₂⟩ := Submission.polyhedral_approx_density_split P μ₂ g₂ hg₂
  -- Steps 2–3: `λ₁ = p₁ + n₂` and `λ₂ = p₂ + n₁` are finite, and for bounded Borel `c`
  -- (★) `∫ c dλ₁ − ∫ c dλ₂ = ∫ c g₁ dμ₁ − ∫ c g₂ dμ₂`.
  have key : ∀ c : Eucl P → ℝ, Measurable c → (∃ C : ℝ, ∀ x, |c x| ≤ C) →
      ∫ x, c x ∂(p₁ + n₂) - ∫ x, c x ∂(p₂ + n₁) =
        ∫ x, c x * g₁ x ∂μ₁ - ∫ x, c x * g₂ x ∂μ₂ := by
    rintro c hc ⟨C, hC⟩
    -- A bounded Borel `c` is integrable against every finite measure.
    have hint : ∀ (ν : Measure (Eucl P)) [IsFiniteMeasure ν], Integrable c ν := fun ν _ =>
      Integrable.of_bound hc.aestronglyMeasurable C
        (ae_of_all ν fun x => (Real.norm_eq_abs (c x)).le.trans (hC x))
    rw [integral_add_measure (hint p₁) (hint n₂), integral_add_measure (hint p₂) (hint n₁)]
    linarith [h₁ c hc ⟨C, hC⟩, h₂ c hc ⟨C, hC⟩]
  -- Step 4: by (★), `λ₁` and `λ₂` agree on smooth tests with compact support in `O`.
  have hsmooth : ∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → ∫ x, ψ x ∂(p₁ + n₂) = ∫ x, ψ x ∂(p₂ + n₁) := by
    intro ψ hψs hψc hψO
    obtain ⟨C, hC⟩ := hψs.continuous.bounded_above_of_compact_support hψc
    linarith [key ψ hψs.continuous.measurable
      ⟨C, fun x => (Real.norm_eq_abs (ψ x)).symm.le.trans (hC x)⟩, hψ ψ hψs hψc hψO]
  -- Step 5: hence `λ₁` and `λ₂` agree on `b`, which vanishes outside `O`.
  have hext := Submission.polyhedral_approx_finite_smooth_ext P (p₁ + n₂) (p₂ + n₁)
    inferInstance inferInstance O hO hsmooth b hbO
  -- Step 6: (★) with `c = b`.
  linarith [key b hb hbC]

/-- Uniqueness of the vector measure in Simon Ch. 6, (2.7)–(2.9) (p. 136), which makes `T ⌞ A`
well defined: if `g₁ μ₁` and `g₂ μ₂` (`gᵢ` locally `μᵢ`-integrable in `U`) agree on `C^∞`
functions with compact support in `U`, then `∫_A u g₁ dμ₁ = ∫_A u g₂ dμ₂` for every Borel `A`
and continuous `u` with compact support in `U`.  For an open `O ⊇ tsupport u` with compact
`L = closure O ⊆ U`, each `gᵢ` is `μᵢ⌞L`-integrable, the hypothesis passes to `μᵢ⌞L` on `O`,
and `1_A u` is bounded, Borel and vanishes outside `O`. -/
theorem Submission.polyhedral_approx_measure_uniqueness :
    ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ),
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn g₁ K μ₁ ∧ IntegrableOn g₂ K μ₂) →
      (∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U → ∫ x, ψ x * g₁ x ∂μ₁ = ∫ x, ψ x * g₂ x ∂μ₂) →
      ∀ A : Set (Eucl P), MeasurableSet A → ∀ u : Eucl P → ℝ, Continuous u →
        HasCompactSupport u → tsupport u ⊆ U →
          ∫ x in A, u x * g₁ x ∂μ₁ = ∫ x in A, u x * g₂ x ∂μ₂ := by
  intro P U hU μ₁ μ₂ g₁ g₂ hint hψ A hA u hu huc huU
  -- Step 1: an open `O` and a compact `L = closure O` with `tsupport u ⊆ O ⊆ L ⊆ U`; each `gᵢ`
  -- is `μᵢ⌞L`-integrable.
  obtain ⟨O, hO, huO, hLU, hL⟩ := exists_open_between_and_isCompact_closure huc hU huU
  have hOL : O ⊆ closure O := subset_closure
  obtain ⟨hi₁, hi₂⟩ := hint (closure O) hL hLU
  -- Step 2: integrating `f gᵢ` over `L` or over `ℝ^P` gives the same when `f = 0` outside `O`.
  have hloc : ∀ (μ : Measure (Eucl P)) (g f : Eucl P → ℝ), (∀ x, x ∉ O → f x = 0) →
      ∫ x in closure O, f x * g x ∂μ = ∫ x, f x * g x ∂μ := fun μ g f hf =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hf x fun h => hx (hOL h), zero_mul]
  -- Step 3: `g₁ (μ₁⌞L)` and `g₂ (μ₂⌞L)` agree on `C^∞` functions with compact support in `O`.
  have hψL : ∀ ψ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → ∫ x in closure O, ψ x * g₁ x ∂μ₁ = ∫ x in closure O, ψ x * g₂ x ∂μ₂ := by
    intro ψ hψs hψc hψO
    have hψ0 : ∀ x, x ∉ O → ψ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hψO h)
    rw [hloc μ₁ g₁ ψ hψ0, hloc μ₂ g₂ ψ hψ0]
    exact hψ ψ hψs hψc ((hψO.trans hOL).trans hLU)
  -- Step 4: `1_A u` is Borel, bounded and vanishes outside `O`.
  have hb : Measurable (A.indicator u) := hu.measurable.indicator hA
  have hbC : ∃ C : ℝ, ∀ x, |A.indicator u x| ≤ C := by
    obtain ⟨C, hC⟩ := hu.bounded_above_of_compact_support huc
    exact ⟨C, fun x => (Real.norm_eq_abs _).symm.le.trans
      ((norm_indicator_le_norm_self u x).trans (hC x))⟩
  have hb0 : ∀ x, x ∉ O → A.indicator u x = 0 := fun x hx =>
    Set.indicator_apply_eq_zero.mpr fun _ => image_eq_zero_of_notMem_tsupport fun h => hx (huO h)
  -- Step 5: `∫_A u gᵢ dμᵢ = ∫_L 1_A u gᵢ dμᵢ`; the integrable version on `O` concludes.
  have hA' : ∀ (μ : Measure (Eucl P)) (g : Eucl P → ℝ),
      ∫ x in A, u x * g x ∂μ = ∫ x in closure O, A.indicator u x * g x ∂μ := fun μ g => by
    rw [hloc μ g _ hb0, ← integral_indicator hA]
    simp only [Set.indicator_mul_left]
  rw [hA' μ₁ g₁, hA' μ₂ g₂]
  exact Submission.polyhedral_approx_integrable_smooth_ext P (μ₁.restrict (closure O))
    (μ₂.restrict (closure O)) g₁ g₂ hi₁ hi₂ O hO hψL (A.indicator u) hb hbC hb0

/-- **Simon Ch. 6, (2.9) and 3.1 (pp. 136, 146).**  If `T = τ(M, θ, ξ)` and `S = T ⌞ A`, then
`S = τ(M ∩ A, θ, ξ)`.  Let `(μ, v)` be the representation of `T` defining `S`.  For a covector
`c`, `⟨c, v⟩` is locally `μ`-integrable and `θ ⟨c, ξ⟩` is locally `Hⁿ ⌞ M`-integrable on `U`
(`polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`).  Both pair
with every smooth `ψ` to `T(ψ c)`, so `polyhedral_approx_measure_uniqueness` equates their
integrals over `A` against continuous compactly supported weights.  Expanding `ω` in the
coordinate wedges `dx^I` (`polyhedral_approx_pairing_expansion`), with the coordinates `ω_I` as
weights, and summing over `I` gives `S(ω) = ∫_A θ ⟨ω, ξ⟩ d(Hⁿ ⌞ M) = τ(M ∩ A, θ, ξ)(ω)`. -/
theorem Submission.polyhedral_approx_restriction_tau : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U n), IsRestriction T A S → ∀ ω : TestFormOn U n, S ω = tauAction n (M ∩ A) θ ξ ω := by
  intro P n U hU T M θ ξ hMθξ hT A S hS ω
  obtain ⟨hA, μ, v, hrep, hSω⟩ := hS
  -- For every covector `c`, `⟨c, v⟩` is locally `μ`-integrable and `θ ⟨c, ξ⟩` is locally
  -- `Hⁿ ⌞ M`-integrable on `U`.
  have hloc : ∀ (c : Covector (Eucl P) n) (K : Set (Eucl P)), IsCompact K → K ⊆ U →
      IntegrableOn (fun x => v x c) K μ ∧
        IntegrableOn (fun x => θ x * ξ x c) K ((μHE[n] : Measure (Eucl P)).restrict M) :=
    fun c K hK hKU =>
      ⟨Submission.polyhedral_approx_rt_integrableOn_apply P n U hU μ v (fun ω => (hrep ω).1)
          K hK hKU c,
        Submission.polyhedral_approx_rt_tau_integrableOn P n U M θ ξ hMθξ K hK hKU c⟩
  -- Both pair with a smooth `ψ` to `T(ψ c)`; hence their integrals over `A` against continuous
  -- compactly supported weights agree.
  have key : ∀ (c : Covector (Eucl P) n) (u : Eucl P → ℝ), Continuous u → HasCompactSupport u →
      tsupport u ⊆ U → ∫ x in A, u x * v x c ∂μ =
        ∫ x in A, u x * (θ x * ξ x c) ∂((μHE[n] : Measure (Eucl P)).restrict M) := by
    intro c
    refine Submission.polyhedral_approx_measure_uniqueness P U hU μ _ (fun x => v x c)
      (fun x => θ x * ξ x c) (hloc c) (fun ψ hψ hψc hψU => ?_) A hA
    -- `ψ c` is a test form in `U`.
    have hmem : (fun x => ψ x • c : DifferentialForm (Eucl P) n) ∈
        testFormOnSubmodule (E := Eucl P) U n :=
      ⟨⟨hψ.smul contDiff_const,
          IsCompact.of_isClosed_subset hψc (isClosed_tsupport _) (tsupport_smul_subset_left _ _)⟩,
        (tsupport_smul_subset_left _ _).trans hψU⟩
    calc ∫ x, ψ x * v x c ∂μ
        = ∫ x, v x (((⟨_, hmem⟩ : TestFormOn U n) : DifferentialForm (Eucl P) n) x) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show ψ x * v x c = v x (ψ x • c)
          rw [map_smul, smul_eq_mul]
      _ = tauAction n M θ ξ (⟨_, hmem⟩ : TestFormOn U n) :=
          (hrep ⟨_, hmem⟩).2.symm.trans (hT ⟨_, hmem⟩)
      _ = ∫ x, ψ x * (θ x * ξ x c) ∂((μHE[n] : Measure (Eucl P)).restrict M) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          show θ x * ξ x (ψ x • c) = ψ x * (θ x * ξ x c)
          rw [map_smul, smul_eq_mul]
          ring
  -- Weighted by a continuous compactly supported `u` with `tsupport u ⊆ U`, both coefficient
  -- functions are integrable.
  have hint : ∀ (c : Covector (Eucl P) n) (u : Eucl P → ℝ), Continuous u →
      HasCompactSupport u → tsupport u ⊆ U → Integrable (fun x => u x * v x c) μ ∧
        Integrable (fun x => u x * (θ x * ξ x c)) ((μHE[n] : Measure (Eucl P)).restrict M) := by
    intro c u hu hus huU
    exact ⟨(IntegrableOn.continuousOn_mul hu.continuousOn (hloc c (tsupport u) hus huU).1
        hus).integrable_of_forall_notMem_eq_zero
          fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx],
      (IntegrableOn.continuousOn_mul hu.continuousOn (hloc c (tsupport u) hus huU).2
        hus).integrable_of_forall_notMem_eq_zero
          fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]⟩
  -- The coordinates `ω_I = ω(e_{I 0}, …, e_{I (n-1)})` are continuous, with compact support
  -- in `U`.
  have hcoord : ∀ I : SimonMultiIndex n P,
      Continuous (fun x => euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I) ∧
        HasCompactSupport
          (fun x => euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I) ∧
        tsupport (fun x => euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I) ⊆
          U := by
    intro I
    have h0 : (fun c : Covector (Eucl P) n => euclideanCovectorCoordinate c I) 0 = 0 := by
      simp [euclideanCovectorCoordinate]
    exact ⟨(ContDiff.continuous ω.property.1.1).eval_const
        (fun j => EuclideanSpace.single (I j) (1 : ℝ)),
      ω.property.1.2.comp_left (g := fun c : Covector (Eucl P) n => euclideanCovectorCoordinate c I)
        h0,
      (tsupport_comp_subset
        (g := fun c : Covector (Eucl P) n => euclideanCovectorCoordinate c I) h0 _).trans
          ω.property.2⟩
  -- Expand `ω` in the coordinate wedges `dx^I` and sum over `I`.
  calc S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ := hSω ω
    _ = ∫ x in A, ∑ I : SimonMultiIndex n P,
          euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I *
            v x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x =>
          (Submission.polyhedral_approx_pairing_expansion P n (v x)
            ((ω : DifferentialForm (Eucl P) n) x)).1)
    _ = ∑ I : SimonMultiIndex n P, ∫ x in A,
          euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I *
            v x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))) ∂μ :=
        integral_finsetSum _ fun I _ =>
          (hint _ _ (hcoord I).1 (hcoord I).2.1 (hcoord I).2.2).1.integrableOn
    _ = ∑ I : SimonMultiIndex n P, ∫ x in A,
          euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I *
            (θ x * ξ x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))))
            ∂((μHE[n] : Measure (Eucl P)).restrict M) :=
        Finset.sum_congr rfl fun I _ => key _ _ (hcoord I).1 (hcoord I).2.1 (hcoord I).2.2
    _ = ∫ x in A, ∑ I : SimonMultiIndex n P,
          euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I *
            (θ x * ξ x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j))))
            ∂((μHE[n] : Measure (Eucl P)).restrict M) :=
        (integral_finsetSum _ fun I _ =>
          (hint _ _ (hcoord I).1 (hcoord I).2.1 (hcoord I).2.2).2.integrableOn).symm
    _ = ∫ x in A, θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)
          ∂((μHE[n] : Measure (Eucl P)).restrict M) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show ∑ I : SimonMultiIndex n P,
            euclideanCovectorCoordinate ((ω : DifferentialForm (Eucl P) n) x) I *
              (θ x * ξ x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j)))) =
          θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)
        rw [(Submission.polyhedral_approx_pairing_expansion P n (ξ x)
          ((ω : DifferentialForm (Eucl P) n) x)).1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by ring
    _ = tauAction n (M ∩ A) θ ξ ω := by
        rw [tauAction, Measure.restrict_restrict hA, inter_comm]
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

/-- **Lower half of the mass formula `M(T) = ∫ |T⃗| dμ_T` (Simon Ch. 6, 2.7–2.8; display (1) in the
proof of Lemma 3.13).**  If `(μ, κ)` represents `Y ∈ 𝒟_k(ℝ^N)` as in (2.7), then
`∫ |κ| dμ ≤ M(Y)` in `[0, ∞]`, where `|w| = (∑_γ w(dx^γ)²)^{1/2}` is the Euclidean norm of a
`k`-vector.  Let `M(Y) < ∞` and `R ∈ ℕ`.  The coordinates `κ^γ` are `μ`-integrable on `B_R`, so
for `ε > 0` there is a continuous form `ω` with `tsupport ω ⊆ B_R`, `|ω| ≤ 1` and
`∫_{B_R} |κ| dμ ≤ ∫ κ(ω) dμ + ε`; by (2.7) and the mass bound, `∫ κ(ω) dμ ≤ M(Y)`.  Hence
`∫_{B_R} |κ| dμ ≤ M(Y)`; let `R ↑ ∞`. -/
theorem Submission.imc_lintegral_coordNorm_le_mass : ∀ (N k : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ : Measure (Eucl N)) (κ : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation Y μ κ → ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ Y.mass := by
  intro N k Y μ κ hY
  -- If `M(Y) = ∞` there is nothing to prove.
  rcases eq_or_ne Y.mass ∞ with hM | hM
  · rw [hM]
    exact le_top
  -- Step 7: the integral over every ball `B_R`, `R ∈ ℕ`, is at most `M(Y)`.
  have hball : ∀ R : ℕ, ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
      (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ ≤ Y.mass := by
    intro R
    -- Step 1: the coordinates `κ^γ` are `μ`-integrable on `closedBall 0 R ⊇ B_R`.
    have hint : ∀ γ : SimonMultiIndex k N,
        IntegrableOn (fun x => euclideanNVectorCoordinate (κ x) γ) (ball (0 : Eucl N) R) μ :=
      fun γ => (Submission.cmb_rb_measureRepresentation_integrableOn_coeff N k univ univ
        isOpen_univ subset_rfl Y μ κ hY (closedBall 0 R) (isCompact_closedBall 0 R)
        (subset_univ _) γ).mono_set ball_subset_closedBall
    -- `B_R ⊂⊂ ℝ^N`, and `M_{B_R}(Y) ≤ M(Y) = ofReal (M(Y).toReal)`.
    have hW : CompactlyContainedOpen (ball (0 : Eucl N) R) univ :=
      ⟨isOpen_ball, (isCompact_closedBall 0 R).closure_of_subset ball_subset_closedBall,
        subset_univ _⟩
    have hmass : Y.massOn (ball (0 : Eucl N) R) ≤ ENNReal.ofReal Y.mass.toReal := by
      rw [ENNReal.ofReal_toReal hM]
      exact Y.massOn_mono (subset_univ _)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    -- Steps 3–6: a continuous form `ω`, `tsupport ω ⊆ B_R`, `|ω| ≤ 1`, nearly attains
    -- `∫_{B_R} |κ| dμ`.
    obtain ⟨ω, hω, hωR, hω1, -, hle⟩ := Submission.imc_mlb_exists_form_lintegral_coordNorm_le
      N k μ κ R hint ε (NNReal.coe_pos.mpr hε)
    -- Step 2: `∫ κ(ω) dμ ≤ |∫ κ(ω) dμ| ≤ M(Y).toReal`.
    have hωM : ∫ x, κ x (ω x) ∂μ ≤ Y.mass.toReal := by
      have h := (Submission.cmb_measureRepresentation_continuous_bound N k univ _ hW Y μ κ hY
        Y.mass.toReal 1 ENNReal.toReal_nonneg hmass ω hω hωR hω1).2
      rw [mul_one] at h
      exact (le_abs_self _).trans h
    calc _ ≤ ENNReal.ofReal (∫ x, κ x (ω x) ∂μ + ε) := hle
      _ ≤ ENNReal.ofReal (Y.mass.toReal + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = Y.mass + ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg, ENNReal.ofReal_toReal hM,
          ENNReal.ofReal_coe_nnreal]
  -- Monotone convergence along the directed exhaustion `⋃_R B_R = ℝ^N`; no measurability of the
  -- integrand is needed.
  calc _ = ∫⁻ x in ⋃ R : ℕ, ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
        (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ := by
        rw [iUnion_ball_nat, Measure.restrict_univ]
    _ = ⨆ R : ℕ, ∫⁻ x in ball (0 : Eucl N) R, ENNReal.ofReal (Real.sqrt
        (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (κ x) γ) ^ 2)) ∂μ :=
        setLIntegral_iUnion_of_directed _
          (Monotone.directed_le fun _ _ h => ball_subset_ball (Nat.cast_le.mpr h))
    _ ≤ Y.mass := iSup_le hball
/-- Riesz–Fischer (the `L¹`-limit step in the proof of Simon Ch. 6, Lemma 3.13): if the `fₙ` are
`μ`-a.e. strongly measurable with `∑ₙ ∫⁻ ‖fₙ₊₁ − fₙ‖ₑ dμ < ∞`, then `fₙ → g` `μ`-a.e. for a
`μ`-a.e. strongly measurable `g`, and `∫⁻ ‖fₙ − g‖ₑ dμ → 0`. -/
theorem Submission.imc_ae_tendsto_of_summable_lintegral :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → X → E), (∀ n, AEStronglyMeasurable (f n) μ) → (∑' n, ∫⁻ x, ‖f (n + 1) x - f n x‖ₑ ∂μ) ≠ ∞ → ∃ g : X → E, AEStronglyMeasurable g μ ∧ (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) ∧ Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ∂μ) atTop (𝓝 0) := by
  intro X _ μ E _ _ f hf hsum
  -- Step 1: the increments `dₙ = ‖fₙ₊₁ − fₙ‖ₑ` have a.e. finite sum (`lintegral_tsum`).
  set d : ℕ → X → ℝ≥0∞ := fun n x => ‖f (n + 1) x - f n x‖ₑ
  have hd : ∀ n, AEMeasurable (d n) μ := fun n => ((hf (n + 1)).sub (hf n)).enorm
  have hS : ∫⁻ x, ∑' n, d n x ∂μ = ∑' n, ∫⁻ x, d n x ∂μ := lintegral_tsum hd
  have hfin : ∀ᵐ x ∂μ, ∑' n, d n x < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hd) (by rw [hS]; exact hsum)
  -- Step 2: where the sum is finite, `(fₙ x)` is Cauchy.
  have hedist : ∀ x n, edist (f n x) (f (n + 1) x) ≤ d n x := fun x n => by
    rw [edist_comm, edist_eq_enorm_sub]
  have hcauchy : ∀ᵐ x ∂μ, CauchySeq (fun n => f n x) := by
    filter_upwards [hfin] with x hx
    exact cauchySeq_of_edist_le_of_tsum_ne_top (fun n => d n x) (hedist x) hx.ne
  -- Step 3: the limit `g`, a.e. strongly measurable as an a.e. limit.
  set g : X → E := fun x => limUnder atTop (fun n => f n x)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    filter_upwards [hcauchy] with x hx
    exact hx.tendsto_limUnder
  refine ⟨g, aestronglyMeasurable_of_tendsto_ae atTop hf hlim, hlim, ?_⟩
  -- Step 4: `‖fₙ − g‖ₑ ≤ ∑_{m ≥ n} dₘ` a.e.
  have htail : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ₑ ≤ ∑' m, d (n + m) x := by
    intro n
    filter_upwards [hfin, hlim] with x hx hxl
    rw [← edist_eq_enorm_sub]
    exact edist_le_tsum_of_edist_le_of_tendsto (fun m => d m x) (hedist x) hxl n
  -- Step 5: integrate; the tails of a finite series tend to `0`.
  have hbound : ∀ n, ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤ ∑' m, ∫⁻ x, d (n + m) x ∂μ := by
    intro n
    calc ∫⁻ x, ‖f n x - g x‖ₑ ∂μ ≤ ∫⁻ x, ∑' m, d (n + m) x ∂μ := lintegral_mono_ae (htail n)
      _ = ∑' m, ∫⁻ x, d (n + m) x ∂μ := lintegral_tsum fun m => hd (n + m)
  have htend : Tendsto (fun n => ∑' m, ∫⁻ x, d (n + m) x ∂μ) atTop (𝓝 0) := by
    have := ENNReal.tendsto_sum_nat_add (fun m => ∫⁻ x, d m x ∂μ) hsum
    simpa [add_comm] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend (fun n => bot_le) hbound
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
/-- Density bound at a weighted tangent point (Simon Ch. 3, Remark 1.8(1)): if `T` is the
approximate tangent space of `M` at `y` with respect to `θ` (Definition 1.7), `θ ≥ 0` on `M`,
`θ(y) > 0`, `C ⊆ M` is null-measurable with `θ|C` continuous at `y`, `Hⁿ(C ∩ B̄_r(y)) < ∞` and `θ`
is `Hⁿ`-integrable on `M ∩ B̄_r(y)` for some `r > 0`, then `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all
sufficiently small `ρ > 0`. -/
theorem Submission.imc_wte_density_bound_of_weightedTangent : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∀ x ∈ M, 0 ≤ θ x) → 0 < θ y → HasWeightedApproximateTangentSpaceAt n M θ y T → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ContinuousWithinAt θ C y → ∃ K : ℝ≥0, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≤ K * ENNReal.ofReal (ρ ^ n) := by
  intro Q n M C θ y T hM hC hCM hθ hθy hT ⟨r, hr, hfin, hint⟩ hθC
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
  -- Step 2: `θ > θ(y)/2` on `C` near `y`, since `θ|C` is continuous at `y` and `θ(y) > 0`.
  obtain ⟨δ, hδ, hδθ⟩ := Metric.continuousWithinAt_iff.1 hθC (θ y / 2) (half_pos hθy)
  refine ⟨((θ y * L₀ + 1) / (θ y / 2)).toNNReal, ?_⟩
  -- Step 3: the weighted blow-up integrals of `φ₀` tend to `θ(y) L₀`, so they are eventually
  -- `≤ θ(y) L₀ + 1`; also eventually `0 < ρ < min(r/2, δ)`.
  filter_upwards [(hT.2 φ₀).eventually (eventually_le_nhds (lt_add_one (θ y * L₀))),
    Ioo_mem_nhdsGT (lt_min (half_pos hr) hδ)] with ρ hρ ⟨hρ0, hρrδ⟩
  have hρr : ρ < r / 2 := hρrδ.trans_le (min_le_left _ _)
  have hρδ : ρ < δ := hρrδ.trans_le (min_le_right _ _)
  have hρn : 0 < ρ ^ n := pow_pos hρ0 n
  have hnorm : ∀ x, ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ = ρ⁻¹ * dist x y := by
    intro x
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hρ0), dist_eq_norm]
  have hcont : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y ρ) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  -- Step 4: `ψ = (φ₀ ∘ η_{y,ρ}) θ` is integrable on `M ∩ B̄_r(y)` (`|φ₀| ≤ 1`) and vanishes off
  -- `B̄_r(y)` (as `2ρ < r`), so it is integrable on `M`; it is nonnegative on `M`.
  have hψM : IntegrableOn (fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x) M
      (μHE[n] : Measure (Eucl Q)) := by
    have hψr : IntegrableOn (fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x)
        (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q)) :=
      Integrable.bdd_mul (c := 1) hint (φ₀.continuous.comp hcont).aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_of_nonneg (hφ₀01 _).1]
          exact (hφ₀01 _).2)
    refine hψr.of_ae_sdiff_eq_zero hM (ae_of_all _ fun x hx => ?_)
    have hxr : r < dist x y := not_le.1 fun h => hx.2 ⟨hx.1, h⟩
    have h2 : 2 ≤ ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ := by
      rw [hnorm, le_inv_mul_iff₀ hρ0]
      linarith
    rw [hφ₀, hzero _ h2, zero_mul]
  have hψ0 : 0 ≤ᵐ[(μHE[n] : Measure (Eucl Q)).restrict M]
      fun x => φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x := by
    filter_upwards [ae_restrict_mem₀ hM] with x hx
    exact mul_nonneg (hφ₀01 _).1 (hθ x hx)
  -- Step 5: `ψ ≥ θ(y)/2` on `C ∩ B̄_ρ(y) ⊆ M`, so `(θ(y)/2) Hⁿ(C ∩ B̄_ρ(y)) ≤ ∫_M ψ`.
  have hA : NullMeasurableSet (C ∩ closedBall y ρ) (μHE[n] : Measure (Eucl Q)) :=
    hC.inter measurableSet_closedBall.nullMeasurableSet
  have hAM : C ∩ closedBall y ρ ⊆ M := inter_subset_left.trans hCM
  have hfinρ : (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (measure_mono (inter_subset_inter_right _
      (closedBall_subset_closedBall (by linarith))))
  have hle : θ y / 2 * (μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ) ≤
      ∫ x in M, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
        ∂(μHE[n] : Measure (Eucl Q)) := by
    calc θ y / 2 * (μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ)
        = ∫ _ in C ∩ closedBall y ρ, θ y / 2 ∂(μHE[n] : Measure (Eucl Q)) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in C ∩ closedBall y ρ, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
            ∂(μHE[n] : Measure (Eucl Q)) := by
          refine setIntegral_mono_ae_restrict (integrableOn_const hfinρ) (hψM.mono_set hAM) ?_
          filter_upwards [ae_restrict_mem₀ hA] with x hx
          have h1 : ‖Poincare.SimonGMT.Chapter03.blowUpMap y ρ x‖ ≤ 1 := by
            rw [hnorm, inv_mul_le_iff₀ hρ0, mul_one]
            exact hx.2
          have hθx := hδθ hx.1 ((mem_closedBall.1 hx.2).trans_lt hρδ)
          rw [Real.dist_eq, abs_lt] at hθx
          rw [hφ₀one _ h1, one_mul]
          linarith [hθx.1]
      _ ≤ ∫ x in M, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
            ∂(μHE[n] : Measure (Eucl Q)) :=
          setIntegral_mono_set hψM hψ0 hAM.eventuallySubset
  -- Step 6: by the blow-up identity (`y + ρ η_{y,ρ}(x) = x`), `∫_M ψ = ρⁿ W(ρ)`, where `W(ρ)` is
  -- the weighted blow-up integral of `φ₀`.
  have hη : ∀ x, y + ρ • Poincare.SimonGMT.Chapter03.blowUpMap y ρ x = x := fun x => by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ0.ne', add_sub_cancel]
  have hW : ∫ x in M, φ₀ (Poincare.SimonGMT.Chapter03.blowUpMap y ρ x) * θ x
        ∂(μHE[n] : Measure (Eucl Q)) =
      ρ ^ n * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y ρ '' M, φ₀ z * θ (y + ρ • z)
        ∂(μHE[n] : Measure (Eucl Q)) := by
    rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y ρ M _ hρ0, mul_inv_cancel_left₀ hρn.ne']
    simp_rw [hη]
  -- Step 7: `(θ(y)/2) Hⁿ(C ∩ B̄_ρ(y)) ≤ (θ(y) L₀ + 1) ρⁿ`; divide by `θ(y)/2 > 0`.
  have hkey : (μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ) ≤
      (θ y * L₀ + 1) / (θ y / 2) * ρ ^ n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (half_pos hθy)]
    have hup := mul_le_mul_of_nonneg_left hρ hρn.le
    rw [← hW] at hup
    linarith
  calc (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y ρ)
      = ENNReal.ofReal ((μHE[n] : Measure (Eucl Q)).real (C ∩ closedBall y ρ)) :=
        (ofReal_measureReal hfinρ).symm
    _ ≤ ENNReal.ofReal ((θ y * L₀ + 1) / (θ y / 2) * ρ ^ n) := ENNReal.ofReal_le_ofReal hkey
    _ = ((θ y * L₀ + 1) / (θ y / 2)).toNNReal * ENNReal.ofReal (ρ ^ n) :=
        ENNReal.ofReal_mul' hρn.le
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
/-- Converse weighted transfer (Simon Ch. 3, Remark 1.8(1)): if `T` is the approximate tangent
space of `M` at `y` with respect to `θ` (Def. 1.7), `C ⊆ M`, `θ|C` is continuous at `y` and
`θ Hⁿ⌞(M ∖ C)` has `n`-density `0` at `y`, then `T` is the approximate tangent space of `C` at `y`
(Def. 1.4).  For `φ ∈ C_c(ℝ^Q)` and small `t > 0`,
`θ(y) t⁻ⁿ ∫_C φ(η_t) = t⁻ⁿ ∫_M φ(η_t) θ - t⁻ⁿ ∫_C φ(η_t) (θ - θ(y)) - t⁻ⁿ ∫_{M∖C} φ(η_t) θ`,
where the first term tends to `θ(y) ∫_T φ` and the other two tend to `0`. -/
theorem Submission.imc_wte_approxTangent_of_weightedTangent : ∀ (Q n : ℕ) (M C : Set (Eucl Q)) (θ : Eucl Q → ℝ) (y : Eucl Q) (T : Submodule ℝ (Eucl Q)), NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → NullMeasurableSet C (μHE[n] : Measure (Eucl Q)) → C ⊆ M → (∀ x ∈ M, 0 ≤ θ x) → 0 < θ y → HasWeightedApproximateTangentSpaceAt n M θ y T → (∃ r : ℝ, 0 < r ∧ (μHE[n] : Measure (Eucl Q)) (C ∩ closedBall y r) < ∞ ∧ IntegrableOn θ (M ∩ closedBall y r) (μHE[n] : Measure (Eucl Q))) → ContinuousWithinAt θ C y → Tendsto (fun ρ : ℝ => (∫⁻ x in (M \ C) ∩ closedBall y ρ, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n C y T := by
  intro Q n M C θ y T hM hC hCM hθ hθy hW hr hθC hdens
  -- Step 2: `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all small `ρ > 0`.
  have hK := Submission.imc_wte_density_bound_of_weightedTangent Q n M C θ y T hM hC hCM hθ hθy
    hW hr hθC
  -- Step 1: `dim T = n`; fix `φ ∈ C_c(ℝ^Q)`.
  refine ⟨hW.1, fun φ => ?_⟩
  -- Step 3: `a(t) = t⁻ⁿ ∫_M φ(η_t) θ → θ(y) ∫_T φ`, since `y + t η_t(x) = x`.
  have ha : Tendsto (fun t : ℝ => (t ^ n)⁻¹ * ∫ x in M,
      φ (Poincare.SimonGMT.Chapter03.blowUpMap y t x) * θ x ∂(μHE[n] : Measure (Eucl Q)))
      (𝓝[>] 0) (𝓝 (θ y * ∫ z in (T : Set (Eucl Q)), φ z ∂(μHE[n] : Measure (Eucl Q)))) := by
    refine (hW.2 φ).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hη : ∀ x, y + t • Poincare.SimonGMT.Chapter03.blowUpMap y t x = x := fun x => by
      rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ (ne_of_gt ht), add_sub_cancel]
    have h := Submission.lpf_wtc_blowup_setIntegral_image Q n y t M
      (fun z => φ z * θ (y + t • z)) ht
    simp only [hη] at h
    exact h
  -- Steps 4–5: the continuity error on `C` and the remainder on `M ∖ C` vanish.
  have hb := Submission.lpf_wtc_wtt_continuity_error_vanishes Q n C θ y φ hC hθC hK
  have hc := Submission.lpf_wtc_wtt_remainder_vanishes Q n (M \ C) θ y φ (hM.diff hC)
    (fun x hx => hθ x hx.1) hdens
  -- Steps 6–7: `t⁻ⁿ ∫_C φ(η_t) = θ(y)⁻¹ (a(t) - b(t) - c(t)) → ∫_T φ`.
  have hm := ((ha.sub hb).sub hc).const_mul (θ y)⁻¹
  rw [sub_zero, sub_zero, ← mul_assoc, inv_mul_cancel₀ hθy.ne', one_mul] at hm
  -- Step 8: back to the blow-ups `η_t(C)`.
  refine hm.congr' ?_
  filter_upwards [Submission.lpf_wtc_wtt_blowup_integral_split Q n M C θ y φ hM hC hCM hr,
    self_mem_nhdsWithin] with t hsplit ht
  rw [Submission.lpf_wtc_blowup_setIntegral_image Q n y t C φ ht, hsplit]
  field_simp
  ring
/-- Upper Density Theorem on `ℝ^Q` (Simon Ch. 1, 3.6, localized as in Remark 3.7(2)) for
`ν = (Hⁿ ⌞ S).withDensity g`: if `∫⁻_{S ∩ K} g dHⁿ < ∞` for every compact `K`, then
`ν(B̄_ρ(y)) / ρⁿ → 0` as `ρ → 0+` for `Hⁿ`-a.e. `y ∉ S`. -/
theorem Submission.imc_ae_zero_density_off_set :
    ∀ (Q n : ℕ) (S : Set (Eucl Q)) (g : Eucl Q → ℝ≥0∞), NullMeasurableSet S (μHE[n] : Measure (Eucl Q)) → (∀ K : Set (Eucl Q), IsCompact K → ∫⁻ x in S ∩ K, g x ∂(μHE[n] : Measure (Eucl Q)) < ∞) → ∀ᵐ y ∂(μHE[n] : Measure (Eucl Q)), y ∉ S → Tendsto (fun ρ : ℝ => (∫⁻ x in S ∩ closedBall y ρ, g x ∂(μHE[n] : Measure (Eucl Q))) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
  intro Q n S g hS hfin
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
  -- Step 3 (Upper Density Theorem, Simon Ch. 1, 3.6): for a finite `m` with `m Aᶜ = 0`, the
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
  -- Step 4 (Simon Ch. 1, Remark 3.7(2)): localize to the compact balls `B̄_{2/3}(x)` (finite
  -- `ν`-mass) around each point `x` of the exceptional set, and use `μHE[n] = c • μH[n]`.
  have hmain : ∀ᵐ y ∂μ, y ∉ A →
      Tendsto (fun ρ : ℝ => ν (closedBall y ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    rw [ae_iff]
    apply measure_null_of_locally_null
    intro x _
    set m := ν.restrict (closedBall x (2 / 3)) with hm_def
    have hm : m univ ≠ ∞ := by
      rw [hm_def, Measure.restrict_apply_univ, hνB _ measurableSet_closedBall]
      exact (hfin _ (isCompact_closedBall x _)).ne
    have hmA : m Aᶜ = 0 := by
      rw [hm_def, Measure.restrict_apply hAm.compl]
      exact measure_mono_null inter_subset_left hνA
    have hr : (0 : ℝ) < 1 / 3 := by norm_num
    refine ⟨_ ∩ ball x (1 / 3), inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
    rw [hμ, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
    refine (congrArg _ (measure_mono_null ?_ (measure_iUnion_null fun k : ℕ =>
      hcore m hm hmA ((k : ℝ≥0∞) + 1)⁻¹ (by simp) (by simp)))).trans (smul_zero _)
    -- a non-tending quotient exceeds some `(k + 1)⁻¹` at arbitrarily small radii
    rintro y ⟨hy, hyx⟩
    simp only [mem_ofPred_eq, not_imp] at hy
    obtain ⟨hyA, hyT⟩ := hy
    rw [ENNReal.tendsto_nhds_zero] at hyT
    push Not at hyT
    obtain ⟨ε, hε, hfreq⟩ := hyT
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.mpr ⟨k, hyA, fun δ hδ => ?_⟩
    obtain ⟨ρ, hρf, hρ⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hδ hr))).exists
    refine ⟨ρ, ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩, ?_⟩
    have hsub : closedBall y ρ ⊆ closedBall x (2 / 3) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      rw [mem_ball] at hyx
      linarith [dist_triangle z y x, hρ.2.trans_le (min_le_right δ (1 / 3))]
    rw [hm_def, Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hsub,
      ← ENNReal.ofReal_pow hρ.1.le]
    refine ENNReal.mul_lt_of_lt_div (lt_of_le_of_lt ?_ hρf)
    exact (ENNReal.inv_le_inv.mpr (by simp)).trans hk.le
  -- Step 5: transfer from the hull `A` back to `S` (they agree `μ`-a.e.).
  filter_upwards [hmain, hS.toMeasurable_ae_eq] with y hy hyA hyS
  refine (hy fun h => hyS (hyA ▸ h)).congr fun ρ => ?_
  rw [hνB _ measurableSet_closedBall]
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), in the quantitative form
used in the proof of Ch. 6, 8.2.  For `r > 0`, the blow-up `η_{x,r}(z) = r⁻¹(z - x)` pushes
`(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so the blow-up integral of `(M, θ)` against `f` is
`(rⁿ)⁻¹ ∫ f(η_{x,r} z) 1_M θ(z) dHⁿ(z)` (`M` is `Hⁿ`-null-measurable).  If `f = 0` off
`B_R(0)` and `|f| ≤ C`, then for `R r ≤ ρ` these integrals exist and those of `(M, θ)` and
`(M', θ')` differ by at most `C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'| dHⁿ → 0`; as
`θ x = θ' x`, the two tangent-space conditions are equivalent. -/
theorem Submission.iwl_weighted_tangent_locality :
    ∀ (P n : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P),
      NullMeasurableSet M (μHE[n] : Measure (Eucl P)) →
      NullMeasurableSet M' (μHE[n] : Measure (Eucl P)) → θ x = θ' x →
      (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) ∧
        IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P))) →
      (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
          ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) →
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q ↔
        HasWeightedApproximateTangentSpaceAt n M' θ' x Q := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P n M M' θ θ' x hM hM' hθx ⟨ρ, hρ, hθρ, hθ'ρ⟩ hlim Q
  -- Change of variables under `η_r = blowUpMap x r`: `∫_{η_r(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η_r dHⁿ`.
  have hcov : ∀ r : ℝ, 0 < r → ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, g y ∂(μHE[n] : Measure (Eucl P)) =
        (r ^ n)⁻¹ * ∫ z in S, g (blowUpMap x r z) ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr S g
    let e : Eucl P ≃ₜ Eucl P :=
      (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
    have he : (e : Eucl P → Eucl P) = blowUpMap x r := by
      funext z
      simp [e, blowUpMap, sub_eq_add_neg]
    have hemb : MeasurableEmbedding (blowUpMap x r) := he ▸ e.measurableEmbedding
    -- `η_r` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η_r⁻¹(B) = x + r • B`.
    have hmp : MeasurePreserving (blowUpMap x r)
        (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) μHE[n] := by
      refine ⟨hemb.measurable, ?_⟩
      ext B hB
      rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
      have hpre : blowUpMap x r ⁻¹' B = (fun z => x + z) '' ((fun z => r • z) '' B) := by
        ext z
        simp only [mem_preimage, mem_image, blowUpMap]
        constructor
        · intro hz
          exact ⟨r • r⁻¹ • (z - x), ⟨r⁻¹ • (z - x), hz, rfl⟩, by
            rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
        · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
          rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
      rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
        Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
        smul_eq_mul, ← mul_assoc]
      have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
          coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
          ENNReal.ofReal_one]
      rw [hc, one_mul]
    rw [hmp.setIntegral_image_emb hemb g S, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- The blow-up integrals of `(M, θ)` and `(M', θ')` against `f` differ by `o(1)` as `r ↓ 0`.
  have hkey : ∀ f : CompactlySupportedContinuousMap (Eucl P) ℝ, Tendsto (fun r : ℝ =>
      (∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P))) -
        ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[n] : Measure (Eucl P)))
      (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- `f = 0` off `B_R(0)` and `|f| ≤ C`.
    obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- `f ∘ η_r` vanishes off `B̄_{R r}(x)`.
    have hvan : ∀ r : ℝ, 0 < r → ∀ z : Eucl P, z ∉ closedBall x (R * r) →
        f (blowUpMap x r z) = 0 := by
      intro r hr z hz
      apply hfR
      rw [mem_closedBall, not_le, dist_eq_norm] at hz
      rw [blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div,
        le_div_iff₀ hr]
      exact hz.le
    -- For `R r ≤ ρ`, `(f ∘ η_r) · 1_S ϑ` is integrable when `ϑ` is integrable on `S ∩ B̄_ρ(x)`.
    have hint : ∀ r : ℝ, 0 < r → R * r ≤ ρ → ∀ (S : Set (Eucl P)) (ϑ : Eucl P → ℝ),
        NullMeasurableSet S (μHE[n] : Measure (Eucl P)) →
        IntegrableOn ϑ (S ∩ closedBall x ρ) (μHE[n] : Measure (Eucl P)) →
        Integrable (fun z => f (blowUpMap x r z) * S.indicator ϑ z)
          (μHE[n] : Measure (Eucl P)) := by
      intro r hr hRr S ϑ hS hϑ
      have hcont : Continuous fun z => f (blowUpMap x r z) :=
        f.continuous.comp ((continuous_const_smul _).comp (continuous_id.sub continuous_const))
      have h1 : IntegrableOn (fun z => f (blowUpMap x r z) * ϑ z) (S ∩ closedBall x ρ)
          (μHE[n] : Measure (Eucl P)) :=
        Integrable.bdd_mul hϑ hcont.aestronglyMeasurable (ae_of_all _ fun z => hC _)
      have h2 : IntegrableOn (fun z => f (blowUpMap x r z) * ϑ z) S
          (μHE[n] : Measure (Eucl P)) := by
        refine h1.of_ae_sdiff_eq_zero hS (ae_of_all _ fun z hz => ?_)
        have hz' : z ∉ closedBall x (R * r) := fun h =>
          hz.2 ⟨hz.1, closedBall_subset_closedBall hRr h⟩
        rw [hvan r hr z hz', zero_mul]
      refine (h2.integrable_indicator₀ hS).congr (ae_of_all _ fun z => ?_)
      exact Set.indicator_mul_right S (fun z => f (blowUpMap x r z)) ϑ
    -- `∫_{η_r(S)} f(y) ϑ(x + r y) dHⁿ(y) = (rⁿ)⁻¹ ∫ f(η_r z) 1_S ϑ(z) dHⁿ(z)`.
    have hI : ∀ r : ℝ, 0 < r → ∀ (S : Set (Eucl P)) (ϑ : Eucl P → ℝ),
        NullMeasurableSet S (μHE[n] : Measure (Eucl P)) →
        ∫ y in blowUpMap x r '' S, f y * ϑ (x + r • y) ∂(μHE[n] : Measure (Eucl P)) =
          (r ^ n)⁻¹ * ∫ z, f (blowUpMap x r z) * S.indicator ϑ z
            ∂(μHE[n] : Measure (Eucl P)) := by
      intro r hr S ϑ hS
      rw [hcov r hr S]
      simp only [hinv r hr.ne']
      rw [← integral_indicator₀ hS]
      congr 2
      funext z
      exact Set.indicator_mul_right S (fun z => f (blowUpMap x r z)) ϑ
    -- The estimate `|I_{M,θ}(r) - I_{M',θ'}(r)| ≤ C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'|`.
    have hbound : ∀ r : ℝ, 0 < r → R * r ≤ ρ →
        ‖(∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P))) -
          ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ n)⁻¹) *
          ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
            ∂(μHE[n] : Measure (Eucl P))) := by
      intro r hr hRr
      rw [hI r hr M θ hM, hI r hr M' θ' hM', ← mul_sub,
        ← integral_sub (hint r hr hRr M θ hM hθρ) (hint r hr hRr M' θ' hM' hθ'ρ), enorm_mul,
        Real.enorm_of_nonneg (by positivity), mul_left_comm]
      gcongr
      calc ‖∫ z, f (blowUpMap x r z) * M.indicator θ z - f (blowUpMap x r z) * M'.indicator θ' z
              ∂(μHE[n] : Measure (Eucl P))‖ₑ
          ≤ ∫⁻ z, ‖f (blowUpMap x r z) * M.indicator θ z -
              f (blowUpMap x r z) * M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ z, (closedBall x (R * r)).indicator
              (fun z => ENNReal.ofReal C * ‖M.indicator θ z - M'.indicator θ' z‖ₑ) z
              ∂(μHE[n] : Measure (Eucl P)) := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ closedBall x (R * r)
            · rw [Set.indicator_of_mem hz, ← mul_sub, enorm_mul, ← ofReal_norm]
              gcongr
              exact hC _
            · rw [hvan r hr z hz, zero_mul, zero_mul, sub_zero, enorm_zero]
              exact zero_le
        _ = ENNReal.ofReal C * ∫⁻ z in closedBall x (R * r),
              ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[n] : Measure (Eucl P)) := by
            rw [lintegral_indicator measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [tendsto_zero_iff_enorm_tendsto_zero]
    have hupper : Tendsto (fun r : ℝ => ENNReal.ofReal C * (ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ
          ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hlim R hR) (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
    refine hbound r hr.1 ?_
    have := hr.2
    rw [lt_div_iff₀ hR] at this
    linarith
  constructor
  · rintro ⟨hQ, hf⟩
    refine ⟨hQ, fun f => ?_⟩
    rw [← hθx]
    simpa using (hf f).sub (hkey f)
  · rintro ⟨hQ, hf⟩
    refine ⟨hQ, fun f => ?_⟩
    rw [hθx]
    simpa using (hf f).add (hkey f)
/-- Simon Ch. 6, 2.8 and 2.12: a mass measure `μ` of `X ∈ 𝒟ₖ(ℝ^N)` vanishes off `spt X`, and
`μ(ℝ^N) ≤ M(X)`, so `μ` is finite when `M(X) < ∞`. -/
theorem Submission.dmr_massMeasure_support_finite :
    ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ : Measure (Eucl N)),
      IsMassMeasure X μ → μ X.supportᶜ = 0 ∧ (X.mass < ∞ → IsFiniteMeasure μ) := by
  intro N k X μ hμ
  constructor
  · -- `(spt X)ᶜ = Z(X)` is a countable union (Lindelöf) of open `W ⊂⊂ ℝ^N` on which `X`
    -- vanishes, and each such `W` has `μ W = M_W(X) = 0`.
    obtain ⟨T, hTc, hTS, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable
      {W : Set (Eucl N) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ univ ∧ X.VanishesOn W}
      fun W hW => hW.1
    have hZ : X.supportᶜ = ⋃₀ T := by
      rw [hTeq, GeometricCurrentOn.support, ← compl_eq_univ_sdiff, compl_compl]
      rfl
    rw [hZ, measure_sUnion_null_iff hTc]
    intro W hWT
    obtain ⟨hWo, hWc, hWU, hWv⟩ := hTS hWT
    rw [hμ.2 W ⟨hWo, hWc, hWU⟩]
    refine nonpos_iff_eq_zero.1 (sSup_le ?_)
    rintro r ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (X ω) ≤ 0
    rw [hWv ω hω.1, ENNReal.ofReal_zero]
  · -- `μ(B_n) = M_{B_n}(X) ≤ M(X)` for the balls `B_n ⊂⊂ ℝ^N`, and `B_n ↑ ℝ^N`.
    intro hfin
    have hball : ∀ n : ℕ, μ (ball (0 : Eucl N) n) ≤ X.mass := fun n => by
      rw [hμ.2 _ ⟨isOpen_ball, (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall, subset_univ _⟩]
      exact X.massOn_mono (subset_univ _)
    have hmono : Monotone fun n : ℕ => ball (0 : Eucl N) n :=
      fun m n hmn => ball_subset_ball (Nat.cast_le.2 hmn)
    have huniv : μ univ ≤ X.mass :=
      calc μ univ = μ (⋃ n : ℕ, ball (0 : Eucl N) n) := by rw [iUnion_ball_nat]
        _ = ⨆ n : ℕ, μ (ball (0 : Eucl N) n) := hmono.measure_iUnion
        _ ≤ X.mass := iSup_le hball
    exact ⟨huniv.trans_lt hfin⟩
/-- **Uniqueness of the vector measure `v μ` of a representation (2.7), Simon Ch. 6, 2.7–2.9
(p. 136).**  Two representations `(μ₁, v₁)`, `(μ₂, v₂)` of `X ∈ 𝒟ₖ(ℝ^N)` have (a) the same set
integrals `∫_A ⟨ω, vᵢ⟩ dμᵢ` over every Borel `A`, for every test form `ω`
(`slicing_representation_unique` with `U = W = ℝ^N`), and (b) the same `∫_A ⟨α, vᵢ⟩ dμᵢ` over
every bounded Borel `A`, for every constant covector `α`: if `A ⊆ closedBall 0 R`, a smooth
cutoff `φ` with `support φ = ball 0 (R + 1)` and `φ = 1` on `closedBall 0 R` makes `φ α` a test
form equal to `α` on `A`, and (a) applies to it. -/
theorem Submission.dmr_measureRepresentation_unique : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ₁ μ₂ : Measure (Eucl N)) (v₁ v₂ : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation X μ₁ v₁ → IsMeasureRepresentation X μ₂ v₂ → (∀ A : Set (Eucl N), MeasurableSet A → ∀ ω : TestFormOn (univ : Set (Eucl N)) k, ∫ x in A, v₁ x ((ω : DifferentialForm (Eucl N) k) x) ∂μ₁ = ∫ x in A, v₂ x ((ω : DifferentialForm (Eucl N) k) x) ∂μ₂) ∧ (∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A → ∀ α : Covector (Eucl N) k, ∫ x in A, v₁ x α ∂μ₁ = ∫ x in A, v₂ x α ∂μ₂) := by
  intro N k X μ₁ μ₂ v₁ v₂ h₁ h₂
  -- Step 1 (part (a)): `slicing_representation_unique` with `U = W = ℝ^N`; both representations
  -- give `∫ ⟨ω, v₁⟩ dμ₁ = X ω = ∫ ⟨ω, v₂⟩ dμ₂`.
  have ha : ∀ A : Set (Eucl N), MeasurableSet A → ∀ ω : TestFormOn (univ : Set (Eucl N)) k,
      ∫ x in A, v₁ x ((ω : DifferentialForm (Eucl N) k) x) ∂μ₁ =
        ∫ x in A, v₂ x ((ω : DifferentialForm (Eucl N) k) x) ∂μ₂ := fun A hA ω =>
    Submission.slicing_representation_unique N k univ isOpen_univ μ₁ μ₂ v₁ v₂
      (fun ω => (h₁ ω).1) (fun ω => (h₂ ω).1) univ isOpen_univ
      (fun ω _ => (h₁ ω).2.symm.trans (h₂ ω).2) A hA ω (subset_univ _)
  refine ⟨ha, fun A hA hAb α => ?_⟩
  -- Step 2: `A ⊆ closedBall 0 R`.
  obtain ⟨R, hR⟩ := hAb.subset_closedBall (0 : Eucl N)
  -- Step 3: a smooth cutoff `φ` with `support φ = ball 0 (R + 1)` and `φ = 1` on
  -- `closedBall 0 R`; it has compact support.
  obtain ⟨φ, hφ, -, hφs, hφ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_ball (x := (0 : Eucl N)) (ε := R + 1)) isClosed_closedBall
    (closedBall_subset_ball (lt_add_one R))
  have hφc : HasCompactSupport φ := by
    refine (isCompact_closedBall (0 : Eucl N) (R + 1)).of_isClosed_subset (isClosed_tsupport φ) ?_
    rw [tsupport, hφs]
    exact closure_ball_subset_closedBall
  -- Step 4: `ω = φ α` is a test form on `ℝ^N`.
  let ω : TestFormOn (univ : Set (Eucl N)) k :=
    ⟨fun x => φ x • α, ⟨⟨hφ.smul contDiff_const, hφc.smul_right⟩, subset_univ _⟩⟩
  -- Step 5: `ω = α` on `A`, so the set integrals over `A` agree.
  have hω : ∀ v : Eucl N → NVector (Eucl N) k,
      EqOn (fun x => v x ((ω : DifferentialForm (Eucl N) k) x)) (fun x => v x α) A := by
    intro v x hx
    change v x (φ x • α) = v x α
    rw [(hφ1 x).1 (hR hx), one_smul]
  -- Step 6: conclude with part (a) for `A` and `ω`.
  rw [← setIntegral_congr_fun hA (hω v₁), ← setIntegral_congr_fun hA (hω v₂)]
  exact ha A hA ω

/-- Restriction of weighted approximate tangent spaces to a Borel set (orientation step of the
proof of Simon Ch. 6, 8.2).  At `Hᵏ`-a.e. `x ∈ M ∩ A` the measure `θ Hᵏ ⌞ (M \ A)` has zero
`k`-density (Upper Density Theorem, Simon Ch. 1, 3.6).  As `|1_M θ - 1_{M ∩ A} θ| = 1_{M \ A} θ`,
the blow-up defect `(rᵏ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M ∩ A} θ| dHᵏ` then tends to `0`, so by
locality (Simon Ch. 3, 1.7) every weighted tangent space of `(M, θ)` at `x` is one of
`(M ∩ A, θ)`. -/
theorem Submission.dmr_weightedTangent_inter :
    ∀ (N k : ℕ) (M : Set (Eucl N)) (θ : Eucl N → ℝ),
      NullMeasurableSet M (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M, 0 < θ x) →
      (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[k] : Measure (Eucl N))) →
      ∀ A : Set (Eucl N), MeasurableSet A →
      ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict (M ∩ A)), ∀ L : Submodule ℝ (Eucl N),
        HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x L := by
  intro N k M θ hM hθ hint A hA
  set μ : Measure (Eucl N) := μHE[k]
  have hMA : NullMeasurableSet (M ∩ A) μ := hM.inter hA.nullMeasurableSet
  have hS : NullMeasurableSet (M \ A) μ := hM.diff hA.nullMeasurableSet
  -- `∫⁻_{(M \ A) ∩ K} θ dHᵏ < ∞` for compact `K`.
  have hfin : ∀ K : Set (Eucl N), IsCompact K → K ⊆ univ →
      ∫⁻ z in (M \ A) ∩ K, ENNReal.ofReal (θ z) ∂μ < ∞ := fun K hK _ =>
    ((hint K hK).mono_set (inter_subset_inter_left _ sdiff_subset)).setLIntegral_lt_top
  -- Zero density of `θ Hᵏ ⌞ (M \ A)` at `Hᵏ ⌞ (M ∩ A)`-a.e. `x`, which lies in `M ∩ A`.
  filter_upwards [ae_restrict_of_ae (Submission.lpf_wtc_ae_zero_density_off_set N k univ (M \ A)
    (fun z => ENNReal.ofReal (θ z)) isOpen_univ hS hfin), ae_restrict_mem₀ hMA] with x hx hxMA
  have hZ := hx (mem_univ x) fun h => h.2 hxMA.2
  -- `‖1_M θ - 1_{M ∩ A} θ‖ₑ = 1_{M \ A} ofReal θ`, as `θ > 0` on `M`.
  have hpt : ∀ z, ‖M.indicator θ z - (M ∩ A).indicator θ z‖ₑ =
      (M \ A).indicator (fun z => ENNReal.ofReal (θ z)) z := by
    intro z
    by_cases hzM : z ∈ M
    · by_cases hzA : z ∈ A
      · rw [indicator_of_mem hzM, indicator_of_mem (mem_inter hzM hzA),
          indicator_of_notMem fun h => h.2 hzA, sub_self, enorm_zero]
      · rw [indicator_of_mem hzM, indicator_of_notMem fun h => hzA h.2,
          indicator_of_mem (mem_sdiff_of_mem hzM hzA), sub_zero,
          Real.enorm_of_nonneg (hθ z hzM).le]
    · rw [indicator_of_notMem hzM, indicator_of_notMem fun h => hzM h.1,
        indicator_of_notMem fun h => hzM h.1, sub_zero, enorm_zero]
  have hF : ∀ s : ℝ, ∫⁻ z in closedBall x s, ‖M.indicator θ z - (M ∩ A).indicator θ z‖ₑ ∂μ =
      ∫⁻ z in (M \ A) ∩ closedBall x s, ENNReal.ofReal (θ z) ∂μ := by
    intro s
    simp_rw [hpt]
    rw [lintegral_indicator₀ (hS.mono Measure.restrict_le_self),
      Measure.restrict_restrict' measurableSet_closedBall]
  -- Tangent locality with `M' = M ∩ A`, `θ' = θ` and `ρ = 1`.
  intro L hL
  refine (Submission.iwl_weighted_tangent_locality N k M (M ∩ A) θ θ x hM hMA rfl
    ⟨1, one_pos, hint _ (isCompact_closedBall x 1),
      (hint _ (isCompact_closedBall x 1)).mono_set (inter_subset_inter_left _ inter_subset_left)⟩
    (fun R hR => ?_) L).mp hL
  -- `ofReal((rᵏ)⁻¹) F(R r) = ofReal(Rᵏ) · (F(R r) / ofReal((R r)ᵏ)) → 0` as `r → 0+`.
  have hRr : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_const_mul R).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r) using mul_pos hR hr
  have hlim := ENNReal.Tendsto.const_mul (hZ.comp hRr)
    (Or.inr (ENNReal.ofReal_ne_top (r := R ^ k)))
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Function.comp_apply, hF, mul_pow, ENNReal.ofReal_mul (by positivity), ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      ENNReal.ofReal_ne_top, ENNReal.ofReal_inv_of_pos (by positivity), div_eq_mul_inv, mul_comm]

/-- Restriction of a rectifiable triple to a Borel set (Simon Ch. 6, 2.9 for `τ(M, θ, ξ)` of
3.1): `(M ∩ A, θ, ξ)` again satisfies the conditions of 3.1.  Every field passes to the subset
`M ∩ A ⊆ M`, the a.e. ones through `Hⁿ⌞(M ∩ A) ≤ Hⁿ⌞M`.  For the orientation,
`Submission.dmr_weightedTangent_inter` makes the weighted approximate tangent space
`span τ` of `(M, θ)` one of `(M ∩ A, θ)` at `Hⁿ⌞(M ∩ A)`-a.e. `x`, with the same frame `τ`. -/
theorem Submission.dmr_rectifiableTriple_inter :
    ∀ (N k : ℕ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) k)
      (A : Set (Eucl N)), IsRectifiableTriple (univ : Set (Eucl N)) k M θ ξ → MeasurableSet A →
      IsRectifiableTriple (univ : Set (Eucl N)) k (M ∩ A) θ ξ := by
  intro N k M θ ξ A hT hA
  have hle : (μHE[k] : Measure (Eucl N)).restrict (M ∩ A) ≤
      (μHE[k] : Measure (Eucl N)).restrict M :=
    Measure.restrict_mono inter_subset_left le_rfl
  have htan := Submission.dmr_weightedTangent_inter N k M θ hT.nullMeasurableSet hT.pos
    (fun K hK => hT.integrableOn K hK (subset_univ K)) A hA
  refine
    { subset := subset_univ _
      nullMeasurableSet := hT.nullMeasurableSet.inter hA.nullMeasurableSet
      countablyRectifiable := hT.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => hT.pos x hx.1
      integrableOn := fun K hK hKU =>
        (hT.integrableOn K hK hKU).mono_set (inter_subset_inter_left K inter_subset_left)
      aestronglyMeasurable := hT.aestronglyMeasurable.mono_measure hle
      orients := ?_ }
  filter_upwards [ae_mono hle hT.orients, htan] with x hx hL
  obtain ⟨τ, hτ, hM, hξ⟩ := hx
  exact ⟨τ, hτ, hL _ hM, hξ⟩

/-- **Mass measure, representation and restriction, Simon Ch. 6, (2.7)–(2.9), 2.12 and 3.1
(pp. 136–137, 146).**  Let `X ∈ 𝒟_k(ℝ^N)` with `M(X) < ∞`.  Then `M_W(X) ≤ M(X) < ∞` for every
`W`, so (R2) of `iwl_restriction_theory` gives the mass measure `μ`, a restriction `Y = X ⌞ A` to
every Borel set `A` and `M_W(Y) = μ(W ∩ A)`, and `rectifiability_mass_measure_representation`
gives a representation `(μ, v)` of `X`.  `μ` is finite and vanishes off `spt X`
(`dmr_massMeasure_support_finite`).  Any two representations of `X` have the same vector measure
on Borel sets (`dmr_measureRepresentation_unique`); this is the uniqueness conjunct and gives
`Y(ω) = ∫_A ⟨ω, v⟩ dμ`, while restrictions are unique by (R1).  If `X = τ(M, θ, ξ)` is integer
multiplicity, then `Y = τ(M ∩ A, θ, ξ)` (`polyhedral_approx_restriction_tau`), `(M ∩ A, θ, ξ)` is a
rectifiable triple (`dmr_rectifiableTriple_inter`) and `θ` is still integer-valued on `M ∩ A`. -/
theorem Submission.deformation_mass_restriction : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k), X.mass < ∞ → ∃ (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) k), IsFiniteMeasure μ ∧ IsMeasureRepresentation X μ v ∧ μ X.supportᶜ = 0 ∧ (∀ (μ' : Measure (Eucl N)) (v' : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation X μ' v' → ∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A → ∀ α : Covector (Eucl N) k, ∫ x in A, v' x α ∂μ' = ∫ x in A, v x α ∂μ) ∧ ∀ A : Set (Eucl N), MeasurableSet A → ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y ∧ (∀ ω : TestFormOn (univ : Set (Eucl N)) k, Y ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl N) k) x) ∂μ) ∧ (∀ W : Set (Eucl N), IsOpen W → Y.massOn W = μ (W ∩ A)) ∧ (∀ Y' : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y' → Y' = Y) ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) := by
  intro N k X hX
  -- `M_W(X) ≤ M(X) < ∞` for every `W ⊂⊂ ℝ^N`.
  have hloc : ∀ W, CompactlyContainedOpen W (univ : Set (Eucl N)) → X.massOn W < ∞ :=
    fun W _ => (X.massOn_mono (subset_univ W)).trans_lt hX
  -- (R2) on `U = ℝ^N`: the mass measure `μ`, restrictions to Borel sets and their masses.
  obtain ⟨μ, hμ, hres, hmass⟩ :=
    Submission.iwl_restriction_theory.2.2 N k univ isOpen_univ X hloc
  -- A representation `(μ, v)` of `X` with respect to its mass measure (2.7).
  obtain ⟨v, -, -, hrep⟩ :=
    (Submission.rectifiability_mass_measure_representation N k univ isOpen_univ X hloc).2 μ hμ
  obtain ⟨hsupp, hfin⟩ := Submission.dmr_massMeasure_support_finite N k X μ hμ
  -- Every representation `(μ', v')` of `X` has the vector measure of `(μ, v)` on Borel sets.
  have huniq := fun (μ' : Measure (Eucl N)) (v' : Eucl N → NVector (Eucl N) k)
      (hrep' : IsMeasureRepresentation X μ' v') =>
    Submission.dmr_measureRepresentation_unique N k X μ' μ v' v hrep' hrep
  refine ⟨μ, v, hfin hX, hrep, hsupp, fun μ' v' hrep' => (huniq μ' v' hrep').2, fun A hA => ?_⟩
  obtain ⟨Y, hY⟩ := hres A hA
  refine ⟨Y, hY, ?_, fun W hW => hmass A Y hY W hW (subset_univ W),
    fun Y' hY' => Submission.iwl_restriction_theory.2.1 N k univ isOpen_univ X A Y' Y hY' hY, ?_⟩
  · -- `Y` is defined through some representation `(μ', v')` of `X`, whose integrals over `A`
    -- agree with those of `(μ, v)`.
    obtain ⟨-, μ', v', hrep', hYω⟩ := hY
    exact fun ω => (hYω ω).trans ((huniq μ' v' hrep').1 A hA ω)
  · -- Simon 3.1: `X ⌞ A = τ(M ∩ A, θ, ξ)`, and `θ` is still integer-valued on `M ∩ A`.
    rintro ⟨M, θ, ξ, hMθξ, hθ, hXτ⟩
    exact ⟨M ∩ A, θ, ξ, Submission.dmr_rectifiableTriple_inter N k M θ ξ A hMθξ hA,
      fun x hx => hθ x hx.1,
      Submission.polyhedral_approx_restriction_tau N k univ isOpen_univ X M θ ξ hMθξ hXτ A Y hY⟩
/-- Locality of approximate tangent spaces (Simon Ch. 3, Def. 1.4): if `E ⊆ E'` are
`Hᵏ`-null-measurable and `Hᵏ(E' ∩ K) < ∞` for every compact `K`, then for `Hᵏ`-a.e. `x ∈ E`
and every subspace `Q`, `Q` is the approximate tangent space of `E` at `x` iff it is that of
`E'` at `x`.  By the Upper Density Theorem `Hᵏ((E' \ E) ∩ B̄_ρ(x)) = o(ρᵏ)` at such `x`, and by
the dilation identity the blow-up integrals of `E` and `E'` then differ by `o(1)`. -/
theorem Submission.imc_approxTangent_iff_of_subset :
    ∀ (N k : ℕ) (E E' : Set (Eucl N)), E ⊆ E' → NullMeasurableSet E (μHE[k] : Measure (Eucl N)) →
      NullMeasurableSet E' (μHE[k] : Measure (Eucl N)) →
      (∀ K : Set (Eucl N), IsCompact K → (μHE[k] : Measure (Eucl N)) (E' ∩ K) < ∞) →
      ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N),
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E x Q ↔
          Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E' x Q := by
  intro N k E E' hEE' hE hE' hfin
  -- Step 1: `Hᵏ((E' \ E) ∩ B̄_ρ(x)) / ρᵏ → 0` as `ρ → 0+`, for `Hᵏ`-a.e. `x ∈ E`.
  have hS : NullMeasurableSet (E' \ E) (μHE[k] : Measure (Eucl N)) := hE'.diff hE
  have hSfin : ∀ K : Set (Eucl N), IsCompact K →
      ∫⁻ _ in (E' \ E) ∩ K, (1 : ℝ≥0∞) ∂(μHE[k] : Measure (Eucl N)) < ∞ := by
    intro K hK
    rw [setLIntegral_one]
    exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hfin K hK)
  filter_upwards [ae_restrict_of_ae
      (Submission.imc_ae_zero_density_off_set N k (E' \ E) (fun _ => 1) hS hSfin),
    ae_restrict_mem₀ hE] with x hx hxE Q
  have hdens := hx fun h => h.2 hxE
  simp only [setLIntegral_one] at hdens
  -- Steps 2–3: for every `f ∈ C_c(ℝᴺ)` the blow-up integrals of `E'` and `E` differ by `o(1)`.
  have key : ∀ f : CompactlySupportedContinuousMap (Eucl N) ℝ, Tendsto (fun r : ℝ =>
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E', f y ∂(μHE[k] : Measure (Eucl N))) -
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E, f y ∂(μHE[k] : Measure (Eucl N)))
      (𝓝[>] 0) (𝓝 0) := by
    intro f
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    obtain ⟨R, hR, hRf⟩ :=
      f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Eucl N)
    -- `f ∘ η_{x,r}` vanishes off `B̄_{Rr}(x)`.
    have hvan : ∀ r : ℝ, 0 < r → ∀ z, z ∉ closedBall x (R * r) →
        f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) = 0 := by
      intro r hr z hz
      by_contra hne
      have hmem := hRf (subset_tsupport f hne)
      rw [mem_closedBall, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr] at hmem
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      linarith [mul_comm R r]
    -- For `r > 0`: `|I_{E'}(r) - I_E(r)| ≤ C Rᵏ Hᵏ((E' \ E) ∩ B̄_{Rr}(x)) / (Rr)ᵏ`.
    have hbound : ∀ r : ℝ, 0 < r →
        ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E', f y
            ∂(μHE[k] : Measure (Eucl N))) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' E, f y
            ∂(μHE[k] : Measure (Eucl N))‖ ≤
        C * R ^ k * ((μHE[k] : Measure (Eucl N)) ((E' \ E) ∩ closedBall x (R * r)) /
          ENNReal.ofReal ((R * r) ^ k)).toReal := by
      intro r hr
      have hcont : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) := by
        refine f.continuous.comp ?_
        unfold Poincare.SimonGMT.Chapter03.blowUpMap
        fun_prop
      -- `f ∘ η_{x,r}` is continuous with compact support, and `Hᵏ ⌞ E'` is finite on compacts.
      have hint : IntegrableOn (fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)) E'
          (μHE[k] : Measure (Eucl N)) := by
        have : IsFiniteMeasureOnCompacts ((μHE[k] : Measure (Eucl N)).restrict E') := by
          refine ⟨fun K hK => ?_⟩
          rw [Measure.restrict_apply hK.measurableSet, inter_comm]
          exact hfin K hK
        exact hcont.integrable_of_hasCompactSupport
          (HasCompactSupport.intro (isCompact_closedBall x (R * r)) (hvan r hr))
      have hsplit : (∫ z in E', f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[k] : Measure (Eucl N))) -
          ∫ z in E, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[k] : Measure (Eucl N)) =
          ∫ z in (E' \ E) ∩ closedBall x (R * r), f (Poincare.SimonGMT.Chapter03.blowUpMap x r z)
            ∂(μHE[k] : Measure (Eucl N)) := by
        rw [← setIntegral_sdiff₀ hE hint hEE']
        exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hS inter_subset_left
          (Eventually.of_forall fun z hz => hvan r hr z fun h => hz.2 ⟨hz.1, h⟩)
      have hfinB : (μHE[k] : Measure (Eucl N)) ((E' \ E) ∩ closedBall x (R * r)) < ∞ :=
        (measure_mono (inter_subset_inter_left _ sdiff_subset)).trans_lt
          (hfin _ (isCompact_closedBall x (R * r)))
      rw [Submission.lpf_wtc_blowup_setIntegral_image N k x r E' f hr,
        Submission.lpf_wtc_blowup_setIntegral_image N k x r E f hr, ← mul_sub, hsplit, norm_mul,
        norm_inv, norm_pow, Real.norm_of_nonneg hr.le, ENNReal.toReal_div,
        ENNReal.toReal_ofReal (by positivity), ← measureReal_def]
      calc (r ^ k)⁻¹ * ‖∫ z in (E' \ E) ∩ closedBall x (R * r),
            f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) ∂(μHE[k] : Measure (Eucl N))‖
          ≤ (r ^ k)⁻¹ *
              (C * (μHE[k] : Measure (Eucl N)).real ((E' \ E) ∩ closedBall x (R * r))) :=
            mul_le_mul_of_nonneg_left
              (norm_setIntegral_le_of_norm_le_const hfinB fun z _ => hC _) (by positivity)
        _ = C * R ^ k * ((μHE[k] : Measure (Eucl N)).real ((E' \ E) ∩ closedBall x (R * r)) /
              (R * r) ^ k) := by
            rw [mul_pow]
            field_simp
    -- `ρ = R r → 0+` as `r → 0+`, so the bound tends to `0` by Step 1.
    have hlin : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hR hr
    have hlim := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hdens.comp hlin)).const_mul (C * R ^ k)
    rw [ENNReal.toReal_zero, mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with r hr using hbound r hr
  -- Step 4: the blow-up integrals of `E` and `E'` have the same limits.
  constructor
  · rintro ⟨hdim, hlim⟩
    exact ⟨hdim, fun f => by simpa using (hlim f).add (key f)⟩
  · rintro ⟨hdim, hlim⟩
    exact ⟨hdim, fun f => by simpa using (hlim f).sub (key f)⟩
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

/-- Simon Ch. 3, Remark 1.8(1): for `Hᵏ`-a.e. `x ∈ E` and every subspace `Q`, `Q` is the
approximate tangent space of `E` at `x` with respect to `θ` (Definition 1.7) iff it is the
approximate tangent space of `E` at `x` (Definition 1.4).  Off an `Hᵏ`-null set, `x` lies in a
compact Lusin piece `C ⊆ E` on which `θ` is continuous, and both `Hᵏ ⌞ (E ∖ C)` and
`θ Hᵏ ⌞ (E ∖ C)` have `k`-density `0` at `x`.  Both tangent conditions then transfer between `E`
and `C`. -/
theorem Submission.imc_weightedTangent_iff_approxTangent : ∀ (N k : ℕ) (E : Set (Eucl N)) (θ : Eucl N → ℝ), NullMeasurableSet E (μHE[k] : Measure (Eucl N)) → (∀ K : Set (Eucl N), IsCompact K → (μHE[k] : Measure (Eucl N)) (E ∩ K) < ∞) → (∀ x ∈ E, 0 < θ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ (E ∩ K) (μHE[k] : Measure (Eucl N))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict E), ∀ Q : Submodule ℝ (Eucl N), HasWeightedApproximateTangentSpaceAt k E θ x Q ↔ Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k E x Q := by
  intro N k E θ hE hEfin hθ hθint
  -- Step 2: compact pieces `C i ⊆ E`, `θ|C i` continuous, covering `E` up to an `Hᵏ`-null set.
  obtain ⟨C, hCc, hCE, hθC, hCfin, hEC⟩ := Submission.lpf_wtc_lusin_compact_pieces N k univ E θ
    isOpen_univ (subset_univ E) hE hθ fun K hK _ => hθint K hK
  have hCm : ∀ i, NullMeasurableSet (C i) (μHE[k] : Measure (Eucl N)) := fun i =>
    (hCc i).isClosed.measurableSet.nullMeasurableSet
  have hS : ∀ i, NullMeasurableSet (E \ C i) (μHE[k] : Measure (Eucl N)) := fun i =>
    hE.diff (hCm i)
  -- Step 3: `Hᵏ ⌞ (E ∖ C i)` and `θ Hᵏ ⌞ (E ∖ C i)` have `k`-density `0` at a.e. `x ∉ E ∖ C i`.
  have hdens₁ : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl N)), x ∉ E \ C i →
      Tendsto (fun ρ : ℝ => (μHE[k] : Measure (Eucl N)) ((E \ C i) ∩ closedBall x ρ) /
        ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) := by
    intro i
    have h := Submission.imc_ae_zero_density_off_set N k (E \ C i) (fun _ => 1) (hS i)
      fun K hK => by
        simp only [setLIntegral_one]
        exact (measure_mono (inter_subset_inter_left K sdiff_subset)).trans_lt (hEfin K hK)
    simpa only [setLIntegral_one] using h
  have hdens₂ : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl N)), x ∉ E \ C i →
      Tendsto (fun ρ : ℝ => (∫⁻ y in (E \ C i) ∩ closedBall x ρ, ENNReal.ofReal (θ y)
        ∂(μHE[k] : Measure (Eucl N))) / ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) := fun i =>
    Submission.imc_ae_zero_density_off_set N k (E \ C i) (fun y => ENNReal.ofReal (θ y)) (hS i)
      fun K hK => (lintegral_mono_set (inter_subset_inter_left K sdiff_subset)).trans_lt
        (hθint K hK).lintegral_lt_top
  -- `Hᵏ ⌞ E`-a.e. `x` lies in some piece `C i`.
  have hcov : ∀ᵐ x ∂(μHE[k] : Measure (Eucl N)), x ∈ E → x ∈ ⋃ i, C i :=
    measure_mono_null (fun x hx => not_imp.1 hx) hEC
  filter_upwards [ae_restrict_mem₀ hE, ae_restrict_of_ae (ae_all_iff.2 hdens₁),
    ae_restrict_of_ae (ae_all_iff.2 hdens₂), (ae_restrict_iff'₀ hE).2 hcov]
    with x hxE hx₁ hx₂ hxC Q
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxC
  have hxS : x ∉ E \ C i := fun h => h.2 hi
  -- Steps 4–7 at `x` are carried out on the piece `C i`; collect the data they need.
  have h₀ : Tendsto (fun ρ : ℝ => (μHE[k] : Measure (Eucl N)) ((C i \ E) ∩ closedBall x ρ) /
      ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) := by
    simp only [sdiff_eq_empty.2 (hCE i), empty_inter, measure_empty, ENNReal.zero_div]
    exact tendsto_const_nhds
  have hθ₀ : ∀ y ∈ E, 0 ≤ θ y := fun y hy => (hθ y hy).le
  have hCr : (μHE[k] : Measure (Eucl N)) (C i ∩ closedBall x 1) < ∞ :=
    (measure_mono inter_subset_left).trans_lt (hCfin i)
  have hr : ∃ r : ℝ, 0 < r ∧ (μHE[k] : Measure (Eucl N)) (C i ∩ closedBall x r) < ∞ ∧
      IntegrableOn θ (E ∩ closedBall x r) (μHE[k] : Measure (Eucl N)) :=
    ⟨1, one_pos, hCr, hθint _ (isCompact_closedBall x 1)⟩
  have hθx : ContinuousWithinAt θ (C i) x := (hθC i).continuousWithinAt hi
  constructor
  · -- (⇒) weighted tangent of `E` ⇒ tangent of `C i` ⇒ tangent of `E`.
    intro hw
    exact Submission.lpf_wtc_tangent_transfer N k E (C i) x Q hE (hCm i)
      (Submission.imc_wte_approxTangent_of_weightedTangent N k E (C i) θ x Q hE (hCm i) (hCE i)
        hθ₀ (hθ x hxE) hw hr hθx (hx₂ i hxS))
      ⟨1, one_pos, hCr⟩ (hx₁ i hxS) h₀
  · -- (⇐) tangent of `E` ⇒ tangent of `C i` ⇒ weighted tangent of `E`.
    intro hu
    exact Submission.lpf_wtc_weighted_tangent_transfer N k E (C i) θ x Q hE (hCm i) (hCE i) hi hθ₀
      (Submission.lpf_wtc_tangent_transfer N k (C i) E x Q (hCm i) hE hu
        ⟨1, one_pos, hEfin _ (isCompact_closedBall x 1)⟩ h₀ (hx₁ i hxS))
      hr hθx (hx₂ i hxS)
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

/-- Pointwise eventual limits of rectifiable triples are rectifiable triples (Simon Ch. 6, 3.13,
last paragraph of the proof: `ξ_Q(x) ∈ Λₙ(TₓM_Q)`, `TₓM₊ = TₓM_Q` up to small measure, hence
`ξ(x) ∈ Λₙ(TₓM₊)`).  With `θⱼ, θ₀ ≥ 1` the sets `Mⱼ`, `M₀` have locally finite `Hᵏ` measure.
`M₀` lies in `⋃ⱼ Mⱼ` up to an `Hᵏ`-null set, so it is countably rectifiable, and `ξ₀` is the
a.e. limit of `Mⱼ.indicator ξⱼ`, so it is a.e. strongly measurable.  For a.e. `x ∈ M₀ ∩ Mⱼ` a
weighted tangent space of `(Mⱼ, θⱼ)` at `x` is one of `(M₀, θ₀)`: weighted and unweighted
tangent spaces agree a.e. (Ch. 3, Remark 1.8(1); `imc_weightedTangent_iff_approxTangent`), and
the approximate tangent spaces of `Mⱼ ∩ M₀` agree a.e. with those of `Mⱼ` and of `M₀`
(`imc_approxTangent_iff_of_subset`).  At such `x`, for `j ≥ J(x)` the frames `τʲ` orienting
`ξⱼ(x)` all span the unique weighted tangent space of `(M₀, θ₀)` at `x`, so
`ξⱼ(x) ∈ {s, -s}` with `s = simpleNVector τᴶ` (`fiw_ims_frame_sign`); this set is closed, hence
contains `ξ₀(x) = lim ξⱼ(x)`. -/
theorem Submission.imc_isRectifiableTriple_of_eventually_mem :
    ∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k) (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), (∀ j, IsRectifiableTriple (univ : Set (Eucl N)) k (M j) (θ j) (ξ j)) → (∀ j, ∀ x ∈ M j, 1 ≤ θ j x) → NullMeasurableSet M₀ (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M₀, 1 ≤ θ₀ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict M₀), (∀ᶠ j in atTop, x ∈ M j) ∧ Tendsto (fun j => ξ j x) atTop (𝓝 (ξ₀ x))) → IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ := by
  have hA := Submission.imc_approxTangent_iff_of_subset
  have hB := Submission.imc_weightedTangent_iff_approxTangent
  have hFrame := Submission.fiw_ims_frame_sign
  intro N k M θ ξ M₀ θ₀ ξ₀ hTri hθ1 hM₀ hθ₀1 hθ₀int hpt
  set H : Measure (Eucl N) := (μHE[k] : Measure (Eucl N)) with hH
  -- Step 1: `ϑ ≥ 1` on `E` and `ϑ` integrable on `E ∩ K` give `H (E ∩ K) < ∞`.
  have hfinGen : ∀ (E : Set (Eucl N)) (ϑ : Eucl N → ℝ), NullMeasurableSet E H →
      (∀ x ∈ E, 1 ≤ ϑ x) → ∀ K : Set (Eucl N), IsCompact K → IntegrableOn ϑ (E ∩ K) H →
      H (E ∩ K) < ∞ := by
    intro E ϑ hE h1 K hK hint
    have hEK : NullMeasurableSet (E ∩ K) H := hE.inter hK.measurableSet.nullMeasurableSet
    calc H (E ∩ K) = ∫⁻ _x in E ∩ K, 1 ∂H := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in E ∩ K, ‖ϑ x‖ₑ ∂H := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hEK] with x hx
          have h := h1 x hx.1
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by linarith)]
          exact ENNReal.one_le_ofReal.mpr h
      _ < ∞ := hint.hasFiniteIntegral
  have hfin : ∀ j, ∀ K : Set (Eucl N), IsCompact K → H (M j ∩ K) < ∞ := fun j K hK =>
    hfinGen (M j) (θ j) (hTri j).nullMeasurableSet (hθ1 j) K hK
      ((hTri j).integrableOn K hK (subset_univ K))
  have hfin₀ : ∀ K : Set (Eucl N), IsCompact K → H (M₀ ∩ K) < ∞ := fun K hK =>
    hfinGen M₀ θ₀ hM₀ hθ₀1 K hK (hθ₀int K hK)
  -- Step 5 (i)–(iv): weighted ↔ unweighted for `(Mⱼ, θⱼ)` and `(M₀, θ₀)`, and locality of
  -- unweighted tangent spaces for `Mⱼ ∩ M₀ ⊆ Mⱼ` and `Mⱼ ∩ M₀ ⊆ M₀`.
  have hBj : ∀ j, ∀ᵐ x ∂(H.restrict (M j)), ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j) x Q := fun j =>
    hB N k (M j) (θ j) (hTri j).nullMeasurableSet (hfin j) (hTri j).pos
      (fun K hK => (hTri j).integrableOn K hK (subset_univ K))
  have hB₀ : ∀ᵐ x ∂(H.restrict M₀), ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k M₀ x Q :=
    hB N k M₀ θ₀ hM₀ hfin₀ (fun x hx => lt_of_lt_of_le one_pos (hθ₀1 x hx)) hθ₀int
  have hAj : ∀ j, ∀ᵐ x ∂(H.restrict (M j ∩ M₀)), ∀ Q : Submodule ℝ (Eucl N),
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j ∩ M₀) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j) x Q := fun j =>
    hA N k (M j ∩ M₀) (M j) inter_subset_left ((hTri j).nullMeasurableSet.inter hM₀)
      (hTri j).nullMeasurableSet (hfin j)
  have hA₀ : ∀ j, ∀ᵐ x ∂(H.restrict (M j ∩ M₀)), ∀ Q : Submodule ℝ (Eucl N),
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j ∩ M₀) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k M₀ x Q := fun j =>
    hA N k (M j ∩ M₀) M₀ inter_subset_right ((hTri j).nullMeasurableSet.inter hM₀) hM₀ hfin₀
  -- Step 5 (T_j): for `H⌞M₀`-a.e. `x ∈ Mⱼ`, weighted tangent spaces of `(Mⱼ, θⱼ)` at `x` are
  -- weighted tangent spaces of `(M₀, θ₀)`.
  have hTj : ∀ j, ∀ᵐ x ∂(H.restrict M₀), x ∈ M j → ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x Q →
        HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x Q := by
    intro j
    have hjM : NullMeasurableSet (M j ∩ M₀) H := (hTri j).nullMeasurableSet.inter hM₀
    have h1 := (ae_restrict_iff'₀ (hTri j).nullMeasurableSet).1 (hBj j)
    have h2 := (ae_restrict_iff'₀ hjM).1 (hAj j)
    have h3 := (ae_restrict_iff'₀ hjM).1 (hA₀ j)
    have h4 := (ae_restrict_iff'₀ hM₀).1 hB₀
    rw [ae_restrict_iff'₀ hM₀]
    filter_upwards [h1, h2, h3, h4] with x h1 h2 h3 h4 hx0 hxj Q hW
    exact (h4 hx0 Q).2 ((h3 ⟨hxj, hx0⟩ Q).1 ((h2 ⟨hxj, hx0⟩ Q).2 ((h1 hxj Q).1 hW)))
  -- Step 6 (O_j): the orientation of `(Mⱼ, θⱼ, ξⱼ)`, read `H⌞M₀`-a.e. on `Mⱼ`.
  have hOj : ∀ j, ∀ᵐ x ∂(H.restrict M₀), x ∈ M j → ∃ τ : Fin k → Eucl N, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x (Submodule.span ℝ (range τ)) ∧
      (ξ j x = simpleNVector τ ∨ ξ j x = -simpleNVector τ) := fun j =>
    ae_restrict_of_ae ((ae_restrict_iff'₀ (hTri j).nullMeasurableSet).1 (hTri j).orients)
  -- Step 7: orientation of the limit; `ξⱼ(x) ∈ {s, -s}` for `j ≥ J`, a closed set.
  have horients : ∀ᵐ x ∂(H.restrict M₀), ∃ τ : Fin k → Eucl N, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x (Submodule.span ℝ (range τ)) ∧
      (ξ₀ x = simpleNVector τ ∨ ξ₀ x = -simpleNVector τ) := by
    have hTall := ae_all_iff.2 hTj
    have hOall := ae_all_iff.2 hOj
    have hmem : ∀ᵐ x ∂(H.restrict M₀), x ∈ M₀ := ae_restrict_mem₀ hM₀
    filter_upwards [hpt, hTall, hOall, hmem] with x hx hT hO hxM
    obtain ⟨hev, hlim⟩ := hx
    have hθx : θ₀ x ≠ 0 := (lt_of_lt_of_le one_pos (hθ₀1 x hxM)).ne'
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    choose! τ hτon hτW hτξ using hO
    refine ⟨τ J, hτon J (hJ J le_rfl), hT J (hJ J le_rfl) _ (hτW J (hJ J le_rfl)), ?_⟩
    set s := simpleNVector (τ J) with hs
    have hmem' : ∀ᶠ j in atTop, ξ j x ∈ ({s, -s} : Set (NVector (Eucl N) k)) := by
      filter_upwards [eventually_ge_atTop J] with j hj
      have hxj : x ∈ M j := hJ j hj
      have hspan : Submodule.span ℝ (range (τ J)) = Submodule.span ℝ (range (τ j)) :=
        HasWeightedApproximateTangentSpaceAt.unique hθx
          (hT J (hJ J le_rfl) _ (hτW J (hJ J le_rfl))) (hT j hxj _ (hτW j hxj))
      have hsign := hFrame N k (τ J) (τ j) (hτon J (hJ J le_rfl)) (hτon j hxj) hspan
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hτξ j hxj with h | h <;> rcases hsign with h' | h'
      · exact Or.inl (by rw [h, h'])
      · exact Or.inr (by rw [h, h'])
      · exact Or.inr (by rw [h, h'])
      · exact Or.inl (by rw [h, h']; ext α; simp [s])
    have hcl : IsClosed ({s, -s} : Set (NVector (Eucl N) k)) := (Set.toFinite _).isClosed
    simpa using hcl.mem_of_tendsto hlim hmem'
  -- Step 3: `M₀ ⊆ (M₀ \ ⋃ⱼ Mⱼ) ∪ ⋃ⱼ Mⱼ`, the first set being `H`-null.
  have hcr : CountablyRectifiable k M₀ := by
    have hZ : H (M₀ \ ⋃ j, M j) = 0 := by
      have h : ∀ᵐ x ∂(H.restrict M₀), x ∈ ⋃ j, M j := by
        filter_upwards [hpt] with x hx
        obtain ⟨j, hj⟩ := hx.1.exists
        exact mem_iUnion.2 ⟨j, hj⟩
      rw [ae_restrict_iff'₀ hM₀, ae_iff] at h
      refine measure_mono_null (fun x hx => ?_) h
      simp only [Set.mem_ofPred_eq, not_imp]
      exact ⟨hx.1, hx.2⟩
    let S : ℕ → Set (Eucl N) := fun i => Nat.casesOn i (M₀ \ ⋃ j, M j) (fun j => M j)
    have hS : ∀ i, CountablyRectifiable k (S i) := by
      intro i
      cases i with
      | zero => exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hZ
      | succ j => exact (hTri j).countablyRectifiable
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion S hS).mono fun x hx => ?_
    by_cases h : x ∈ ⋃ j, M j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨j + 1, hj⟩
    · exact mem_iUnion.2 ⟨0, ⟨hx, h⟩⟩
  -- Step 4: `ξ₀` is the `H⌞M₀`-a.e. limit of `Mⱼ.indicator ξⱼ`.  The pseudo-metrizable
  -- structure of `NVector (Eucl N) k` is supplied by hand: its topology is
  -- `ContinuousLinearMap.topologicalSpace`, which is the operator-norm topology.
  have hmeas : AEStronglyMeasurable ξ₀ (H.restrict M₀) := by
    have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl N) k) :=
      ⟨⟨inferInstance, rfl, @EMetric.instIsCountablyGeneratedUniformity (NVector (Eucl N) k) _⟩⟩
    have hg : ∀ j, AEStronglyMeasurable ((M j).indicator (ξ j)) (H.restrict M₀) := fun j =>
      ((aestronglyMeasurable_indicator_iff₀ (hTri j).nullMeasurableSet).2
        (hTri j).aestronglyMeasurable).restrict
    refine aestronglyMeasurable_of_tendsto_ae atTop hg ?_
    filter_upwards [hpt] with x hx
    refine hx.2.congr' ?_
    filter_upwards [hx.1] with j hj
    rw [indicator_of_mem hj]
  -- Step 8: assemble the fields.
  exact { subset := subset_univ _, nullMeasurableSet := hM₀, countablyRectifiable := hcr,
          pos := fun x hx => lt_of_lt_of_le one_pos (hθ₀1 x hx),
          integrableOn := fun K hK _ => hθ₀int K hK,
          aestronglyMeasurable := hmeas, orients := horients }
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

/-- **Integer multiplicity limit of summably `L¹`-Cauchy densities (Simon Ch. 6, 3.13, printed
(2)–(3), pp. 149–150).**  Let `(M_p, θ_p, ξ_p)` be rectifiable triples in `ℝ^N` with
natural-valued multiplicities and densities `κ_p = 1_{M_p} θ_p ξ_p`, and suppose
`∑_p ∫ |κ_{p+1} - κ_p| dHᵏ < ∞`, where `|w|² = ∑_γ w(dx^γ)²`.  Then some rectifiable triple
`(M₀, θ₀, ξ₀)` with natural-valued multiplicity has `τ(M_p, θ_p, ξ_p)(ω) → τ(M₀, θ₀, ξ₀)(ω)` for
every continuous compactly supported `ω`.  The coordinates `f_p = (κ_p(dx^γ))_γ` converge a.e. and
in `L¹` to some `g`.  As `|ξ_p| = 1`, `‖f_p‖ = 1_{M_p} θ_p` a.e. is natural-valued, hence
eventually constant, so `θ₀ = ‖g‖` is natural-valued.  Take `M₀ = {θ₀ ≥ 1}` and
`ξ₀ = θ₀⁻¹ L(g)`, where `L(a) = ∑_γ a_γ e^γ` inverts the coordinates. -/
theorem Submission.imc_im_density_limit : ∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k), (∀ p, IsRectifiableTriple (univ : Set (Eucl N)) k (M p) (θ p) (ξ p)) → (∀ p, ∀ x ∈ M p, ∃ m : ℕ, θ p x = m) → (∑' p, ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate ((M (p + 1)).indicator (fun y => θ (p + 1) y • ξ (p + 1) y) x - (M p).indicator (fun y => θ p y • ξ p y) x) γ) ^ 2)) ∂(μHE[k] : Measure (Eucl N))) ≠ ∞ → ∃ (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ m : ℕ, θ₀ x = m) ∧ ∀ ω : Eucl N → Covector (Eucl N) k, Continuous ω → HasCompactSupport ω → Tendsto (fun p => tauAction k (M p) (θ p) (ξ p) ω) atTop (𝓝 (tauAction k M₀ θ₀ ξ₀ ω)) := by
  have hC2 := Submission.imc_ae_tendsto_of_summable_lintegral
  have hOrient := Submission.imc_isRectifiableTriple_of_eventually_mem
  have hPair := Submission.polyhedral_approx_pairing_expansion
  have hTau := Submission.ltg_tau_integrable
  intro N k M θ ξ hTri hNat hsum
  set H : Measure (Eucl N) := (μHE[k] : Measure (Eucl N)) with hH
  -- Step 1(a): `θ_p ≥ 1` on `M_p`, as `θ_p` is natural-valued and positive there.
  have hθ1 : ∀ p, ∀ x ∈ M p, 1 ≤ θ p x := by
    intro p x hx
    obtain ⟨m, hm⟩ := hNat p x hx
    have hpos := (hTri p).pos x hx
    rw [hm] at hpos ⊢
    have : m ≠ 0 := by rintro rfl; simp at hpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  -- Step 1: the densities `κ_p = 1_{M_p} θ_p ξ_p` and their coordinates `f_p = c(κ_p) ∈ ℝ^I`,
  -- where `c(w) = (w(dx^γ))_γ` is additive with `‖c(w)‖ = |w|` (Step 0(a)).
  set κ : ℕ → Eucl N → NVector (Eucl N) k :=
    fun p => (M p).indicator (fun y => θ p y • ξ p y) with hκ
  set c : NVector (Eucl N) k → EuclideanSpace ℝ (SimonMultiIndex k N) :=
    fun w => WithLp.toLp 2 (fun γ => euclideanNVectorCoordinate w γ) with hc
  set f : ℕ → Eucl N → EuclideanSpace ℝ (SimonMultiIndex k N) := fun p x => c (κ p x) with hf
  have hnormc : ∀ w : NVector (Eucl N) k,
      ‖c w‖ₑ = ENNReal.ofReal
        (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate w γ) ^ 2)) := by
    intro w
    rw [← ofReal_norm, EuclideanSpace.norm_eq]
    simp [hc, Real.norm_eq_abs, sq_abs]
  have hcsub : ∀ w w' : NVector (Eucl N) k, c (w - w') = c w - c w' := by
    intro w w'
    ext γ
    simp [hc, euclideanNVectorCoordinate]
  -- Step 1(b): `f_p` is a.e. strongly measurable.  Its `γ`-coordinate `1_{M_p} θ_p ξ_p(dx^γ)` is
  -- integrable on each `M_p ∩ closedBall 0 n` (tau_integrable (a)), and these cover `M_p`.
  have hcoord : ∀ p (γ : SimonMultiIndex k N),
      AEStronglyMeasurable (fun x => euclideanNVectorCoordinate (κ p x) γ) H := by
    intro p γ
    have heq : (fun x => euclideanNVectorCoordinate (κ p x) γ) =
        (M p).indicator
          (fun x => θ p x * ξ p x (wedgeCovectors k (fun j => EuclideanSpace.proj (γ j)))) := by
      funext x
      by_cases hx : x ∈ M p
      · simp [hκ, hx, euclideanNVectorCoordinate]
      · simp [hκ, hx, euclideanNVectorCoordinate]
    rw [heq, aestronglyMeasurable_indicator_iff₀ (hTri p).nullMeasurableSet]
    have hU : (⋃ n : ℕ, M p ∩ closedBall (0 : Eucl N) n) = M p := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · rintro ⟨n, hx, -⟩
        exact hx
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
        exact ⟨n, hx, hn⟩
    rw [← hU, aestronglyMeasurable_iUnion_iff]
    intro n
    exact ((hTau N k univ (M p) (θ p) (ξ p) (hTri p)).1 _ _ (isCompact_closedBall 0 n)
      (subset_univ _)).aestronglyMeasurable
  have hfmeas : ∀ p, AEStronglyMeasurable (f p) H := by
    intro p
    have hpi : AEStronglyMeasurable
        (fun x => (fun γ => euclideanNVectorCoordinate (κ p x) γ : SimonMultiIndex k N → ℝ)) H :=
      (aemeasurable_pi_iff.2 fun γ => (hcoord p γ).aemeasurable).aestronglyMeasurable
    exact (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable hpi
  -- Step 1(c): `‖f_{p+1} - f_p‖ = |κ_{p+1} - κ_p|`, so the series is the hypothesis.
  have hsum' : (∑' p, ∫⁻ x, ‖f (p + 1) x - f p x‖ₑ ∂H) ≠ ∞ := by
    convert hsum using 4 with p x
    simp only [hf, ← hcsub, hnormc]
    rfl
  -- Step 2: `f_p → g` a.e. and in `L¹` (l1_cauchy_limit).
  obtain ⟨g, hgmeas, hgae, hgL1⟩ :=
    hC2 (Eucl N) H (EuclideanSpace ℝ (SimonMultiIndex k N)) f hfmeas hsum'
  -- Step 0(d): `|τ₁ ∧ ⋯ ∧ τ_k| = 1` for orthonormal `τ`.  The covector
  -- `α₀ = ⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τ_k, ·⟩` has `α₀(τ) = det 1 = 1` and the same coordinates as
  -- `simpleNVector τ` (transposed determinants); expand `α₀(τ)` by the pairing expansion.
  have hunitfact : ∀ τ : Fin k → Eucl N, Orthonormal ℝ τ →
      ∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (simpleNVector τ) γ) ^ 2 = 1 := by
    intro τ hτ
    set α₀ : Covector (Eucl N) k := wedgeCovectors k (fun i => innerSL ℝ (τ i)) with hα₀
    have h1 : simpleNVector τ α₀ = 1 := by
      rw [simpleNVector_apply, hα₀, wedgeCovectors_apply_det]
      have : (Matrix.of fun i j => (innerSL ℝ (τ i)) (τ j)) = 1 := by
        ext i j
        rw [Matrix.of_apply, innerSL_apply_apply, Matrix.one_apply]
        exact orthonormal_iff_ite.mp hτ i j
      rw [this, Matrix.det_one]
    have h2 : ∀ γ : SimonMultiIndex k N, euclideanCovectorCoordinate α₀ γ =
        euclideanNVectorCoordinate (simpleNVector τ) γ := by
      intro γ
      simp only [euclideanCovectorCoordinate, euclideanNVectorCoordinate, simpleNVector_apply, hα₀]
      rw [wedgeCovectors_apply_det, wedgeCovectors_apply_det, ← Matrix.det_transpose]
      congr 1
      ext i j
      simp [Matrix.transpose_apply, EuclideanSpace.inner_single_right]
    have h3 := (hPair N k (simpleNVector τ) α₀).1
    rw [h1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [h2, sq]
    rfl
  -- Step 1(d): `‖f_p‖ = 1_{M_p} θ_p` a.e., as `ξ_p = ±simpleNVector τ` a.e. on `M_p`.
  have hunit : ∀ p, ∀ᵐ x ∂H, ‖f p x‖ = (M p).indicator (θ p) x := by
    intro p
    have hor := (hTri p).orients
    rw [ae_restrict_iff'₀ (hTri p).nullMeasurableSet] at hor
    filter_upwards [hor] with x hx
    by_cases hxM : x ∈ M p
    · obtain ⟨τ, hτ, -, hξ⟩ := hx hxM
      rw [indicator_of_mem hxM]
      have hθpos := (hTri p).pos x hxM
      have hfx : f p x = θ p x • c (ξ p x) := by
        ext γ
        simp [hf, hc, hκ, hxM, euclideanNVectorCoordinate]
      rw [hfx, norm_smul, Real.norm_eq_abs, abs_of_pos hθpos]
      have hc1 : ‖c (ξ p x)‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        have hs : ∑ γ : SimonMultiIndex k N, ‖(c (ξ p x)) γ‖ ^ 2 = 1 := by
          rw [← hunitfact τ hτ]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rcases hξ with h | h
          · simp [hc, h, Real.norm_eq_abs, sq_abs]
          · simp [hc, h, Real.norm_eq_abs, sq_abs, euclideanNVectorCoordinate]
        rw [hs, Real.sqrt_one]
      rw [hc1, mul_one]
    · rw [indicator_of_notMem hxM]
      have : κ p x = 0 := by simp [hκ, hxM]
      simp [hf, this, hc, euclideanNVectorCoordinate]
      rfl
  -- Step 3: a.e., the natural numbers `1_{M_p} θ_p(x) = ‖f_p(x)‖ → ‖g(x)‖` are eventually
  -- constant, so `‖g(x)‖` is a natural number, attained for all large `p`.
  have hnatlim : ∀ᵐ x ∂H, ∃ m : ℕ, ‖g x‖ = m ∧ ∀ᶠ p in atTop, (M p).indicator (θ p) x = m := by
    filter_upwards [hgae, ae_all_iff.2 hunit] with x hx hu
    have hnat : ∀ p, ∃ n : ℕ, (M p).indicator (θ p) x = n := by
      intro p
      by_cases hxM : x ∈ M p
      · rw [indicator_of_mem hxM]
        exact hNat p x hxM
      · exact ⟨0, by simp [indicator_of_notMem hxM]⟩
    choose n hn using hnat
    have hlim : Tendsto (fun p => (n p : ℝ)) atTop (𝓝 ‖g x‖) := by
      refine hx.norm.congr fun p => ?_
      rw [hu p, hn p]
    obtain ⟨P, hP⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)
    have hconst : ∀ p ≥ P, n p = n P := by
      intro p hp
      have h1 := hP p hp
      have h2 := hP P le_rfl
      rw [Real.dist_eq] at h1 h2
      have hlt : |(n p : ℝ) - n P| < 1 := by
        have := abs_sub_le (n p : ℝ) ‖g x‖ (n P)
        rw [abs_sub_comm ‖g x‖ (n P : ℝ)] at this
        linarith
      have hlt' : |((n p : ℤ) - n P : ℤ)| < 1 := by exact_mod_cast hlt
      have : ((n p : ℤ) - n P : ℤ) = 0 := Int.abs_lt_one_iff.mp hlt'
      omega
    refine ⟨n P, ?_, ?_⟩
    · refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
      exact eventually_atTop.2 ⟨P, fun p hp => by
        show (n P : ℝ) = n p
        rw [hconst p hp]⟩
    · exact eventually_atTop.2 ⟨P, fun p hp => by rw [hn p, hconst p hp]⟩
  -- Step 4: the limit data `θ₀ = ⌊‖g‖ + 1/2⌋₊`, `M₀ = {θ₀ ≥ 1}` and `ξ₀ = θ₀⁻¹ L(g)`, where
  -- `L(a) = ∑_γ a_γ e^γ` and `e^γ = e_{γ(0)} ∧ ⋯ ∧ e_{γ(k-1)}`.
  set θ₀ : Eucl N → ℝ := fun x => ((Nat.floor (‖g x‖ + 1 / 2) : ℕ) : ℝ) with hθ₀
  set M₀ : Set (Eucl N) := {x | 1 ≤ θ₀ x} with hM₀
  set e : SimonMultiIndex k N → NVector (Eucl N) k :=
    fun γ => simpleNVector (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) with he
  set L : EuclideanSpace ℝ (SimonMultiIndex k N) → NVector (Eucl N) k :=
    fun a => ∑ γ, a γ • e γ with hL
  set ξ₀ : Eucl N → NVector (Eucl N) k := fun x => (θ₀ x)⁻¹ • L (g x) with hξ₀
  -- Step 0(b): `L(c(w)) = w`, by the pairing expansion.
  have hLc : ∀ w : NVector (Eucl N) k, L (c w) = w := by
    intro w
    ext α
    have h := (hPair N k w α).1
    rw [h]
    simp only [hL, hc, he, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, simpleNVector_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp [euclideanCovectorCoordinate, mul_comm]
    left; rfl
  -- Step 3: `θ₀ = ‖g‖` a.e., as `⌊m + 1/2⌋₊ = m`.
  have hθ₀g : ∀ᵐ x ∂H, θ₀ x = ‖g x‖ := by
    filter_upwards [hnatlim] with x hx
    obtain ⟨m, hm, -⟩ := hx
    simp only [hθ₀, hm]
    have : Nat.floor ((m : ℝ) + 1 / 2) = m := by
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> norm_num
    rw [this]
  -- Step 4(a)–(b): `θ₀` is natural-valued, `θ₀ ≥ 1` on `M₀`, and `θ₀` is a.e. measurable
  -- (`t ↦ ⌊t⌋₊` is monotone), so `M₀` is null-measurable.
  have hfloor : Measurable (fun t : ℝ => ((Nat.floor t : ℕ) : ℝ)) := by
    have hm : Monotone (fun t : ℝ => ((Nat.floor t : ℕ) : ℝ)) := fun a b hab => by
      show ((Nat.floor a : ℕ) : ℝ) ≤ ((Nat.floor b : ℕ) : ℝ)
      exact_mod_cast Nat.floor_mono hab
    exact hm.measurable
  have hθ₀meas : AEMeasurable θ₀ H :=
    hfloor.comp_aemeasurable (hgmeas.norm.aemeasurable.add_const _)
  have hM₀meas : NullMeasurableSet M₀ H :=
    hθ₀meas.nullMeasurableSet_preimage measurableSet_Ici
  have hθ₀1 : ∀ x ∈ M₀, 1 ≤ θ₀ x := fun x hx => hx
  -- Step 4(c): `θ₀` is integrable on `M₀ ∩ K`.  Pick `p` with `∫ ‖f_p - g‖ < ∞`; then a.e.
  -- `θ₀ = ‖g‖ ≤ ‖f_p‖ + ‖f_p - g‖`, and `∫_K ‖f_p‖ = ∫_{M_p ∩ K} θ_p < ∞` by Step 1(d).
  have hθ₀int : ∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) H := by
    intro K hK
    obtain ⟨p, hp⟩ : ∃ p, ∫⁻ x, ‖f p x - g x‖ₑ ∂H < ∞ := by
      obtain ⟨p, hp⟩ := (hgL1.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
      exact ⟨p, hp.trans ENNReal.one_lt_top⟩
    have hfpK : ∫⁻ x in K, ‖f p x‖ₑ ∂H < ∞ := by
      have hint : IntegrableOn (θ p) (M p ∩ K) H := (hTri p).integrableOn K hK (subset_univ K)
      have hae : ∀ᵐ x ∂(H.restrict K), ‖f p x‖ₑ = (M p).indicator (fun y => ‖θ p y‖ₑ) x := by
        filter_upwards [ae_restrict_of_ae (hunit p)] with x hx
        rw [← ofReal_norm, hx, ← enorm_indicator_eq_indicator_enorm, ← ofReal_norm]
        congr 1
        rw [Real.norm_eq_abs, abs_of_nonneg]
        by_cases hxM : x ∈ M p
        · rw [indicator_of_mem hxM]
          exact ((hTri p).pos x hxM).le
        · rw [indicator_of_notMem hxM]
      rw [lintegral_congr_ae hae, lintegral_indicator₀
        ((hTri p).nullMeasurableSet.mono Measure.restrict_le_self),
        Measure.restrict_restrict₀ ((hTri p).nullMeasurableSet.mono Measure.restrict_le_self)]
      exact hint.hasFiniteIntegral
    have hθ₀ae : ∀ᵐ x ∂(H.restrict (M₀ ∩ K)), ‖θ₀ x‖ₑ ≤ ‖g x‖ₑ := by
      filter_upwards [ae_restrict_of_ae hθ₀g] with x hx
      rw [hx]
      simp
    refine ⟨hθ₀meas.aestronglyMeasurable.restrict, ?_⟩
    calc ∫⁻ x in M₀ ∩ K, ‖θ₀ x‖ₑ ∂H ≤ ∫⁻ x in M₀ ∩ K, ‖g x‖ₑ ∂H := lintegral_mono_ae hθ₀ae
      _ ≤ ∫⁻ x in K, ‖g x‖ₑ ∂H := lintegral_mono_set inter_subset_right
      _ ≤ ∫⁻ x in K, (‖f p x‖ₑ + ‖f p x - g x‖ₑ) ∂H := lintegral_mono fun x => by
            calc ‖g x‖ₑ = ‖f p x - (f p x - g x)‖ₑ := by rw [sub_sub_cancel]
              _ ≤ ‖f p x‖ₑ + ‖f p x - g x‖ₑ := enorm_sub_le
      _ = ∫⁻ x in K, ‖f p x‖ₑ ∂H + ∫⁻ x in K, ‖f p x - g x‖ₑ ∂H :=
            lintegral_add_left' (hfmeas p).enorm.restrict _
      _ < ∞ := ENNReal.add_lt_top.2 ⟨hfpK, (setLIntegral_le_lintegral _ _).trans_lt hp⟩
  -- Step 4(d): for a.e. `x ∈ M₀`, eventually `x ∈ M_p` and `θ_p(x) = θ₀(x)`, so
  -- `ξ_p(x) = θ₀(x)⁻¹ L(f_p(x)) → θ₀(x)⁻¹ L(g(x)) = ξ₀(x)`, as `L` is continuous.
  have hLcont : Continuous L := by
    have : ContinuousAdd (NVector (Eucl N) k) :=
      ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl N) k)).continuous_add⟩
    simp only [hL]
    fun_prop
  have hpt : ∀ᵐ x ∂(H.restrict M₀), (∀ᶠ p in atTop, x ∈ M p) ∧
      Tendsto (fun p => ξ p x) atTop (𝓝 (ξ₀ x)) := by
    have hmem : ∀ᵐ x ∂(H.restrict M₀), x ∈ M₀ := ae_restrict_mem₀ hM₀meas
    filter_upwards [hmem, ae_restrict_of_ae hnatlim, ae_restrict_of_ae hgae,
      ae_restrict_of_ae hθ₀g] with x hxM₀ hnx hgx hθx
    obtain ⟨m, hm, hev⟩ := hnx
    have hθ₀m : θ₀ x = m := by rw [hθx, hm]
    have hm1 : (1 : ℝ) ≤ m := hθ₀m ▸ hxM₀
    have hev' : ∀ᶠ p in atTop, x ∈ M p ∧ θ p x = θ₀ x := by
      filter_upwards [hev] with p hp
      have hne : (M p).indicator (θ p) x ≠ 0 := by
        rw [hp]
        exact (lt_of_lt_of_le one_pos hm1).ne'
      have hxp : x ∈ M p := by
        by_contra h
        exact hne (indicator_of_notMem h _)
      exact ⟨hxp, by rw [← indicator_of_mem hxp (θ p), hp, hθ₀m]⟩
    refine ⟨hev'.mono fun p hp => hp.1, ?_⟩
    have hθ₀ne : θ₀ x ≠ 0 := by
      rw [hθ₀m]
      exact (lt_of_lt_of_le one_pos hm1).ne'
    have hconv : Tendsto (fun p => (θ₀ x)⁻¹ • L (f p x)) atTop (𝓝 ((θ₀ x)⁻¹ • L (g x))) :=
      ((hLcont.tendsto _).comp hgx).const_smul _
    refine hconv.congr' ?_
    filter_upwards [hev'] with p hp
    have hκx : κ p x = θ₀ x • ξ p x := by
      simp only [hκ, indicator_of_mem hp.1, hp.2]
    show (θ₀ x)⁻¹ • L (c (κ p x)) = ξ p x
    rw [hLc, hκx, smul_smul, inv_mul_cancel₀ hθ₀ne, one_smul]
  -- Step 5: `(M₀, θ₀, ξ₀)` is a rectifiable triple (limit_triple), natural-valued by Step 4(a).
  have hTri₀ : IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ :=
    hOrient N k M θ ξ M₀ θ₀ ξ₀ hTri hθ1 hM₀meas hθ₀1 hθ₀int hpt
  refine ⟨M₀, θ₀, ξ₀, hTri₀, fun x _ => ⟨_, rfl⟩, fun ω hωc hωs => ?_⟩
  -- Step 6: convergence of the τ-actions.  The integrands are integrable (tau_integrable (b)).
  have hint : ∀ p, IntegrableOn (fun x => θ p x * ξ p x (ω x)) (M p) H := fun p =>
    (hTau N k univ (M p) (θ p) (ξ p) (hTri p)).2 ω hωc hωs (subset_univ _)
  have hint₀ : IntegrableOn (fun x => θ₀ x * ξ₀ x (ω x)) M₀ H :=
    (hTau N k univ M₀ θ₀ ξ₀ hTri₀).2 ω hωc hωs (subset_univ _)
  -- A uniform bound `|ω| ≤ C`: `x ↦ |ω(x)|` is continuous with compact support.
  have hωnorm : Continuous fun x => covectorEuclideanNorm (ω x) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((continuous_eval_const _).comp hωc).pow 2
    · exact continuous_const
  have hsupp : HasCompactSupport (fun x => covectorEuclideanNorm (ω x)) := by
    refine hωs.mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h
    apply hx
    rw [h]
    exact covectorEuclideanNorm_zero N k
  obtain ⟨C₀, hC₀⟩ := hωnorm.bddAbove_range_of_hasCompactSupport hsupp
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ x, covectorEuclideanNorm (ω x) ≤ C := fun x =>
    (hC₀ ⟨x, rfl⟩).trans (le_max_left _ _)
  -- Step 6(a)–(b): `τ(M_p, θ_p, ξ_p)(ω) = ∫ κ_p(ω)` and `τ(M₀, θ₀, ξ₀)(ω) = ∫ κ₀(ω)`, with
  -- integrable integrands.
  have hκapp : ∀ p x, κ p x (ω x) = (M p).indicator (fun y => θ p y * ξ p y (ω y)) x := by
    intro p x
    by_cases hx : x ∈ M p
    · simp [hκ, hx]
    · simp [hκ, hx]
  set κ₀ : Eucl N → NVector (Eucl N) k := M₀.indicator (fun y => θ₀ y • ξ₀ y) with hκ₀
  have hκ₀app : ∀ x, κ₀ x (ω x) = M₀.indicator (fun y => θ₀ y * ξ₀ y (ω y)) x := by
    intro x
    by_cases hx : x ∈ M₀
    · simp [hκ₀, hx]
    · simp [hκ₀, hx]
  have htau : ∀ p, tauAction k (M p) (θ p) (ξ p) ω = ∫ x, κ p x (ω x) ∂H := by
    intro p
    simp_rw [hκapp]
    rw [integral_indicator₀ (hTri p).nullMeasurableSet]
    rfl
  have htau₀ : tauAction k M₀ θ₀ ξ₀ ω = ∫ x, κ₀ x (ω x) ∂H := by
    simp_rw [hκ₀app]
    rw [integral_indicator₀ hM₀meas]
    rfl
  have hintp : ∀ p, Integrable (fun x => κ p x (ω x)) H := by
    intro p
    simp_rw [hκapp]
    exact (hint p).integrable_indicator₀ (hTri p).nullMeasurableSet
  have hint₀' : Integrable (fun x => κ₀ x (ω x)) H := by
    simp_rw [hκ₀app]
    exact hint₀.integrable_indicator₀ hM₀meas
  -- Step 6(c): `κ₀ = L(g)` a.e.; off `M₀`, `θ₀ = 0 = ‖g‖`.
  have hκ₀L : ∀ᵐ x ∂H, κ₀ x = L (g x) := by
    filter_upwards [hθ₀g] with x hx
    by_cases hxM : x ∈ M₀
    · have hne : θ₀ x ≠ 0 := (lt_of_lt_of_le one_pos (show (1 : ℝ) ≤ θ₀ x from hxM)).ne'
      simp only [hκ₀, indicator_of_mem hxM, hξ₀, smul_smul, mul_inv_cancel₀ hne, one_smul]
    · have hlt : θ₀ x < 1 := not_le.mp hxM
      have h0 : θ₀ x = 0 := by
        have hfl : Nat.floor (‖g x‖ + 1 / 2) < 1 := by
          have : ((Nat.floor (‖g x‖ + 1 / 2) : ℕ) : ℝ) < 1 := hlt
          exact_mod_cast this
        simp only [hθ₀, Nat.lt_one_iff.mp hfl, Nat.cast_zero]
      have hg0 : g x = 0 := by
        rw [h0] at hx
        exact norm_eq_zero.mp hx.symm
      simp only [hκ₀, indicator_of_notMem hxM, hg0, hL]
      simp
  -- Step 0(a), (c): `L` is additive and `|L(a)(α)| ≤ m ‖a‖ |α|`, where `m = #I`.
  have hLsub : ∀ a b : EuclideanSpace ℝ (SimonMultiIndex k N), L (a - b) = L a - L b := by
    intro a b
    ext α
    simp [hL, sub_mul, Finset.sum_sub_distrib]
  have hLbound : ∀ (a : EuclideanSpace ℝ (SimonMultiIndex k N)) (α : Covector (Eucl N) k),
      |L a α| ≤ (Fintype.card (SimonMultiIndex k N) : ℝ) * ‖a‖ * covectorEuclideanNorm α := by
    intro a α
    have hexp : L a α = ∑ γ, a γ * euclideanCovectorCoordinate α γ := by
      simp [hL, he, euclideanCovectorCoordinate]
    rw [hexp]
    calc |∑ γ, a γ * euclideanCovectorCoordinate α γ|
        ≤ ∑ γ, |a γ * euclideanCovectorCoordinate α γ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _γ : SimonMultiIndex k N, ‖a‖ * covectorEuclideanNorm α := by
          refine Finset.sum_le_sum fun γ _ => ?_
          rw [abs_mul]
          exact mul_le_mul (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le a γ)
            ((hPair N k 0 α).2 γ) (abs_nonneg _) (norm_nonneg _)
      _ = (Fintype.card (SimonMultiIndex k N) : ℝ) * ‖a‖ * covectorEuclideanNorm α := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  -- Step 6(d)–(e): `∫ |κ_p(ω) - κ₀(ω)| ≤ m C ∫ ‖f_p - g‖ → 0`, hence `∫ κ_p(ω) → ∫ κ₀(ω)`.
  set m : ℝ := (Fintype.card (SimonMultiIndex k N) : ℝ) with hm
  have hL1 : Tendsto (fun p => ∫⁻ x, ‖κ p x (ω x) - κ₀ x (ω x)‖ₑ ∂H) atTop (𝓝 0) := by
    have hb : ∀ p, ∫⁻ x, ‖κ p x (ω x) - κ₀ x (ω x)‖ₑ ∂H ≤
        ENNReal.ofReal (m * C) * ∫⁻ x, ‖f p x - g x‖ₑ ∂H := by
      intro p
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hκ₀L] with x hx
      have hdiff : κ p x (ω x) - κ₀ x (ω x) = L (f p x - g x) (ω x) := by
        rw [hx, hLsub]
        show κ p x (ω x) - L (g x) (ω x) = (L (c (κ p x)) - L (g x)) (ω x)
        rw [hLc]
        rfl
      rw [hdiff, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.norm_eq_abs]
      calc |L (f p x - g x) (ω x)| ≤ m * ‖f p x - g x‖ * covectorEuclideanNorm (ω x) :=
            hLbound _ _
        _ ≤ m * ‖f p x - g x‖ * C := by
            gcongr
            exact hCb x
        _ = m * C * ‖f p x - g x‖ := by ring
    have hlim : Tendsto (fun p => ENNReal.ofReal (m * C) * ∫⁻ x, ‖f p x - g x‖ₑ ∂H) atTop
        (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hgL1 (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun p => bot_le) hb
  rw [htau₀]
  simp_rw [htau]
  exact tendsto_integral_of_L1 _ hint₀'.aestronglyMeasurable (Eventually.of_forall hintp) hL1

/-- **Completeness of integer multiplicity currents (Simon Ch. 6, Lemma 3.13, p. 149).**  If
`T_j ∈ 𝒟ₖ(ℝ^N)` are integer multiplicity and `M(T − T_j) → 0`, then `T` is integer
multiplicity.  Write `T_j = τ(M_j, θ_j, ξ_j)` and `κ_j := 1_{M_j} θ_j ξ_j`.  Along a subsequence
with `M(T − T_{φ(p)}) < 2⁻ᵖ`, subadditivity of mass gives `M(T_{φ(p+1)} − T_{φ(p)}) ≤ 2 · 2⁻ᵖ`.
As `(Hᵏ, κ_{φ(p+1)} − κ_{φ(p)})` represents `T_{φ(p+1)} − T_{φ(p)}` (2.7), the mass lower bound
(printed (1)) makes `∑_p ∫ |κ_{φ(p+1)} − κ_{φ(p)}| dHᵏ` finite.  The densities then converge to an
integer multiplicity triple `(M₀, θ₀, ξ₀)` with `τ(M_{φ(p)}, θ_{φ(p)}, ξ_{φ(p)})(ω) →
τ(M₀, θ₀, ξ₀)(ω)` (printed (2)–(3)).  Finally `|T(ω) − T_j(ω)| ≤ c · M(T − T_j) → 0` whenever
`|ω| ≤ c`, so `T = τ(M₀, θ₀, ξ₀)`. -/
theorem Submission.deformation_im_completeness : ∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl N)) k), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ ε : ℝ≥0∞, 0 < ε → ∃ J : ℕ, ∀ j, J ≤ j → ∀ D : GeometricCurrentOn (univ : Set (Eucl N)) k, (∀ ω, D ω = T ω - Tj j ω) → D.mass < ε) → IsIntegerMultiplicity T := by
  intro N k T Tj hIM hconv
  -- Step 1: triples `T_j = τ(M_j, θ_j, ξ_j)` with natural multiplicity.
  choose M θ ξ hMθξ hnat hTj using hIM
  -- Step 2: the difference `A − B` of two currents is a current.
  let sub : GeometricCurrentOn (univ : Set (Eucl N)) k →
      GeometricCurrentOn (univ : Set (Eucl N)) k → GeometricCurrentOn (univ : Set (Eucl N)) k :=
    fun A B => ⟨A.toCurrent - B.toCurrent, fun ωs h => by
      simpa using (A.continuous' ωs h).sub (B.continuous' ωs h)⟩
  -- Step 3: `-ω` is admissible with `ω`, so mass is subadditive: if `D = E₁ − E₂`, then
  -- `D(ω) = E₁(ω) + E₂(−ω) ≤ M(E₁) + M(E₂)` for every admissible `ω`.
  have hneg : ∀ ω : TestFormOn (univ : Set (Eucl N)) k,
      ω ∈ massAdmissibleOn univ k univ → -ω ∈ massAdmissibleOn univ k univ := fun ω hω =>
    ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
  have hmass : ∀ D E₁ E₂ : GeometricCurrentOn (univ : Set (Eucl N)) k,
      (∀ ω, D ω = E₁ ω - E₂ ω) → D.mass ≤ E₁.mass + E₂.mass := by
    intro D E₁ E₂ hD
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    calc ENNReal.ofReal (D ω) = ENNReal.ofReal (E₁ ω + E₂ (-ω)) := by
          rw [hD, sub_eq_add_neg, map_neg E₂.toCurrent ω]
      _ ≤ ENNReal.ofReal (E₁ ω) + ENNReal.ofReal (E₂ (-ω)) := ENNReal.ofReal_add_le
      _ ≤ E₁.mass + E₂.mass := add_le_add (E₁.le_massOn hω) (E₂.le_massOn (hneg ω hω))
  -- Step 4: a subsequence with `M(T − T_{φ(p)}) < 2⁻ᵖ` (Simon's proof of 3.13); then
  -- `T_{φ(p+1)} − T_{φ(p)} = (T − T_{φ(p)}) − (T − T_{φ(p+1)})` has mass `≤ 2 · 2⁻ᵖ`.
  obtain ⟨φ, hφ, hφm⟩ := extraction_forall_of_eventually fun p : ℕ =>
    (show ∀ᶠ j in atTop, ∀ D : GeometricCurrentOn (univ : Set (Eucl N)) k,
        (∀ ω, D ω = T ω - Tj j ω) → D.mass < (2⁻¹ : ℝ≥0∞) ^ p from
      eventually_atTop.2 (hconv _ (ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) p)))
  have hD : ∀ p, (sub (Tj (φ (p + 1))) (Tj (φ p))).mass ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ p := by
    intro p
    calc (sub (Tj (φ (p + 1))) (Tj (φ p))).mass
        ≤ (sub T (Tj (φ p))).mass + (sub T (Tj (φ (p + 1)))).mass :=
          hmass _ _ _ fun ω => by
            change Tj (φ (p + 1)) ω - Tj (φ p) ω = (T ω - Tj (φ p) ω) - (T ω - Tj (φ (p + 1)) ω)
            ring
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ p + (2⁻¹ : ℝ≥0∞) ^ p :=
          add_le_add (hφm p (sub T (Tj (φ p))) fun _ => rfl).le
            ((hφm (p + 1) (sub T (Tj (φ (p + 1)))) fun _ => rfl).le.trans
              (pow_le_pow_right_of_le_one' (by norm_num) p.le_succ))
      _ = 2 * (2⁻¹ : ℝ≥0∞) ^ p := (two_mul _).symm
  -- Step 5: `T_j(ω) = ∫ κ_j(ω) dHᵏ` with an integrable integrand (`ltg_tau_integrable` (b)).
  have hrep : ∀ j (ω : TestFormOn (univ : Set (Eucl N)) k),
      Integrable (fun x => (M j).indicator (fun y => θ j y • ξ j y) x
        ((ω : DifferentialForm (Eucl N) k) x)) (μHE[k] : Measure (Eucl N)) ∧
      Tj j ω = ∫ x, (M j).indicator (fun y => θ j y • ξ j y) x
        ((ω : DifferentialForm (Eucl N) k) x) ∂(μHE[k] : Measure (Eucl N)) := by
    intro j ω
    have hκ : (fun x => (M j).indicator (fun y => θ j y • ξ j y) x
        ((ω : DifferentialForm (Eucl N) k) x)) =
        (M j).indicator (fun x => θ j x * ξ j x ((ω : DifferentialForm (Eucl N) k) x)) := by
      funext x
      by_cases hx : x ∈ M j <;> simp [hx]
    rw [hκ, integral_indicator₀ (hMθξ j).nullMeasurableSet, hTj j ω]
    exact ⟨((Submission.ltg_tau_integrable N k univ (M j) (θ j) (ξ j) (hMθξ j)).2 _
      (ContDiff.continuous ω.2.1.1) ω.2.1.2 (subset_univ _)).integrable_indicator₀
        (hMθξ j).nullMeasurableSet, rfl⟩
  -- Step 6: hence `(Hᵏ, κ_{φ(p+1)} − κ_{φ(p)})` represents `T_{φ(p+1)} − T_{φ(p)}` (2.7).
  have hrepD : ∀ p, IsMeasureRepresentation (sub (Tj (φ (p + 1))) (Tj (φ p)))
      (μHE[k] : Measure (Eucl N)) fun x =>
        (M (φ (p + 1))).indicator (fun y => θ (φ (p + 1)) y • ξ (φ (p + 1)) y) x -
          (M (φ p)).indicator (fun y => θ (φ p) y • ξ (φ p) y) x := by
    intro p ω
    obtain ⟨h₁, e₁⟩ := hrep (φ (p + 1)) ω
    obtain ⟨h₂, e₂⟩ := hrep (φ p) ω
    exact ⟨h₁.sub h₂, (congrArg₂ (· - ·) e₁ e₂).trans (integral_sub h₁ h₂).symm⟩
  -- Step 7: the mass lower bound (printed (1)) gives
  -- `∑_p ∫ |κ_{φ(p+1)} − κ_{φ(p)}| dHᵏ ≤ ∑_p 2 · 2⁻ᵖ = 4`.
  have hsum : (∑' p, ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N,
      (euclideanNVectorCoordinate ((M (φ (p + 1))).indicator
        (fun y => θ (φ (p + 1)) y • ξ (φ (p + 1)) y) x -
          (M (φ p)).indicator (fun y => θ (φ p) y • ξ (φ p) y) x) γ) ^ 2))
      ∂(μHE[k] : Measure (Eucl N))) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun p =>
      (Submission.imc_lintegral_coordNorm_le_mass N k _ _ _ (hrepD p)).trans (hD p))
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    norm_num
  -- Step 8: the densities converge to an integer multiplicity triple `(M₀, θ₀, ξ₀)` with
  -- `τ(M_{φ(p)}, θ_{φ(p)}, ξ_{φ(p)})(ω) → τ(M₀, θ₀, ξ₀)(ω)` (printed (2)–(3)).
  obtain ⟨M₀, θ₀, ξ₀, hT₀, hnat₀, hlim⟩ := Submission.imc_im_density_limit N k
    (fun p => M (φ p)) (fun p => θ (φ p)) (fun p => ξ (φ p)) (fun p => hMθξ (φ p))
    (fun p => hnat (φ p)) hsum
  -- Step 9: `T_j(ω) → T(ω)`: if `|ω| ≤ c`, then `±c⁻¹ω` are admissible, so
  -- `|T(ω) − T_j(ω)| ≤ c · M(T − T_j)`.  Here `|aα| = |a| |α|` for the coefficient norm.
  have hsmul : ∀ (a : ℝ) (α : Covector (Eucl N) k),
      covectorEuclideanNorm (a • α) = |a| * covectorEuclideanNorm α := by
    intro a α
    simp only [covectorEuclideanNorm]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hweak : ∀ ω : TestFormOn (univ : Set (Eucl N)) k,
      Tendsto (fun j => Tj j ω) atTop (𝓝 (T ω)) := by
    intro ω
    -- `|ω|` is continuous with compact support, hence bounded by `c := max C 1`.
    have hcont : Continuous fun x =>
        covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) k) x) := by
      simp only [covectorEuclideanNorm]
      refine (continuous_finsetSum _ fun I _ => ?_).sqrt
      by_cases hI : StrictMono I <;> simp only [hI, ↓reduceIte]
      · exact ((continuous_eval_const _).comp (ContDiff.continuous ω.2.1.1)).pow 2
      · exact continuous_const
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
      (ω.2.1.2.mono fun x hx h0 => hx (by simp [h0]))
    have hc : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
    have hadm : (max C 1)⁻¹ • ω ∈ massAdmissibleOn univ k univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      change covectorEuclideanNorm ((max C 1)⁻¹ • (ω : DifferentialForm (Eucl N) k) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.2 hc), inv_mul_le_one₀ hc]
      exact (Real.le_norm_self _).trans ((hC x).trans (le_max_left C 1))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J, hJ⟩ := hconv (ENNReal.ofReal ((max C 1)⁻¹ * ε))
      (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hc) hε))
    refine ⟨J, fun j hj => ?_⟩
    have hm := hJ j hj (sub T (Tj j)) fun _ => rfl
    have h₁ := ((sub T (Tj j)).le_massOn hadm).trans_lt hm
    have h₂ := ((sub T (Tj j)).le_massOn (hneg _ hadm)).trans_lt hm
    rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos (inv_pos.2 hc) hε)] at h₁ h₂
    change T ((max C 1)⁻¹ • ω) - Tj j ((max C 1)⁻¹ • ω) < _ at h₁
    change T (-((max C 1)⁻¹ • ω)) - Tj j (-((max C 1)⁻¹ • ω)) < _ at h₂
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub] at h₁
    rw [map_neg T.toCurrent, map_neg (Tj j).toCurrent, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul, neg_sub_neg, ← mul_sub] at h₂
    rw [Real.dist_eq, abs_sub_lt_iff]
    exact ⟨lt_of_mul_lt_mul_left h₂ (inv_nonneg.2 hc.le),
      lt_of_mul_lt_mul_left h₁ (inv_nonneg.2 hc.le)⟩
  -- Step 10: `T(ω) = lim_p T_{φ(p)}(ω) = lim_p τ(M_{φ(p)}, θ_{φ(p)}, ξ_{φ(p)})(ω) =
  -- τ(M₀, θ₀, ξ₀)(ω)`, so `T = τ(M₀, θ₀, ξ₀)` is integer multiplicity.
  refine ⟨M₀, θ₀, ξ₀, hT₀, hnat₀, fun ω => tendsto_nhds_unique
    ((hweak ω).comp hφ.tendsto_atTop) ?_⟩
  exact (hlim _ (ContDiff.continuous ω.2.1.1) ω.2.1.2).congr fun p => (hTj (φ p) ω).symm

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

/-- **Choice of a good centre** (Simon Ch. 6, proof of the Deformation Theorem 5.1, printed
(1)–(7)).  Let `d = m + 1 + ℓ`, `𝒥` the `N` index sets `J ⊆ {1, …, d}` with `|J| = m + 2`,
`q = (1/2, …, 1/2)`, `V = L^d(B_{1/4}(q)) ∈ (0, ∞)` and `β = (2 N 10^{m+2} + 1) / V`, so that
`2 N 10^{m+2} / β < V`; the constant is `c = N β`.  For `J ∈ 𝒥`, `p_J x = (x_i)_{i ∈ J}` and a
finite measure `μ`, `Bad J μ` is the set of centres `g` with `|g - p_J q| < 1/4` such that some
`σ ∈ (0, 1/4)` has `μ(T_J(g, σ)) > β σ^{m+2} μ(ℝ^d)`, where
`T_J(g, σ) = {x : |p_J x - g - z| < σ for some z ∈ ℤ^J}`.  By `dgc_cylinder_volume` and
`dgc_periodic_maximal`, `A J μ = {a ∈ [0,1]^d : p_J a ∈ Bad J μ}` has `L^d(A J μ) ≤ 10^{m+2} / β`,
so the `2N` sets `A J μᵢ` miss a point `a` of `B_{1/4}(q) ⊆ [0,1]^d`.  Then
`Σᵢ (aᵢ - 1/2)² < 1/16` and `|p_J a - p_J q| < 1/4`, hence `μᵢ(T_J(p_J a, σ)) ≤ β σ^{m+2} μᵢ(ℝ^d)`
for every `J ∈ 𝒥` and `σ ∈ (0, 1/4)`.  By `dgc_tube_cover`,
`{dist(·, La) < σ} ⊆ ⋃_{J ∈ 𝒥} T_J(p_J a, σ)`, and summing over the `N` sets `J` gives
`μᵢ{dist(·, La) < σ} ≤ N β σ^{m+2} μᵢ(ℝ^d)`. -/
theorem Submission.deformation_good_center : ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ μ₁ μ₂ : Measure (Eucl (m + 1 + ℓ)), IsFiniteMeasure μ₁ → IsFiniteMeasure μ₂ → ∃ a : Eucl (m + 1 + ℓ), ∑ i, (a i - 1 / 2) ^ 2 < 1 / 16 ∧ ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∀ σ : ℝ, 0 < σ → σ < 1 / 4 → μ₁ {x | infDist x La < σ} ≤ c * ENNReal.ofReal (σ ^ (m + 2)) * μ₁ univ ∧ μ₂ {x | infDist x La < σ} ≤ c * ENNReal.ofReal (σ ^ (m + 2)) * μ₂ univ := by
  intro m ℓ hℓ
  have hkd : m + 2 ≤ m + 1 + ℓ := by omega
  generalize m + 1 + ℓ = d at hkd ⊢
  -- `𝒥`: the `N` coordinate sets `J ⊆ {1, …, d}` with `|J| = m + 2`.
  set 𝒥 : Finset (Finset (Fin d)) := Finset.univ.filter (fun J => J.card = m + 2)
  set N : ℕ := 𝒥.card
  -- `q = (1/2, …, 1/2)` and `V = L^d(B_{1/4}(q)) ∈ (0, ∞)`.
  set q : Eucl d := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  have hball_pos : 0 < volume (ball q (1 / 4 : ℝ)) := measure_ball_pos _ _ (by norm_num)
  have hball_lt : volume (ball q (1 / 4 : ℝ)) < ∞ := measure_ball_lt_top
  set V : ℝ := (volume (ball q (1 / 4 : ℝ))).toReal
  have hV : 0 < V := ENNReal.toReal_pos hball_pos.ne' hball_lt.ne
  have hVball : ENNReal.ofReal V = volume (ball q (1 / 4 : ℝ)) := ENNReal.ofReal_toReal hball_lt.ne
  -- `β = (2 N 10^{m+2} + 1) / V`, so that `2 N 10^{m+2} / β < V`.
  set β : ℝ := (2 * N * 10 ^ (m + 2) + 1) / V with hβ_def
  have hβ : 0 < β := by positivity
  have hβV : 2 * N * (10 ^ (m + 2) / β) < V := by
    rw [hβ_def, div_div_eq_mul_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨Real.toNNReal (N * β), ?_⟩
  intro μ₁ μ₂ h₁ h₂
  -- `p_J x = (x_i)_{i ∈ J}`; the bad set `Bad J μ` of centres `g` near `p_J q` and the set
  -- `A J μ` of `a ∈ [0,1]^d` with `p_J a ∈ Bad J μ`.
  let Bad : ∀ J : Finset (Fin d), Measure (Eucl d) → Set (EuclideanSpace ℝ J) := fun J μ =>
    {g : EuclideanSpace ℝ J | dist g (WithLp.toLp 2 (fun i : J => q i)) < 1 / 4 ∧
      ∃ σ : ℝ, 0 < σ ∧ σ < 1 / 4 ∧ ENNReal.ofReal (β * σ ^ Fintype.card J) * μ univ <
        μ {x | ∃ z : J → ℤ, ∑ i, ((WithLp.toLp 2 (fun i : J => x i) : EuclideanSpace ℝ J) i -
          g i - z i) ^ 2 < σ ^ 2}}
  let A : Finset (Fin d) → Measure (Eucl d) → Set (Eucl d) := fun J μ =>
    {a : Eucl d | (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧ WithLp.toLp 2 (fun i : J => a i) ∈ Bad J μ}
  -- Cylinder bound followed by the maximal estimate: `L^d(A J μ) ≤ 10^{m+2} / β`.
  have hA : ∀ J ∈ 𝒥, ∀ μ : Measure (Eucl d), IsFiniteMeasure μ →
      volume (A J μ) ≤ ENNReal.ofReal (10 ^ (m + 2) / β) := by
    intro J hJ μ hμ
    have hJc : J.card = m + 2 := (Finset.mem_filter.mp hJ).2
    have hp : Measurable
        (fun x : Eucl d => (WithLp.toLp 2 (fun i : J => x i) : EuclideanSpace ℝ J)) :=
      Continuous.measurable (by fun_prop)
    have h1 := Submission.dgc_cylinder_volume (Fin d) J (Bad J μ)
    have h2 := Submission.dgc_periodic_maximal J (Eucl d) μ hμ
      (fun x : Eucl d => (WithLp.toLp 2 (fun i : J => x i) : EuclideanSpace ℝ J)) hp
      (WithLp.toLp 2 (fun i : J => q i)) β hβ
    have h3 : ENNReal.ofReal (10 ^ Fintype.card J / β) = ENNReal.ofReal (10 ^ (m + 2) / β) := by
      rw [Fintype.card_coe, hJc]
    exact h1.trans (h2.trans_eq h3)
  -- The union of the `2N` sets `A J μᵢ` has measure `< L^d(B_{1/4}(q))`.
  have hU : volume (⋃ J ∈ 𝒥, (A J μ₁ ∪ A J μ₂)) < volume (ball q (1 / 4 : ℝ)) := by
    calc volume (⋃ J ∈ 𝒥, (A J μ₁ ∪ A J μ₂))
        ≤ ∑ J ∈ 𝒥, volume (A J μ₁ ∪ A J μ₂) := measure_biUnion_finset_le _ _
      _ ≤ ∑ J ∈ 𝒥, (ENNReal.ofReal (10 ^ (m + 2) / β) + ENNReal.ofReal (10 ^ (m + 2) / β)) :=
          Finset.sum_le_sum fun J hJ =>
            (measure_union_le _ _).trans (add_le_add (hA J hJ μ₁ h₁) (hA J hJ μ₂ h₂))
      _ = ENNReal.ofReal (2 * N * (10 ^ (m + 2) / β)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal V := (ENNReal.ofReal_lt_ofReal_iff hV).mpr hβV
      _ = volume (ball q (1 / 4 : ℝ)) := hVball
  -- Hence some `a ∈ B_{1/4}(q)` lies in no `A J μᵢ`.
  obtain ⟨a, haball, haA⟩ : ∃ a ∈ ball q (1 / 4 : ℝ), a ∉ ⋃ J ∈ 𝒥, (A J μ₁ ∪ A J μ₂) := by
    by_contra h
    push Not at h
    exact absurd (measure_mono (μ := volume) h) (not_le.mpr hU)
  have hdist : dist a q < 1 / 4 := mem_ball.mp haball
  have hqi : ∀ i, q i = 1 / 2 := fun i => rfl
  -- `a ∈ [0,1]^d`, since `|a_i - 1/2| ≤ |a - q| < 1/4`.
  have hcube : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := by
    intro i
    have h := (PiLp.dist_apply_le a q i).trans_lt hdist
    rw [Real.dist_eq, hqi] at h
    have h' := abs_lt.mp h
    constructor <;> linarith [h'.1, h'.2]
  -- `|p_J a - p_J q| ≤ |a - q| < 1/4`.
  have hdistJ : ∀ J : Finset (Fin d), dist (WithLp.toLp 2 (fun i : J => a i) : EuclideanSpace ℝ J)
      (WithLp.toLp 2 (fun i : J => q i)) < 1 / 4 := by
    intro J
    refine lt_of_le_of_lt ?_ hdist
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    apply Real.sqrt_le_sqrt
    rw [Finset.sum_coe_sort J (fun i => dist (a i) (q i) ^ 2)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg _)
  -- Good centres: `p_J a ∉ Bad J μ` gives the tube estimate for every `σ ∈ (0, 1/4)`.
  have hgood : ∀ J ∈ 𝒥, ∀ μ : Measure (Eucl d), a ∉ A J μ → ∀ σ : ℝ, 0 < σ → σ < 1 / 4 →
      μ {x | ∃ z : J → ℤ, ∑ i : J, (x i - a i - z i) ^ 2 < σ ^ 2} ≤
        ENNReal.ofReal (β * σ ^ (m + 2)) * μ univ := by
    intro J hJ μ haJ σ hσ hσ'
    have hJc : J.card = m + 2 := (Finset.mem_filter.mp hJ).2
    by_contra hlt
    push Not at hlt
    apply haJ
    refine ⟨hcube, hdistJ J, σ, hσ, hσ', ?_⟩
    rw [Fintype.card_coe, hJc]
    exact hlt
  have hnot : ∀ J ∈ 𝒥, a ∉ A J μ₁ ∧ a ∉ A J μ₂ := fun J hJ =>
    ⟨fun h => haA (mem_iUnion₂.mpr ⟨J, hJ, Or.inl h⟩),
      fun h => haA (mem_iUnion₂.mpr ⟨J, hJ, Or.inr h⟩)⟩
  -- Tube cover and summation over the `N` sets `J`.
  have hfinal : ∀ μ : Measure (Eucl d), (∀ J ∈ 𝒥, a ∉ A J μ) →
      ∀ La : Set (Eucl d), La = {y | ∃ J : Finset (Fin d), J.card = m + 2 ∧
        ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∀ σ : ℝ, 0 < σ → σ < 1 / 4 →
      μ {x | infDist x La < σ} ≤
        (Real.toNNReal (N * β) : ℝ≥0∞) * ENNReal.ofReal (σ ^ (m + 2)) * μ univ := by
    intro μ hμa La hLa σ hσ hσ'
    have hsub : {x | infDist x La < σ} ⊆
        ⋃ J ∈ 𝒥, {x : Eucl d | ∃ z : J → ℤ, ∑ i : J, (x i - a i - z i) ^ 2 < σ ^ 2} := by
      intro x hx
      obtain ⟨J, hJ, z, hz⟩ := Submission.dgc_tube_cover d (m + 2) hkd a La hLa σ x hx
      exact mem_iUnion₂.mpr ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩, z, hz⟩
    calc μ {x | infDist x La < σ}
        ≤ μ (⋃ J ∈ 𝒥, {x : Eucl d | ∃ z : J → ℤ, ∑ i : J, (x i - a i - z i) ^ 2 < σ ^ 2}) :=
          measure_mono hsub
      _ ≤ ∑ J ∈ 𝒥, μ {x : Eucl d | ∃ z : J → ℤ, ∑ i : J, (x i - a i - z i) ^ 2 < σ ^ 2} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ J ∈ 𝒥, ENNReal.ofReal (β * σ ^ (m + 2)) * μ univ :=
          Finset.sum_le_sum fun J hJ => hgood J hJ μ (hμa J hJ) σ hσ hσ'
      _ = (Real.toNNReal (N * β) : ℝ≥0∞) * ENNReal.ofReal (σ ^ (m + 2)) * μ univ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          change (N : ℝ≥0∞) * _ = ENNReal.ofReal (N * β) * _ * _
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
          ring
  -- Conclusion.
  have hsum : ∑ i, (a i - 1 / 2) ^ 2 < 1 / 16 := by
    have h := hdist
    rw [EuclideanSpace.dist_eq, Real.sqrt_lt' (by norm_num)] at h
    simp only [Real.dist_eq, sq_abs, hqi] at h
    norm_num at h ⊢
    exact h
  exact ⟨a, hsum, fun La hLa σ hσ hσ' =>
    ⟨hfinal μ₁ (fun J hJ => (hnot J hJ).1) La hLa σ hσ hσ',
      hfinal μ₂ (fun J hJ => (hnot J hJ).2) La hLa σ hσ hσ'⟩⟩

end GMT.Ch06
