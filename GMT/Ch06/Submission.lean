import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral

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

/-- The case `n = 0` of Simon Ch. 6, 8.2 (p. 176, "trivial in case `n = 0`"), on a set `W` with
`closure W` compact (used for 6.3): let `X_j ⇀ X` and, on test forms supported in `W`, let
`X_j(ω) = ∑ᶠ_{x ∈ N_j} c_j(x) ω(x)` with integers `c_j ≠ 0` on `N_j`, `N_j ∩ W` finite and
`∑_{x ∈ N_j ∩ W} |c_j(x)| ≤ Λ`.  Then on such forms `X(ω) = ∑_{x ∈ D} a(x) ω(x)` for a finite
`D ⊆ W` and integers `a`.  Each `N_j ∩ W` has at most `Q = ⌊Λ⌋₊` points, with `|c_j| ≤ ⌊Λ⌋`;
padding with `0`-weighted copies of `0` gives configurations of length `Q` in a compact set, a
subsequence converges, limit points outside `W` contribute `0` and equal ones are grouped. -/
theorem Submission.br_zd_dirac_local_limit : ∀ (P : ℕ) (U W : Set (Eucl P)) (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0) (N : ℕ → Set (Eucl P)) (c : ℕ → Eucl P → ℤ) (Λ : ℝ), IsCompact (closure W) → WeaklyConvergesOn Xj X → (∀ j, ∀ x ∈ N j, c j x ≠ 0) → (∀ j, (N j ∩ W).Finite) → (∀ j (S : Finset (Eucl P)), (↑S : Set (Eucl P)) ⊆ N j ∩ W → ∑ x ∈ S, |(c j x : ℝ)| ≤ Λ) → (∀ j (ω : TestFormOn U 0), tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W → Xj j ω = ∑ᶠ x ∈ N j, (c j x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) → ∃ (D : Finset (Eucl P)) (a : Eucl P → ℤ), (↑D : Set (Eucl P)) ⊆ W ∧ ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W → X ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  intro P U W Xj X N c Λ hW hconv hc hfin hbound hrepr
  classical
  -- `ω°(x) = ω(x)(![])` is continuous and vanishes off `tsupport ω`.
  have hcont : ∀ ω : TestFormOn U 0,
      Continuous fun x => (ω : DifferentialForm (Eucl P) 0) x ![] := fun ω =>
    ω.property.1.1.continuous.eval_const _
  have hvan : ∀ (ω : TestFormOn U 0) (x : Eucl P),
      x ∉ tsupport (ω : DifferentialForm (Eucl P) 0) →
        (ω : DifferentialForm (Eucl P) 0) x ![] = 0 := fun ω x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  -- Step 1: on forms supported in `W`, `X_j(ω) = ∑_{x ∈ A_j} c_j(x) ω°(x)`, `A_j = N_j ∩ W`.
  let A : ℕ → Finset (Eucl P) := fun j => (hfin j).toFinset
  have hA : ∀ j x, x ∈ A j ↔ x ∈ N j ∧ x ∈ W := fun j x => by simp [A]
  have hXj : ∀ j (ω : TestFormOn U 0), tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W →
      Xj j ω = ∑ x ∈ A j, (c j x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
    intro j ω hω
    rw [hrepr j ω hω]
    refine finsum_mem_eq_sum_of_subset _ ?_ fun x hx => ((hA j x).1 hx).1
    rintro x ⟨hxN, hx0⟩
    refine (hA j x).2 ⟨hxN, by_contra fun hxW => hx0 ?_⟩
    simp [hvan ω x fun h => hxW (hω h)]
  -- Step 2: `#A_j ≤ Q = ⌊Λ⌋₊` (as `|c_j| ≥ 1` on `N_j`) and `|c_j| ≤ m = ⌊Λ⌋` on `A_j`.
  have hΛ : 0 ≤ Λ := by simpa using hbound 0 ∅ (by simp)
  obtain ⟨Q, hcard⟩ : ∃ Q : ℕ, ∀ j, (A j).card ≤ Q := by
    refine ⟨⌊Λ⌋₊, fun j => Nat.le_floor ?_⟩
    calc ((A j).card : ℝ) = ∑ x ∈ A j, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ A j, |(c j x : ℝ)| := Finset.sum_le_sum fun x hx => by
          exact_mod_cast Int.one_le_abs (hc j x ((hA j x).1 hx).1)
      _ ≤ Λ := hbound j (A j) fun x hx => (hA j x).1 hx
  obtain ⟨m, hm, hcoef⟩ : ∃ m : ℤ, 0 ≤ m ∧ ∀ j, ∀ x ∈ A j, |c j x| ≤ m := by
    refine ⟨⌊Λ⌋, Int.floor_nonneg.2 hΛ, fun j x hx => Int.le_floor.2 ?_⟩
    simpa using hbound j {x} (by simpa using (hA j x).1 hx)
  -- Step 3: pad each configuration to length `Q` by points `0` with coefficient `0`.
  have pad : ∀ (n : ℕ) (B : Finset (Eucl P)), B.card ≤ n → ∀ d : Eucl P → ℤ,
      ∃ (p : Fin n → Eucl P) (b : Fin n → ℤ), (∀ ℓ, p ℓ ∈ B ∨ p ℓ = 0) ∧
        (∀ ℓ, b ℓ = 0 ∨ ∃ x ∈ B, b ℓ = d x) ∧
        ∀ g : Eucl P → ℝ, ∑ x ∈ B, (d x : ℝ) * g x = ∑ ℓ, (b ℓ : ℝ) * g (p ℓ) := by
    intro n
    induction n with
    | zero =>
      intro B hB d
      obtain rfl : B = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hB)
      exact ⟨Fin.elim0, Fin.elim0, fun ℓ => ℓ.elim0, fun ℓ => ℓ.elim0, fun g => by simp⟩
    | succ n ih =>
      intro B hB d
      rcases B.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact ⟨fun _ => 0, fun _ => 0, fun _ => Or.inr rfl, fun _ => Or.inl rfl, fun g => by simp⟩
      obtain ⟨p, b, hp, hb, hpb⟩ :=
        ih (B.erase x) (by rw [Finset.card_erase_of_mem hx]; omega) d
      refine ⟨Fin.cons x p, Fin.cons (d x) b, fun ℓ => ?_, fun ℓ => ?_, fun g => ?_⟩
      · refine Fin.cases (by simp [hx]) (fun i => ?_) ℓ
        simpa using (hp i).imp_left Finset.mem_of_mem_erase
      · refine Fin.cases (Or.inr ⟨x, hx, by simp⟩) (fun i => ?_) ℓ
        simpa using (hb i).imp_right fun ⟨z, hz, h⟩ => ⟨z, Finset.mem_of_mem_erase hz, h⟩
      · rw [← Finset.add_sum_erase B _ hx, hpb g, Fin.sum_univ_succ]
        simp
  choose p b hp hb hpb using fun j => pad Q (A j) (hcard j) (c j)
  -- Step 4: `(p_j, b_j) ∈ (closure W ∪ {0})^Q × [-m, m]^Q`, which is compact; extract a
  -- subsequence `ψ` with `(p_{ψ i}, b_{ψ i}) → (y, β)`.
  have hK : IsCompact ((Set.univ.pi fun _ : Fin Q => closure W ∪ {0}) ×ˢ
      (Set.univ.pi fun _ : Fin Q => Set.Icc (-m) m)) :=
    (isCompact_univ_pi fun _ => hW.union isCompact_singleton).prod
      (isCompact_univ_pi fun _ => (Set.finite_Icc _ _).isCompact)
  have hmem : ∀ j, (p j, b j) ∈ (Set.univ.pi fun _ : Fin Q => closure W ∪ {0}) ×ˢ
      (Set.univ.pi fun _ : Fin Q => Set.Icc (-m) m) := by
    refine fun j => ⟨fun ℓ _ => ?_, fun ℓ _ => ?_⟩
    · exact (hp j ℓ).imp (fun h => subset_closure ((hA j _).1 h).2) id
    · show b j ℓ ∈ Set.Icc (-m) m
      rcases hb j ℓ with h | ⟨x, hx, h⟩
      · rw [h]
        exact ⟨neg_nonpos.2 hm, hm⟩
      · rw [h]
        exact abs_le.1 (hcoef j x hx)
  obtain ⟨⟨y, β⟩, -, ψ, hψ, hlim⟩ := hK.tendsto_subseq hmem
  -- Step 5: `X(ω) = ∑_ℓ β_ℓ ω°(y_ℓ)` by continuity of `(p, b) ↦ ∑_ℓ b_ℓ ω°(p_ℓ)`.
  have hX : ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Eucl P) 0) ⊆ W →
      X ω = ∑ ℓ, (β ℓ : ℝ) * (ω : DifferentialForm (Eucl P) 0) (y ℓ) ![] := by
    intro ω hω
    have hΦ : Continuous fun q : (Fin Q → Eucl P) × (Fin Q → ℤ) =>
        ∑ ℓ, (q.2 ℓ : ℝ) * (ω : DifferentialForm (Eucl P) 0) (q.1 ℓ) ![] :=
      continuous_finsetSum _ fun ℓ _ =>
        ((continuous_of_discreteTopology (f := fun z : ℤ => (z : ℝ))).comp
          ((continuous_apply ℓ).comp continuous_snd)).mul
          ((hcont ω).comp ((continuous_apply ℓ).comp continuous_fst))
    refine tendsto_nhds_unique ((hconv ω).comp hψ.tendsto_atTop) ?_
    refine ((hΦ.tendsto (y, β)).comp hlim).congr fun i => ?_
    simp only [Function.comp_apply]
    rw [hXj (ψ i) ω hω, hpb (ψ i)]
  -- Steps 6–7: limit points outside `W` contribute `0`; group the others by position.
  let s : Finset (Fin Q) := Finset.univ.filter fun ℓ => y ℓ ∈ W
  refine ⟨s.image y, fun z => ∑ ℓ ∈ s.filter fun ℓ => y ℓ = z, β ℓ, ?_, fun ω hω => ?_⟩
  · intro z hz
    rw [Finset.coe_image] at hz
    obtain ⟨ℓ, hℓ, rfl⟩ := hz
    simpa [s] using hℓ
  · rw [hX ω hω, ← Finset.sum_subset (Finset.subset_univ s) fun ℓ _ hℓ => ?_,
      ← Finset.sum_fiberwise_of_maps_to fun ℓ hℓ => Finset.mem_image_of_mem y hℓ]
    · refine Finset.sum_congr rfl fun z _ => ?_
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ℓ hℓ => by rw [(Finset.mem_filter.1 hℓ).2]
    · have hyW : y ℓ ∉ W := by simpa [s] using hℓ
      rw [hvan ω (y ℓ) fun h => hyW (hω h), mul_zero]
/-- Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): a finite
integer combination of point masses `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`, `D ⊆ U`, is the integer
multiplicity current `τ(M, θ, ξ)` with `M = {x ∈ D : a(x) ≠ 0}`, `θ = |a|` and `ξ = ±1` the sign
of `a`.  `Y` is continuous since convergence of test forms gives pointwise convergence.  `M` is
finite, so it is `H⁰`-measurable and countably `0`-rectifiable and `H⁰`-integrals over it are
finite sums; at `x ∈ M`, for small `r` the blow-up `η_{x,r}(M)` meets the support of a given
`f ∈ C_c` only in `0`, so the weighted tangent space is `{0}`, spanned by the empty frame. -/
theorem Submission.br_zd_finite_dirac_im :
    ∀ (P : ℕ) (U : Set (Eucl P)) (D : Finset (Eucl P)) (a : Eucl P → ℤ),
      (↑D : Set (Eucl P)) ⊆ U → ∃ Y : GeometricCurrentOn U 0, IsIntegerMultiplicity Y ∧
        ∀ ω : TestFormOn U 0,
          Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  classical
  intro P U D a hDU
  -- `H⁰{x} = 1`, so `H⁰`-integrals over finite sets are finite sums.
  have hpt : ∀ x : Eucl P, (μHE[0] : Measure (Eucl P)) {x} = 1 := fun x => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      IntegrableOn g (F : Set (Eucl P)) (μHE[0] : Measure (Eucl P)) := by
    intro F g
    rw [← biUnion_of_singleton (F : Set (Eucl P)), Finset.set_biUnion_coe,
      integrableOn_finset_iUnion]
    exact fun x _ => integrableOn_singleton (hx := by rw [hpt]; exact ENNReal.one_lt_top)
  have hsum : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
      ∫ x in (F : Set (Eucl P)), g x ∂(μHE[0] : Measure (Eucl P)) = ∑ x ∈ F, g x := by
    intro F g
    rw [setIntegral_finset F (hint F g)]
    simp only [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
  -- The current `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`: if `ω_j → 0`, then `ω_j(x) → 0` for every `x`
  -- (uniformly on the common compact support `K`, and `ω_j(x) = 0` off `K`).
  let L : TestFormOn U 0 →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]
      map_add' := fun ω η => by simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun t ω => by simp [Finset.mul_sum, mul_left_comm] }
  have hcont : ∀ ωs : ℕ → TestFormOn U 0, TestFormOnConverges ωs 0 →
      Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    rintro ωs ⟨K, -, -, hsupp, -, hconv⟩
    have hx : ∀ x, Tendsto (fun j => (ωs j : DifferentialForm (Eucl P) 0) x ![]) atTop (𝓝 0) := by
      intro x
      by_cases hxK : x ∈ K
      · have hev : Continuous fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Eucl P)
            (Covector (Eucl P) 0) => T ![] ![] := by fun_prop
        simpa [Function.comp_def] using (hev.tendsto _).comp ((hconv 0).tendsto_at hxK)
      · have h0 : ∀ j, (ωs j : DifferentialForm (Eucl P) 0) x = 0 := fun j =>
          image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp j h)
        simp [h0]
    simpa [L] using tendsto_finsetSum D fun x _ => (hx x).const_mul (a x : ℝ)
  obtain ⟨Y, hY⟩ : ∃ Y : GeometricCurrentOn U 0, ∀ ω : TestFormOn U 0,
      Y ω = ∑ x ∈ D, (a x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] :=
    ⟨⟨L, hcont⟩, fun ω => rfl⟩
  refine ⟨Y, ?_, hY⟩
  -- The triple: `M = {a ≠ 0}`, `θ = |a|`, `ξ = -ε` on `N = {a < 0}` and `ξ = ε` elsewhere, where
  -- `⟨α, ε⟩ = α(![])`; then `θ(x) ⟨α, ξ(x)⟩ = a(x) α(![])` on `M`.
  set M : Finset (Eucl P) := D.filter (fun x => a x ≠ 0) with hM
  set N : Finset (Eucl P) := D.filter (fun x => a x < 0) with hN
  let ε : NVector (Eucl P) 0 := simpleNVector ![]
  let θ : Eucl P → ℝ := fun x => |(a x : ℝ)|
  let ξ : Eucl P → NVector (Eucl P) 0 := fun x => if x ∈ N then -ε else ε
  have hMmeas : MeasurableSet (M : Set (Eucl P)) := M.finite_toSet.measurableSet
  have hterm : ∀ x ∈ M, ∀ α : Covector (Eucl P) 0, θ x * ξ x α = (a x : ℝ) * α ![] := by
    intro x hx α
    have hxD : x ∈ D := (Finset.mem_filter.1 hx).1
    by_cases hneg : a x < 0
    · have hxN : x ∈ N := Finset.mem_filter.2 ⟨hxD, hneg⟩
      have ha : (a x : ℝ) < 0 := by exact_mod_cast hneg
      simp only [θ, ξ, ε, hxN, ↓reduceIte, neg_apply, simpleNVector_apply,
        abs_of_neg ha]
      ring
    · have hxN : x ∉ N := fun h => hneg (Finset.mem_filter.1 h).2
      have ha : (0 : ℝ) ≤ a x := by exact_mod_cast not_lt.1 hneg
      simp only [θ, ξ, ε, hxN, ↓reduceIte, simpleNVector_apply, abs_of_nonneg ha]
  refine ⟨M, θ, ξ,
    { subset := fun x hx => hDU (Finset.mem_filter.1 hx).1
      nullMeasurableSet := hMmeas.nullMeasurableSet
      countablyRectifiable := ?_
      pos := fun x hx => abs_pos.2 (Int.cast_ne_zero.2 (Finset.mem_filter.1 hx).2)
      integrableOn := fun K _ _ => (hint M θ).mono_set inter_subset_left
      aestronglyMeasurable := ?_
      orients := ?_ }, fun x _ => ⟨(a x).natAbs, by simp [θ, Nat.cast_natAbs, Int.cast_abs]⟩, ?_⟩
  · -- `M` is countable, hence covered by the ranges of countably many constant maps.
    obtain ⟨g, hg⟩ := countable_iff_exists_subset_range.1 M.finite_toSet.countable
    refine ⟨∅, measure_empty, fun j _ => g j, fun j => ⟨0, LipschitzWith.const _⟩, fun y hy => ?_⟩
    obtain ⟨j, rfl⟩ := hg hy
    exact Or.inr (mem_iUnion.2 ⟨j, 0, rfl⟩)
  · -- `ξ` is constant off and on the finite set `N`.
    exact (StronglyMeasurable.ite N.finite_toSet.measurableSet stronglyMeasurable_const
      stronglyMeasurable_const).aestronglyMeasurable
  · -- Every `x ∈ M` is oriented by the empty frame, spanning the weighted tangent space `{0}`.
    refine ae_restrict_of_forall_mem hMmeas fun x hx =>
      ⟨![], ⟨fun i => i.elim0, fun i => i.elim0⟩, ?_, ?_⟩
    · rw [range_eq_empty, Submodule.span_empty]
      refine ⟨finrank_bot ℝ (Eucl P), fun f => ?_⟩
      have hbot : ∫ y in ((⊥ : Submodule ℝ (Eucl P)) : Set (Eucl P)), f y
          ∂(μHE[0] : Measure (Eucl P)) = f 0 := by
        simp
      rw [hbot]
      -- `f = 0` off `B_R(0)`, and the points of `M \ {x}` have distance `≥ d` from `x`; so for
      -- `0 < r < d / R` only `y = x` contributes to `∑_{y ∈ M} f(η_{x,r}(y)) θ(y)`.
      obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
      obtain ⟨d, hd, hdM⟩ := Metric.isOpen_iff.mp
        (M.erase x).finite_toSet.isClosed.isOpen_compl x (by simp)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (div_pos hd hR)] with r ⟨hr0, hrd⟩
      have hinj : Function.Injective (blowUpMap x r) := fun y z h => by
        simpa [blowUpMap, hr0.ne'] using h
      have hback : ∀ y, x + r • blowUpMap x r y = y := fun y => by
        simp [blowUpMap, smul_smul, hr0.ne']
      rw [← Finset.coe_image, hsum, Finset.sum_image fun y _ z _ h => hinj h]
      simp only [hback]
      rw [Finset.sum_eq_single x (fun y hy hyx => ?_) (fun h => absurd hx h)]
      · simp [blowUpMap, mul_comm]
      · have hyd : d ≤ ‖y - x‖ := by
          rw [← dist_eq_norm]
          by_contra h
          exact hdM (mem_ball.2 (not_le.1 h)) (Finset.mem_erase.2 ⟨hyx, hy⟩)
        rw [lt_div_iff₀ hR] at hrd
        rw [hfR, zero_mul]
        rw [blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0, le_inv_mul_iff₀ hr0]
        linarith
    · by_cases hxN : x ∈ N
      · exact Or.inr (by simp [ξ, ε, hxN])
      · exact Or.inl (by simp [ξ, ε, hxN])
  · -- `τ(M, θ, ξ)(ω) = ∑_{x ∈ M} a(x) ω(x) = ∑_{x ∈ D} a(x) ω(x)`, as `a = 0` on `D \ M`.
    intro ω
    rw [hY, tauAction, hsum, Finset.sum_congr rfl fun x hx => hterm x hx _, hM,
      Finset.sum_filter_of_ne]
    intro x _ hne ha
    exact hne (by simp [ha])
/-- Locality of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1 (‡)), the locality step in the proof of 6.3: on
forms `ω` with `tsupport ω ⊆ V`, `V` open, `τ(M, θ, ξ)(ω)` only depends on `M ∩ V` up to
`Hᵏ`-null sets and on `θ, ξ` up to `Hᵏ ⌞ (M ∩ V)`-null sets.  Both integrands vanish off `V`,
so `∫_M = ∫_{M ∩ V}` and `∫_{M'} = ∫_{M' ∩ V}`; these agree since `M ∩ V`, `M' ∩ V` are
`Hᵏ`-a.e. equal and the integrands agree a.e. on `M ∩ V`.  No integrability is needed. -/
theorem Submission.ltg_tau_congr_on_open :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (ξ ξ' : Eucl P → NVector (Eucl P) k)
      (V : Set (Eucl P)), IsOpen V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ x = θ' x ∧ ξ x = ξ' x) →
      ∀ ω : DifferentialForm (Eucl P) k, tsupport ω ⊆ V →
        tauAction k M θ ξ ω = tauAction k M' θ' ξ' ω := by
  intro P k M M' θ θ' ξ ξ' V hV hMM' hθξ ω hω
  -- Both integrands vanish off `V`, since `ω = 0` off `tsupport ω ⊆ V`.
  have hvan : ∀ (η : Eucl P → ℝ) (ζ : Eucl P → NVector (Eucl P) k) (x : Eucl P), x ∉ V →
      η x * ζ x (ω x) = 0 := by
    intro η ζ x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), map_zero, mul_zero]
  -- Hence `∫_A = ∫_{A ∩ V}` for both integrands.
  have hcut : ∀ (A : Set (Eucl P)) (η : Eucl P → ℝ) (ζ : Eucl P → NVector (Eucl P) k),
      ∫ x in A, η x * ζ x (ω x) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ x in A ∩ V, η x * ζ x (ω x) ∂(μHE[k] : Measure (Eucl P)) := by
    intro A η ζ
    rw [inter_comm, ← Measure.restrict_restrict hV.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan η ζ)]
  -- `M ∩ V` and `M' ∩ V` differ by subsets of the null set `(M ∆ M') ∩ V`.
  have hset : M ∩ V =ᵐ[(μHE[k] : Measure (Eucl P))] M' ∩ V := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ hMM'
      rintro x ⟨⟨hxM, hxV⟩, hx⟩
      exact ⟨Or.inl ⟨hxM, fun hxM' => hx ⟨hxM', hxV⟩⟩, hxV⟩
    · refine measure_mono_null ?_ hMM'
      rintro x ⟨⟨hxM', hxV⟩, hx⟩
      exact ⟨Or.inr ⟨hxM', fun hxM => hx ⟨hxM, hxV⟩⟩, hxV⟩
  -- The integrands agree `Hᵏ ⌞ (M ∩ V)`-a.e.
  have hae : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)),
      θ x * ξ x (ω x) = θ' x * ξ' x (ω x) := by
    filter_upwards [hθξ] with x hx
    rw [hx.1, hx.2]
  calc tauAction k M θ ξ ω
      = ∫ x in M ∩ V, θ x * ξ x (ω x) ∂(μHE[k] : Measure (Eucl P)) := hcut M θ ξ
    _ = ∫ x in M ∩ V, θ' x * ξ' x (ω x) ∂(μHE[k] : Measure (Eucl P)) := integral_congr_ae hae
    _ = ∫ x in M' ∩ V, θ' x * ξ' x (ω x) ∂(μHE[k] : Measure (Eucl P)) :=
        setIntegral_congr_set hset
    _ = tauAction k M' θ' ξ' ω := (hcut M' θ' ξ').symm

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
/-- Rescaling a vanishing normalized quotient: if `F(ρ) / ρᵏ → 0` as `ρ → 0+`, then
`r⁻ᵏ · F(R r) → 0` as `r → 0+` for every `R > 0`. -/
theorem Submission.iwl_imc_quotient_rescale_tendsto_zero :
    ∀ (k : ℕ) (F : ℝ → ℝ≥0∞), Tendsto (fun ρ : ℝ => F ρ / ENNReal.ofReal (ρ ^ k)) (𝓝[>] 0) (𝓝 0) →
      ∀ R : ℝ, 0 < R →
        Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * F (R * r)) (𝓝[>] 0) (𝓝 0) := by
  intro k F hF R hR
  -- `r ↦ R r` maps `𝓝[>] 0` to `𝓝[>] 0`.
  have hmap : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_id.const_mul R
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hR hr
  -- `ofReal (Rᵏ) · F(R r) / ofReal ((R r)ᵏ) → 0`, as `ofReal (Rᵏ) ≠ ∞`.
  have hlim := ENNReal.Tendsto.const_mul (hF.comp hmap)
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (R ^ k) ≠ ∞))
  rw [mul_zero] at hlim
  -- For `r > 0`, `ofReal ((R r)ᵏ) = ofReal (Rᵏ) · ofReal (rᵏ)` with `0 < ofReal (Rᵏ) < ∞`.
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hRk : 0 < R ^ k := pow_pos hR k
  have hrk : 0 < r ^ k := pow_pos hr' k
  have hRk0 : ENNReal.ofReal (R ^ k) ≠ 0 := by simpa using hRk
  simp only [Function.comp_apply]
  rw [mul_pow, ENNReal.ofReal_mul hRk.le, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hRk0) (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ← mul_assoc,
    ENNReal.mul_inv_cancel hRk0 ENNReal.ofReal_ne_top, one_mul, ENNReal.ofReal_inv_of_pos hrk]
/-- Simon Ch. 1, Theorem 3.3 (with `A₁ = A`, `A₂ = V`): if `Θ*ⁿ(ν, x) ≥ t` on `A ⊆ V`, `V` open,
then `t Hⁿ(A) ≤ ν(V)`.  The isodiametric inequality (coordinate Steiner symmetrization)
shows that a closed ball of radius `r` has `μHE[n]`-cost at most `ωₙ rⁿ`, and the five-times
covering argument with its finite-tail step bounds `μHE[n](A)` by the cost of a disjoint family
of balls `B̄ ⊆ V` with `τ ωₙ rⁿ ≤ ν(B̄)`. -/
theorem Submission.rectifiability_density_comparison : ∀ (P n : ℕ) (ν : Measure (Eucl P)) (A V : Set (Eucl P)) (t : ℝ≥0∞), IsOpen V → A ⊆ V → (∀ x ∈ A, t ≤ dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x) → t * (μHE[n] : Measure (Eucl P)) A ≤ ν V := by
  -- Normalization: `μHE[m] = c • μH[m]` with `c 2ᵐ ≤ ωₘ` (Simon Ch. 1, 2.9–2.10).
  have hnorm : ∀ m : ℕ, ((Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin m))) μH[(m : ℝ)] : ℝ≥0) : ℝ≥0∞) * 2 ^ m ≤
        Poincare.SimonGMT.Chapter01.realUnitBallVolume (m : ℝ) := by
    intro m
    rcases m with _ | k
    · -- Dimension zero: `μHE[0] = μH[0]` forces the scalar to be one.
      have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 0)) => μ {0})
        (Measure.euclideanHausdorffMeasure_zero (X := EuclideanSpace ℝ (Fin 0)))
      simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Nat.cast_zero,
        Measure.hausdorffMeasure_zero_singleton, ENNReal.smul_def, smul_eq_mul, mul_one] at h
      simp [h, Poincare.SimonGMT.Chapter01.realUnitBallVolume_zero]
    obtain ⟨ω, hω⟩ : ∃ ω, Poincare.SimonGMT.Chapter01.realUnitBallVolume ((k + 1 : ℕ) : ℝ) = ω :=
      ⟨_, rfl⟩
    rw [hω]
    have hω0 : ω ≠ 0 :=
      hω ▸ (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (by positivity)).ne'
    have hωtop : ω ≠ ∞ := hω ▸ Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
    -- The isodiametric inequality `Lᵏ⁺¹(C) ≤ ω (diam C / 2)ᵏ⁺¹`, by coordinate Steiner
    -- symmetrization (Simon Ch. 1, 2.10).
    have isodiam : ∀ C : Set (EuclideanSpace ℝ (Fin (k + 1))),
        volume C ≤ ω * (ediam C / 2) ^ (k + 1) := by
      -- Two real slices at cross-distance `≤ d` have total length `≤ 2d`.
      have vol_add_le : ∀ S T : Set ℝ, S.Nonempty → T.Nonempty → ∀ d : ℝ,
          (∀ a ∈ S, ∀ b ∈ T, dist a b ≤ d) → volume S + volume T ≤ ENNReal.ofReal (2 * d) := by
        intro S T hS hT d hcross
        obtain ⟨a₀, ha₀⟩ := hS
        obtain ⟨b₀, hb₀⟩ := hT
        have hdist : ∀ a ∈ S, ∀ b ∈ T, a - b ≤ d ∧ b - a ≤ d := fun a ha b hb =>
          abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hcross a ha b hb)
        have hSl : BddBelow S := ⟨b₀ - d, fun a ha => by have := (hdist a ha b₀ hb₀).2; linarith⟩
        have hSu : BddAbove S := ⟨b₀ + d, fun a ha => by have := (hdist a ha b₀ hb₀).1; linarith⟩
        have hTl : BddBelow T := ⟨a₀ - d, fun b hb => by have := (hdist a₀ ha₀ b hb).1; linarith⟩
        have hTu : BddAbove T := ⟨a₀ + d, fun b hb => by have := (hdist a₀ ha₀ b hb).2; linarith⟩
        have hST : sSup S ≤ d + sInf T := by
          apply csSup_le ⟨a₀, ha₀⟩
          intro a ha
          have h : a - d ≤ sInf T := le_csInf ⟨b₀, hb₀⟩ fun b hb => by
            have := (hdist a ha b hb).1
            linarith
          linarith
        have hTS : sSup T ≤ d + sInf S := by
          apply csSup_le ⟨b₀, hb₀⟩
          intro b hb
          have h : b - d ≤ sInf S := le_csInf ⟨a₀, ha₀⟩ fun a ha => by
            have := (hdist a ha b hb).2
            linarith
          linarith
        have hwS : 0 ≤ sSup S - sInf S :=
          sub_nonneg.mpr ((csInf_le hSl ha₀).trans (le_csSup hSu ha₀))
        have hwT : 0 ≤ sSup T - sInf T :=
          sub_nonneg.mpr ((csInf_le hTl hb₀).trans (le_csSup hTu hb₀))
        calc
          volume S + volume T ≤ volume (Icc (sInf S) (sSup S)) + volume (Icc (sInf T) (sSup T)) :=
            add_le_add (measure_mono (subset_Icc_csInf_csSup hSl hSu))
              (measure_mono (subset_Icc_csInf_csSup hTl hTu))
          _ = ENNReal.ofReal ((sSup S - sInf S) + (sSup T - sInf T)) := by
            rw [Real.volume_Icc, Real.volume_Icc, ENNReal.ofReal_add hwS hwT]
          _ ≤ ENNReal.ofReal (2 * d) := ENNReal.ofReal_le_ofReal (by linarith)
      -- The centered interval `cs S` of the same length as a real slice `S`.
      obtain ⟨cs, hcs⟩ : ∃ cs : Set ℝ → Set ℝ,
          ∀ S t, t ∈ cs S ↔ (S.Nonempty ∧ |t| ≤ (volume S).toReal / 2) :=
        ⟨fun S => {t | S.Nonempty ∧ |t| ≤ (volume S).toReal / 2}, fun _ _ => Iff.rfl⟩
      have cs_dist : ∀ (S T : Set ℝ) (d : ℝ), (∀ a ∈ S, ∀ b ∈ T, dist a b ≤ d) →
          ∀ x ∈ cs S, ∀ y ∈ cs T, dist x y ≤ d := by
        intro S T d hcross x hx y hy
        rw [hcs] at hx hy
        have hsum := vol_add_le S T hx.1 hy.1 d hcross
        have hfin : volume S + volume T ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
        have hSfin : volume S ≠ ∞ := (ENNReal.add_ne_top.mp hfin).1
        have hTfin : volume T ≠ ∞ := (ENNReal.add_ne_top.mp hfin).2
        have hd : 0 ≤ d := by
          obtain ⟨a, ha⟩ := hx.1
          obtain ⟨b, hb⟩ := hy.1
          exact dist_nonneg.trans (hcross a ha b hb)
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
        rw [ENNReal.toReal_add hSfin hTfin, ENNReal.toReal_ofReal (by positivity)] at hreal
        calc
          dist x y = |x - y| := Real.dist_eq _ _
          _ ≤ |x| + |y| := abs_sub _ _
          _ ≤ (volume S).toReal / 2 + (volume T).toReal / 2 := add_le_add hx.2 hy.2
          _ ≤ d := by linarith
      have cs_vol : ∀ S : Set ℝ, volume S ≠ ∞ → volume (cs S) = volume S := by
        intro S hfin
        rcases S.eq_empty_or_nonempty with rfl | hS
        · have hempty : cs ∅ = ∅ := by
            ext t
            simp [hcs]
          simp [hempty]
        · have hinterval : cs S = Icc (-(volume S).toReal / 2) ((volume S).toReal / 2) := by
            ext x
            simp [hcs, hS, abs_le, neg_div]
          rw [hinterval, Real.volume_Icc]
          convert ENNReal.ofReal_toReal hfin using 1
          congr 1
          ring
      have cs_neg : ∀ S t, t ∈ cs S → -t ∈ cs S := by
        intro S t h
        rw [hcs] at h ⊢
        simpa only [abs_neg] using h
      -- Changing one coordinate changes the squared distance by that coordinate's change.
      have dist_update : ∀ (j : Fin (k + 1)) (x y : EuclideanSpace ℝ (Fin (k + 1))) (a b : ℝ),
          dist (WithLp.toLp 2 (Function.update x.ofLp j a))
              (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
            dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
        intro j x y a b
        rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
        have hsum := Finset.sum_erase_add Finset.univ
          (fun i : Fin (k + 1) => dist (x i) (y i) ^ 2) (Finset.mem_univ j)
        have hsum' := Finset.sum_erase_add Finset.univ
          (fun i : Fin (k + 1) => dist (Function.update x.ofLp j a i)
            (Function.update y.ofLp j b i) ^ 2) (Finset.mem_univ j)
        have hrest : (∑ i ∈ Finset.univ.erase j,
            dist (Function.update x.ofLp j a i) (Function.update y.ofLp j b i) ^ 2) =
            ∑ i ∈ Finset.univ.erase j, dist (x i) (y i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]
        rw [hrest, Function.update_self, Function.update_self] at hsum'
        linarith
      -- Coordinate slices `sl j A x` and the Steiner symmetrization `st j A`.
      obtain ⟨sl, hsl⟩ : ∃ sl : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin (k + 1))) →
          EuclideanSpace ℝ (Fin (k + 1)) → Set ℝ,
          ∀ j A x t, t ∈ sl j A x ↔ WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A :=
        ⟨fun j A x => {t | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A},
          fun _ _ _ _ => Iff.rfl⟩
      obtain ⟨st, hst⟩ : ∃ st : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin (k + 1))) →
          Set (EuclideanSpace ℝ (Fin (k + 1))), ∀ j A x, x ∈ st j A ↔ x j ∈ cs (sl j A x) :=
        ⟨fun j A => {x | x j ∈ cs (sl j A x)}, fun _ _ _ => Iff.rfl⟩
      -- Steiner symmetrization does not increase the diameter.
      have st_diam : ∀ j A, ediam (st j A) ≤ ediam A := by
        intro j A
        by_cases hfin : ediam A = ∞
        · rw [hfin]
          exact le_top
        have hbounded : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
        have hdiam : ediam (st j A) ≤ ENNReal.ofReal (diam A) := by
          apply ediam_le_of_forall_dist_le
          intro x hx y hy
          rw [hst] at hx hy
          obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = diam A ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 :=
            ⟨_, rfl⟩
          have hsq : ∀ a ∈ sl j A x, ∀ b ∈ sl j A y, dist a b ^ 2 ≤ D := by
            intro a ha b hb
            rw [hsl] at ha hb
            have hd := dist_le_diam_of_mem hbounded ha hb
            have hsq' : dist (WithLp.toLp 2 (Function.update x.ofLp j a))
                (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 ≤ diam A ^ 2 :=
              pow_le_pow_left₀ dist_nonneg hd 2
            rw [dist_update] at hsq'
            linarith
          have hD : 0 ≤ D := by
            obtain ⟨a, ha⟩ := ((hcs _ _).1 hx).1
            obtain ⟨b, hb⟩ := ((hcs _ _).1 hy).1
            exact (sq_nonneg (dist a b)).trans (hsq a ha b hb)
          have hsqrt := Real.sq_sqrt hD
          have hcross : ∀ a ∈ sl j A x, ∀ b ∈ sl j A y, dist a b ≤ Real.sqrt D := by
            intro a ha b hb
            have h := hsq a ha b hb
            nlinarith [dist_nonneg (x := a) (y := b), Real.sqrt_nonneg D]
          have hcentered := cs_dist _ _ _ hcross _ hx _ hy
          have hcentered_sq : dist (x j) (y j) ^ 2 ≤ D := by
            nlinarith [dist_nonneg (x := x j) (y := y j), Real.sqrt_nonneg D]
          rw [hD_def] at hcentered_sq
          nlinarith [dist_nonneg (x := x) (y := y), diam_nonneg (s := A)]
        simpa only [diam, ENNReal.ofReal_toReal hfin] using hdiam
      -- Steiner symmetrization of a compact set does not decrease the volume (Fubini).
      have st_vol : ∀ j A, IsCompact A → volume A ≤ volume (st j A) := by
        intro j A hA
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) j
        let φ : ℝ × (Fin k → ℝ) → EuclideanSpace ℝ (Fin (k + 1)) :=
          fun p => WithLp.toLp 2 (e.symm p)
        have hφ : MeasurePreserving φ volume volume :=
          (PiLp.volume_preserving_toLp (Fin (k + 1))).comp
            (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
        have hφcoord : ∀ (t : ℝ) (z : Fin k → ℝ), φ (t, z) j = t := fun t z =>
          Fin.insertNth_apply_same (α := fun _ : Fin (k + 1) => ℝ) j t z
        let T := toMeasurable volume (st j A)
        have hT : MeasurableSet T := measurableSet_toMeasurable volume (st j A)
        have hTA : st j A ⊆ T := subset_toMeasurable volume (st j A)
        have hslice : ∀ (t : ℝ) (z : Fin k → ℝ),
            sl j A (φ (t, z)) = (fun s => φ (s, z)) ⁻¹' A := by
          intro t z
          ext s
          rw [hsl]
          change (WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ A) ↔
            WithLp.toLp 2 (j.insertNth s z) ∈ A
          rw [Fin.update_insertNth]
        have hfinite : ∀ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) ≠ ∞ := by
          intro z
          have hproj : IsCompact ((fun x : EuclideanSpace ℝ (Fin (k + 1)) => x j) '' A) :=
            hA.image (by fun_prop)
          have hsub : (fun t => φ (t, z)) ⁻¹' A ⊆
              (fun x : EuclideanSpace ℝ (Fin (k + 1)) => x j) '' A := by
            intro t ht
            exact ⟨φ (t, z), ht, hφcoord t z⟩
          exact (measure_lt_top_of_subset hsub hproj.measure_lt_top.ne).ne
        calc
          volume A = volume (φ ⁻¹' A) :=
            (hφ.measure_preimage hA.measurableSet.nullMeasurableSet).symm
          _ = ∫⁻ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' A) :=
            Measure.prod_apply_symm (hA.measurableSet.preimage hφ.measurable)
          _ = ∫⁻ z : Fin k → ℝ, volume (cs ((fun t => φ (t, z)) ⁻¹' A)) := by
            apply lintegral_congr
            intro z
            exact (cs_vol _ (hfinite z)).symm
          _ ≤ ∫⁻ z : Fin k → ℝ, volume ((fun t => φ (t, z)) ⁻¹' T) := by
            apply lintegral_mono
            intro z
            apply measure_mono
            intro t ht
            apply hTA
            show φ (t, z) ∈ st j A
            rw [hst, hφcoord, hslice]
            exact ht
          _ = volume (φ ⁻¹' T) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
          _ = volume T := hφ.measure_preimage hT.nullMeasurableSet
          _ = volume (st j A) := measure_toMeasurable (st j A)
      -- Coordinate reflections `rf j`.
      obtain ⟨rf, hrf⟩ : ∃ rf : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)) →
          EuclideanSpace ℝ (Fin (k + 1)),
          ∀ j x, rf j x = WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :=
        ⟨fun j x => WithLp.toLp 2 (Function.update x.ofLp j (-x j)), fun _ _ => rfl⟩
      have rf_same : ∀ j x, rf j x j = -x j := by
        intro j x
        simp [hrf]
      have rf_ne : ∀ i j, i ≠ j → ∀ x, rf j x i = x i := by
        intro i j hij x
        rw [hrf]
        exact Function.update_of_ne hij _ _
      have rf_invol : ∀ j x, rf j (rf j x) = x := by
        intro j x
        ext i
        by_cases hij : i = j
        · subst i
          simp [rf_same]
        · simp only [rf_ne i j hij]
      have rf_cont : ∀ j, Continuous (rf j) := by
        intro j
        have hfun : rf j = fun x => WithLp.toLp 2 (Function.update x.ofLp j (-x j)) :=
          funext (hrf j)
        rw [hfun]
        apply (PiLp.continuous_toLp 2 (fun _ : Fin (k + 1) => ℝ)).comp
        apply continuous_pi
        intro i
        by_cases hij : i = j
        · subst i
          simpa only [Function.update_self] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (k + 1)) => -x j) by fun_prop)
        · simpa only [Function.update_of_ne hij] using
            (show Continuous (fun x : EuclideanSpace ℝ (Fin (k + 1)) => x i) by fun_prop)
      have sl_rf_same : ∀ j A x, sl j A (rf j x) = sl j A x := by
        intro j A x
        ext t
        rw [hsl, hsl, hrf]
        change (WithLp.toLp 2 (Function.update (Function.update x.ofLp j (-x j)) j t) ∈ A) ↔ _
        rw [Function.update_idem]
      have rf_update : ∀ i j, i ≠ j → ∀ x t,
          rf i (WithLp.toLp 2 (Function.update x.ofLp j t)) =
            WithLp.toLp 2 (Function.update (rf i x).ofLp j t) := by
        intro i j hij x t
        ext l
        by_cases hli : l = i
        · subst l
          simp [hrf, hij]
        · by_cases hlj : l = j
          · subst l
            simp [hrf, hij, Ne.symm hij]
          · simp [hrf, Function.update_apply, hli, hlj]
      have sl_rf_symm : ∀ i j, i ≠ j → ∀ A, (∀ x ∈ A, rf i x ∈ A) →
          ∀ x, sl j A (rf i x) = sl j A x := by
        intro i j hij A hA x
        ext t
        rw [hsl, hsl, ← rf_update i j hij]
        constructor
        · intro h
          simpa only [rf_invol] using hA _ h
        · exact hA _
      have st_rf_same : ∀ j A, ∀ x ∈ st j A, rf j x ∈ st j A := by
        intro j A x hx
        rw [hst] at hx ⊢
        rw [rf_same, sl_rf_same]
        exact cs_neg _ _ hx
      have st_rf_pres : ∀ i j, i ≠ j → ∀ A, (∀ x ∈ A, rf i x ∈ A) →
          ∀ x ∈ st j A, rf i x ∈ st j A := by
        intro i j hij A hA x hx
        rw [hst] at hx ⊢
        rw [rf_ne j i (Ne.symm hij), sl_rf_symm i j hij A hA]
        exact hx
      have closure_rf : ∀ i (A : Set (EuclideanSpace ℝ (Fin (k + 1)))),
          (∀ x ∈ A, rf i x ∈ A) → ∀ x ∈ closure A, rf i x ∈ closure A := by
        intro i A hA x hx
        have hsub : A ⊆ rf i ⁻¹' closure A := fun y hy => subset_closure (hA y hy)
        exact closure_minimal hsub (isClosed_closure.preimage (rf_cont i)) hx
      -- Successive closed Steiner symmetrizations in all coordinates.
      have hfinite : ∀ K₀ : Set (EuclideanSpace ℝ (Fin (k + 1))), IsCompact K₀ →
          ∀ s : Finset (Fin (k + 1)), ∃ K : Set (EuclideanSpace ℝ (Fin (k + 1))), IsCompact K ∧
            ediam K ≤ ediam K₀ ∧ volume K₀ ≤ volume K ∧ ∀ i ∈ s, ∀ x ∈ K, rf i x ∈ K := by
        intro K₀ hK₀ s
        induction s using Finset.induction_on with
        | empty => exact ⟨K₀, hK₀, le_rfl, le_rfl, by simp⟩
        | @insert i s hi ih =>
          obtain ⟨K, hK, hdiam, hvol, hsym⟩ := ih
          have hdK : ediam (closure (st i K)) ≤ ediam K := by
            rw [ediam_closure]
            exact st_diam i K
          refine ⟨closure (st i K), ?_, hdK.trans hdiam,
            hvol.trans ((st_vol i K hK).trans (measure_mono subset_closure)), ?_⟩
          · apply Bornology.IsBounded.isCompact_closure
            apply isBounded_iff_ediam_ne_top.mpr
            exact ne_top_of_le_ne_top hK.isBounded.ediam_ne_top (st_diam i K)
          · intro l hl
            rcases Finset.mem_insert.mp hl with rfl | hls
            · exact closure_rf l _ (st_rf_same l K)
            · apply closure_rf l _
              apply st_rf_pres l i _ K (hsym l hls)
              rintro rfl
              exact hi hls
      -- Symmetry in every coordinate hyperplane gives central symmetry.
      have neg_mem : ∀ K : Set (EuclideanSpace ℝ (Fin (k + 1))),
          (∀ i, ∀ x ∈ K, rf i x ∈ K) → ∀ x ∈ K, -x ∈ K := by
        intro K hK x hx
        have hmem : ∀ s : Finset (Fin (k + 1)),
            WithLp.toLp 2 (fun l => if l ∈ s then -x l else x l) ∈ K := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using hx
          | @insert i s hi ih =>
            have h := hK i _ ih
            convert h using 1
            ext l
            by_cases hli : l = i
            · subst l
              simp [hrf, hi]
            · simp [hrf, hli]
        have heq : (WithLp.toLp 2 fun l => -x l) = -x := by
          ext l
          rfl
        simpa only [Finset.mem_univ, ite_true, heq] using hmem Finset.univ
      -- Conclusion for a general set `C`.
      intro C
      by_cases hfin : ediam C = ∞
      · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
          ENNReal.top_pow (Nat.succ_ne_zero k), ENNReal.mul_top hω0]
        exact le_top
      have hbdd : Bornology.IsBounded C := isBounded_iff_ediam_ne_top.mpr hfin
      obtain ⟨K, hK, hdiamK, hvolK, hsymK⟩ :=
        hfinite (closure C) hbdd.isCompact_closure Finset.univ
      have hneg := neg_mem K (fun i => hsymK i (Finset.mem_univ i))
      have hKb : Bornology.IsBounded K := hK.isBounded
      have hsub : K ⊆ closedBall 0 (diam K / 2) := by
        intro x hx
        have hdist := dist_le_diam_of_mem hKb hx (hneg x hx)
        rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at hdist
        norm_num at hdist
        rw [mem_closedBall, dist_zero_right]
        linarith
      have hpi : Real.sqrt Real.pi ^ (k + 1) = Real.pi ^ (((k + 1 : ℕ) : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
        congr 1
        push_cast
        ring
      have hball : volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) (diam K / 2)) =
          ω * ENNReal.ofReal (diam K / 2) ^ (k + 1) := by
        rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, hpi, ← hω,
          Poincare.SimonGMT.Chapter01.realUnitBallVolume_eq, mul_comm]
      calc
        volume C ≤ volume (closure C) := measure_mono subset_closure
        _ ≤ volume K := hvolK
        _ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) (diam K / 2)) :=
          measure_mono hsub
        _ = ω * ENNReal.ofReal (diam K / 2) ^ (k + 1) := hball
        _ = ω * (ediam K / 2) ^ (k + 1) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat, diam,
            ENNReal.ofReal_toReal hKb.ediam_ne_top]
        _ ≤ ω * (ediam C / 2) ^ (k + 1) := by
          have hKC : ediam K ≤ ediam C := (ediam_closure C) ▸ hdiamK
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ zero_le (ENNReal.div_le_div_right hKC 2) _) zero_le
    -- Hence `ω⁻¹ 2ᵏ⁺¹ Lᵏ⁺¹ ≤ μH[k+1]`, and comparing on the unit ball gives `c 2ᵏ⁺¹ ≤ ω`.
    have hle : (ω⁻¹ * 2 ^ (k + 1)) •
        (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) ≤ μH[((k + 1 : ℕ) : ℝ)] := by
      refine Measure.le_mkMetric (fun r : ℝ≥0∞ => r ^ ((k + 1 : ℕ) : ℝ)) _ 1 one_pos fun s _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
      calc
        ω⁻¹ * 2 ^ (k + 1) * volume s ≤ ω⁻¹ * 2 ^ (k + 1) * (ω * (ediam s / 2) ^ (k + 1)) := by
          gcongr
          exact isodiam s
        _ = (2 * (ediam s / 2)) ^ (k + 1) := by
          rw [mul_pow, mul_assoc, mul_left_comm (2 ^ (k + 1)), ← mul_assoc,
            ENNReal.inv_mul_cancel hω0 hωtop, one_mul]
        _ = ediam s ^ (k + 1) := by
          rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    have hB : volume (closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) = ω := by
      rw [Poincare.SimonGMT.Chapter01.volume_closedBall_eq_densityNormalization (k + 1) 0 one_pos,
        hω]
      simp
    have hHB : 2 ^ (k + 1) ≤ (μH[((k + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        (closedBall 0 1) := by
      have h := Measure.le_iff'.1 hle (closedBall 0 1)
      rwa [Measure.smul_apply, smul_eq_mul, hB, mul_comm, ← mul_assoc,
        ENNReal.mul_inv_cancel hω0 hωtop, one_mul] at h
    have hvol := Measure.isAddLeftInvariant_eq_smul
      (volume : Measure (EuclideanSpace ℝ (Fin (k + 1)))) (μH[((k + 1 : ℕ) : ℝ)])
    have h2 := congrArg
      (fun μ : Measure (EuclideanSpace ℝ (Fin (k + 1))) => μ (closedBall 0 1)) hvol
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hB] at h2
    calc
      _ ≤ ((Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin (k + 1))))
            μH[((k + 1 : ℕ) : ℝ)] : ℝ≥0) : ℝ≥0∞) *
          (μH[((k + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (k + 1)))) (closedBall 0 1) := by
        gcongr
      _ = _ := h2.symm
  intro P n ν A V t hV hAV hden
  obtain ⟨ω, hω⟩ : ∃ ω, Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) = ω := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)] = c := ⟨_, rfl⟩
  have hcω : (c : ℝ≥0∞) * 2 ^ n ≤ ω := hc ▸ hω ▸ hnorm n
  have hω0 : ω ≠ 0 := hω ▸ (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (by positivity)).ne'
  have hωtop : ω ≠ ∞ := hω ▸ Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
  -- `μHE[n] = c • μH[n]`, and `μH[n]` is the supremum of its size-`δ` approximations `pre δ`.
  have hHE : (μHE[n] : Measure (Eucl P)) A = c * ⨆ (δ : ℝ≥0∞) (_ : 0 < δ),
      OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A := by
    rw [Measure.euclideanHausdorffMeasure_def, hc, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul, ← Measure.toOuterMeasure_apply, Measure.hausdorffMeasure,
      Measure.mkMetric_toOuterMeasure, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
      OuterMeasure.iSup_apply]
    simp only [OuterMeasure.iSup_apply]
  by_cases hVfin : ν V = ∞
  · rw [hVfin]
    exact le_top
  -- It suffices to prove `τ μHE[n](A) ≤ ν(V)` for `0 < τ < t`, scale by scale.
  rw [hHE]
  conv_lhs => rw [← ENNReal.iSup_lt_eq_self t]
  simp only [ENNReal.iSup_mul]
  refine iSup₂_le fun τ hτ => ?_
  rcases eq_or_ne τ 0 with rfl | hτ0
  · simp
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine iSup_le fun δ => ?_
  rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
  refine iSup_le fun hδ => ?_
  obtain ⟨R, -, hR0, hRδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
  -- The fine family of closed balls `B̄ᵣ(x) ⊆ V`, `x ∈ A`, `r < R/10`, `τ ω rⁿ ≤ ν(B̄ᵣ(x))`.
  let B : Set (Eucl P × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ b.2 < R / 10 ∧
    closedBall b.1 b.2 ⊆ V ∧ τ * (ω * ENNReal.ofReal b.2 ^ (n : ℝ)) ≤ ν (closedBall b.1 b.2)}
  have hfine : ∀ x ∈ A, ∀ ε > 0, ∃ b ∈ B,
      x ∈ closedBall b.1 b.2 ∧ diam (closedBall b.1 b.2) < ε := by
    intro x hx ε hε
    obtain ⟨RV, hRV, hRVV⟩ := nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds (hAV hx))
    have hpos : 0 < min (min (R / 10) (ε / 2)) RV :=
      lt_min (lt_min (by positivity) (half_pos hε)) hRV
    have hτx : τ < dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x :=
      hτ.trans_le (hden x hx)
    obtain ⟨r, hqr, hr⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hτx).and_eventually
      (Ioo_mem_nhdsGT hpos)).exists
    have hr0 : 0 < r := hr.1
    have hrR : r < R / 10 := hr.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hrε : r < ε / 2 := hr.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hrV : r < RV := hr.2.trans_le (min_le_right _ _)
    have hnorm0 : ω * ENNReal.ofReal r ^ (n : ℝ) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr0) ENNReal.ofReal_ne_top).ne'
    have hnormtop : ω * ENNReal.ofReal r ^ (n : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    rw [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient, hω, univ_inter,
      Measure.toOuterMeasure_apply] at hqr
    have hmass : τ * (ω * ENNReal.ofReal r ^ (n : ℝ)) ≤ ν (closedBall x r) :=
      ((ENNReal.lt_div_iff_mul_lt (Or.inl hnorm0) (Or.inl hnormtop)).mp hqr).le
    refine ⟨(x, r), ⟨hx, hr0, hrR, (closedBall_subset_closedBall hrV.le).trans hRVV, hmass⟩,
      mem_closedBall_self hr0.le, (diam_closedBall hr0.le).trans_lt (by linarith)⟩
  -- The five-times covering lemma (Simon Ch. 1, 3.4) gives a disjoint subfamily `D`.
  obtain ⟨D, hDB, hdisj, hcover⟩ := Poincare.SimonGMT.Chapter01.exists_fiveTimesCovering B
    Prod.fst Prod.snd (fun b hb => hb.2.1.le) R
    (fun b hb => (diam_closedBall hb.2.1.le).trans (by have := hb.2.2.1; linarith))
  have hdisj' : Pairwise (fun i j : D =>
      Disjoint (closedBall i.val.1 i.val.2) (closedBall j.val.1 j.val.2)) :=
    fun i j hij => hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hpos : ∀ b : D, 0 < ν (closedBall b.val.1 b.val.2) := by
    intro b
    have hb := hDB b.property
    exact (pos_iff_ne_zero.mpr (mul_ne_zero hτ0 (mul_ne_zero hω0
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hb.2.1) ENNReal.ofReal_ne_top).ne'))).trans_le
      hb.2.2.2.2
  have hUV : (⋃ b : D, closedBall b.val.1 b.val.2) ⊆ V :=
    iUnion_subset fun b => (hDB b.property).2.2.2.1
  have hcount := ν.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
    (fun b : D => measurableSet_closedBall) hdisj' (ne_top_of_le_ne_top hVfin (measure_mono hUV))
  have hDc : Countable D := countable_univ_iff.mp (by simpa only [hpos, ofPred_true] using hcount)
  -- Total cost of the disjoint family: `τ ∑ ω rⁿ ≤ ∑ ν(B̄ᵣ) ≤ ν(V)`.
  let w : D → ℝ≥0∞ := fun b => ω * ENNReal.ofReal b.val.2 ^ (n : ℝ)
  have hsum : τ * ∑' b : D, w b ≤ ν V := by
    rw [← ENNReal.tsum_mul_left]
    calc
      ∑' b : D, τ * w b ≤ ∑' b : D, ν (closedBall b.val.1 b.val.2) :=
        ENNReal.tsum_le_tsum fun b => (hDB b.property).2.2.2.2
      _ = ν (⋃ b : D, closedBall b.val.1 b.val.2) :=
        (measure_iUnion hdisj' (fun _ => measurableSet_closedBall)).symm
      _ ≤ ν V := measure_mono hUV
  have hsumfin : ∑' b : D, w b ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hτ0] at hsum
    exact hVfin (top_le_iff.mp hsum)
  -- Costs of the selected balls and of their five-times enlargements at scale `δ`.
  have hediam : ∀ (x : Eucl P) (r : ℝ), ediam (closedBall x r) ≤ 2 * ENNReal.ofReal r := by
    intro x r
    calc
      ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
        ediam_le_of_forall_dist_le fun y hy z hz => by
          have hy' := mem_closedBall.mp hy
          have hz' := mem_closedBall.mp hz
          linarith [dist_triangle_right y z x]
      _ = 2 * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hcost : ∀ (x : Eucl P) (r : ℝ), 0 ≤ r → 2 * r ≤ R →
      (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
        (closedBall x r) ≤ ω * ENNReal.ofReal r ^ (n : ℝ) := by
    intro x r hr hrR
    have hle : ediam (closedBall x r) ≤ δ := by
      refine (hediam x r).trans (le_trans ?_ hRδ.le)
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hrR
    calc
      (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
          (closedBall x r) ≤ c * ediam (closedBall x r) ^ (n : ℝ) := by
        gcongr
        exact OuterMeasure.mkMetric'.pre_le hle
      _ ≤ c * (2 * ENNReal.ofReal r) ^ (n : ℝ) := by
        gcongr
        exact hediam x r
      _ = (c * 2 ^ n) * ENNReal.ofReal r ^ (n : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.rpow_natCast, mul_assoc]
      _ ≤ ω * ENNReal.ofReal r ^ (n : ℝ) := by
        gcongr
  have hsmall : ∀ b : D, (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
      (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ (closedBall b.val.1 b.val.2) ≤ w b := by
    intro b
    have hb := hDB b.property
    exact hcost _ _ hb.2.1.le (by linarith [hb.2.2.1])
  have hlarge : ∀ b : D, (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
      (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ (closedBall b.val.1 (5 * b.val.2)) ≤
        5 ^ n * w b := by
    intro b
    have hb := hDB b.property
    refine (hcost _ _ (by linarith [hb.2.1]) (by linarith [hb.2.2.1])).trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.rpow_natCast, ENNReal.ofReal_ofNat]
    simp only [w]
    ring
  -- Simon's finite-tail step (Corollary 3.5): the enlarged tail costs vanish in the limit.
  have hlim : Tendsto (fun F : Finset D => (∑' b, w b) + 5 ^ n * ∑' b : {b // b ∉ F}, w b)
      atTop (𝓝 (∑' b, w b)) := by
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_tsum_compl_atTop_zero hsumfin) (Or.inr (by simp)))
  have hηA : (c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
      (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A ≤ ∑' b, w b := by
    apply ge_of_tendsto' hlim
    intro F
    let F' : Finset (Eucl P × ℝ) := F.image Subtype.val
    have hsub : A ⊆ (⋃ b ∈ F, closedBall b.val.1 b.val.2) ∪
        ⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2) := by
      intro x hx
      by_cases hxF : x ∈ ⋃ b ∈ F, closedBall b.val.1 b.val.2
      · exact Or.inl hxF
      · right
        have hxF' : x ∉ ⋃ b ∈ F', closedBall b.1 b.2 := by
          simpa only [F', Finset.mem_image, mem_iUnion, exists_prop,
            exists_exists_and_eq_and] using hxF
        obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp
          (Poincare.SimonGMT.Chapter01.fiveTimesCovering_finite_remainder A B D Prod.fst
            Prod.snd hfine (fun b hb => by
              obtain ⟨d, hd, hinter, _, hsub⟩ := hcover b hb
              exact ⟨d, hd, hinter, hsub⟩) F' ⟨hx, hxF'⟩)
        have hbF : (⟨b, hb.1⟩ : D) ∉ F := by
          intro h
          exact hb.2 (Finset.mem_image.mpr ⟨⟨b, hb.1⟩, h, rfl⟩)
        exact mem_iUnion.mpr ⟨⟨⟨b, hb.1⟩, hbF⟩, hxb⟩
    set η := OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
    calc
      (c : ℝ≥0∞) * η A ≤ c * (η (⋃ b ∈ F, closedBall b.val.1 b.val.2) +
          η (⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2))) := by
        gcongr
        exact (measure_mono hsub).trans (measure_union_le _ _)
      _ = c * η (⋃ b ∈ F, closedBall b.val.1 b.val.2) +
          c * η (⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2)) :=
        mul_add _ _ _
      _ ≤ (∑ b ∈ F, w b) + ∑' b : {b : D // b ∉ F}, 5 ^ n * w b := by
        gcongr
        · calc
            (c : ℝ≥0∞) * η (⋃ b ∈ F, closedBall b.val.1 b.val.2) ≤
                c * ∑ b ∈ F, η (closedBall b.val.1 b.val.2) := by
              gcongr
              exact measure_biUnion_finset_le _ _
            _ = ∑ b ∈ F, c * η (closedBall b.val.1 b.val.2) := Finset.mul_sum _ _ _
            _ ≤ ∑ b ∈ F, w b := Finset.sum_le_sum fun b _ => hsmall b
        · calc
            (c : ℝ≥0∞) * η (⋃ b : {b : D // b ∉ F}, closedBall b.val.val.1 (5 * b.val.val.2)) ≤
                c * ∑' b : {b : D // b ∉ F}, η (closedBall b.val.val.1 (5 * b.val.val.2)) := by
              gcongr
              exact measure_iUnion_le _
            _ = ∑' b : {b : D // b ∉ F}, c * η (closedBall b.val.val.1 (5 * b.val.val.2)) :=
              ENNReal.tsum_mul_left.symm
            _ ≤ ∑' b : {b : D // b ∉ F}, 5 ^ n * w b :=
              ENNReal.tsum_le_tsum fun b => hlarge b
      _ ≤ (∑' b, w b) + 5 ^ n * ∑' b : {b : D // b ∉ F}, w b := by
        rw [ENNReal.tsum_mul_left]
        exact add_le_add (ENNReal.sum_le_tsum F) le_rfl
  calc
    τ * ((c : ℝ≥0∞) * OuterMeasure.mkMetric'.pre
        (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A) ≤ τ * ∑' b, w b := by
      gcongr
    _ ≤ ν V := hsum
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

/-- **`(Hᵏ⌞M, θξ)` represents `τ(M, θ, ξ)` as in (2.7) (Simon Ch. 6, 3.1, p. 146).**  If
`X(ω) = τ(M, θ, ξ)(ω)` for every `ω ∈ 𝒟ᵏ(U)` and `(M, θ, ξ)` is a rectifiable triple in `U`, then
`⟨ω, θξ⟩` is `Hᵏ⌞M`-integrable and `X(ω) = ∫ ⟨ω, θξ⟩ d(Hᵏ⌞M)`.  Pointwise
`⟨ω(x), θ(x)ξ(x)⟩ = θ(x)⟨ω(x), ξ(x)⟩`, which is integrable on `M` by `ltg_tau_integrable` since a
test form is continuous with compact support in `U`. -/
theorem Submission.iwl_imc_tau_measure_representation : ∀ (P k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (X : GeometricCurrentOn U k), IsRectifiableTriple U k M θ ξ → (∀ ω : TestFormOn U k, X ω = tauAction k M θ ξ ω) → IsMeasureRepresentation X ((μHE[k] : Measure (Eucl P)).restrict M) (fun x => θ x • ξ x) := by
  intro P k U M θ ξ X hT hX ω
  -- Step 3: `⟨ω(x), θ(x)ξ(x)⟩ = θ(x)⟨ω(x), ξ(x)⟩` (scalar multiplication is pointwise).
  have hfun : (fun x => (θ x • ξ x) ((ω : DifferentialForm (Eucl P) k) x)) =
      fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x) := by
    funext x
    simp only [smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  -- Steps 1–2: `ω` is continuous with compact support in `U`, so `ltg_tau_integrable` applies.
  · show Integrable (fun x => (θ x • ξ x) ((ω : DifferentialForm (Eucl P) k) x)) _
    rw [hfun]
    exact (Submission.ltg_tau_integrable P k U M θ ξ hT).2 ω ω.2.1.1.continuous ω.2.1.2 ω.2.2
  -- Step 4: `X(ω) = τ(M, θ, ξ)(ω) = ∫_M θ⟨ω, ξ⟩ dHᵏ`.
  · show X ω = ∫ x, (θ x • ξ x) ((ω : DifferentialForm (Eucl P) k) x) ∂_
    rw [hfun]
    exact hX ω
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
/-- **Helly selection with a countable exceptional set** (the selection step in the proof of
Simon Ch. 6, 8.2 and Remark 8.3(1), p. 176: "an argument like that in 6.7(2) of Ch. 2").
Nondecreasing `F j : ℝ → ℝ` with `|F j t| ≤ C` have a subsequence `F (ψ j)` converging at every
rational to a nondecreasing `g` (Tychonoff for `∏_{q ∈ ℚ} [-C, C]`).  The left envelope
`F⁻(t) = sup_{q < t} g(q)` is nondecreasing, so its discontinuity set `E` is countable; for
`s ∉ E`, rationals `a < s < b` near `s` give `g(b) - g(a) < ε`, hence
`F (ψ j) b - F (ψ j) a < ε` for all large `j`. -/
theorem Submission.iwl_rl_monotone_helly_selection : ∀ (F : ℕ → ℝ → ℝ) (C : ℝ), (∀ j, Monotone (F j)) → (∀ j t, |F j t| ≤ C) → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, a < s ∧ s < b ∧ ∀ᶠ j in atTop, F (ψ j) b - F (ψ j) a < ε := by
  intro F C hmono hbound
  -- Tychonoff: the restrictions `q ↦ F j q` lie in the compact box `∏_{q ∈ ℚ} [-C, C]`, and
  -- `ℚ → ℝ` is first countable, so some subsequence converges pointwise on `ℚ` to `g`.
  have hK : IsCompact (univ.pi fun _ : ℚ => Icc (-C) C) := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨g, hgK, ψ, hψ, hlim⟩ := hK.tendsto_subseq (x := fun j (q : ℚ) => F j q)
    fun j => mem_univ_pi.mpr fun q => abs_le.mp (hbound j q)
  have hconv : ∀ q : ℚ, Tendsto (fun j => F (ψ j) q) atTop (𝓝 (g q)) :=
    fun q => tendsto_pi_nhds.mp hlim q
  have hgC : ∀ q, g q ≤ C := fun q => (mem_univ_pi.mp hgK q).2
  -- `g` is nondecreasing on `ℚ`, as a pointwise limit of nondecreasing functions.
  have hgmono : Monotone g := fun q q' h =>
    le_of_tendsto_of_tendsto' (hconv q) (hconv q') fun j => hmono (ψ j) (Rat.cast_le.mpr h)
  -- The left envelope `F⁻(t) = sup_{q < t} g(q)`: `g(q) ≤ F⁻(t)` for `q < t` and
  -- `F⁻(t) ≤ g(q)` for `t ≤ q`.
  obtain ⟨Fm, hFa, hFb⟩ : ∃ Fm : ℝ → ℝ, (∀ (q : ℚ) (t : ℝ), (q : ℝ) < t → g q ≤ Fm t) ∧
      ∀ (q : ℚ) (t : ℝ), t ≤ q → Fm t ≤ g q := by
    refine ⟨fun t => ⨆ q : {q : ℚ // (q : ℝ) < t}, g q, fun q t h => ?_, fun q t h => ?_⟩
    · exact le_ciSup (f := fun q : {q : ℚ // (q : ℝ) < t} => g q)
        ⟨C, by rintro _ ⟨q', rfl⟩; exact hgC q'⟩ ⟨q, h⟩
    · obtain ⟨q₀, hq₀⟩ := exists_rat_lt t
      have : Nonempty {q : ℚ // (q : ℝ) < t} := ⟨⟨q₀, hq₀⟩⟩
      exact ciSup_le fun q' => hgmono (Rat.cast_le.mp (q'.2.le.trans h))
  -- `F⁻` is nondecreasing: compare both sides with `g(q)` for a rational `t < q < t'`.
  have hFm : Monotone Fm := by
    intro t t' h
    rcases h.lt_or_eq with h | rfl
    · obtain ⟨q, hq, hq'⟩ := exists_rat_btwn h
      exact (hFb q t hq.le).trans (hFa q t' hq')
    · exact le_rfl
  -- The exceptional set is the countable set of discontinuity points of `F⁻`.
  refine ⟨ψ, {s | ¬ContinuousAt Fm s}, hψ, hFm.countable_not_continuousAt, fun s hs ε hε => ?_⟩
  have hcont : ContinuousAt Fm s := not_not.mp hs
  obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by linarith)
  -- Rationals `s - δ < a < s < b < s + δ / 2` give `g(b) - g(a) ≤ F⁻(s + δ / 2) - F⁻(a) < ε / 2`.
  obtain ⟨a, ha, ha'⟩ := exists_rat_btwn (show s - δ < s by linarith)
  obtain ⟨b, hb, hb'⟩ := exists_rat_btwn (show s < s + δ / 2 by linarith)
  refine ⟨a, b, ha', hb, ?_⟩
  have h1 : g b ≤ Fm (s + δ / 2) := hFa b _ hb'
  have h2 : Fm a ≤ g a := hFb a a le_rfl
  have h3 := @hδs (s + δ / 2) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h4 := @hδs a (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at h3 h4
  have hgab : g b - g a < ε := by linarith [h3.2, h4.1]
  -- Pointwise convergence at `a` and `b` along `ψ`.
  exact ((hconv b).sub (hconv a)).eventually (gt_mem_nhds hgab)
/-- **Smooth cutoff of a test form between two disjoint closed sets** (the cutoffs `χω` and `ζω`
in the proof of Simon Ch. 6, 8.2, p. 176).  Normality of `ℝ^P` gives open `N₀ ⊇ C₀` and
`N₁ ⊇ C₁` with disjoint closures, and the smooth Urysohn lemma gives a `C^∞` function
`χ : ℝ^P → [0, 1]` with `χ = 0` on `closure N₀` and `χ = 1` on `closure N₁`.  Then `ω' = χ ω` is
a test form in `U` with `tsupport ω' ⊆ tsupport ω`, and `|ω - ω'| = (1 - χ) |ω| ≤ |ω|` by
homogeneity of the Euclidean coefficient norm. -/
theorem Submission.iwl_rl_testForm_smooth_cutoff : ∀ (P k : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U k) (C₀ C₁ : Set (Eucl P)), IsClosed C₀ → IsClosed C₁ → Disjoint C₀ C₁ → ∃ ω' : TestFormOn U k, (∃ N₀ : Set (Eucl P), IsOpen N₀ ∧ C₀ ⊆ N₀ ∧ ∀ x ∈ N₀, (ω' : DifferentialForm (Eucl P) k) x = 0) ∧ (∃ N₁ : Set (Eucl P), IsOpen N₁ ∧ C₁ ⊆ N₁ ∧ ∀ x ∈ N₁, (ω' : DifferentialForm (Eucl P) k) x = (ω : DifferentialForm (Eucl P) k) x) ∧ tsupport (ω' : DifferentialForm (Eucl P) k) ⊆ tsupport (ω : DifferentialForm (Eucl P) k) ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x - (ω' : DifferentialForm (Eucl P) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) := by
  intro P k U ω C₀ C₁ hC₀ hC₁ hd
  -- Step 1: by normality, open `N₁ ⊇ C₁` and `N₀ ⊇ C₀` with disjoint closures.
  obtain ⟨N₁, hN₁, hCN₁, hN₁C₀⟩ :=
    normal_exists_closure_subset hC₁ hC₀.isOpen_compl hd.subset_compl_left
  obtain ⟨N₀, hN₀, hCN₀, hN₀N₁⟩ :=
    normal_exists_closure_subset hC₀ isClosed_closure.isOpen_compl (subset_compl_comm.mp hN₁C₀)
  -- Step 2: a smooth Urysohn function `χ : ℝ^P → [0, 1]`, `0` on `closure N₀`, `1` on `closure N₁`.
  obtain ⟨χ, hχ, hχr, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    isClosed_closure isClosed_closure (subset_compl_iff_disjoint_right.mp hN₀N₁)
  -- Step 3: homogeneity of the Euclidean coefficient norm, `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- Step 4: `ω' = χ ω` is a test form in `U` with `tsupport ω' ⊆ tsupport ω`.
  let f : DifferentialForm (Eucl P) k := fun x => χ x • (ω : DifferentialForm (Eucl P) k) x
  have hfω : tsupport f ⊆ tsupport (ω : DifferentialForm (Eucl P) k) :=
    tsupport_smul_subset_right χ _
  have hf : f ∈ TestFormOn U k :=
    ⟨⟨hχ.smul ω.2.1.1, ω.2.1.2.of_isClosed_subset (isClosed_tsupport f) hfω⟩, hfω.trans ω.2.2⟩
  refine ⟨⟨f, hf⟩, ⟨N₀, hN₀, hCN₀, fun x hx => ?_⟩, ⟨N₁, hN₁, hCN₁, fun x hx => ?_⟩, hfω,
    fun x => ?_⟩
  · -- Step 5 (i): `χ = 0` on `N₀ ⊆ closure N₀`.
    change χ x • (ω : DifferentialForm (Eucl P) k) x = 0
    rw [(hχ0 x).mp (subset_closure hx), zero_smul]
  · -- (ii): `χ = 1` on `N₁ ⊆ closure N₁`.
    change χ x • (ω : DifferentialForm (Eucl P) k) x = (ω : DifferentialForm (Eucl P) k) x
    rw [(hχ1 x).mp (subset_closure hx), one_smul]
  · -- Step 6 (iv): `ω - χ ω = (1 - χ) ω` with `0 ≤ 1 - χ ≤ 1`.
    obtain ⟨h0, h1⟩ := hχr (mem_range_self x)
    change covectorEuclideanNorm
      ((ω : DifferentialForm (Eucl P) k) x - χ x • (ω : DifferentialForm (Eucl P) k) x) ≤ _
    have hsub : (ω : DifferentialForm (Eucl P) k) x - χ x • (ω : DifferentialForm (Eucl P) k) x =
        (1 - χ x) • (ω : DifferentialForm (Eucl P) k) x :=
      ((sub_smul (1 : ℝ) (χ x) ((ω : DifferentialForm (Eucl P) k) x)).trans (by rw [one_smul])).symm
    rw [hsub, hsmul, abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (by linarith)
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
/-- **Local mass along increasing unions of open sets** (continuity from below of `W ↦ M_W(T)`
on open sets, used in the selection argument of Simon Ch. 6, Remark 8.3(1), p. 176).  If
`O₀ ⊆ O₁ ⊆ ⋯` are open, then `M_{⋃ᵢ Oᵢ}(T) = supᵢ M_{Oᵢ}(T)` in `[0, ∞]`.  `≥` is monotonicity
of `M`.  For `≤`, a form admissible for `⋃ᵢ Oᵢ` has compact support, which the increasing open
cover `(Oᵢ)` covers by a single `Oᵢ`; the form is then admissible for that `Oᵢ`. -/
theorem Submission.iwl_rl_massOn_iUnion_monotone : ∀ (P k : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U k) (O : ℕ → Set (Eucl P)), (∀ i, IsOpen (O i)) → Monotone O → T.massOn (⋃ i, O i) = ⨆ i, T.massOn (O i) := by
  intro P k U T O hO hmono
  -- `≥`: each `Oᵢ ⊆ ⋃ᵢ Oᵢ`, and `M` is monotone in the support region.
  refine le_antisymm ?_ (iSup_le fun i => T.massOn_mono (subset_iUnion O i))
  -- `≤`: it suffices to bound `ofReal (T ω)` for every `ω` admissible for `⋃ᵢ Oᵢ`.
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- `tsupport ω` is compact and lies in the directed open union, hence in a single `Oᵢ`.
  obtain ⟨i, hi⟩ := IsCompact.elim_directed_cover ω.property.1.2 O hO hω.1 hmono.directed_le
  -- So `ω` is admissible for `Oᵢ`: `ofReal (T ω) ≤ M_{Oᵢ}(T) ≤ supᵢ M_{Oᵢ}(T)`.
  exact le_iSup_of_le i (T.le_massOn ⟨hi, hω.2⟩)
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

/-- **Patching lemma** (P4) of the proof of Simon Ch. 6, 8.2 (Remark 8.3(1)): a current that
agrees near every point of `U` with an integer multiplicity current is integer multiplicity.
By Lindelöf, countably many `V (e i)` cover `U`, with `X = Y (e i) = τ(Mᵢ, θᵢ, ξᵢ)` on forms
supported in `V (e i)`.  On overlaps the vector densities `1_{Mᵢ} θᵢ ξᵢ` agree `Hᵏ`-a.e. (test
with `g dx^β`, `g ∈ C_c^∞`, and expand covectors by `Submission.slicing_ru_covector_expansion`),
hence so do the multiplicities `1_{Mᵢ} θᵢ`, since `‖ξᵢ‖ = 1` a.e.
(`Submission.lpf_simple_nvector_algebra`).  The triple `(M, θ, ξ)` glued along
`D i = V (e i) \ ⋃_{j < i} V (e j)` therefore agrees a.e. with `(Mᵢ, θᵢ, ξᵢ)` on `V (e i)`;
`Submission.iwl_weighted_tangent_locality` transfers the orientation condition from `(Mᵢ, θᵢ)`
to `(M, θ)`, and `X = τ(M, θ, ξ)` by a smooth partition of unity. -/
theorem Submission.iwl_im_patching : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k, (∀ x ∈ U, ∃ V : Set (Eucl P), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y ∧ ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = Y ω) → IsIntegerMultiplicity X := by
  intro P k U hU X hloc
  -- Empty domain: `X = 0 = τ(∅, 1, 0)`.
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · refine ⟨∅, fun _ => 1, fun _ => 0, ⟨Subset.rfl, nullMeasurableSet_empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
      fun x hx => absurd hx (notMem_empty x), fun K _ _ => by simp,
      aestronglyMeasurable_const,
      ae_restrict_of_forall_mem MeasurableSet.empty fun x hx => absurd hx (notMem_empty x)⟩,
      fun x hx => absurd hx (notMem_empty x), fun ω => ?_⟩
    have hω : ω = 0 := by
      apply Subtype.ext
      funext x
      exact image_eq_zero_of_notMem_tsupport fun hx => notMem_empty x (ω.2.2 hx)
    rw [hω, tauAction, Measure.restrict_empty, integral_zero_measure]
    exact map_zero X.toCurrent
  -- Fact (a): `‖ξ‖ = 1` `Hᵏ`-a.e. on `M`.  A.e. `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ` orthonormal, and
  -- `‖τ₁ ∧ ⋯ ∧ τₖ‖² = det (⟪τᵢ, τⱼ⟫) = 1`.
  have norm_eq_one : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ} {ξ : Eucl P → NVector (Eucl P) k},
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ M → ‖ξ x‖ = 1 := by
    intro M θ ξ h
    rw [← ae_restrict_iff'₀ h.nullMeasurableSet]
    filter_upwards [h.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hgram : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext i j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
    have hsq := Submission.lpf_simple_nvector_algebra.1 P k τ
    rw [hgram, Matrix.det_one] at hsq
    have h1 : ‖simpleNVector τ‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg (simpleNVector τ)) two_ne_zero).mp hsq
    rcases hξ with hξ | hξ
    · rw [hξ, h1]
    · rw [hξ, ContinuousLinearMap.opNorm_neg, h1]
  -- Fact (d): `‖1_M θ ξ‖ = 1_M θ` a.e., as `θ > 0` on `M`.
  have norm_indicator : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ} {ξ : Eucl P → NVector (Eucl P) k},
      IsRectifiableTriple U k M θ ξ → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)),
        ‖M.indicator (fun y => θ y • ξ y) x‖ = M.indicator θ x := by
    intro M θ ξ h
    filter_upwards [norm_eq_one h] with x hx
    by_cases hxM : x ∈ M
    · rw [indicator_of_mem hxM, indicator_of_mem hxM,
        @norm_smul ℝ (NVector (Eucl P) k) _ _ _ NormedSpace.toNormSMulClass, hx hxM, mul_one,
        Real.norm_of_nonneg (h.pos x hxM).le]
    · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, ContinuousLinearMap.opNorm_zero]
  -- `τ(M, θ, ξ)(ω) = ∫ ⟨ω, 1_M θ ξ⟩ dHᵏ` (Simon Ch. 6, 3.1 (‡)) for `Hᵏ`-null-measurable `M`.
  have tau_eq_integral : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ}
      {ξ : Eucl P → NVector (Eucl P) k}, NullMeasurableSet M (μHE[k] : Measure (Eucl P)) →
      ∀ ω : DifferentialForm (Eucl P) k, tauAction k M θ ξ ω =
        ∫ x, M.indicator (fun y => θ y • ξ y) x (ω x) ∂(μHE[k] : Measure (Eucl P)) := by
    intro M θ ξ hM ω
    rw [tauAction, ← integral_indicator₀ hM]
    congr 1
    funext x
    by_cases hx : x ∈ M <;> simp [hx]
  -- Fact (b): for a continuous form `η`, `⟨η, 1_M θ ξ⟩` is `Hᵏ`-integrable on each compact
  -- `K ⊆ U`, since `|⟨η, θ ξ⟩| ≤ |θ| sup_K ‖η‖` a.e. on `M ∩ K`.
  have integrableOn_pairing : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ}
      {ξ : Eucl P → NVector (Eucl P) k}, IsRectifiableTriple U k M θ ξ →
      ∀ {K : Set (Eucl P)}, IsCompact K → K ⊆ U → ∀ {η : DifferentialForm (Eucl P) k},
      Continuous η → IntegrableOn (fun x => M.indicator (fun y => θ y • ξ y) x (η x)) K
        (μHE[k] : Measure (Eucl P)) := by
    intro M θ ξ h K hK hKU η hη
    have heq : (fun x => M.indicator (fun y => θ y • ξ y) x (η x)) =
        M.indicator (fun y => θ y * ξ y (η y)) := by
      funext x
      by_cases hx : x ∈ M <;> simp [hx]
    rw [heq, integrableOn_indicator_iff h.nullMeasurableSet]
    have hθ := h.integrableOn K hK hKU
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hη.continuousOn
    have hev : Continuous fun p : NVector (Eucl P) k × Covector (Eucl P) k => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    have hmeas : AEStronglyMeasurable (fun y => ξ y (η y))
        ((μHE[k] : Measure (Eucl P)).restrict (M ∩ K)) :=
      hev.comp_aestronglyMeasurable
        ((h.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono inter_subset_left le_rfl)).prodMk hη.aestronglyMeasurable)
    refine Integrable.mono' (hθ.norm.mul_const C) (hθ.aestronglyMeasurable.mul hmeas) ?_
    rw [ae_restrict_iff'₀ (h.nullMeasurableSet.inter hK.measurableSet.nullMeasurableSet)]
    filter_upwards [norm_eq_one h] with y hy hyMK
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖ξ y (η y)‖ ≤ ‖ξ y‖ * ‖η y‖ := (ξ y).le_opNorm (η y)
      _ = ‖η y‖ := by rw [hy hyMK.1, one_mul]
      _ ≤ C := hC y hyMK.2
  -- Fact (b) for continuous `η` with compact support in `U`: `⟨η, 1_M θ ξ⟩` vanishes off
  -- `tsupport η`, so it is `Hᵏ`-integrable.
  have integrable_pairing : ∀ {M : Set (Eucl P)} {θ : Eucl P → ℝ}
      {ξ : Eucl P → NVector (Eucl P) k}, IsRectifiableTriple U k M θ ξ →
      ∀ {η : DifferentialForm (Eucl P) k}, Continuous η → HasCompactSupport η →
      tsupport η ⊆ U → Integrable (fun x => M.indicator (fun y => θ y • ξ y) x (η x))
        (μHE[k] : Measure (Eucl P)) := by
    intro M θ ξ h η hη hηc hηU
    have hsupp : (Function.support fun x => M.indicator (fun y => θ y • ξ y) x (η x)) ⊆
        tsupport η := by
      intro x hx
      by_contra hxη
      apply hx
      dsimp only
      rw [image_eq_zero_of_notMem_tsupport hxη, map_zero]
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    exact integrableOn_pairing h hηc hηU hη
  -- Fact (c), uniqueness of the vector measure `θ ξ Hᵏ ⌞ M`: if `τ(M, θ, ξ)` and `τ(M', θ', ξ')`
  -- agree on test forms supported in an open `O ⊆ U`, then `1_M θ ξ = 1_{M'} θ' ξ'` a.e. on `O`.
  -- For a constant covector `α`, testing with `ω = g α` (`g ∈ C_c^∞(O)`) shows that the locally
  -- integrable `⟨α, 1_M θ ξ - 1_{M'} θ' ξ'⟩` vanishes as a distribution on `O`, hence a.e. on
  -- `O`; the coordinate covectors `dx^β` determine an `n`-vector.
  have ae_eq : ∀ {O : Set (Eucl P)}, IsOpen O → O ⊆ U → ∀ {M M' : Set (Eucl P)}
      {θ θ' : Eucl P → ℝ} {ξ ξ' : Eucl P → NVector (Eucl P) k},
      IsRectifiableTriple U k M θ ξ → IsRectifiableTriple U k M' θ' ξ' →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M θ ξ ω = tauAction k M' θ' ξ' ω) →
      ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
        M.indicator (fun y => θ y • ξ y) x = M'.indicator (fun y => θ' y • ξ' y) x := by
    intro O hO hOU M M' θ θ' ξ ξ' h h' heq
    have hcoord : ∀ α : Covector (Eucl P) k, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ O →
        M.indicator (fun y => θ y • ξ y) x α = M'.indicator (fun y => θ' y • ξ' y) x α := by
      intro α
      have hli : LocallyIntegrableOn (fun x => M.indicator (fun y => θ y • ξ y) x α -
          M'.indicator (fun y => θ' y • ξ' y) x α) O (μHE[k] : Measure (Eucl P)) := by
        rw [locallyIntegrableOn_iff hO.isLocallyClosed]
        intro K hKO hK
        exact (integrableOn_pairing h hK (hKO.trans hOU) (η := fun _ => α)
          continuous_const).sub
          (integrableOn_pairing h' hK (hKO.trans hOU) (η := fun _ => α) continuous_const)
      have key := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
      · filter_upwards [key] with x hx hxO
        exact sub_eq_zero.mp (hx hxO)
      intro g hg hgc hgO
      have hηc : Continuous fun x => g x • α := hg.continuous.smul continuous_const
      have hηcs : HasCompactSupport fun x => g x • α := hgc.smul_right (f' := fun _ => α)
      have hηO : tsupport (fun x => g x • α) ⊆ O := (tsupport_smul_subset_left _ _).trans hgO
      have h1 := integrable_pairing h hηc hηcs (hηO.trans hOU)
      have h2 := integrable_pairing h' hηc hηcs (hηO.trans hOU)
      have heqα := heq ⟨fun x => g x • α, ⟨hg.smul contDiff_const, hηcs⟩, hηO.trans hOU⟩ hηO
      rw [tau_eq_integral h.nullMeasurableSet, tau_eq_integral h'.nullMeasurableSet] at heqα
      calc ∫ x, g x • (M.indicator (fun y => θ y • ξ y) x α -
            M'.indicator (fun y => θ' y • ξ' y) x α) ∂(μHE[k] : Measure (Eucl P))
          = ∫ x, (M.indicator (fun y => θ y • ξ y) x (g x • α) -
              M'.indicator (fun y => θ' y • ξ' y) x (g x • α)) ∂(μHE[k] : Measure (Eucl P)) := by
            congr 1
            funext x
            simp only [map_smul, smul_eq_mul, mul_sub]
        _ = ∫ x, M.indicator (fun y => θ y • ξ y) x (g x • α) ∂(μHE[k] : Measure (Eucl P)) -
              ∫ x, M'.indicator (fun y => θ' y • ξ' y) x (g x • α)
                ∂(μHE[k] : Measure (Eucl P)) := integral_sub h1 h2
        _ = 0 := sub_eq_zero.mpr heqα
    have hall := ae_all_iff.mpr fun β : SimonMultiIndex k P =>
      hcoord (wedgeCovectors k fun j => EuclideanSpace.proj (β j))
    filter_upwards [hall] with x hx hxO
    refine ContinuousLinearMap.ext fun α => ?_
    rw [Submission.slicing_ru_covector_expansion P k α, map_sum, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_smul, map_smul, hx β hxO]
  -- Step 1 (Lindelöf): countably many `V (e i)` cover `U`.
  have hloc' : ∀ x : U, ∃ V : Set (Eucl P), IsOpen V ∧ (x : Eucl P) ∈ V ∧ V ⊆ U ∧
      ∃ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y ∧
        ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V → X ω = Y ω :=
    fun x => hloc x x.2
  choose V hVo hxV hVU Y hY hXY using hloc'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcovT : ∀ y ∈ U, ∃ x ∈ T, y ∈ V x := by
    intro y hy
    have hy' : y ∈ ⋃ x ∈ T, V x := by
      rw [hTU]
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
    simpa only [mem_iUnion, exists_prop] using hy'
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨x₀, hx₀T, -⟩ := hcovT y₀ hy₀
  obtain ⟨e, rfl⟩ := hTc.exists_eq_range ⟨x₀, hx₀T⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Set (Eucl P), ∀ i, W i = V (e i) := ⟨_, fun _ => rfl⟩
  have hWo : ∀ i, IsOpen (W i) := fun i => by rw [hW]; exact hVo (e i)
  have hWU : ∀ i, W i ⊆ U := fun i => by rw [hW]; exact hVU (e i)
  have hcov : ∀ x ∈ U, ∃ i, x ∈ W i := by
    intro x hx
    obtain ⟨_, ⟨i, rfl⟩, hxi⟩ := hcovT x hx
    exact ⟨i, by rw [hW]; exact hxi⟩
  -- The local integer multiplicity triples `Y (e i) = τ(Mᵢ, θᵢ, ξᵢ)`.
  have hY' : ∀ i, ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k),
      IsRectifiableTriple U k M θ ξ ∧ (∀ x ∈ M, ∃ n : ℕ, θ x = n) ∧
        ∀ ω : TestFormOn U k, Y (e i) ω = tauAction k M θ ξ ω := fun i => hY (e i)
  choose Ms θs ξs hTr hNat hRep using hY'
  have hXW : ∀ i (ω : TestFormOn U k), tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W i →
      X ω = tauAction k (Ms i) (θs i) (ξs i) ω := fun i ω hω =>
    (hXY (e i) ω (by rw [← hW]; exact hω)).trans (hRep i ω)
  -- Step 2: the local triples agree a.e. on overlaps (facts (c), (d)).
  have hcompat : ∀ i j, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ W i ∩ W j →
      (Ms i).indicator (fun y => θs i y • ξs i y) x =
        (Ms j).indicator (fun y => θs j y • ξs j y) x ∧
      (Ms i).indicator (θs i) x = (Ms j).indicator (θs j) x := by
    intro i j
    have hF := ae_eq ((hWo i).inter (hWo j)) (inter_subset_left.trans (hWU i)) (hTr i) (hTr j)
      fun ω hω => (hXW i ω (hω.trans inter_subset_left)).symm.trans
        (hXW j ω (hω.trans inter_subset_right))
    filter_upwards [hF, norm_indicator (hTr i), norm_indicator (hTr j)] with x h1 h2 h3 hx
    refine ⟨h1 hx, ?_⟩
    rw [← h2, ← h3, h1 hx]
  -- Step 3: glue along `D i = {x ∈ U | i is the least index with x ∈ W i}`.
  obtain ⟨idx, hidx⟩ : ∃ idx : Eucl P → ℕ, ∀ x, idx x = sInf {i | x ∈ W i} :=
    ⟨_, fun _ => rfl⟩
  have hidx_mem : ∀ x ∈ U, x ∈ W (idx x) := fun x hx => by
    rw [hidx]
    exact Nat.sInf_mem (hcov x hx)
  have hidx_le : ∀ x i, x ∈ W i → idx x ≤ i := fun x i hx => by
    rw [hidx]
    exact Nat.sInf_le hx
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Set (Eucl P), ∀ i, D i = {x | x ∈ U ∧ idx x = i} :=
    ⟨_, fun _ => rfl⟩
  have hmemD : ∀ x ∈ U, x ∈ D (idx x) := fun x hx => by
    rw [hD]
    exact ⟨hx, rfl⟩
  have hDU : ∀ i, D i ⊆ U := fun i x hx => by
    rw [hD] at hx
    exact hx.1
  have hidxD : ∀ i x, x ∈ D i → idx x = i := fun i x hx => by
    rw [hD] at hx
    exact hx.2
  have hDW : ∀ i, D i ⊆ W i := fun i x hx => by
    rw [← hidxD i x hx]
    exact hidx_mem x (hDU i hx)
  have hDmeas : ∀ i, MeasurableSet (D i) := by
    intro i
    have hDeq : D i = W i \ ⋃ j ∈ Finset.range i, W j := by
      ext x
      simp only [Set.mem_sdiff, mem_iUnion, Finset.mem_range, exists_prop, not_exists, not_and]
      constructor
      · intro hx
        refine ⟨hDW i hx, fun j hj hxj => ?_⟩
        have := hidx_le x j hxj
        rw [hidxD i x hx] at this
        omega
      · rintro ⟨hxi, hnot⟩
        rw [hD]
        refine ⟨hWU i hxi, le_antisymm (hidx_le x i hxi) ?_⟩
        by_contra hlt
        exact hnot _ (not_le.mp hlt) (hidx_mem x (hWU i hxi))
    rw [hDeq]
    exact (hWo i).measurableSet.diff
      (Finset.measurableSet_biUnion _ fun j _ => (hWo j).measurableSet)
  obtain ⟨M, hM⟩ : ∃ M : Set (Eucl P), M = ⋃ i, D i ∩ Ms i := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : Eucl P → ℝ, ∀ x, θ x = θs (idx x) x := ⟨_, fun _ => rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Eucl P → NVector (Eucl P) k, ∀ x, ξ x = ξs (idx x) x :=
    ⟨_, fun _ => rfl⟩
  have hMD : ∀ i x, x ∈ D i → (x ∈ M ↔ x ∈ Ms i) := by
    intro i x hx
    rw [hM, mem_iUnion]
    constructor
    · rintro ⟨j, hxj, hxM⟩
      rwa [← hidxD j x hxj, hidxD i x hx] at hxM
    · exact fun hxM => ⟨i, hx, hxM⟩
  have hθD : ∀ i x, x ∈ D i → θ x = θs i x := fun i x hx => by rw [hθ, hidxD i x hx]
  have hξD : ∀ i x, x ∈ D i → ξ x = ξs i x := fun i x hx => by rw [hξ, hidxD i x hx]
  have hFD : ∀ i x, x ∈ D i →
      M.indicator (fun y => θ y • ξ y) x = (Ms i).indicator (fun y => θs i y • ξs i y) x ∧
      M.indicator θ x = (Ms i).indicator (θs i) x := by
    intro i x hx
    by_cases hxM : x ∈ Ms i
    · have hxM' : x ∈ M := (hMD i x hx).mpr hxM
      simp only [indicator_of_mem hxM, indicator_of_mem hxM', hθD i x hx, hξD i x hx, and_self]
    · have hxM' : x ∉ M := fun h => hxM ((hMD i x hx).mp h)
      simp only [indicator_of_notMem hxM, indicator_of_notMem hxM', and_self]
  -- Step 4: on `W i` the glued triple agrees a.e. with the `i`-th one.
  have hagree : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ W i →
      M.indicator (fun y => θ y • ξ y) x = (Ms i).indicator (fun y => θs i y • ξs i y) x ∧
      M.indicator θ x = (Ms i).indicator (θs i) x := by
    intro i
    filter_upwards [ae_all_iff.mpr fun j => hcompat j i] with x hx hxi
    have hxU := hWU i hxi
    obtain ⟨h1, h2⟩ := hFD _ x (hmemD x hxU)
    obtain ⟨h3, h4⟩ := hx (idx x) ⟨hidx_mem x hxU, hxi⟩
    exact ⟨h1.trans h3, h2.trans h4⟩
  -- Step 6: `(M, θ, ξ)` is a rectifiable triple.
  have hMnull : NullMeasurableSet M (μHE[k] : Measure (Eucl P)) := by
    rw [hM]
    exact NullMeasurableSet.iUnion fun i =>
      (hDmeas i).nullMeasurableSet.inter (hTr i).nullMeasurableSet
  have hMU : M ⊆ U := by
    rw [hM]
    exact iUnion_subset fun i => inter_subset_left.trans (hDU i)
  have hGloc : LocallyIntegrableOn (M.indicator θ) U (μHE[k] : Measure (Eucl P)) := by
    intro x hxU
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp (hWo (idx x)) x (hidx_mem x hxU)
    have hsub : closedBall x (ε / 2) ⊆ W (idx x) :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεW
    refine ⟨closedBall x (ε / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hε)), ?_⟩
    have hint : IntegrableOn ((Ms (idx x)).indicator (θs (idx x))) (closedBall x (ε / 2))
        (μHE[k] : Measure (Eucl P)) := by
      rw [integrableOn_indicator_iff (hTr _).nullMeasurableSet]
      exact (hTr _).integrableOn _ (isCompact_closedBall x _) (hsub.trans (hWU _))
    refine hint.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (hagree (idx x)),
      ae_restrict_mem measurableSet_closedBall] with y hy hyB
    exact (hy (hsub hyB)).2.symm
  have hθint : ∀ K, IsCompact K → K ⊆ U →
      IntegrableOn θ (M ∩ K) (μHE[k] : Measure (Eucl P)) := by
    intro K hK hKU
    rw [← integrableOn_indicator_iff hMnull]
    exact hGloc.integrableOn_compact_subset hKU hK
  have hTriple : IsRectifiableTriple U k M θ ξ := by
    refine ⟨hMU, hMnull, ?_, ?_, hθint, ?_, ?_⟩
    · refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion Ms fun i =>
        (hTr i).countablyRectifiable).mono ?_
      rw [hM]
      exact iUnion_mono fun i => inter_subset_right
    · intro x hx
      rw [hM, mem_iUnion] at hx
      obtain ⟨i, hxD, hxM⟩ := hx
      rw [hθD i x hxD]
      exact (hTr i).pos x hxM
    · have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) k) :=
        ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
      rw [hM, aestronglyMeasurable_iUnion_iff]
      intro i
      refine ((hTr i).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)).congr ?_
      filter_upwards [ae_restrict_mem₀
        ((hDmeas i).nullMeasurableSet.inter (hTr i).nullMeasurableSet)] with x hx
      exact (hξD i x hx.1).symm
    · have key : ∀ i, ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)).restrict (D i ∩ Ms i),
          ∃ τ : Fin k → Eucl P, Orthonormal ℝ τ ∧
            HasWeightedApproximateTangentSpaceAt k M θ x (Submodule.span ℝ (range τ)) ∧
            (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
        intro i
        filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right (hTr i).orients,
          ae_restrict_mem₀ ((hDmeas i).nullMeasurableSet.inter (hTr i).nullMeasurableSet)]
          with x hx hxDM
        obtain ⟨τ, hτ, hT, hξx⟩ := hx
        obtain ⟨hxD, -⟩ := hxDM
        refine ⟨τ, hτ, ?_, by rwa [hξD i x hxD]⟩
        -- Transfer the tangent plane from `(Mᵢ, θᵢ)` to `(M, θ)` by tangent locality.
        obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp (hWo i) x (hDW i hxD)
        have hρ : 0 < ε / 2 := half_pos hε
        have hsub : closedBall x (ε / 2) ⊆ W i :=
          (closedBall_subset_ball (half_lt_self hε)).trans hεW
        refine (Submission.iwl_weighted_tangent_locality P k (Ms i) M (θs i) θ x
          (hTr i).nullMeasurableSet hMnull (hθD i x hxD).symm
          ⟨ε / 2, hρ, (hTr i).integrableOn _ (isCompact_closedBall x _) (hsub.trans (hWU i)),
            hθint _ (isCompact_closedBall x _) (hsub.trans (hWU i))⟩ ?_ _).mp hT
        intro R hR
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
        have hRr : R * r ≤ ε / 2 := by
          have := (lt_div_iff₀ hR).mp hr.2
          linarith [mul_comm R r]
        have hae : ∀ᵐ z ∂(μHE[k] : Measure (Eucl P)).restrict (closedBall x (R * r)),
            ‖(Ms i).indicator (θs i) z - M.indicator θ z‖ₑ = 0 := by
          filter_upwards [ae_restrict_of_ae (hagree i),
            ae_restrict_mem measurableSet_closedBall] with z hz hzB
          rw [(hz (hsub (closedBall_subset_closedBall hRr hzB))).2, sub_self, enorm_zero]
        rw [lintegral_congr_ae hae, lintegral_zero, mul_zero]
      have := (ae_restrict_iUnion_iff (fun i => D i ∩ Ms i) _).mpr key
      rwa [← hM] at this
  -- Step 5: `X = τ(M, θ, ξ)` on forms supported in some `W i`, hence on all forms.
  have hXloc : ∀ i (ω : TestFormOn U k), tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W i →
      X ω = tauAction k M θ ξ ω := by
    intro i ω hω
    rw [hXW i ω hω, tau_eq_integral (hTr i).nullMeasurableSet, tau_eq_integral hMnull]
    refine integral_congr_ae ?_
    filter_upwards [hagree i] with x hx
    by_cases hxW : x ∈ W i
    · rw [(hx hxW).1]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hω h), map_zero, map_zero]
  refine ⟨M, θ, ξ, hTriple, ?_, fun ω => ?_⟩
  · intro x hx
    rw [hM, mem_iUnion] at hx
    obtain ⟨i, hxD, hxM⟩ := hx
    rw [hθD i x hxD]
    exact hNat i x hxM
  -- A smooth partition of unity `(ρᵢ)` subordinate to a finite subcover of `tsupport ω` splits
  -- `ω = ∑ ρᵢ ω`; `X` is linear and `τ(M, θ, ξ)` is additive on the integrable pieces.
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) := ω.2.1.1
  have hωc : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
  have hωU : tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U := ω.2.2
  obtain ⟨t, ht⟩ := hωc.isCompact.elim_finite_subcover W hWo
    (hωU.trans fun x hx => mem_iUnion.mpr (hcov x hx))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ (Eucl P))
    (isClosed_tsupport (ω : DifferentialForm (Eucl P) k)) (fun i : t => W i) (fun i => hWo i)
    (by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  have hρs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i =>
    contMDiff_iff_contDiff.mp (ρ i).contMDiff
  let ωi : t → TestFormOn U k := fun i =>
    ⟨fun x => ρ i x • (ω : DifferentialForm (Eucl P) k) x,
      ⟨(hρs i).smul hωs, IsCompact.of_isClosed_subset hωc (isClosed_tsupport _)
        (tsupport_smul_subset_right _ _)⟩, (tsupport_smul_subset_right _ _).trans hωU⟩
  have hsum' : ∀ x, (ω : DifferentialForm (Eucl P) k) x =
      ∑ i, ρ i x • (ω : DifferentialForm (Eucl P) k) x := by
    intro x
    by_cases hx : x ∈ tsupport (ω : DifferentialForm (Eucl P) k)
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one hx, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [hsum' x, Submodule.coe_sum, Finset.sum_apply]
  have hint : ∀ i, Integrable (fun x => M.indicator (fun y => θ y • ξ y) x
      ((ωi i : DifferentialForm (Eucl P) k) x)) (μHE[k] : Measure (Eucl P)) := fun i =>
    integrable_pairing hTriple (ωi i).2.1.1.continuous (ωi i).2.1.2 (ωi i).2.2
  calc X ω = ∑ i, X (ωi i) := by
        conv_lhs => rw [hsum]
        exact map_sum X.toCurrent _ _
    _ = ∑ i, tauAction k M θ ξ (ωi i) :=
        Finset.sum_congr rfl fun i _ =>
          hXloc i (ωi i) ((tsupport_smul_subset_left _ _).trans (hρ i))
    _ = tauAction k M θ ξ ω := by
        simp only [tau_eq_integral hMnull]
        rw [← integral_finsetSum _ fun i _ => hint i]
        congr 1
        funext x
        rw [hsum' x, map_sum]

/-- Simon Ch. 6, 8.2 in the case `n = 0` (p. 176, "the theorem is trivial in case `n = 0`"): a
weak limit `X` of integer multiplicity `X_j ∈ 𝒟₀(U)` with `sup_j M_W(X_j) < ∞` for all `W ⊂⊂ U` is
integer multiplicity.  Each `X_j = τ(M_j, θ_j, ξ_j)` is a locally finite sum
`X_j(ω) = ∑_{x ∈ M_j} c_j(x) ω(x)` with `c_j = ±θ_j ∈ ℤ ∖ {0}`, and testing with signed bumps gives
`∑_{x ∈ S} |c_j(x)| ≤ M_W(X_j)` for finite `S ⊆ M_j ∩ W`.  On `W = B_{ε/2}(x₀) ⊂⊂ U`,
`br_zd_dirac_local_limit` makes `X` a finite integer Dirac sum on forms supported in `W`, which is
integer multiplicity by `br_zd_finite_dirac_im`, and `iwl_im_patching` globalizes. -/
theorem Submission.iwl_zero_dim_integrality : ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U 0) (X : GeometricCurrentOn U 0), (∀ j, IsIntegerMultiplicity (Xj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, (Xj j).massOn W) < ∞) → WeaklyConvergesOn Xj X → IsIntegerMultiplicity X := by
  classical
  intro P U hU Xj X hXj hmass hconv
  -- Step 1: an integer multiplicity `Y = τ(M, θ, ξ) ∈ 𝒟₀(U)` is `Y(ω) = ∑ᶠ_{x ∈ M} c(x) ω(x)(![])`
  -- with `c(x) ≠ 0` on `M` and `M ∩ K` finite for compact `K ⊆ U`.
  have hrepr : ∀ Y : GeometricCurrentOn U 0, IsIntegerMultiplicity Y →
      ∃ (N : Set (Eucl P)) (c : Eucl P → ℤ),
        (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) ∧ (∀ x ∈ N, c x ≠ 0) ∧
          ∀ ω : TestFormOn U 0,
            Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![] := by
    rintro Y ⟨M, θ, ξ, hT, hθ, hY⟩
    set μ : Measure (Eucl P) := (μHE[0] : Measure (Eucl P)) with hμ
    -- `H⁰ = μH[0]` gives every point mass `1`.
    have hpt : ∀ x : Eucl P, μ {x} = 1 := fun x => by
      rw [hμ, Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
    -- `H⁰`-null sets are empty.
    have hnull : ∀ E : Set (Eucl P), μ E = 0 → E = ∅ := by
      intro E hE
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have h1 := measure_mono (μ := μ) (singleton_subset_iff.2 hx)
      rw [hpt, hE] at h1
      exact absurd h1 (by simp)
    -- `H⁰` of a finset is its cardinality.
    have hcard : ∀ F : Finset (Eucl P), μ (F : Set (Eucl P)) = F.card := by
      intro F
      rw [← sum_measure_singleton]
      simp [hpt]
    -- Sets of finite `H⁰` measure are finite.
    have hfin : ∀ E : Set (Eucl P), μ E < ∞ → E.Finite := by
      intro E hE
      by_contra hinf
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hE.ne
      obtain ⟨F, hFE, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
      have h1 := measure_mono (μ := μ) hFE
      rw [hcard, hFcard] at h1
      exact absurd (h1.trans_lt hn) (lt_irrefl _)
    -- Integrals over finsets are finite sums.
    have hint : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
        IntegrableOn g (F : Set (Eucl P)) μ := by
      intro F g
      rw [← biUnion_of_singleton (F : Set (Eucl P)), Finset.set_biUnion_coe,
        integrableOn_finset_iUnion]
      exact fun x _ => integrableOn_singleton (hx := by rw [hpt]; exact ENNReal.one_lt_top)
    have hsum : ∀ (F : Finset (Eucl P)) (g : Eucl P → ℝ),
        ∫ x in (F : Set (Eucl P)), g x ∂μ = ∑ x ∈ F, g x := by
      intro F g
      rw [setIntegral_finset F (hint F g)]
      simp only [measureReal_def, hpt, ENNReal.toReal_one, one_smul]
    -- `θ ≥ 1` on `M`.
    have hθ1 : ∀ x ∈ M, (1 : ℝ) ≤ θ x := by
      intro x hx
      obtain ⟨k, hk⟩ := hθ x hx
      have hpos := hT.pos x hx
      rw [hk] at hpos ⊢
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hpos)
    -- Local finiteness: `H⁰(M ∩ K) ≤ ∫_{M ∩ K} θ dH⁰ < ∞`.
    have hlocfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (M ∩ K).Finite := by
      intro K hK hKU
      apply hfin
      have hMK : NullMeasurableSet (M ∩ K) μ :=
        hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
      have h1 : IntegrableOn (fun _ => (1 : ℝ)) (M ∩ K) μ := by
        refine (hT.integrableOn K hK hKU).mono' aestronglyMeasurable_const ?_
        filter_upwards [ae_restrict_mem₀ hMK] with x hx
        simpa using hθ1 x hx.1
      rcases (integrableOn_const_iff (by simp)).1 h1 with h | h
      · simp at h
      · exact h
    -- Orientation at every point of `M`: its failure set is `H⁰`-null in `M`, hence empty.
    set ε : NVector (Eucl P) 0 := simpleNVector (![] : Fin 0 → Eucl P) with hε
    have horient : ∀ x ∈ M, ξ x = ε ∨ ξ x = -ε := by
      have h := hT.orients
      rw [Filter.Eventually, mem_ae_iff] at h
      have h2 := Measure.le_restrict_apply (μ := μ) (s := M) _ |>.trans_eq h
      rw [nonpos_iff_eq_zero] at h2
      have h3 := hnull _ h2
      intro x hx
      have hx' : x ∉ {x | ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
          HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
          (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)}ᶜ := by
        intro hmem
        have : x ∈ ({x | ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
          HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
          (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)}ᶜ ∩ M) := ⟨hmem, hx⟩
        rw [h3] at this
        exact this
      rw [Set.notMem_compl_iff] at hx'
      obtain ⟨τ, -, -, hτ⟩ := hx'
      rwa [Subsingleton.elim τ ![]] at hτ
    -- The unit `0`-covector `1`: every `0`-covector is `α = α(![]) • 1`.
    set one0 : Covector (Eucl P) 0 :=
      ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) 1 with hone0
    have hdecomp : ∀ (α : Covector (Eucl P) 0), α = α ![] • one0 := by
      intro α
      ext v
      rw [Subsingleton.elim v ![]]
      simp [one0]
    have hpair : ∀ (w : NVector (Eucl P) 0) (α : Covector (Eucl P) 0),
        w α = α ![] * w one0 := by
      intro w α
      conv_lhs => rw [hdecomp α]
      rw [map_smul, smul_eq_mul]
    -- The coefficients `c(x) = ⌊θ(x) ξ(x)(1)⌋`, equal to `±θ(x) ∈ ℤ ∖ {0}` on `M`.
    let c : Eucl P → ℤ := fun x => ⌊θ x * ξ x one0⌋
    have hcM : ∀ x ∈ M, (c x : ℝ) = θ x * ξ x one0 ∧ c x ≠ 0 := by
      intro x hx
      obtain ⟨k, hk⟩ := hθ x hx
      have hk1 : (1 : ℝ) ≤ k := hk ▸ hθ1 x hx
      have hk1' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      have hεone : ε one0 = 1 := by simp [ε, one0]
      rcases horient x hx with h | h
      · have he : θ x * ξ x one0 = ((k : ℤ) : ℝ) := by rw [h, hεone, hk]; simp
        refine ⟨by simp only [c, he, Int.floor_intCast], ?_⟩
        simp only [c, he, Int.floor_intCast]
        omega
      · have he : θ x * ξ x one0 = (Int.cast (-(k : ℤ)) : ℝ) := by
          rw [h, neg_apply, hεone, hk]; simp
        refine ⟨by simp only [c, he, Int.floor_intCast], ?_⟩
        simp only [c, he, Int.floor_intCast]
        omega
    refine ⟨M, c, hlocfin, fun x hx => (hcM x hx).2, ?_⟩
    -- The integral over `M` is the finite sum over `S = M ∩ spt ω`.
    intro ω
    set f : DifferentialForm (Eucl P) 0 := (ω : DifferentialForm (Eucl P) 0) with hf
    have hKc : IsCompact (tsupport f) := ω.property.1.2
    have hKU : tsupport f ⊆ U := ω.property.2
    have hSfin : (M ∩ tsupport f).Finite := hlocfin _ hKc hKU
    set S : Finset (Eucl P) := hSfin.toFinset with hS
    have hSM : (S : Set (Eucl P)) = M ∩ tsupport f := hSfin.coe_toFinset
    have hzero : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    rw [hY ω, tauAction]
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := (S : Set (Eucl P)))
      hT.nullMeasurableSet (by rw [hSM]; exact inter_subset_left)
      (Eventually.of_forall fun x hx => ?_)]
    · rw [hsum, finsum_mem_eq_sum_of_subset _ (t := S) ?_ (by rw [hSM]; exact inter_subset_left)]
      · refine Finset.sum_congr rfl fun x hx => ?_
        have hxM : x ∈ M := by
          have : x ∈ (S : Set (Eucl P)) := hx
          rw [hSM] at this
          exact this.1
        rw [hpair, (hcM x hxM).1]
        ring
      · rintro x ⟨hxM, hx0⟩
        rw [hSM]
        refine ⟨hxM, subset_tsupport _ ?_⟩
        intro hfx
        apply hx0
        simp [hfx]
    · have hx' : x ∉ tsupport f := fun h => hx.2 (by rw [hSM]; exact ⟨hx.1, h⟩)
      have h0 : (ω : DifferentialForm (Eucl P) 0) x = 0 := hzero x hx'
      simp [h0]
  -- Step 2: if `Y(ω) = ∑ᶠ_{x ∈ N} c(x) ω(x)(![])` with `N ∩ K` finite for compact `K ⊆ U`, then
  -- `∑_{x ∈ S} |c(x)| ≤ M_W(Y)` for finite `S ⊆ N ∩ W`, `W ⊆ U` open.  Test with
  -- `ω = ∑_{x ∈ S} sign(c(x)) φₓ`, where the bumps `φₓ` (`φₓ(x) = 1`) have pairwise disjoint
  -- supports `B(x, δ) ⊆ W` meeting `N` only in `x`: then `|ω| ≤ 1` and `Y(ω) = ∑_{x ∈ S} |c(x)|`.
  have hmassge : ∀ (W N : Set (Eucl P)) (Y : GeometricCurrentOn U 0) (c : Eucl P → ℤ),
      IsOpen W → W ⊆ U → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) →
      (∀ ω : TestFormOn U 0,
        Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) →
      ∀ S : Finset (Eucl P), (↑S : Set (Eucl P)) ⊆ N ∩ W →
        ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) ≤ Y.massOn W := by
    intro W N Y c hW hWU hN hY S hS
    -- A common radius `δ > 0`: for `x ∈ S`, `B̄(x, 2δ) ⊆ W` and `N ∩ B̄(x, 2δ) = {x}`.
    have hloc : ∀ x ∈ S, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        closedBall x (2 * δ) ⊆ W ∧ ∀ y ∈ N, dist y x ≤ 2 * δ → y = x := by
      intro x hx
      obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW x (hS hx).2
      have hfin : (N ∩ closedBall x (r / 2)).Finite :=
        hN _ (isCompact_closedBall x (r / 2))
          (((closedBall_subset_ball (half_lt_self hr)).trans hrW).trans hWU)
      obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.mp
        (hfin.subset (sdiff_subset (t := {x}))).isClosed.isOpen_compl x (by simp)
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (r / 4) (ε / 4) by positivity)]
        with δ ⟨hδ0, hδ⟩
      have h1 : δ < r / 4 := hδ.trans_le (min_le_left _ _)
      have h2 : δ < ε / 4 := hδ.trans_le (min_le_right _ _)
      refine ⟨(closedBall_subset_ball (by linarith)).trans hrW, fun y hyN hyx => ?_⟩
      by_contra hne
      exact hεF (mem_ball.2 (by linarith)) ⟨⟨hyN, mem_closedBall.2 (by linarith)⟩, hne⟩
    obtain ⟨δ, hδS, hδ : 0 < δ⟩ :=
      (((Filter.eventually_all_finset S).2 hloc).and self_mem_nhdsWithin).exists
    -- Bumps `φ x` with `φ x = 1` on `B̄(x, δ/2)`, support `B(x, δ)`, and signs `s x` of `c x`.
    let φ : (x : Eucl P) → ContDiffBump x := fun x => ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
    let s : Eucl P → ℝ := fun x => if 0 ≤ (c x : ℝ) then 1 else -1
    have hφ0 : ∀ x y, δ ≤ dist y x → φ x y = 0 := fun x y h => (φ x).zero_of_le_dist h
    have hφ1 : ∀ x, φ x x = 1 := fun x =>
      (φ x).one_of_mem_closedBall (mem_closedBall_self (half_pos hδ).le)
    -- The balls `B(x, δ)`, `x ∈ S`, are pairwise disjoint.
    have hsep : ∀ x ∈ S, ∀ x' ∈ S, x' ≠ x → ∀ y, dist y x < δ → δ ≤ dist y x' := by
      intro x hx x' hx' hne y hy
      by_contra h
      refine hne ((hδS x hx).2 x' (hS hx').1 ?_)
      have := dist_triangle x' y x
      rw [dist_comm x' y] at this
      linarith
    let h : Eucl P → ℝ := fun y => ∑ x ∈ S, s x * φ x y
    have hh0 : ∀ y, h y ≠ 0 → ∃ x ∈ S, dist y x < δ := by
      intro y hy
      by_contra hcon
      exact hy (Finset.sum_eq_zero fun x hx => by
        rw [hφ0 x y (not_lt.1 fun h' => hcon ⟨x, hx, h'⟩), mul_zero])
    have hhS : ∀ x ∈ S, h x = s x := by
      intro x hx
      rw [show h x = ∑ x' ∈ S, s x' * φ x' x from rfl,
        Finset.sum_eq_single_of_mem x hx fun x' hx' hne =>
          by rw [hφ0 x' x (hsep x hx x' hx' hne x (by simpa using hδ)), mul_zero],
        hφ1, mul_one]
    have hh1 : ∀ y, |h y| ≤ 1 := by
      intro y
      by_cases hy : h y = 0
      · simp [hy]
      obtain ⟨x, hx, hyx⟩ := hh0 y hy
      rw [show h y = ∑ x' ∈ S, s x' * φ x' y from rfl,
        Finset.sum_eq_single_of_mem x hx fun x' hx' hne =>
          by rw [hφ0 x' y (hsep x hx x' hx' hne y hyx), mul_zero], abs_mul]
      have hs : |s x| = 1 := by simp only [s]; split_ifs <;> simp
      rw [hs, one_mul, abs_of_nonneg (φ x).nonneg]
      exact (φ x).le_one
    -- The test form `ω = h • 𝟙`, where `𝟙` is the `0`-covector with value `1`.
    let e : Covector (Eucl P) 0 :=
      ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) (1 : ℝ)
    let f : DifferentialForm (Eucl P) 0 := fun y => h y • e
    have hfe : ∀ y, f y ![] = h y := fun y => by simp [f, e]
    set B : Set (Eucl P) := ⋃ x ∈ S, closedBall x δ
    have hB : IsCompact B := S.isCompact_biUnion fun x _ => isCompact_closedBall x δ
    have hBW : B ⊆ W := iUnion₂_subset fun x hx =>
      (closedBall_subset_closedBall (by linarith)).trans (hδS x hx).1
    have hfB : ∀ y, y ∉ B → f y = 0 := by
      intro y hy
      by_contra hne
      obtain ⟨x, hx, hyx⟩ := hh0 y fun h0 => hne (by simp [f, h0])
      exact hy (mem_iUnion₂.2 ⟨x, hx, mem_closedBall.2 hyx.le⟩)
    have hfsupp : tsupport f ⊆ B :=
      closure_minimal (fun y hy => by_contra fun hyB => hy (hfB y hyB)) hB.isClosed
    have hfsmooth : IsSmoothForm f :=
      (ContDiff.sum fun x _ => contDiff_const.mul (φ x).contDiff).smul contDiff_const
    have hfcpt : HasCompactSupport f := HasCompactSupport.intro hB hfB
    let ω : TestFormOn U 0 := ⟨f, show IsTestForm f ∧ tsupport f ⊆ U from
      ⟨⟨hfsmooth, hfcpt⟩, hfsupp.trans (hBW.trans hWU)⟩⟩
    have hadm : ω ∈ massAdmissibleOn U 0 W := by
      refine show tsupport f ⊆ W ∧ ∀ y, covectorEuclideanNorm (f y) ≤ 1 from
        ⟨hfsupp.trans hBW, fun y => ?_⟩
      -- For a `0`-covector `α`, the coefficient norm is `|α(![])|`.
      rw [covectorEuclideanNorm, Fintype.sum_unique, ite_eq_left (Subsingleton.strictMono _),
        show (fun i => EuclideanSpace.basisFun (Fin P) ℝ ((default : Fin 0 → Fin P) i)) = ![] from
          Subsingleton.elim _ _, hfe, Real.sqrt_sq_eq_abs]
      exact hh1 y
    -- Only the points of `S` contribute to `Y(ω) = ∑ᶠ_{y ∈ N} c(y) h(y)`, and `h = s` on `S`.
    have hval : Y ω = ∑ x ∈ S, |(c x : ℝ)| := by
      rw [hY]
      change ∑ᶠ y ∈ N, (c y : ℝ) * f y ![] = _
      simp_rw [hfe]
      rw [finsum_mem_eq_sum_of_inter_support_eq (fun y => (c y : ℝ) * h y) (t := S) ?_]
      · refine Finset.sum_congr rfl fun x hx => ?_
        rw [hhS x hx]
        simp only [s]
        split_ifs with h0
        · rw [mul_one, abs_of_nonneg h0]
        · rw [mul_neg_one, abs_of_neg (not_le.1 h0)]
      · ext y
        simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
        constructor
        · rintro ⟨hyN, hy⟩
          refine ⟨?_, hy⟩
          obtain ⟨x, hx, hyx⟩ := hh0 y (right_ne_zero_of_mul hy)
          rw [(hδS x hx).2 y hyN (by linarith)]
          exact hx
        · rintro ⟨hyS, hy⟩
          exact ⟨(hS hyS).1, hy⟩
    calc ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) = ENNReal.ofReal (Y ω) := by rw [hval]
      _ ≤ Y.massOn W := Y.le_massOn hadm
  -- Steps 3–7: on `W = B_{ε/2}(x₀) ⊂⊂ U`, `Λ = sup_j M_W(X_j) < ∞` bounds the coefficients of the
  -- `X_j` in `W`, so `X` agrees on forms supported in `W` with a finite integer Dirac sum, which is
  -- integer multiplicity; `iwl_im_patching` (with `k = 0`) globalizes.
  choose N c hNfin hc hN using fun j => hrepr (Xj j) (hXj j)
  refine Submission.iwl_im_patching P 0 U hU X fun x₀ hx₀ => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hWU : closure (ball x₀ (ε / 2)) ⊆ U :=
    closure_ball_subset_closedBall.trans ((closedBall_subset_ball (half_lt_self hε)).trans hεU)
  have hWcpt : IsCompact (closure (ball x₀ (ε / 2))) :=
    (isCompact_closedBall x₀ (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hΛ : (⨆ j, (Xj j).massOn (ball x₀ (ε / 2))) ≠ ∞ :=
    (hmass _ ⟨isOpen_ball, hWcpt, hWU⟩).ne
  obtain ⟨D, a, hDW, hXD⟩ := Submission.br_zd_dirac_local_limit P U (ball x₀ (ε / 2)) Xj X N c
    _ hWcpt hconv hc
    (fun j => (hNfin j _ hWcpt hWU).subset (inter_subset_inter_right _ subset_closure))
    (fun j S hS => (ENNReal.ofReal_le_iff_le_toReal hΛ).1
      ((hmassge _ (N j) (Xj j) (c j) isOpen_ball (subset_closure.trans hWU) (hNfin j) (hN j) S
        hS).trans (le_iSup (fun i => (Xj i).massOn (ball x₀ (ε / 2))) j)))
    (fun j ω _ => hN j ω)
  obtain ⟨Y, hYim, hY⟩ := Submission.br_zd_finite_dirac_im P U D a
    (hDW.trans (subset_closure.trans hWU))
  exact ⟨ball x₀ (ε / 2), isOpen_ball, mem_ball_self (half_pos hε), subset_closure.trans hWU, Y,
    hYim, fun ω hω => (hXD ω hω).trans (hY ω).symm⟩
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

/-- Orientations of rectifiable triples agree up to sign on the overlap where every weighted
approximate tangent space of `(M₁, θ₁)` is one of `(M₂, θ₂)` (Simon Ch. 6, 3.1: `ξ(x)` is
`±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`).  At `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂` the `orients`
fields give orthonormal frames `τ`, `τ'` with `ξ₁(x) = ±s(τ)` and `ξ₂(x) = ±s(τ')`, where
`s = simpleNVector`.  By hypothesis `span τ` is a weighted approximate tangent space of
`(M₂, θ₂)` at `x`, so `span τ = span τ'` by uniqueness (Ch. 3, 1.7; `θ₂(x) > 0`), and
`Submission.fiw_ims_frame_sign` gives `s(τ') = ±s(τ)`. -/
theorem Submission.fiw_ims_orientation_sign :
    ∀ (P n : ℕ) (U M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ)
      (ξ₁ ξ₂ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple U n M₁ θ₁ ξ₁ → IsRectifiableTriple U n M₂ θ₂ ξ₂ →
      (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q →
          HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q) →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ξ₁ x = ξ₂ x ∨ ξ₁ x = -ξ₂ x := by
  intro P n U M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ h₁ h₂ htan
  -- Step 1: `M₁ ∩ M₂` is `Hⁿ`-null-measurable, so a.e. point of the overlap lies in it.
  have hmem : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), x ∈ M₁ ∩ M₂ :=
    ae_restrict_mem₀ (h₁.nullMeasurableSet.inter h₂.nullMeasurableSet)
  -- Step 2: both orientation conditions hold a.e. on the overlap.
  have ho₁ := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M₁ ∩ M₂ ⊆ M₁) h₁.orients
  have ho₂ := ae_restrict_of_ae_restrict_of_subset (inter_subset_right : M₁ ∩ M₂ ⊆ M₂) h₂.orients
  filter_upwards [hmem, ho₁, ho₂, htan] with x hx hx₁ hx₂ hQ
  obtain ⟨τ, hτ, hT, hξ₁⟩ := hx₁
  obtain ⟨τ', hτ', hT', hξ₂⟩ := hx₂
  -- Step 3: `span τ` is also a weighted approximate tangent space of `(M₂, θ₂)` at `x`, and
  -- `θ₂ x > 0`, so it is `span τ'`.
  have hspan : Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') :=
    (hQ _ hT).unique (h₂.pos x hx.2).ne' hT'
  -- Step 4: `s(τ') = ±s(τ)`; combine the three signs.  (`rw [neg_neg]` and `simp` do not fire
  -- on `NVector` negation at this pin, but `neg_neg` applied to a term does.)
  have hnn : ∀ v : NVector (Eucl P) n, - -v = v := fun v => neg_neg v
  rcases Submission.fiw_ims_frame_sign P n τ τ' hτ hτ' hspan with hs | hs <;>
    rcases hξ₁ with hξ₁ | hξ₁ <;> rcases hξ₂ with hξ₂ | hξ₂ <;> rw [hξ₁, hξ₂, hs] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact Or.inl (hnn _).symm
    | exact Or.inr (hnn _).symm

/-- Upper density theorem at every scale `Rr` (Simon Ch. 1, 3.6 with Remark 3.7(2)): if
`∫⁻_{S ∩ K} g dHᵏ < ∞` for every compact `K ⊆ U`, then for `Hᵏ`-a.e. `x ∈ U \ S` and every
`R > 0`, `r⁻ᵏ ∫⁻_{S ∩ B̄_{Rr}(x)} g dHᵏ → 0` as `r → 0+`.  The unit-scale case
`ρ⁻ᵏ ∫⁻_{S ∩ B̄_ρ(x)} g dHᵏ → 0` is `lpf_wtc_ae_zero_density_off_set`; the change of scale
`ρ = Rr` is `iwl_imc_quotient_rescale_tendsto_zero`. -/
theorem Submission.iwl_imc_density_zero_off_set : ∀ (P k : ℕ) (U S : Set (Eucl P)) (g : Eucl P → ℝ≥0∞), IsOpen U → NullMeasurableSet S (μHE[k] : Measure (Eucl P)) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∫⁻ y in S ∩ K, g y ∂(μHE[k] : Measure (Eucl P)) < ∞) → ∀ᵐ x ∂(μHE[k] : Measure (Eucl P)), x ∈ U → x ∉ S → ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ y in S ∩ closedBall x (R * r), g y ∂(μHE[k] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
  intro P k U S g hU hS hg
  -- Unit scale: for `Hᵏ`-a.e. `x ∈ U \ S`, `F_x(ρ) / ρᵏ → 0`, `F_x(ρ) = ∫⁻_{S ∩ B̄_ρ(x)} g dHᵏ`.
  filter_upwards [Submission.lpf_wtc_ae_zero_density_off_set P k U S g hU hS hg]
    with x hx hxU hxS R hR
  -- Change of scale `ρ = Rr`: `r⁻ᵏ F_x(Rr) → 0`.
  exact Submission.iwl_imc_quotient_rescale_tendsto_zero k
    (fun ρ => ∫⁻ y in S ∩ closedBall x ρ, g y ∂(μHE[k] : Measure (Eucl P))) (hx hxU hxS) R hR

/-- **Integer linear combinations of integer multiplicity currents (Simon Ch. 6, 3.2 Remark (1),
p. 146), given tangent comparison.**  Assume (T): for null-measurable `M₁, M₂ ⊆ U` and
`θ₁, θ₂ ≥ 1` on them, locally `Hᵏ`-integrable in `U`, at `Hᵏ`-a.e. `x ∈ M₁ ∩ M₂` every weighted
approximate tangent space of `(M₁, θ₁)` is one of `(M₂, θ₂)`.  Let `X = τ(M₁, θ₁, ξ₁)`,
`Y = τ(M₂, θ₂, ξ₂)` and `Z = aX + bY` with `a, b ∈ ℤ`.  By (T) and `fiw_ims_orientation_sign`,
`ξ₁ = ±ξ₂` a.e. on `M₁ ∩ M₂`.  With `σ = -1` on the anti-aligned part of the overlap and `1`
elsewhere, `c = a 1_{M₁}θ₁ + bσ 1_{M₂}θ₂` is integer-valued, and `Z = τ(M, θ, ξ)` for
`M = {c ≠ 0}`, `θ = |c|`, `ξ = sgn(c) ξ₀` (`ξ₀ = ξ₁` on `M₁`, `ξ₂` on `M₂ \ M₁`): a.e.
`a 1_{M₁}θ₁⟨ω, ξ₁⟩ + b 1_{M₂}θ₂⟨ω, ξ₂⟩ = 1_M θ⟨ω, ξ⟩`, integrable by
`iwl_imc_tau_measure_representation`.  (T) for `(M_l, θ_l)` and `(M, θ)` transfers the
orientations, so `(M, θ, ξ)` is a rectifiable triple. -/
theorem Submission.iwl_imc_lincomb_im : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → (∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl P)) → (∀ x ∈ M₁, 1 ≤ θ₁ x) → (∀ x ∈ M₂, 1 ≤ θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q) → ∀ (X Y Z : GeometricCurrentOn U k) (a b : ℤ), IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn U k, Z ω = (a : ℝ) * X ω + (b : ℝ) * Y ω) → IsIntegerMultiplicity Z := by
  intro P k U hU hT X Y Z a b hX hY hZ
  classical
  -- `NVector (Eucl P) k` is a normed space; instance search misses its pseudometrizability.
  have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl P) k) := by
    let u : UniformSpace (NVector (Eucl P) k) := PseudoMetricSpace.toUniformSpace
    have : (uniformity (NVector (Eucl P) k)).IsCountablyGenerated :=
      @EMetric.instIsCountablyGeneratedUniformity _ PseudoMetricSpace.toPseudoEMetricSpace
    exact @UniformSpace.pseudoMetrizableSpace _ u this
  -- Step 0: the data.
  obtain ⟨M₁, θ₁, ξ₁, h₁, hN₁, hX⟩ := hX
  obtain ⟨M₂, θ₂, ξ₂, h₂, hN₂, hY⟩ := hY
  have hge1 : ∀ (M' : Set (Eucl P)) (θ' : Eucl P → ℝ), (∀ x ∈ M', 0 < θ' x) →
      (∀ x ∈ M', ∃ n : ℕ, θ' x = n) → ∀ x ∈ M', 1 ≤ θ' x := by
    intro M' θ' hpos hnat x hx
    obtain ⟨n, hn⟩ := hnat x hx
    have hp := hpos x hx
    rw [hn] at hp ⊢
    have : 0 < n := by exact_mod_cast hp
    exact_mod_cast this
  have hθ₁1 := hge1 M₁ θ₁ h₁.pos hN₁
  have hθ₂1 := hge1 M₂ θ₂ h₂.pos hN₂
  have hM₁ := h₁.nullMeasurableSet
  have hM₂ := h₂.nullMeasurableSet
  -- Step 1: orientations agree up to sign on the overlap.
  have hsign := Submission.fiw_ims_orientation_sign P k U M₁ M₂ θ₁ θ₂ ξ₁ ξ₂ h₁ h₂
    (hT M₁ M₂ θ₁ θ₂ h₁.subset h₂.subset hM₁ hM₂ hθ₁1 hθ₂1 h₁.integrableOn h₂.integrableOn)
  rw [ae_restrict_iff'₀ (hM₁.inter hM₂)] at hsign
  -- Step 3(a): multiplicities are a.e.-strongly measurable on their carriers.
  have hθm : ∀ (M' : Set (Eucl P)) (θ' : Eucl P → ℝ), M' ⊆ U →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ' (M' ∩ K) (μHE[k] : Measure (Eucl P))) →
      AEStronglyMeasurable θ' ((μHE[k] : Measure (Eucl P)).restrict M') := by
    intro M' θ' hM'U hint
    apply LocallyIntegrableOn.aestronglyMeasurable
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x (hM'U hx)
    refine ⟨M' ∩ closedBall x (ε / 2),
      inter_mem_nhdsWithin _ (closedBall_mem_nhds x (half_pos hε)), ?_⟩
    exact hint _ (isCompact_closedBall x (ε / 2))
      ((closedBall_subset_ball (half_lt_self hε)).trans hball)
  have hθ₁m := hθm M₁ θ₁ h₁.subset h₁.integrableOn
  have hθ₂m := hθm M₂ θ₂ h₂.subset h₂.integrableOn
  -- Step 3(c): the anti-aligned part `Em` of the overlap is null-measurable.
  set B : Set (Eucl P) := {x | M₁.indicator ξ₁ x = M₂.indicator ξ₂ x} with hB
  have hBnm : NullMeasurableSet B (μHE[k] : Measure (Eucl P)) :=
    ((aestronglyMeasurable_indicator_iff₀ hM₁).2 h₁.aestronglyMeasurable).nullMeasurableSet_eq_fun
      ((aestronglyMeasurable_indicator_iff₀ hM₂).2 h₂.aestronglyMeasurable)
  set Em : Set (Eucl P) := (M₁ ∩ M₂) \ B with hEm
  have hEmnm : NullMeasurableSet Em (μHE[k] : Measure (Eucl P)) := (hM₁.inter hM₂).diff hBnm
  have hEmM₂ : Em ⊆ M₂ := fun x hx => hx.1.2
  -- Step 2: the integer multiplicity `c`, carrier `M`, `θ = |c|`, `ξ = sgn(c) • ξ₀`.
  set σ : Eucl P → ℝ := fun x => if x ∈ Em then -1 else 1 with hσ
  set c : Eucl P → ℝ := fun x =>
    (a : ℝ) * M₁.indicator θ₁ x + (b : ℝ) * (σ x * M₂.indicator θ₂ x) with hc
  set M : Set (Eucl P) := {x | c x ≠ 0} with hM
  set θ : Eucl P → ℝ := fun x => |c x| with hθ
  set ξ₀ : Eucl P → NVector (Eucl P) k := M₁.piecewise ξ₁ (M₂.indicator ξ₂) with hξ₀
  set ξ : Eucl P → NVector (Eucl P) k := fun x => (if 0 ≤ c x then (1 : ℝ) else -1) • ξ₀ x
    with hξ
  -- Measurability of `c`.
  have hσm : AEStronglyMeasurable σ (μHE[k] : Measure (Eucl P)) := by
    have h := AEStronglyMeasurable.piecewise (f := fun _ => (-1 : ℝ)) (g := fun _ => (1 : ℝ))
      hEmnm aestronglyMeasurable_const aestronglyMeasurable_const
    convert h using 1
    funext x
    simp only [hσ, Set.piecewise]
  have hcm : AEStronglyMeasurable c (μHE[k] : Measure (Eucl P)) :=
    (((aestronglyMeasurable_indicator_iff₀ hM₁).2 hθ₁m).const_mul (a : ℝ)).add
      ((hσm.mul ((aestronglyMeasurable_indicator_iff₀ hM₂).2 hθ₂m)).const_mul (b : ℝ))
  have hMnm : NullMeasurableSet M (μHE[k] : Measure (Eucl P)) := hcm.nullMeasurableSet_support
  -- `c` vanishes off `M₁ ∪ M₂`.
  have hMsub : M ⊆ M₁ ∪ M₂ := by
    intro x hx
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    apply hx
    simp [hc, hcon.1, hcon.2]
  have hMU : M ⊆ U := hMsub.trans (union_subset h₁.subset h₂.subset)
  -- Step 2(a): `c` is integer-valued.
  have hcZ : ∀ x, ∃ z : ℤ, c x = z := by
    intro x
    have hi₁ : ∃ n : ℕ, M₁.indicator θ₁ x = n := by
      by_cases hx : x ∈ M₁
      · rw [indicator_of_mem hx]; exact hN₁ x hx
      · exact ⟨0, by simp [hx]⟩
    have hi₂ : ∃ n : ℕ, M₂.indicator θ₂ x = n := by
      by_cases hx : x ∈ M₂
      · rw [indicator_of_mem hx]; exact hN₂ x hx
      · exact ⟨0, by simp [hx]⟩
    obtain ⟨n₁, hn₁⟩ := hi₁
    obtain ⟨n₂, hn₂⟩ := hi₂
    by_cases hxE : x ∈ Em
    · refine ⟨a * n₁ + b * (-1 * n₂), ?_⟩
      simp only [hc, hσ, hxE, ite_true, hn₁, hn₂]
      push_cast; ring
    · refine ⟨a * n₁ + b * (1 * n₂), ?_⟩
      simp only [hc, hσ, hxE, ite_false, hn₁, hn₂]
      push_cast; ring
  have hθN : ∀ x ∈ M, ∃ n : ℕ, θ x = n := by
    intro x _
    obtain ⟨z, hz⟩ := hcZ x
    exact ⟨z.natAbs, by simp only [hθ, hz, Nat.cast_natAbs, Int.cast_abs]⟩
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨z, hz⟩ := hcZ x
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hx (by rw [hz, Int.cast_zero])
    have h1 : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    simp only [hθ, hz, ← Int.cast_abs]
    exact_mod_cast h1
  have hθpos : ∀ x ∈ M, 0 < θ x := fun x hx => zero_lt_one.trans_le (hθ1 x hx)
  -- Step 5 (integrableOn): `|c| ≤ |a| 1_{M₁} θ₁ + |b| 1_{M₂} θ₂`.
  have hind₁ : ∀ x, 0 ≤ M₁.indicator θ₁ x := fun x =>
    Set.indicator_nonneg (fun y hy => zero_le_one.trans (hθ₁1 y hy)) x
  have hind₂ : ∀ x, 0 ≤ M₂.indicator θ₂ x := fun x =>
    Set.indicator_nonneg (fun y hy => zero_le_one.trans (hθ₂1 y hy)) x
  have habsσ : ∀ x, |σ x| = 1 := by
    intro x
    simp only [hσ]
    split_ifs <;> simp
  have hcbound : ∀ x, |c x| ≤ |(a : ℝ)| * M₁.indicator θ₁ x + |(b : ℝ)| * M₂.indicator θ₂ x := by
    intro x
    calc |c x| ≤ |(a : ℝ) * M₁.indicator θ₁ x| + |(b : ℝ) * (σ x * M₂.indicator θ₂ x)| :=
          abs_add_le _ _
      _ = |(a : ℝ)| * M₁.indicator θ₁ x + |(b : ℝ)| * M₂.indicator θ₂ x := by
          rw [abs_mul, abs_mul, abs_mul, habsσ, one_mul, abs_of_nonneg (hind₁ x),
            abs_of_nonneg (hind₂ x)]
  have hθint : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      IntegrableOn θ (M ∩ K) (μHE[k] : Measure (Eucl P)) := by
    intro K hK hKU
    have hg₁ : Integrable (M₁.indicator θ₁) ((μHE[k] : Measure (Eucl P)).restrict K) := by
      rw [integrable_indicator_iff₀ (hM₁.mono Measure.restrict_le_self), IntegrableOn,
        Measure.restrict_restrict' hK.isClosed.measurableSet]
      exact h₁.integrableOn K hK hKU
    have hg₂ : Integrable (M₂.indicator θ₂) ((μHE[k] : Measure (Eucl P)).restrict K) := by
      rw [integrable_indicator_iff₀ (hM₂.mono Measure.restrict_le_self), IntegrableOn,
        Measure.restrict_restrict' hK.isClosed.measurableSet]
      exact h₂.integrableOn K hK hKU
    have hg : IntegrableOn (fun x => |(a : ℝ)| * M₁.indicator θ₁ x +
        |(b : ℝ)| * M₂.indicator θ₂ x) (M ∩ K) (μHE[k] : Measure (Eucl P)) :=
      ((hg₁.const_mul _).add (hg₂.const_mul _)).mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)
    refine hg.mono' (continuous_abs.comp_aestronglyMeasurable hcm).restrict ?_
    exact Eventually.of_forall fun x => by
      show ‖|c x|‖ ≤ _
      rw [Real.norm_eq_abs, abs_abs]
      exact hcbound x
  -- Step 3(e): `ξ` is a.e.-strongly measurable on `M`.
  have hξm : AEStronglyMeasurable ξ ((μHE[k] : Measure (Eucl P)).restrict M) := by
    have hs : AEStronglyMeasurable (fun x => if 0 ≤ c x then (1 : ℝ) else -1)
        (μHE[k] : Measure (Eucl P)) := by
      have hmeas : Measurable (fun t : ℝ => if 0 ≤ t then (1 : ℝ) else -1) :=
        Measurable.ite measurableSet_Ici measurable_const measurable_const
      exact (hmeas.comp_aemeasurable hcm.aemeasurable).aestronglyMeasurable
    have hξ₀ : AEStronglyMeasurable ξ₀ ((μHE[k] : Measure (Eucl P)).restrict M) := by
      refine AEStronglyMeasurable.piecewise (hM₁.mono Measure.restrict_le_self) ?_ ?_
      · exact h₁.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
      · exact ((aestronglyMeasurable_indicator_iff₀ hM₂).2 h₂.aestronglyMeasurable).restrict.restrict
    exact hs.restrict.smul hξ₀
  -- Step 2(b): `θ x • ξ x` acts as `c x • ξ₀ x`.
  have hθξ : ∀ x (α : Covector (Eucl P) k), θ x * ξ x α = c x * ξ₀ x α := by
    intro x α
    simp only [hθ, hξ, smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  -- Step 5 (orients): tangent comparison between `(M_l, θ_l)` and `(M, θ)`.
  have hloc₁ := hT M₁ M θ₁ θ h₁.subset hMU hM₁ hMnm hθ₁1 hθ1 h₁.integrableOn hθint
  have hloc₂ := hT M₂ M θ₂ θ h₂.subset hMU hM₂ hMnm hθ₂1 hθ1 h₂.integrableOn hθint
  rw [ae_restrict_iff'₀ (hM₁.inter hMnm)] at hloc₁
  rw [ae_restrict_iff'₀ (hM₂.inter hMnm)] at hloc₂
  have ho₁ := (ae_restrict_iff'₀ hM₁).1 h₁.orients
  have ho₂ := (ae_restrict_iff'₀ hM₂).1 h₂.orients
  have hsgn : ∀ x, ∀ w : NVector (Eucl P) k, ∀ τ : Fin k → Eucl P,
      (w = simpleNVector τ ∨ w = -simpleNVector τ) →
      ((if 0 ≤ c x then (1 : ℝ) else -1) • w = simpleNVector τ ∨
        (if 0 ≤ c x then (1 : ℝ) else -1) • w = -simpleNVector τ) := by
    intro x w τ hw
    split_ifs
    · rw [one_smul]; exact hw
    · rcases hw with rfl | rfl
      · right
        exact ContinuousLinearMap.ext fun α => by
          simp only [smul_apply, neg_apply, smul_eq_mul,
            neg_one_mul]
      · left
        exact ContinuousLinearMap.ext fun α => by
          simp only [smul_apply, neg_apply, smul_eq_mul,
            neg_one_mul, neg_neg]
  have horient : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∃ τ : Fin k → Eucl P,
      Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k M θ x (Submodule.span ℝ (range τ)) ∧
      (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ) := by
    rw [ae_restrict_iff'₀ hMnm]
    filter_upwards [hloc₁, hloc₂, ho₁, ho₂] with x hl₁ hl₂ hx₁ hx₂ hxM
    by_cases hxM₁ : x ∈ M₁
    · obtain ⟨τ, hτ, hTx, hξτ⟩ := hx₁ hxM₁
      refine ⟨τ, hτ, hl₁ ⟨hxM₁, hxM⟩ _ hTx, ?_⟩
      have h0 : ξ₀ x = ξ₁ x := by simp only [hξ₀, Set.piecewise_eq_of_mem _ _ _ hxM₁]
      simp only [hξ, h0]
      exact hsgn x _ τ hξτ
    · have hxM₂ : x ∈ M₂ := (hMsub hxM).resolve_left hxM₁
      obtain ⟨τ, hτ, hTx, hξτ⟩ := hx₂ hxM₂
      refine ⟨τ, hτ, hl₂ ⟨hxM₂, hxM⟩ _ hTx, ?_⟩
      have h0 : ξ₀ x = ξ₂ x := by
        simp only [hξ₀, Set.piecewise_eq_of_notMem _ _ _ hxM₁, indicator_of_mem hxM₂]
      simp only [hξ, h0]
      exact hsgn x _ τ hξτ
  refine ⟨M, θ, ξ, ⟨hMU, hMnm,
    (((Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun i : ℕ => if i = 0 then M₁ else M₂)
      fun i => by split_ifs; exacts [h₁.countablyRectifiable, h₂.countablyRectifiable])).mono
      (hMsub.trans (union_subset (subset_iUnion_of_subset 0 (by simp))
        (subset_iUnion_of_subset 1 (by simp))))),
    hθpos, hθint, hξm, horient⟩, hθN, ?_⟩
  -- Step 4: the representation `Z = τ(M, θ, ξ)`.
  intro ω
  set w : DifferentialForm (Eucl P) k := (ω : DifferentialForm (Eucl P) k) with hw
  have hrep₁ := (Submission.iwl_imc_tau_measure_representation P k U M₁ θ₁ ξ₁ X h₁ hX ω).1
  have hrep₂ := (Submission.iwl_imc_tau_measure_representation P k U M₂ θ₂ ξ₂ Y h₂ hY ω).1
  have hi₁ : IntegrableOn (fun x => θ₁ x * ξ₁ x (w x)) M₁ (μHE[k] : Measure (Eucl P)) := by
    simp only [smul_apply, smul_eq_mul] at hrep₁
    exact hrep₁
  have hi₂ : IntegrableOn (fun x => θ₂ x * ξ₂ x (w x)) M₂ (μHE[k] : Measure (Eucl P)) := by
    simp only [smul_apply, smul_eq_mul] at hrep₂
    exact hrep₂
  have hI₁ := (integrable_indicator_iff₀ hM₁).2 hi₁
  have hI₂ := (integrable_indicator_iff₀ hM₂).2 hi₂
  rw [hZ ω, hX ω, hY ω]
  unfold tauAction
  rw [← integral_indicator₀ hM₁, ← integral_indicator₀ hM₂, ← integral_indicator₀ hMnm,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hI₁.const_mul (a : ℝ)) (hI₂.const_mul (b : ℝ))]
  refine integral_congr_ae ?_
  filter_upwards [hsign] with x hx
  have hR : M.indicator (fun x => θ x * ξ x (w x)) x = c x * ξ₀ x (w x) := by
    by_cases hxM : x ∈ M
    · rw [indicator_of_mem hxM, hθξ]
    · rw [indicator_of_notMem hxM]
      have h0 : c x = 0 := by
        by_contra hne
        exact hxM hne
      rw [h0, zero_mul]
  change (a : ℝ) * M₁.indicator (fun x => θ₁ x * ξ₁ x (w x)) x +
    (b : ℝ) * M₂.indicator (fun x => θ₂ x * ξ₂ x (w x)) x =
      M.indicator (fun x => θ x * ξ x (w x)) x
  rw [hR]
  by_cases hx1 : x ∈ M₁ <;> by_cases hx2 : x ∈ M₂
  · have h0 : ξ₀ x = ξ₁ x := by simp only [hξ₀, Set.piecewise_eq_of_mem _ _ _ hx1]
    by_cases hxB : x ∈ B
    · have hxE : x ∉ Em := fun h => h.2 hxB
      have heq : ξ₁ x = ξ₂ x := by
        have h := hxB
        simp only [hB, mem_ofPred_eq, indicator_of_mem hx1, indicator_of_mem hx2] at h
        exact h
      simp only [indicator_of_mem hx1, indicator_of_mem hx2, hc, hσ, hxE, ite_false, h0, heq]
      ring
    · have hxE : x ∈ Em := ⟨⟨hx1, hx2⟩, hxB⟩
      have hneg : ξ₁ x = -ξ₂ x := by
        rcases hx ⟨hx1, hx2⟩ with h | h
        · exfalso
          apply hxB
          simp only [hB, mem_ofPred_eq, indicator_of_mem hx1, indicator_of_mem hx2]
          exact h
        · exact h
      have hα : ξ₁ x (w x) = -(ξ₂ x (w x)) := by rw [hneg, neg_apply]
      simp only [indicator_of_mem hx1, indicator_of_mem hx2, hc, hσ, hxE, ite_true, h0]
      linear_combination (b : ℝ) * θ₂ x * hα
  · have hxE : x ∉ Em := fun h => hx2 h.1.2
    have h0 : ξ₀ x = ξ₁ x := by simp only [hξ₀, Set.piecewise_eq_of_mem _ _ _ hx1]
    simp only [indicator_of_mem hx1, indicator_of_notMem hx2, hc, hσ, hxE, ite_false, h0]
    ring
  · have hxE : x ∉ Em := fun h => hx1 h.1.1
    have h0 : ξ₀ x = ξ₂ x := by
      simp only [hξ₀, Set.piecewise_eq_of_notMem _ _ _ hx1, indicator_of_mem hx2]
    simp only [indicator_of_notMem hx1, indicator_of_mem hx2, hc, hσ, hxE, ite_false, h0]
    ring
  · simp only [indicator_of_notMem hx1, indicator_of_notMem hx2, hc]
    ring

/-- Normalized Lebesgue points (Simon Ch. 1, 3.23 with Theorem 3.3): for `Hᵏ⌞M`-a.e. `x` and
every `R > 0`, `r⁻ᵏ ∫_{M ∩ B̄_{Rr}(x)} |f - f(x)| dHᵏ → 0` as `r ↓ 0`.  On a ball `W` with
`K = B̄ ⊆ U`, Lebesgue–Besicovitch differentiation for the finite measure `λ = Hᵏ⌞(M ∩ K)` makes
the `λ`-averages over `B̄_ρ(x)` tend to `0`, and density comparison gives `Θ*ᵏ(λ, x) < ∞`, so
`λ(B̄_ρ(x)) ≤ C ωₖ ρᵏ` for small `ρ`. -/
theorem Submission.iwl_imc_normalized_lebesgue_points : ∀ (P k : ℕ) (U M : Set (Eucl P)) (f : Eucl P → ℝ), IsOpen U → M ⊆ U → NullMeasurableSet M (μHE[k] : Measure (Eucl P)) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (μHE[k] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn f (M ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ y in M ∩ closedBall x (R * r), ‖f y - f x‖ₑ ∂(μHE[k] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
  intro P k U M f hU hMU hMm hfin hint
  set H : Measure (Eucl P) := (μHE[k] : Measure (Eucl P)) with hH
  -- The claim for `x` in one ball `W = B_s(y)` whose closure `K = B̄_s(y)` lies in `U`.
  have key : ∀ p : Eucl P × ℝ, closedBall p.1 p.2 ⊆ U →
      ∀ᵐ x ∂(H.restrict M), x ∈ ball p.1 p.2 → ∀ R : ℝ, 0 < R →
        Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) *
          ∫⁻ y in M ∩ closedBall x (R * r), ‖f y - f x‖ₑ ∂H) (𝓝[>] 0) (𝓝 0) := by
    rintro ⟨y, s⟩ hKU
    dsimp only at hKU ⊢
    have hK : IsCompact (closedBall y s) := isCompact_closedBall y s
    have hWK : ball y s ⊆ closedBall y s := ball_subset_closedBall
    -- `λ = Hᵏ⌞(M ∩ K)` is a finite measure and `f ∈ L¹(λ)`.
    set lam : Measure (Eucl P) := H.restrict (M ∩ closedBall y s) with hlam
    have hMK : NullMeasurableSet (M ∩ closedBall y s) H :=
      hMm.inter measurableSet_closedBall.nullMeasurableSet
    have hlamfin : IsFiniteMeasure lam := isFiniteMeasure_restrict.2 (hfin _ hK hKU).ne
    have hfl : Integrable f lam := hint _ hK hKU
    -- Lebesgue–Besicovitch differentiation along closed balls (Simon Ch. 1, 3.23).
    have hleb : ∀ᵐ x ∂lam, Tendsto (fun ρ : ℝ =>
        (∫⁻ z in closedBall x ρ, ‖f z - f x‖ₑ ∂lam) / lam (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) := by
      filter_upwards [(Besicovitch.vitaliFamily lam).ae_tendsto_lintegral_enorm_sub_div
        hfl.locallyIntegrable] with x hx
      exact hx.comp (Besicovitch.tendsto_filterAt lam x)
    have hleb' : ∀ᵐ x ∂(H.restrict M), x ∈ ball y s → Tendsto (fun ρ : ℝ =>
        (∫⁻ z in closedBall x ρ, ‖f z - f x‖ₑ ∂lam) / lam (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) := by
      rw [hlam, ae_restrict_iff'₀ hMK] at hleb
      rw [ae_restrict_iff'₀ hMm]
      filter_upwards [hleb] with x hx hxM hxW
      exact hx ⟨hxM, hWK hxW⟩
    -- `Θ*ᵏ(λ, x) < ∞` for `Hᵏ`-a.e. `x ∈ W`: density comparison (Simon Ch. 1, 3.3) with `t = ∞`.
    have hdens : ∀ᵐ x ∂(H.restrict M), x ∈ ball y s →
        dimensionalUpperDensity lam.toOuterMeasure (k : ℝ) univ x < ∞ := by
      have h0 : H {x | x ∈ ball y s ∧
          dimensionalUpperDensity lam.toOuterMeasure (k : ℝ) univ x = ∞} = 0 := by
        have h := Submission.rectifiability_density_comparison P k lam
          {x | x ∈ ball y s ∧ dimensionalUpperDensity lam.toOuterMeasure (k : ℝ) univ x = ∞}
          (ball y s) ∞ isOpen_ball (fun x hx => hx.1) (fun x hx => hx.2.ge)
        by_contra hne
        rw [ENNReal.top_mul hne] at h
        exact measure_ne_top lam _ (top_le_iff.1 h)
      refine ae_restrict_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx hxW
      exact lt_top_iff_ne_top.2 fun h => hx ⟨hxW, h⟩
    filter_upwards [hleb', hdens, ae_restrict_mem₀ hMm] with x hlebx hdensx hxM hxW R hR
    -- `λ(B̄_ρ(x)) ≤ C ωₖ ρᵏ` for small `ρ`, from `Θ*ᵏ(λ, x) < C < ∞`.
    obtain ⟨C, hC, hCtop⟩ := exists_between (hdensx hxW)
    set ω := Poincare.SimonGMT.Chapter01.realUnitBallVolume (k : ℝ) with hω
    have hω0 : ω ≠ 0 :=
      (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg k)).ne'
    have hωtop : ω ≠ ∞ := Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
    have hbound : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), lam (closedBall x ρ) ≤ C * (ω * ENNReal.ofReal ρ ^ k) := by
      filter_upwards [Filter.eventually_lt_of_limsup_lt hC, self_mem_nhdsWithin] with ρ hρ hρ0
      simp only [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient,
        Measure.toOuterMeasure_apply, univ_inter, ENNReal.rpow_natCast] at hρ
      have hd0 : ω * ENNReal.ofReal ρ ^ k ≠ 0 :=
        mul_ne_zero hω0 (pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ0).ne')
      have hdtop : ω * ENNReal.ofReal ρ ^ k ≠ ∞ :=
        ENNReal.mul_ne_top hωtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      exact ((ENNReal.div_lt_iff (Or.inl hd0) (Or.inl hdtop)).1 hρ).le
    -- The rescaling `r ↦ R r` maps `𝓝[>] 0` to itself; small balls lie in `W`.
    have hscale : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hR hr
    have hsub : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), closedBall x ρ ⊆ ball y s :=
      (eventually_closedBall_subset (isOpen_ball.mem_nhds hxW)).filter_mono nhdsWithin_le_nhds
    set a : ℝ → ℝ≥0∞ := fun ρ =>
      (∫⁻ z in closedBall x ρ, ‖f z - f x‖ₑ ∂lam) / lam (closedBall x ρ) with ha
    -- `r⁻ᵏ ∫_{M ∩ B̄_{Rr}(x)} |f - f(x)| dHᵏ ≤ C ωₖ Rᵏ a(R r) → 0`.
    have hc : C * ω * ENNReal.ofReal R ^ k ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hCtop.ne hωtop)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    have hlim := ENNReal.Tendsto.const_mul ((hlebx hxW).comp hscale) (Or.inr hc)
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun r => zero_le) ?_
    filter_upwards [hscale.eventually hbound, hscale.eventually hsub, self_mem_nhdsWithin]
      with r hrb hrW hr0
    have hr0 : (0 : ℝ) < r := hr0
    have hRr : (0 : ℝ) < R * r := mul_pos hR hr0
    -- `M ∩ B̄_{Rr}(x) = B̄_{Rr}(x) ∩ (M ∩ K)`, so the integral is the `λ`-integral.
    have hI : ∫⁻ z in M ∩ closedBall x (R * r), ‖f z - f x‖ₑ ∂H =
        lam (closedBall x (R * r)) * a (R * r) := by
      rw [ha, ENNReal.mul_div_cancel' (fun h0 => setLIntegral_measure_zero _ _ h0)
        (fun htop => absurd htop (measure_ne_top lam _)), hlam,
        Measure.restrict_restrict measurableSet_closedBall]
      congr 2
      ext z
      exact ⟨fun hz => ⟨hz.2, hz.1, hWK (hrW hz.2)⟩, fun hz => ⟨hz.2.1, hz.1⟩⟩
    have hpow : ENNReal.ofReal ((r ^ k)⁻¹) * ENNReal.ofReal (R * r) ^ k =
        ENNReal.ofReal R ^ k := by
      rw [← ENNReal.ofReal_pow hRr.le, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hr0.le k)),
        ← ENNReal.ofReal_pow hR.le, mul_pow, ← mul_assoc, mul_comm _ (R ^ k), mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero k hr0.ne'), mul_one]
    calc ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ z in M ∩ closedBall x (R * r), ‖f z - f x‖ₑ ∂H
        = ENNReal.ofReal ((r ^ k)⁻¹) * (lam (closedBall x (R * r)) * a (R * r)) := by rw [hI]
      _ ≤ ENNReal.ofReal ((r ^ k)⁻¹) * (C * (ω * ENNReal.ofReal (R * r) ^ k) * a (R * r)) := by
        gcongr
      _ = C * ω * (ENNReal.ofReal ((r ^ k)⁻¹) * ENNReal.ofReal (R * r) ^ k) * a (R * r) := by
        ring
      _ = C * ω * ENNReal.ofReal R ^ k * a (R * r) := by rw [hpow]
  -- Countably many balls `B_s(y)` with `B̄_s(y) ⊆ U` cover `U` (second countability).
  obtain ⟨T, hTI, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable
    {p : Eucl P × ℝ | closedBall p.1 p.2 ⊆ U} (fun p => ball p.1 p.2) fun p _ => isOpen_ball
  have hall : ∀ᵐ x ∂(H.restrict M), ∀ p ∈ T, x ∈ ball p.1 p.2 → ∀ R : ℝ, 0 < R →
      Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) *
        ∫⁻ y in M ∩ closedBall x (R * r), ‖f y - f x‖ₑ ∂H) (𝓝[>] 0) (𝓝 0) :=
    (ae_ball_iff hTc).2 fun p hp => key p (hTI hp)
  filter_upwards [hall, ae_restrict_mem₀ hMm] with x hx hxM
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x (hMU hxM)
  have hxT : x ∈ ⋃ p ∈ T, ball p.1 p.2 := hTU ▸ mem_iUnion₂.2
    ⟨(x, ε / 2), (closedBall_subset_ball (half_lt_self hε)).trans hεU, mem_ball_self (half_pos hε)⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hxT
  exact hx p hp hxp

/-- Tangent planes agree on the overlap (for Simon Ch. 6, 3.2 (1); Ch. 3, 1.7): given the tangent
locality (TL), for `Hᵏ⌞(M₁ ∩ M₂)`-a.e. `x` every weighted approximate tangent plane of `(M₁, θ₁)`
at `x` is one of `(M₂, θ₂)`.  At normalized Lebesgue points of `θ₁, θ₂` on `M₁ ∩ M₂` where
`M₁ Δ M₂` has density zero, (TL) compares each `(M_l, θ_l)` with the constant weight `θ_l(x)` on
`M₁ ∩ M₂`, and a nonzero constant factor does not change the tangent condition. -/
theorem Submission.iwl_imc_tangent_overlap : ∀ (P k : ℕ), (∀ (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P), NullMeasurableSet M (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M' (μHE[k] : Measure (Eucl P)) → θ x = θ' x → (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[k] : Measure (Eucl P)) ∧ IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[k] : Measure (Eucl P))) → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[k] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Q ↔ HasWeightedApproximateTangentSpaceAt k M' θ' x Q) → ∀ U : Set (Eucl P), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl P)) → (∀ x ∈ M₁, 1 ≤ θ₁ x) → (∀ x ∈ M₂, 1 ≤ θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q := by
  intro P k hTL U hU M₁ M₂ θ₁ θ₂ hM₁U hM₂U hM₁ hM₂ hθ₁ hθ₂ hint₁ hint₂
  set H : Measure (Eucl P) := (μHE[k] : Measure (Eucl P)) with hH
  have hNm : NullMeasurableSet (M₁ ∩ M₂) H := hM₁.inter hM₂
  -- Step 1: `Hᵏ(M₁ ∩ M₂ ∩ K) ≤ Hᵏ(M₁ ∩ K) ≤ ∫_{M₁ ∩ K} |θ₁| dHᵏ < ∞`, since `θ₁ ≥ 1` on `M₁`.
  have hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → H (M₁ ∩ M₂ ∩ K) < ∞ := by
    intro K hK hKU
    have hMK : NullMeasurableSet (M₁ ∩ K) H :=
      hM₁.inter hK.isClosed.measurableSet.nullMeasurableSet
    calc H (M₁ ∩ M₂ ∩ K) ≤ H (M₁ ∩ K) :=
          measure_mono (show M₁ ∩ M₂ ∩ K ⊆ M₁ ∩ K from fun y hy => ⟨hy.1.1, hy.2⟩)
      _ = ∫⁻ _ in M₁ ∩ K, 1 ∂H := (setLIntegral_one _).symm
      _ ≤ ∫⁻ y in M₁ ∩ K, ‖θ₁ y‖ₑ ∂H := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem₀ hMK] with y hy
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.one_le_ofReal.2 ((hθ₁ y hy.1).trans (le_abs_self _))
      _ < ∞ := (hint₁ K hK hKU).hasFiniteIntegral
  -- Step 2: normalized Lebesgue points of `θ₁` and `θ₂` on `M₁ ∩ M₂`.
  have hL₁ := Submission.iwl_imc_normalized_lebesgue_points P k U (M₁ ∩ M₂) θ₁ hU
    (inter_subset_left.trans hM₁U) hNm hfin fun K hK hKU => (hint₁ K hK hKU).mono_set
      (show M₁ ∩ M₂ ∩ K ⊆ M₁ ∩ K from fun y hy => ⟨hy.1.1, hy.2⟩)
  have hL₂ := Submission.iwl_imc_normalized_lebesgue_points P k U (M₁ ∩ M₂) θ₂ hU
    (inter_subset_left.trans hM₁U) hNm hfin fun K hK hKU => (hint₂ K hK hKU).mono_set
      (show M₁ ∩ M₂ ∩ K ⊆ M₂ ∩ K from fun y hy => ⟨hy.1.2, hy.2⟩)
  -- Step 3: `S = M₁ Δ M₂` has density zero off `S` for `g = 1_{M₁}|θ₁| + 1_{M₂}|θ₂|`.
  set S : Set (Eucl P) := symmDiff M₁ M₂
  have hSm : NullMeasurableSet S H := hM₁.symmDiff hM₂
  set g : Eucl P → ℝ≥0∞ := fun y =>
    M₁.indicator (fun z => ‖θ₁ z‖ₑ) y + M₂.indicator (fun z => ‖θ₂ z‖ₑ) y
  have hgK : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∫⁻ y in S ∩ K, g y ∂H < ∞ := by
    intro K hK hKU
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    -- `∫_K 1_M |θ| dHᵏ = ∫_{M ∩ K} |θ| dHᵏ`, and `1_M |θ|` is a.e.-measurable on `K`.
    have piece : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ), NullMeasurableSet M H →
        IntegrableOn θ (M ∩ K) H → AEMeasurable (M.indicator fun z => ‖θ z‖ₑ) (H.restrict K) ∧
          ∫⁻ y in K, M.indicator (fun z => ‖θ z‖ₑ) y ∂H < ∞ := by
      intro M θ hM hθ
      have hM' : NullMeasurableSet M (H.restrict K) := hM.mono Measure.restrict_le_self
      have hres : (H.restrict K).restrict M = H.restrict (M ∩ K) := Measure.restrict_restrict' hKm
      refine ⟨(aemeasurable_indicator_iff₀ hM').2 ?_, ?_⟩
      · rw [hres]
        exact hθ.aestronglyMeasurable.enorm
      · rw [lintegral_indicator₀ hM', hres]
        exact hθ.hasFiniteIntegral
    obtain ⟨h₁m, h₁⟩ := piece M₁ θ₁ hM₁ (hint₁ K hK hKU)
    obtain ⟨-, h₂⟩ := piece M₂ θ₂ hM₂ (hint₂ K hK hKU)
    calc ∫⁻ y in S ∩ K, g y ∂H ≤ ∫⁻ y in K, g y ∂H := lintegral_mono_set inter_subset_right
      _ = ∫⁻ y in K, M₁.indicator (fun z => ‖θ₁ z‖ₑ) y ∂H +
          ∫⁻ y in K, M₂.indicator (fun z => ‖θ₂ z‖ₑ) y ∂H := lintegral_add_left' h₁m _
      _ < ∞ := ENNReal.add_lt_top.2 ⟨h₁, h₂⟩
  have hD := Submission.iwl_imc_density_zero_off_set P k U S g hU hSm hgK
  -- Step 4: a nonzero constant factor in the weight does not change the tangent condition.
  have scale : ∀ (N : Set (Eucl P)) (φ ψ : Eucl P → ℝ) (c : ℝ) (x : Eucl P)
      (Q : Submodule ℝ (Eucl P)), c ≠ 0 → (∀ y, ψ y = c * φ y) →
      (HasWeightedApproximateTangentSpaceAt k N ψ x Q ↔
        HasWeightedApproximateTangentSpaceAt k N φ x Q) := by
    intro N φ ψ c x Q hc hψ
    unfold HasWeightedApproximateTangentSpaceAt
    refine and_congr_right fun _ => forall_congr' fun f => ?_
    have key : ∀ (s : Set (Eucl P)) (r : ℝ), ∫ y in s, f y * ψ (x + r • y) ∂μHE[k] =
        c * ∫ y in s, f y * φ (x + r • y) ∂μHE[k] := by
      intro s r
      rw [← integral_const_mul]
      congr 1
      funext y
      rw [hψ]
      ring
    simp only [key, hψ x, mul_assoc]
    constructor
    · intro h
      have h' := h.const_mul c⁻¹
      simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at h'
      exact h'
    · intro h
      exact h.const_mul c
  -- Step 5: by (TL), `(M, θ)` has the same tangent planes at `x` as `(M₁ ∩ M₂, θ(x))`.
  have compare : ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ), NullMeasurableSet M H → M₁ ∩ M₂ ⊆ M →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) H) →
      (∀ z ∈ M, z ∉ M₁ ∩ M₂ → z ∈ S) → (∀ z ∈ M, ‖θ z‖ₑ ≤ g z) → ∀ x ∈ U,
      (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) *
        ∫⁻ y in M₁ ∩ M₂ ∩ closedBall x (R * r), ‖θ y - θ x‖ₑ ∂H) (𝓝[>] 0) (𝓝 0)) →
      (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) *
        ∫⁻ y in S ∩ closedBall x (R * r), g y ∂H) (𝓝[>] 0) (𝓝 0)) →
      ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Q ↔
        HasWeightedApproximateTangentSpaceAt k (M₁ ∩ M₂) (fun _ => θ x) x Q := by
    intro M θ hMm hNM hint hMS hθg x hxU hL hDx Q
    have hsmall : ∀ᶠ ρ in 𝓝 (0 : ℝ), closedBall x ρ ⊆ U :=
      eventually_closedBall_subset (hU.mem_nhds hxU)
    obtain ⟨ρ, hρU, hρ⟩ := ((hsmall.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
    refine hTL M (M₁ ∩ M₂) θ (fun _ => θ x) x hMm hNm rfl
      ⟨ρ, hρ, hint _ (isCompact_closedBall x ρ) hρU,
        integrableOn_const (hfin _ (isCompact_closedBall x ρ) hρU).ne⟩ ?_ Q
    intro R hR
    have hscale : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const.mul continuous_id).tendsto' 0 0 (mul_zero R)).mono_left
        nhdsWithin_le_nhds
    have hlim := (hL R hR).add (hDx R hR)
    rw [add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun r => zero_le) ?_
    filter_upwards [hscale.eventually hsmall] with r hrU
    have hBm : MeasurableSet (closedBall x (R * r)) := measurableSet_closedBall
    -- `|1_M θ - 1_{M₁ ∩ M₂} θ(x)| ≤ 1_{M₁ ∩ M₂} |θ - θ(x)| + 1_S g` pointwise.
    have hpt : ∀ z, ‖M.indicator θ z - (M₁ ∩ M₂).indicator (fun _ => θ x) z‖ₑ ≤
        (M₁ ∩ M₂).indicator (fun y => ‖θ y - θ x‖ₑ) z + S.indicator g z := by
      intro z
      by_cases hzN : z ∈ M₁ ∩ M₂
      · rw [indicator_of_mem (hNM hzN), indicator_of_mem hzN, indicator_of_mem hzN]
        exact le_self_add
      · rw [indicator_of_notMem hzN, indicator_of_notMem hzN, sub_zero, zero_add]
        by_cases hzM : z ∈ M
        · rw [indicator_of_mem hzM, indicator_of_mem (hMS z hzM hzN)]
          exact hθg z hzM
        · rw [indicator_of_notMem hzM, enorm_zero]
          exact zero_le
    have hNB : NullMeasurableSet (M₁ ∩ M₂) (H.restrict (closedBall x (R * r))) :=
      hNm.mono Measure.restrict_le_self
    have hSB : NullMeasurableSet S (H.restrict (closedBall x (R * r))) :=
      hSm.mono Measure.restrict_le_self
    have hmeas : AEMeasurable ((M₁ ∩ M₂).indicator fun y => ‖θ y - θ x‖ₑ)
        (H.restrict (closedBall x (R * r))) := by
      refine (aemeasurable_indicator_iff₀ hNB).2 ?_
      rw [Measure.restrict_restrict' hBm]
      exact (((hint _ (isCompact_closedBall x (R * r)) hrU).aestronglyMeasurable.sub
        aestronglyMeasurable_const).enorm).mono_measure (Measure.restrict_mono
          (show M₁ ∩ M₂ ∩ closedBall x (R * r) ⊆ M ∩ closedBall x (R * r) from
            fun y hy => ⟨hNM hy.1, hy.2⟩) le_rfl)
    rw [← mul_add]
    gcongr
    calc ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - (M₁ ∩ M₂).indicator (fun _ => θ x) z‖ₑ ∂H
        ≤ ∫⁻ z in closedBall x (R * r),
            ((M₁ ∩ M₂).indicator (fun y => ‖θ y - θ x‖ₑ) z + S.indicator g z) ∂H :=
          lintegral_mono hpt
      _ = ∫⁻ z in closedBall x (R * r), (M₁ ∩ M₂).indicator (fun y => ‖θ y - θ x‖ₑ) z ∂H +
            ∫⁻ z in closedBall x (R * r), S.indicator g z ∂H := lintegral_add_left' hmeas _
      _ = ∫⁻ y in M₁ ∩ M₂ ∩ closedBall x (R * r), ‖θ y - θ x‖ₑ ∂H +
            ∫⁻ y in S ∩ closedBall x (R * r), g y ∂H := by
          rw [lintegral_indicator₀ hNB, lintegral_indicator₀ hSB, Measure.restrict_restrict' hBm,
            Measure.restrict_restrict' hBm]
  -- Step 6: chain the two comparisons through the constant weights `θ₁(x)` and `θ₂(x)`.
  filter_upwards [hL₁, hL₂, ae_restrict_of_ae (s := M₁ ∩ M₂) hD, ae_restrict_mem₀ hNm]
    with x hx₁ hx₂ hxD hxN Q hQ
  have hxU : x ∈ U := hM₁U hxN.1
  have hxS : x ∉ S := fun h => by
    rcases mem_symmDiff.1 h with ⟨-, h'⟩ | ⟨-, h'⟩
    exacts [h' hxN.2, h' hxN.1]
  have hDx := hxD hxU hxS
  have c₁ := compare M₁ θ₁ hM₁ inter_subset_left hint₁
    (fun z hz hzN => mem_symmDiff.2 (Or.inl ⟨hz, fun h => hzN ⟨hz, h⟩⟩))
    (fun z hz => by
      show ‖θ₁ z‖ₑ ≤ M₁.indicator (fun z => ‖θ₁ z‖ₑ) z + M₂.indicator (fun z => ‖θ₂ z‖ₑ) z
      rw [indicator_of_mem hz]
      exact le_self_add) x hxU hx₁ hDx Q
  have c₂ := compare M₂ θ₂ hM₂ inter_subset_right hint₂
    (fun z hz hzN => mem_symmDiff.2 (Or.inr ⟨hz, fun h => hzN ⟨h, hz⟩⟩))
    (fun z hz => by
      show ‖θ₂ z‖ₑ ≤ M₁.indicator (fun z => ‖θ₁ z‖ₑ) z + M₂.indicator (fun z => ‖θ₂ z‖ₑ) z
      rw [indicator_of_mem hz]
      exact le_add_self) x hxU hx₂ hDx Q
  have hθ₁x : θ₁ x ≠ 0 := (zero_lt_one.trans_le (hθ₁ x hxN.1)).ne'
  have hθ₂x : θ₂ x ≠ 0 := (zero_lt_one.trans_le (hθ₂ x hxN.2)).ne'
  exact c₂.2 ((scale (M₁ ∩ M₂) (fun _ => θ₁ x) (fun _ => θ₂ x) (θ₂ x / θ₁ x) x Q
    (div_ne_zero hθ₂x hθ₁x) fun _ => (div_mul_cancel₀ _ hθ₁x).symm).2 (c₁.1 hQ))

/-- **Restriction of an integer multiplicity current (Simon Ch. 6, 2.9 and 3.1).**  Assume the
tangent comparison principle (T) in `U`: for `Hᵏ ⌞ (M₁ ∩ M₂)`-a.e. `x`, every weighted approximate
tangent space of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.  If `X = τ(M, θ, ξ)` is integer
multiplicity and `S = X ⌞ A`, then `S = τ(M ∩ A, θ, ξ)` is integer multiplicity.  Both `(μ, v)`
and `(Hᵏ ⌞ M, θ ξ)` represent `X`, so by uniqueness of the representation (2.7) `S(ω) =
∫_A θ ⟨ω, ξ⟩ d(Hᵏ ⌞ M)`.  The triple `(M ∩ A, θ, ξ)` inherits every condition from `(M, θ, ξ)`;
for the orientation, (T) applied to `(M, θ)` and `(M ∩ A, θ)` transfers the tangent spaces. -/
theorem Submission.iwl_imc_restriction_im : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → (∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl P)) → (∀ x ∈ M₁, 1 ≤ θ₁ x) → (∀ x ∈ M₂, 1 ≤ θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q) → ∀ (X : GeometricCurrentOn U k) (A : Set (Eucl P)) (S : GeometricCurrentOn U k), IsIntegerMultiplicity X → IsRestriction X A S → IsIntegerMultiplicity S := by
  rintro P k U hU hT X A S ⟨M, θ, ξ, hX, hθ, hXτ⟩ ⟨hA, μ, v, hrepr, hS⟩
  -- Step 1: `θ ≥ 1` on `M`, as `θ` is positive and natural-valued there.
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨n, hn⟩ := hθ x hx
    have h0 : (0 : ℝ) < n := hn ▸ hX.pos x hx
    rw [hn]
    exact_mod_cast h0
  -- Step 2: `(Hᵏ ⌞ M, θ ξ)` is a second representation of `X`.
  have hrepr2 := Submission.iwl_imc_tau_measure_representation P k U M θ ξ X hX hXτ
  -- Step 3: by uniqueness of the representation, `S = τ(M ∩ A, θ, ξ)`.
  have hSτ : ∀ ω : TestFormOn U k, S ω = tauAction k (M ∩ A) θ ξ ω := by
    intro ω
    rw [hS ω, Submission.slicing_representation_unique P k U hU μ
      ((μHE[k] : Measure (Eucl P)).restrict M) v (fun x => θ x • ξ x) (fun ω => (hrepr ω).1)
      (fun ω => (hrepr2 ω).1) U hU (fun ω _ => by rw [← (hrepr ω).2, ← (hrepr2 ω).2]) A hA ω
      ω.2.2, Measure.restrict_restrict hA, inter_comm A M]
    simp only [tauAction, smul_apply, smul_eq_mul]
  -- Step 4: the triple `(M ∩ A, θ, ξ)` inherits the conditions on `(M, θ, ξ)`.
  have hsub : M ∩ A ⊆ U := inter_subset_left.trans hX.subset
  have hnull : NullMeasurableSet (M ∩ A) (μHE[k] : Measure (Eucl P)) :=
    hX.nullMeasurableSet.inter hA.nullMeasurableSet
  have hint : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      IntegrableOn θ (M ∩ A ∩ K) (μHE[k] : Measure (Eucl P)) := fun K hK hKU =>
    (hX.integrableOn K hK hKU).mono_set (inter_subset_inter_left K inter_subset_left)
  -- The orientation: (T) for `(M, θ)` and `(M ∩ A, θ)`, where `M ∩ (M ∩ A) = M ∩ A`.
  have hTA := hT M (M ∩ A) θ θ hX.subset hsub hX.nullMeasurableSet hnull hθ1
    (fun x hx => hθ1 x hx.1) hX.integrableOn hint
  rw [inter_eq_right.2 inter_subset_left] at hTA
  have hMA : IsRectifiableTriple U k (M ∩ A) θ ξ := by
    refine ⟨hsub, hnull, hX.countablyRectifiable.mono inter_subset_left,
      fun x hx => hX.pos x hx.1, hint,
      hX.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl), ?_⟩
    filter_upwards [hTA, ae_restrict_of_ae_restrict_of_subset inter_subset_left hX.orients]
      with x hx hxo
    obtain ⟨τ, hτ, hτM, hξ⟩ := hxo
    exact ⟨τ, hτ, hx _ hτM, hξ⟩
  -- Step 5: `S = τ(M ∩ A, θ, ξ)` with `θ` natural-valued on `M ∩ A ⊆ M`.
  exact ⟨M ∩ A, θ, ξ, hMA, fun x hx => hθ x hx.1, hSτ⟩
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

/-- **Integer multiplicity currents (Simon Ch. 6, 3.2 Remarks (1), (3) and 2.9).**  For open
`U ⊆ ℝ^P`:
(a) an integer multiplicity `X = τ(M, θ, ξ)` has `M_W(X) < ∞` for `W ⊂⊂ U`, since
`(Hᵏ ⌞ M, θ ξ)` represents `X` (2.7) and (R0) of `iwl_restriction_theory` applies;
(b) a restriction `S = X ⌞ A` is `τ(M ∩ A, θ, ξ)` by uniqueness of the representation, and the
tangent comparison principle (T) (`iwl_imc_tangent_overlap`, fed by the locality of weighted
tangent spaces `iwl_weighted_tangent_locality`) transfers the tangent spaces of `(M, θ)` to
`(M ∩ A, θ)` a.e. on `M ∩ A`;
(c) `Z = aX + bY` is integer multiplicity by `iwl_imc_lincomb_im`, again fed by (T). -/
theorem Submission.iwl_im_closure : (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k, IsIntegerMultiplicity X → ∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) ∧ (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X : GeometricCurrentOn U k) (A : Set (Eucl P)) (S : GeometricCurrentOn U k), IsIntegerMultiplicity X → IsRestriction X A S → IsIntegerMultiplicity S) ∧ (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (X Y Z : GeometricCurrentOn U k) (a b : ℤ), IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn U k, Z ω = (a : ℝ) * X ω + (b : ℝ) * Y ω) → IsIntegerMultiplicity Z) := by
  -- (T): for `Hᵏ ⌞ (M₁ ∩ M₂)`-a.e. `x`, the weighted tangent spaces of `(M₁, θ₁)` at `x` are
  -- those of `(M₂, θ₂)`; the locality hypothesis is `iwl_weighted_tangent_locality`.
  have hT := fun (P k : ℕ) (U : Set (Eucl P)) (hU : IsOpen U) =>
    Submission.iwl_imc_tangent_overlap P k (Submission.iwl_weighted_tangent_locality P k) U hU
  refine ⟨?_, ?_, ?_⟩
  -- (a): `(Hᵏ ⌞ M, θ ξ)` represents `X = τ(M, θ, ξ)`, so (R0) bounds `M_W(X)`.
  · rintro P k U hU X ⟨M, θ, ξ, hX, -, hXτ⟩ W hW
    exact Submission.iwl_restriction_theory.1 P k U hU X _ _
      (Submission.iwl_imc_tau_measure_representation P k U M θ ξ X hX hXτ) W hW
  -- (b): `S = X ⌞ A = τ(M ∩ A, θ, ξ)`.
  · rintro P k U hU X A S ⟨M, θ, ξ, hX, hθ, hXτ⟩ ⟨hA, μ, v, hrepr, hS⟩
    -- Step 1: `θ ≥ 1` on `M`, as `θ` is positive and natural-valued there.
    have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
      intro x hx
      obtain ⟨n, hn⟩ := hθ x hx
      have h0 : (0 : ℝ) < n := hn ▸ hX.pos x hx
      rw [hn]
      exact_mod_cast h0
    -- Step 2: `(Hᵏ ⌞ M, θ ξ)` is a second representation of `X`.
    have hrepr2 := Submission.iwl_imc_tau_measure_representation P k U M θ ξ X hX hXτ
    -- Step 3: by uniqueness of the representation, `S(ω) = ∫_A θ ⟨ω, ξ⟩ d(Hᵏ ⌞ M)`.
    have hSτ : ∀ ω : TestFormOn U k, S ω = tauAction k (M ∩ A) θ ξ ω := by
      intro ω
      rw [hS ω, Submission.slicing_representation_unique P k U hU μ
        ((μHE[k] : Measure (Eucl P)).restrict M) v (fun x => θ x • ξ x) (fun ω => (hrepr ω).1)
        (fun ω => (hrepr2 ω).1) U hU (fun ω _ => by rw [← (hrepr ω).2, ← (hrepr2 ω).2]) A hA ω
        ω.2.2, Measure.restrict_restrict hA, inter_comm A M]
      simp only [tauAction, smul_apply, smul_eq_mul]
    -- Step 4: the triple `(M ∩ A, θ, ξ)` inherits the conditions on `(M, θ, ξ)`.
    have hsub : M ∩ A ⊆ U := inter_subset_left.trans hX.subset
    have hnull : NullMeasurableSet (M ∩ A) (μHE[k] : Measure (Eucl P)) :=
      hX.nullMeasurableSet.inter hA.nullMeasurableSet
    have hint : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
        IntegrableOn θ (M ∩ A ∩ K) (μHE[k] : Measure (Eucl P)) := fun K hK hKU =>
      (hX.integrableOn K hK hKU).mono_set (inter_subset_inter_left K inter_subset_left)
    -- The orientation: (T) for `(M, θ)` and `(M ∩ A, θ)`, where `M ∩ (M ∩ A) = M ∩ A`.
    have hTA := hT P k U hU M (M ∩ A) θ θ hX.subset hsub hX.nullMeasurableSet hnull hθ1
      (fun x hx => hθ1 x hx.1) hX.integrableOn hint
    rw [inter_eq_right.2 inter_subset_left] at hTA
    have hMA : IsRectifiableTriple U k (M ∩ A) θ ξ := by
      refine ⟨hsub, hnull, hX.countablyRectifiable.mono inter_subset_left,
        fun x hx => hX.pos x hx.1, hint,
        hX.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl), ?_⟩
      filter_upwards [hTA, ae_restrict_of_ae_restrict_of_subset inter_subset_left hX.orients]
        with x hx hxo
      obtain ⟨τ, hτ, hτM, hξ⟩ := hxo
      exact ⟨τ, hτ, hx _ hτM, hξ⟩
    -- Step 5: `S = τ(M ∩ A, θ, ξ)` with `θ` natural-valued on `M ∩ A ⊆ M`.
    exact ⟨M ∩ A, θ, ξ, hMA, fun x hx => hθ x hx.1, hSτ⟩
  -- (c): integer linear combinations, from (T).
  · intro P k U hU X Y Z a b hX hY hZ
    exact Submission.iwl_imc_lincomb_im P k U hU (hT P k U hU) X Y Z a b hX hY hZ
/-- Cutoff estimate: if `S = Y ⌞ {φ < s}`, `ω'` vanishes where `φ ≥ s`, and `ω - ω'` is
supported in `{x ∈ W : a < φ x}` with `|ω - ω'| ≤ c`, then
`|S(ω) - Y(ω')| ≤ c (M_{W ∩ {φ < s}}(Y) - M_{W ∩ {φ < a}}(Y))`. -/
theorem Submission.iwl_rl_restriction_cutoff_estimate :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (φ : Eucl P → ℝ) (a s c : ℝ) (Y S : GeometricCurrentOn U k)
      (μ : Measure (Eucl P)) (ω ω' : TestFormOn U k), IsOpen W → W ⊆ U → ContinuousOn φ U →
      a < s → IsRestriction Y {x | x ∈ U ∧ φ x < s} S →
      (∀ (A : Set (Eucl P)) (S' : GeometricCurrentOn U k), IsRestriction Y A S' →
        ∀ W' : Set (Eucl P), IsOpen W' → W' ⊆ U → S'.massOn W' = μ (W' ∩ A)) →
      Y.massOn W < ∞ → (∀ x ∈ U, s ≤ φ x → (ω' : DifferentialForm (Eucl P) k) x = 0) →
      tsupport ((ω : DifferentialForm (Eucl P) k) - (ω' : DifferentialForm (Eucl P) k)) ⊆
        {x | x ∈ W ∧ a < φ x} →
      (∀ x, covectorEuclideanNorm
        ((ω : DifferentialForm (Eucl P) k) x - (ω' : DifferentialForm (Eucl P) k) x) ≤ c) →
      |S ω - Y ω'| ≤ c * ((Y.massOn {x | x ∈ W ∧ φ x < s}).toReal -
        (Y.massOn {x | x ∈ W ∧ φ x < a}).toReal) := by
  intro P k U W φ a s c Y S μ ω ω' hWo hWU hφ has hS hμ hYW hω' hsupp hnorm
  -- `S = Y ⌞ {φ < s}` through a representation `(μ₀, v₀)` of `Y`.
  obtain ⟨-, μ₀, v₀, hrep, hSint⟩ := id hS
  -- `Y` is its own restriction to `univ`, so `M_{W'}(Y) = μ W'` for open `W' ⊆ U`.
  have hYmass : ∀ W' : Set (Eucl P), IsOpen W' → W' ⊆ U → Y.massOn W' = μ W' := by
    intro W' hW'o hW'U
    have hY : IsRestriction Y univ Y :=
      ⟨MeasurableSet.univ, μ₀, v₀, hrep, fun η => by rw [Measure.restrict_univ]; exact (hrep η).2⟩
    rw [hμ univ Y hY W' hW'o hW'U, inter_univ]
  -- `W_t = {x ∈ W : φ x < t}` and `W'' = {x ∈ W : a < φ x}` are open subsets of `U`.
  have hφW : ContinuousOn φ W := hφ.mono hWU
  have hWt : ∀ t : ℝ, IsOpen {x | x ∈ W ∧ φ x < t} := fun t =>
    hφW.isOpen_inter_preimage hWo isOpen_Iio
  have hWtU : ∀ t : ℝ, {x | x ∈ W ∧ φ x < t} ⊆ U := fun t x hx => hWU hx.1
  have hW'' : IsOpen {x | x ∈ W ∧ a < φ x} := hφW.isOpen_inter_preimage hWo isOpen_Ioi
  have hW''U : {x | x ∈ W ∧ a < φ x} ⊆ U := fun x hx => hWU hx.1
  rw [hYmass _ (hWt s) (hWtU s), hYmass _ (hWt a) (hWtU a)]
  -- `ω'` vanishes off `{x ∈ U : φ x < s}`, so `S ω' = Y ω'`.
  have hSY : S ω' = Y ω' := by
    rw [hSint ω', (hrep ω').2]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx0 : (ω' : DifferentialForm (Eucl P) k) x = 0 := by
      by_cases hxU : x ∈ U
      · exact hω' x hxU (not_lt.mp fun hxs => hx ⟨hxU, hxs⟩)
      · exact image_eq_zero_of_notMem_tsupport fun hx' => hxU (ω'.2.2 hx')
    rw [hx0, map_zero]
  -- `D = W'' ∩ {x ∈ U : φ x < s}` and `W_a` are disjoint subsets of `W_s`.
  have hdisj : Disjoint ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s})
      {x | x ∈ W ∧ φ x < a} := by
    rw [Set.disjoint_left]
    rintro x ⟨⟨-, hax⟩, -⟩ ⟨-, hxa⟩
    exact lt_asymm hax hxa
  have hadd : μ ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s}) + μ {x | x ∈ W ∧ φ x < a} ≤
      μ {x | x ∈ W ∧ φ x < s} := by
    rw [← measure_union hdisj (hWt a).measurableSet]
    refine measure_mono ?_
    rintro x (⟨⟨hxW, -⟩, -, hxs⟩ | ⟨hxW, hxa⟩)
    · exact ⟨hxW, hxs⟩
    · exact ⟨hxW, hxa.trans has⟩
  -- All three measures are finite, as `M_W(Y) < ∞`.
  have hfin : ∀ t : ℝ, μ {x | x ∈ W ∧ φ x < t} < ∞ := fun t => by
    rw [← hYmass _ (hWt t) (hWtU t)]
    exact (Y.massOn_mono fun x hx => hx.1).trans_lt hYW
  have hfinD : μ ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s}) < ∞ :=
    (le_self_add.trans hadd).trans_lt (hfin s)
  have hreal : (μ ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s})).toReal ≤
      (μ {x | x ∈ W ∧ φ x < s}).toReal - (μ {x | x ∈ W ∧ φ x < a}).toReal := by
    have h := ENNReal.toReal_mono (hfin s).ne hadd
    rw [ENNReal.toReal_add hfinD.ne (hfin a).ne] at h
    linarith
  -- `M_{W''}(S) = μ D`.
  have hSmass : S.massOn {x | x ∈ W ∧ a < φ x} ≤
      ENNReal.ofReal (μ ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s})).toReal := by
    rw [hμ _ S hS _ hW'' hW''U, ENNReal.ofReal_toReal hfinD.ne]
  -- `c ≥ 0`.
  have hc : 0 ≤ c := (covectorEuclideanNorm_nonneg _).trans (hnorm 0)
  -- The basic mass estimate for `S` on `W''` applied to `ω - ω'`.
  have hbound := Submission.cmb_abs_apply_le_of_massOn_le P k U {x | x ∈ W ∧ a < φ x} S
    (ω - ω') _ c ENNReal.toReal_nonneg hSmass (by simpa using hsupp) (by simpa using hnorm)
  -- `S ω - Y ω' = S ω - S ω' = S (ω - ω')`.
  have hlin : S ω - Y ω' = S (ω - ω') := by
    rw [← hSY]
    exact (S.toCurrent.map_sub ω ω').symm
  rw [hlin]
  calc |S (ω - ω')|
      ≤ (μ ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s})).toReal * c := hbound
    _ = c * (μ ({x | x ∈ W ∧ a < φ x} ∩ {x | x ∈ U ∧ φ x < s})).toReal := mul_comm _ _
    _ ≤ c * ((μ {x | x ∈ W ∧ φ x < s}).toReal - (μ {x | x ∈ W ∧ φ x < a}).toReal) :=
      mul_le_mul_of_nonneg_left hreal hc
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
/-- **Restrictions of weakly convergent currents converge weakly** (Simon Ch. 6, Remark 8.3(1)
and (1), (8) in the proof of 8.2, p. 176: "4.5(1) and a selection argument as in 6.7(2) of
Ch. 2").  `F_j(t) = M_{W ∩ {φ < t}}(X_j)` is nondecreasing in `t` and bounded by
`sup_j M_W(X_j)`, so Helly selection gives `ψ` and a countable `E` such that for `s ∉ E` the
increments `F_{ψ j}(b) - F_{ψ j}(a)` over some `a < s < b` are eventually small.  The
restrictions give measure representations, hence mass measures (restriction theory).
(A) For `tsupport ω ⊆ W` and `a < s`, a smooth cutoff `ω'` of `ω` vanishes on `{φ ≥ s}` and
equals `ω` near `tsupport ω ∩ {φ ≤ a}`; the cutoff estimate bounds `|R_j ω - X_{ψ j} ω'|` by
`c (F_{ψ j}(s) - F_{ψ j}(a))` and `|R ω - X ω'|` by `c (M_{W_s}(X) - M_{W_a}(X))`, which is small
for `a` near `s` by continuity of `t ↦ M_{W_t}(X)` from below, while `X_{ψ j} ω' → X ω'`.
(B) If `{φ ≤ s} ⊆ K ⊆ W`, a cutoff `ω''` equal to `ω` near `K` and supported in `W` has the
same restrictions to `{φ < s}`, so (A) applied to `ω''` gives `R_j ω → R ω`. -/
theorem Submission.iwl_restriction_weak_limit : ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P)) (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U → (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k), (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) → IsRestriction X {x | x ∈ U ∧ φ x < s} R → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K → WeaklyConvergesOn Rj R) := by
  intro P k U hU Xj X W φ hconv hWo hWU hsup hφ
  -- `W_t = {x ∈ W : φ x < t}` is an open subset of `W`.
  have hWt : ∀ t : ℝ, IsOpen {x | x ∈ W ∧ φ x < t} := fun t =>
    (hφ.mono hWU).isOpen_inter_preimage hWo isOpen_Iio
  have hWtW : ∀ t : ℝ, {x | x ∈ W ∧ φ x < t} ⊆ W := fun t x hx => hx.1
  -- Uniform bound `M_W(X_j) ≤ sup_j M_W(X_j) < ∞`, and `M_W(X) < ∞` by lower semicontinuity.
  have hXjW : ∀ j, (Xj j).massOn W ≤ ⨆ j, (Xj j).massOn W := fun j =>
    le_iSup (fun j => (Xj j).massOn W) j
  have hXW : X.massOn W < ∞ :=
    calc X.massOn W ≤ liminf (fun j => (Xj j).massOn W) atTop := hconv.massOn_le_liminf W
      _ ≤ limsup (fun j => (Xj j).massOn W) atTop := liminf_le_limsup
      _ ≤ ⨆ j, (Xj j).massOn W := limsup_le_iSup
      _ < ∞ := hsup
  have hXfin : ∀ t, X.massOn {x | x ∈ W ∧ φ x < t} ≠ ∞ := fun t =>
    ((X.massOn_mono (hWtW t)).trans_lt hXW).ne
  -- `F_j(t) = M_{W_t}(X_j)` is nondecreasing in `t` with values in `[0, sup_j M_W(X_j)]`.
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → ℝ, ∀ j t, F j t = ((Xj j).massOn {x | x ∈ W ∧ φ x < t}).toReal :=
    ⟨_, fun _ _ => rfl⟩
  have hFmono : ∀ j, Monotone (F j) := fun j t t' htt' => by
    rw [hF, hF]
    exact ENNReal.toReal_mono (((Xj j).massOn_mono (hWtW t')).trans (hXjW j) |>.trans_lt hsup).ne
      ((Xj j).massOn_mono fun x hx => ⟨hx.1, hx.2.trans_le htt'⟩)
  have hFbound : ∀ j t, |F j t| ≤ (⨆ j, (Xj j).massOn W).toReal := fun j t => by
    rw [hF, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hsup.ne (((Xj j).massOn_mono (hWtW t)).trans (hXjW j))
  -- Helly selection: `ψ` and the countable exceptional set `E`.
  obtain ⟨ψ, E, hψ, hE, hHelly⟩ :=
    Submission.iwl_rl_monotone_helly_selection F _ hFmono hFbound
  refine ⟨ψ, E, hψ, hE, fun s hs Rj R hRj hR => ?_⟩
  -- A current with a restriction has a measure representation, hence locally finite mass and a
  -- mass measure computing the masses of all of its restrictions (restriction theory).
  have hmeas : ∀ (Y S : GeometricCurrentOn U k) (A : Set (Eucl P)), IsRestriction Y A S →
      ∃ μ : Measure (Eucl P), ∀ (A' : Set (Eucl P)) (S' : GeometricCurrentOn U k),
        IsRestriction Y A' S' → ∀ W' : Set (Eucl P), IsOpen W' → W' ⊆ U →
          S'.massOn W' = μ (W' ∩ A') := by
    intro Y S A hYS
    obtain ⟨-, μ, v, hrep, -⟩ := hYS
    obtain ⟨μ', -, -, hmass⟩ := Submission.iwl_restriction_theory.2.2 P k U hU Y
      (Submission.iwl_restriction_theory.1 P k U hU Y μ v hrep)
    exact ⟨μ', hmass⟩
  -- (A) Convergence on test forms supported in `W`.
  have hA : ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
      Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω)) := by
    intro ω hωW
    obtain ⟨c, hc, hωc⟩ := Submission.br_la_testForm_covectorNorm_bounded P k U ω
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h2c : 0 < 2 * c + 1 := by linarith
    obtain ⟨δ, hδ, hεδ⟩ : ∃ δ : ℝ, 0 < δ ∧ (2 * c + 1) * δ = ε :=
      ⟨ε / (2 * c + 1), div_pos hε h2c, mul_div_cancel₀ ε h2c.ne'⟩
    -- Helly at `s ∉ E`: `F_{ψ j}(b₀) - F_{ψ j}(a₀) < δ` for all large `j`.
    obtain ⟨a₀, b₀, ha₀, hb₀, hev⟩ := hHelly s hs δ hδ
    -- Continuity from below of `t ↦ M_{W_t}(X)` at `s`, via `W_s = ⋃ᵢ W_{s - 1/(i+1)}`.
    obtain ⟨a₁, ha₁, hXa₁⟩ : ∃ a₁ < s, (X.massOn {x | x ∈ W ∧ φ x < s}).toReal -
        (X.massOn {x | x ∈ W ∧ φ x < a₁}).toReal < δ := by
      have hOmono : Monotone fun i : ℕ => {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)} := by
        intro i i' hii' x hx
        refine ⟨hx.1, hx.2.trans_le ?_⟩
        have h0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
        have h1 : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.mpr hii'
        have := one_div_le_one_div_of_le h0 (by linarith : (i : ℝ) + 1 ≤ (i' : ℝ) + 1)
        linarith
      have hUnion : (⋃ i : ℕ, {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)}) =
          {x | x ∈ W ∧ φ x < s} := by
        ext x
        simp only [mem_iUnion, mem_ofPred_eq]
        constructor
        · rintro ⟨i, hxW, hxi⟩
          have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
          exact ⟨hxW, by linarith⟩
        · rintro ⟨hxW, hxs⟩
          obtain ⟨i, hi⟩ := exists_nat_one_div_lt (sub_pos.mpr hxs)
          exact ⟨i, hxW, by linarith⟩
      have hiU : X.massOn (⋃ i : ℕ, {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)}) =
          ⨆ i : ℕ, X.massOn {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)} :=
        Submission.iwl_rl_massOn_iUnion_monotone P k U X
          (fun i : ℕ => {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)}) (fun i => hWt _) hOmono
      have hreal : (X.massOn {x | x ∈ W ∧ φ x < s}).toReal =
          ⨆ i : ℕ, (X.massOn {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)}).toReal := by
        rw [← hUnion, hiU, ENNReal.toReal_iSup fun i => hXfin _]
      obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup (show (X.massOn {x | x ∈ W ∧ φ x < s}).toReal - δ <
          ⨆ i : ℕ, (X.massOn {x | x ∈ W ∧ φ x < s - 1 / ((i : ℝ) + 1)}).toReal by
        rw [← hreal]; linarith)
      have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
      exact ⟨s - 1 / ((i : ℝ) + 1), by linarith, by linarith⟩
    obtain ⟨a, ha₀a, ha₁a, has⟩ : ∃ a, a₀ ≤ a ∧ a₁ ≤ a ∧ a < s :=
      ⟨max a₀ a₁, le_max_left _ _, le_max_right _ _, max_lt ha₀ ha₁⟩
    -- The cutoff `ω'`: `0` near `tsupport ω ∩ {φ ≥ s}`, `ω` near `tsupport ω ∩ {φ ≤ a}`.
    have hφK : ContinuousOn φ (tsupport (ω : DifferentialForm (Eucl P) k)) :=
      hφ.mono (hωW.trans hWU)
    obtain ⟨ω', ⟨N₀, -, hCN₀, hω'0⟩, ⟨N₁, hN₁, hCN₁, hω'1⟩, hω'supp, hω'norm⟩ :=
      Submission.iwl_rl_testForm_smooth_cutoff P k U ω
        (tsupport (ω : DifferentialForm (Eucl P) k) ∩ φ ⁻¹' Ici s)
        (tsupport (ω : DifferentialForm (Eucl P) k) ∩ φ ⁻¹' Iic a)
        (hφK.preimage_isClosed_of_isClosed (isClosed_tsupport _) isClosed_Ici)
        (hφK.preimage_isClosed_of_isClosed (isClosed_tsupport _) isClosed_Iic)
        (Set.disjoint_left.mpr fun x hx₀ hx₁ => by
          have h₀ : s ≤ φ x := hx₀.2
          have h₁ : φ x ≤ a := hx₁.2
          linarith)
    -- `ω'` vanishes on `{x ∈ U : s ≤ φ x}`.
    have hω'zero : ∀ x ∈ U, s ≤ φ x → (ω' : DifferentialForm (Eucl P) k) x = 0 := by
      intro x _ hx
      by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Eucl P) k)
      · exact hω'0 x (hCN₀ ⟨hxK, hx⟩)
      · exact image_eq_zero_of_notMem_tsupport fun h => hxK (hω'supp h)
    -- `ω - ω'` is supported in `tsupport ω ∖ N₁ ⊆ {x ∈ W : a < φ x}`.
    have hdiff : tsupport ((ω : DifferentialForm (Eucl P) k) - (ω' : DifferentialForm (Eucl P) k)) ⊆
        {x | x ∈ W ∧ a < φ x} := by
      have h1 : tsupport ((ω : DifferentialForm (Eucl P) k) - (ω' : DifferentialForm (Eucl P) k)) ⊆
          tsupport (ω : DifferentialForm (Eucl P) k) ∩ N₁ᶜ := by
        refine closure_minimal (fun x hx => ⟨?_, fun hxN => hx ?_⟩)
          ((isClosed_tsupport _).inter hN₁.isClosed_compl)
        · by_contra hxK
          apply hx
          rw [Pi.sub_apply, image_eq_zero_of_notMem_tsupport hxK,
            image_eq_zero_of_notMem_tsupport fun h => hxK (hω'supp h), sub_zero]
        · rw [Pi.sub_apply, hω'1 x hxN, sub_self]
      intro x hx
      obtain ⟨hxK, hxN⟩ := h1 hx
      exact ⟨hωW hxK, not_le.mp fun hxa => hxN (hCN₁ ⟨hxK, hxa⟩)⟩
    have hnorm : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x -
        (ω' : DifferentialForm (Eucl P) k) x) ≤ c := fun x => (hω'norm x).trans (hωc x)
    -- The cutoff estimates for `X_{ψ j}` and for `X`.
    have hestj : ∀ j, |Rj j ω - Xj (ψ j) ω'| ≤ c * (F (ψ j) s - F (ψ j) a) := by
      intro j
      obtain ⟨μ, hμ⟩ := hmeas _ _ _ (hRj j)
      rw [hF, hF]
      exact Submission.iwl_rl_restriction_cutoff_estimate P k U W φ a s c (Xj (ψ j)) (Rj j) μ ω ω'
        hWo hWU hφ has (hRj j) hμ ((hXjW (ψ j)).trans_lt hsup) hω'zero hdiff hnorm
    have hest : |R ω - X ω'| ≤ c * ((X.massOn {x | x ∈ W ∧ φ x < s}).toReal -
        (X.massOn {x | x ∈ W ∧ φ x < a}).toReal) := by
      obtain ⟨μ, hμ⟩ := hmeas _ _ _ hR
      exact Submission.iwl_rl_restriction_cutoff_estimate P k U W φ a s c X R μ ω ω'
        hWo hWU hφ has hR hμ hXW hω'zero hdiff hnorm
    have hXa : (X.massOn {x | x ∈ W ∧ φ x < s}).toReal -
        (X.massOn {x | x ∈ W ∧ φ x < a}).toReal < δ := by
      have : (X.massOn {x | x ∈ W ∧ φ x < a₁}).toReal ≤
          (X.massOn {x | x ∈ W ∧ φ x < a}).toReal :=
        ENNReal.toReal_mono (hXfin a) (X.massOn_mono fun x hx => ⟨hx.1, hx.2.trans_le ha₁a⟩)
      linarith
    -- Weak convergence on the fixed test form `ω'`.
    have hconvω' : Tendsto (fun j => Xj (ψ j) ω') atTop (𝓝 (X ω')) :=
      (hconv ω').comp hψ.tendsto_atTop
    have hev' : ∀ᶠ j in atTop, |Xj (ψ j) ω' - X ω'| < δ := by
      filter_upwards [Metric.tendsto_nhds.mp hconvω' δ hδ] with j hj
      rwa [Real.dist_eq] at hj
    filter_upwards [hev, hev'] with j hj₁ hj₂
    have hFa : F (ψ j) a₀ ≤ F (ψ j) a := hFmono _ ha₀a
    have hFs : F (ψ j) s ≤ F (ψ j) b₀ := hFmono _ hb₀.le
    have e₁ : c * (F (ψ j) s - F (ψ j) a) ≤ c * δ :=
      mul_le_mul_of_nonneg_left (by linarith) hc.le
    have e₃ : c * ((X.massOn {x | x ∈ W ∧ φ x < s}).toReal -
        (X.massOn {x | x ∈ W ∧ φ x < a}).toReal) ≤ c * δ :=
      mul_le_mul_of_nonneg_left hXa.le hc.le
    have t₁ := abs_sub_le (Rj j ω) (Xj (ψ j) ω') (R ω)
    have t₂ := abs_sub_le (Xj (ψ j) ω') (X ω') (R ω)
    have t₃ : |X ω' - R ω| = |R ω - X ω'| := abs_sub_comm _ _
    rw [Real.dist_eq]
    linarith [hestj j, hest]
  -- (B) If `{x ∈ U : φ x ≤ s} ⊆ K ⊆ W` with `K` compact, cut `ω` off near `K` inside `W`.
  refine ⟨hA, fun K hK hKW hsK => ?_⟩
  intro ω
  obtain ⟨ω'', ⟨N₀, hN₀, hCN₀, hω''0⟩, ⟨N₁, -, hCN₁, hω''1⟩, -, -⟩ :=
    Submission.iwl_rl_testForm_smooth_cutoff P k U ω Wᶜ K hWo.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKW)
  -- `ω'' = 0` on `N₀ ⊇ ℝ^P ∖ W`, so `tsupport ω'' ⊆ ℝ^P ∖ N₀ ⊆ W`.
  have hω''W : tsupport (ω'' : DifferentialForm (Eucl P) k) ⊆ W := by
    refine (closure_minimal ?_ hN₀.isClosed_compl).trans (compl_subset_comm.mp hCN₀)
    intro x hx hxN
    exact hx (hω''0 x hxN)
  -- `ω'' = ω` on `N₁ ⊇ K ⊇ {x ∈ U : φ x < s}`, so restrictions to `{φ < s}` agree on them.
  have hsame : ∀ (Y S : GeometricCurrentOn U k), IsRestriction Y {x | x ∈ U ∧ φ x < s} S →
      S ω'' = S ω := by
    rintro Y S ⟨hAm, μ, v, -, hS⟩
    rw [hS ω, hS ω'']
    exact setIntegral_congr_fun hAm fun x hx =>
      congrArg (v x) (hω''1 x (hCN₁ (hsK ⟨hx.1, hx.2.le⟩)))
  have h := (hA ω'' hω''W).congr fun j => hsame _ _ (hRj j)
  rwa [hsame X R hR] at h
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

/-- **The Lipschitz push-forward by a differentiable map is the classical one** (Simon Ch. 6,
remark after 3.10, p. 148: for `f` of class `C¹`, `f_# T` of 3.6 agrees with 2.23).  If
`S = f_# X` in the sense of 3.6 with `X = τ(M, θ, ξ)`, and `η = Df^# (ω ∘ f)` on an open set
`N ⊇ spt X`, then `S(ω) = X(η)`.  `Hⁿ`-a.e. point of `M` lies in `spt X ⊆ N`
(`Submission.iwl_sp_rectifiable_support_null`) and has `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for a frame `τ` of
`TₓM`.  There the derivative of `t ↦ f(x + tτᵢ)` at `0` is both `L(x)τᵢ` and `Df(x)τᵢ`, so
`⟨ω(f(x)), L(x)_# ξ(x)⟩ = ⟨Df(x)^# ω(f(x)), ξ(x)⟩ = ⟨η(x), ξ(x)⟩`. -/
theorem Submission.iwl_sp_lipschitzPushforward_apply_eq : ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (X : GeometricCurrentOn U n) (S : GeometricCurrentOn V n) (f : Eucl P → Eucl Q), Differentiable ℝ f → IsLipschitzPushforward X f S → ∀ (ω : TestFormOn V n) (η : TestFormOn U n), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) n) x = ((ω : DifferentialForm (Eucl Q) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η := by
  intro P Q n U V X S f hf hpush ω η hN
  obtain ⟨M, θ, ξ, L, hT, hX, hL, hS⟩ := hpush
  obtain ⟨N, -, hXN, hη⟩ := hN
  -- Step 1: `S(ω)` and `X(η) = τ(M, θ, ξ)(η)` are integrals over `M`; compare the integrands
  -- `Hⁿ ⌞ M`-a.e. (no integrability is needed for this).
  rw [hS, hX η, tauAction]
  refine integral_congr_ae ?_
  -- Step 2: `Hⁿ ⌞ M`-a.e. point lies in `spt X`, as `Hⁿ(M ∖ spt X) = 0`.
  have hspt : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ X.support := by
    rw [ae_restrict_iff'₀ hT.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (Submission.iwl_sp_rectifiable_support_null P n U X M θ ξ hT hX)] with x hx hxM
    by_contra hxX
    exact hx ⟨hxM, hxX⟩
  -- Step 3: at such `x`, `L(x)` has the tangential derivatives of `f` and `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ`
  -- for a frame `τ` of an approximate tangent space.
  filter_upwards [hspt, hL, hT.orients] with x hxX hLx hor
  obtain ⟨τ, -, htan, hξ⟩ := hor
  -- Step 4: `L(x) τᵢ = Df(x) τᵢ`, both being the derivative of `t ↦ f(x + tτᵢ)` at `t = 0`.
  have hτ : L x ∘ τ = fderiv ℝ f x ∘ τ := by
    funext i
    have hline : HasDerivAt (fun t : ℝ => x + t • τ i) (τ i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (τ i)).const_add x
    have hDf : HasDerivAt (fun t : ℝ => f (x + t • τ i)) (fderiv ℝ f x (τ i)) 0 :=
      (hf x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact (hLx _ htan (τ i) (Submodule.subset_span ⟨i, rfl⟩)).unique hDf
  -- Step 5: hence `⟨ω(f(x)), L(x)_# ξ(x)⟩ = ±ω(f(x))(L(x) ∘ τ) = ±ω(f(x))(Df(x) ∘ τ)
  -- = ⟨Df(x)^# ω(f(x)), ξ(x)⟩ = ⟨η(x), ξ(x)⟩`, using `x ∈ spt X ⊆ N`.
  rw [hη x (hXN hxX)]
  rcases hξ with hξ | hξ <;> simp [hξ, nVectorPushforward, hτ]
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

/-- Mass bound for currents related by compatible pull-backs (step 6 of the smooth push-forward
step in the proof of Simon Ch. 6, 8.2): if `Y(ω) = Z(η)` whenever `η = f^#ω` near `A`, and
`‖Df‖ ≤ c`, then `M_W(Y) ≤ c^j M_{f⁻¹(W) ∩ U}(Z)`.  For `ω` admissible for `M_W(Y)`, the
compatible form `η = ζ f^#ω` (`Submission.iwl_sp_exists_compatible_testForm`) has
`Y(ω) = Z(η)`, `spt η ⊆ f⁻¹(W) ∩ U` and `|η| ≤ ‖Df‖^j |ω ∘ f| ≤ c^j`
(`Submission.iwl_sp_covectorEuclideanNorm_pullback_le`), so `c^{-j} η` is admissible for
`M_{f⁻¹(W) ∩ U}(Z)`; if `c^j = 0`, then `j ≥ 1`, `Df = 0` and `η = 0`. -/
theorem Submission.iwl_sp_massOn_le_of_compatible : ∀ (P Q j : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (A : Set (Eucl P)) (Y : GeometricCurrentOn V j) (Z : GeometricCurrentOn U j) (f : Eucl P → Eucl Q) (c : ℝ), IsOpen U → A ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ A)) → (∀ (ω : TestFormOn V j) (η : TestFormOn U j), (∃ N : Set (Eucl P), IsOpen N ∧ A ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) j) x = ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → Y ω = Z η) → 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), Y.massOn W ≤ ENNReal.ofReal (c ^ j) * Z.massOn (f ⁻¹' W ∩ U) := by
  intro P Q j U V A Y Z f c hU hAU hf hprop hcompat hc hDf W
  -- Step 0: the Euclidean coefficient norm is absolutely homogeneous.
  have hsmul : ∀ (t : ℝ) (β : Covector (Eucl P) j),
      covectorEuclideanNorm (t • β) = |t| * covectorEuclideanNorm β := by
    intro t β
    simp only [covectorEuclideanNorm, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun I _ => by rw [mul_ite, mul_zero]
  apply sSup_le
  rintro _ ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (Y ω) ≤ _
  -- Step 2: the compatible form `η = ζ f^#ω`, with `Y(ω) = Z(η)`.
  obtain ⟨η, ζ, N, hN, hAN, hζ, hηζ, hηN, hηsupp⟩ :=
    Submission.iwl_sp_exists_compatible_testForm P Q j U V A f hU hAU hf hprop ω
  rw [hcompat ω η ⟨N, hN, hAN, hηN⟩]
  -- Step 3: `spt η ⊆ f⁻¹(W) ∩ U`.
  have hsupp : tsupport (η : DifferentialForm (Eucl P) j) ⊆ f ⁻¹' W ∩ U :=
    subset_inter (hηsupp.trans (preimage_mono hω.1)) η.property.2
  -- Step 4: `|η(x)| ≤ ‖Df(x)‖^j |ω(f(x))| ≤ c^j`.
  have hbound : ∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) j) x) ≤ c ^ j := by
    intro x
    rw [hηζ x, hsmul, abs_of_nonneg (hζ x).1]
    calc ζ x * covectorEuclideanNorm
          (((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x))
        ≤ covectorEuclideanNorm
          (((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap (fderiv ℝ f x)) :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hζ x).2
      _ ≤ ‖fderiv ℝ f x‖ ^ j * covectorEuclideanNorm ((ω : DifferentialForm (Eucl Q) j) (f x)) :=
          Submission.iwl_sp_covectorEuclideanNorm_pullback_le P Q j _ _
      _ ≤ c ^ j * 1 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDf x) j) (hω.2 (f x))
            (covectorEuclideanNorm_nonneg _) (pow_nonneg hc j)
      _ = c ^ j := mul_one _
  rcases (pow_nonneg hc j).eq_or_lt with h0 | hpos
  · -- Step 5: `c^j = 0`, so `j ≠ 0`, `Df = 0` and `η = 0`.
    have hj : j ≠ 0 := by
      rintro rfl
      simp at h0
    have hc0 : c = 0 := (pow_eq_zero_iff hj).mp h0.symm
    have hη0 : η = 0 := by
      apply Subtype.ext
      funext x
      show (η : DifferentialForm (Eucl P) j) x = 0
      have hpb0 : ((ω : DifferentialForm (Eucl Q) j) (f x)).compContinuousLinearMap
          (fderiv ℝ f x) = 0 := by
        ext v
        rw [norm_le_zero_iff.mp ((hDf x).trans hc0.le),
          ContinuousAlternatingMap.compContinuousLinearMap_apply,
          ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
        exact ((ω : DifferentialForm (Eucl Q) j) (f x)).map_coord_zero
          ⟨0, Nat.pos_of_ne_zero hj⟩ rfl
      rw [hηζ x, hpb0, smul_zero]
    rw [hη0, map_zero, ENNReal.ofReal_zero]
    exact zero_le
  · -- Step 6: `c^{-j} η` is admissible for `M_{f⁻¹(W) ∩ U}(Z)`.
    have hη₁ : ((c ^ j)⁻¹ • η : TestFormOn U j) ∈ massAdmissibleOn U j (f ⁻¹' W ∩ U) := by
      refine ⟨(tsupport_smul_subset_right (fun _ => (c ^ j)⁻¹)
        (η : DifferentialForm (Eucl P) j)).trans hsupp, fun x => ?_⟩
      change covectorEuclideanNorm ((c ^ j)⁻¹ • (η : DifferentialForm (Eucl P) j) x) ≤ 1
      rw [hsmul, abs_of_pos (inv_pos.mpr hpos)]
      calc (c ^ j)⁻¹ * covectorEuclideanNorm ((η : DifferentialForm (Eucl P) j) x)
          ≤ (c ^ j)⁻¹ * c ^ j := mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hpos.le)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    rw [← smul_inv_smul₀ hpos.ne' η, map_smul, smul_eq_mul,
      ENNReal.ofReal_mul (pow_nonneg hc j)]
    gcongr
    exact Z.le_massOn hη₁
/-- **Boundary commutes with smooth push-forward** (Simon Ch. 6, 2.24(1), p. 141:
`∂ f_# T = f_# ∂T`).  Let `f` be `C^∞`.  If `S(ω′) = X(η′)` whenever `η′ = f^# ω′` on an open set
containing `spt X` (degree `k + 1`), then `∂S(ω) = ∂X(η)` whenever `η = f^# ω` on an open set `N`
containing `spt X` (degree `k`), where `(f^# ω)(x) = Df(x)^# ω(f(x))`.  On `N`,
`dη = d(f^# ω) = f^# dω` by locality of `d` and its naturality under pull-back
(`extDeriv_pullback`), so the hypothesis applies to `(dω, dη)`: `∂S(ω) = S(dω) = X(dη) = ∂X(η)`. -/
theorem Submission.iwl_sp_boundary_apply_eq_of_compatible : ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (X : GeometricCurrentOn U (k + 1)) (S : GeometricCurrentOn V (k + 1)) (f : Eucl P → Eucl Q), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) → ∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η := by
  intro P Q k U V X S f hf hS ω η ⟨N, hN, hXN, hηN⟩
  -- `∂S(ω) = S(dω)` and `∂X(η) = X(dη)`; apply the degree-`(k + 1)` hypothesis to `(dω, dη, N)`.
  rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply]
  refine hS _ _ ⟨N, hN, hXN, fun x hx => ?_⟩
  change extDeriv (η : DifferentialForm (Eucl P) k) x =
    (extDeriv (ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)
  -- Locality: `η = f^# ω` near `x`, as `N` is open, so `(dη)(x) = d(f^# ω)(x)`.
  have hloc : (η : DifferentialForm (Eucl P) k) =ᶠ[𝓝 x] fun y =>
      ((ω : DifferentialForm (Eucl Q) k) (f y)).compContinuousLinearMap (fderiv ℝ f y) :=
    Filter.eventually_of_mem (hN.mem_nhds hx) hηN
  rw [hloc.extDeriv_eq]
  -- Naturality: `d(f^# ω)(x) = Df(x)^# (dω)(f(x))`, as `ω` and `f` are `C^∞` and `2 ≤ ∞`.
  exact extDeriv_pullback (ω.property.1.1.differentiable (by simp)).differentiableAt
    hf.contDiffAt (by simp)

/-- **Smooth push-forward of an integer multiplicity current** (Simon Ch. 6, 2.23–2.24, p. 139,
and Lemma 3.9, p. 148).  Assume Lemma 3.9 (`LipschitzPushforwardIntegerMultiplicity`).  Let
`X ∈ 𝒟_{k+1}(U)` be integer multiplicity and `f` be `C^∞` with `f(U) ⊆ V` and `f | spt X` proper.
Then the integer multiplicity push-forward `S = f_# X` of 3.9 is the push-forward of 2.23 (remark
after 3.10, p. 148): (1) `S(ω) = X(η)` whenever `η = f^# ω` on an open set containing `spt X`;
(2) `∂S(ω) = ∂X(η)` likewise (2.24(1)); (3) if `‖Df‖ ≤ c`, then
`M_W(S) ≤ c^{k+1} M_{f⁻¹(W) ∩ U}(X)` and `M_W(∂S) ≤ c^k M_{f⁻¹(W) ∩ U}(∂X)`. -/
theorem Submission.iwl_smooth_pushforward : LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U) := by
  intro hLip P Q k U V hU hV X f hX hf hfUV hprop
  -- Step 1: `f` is `C¹`, hence locally Lipschitz on `U`, so 3.9 gives an integer multiplicity
  -- `S` which is the push-forward `f_# X` of (3.6).
  obtain ⟨S, hSX, hS⟩ := hLip P Q (k + 1) U V hU hV X f hX
    (hf.of_le (m := 1) (by exact_mod_cast le_top)).locallyLipschitz.locallyLipschitzOn hfUV hprop
  -- Steps 2–4, assertion (1): as `f` is differentiable, (3.6) agrees with the push-forward of 2.23.
  have h₁ := Submission.iwl_sp_lipschitzPushforward_apply_eq P Q (k + 1) U V X S f
    (hf.differentiable (by simp)) hSX
  -- Step 5, assertion (2): `∂ f_# X = f_# ∂X`.
  have h₂ := Submission.iwl_sp_boundary_apply_eq_of_compatible P Q k U V X S f hf h₁
  -- Step 6, assertion (3): the mass comparison with `A = spt X ⊆ U`, applied to `(S, X)` in
  -- degree `k + 1` through (1) and to `(∂S, ∂X)` in degree `k` through (2).
  exact ⟨S, hS, h₁, h₂, fun c hc hDf W =>
    ⟨Submission.iwl_sp_massOn_le_of_compatible P Q (k + 1) U V X.support S X f c hU
        X.support_subset_domain hf hprop h₁ hc hDf W,
      Submission.iwl_sp_massOn_le_of_compatible P Q k U V X.support S.boundary X.boundary f c hU
        X.support_subset_domain hf hprop h₂ hc hDf W⟩⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

theorem Submission.iwl_top_dim_integrality : ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T := by
  intro m
  classical
  /- Notation: n = m + 1, E = Eucl n, e the standard frame, dx = e₁* ∧ ⋯ ∧ eₙ*. -/
  obtain ⟨e, he⟩ : ∃ e : Fin (m+1) → Eucl (m+1), e = fun i => EuclideanSpace.single i (1:ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨dx, hdx⟩ : ∃ dx : Covector (Eucl (m+1)) (m+1),
      dx = wedgeCovectors (m+1) (fun i => (EuclideanSpace.proj i : Eucl (m+1) →L[ℝ] ℝ)) :=
    ⟨_, rfl⟩
  have hvol : (μHE[m+1] : Measure (Eucl (m+1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m+1)
  have hT0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true]
  have hbe : (⇑(EuclideanSpace.basisFun (Fin (m+1)) ℝ) : Fin (m+1) → Eucl (m+1)) = e := by
    rw [he]; funext i; simp only [EuclideanSpace.basisFun_apply]
  /- Step 1: top-degree covectors. -/
  have hdxe : dx e = 1 := by
    rw [hdx, he, wedgeCovectors_apply_det]
    have : (Matrix.of fun i j => (EuclideanSpace.proj i : Eucl (m+1) →L[ℝ] ℝ)
        (EuclideanSpace.single j (1:ℝ))) = 1 := by
      ext i j
      simp only [PiLp.proj_apply, PiLp.single_apply, Matrix.of_apply, Matrix.one_apply]
    rw [this, Matrix.det_one]
  have hP1 : ∀ (α : Covector (Eucl (m+1)) (m+1)) (v : Fin (m+1) → Eucl (m+1)),
      α v = α e * dx v := by
    intro α v
    classical
    let b := (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis
    have hbe' : (⇑b : Fin (m+1) → Eucl (m+1)) = e := by
      rw [← hbe]; exact OrthonormalBasis.coe_toBasis _
    have h1 := AlternatingMap.eq_smul_basis_det b α.toAlternatingMap
    have h2 : α v = α ⇑b * b.det v := by
      have := congrArg (fun f => f v) h1
      simpa only [AlternatingMap.coe_mk, ContinuousMultilinearMap.coe_coe, ContinuousAlternatingMap.coe_toContinuousMultilinearMap, AlternatingMap.smul_apply, smul_eq_mul] using this
    rw [h2, hbe', hdx, wedgeCovectors_apply_det, Module.Basis.det_apply]
    congr 2
  have hP1' : ∀ (w : NVector (Eucl (m+1)) (m+1)) (α : Covector (Eucl (m+1)) (m+1)),
      w α = α e * w dx := by
    intro w α
    have hα : α = α e • dx := by
      ext v
      rw [hP1 α v]
      simp only [ContinuousAlternatingMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [hα]
    rw [map_smul, smul_eq_mul]
  have hP3 : ∀ τ : Fin (m+1) → Eucl (m+1), Orthonormal ℝ τ → dx τ = 1 ∨ dx τ = -1 := by
    intro τ hτ
    rw [hdx, wedgeCovectors_apply_det]
    set A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
      Matrix.of fun i j => (EuclideanSpace.proj i : Eucl (m+1) →L[ℝ] ℝ) (τ j) with hA
    have hAA : A.transpose * A = 1 := by
      ext i j
      rw [Matrix.mul_apply, Matrix.one_apply, ← (orthonormal_iff_ite.mp hτ) i j]
      simp only [PiLp.proj_apply, Matrix.transpose_apply, Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial, mul_comm, A]
    have hdet : A.det * A.det = 1 := by
      have := congrArg Matrix.det hAA
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact mul_self_eq_one_iff.mp hdet
  have hP5 : ∀ (P k : ℕ) (α : Covector (Eucl P) k) (B : ℝ), 0 ≤ B →
      (∀ I : Fin k → Fin P, |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ B) →
      covectorEuclideanNorm α ≤ Real.sqrt ((P:ℝ)^k) * B := by
    intro P k α B hB h
    unfold covectorEuclideanNorm
    rw [show Real.sqrt ((P:ℝ)^k) * B = Real.sqrt ((P:ℝ)^k * B^2) by
      rw [Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg P) k), Real.sqrt_sq hB]]
    apply Real.sqrt_le_sqrt
    calc (∑ I : Fin k → Fin P, if StrictMono I then
            (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)))^2 else 0)
          ≤ ∑ _I : Fin k → Fin P, B^2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · exact sq_le_sq' (abs_le.mp (h I)).1 (abs_le.mp (h I)).2
            · exact sq_nonneg B
      _ = (P:ℝ)^k * B^2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul, Nat.cast_pow]
  have hP6 : ∀ (P k : ℕ) (α : Covector (Eucl P) k) (c : ℝ),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro P k α c
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro I _
    split_ifs <;> simp only [EuclideanSpace.basisFun_apply, ContinuousAlternatingMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_pow, mul_zero]
  have hP7 : ∀ (ψ : Eucl (m+1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ∀ (z x : Eucl (m+1)),
      exteriorDerivative (fun y => ψ y • dx.curryLeft z) x e = fderiv ℝ ψ x z := by
    intro ψ hψ z x
    have hψd : Differentiable ℝ ψ := hψ.differentiable hT0
    have hd : DifferentiableAt ℝ (fun y => ψ y • dx.curryLeft z) x := (hψd x).smul_const _
    rw [exteriorDerivative_apply hd]
    have hterm : ∀ i : Fin (m+1),
        fderiv ℝ (fun y => (ψ y • dx.curryLeft z) (Fin.removeNth i e)) x (e i)
          = fderiv ℝ ψ x (e i) * dx (Matrix.vecCons z (Fin.removeNth i e)) := by
      intro i
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
        ContinuousAlternatingMap.curryLeft_apply_apply]
      rw [fderiv_mul_const (hψd x)]
      simp only [smul_apply, smul_eq_mul, mul_comm]
    simp only [hterm]
    have hP4 : ∀ g : Eucl (m+1) →L[ℝ] ℝ,
        ∑ i : Fin (m+1), (-1 : ℤ) ^ (i : ℕ) • (g (e i) * dx (Matrix.vecCons z (Fin.removeNth i e)))
          = g z * dx e := by
      intro g
      set F := ContinuousAlternatingMap.alternatizeUncurryFin (g.smulRight dx) with hF
      have h0 : F (Matrix.vecCons z e) = 0 := by
        apply F.toAlternatingMap.map_linearDependent
        intro hli
        have := hli.fintype_card_le_finrank
        simp only [Fintype.card_fin, finrank_euclideanSpace, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at this
      have hrem : ∀ i : Fin (m+1), Fin.removeNth i.succ (Matrix.vecCons z e) =
          Matrix.vecCons z (Fin.removeNth i e) := by
        intro i
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.removeNth_apply, ne_eq, Fin.succ_ne_zero, not_false_eq_true, Fin.succAbove_ne_zero_zero, Matrix.cons_val_zero]
        · simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ, Matrix.cons_val_succ]
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ] at h0
      simp only [hrem, ContinuousLinearMap.smulRight_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.removeNth_zero, ContinuousAlternatingMap.smul_apply, Fin.val_zero,
        pow_zero, one_smul, Fin.val_succ, pow_succ] at h0
      rw [show Fin.tail (Matrix.vecCons z e) = e from Fin.tail_cons _ _] at h0
      have h1 : ∀ x : Fin (m+1),
          ((-1 : ℤ) ^ (x : ℕ) * -1) • g (e x) • dx (Matrix.vecCons z (x.removeNth e))
            = -((-1 : ℤ) ^ (x : ℕ) • (g (e x) * dx (Matrix.vecCons z (x.removeNth e)))) := by
        intro x; rw [mul_neg_one, neg_smul, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_neg_distrib, smul_eq_mul] at h0
      linarith
    rw [hP4, hdxe, mul_one]
  have hcoef_bd : ∀ (z : Eucl (m+1)) (I : Fin m → Fin (m+1)),
      |dx.curryLeft z (fun i => EuclideanSpace.basisFun (Fin (m+1)) ℝ (I i))| ≤ ‖dx‖ * ‖z‖ := by
    intro z I
    rw [ContinuousAlternatingMap.curryLeft_apply_apply]
    refine (dx.le_opNorm _).trans (le_of_eq ?_)
    rw [Fin.prod_univ_succ]
    simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one]
  obtain ⟨κ, hκ0, hκN⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ z : Eucl (m+1),
      covectorEuclideanNorm (dx.curryLeft z) ≤ κ * ‖z‖ := by
    obtain ⟨κ₀, hκ₀, hκ₀N⟩ : ∃ κ₀ : ℝ, 0 ≤ κ₀ ∧ ∀ z : Eucl (m+1),
        covectorEuclideanNorm (dx.curryLeft z) ≤ κ₀ * (‖dx‖ * ‖z‖) :=
      ⟨_, Real.sqrt_nonneg _, fun z => hP5 (m+1) m (dx.curryLeft z) (‖dx‖ * ‖z‖)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hcoef_bd z)⟩
    refine ⟨κ₀ * ‖dx‖ + 1, add_pos_of_nonneg_of_pos (mul_nonneg hκ₀ (norm_nonneg _)) one_pos,
      fun z => (hκ₀N z).trans ?_⟩
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg z)
  /- Test forms `a • c` and the mass bound. -/
  have hform : ∀ (U' : Set (Eucl (m+1))) (k : ℕ) (a : Eucl (m+1) → ℝ) (c : Covector (Eucl (m+1)) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U' →
      ∃ ω : TestFormOn U' k, ∀ x, (ω : DifferentialForm (Eucl (m+1)) k) x = a x • c := by
    intro U' k a c ha hac haU
    exact ⟨⟨fun x => a x • c, ⟨⟨ha.smul contDiff_const, hac.smul_right⟩,
      (tsupport_smul_subset_left _ _).trans haU⟩⟩, fun x => rfl⟩
  have hmassb : ∀ (U' : Set (Eucl (m+1))) (k : ℕ) (S : GeometricCurrentOn U' k)
      (W : Set (Eucl (m+1))) (ω : TestFormOn U' k) (C : ℝ), 0 < C →
      tsupport (ω : DifferentialForm (Eucl (m+1)) k) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m+1)) k) x) ≤ C) →
      S.massOn W ≠ ⊤ → |S ω| ≤ C * (S.massOn W).toReal := by
    intro U' k S W ω C hC hωW hωC hfin
    have hle : ∀ s : ℝ, |s| = 1 → s * S ω ≤ C * (S.massOn W).toReal := by
      intro s hs
      have hadm : ((C⁻¹ * s) • ω) ∈ massAdmissibleOn U' k W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => C⁻¹ * s) _).trans hωW, fun x => ?_⟩
        change covectorEuclideanNorm ((C⁻¹ * s) • (ω : DifferentialForm (Eucl (m+1)) k) x) ≤ 1
        rw [hP6, abs_mul, hs, mul_one, abs_of_pos (inv_pos.2 hC), inv_mul_le_iff₀ hC, mul_one]
        exact hωC x
      have h := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (S.le_massOn hadm)
      rw [map_smul, smul_eq_mul] at h
      calc s * S ω = C * (C⁻¹ * s * S ω) := by rw [mul_assoc C⁻¹, mul_inv_cancel_left₀ hC.ne']
        _ ≤ C * (S.massOn W).toReal := mul_le_mul_of_nonneg_left h hC.le
    have h1 := hle (-1) (by rw [abs_neg, abs_one])
    have h2 := hle 1 abs_one
    rw [neg_one_mul] at h1
    rw [one_mul] at h2
    exact abs_le.2 ⟨by linarith only [h1], h2⟩
  /- Step 3(i): L¹ duality against smooth test functions. -/
  have hL5 : ∀ (f : Eucl (m+1) → ℝ) (K V : Set (Eucl (m+1))) (c : ℝ), Measurable f →
    IsCompact K → IsOpen V → K ⊆ V →
    (∀ K' : Set (Eucl (m+1)), IsCompact K' → K' ⊆ V → IntegrableOn f K') →
    (∀ ψ : Eucl (m+1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∀ x, |ψ x| ≤ 1) → ∫ x, f x * ψ x ≤ c) →
    ∫⁻ x in K, ‖f x‖ₑ ≤ ENNReal.ofReal c := by
    intro f K V c hf hK hV hKV hint hdual
    obtain ⟨r, hr0, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
    have hK₁ : IsCompact (cthickening r K) := hK.cthickening
    have hfK₁ : IntegrableOn f (cthickening r K) := hint _ hK₁ hrV
    -- Claim A: disjoint compact pieces
    have claimA : ∀ C₁ C₂ : Set (Eucl (m+1)), IsCompact C₁ → IsCompact C₂ → C₁ ⊆ K → C₂ ⊆ K →
        Disjoint C₁ C₂ → (∫ x in C₁, f x) - (∫ x in C₂, f x) ≤ c := by
      intro C₁ C₂ hC₁ hC₂ hC₁K hC₂K hC12
      obtain ⟨δ, hδ0, hδ⟩ := hC12.exists_thickenings hC₁ hC₂.isClosed
      let u : ℕ → ℝ := fun k => min δ r / (k + 2)
      have hu : u = (fun k => min δ r / (k + 2) : ℕ → ℝ) := rfl
      have hu0 : ∀ k, 0 < u k := fun k => div_pos (lt_min hδ0 hr0)
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) two_pos)
      have huδ : ∀ k, u k ≤ δ := fun k => (div_le_self (lt_min hδ0 hr0).le
        (le_add_of_nonneg_of_le (Nat.cast_nonneg k) one_le_two)).trans (min_le_left _ _)
      have hur : ∀ k, u k ≤ r := fun k => (div_le_self (lt_min hδ0 hr0).le
        (le_add_of_nonneg_of_le (Nat.cast_nonneg k) one_le_two)).trans (min_le_right _ _)
      have hulim : Tendsto u atTop (𝓝 0) := by
        have : Tendsto (fun k : ℕ => ((k:ℝ) + 2)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        simpa only [u, div_eq_mul_inv, mul_zero] using this.const_mul (min δ r)
      have hg : ∀ (C : Set (Eucl (m+1))), IsClosed C → ∀ k, ∃ g : Eucl (m+1) → ℝ,
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ range g ⊆ Icc 0 1 ∧ Function.support g = thickening (u k) C ∧ ∀ x, x ∈ C ↔ g x = 1 := by
        intro C hC k
        exact exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
          isOpen_thickening hC (self_subset_thickening (hu0 k) C)
      choose g₁ hg₁s hg₁r hg₁supp hg₁1 using hg C₁ hC₁.isClosed
      choose g₂ hg₂s hg₂r hg₂supp hg₂1 using hg C₂ hC₂.isClosed
      have hdisjk : ∀ k, Disjoint (thickening (u k) C₁) (thickening (u k) C₂) := fun k =>
        hδ.mono (thickening_mono (huδ k) _) (thickening_mono (huδ k) _)
      have hrange : ∀ (g : ℕ → Eucl (m+1) → ℝ), (∀ k, range (g k) ⊆ Icc 0 1) → ∀ k x,
          0 ≤ g k x ∧ g k x ≤ 1 := fun g h k x => h k (mem_range_self x)
      let ψ : ℕ → Eucl (m+1) → ℝ := fun k x => g₁ k x - g₂ k x
      have hψ : ψ = fun k x => g₁ k x - g₂ k x := rfl
      have hsuppψ : ∀ k, Function.support (ψ k) ⊆ thickening (u k) K := by
        intro k x hx
        by_contra hxK
        have h1 : g₁ k x = 0 := by
          by_contra h; exact hxK (thickening_subset_of_subset _ hC₁K ((hg₁supp k) ▸ h))
        have h2 : g₂ k x = 0 := by
          by_contra h; exact hxK (thickening_subset_of_subset _ hC₂K ((hg₂supp k) ▸ h))
        exact hx (by simp only [h1, h2, sub_self, ψ])
      have htsuppψ : ∀ k, tsupport (ψ k) ⊆ cthickening r K := fun k =>
        (closure_mono (hsuppψ k)).trans ((closure_thickening_subset_cthickening _ _).trans
          (cthickening_mono (hur k) _))
      have hψbound : ∀ k x, |ψ k x| ≤ 1 := by
        intro k x
        have a1 := hrange g₁ hg₁r k x
        have a2 := hrange g₂ hg₂r k x
        by_cases hx1 : g₁ k x = 0
        · simp only [ψ, hx1, zero_sub, abs_neg]; rw [abs_of_nonneg a2.1]; exact a2.2
        · have hx2 : g₂ k x = 0 := by
            by_contra h
            have m1 : x ∈ thickening (u k) C₁ := (hg₁supp k) ▸ hx1
            have m2 : x ∈ thickening (u k) C₂ := (hg₂supp k) ▸ h
            exact (hdisjk k).le_bot ⟨m1, m2⟩
          simp only [ψ, hx2, sub_zero]; rw [abs_of_nonneg a1.1]; exact a1.2
      have hle : ∀ k, ∫ x, f x * ψ k x ≤ c := fun k =>
        hdual (ψ k) ((hg₁s k).sub (hg₂s k))
          (IsCompact.of_isClosed_subset hK₁ (isClosed_tsupport _) (htsuppψ k))
          ((htsuppψ k).trans hrV) (hψbound k)
      -- pointwise limit
      have hlim : ∀ x, Tendsto (fun k => f x * ψ k x) atTop
          (𝓝 (f x * (C₁.indicator 1 x - C₂.indicator 1 x))) := by
        intro x
        apply Tendsto.const_mul
        by_cases hx1 : x ∈ C₁
        · have hx2 : x ∉ C₂ := fun h => hC12.le_bot ⟨hx1, h⟩
          have : ∀ k, ψ k x = 1 := by
            intro k
            have e1 : g₁ k x = 1 := (hg₁1 k x).1 hx1
            have e2 : g₂ k x = 0 := by
              by_contra h
              have m2 : x ∈ thickening (u k) C₂ := (hg₂supp k) ▸ h
              exact (hdisjk k).le_bot ⟨self_subset_thickening (hu0 k) _ hx1, m2⟩
            simp only [e1, e2, sub_zero, ψ]
          simp only [this, indicator_of_mem hx1, indicator_of_notMem hx2]
          simp only [Pi.one_apply, sub_zero, tendsto_const_nhds_iff]
        · by_cases hx2 : x ∈ C₂
          · have : ∀ k, ψ k x = -1 := by
              intro k
              have e2 : g₂ k x = 1 := (hg₂1 k x).1 hx2
              have e1 : g₁ k x = 0 := by
                by_contra h
                have m1 : x ∈ thickening (u k) C₁ := (hg₁supp k) ▸ h
                exact (hdisjk k).le_bot ⟨m1, self_subset_thickening (hu0 k) _ hx2⟩
              simp only [e1, e2, zero_sub, ψ]
            simp only [this, indicator_of_mem hx2, indicator_of_notMem hx1]
            simp only [Pi.one_apply, zero_sub, tendsto_const_nhds_iff]
          · simp only [indicator_of_notMem hx1, indicator_of_notMem hx2, sub_zero]
            have hev : ∀ (C : Set (Eucl (m+1))) (g : ℕ → Eucl (m+1) → ℝ), IsClosed C → x ∉ C →
                (∀ k, Function.support (g k) = thickening (u k) C) → ∀ᶠ k in atTop, g k x = 0 := by
              intro C g hC hxC hgs
              obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε C := by
                rw [← hC.closure_eq, closure_eq_iInter_thickening C] at hxC
                simpa only [mem_iInter, not_forall, not_imp, exists_prop] using hxC
              filter_upwards [(tendsto_order.1 hulim).2 _ εpos] with k hk
              rw [← Function.notMem_support, hgs]
              exact fun h => hε (thickening_mono hk.le C h)
            apply tendsto_const_nhds.congr'
            filter_upwards [hev C₁ g₁ hC₁.isClosed hx1 hg₁supp, hev C₂ g₂ hC₂.isClosed hx2 hg₂supp]
              with k h1 h2
            simp only [h1, h2, sub_self, ψ]
      have hdom : Tendsto (fun k => ∫ x, f x * ψ k x) atTop
          (𝓝 (∫ x, f x * (C₁.indicator 1 x - C₂.indicator 1 x))) := by
        refine tendsto_integral_of_dominated_convergence (fun x => (cthickening r K).indicator
          (fun x => ‖f x‖) x) (fun k => ?_) ?_ (fun k => ?_) (Eventually.of_forall hlim)
        · exact hf.aestronglyMeasurable.mul
            ((hg₁s k).continuous.sub (hg₂s k).continuous).aestronglyMeasurable
        · exact (integrable_indicator_iff hK₁.measurableSet).2 hfK₁.norm
        · refine Eventually.of_forall (fun x => ?_)
          by_cases hx : x ∈ cthickening r K
          · rw [indicator_of_mem hx, norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hψbound k x)
          · have : ψ k x = 0 := by
              by_contra h
              exact hx ((subset_tsupport _).trans (htsuppψ k) h)
            simp only [this, mul_zero, norm_zero, Real.norm_eq_abs, indicator_of_notMem hx, Std.le_refl]
      have hval : ∫ x, f x * (C₁.indicator 1 x - C₂.indicator 1 x) =
          (∫ x in C₁, f x) - (∫ x in C₂, f x) := by
        have e : (fun x => f x * (C₁.indicator 1 x - C₂.indicator 1 x)) =
            fun x => C₁.indicator f x - C₂.indicator f x := by
          funext x
          by_cases h1 : x ∈ C₁ <;> by_cases h2 : x ∈ C₂ <;> simp only [h1, indicator_of_mem, Pi.one_apply, h2, sub_self, mul_zero, not_false_eq_true, indicator_of_notMem, sub_zero, mul_one, zero_sub, mul_neg]
        rw [e, integral_sub ((integrable_indicator_iff hC₁.measurableSet).2 (hint C₁ hC₁ (hC₁K.trans hKV)))
          ((integrable_indicator_iff hC₂.measurableSet).2 (hint C₂ hC₂ (hC₂K.trans hKV))),
          integral_indicator hC₁.measurableSet, integral_indicator hC₂.measurableSet]
      rw [← hval]
      exact le_of_tendsto' hdom hle
    -- inner regularity and absolute continuity
    have hfK : IntegrableOn f K := hint K hK hKV
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    let F : Eucl (m+1) → ℝ≥0∞ := K.indicator (fun x => ‖f x‖ₑ)
    have hF : F = K.indicator (fun x => ‖f x‖ₑ) := rfl
    have hFfin : ∫⁻ x, F x ≠ ⊤ := by
      rw [lintegral_indicator hK.measurableSet]
      exact hfK.hasFiniteIntegral.ne
    have hε2 : ((ε : ℝ≥0∞) / 2) ≠ 0 := by
      simpa only [ne_eq, ENNReal.div_eq_zero_iff, ENNReal.coe_eq_zero, ENNReal.ofNat_ne_top, or_false] using hε.ne'
    obtain ⟨η, hη0, hη⟩ := exists_pos_setLIntegral_lt_of_measure_lt hFfin hε2
    let Pset := K ∩ {x | 0 ≤ f x}
    have hPset : Pset = K ∩ {x | 0 ≤ f x} := rfl
    let Nset := K ∩ {x | f x < 0}
    have hNset : Nset = K ∩ {x | f x < 0} := rfl
    have hPm : MeasurableSet Pset := hK.measurableSet.inter (measurableSet_le measurable_const hf)
    have hNm : MeasurableSet Nset := hK.measurableSet.inter (measurableSet_lt hf measurable_const)
    have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
    obtain ⟨C₁, hC₁P, hC₁, hC₁η⟩ := hPm.exists_isCompact_sdiff_lt
      (measure_ne_top_of_subset inter_subset_left hKfin) hη0.ne'
    obtain ⟨C₂, hC₂N, hC₂, hC₂η⟩ := hNm.exists_isCompact_sdiff_lt
      (measure_ne_top_of_subset inter_subset_left hKfin) hη0.ne'
    have hC₁K : C₁ ⊆ K := hC₁P.trans inter_subset_left
    have hC₂K : C₂ ⊆ K := hC₂N.trans inter_subset_left
    have hdisj : Disjoint C₁ C₂ := by
      rw [Set.disjoint_left]
      intro x h1 h2
      have a1 : 0 ≤ f x := (hC₁P h1).2
      have a2 : f x < 0 := (hC₂N h2).2
      exact absurd a1 (not_le.2 a2)
    have hA := claimA C₁ C₂ hC₁ hC₂ hC₁K hC₂K hdisj
    -- the remainders are small
    have hrem : ∀ A : Set (Eucl (m+1)), MeasurableSet A → A ⊆ K → volume A < η →
        ∫⁻ x in A, ‖f x‖ₑ < (ε : ℝ≥0∞) / 2 := by
      intro A hAm hAK hAη
      calc ∫⁻ x in A, ‖f x‖ₑ = ∫⁻ x in A, F x :=
            setLIntegral_congr_fun hAm (fun x hx => by simp only [indicator_of_mem (hAK hx), F])
        _ < (ε : ℝ≥0∞) / 2 := hη A hAη
    have r1 := hrem (Pset \ C₁) (hPm.diff hC₁.measurableSet) (sdiff_subset.trans inter_subset_left) hC₁η
    have r2 := hrem (Nset \ C₂) (hNm.diff hC₂.measurableSet) (sdiff_subset.trans inter_subset_left) hC₂η
    have e1 : ∫⁻ x in C₁, ‖f x‖ₑ = ENNReal.ofReal (∫ x in C₁, f x) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hint C₁ hC₁ (hC₁K.trans hKV))
        ((ae_restrict_iff' hC₁.measurableSet).2 (Eventually.of_forall (fun x hx => (hC₁P hx).2)))]
      exact setLIntegral_congr_fun hC₁.measurableSet (fun x hx => by
        rw [Real.enorm_of_nonneg (hC₁P hx).2])
    have e2 : ∫⁻ x in C₂, ‖f x‖ₑ = ENNReal.ofReal (-(∫ x in C₂, f x)) := by
      have hneg : IntegrableOn (fun x => -f x) C₂ := (hint C₂ hC₂ (hC₂K.trans hKV)).neg
      rw [← integral_neg, ofReal_integral_eq_lintegral_ofReal hneg
        ((ae_restrict_iff' hC₂.measurableSet).2 (Eventually.of_forall (fun x hx =>
          (neg_nonneg.2 (hC₂N hx).2.le))))]
      refine setLIntegral_congr_fun hC₂.measurableSet (fun x hx => ?_)
      rw [← enorm_neg (f x), Real.enorm_of_nonneg (neg_nonneg.2 (hC₂N hx).2.le)]
    have hKsplit : K = (C₁ ∪ (Pset \ C₁)) ∪ (C₂ ∪ (Nset \ C₂)) := by
      ext x
      constructor
      · intro hx
        by_cases h : 0 ≤ f x
        · by_cases h1 : x ∈ C₁
          · exact Or.inl (Or.inl h1)
          · exact Or.inl (Or.inr ⟨⟨hx, h⟩, h1⟩)
        · by_cases h2 : x ∈ C₂
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨⟨hx, lt_of_not_ge h⟩, h2⟩)
      · rintro ((h | h) | (h | h))
        · exact hC₁K h
        · exact h.1.1
        · exact hC₂K h
        · exact h.1.1
    have hle1 : ∫⁻ x in K, ‖f x‖ₑ ≤ ((∫⁻ x in C₁, ‖f x‖ₑ) + (∫⁻ x in Pset \ C₁, ‖f x‖ₑ)) +
        ((∫⁻ x in C₂, ‖f x‖ₑ) + (∫⁻ x in Nset \ C₂, ‖f x‖ₑ)) := by
      conv_lhs => rw [hKsplit]
      refine (lintegral_union_le (fun x => ‖f x‖ₑ) _ _).trans (add_le_add ?_ ?_)
      · exact lintegral_union_le (fun x => ‖f x‖ₑ) C₁ (Pset \ C₁)
      · exact lintegral_union_le (fun x => ‖f x‖ₑ) C₂ (Nset \ C₂)
    have hsum : ENNReal.ofReal (∫ x in C₁, f x) + ENNReal.ofReal (-(∫ x in C₂, f x)) ≤ ENNReal.ofReal c := by
      have p1 : 0 ≤ ∫ x in C₁, f x := setIntegral_nonneg hC₁.measurableSet (fun x hx => (hC₁P hx).2)
      have p2 : 0 ≤ -(∫ x in C₂, f x) :=
        neg_nonneg.2 (setIntegral_nonpos hC₂.measurableSet (fun x hx => (hC₂N hx).2.le))
      rw [← ENNReal.ofReal_add p1 p2, ← sub_eq_add_neg]
      exact ENNReal.ofReal_le_ofReal hA
    calc ∫⁻ x in K, ‖f x‖ₑ ≤ ((∫⁻ x in C₁, ‖f x‖ₑ) + (∫⁻ x in Pset \ C₁, ‖f x‖ₑ)) +
        ((∫⁻ x in C₂, ‖f x‖ₑ) + (∫⁻ x in Nset \ C₂, ‖f x‖ₑ)) := hle1
      _ ≤ (ENNReal.ofReal (∫ x in C₁, f x) + (ε : ℝ≥0∞) / 2) +
          (ENNReal.ofReal (-(∫ x in C₂, f x)) + (ε : ℝ≥0∞) / 2) := by
        exact add_le_add (add_le_add e1.le r1.le) (add_le_add e2.le r2.le)
      _ = (ENNReal.ofReal (∫ x in C₁, f x) + ENNReal.ofReal (-(∫ x in C₂, f x))) +
          ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := add_add_add_comm _ _ _ _
      _ ≤ ENNReal.ofReal c + ε := add_le_add hsum (ENNReal.add_halves _).le
  /- Step 3(ii) / Remark 2.35: the translation estimate. -/
  have hTE : ∀ (β : Eucl (m+1) → ℝ) (K V : Set (Eucl (m+1))) (δ B : ℝ), Measurable β → IsCompact K → IsOpen V →
    0 < δ → cthickening (2 * δ) K ⊆ V →
    (∀ K' : Set (Eucl (m+1)), IsCompact K' → K' ⊆ V → IntegrableOn β K') →
    (∀ (ψ : Eucl (m+1) → ℝ) (z : Eucl (m+1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∀ x, |ψ x| ≤ 1) → |∫ x, β x * fderiv ℝ ψ x z| ≤ ‖z‖ * B) →
    ∀ z : Eucl (m+1), ‖z‖ ≤ δ → ∫⁻ x in K, ‖β x - β (x - z)‖ₑ ≤ ENNReal.ofReal (‖z‖ * B) := by
    intro β K V δ B hβ hK hV hδ hKV hint hH z hz
    -- geometry: points of the δ-thickening stay in V after a shift by t•z, |t| ≤ 1
    have hshift : ∀ y ∈ thickening δ K, ∀ t : ℝ, |t| ≤ 1 → y - t • z ∈ cthickening (2 * δ) K := by
      intro y hy t ht
      obtain ⟨x, hxK, hyx⟩ := mem_thickening_iff.1 hy
      apply mem_cthickening_of_dist_le _ x _ _ hxK
      have h1 : ‖t • z‖ ≤ δ := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖z‖ ≤ 1 * δ := mul_le_mul ht hz (norm_nonneg _) zero_le_one
          _ = δ := one_mul δ
      calc dist (y - t • z) x = ‖(y - x) - t • z‖ := by rw [dist_eq_norm, sub_right_comm]
        _ ≤ ‖y - x‖ + ‖t • z‖ := norm_sub_le _ _
        _ ≤ δ + δ := add_le_add (by rw [← dist_eq_norm]; exact hyx.le) h1
        _ = 2 * δ := (two_mul δ).symm
    have hK2 : IsCompact (cthickening (2 * δ) K) := hK.cthickening
    have hβK2 : IntegrableOn β (cthickening (2 * δ) K) := hint _ hK2 hKV
    -- integrability of the translate on compact subsets of the δ-thickening
    have htrans : ∀ K' : Set (Eucl (m+1)), IsCompact K' → K' ⊆ thickening δ K →
        IntegrableOn (fun x => β (x - z)) K' := by
      intro K' hK' hK'V
      have hS : (fun x => x - z) '' K' ⊆ cthickening (2 * δ) K := by
        rintro _ ⟨x, hx, rfl⟩
        simpa only [one_smul] using hshift x (hK'V hx) 1 abs_one.le
      have hSc : IsCompact ((fun x => x - z) '' K') := hK'.image (continuous_id.sub continuous_const)
      have hI : Integrable (((fun x => x - z) '' K').indicator β) :=
        (integrable_indicator_iff hSc.measurableSet).2 (hβK2.mono_set hS)
      refine (hI.comp_sub_right z).integrableOn.congr_fun (fun x hx => ?_) hK'.measurableSet
      simp only
      rw [indicator_of_mem (show x - z ∈ (fun x => x - z) '' K' from ⟨x, hx, rfl⟩)]
    apply hL5 (fun x => β x - β (x - z)) K (thickening δ K) (‖z‖ * B)
      (hβ.sub (hβ.comp (measurable_id.sub_const z))) hK isOpen_thickening (self_subset_thickening hδ K)
    · intro K' hK' hK'V
      exact (hint K' hK' (fun y hy => hKV (by simpa only [zero_smul, sub_zero] using hshift y (hK'V hy) 0 (abs_zero.trans_le zero_le_one)))).sub
        (htrans K' hK' hK'V)
    · intro ψ hψ hψc hψV hψ1
      have hψd : Differentiable ℝ ψ := hψ.differentiable hT0
      have hKψ : IsCompact (tsupport ψ) := hψc
      have hKψV : tsupport ψ ⊆ V := fun y hy => hKV (by simpa only [zero_smul, sub_zero] using hshift y (hψV hy) 0 (abs_zero.trans_le zero_le_one))
      -- integrability of the two products
      have hI1 : Integrable (fun x => β x * ψ x) := by
        rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
        · exact (hint _ hKψ hKψV).mul_continuousOn hψ.continuous.continuousOn hKψ
        · intro x hx; exact subset_tsupport _ (right_ne_zero_of_mul hx)
      have hI2 : Integrable (fun x => β (x - z) * ψ x) := by
        rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
        · exact (htrans _ hKψ hψV).mul_continuousOn hψ.continuous.continuousOn hKψ
        · intro x hx; exact subset_tsupport _ (right_ne_zero_of_mul hx)
      have hI3 : Integrable (fun y => β y * ψ (y + z)) := by
        have := hI2.comp_add_right z
        simpa only [add_sub_cancel_right] using this
      -- reduce to the shifted difference
      have hshiftint : ∫ x, β (x - z) * ψ x = ∫ y, β y * ψ (y + z) := by
        have := integral_sub_right_eq_self (μ := (volume : Measure (Eucl (m+1))))
          (fun y => β y * ψ (y + z)) z
        simpa only [sub_add_cancel] using this
      have hsplit : ∫ x, (β x - β (x - z)) * ψ x = -∫ y, β y * (ψ (y + z) - ψ y) := by
        have e1 : (fun x => (β x - β (x - z)) * ψ x) = fun x => β x * ψ x - β (x - z) * ψ x := by
          funext x; ring
        have e2 : (fun y => β y * (ψ (y + z) - ψ y)) = fun y => β y * ψ (y + z) - β y * ψ y := by
          funext y; ring
        rw [e1, e2, integral_sub hI1 hI2, integral_sub hI3 hI1, hshiftint]
        ring
      -- fundamental theorem of calculus along the segment
      let D : ℝ → Eucl (m+1) → ℝ := fun t y => β y * fderiv ℝ ψ (y + t • z) z
      have hD : D = fun t y => β y * fderiv ℝ ψ (y + t • z) z := rfl
      have hFTC : ∀ y, ψ (y + z) - ψ y = ∫ t in (0:ℝ)..1, fderiv ℝ ψ (y + t • z) z := by
        intro y
        have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => ψ (y + t • z))
            (fderiv ℝ ψ (y + t • z) z) t := by
          intro t _
          have h1 : HasDerivAt (fun t : ℝ => y + t • z) z t := by
            simpa only [hasDerivAt_const_add_iff, id_eq, one_smul] using ((hasDerivAt_id t).smul_const z).const_add y
          exact (hψd (y + t • z)).hasFDerivAt.comp_hasDerivAt t h1
        have hcont : Continuous (fun t : ℝ => fderiv ℝ ψ (y + t • z) z) :=
          ((hψ.continuous_fderiv hT0).comp (continuous_const.add
            (continuous_id.smul continuous_const))).clm_apply continuous_const
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
        simp only [one_smul, zero_smul, add_zero]
      -- Fubini
      obtain ⟨C, hC⟩ := (hψc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv hT0)
      have : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) 1)) :=
        isFiniteMeasure_restrict.2 (by simp only [uIoc, zero_le_one, inf_of_le_left, sup_of_le_right, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true])
      have hmem : ∀ᵐ p ∂((volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Eucl (m+1)))),
          p.1 ∈ uIoc (0:ℝ) 1 := by
        have e : (volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Eucl (m+1))) =
            ((volume : Measure ℝ).prod (volume : Measure (Eucl (m+1)))).restrict (uIoc 0 1 ×ˢ univ) := by
          rw [← Measure.prod_restrict, Measure.restrict_univ]
        rw [e]
        filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod MeasurableSet.univ)] with p hp
        exact hp.1
      have hfz : ∀ x, x ∉ tsupport ψ → fderiv ℝ ψ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
      have hDint : Integrable (Function.uncurry D) ((volume.restrict (uIoc (0:ℝ) 1)).prod volume) := by
        have hbound : Integrable (fun p : ℝ × Eucl (m+1) =>
            (C * ‖z‖) * (cthickening (2 * δ) K).indicator (fun y => ‖β y‖) p.2)
            ((volume.restrict (uIoc (0:ℝ) 1)).prod volume) := by
          have h1 : Integrable (fun _ : ℝ => C * ‖z‖) (volume.restrict (uIoc (0:ℝ) 1)) :=
            integrable_const _
          have h2 : Integrable ((cthickening (2 * δ) K).indicator (fun y => ‖β y‖)) :=
            (integrable_indicator_iff hK2.measurableSet).2 hβK2.norm
          exact h1.mul_prod h2
        refine hbound.mono' ?_ ?_
        · exact ((hβ.comp measurable_snd).aestronglyMeasurable).mul
            (((hψ.continuous_fderiv hT0).comp (continuous_snd.add
              (continuous_fst.smul continuous_const))).clm_apply continuous_const).aestronglyMeasurable
        · filter_upwards [hmem] with p hp
          rcases p with ⟨t, y⟩
          have ht1 : |t| ≤ 1 := by
            rw [uIoc_of_le zero_le_one] at hp
            rw [abs_of_pos hp.1]; exact hp.2
          simp only [Function.uncurry_apply_pair, D, norm_mul]
          by_cases hy : y ∈ cthickening (2 * δ) K
          · rw [indicator_of_mem hy]
            calc ‖β y‖ * ‖fderiv ℝ ψ (y + t • z) z‖ ≤ ‖β y‖ * (C * ‖z‖) :=
                  mul_le_mul_of_nonneg_left (((fderiv ℝ ψ (y + t • z)).le_opNorm z).trans
                    (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))) (norm_nonneg _)
              _ = C * ‖z‖ * ‖β y‖ := by ring
          · have hnot : y + t • z ∉ tsupport ψ := by
              intro h
              apply hy
              simpa only [add_sub_cancel_right] using hshift (y + t • z) (hψV h) t ht1
            rw [hfz _ hnot, indicator_of_notMem hy]
            simp only [Real.norm_eq_abs, zero_apply, norm_zero, mul_zero, Std.le_refl]
      have hswap : ∫ y, β y * (ψ (y + z) - ψ y) = ∫ t in (0:ℝ)..1, ∫ y, D t y := by
        rw [intervalIntegral_integral_swap hDint]
        congr 1
        funext y
        rw [hFTC y, ← intervalIntegral.integral_const_mul]
      have hbd : ∀ t ∈ uIoc (0:ℝ) 1, ‖∫ y, D t y‖ ≤ ‖z‖ * B := by
        intro t ht
        have ht1 : |t| ≤ 1 := by
          rw [uIoc_of_le zero_le_one] at ht
          rw [abs_of_pos ht.1]; exact ht.2
        have hts : tsupport (fun y => ψ (y + t • z)) ⊆ V := by
          have e : (fun y => ψ (y + t • z)) = ψ ∘ (Homeomorph.addRight (t • z)) := rfl
          rw [e, tsupport_comp_eq_preimage]
          intro y hy
          apply hKV
          simpa only [add_sub_cancel_right] using hshift (y + t • z) (hψV hy) t ht1
        have h := hH (fun y => ψ (y + t • z)) z (hψ.comp (contDiff_id.add contDiff_const))
          (hψc.comp_homeomorph (Homeomorph.addRight (t • z))) hts (fun x => hψ1 _)
        simp only [fderiv_comp_add_right] at h
        rw [Real.norm_eq_abs]
        exact h
      have hfinal := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      rw [hsplit, hswap]
      rw [Real.norm_eq_abs] at hfinal
      have : |∫ t in (0:ℝ)..1, ∫ y, D t y| ≤ ‖z‖ * B := by simpa only [sub_zero, abs_one, mul_one] using hfinal
      exact (neg_le_abs _).trans this
  /- Step 4 (Simon 2.6 for this sequence): the mollification Cauchy estimate. -/
  have hR4 : ∀ (β : ℕ → Eucl (m+1) → ℝ) (K V : Set (Eucl (m+1))) (δ B : ℝ),
    (∀ j, Measurable (β j)) → IsCompact K → IsOpen V → 0 < δ → cthickening δ K ⊆ V → 0 ≤ B →
    (∀ j (K' : Set (Eucl (m+1))), IsCompact K' → K' ⊆ V → IntegrableOn (β j) K') →
    (∀ j (z : Eucl (m+1)), ‖z‖ ≤ δ → ∫⁻ x in K, ‖β j x - β j (x - z)‖ₑ ≤ ENNReal.ofReal (‖z‖ * B)) →
    (∀ φ : Eucl (m+1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ closedBall 0 δ →
      (∃ A : ℝ, ∀ j, ∀ x ∈ K, |∫ y, β j y * φ (x - y)| ≤ A) ∧
      ∀ x ∈ K, ∃ L : ℝ, Tendsto (fun j => ∫ y, β j y * φ (x - y)) atTop (𝓝 L)) →
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ x in K, ‖β j x - β k x‖ₑ ≤ ENNReal.ofReal η := by
    intro β K V δ B hβ hK hV hδ hKV hB hint hTE hmoll η hη
    -- choose the scale ε
    have hB1 : 0 < B + 1 := add_pos_of_nonneg_of_pos hB one_pos
    have hη4 : 0 < η / 4 / (B + 1) := div_pos (div_pos hη four_pos) hB1
    let ε : ℝ := min δ (η / 4 / (B + 1))
    have hε0 : 0 < ε := lt_min hδ hη4
    have hεδ : ε ≤ δ := min_le_left _ _
    have hεB : ε * B ≤ η / 4 :=
      calc ε * B ≤ η / 4 / (B + 1) * (B + 1) :=
            mul_le_mul (min_le_right _ _) (le_add_of_nonneg_right zero_le_one) hB hη4.le
        _ = η / 4 := div_mul_cancel₀ _ hB1.ne'
    -- normalized bump φ supported in closedBall 0 ε
    let b : ContDiffBump (0 : Eucl (m+1)) := ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩
    have hbint : Integrable (b : Eucl (m+1) → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    have hbpos : 0 < ∫ x, (b : Eucl (m+1) → ℝ) x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => b.nonneg) hbint, b.support_eq]
      exact measure_ball_pos _ _ hε0
    let I := ∫ x, (b : Eucl (m+1) → ℝ) x
    have hI : I = ∫ x, (b : Eucl (m+1) → ℝ) x := rfl
    let φ : Eucl (m+1) → ℝ := fun x => I⁻¹ * b x
    have hφ : φ = fun x => I⁻¹ * b x := rfl
    have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := contDiff_const.mul b.contDiff
    have hφc : HasCompactSupport φ := b.hasCompactSupport.mul_left
    have hφnn : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (inv_nonneg.2 hbpos.le) b.nonneg
    have hφint : ∫ x, φ x = 1 := by
      rw [hφ, integral_const_mul, ← hI, inv_mul_cancel₀ hbpos.ne']
    have hφsupp : ∀ z, φ z ≠ 0 → ‖z‖ ≤ ε := by
      intro z hz
      have : z ∈ Function.support (b : Eucl (m+1) → ℝ) := by
        intro h; exact hz (by simp only [h, mul_zero, φ])
      rw [b.support_eq] at this
      simpa only [ge_iff_le] using (mem_ball_zero_iff.1 this).le
    have hφts : tsupport φ ⊆ closedBall 0 δ := by
      refine (tsupport_mul_subset_right).trans ?_
      rw [b.tsupport_eq]
      exact closedBall_subset_closedBall hεδ
    obtain ⟨⟨A, hA⟩, hlim⟩ := hmoll φ hφs hφc hφts
    let G : ℕ → Eucl (m+1) → ℝ := fun j x => ∫ y, β j y * φ (x - y)
    have hG : G = fun j x => ∫ y, β j y * φ (x - y) := rfl
    have hφc0 : Continuous φ := hφs.continuous
    -- measurability of the mollifications
    have hGm : ∀ j, Measurable (G j) := by
      intro j
      have : StronglyMeasurable (Function.uncurry (fun x y => β j y * φ (x - y))) :=
        (((hβ j).comp measurable_snd).mul
          (hφc0.measurable.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
      exact (this.integral_prod_right).measurable
    -- mollification error, uniformly in j
    have herr : ∀ j, ∫⁻ x in K, ‖β j x - G j x‖ₑ ≤ ENNReal.ofReal (ε * B) := by
      intro j
      have hpt : ∀ x ∈ K, ‖β j x - G j x‖ₑ ≤
          ∫⁻ z, ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z) := by
        intro x hx
        -- integrability of the translated density against φ
        have hS : (fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε ⊆ V := by
          rintro _ ⟨z, hz, rfl⟩
          apply hKV
          apply mem_cthickening_of_dist_le _ x _ _ hx
          rw [dist_eq_norm]
          simpa only [sub_sub_cancel_left, norm_neg] using (mem_closedBall_zero_iff.1 hz).trans hεδ
        have hSc : IsCompact ((fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε) :=
          (isCompact_closedBall 0 ε).image (continuous_const.sub continuous_id)
        have hI0 : Integrable (((fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε).indicator (β j)) :=
          (integrable_indicator_iff hSc.measurableSet).2 (hint j _ hSc hS)
        have hI1 : IntegrableOn (fun z => β j (x - z)) (closedBall (0 : Eucl (m+1)) ε) := by
          refine (hI0.comp_sub_left x).integrableOn.congr_fun (fun z hz => ?_) measurableSet_closedBall
          simp only
          rw [indicator_of_mem (show x - z ∈ (fun z => x - z) '' closedBall (0 : Eucl (m+1)) ε from
            ⟨z, hz, rfl⟩)]
        have hI2 : Integrable (fun z => β j (x - z) * φ z) := by
          rw [← integrableOn_iff_integrable_of_support_subset (s := closedBall (0 : Eucl (m+1)) ε)]
          · exact hI1.mul_continuousOn hφc0.continuousOn (isCompact_closedBall 0 ε)
          · intro z hz
            exact mem_closedBall_zero_iff.2 (hφsupp z (right_ne_zero_of_mul hz))
        have hI3 : Integrable (fun z => β j x * φ z) :=
          (hφc0.integrable_of_hasCompactSupport hφc).const_mul _
        have hGx : G j x = ∫ z, β j (x - z) * φ z := by
          have := integral_sub_left_eq_self (fun y => β j y * φ (x - y))
            (volume : Measure (Eucl (m+1))) x
          simpa only [sub_sub_cancel] using this.symm
        have hdiff : β j x - G j x = ∫ z, (β j x - β j (x - z)) * φ z := by
          have e : (fun z => (β j x - β j (x - z)) * φ z) = fun z => β j x * φ z - β j (x - z) * φ z := by
            funext z; ring
          rw [e, integral_sub hI3 hI2, integral_const_mul, hφint, mul_one, hGx]
        rw [hdiff]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1
        funext z
        rw [enorm_mul, Real.enorm_of_nonneg (hφnn z)]
      have hjoint : Measurable (Function.uncurry
          (fun x z => ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z))) :=
        ((((hβ j).comp measurable_fst).sub ((hβ j).comp (measurable_fst.sub measurable_snd))).enorm).mul
          (ENNReal.measurable_ofReal.comp (hφc0.measurable.comp measurable_snd))
      calc ∫⁻ x in K, ‖β j x - G j x‖ₑ
          ≤ ∫⁻ x in K, ∫⁻ z, ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z) :=
            setLIntegral_mono hjoint.lintegral_prod_right' hpt
        _ = ∫⁻ z, ∫⁻ x in K, ‖β j x - β j (x - z)‖ₑ * ENNReal.ofReal (φ z) :=
            lintegral_lintegral_swap hjoint.aemeasurable
        _ = ∫⁻ z, ENNReal.ofReal (φ z) * ∫⁻ x in K, ‖β j x - β j (x - z)‖ₑ := by
            congr 1
            funext z
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
        _ ≤ ∫⁻ z, ENNReal.ofReal (φ z) * ENNReal.ofReal (ε * B) := by
            refine lintegral_mono (fun z => ?_)
            by_cases hz : φ z = 0
            · simp only [hz, ENNReal.ofReal_zero, zero_mul, Std.le_refl]
            · gcongr
              exact (hTE j z ((hφsupp z hz).trans hεδ)).trans
                (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hφsupp z hz) hB))
        _ = ENNReal.ofReal (ε * B) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
              ← ofReal_integral_eq_lintegral_ofReal (hφc0.integrable_of_hasCompactSupport hφc)
                (Eventually.of_forall hφnn), hφint, ENNReal.ofReal_one, one_mul]
    -- Cauchy property of the mollifications in L¹(K), from pointwise convergence
    have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
    have hGG : Tendsto (fun p : ℕ × ℕ => ∫⁻ x in K, ‖G p.1 x - G p.2 x‖ₑ) atTop (𝓝 0) := by
      have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict K)
        (l := (atTop : Filter (ℕ × ℕ))) (F := fun p x => ‖G p.1 x - G p.2 x‖ₑ) (f := fun _ => 0)
        (fun _ => ENNReal.ofReal (2 * A))
        (Eventually.of_forall (fun p => ((hGm p.1).sub (hGm p.2)).enorm))
        (Eventually.of_forall (fun p => by
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          have h1 := hA p.1 x hx
          have h2 := hA p.2 x hx
          have hA0 : 0 ≤ A := (abs_nonneg _).trans h1
          calc ‖G p.1 x - G p.2 x‖ₑ ≤ ‖G p.1 x‖ₑ + ‖G p.2 x‖ₑ := enorm_sub_le
            _ ≤ ENNReal.ofReal A + ENNReal.ofReal A := by
                rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
                exact add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
            _ = ENNReal.ofReal (2 * A) := by rw [← ENNReal.ofReal_add hA0 hA0, two_mul]))
        (by rw [lintegral_const, Measure.restrict_apply_univ]
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin)
        (by
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          obtain ⟨L, hL⟩ := hlim x hx
          have h1 : Tendsto (fun p : ℕ × ℕ => G p.1 x - G p.2 x) atTop (𝓝 (L - L)) := by
            rw [← prod_atTop_atTop_eq]
            exact (hL.comp tendsto_fst).sub (hL.comp tendsto_snd)
          rw [sub_self] at h1
          have h2 := (continuous_enorm.tendsto (0 : ℝ)).comp h1
          rw [enorm_zero] at h2
          exact h2)
      simpa only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, zero_mul] using h
    have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (half_pos hη)
    obtain ⟨N2, hN2⟩ := (ENNReal.tendsto_atTop_zero.1 hGG) (ENNReal.ofReal (η / 2)) hη2
    refine ⟨max N2.1 N2.2, fun j hj k hk => ?_⟩
    have hjk : ∫⁻ x in K, ‖G j x - G k x‖ₑ ≤ ENNReal.ofReal (η / 2) :=
      hN2 (j, k) ⟨le_trans (le_max_left _ _) hj, le_trans (le_max_right _ _) hk⟩
    have hm1 : Measurable (fun x => ‖β j x - G j x‖ₑ) := ((hβ j).sub (hGm j)).enorm
    have hm2 : Measurable (fun x => ‖G j x - G k x‖ₑ) := ((hGm j).sub (hGm k)).enorm
    calc ∫⁻ x in K, ‖β j x - β k x‖ₑ
        ≤ ∫⁻ x in K, (‖β j x - G j x‖ₑ + ‖G j x - G k x‖ₑ + ‖β k x - G k x‖ₑ) := by
          refine lintegral_mono (fun x => ?_)
          calc ‖β j x - β k x‖ₑ = ‖(β j x - G j x) + (G j x - G k x) - (β k x - G k x)‖ₑ := by
                congr 1; ring
            _ ≤ ‖(β j x - G j x) + (G j x - G k x)‖ₑ + ‖β k x - G k x‖ₑ := enorm_sub_le
            _ ≤ ‖β j x - G j x‖ₑ + ‖G j x - G k x‖ₑ + ‖β k x - G k x‖ₑ :=
                add_le_add (enorm_add_le _ _) le_rfl
      _ = (∫⁻ x in K, ‖β j x - G j x‖ₑ) + (∫⁻ x in K, ‖G j x - G k x‖ₑ) +
          (∫⁻ x in K, ‖β k x - G k x‖ₑ) := by
          have hm3 : Measurable (fun x => ‖β k x - G k x‖ₑ) := ((hβ k).sub (hGm k)).enorm
          rw [lintegral_add_right _ hm3, lintegral_add_right _ hm2]
      _ ≤ ENNReal.ofReal (ε * B) + ENNReal.ofReal (η / 2) + ENNReal.ofReal (ε * B) :=
          add_le_add (add_le_add (herr j) hjk) (herr k)
      _ ≤ ENNReal.ofReal η := by
          have h0 : 0 ≤ ε * B := mul_nonneg hε0.le hB
          rw [← ENNReal.ofReal_add h0 (half_pos hη).le,
            ← ENNReal.ofReal_add (add_nonneg h0 (half_pos hη).le) h0]
          exact ENNReal.ofReal_le_ofReal (by linarith only [hεB])
  have hhalf : ∀ k : ℕ, ENNReal.ofReal ((1/2 : ℝ) ^ k) = (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hint1 : ∀ a b : ℝ, (∃ k : ℤ, a = k) → (∃ k : ℤ, b = k) → a ≠ b → (1 : ℝ≥0∞) ≤ ‖a - b‖ₑ := by
    rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩ hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    have h1 : (1 : ℝ) ≤ |(p : ℝ) - q| := by
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hpq)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.one_le_ofReal.2 h1
  /- Step 6: Lebesgue points of `βh` in the blow-up form required by the tangent locality. -/
  have hLeb : ∀ (f : Eucl (m+1) → ℝ) (C : Set (Eucl (m+1))), IsCompact C → IntegrableOn f C →
      ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), ∀ ρ : ℝ, 0 < ρ → closedBall x ρ ⊆ C → ∀ R : ℝ, 0 < R →
        Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ (m+1))⁻¹) *
          ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ) (𝓝[>] 0) (𝓝 0) := by
    intro f C hC hf
    let g := C.indicator f
    have hg : g = C.indicator f := rfl
    have hgi : Integrable g := (integrable_indicator_iff hC.measurableSet).2 hf
    have hv := (Besicovitch.vitaliFamily (volume : Measure (Eucl (m+1)))).ae_tendsto_lintegral_enorm_sub_div
      hgi.locallyIntegrable
    filter_upwards [hv] with x hx ρ hρ hxC R hR
    have hxC' : x ∈ C := hxC (mem_closedBall_self hρ.le)
    have h1 := hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (Eucl (m+1))) x)
    have hRr : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa only [mul_zero] using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hR hr
    have h2 := h1.comp hRr
    let c0 : ℝ≥0∞ := volume (ball (0 : Eucl (m+1)) 1)
    have hc0 : c0 = volume (ball (0 : Eucl (m+1)) 1) := rfl
    have hc0fin : c0 ≠ ⊤ := measure_ball_lt_top.ne
    have h3 := ENNReal.Tendsto.const_mul h2
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc0fin) :
        (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal (R ^ (m+1)) * c0 ≠ ⊤)
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (show (0:ℝ) < ρ / R from div_pos hρ hR))] with r hr hrρ
    have hr0 : 0 < r := hr
    have hr0' : r ≠ 0 := hr0.ne'
    have hRrρ : R * r ≤ ρ := (le_div_iff₀' hR).1 hrρ
    have hball : closedBall x (R * r) ⊆ C := (closedBall_subset_closedBall hRrρ).trans hxC
    have hvolB : volume (closedBall x (R * r)) = ENNReal.ofReal ((R * r) ^ (m+1)) * c0 := by
      rw [Measure.addHaar_closedBall _ _ (mul_pos hR hr0).le, finrank_euclideanSpace, Fintype.card_fin]
    have hvol0 : volume (closedBall x (R * r)) ≠ 0 := (measure_closedBall_pos _ _ (mul_pos hR hr0)).ne'
    have hvolT : volume (closedBall x (R * r)) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hint : ∫⁻ z in closedBall x (R * r), ‖g z - g x‖ₑ =
        ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ := by
      refine setLIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
      simp only [g, indicator_of_mem (hball hz), indicator_of_mem hxC']
    simp only [Function.comp_apply]
    rw [hint]
    let I := ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ
    have hI : I = ∫⁻ z in closedBall x (R * r), ‖f z - f x‖ₑ := rfl
    calc ENNReal.ofReal (R ^ (m+1)) * c0 * (I / volume (closedBall x (R * r)))
        = (ENNReal.ofReal ((r ^ (m+1))⁻¹) * volume (closedBall x (R * r))) *
            (I / volume (closedBall x (R * r))) := by
          congr 1
          rw [hvolB, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hr0.le _))]
          congr 2
          rw [mul_pow, mul_comm (R ^ (m+1)), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr0'),
            one_mul]
      _ = ENNReal.ofReal ((r ^ (m+1))⁻¹) * I := by
          rw [mul_assoc, ENNReal.mul_div_cancel hvol0 hvolT]
  have hconstTan : ∀ (c : ℝ) (x : Eucl (m+1)),
      HasWeightedApproximateTangentSpaceAt (m+1) (univ : Set (Eucl (m+1))) (fun _ => c) x ⊤ := by
    intro c x
    refine ⟨by simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin], fun f => ?_⟩
    have himg : ∀ r : ℝ, 0 < r →
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (univ : Set (Eucl (m+1))) = univ := by
      intro r hr
      refine eq_univ_of_forall (fun y => ⟨x + r • y, mem_univ _, ?_⟩)
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [himg r hr, Measure.restrict_univ, Submodule.top_coe, Measure.restrict_univ, integral_mul_const,
      mul_comm]
  intro U hU Tj T hTj hbd hconv
  /- A compact exhaustion of `U` (no `infDist`). -/
  obtain ⟨K, hKc, hKU, hKmono, hKcov⟩ : ∃ K : ℕ → Set (Eucl (m+1)),
      (∀ l, IsCompact (K l)) ∧ (∀ l, K l ⊆ U) ∧ (∀ l l', l ≤ l' → K l ⊆ K l') ∧
      (∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → ∃ l, C ⊆ K l) := by
    refine ⟨fun l => {x | ‖x‖ ≤ l ∧ ∀ y, y ∉ U → ((l:ℝ) + 1)⁻¹ ≤ dist x y}, fun l => ?_,
      fun l x hx => ?_, fun l l' hll' x hx => ?_, fun C hC hCU => ?_⟩
    · apply isCompact_of_isClosed_isBounded
      · have h1 : IsClosed {x : Eucl (m+1) | ‖x‖ ≤ (l:ℝ)} := isClosed_le continuous_norm continuous_const
        have h2 : IsClosed {x : Eucl (m+1) | ∀ y, y ∉ U → ((l:ℝ) + 1)⁻¹ ≤ dist x y} := by
          simp only [ofPred_forall]
          exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
            isClosed_le continuous_const (continuous_id.dist continuous_const)))
        exact h1.inter h2
      · exact (isBounded_closedBall (x := (0 : Eucl (m+1))) (r := (l:ℝ))).subset
          (fun x hx => mem_closedBall_zero_iff.2 hx.1)
    · by_contra hxU
      exact absurd ((hx.2 x hxU).trans_eq (dist_self x)) (not_le.2 (inv_pos.2 (Nat.cast_add_one_pos l)))
    · have hl : (l:ℝ) ≤ l' := Nat.cast_le.2 hll'
      exact ⟨hx.1.trans hl, fun y hy => (inv_anti₀ (Nat.cast_add_one_pos l)
        (add_le_add_left hl 1)).trans (hx.2 y hy)⟩
    · obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
      obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Eucl (m+1))
      obtain ⟨l, hl⟩ := exists_nat_gt (max R δ⁻¹)
      have h1 : ((l:ℝ) + 1)⁻¹ ≤ δ := by
        rw [inv_le_comm₀ (Nat.cast_add_one_pos l) hδ]
        exact ((le_max_right R δ⁻¹).trans hl.le).trans (le_add_of_nonneg_right zero_le_one)
      refine ⟨l, fun x hx => ⟨(mem_closedBall_zero_iff.1 (hR hx)).trans
        ((le_max_left R δ⁻¹).trans hl.le), fun y hy => ?_⟩⟩
      by_contra hlt
      exact hy (hδU (mem_cthickening_of_dist_le y x δ C hx
        (by rw [dist_comm]; exact (le_of_lt (not_le.1 hlt)).trans h1)))
  /- Step 2: every `T_j` has a Borel integer-valued locally integrable density. -/
  have hdens : ∀ j, ∃ β : Eucl (m+1) → ℝ, Measurable β ∧ (∀ x, ∃ k : ℤ, β x = k) ∧
      (∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → IntegrableOn β C) ∧
      ∀ ω : TestFormOn U (m+1),
        Tj j ω = ∫ x, β x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
    intro j
    obtain ⟨M, θ, ξ, htr, hθN, hact⟩ := hTj j
    have hMn : NullMeasurableSet M (volume : Measure (Eucl (m+1))) := by
      rw [← hvol]; exact htr.nullMeasurableSet
    obtain ⟨M', hM'M, hM'm, hMM'⟩ := hMn.exists_measurable_subset_ae_eq
    let f : Eucl (m+1) → ℝ := fun x => θ x * ξ x dx
    have hf : f = fun x => θ x * ξ x dx := rfl
    let b : Eucl (m+1) → ℝ := M'.indicator f
    have hb : b = M'.indicator f := rfl
    have hbact : ∀ ω : TestFormOn U (m+1),
        Tj j ω = ∫ x, b x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
      intro ω
      rw [hact ω, tauAction, hvol, ← setIntegral_congr_set hMM', ← integral_indicator hM'm]
      congr 1
      funext x
      by_cases hx : x ∈ M'
      · simp only [b, indicator_of_mem hx, f]
        rw [hP1' (ξ x) ((ω : DifferentialForm (Eucl (m+1)) (m+1)) x)]
        ring
      · simp only [indicator_of_notMem hx, zero_mul, b]
    have hae : ∀ᵐ x ∂(volume.restrict M'), (∃ k : ℤ, f x = k) ∧ |f x| = θ x := by
      have ho := htr.orients
      rw [hvol] at ho
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hM'M ho, ae_restrict_mem hM'm]
        with x hx hxM'
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      obtain ⟨k, hk⟩ := hθN x (hM'M hxM')
      have hθpos := htr.pos x (hM'M hxM')
      have hs : ξ x dx = 1 ∨ ξ x dx = -1 := by
        rcases hξ with h | h <;> rw [h]
        · simpa only [simpleNVector_apply] using hP3 τ hτ
        · rcases hP3 τ hτ with h' | h' <;> simp only [neg_apply, simpleNVector_apply, h', or_true, neg_neg, true_or]
      refine ⟨?_, ?_⟩
      · rcases hs with h | h
        · exact ⟨k, by simp only [hk, h, mul_one, Int.cast_natCast, f]⟩
        · exact ⟨-k, by simp only [hk, h, mul_neg, mul_one, Int.cast_neg, Int.cast_natCast, f]⟩
      · rcases hs with h | h <;> simp only [h, mul_one, abs_of_pos hθpos, f, mul_neg, abs_neg]
    have hfm : AEStronglyMeasurable f (volume.restrict M') := by
      have hξm : AEStronglyMeasurable ξ (volume.restrict M) := by
        rw [← hvol]; exact htr.aestronglyMeasurable
      have hσ : AEStronglyMeasurable (fun x => ξ x dx) (volume.restrict M) :=
        hξm.apply_continuousLinearMap dx
      have hθ : AEStronglyMeasurable θ (volume.restrict M) := by
        have hMU : M = ⋃ l, M ∩ K l := by
          ext x
          constructor
          · intro hx
            obtain ⟨l, hl⟩ := hKcov {x} isCompact_singleton (singleton_subset_iff.2 (htr.subset hx))
            exact mem_iUnion.2 ⟨l, hx, hl rfl⟩
          · intro hx
            obtain ⟨l, hl⟩ := mem_iUnion.1 hx
            exact hl.1
        rw [hMU, aestronglyMeasurable_iUnion_iff]
        intro l
        have := htr.integrableOn (K l) (hKc l) (hKU l)
        rw [hvol] at this
        exact this.aestronglyMeasurable
      exact (hθ.mul hσ).mono_measure (Measure.restrict_mono hM'M le_rfl)
    have hbm : AEStronglyMeasurable b volume := (aestronglyMeasurable_indicator_iff hM'm).2 hfm
    have hbi : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → IntegrableOn b C := by
      intro C hC hCU
      have hθi := htr.integrableOn C hC hCU
      rw [hvol] at hθi
      have hfi : IntegrableOn f (M' ∩ C) := by
        refine (hθi.mono_set (inter_subset_inter_left _ hM'M)).mono' ?_ ?_
        · exact hfm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
        · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae] with x hx
          rw [Real.norm_eq_abs, hx.2]
      exact IntegrableOn.integrable_indicator
        (by rw [IntegrableOn, Measure.restrict_restrict hM'm]; exact hfi) hM'm
    obtain ⟨b', hb'm, hbb'⟩ : ∃ b' : Eucl (m+1) → ℝ, StronglyMeasurable b' ∧ b =ᵐ[volume] b' :=
      ⟨hbm.mk b, hbm.stronglyMeasurable_mk, hbm.ae_eq_mk⟩
    have hbz : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), ∃ k : ℤ, b x = k := by
      have h1 : ∀ᵐ x ∂(volume.restrict M'), ∃ k : ℤ, b x = k := by
        filter_upwards [hae, ae_restrict_mem hM'm] with x hx hxM'
        obtain ⟨k, hk⟩ := hx.1
        exact ⟨k, by simp only [indicator_of_mem hxM', hk, b]⟩
      have h2 : ∀ᵐ x ∂(volume.restrict M'ᶜ), ∃ k : ℤ, b x = k := by
        filter_upwards [ae_restrict_mem hM'm.compl] with x hx
        exact ⟨0, by simp only [indicator_of_notMem hx, Int.cast_zero, b]⟩
      exact ae_of_ae_restrict_of_ae_restrict_compl M' h1 h2
    let β : Eucl (m+1) → ℝ := fun x => if (∃ k : ℤ, b' x = k) then b' x else 0
    have hβ : β = fun x => if (∃ k : ℤ, b' x = k) then b' x else 0 := rfl
    have hset : MeasurableSet {x | ∃ k : ℤ, b' x = k} := by
      have : {x | ∃ k : ℤ, b' x = k} = b' ⁻¹' (range (Int.cast : ℤ → ℝ)) := by
        ext x
        simp only [mem_ofPred_eq, mem_preimage, mem_range, eq_comm]
      rw [this]
      exact hb'm.measurable (countable_range _).measurableSet
    have hβm : Measurable β := Measurable.ite hset hb'm.measurable measurable_const
    have hββ : b =ᵐ[volume] β := by
      filter_upwards [hbb', hbz] with x h1 h2
      have h3 : ∃ k : ℤ, b' x = k := h1 ▸ h2
      simp only [β, ite_eq_left h3, h1]
    refine ⟨β, hβm, fun x => ?_, fun C hC hCU => (hbi C hC hCU).congr_fun_ae (ae_restrict_of_ae hββ),
      fun ω => ?_⟩
    · by_cases h : ∃ k : ℤ, b' x = k
      · simp only [β, ite_eq_left h]
        exact h
      · simp only [β, ite_eq_right h]
        exact ⟨0, by simp only [Int.cast_zero]⟩
    · rw [hbact ω]
      exact integral_congr_ae (hββ.mono fun x hx => by simp only [hx])
  choose β hβm hβz hβi hβT using hdens
  /- Step 4: `(β j)` is Cauchy in L¹(C) for every compact `C ⊆ U`. -/
  have hCauchy : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ∫⁻ x in C, ‖β j x - β k x‖ₑ ≤ ENNReal.ofReal η := by
    intro C hC hCU η hη
    obtain ⟨r, hr0, hrU⟩ := hC.exists_cthickening_subset_open hU hCU
    let V : Set (Eucl (m+1)) := thickening r C
    have hVo : IsOpen V := isOpen_thickening
    have hVU : V ⊆ U := (thickening_subset_cthickening _ _).trans hrU
    have hδ0 : 0 < r / 4 := div_pos hr0 four_pos
    have h2δ : cthickening (2 * (r / 4)) C ⊆ V :=
      cthickening_subset_thickening' hr0 (by linarith only [hr0]) C
    have hδV : cthickening (r / 4) C ⊆ V :=
      (cthickening_mono (by linarith only [hr0]) C).trans h2δ
    have hS := hbd V ⟨hVo, hC.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening _ _), (closure_thickening_subset_cthickening _ _).trans hrU⟩
    let S := ⨆ j, ((Tj j).massOn V + (Tj j).boundary.massOn V)
    have hSfin : S ≠ ⊤ := hS.ne
    have hmT : ∀ j, (Tj j).massOn V ≤ S := fun j =>
      le_trans le_self_add (le_iSup (fun j => (Tj j).massOn V + (Tj j).boundary.massOn V) j)
    have hmB : ∀ j, (Tj j).boundary.massOn V ≤ S := fun j =>
      le_trans le_add_self (le_iSup (fun j => (Tj j).massOn V + (Tj j).boundary.massOn V) j)
    let B : ℝ := κ * S.toReal
    have hB0 : 0 ≤ B := mul_nonneg hκ0.le ENNReal.toReal_nonneg
    -- the boundary hypothesis of the translation estimate
    have hH : ∀ j (ψ : Eucl (m+1) → ℝ) (z : Eucl (m+1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ V → (∀ x, |ψ x| ≤ 1) →
        |∫ x, β j x * fderiv ℝ ψ x z| ≤ ‖z‖ * B := by
      intro j ψ z hψ hψc hψV hψ1
      rcases eq_or_ne z 0 with rfl | hz
      · simp only [map_zero, mul_zero, integral_zero, abs_zero, norm_zero, zero_mul, le_refl]
      obtain ⟨ω, hω⟩ := hform U m ψ (dx.curryLeft z) hψ hψc (hψV.trans hVU)
      have hωfun : (ω : DifferentialForm (Eucl (m+1)) m) = fun y => ψ y • dx.curryLeft z := funext hω
      have hval : (Tj j).boundary ω = ∫ x, β j x * fderiv ℝ ψ x z := by
        rw [GeometricCurrentOn.boundary_apply, hβT]
        congr 1
        funext x
        congr 1
        change exteriorDerivative (ω : DifferentialForm (Eucl (m+1)) m) x e = _
        rw [hωfun]
        exact hP7 ψ hψ z x
      have h1 := hmassb U m (Tj j).boundary V ω (κ * ‖z‖) (mul_pos hκ0 (norm_pos_iff.2 hz))
        (by rw [hωfun]; exact (tsupport_smul_subset_left _ _).trans hψV)
        (fun x => by
          rw [hω x, hP6]
          exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hψ1 x)).trans (hκN z))
        (ne_top_of_le_ne_top hSfin (hmB j))
      rw [hval] at h1
      calc |∫ x, β j x * fderiv ℝ ψ x z| ≤ κ * ‖z‖ * ((Tj j).boundary.massOn V).toReal := h1
        _ ≤ κ * ‖z‖ * S.toReal := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hSfin (hmB j))
            (mul_nonneg hκ0.le (norm_nonneg z))
        _ = ‖z‖ * B := by rw [mul_comm κ, mul_assoc]
    have hTEj : ∀ j (z : Eucl (m+1)), ‖z‖ ≤ r / 4 →
        ∫⁻ x in C, ‖β j x - β j (x - z)‖ₑ ≤ ENNReal.ofReal (‖z‖ * B) := fun j z hz =>
      hTE (β j) C V (r / 4) B (hβm j) hC hVo hδ0 h2δ
        (fun K' hK' hK'V => hβi j K' hK' (hK'V.trans hVU)) (hH j) z hz
    -- mollifications of the T_j are tested by `φ(x - ·) dx`
    have hmoll : ∀ φ : Eucl (m+1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ closedBall 0 (r / 4) →
        (∃ A : ℝ, ∀ j, ∀ x ∈ C, |∫ y, β j y * φ (x - y)| ≤ A) ∧
        ∀ x ∈ C, ∃ L : ℝ, Tendsto (fun j => ∫ y, β j y * φ (x - y)) atTop (𝓝 L) := by
      intro φ hφ hφc hφts
      obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
      have hax : ∀ x ∈ C, ∃ ω : TestFormOn U (m+1),
          (∀ y, (ω : DifferentialForm (Eucl (m+1)) (m+1)) y = φ (x - y) • dx) ∧
          tsupport (ω : DifferentialForm (Eucl (m+1)) (m+1)) ⊆ V ∧
          ∀ j, Tj j ω = ∫ y, β j y * φ (x - y) := by
        intro x hx
        have hts : tsupport (fun y => φ (x - y)) ⊆ V := by
          have e1 : (fun y => φ (x - y)) = φ ∘ (Homeomorph.subLeft x) := rfl
          rw [e1, tsupport_comp_eq_preimage]
          intro y hy
          apply hδV
          have h1 := hφts hy
          rw [mem_closedBall, dist_zero_right] at h1
          apply mem_cthickening_of_dist_le y x (r / 4) C hx
          rw [dist_comm, dist_eq_norm]
          simpa only [Homeomorph.subLeft_apply] using h1
        obtain ⟨ω, hω⟩ := hform U (m+1) (fun y => φ (x - y)) dx
          (hφ.comp (contDiff_const.sub contDiff_id))
          (hφc.comp_homeomorph (Homeomorph.subLeft x)) (hts.trans hVU)
        refine ⟨ω, hω, ?_, fun j => ?_⟩
        · rw [show (ω : DifferentialForm (Eucl (m+1)) (m+1)) = fun y => φ (x - y) • dx from funext hω]
          exact (tsupport_smul_subset_left _ _).trans hts
        · rw [hβT]
          congr 1
          funext y
          rw [hω y, ContinuousAlternatingMap.smul_apply, hdxe, smul_eq_mul, mul_one]
      have hCm : 0 < (|Cφ| + 1) * (covectorEuclideanNorm dx + 1) :=
        mul_pos (add_pos_of_nonneg_of_pos (abs_nonneg _) one_pos)
          (add_pos_of_nonneg_of_pos (covectorEuclideanNorm_nonneg _) one_pos)
      refine ⟨⟨(|Cφ| + 1) * (covectorEuclideanNorm dx + 1) * S.toReal, fun j x hx => ?_⟩,
        fun x hx => ?_⟩
      · obtain ⟨ω, hω, hωV, hωT⟩ := hax x hx
        rw [← hωT j]
        refine (hmassb U (m+1) (Tj j) V ω _ hCm hωV (fun y => ?_)
          (ne_top_of_le_ne_top hSfin (hmT j))).trans
          (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hSfin (hmT j)) hCm.le)
        rw [hω y, hP6]
        exact mul_le_mul ((Real.norm_eq_abs _).symm.le.trans ((hCφ _).trans ((le_abs_self Cφ).trans
          (le_add_of_nonneg_right zero_le_one)))) (le_add_of_nonneg_right zero_le_one)
          (covectorEuclideanNorm_nonneg _) (add_nonneg (abs_nonneg _) zero_le_one)
      · obtain ⟨ω, hω, hωV, hωT⟩ := hax x hx
        exact ⟨T ω, (hconv ω).congr (fun j => hωT j)⟩
    exact hR4 β C V (r / 4) B hβm hC hVo hδ0 hδV hB0
      (fun j K' hK' hK'V => hβi j K' hK' (hK'V.trans hVU)) hTEj hmoll η hη
  /- Step 4: a subsequence converging a.e. on `U` to an integer-valued Borel limit. -/
  have hN : ∀ l : ℕ, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ x in K l, ‖β j x - β k x‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ l := by
    intro l
    obtain ⟨N, hN⟩ := hCauchy (K l) (hKc l) (hKU l) ((1/2 : ℝ) ^ l) (pow_pos one_half_pos l)
    exact ⟨N, fun j hj k hk => (hN j hj k hk).trans (hhalf l).le⟩
  choose N hN using hN
  obtain ⟨φ, hφmono, hφN⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ l, N l ≤ φ l := by
    refine ⟨fun l => l + ∑ i ∈ Finset.range (l+1), N i, strictMono_nat_of_lt_succ (fun l => ?_),
      fun l => ?_⟩
    · show l + ∑ i ∈ Finset.range (l+1), N i < (l + 1) + ∑ i ∈ Finset.range (l+1+1), N i
      simp only [Finset.sum_range_succ]
      omega
    · have : N l ≤ ∑ i ∈ Finset.range (l+1), N i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ l)
      show N l ≤ l + ∑ i ∈ Finset.range (l+1), N i
      omega
  have hpair : ∀ l k k', l ≤ k → k ≤ k' →
      ∫⁻ x in K l, ‖β (φ k) x - β (φ k') x‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro l k k' hlk hkk'
    calc ∫⁻ x in K l, ‖β (φ k) x - β (φ k') x‖ₑ ≤ ∫⁻ x in K k, ‖β (φ k) x - β (φ k') x‖ₑ :=
          lintegral_mono_set (hKmono l k hlk)
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ k := hN k (φ k) (hφN k) (φ k') ((hφN k).trans (hφmono.monotone hkk'))
  have hev : ∀ l, ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ K l →
      ∀ᶠ k in atTop, β (φ (k+1)) x = β (φ k) x := by
    intro l
    let A : ℕ → Set (Eucl (m+1)) := fun k => K l ∩ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x}
     
    have hA : A = fun k => K l ∩ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} := rfl
    have hAle : ∀ k, volume (A k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
      intro k
      have hmeas : MeasurableSet {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} :=
        (measurableSet_eq_fun (hβm _) (hβm _)).compl
      calc volume (A k)
          = ∫⁻ x in K l, {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x}.indicator 1 x := by
            rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas, inter_comm]
        _ ≤ ∫⁻ x in K l, ‖β (φ (k + l)) x - β (φ (k + l + 1)) x‖ₑ := by
            refine lintegral_mono (fun x => ?_)
            by_cases hx : β (φ (k + l + 1)) x ≠ β (φ (k + l)) x
            · rw [indicator_of_mem (show x ∈ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} from hx),
                Pi.one_apply]
              exact hint1 _ _ (hβz _ x) (hβz _ x) (Ne.symm hx)
            · rw [indicator_of_notMem (show x ∉ {x | β (φ (k + l + 1)) x ≠ β (φ (k + l)) x} from hx)]
              exact zero_le
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + l) := hpair l (k + l) (k + l + 1) (by omega) (by omega)
        _ ≤ (2⁻¹ : ℝ≥0∞) ^ k := pow_le_pow_of_le_one (zero_le) (ENNReal.inv_le_one.2 one_le_two) (by omega)
    have hsum : ∑' k, volume (A k) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hAle)
      rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    filter_upwards [ae_eventually_notMem hsum] with x hx hxK
    rw [eventually_atTop] at hx ⊢
    obtain ⟨k0, hk0⟩ := hx
    refine ⟨k0 + l, fun k hk => ?_⟩
    have h1 := hk0 (k - l) (by omega)
    have e1 : k - l + l = k := by omega
    simp only [A, mem_inter_iff, mem_ofPred_eq, not_and, not_not, e1] at h1
    exact h1 hxK
  have hconvx : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ U →
      ∃ c, Tendsto (fun k => β (φ k) x) atTop (𝓝 c) ∧ ∃ z : ℤ, c = z := by
    filter_upwards [ae_all_iff.2 hev] with x hx hxU
    obtain ⟨l, hl⟩ := hKcov {x} isCompact_singleton (singleton_subset_iff.2 hxU)
    obtain ⟨k0, hk0⟩ := eventually_atTop.1 (hx l (hl rfl))
    have hconst : ∀ k ≥ k0, β (φ k) x = β (φ k0) x := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [hk0 k hk, ih]
    exact ⟨β (φ k0) x, tendsto_atTop_of_eventually_const hconst, hβz _ x⟩
  let βl : Eucl (m+1) → ℝ := fun x => limUnder atTop (fun k => β (φ k) x)
  have hβl : βl = fun x => limUnder atTop (fun k => β (φ k) x) := rfl
  have hβlm : Measurable βl :=
    (StronglyMeasurable.limUnder (fun k => (hβm (φ k)).stronglyMeasurable)).measurable
  let βh : Eucl (m+1) → ℝ := fun x => if (∃ k : ℤ, βl x = k) then βl x else 0
  have hβh : βh = fun x => if (∃ k : ℤ, βl x = k) then βl x else 0 := rfl
  have hβhm : Measurable βh := by
    have hset : MeasurableSet {x | ∃ k : ℤ, βl x = k} := by
      have : {x | ∃ k : ℤ, βl x = k} = βl ⁻¹' (range (Int.cast : ℤ → ℝ)) := by
        ext x
        simp only [eq_comm, mem_ofPred_eq, mem_preimage, mem_range]
      rw [this]
      exact hβlm (countable_range _).measurableSet
    exact Measurable.ite hset hβlm measurable_const
  have hβhz : ∀ x, ∃ k : ℤ, βh x = k := by
    intro x
    by_cases h : ∃ k : ℤ, βl x = k
    · simp only [βh, ite_eq_left h]
      exact h
    · simp only [βh, ite_eq_right h]
      exact ⟨0, by simp only [Int.cast_zero]⟩
  have hlim : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ U →
      Tendsto (fun k => β (φ k) x) atTop (𝓝 (βh x)) := by
    filter_upwards [hconvx] with x hx hxU
    obtain ⟨c, hc, z, hz⟩ := hx hxU
    have h1 : βl x = c := hc.limUnder_eq
    have h2 : βh x = c := by
      simp only [βh, h1]
      rw [ite_eq_left ⟨z, hz⟩]
    rw [h2]
    exact hc
  /- Fatou: L¹ convergence on the exhaustion. -/
  have hfatou : ∀ l k, l ≤ k → ∫⁻ x in K l, ‖β (φ k) x - βh x‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro l k hlk
    have hae : ∀ᵐ x ∂(volume.restrict (K l)),
        Tendsto (fun k' => ‖β (φ k) x - β (φ k') x‖ₑ) atTop (𝓝 ‖β (φ k) x - βh x‖ₑ) := by
      filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem (hKc l).measurableSet] with x hx hxK
      exact (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub (hx (hKU l hxK)))
    calc ∫⁻ x in K l, ‖β (φ k) x - βh x‖ₑ
        = ∫⁻ x in K l, liminf (fun k' => ‖β (φ k) x - β (φ k') x‖ₑ) atTop :=
          lintegral_congr_ae (hae.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun k' => ∫⁻ x in K l, ‖β (φ k) x - β (φ k') x‖ₑ) atTop :=
          lintegral_liminf_le' (fun k' => (((hβm _).sub (hβm _)).enorm).aemeasurable)
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ k :=
          liminf_le_of_frequently_le' ((eventually_atTop.2
            ⟨k, fun k' hk' => hpair l k k' hlk hk'⟩).frequently)
  have hβhi : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U → IntegrableOn βh C := by
    intro C hC hCU
    obtain ⟨l, hl⟩ := hKcov C hC hCU
    refine IntegrableOn.mono_set ?_ hl
    have h1 := hβi (φ l) (K l) (hKc l) (hKU l)
    refine ⟨hβhm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ x in K l, ‖βh x‖ₑ ≤ ∫⁻ x in K l, (‖β (φ l) x‖ₑ + ‖β (φ l) x - βh x‖ₑ) :=
          lintegral_mono (fun x => by
            calc ‖βh x‖ₑ = ‖β (φ l) x - (β (φ l) x - βh x)‖ₑ := by congr 1; ring
              _ ≤ ‖β (φ l) x‖ₑ + ‖β (φ l) x - βh x‖ₑ := enorm_sub_le)
      _ = (∫⁻ x in K l, ‖β (φ l) x‖ₑ) + ∫⁻ x in K l, ‖β (φ l) x - βh x‖ₑ :=
          lintegral_add_left ((hβm _).enorm) _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1.hasFiniteIntegral,
          (hfatou l l le_rfl).trans_lt (ENNReal.pow_lt_top (ENNReal.inv_lt_top.2 two_pos))⟩
  have hL1 : ∀ C : Set (Eucl (m+1)), IsCompact C → C ⊆ U →
      Tendsto (fun k => ∫⁻ x in C, ‖β (φ k) x - βh x‖ₑ) atTop (𝓝 0) := by
    intro C hC hCU
    obtain ⟨l, hl⟩ := hKcov C hC hCU
    have hgeom : Tendsto (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeom
      (Eventually.of_forall fun k => zero_le) ?_
    filter_upwards [eventually_ge_atTop l] with k hk
    exact (lintegral_mono_set hl).trans (hfatou l k hk)
  /- Step 5: `T = [[U]] ⌞ βh`. -/
  have hTβ : ∀ ω : TestFormOn U (m+1),
      T ω = ∫ x, βh x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
    intro ω
    let a : Eucl (m+1) → ℝ := fun x => (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e
    have ha : a = fun x => (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := rfl
    have hωc : Continuous (ω : DifferentialForm (Eucl (m+1)) (m+1)) := ω.property.1.1.continuous
    have hac : Continuous a := (continuous_eval_const e).comp hωc
    let KΩ := tsupport (ω : DifferentialForm (Eucl (m+1)) (m+1))
    have hKΩ : KΩ = tsupport (ω : DifferentialForm (Eucl (m+1)) (m+1)) := rfl
    have hKΩc : IsCompact KΩ := ω.property.1.2
    have hKΩU : KΩ ⊆ U := ω.property.2
    have ha0 : ∀ x, x ∉ KΩ → a x = 0 := by
      intro x hx
      simp only [a, image_eq_zero_of_notMem_tsupport hx]
      rfl
    obtain ⟨Ca, hCa⟩ : ∃ Ca : ℝ, ∀ x, |a x| ≤ Ca := by
      obtain ⟨Ca, hCa⟩ := hKΩc.exists_bound_of_continuousOn hac.continuousOn
      refine ⟨max Ca 0, fun x => ?_⟩
      by_cases hx : x ∈ KΩ
      · exact ((Real.norm_eq_abs (a x)).symm.le.trans (hCa x hx)).trans (le_max_left _ _)
      · rw [ha0 x hx, abs_zero]
        exact le_max_right _ _
    have hsupp : ∀ g : Eucl (m+1) → ℝ, Function.support (fun x => g x * a x) ⊆ KΩ := by
      intro g x hx
      by_contra h
      exact hx (show g x * a x = 0 by rw [ha0 x h, mul_zero])
    have hint : ∀ g : Eucl (m+1) → ℝ, IntegrableOn g KΩ → Integrable (fun x => g x * a x) := by
      intro g hg
      rw [← integrableOn_iff_integrable_of_support_subset (hsupp g)]
      exact hg.mul_continuousOn hac.continuousOn hKΩc
    have h1 : Tendsto (fun k => Tj (φ k) ω) atTop (𝓝 (T ω)) :=
      (hconv ω).comp hφmono.tendsto_atTop
    have h2 : Tendsto (fun k => ∫ x, β (φ k) x * a x) atTop (𝓝 (∫ x, βh x * a x)) := by
      have hbound : ∀ k, ‖(∫ x, β (φ k) x * a x) - ∫ x, βh x * a x‖ₑ ≤
          ENNReal.ofReal Ca * ∫⁻ x in KΩ, ‖β (φ k) x - βh x‖ₑ := by
        intro k
        rw [← integral_sub (hint _ (hβi (φ k) KΩ hKΩc hKΩU)) (hint _ (hβhi KΩ hKΩc hKΩU))]
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        rw [← lintegral_indicator hKΩc.measurableSet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono (fun x => ?_)
        by_cases hx : x ∈ KΩ
        · rw [indicator_of_mem hx, ← sub_mul, enorm_mul, mul_comm (ENNReal.ofReal Ca)]
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hCa x)
        · rw [indicator_of_notMem hx, ha0 x hx]
          simp
      have h3 : Tendsto (fun k => ENNReal.ofReal Ca * ∫⁻ x in KΩ, ‖β (φ k) x - βh x‖ₑ) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Ca) (hL1 KΩ hKΩc hKΩU)
          (Or.inr ENNReal.ofReal_ne_top)
        rwa [mul_zero] at this
      have h4 : Tendsto (fun k => ‖(∫ x, β (φ k) x * a x) - ∫ x, βh x * a x‖ₑ) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun k => zero_le) hbound
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h4
      simpa [Function.comp_def, toReal_enorm] using h5
    have h1' : Tendsto (fun k => ∫ x, β (φ k) x * a x) atTop (𝓝 (T ω)) :=
      h1.congr (fun k => hβT (φ k) ω)
    exact tendsto_nhds_unique h1' h2
  /- Step 6: the tangent spaces of `({βh ≠ 0}, |βh|)`. -/
  let Mh : Set (Eucl (m+1)) := {x | x ∈ U ∧ βh x ≠ 0}
  have hMh : Mh = {x | x ∈ U ∧ βh x ≠ 0} := rfl
  have hMhm : MeasurableSet Mh := hU.measurableSet.inter (hβhm (measurableSet_singleton 0).compl)
  have htan : ∀ᵐ x ∂(volume : Measure (Eucl (m+1))), x ∈ U → βh x ≠ 0 →
      HasWeightedApproximateTangentSpaceAt (m+1) Mh (fun x => |βh x|) x ⊤ := by
    have hall := ae_all_iff.2 (fun l => hLeb βh (K l) (hKc l) (hβhi _ (hKc l) (hKU l)))
    filter_upwards [hall] with x hx hxU hx0
    obtain ⟨ρ, hρ0, hρU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hxU)
    obtain ⟨l, hl⟩ := hKcov _ (isCompact_closedBall x ρ) hρU
    refine (Submission.iwl_weighted_tangent_locality (m+1) (m+1) Mh univ (fun y => |βh y|)
      (fun _ => |βh x|) x ?_ ?_ rfl ?_ ?_ ⊤).2 (hconstTan _ x)
    · rw [hvol]
      exact hMhm.nullMeasurableSet
    · rw [hvol]
      exact MeasurableSet.univ.nullMeasurableSet
    · refine ⟨ρ, hρ0, ?_, ?_⟩
      · rw [hvol]
        exact IntegrableOn.mono_set (Integrable.abs (hβhi _ (isCompact_closedBall x ρ) hρU))
          inter_subset_right
      · rw [hvol]
        exact (integrableOn_const (measure_closedBall_lt_top.ne)).mono_set inter_subset_right
    · intro R hR
      rw [hvol]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hx l ρ hρ0 hl R hR)
        (Eventually.of_forall fun r => zero_le) ?_
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_le_nhds (div_pos hρ0 hR))] with r hr hrρ
      have hRrρ : R * r ≤ ρ := (le_div_iff₀' hR).1 hrρ
      refine mul_le_mul_right (setLIntegral_mono ((hβhm.sub measurable_const).enorm)
        (fun z hz => ?_)) _
      have hzU : z ∈ U := hρU (closedBall_subset_closedBall hRrρ hz)
      have hind : Mh.indicator (fun x => |βh x|) z = |βh z| := by
        by_cases h0 : βh z = 0
        · rw [indicator_of_notMem (fun h => h.2 h0), h0, abs_zero]
        · rw [indicator_of_mem (show z ∈ Mh from ⟨hzU, h0⟩)]
      rw [hind, indicator_of_mem (mem_univ z)]
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub _ _)
  /- Step 6: `T = τ(Mh, |βh|, sign(βh) e₁ ∧ ⋯ ∧ eₙ)` is integer multiplicity. -/
  let ξ : Eucl (m+1) → NVector (Eucl (m+1)) (m+1) :=
    fun x => if 0 ≤ βh x then simpleNVector e else -simpleNVector e
  have hξ : ξ = fun x => if 0 ≤ βh x then simpleNVector e else -simpleNVector e := rfl
  have hval : ∀ (ω : TestFormOn U (m+1)) x,
      |βh x| * ξ x ((ω : DifferentialForm (Eucl (m+1)) (m+1)) x) =
        βh x * (ω : DifferentialForm (Eucl (m+1)) (m+1)) x e := by
    intro ω x
    by_cases h : 0 ≤ βh x
    · simp only [ξ, ite_eq_left h, simpleNVector_apply, abs_of_nonneg h]
    · simp only [ξ, ite_eq_right h, neg_apply, simpleNVector_apply,
        abs_of_neg (lt_of_not_ge h)]
      ring
  refine ⟨Mh, fun x => |βh x|, ξ, ⟨fun x hx => hx.1, (by rw [hvol]; exact hMhm.nullMeasurableSet), ?_,
    fun x hx => abs_pos.2 hx.2, fun C hC hCU => ?_, ?_, ?_⟩, fun x hx => ?_,
    fun ω => ?_⟩
  · refine ⟨∅, measure_empty, fun _ => id, fun _ => ⟨1, LipschitzWith.id⟩, fun x _ => Or.inr ?_⟩
    exact mem_iUnion.2 ⟨0, mem_range_self x⟩
  · rw [hvol]
    exact IntegrableOn.mono_set (Integrable.abs (hβhi C hC hCU)) inter_subset_right
  · exact (stronglyMeasurable_const.piecewise (measurableSet_le measurable_const hβhm)
      stronglyMeasurable_const).aestronglyMeasurable
  · rw [hvol]
    filter_upwards [ae_restrict_of_ae htan, ae_restrict_mem hMhm] with x hx hxM
    refine ⟨e, hbe ▸ (EuclideanSpace.basisFun (Fin (m+1)) ℝ).orthonormal, ?_, ?_⟩
    · have hspan : Submodule.span ℝ (range e) = ⊤ := by
        rw [← hbe, ← OrthonormalBasis.coe_toBasis]
        exact (EuclideanSpace.basisFun (Fin (m+1)) ℝ).toBasis.span_eq
      rw [hspan]
      exact hx hxM.1 hxM.2
    · by_cases h : 0 ≤ βh x
      · exact Or.inl (ite_eq_left h)
      · exact Or.inr (ite_eq_right h)
  · obtain ⟨k, hk⟩ := hβhz x
    exact ⟨k.natAbs, by simp only [hk, Nat.cast_natAbs, Int.cast_abs]⟩
  · rw [hTβ ω, tauAction, hvol]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Mh) (fun x hx => ?_)]
    · exact setIntegral_congr_fun hMhm (fun x _ => (hval ω x).symm)
    · by_cases hxU : x ∈ U
      · have h0 : βh x = 0 := by
          by_contra h
          exact hx ⟨hxU, h⟩
        simp [h0]
      · have h0 : (ω : DifferentialForm (Eucl (m+1)) (m+1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hxU (ω.property.2 h))
        simp [h0]

end GMT.Ch06
