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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
