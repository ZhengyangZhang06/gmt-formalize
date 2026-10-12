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

set_option maxHeartbeats 1000000 in
/-- **Positive density** (Steps 6–9 of the proof of Simon Ch. 6, Theorem 8.2, pp. 176–178).  If
`m + 2 ≤ P`, `T_j ∈ 𝒟_{m+1}(ℝ^P)` are integer multiplicity cycles with `sup_j M(T_j) < ∞`,
`T_j ⇀ T`, and (BLI) holds, then the mass measure `μ = μ_T` has positive upper density
`Θ*^{m+1}(μ, x)` at `μ`-a.e. `x`.

* (1) `∂(T ⌞ B_r(x))` is integer multiplicity for a.e. `r > 0`: slices of the `T_j` by `|· - x|`,
  Fatou, `iwl_restriction_weak_limit` and (BLI).
* (2)–(3) If `μ(B_δ(x)) < (κδ/(4·2^m(m+1)))^{m+1}`, some good `r ∈ (0, δ)` has
  `M(∂(T ⌞ B_r(x))) ≤ κ F(r)^m`, `F(r) = μ(B_r(x))^{1/(m+1)}`.  Otherwise the integrated slicing
  inequality (4.10) gives `F(b)^{m+1} - F(a)^{m+1} ≥ κ (b - a) F(a)^m`, hence uniform increments
  `F(a + s) ≥ F(a) + κ s/(2^m(m+1))`, and iterating them contradicts the smallness of `μ(B_δ(x))`.
* (4) For such `r` there is `S_r` with `∂S_r = ∂(T ⌞ B_r(x))`, `spt S_r ⊆ B̄_{3r}(x)` and
  `M(S_r) ≤ μ(B_r(x))/2`: for `m = 0` the boundary is an integer multiplicity `0`-current of mass
  `< 1`, hence `0` (footnote 5); for `m ≥ 1` the isoperimetric filling is compressed into
  `B_{3r}(x)` by `iwl_smooth_pushforward` along `y ↦ x + r Φ₀((y - x)/r)`, `Φ₀ = id` near `B̄₂(0)`.
* (5)–(6) Besicovitch disjoint closed balls cover `μ`-almost all of `{Θ* < ε₀}`; the cycles
  `S_i - T ⌞ B_i` satisfy the cone estimate `|Z(ω)| ≤ K L_ω R` (constant forms are exact), so
  `T(ω) ≤ μ(ℝ^P) - μ(⋃ B_i)/2 + O(δ)` for `|ω| ≤ 1`; lower semicontinuity of mass then forces
  `μ({Θ* < ε₀}) = 0`. -/
theorem Submission.iwl_positive_density : ∀ (P m : ℕ), m + 2 ≤ P → SlicingTheorem → IsoperimetricTheorem → LipschitzPushforwardIntegerMultiplicity → (∀ (Yj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Yj j).boundary) → (⨆ j, (Yj j).boundary.mass) < ∞ → WeaklyConvergesOn (fun j => (Yj j).boundary) Y.boundary → IsIntegerMultiplicity Y.boundary) → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ j, (Tj j).boundary = 0) → (⨆ j, (Tj j).mass) < ∞ → WeaklyConvergesOn Tj T → ∃ μ : Measure (Eucl P), IsMassMeasure T μ ∧ ∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x := by
  have iwl_restriction_weak_limit := Submission.iwl_restriction_weak_limit
  have iwl_smooth_pushforward := Submission.iwl_smooth_pushforward
  intro P m hmP hSlice hIso hLPF hBLI Tj T hTim hTbd hΛ hconv
  classical
  obtain ⟨-, hR1, hR2⟩ := Submission.iwl_restriction_theory
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
  /- ### Generic facts about currents on `ℝ^P`. -/
  have euclNormLe : ∀ {k : ℕ} (α : Covector (Eucl P) k),
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin k → Fin P)) * ‖α‖ := by
    intro k α
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
  have hsmul : ∀ {k : ℕ} (t : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro k t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  have hbdd : ∀ {k : ℕ} (θ : TestFormOn (univ : Set (Eucl P)) k), ∃ C : ℝ,
      ∀ y, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) k) y) ≤ C := by
    intro k θ
    obtain ⟨C, hC⟩ := θ.property.1.1.continuous.bounded_above_of_compact_support θ.property.1.2
    exact ⟨Real.sqrt (Fintype.card (Fin k → Fin P)) * C, fun y =>
      (euclNormLe _).trans (mul_le_mul_of_nonneg_left (hC y) (Real.sqrt_nonneg _))⟩
  have habs : ∀ {k : ℕ} (X : GeometricCurrentOn (univ : Set (Eucl P)) k)
      (θ : TestFormOn (univ : Set (Eucl P)) k) (C : ℝ), X.mass ≠ ∞ →
      (∀ y, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) k) y) ≤ C) →
      |X θ| ≤ X.mass.toReal * C := by
    intro k X θ C hX hC
    refine Submission.cmb_abs_apply_le_of_massOn_le P k univ univ X θ X.mass.toReal C
      ENNReal.toReal_nonneg ?_ (subset_univ _) hC
    rw [ENNReal.ofReal_toReal hX]
    exact le_rfl
  have hzero_of_mass : ∀ {k : ℕ} (X : GeometricCurrentOn (univ : Set (Eucl P)) k),
      X.mass = 0 → X = 0 := by
    intro k X hX
    apply GeometricCurrentOn.ext
    intro θ
    obtain ⟨C, hC⟩ := hbdd θ
    have h := habs X θ C (by rw [hX]; exact ENNReal.zero_ne_top) hC
    rw [hX, ENNReal.toReal_zero, zero_mul] at h
    rw [GeometricCurrentOn.zero_apply]
    exact abs_nonpos_iff.1 h
  have hmass_zero : ∀ {k : ℕ} (W : Set (Eucl P)),
      (0 : GeometricCurrentOn (univ : Set (Eucl P)) k).massOn W = 0 := by
    intro k W
    apply le_antisymm ?_ bot_le
    apply sSup_le
    rintro _ ⟨θ, -, rfl⟩
    simp
  have hzeroRestr : ∀ {k : ℕ} (A : Set (Eucl P)) (B : GeometricCurrentOn (univ : Set (Eucl P)) k),
      IsRestriction (0 : GeometricCurrentOn (univ : Set (Eucl P)) k) A B → B = 0 := by
    intro k A B hB
    have h0 : IsRestriction (0 : GeometricCurrentOn (univ : Set (Eucl P)) k) A 0 :=
      ⟨hB.1, 0, 0, fun θ => ⟨integrable_zero_measure, by simp⟩, fun θ => by simp⟩
    exact hR1 P k univ isOpen_univ 0 A B 0 hB h0
  have hF2 : ∀ {k : ℕ} (X : GeometricCurrentOn (univ : Set (Eucl P)) k)
      (θ₁ θ₂ : TestFormOn (univ : Set (Eucl P)) k) (N : Set (Eucl P)), IsOpen N →
      X.support ⊆ N → (∀ y ∈ N, (θ₁ : DifferentialForm (Eucl P) k) y =
        (θ₂ : DifferentialForm (Eucl P) k) y) → X θ₁ = X θ₂ := by
    intro k X θ₁ θ₂ N hN hsupp heq
    have hts : tsupport ((θ₁ - θ₂ : TestFormOn (univ : Set (Eucl P)) k) :
        DifferentialForm (Eucl P) k) ⊆ Nᶜ := by
      refine closure_minimal (fun y hy hyN => hy ?_) hN.isClosed_compl
      change (θ₁ : DifferentialForm (Eucl P) k) y - (θ₂ : DifferentialForm (Eucl P) k) y = 0
      rw [heq y hyN, sub_self]
    have h := Submission.isoperimetric_apply_eq_zero_of_disjoint_support P k univ X (θ₁ - θ₂)
      (Disjoint.mono_left hts (disjoint_compl_left_iff_subset.2 hsupp))
    change X.toCurrent (θ₁ - θ₂) = 0 at h
    rw [map_sub X.toCurrent θ₁ θ₂] at h
    exact sub_eq_zero.1 h
  /- Smoothness of pulled-back forms `y ↦ ω(Φ y) ∘ DΦ(y)`. -/
  have pullSmooth : ∀ {k : ℕ} (Φ : Eucl P → Eucl P) (ω : Eucl P → Covector (Eucl P) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => (ω (Φ y)).compContinuousLinearMap (fderiv ℝ Φ y)) := by
    intro k Φ ω hΦ hω
    have hexp : (fun y => (ω (Φ y)).compContinuousLinearMap (fderiv ℝ Φ y)) = fun y =>
        ∑ I : SimonMultiIndex k P, euclideanCovectorCoordinate
          ((ω (Φ y)).compContinuousLinearMap (fderiv ℝ Φ y)) I •
            wedgeCovectors k (fun j => EuclideanSpace.proj (I j)) := by
      funext y
      exact Submission.cmb_covector_eq_sum_coord_smul_wedge P k _
    rw [hexp]
    refine ContDiff.sum fun I _ => ?_
    suffices hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => euclideanCovectorCoordinate
        ((ω (Φ y)).compContinuousLinearMap (fderiv ℝ Φ y)) I) from hc.smul contDiff_const
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ Φ y) :=
      hΦ.fderiv_right (by simp)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y =>
        ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
          (fun _ : Fin k => Eucl P) (fun _ : Fin k => Eucl P) ℝ (fun _ => fderiv ℝ Φ y)) :=
      (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ => hD)
    let L : Covector (Eucl P) k →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Eucl P) ℝ :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => L (ω (Φ y))) :=
      L.contDiff.comp (hω.comp hΦ)
    have h3 := h1.clm_apply h2
    have h4 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Eucl P) ℝ
      (fun j => EuclideanSpace.single (I j) (1 : ℝ))).contDiff.comp h3
    convert h4 using 1
    funext y
    rfl
  /- Radial compression maps with uniformly bounded derivative. -/
  have hcomp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Eucl P) (r : ℝ), 0 < r →
      ∃ Φ : Eucl P → Eucl P, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
        (∀ y ∈ ball x (2 * r), Φ =ᶠ[𝓝 y] id) ∧ (∀ y, Φ y ∈ ball x (3 * r)) ∧
        (∀ y, ‖fderiv ℝ Φ y‖ ≤ C) ∧ (∀ y, 3 * r < dist y x → Φ =ᶠ[𝓝 y] fun _ => x) := by
    let b : ContDiffBump (0 : Eucl P) := ⟨2, 3, by norm_num, by norm_num⟩
    let Φ₀ : Eucl P → Eucl P := fun z => b z • z
    have hΦ₀s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₀ := b.contDiff.smul contDiff_id
    have hΦ₀c : HasCompactSupport Φ₀ := b.hasCompactSupport.smul_right
    obtain ⟨C, hC⟩ := (hΦ₀s.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (HasCompactSupport.fderiv (𝕜 := ℝ) hΦ₀c)
    refine ⟨C, (norm_nonneg _).trans (hC 0), fun x r hr => ?_⟩
    let g : Eucl P → Eucl P := fun y => r⁻¹ • (y - x)
    have hgc : Continuous g := (continuous_id.sub continuous_const).const_smul r⁻¹
    have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
      (contDiff_id.sub contDiff_const).const_smul r⁻¹
    have hgn : ∀ y, ‖g y‖ = r⁻¹ * dist y x := by
      intro y
      simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, dist_eq_norm]
    refine ⟨fun y => x + r • Φ₀ (g y), ?_, ?_, ?_, ?_, ?_⟩
    · exact contDiff_const.add ((hΦ₀s.comp hgs).const_smul r)
    · intro y hy
      have hgy : g y ∈ ball (0 : Eucl P) 2 := by
        rw [mem_ball_zero_iff, hgn, inv_mul_lt_iff₀ hr]
        rw [mem_ball] at hy
        linarith
      filter_upwards [hgc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hgy)] with z hz
      have h1 : b (g z) = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hz)
      show x + r • (b (g z) • g z) = z
      rw [h1, one_smul]
      simp only [g, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    · intro y
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have h3 : ‖Φ₀ (g y)‖ < 3 := by
        by_cases h0 : b (g y) = 0
        · simp [Φ₀, h0]
        · have hmem : g y ∈ ball (0 : Eucl P) 3 := by
            have := b.support_eq
            rw [← this]
            exact h0
          simp only [Φ₀, norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
          calc b (g y) * ‖g y‖ ≤ 1 * ‖g y‖ :=
                mul_le_mul_of_nonneg_right b.le_one (norm_nonneg _)
            _ < 3 := by simpa using (mem_ball_zero_iff.1 hmem)
      nlinarith
    · intro y
      have h1 : HasFDerivAt g (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P)) y :=
        ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x).const_smul r⁻¹
      have h2 : HasFDerivAt (fun y => Φ₀ (g y))
          ((fderiv ℝ Φ₀ (g y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P))) y :=
        ((hΦ₀s.differentiable (by simp)).differentiableAt (x := g y)).hasFDerivAt.comp y h1
      have h3 : HasFDerivAt (fun y => x + r • Φ₀ (g y))
          (r • (fderiv ℝ Φ₀ (g y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P))) y :=
        (h2.const_smul r).const_add x
      have heq : r • (fderiv ℝ Φ₀ (g y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P)) =
          fderiv ℝ Φ₀ (g y) := by
        refine ContinuousLinearMap.ext fun v => ?_
        simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, map_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      rw [h3.fderiv, heq]
      exact hC _
    · intro y hy
      have hgy : g y ∈ {z : Eucl P | 3 < ‖z‖} := by
        show 3 < ‖g y‖
        rw [hgn, lt_inv_mul_iff₀ hr]
        linarith
      filter_upwards [hgc.continuousAt.preimage_mem_nhds
        ((isOpen_lt continuous_const continuous_norm).mem_nhds hgy)] with z hz
      have h0 : b (g z) = 0 := b.zero_of_le_dist (by
        rw [dist_zero_right]; exact le_of_lt hz)
      show x + r • (b (g z) • g z) = x
      rw [h0, zero_smul, smul_zero, add_zero]
  /- An integer multiplicity `0`-current of mass `< 1` vanishes (footnote 5). -/
  have hZD : ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) 0, IsIntegerMultiplicity Z →
      Z.mass < 1 → Z = 0 := by
    intro Z hZ hm
    classical
    obtain ⟨M, θ, ξ, htri, hθN, hZeq⟩ := hZ
    set ν : Measure (Eucl P) := (μHE[0] : Measure (Eucl P)) with hν
    have hν0 : ν = μH[0] := MeasureTheory.Measure.euclideanHausdorffMeasure_zero
    have hsing : ∀ y : Eucl P, ν {y} = 1 := by
      intro y; rw [hν0]; exact Measure.hausdorffMeasure_zero_singleton y
    suffices hM : M = ∅ by
      apply GeometricCurrentOn.ext
      intro ω
      rw [hZeq ω]
      simp [tauAction, hM]
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hne
    have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
      intro x hx
      obtain ⟨k, hk⟩ := hθN x hx
      have hpos := htri.pos x hx
      rw [hk] at hpos ⊢
      have : k ≠ 0 := by rintro rfl; simp at hpos
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    -- an infinite set has infinite `ν`-measure
    have hinfm : ∀ s : Set (Eucl P), s.Infinite → ν s = ∞ := by
      intro s hs
      refine ENNReal.eq_top_of_forall_nnreal_le fun c => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge (c : ℝ)
      obtain ⟨F, hFs, hFc⟩ := hs.exists_subset_card_eq n
      calc (c : ℝ≥0∞) ≤ n := by exact_mod_cast hn
        _ = ∑ y ∈ F, ν {y} := by simp [hsing, hFc]
        _ = ν (⋃ y ∈ F, {y}) := (measure_biUnion_finset (fun a _ b _ hab => by
              simpa using hab) (fun y _ => measurableSet_singleton y)).symm
        _ ≤ ν s := measure_mono (Set.iUnion₂_subset fun y hy => Set.singleton_subset_iff.2 (hFs hy))
    have hfin : (M ∩ closedBall x₀ 1).Finite := by
      by_contra hinf
      have hint := htri.integrableOn (closedBall x₀ 1) (isCompact_closedBall _ _) (subset_univ _)
      have hnm : NullMeasurableSet (M ∩ closedBall x₀ 1) ν :=
        htri.nullMeasurableSet.inter measurableSet_closedBall.nullMeasurableSet
      have hle : ν (M ∩ closedBall x₀ 1) ≤ ∫⁻ x in M ∩ closedBall x₀ 1, ENNReal.ofReal (θ x) ∂ν := by
        rw [← setLIntegral_one]
        apply lintegral_mono_ae
        rw [ae_restrict_iff'₀ hnm]
        refine Eventually.of_forall fun x hx => ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hθ1 x hx.1)
      have hlt : ∫⁻ x in M ∩ closedBall x₀ 1, ENNReal.ofReal (θ x) ∂ν < ∞ := hint.lintegral_lt_top
      rw [hinfm _ hinf] at hle
      exact absurd (hle.trans_lt hlt) (lt_irrefl _)
    -- an isolating radius
    have hF : ((M ∩ closedBall x₀ 1) \ {x₀}).Finite := hfin.sdiff
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 hF.isClosed.isOpen_compl x₀ (by simp)
    set ρ := min ρ₀ 1 with hρ
    have hρpos : 0 < ρ := lt_min hρ₀ one_pos
    have hiso : ∀ y ∈ M, y ∈ ball x₀ ρ → y = x₀ := by
      intro y hyM hyb
      by_contra hne'
      have h1 : y ∈ ball x₀ ρ₀ := ball_subset_ball (min_le_left _ _) hyb
      have h2 : y ∈ closedBall x₀ 1 := ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hyb)
      exact hball h1 ⟨⟨hyM, h2⟩, hne'⟩
    -- the orientation at `x₀`
    let one0 : Covector (Eucl P) 0 := ContinuousAlternatingMap.constOfIsEmpty ℝ (Eucl P) (Fin 0) (1 : ℝ)
    have hor : ∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
        HasWeightedApproximateTangentSpaceAt 0 M θ x₀ (Submodule.span ℝ (range τ)) ∧
        (ξ x₀ = simpleNVector τ ∨ ξ x₀ = -simpleNVector τ) := by
      by_contra hcon
      have h := htri.orients
      rw [ae_iff] at h
      have hsub : ({x₀} : Set (Eucl P)) ⊆ {x | ¬∃ τ : Fin 0 → Eucl P, Orthonormal ℝ τ ∧
          HasWeightedApproximateTangentSpaceAt 0 M θ x (Submodule.span ℝ (range τ)) ∧
          (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)} := by
        intro z hz; rw [mem_singleton_iff] at hz; subst hz; exact hcon
      have h0 := measure_mono_null hsub h
      rw [Measure.restrict_apply (measurableSet_singleton x₀),
        (Set.singleton_subset_iff.2 hx₀ : ({x₀} : Set (Eucl P)) ⊆ M) |> Set.inter_eq_left.2,
        hsing] at h0
      exact one_ne_zero h0
    obtain ⟨τ, -, -, hτ⟩ := hor
    set s : ℝ := ξ x₀ one0 with hs
    have hs2 : s * s = 1 := by
      have h1 : simpleNVector τ one0 = 1 := by
        simp [one0, simpleNVector_apply]
      rcases hτ with h | h
      · rw [hs, h, h1]; norm_num
      · rw [hs, h]
        change -(simpleNVector τ one0) * -(simpleNVector τ one0) = 1
        rw [h1]; norm_num
    -- the test form
    let φ : ContDiffBump x₀ := ⟨ρ / 2, ρ, by positivity, by linarith⟩
    let ωf : DifferentialForm (Eucl P) 0 := fun y => (s * φ y) • one0
    have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ωf :=
      (contDiff_const.mul φ.contDiff).smul contDiff_const
    have hωc : HasCompactSupport ωf := by
      have : HasCompactSupport (fun y => s * φ y) := φ.hasCompactSupport.mul_left
      exact this.smul_right
    let ω : TestFormOn (univ : Set (Eucl P)) 0 := ⟨ωf, ⟨hωs, hωc⟩, subset_univ _⟩
    have hval : Z ω = θ x₀ := by
      rw [hZeq ω]
      unfold tauAction
      have hzero : ∀ y ∈ M \ {x₀}, θ y * ξ y (ωf y) = 0 := by
        intro y hy
        have hyb : y ∉ ball x₀ ρ := fun hb => hy.2 (hiso y hy.1 hb)
        have h0 : φ y = 0 := by
          by_contra h
          have : y ∈ Function.support φ := h
          rw [φ.support_eq] at this
          exact hyb this
        simp [ωf, h0]
      change ∫ x in M, θ x * ξ x (ωf x) ∂ν = θ x₀
      rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero htri.nullMeasurableSet
        (Set.singleton_subset_iff.2 hx₀) (Eventually.of_forall hzero), integral_singleton]
      have hφ1 : φ x₀ = 1 := φ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
      have hsing' : (μHE[0] : Measure (Eucl P)) {x₀} = 1 := hsing x₀
      simp only [measureReal_def, hsing', ENNReal.toReal_one, ωf, hφ1, mul_one, map_smul,
        smul_eq_mul, one_mul]
      rw [← hs, hs2, mul_one]
    have hnorm1 : covectorEuclideanNorm one0 = 1 := by
      unfold covectorEuclideanNorm
      have hsm : ∀ I : Fin 0 → Fin P, StrictMono I := fun I a => a.elim0
      simp [hsm, one0]
    have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) 0),
        covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
      intro t α
      unfold covectorEuclideanNorm
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · simp
    have hadm : ω ∈ massAdmissibleOn (univ : Set (Eucl P)) 0 univ := by
      refine ⟨subset_univ _, fun y => ?_⟩
      change covectorEuclideanNorm ((s * φ y) • one0) ≤ 1
      rw [hsmul, hnorm1, mul_one, abs_mul]
      have habs : |s| = 1 := by
        have := hs2
        nlinarith [abs_mul_abs_self s, abs_nonneg s]
      rw [habs, one_mul, abs_of_nonneg φ.nonneg]
      exact φ.le_one
    have hle := Z.le_massOn hadm
    rw [hval] at hle
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (θ x₀) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hθ1 x₀ hx₀)
    exact absurd (this.trans hle) (not_le.2 hm)
  /- ### Step 1: `∂T = 0`, `M(T) ≤ Λ`, the mass measure `μ`. -/
  set Λ : ℝ≥0∞ := ⨆ j, (Tj j).mass with hΛdef
  have hTb : T.boundary = 0 := by
    apply GeometricCurrentOn.ext
    intro θ
    have h1 := hconv.boundary θ
    have h2 : (fun j => (Tj j).boundary θ) = fun _ => (0 : ℝ) := by
      funext j; rw [hTbd j]; rfl
    rw [h2] at h1
    rw [GeometricCurrentOn.zero_apply]
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hTmass : T.mass ≤ Λ :=
    (hconv.massOn_le_liminf univ).trans (le_trans liminf_le_limsup limsup_le_iSup)
  have hTfinW : ∀ W, CompactlyContainedOpen W (univ : Set (Eucl P)) → T.massOn W < ∞ :=
    fun W _ => (T.massOn_mono (subset_univ W)).trans_lt (hTmass.trans_lt hΛ)
  obtain ⟨μ, hμ, hμres, hμmass⟩ := hR2 P (m + 1) univ isOpen_univ T hTfinW
  refine ⟨μ, hμ, ?_⟩
  obtain ⟨S₀, hS₀⟩ := hμres univ MeasurableSet.univ
  obtain ⟨μ', v', hrep, -⟩ := hS₀.2
  have hresval : ∀ (A : Set (Eucl P)) (R : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
      IsRestriction T A R → ∀ θ : TestFormOn (univ : Set (Eucl P)) (m + 1),
        R θ = ∫ y in A, v' y ((θ : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' := by
    intro A R hR θ
    obtain ⟨hA, μ₁, v₁, hrep₁, hR₁⟩ := hR
    rw [hR₁ θ]
    exact setInt isOpen_univ hrep₁ hrep hA θ
  have hS₀T : S₀ = T := by
    apply GeometricCurrentOn.ext
    intro θ
    rw [hresval univ S₀ hS₀ θ, Measure.restrict_univ]
    exact ((hrep θ).2).symm
  have hμuniv : μ univ = T.mass := by
    have h := hμmass univ S₀ hS₀ univ isOpen_univ (subset_univ _)
    rw [hS₀T, inter_univ] at h
    exact h.symm
  have hμfin : μ univ < ∞ := hμuniv ▸ (hTmass.trans_lt hΛ)
  have : IsFiniteMeasure μ := ⟨hμfin⟩
  have hresmass : ∀ (A : Set (Eucl P)) (R : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
      IsRestriction T A R → R.mass = μ A := by
    intro A R hR
    have h := hμmass A R hR univ isOpen_univ (subset_univ _)
    rw [univ_inter] at h
    exact h
  /- ### Restrictions of `T` to balls and slices by `dist · x`. -/
  have hballSet : ∀ (x : Eucl P) (r : ℝ),
      {y | y ∈ (univ : Set (Eucl P)) ∧ dist y x < r} = ball x r := by
    intro x r; ext y; simp [mem_ball]
  choose AB hAB using fun (x : Eucl P) (r : ℝ) =>
    hμres {y | y ∈ (univ : Set (Eucl P)) ∧ dist y x < r} (by rw [hballSet]; exact measurableSet_ball)
  have hd1 : ∀ x : Eucl P, LipschitzOnWith 1 (fun y => dist y x) (univ : Set (Eucl P)) :=
    fun x => (LipschitzWith.dist_left x).lipschitzOnWith
  have hdder : ∀ x : Eucl P, ∀ᵐ y ∂(volume : Measure (Eucl P)), y ∈ (univ : Set (Eucl P)) →
      ‖fderiv ℝ (fun y => dist y x) y‖₊ ≤ (1 : ℝ≥0) := by
    intro x
    refine Eventually.of_forall fun y _ => ?_
    have h := norm_fderiv_le_of_lipschitz ℝ (LipschitzWith.dist_left x) (x₀ := y)
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact_mod_cast h
  have hTfin2 : ∀ W, CompactlyContainedOpen W (univ : Set (Eucl P)) →
      T.massOn W < ∞ ∧ T.boundary.massOn W < ∞ :=
    fun W hW => ⟨hTfinW W hW, by rw [hTb, hmass_zero]; exact ENNReal.zero_lt_top⟩
  choose S hSsl hSsupp hSim hSint using fun x : Eucl P =>
    hSlice P m univ isOpen_univ T hTfin2 (fun y => dist y x) 1 (hd1 x)
  have hSeq : ∀ (x : Eucl P) (r : ℝ), S x r = (AB x r).boundary := by
    intro x r
    obtain ⟨A, B, hA, hB, hSAB⟩ := hSsl x r
    have hB' : IsRestriction (0 : GeometricCurrentOn (univ : Set (Eucl P)) m)
        {y | y ∈ (univ : Set (Eucl P)) ∧ dist y x < r} B := by rw [← hTb]; exact hB
    have hB0 : B = 0 := hzeroRestr _ B hB'
    have hAA : A = AB x r := hR1 P (m + 1) univ isOpen_univ T _ A (AB x r) hA (hAB x r)
    apply GeometricCurrentOn.ext
    intro θ
    rw [hSAB θ, hB0, hAA, GeometricCurrentOn.zero_apply, sub_zero]
  have hsph : ∀ x : Eucl P, ∀ᵐ r ∂(volume : Measure ℝ), μ (sphere x r) = 0 := by
    intro x
    have hc : {r : ℝ | 0 < μ (sphere x r)}.Countable :=
      Measure.countable_meas_pos_of_disjoint_iUnion (fun r => isClosed_sphere.measurableSet)
        (fun r₁ r₂ h => Set.disjoint_left.2 fun y h1 h2 => h (by
          rw [mem_sphere] at h1 h2; rw [← h1, ← h2]))
    filter_upwards [hc.ae_notMem volume] with r hr
    simpa [pos_iff_ne_zero] using hr
  /- ### Step 6 (printed (1)): `∂(T ⌞ B_r(x))` is integer multiplicity for a.e. `r > 0`. -/
  have hdm : ∀ x : Eucl P, Measurable (fun y : Eucl P => dist y x) :=
    fun x => (continuous_id.dist continuous_const).measurable
  have hB3 : ∀ x : Eucl P, ∀ᵐ r ∂(volume : Measure ℝ), 0 < r → IsIntegerMultiplicity (S x r) := by
    intro x
    have hTjmass : ∀ j, (Tj j).mass ≤ Λ := fun j => le_iSup (fun j => (Tj j).mass) j
    have hTjfin : ∀ j W, CompactlyContainedOpen W (univ : Set (Eucl P)) →
        (Tj j).massOn W < ∞ ∧ (Tj j).boundary.massOn W < ∞ := fun j W _ =>
      ⟨((Tj j).massOn_mono (subset_univ W)).trans_lt ((hTjmass j).trans_lt hΛ),
        by rw [hTbd j, hmass_zero]; exact ENNReal.zero_lt_top⟩
    choose Sj hSjsl hSjsupp hSjim hSjint using fun j =>
      hSlice P m univ isOpen_univ (Tj j) (hTjfin j) (fun y => dist y x) 1 (hd1 x)
    have hTjres : ∀ j (A : Set (Eucl P)), MeasurableSet A →
        ∃ R : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), IsRestriction (Tj j) A R ∧
          R.mass ≤ Λ := by
      intro j A hA
      obtain ⟨μj, -, hμjres, hμjmass⟩ :=
        hR2 P (m + 1) univ isOpen_univ (Tj j) (fun W hW => (hTjfin j W hW).1)
      obtain ⟨R, hR⟩ := hμjres A hA
      obtain ⟨S₁, hS₁⟩ := hμjres univ MeasurableSet.univ
      have hS₁T : S₁ = Tj j := by
        apply GeometricCurrentOn.ext
        intro θ
        obtain ⟨μ₁, v₁, hrep₁, hS₁v⟩ := hS₁.2
        rw [hS₁v θ, Measure.restrict_univ]
        exact ((hrep₁ θ).2).symm
      refine ⟨R, hR, ?_⟩
      have h1 := hμjmass A R hR univ isOpen_univ (subset_univ _)
      have h2 := hμjmass univ S₁ hS₁ univ isOpen_univ (subset_univ _)
      rw [hS₁T] at h2
      calc R.mass = μj (univ ∩ A) := h1
        _ ≤ μj (univ ∩ univ) := measure_mono (inter_subset_inter_right _ (subset_univ _))
        _ = (Tj j).mass := h2.symm
        _ ≤ Λ := hTjmass j
    have hSjeq : ∀ j t, ∃ A : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
        IsRestriction (Tj j) {y | y ∈ (univ : Set (Eucl P)) ∧ dist y x < t} A ∧
          Sj j t = A.boundary := by
      intro j t
      obtain ⟨A, B, hA, hB, hSAB⟩ := hSjsl j t
      have hB' : IsRestriction (0 : GeometricCurrentOn (univ : Set (Eucl P)) m)
          {y | y ∈ (univ : Set (Eucl P)) ∧ dist y x < t} B := by rw [← hTbd j]; exact hB
      have hB0 := hzeroRestr _ B hB'
      refine ⟨A, hA, ?_⟩
      apply GeometricCurrentOn.ext
      intro θ
      rw [hSAB θ, hB0, GeometricCurrentOn.zero_apply, sub_zero]
    choose Aj hAj hSjA using hSjeq
    have key : ∀ Nn : ℕ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) ((Nn : ℝ) + 1) →
        IsIntegerMultiplicity (S x t) := by
      intro Nn
      have hWfin : (⨆ j, (Tj j).massOn (ball x ((Nn : ℝ) + 2))) < ∞ :=
        (iSup_mono fun j => (Tj j).massOn_mono (subset_univ _)).trans_lt hΛ
      obtain ⟨ψ, Ex, hψ, hEx, hlim⟩ := iwl_restriction_weak_limit P (m + 1) univ isOpen_univ Tj T
        (ball x ((Nn : ℝ) + 2)) (fun y => dist y x) hconv isOpen_ball (subset_univ _) hWfin
        (continuous_id.dist continuous_const).continuousOn
      have hgj : ∀ j, ∃ g : ℝ → ℝ≥0∞, Measurable g ∧
          (∀ t ∈ Ioo (0 : ℝ) ((Nn : ℝ) + 1), (Sj j t).mass ≤ g t) ∧
          ∫⁻ t in Ioo (0 : ℝ) ((Nn : ℝ) + 1), g t ≤ Λ := by
        intro j
        obtain ⟨R, hR, hRm⟩ := hTjres j
          {y | y ∈ (univ : Set (Eucl P)) ∧ 0 < dist y x ∧ dist y x < (Nn : ℝ) + 1}
          (MeasurableSet.univ.inter ((measurableSet_lt measurable_const (hdm x)).inter
            (measurableSet_lt (hdm x) measurable_const)))
        obtain ⟨g, hg, hgle, hgint⟩ := hSjint j univ isOpen_univ (subset_refl _) 1 (hdder x) 0
          ((Nn : ℝ) + 1) (by positivity) R hR
        refine ⟨g, hg, hgle, hgint.trans ?_⟩
        rw [ENNReal.coe_one, one_mul]
        exact hRm
      choose g hgm hgle hgint using hgj
      set h : ℝ → ℝ≥0∞ := fun t => liminf (fun j => g (ψ j) t) atTop with hh
      have hhm : Measurable h := Measurable.liminf fun j => hgm (ψ j)
      have hhint : ∫⁻ t in Ioo (0 : ℝ) ((Nn : ℝ) + 1), h t ≤ Λ :=
        (lintegral_liminf_le fun j => hgm (ψ j)).trans
          (liminf_le_of_frequently_le' (Frequently.of_forall fun j => hgint (ψ j)))
      have hhfin : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) ((Nn : ℝ) + 1))), h t < ∞ :=
        ae_lt_top hhm (ne_top_of_le_ne_top hΛ.ne hhint)
      rw [ae_restrict_iff' measurableSet_Ioo] at hhfin
      have him : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j, IsIntegerMultiplicity (Sj (ψ j) t) :=
        ae_all_iff.2 fun j => hSjim (ψ j) (hTim (ψ j))
      filter_upwards [hhfin, him, hEx.ae_notMem volume] with t ht1 ht2 ht3 htI
      have hht := ht1 htI
      obtain ⟨-, hK⟩ := hlim t ht3 (fun j => Aj (ψ j) t) (AB x t) (fun j => hAj (ψ j) t) (hAB x t)
      have hconvA : WeaklyConvergesOn (fun j => Aj (ψ j) t) (AB x t) :=
        hK (closedBall x t) (isCompact_closedBall x t)
          (closedBall_subset_ball (by linarith [htI.2])) (fun y hy => by
            simpa [mem_closedBall] using hy.2)
      have hfreq : ∃ᶠ j in atTop, g (ψ j) t < h t + 1 :=
        frequently_lt_of_liminf_lt (by isBoundedDefault)
          (ENNReal.lt_add_right hht.ne one_ne_zero)
      obtain ⟨σ, hσ, hσg⟩ := extraction_of_frequently_atTop hfreq
      have hmassσ : (⨆ j, (Aj (ψ (σ j)) t).boundary.mass) < ∞ := by
        refine lt_of_le_of_lt (iSup_le fun j => ?_) (ENNReal.add_lt_top.2 ⟨hht, ENNReal.one_lt_top⟩)
        rw [← hSjA]
        exact (hgle (ψ (σ j)) t htI).trans (hσg j).le
      have hconvσ : WeaklyConvergesOn (fun j => (Aj (ψ (σ j)) t).boundary) (AB x t).boundary :=
        fun θ => (hconvA.boundary θ).comp hσ.tendsto_atTop
      have him' := hBLI (fun j => Aj (ψ (σ j)) t) (AB x t)
        (fun j => by rw [← hSjA]; exact ht2 (σ j)) hmassσ hconvσ
      rw [hSeq]
      exact him'
    have hall := ae_all_iff.2 key
    filter_upwards [hall] with t ht htpos
    obtain ⟨Nn, hNn⟩ := exists_nat_gt t
    exact ht Nn ⟨htpos, by linarith⟩
  /- ### The function `F x r = μ(B_r(x))^{1/(m+1)}`. -/
  set F : Eucl P → ℝ → ℝ := fun x r => (μ (ball x r)).toReal ^ (((m + 1 : ℕ) : ℝ)⁻¹) with hFdef
  /- ### Steps 7–8 (printed (2), (3)): radii with small boundary mass. -/
  have hC : ∀ (x : Eucl P) (κ δ : ℝ), 0 < κ → 0 < δ →
      (μ (ball x δ)).toReal < (κ * δ / (4 * 2 ^ m * ((m : ℝ) + 1))) ^ (m + 1) →
      ∃ r ∈ Ioo 0 δ, IsIntegerMultiplicity (S x r) ∧ μ (sphere x r) = 0 ∧
        (S x r).mass ≤ ENNReal.ofReal (κ * F x r ^ m) := by
    intro x κ δ hκ hδ hsmall
    by_contra hcon
    push Not at hcon
    have hgood : ∀ᵐ t ∂(volume : Measure ℝ), 0 < t →
        IsIntegerMultiplicity (S x t) ∧ μ (sphere x t) = 0 := by
      filter_upwards [hB3 x, hsph x] with t h1 h2 ht using ⟨h1 ht, h2⟩
    set f : ℝ → ℝ := fun r => (μ (ball x r)).toReal with hf
    have hfnn : ∀ r, 0 ≤ f r := fun r => ENNReal.toReal_nonneg
    have hfmono : Monotone f := fun r₁ r₂ h =>
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (ball_subset_ball h))
    have hFmono : Monotone (F x) := fun r₁ r₂ h =>
      Real.rpow_le_rpow (hfnn r₁) (hfmono h) (by positivity)
    have hFnn : ∀ r, 0 ≤ F x r := fun r => Real.rpow_nonneg (hfnn r) _
    have hFpow : ∀ r, F x r ^ (m + 1) = f r := fun r =>
      Real.rpow_inv_natCast_pow (hfnn r) (Nat.succ_ne_zero m)
    -- (3): `F > 0` on `(0, δ)`
    have hFpos : ∀ t ∈ Ioo 0 δ, 0 < F x t := by
      intro t₀ ht₀
      by_contra hle
      have hF0 : F x t₀ = 0 := le_antisymm (not_lt.1 hle) (hFnn t₀)
      have hex : ∃ t ∈ Ioo 0 t₀, IsIntegerMultiplicity (S x t) ∧ μ (sphere x t) = 0 := by
        by_contra hno
        push Not at hno
        have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ Ioo 0 t₀ := by
          filter_upwards [hgood] with t ht htI
          obtain ⟨h1, h2⟩ := ht htI.1
          exact hno t htI h1 h2
        have h2 := measure_eq_zero_iff_ae_notMem.2 h1
        rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h2
        linarith [ht₀.1]
      obtain ⟨t, ht, him, hsp⟩ := hex
      have hft : f t = 0 := by
        have h1 : f t ≤ f t₀ := hfmono ht.2.le
        have h0 : f t₀ = 0 := by rw [← hFpow t₀, hF0]; simp
        linarith [hfnn t]
      have hμt : μ (ball x t) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).1 hft with h | h
        · exact h
        · exact absurd h (measure_ne_top μ _)
      have hA0 : AB x t = 0 := by
        apply hzero_of_mass
        rw [hresmass _ _ (hAB x t), hballSet]
        exact hμt
      have hS0 : S x t = 0 := by
        rw [hSeq, hA0]
        apply GeometricCurrentOn.ext
        intro θ
        rfl
      have h1 := hcon t ⟨ht.1, ht.2.trans ht₀.2⟩ him hsp
      have h2 : (S x t).mass = 0 := by rw [hS0]; exact hmass_zero univ
      rw [h2] at h1
      exact absurd h1 (not_lt.2 bot_le)
    -- (2): the integrated slicing inequality
    have hC2 : ∀ a b, 0 < a → a < b → b < δ → κ * (b - a) * F x a ^ m ≤ f b - f a := by
      intro a b ha hab hbδ
      have hmeasab : MeasurableSet
          {y | y ∈ (univ : Set (Eucl P)) ∧ a < dist y x ∧ dist y x < b} :=
        MeasurableSet.univ.inter ((measurableSet_lt measurable_const (hdm x)).inter
          (measurableSet_lt (hdm x) measurable_const))
      obtain ⟨R, hR⟩ := hμres _ hmeasab
      obtain ⟨g, hg, hgle, hgint⟩ := hSint x univ isOpen_univ (subset_refl _) 1 (hdder x) a b hab R hR
      have hRm : R.massOn univ ≤ μ (ball x b) - μ (ball x a) := by
        have h := hμmass _ R hR univ isOpen_univ (subset_univ _)
        rw [h, ← measure_sdiff (ball_subset_ball hab.le) measurableSet_ball.nullMeasurableSet
          (measure_ne_top μ _)]
        apply measure_mono
        rintro y ⟨-, -, hy1, hy2⟩
        exact ⟨mem_ball.2 hy2, fun h => (not_lt.2 hy1.le) (mem_ball.1 h)⟩
      have hlow : ENNReal.ofReal (κ * F x a ^ m) * volume (Ioo a b) ≤ ∫⁻ t in Ioo a b, g t := by
        rw [← setLIntegral_const]
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hgood] with t ht htI
        obtain ⟨him, hsp⟩ := ht (ha.trans htI.1)
        have h1 := hcon t ⟨ha.trans htI.1, htI.2.trans hbδ⟩ him hsp
        have h2 : (S x t).mass ≤ g t := hgle t htI
        have h3 : ENNReal.ofReal (κ * F x a ^ m) ≤ ENNReal.ofReal (κ * F x t ^ m) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hFnn a) (hFmono htI.1.le) m) hκ.le)
        exact h3.trans (h1.le.trans h2)
      have htot : ENNReal.ofReal (κ * F x a ^ m * (b - a)) ≤ μ (ball x b) - μ (ball x a) := by
        rw [ENNReal.ofReal_mul (by positivity), ← Real.volume_Ioo]
        refine hlow.trans (hgint.trans ?_)
        rw [ENNReal.coe_one, one_mul]
        exact hRm
      have hfin : μ (ball x b) - μ (ball x a) ≠ ∞ :=
        ne_top_of_le_ne_top (measure_ne_top μ (ball x b)) tsub_le_self
      have h := (ENNReal.ofReal_le_iff_le_toReal hfin).1 htot
      rw [ENNReal.toReal_sub_of_le (measure_mono (ball_subset_ball hab.le)) (measure_ne_top μ _)] at h
      calc κ * (b - a) * F x a ^ m = κ * F x a ^ m * (b - a) := by ring
        _ ≤ f b - f a := h
    -- the uniform step
    set c : ℝ := κ / (2 ^ m * ((m : ℝ) + 1)) with hc
    have hcpos : 0 < c := by positivity
    have hstep : ∀ a s, 0 < a → 0 < s → a + s < δ → c * s ≤ F x a →
        F x a + c * s ≤ F x (a + s) := by
      intro a s ha hs hasδ hcs
      have hA := hFpos a ⟨ha, by linarith⟩
      have hAB : F x a ≤ F x (a + s) := hFmono (by linarith)
      by_cases h2 : F x (a + s) ≤ 2 * F x a
      · have h1 := hC2 a (a + s) ha (by linarith) hasδ
        rw [← hFpow, ← hFpow] at h1
        have hgeo : F x (a + s) ^ (m + 1) - F x a ^ (m + 1) ≤
            ((m : ℝ) + 1) * F x (a + s) ^ m * (F x (a + s) - F x a) := by
          rw [← geom_sum₂_mul]
          apply mul_le_mul_of_nonneg_right _ (sub_nonneg.2 hAB)
          calc ∑ i ∈ Finset.range (m + 1), F x (a + s) ^ i * F x a ^ (m + 1 - 1 - i)
              ≤ ∑ _i ∈ Finset.range (m + 1), F x (a + s) ^ m := by
                apply Finset.sum_le_sum
                intro i hi
                have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
                calc F x (a + s) ^ i * F x a ^ (m + 1 - 1 - i)
                    ≤ F x (a + s) ^ i * F x (a + s) ^ (m + 1 - 1 - i) :=
                      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.le hAB _)
                        (pow_nonneg (hA.le.trans hAB) _)
                  _ = F x (a + s) ^ m := by rw [← pow_add]; congr 1; omega
            _ = ((m : ℝ) + 1) * F x (a + s) ^ m := by simp
        have hBm : F x (a + s) ^ m ≤ 2 ^ m * F x a ^ m := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hA.le.trans hAB) h2 m
        have hApos : 0 < F x a ^ m := pow_pos hA m
        have hkey : κ * s * F x a ^ m ≤
            (((m : ℝ) + 1) * 2 ^ m * (F x (a + s) - F x a)) * F x a ^ m := by
          calc κ * s * F x a ^ m = κ * (a + s - a) * F x a ^ m := by ring
            _ ≤ F x (a + s) ^ (m + 1) - F x a ^ (m + 1) := h1
            _ ≤ ((m : ℝ) + 1) * F x (a + s) ^ m * (F x (a + s) - F x a) := hgeo
            _ ≤ ((m : ℝ) + 1) * (2 ^ m * F x a ^ m) * (F x (a + s) - F x a) := by
                apply mul_le_mul_of_nonneg_right _ (sub_nonneg.2 hAB)
                exact mul_le_mul_of_nonneg_left hBm (by positivity)
            _ = (((m : ℝ) + 1) * 2 ^ m * (F x (a + s) - F x a)) * F x a ^ m := by ring
        have hks : κ * s ≤ ((m : ℝ) + 1) * 2 ^ m * (F x (a + s) - F x a) :=
          le_of_mul_le_mul_right hkey hApos
        have : c * s ≤ F x (a + s) - F x a := by
          rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          linarith
        linarith
      · push Not at h2
        linarith
    have hiter : ∀ (a₀ σ : ℝ), 0 < a₀ → 0 < σ → c * σ ≤ F x a₀ → ∀ k : ℕ,
        a₀ + k * σ < δ → F x a₀ + c * (k * σ) ≤ F x (a₀ + k * σ) := by
      intro a₀ σ ha₀ hσ hcσ k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        push_cast at hk
        have hk' : a₀ + k * σ < δ := by nlinarith
        have ih' := ih hk'
        have hstep' := hstep (a₀ + k * σ) σ (by positivity) hσ (by linarith)
          (hcσ.trans (hFmono (by nlinarith)))
        push_cast
        calc F x a₀ + c * ((k + 1) * σ) = (F x a₀ + c * (k * σ)) + c * σ := by ring
          _ ≤ F x (a₀ + k * σ) + c * σ := by linarith
          _ ≤ F x (a₀ + k * σ + σ) := hstep'
          _ = F x (a₀ + (k + 1) * σ) := by ring_nf
    have hF34 : c * δ / 4 ≤ F x (3 * δ / 4) := by
      have ha₀ : (0 : ℝ) < δ / 4 := by positivity
      have hFa₀ := hFpos (δ / 4) ⟨ha₀, by linarith⟩
      by_cases hbig : c * δ / 4 ≤ F x (δ / 4)
      · exact hbig.trans (hFmono (by linarith))
      · push Not at hbig
        set σ := F x (δ / 4) / c with hσdef
        have hσpos : 0 < σ := div_pos hFa₀ hcpos
        have hσlt : σ < δ / 4 := by
          rw [hσdef, div_lt_iff₀ hcpos]; linarith
        have hcσ : c * σ ≤ F x (δ / 4) := by
          rw [hσdef, mul_div_cancel₀ _ hcpos.ne']
        set k := ⌊(δ / 2) / σ⌋₊ with hkdef
        have hk1 : (k : ℝ) * σ ≤ δ / 2 := by
          have := Nat.floor_le (div_nonneg (by positivity : (0 : ℝ) ≤ δ / 2) hσpos.le)
          rw [← hkdef, le_div_iff₀ hσpos] at this
          exact this
        have hk2 : δ / 2 < ((k : ℝ) + 1) * σ := by
          have := Nat.lt_floor_add_one ((δ / 2) / σ)
          rw [← hkdef, div_lt_iff₀ hσpos] at this
          exact this
        have h := hiter (δ / 4) σ ha₀ hσpos hcσ k (by linarith)
        calc c * δ / 4 ≤ c * (k * σ) := by nlinarith
          _ ≤ F x (δ / 4) + c * (k * σ) := by linarith [hFnn (δ / 4)]
          _ ≤ F x (δ / 4 + k * σ) := h
          _ ≤ F x (3 * δ / 4) := hFmono (by linarith)
    have hfδ : (c * δ / 4) ^ (m + 1) ≤ f δ := by
      calc (c * δ / 4) ^ (m + 1) ≤ F x (3 * δ / 4) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) hF34 _
        _ = f (3 * δ / 4) := hFpow _
        _ ≤ f δ := hfmono (by linarith)
    have hceq : c * δ / 4 = κ * δ / (4 * 2 ^ m * ((m : ℝ) + 1)) := by
      rw [hc, div_mul_eq_mul_div, div_div]
      congr 1
      ring
    rw [hceq] at hfδ
    exact absurd hsmall (not_lt.2 hfδ)
  /- ### Step 8 (printed (4), footnote 5): comparison surfaces. -/
  have hIsoP : ∀ m' : ℕ, m = m' + 1 → ∃ c₁ : ℝ≥0,
      ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) (m' + 1),
      IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 →
      ∃ R : GeometricCurrentOn (univ : Set (Eucl P)) (m' + 2), IsIntegerMultiplicity R ∧
        IsCompact R.support ∧ R.boundary = Z ∧
        R.mass ^ (((m' + 1 : ℕ) : ℝ) / ((m' + 2 : ℕ) : ℝ)) ≤ c₁ * Z.mass := by
    intro m' hm'
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, P = m' + 2 + ℓ := ⟨P - (m' + 2), by omega⟩
    subst hℓ
    exact hIso m' ℓ (by omega)
  have hD : ∃ κ : ℝ, 0 < κ ∧ ∀ (x : Eucl P) (r : ℝ), 0 < r → IsIntegerMultiplicity (S x r) →
      (S x r).mass ≤ ENNReal.ofReal (κ * F x r ^ m) →
      ∃ Sr : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
        (∀ θ, Sr.boundary θ = (AB x r).boundary θ) ∧
        (∀ θ : TestFormOn (univ : Set (Eucl P)) (m + 1),
          Disjoint (tsupport (θ : DifferentialForm (Eucl P) (m + 1))) (closedBall x (3 * r)) →
            Sr θ = 0) ∧
        Sr.mass ≤ 2⁻¹ * μ (ball x r) := by
    have hSsph : ∀ x r, (S x r).support ⊆ sphere x r := fun x r y hy => by
      have h := (hSsupp x r hy).2
      exact h
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      refine ⟨1 / 2, by norm_num, fun x r hr him hmass => ⟨0, fun θ => ?_, fun θ _ => rfl, ?_⟩⟩
      · have hlt : (S x r).mass < 1 := by
          refine hmass.trans_lt ?_
          rw [pow_zero, mul_one, ← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
        have hS0 : S x r = 0 := hZD (S x r) him hlt
        rw [← hSeq, hS0]
        rfl
      · rw [show (0 : GeometricCurrentOn (univ : Set (Eucl P)) (0 + 1)).mass = 0 from
          hmass_zero (k := 0 + 1) univ]
        exact bot_le
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨c₁, hc₁⟩ := hIsoP m' rfl
      obtain ⟨CΦ, hCΦ0, hΦ⟩ := hcomp
      set κ : ℝ := 1 / (4 * (CΦ + 1) ^ (m' + 2) * ((c₁ : ℝ) + 1)) with hκdef
      have hκpos : 0 < κ := by positivity
      refine ⟨κ, hκpos, fun x r hr him hmass => ?_⟩
      set Z := S x r with hZdef
      have hZb : Z.boundary = 0 := by
        rw [hZdef, hSeq]; exact GeometricCurrentOn.boundary_boundary _
      have hZsupp : Z.support ⊆ sphere x r := hSsph x r
      have hZcl : IsClosed Z.support := by
        have h : Z.support = Z.zeroRegionᶜ := by
          ext y; simp [GeometricCurrentOn.support]
        rw [h]; exact Z.isOpen_zeroRegion.isClosed_compl
      have hZcpt : IsCompact Z.support := (isCompact_sphere x r).of_isClosed_subset hZcl hZsupp
      obtain ⟨S', hS'im, hS'cpt, hS'b, hS'mass⟩ := hc₁ Z him hZcpt hZb
      obtain ⟨Φ, hΦs, hΦid, hΦball, hΦd, hΦfar⟩ := hΦ x r hr
      obtain ⟨Sr, -, hSrval, hSrbval, hSrmass⟩ := iwl_smooth_pushforward hLPF P P (m' + 1) univ univ
        isOpen_univ isOpen_univ S' Φ hS'im hΦs (mapsTo_univ _ _)
        (fun K hK _ => hS'cpt.inter_left (hK.isClosed.preimage hΦs.continuous))
      refine ⟨Sr, fun θ => ?_, fun θ hθ => ?_, ?_⟩
      · have hpbs := pullSmooth Φ (θ : DifferentialForm (Eucl P) (m' + 1)) hΦs θ.property.1.1
        have hpbc : HasCompactSupport (fun y => ((θ : DifferentialForm (Eucl P) (m' + 1))
            (Φ y)).compContinuousLinearMap (fderiv ℝ Φ y)) := by
          refine HasCompactSupport.intro (isCompact_closedBall x (3 * r)) fun y hy => ?_
          have hfar : 3 * r < dist y x := by
            rw [mem_closedBall, not_le] at hy; exact hy
          have hd0 : fderiv ℝ Φ y = 0 := by
            rw [(hΦfar y hfar).fderiv_eq]; exact fderiv_const_apply x
          rw [hd0]
          ext v
          simp
        let η : TestFormOn (univ : Set (Eucl P)) (m' + 1) := ⟨_, ⟨hpbs, hpbc⟩, subset_univ _⟩
        have h1 := hSrbval θ η ⟨univ, isOpen_univ, subset_univ _, fun y _ => rfl⟩
        have h2 : S'.boundary η = Z η := by rw [hS'b]
        have h3 : Z η = Z θ := by
          apply hF2 Z η θ (ball x (2 * r)) isOpen_ball
          · refine hZsupp.trans fun y hy => ?_
            rw [mem_sphere] at hy
            rw [mem_ball, hy]
            linarith
          · intro y hy
            have hev := hΦid y hy
            have hΦy : Φ y = y := hev.eq_of_nhds
            have hdy : fderiv ℝ Φ y = ContinuousLinearMap.id ℝ (Eucl P) := by
              rw [hev.fderiv_eq]; exact fderiv_id
            change ((θ : DifferentialForm (Eucl P) (m' + 1)) (Φ y)).compContinuousLinearMap
              (fderiv ℝ Φ y) = (θ : DifferentialForm (Eucl P) (m' + 1)) y
            rw [hΦy, hdy]
            ext v
            simp
        rw [h1, h2, h3, hZdef, hSeq]
      · have h := hSrval θ 0 ⟨univ, isOpen_univ, subset_univ _, fun y _ => by
          have hy : (θ : DifferentialForm (Eucl P) (m' + 1 + 1)) (Φ y) = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              Set.disjoint_left.1 hθ h (ball_subset_closedBall (hΦball y)))
          change (0 : Covector (Eucl P) (m' + 1 + 1)) =
            ((θ : DifferentialForm (Eucl P) (m' + 1 + 1)) (Φ y)).compContinuousLinearMap
              (fderiv ℝ Φ y)
          rw [hy]
          ext v
          simp⟩
        rw [h]
        exact map_zero S'.toCurrent
      · have hm1 : Sr.mass ≤ ENNReal.ofReal (CΦ ^ (m' + 2)) * S'.mass := by
          have h := (hSrmass CΦ hCΦ0 hΦd univ).1
          rw [preimage_univ, inter_univ] at h
          exact h
        set f : ℝ := (μ (ball x r)).toReal with hfdef
        have hf0 : 0 ≤ f := ENNReal.toReal_nonneg
        set y₁ : ℝ := (c₁ : ℝ) * κ with hy₁def
        have hc₁0 : (0 : ℝ) ≤ c₁ := c₁.coe_nonneg
        have hy₁0 : 0 ≤ y₁ := by positivity
        have hApos : 0 < (CΦ + 1) ^ (m' + 2) := by positivity
        have hA1 : 1 ≤ (CΦ + 1) ^ (m' + 2) := one_le_pow₀ (by linarith)
        have hkap : ((c₁ : ℝ) + 1) * κ = 1 / (4 * (CΦ + 1) ^ (m' + 2)) := by
          rw [hκdef]; field_simp
        have hy₁le : y₁ ≤ ((c₁ : ℝ) + 1) * κ := by
          rw [hy₁def]; exact mul_le_mul_of_nonneg_right (by linarith) hκpos.le
        have hy₁1 : y₁ ≤ 1 := by
          refine hy₁le.trans ?_
          rw [hkap, div_le_one (by positivity)]
          linarith
        have hprod : CΦ ^ (m' + 2) * y₁ ≤ 1 / 4 := by
          calc CΦ ^ (m' + 2) * y₁ ≤ (CΦ + 1) ^ (m' + 2) * (((c₁ : ℝ) + 1) * κ) :=
                mul_le_mul (pow_le_pow_left₀ hCΦ0 (by linarith) _) hy₁le hy₁0 hApos.le
            _ = 1 / 4 := by rw [hkap]; field_simp
        have hFpow' : F x r ^ (m' + 1) = f ^ (((m' + 1 : ℕ) : ℝ) / ((m' + 2 : ℕ) : ℝ)) := by
          change ((μ (ball x r)).toReal ^ (((m' + 1 + 1 : ℕ) : ℝ)⁻¹)) ^ (m' + 1) = _
          rw [← Real.rpow_natCast, ← Real.rpow_mul hf0, inv_mul_eq_div]
        have hS'le : S'.mass ≤ ENNReal.ofReal (y₁ * f) := by
          by_contra hgt
          push Not at hgt
          set q : ℝ := ((m' + 1 : ℕ) : ℝ) / ((m' + 2 : ℕ) : ℝ) with hqdef
          have hq0 : 0 < q := by positivity
          have hq1 : q ≤ 1 := by
            rw [hqdef, div_le_one (by positivity)]; push_cast; linarith
          have h1 : ENNReal.ofReal (y₁ * f) ^ q < S'.mass ^ q := ENNReal.rpow_lt_rpow hgt hq0
          have h2 : S'.mass ^ q ≤ ENNReal.ofReal (y₁ * F x r ^ (m' + 1)) := by
            refine hS'mass.trans ?_
            calc (c₁ : ℝ≥0∞) * Z.mass ≤ (c₁ : ℝ≥0∞) * ENNReal.ofReal (κ * F x r ^ (m' + 1)) :=
                  by gcongr
              _ = ENNReal.ofReal (y₁ * F x r ^ (m' + 1)) := by
                  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hc₁0, hy₁def, mul_assoc]
          have h3 : ENNReal.ofReal (y₁ * F x r ^ (m' + 1)) ≤ ENNReal.ofReal (y₁ * f) ^ q := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.mul_rpow hy₁0 hf0, hFpow']
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hf0 _)
            rcases hy₁0.eq_or_lt with h0 | hpos
            · rw [← h0, Real.zero_rpow hq0.ne']
            · calc y₁ = y₁ ^ (1 : ℝ) := (Real.rpow_one _).symm
                _ ≤ y₁ ^ q := Real.rpow_le_rpow_of_exponent_ge hpos hy₁1 hq1
          exact absurd (h3.trans_lt (h1.trans_le h2)) (lt_irrefl _)
        calc Sr.mass ≤ ENNReal.ofReal (CΦ ^ (m' + 2)) * S'.mass := hm1
          _ ≤ ENNReal.ofReal (CΦ ^ (m' + 2)) * ENNReal.ofReal (y₁ * f) := by gcongr
          _ = ENNReal.ofReal (CΦ ^ (m' + 2) * (y₁ * f)) := (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (2⁻¹ * f) := by
              apply ENNReal.ofReal_le_ofReal
              rw [← mul_assoc]
              apply mul_le_mul_of_nonneg_right _ hf0
              linarith
          _ = 2⁻¹ * μ (ball x r) := by
              rw [ENNReal.ofReal_mul (by norm_num), hfdef, ENNReal.ofReal_toReal (measure_ne_top μ _),
                ENNReal.ofReal_inv_of_pos (by norm_num)]
              norm_num
  /- ### Step 9 (printed (5), (6)): covering. -/
  obtain ⟨κ, hκ, hDκ⟩ := hD
  /- The cone estimate (printed "by 2.27, 2.30"): a cycle `Z` vanishing off `B̄_R(x)` with
  `|Z(θ)| ≤ K sup|θ|` satisfies `|Z(ω)| ≤ K L_ω R`. -/
  have hcone : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), ∃ L : ℝ, 0 ≤ L ∧
      ∀ (Z : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P) (R K : ℝ),
      0 < R → 0 ≤ K → Z.boundary = 0 →
      (∀ θ : TestFormOn (univ : Set (Eucl P)) (m + 1),
        Disjoint (tsupport (θ : DifferentialForm (Eucl P) (m + 1))) (closedBall x R) → Z θ = 0) →
      (∀ (θ : TestFormOn (univ : Set (Eucl P)) (m + 1)) (C : ℝ),
        (∀ y, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) (m + 1)) y) ≤ C) →
          |Z θ| ≤ K * C) →
      |Z ω| ≤ K * L * R := by
    intro ω
    set ωf : DifferentialForm (Eucl P) (m + 1) := (ω : DifferentialForm (Eucl P) (m + 1)) with hωf
    have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ωf := ω.property.1.1
    have hωc : HasCompactSupport ωf := ω.property.1.2
    obtain ⟨C₁, hC₁⟩ := (hωs.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (HasCompactSupport.fderiv (𝕜 := ℝ) hωc)
    have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
    have hlip : ∀ y y', ‖ωf y - ωf y'‖ ≤ C₁ * ‖y - y'‖ := by
      intro y y'
      exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => (hωs.differentiable (by simp)).differentiableAt) (fun z _ => hC₁ z)
        (mem_univ y') (mem_univ y)
    set N : ℝ := Real.sqrt (Fintype.card (Fin (m + 1) → Fin P)) with hN
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    refine ⟨2 * (N * C₁), by positivity, ?_⟩
    intro Z x R K hR hK hZb hZv hZm
    set α : Covector (Eucl P) (m + 1) := ωf x with hα
    let L0 : Eucl P →L[ℝ] Covector (Eucl P) m := (((m : ℝ) + 1)⁻¹ • α).curryLeft
    let η₀ : DifferentialForm (Eucl P) m := fun y => L0 y - L0 x
    have hη₀d : ∀ y, HasFDerivAt η₀ L0 y := fun y => L0.hasFDerivAt.sub_const (L0 x)
    have hη₀s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η₀ := L0.contDiff.sub contDiff_const
    have hη₀ext : ∀ y, extDeriv η₀ y = α := by
      intro y
      rw [extDeriv, (hη₀d y).fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      have : ((m + 1 : ℕ) : ℝ) * ((m : ℝ) + 1)⁻¹ = 1 := by
        push_cast
        exact mul_inv_cancel₀ (by positivity)
      rw [this, one_smul]
    let χ : ContDiffBump x := ⟨2 * R, 3 * R, by positivity, by linarith⟩
    let β : DifferentialForm (Eucl P) m := fun y => χ y • η₀ y
    have hβs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β := χ.contDiff.smul hη₀s
    have hβc : HasCompactSupport β := χ.hasCompactSupport.smul_right
    let βT : TestFormOn (univ : Set (Eucl P)) m := ⟨β, ⟨hβs, hβc⟩, subset_univ _⟩
    have hdβ : ∀ y ∈ ball x (2 * R), extDeriv β y = α := by
      intro y hy
      have h : β =ᶠ[𝓝 y] η₀ := by
        filter_upwards [isOpen_ball.mem_nhds hy] with z hz
        have : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
        simp [β, this]
      rw [h.extDeriv_eq, hη₀ext]
    have hZd : Z (exteriorDerivativeTestOn univ m βT) = 0 := by
      have h := congrArg (fun S : GeometricCurrentOn (univ : Set (Eucl P)) m => S βT) hZb
      simpa using h
    let θT : TestFormOn (univ : Set (Eucl P)) (m + 1) := ω - exteriorDerivativeTestOn univ m βT
    have hθval : ∀ y ∈ ball x (2 * R), (θT : DifferentialForm (Eucl P) (m + 1)) y = ωf y - α := by
      intro y hy
      change ωf y - extDeriv β y = ωf y - α
      rw [hdβ y hy]
    have hZθ : Z ω = Z θT := by
      have h := map_sub Z.toCurrent ω (exteriorDerivativeTestOn univ m βT)
      change Z ω = Z.toCurrent (ω - exteriorDerivativeTestOn univ m βT)
      rw [h]
      change Z ω = Z ω - Z (exteriorDerivativeTestOn univ m βT)
      rw [hZd, sub_zero]
    let ψ : ContDiffBump x := ⟨3 / 2 * R, 2 * R, by positivity, by linarith⟩
    let θ'f : DifferentialForm (Eucl P) (m + 1) :=
      fun y => ψ y • (θT : DifferentialForm (Eucl P) (m + 1)) y
    have hθ's : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ'f := ψ.contDiff.smul θT.property.1.1
    have hθ'c : HasCompactSupport θ'f := ψ.hasCompactSupport.smul_right
    let θ'T : TestFormOn (univ : Set (Eucl P)) (m + 1) := ⟨θ'f, ⟨hθ's, hθ'c⟩, subset_univ _⟩
    have hZθ' : Z θT = Z θ'T := by
      have hdiff : Z (θT - θ'T) = 0 := by
        apply hZv
        have hsub : tsupport ((θT - θ'T : TestFormOn (univ : Set (Eucl P)) (m + 1)) :
            DifferentialForm (Eucl P) (m + 1)) ⊆ (ball x (3 / 2 * R))ᶜ := by
          apply closure_minimal _ isOpen_ball.isClosed_compl
          intro y hy hyb
          apply hy
          have h1 : ψ y = 1 := ψ.one_of_mem_closedBall (ball_subset_closedBall hyb)
          change (θT : DifferentialForm (Eucl P) (m + 1)) y - ψ y • (θT : DifferentialForm (Eucl P) (m + 1)) y = 0
          rw [h1, one_smul, sub_self]
        refine Disjoint.mono_left hsub ?_
        rw [disjoint_compl_left_iff_subset]
        exact closedBall_subset_ball (by linarith)
      have h := map_sub Z.toCurrent θT θ'T
      change Z.toCurrent (θT - θ'T) = 0 at hdiff
      rw [h] at hdiff
      change Z θT - Z θ'T = 0 at hdiff
      linarith
    have hbound : ∀ y, covectorEuclideanNorm (θ'f y) ≤ 2 * R * (N * C₁) := by
      intro y
      change covectorEuclideanNorm (ψ y • (θT : DifferentialForm (Eucl P) (m + 1)) y) ≤ _
      rw [hsmul]
      by_cases hy : y ∈ ball x (2 * R)
      · rw [hθval y hy, abs_of_nonneg ψ.nonneg]
        have h1 : covectorEuclideanNorm (ωf y - α) ≤ N * (C₁ * ‖y - x‖) :=
          (euclNormLe _).trans (mul_le_mul_of_nonneg_left (hlip y x) hN0)
        have h2 : ‖y - x‖ < 2 * R := by rwa [mem_ball, dist_eq_norm] at hy
        have h3 : covectorEuclideanNorm (ωf y - α) ≤ 2 * R * (N * C₁) := by
          refine h1.trans ?_
          have : N * (C₁ * ‖y - x‖) = (N * C₁) * ‖y - x‖ := by ring
          rw [this, mul_comm (2 * R)]
          exact mul_le_mul_of_nonneg_left h2.le (by positivity)
        calc ψ y * covectorEuclideanNorm (ωf y - α) ≤ 1 * covectorEuclideanNorm (ωf y - α) :=
              mul_le_mul_of_nonneg_right ψ.le_one (covectorEuclideanNorm_nonneg _)
          _ ≤ 2 * R * (N * C₁) := by rw [one_mul]; exact h3
      · have h0 : ψ y = 0 := by
          by_contra h
          have : y ∈ Function.support ψ := h
          rw [ψ.support_eq] at this
          exact hy this
        rw [h0, abs_zero, zero_mul]
        positivity
    calc |Z ω| = |Z θ'T| := by rw [hZθ, hZθ']
      _ ≤ K * (2 * R * (N * C₁)) := hZm θ'T _ hbound
      _ = K * (2 * (N * C₁)) * R := by ring
  set c' : ℝ := κ / (4 * 2 ^ m * ((m : ℝ) + 1)) with hc'
  have hc'pos : 0 < c' := by positivity
  set ωN : ℝ≥0∞ := Poincare.SimonGMT.Chapter01.realUnitBallVolume ((m + 1 : ℕ) : ℝ) with hωN
  have hωN0 : ωN ≠ 0 := (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (by positivity)).ne'
  have hωNtop : ωN ≠ ∞ := Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
  set ε₀ : ℝ≥0∞ := ENNReal.ofReal (c' ^ (m + 1)) / ωN with hε₀
  have hε₀pos : 0 < ε₀ := ENNReal.div_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hωNtop
  set A₀ : Set (Eucl P) :=
    {x | dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x < ε₀} with hA₀def
  -- at points of `A₀` there are arbitrarily small radii with `μ(B_δ(x)) < (c' δ)^(m+1)`
  have hsmallball : ∀ x ∈ A₀, ∀ δ₀ > 0, ∃ δ ∈ Ioo 0 δ₀,
      (μ (ball x δ)).toReal < (κ * δ / (4 * 2 ^ m * ((m : ℝ) + 1))) ^ (m + 1) := by
    intro x hx δ₀ hδ₀
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
        μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x r < ε₀ :=
      eventually_lt_of_limsup_lt hx (by isBoundedDefault)
    have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 δ₀ := Ioo_mem_nhdsGT hδ₀
    obtain ⟨δ, hδq, hδI⟩ := (hev.and hev2).exists
    refine ⟨δ, hδI, ?_⟩
    have hδ0 : 0 < δ := hδI.1
    unfold Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient at hδq
    rw [Measure.toOuterMeasure_apply, univ_inter] at hδq
    have hpowne : ENNReal.ofReal δ ^ (((m + 1 : ℕ) : ℝ)) ≠ 0 := by
      rw [ENNReal.ofReal_rpow_of_nonneg hδ0.le (by positivity)]
      exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hpowtop : ENNReal.ofReal δ ^ (((m + 1 : ℕ) : ℝ)) ≠ ∞ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hδ0.le (by positivity)]
      exact ENNReal.ofReal_ne_top
    rw [ENNReal.div_lt_iff (Or.inl (mul_ne_zero hωN0 hpowne))
      (Or.inl (ENNReal.mul_ne_top hωNtop hpowtop))] at hδq
    have heq : ε₀ * (ωN * ENNReal.ofReal δ ^ (((m + 1 : ℕ) : ℝ))) =
        ENNReal.ofReal ((κ * δ / (4 * 2 ^ m * ((m : ℝ) + 1))) ^ (m + 1)) := by
      rw [hε₀, ← mul_assoc, ENNReal.div_mul_cancel hωN0 hωNtop,
        ENNReal.ofReal_rpow_of_nonneg hδ0.le (by positivity), Real.rpow_natCast,
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      congr 2
      rw [hc', div_mul_eq_mul_div]
    rw [heq] at hδq
    have hlt := (measure_mono (μ := μ) ball_subset_closedBall).trans_lt hδq
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hlt |>.trans_le
      (by rw [ENNReal.toReal_ofReal (by positivity)])
  -- admissible radii for the Besicovitch covering
  let fadm : Eucl P → Set ℝ := fun x => {r | 0 < r ∧ μ (sphere x r) = 0 ∧
    ∃ Sr : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
      (∀ θ, Sr.boundary θ = (AB x r).boundary θ) ∧
      (∀ θ : TestFormOn (univ : Set (Eucl P)) (m + 1),
        Disjoint (tsupport (θ : DifferentialForm (Eucl P) (m + 1))) (closedBall x (3 * r)) →
          Sr θ = 0) ∧
      Sr.mass ≤ 2⁻¹ * μ (ball x r)}
  have hfadm : ∀ x ∈ A₀, ∀ δ > 0, (fadm x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ₀ hδ₀
    obtain ⟨δ, hδI, hδs⟩ := hsmallball x hx δ₀ hδ₀
    obtain ⟨r, hrI, him, hsp, hmass⟩ := hC x κ δ hκ hδI.1 hδs
    obtain ⟨Sr, h1, h2, h3⟩ := hDκ x r hrI.1 him hmass
    exact ⟨r, ⟨hrI.1, hsp, Sr, h1, h2, h3⟩, hrI.1, hrI.2.trans hδI.2⟩
  have hA₀ : μ A₀ = 0 := by
    by_contra hne
    set a : ℝ≥0∞ := μ A₀ with ha
    have hatop : a ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ univ) (measure_mono (subset_univ _))
    have hapos : 0 < a.toReal := ENNReal.toReal_pos hne hatop
    have haU : a.toReal ≤ (μ univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (subset_univ _))
    have hkey : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
        (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) (m + 1)) y) ≤ 1) →
        T ω ≤ (μ univ).toReal - a.toReal / 2 := by
      intro ω hω1
      obtain ⟨L, hL0, hL⟩ := hcone ω
      have hint : Integrable (fun y => v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y)) μ' :=
        (hrep ω).1
      have hl : ∀ l : ℕ, T ω ≤ (μ univ).toReal - a.toReal / 2 +
          9 / 2 * L * (μ univ).toReal * (1 / ((l : ℝ) + 1)) := by
        intro l
        have hRpos : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        obtain ⟨t, rr, htc, -, htr, htnull, htdisj⟩ :=
          Besicovitch.exists_disjoint_closedBall_covering_ae μ fadm A₀ hfadm
            (fun _ => 1 / ((l : ℝ) + 1)) (fun _ _ => hRpos)
        have hSx : ∀ i : t, ∃ Sr : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
            (∀ θ, Sr.boundary θ = (AB (i : Eucl P) (rr i)).boundary θ) ∧
            (∀ θ : TestFormOn (univ : Set (Eucl P)) (m + 1),
              Disjoint (tsupport (θ : DifferentialForm (Eucl P) (m + 1)))
                (closedBall (i : Eucl P) (3 * rr i)) → Sr θ = 0) ∧
            Sr.mass ≤ 2⁻¹ * μ (ball (i : Eucl P) (rr i)) := fun i => (htr i i.2).1.2.2
        choose SS hSSb hSSv hSSm using hSx
        have : Countable t := htc.to_subtype
        have hBm : ∀ i : t, MeasurableSet (closedBall (i : Eucl P) (rr i)) :=
          fun i => measurableSet_closedBall
        have hBd : Pairwise (Function.onFun Disjoint fun i : t => closedBall (i : Eucl P) (rr i)) :=
          fun i j hij => htdisj i.2 j.2 (fun h => hij (Subtype.ext h))
        set U : Set (Eucl P) := ⋃ i : t, closedBall (i : Eucl P) (rr i) with hUdef
        have hUm : MeasurableSet U := MeasurableSet.iUnion hBm
        have hAU : a ≤ μ U := by
          have hU' : (⋃ x ∈ t, closedBall x (rr x)) = U := Set.biUnion_eq_iUnion _ _
          rw [hU'] at htnull
          calc a = μ A₀ := rfl
            _ ≤ μ (A₀ \ U ∪ U) := measure_mono (fun y hy => by
                by_cases hyU : y ∈ U
                · exact Or.inr hyU
                · exact Or.inl ⟨hy, hyU⟩)
            _ ≤ μ (A₀ \ U) + μ U := measure_union_le _ _
            _ = μ U := by rw [htnull, zero_add]
        have hTω : T ω = ∫ y in Uᶜ, v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' +
            ∫ y in U, v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' := by
          rw [(hrep ω).2]
          exact (integral_add_compl hUm hint).symm.trans (add_comm _ _)
        have hsum : HasSum (fun i : t => ∫ y in closedBall (i : Eucl P) (rr i),
            v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ')
            (∫ y in U, v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ') :=
          hasSum_integral_iUnion hBm hBd hint.integrableOn
        obtain ⟨Rc, hRc⟩ := hμres Uᶜ hUm.compl
        have hcompl : ∫ y in Uᶜ, v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' ≤
            (μ Uᶜ).toReal := by
          rw [← hresval _ _ hRc ω]
          have h := habs Rc ω 1 (by rw [hresmass _ _ hRc]; exact measure_ne_top μ _) hω1
          rw [hresmass _ _ hRc, mul_one] at h
          exact (le_abs_self _).trans h
        set cl : ℝ := 9 / 2 * L * (1 / ((l : ℝ) + 1)) with hcl
        have hcl0 : 0 ≤ cl := by positivity
        have hball : ∀ i : t, ∫ y in closedBall (i : Eucl P) (rr i),
            v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' ≤
              (2⁻¹ + cl) * (μ (closedBall (i : Eucl P) (rr i))).toReal := by
          rintro ⟨x, hxt⟩
          have hr := htr x hxt
          obtain ⟨⟨hr0, hsp, -⟩, -, hrl⟩ := hr
          change ∫ y in closedBall x (rr x), v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' ≤
            (2⁻¹ + cl) * (μ (closedBall x (rr x))).toReal
          have hcb : ∫ y in closedBall x (rr x), v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' =
              AB x (rr x) ω := by
            rw [hresval _ _ (hAB x (rr x)) ω, hballSet]
            obtain ⟨Rs, hRs⟩ := hμres (sphere x (rr x)) isClosed_sphere.measurableSet
            have hs0 : ∫ y in sphere x (rr x), v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ'
                = 0 := by
              rw [← hresval _ _ hRs ω]
              have h := habs Rs ω 1 (by rw [hresmass _ _ hRs]; exact measure_ne_top μ _) hω1
              rw [hresmass _ _ hRs, hsp, ENNReal.toReal_zero, zero_mul] at h
              exact abs_nonpos_iff.1 h
            have hdisj : Disjoint (ball x (rr x)) (sphere x (rr x)) :=
              Set.disjoint_left.2 fun y h1 h2 => by
                rw [mem_ball] at h1; rw [mem_sphere] at h2; linarith
            rw [← ball_union_sphere, setIntegral_union hdisj isClosed_sphere.measurableSet
              hint.integrableOn hint.integrableOn, hs0, add_zero]
          set Sx := SS ⟨x, hxt⟩ with hSxdef
          set Ax := AB x (rr x) with hAxdef
          let Zx : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1) :=
            ⟨Sx.toCurrent - Ax.toCurrent, fun ωs h => by
              simpa using (Sx.continuous' ωs h).sub (Ax.continuous' ωs h)⟩
          have hZxapp : ∀ θ, Zx θ = Sx θ - Ax θ := fun θ => rfl
          have hZxb : Zx.boundary = 0 := by
            apply GeometricCurrentOn.ext
            intro θ
            have h := hSSb ⟨x, hxt⟩ θ
            rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply] at h
            rw [GeometricCurrentOn.boundary_apply, hZxapp, GeometricCurrentOn.zero_apply]
            rw [hSxdef, h, sub_self]
          have hZxv : ∀ θ : TestFormOn (univ : Set (Eucl P)) (m + 1),
              Disjoint (tsupport (θ : DifferentialForm (Eucl P) (m + 1)))
                (closedBall x (3 * rr x)) → Zx θ = 0 := by
            intro θ hθ
            rw [hZxapp, hSSv ⟨x, hxt⟩ θ hθ, hAxdef, hresval _ _ (hAB x (rr x)) θ, zero_sub,
              neg_eq_zero]
            apply setIntegral_eq_zero_of_forall_eq_zero
            intro y hy
            have hyb : y ∈ closedBall x (3 * rr x) := by
              have h := hy.2
              rw [mem_closedBall]
              linarith
            have h0 : (θ : DifferentialForm (Eucl P) (m + 1)) y = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => Set.disjoint_left.1 hθ h hyb)
            rw [h0, map_zero]
          have hSxfin : Sx.mass ≠ ∞ :=
            ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _))
              (hSSm ⟨x, hxt⟩)
          have hAxm : Ax.mass = μ (ball x (rr x)) := by
            rw [hAxdef, hresmass _ _ (hAB x (rr x)), hballSet]
          have hAxfin : Ax.mass ≠ ∞ := by rw [hAxm]; exact measure_ne_top μ _
          have hZxm : ∀ (θ : TestFormOn (univ : Set (Eucl P)) (m + 1)) (C : ℝ),
              (∀ y, covectorEuclideanNorm ((θ : DifferentialForm (Eucl P) (m + 1)) y) ≤ C) →
                |Zx θ| ≤ (Sx.mass.toReal + Ax.mass.toReal) * C := by
            intro θ C hC
            rw [hZxapp]
            calc |Sx θ - Ax θ| ≤ |Sx θ| + |Ax θ| := abs_sub _ _
              _ ≤ Sx.mass.toReal * C + Ax.mass.toReal * C :=
                add_le_add (habs Sx θ C hSxfin hC) (habs Ax θ C hAxfin hC)
              _ = (Sx.mass.toReal + Ax.mass.toReal) * C := by ring
          have hcone' := hL Zx x (3 * rr x) (Sx.mass.toReal + Ax.mass.toReal) (by linarith)
            (by positivity) hZxb hZxv hZxm
          have hμbc : μ (ball x (rr x)) ≤ μ (closedBall x (rr x)) :=
            measure_mono ball_subset_closedBall
          have hSxm' : Sx.mass.toReal ≤ 2⁻¹ * (μ (closedBall x (rr x))).toReal := by
            have h1 : Sx.mass ≤ 2⁻¹ * μ (closedBall x (rr x)) :=
              (hSSm ⟨x, hxt⟩).trans (mul_le_mul_of_nonneg_left hμbc bot_le)
            have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _)) h1
            rwa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
          have hAxm' : Ax.mass.toReal ≤ (μ (closedBall x (rr x))).toReal := by
            rw [hAxm]; exact ENNReal.toReal_mono (measure_ne_top μ _) hμbc
          have hSxω : Sx ω ≤ 2⁻¹ * (μ (closedBall x (rr x))).toReal := by
            have h := habs Sx ω 1 hSxfin hω1
            rw [mul_one] at h
            exact (le_abs_self _).trans (h.trans hSxm')
          have hK : Sx.mass.toReal + Ax.mass.toReal ≤ 3 / 2 * (μ (closedBall x (rr x))).toReal := by
            linarith
          have hZω : -Zx ω ≤ cl * (μ (closedBall x (rr x))).toReal := by
            have h1 := neg_le_abs (Zx ω)
            have h2 : (Sx.mass.toReal + Ax.mass.toReal) * L * (3 * rr x) ≤
                3 / 2 * (μ (closedBall x (rr x))).toReal * L * (3 * (1 / ((l : ℝ) + 1))) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hK hL0) (by linarith)
                (by linarith) (mul_nonneg (by positivity) hL0)
            have h3 : 3 / 2 * (μ (closedBall x (rr x))).toReal * L * (3 * (1 / ((l : ℝ) + 1))) =
                cl * (μ (closedBall x (rr x))).toReal := by rw [hcl]; ring
            linarith
          have hAx : Ax ω = Sx ω - Zx ω := by rw [hZxapp]; ring
          rw [hcb, hAx]
          have h4 : (2⁻¹ + cl) * (μ (closedBall x (rr x))).toReal =
              2⁻¹ * (μ (closedBall x (rr x))).toReal + cl * (μ (closedBall x (rr x))).toReal := by
            ring
          linarith
        have hsum2 : HasSum (fun i : t => (2⁻¹ + cl) * (μ (closedBall (i : Eucl P) (rr i))).toReal)
            ((2⁻¹ + cl) * (μ U).toReal) := by
          apply HasSum.mul_left
          have h1 : μ U = ∑' i : t, μ (closedBall (i : Eucl P) (rr i)) := measure_iUnion hBd hBm
          rw [h1, ENNReal.tsum_toReal_eq (fun i => measure_ne_top μ _)]
          exact (ENNReal.summable_toReal (h1 ▸ measure_ne_top μ U)).hasSum
        have hUle : ∫ y in U, v' y ((ω : DifferentialForm (Eucl P) (m + 1)) y) ∂μ' ≤
            (2⁻¹ + cl) * (μ U).toReal := hasSum_le hball hsum hsum2
        have hμsplit : (μ Uᶜ).toReal + (μ U).toReal = (μ univ).toReal := by
          rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), add_comm,
            measure_add_measure_compl hUm]
        have haU' : a.toReal ≤ (μ U).toReal := ENNReal.toReal_mono (measure_ne_top μ _) hAU
        have hUuniv : (μ U).toReal ≤ (μ univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (subset_univ _))
        have hprod : 0 ≤ cl * ((μ univ).toReal - (μ U).toReal) :=
          mul_nonneg hcl0 (sub_nonneg.2 hUuniv)
        rw [hTω]
        have h5 : 9 / 2 * L * (μ univ).toReal * (1 / ((l : ℝ) + 1)) = cl * (μ univ).toReal := by
          rw [hcl]; ring
        rw [h5]
        nlinarith [hcompl, hUle]
      have htend : Tendsto (fun l : ℕ => (μ univ).toReal - a.toReal / 2 +
          9 / 2 * L * (μ univ).toReal * (1 / ((l : ℝ) + 1))) atTop
          (𝓝 ((μ univ).toReal - a.toReal / 2)) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul
          (9 / 2 * L * (μ univ).toReal)
        have h' := h.const_add ((μ univ).toReal - a.toReal / 2)
        simpa using h'
      exact ge_of_tendsto' htend hl
    have hTm : T.mass ≤ ENNReal.ofReal ((μ univ).toReal - a.toReal / 2) := by
      apply sSup_le
      rintro _ ⟨ω, hω, rfl⟩
      exact ENNReal.ofReal_le_ofReal (hkey ω hω.2)
    have hlt : ENNReal.ofReal ((μ univ).toReal - a.toReal / 2) < μ univ := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top μ univ)]
      linarith
    exact absurd (hTm.trans_lt (hlt.trans_eq hμuniv)) (lt_irrefl _)
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hA₀
  have hx' : ¬ 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x := hx
  rw [not_lt, nonpos_iff_eq_zero] at hx'
  show _ < ε₀
  rw [hx']
  exact hε₀pos

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
