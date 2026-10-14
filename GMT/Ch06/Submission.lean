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
/-- **Support of a current vanishing off a closed set (Simon Ch. 6, 2.11).**  If `Z ∈ 𝒟_q(V)`,
`V` open, kills every test form whose support misses the closed set `K`, then `spt Z ⊆ K`.  A point
`x ∈ V \ K` has a ball `B_ε(x) ⊆ V \ K`; `W = B_{ε/2}(x)` is open with compact closure
`closure W ⊆ B_ε(x) ⊆ V`, and `Z` vanishes on `W`, so `x` lies in the zero region of `Z`. -/
theorem Submission.fiw_tb_ext_support_subset : ∀ (P q : ℕ) (V K : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen V → IsClosed K → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → Z.support ⊆ K := by
  intro P q V K Z hV hK hZ x hx
  by_contra hxK
  obtain ⟨hxV, hxz⟩ := hx
  -- `V \ K` is an open neighbourhood of `x`: pick `B_ε(x) ⊆ V \ K`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hV.sdiff hK) x ⟨hxV, hxK⟩
  -- `W = B_{ε/2}(x)` is one of the open sets whose union is the zero region of `Z`.
  apply hxz
  refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (half_pos hε)⟩
  · exact (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  · exact (closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (half_lt_self hε))).trans (hball.trans sdiff_subset)
  · -- a test form supported in `W ⊆ B_ε(x)` has support disjoint from `K`
    intro ω hω
    apply hZ
    rw [Set.disjoint_left]
    intro y hy hyK
    exact (hball (ball_subset_ball (half_le_self hε.le) (hω hy))).2 hyK
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
/-- **Covector evaluation bound** (for `M(T) < ∞` in the proof of Simon Ch. 6, 6.1, p. 169).
If `|τ_j| ≤ 1` for all `j`, then `|α(τ_1, …, τ_n)| ≤ P^n |α|`, `|α|` the Euclidean coefficient
norm of Remark 2.6.  Expanding each `τ_j` in the standard basis `e_1, …, e_P` gives
`α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)` over the `P^n` maps `f : Fin n → Fin P`.  Each coefficient has
absolute value at most `1`, and `|α(e_f)| ≤ |α|`: `α(e_f) = 0` unless `f` is injective, and then
`α(e_f) = ±α(e_{f ∘ σ})` for the permutation `σ` sorting `f`, where `f ∘ σ` is strictly
increasing. -/
theorem Submission.isoperimetric_abs_covector_apply_le : ∀ (P n : ℕ) (α : Covector (Eucl P) n) (τ : Fin n → Eucl P), (∀ j, ‖τ j‖ ≤ 1) → |α τ| ≤ (P : ℝ) ^ n * covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `|α(e_f)| ≤ |α|` for every `f : Fin n → Fin P`.
  have hcoef : ∀ f : Fin n → Fin P,
      |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| ≤ covectorEuclideanNorm α := by
    intro f
    by_cases hf : Function.Injective f
    · -- Sort `f`: `f ∘ σ` is monotone and injective, hence strictly increasing.
      set σ := Tuple.sort f
      have hmono : StrictMono (f ∘ σ) :=
        (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
      have hperm : α (fun j => EuclideanSpace.basisFun (Fin P) ℝ ((f ∘ σ) j)) =
          Equiv.Perm.sign σ • α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) :=
        α.toAlternatingMap.map_perm (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) σ
      have habs : |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| =
          |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ ((f ∘ σ) j))| := by
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      -- `α(e_{f ∘ σ})²` is one of the summands of `|α|²`.
      rw [habs]
      unfold covectorEuclideanNorm
      apply Real.abs_le_sqrt
      have := Finset.single_le_sum (f := fun I : Fin n → Fin P =>
          if StrictMono I then (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ (f ∘ σ))
      simpa only [hmono, ite_true] using this
    · -- Two equal arguments: `α(e_f) = 0`.
      have hv : ¬Function.Injective fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j) :=
        fun hv => hf (Function.Injective.of_comp (f := EuclideanSpace.basisFun (Fin P) ℝ) hv)
      rw [α.map_eq_zero_of_not_injective _ hv, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  -- Step 2: multilinear expansion `α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)`.
  have hexp : α τ = ∑ f : Fin n → Fin P,
      (∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j)) := by
    have h1 : α τ = α (fun j => ∑ a, τ j a • EuclideanSpace.basisFun (Fin P) ℝ a) := by
      congr 1
      funext j
      simpa only [EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (τ j)).symm
    rw [h1, α.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [α.map_smul_univ, smul_eq_mul]
  -- Step 3: `|∏_j τ_j(f j)| ≤ 1`, as `|τ_j(a)| ≤ |τ_j| ≤ 1`.
  have hprod : ∀ f : Fin n → Fin P, |∏ j, τ j (f j)| ≤ 1 := by
    intro f
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ =>
      (show |τ j (f j)| ≤ ‖τ j‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (τ j) (f j)).trans (hτ j)
  -- Step 4: sum the bound `|α|` over the `P ^ n` maps `f`.
  calc |α τ| = |∑ f : Fin n → Fin P,
        (∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| := by
          rw [hexp]
    _ ≤ ∑ f : Fin n → Fin P,
        |(∏ j, τ j (f j)) * α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : Fin n → Fin P, covectorEuclideanNorm α := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul]
        calc |∏ j, τ j (f j)| * |α (fun j => EuclideanSpace.basisFun (Fin P) ℝ (f j))|
            ≤ 1 * covectorEuclideanNorm α :=
              mul_le_mul (hprod f) (hcoef f) (abs_nonneg _) zero_le_one
          _ = covectorEuclideanNorm α := one_mul _
    _ = (P : ℝ) ^ n * covectorEuclideanNorm α := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

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
/-- Cut-off of a null sequence: if every derivative of `ψ_l` tends to `0` uniformly on
`K = tsupport ζ`, then the test forms `φ_l = ζ ψ_l` tend to `0` in `𝒟ᵏ(U)`.  By the Leibniz rule,
`D^j φ_l` is controlled on `K` by the bounded derivatives of `ζ` and the derivatives of `ψ_l` of
order `≤ j`. -/
theorem Submission.iwl_cr_ce_cutoff_converges_zero :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (ζ : Eucl P → ℝ) (ψs : ℕ → DifferentialForm (Eucl P) k)
      (φs : ℕ → TestFormOn U k), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ U → (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψs l)) →
      (∀ l x, (φs l : DifferentialForm (Eucl P) k) x = ζ x • ψs l x) →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ,
        ‖iteratedFDeriv ℝ j (ψs l) x‖ ≤ ε) →
      TestFormOnConverges φs 0 := by
  intro P k U ζ ψs φs hζ hζc hζU hψ hφ hsmall
  -- Leibniz estimate, by induction on the order `j`, for a continuous bilinear `B`: if every
  -- derivative of `f` is bounded on `K = tsupport ζ` and every derivative of `g l` tends to `0`
  -- uniformly on `K`, then `D^j (B (f ·) (g l ·))` tends to `0` uniformly on `K`.
  have key : ∀ (j : ℕ) (F₁ F₂ G : Type) [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
      [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : F₁ →L[ℝ] F₂ →L[ℝ] G) (f : Eucl P → F₁) (g : ℕ → Eucl P → F₂),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g l)) →
      (∀ i, ∃ C, ∀ x ∈ tsupport ζ, ‖iteratedFDeriv ℝ i f x‖ ≤ C) →
      (∀ (i : ℕ) (ε : ℝ), 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ,
        ‖iteratedFDeriv ℝ i (g l) x‖ ≤ ε) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ x ∈ tsupport ζ,
        ‖iteratedFDeriv ℝ j (fun y => B (f y) (g l y)) x‖ ≤ ε := by
    intro j
    induction j with
    | zero =>
      intro F₁ F₂ G _ _ _ _ _ _ B f g _ _ hfb hgs ε hε
      obtain ⟨C, hC⟩ := hfb 0
      have hA : 0 < ‖B‖ * |C| + 1 := by positivity
      filter_upwards [hgs 0 (ε / (‖B‖ * |C| + 1)) (div_pos hε hA)] with l hl x hx
      have h1 := hC x hx
      have h2 := hl x hx
      rw [norm_iteratedFDeriv_zero] at h1 h2 ⊢
      calc ‖B (f x) (g l x)‖ ≤ ‖B‖ * ‖f x‖ * ‖g l x‖ := B.le_opNorm₂ _ _
        _ ≤ (‖B‖ * |C| + 1) * (ε / (‖B‖ * |C| + 1)) := by
          apply mul_le_mul _ h2 (norm_nonneg _) hA.le
          nlinarith [norm_nonneg B, h1.trans (le_abs_self C), norm_nonneg (f x)]
        _ = ε := by field_simp
    | succ j ih =>
      intro F₁ F₂ G _ _ _ _ _ _ B f g hf hg hfb hgs ε hε
      have hf' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right le_rfl
      have hg' : ∀ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (g l)) :=
        fun l => (hg l).fderiv_right le_rfl
      -- `D (B (f ·) (g l ·)) = B (f ·) (D (g l) ·) + B (D f ·) (g l ·)`, with the bilinear maps
      -- `precompR` and `precompL` built from `B`.
      have hD : ∀ l, fderiv ℝ (fun y => B (f y) (g l y)) =
          fun y => B.precompR (Eucl P) (f y) (fderiv ℝ (g l) y) +
            B.precompL (Eucl P) (fderiv ℝ f y) (g l y) := fun l => funext fun y =>
        B.fderiv_of_bilinear (hf.differentiable (by simp)).differentiableAt
          ((hg l).differentiable (by simp)).differentiableAt
      have h1 := ih F₁ (Eucl P →L[ℝ] F₂) (Eucl P →L[ℝ] G) (B.precompR (Eucl P)) f
        (fun l => fderiv ℝ (g l)) hf hg' hfb
        (fun i ε hε => by
          filter_upwards [hgs (i + 1) ε hε] with l hl x hx
          rw [norm_iteratedFDeriv_fderiv]
          exact hl x hx) (ε / 2) (half_pos hε)
      have h2 := ih (Eucl P →L[ℝ] F₁) F₂ (Eucl P →L[ℝ] G) (B.precompL (Eucl P)) (fderiv ℝ f) g
        hf' hg (fun i => by
          obtain ⟨C, hC⟩ := hfb (i + 1)
          exact ⟨C, fun x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hC x hx⟩)
        hgs (ε / 2) (half_pos hε)
      filter_upwards [h1, h2] with l hl1 hl2 x hx
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => B.precompR (Eucl P) (f y) (fderiv ℝ (g l) y)) :=
        (B.precompR (Eucl P)).isBoundedBilinearMap.contDiff.comp (hf.prodMk (hg' l))
      have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y => B.precompL (Eucl P) (fderiv ℝ f y) (g l y)) :=
        (B.precompL (Eucl P)).isBoundedBilinearMap.contDiff.comp (hf'.prodMk (hg l))
      rw [← norm_iteratedFDeriv_fderiv, hD l,
        fun_iteratedFDeriv_add_apply (hc1.contDiffAt.of_le (mod_cast le_top))
          (hc2.contDiffAt.of_le (mod_cast le_top))]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add (hl1 x hx) (hl2 x hx)
        _ = ε := add_halves ε
  -- Every derivative of the cut-off is bounded.
  have hζb : ∀ i, ∃ C, ∀ x ∈ tsupport ζ, ‖iteratedFDeriv ℝ i ζ x‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ :=
      (hζ.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
        (hζc.iteratedFDeriv i)
    exact ⟨C, fun x _ => hC x⟩
  have hfun : ∀ l, (φs l : DifferentialForm (Eucl P) k) =
      fun y => ContinuousLinearMap.lsmul ℝ ℝ (ζ y) (ψs l y) := fun l => funext fun y => by
    simp only [hφ l y, ContinuousLinearMap.lsmul_apply]
  refine ⟨tsupport ζ, hζc.isCompact, hζU, fun l => ?_, ?_, fun j => ?_⟩
  · rw [funext (hφ l)]
    exact tsupport_smul_subset_left _ _
  · simp
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [key j ℝ (Covector (Eucl P) k) (Covector (Eucl P) k)
      (ContinuousLinearMap.lsmul ℝ ℝ) ζ ψs hζ hψ hζb hsmall (ε / 2) (half_pos hε)] with l hl x hx
    rw [hfun l]
    simp only [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left]
    exact (hl x hx).trans_lt (half_lt_self hε)

/-- **The cut-off radial operator** behind the cone `h#([[(0,1)]] × T)`, `h(t, x) = t x`
(Simon Ch. 6, 2.30), with `h#` taken through a cut-off `ζ` as in 2.23.  Choose `ψ_ω` as in (H)
for each `ω ∈ 𝒟ᵐ⁺¹(ℝ^P)`; by (i), `ω ↦ ψ_ω` is linear.  For `r₀ = max r 0` and a bump `ζ` with
`ζ = 1` on `B̄_{r₀+1}(0)` and `spt ζ = B̄_{r₀+2}(0)`, `Φ(ω) = ζ ψ_ω` is a linear map
`𝒟ᵐ⁺¹(ℝ^P) → 𝒟ᵐ(ℝ^P)` agreeing with `ψ_ω` on `B_r(0)`.  If `ω_l → 0`, then for `i ≤ j`
eventually `‖Dⁱω_l‖ ≤ ε / (r₀ + 2 + j)` on all of `ℝ^P`, so (iii) gives `‖Dʲψ_{ω_l}‖ ≤ ε` on
`spt ζ`, and `iwl_cr_ce_cutoff_converges_zero` yields `Φ(ω_l) → 0`. -/
theorem Submission.iwl_cr_ce_cutoff_radial_operator : ∀ (P m : ℕ) (r : ℝ), (∀ ω : DifferentialForm (Eucl P) (m + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∃ ψ : DifferentialForm (Eucl P) m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ (x : Eucl P) (v : Fin m → Eucl P), ψ x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) ∧ ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D) → ∃ Φ : TestFormOn (univ : Set (Eucl P)) (m + 1) →ₗ[ℝ] TestFormOn (univ : Set (Eucl P)) m, (∀ ωs : ℕ → TestFormOn (univ : Set (Eucl P)) (m + 1), TestFormOnConverges ωs 0 → TestFormOnConverges (fun l => Φ (ωs l)) 0) ∧ ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P), x ∈ ball (0 : Eucl P) r → ∀ v : Fin m → Eucl P, (Φ ω : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v) := by
  intro P m r H
  -- Step 1: choose `ψ_ω` for every test form `ω` (test forms are `C^∞`).
  have hsmooth : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) (m + 1)) :=
    fun ω => ω.2.1.1
  choose ψ hψsmooth hψformula hψbound using
    fun ω : TestFormOn (univ : Set (Eucl P)) (m + 1) => H ω (hsmooth ω)
  -- Step 2: the integrands `t ↦ tᵐ ω(t x)(w)` are continuous, hence interval integrable.
  have hint : ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P)
      (w : Fin (m + 1) → Eucl P), IntervalIntegrable
        (fun t : ℝ => t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) w) volume 0 1 := by
    intro ω x w
    apply Continuous.intervalIntegrable
    exact (continuous_pow m).mul ((continuous_eval_const w).comp
      ((hsmooth ω).continuous.comp (continuous_id.smul continuous_const)))
  -- Step 3: by (i) and linearity of the integral, `ω ↦ ψ_ω` is linear.
  have hadd : ∀ ω ω' : TestFormOn (univ : Set (Eucl P)) (m + 1), ψ (ω + ω') = ψ ω + ψ ω' := by
    intro ω ω'
    funext x
    ext v
    rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, hψformula, hψformula, hψformula,
      ← intervalIntegral.integral_add (hint ω x _) (hint ω' x _)]
    congr 1
    funext t
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add]
  have hsmul : ∀ (c : ℝ) (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)),
      ψ (c • ω) = c • ψ ω := by
    intro c ω
    funext x
    ext v
    rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, hψformula, hψformula, smul_eq_mul,
      ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  -- Step 4: a bump `ζ` with `ζ = 1` on `B̄_{r₀+1}(0)` and `tsupport ζ = B̄_{r₀+2}(0)`.
  set r₀ := max r 0
  have hr₀ : 0 ≤ r₀ := le_max_right r 0
  let ζ : ContDiffBump (0 : Eucl P) := ⟨r₀ + 1, r₀ + 2, by linarith, by linarith⟩
  have hζsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ζ : Eucl P → ℝ) := ζ.contDiff
  have hζcpt : HasCompactSupport (ζ : Eucl P → ℝ) := ζ.hasCompactSupport
  -- Step 5: `Φ(ω) = ζ ψ_ω` is a test form, and `Φ` is linear by step 3.
  have hmem : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      (fun x => ζ x • ψ ω x) ∈ TestFormOn (univ : Set (Eucl P)) m := fun ω =>
    ⟨⟨hζsmooth.smul (hψsmooth ω), hζcpt.smul_right⟩, subset_univ _⟩
  let Φ : TestFormOn (univ : Set (Eucl P)) (m + 1) →ₗ[ℝ] TestFormOn (univ : Set (Eucl P)) m :=
    { toFun := fun ω => ⟨fun x => ζ x • ψ ω x, hmem ω⟩
      map_add' := by
        intro ω ω'
        apply Subtype.ext
        funext x
        simp only [hadd, Pi.add_apply, smul_add, AddMemClass.mk_add_mk]
      map_smul' := by
        intro c ω
        apply Subtype.ext
        funext x
        simp only [hsmul, Pi.smul_apply, smul_comm (ζ x) c, RingHom.id_apply,
          SetLike.mk_smul_mk] }
  refine ⟨Φ, ?_, ?_⟩
  -- Steps 7–11, property (a): `iwl_cr_ce_cutoff_converges_zero` with `ψ_l = ψ_{ω_l}`.
  · intro ωs hωs
    refine Submission.iwl_cr_ce_cutoff_converges_zero P m univ ζ (fun l => ψ (ωs l))
      (fun l => Φ (ωs l)) hζsmooth hζcpt (subset_univ _) (fun l => hψsmooth _) (fun l x => rfl) ?_
    intro j ε hε
    obtain ⟨K, -, -, hsupp, -, hconv⟩ := hωs
    have hpos : 0 < r₀ + 2 + j := by positivity
    set D := ε / (r₀ + 2 + j) with hDdef
    have hD : 0 < D := div_pos hε hpos
    -- Step 9: eventually `‖Dⁱω_l‖ ≤ D` on all of `ℝ^P` for every `i ≤ j`: on `K` by uniform
    -- convergence to `Dⁱ0 = 0`, and off `K ⊇ tsupport ω_l` because `Dⁱω_l` vanishes there.
    have hsmall : ∀ᶠ l in atTop, ∀ i ∈ Finset.range (j + 1), ∀ y,
        ‖iteratedFDeriv ℝ i (ωs l : DifferentialForm (Eucl P) (m + 1)) y‖ ≤ D := by
      rw [Filter.eventually_all_finset]
      intro i _
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconv i) D hD] with l hl y
      by_cases hy : y ∈ K
      · have h1 := hl y hy
        simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply,
          dist_zero_left] at h1
        exact h1.le
      · have h0 : iteratedFDeriv ℝ i (ωs l : DifferentialForm (Eucl P) (m + 1)) y = 0 :=
          image_eq_zero_of_notMem_tsupport fun h =>
            hy (hsupp l (tsupport_iteratedFDeriv_subset i h))
        rw [h0, norm_zero]
        exact hD.le
    -- Step 10: (iii) with `R = r₀ + 2` bounds `‖Dʲψ_{ω_l}‖` by `(r₀ + 2 + j) D = ε` on
    -- `tsupport ζ = B̄_{r₀+2}(0)`.
    filter_upwards [hsmall] with l hl x hx
    rw [ζ.tsupport_eq] at hx
    calc ‖iteratedFDeriv ℝ j (ψ (ωs l)) x‖ ≤ (r₀ + 2 + j) * D :=
          hψbound (ωs l) j (r₀ + 2) D hD.le
            (fun i hi y _ => hl i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) y) x hx
      _ = ε := by rw [hDdef]; exact mul_div_cancel₀ ε hpos.ne'
  -- Step 6, property (b): `ζ = 1` on `B_r(0) ⊆ B̄_{r₀+1}(0)`, so `Φ(ω) = ψ_ω` there; use (i).
  · intro ω x hx v
    have hx' : x ∈ closedBall (0 : Eucl P) ζ.rIn := by
      rw [mem_closedBall, dist_zero_right]
      rw [mem_ball, dist_zero_right] at hx
      change ‖x‖ ≤ r₀ + 1
      have : r ≤ r₀ := le_max_left r 0
      linarith
    change (ζ x • ψ ω x) v = _
    rw [ζ.one_of_mem_closedBall hx', one_smul, hψformula]
/-- **Radial coefficient bound** (for the cone mass estimate, Simon Ch. 6, 2.27 and 2.30,
pp. 140–141, in the proof of 8.2, p. 177).  If `|ω(y)| ≤ 1` for all `y` and
`β(v) = ∫₀¹ tᵐ ω(tx)(x, v) dt` for all `v`, then `|β| ≤ P^{2m+1} |x|`, `|·|` the Euclidean
coefficient norm of Remark 2.6.  Put `K = P^{m+1} |x|`.  If `|u_i| ≤ 1` for all `i`, then
`α(x, u) = |x| α(x/|x|, u)`, so `|α(x, u)| ≤ K |α|` by `isoperimetric_abs_covector_apply_le`.
Hence `|β(e_I)| ≤ K` for each of the `P^m` maps `I : Fin m → Fin P`, and
`|β| ≤ (P^m K²)^{1/2} ≤ P^m K = P^{2m+1} |x|`. -/
theorem Submission.iwl_cr_cest_radial_coeff_bound : ∀ (P m : ℕ) (ω : DifferentialForm (Eucl P) (m + 1)) (x : Eucl P) (β : Covector (Eucl P) m), (∀ y, covectorEuclideanNorm (ω y) ≤ 1) → (∀ v : Fin m → Eucl P, β v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) → covectorEuclideanNorm β ≤ (P : ℝ) ^ (2 * m + 1) * ‖x‖ := by
  intro P m ω x β hω hβ
  classical
  set K : ℝ := (P : ℝ) ^ (m + 1) * ‖x‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (pow_nonneg (Nat.cast_nonneg P) _) (norm_nonneg x)
  -- Step 1: `|α(x, u)| ≤ K |α|` whenever `|u_i| ≤ 1` for all `i`.
  have hcoef : ∀ (α : Covector (Eucl P) (m + 1)) (u : Fin m → Eucl P), (∀ i, ‖u i‖ ≤ 1) →
      |α (Fin.cons x u)| ≤ K * covectorEuclideanNorm α := by
    intro α u hu
    by_cases hx : x = 0
    · -- The first argument vanishes.
      have h0 : α (Fin.cons x u) = 0 := α.map_coord_zero 0 (by simp [hx])
      rw [h0, abs_zero]
      exact mul_nonneg hK0 (covectorEuclideanNorm_nonneg α)
    · -- `α(x, u) = |x| α(τ)` for `τ = (x/|x|, u)`, whose entries have norm at most `1`.
      have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set τ : Fin (m + 1) → Eucl P := Fin.cons (‖x‖⁻¹ • x) u
      have hτ : ∀ j, ‖τ j‖ ≤ 1 := by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [τ, norm_smul, inv_mul_cancel₀ hx0.ne']
        · simpa [τ] using hu i
      have hxu : (Fin.cons x u : Fin (m + 1) → Eucl P) = Function.update τ 0 (‖x‖ • τ 0) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [τ, smul_smul, mul_inv_cancel₀ hx0.ne']
        · simp [τ]
      rw [hxu, α.map_update_smul, Function.update_eq_self, smul_eq_mul, abs_mul,
        abs_of_pos hx0]
      calc ‖x‖ * |α τ| ≤ ‖x‖ * ((P : ℝ) ^ (m + 1) * covectorEuclideanNorm α) :=
            mul_le_mul_of_nonneg_left
              (Submission.isoperimetric_abs_covector_apply_le P (m + 1) α τ hτ) hx0.le
        _ = K * covectorEuclideanNorm α := by rw [hK]; ring
  -- Step 2: `|β(e_I)| ≤ K` for every `I : Fin m → Fin P`.
  have hcoord : ∀ I : Fin m → Fin P,
      |β (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))| ≤ K := by
    intro I
    have he : ∀ i, ‖EuclideanSpace.basisFun (Fin P) ℝ (I i)‖ ≤ 1 := fun i =>
      ((EuclideanSpace.basisFun (Fin P) ℝ).orthonormal.1 (I i)).le
    -- On `Ι(0, 1) = (0, 1]`, `0 ≤ tᵐ ≤ 1` and `|ω(tx)(x, e_I)| ≤ K |ω(tx)| ≤ K`.
    have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖t ^ m * ω (t • x) (Fin.cons x fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))‖ ≤ K := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have htm : 0 ≤ t ^ m := pow_nonneg ht.1.le m
      have htm1 : t ^ m ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have hval := (hcoef (ω (t • x)) _ he).trans
        (mul_le_of_le_one_right hK0 (hω (t • x)))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htm]
      exact (mul_le_of_le_one_left (abs_nonneg _) htm1).trans hval
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h
    rw [hβ]
    exact h
  -- Step 3: `|β|² ≤ P^m K² ≤ (P^m K)²`, as `P^m ≤ (P^m)²`.
  unfold covectorEuclideanNorm
  refine (Real.sqrt_le_sqrt (y := ((P : ℝ) ^ m * K) ^ 2) ?_).trans_eq ?_
  · calc _ ≤ ∑ _I : Fin m → Fin P, K ^ 2 := by
          refine Finset.sum_le_sum fun I _ => ?_
          split_ifs
          · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord I) 2
          · positivity
      _ = (P : ℝ) ^ m * K ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      _ ≤ ((P : ℝ) ^ m) ^ 2 * K ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg K)
          exact_mod_cast Nat.le_self_pow two_ne_zero (P ^ m)
      _ = ((P : ℝ) ^ m * K) ^ 2 := (mul_pow _ _ 2).symm
  · rw [Real.sqrt_sq (mul_nonneg (pow_nonneg (Nat.cast_nonneg P) m) hK0), hK]
    ring

/-- **Cut-off radial form** (cone construction, Simon Ch. 6, 2.30–2.32 (pp. 141–142), as used in
the proof of 8.2).  Let `ψ₀(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt` be smooth and `0 < r < s`.  For the
bump function `ζ` equal to `1` on `B̄_r(0)` with support `B_s(0)`, `ψ = ζ ψ₀` is a test form
agreeing with `ψ₀` on `B_r(0)`.  If `|ω| ≤ 1`, then `|ψ(x)| = ζ(x) |ψ₀(x)|`, which is at most
`P^{2m+1} ‖x‖ ≤ P^{2m+1} s` for `‖x‖ < s` and `0` otherwise. -/
theorem Submission.iwl_cr_cest_cutoff_radial_form : ∀ (P m : ℕ) (ω : DifferentialForm (Eucl P) (m + 1)) (ψ₀ : DifferentialForm (Eucl P) m) (r s : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀ → (∀ (x : Eucl P) (v : Fin m → Eucl P), ψ₀ x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) → 0 < r → r < s → ∃ ψ : TestFormOn (univ : Set (Eucl P)) m, (∀ x ∈ ball (0 : Eucl P) r, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) ∧ ((∀ y, covectorEuclideanNorm (ω y) ≤ 1) → ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) m) x) ≤ (P : ℝ) ^ (2 * m + 1) * s) := by
  intro P m ω ψ₀ r s hψ₀ hrad hr hrs
  -- Step 1: the bump function `ζ = 1` on `B̄_r(0)`, `support ζ = B_s(0)`, `0 ≤ ζ ≤ 1`.
  obtain ⟨ζ, hζr, hζs⟩ : ∃ ζ : ContDiffBump (0 : Eucl P), ζ.rIn = r ∧ ζ.rOut = s :=
    ⟨⟨r, s, hr, hrs⟩, rfl, rfl⟩
  -- Step 2: `ζ ψ₀` is smooth with compact support, i.e. a test form on `ℝ^P`.
  have hmem : (ζ : Eucl P → ℝ) • ψ₀ ∈ testFormOnSubmodule (univ : Set (Eucl P)) m :=
    ⟨⟨ζ.contDiff.smul hψ₀, ζ.hasCompactSupport.smul_right⟩, subset_univ _⟩
  refine ⟨⟨(ζ : Eucl P → ℝ) • ψ₀, hmem⟩, fun x hx v => ?_, fun hω x => ?_⟩
  -- Step 3: `ζ = 1` on `B_r(0)`, so there `ψ = ψ₀` satisfies the radial formula.
  · have hζx : ζ x = 1 := ζ.one_of_mem_closedBall (by rw [hζr]; exact ball_subset_closedBall hx)
    change ((ζ : Eucl P → ℝ) • ψ₀) x v = _
    rw [Pi.smul_apply', ContinuousAlternatingMap.smul_apply, hζx, one_smul, hrad]
  -- Step 4: homogeneity `|a α| = |a| |α|` of the Euclidean coefficient norm.
  · have hsmul : ∀ (a : ℝ) (α : Covector (Eucl P) m),
        covectorEuclideanNorm (a • α) = |a| * covectorEuclideanNorm α := by
      intro a α
      unfold covectorEuclideanNorm
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    -- Step 5: `|ψ(x)| = ζ(x) |ψ₀(x)|`; bound it on `B_s(0)` and note it vanishes outside.
    change covectorEuclideanNorm (((ζ : Eucl P → ℝ) • ψ₀) x) ≤ _
    rw [Pi.smul_apply', hsmul, abs_of_nonneg ζ.nonneg]
    have hc : 0 ≤ (P : ℝ) ^ (2 * m + 1) := pow_nonneg (Nat.cast_nonneg P) _
    by_cases hxs : ‖x‖ < s
    · have hψ₀x : covectorEuclideanNorm (ψ₀ x) ≤ (P : ℝ) ^ (2 * m + 1) * ‖x‖ :=
        Submission.iwl_cr_cest_radial_coeff_bound P m ω x (ψ₀ x) hω (hrad x)
      calc ζ x * covectorEuclideanNorm (ψ₀ x) ≤ 1 * ((P : ℝ) ^ (2 * m + 1) * ‖x‖) :=
            mul_le_mul ζ.le_one hψ₀x (covectorEuclideanNorm_nonneg _) zero_le_one
        _ ≤ (P : ℝ) ^ (2 * m + 1) * s := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left hxs.le hc
    · have hζx : ζ x = 0 := by
        rw [← Function.notMem_support, ζ.support_eq, hζs, mem_ball_zero_iff]
        exact hxs
      rw [hζx, zero_mul]
      exact mul_nonneg hc (hr.trans hrs).le
/-- **Support of the cone** (the cone `0 ⨯ X` of Simon Ch. 6, 2.30, p. 141).  Suppose
`spt X ⊆ B̄_R(0)` and `C(ω) = X(ψ)` whenever `ψ` agrees on an open neighbourhood of `spt X` with
the radial form `x ↦ ∫_0^1 t^m ω(tx)(x, ·) dt`.  Then `spt C ⊆ B̄_R(0)`: for `‖p‖ > R` and
`r = (‖p‖ − R)/2`, a test form `ω` supported in `B_r(p)` vanishes at `tx` for `x ∈ B_{R+r}(0)`,
`t ∈ [0, 1]`, so `ψ = 0` is admissible and `C(ω) = X(0) = 0`; thus `C` vanishes on `B_r(p)`
and `p ∉ spt C`. -/
theorem Submission.iwl_cr_cest_cone_support : ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → C.support ⊆ closedBall 0 R := by
  intro P m R X C hX hcone p hp
  -- Suppose `‖p‖ > R` and put `r = (‖p‖ - R) / 2 > 0`.
  by_contra hpR
  rw [mem_closedBall_zero_iff, not_le] at hpR
  set r := (‖p‖ - R) / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  -- `C` vanishes on `B_r(p)`: for `tsupport ω ⊆ B_r(p)`, `ψ = 0` satisfies the radial formula
  -- on `N = B_{R+r}(0) ⊇ spt X`, so `C ω = X 0 = 0`.
  have hvan : C.VanishesOn (ball p r) := by
    intro ω hω
    have hC := hcone ω 0
      ⟨ball 0 (R + r), isOpen_ball, hX.trans (closedBall_subset_ball (by linarith)), ?_⟩
    · rw [hC, map_zero]
    intro x hx v
    have hx' : ‖x‖ < R + r := mem_ball_zero_iff.mp hx
    -- For `t ∈ [0, 1]`, `‖tx‖ ≤ ‖x‖ < R + r = ‖p‖ - r`, so `tx ∉ B_r(p) ⊇ tsupport ω`.
    have hzero : EqOn (fun t : ℝ =>
        t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v))
        (fun _ => 0) (uIcc 0 1) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have htx : t • x ∉ tsupport (ω : DifferentialForm (Eucl P) (m + 1)) := by
        intro hmem
        have h1 : dist (t • x) p < r := hω hmem
        rw [dist_eq_norm] at h1
        have h2 : ‖t • x‖ ≤ ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2
        have h3 : ‖p‖ ≤ ‖t • x‖ + ‖t • x - p‖ := by
          have h4 := norm_le_insert' p (t • x)
          rwa [norm_sub_rev] at h4
        linarith
      simp only [image_eq_zero_of_notMem_tsupport htx, ContinuousAlternatingMap.coe_zero,
        Pi.zero_apply, mul_zero]
    simp only [Submodule.coe_zero, Pi.zero_apply, ContinuousAlternatingMap.coe_zero]
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
  -- Hence `B_r(p)` lies in the zero region of `C`, contradicting `p ∈ spt C`.
  exact hp.2 ⟨ball p r, ⟨isOpen_ball, by rw [closure_ball p hr.ne']; exact isCompact_closedBall p r,
    subset_univ _, hvan⟩, mem_ball_self hr⟩
/-- Mass comparison through bounded transfer forms: if for every mass-admissible `ω` and `δ > 0`
there is a test form `ψ` with `C(ω) = X(ψ)` and `|ψ(x)| ≤ c (R + δ)` everywhere, then
`M(C) ≤ c R · M(X)`. -/
theorem Submission.iwl_cr_cest_mass_le_of_forms :
    ∀ (P n k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) n)
      (C : GeometricCurrentOn (univ : Set (Eucl P)) k) (c R : ℝ), 0 ≤ c → 0 ≤ R → X.mass < ∞ →
      (∀ ω ∈ massAdmissibleOn (univ : Set (Eucl P)) k univ, ∀ δ : ℝ, 0 < δ →
        ∃ ψ : TestFormOn (univ : Set (Eucl P)) n, C ω = X ψ ∧
          ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) n) x) ≤ c * (R + δ)) →
      C.mass ≤ ENNReal.ofReal (c * R) * X.mass := by
  intro P n k X C c R hc hR hX hforms
  -- `M(X) = ofReal B` with `B = M(X).toReal ≥ 0`.
  set B := X.mass.toReal
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hXB : X.mass = ENNReal.ofReal B := (ENNReal.ofReal_toReal hX.ne).symm
  -- Every admissible `ω` has `C(ω) ≤ c R B`: use the transfer form for `δ = ε / (B c + 1)`.
  have key : ∀ ω ∈ massAdmissibleOn (univ : Set (Eucl P)) k univ, C ω ≤ c * R * B := by
    intro ω hω
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hBc : 0 ≤ B * c := mul_nonneg hB hc
    have hBc1 : 0 < B * c + 1 := by linarith
    have hδ : 0 < ε / (B * c + 1) := div_pos hε hBc1
    obtain ⟨ψ, hCψ, hψ⟩ := hforms ω hω (ε / (B * c + 1)) hδ
    have habs := Submission.cmb_abs_apply_le_of_massOn_le P n univ univ X ψ B
      (c * (R + ε / (B * c + 1))) hB hXB.le (subset_univ _) hψ
    have hBcδ : B * c * (ε / (B * c + 1)) < ε := by
      have e : B * c * (ε / (B * c + 1)) + ε / (B * c + 1) = ε := by field_simp
      linarith
    calc C ω = X ψ := hCψ
      _ ≤ |X ψ| := le_abs_self _
      _ ≤ B * (c * (R + ε / (B * c + 1))) := habs
      _ = c * R * B + B * c * (ε / (B * c + 1)) := by ring
      _ < c * R * B + ε := by linarith
  -- Take the supremum over admissible `ω`.
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  calc ENNReal.ofReal (C ω) ≤ ENNReal.ofReal (c * R * B) :=
        ENNReal.ofReal_le_ofReal (key ω hω)
    _ = ENNReal.ofReal (c * R) * ENNReal.ofReal B := ENNReal.ofReal_mul (mul_nonneg hc hR)
    _ = ENNReal.ofReal (c * R) * X.mass := by rw [hXB]
/-- Smoothness of a parametric interval integral, with all derivatives under the integral sign:
for `G : ℝ × ℝ^P → V` of class `C^∞` (`V` complete), `g x = ∫_a^b G(t, x) dt` is `C^∞`, every
`x`-derivative `(t, x) ↦ ∂_x^j G(t, x)` is continuous, and `D^j g(x) = ∫_a^b ∂_x^j G(t, x) dt`.

Proof.  For smooth `H : ℝ × ℝ^P → W` the `x`-derivative `H'(t, x) = DH(t, x) ∘ inr` is smooth with
values in the complete space `ℝ^P →L W`.  Bounding `‖H'‖` on the compact set
`[[a, b]] × closedBall x₀ 1` and differentiating under the integral sign gives
`D(∫_a^b H(t, ·) dt) = ∫_a^b H'(t, ·) dt`.  Induction on `j`, over all complete codomains at once,
identifies `D^{j+1}` with `D^j ∘ D` through the currying isometry, which commutes with the
interval integral; `C^j` for every `j` is `C^∞`. -/
theorem Submission.iwl_cr_ro_intervalIntegral_contDiff :
    ∀ (P : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (G : ℝ × Eucl P → V) (a b : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl P => ∫ t in a..b, G (t, x)) ∧ (∀ j : ℕ, Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => G (p.1, z)) p.2)) ∧ ∀ (j : ℕ) (x : Eucl P), iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, G (t, y)) x = ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => G (t, z)) x := by
  intro P V _ _ _ G a b hG
  -- The partial derivative of a smooth `H` in `x` is `H'(t, x) = DH(t, x) ∘ inr` (chain rule).
  have hderiv : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (H : ℝ × Eucl P → W),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ (t : ℝ) (x : Eucl P),
      HasFDerivAt (fun z : Eucl P => H (t, z))
        ((fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x := by
    intro W _ _ H hH t x
    exact (hH.differentiable (by simp) (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- One differentiation under the integral sign: `‖H'‖ ≤ K` on `[[a, b]] × closedBall x₀ 1`.
  have hstep : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H → ∀ x₀ : Eucl P,
      HasFDerivAt (fun x : Eucl P => ∫ t in a..b, H (t, x))
        (∫ t in a..b, (fderiv ℝ H (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P))) x₀ := by
    intro W _ _ _ H hH x₀
    have hHc : Continuous H := hH.continuous
    have hH'c : Continuous fun p : ℝ × Eucl P =>
        (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) :=
      (hH.continuous_fderiv (by simp)).clm_comp continuous_const
    obtain ⟨K, hK⟩ := (isCompact_uIcc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      hH'c.continuousOn
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => H (t, x))
      (F' := fun x t => (fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)))
      (bound := fun _ => K) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x =>
        (hHc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      ((hHc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hH'c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx =>
        hK (t, x) ⟨uIoc_subset_uIcc ht, ball_subset_closedBall hx⟩)
      intervalIntegrable_const
      (Eventually.of_forall fun t x _ => hderiv W H hH t x)
  -- Induction on `j` over all complete codomains: `C^j`, continuity of `∂_x^j H`, and
  -- `D^j (∫_a^b H(t, ·) dt) = ∫_a^b ∂_x^j H(t, ·) dt`.
  have claim : ∀ j : ℕ, ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (H : ℝ × Eucl P → W), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H →
      ContDiff ℝ j (fun x : Eucl P => ∫ t in a..b, H (t, x)) ∧
      Continuous (fun p : ℝ × Eucl P => iteratedFDeriv ℝ j (fun z : Eucl P => H (p.1, z)) p.2) ∧
      ∀ x : Eucl P, iteratedFDeriv ℝ j (fun y : Eucl P => ∫ t in a..b, H (t, y)) x =
        ∫ t in a..b, iteratedFDeriv ℝ j (fun z : Eucl P => H (t, z)) x := by
    intro j
    induction j with
    | zero =>
      intro W _ _ _ H hH
      have hHc : Continuous H := hH.continuous
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_zero, contDiff_zero]
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun x t => H (t, x)) (hHc.comp continuous_swap) a b
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
        exact (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.continuous.comp hHc
      · intro x
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact (LinearIsometry.intervalIntegral_comp_comm
          (continuousMultilinearCurryFin0 ℝ (Eucl P) W).symm.toLinearIsometry
          (fun t => H (t, x))).symm
    | succ j ih =>
      intro W _ _ _ H hH
      set H' : ℝ × Eucl P → (Eucl P →L[ℝ] W) :=
        fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Eucl P)) with hH'
      have hH'smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H' :=
        (hH.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_comp contDiff_const
      obtain ⟨ih1, ih2, ih3⟩ := ih (Eucl P →L[ℝ] W) H' hH'smooth
      have hg : fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) =
          fun x => ∫ t in a..b, H' (t, x) := by
        funext x
        exact (hstep W H hH x).fderiv
      have hgd : Differentiable ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) :=
        fun x => (hstep W H hH x).differentiableAt
      have hpart : ∀ t : ℝ, fderiv ℝ (fun z : Eucl P => H (t, z)) = fun z => H' (t, z) :=
        fun t => funext fun z => (hderiv W H hH t z).fderiv
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
        refine ⟨hgd, fun h => absurd h (by simp), ?_⟩
        rw [hg]
        exact ih1
      · have : (fun p : ℝ × Eucl P => iteratedFDeriv ℝ (j + 1) (fun z : Eucl P => H (p.1, z)) p.2) =
            fun p => (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm
              (iteratedFDeriv ℝ j (fun z : Eucl P => H' (p.1, z)) p.2) := by
          funext p
          rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
          congr 2
          exact hpart p.1
        rw [this]
        exact (continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm.continuous.comp ih2
      · intro x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        have : (fun y => fderiv ℝ (fun x : Eucl P => ∫ t in a..b, H (t, x)) y) =
            fun x => ∫ t in a..b, H' (t, x) := hg
        rw [this, ih3 x]
        have hint : IntervalIntegrable
            (fun t : ℝ => iteratedFDeriv ℝ j (fun z : Eucl P => H' (t, z)) x) volume a b :=
          (ih2.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
        have e := ContinuousLinearMap.intervalIntegral_comp_comm
          ((continuousMultilinearCurryRightEquiv' ℝ j (Eucl P) W).symm :
            (Eucl P [×j]→L[ℝ] (Eucl P →L[ℝ] W)) →L[ℝ] (Eucl P [×(j + 1)]→L[ℝ] W)) hint
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          ContinuousLinearEquiv.coe_coe] at e
        rw [← e]
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
        congr 2
        exact (hpart t).symm
  exact ⟨contDiff_infty.2 fun n => (claim n V G hG).1,
    fun j => (claim j V G hG).2.1,
    fun j x => (claim j V G hG).2.2 x⟩
/-- Integrand of the radial homotopy operator.  For a `C^∞` `(k + 1)`-form `ω` and `a ∈ ℕ`, the map
`F(t, x) = tᵃ • (ω(t • x)).curryLeft x`, i.e. `F(t, x)(v) = tᵃ ω(tx)(x, v)`, is `C^∞` on
`ℝ × ℝ^P`, and for fixed `t` the derivative of `F(t, ·)` at `x` is
`w ↦ (v ↦ tᵃ (t Dω(tx)[w](x, v) + ω(tx)(w, v)))`, where `(y, v) = Fin.cons y v`. -/
theorem Submission.iwl_cr_ro_integrand_contDiff_fderiv :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) ∧
          ∀ (t : ℝ) (x w : Eucl P) (v : Fin k → Eucl P),
            fderiv ℝ (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x w v =
              t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v)) := by
  intro P k a ω hω
  -- The interior product `α ↦ α.curryLeft` as an (opaque) continuous linear map `B`.
  obtain ⟨B, hB⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      ∀ α, B α = α.curryLeft :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
        (n := k)).toContinuousLinearMap, fun α => rfl⟩
  refine ⟨?_, ?_⟩
  · -- `F(p) = p.1ᵃ • B (ω (p.1 • p.2)) p.2` is built from `C^∞` pieces.
    have hfun : (fun p : ℝ × Eucl P => p.1 ^ a • (ω (p.1 • p.2)).curryLeft p.2) =
        fun p => p.1 ^ a • B (ω (p.1 • p.2)) p.2 := by
      funext p; rw [hB]
    rw [hfun]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => p.1 • p.2) :=
      contDiff_fst.smul contDiff_snd
    -- Naming the codomain `F` lets the normed instances on `Covector` be unified with `B`'s.
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Eucl P => B (ω (p.1 • p.2))) := by
      exact (ContinuousLinearMap.contDiff (F := Eucl P →L[ℝ] Covector (Eucl P) k) B).comp
        (hω.comp hs)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × Eucl P => B (ω (p.1 • p.2)) p.2) :=
      h1.clm_apply contDiff_snd
    exact (contDiff_fst.pow a).smul h2
  · intro t x w v
    have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
        fun z => t ^ a • B (ω (t • z)) z := by
      funext z; rw [hB]
    rw [hfun]
    have hω' : HasFDerivAt ω (fderiv ℝ ω (t • x)) (t • x) :=
      (hω.differentiable (by simp) (t • x)).hasFDerivAt
    have hs : HasFDerivAt (fun z : Eucl P => t • z) (t • ContinuousLinearMap.id ℝ (Eucl P)) x :=
      (hasFDerivAt_id x).const_smul t
    -- Chain rule for `z ↦ B (ω (t • z))`.
    have hc : HasFDerivAt (fun z : Eucl P => B (ω (t • z)))
        (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))) x := by
      exact HasFDerivAt.comp (F := Covector (Eucl P) (k + 1))
        (G := Eucl P →L[ℝ] Covector (Eucl P) k) x
        (ContinuousLinearMap.hasFDerivAt (F := Eucl P →L[ℝ] Covector (Eucl P) k) B)
        (hω'.comp x hs)
    -- Product rule for `z ↦ B (ω (t • z)) z`, then scaling by `tᵃ`.
    have happ := hc.clm_apply (hasFDerivAt_id x)
    have hf : HasFDerivAt (fun z : Eucl P => t ^ a • B (ω (t • z)) z)
        (t ^ a • ((B (ω (t • x))).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
          (B.comp ((fderiv ℝ ω (t • x)).comp (t • ContinuousLinearMap.id ℝ (Eucl P)))).flip x)) x :=
      happ.const_smul (t ^ a)
    -- Evaluate at `w` and `v`; `Matrix.vecCons` is definitionally `Fin.cons`.
    rw [hf.fderiv]
    simp only [_root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, hB,
      ContinuousAlternatingMap.curryLeft_apply_apply, map_smul, smul_eq_mul,
      ContinuousAlternatingMap.curryLeft_smul]
    rw [add_comm]
    rfl
/-- Bound on the `j`-th derivative of the radial-homotopy integrand: for `t ∈ [0, 1]` and
`‖x‖ ≤ R`, `‖D^j (z ↦ t^a • ι_z ω(t z))(x)‖ ≤ (R + j) D` when `‖D^i ω‖ ≤ D` on `closedBall 0 R`
for all `i ≤ j`.  Writing the integrand as `t^a • B (g z) z` with `g z = ω (t • z)` and `B` the
interior product (`‖B u v‖ ≤ ‖u‖ ‖v‖`), the Leibniz rule for `z ↦ B (g z) z`, proved below by
induction on the order, gives `‖D^j (B (g ·) ·)(x)‖ ≤ ‖x‖ ‖D^j g(x)‖ + j ‖D^(j-1) g(x)‖`, and
`‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` since `‖t x‖ ≤ R`. -/
theorem Submission.iwl_cr_ro_integrand_iteratedFDeriv_le :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
        (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R,
          ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤
            (R + j) * D := by
  intro P k a ω hω j R D hD hbound t ht x hx
  -- Leibniz bound for `z ↦ B (g z) z`.  Since `D (B (g ·) ·)(z) = B (g z) + B' (Dg z) z` with
  -- `B' A z h = B (A h) z`, again of the same shape, induction on the order gives
  -- `‖D^n (B (g ·) ·)(y)‖ ≤ ‖y‖ ‖D^n g(y)‖ + n ‖D^(n-1) g(y)‖`.
  have leibniz : ∀ (n : ℕ) (F G : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : F →L[ℝ] Eucl P →L[ℝ] G),
      (∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) →
      ∀ g : Eucl P → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → ∀ y : Eucl P,
        ‖iteratedFDeriv ℝ n (fun z => B (g z) z) y‖ ≤
          ‖y‖ * ‖iteratedFDeriv ℝ n g y‖ + n * ‖iteratedFDeriv ℝ (n - 1) g y‖ := by
    intro n
    induction n with
    | zero =>
      intro F G _ _ _ _ B hB g hg y
      rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, Nat.cast_zero, zero_mul, add_zero,
        mul_comm]
      exact hB (g y) y
    | succ n ih =>
      intro F G _ _ _ _ B hB g hg y
      obtain ⟨B', hB'apply, hB'bound⟩ :
          ∃ B' : (Eucl P →L[ℝ] F) →L[ℝ] Eucl P →L[ℝ] Eucl P →L[ℝ] G,
            (∀ A z h, B' A z h = B (A h) z) ∧ ∀ A z, ‖B' A z‖ ≤ ‖A‖ * ‖z‖ := by
        refine ⟨((ContinuousLinearMap.compL ℝ (Eucl P) F G).comp B.flip).flip,
          fun A z h => rfl, fun A z => ?_⟩
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        show ‖B (A h) z‖ ≤ ‖A‖ * ‖z‖ * ‖h‖
        calc ‖B (A h) z‖ ≤ ‖A h‖ * ‖z‖ := hB (A h) z
          _ ≤ ‖A‖ * ‖h‖ * ‖z‖ := by gcongr; exact A.le_opNorm h
          _ = ‖A‖ * ‖z‖ * ‖h‖ := by ring
      have hBnorm : ‖B‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [one_mul]
        exact hB u v
      have hgd : Differentiable ℝ g := (contDiff_infty_iff_fderiv.1 hg).1
      have hdg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
        (contDiff_infty_iff_fderiv.1 hg).2
      have hderiv : fderiv ℝ (fun z => B (g z) z) = fun z => B (g z) + B' (fderiv ℝ g z) z := by
        funext z
        have h1 : HasFDerivAt (fun z => B (g z)) (B.comp (fderiv ℝ g z)) z :=
          B.hasFDerivAt.comp z (hgd z).hasFDerivAt
        have h2 : HasFDerivAt (fun z => B (g z) z)
            ((B (g z)).comp (ContinuousLinearMap.id ℝ (Eucl P)) +
              (B.comp (fderiv ℝ g z)).flip z) z :=
          h1.clm_apply (hasFDerivAt_id z)
        rw [h2.fderiv]
        ext h
        simp [hB'apply]
      have hc1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B (g z)) := B.contDiff.comp hg
      have hc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => B' (fderiv ℝ g z) z) :=
        B'.isBoundedBilinearMap.contDiff.comp (hdg.prodMk contDiff_id)
      have hle : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
      have hadd : iteratedFDeriv ℝ n (fun z => B (g z) + B' (fderiv ℝ g z) z) y =
          iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y :=
        iteratedFDeriv_add_apply (hc1.contDiffAt.of_le hle) (hc2.contDiffAt.of_le hle)
      have hcomp : iteratedFDeriv ℝ n (fun z => B (g z)) y =
          B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y) :=
        B.iteratedFDeriv_comp_left hg.contDiffAt hle
      have e1 : ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ ≤ ‖iteratedFDeriv ℝ n g y‖ := by
        rw [hcomp]
        calc ‖B.compContinuousMultilinearMap (iteratedFDeriv ℝ n g y)‖
            ≤ ‖B‖ * ‖iteratedFDeriv ℝ n g y‖ := B.norm_compContinuousMultilinearMap_le _
          _ ≤ 1 * ‖iteratedFDeriv ℝ n g y‖ := by gcongr
          _ = ‖iteratedFDeriv ℝ n g y‖ := one_mul _
      have e2 := ih (Eucl P →L[ℝ] F) (Eucl P →L[ℝ] G) B' hB'bound (fderiv ℝ g) hdg y
      rw [norm_iteratedFDeriv_fderiv] at e2
      have e3 : (n : ℝ) * ‖iteratedFDeriv ℝ (n - 1) (fderiv ℝ g) y‖ =
          n * ‖iteratedFDeriv ℝ n g y‖ := by
        rcases n with _ | m
        · simp
        · rw [norm_iteratedFDeriv_fderiv, Nat.add_sub_cancel]
      rw [e3] at e2
      rw [← norm_iteratedFDeriv_fderiv, hderiv, hadd, Nat.add_sub_cancel]
      calc ‖iteratedFDeriv ℝ n (fun z => B (g z)) y +
            iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖
          ≤ ‖iteratedFDeriv ℝ n (fun z => B (g z)) y‖ +
            ‖iteratedFDeriv ℝ n (fun z => B' (fderiv ℝ g z) z) y‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ n g y‖ +
            (‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ + n * ‖iteratedFDeriv ℝ n g y‖) :=
              add_le_add e1 e2
        _ = ‖y‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ +
            ((n + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ n g y‖ := by push_cast; ring
  -- The interior product `B α = α.curryLeft`, a linear isometry, so `‖B u v‖ ≤ ‖u‖ ‖v‖`.
  obtain ⟨B, hB, hBbound⟩ :
      ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] Eucl P →L[ℝ] Covector (Eucl P) k,
        (∀ α, B α = α.curryLeft) ∧ ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖ := by
    refine ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
      (n := k)).toContinuousLinearMap, fun α => rfl, fun u v => ?_⟩
    calc ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u v‖
        ≤ ‖(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ)
          (n := k)).toContinuousLinearMap u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖u‖ * ‖v‖ := by
          rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hR : 0 ≤ R := (norm_nonneg x).trans hx'
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
      fun z => t ^ a • B (ω (t • z)) z := by
    funext z; rw [hB]
  rw [hfun]
  -- `g z = ω (L z)` with `L = t • id`, `‖L‖ ≤ 1`, so `‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` for `i ≤ j`.
  set L : Eucl P →L[ℝ] Eucl P := t • ContinuousLinearMap.id ℝ (Eucl P) with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖ContinuousLinearMap.id ℝ (Eucl P)‖ ≤ 1 * 1 :=
          mul_le_mul ht1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgfun : (fun z : Eucl P => ω (t • z)) = ω ∘ L := by
    funext z; simp [hL]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => ω (t • z)) := by
    rw [hgfun]; exact hω.comp L.contDiff
  have hgnorm : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ ≤ D := by
    intro i hi
    rw [hgfun, L.iteratedFDeriv_comp_right hω x (by exact_mod_cast le_top)]
    have hLx : L x ∈ closedBall (0 : Eucl P) R := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ 1 * R := mul_le_mul hLnorm hx' (norm_nonneg x) zero_le_one
        _ = R := one_mul R
    calc ‖(iteratedFDeriv ℝ i ω (L x)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ i ω (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ D * 1 := by
          apply mul_le_mul (hbound i hi _ hLx) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
      _ = D := mul_one D
  -- Pull out `t^a` (`0 ≤ t^a ≤ 1`) and apply the Leibniz bound.
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => B (ω (t • z)) z) :=
    B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)
  have hsmul : iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • B (ω (t • z)) z) x =
      t ^ a • iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x :=
    iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [hsmul, norm_smul]
  have hta : ‖t ^ a‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1
  have key := leibniz j _ _ B hBbound (fun z => ω (t • z)) hg x
  have hsum : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ +
      j * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ (R + j) * D := by
    have e1 : ‖x‖ * ‖iteratedFDeriv ℝ j (fun z => ω (t • z)) x‖ ≤ R * D :=
      mul_le_mul hx' (hgnorm j le_rfl) (norm_nonneg _) hR
    have e2 : (j : ℝ) * ‖iteratedFDeriv ℝ (j - 1) (fun z => ω (t • z)) x‖ ≤ j * D :=
      mul_le_mul_of_nonneg_left (hgnorm (j - 1) (Nat.sub_le j 1)) (Nat.cast_nonneg j)
    linarith
  calc ‖t ^ a‖ * ‖iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) z) x‖
      ≤ 1 * ((R + j) * D) := mul_le_mul hta (key.trans hsum) (norm_nonneg _) zero_le_one
    _ = (R + j) * D := one_mul _

/-- The radial homotopy operator `ψ(x) = ∫₀¹ tᵃ x ⌟ ω(t x) dt` (proof of Simon Ch. 6, 8.2,
Part I): for a smooth `(k + 1)`-form `ω`, `ψ` is a smooth `k`-form with
(i) `ψ(x)(v) = ∫₀¹ tᵃ ω(t x)(x, v) dt`,
(ii) `Dψ(x)[w](v) = ∫₀¹ tᵃ (t Dω(t x)[w](x, v) + ω(t x)(w, v)) dt`, and
(iii) `‖Dʲψ(x)‖ ≤ (R + j) D` on `B̄_R(0)` whenever `‖Dⁱω‖ ≤ D` there for all `i ≤ j`.
The integrand `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is jointly smooth, so `ψ = ∫₀¹ F(t, ·) dt`
is smooth with `Dʲψ = ∫₀¹ Dʲ_x F dt`; evaluation commutes with the integral. -/
theorem Submission.iwl_cr_radial_operator :
    ∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∃ ψ : DifferentialForm (Eucl P) k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
        (∀ (x : Eucl P) (v : Fin k → Eucl P),
          ψ x v = ∫ t in (0 : ℝ)..1, t ^ a * ω (t • x) (Fin.cons x v)) ∧
        (∀ (x w : Eucl P) (v : Fin k → Eucl P),
          fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1,
            t ^ a * (t * fderiv ℝ ω (t • x) w (Fin.cons x v) + ω (t • x) (Fin.cons w v))) ∧
        ∀ (j : ℕ) (R D : ℝ), 0 ≤ D →
          (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) →
          ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D := by
  intro P k a ω hω
  -- `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is smooth; `ψ = ∫₀¹ F(t, ·) dt` and
  -- `Dʲψ(x) = ∫₀¹ Dʲ(F(t, ·))(x) dt`, with `(t, x) ↦ Dʲ(F(t, ·))(x)` continuous.
  obtain ⟨hGsmooth, hGderiv⟩ := Submission.iwl_cr_ro_integrand_contDiff_fderiv P k a ω hω
  obtain ⟨hψsmooth, hGcont, hψiter⟩ :=
    Submission.iwl_cr_ro_intervalIntegral_contDiff P (Covector (Eucl P) k) _ 0 1 hGsmooth
  dsimp only at hψsmooth hGcont hψiter
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, t ^ a • (ω (t • x)).curryLeft x, hψsmooth, ?_, ?_, ?_⟩
  · -- (i): evaluation at `v` is a continuous linear map, so it commutes with the integral.
    intro x v
    have hc : Continuous fun t : ℝ => t ^ a • (ω (t • x)).curryLeft x :=
      hGsmooth.continuous.comp (continuous_id.prodMk continuous_const)
    have e := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousAlternatingMap.apply_apply] at e
    beta_reduce
    rw [← e]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      smul_eq_mul]
    rfl
  · -- (ii): `Dψ(x)[w] = D¹ψ(x)(w)`; evaluate `∫₀¹ D¹(F(t, ·))(x) dt` at `w`, then at `v`.
    intro x w v
    have hc₁ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x :=
      (hGcont 1).comp (continuous_id.prodMk continuous_const)
    have hc₂ : Continuous fun t : ℝ =>
        iteratedFDeriv ℝ 1 (fun z => t ^ a • (ω (t • z)).curryLeft z) x (fun _ => w) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
        (fun _ => w)).continuous.comp hc₁
    have e₁ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Eucl P) (Covector (Eucl P) k)
      (fun _ => w)).intervalIntegral_comp_comm (hc₁.intervalIntegrable (μ := volume) 0 1)
    have e₂ := (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).intervalIntegral_comp_comm
      (hc₂.intervalIntegrable (μ := volume) 0 1)
    simp only [ContinuousMultilinearMap.apply_apply, ContinuousAlternatingMap.apply_apply] at e₁ e₂
    have e₀ : ∀ f : Eucl P → Covector (Eucl P) k,
        fderiv ℝ f x w = iteratedFDeriv ℝ 1 f x (fun _ => w) :=
      fun f => (iteratedFDeriv_one_apply (fun _ : Fin 1 => w)).symm
    rw [e₀, hψiter 1 x, ← e₁, ← e₂]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [iteratedFDeriv_one_apply]
    exact hGderiv t x w v
  · -- (iii): `‖Dʲψ(x)‖ ≤ ∫₀¹ ‖Dʲ(F(t, ·))(x)‖ dt ≤ (R + j) D`.
    intro j R D hD hω_le x hx
    rw [hψiter j x]
    have hle : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ j (fun z => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D := by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Submission.iwl_cr_ro_integrand_iteratedFDeriv_le P k a ω hω j R D hD hω_le t
        ⟨ht.1.le, ht.2⟩ x hx
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
    rwa [sub_zero, abs_one, mul_one] at h
/-- Pointwise integrand identity of the radial homotopy formula: for `L : E →L[ℝ] Λ^{k+1}(E)`,
`α ∈ Λ^{k+1}(E)`, `x ∈ E`, `u ∈ E^{k+1}`, `t ∈ ℝ` and `û_j = removeNth j u`,
`t^{k+1} Alt(L)(x, u) + ∑_j (-1)^j t^k (t L(u_j)(x, û_j) + α(u_j, û_j))
  = t^{k+1} L(x)(u) + (k + 1) t^k α(u)`.
Expanding `Alt(L)(x, u) = L(x)(u) - ∑_j (-1)^j L(u_j)(x, û_j)` cancels the `t^{k+1}` cross
terms, and `alternatizeUncurryFin (curryLeft α) = (k + 1) • α` evaluates the `α`-sum. -/
theorem Submission.iwl_cr_rh_integrand_identity :
    ∀ (P k : ℕ) (L : Eucl P →L[ℝ] Covector (Eucl P) (k + 1)) (α : Covector (Eucl P) (k + 1))
      (x : Eucl P) (u : Fin (k + 1) → Eucl P) (t : ℝ),
      t ^ (k + 1) * ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) +
          ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
            (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) +
              α (Fin.cons (u j) (Fin.removeNth j u)))) =
        t ^ (k + 1) * L x u + ((k : ℝ) + 1) * t ^ k * α u := by
  intro P k L α x u t
  -- `removeNth (j + 1) (x, u) = (x, removeNth j u)`.
  have hrem : ∀ j : Fin (k + 1),
      Fin.removeNth j.succ (Fin.cons x u : Fin (k + 2) → Eucl P) =
        Fin.cons x (Fin.removeNth j u) :=
    fun j => Fin.cons_comp_succ_succAbove x u j
  -- Split `Alt(L)(x, u)` into the index `0` and the indices `j.succ`.
  have hA : ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) =
      L x u - ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
        L (u j) (Fin.cons x (Fin.removeNth j u)) := by
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
      Fin.val_succ, Fin.cons_succ, hrem, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      pow_succ, mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  -- `∑_j (-1)^j α(u_j, û_j) = (k + 1) α(u)`: evaluate `Alt(curryLeft α) = (k + 1) • α` at `u`.
  have hB : ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * α (Fin.cons (u j) (Fin.removeNth j u)) =
      ((k : ℝ) + 1) * α u := by
    have h := congrArg (fun f => f u) (ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft α)
    simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.smul_apply,
      zsmul_eq_mul, nsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.cast_add,
      Nat.cast_one] at h
    exact h
  -- Distribute `(-1)^j t^k (t a_j + b_j) = t^{k+1} (-1)^j a_j + t^k (-1)^j b_j` over the sum.
  have hsum : ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
        (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) +
          α (Fin.cons (u j) (Fin.removeNth j u)))) =
      t ^ (k + 1) * ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
          L (u j) (Fin.cons x (Fin.removeNth j u)) +
        t ^ k * ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
          α (Fin.cons (u j) (Fin.removeNth j u)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hA, hsum, hB]
  ring

/-- Radial fundamental theorem of calculus: for a smooth form `φ`,
`∫₀¹ (t^(m+1) Dφ(t x)[x](u) + (m + 1) t^m φ(t x)(u)) dt = φ(x)(u)`, since the integrand is the
derivative of `g(t) = t^(m+1) φ(t x)(u)` and `g(1) - g(0) = φ(x)(u)`. -/
theorem Submission.iwl_cr_rh_radial_ftc :
    ∀ (P n m : ℕ) (φ : DifferentialForm (Eucl P) n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ (x : Eucl P) (u : Fin n → Eucl P),
        ∫ t in (0 : ℝ)..1, (t ^ (m + 1) * fderiv ℝ φ (t • x) x u +
          ((m : ℝ) + 1) * t ^ m * φ (t • x) u) = φ x u := by
  intro P n m φ hφ x u
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- `g(s) = s^(m+1) φ(s x)(u)` has the integrand as derivative at every `t`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s ^ (m + 1) * φ (s • x) u)
        (t ^ (m + 1) * fderiv ℝ φ (t • x) x u + ((m : ℝ) + 1) * t ^ m * φ (t • x) u) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => φ (s • x)) (fderiv ℝ φ (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun s : ℝ => φ (s • x) u) (fderiv ℝ φ (t • x) x u) t :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).hasFDerivAt.comp_hasDerivAt t h2
    refine ((hasDerivAt_pow (m + 1) t).fun_mul h3).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  -- The integrand is continuous, hence interval integrable.
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (m + 1) * fderiv ℝ φ (t • x) x u +
      ((m : ℝ) + 1) * t ^ m * φ (t • x) u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hc1 : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x u := by
      have : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x :=
        (hcont.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
      exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).continuous.comp this
    have hc2 : Continuous fun t : ℝ => φ (t • x) u :=
      (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ u).continuous.comp
        (hφ.continuous.comp (continuous_id.smul continuous_const))
    exact ((continuous_pow (m + 1)).mul hc1).add
      ((continuous_const.mul (continuous_pow m)).mul hc2)
  -- Fundamental theorem of calculus on `[0, 1]`: `g(1) - g(0) = φ(x)(u) - 0`.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- Radial homotopy formula in degree zero: if `χ(x)(v) = ∫₀¹ t⁰ dφ(t x)(x, v) dt` for a smooth
`0`-form `φ`, then `χ(x) = φ(x) - φ(0)` (fundamental theorem of calculus along `t ↦ t x`). -/
theorem Submission.iwl_cr_rh_degree_zero :
    ∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ (x : Eucl P) (v : Fin 0 → Eucl P),
        χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) →
      ∀ x, χ x = φ x - φ 0 := by
  intro P φ χ hφ hχ x
  ext v
  -- `dφ(t x)(x, v) = Dφ(t x)[x](v)`: the alternating sum has the single term `i = 0`.
  have hd : ∀ t : ℝ, extDeriv φ (t • x) (Fin.cons x v) = fderiv ℝ φ (t • x) x v := by
    intro t
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [hχ x v, ContinuousAlternatingMap.sub_apply]
  simp only [pow_zero, one_mul, hd]
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- `s ↦ φ(s x)(v)` has derivative `Dφ(t x)[x](v)` at every `t`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => φ (s • x) v) (fderiv ℝ φ (t • x) x v) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 : HasDerivAt (fun s : ℝ => φ (s • x)) (fderiv ℝ φ (t • x) x) t :=
      (hdiff (t • x)).hasFDerivAt.comp_hasDerivAt t h1
    exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).hasFDerivAt.comp_hasDerivAt t h2
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ φ (t • x) x v) volume 0 1 := by
    apply Continuous.intervalIntegrable
    have : Continuous fun t : ℝ => fderiv ℝ φ (t • x) x :=
      (hcont.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    exact (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ v).continuous.comp this
  -- Fundamental theorem of calculus on `[0, 1]`.
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **Radial homotopy formula on `ℝ^P`** (the form version of Simon Ch. 6, 2.25–2.26 and 2.31 for
the homotopy `(t, x) ↦ t x`, used by the cone construction in the proof of 8.2).
(a) If `φ` is a smooth `(k + 1)`-form, `Dψ(x)[w](v) = ∫₀¹ tᵏ (t Dφ(tx)[w](x, v) + φ(tx)(w, v)) dt`
and `χ(x)(v) = ∫₀¹ tᵏ⁺¹ dφ(tx)(x, v) dt`, then `χ + dψ = φ`, i.e. `H(dφ) + d(H′φ) = φ`.
(b) For a smooth `0`-form `φ`, `H(dφ)(x) = φ(x) − φ(0)`.

For (a), `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ)` with `ûⱼ = removeNth j u`.  All integrands are
continuous, so `χ(x)(u) + dψ(x)(u)` is a single integral over `[0, 1]`.  The cross terms cancel and
`∑ⱼ (-1)ʲ α(uⱼ, ûⱼ) = (k + 1) α(u)`, so its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`,
the derivative of `t ↦ tᵏ⁺¹ φ(tx)(u)`, whose integral over `[0, 1]` is `φ(x)(u)`. -/
theorem Submission.iwl_cr_radial_homotopy : (∀ (P k : ℕ) (φ : DifferentialForm (Eucl P) (k + 1)) (ψ : DifferentialForm (Eucl P) k) (χ : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x w : Eucl P) (v : Fin k → Eucl P), fderiv ℝ ψ x w v = ∫ t in (0 : ℝ)..1, t ^ k * (t * fderiv ℝ φ (t • x) w (Fin.cons x v) + φ (t • x) (Fin.cons w v))) → (∀ (x : Eucl P) (v : Fin (k + 1) → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ (k + 1) * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x + extDeriv ψ x = φ x) ∧ (∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x : Eucl P) (v : Fin 0 → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x = φ x - φ 0) := by
  refine ⟨fun P k φ ψ χ hφ hψ hχ x => ?_, Submission.iwl_cr_rh_degree_zero⟩
  -- `φ`, `Dφ`, `dφ = alternatizeUncurryFinCLM ∘ Dφ` and `t ↦ t • x` are continuous.
  have hφc : Continuous φ := hφ.continuous
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hdφ : Continuous (extDeriv φ) :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp hDφ
  have hsx : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
  ext u
  -- The `j`-th integrand of `dψ(x)(u)` and the integrand of `χ(x)(u)` are continuous in `t`.
  have hg : ∀ j : Fin (k + 1), Continuous fun t : ℝ => t ^ k * (t * fderiv ℝ φ (t • x) (u j)
      (Fin.cons x (Fin.removeNth j u)) + φ (t • x) (Fin.cons (u j) (Fin.removeNth j u))) := by
    intro j
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (t • x) (u j) (Fin.cons x (Fin.removeNth j u)) :=
      ((hDφ.comp hsx).clm_apply continuous_const).eval_const _
    have h2 : Continuous fun t : ℝ => φ (t • x) (Fin.cons (u j) (Fin.removeNth j u)) :=
      (hφc.comp hsx).eval_const _
    exact (continuous_pow k).mul ((continuous_id.mul h1).add h2)
  have hf : Continuous fun t : ℝ => t ^ (k + 1) * extDeriv φ (t • x) (Fin.cons x u) :=
    (continuous_pow (k + 1)).mul ((hdφ.comp hsx).eval_const _)
  -- `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ) = ∑ⱼ (-1)ʲ ∫₀¹ tᵏ (t Dφ(tx)[uⱼ](x, ûⱼ) + φ(tx)(uⱼ, ûⱼ)) dt`.
  have hdψ : extDeriv ψ x u = ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) *
      ∫ t in (0 : ℝ)..1, t ^ k * (t * fderiv ℝ φ (t • x) (u j) (Fin.cons x (Fin.removeNth j u)) +
        φ (t • x) (Fin.cons (u j) (Fin.removeNth j u))) := by
    rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hψ x (u j) (Fin.removeNth j u), zsmul_eq_mul]
    push_cast
    rfl
  rw [ContinuousAlternatingMap.add_apply, hχ x u, hdψ]
  -- Collect `χ(x)(u) + dψ(x)(u)` into a single integral over `[0, 1]`.
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun j _ => ((hg j).const_mul _).intervalIntegrable 0 1,
    ← intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
      ((continuous_finsetSum _ fun j _ => (hg j).const_mul _).intervalIntegrable 0 1)]
  -- Its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`, so the integral is `φ(x)(u)`.
  rw [← Submission.iwl_cr_rh_radial_ftc P (k + 1) k φ hφ x u]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact Submission.iwl_cr_rh_integrand_identity P k (fderiv ℝ φ (t • x)) (φ (t • x)) x u t

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

/-- The cone `0 ⨯ X` over `X ∈ 𝒟ₘ(ℝ^P)` with `spt X ⊆ B̄_R(0)` (**Simon Ch. 6, 2.23, 2.30**):
`C(ω) := X(Φ ω)` for the cut-off radial operator `Φ ω = ζ · Hω`, which satisfies
`Hω(x)(v) = ∫₀¹ tᵐ ω(tx)(x, v) dt` on `B_r(0)`, `r = max R 0 + 1`.  `Φ` maps null sequences to
null sequences, so `C` is a current; a test form `ψ` with the `Hω`-formula on an open `N ⊇ spt X`
agrees with `Φ ω` on the open `N ∩ B_r(0) ⊇ spt X`, so `X ψ = X (Φ ω) = C ω` by locality. -/
theorem Submission.iwl_cr_cone_exists : ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m), X.support ⊆ closedBall 0 R → ∃ C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) := by
  intro P m R X hX
  -- The cut-off radial operator on `B_r(0)`, `r = max R 0 + 1`: its hypothesis is the radial
  -- operator with `k = a = m`, without the derivative formula.
  obtain ⟨Φ, hΦ, hΦH⟩ := Submission.iwl_cr_ce_cutoff_radial_operator P m (max R 0 + 1)
    fun ω hω => by
      obtain ⟨ψ, hψ, hψH, -, hψD⟩ := Submission.iwl_cr_radial_operator P m m ω hω
      exact ⟨ψ, hψ, hψH, hψD⟩
  -- `C = X ∘ Φ` is a current, since `Φ` maps null sequences to null sequences.
  refine ⟨⟨X.toCurrent ∘ₗ Φ, fun ωs hωs => X.continuous' (fun l => Φ (ωs l)) (hΦ ωs hωs)⟩, ?_⟩
  rintro ω ψ ⟨N, hN, hXN, hψN⟩
  -- `Φ ω = ψ` on the open set `N ∩ B_r(0) ⊇ spt X`, so `X (Φ ω) = X ψ` by locality.
  have hXr : X.support ⊆ ball 0 (max R 0 + 1) :=
    hX.trans (closedBall_subset_ball ((le_max_left R 0).trans_lt (lt_add_one _)))
  exact Submission.iwl_cr_ce_apply_eq_of_eqOn_nhds_support P m univ X (Φ ω) ψ
    (N ∩ ball 0 (max R 0 + 1)) (hN.inter isOpen_ball) (subset_inter hXN hXr)
    fun x hx => ContinuousAlternatingMap.ext fun v =>
      (hΦH ω x hx.2 v).trans (hψN x hx.1 v).symm

/-- **Cone estimates** (items 3–4 of the cycle reduction; cf. the cone 2.30 and the mass bound
2.27 of Simon Ch. 6).  With `c = P^{2m+1}` and `R ≥ 0`: if `spt X ⊆ B̄_R(0)` and `C` is a cone
over `X`, i.e. `C(ω) = X(ψ)` whenever `ψ(x)(v) = ∫₀¹ t^m ω(tx)(x, v) dt` near `spt X`, then
`spt C ⊆ B̄_R(0)` and `M(C) ≤ c R M(X)`; and if `X_j ⇀ X` (all supported in `B̄_R(0)`), the
cones `C_j` over `X_j` converge weakly to `C`.  Each `ω` is tested through one cut-off radial
form `ψ = ζ ψ_ω`, with `ζ = 1` near `B̄_R(0)`. -/
theorem Submission.iwl_cr_cone_estimates : ∀ (P m : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 ≤ R → (∀ (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → C.support ⊆ closedBall 0 R ∧ (X.mass < ∞ → C.mass ≤ ENNReal.ofReal (c * R) * X.mass)) ∧ (∀ (Xj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) m) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (Cj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, (Xj j).support ⊆ closedBall 0 R) → X.support ⊆ closedBall 0 R → (∀ j, (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ (Xj j).support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → (Cj j) ω = (Xj j) ψ)) → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → WeaklyConvergesOn Xj X → WeaklyConvergesOn Cj C) := by
  intro P m
  -- Step 1: for `0 < r < s`, `ω` has a cut-off radial form `ψ`, satisfying the radial formula on
  -- `B_r(0)` and `|ψ| ≤ P^{2m+1} s` if `|ω| ≤ 1`.
  have hcut : ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (r s : ℝ), 0 < r → r < s →
      ∃ ψ : TestFormOn (univ : Set (Eucl P)) m,
        (∀ x ∈ ball (0 : Eucl P) r, ∀ v : Fin m → Eucl P,
          (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1,
            t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) ∧
        ((∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) (m + 1)) y) ≤ 1) →
          ∀ x, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl P) m) x) ≤
            (P : ℝ) ^ (2 * m + 1) * s) := by
    intro ω r s hr hrs
    obtain ⟨ψ₀, hψ₀, hψ₀eq, -⟩ :=
      Submission.iwl_cr_radial_operator P m m (ω : DifferentialForm (Eucl P) (m + 1))
        ω.property.1.1
    exact Submission.iwl_cr_cest_cutoff_radial_form P m ω ψ₀ r s hψ₀ hψ₀eq hr hrs
  refine ⟨(P : ℝ) ^ (2 * m + 1), by positivity, fun R hR => ⟨?_, ?_⟩⟩
  · -- Step 2 (a): support, and mass with `ψ` cut off between `B_{R+δ/2}(0)` and `B_{R+δ}(0)`.
    intro X C hX hcone
    refine ⟨Submission.iwl_cr_cest_cone_support P m R X C hX hcone, fun hXm => ?_⟩
    refine Submission.iwl_cr_cest_mass_le_of_forms P m (m + 1) X C ((P : ℝ) ^ (2 * m + 1)) R
      (by positivity) hR hXm fun ω hω δ hδ => ?_
    obtain ⟨ψ, hψeq, hψle⟩ := hcut ω (R + δ / 2) (R + δ) (by linarith) (by linarith)
    exact ⟨ψ, hcone ω ψ ⟨ball 0 (R + δ / 2), isOpen_ball,
      hX.trans (closedBall_subset_ball (by linarith)), hψeq⟩, hψle hω.2⟩
  · -- Step 3 (b): one `ψ`, cut off between `B_{R+1}(0)` and `B_{R+2}(0)`, serves every `j`, so
    -- `C_j(ω) = X_j(ψ) → X(ψ) = C(ω)`.
    intro Xj X Cj C hXj hX hconej hcone hconv ω
    obtain ⟨ψ, hψeq, -⟩ := hcut ω (R + 1) (R + 2) (by linarith) (by linarith)
    have hj : ∀ j, Cj j ω = Xj j ψ := fun j => hconej j ω ψ ⟨ball 0 (R + 1), isOpen_ball,
      (hXj j).trans (closedBall_subset_ball (by linarith)), hψeq⟩
    rw [hcone ω ψ ⟨ball 0 (R + 1), isOpen_ball,
      hX.trans (closedBall_subset_ball (by linarith)), hψeq⟩]
    exact (hconv ψ).congr fun j => (hj j).symm
/-- Simon 2.31 for `X = ∂Y` with `spt Y` compact: the cone `C = 0 ⨯ ∂Y` (`C(ω) = ∂Y(ψ)` whenever
`ψ = H(ω)` near `spt ∂Y`) has `∂C = ∂Y`.  For `φ ∈ 𝒟ᵐ` the radial form `χ = H(dφ)` satisfies
`dχ = dφ` by the radial homotopy formula, and `ζχ`, with a cut-off `ζ = 1` near `spt Y`, is
admissible in the cone identity, so `∂C(φ) = C(dφ) = Y(d(ζχ)) = Y(dφ) = ∂Y(φ)`. -/
theorem Submission.iwl_cr_cone_boundary :
    ∀ (P m : ℕ) (R : ℝ) (Y C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
      Y.support ⊆ closedBall 0 R →
      (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m),
        (∃ N : Set (Eucl P), IsOpen N ∧ Y.boundary.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P,
          (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1,
            t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) →
        C ω = Y.boundary ψ) →
      C.boundary = Y.boundary := by
  intro P m R Y C hY hcone
  -- `dχ = dφ` for `χ = H(dφ)`: in degree `0`, `χ = φ - φ 0`; in degree `k + 1`, `χ + dψ = φ`
  -- with `ψ = Hφ`, and `d(dψ) = 0`.
  have hd : ∀ (k : ℕ) (φ χ : DifferentialForm (Eucl P) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ →
      (∀ (x : Eucl P) (v : Fin k → Eucl P),
        χ x v = ∫ t in (0 : ℝ)..1, t ^ k * extDeriv φ (t • x) (Fin.cons x v)) →
      extDeriv χ = extDeriv φ := by
    intro k
    cases k with
    | zero =>
      intro φ χ hφ _ hχ
      have hχφ : χ = fun x => φ x - φ 0 :=
        funext (Submission.iwl_cr_radial_homotopy.2 P φ χ hφ hχ)
      subst hχφ
      funext x
      rw [extDeriv, extDeriv, fderiv_sub_const]
    | succ k =>
      intro φ χ hφ hχs hχ
      obtain ⟨ψ, hψ, -, hψd, -⟩ := Submission.iwl_cr_radial_operator P k k φ hφ
      have hφχ : φ = χ + extDeriv ψ := funext fun x =>
        (Submission.iwl_cr_radial_homotopy.1 P k φ ψ χ hφ hψd hχ x).symm
      have hdψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extDeriv ψ) := by
        change ContDiff ℝ _ (fun x => ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ ψ x))
        simpa only [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, Function.comp_def]
          using (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).contDiff.comp
            (hψ.fderiv_right (by simp))
      funext x
      rw [hφχ, extDeriv_add (hχs.differentiable (by simp)).differentiableAt
        (hdψ.differentiable (by simp)).differentiableAt, extDeriv_extDeriv hψ (by simp),
        Pi.zero_apply, add_zero]
  -- A cut-off `ζ` with `ζ = 1` on the ball `B = B_{R₀+1}(0) ⊇ spt Y ⊇ spt ∂Y`.
  have hR₀ : 0 ≤ max R 0 := le_max_right R 0
  let ζ : ContDiffBump (0 : Eucl P) := ⟨max R 0 + 1, max R 0 + 2, by linarith, by linarith⟩
  have hζ : ∀ x ∈ ball (0 : Eucl P) (max R 0 + 1), ζ x = 1 := fun x hx =>
    ζ.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hYB : Y.support ⊆ ball (0 : Eucl P) (max R 0 + 1) :=
    hY.trans (closedBall_subset_ball (by linarith [le_max_left R 0]))
  refine GeometricCurrentOn.ext fun φ => ?_
  rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply]
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : DifferentialForm (Eucl P) m) := φ.property.1.1
  have hdφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extDeriv (φ : DifferentialForm (Eucl P) m)) :=
    (exteriorDerivativeTestOn univ m φ).property.1.1
  -- `χ = H(dφ)` and the test form `ζχ`.
  obtain ⟨χ, hχs, hχ, -, -⟩ := Submission.iwl_cr_radial_operator P m m _ hdφ
  let ζχ : TestFormOn (univ : Set (Eucl P)) m :=
    ⟨fun x => ζ x • χ x, ⟨⟨ζ.contDiff.smul hχs, ζ.hasCompactSupport.smul_right⟩, subset_univ _⟩⟩
  -- `ζχ` satisfies the `H(dφ)`-formula on `B ⊇ spt ∂Y`, so `C(dφ) = ∂Y(ζχ) = Y(d(ζχ))`.
  have hC : C (exteriorDerivativeTestOn univ m φ) = Y.boundary ζχ := by
    refine hcone _ _ ⟨ball 0 (max R 0 + 1), isOpen_ball,
      (Submission.iwl_cr_support_lemmas.1 P m univ Y).trans hYB, ?_⟩
    intro x hx v
    change (ζ x • χ x) v = _
    rw [ContinuousAlternatingMap.smul_apply, hζ x hx, one_smul, hχ x v]
    rfl
  rw [hC, GeometricCurrentOn.boundary_apply]
  -- `d(ζχ) = dχ = dφ` on `B`.
  have hdχ := hd m _ χ hφ hχs hχ
  have hloc : ∀ x ∈ ball (0 : Eucl P) (max R 0 + 1),
      extDeriv (ζχ : DifferentialForm (Eucl P) m) x =
        extDeriv (φ : DifferentialForm (Eucl P) m) x := by
    intro x hx
    rw [← hdχ]
    apply Filter.EventuallyEq.extDeriv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    change ζ y • χ y = χ y
    rw [hζ y hy, one_smul]
  -- So `d(ζχ) - dφ` vanishes on `B ⊇ spt Y`, and `Y` kills it.
  have hsupp : tsupport ((exteriorDerivativeTestOn univ m ζχ - exteriorDerivativeTestOn univ m φ :
      TestFormOn (univ : Set (Eucl P)) (m + 1)) : DifferentialForm (Eucl P) (m + 1)) ⊆
      (ball (0 : Eucl P) (max R 0 + 1))ᶜ := by
    refine closure_minimal ?_ isOpen_ball.isClosed_compl
    intro x hx hxB
    apply hx
    change extDeriv (ζχ : DifferentialForm (Eucl P) m) x -
      extDeriv (φ : DifferentialForm (Eucl P) m) x = 0
    rw [hloc x hxB, sub_self]
  have h0 := Submission.isoperimetric_apply_eq_zero_of_disjoint_support P (m + 1) univ Y _
    (Set.disjoint_of_subset_left hsupp hYB.disjoint_compl_left)
  rw [map_sub Y.toCurrent] at h0
  exact sub_eq_zero.1 h0

/-- Slices of a form supported off `Φ([0, 1] × B̄_R(0))`, `Φ(s, x) = (s, x) ∈ ℝ^{P+1}`, are
annihilated by `X`: for `s ∈ [0, 1]`, `tsupport (φ s)` lies in the closed set
`{x | Φ(s, x) ∈ tsupport η}`, which misses `B̄_R(0) ⊇ spt X`, so `X (φ s) = 0` and the integral
over `[0, 1]` vanishes. -/
theorem Submission.iwl_cr_ci_ps_slice_integral_eq_zero :
    ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m)
      (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1))
      (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m),
      X.support ⊆ closedBall 0 R →
      Disjoint (tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)))
        ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ''
          (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P),
        (φ s : DifferentialForm (Eucl P) m) x v =
          (η : DifferentialForm (Eucl (P + 1)) (m + 1))
            ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
              (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))
            (Fin.cons (EuclideanSpace.single 0 1) fun i =>
              (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
                (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) →
      ∫ s in (0 : ℝ)..1, X (φ s) = 0 := by
  intro P m R X η φ hX hdisj hφ
  have hzero : ∀ s ∈ Icc (0 : ℝ) 1, X (φ s) = 0 := by
    intro s hs
    -- `C_s = {x | Φ(s, x) ∈ tsupport η}` is closed, as `x ↦ Φ(s, x)` is continuous.
    have hΦ : Continuous fun x : Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) :=
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
        (continuous_const.finCons (EuclideanSpace.equiv (Fin P) ℝ).continuous)
    have hC := (isClosed_tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1))).preimage hΦ
    -- `φ s` vanishes off `C_s` by the slice identity, so `tsupport (φ s) ⊆ C_s`.
    have hsupp : tsupport (φ s : DifferentialForm (Eucl P) m) ⊆
        (fun x : Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ⁻¹'
          tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)) := by
      refine closure_minimal ?_ hC
      intro x hx
      by_contra hxC
      have hxC' : (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) ∉
          tsupport (η : DifferentialForm (Eucl (P + 1)) (m + 1)) := hxC
      refine Function.mem_support.1 hx ?_
      ext v
      rw [hφ s hs x v, image_eq_zero_of_notMem_tsupport hxC']
      rfl
    -- `spt X ⊆ B̄_R(0)` misses `C_s`: `Φ(s, x) ∈ Φ([0, 1] × B̄_R(0))` lies off `tsupport η`.
    refine Submission.isoperimetric_apply_eq_zero_of_disjoint_support P m univ X (φ s) ?_
    rw [Set.disjoint_left]
    intro x hx hxX
    exact Set.disjoint_left.1 hdisj (Set.mem_preimage.1 (hsupp hx))
      ⟨(s, x), Set.mk_mem_prod hs (hX hxX), rfl⟩
  -- The integrand vanishes on `uIcc 0 1 = [0, 1]`.
  have hcongr : EqOn (fun s => X (φ s)) (fun _ => (0 : ℝ)) (uIcc 0 1) := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact hzero s hs
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_zero]
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

/-- **Support of the product current `[[(0,1)]] × X`.**  With `Φ(s, x) = (s, x)`, the set
`L = Φ([0, 1] × B̄_R(0))` is compact as a continuous image of a compact set, hence closed.  If
`tsupport η` misses `L`, the slices `φ s = η(Φ(s, ·))(e₀, ι ·)` are annihilated by `X` (whose
support lies in `B̄_R(0)`), so `Z η = ∫₀¹ X (φ s) ds = 0`; by the support criterion, `spt Z ⊆ L`. -/
theorem Submission.iwl_cr_ci_product_support : ∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), (φ s : DifferentialForm (Eucl P) m) x v = (η : DifferentialForm (Eucl (P + 1)) (m + 1)) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → IsCompact ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) ∧ Z.support ⊆ ((fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) '' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : Eucl P) R)) := by
  intro P m R X Z hX hProd
  -- `L = Φ([0, 1] × B̄_R(0))` is compact, being a continuous image of a compact set.
  have hΦ : Continuous fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)) := by
    fun_prop
  have hL := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : Eucl P) R)).image hΦ
  -- `L` is closed, so it contains `spt Z` once `Z` kills every test form supported off `L`.
  refine ⟨hL, Submission.fiw_tb_ext_support_subset (P + 1) (m + 1) univ _ Z isOpen_univ
    hL.isClosed fun η hη => ?_⟩
  -- `Z η = ∫₀¹ X (φ s) ds` for the slices `φ s` of `η`, and that integral vanishes.
  obtain ⟨φ, -, hφ⟩ := Submission.iwl_cr_ci_slice_testForm P m η
  exact (hProd η φ fun s _ x v => hφ s x v).trans
    (Submission.iwl_cr_ci_ps_slice_integral_eq_zero P m R X η φ hX hη fun s _ x v => hφ s x v)
/-- Cut-off pull-backs of smooth forms are test forms (step 5 of the proof of Simon Ch. 6, 8.2):
for smooth `f : ℝ^P → ℝ^Q`, a smooth form `ω` and a smooth compactly supported `χ`,
`η(y) = χ(y) ω(f(y)) ∘ Df(y)` is smooth (the pull-back `B ↦ (α ↦ α ∘ B)` is analytic) and has
compact support. -/
theorem Submission.iwl_cr_ci_cutoff_pullback_testForm :
    ∀ (P Q k : ℕ) (f : Eucl P → Eucl Q) (χ : Eucl P → ℝ) (ω : DifferentialForm (Eucl Q) k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ →
      HasCompactSupport χ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω →
      ∃ η : TestFormOn (univ : Set (Eucl P)) k, ∀ y, (η : DifferentialForm (Eucl P) k) y =
        χ y • (ω (f y)).compContinuousLinearMap (fderiv ℝ f y) := by
  intro P Q k f χ ω hf hχ hχc hω
  -- `y ↦ Df(y)` is smooth.
  have hDf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right le_rfl
  -- The pull-back operator `B ↦ (α ↦ α ∘ B)` is analytic, hence smooth.
  have hpull : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (Eucl P →L[ℝ] Eucl Q) → Covector (Eucl Q) k →L[ℝ] Covector (Eucl P) k) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- So `p(y) = ω(f(y)) ∘ Df(y)` is smooth, and `η = χ • p` is smooth with compact support.
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => (ω (f y)).compContinuousLinearMap (fderiv ℝ f y)) :=
    (hpull.comp hDf).clm_apply (hω.comp hf)
  exact ⟨⟨fun y => χ y • (ω (f y)).compContinuousLinearMap (fderiv ℝ f y),
    ⟨hχ.smul hp, hχc.smul_right⟩, subset_univ _⟩, fun y => rfl⟩
/-- The cone map `h(y) = y₀ • π(y)`, `π(y) = (y₁, …, y_P)`, is a product of continuous linear maps,
hence smooth, and `h(Φ(s, x)) = s • x` for `Φ(s, x) = (s, x)`.  By the product rule
`Dh(y)(w) = y₀ • π(w) + w₀ • π(y)`, so `Dh(Φ(s, x))` maps `e₀ ↦ x` and `ι(w) = Φ(0, w) ↦ s • w`;
multilinearity then gives `α(x, s • v₁, …, s • vₘ) = s ^ m * α(x, v₁, …, vₘ)`. -/
theorem Submission.iwl_cr_ci_cone_map :
    ∀ (P m : ℕ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Eucl (P + 1) =>
      y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) ∧
    ∀ (s : ℝ) (x : Eucl P), (fun y : Eucl (P + 1) =>
      y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
      ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) =
      s • x ∧
    ∀ (α : Covector (Eucl P) (m + 1)) (v : Fin m → Eucl P),
      (α.compContinuousLinearMap (fderiv ℝ (fun y : Eucl (P + 1) =>
        y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))))
        (Fin.cons (EuclideanSpace.single 0 1) fun i =>
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) =
      s ^ m * α (Fin.cons x v) := by
  intro P m
  -- `p₀(y) = y₀` and `π(y) = (y₁, …, y_P)` are continuous linear maps, and `h(y) = p₀(y) • π(y)`.
  let p₀ : Eucl (P + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  let π : Eucl (P + 1) →L[ℝ] Eucl P :=
    (EuclideanSpace.equiv (Fin P) ℝ).symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.pi fun j : Fin P => ContinuousLinearMap.proj j.succ) ∘L
      (EuclideanSpace.equiv (Fin (P + 1)) ℝ).toContinuousLinearMap
  have hh : (fun y : Eucl (P + 1) => y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm
      (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) = fun y => p₀ y • π y := rfl
  -- Values on `Φ(t, z)`: `p₀(Φ(t, z)) = t` and `π(Φ(t, z)) = z`.
  have hp₀Φ : ∀ (t : ℝ) (z : Eucl P), p₀ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons t (EuclideanSpace.equiv (Fin P) ℝ z))) = t := fun t z => rfl
  have hπΦ : ∀ (t : ℝ) (z : Eucl P), π ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons t (EuclideanSpace.equiv (Fin P) ℝ z))) = z := fun t z => rfl
  refine ⟨?_, fun s x => ⟨?_, fun α v => ?_⟩⟩
  · rw [hh]
    exact p₀.contDiff.smul π.contDiff
  · rw [hh]
    show p₀ _ • π _ = s • x
    rw [hp₀Φ, hπΦ]
  · -- Product rule: `Dh(Φ(s, x)) = s • π + p₀.smulRight x`.
    have hD : fderiv ℝ (fun y : Eucl (P + 1) => y 0 • (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))
        ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) = s • π + p₀.smulRight x := by
      have hd := (p₀.hasFDerivAt (x := (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)))).smul π.hasFDerivAt
      rw [hp₀Φ, hπΦ] at hd
      rw [hh]
      exact hd.fderiv
    -- `Dh(Φ(s, x)) e₀ = s • 0 + 1 • x = x` and `Dh(Φ(s, x)) (ι w) = s • w + 0 • x = s • w`.
    have he₀ : (s • π + p₀.smulRight x) (EuclideanSpace.single 0 1) = x := by
      have h1 : p₀ (EuclideanSpace.single 0 1) = 1 := by simp [p₀]
      have h2 : π (EuclideanSpace.single 0 1) = 0 := by
        ext j
        simp [π, Fin.succ_ne_zero]
      rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, h1, h2, smul_zero,
        one_smul, zero_add]
    have hι : ∀ w : Eucl P, (s • π + p₀.smulRight x) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ w))) = s • w := by
      intro w
      rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hp₀Φ, hπΦ, zero_smul,
        add_zero]
    rw [hD, ContinuousAlternatingMap.compContinuousLinearMap_apply, Fin.comp_cons, he₀]
    have hcomp : (⇑(s • π + p₀.smulRight x) ∘ fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i)))) = fun i => s • v i :=
      funext fun i => hι (v i)
    rw [hcomp]
    -- Multilinearity: `α(x, s • v₁, …, s • vₘ) = (1 * s ^ m) • α(x, v₁, …, vₘ)`.
    have key : (Fin.cons x (fun i => s • v i) : Fin (m + 1) → Eucl P) =
        fun j => (Fin.cons (1 : ℝ) (fun _ : Fin m => s) : Fin (m + 1) → ℝ) j •
          (Fin.cons x v : Fin (m + 1) → Eucl P) j := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero, one_smul]
      · simp only [Fin.cons_succ]
    rw [key, ContinuousAlternatingMap.map_smul_univ, Fin.prod_univ_succ, smul_eq_mul]
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
/-- The product `χ(y) = ϑ(y₀) ζ(π y)` of cut-offs on `ℝ` and `ℝ^P`, `π y = (y₁, …, y_P)`, is a
cut-off on `ℝ^{P+1}`: `y ↦ y₀` and `π` are linear, so `χ` is smooth, and `‖y‖ ≤ |y₀| + ‖π y‖`
puts `support χ` inside the compact ball `B̄_{a+b}(0)`, where `tsupport ϑ ⊆ B̄_a(0)` and
`tsupport ζ ⊆ B̄_b(0)`. -/
theorem Submission.iwl_cr_ci_product_cutoff :
    ∀ (P : ℕ) (ϑ : ℝ → ℝ) (ζ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑ →
      HasCompactSupport ϑ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ → HasCompactSupport ζ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Eucl (P + 1) => ϑ (y 0) *
        ζ ((EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ∧
      HasCompactSupport (fun y : Eucl (P + 1) => ϑ (y 0) *
        ζ ((EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) := by
  intro P ϑ ζ hϑ hϑc hζ hζc
  -- `π y = (y₁, …, y_P)`: the equivalences `EuclideanSpace.equiv` around `Fin.tail`.
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) π :=
    (EuclideanSpace.equiv (Fin P) ℝ).symm.contDiff.comp
      ((contDiff_pi.2 fun j : Fin P => contDiff_apply ℝ ℝ j.succ).comp
        (EuclideanSpace.equiv (Fin (P + 1)) ℝ).contDiff)
  refine ⟨(hϑ.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (P + 1))).contDiff).mul
    (hζ.comp hπ), ?_⟩
  -- `‖y‖² = y₀² + ‖π y‖²`, hence `‖y‖ ≤ |y₀| + ‖π y‖`.
  have hnorm : ∀ y : Eucl (P + 1), ‖y‖ ≤ |y 0| + ‖π y‖ := by
    intro y
    have h1 : ‖y‖ ^ 2 = y 0 ^ 2 + ‖π y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    have h2 : ‖y‖ ^ 2 ≤ (|y 0| + ‖π y‖) ^ 2 := by
      rw [h1, add_sq, sq_abs]
      nlinarith [abs_nonneg (y 0), norm_nonneg (π y)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  -- `χ y ≠ 0` forces `|y₀| ≤ a` and `‖π y‖ ≤ b`, so `support χ ⊆ B̄_{a+b}(0)`.
  obtain ⟨a, ha⟩ := hϑc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨b, hb⟩ := hζc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl (P + 1)) (a + b)) ?_
  intro y hy
  by_contra hne
  have h0 : y 0 ∈ closedBall (0 : ℝ) a := ha (subset_tsupport _ (left_ne_zero_of_mul hne))
  have hπy : π y ∈ closedBall (0 : Eucl P) b := hb (subset_tsupport _ (right_ne_zero_of_mul hne))
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at h0
  rw [mem_closedBall_zero_iff] at hπy
  exact hy (mem_closedBall_zero_iff.2 ((hnorm y).trans (add_le_add h0 hπy)))
/-- **`Hⁿ(M ∩ K) < ∞` for integer multiplicity triples (Simon Ch. 6, 3.1).**  If
`(M, θ, ξ)` is a rectifiable triple in `U` and `θ` is integer-valued on `M`, then `θ ≥ 1` on `M`
(`θ > 0`), so for compact `K ⊆ U`:
`Hⁿ(M ∩ K) = ∫⁻_{M ∩ K} 1 dHⁿ ≤ ∫⁻_{M ∩ K} |θ| dHⁿ < ∞` (`θ` is `Hⁿ`-integrable on `M ∩ K`). -/
theorem Submission.iwl_cr_ci_ie_measure_inter_compact_lt_top : ∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (K : Set (Eucl P)), IsRectifiableTriple U n M θ ξ → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → IsCompact K → K ⊆ U → (μHE[n] : Measure (Eucl P)) (M ∩ K) < ∞ := by
  intro P n U M θ ξ K hT hint hK hKU
  -- `θ = k ∈ ℕ` and `θ > 0` force `θ ≥ 1` on `M`.
  have h1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hint x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    have hk0 : k ≠ 0 := by rintro rfl; simp at hpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hθ : IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) := hT.integrableOn K hK hKU
  have hnm : NullMeasurableSet (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
  -- `‖θ‖ₑ ≥ 1` a.e. on `M ∩ K`.
  have hae : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)), (1 : ℝ≥0∞) ≤ ‖θ x‖ₑ := by
    filter_upwards [ae_restrict_mem₀ hnm] with x hx
    have h := h1 x hx.1
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by linarith)]
    exact ENNReal.one_le_ofReal.mpr h
  -- `Hⁿ(M ∩ K) = ∫⁻_{M ∩ K} 1 ≤ ∫⁻_{M ∩ K} ‖θ‖ₑ < ∞`.
  calc (μHE[n] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, (1 : ℝ≥0∞) ∂(μHE[n] : Measure (Eucl P)) := (setLIntegral_one _).symm
    _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hae
    _ < ∞ := hθ.hasFiniteIntegral
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
/-- **An `n`-vector commutes with the interval integral of a continuous covector family.**  If
`f : ℝ → Λᵐ(ℝ^P)` is continuous and `c(v) = ∫_a^b f(s)(v) ds` for every `v`, then
`∫_a^b w(f(s)) ds = w(c)` for every `w ∈ Λₘ(ℝ^P)`: evaluation at `v` is a continuous linear
functional, so `(∫_a^b f)(v) = ∫_a^b f(s)(v) ds = c(v)` and `∫_a^b f = c`; then `w` commutes with
the integral (`ContinuousLinearMap.intervalIntegral_comp_comm`). -/
theorem Submission.iwl_cr_ci_ie_nvector_intervalIntegral : ∀ (P m : ℕ) (a b : ℝ) (f : ℝ → Covector (Eucl P) m) (c : Covector (Eucl P) m) (w : NVector (Eucl P) m), Continuous f → (∀ v : Fin m → Eucl P, c v = ∫ s in a..b, f s v) → ∫ s in a..b, w (f s) = w c := by
  intro P m a b f c w hf hc
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  -- `∫_a^b f = c`: both agree at every `v`, via the evaluation functional `α ↦ α v`.
  have hI : (∫ s in a..b, f s) = c := by
    ext v
    rw [hc v]
    let L : Covector (Eucl P) m →L[ℝ] ℝ :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Eucl P) ℝ v).comp
        (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
    have hL : ∀ α : Covector (Eucl P) m, L α = α v := fun α => rfl
    have h := L.intervalIntegral_comp_comm hfi
    simp only [hL] at h
    exact h.symm
  -- `w` commutes with the integral.
  rw [w.intervalIntegral_comp_comm hfi, hI]

/-- **Fubini for `∫ θ ⟨Φ(s), ξ⟩ dμ` over `s ∈ [0, 1]`.**  Let `μ` be s-finite, `θ ∈ L¹(μ)` and
`|ξ(x)(α)| ≤ ‖α‖` for `μ`-a.e. `x`, let `(s, x) ↦ Φ(s)(x)` be continuous with `‖Φ(s)(x)‖ ≤ B` on
`[0, 1] × ℝ^P`, and `Ψ(x) = ∫₀¹ Φ(s)(x) ds`.  Then `∫₀¹ ∫ θ ξ(Φ(s)) dμ ds = ∫ θ ξ(Ψ) dμ`: the
integrand is dominated by `B |θ(x)|` for `𝓛¹ ⌞ (0, 1] × μ`-a.e. `(s, x)`, so Fubini applies
(`integral_integral_swap`), and the inner integral is
`θ(x) ∫₀¹ ξ(x)(Φ(s)(x)) ds = θ(x) ξ(x)(Ψ(x))` (`iwl_cr_ci_ie_nvector_intervalIntegral`). -/
theorem Submission.iwl_cr_ci_ie_param_fubini : ∀ (P m : ℕ) (μ : Measure (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) m) (Φ : ℝ → Eucl P → Covector (Eucl P) m) (Ψ : Eucl P → Covector (Eucl P) m) (B : ℝ), SFinite μ → Integrable θ μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖) → Continuous (fun p : ℝ × Eucl P => Φ p.1 p.2) → (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, ‖Φ s x‖ ≤ B) → (∀ (x : Eucl P) (v : Fin m → Eucl P), Ψ x v = ∫ s in (0 : ℝ)..1, Φ s x v) → ∫ s in (0 : ℝ)..1, ∫ x, θ x * ξ x (Φ s x) ∂μ = ∫ x, θ x * ξ x (Ψ x) ∂μ := by
  intro P m μ θ ξ Φ Ψ B hμ hθ hξ hbd hΦ hB hΨ
  -- `ν = 𝓛¹ ⌞ (0, 1]` is finite, and `F(s, x) = θ(x) ξ(x)(Φ(s)(x))` on `ℝ × ℝ^P`.
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have _instν : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  set F : ℝ → Eucl P → ℝ := fun s x => θ x * ξ x (Φ s x) with hF
  -- `F` is a.e. strongly measurable for `ν × μ`: `θ`, `ξ` only depend on `x`, `Φ` is jointly
  -- continuous and the evaluation `(w, α) ↦ w(α)` is continuous.
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (ν.prod μ) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × Eucl P => θ p.2) (ν.prod μ) :=
      hθ.aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × Eucl P => ξ p.2) (ν.prod μ) := hξ.comp_snd
    have h3 : AEStronglyMeasurable (fun p : ℝ × Eucl P => Φ p.1 p.2) (ν.prod μ) :=
      hΦ.aestronglyMeasurable
    exact h1.mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ h2 h3)
  -- `ν × μ`-a.e. `s ∈ (0, 1]` and `|ξ(x)(α)| ≤ ‖α‖`, so `|F(s, x)| ≤ |θ(x)| ‖Φ(s)(x)‖ ≤ B |θ(x)|`.
  have hbound : ∀ᵐ p ∂(ν.prod μ), ‖Function.uncurry F p‖ ≤ B * ‖θ p.2‖ := by
    have hs : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ Ioc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hx : ∀ᵐ p ∂(ν.prod μ), ∀ α : Covector (Eucl P) m, |ξ p.2 α| ≤ ‖α‖ :=
      Measure.quasiMeasurePreserving_snd.ae hbd
    filter_upwards [hs, hx] with p hp1 hp2
    simp only [Function.uncurry, hF, norm_mul, Real.norm_eq_abs]
    calc |θ p.2| * |ξ p.2 (Φ p.1 p.2)| ≤ |θ p.2| * B := by
          gcongr
          exact (hp2 _).trans (hB p.1 (Ioc_subset_Icc_self hp1) p.2)
      _ = B * |θ p.2| := mul_comm _ _
  -- `B |θ|` is `ν × μ`-integrable (`ν` finite), hence so is `F`.
  have hG : Integrable (fun p : ℝ × Eucl P => B * ‖θ p.2‖) (ν.prod μ) :=
    (integrable_const B).mul_prod hθ.norm
  have hint : Integrable (Function.uncurry F) (ν.prod μ) := hG.mono' hmeas hbound
  -- Fubini, with `∫₀¹ = ∫ dν` since `0 ≤ 1`.
  rw [intervalIntegral.integral_of_le zero_le_one]
  change ∫ s, ∫ x, F s x ∂μ ∂ν = _
  rw [integral_integral_swap hint]
  congr 1
  funext x
  -- The inner integral: `∫₀¹ θ(x) ξ(x)(Φ(s)(x)) ds = θ(x) ξ(x)(Ψ(x))`.
  change ∫ s in Ioc (0 : ℝ) 1, θ x * ξ x (Φ s x) = _
  rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul]
  congr 1
  exact Submission.iwl_cr_ci_ie_nvector_intervalIntegral P m 0 1 (fun s => Φ s x) (Ψ x) (ξ x)
    (hΦ.comp (continuous_id.prodMk continuous_const)) (hΨ x)

/-- **Exchange of an integer multiplicity current with `∫₀¹ ds` (Simon Ch. 6, 8.2, cone
construction).**  Let `X = τ(M, θ, ξ)` be integer multiplicity, `(s, x) ↦ φ(s)(x)` continuous with
`spt φ(s) ⊆ K` (`K` compact) for `s ∈ [0, 1]`, and `ψ(x)(v) = ∫₀¹ φ(s)(x)(v) ds`.  Then
`∫₀¹ X(φ(s)) ds = X(ψ)`: `μ_K := Hᵐ⌞(M ∩ K)` is finite (`θ ≥ 1` on `M`), every `φ(s)` and `ψ`
vanish off `K`, so `X(φ(s))` and `X(ψ)` are `μ_K`-integrals, and Fubini applies to
`θ(x) ξ(x)(φ(s)(x))`, dominated by `B |θ(x)|` with `B = sup_{[0,1] × K} ‖φ‖` and `|ξ(x)(α)| ≤ ‖α‖`. -/
theorem Submission.iwl_cr_ci_integral_exchange : ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (K : Set (Eucl P)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m) (ψ : TestFormOn (univ : Set (Eucl P)) m), IsIntegerMultiplicity X → IsCompact K → Continuous (fun p : ℝ × Eucl P => (φ p.1 : DifferentialForm (Eucl P) m) p.2) → (∀ s ∈ Icc (0 : ℝ) 1, tsupport (φ s : DifferentialForm (Eucl P) m) ⊆ K) → (∀ (x : Eucl P) (v : Fin m → Eucl P), (ψ : DifferentialForm (Eucl P) m) x v = ∫ s in (0 : ℝ)..1, (φ s : DifferentialForm (Eucl P) m) x v) → ∫ s in (0 : ℝ)..1, X (φ s) = X ψ := by
  intro P m X K φ ψ hX hK hφc hsupp hψ
  -- `X = τ(M, θ, ξ)` with `θ` integer valued on `M`.
  obtain ⟨M, θ, ξ, hT, hint, hXτ⟩ := hX
  -- `μ_K := Hᵐ⌞(M ∩ K)` is finite; `θ` is `μ_K`-integrable and `ξ` is `μ_K`-measurable.
  have hfin : (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞ :=
    Submission.iwl_cr_ci_ie_measure_inter_compact_lt_top P m univ M θ ξ K hT hint hK
      (subset_univ K)
  have _instK : IsFiniteMeasure ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hθ : Integrable θ ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) :=
    hT.integrableOn K hK (subset_univ K)
  have hξ : AEStronglyMeasurable ξ ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) :=
    hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  -- `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₘ` for an orthonormal `τ`, so `|ξ(x)(α)| ≤ ‖α‖` `μ_K`-a.e.
  have hbd : ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)),
      ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖ := by
    have h : ∀ᵐ x ∂((μHE[m] : Measure (Eucl P)).restrict M),
        ∀ α : Covector (Eucl P) m, |ξ x α| ≤ ‖α‖ :=
      hT.orients.mono fun x ⟨τ, hτ, _, hξx⟩ => Submission.fiw_ims_tt_unit_bound P m τ (ξ x) hτ hξx
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left h
  -- Every `φ(s)`, `s ∈ [0, 1]`, and `ψ` vanish off `K`.
  have hφ0 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∉ K, (φ s : DifferentialForm (Eucl P) m) x = 0 :=
    fun s hs x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp s hs h)
  have hψ0 : ∀ x ∉ K, (ψ : DifferentialForm (Eucl P) m) x = 0 := by
    intro x hx
    ext v
    rw [hψ x v]
    have h : ∫ s in (0 : ℝ)..1, (φ s : DifferentialForm (Eucl P) m) x v
        = ∫ s in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      simp [hφ0 s hs x hx]
    rw [h]
    simp
  -- `‖φ(s)(x)‖ ≤ B` on the compact set `[0, 1] × K`, hence for all `x` when `s ∈ [0, 1]`.
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖(φ s : DifferentialForm (Eucl P) m) x‖ ≤ B := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hφc.continuousOn
    refine ⟨max C 0, fun s hs x => ?_⟩
    by_cases hx : x ∈ K
    · exact (hC (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)
    · rw [hφ0 s hs x hx, norm_zero]
      exact le_max_right _ _
  -- For `ω` vanishing off `K`, `X(ω) = ∫ θ ξ(ω) dμ_K`.
  have hXK : ∀ ω : TestFormOn (univ : Set (Eucl P)) m,
      (∀ x ∉ K, (ω : DifferentialForm (Eucl P) m) x = 0) →
      X ω = ∫ x, θ x * ξ x ((ω : DifferentialForm (Eucl P) m) x)
        ∂((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) := by
    intro ω hω
    rw [hXτ ω, tauAction, ← setIntegral_indicator hK.isClosed.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hω x hx]
  -- Fubini on `[0, 1] × (M ∩ K)`: `∫₀¹ ∫ θ ξ(φ(s)) dμ_K ds = ∫ θ ξ(ψ) dμ_K`.
  have hmain := Submission.iwl_cr_ci_ie_param_fubini P m
    ((μHE[m] : Measure (Eucl P)).restrict (M ∩ K)) θ ξ
    (fun s => (φ s : DifferentialForm (Eucl P) m)) ψ B inferInstance hθ hξ hbd hφc hBd hψ
  rw [hXK ψ hψ0, ← hmain]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  exact hXK (φ s) (hφ0 s hs)
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

/-- The cone `0 ⨯ X` over an integer multiplicity `X` with `spt X ⊆ B̄_R(0)` is integer
multiplicity.  `Z = [[(0,1)]] × X` is integer multiplicity with compact support, so `H_push` gives
its integer multiplicity push-forward `S` by the cone map `h(y) = y₀ • π(y)`.  Testing with
`η = ϑ(y₀) ζ(π y) • h^# ω`, which agrees with `h^# ω` near `spt Z`, the slices of `η` are
`ζ(x) sᵐ ω(s x)(x, ·)`, so `S(ω) = Z(η) = ∫₀¹ X(η_s) ds = X(ζ ψ_ω) = C(ω)` for the radial integral
`ψ_ω(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt`. -/
theorem Submission.iwl_cr_cone_integer_multiplicity :
    ∀ (P m : ℕ),
      (∀ (Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1)) (f : Eucl (P + 1) → Eucl P),
        IsIntegerMultiplicity Z → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
        (∀ K : Set (Eucl P), IsCompact K → IsCompact (f ⁻¹' K ∩ Z.support)) →
        ∃ S : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), IsIntegerMultiplicity S ∧
          ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1))
            (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)),
            (∃ N : Set (Eucl (P + 1)), IsOpen N ∧ Z.support ⊆ N ∧ ∀ y ∈ N,
              (η : DifferentialForm (Eucl (P + 1)) (m + 1)) y =
                ((ω : DifferentialForm (Eucl P) (m + 1)) (f y)).compContinuousLinearMap
                  (fderiv ℝ f y)) →
            S ω = Z η) →
      ∀ (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m)
        (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
        IsIntegerMultiplicity X → X.support ⊆ closedBall 0 R →
        (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m),
          (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P,
            (ψ : DifferentialForm (Eucl P) m) x v =
              ∫ t in (0 : ℝ)..1,
                t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) →
          C ω = X ψ) →
        IsIntegerMultiplicity C := by
  intro P m hpush R X C hX hXR hcone
  -- `Z = [[(0,1)]] × X` is integer multiplicity, `Z(η) = ∫₀¹ X(η_s) ds` for the slices
  -- `η_s = η(Φ(s, ·))(e₀, ι ·)`, and `spt Z` lies in the compact set `L = Φ([0,1] × B̄_R(0))`.
  obtain ⟨Z, hZ, hZη⟩ := Submission.iwl_cr_interval_product_im P m X hX
  obtain ⟨hLc, hZL⟩ := Submission.iwl_cr_ci_product_support P m R X Z hXR hZη
  -- The cone map `h(y) = y₀ • π(y)` is `C^∞` and proper on the closed set `spt Z ⊆ L`, so `Z`
  -- pushes forward to an integer multiplicity `S = τ(M, θ, ξ)`.
  obtain ⟨hh, hhΦ⟩ := Submission.iwl_cr_ci_cone_map P m
  have hZc : IsClosed Z.support := isClosed_univ.sdiff Z.isOpen_zeroRegion
  obtain ⟨S, ⟨M, θ, ξ, hMθξ, hθ, hSτ⟩, hSZ⟩ := hpush Z _ hZ hh fun K hK =>
    hLc.of_isClosed_subset ((hK.isClosed.preimage hh.continuous).inter hZc)
      (inter_subset_right.trans hZL)
  -- It remains to show `C(ω) = S(ω)` for every `ω`.
  refine ⟨M, θ, ξ, hMθξ, hθ, fun ω => ?_⟩
  rw [← hSτ ω]
  -- Cut-offs `ϑ = 1` on `[-1, 2]` and `ζ = 1` on `B̄_r(0)`, where `R < r`.
  obtain ⟨r, hr0, hRr⟩ : ∃ r : ℝ, 0 < r ∧ R < r :=
    ⟨max R 0 + 1, by linarith [le_max_right R 0], by linarith [le_max_left R 0]⟩
  obtain ⟨ϑ, hϑs, hϑc, hϑ1⟩ : ∃ ϑ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϑ ∧
      HasCompactSupport ϑ ∧ ∀ s ∈ Icc (-1 : ℝ) 2, ϑ s = 1 := by
    let b : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 2, by norm_num, by norm_num⟩
    refine ⟨b, b.contDiff, b.hasCompactSupport, fun s hs => b.one_of_mem_closedBall ?_⟩
    show dist s (1 / 2) ≤ 3 / 2
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨ζ, hζs, hζc, hζ1⟩ : ∃ ζ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ ∧
      HasCompactSupport ζ ∧ ∀ x ∈ closedBall (0 : Eucl P) r, ζ x = 1 := by
    let b : ContDiffBump (0 : Eucl P) := ⟨r, r + 1, hr0, by linarith⟩
    exact ⟨b, b.contDiff, b.hasCompactSupport, fun x hx => b.one_of_mem_closedBall hx⟩
  -- The test form `η = χ • h^# ω` on `ℝ^{P+1}`, `χ(y) = ϑ(y₀) ζ(π y)`.
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) (m + 1)) :=
    ω.property.1.1
  obtain ⟨hχs, hχc⟩ := Submission.iwl_cr_ci_product_cutoff P ϑ ζ hϑs hϑc hζs hζc
  obtain ⟨η, hη⟩ :=
    Submission.iwl_cr_ci_cutoff_pullback_testForm (P + 1) P (m + 1) _ _ _ hh hχs hχc hωs
  -- `χ = 1` on the open set `N = {y : y₀ ∈ (-1, 2), π y ∈ B_r(0)} ⊇ L ⊇ spt Z`, so `S(ω) = Z(η)`.
  have hSη : S ω = Z η := by
    refine hSZ ω η ⟨(fun y : Eucl (P + 1) => y 0) ⁻¹' Ioo (-1) 2 ∩
      (fun y : Eucl (P + 1) => (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) ⁻¹' ball 0 r,
      (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop)), ?_, ?_⟩
    · intro _ hy
      obtain ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩ := hZL hy
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show -1 < s
        linarith [hs.1]
      · show s < 2
        linarith [hs.2]
      · show x ∈ ball (0 : Eucl P) r
        exact mem_ball.2 ((mem_closedBall.1 hx).trans_lt hRr)
    · intro y hy
      have hy0 : y 0 ∈ Icc (-1 : ℝ) 2 := ⟨hy.1.1.le, hy.1.2.le⟩
      have hyπ : (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ closedBall (0 : Eucl P) r :=
        ball_subset_closedBall hy.2
      rw [hη y, hϑ1 _ hy0, hζ1 _ hyπ, one_mul, one_smul]
  -- The slices `φ(s)` of `η`: `Z(η) = ∫₀¹ X(φ(s)) ds`, and `φ(s)(x)(v) = ζ(x) sᵐ ω(s x)(x, v)` for
  -- `s ∈ [0, 1]`, because `Dh(Φ(s, x))` maps `e₀ ↦ x` and `ι v ↦ s v`.
  obtain ⟨φ, hφc, hφ⟩ := Submission.iwl_cr_ci_slice_testForm P m η
  have hZφ : Z η = ∫ s in (0 : ℝ)..1, X (φ s) := hZη η φ fun s _ x v => hφ s x v
  have hφv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P),
      (φ s : DifferentialForm (Eucl P) m) x v =
        ζ x * (s ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (s • x) (Fin.cons x v)) := by
    intro s hs x v
    have hΦ0 : ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
        (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x)) : Eucl (P + 1)) 0 = s := rfl
    have hπΦ : (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
          (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))))) = x := rfl
    rw [hφ, hη, ContinuousAlternatingMap.smul_apply, smul_eq_mul, (hhΦ s x).2, hΦ0, hπΦ,
      hϑ1 s ⟨by linarith [hs.1], by linarith [hs.2]⟩, one_mul]
  -- `ψ = ζ ψ_ω` with `ψ_ω(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt` is a test form, and `C(ω) = X(ψ)` by
  -- the cone property, since `ζ = 1` on the open ball `B_r(0) ⊇ B̄_R(0) ⊇ spt X`.
  obtain ⟨ψω, hψωs, hψω, -⟩ :=
    Submission.iwl_cr_radial_operator P m m (ω : DifferentialForm (Eucl P) (m + 1)) hωs
  obtain ⟨ψ, hψ⟩ : ∃ ψ : TestFormOn (univ : Set (Eucl P)) m,
      ∀ x, (ψ : DifferentialForm (Eucl P) m) x = ζ x • ψω x :=
    ⟨⟨fun x => ζ x • ψω x, ⟨⟨hζs.smul hψωs, hζc.smul_right⟩, subset_univ _⟩⟩, fun _ => rfl⟩
  have hCψ : C ω = X ψ := by
    refine hcone ω ψ ⟨ball 0 r, isOpen_ball,
      fun x hx => mem_ball.2 ((mem_closedBall.1 (hXR hx)).trans_lt hRr), fun x hx v => ?_⟩
    rw [hψ, ContinuousAlternatingMap.smul_apply, smul_eq_mul, hζ1 x (ball_subset_closedBall hx),
      one_mul, hψω]
  -- `∫₀¹ X(φ(s)) ds = X(ψ)`: every `φ(s)`, `s ∈ [0, 1]`, is supported in `tsupport ζ`, and
  -- `ψ(x)(v) = ∫₀¹ φ(s)(x)(v) ds`.
  have hXψ : ∫ s in (0 : ℝ)..1, X (φ s) = X ψ := by
    refine Submission.iwl_cr_ci_integral_exchange P m X (tsupport ζ) φ ψ hX hζc hφc
      (fun s hs => closure_mono fun x hx => ?_) fun x v => ?_
    · rw [Function.mem_support] at hx ⊢
      contrapose! hx
      ext v
      rw [hφv s hs x v, hx, zero_mul, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    · rw [hψ, ContinuousAlternatingMap.smul_apply, smul_eq_mul, hψω,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hs
      exact (hφv s hs x v).symm
  rw [hSη, hZφ, hXψ, hCψ]
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

/-- **Simon Ch. 6, Remark 8.3(1) (p. 176).**  Assuming the slicing theorem, Theorem 8.2 on an
open `U ⊆ ℝ^P` follows from its case for currents in `ℝ^P` supported in a fixed compact set.
Near each `ξ₀ ∈ U`: slice the `T_j` by `|x - ξ₀|`; choose (Fatou, Helly) a radius `r` with
integer multiplicity slices of bounded mass along a subsequence on which
`T_j ⌞ B_r(ξ₀) ⇀ T ⌞ B_r(ξ₀)`; extend these integral currents to `ℝ^P` by a cutoff `χ`
(`Z ↦ Z(χ ·)`, continuous by the mass bound), apply the compact case and restrict back to `U`.
Then `T = T ⌞ B_r(ξ₀)` near `ξ₀`, and the local representations patch together
(`iwl_im_patching`).  The auxiliary facts are local steps. -/
theorem Submission.iwl_localization : ∀ (P m : ℕ), SlicingTheorem → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, ((Tj j).mass + (Tj j).boundary.mass)) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → (∀ (U : Set (Eucl P)), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) := by
  /- (F4) A restriction `X ⌞ A` (Simon 2.9) only sees the values of a test form on `A`. -/
  have restr_congr : ∀ {P k : ℕ} {U A : Set (Eucl P)} {X S : GeometricCurrentOn U k},
      IsRestriction X A S → ∀ ω ω' : TestFormOn U k,
      (∀ x ∈ A, (ω : DifferentialForm (Eucl P) k) x = (ω' : DifferentialForm (Eucl P) k) x) →
      S ω = S ω' := by
    intro P k U A X S hS ω ω' h
    obtain ⟨hA, μ, v, -, hSω⟩ := hS
    rw [hSω, hSω]
    refine setIntegral_congr_fun hA ?_
    intro x hx
    exact congrArg (v x) (h x hx)
  /- The Euclidean coefficient norm of a covector is controlled by its operator norm. -/
  have abs_apply_orthonormal_le : ∀ {P k : ℕ} {τ : Fin k → Eucl P}, Orthonormal ℝ τ →
      ∀ (α : Covector (Eucl P) k), |α τ| ≤ ‖α‖ := by
    intro P k τ hτ α
    have h1 := α.le_opNorm τ
    have h2 : ∏ j, ‖τ j‖ = 1 := Finset.prod_eq_one (fun j _ => hτ.1 j)
    rw [h2, mul_one, Real.norm_eq_abs] at h1
    exact h1
  have cEN_small : ∀ {P k : ℕ} (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ α : Covector (Eucl P) k, ‖α‖ < δ → covectorEuclideanNorm α < η := by
    intro P k η hη
    have hN : (0 : ℝ) ≤ (Fintype.card (Fin k → Fin P) : ℝ) := Nat.cast_nonneg _
    have hN1 : (0 : ℝ) < (Fintype.card (Fin k → Fin P) : ℝ) + 1 := by linarith
    refine ⟨η / ((Fintype.card (Fin k → Fin P) : ℝ) + 1), div_pos hη hN1, fun α hα => ?_⟩
    have hcEN : covectorEuclideanNorm α ≤ ((Fintype.card (Fin k → Fin P) : ℝ) + 1) * ‖α‖ := by
      unfold covectorEuclideanNorm
      rw [Real.sqrt_le_left (mul_nonneg hN1.le (norm_nonneg α))]
      refine (Finset.sum_le_card_nsmul _ _ (‖α‖ ^ 2) fun I _ => ?_).trans ?_
      · split_ifs with hI
        · have h := abs_apply_orthonormal_le
            ((EuclideanSpace.basisFun (Fin P) ℝ).orthonormal.comp I hI.injective) α
          exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
        · exact sq_nonneg _
      · rw [Finset.card_univ, nsmul_eq_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    calc covectorEuclideanNorm α ≤ ((Fintype.card (Fin k → Fin P) : ℝ) + 1) * ‖α‖ := hcEN
      _ < ((Fintype.card (Fin k → Fin P) : ℝ) + 1) *
          (η / ((Fintype.card (Fin k → Fin P) : ℝ) + 1)) := mul_lt_mul_of_pos_left hα hN1
      _ = η := mul_div_cancel₀ η hN1.ne'
  /- Step 7: `w ↦ Z(cut w)` is a current on `ℝ^P` when `Z` has finite mass and `cut` does not
  increase pointwise covector norms: test forms converging in `𝒟(ℝ^P)` converge uniformly, and
  `|Z(η)| ≤ M(Z) sup |η|`. -/
  have ext_current : ∀ {P k : ℕ} {U : Set (Eucl P)}
      (cut : TestFormOn (univ : Set (Eucl P)) k →ₗ[ℝ] TestFormOn U k),
      (∀ w x, covectorEuclideanNorm ((cut w : DifferentialForm (Eucl P) k) x) ≤
        covectorEuclideanNorm ((w : DifferentialForm (Eucl P) k) x)) →
      ∀ Z : GeometricCurrentOn U k, Z.massOn U < ∞ →
      ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) k, ∀ w, Y w = Z (cut w) := by
    intro P k U cut hcut Z hZ
    refine ⟨⟨Z.toCurrent ∘ₗ cut, fun ws hws => ?_⟩, fun _ => rfl⟩
    obtain ⟨K', -, -, hsupp, -, hder⟩ := hws
    have hB0 : 0 ≤ (Z.massOn U).toReal := ENNReal.toReal_nonneg
    have hB1 : 0 < (Z.massOn U).toReal + 1 := by linarith
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hη : 0 < ε / ((Z.massOn U).toReal + 1) := div_pos hε hB1
    obtain ⟨δ, hδ, hδη⟩ := cEN_small (P := P) (k := k) _ hη
    obtain ⟨L, hL⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (hder 0) δ hδ)
    refine ⟨L, fun l hl => ?_⟩
    have hsmall : ∀ x, covectorEuclideanNorm ((cut (ws l) : DifferentialForm (Eucl P) k) x) ≤
        ε / ((Z.massOn U).toReal + 1) := by
      intro x
      refine (hcut _ x).trans (hδη _ ?_).le
      by_cases hx : x ∈ K'
      · have h1 := hL l hl x hx
        have h0 : ((0 : TestFormOn (univ : Set (Eucl P)) k) : DifferentialForm (Eucl P) k) =
            0 := rfl
        rw [h0, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
          norm_iteratedFDeriv_zero] at h1
        exact h1
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp l h)), norm_zero]
        exact hδ
    have hle := Submission.cmb_abs_apply_le_of_massOn_le P k U U Z (cut (ws l)) _ _ hB0
      (ENNReal.ofReal_toReal hZ.ne).ge (cut (ws l)).property.2 hsmall
    rw [dist_zero_right, Real.norm_eq_abs]
    calc |(Z.toCurrent ∘ₗ cut) (ws l)| ≤
          (Z.massOn U).toReal * (ε / ((Z.massOn U).toReal + 1)) := hle
      _ < ((Z.massOn U).toReal + 1) * (ε / ((Z.massOn U).toReal + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one _) hη
      _ = ε := mul_div_cancel₀ ε hB1.ne'
  /- Steps 4–5: Fatou and the choice of a good radius. -/
  have h_iwl_loc_good_radius : ∀ (a b : ℝ), a < b → ∀ (g : ℕ → ℝ → ℝ≥0∞) (Λ : ℝ≥0∞)
      (E : Set ℝ) (Q : ℕ → ℝ → Prop), (∀ j, Measurable (g j)) →
      (∀ j, ∫⁻ t in Ioo a b, g j t ≤ Λ) → Λ < ∞ → E.Countable →
      (∀ j, ∀ᵐ t ∂(volume : Measure ℝ), Q j t) → ∃ r ∈ Ioo a b, r ∉ E ∧ (∀ j, Q j r) ∧
      ∃ (C : ℝ≥0∞) (σ : ℕ → ℕ), C < ∞ ∧ StrictMono σ ∧ ∀ j, g (σ j) r ≤ C := by
    intro a b hab g Λ E Q hgm hgint hΛ hE hQ
    set h : ℝ → ℝ≥0∞ := fun t => liminf (fun j => g j t) atTop with hh
    have hhm : Measurable h := Measurable.liminf hgm
    have hfatou : ∫⁻ t in Ioo a b, h t ≤ Λ := by
      calc ∫⁻ t in Ioo a b, h t ≤ liminf (fun j => ∫⁻ t in Ioo a b, g j t) atTop :=
            lintegral_liminf_le hgm
        _ ≤ Λ := liminf_le_of_le (by isBoundedDefault) fun c hc => by
            obtain ⟨j, hj⟩ := hc.exists
            exact hj.trans (hgint j)
    have hfin : ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t < ∞ :=
      ae_lt_top hhm (ne_of_lt (lt_of_le_of_lt hfatou hΛ))
    have hEnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ E := hE.ae_notMem _
    have hQall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j, Q j t := ae_all_iff.2 hQ
    have hall : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
        t ∈ Ioo a b ∧ t ∉ E ∧ (∀ j, Q j t) ∧ h t < ∞ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hEnull,
        ae_restrict_of_ae hQall, hfin] with t h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    have hne : (volume.restrict (Ioo a b)) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo]
      simpa using hab
    have : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.2 hne
    obtain ⟨r, hr1, hr2, hr3, hr4⟩ := hall.exists
    refine ⟨r, hr1, hr2, hr3, h r + 1, ?_⟩
    have hlt : liminf (fun j => g j r) atTop < h r + 1 :=
      ENNReal.lt_add_right hr4.ne one_ne_zero
    have hfreq : ∃ᶠ j in atTop, g j r < h r + 1 :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    obtain ⟨σ, hσ, hσP⟩ := extraction_of_frequently_atTop hfreq
    exact ⟨σ, ENNReal.add_lt_top.2 ⟨hr4, ENNReal.one_lt_top⟩, hσ, fun j => (hσP j).le⟩
  /- Step 7(v), core: a `τ`-current vanishing on test forms supported in an open `O` has an
  `Hᵏ`-null carrier in `O`. -/
  have covector_finiteDimensional : ∀ (P k : ℕ), FiniteDimensional ℝ (Covector (Eucl P) k) := by
    intro P k
    let Φ : Covector (Eucl P) k →ₗ[ℝ] ((Fin k → Fin P) → ℝ) :=
      { toFun := fun α J => α (fun i => EuclideanSpace.single (J i) (1 : ℝ))
        map_add' := by intro α β; ext J; simp
        map_smul' := by intro c α; ext J; simp }
    refine FiniteDimensional.of_injective Φ ?_
    intro α β h
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
    intro v _
    have := congrFun h v
    simpa [Φ] using this
  have wedge_inner_apply_orthonormal : ∀ {P k : ℕ} {τ : Fin k → Eucl P}, Orthonormal ℝ τ →
      wedgeCovectors k (fun i => (innerSL ℝ (τ i) : Eucl P →L[ℝ] ℝ)) τ = 1 := by
    intro P k τ hτ
    rw [wedgeCovectors_apply_det]
    have hM : (Matrix.of fun i j => (innerSL ℝ (τ i) : Eucl P →L[ℝ] ℝ) (τ j)) = 1 := by
      ext i j
      rw [Matrix.of_apply, innerSL_apply_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.1 hτ i j
    rw [hM, Matrix.det_one]
  have h_iwl_loc_tau_carrier_null : ∀ (P k : ℕ) (U O M : Set (Eucl P)) (θ : Eucl P → ℝ)
      (ξ : Eucl P → NVector (Eucl P) k), IsOpen O → O ⊆ U → IsRectifiableTriple U k M θ ξ →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ O →
        tauAction k M θ ξ (ω : DifferentialForm (Eucl P) k) = 0) →
      (μHE[k] : Measure (Eucl P)) (M ∩ O) = 0 := by
    intro P k U O M θ ξ hO hOU hT hvan
    have : FiniteDimensional ℝ (Covector (Eucl P) k) := covector_finiteDimensional P k
    let b := Module.finBasis ℝ (Covector (Eucl P) k)
    have hbound : ∀ i, ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
        |ξ x (b i)| ≤ ‖b i‖ := by
      intro i
      filter_upwards [hT.orients] with x hx
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      have key := abs_apply_orthonormal_le hτ (b i)
      rcases hξ with h | h
      · rw [h, simpleNVector_apply]; exact key
      · rw [h, neg_apply, simpleNVector_apply, abs_neg]; exact key
    have hne : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ξ x ≠ 0 := by
      filter_upwards [hT.orients] with x hx
      obtain ⟨τ, hτ, -, hξ⟩ := hx
      intro h0
      have h1 := wedge_inner_apply_orthonormal hτ
      set α := wedgeCovectors k (fun i => (innerSL ℝ (τ i) : Eucl P →L[ℝ] ℝ)) with hα
      rcases hξ with h | h
      · have h2 : ξ x α = simpleNVector τ α := by rw [h]
        rw [h0, simpleNVector_apply, h1] at h2
        simp at h2
      · have h2 : ξ x α = (-simpleNVector τ) α := by rw [h]
        rw [h0, neg_apply, simpleNVector_apply, h1] at h2
        simp at h2
    have hzero : ∀ i, ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M),
        x ∈ O → θ x * ξ x (b i) = 0 := by
      intro i
      refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (f := fun x => θ x * ξ x (b i)) ?_ ?_
      · rw [locallyIntegrableOn_iff hO.isLocallyClosed]
        intro K hKO hK
        have hθK : Integrable θ (((μHE[k] : Measure (Eucl P)).restrict M).restrict K) := by
          rw [Measure.restrict_restrict hK.measurableSet, inter_comm]
          exact hT.integrableOn K hK (hKO.trans hOU)
        have hc : Continuous (fun L : NVector (Eucl P) k => L (b i)) :=
          (ContinuousLinearMap.apply ℝ ℝ (b i)).continuous
        show Integrable _ _
        refine Integrable.mono' (hθK.norm.mul_const ‖b i‖) ?_ ?_
        · exact hθK.aestronglyMeasurable.mul
            (hc.comp_aestronglyMeasurable hT.aestronglyMeasurable.restrict)
        · filter_upwards [ae_restrict_of_ae (hbound i)] with x hx
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      · intro g hg hgc hgO
        let ω : DifferentialForm (Eucl P) k := fun x => g x • b i
        have hsupp : Function.support ω ⊆ Function.support g := by
          intro x hx
          rw [Function.mem_support] at hx ⊢
          intro hgx
          apply hx
          simp [ω, hgx]
        have hωO : tsupport ω ⊆ O := (closure_mono hsupp).trans hgO
        have hωmem : ω ∈ TestFormOn U k := by
          show (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω ∧ HasCompactSupport ω) ∧ tsupport ω ⊆ U
          exact ⟨⟨hg.smul contDiff_const, hgc.mono hsupp⟩, hωO.trans hOU⟩
        have h := hvan ⟨ω, hωmem⟩ hωO
        have heq : (fun x => g x • (θ x * ξ x (b i))) = fun x => θ x * ξ x (ω x) := by
          funext x
          simp only [ω, map_smul, smul_eq_mul]
          ring
        calc ∫ x, g x • (θ x * ξ x (b i)) ∂((μHE[k] : Measure (Eucl P)).restrict M)
            = ∫ x, θ x * ξ x (ω x) ∂((μHE[k] : Measure (Eucl P)).restrict M) := by rw [heq]
          _ = 0 := h
    have hmem : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), x ∈ M :=
      ae_restrict_mem₀ hT.nullMeasurableSet
    have hnot : ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), x ∉ O := by
      have hall := ae_all_iff.2 hzero
      filter_upwards [hall, hne, hmem] with x hx hxne hxM hxO
      apply hxne
      have hθ : 0 < θ x := hT.pos x hxM
      have hvan' : ∀ i, ξ x (b i) = 0 := fun i => by
        rcases mul_eq_zero.1 (hx i hxO) with h | h
        · exact absurd h hθ.ne'
        · exact h
      have hlin : (ξ x : Covector (Eucl P) k →ₗ[ℝ] ℝ) = 0 :=
        b.ext (fun i => by simpa using hvan' i)
      ext α
      simpa using LinearMap.congr_fun hlin α
    have h0 : ((μHE[k] : Measure (Eucl P)).restrict M) O = 0 :=
      measure_eq_zero_iff_ae_notMem.2 hnot
    rw [Measure.restrict_apply hO.measurableSet] at h0
    rwa [inter_comm]
  /- Step 7: a smooth cutoff `χ`, `0 ≤ χ ≤ 1`, `χ = 1` near `K`, `tsupport χ ⊆ U` compact. -/
  have exists_cutoff : ∀ {P : ℕ} {U K : Set (Eucl P)}, IsOpen U → IsCompact K → K ⊆ U →
      ∃ χ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
        ∃ N : Set (Eucl P), IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, χ x = 1 := by
    intro P U K hU hK hKU
    obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
    obtain ⟨f, hf, hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
      (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
    have htsupp : tsupport f ⊆ cthickening δ K := by
      rw [tsupport, hsupp]
      exact closure_thickening_subset_cthickening δ K
    refine ⟨f, hf, ?_, htsupp.trans hδU, fun x => hrange (mem_range_self x),
      thickening (δ / 2) K, isOpen_thickening, self_subset_thickening (half_pos hδ) K,
      fun x hx => (hone x).1 (thickening_subset_cthickening _ _ hx)⟩
    exact hK.cthickening.of_isClosed_subset (isClosed_tsupport f) htsupp
  have covectorEuclideanNorm_smul_le : ∀ {P n : ℕ} {t : ℝ}, (0 ≤ t ∧ t ≤ 1) →
      ∀ (α : Covector (Eucl P) n), covectorEuclideanNorm (t • α) ≤ covectorEuclideanNorm α := by
    intro P n t ht α
    unfold covectorEuclideanNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro I _
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      have h1 : t ^ 2 ≤ 1 := by nlinarith
      have h2 : 0 ≤ (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 := sq_nonneg _
      nlinarith
    · exact le_refl _
  have cut_mem : ∀ {P j : ℕ} {U : Set (Eucl P)} (χ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ U →
      ∀ (w : TestFormOn (univ : Set (Eucl P)) j),
      (fun x => χ x • (w : DifferentialForm (Eucl P) j) x) ∈ TestFormOn U j := by
    intro P j U χ hχ hχU w
    have hw : IsTestForm (w : DifferentialForm (Eucl P) j) ∧
        tsupport (w : DifferentialForm (Eucl P) j) ⊆ univ := w.property
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hχ.smul hw.1.1
    · refine hw.1.2.mono ?_
      intro x hx
      by_contra h
      apply hx
      simp only
      rw [Function.notMem_support.1 h, smul_zero]
    · exact (tsupport_smul_subset_left _ _).trans hχU
  /- Step 7(v): the cutoff extension `w ↦ Z(χ w)` to `ℝ^P` of an integer multiplicity `Z`
  vanishing on test forms supported off a compact `K` (with `χ = 1` on `K`) is integer
  multiplicity: the carrier of `Z` is `Hᵏ`-null off `K`. -/
  have extension_im : ∀ (P k : ℕ) (U K : Set (Eucl P)) (χ : Eucl P → ℝ), IsOpen U →
      IsCompact K → K ⊆ U → (∀ x ∈ K, χ x = 1) → ∀ (Z : GeometricCurrentOn U k)
      (Y : GeometricCurrentOn (univ : Set (Eucl P)) k)
      (cut : TestFormOn (univ : Set (Eucl P)) k → TestFormOn U k),
      (∀ w x, (cut w : DifferentialForm (Eucl P) k) x =
        χ x • (w : DifferentialForm (Eucl P) k) x) →
      IsIntegerMultiplicity Z →
      (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U \ K → Z ω = 0) →
      (∀ w, Y w = Z (cut w)) → IsIntegerMultiplicity Y := by
    intro P k U K χ hU hK hKU hχK Z Y cut hcut hZ hvan hYZ
    obtain ⟨M, θ, ξ, hT, hθ, hZτ⟩ := hZ
    have hnull : (μHE[k] : Measure (Eucl P)) (M \ K) = 0 := by
      refine measure_mono_null ?_ (h_iwl_loc_tau_carrier_null P k U (U \ K) M θ ξ
        (hU.sdiff hK.isClosed) sdiff_subset hT fun ω hω => (hZτ ω).symm.trans (hvan ω hω))
      intro x hx
      exact ⟨hx.1, hT.subset hx.1, hx.2⟩
    have hsub : M ∩ K ⊆ M := inter_subset_left
    have hMK : NullMeasurableSet (M ∩ K) (μHE[k] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
    have hsd : (μHE[k] : Measure (Eucl P)) (symmDiff M (M ∩ K) ∩ univ) = 0 := by
      refine measure_mono_null (fun x hx => ?_) hnull
      rcases mem_symmDiff.1 hx.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, fun h3 => h2 ⟨h1, h3⟩⟩
      · exact absurd h1.1 h2
    refine ⟨M ∩ K, θ, ξ, ⟨subset_univ _, hMK, hT.countablyRectifiable.mono hsub,
      fun x hx => hT.pos x hx.1, fun K' _ _ => (hT.integrableOn K hK hKU).mono_set
        inter_subset_left,
      hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩,
      fun x hx => hθ x hx.1, fun w => ?_⟩
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hT.orients] with x hx
      obtain ⟨τ, hτ, htan, hξ⟩ := hx
      exact ⟨τ, hτ, Submission.br_weightedTangent_congr P k M (M ∩ K) θ θ x univ isOpen_univ
        (mem_univ x) hsd (Eventually.of_forall fun _ => rfl) rfl _ htan, hξ⟩
    · rw [hYZ, hZτ]
      unfold tauAction
      have hae : M =ᵐ[(μHE[k] : Measure (Eucl P))] (M ∩ K) := by
        refine ae_eq_set.2 ⟨?_, ?_⟩
        · rw [sdiff_self_inter]; exact hnull
        · rw [sdiff_eq_empty.2 hsub]; exact measure_empty
      rw [setIntegral_congr_set hae]
      refine setIntegral_congr_fun₀ hMK ?_
      intro x hx
      show θ x * ξ x ((cut w : DifferentialForm (Eucl P) k) x) =
        θ x * ξ x ((w : DifferentialForm (Eucl P) k) x)
      rw [hcut, hχK x hx.2, one_smul]
  /- Step 9: restricting an integer multiplicity current to an open subdomain. -/
  have restrict_domain_im : ∀ (P k : ℕ) (U V : Set (Eucl P)) (hVU : V ⊆ U), IsOpen V →
      ∀ (Y : GeometricCurrentOn U k) (X : GeometricCurrentOn V k), IsIntegerMultiplicity Y →
      (∀ ω : TestFormOn V k, X ω = Y (testFormOnInclusion hVU k ω)) →
      IsIntegerMultiplicity X := by
    intro P k U V hVU hV Y X hY hXY
    obtain ⟨M, θ, ξ, hT, hθint, hYω⟩ := hY
    have hMV : NullMeasurableSet (M ∩ V) (μHE[k] : Measure (Eucl P)) :=
      hT.nullMeasurableSet.inter hV.measurableSet.nullMeasurableSet
    refine ⟨M ∩ V, θ, ξ, ?_, fun x hx => hθint x hx.1, ?_⟩
    · refine
        { subset := fun x hx => hx.2
          nullMeasurableSet := hMV
          countablyRectifiable := hT.countablyRectifiable.mono inter_subset_left
          pos := fun x hx => hT.pos x hx.1
          integrableOn := fun K hK hKV =>
            (hT.integrableOn K hK (hKV.trans hVU)).mono_set
              (fun x hx => ⟨hx.1.1, hx.2⟩)
          aestronglyMeasurable :=
            hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
          orients := ?_ }
      have hsdV : (μHE[k] : Measure (Eucl P)) (symmDiff M (M ∩ V) ∩ V) = 0 := by
        refine measure_mono_null (fun y hy => ?_) measure_empty
        rcases mem_symmDiff.1 hy.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2 ⟨h1, hy.2⟩
        · exact h2 h1.1
      have h1 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left : M ∩ V ⊆ M) hT.orients
      have h2 := ae_restrict_mem₀ hMV
      filter_upwards [h1, h2] with x hx hxMV
      obtain ⟨τ, hτ, htan, hξ⟩ := hx
      exact ⟨τ, hτ, Submission.br_weightedTangent_congr P k M (M ∩ V) θ θ x V hV hxMV.2 hsdV
        (Eventually.of_forall fun _ => rfl) rfl _ htan, hξ⟩
    · intro ω
      rw [hXY ω, hYω]
      have hsupp : ∀ x, x ∉ V → θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x) = 0 := by
        intro x hx
        have h0 : (ω : DifferentialForm (Eucl P) k) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (ω.property.2 h))
        rw [h0, map_zero, mul_zero]
      show ∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)
          ∂(μHE[k] : Measure (Eucl P)) =
        ∫ x in M ∩ V, θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)
          ∂(μHE[k] : Measure (Eucl P))
      rw [inter_comm M V, ← Measure.restrict_restrict hV.measurableSet,
        setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  /- Steps 1–11: the assembly. -/
  intro P m hSlice hCpt U hU Tj T hTj hbd hconv
  obtain ⟨-, -, hR2⟩ := Submission.iwl_restriction_theory
  obtain ⟨-, hIMb, hIMc⟩ := Submission.iwl_im_closure
  -- local finiteness of the masses of `T_j`, `∂T_j` and `T`
  have hTjfin : ∀ j, ∀ W, CompactlyContainedOpen W U →
      (Tj j).massOn W < ∞ ∧ (Tj j).boundary.massOn W < ∞ := by
    intro j W hW
    have hlt := lt_of_le_of_lt
      (le_iSup (fun j => (Tj j).massOn W + (Tj j).boundary.massOn W) j) (hbd W hW)
    exact ⟨lt_of_le_of_lt le_self_add hlt, lt_of_le_of_lt le_add_self hlt⟩
  have hTfin : ∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ := by
    intro W hW
    refine lt_of_le_of_lt (hconv.massOn_le_liminf W) (lt_of_le_of_lt ?_ (hbd W hW))
    exact (Filter.liminf_le_limsup (u := fun j => (Tj j).massOn W) (f := atTop)).trans
      (limsup_le_iSup.trans (iSup_mono fun j => le_self_add))
  apply Submission.iwl_im_patching P (m + 1) U hU T
  intro ξ₀ hξ₀
  -- Step 1: `r₀`, the distance `d₀ = |· - ξ₀|` and `W₀ = B_{2r₀}(ξ₀) ⊂⊂ U`
  obtain ⟨ε, hε, hballU⟩ := Metric.isOpen_iff.mp hU ξ₀ hξ₀
  obtain ⟨r₀, hr₀pos, hr₀ε⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ 2 * r₀ < ε :=
    ⟨ε / 3, by positivity, by linarith⟩
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : Eucl P → ℝ, ∀ x, d₀ x = dist x ξ₀ :=
    ⟨fun x => dist x ξ₀, fun _ => rfl⟩
  have h2r₀ : (2 * r₀) ≠ 0 := by positivity
  have hcW₀U : closedBall ξ₀ (2 * r₀) ⊆ U := (closedBall_subset_ball hr₀ε).trans hballU
  have hW₀U : ball ξ₀ (2 * r₀) ⊆ U := ball_subset_closedBall.trans hcW₀U
  have hW₀cc : CompactlyContainedOpen (ball ξ₀ (2 * r₀)) U := by
    refine ⟨isOpen_ball, ?_, ?_⟩
    · rw [closure_ball _ h2r₀]; exact isCompact_closedBall _ _
    · rw [closure_ball _ h2r₀]; exact hcW₀U
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ≥0∞, Λ₀ = ⨆ j, ((Tj j).massOn (ball ξ₀ (2 * r₀)) +
      (Tj j).boundary.massOn (ball ξ₀ (2 * r₀))) := ⟨_, rfl⟩
  have hΛ₀fin : Λ₀ < ∞ := by rw [hΛ₀]; exact hbd _ hW₀cc
  have hΛ₀le : ∀ j, (Tj j).massOn (ball ξ₀ (2 * r₀)) +
      (Tj j).boundary.massOn (ball ξ₀ (2 * r₀)) ≤ Λ₀ := fun j => by
    rw [hΛ₀]
    exact le_iSup (fun j => (Tj j).massOn (ball ξ₀ (2 * r₀)) +
      (Tj j).boundary.massOn (ball ξ₀ (2 * r₀))) j
  have hd₀lip : LipschitzWith 1 d₀ := by
    rw [show d₀ = fun x => dist x ξ₀ from funext hd₀]
    exact LipschitzWith.dist_left ξ₀
  have hd₀cont : Continuous d₀ := hd₀lip.continuous
  have hfderiv : ∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ U → ‖fderiv ℝ d₀ x‖₊ ≤ (1 : ℝ≥0) :=
    Eventually.of_forall fun x _ => by
      have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hd₀lip
      rw [← NNReal.coe_le_coe]; simpa using this
  -- Step 2: slices of every `T_j` by `d₀`; mass measures and restrictions (Simon 2.7–2.9)
  choose S hSslice hSsupp hSim hSmass using
    fun j => hSlice P m U hU (Tj j) (hTjfin j) d₀ 1 hd₀lip.lipschitzOnWith
  choose μ hμmass hμex hμid using
    fun j => hR2 P (m + 1) U hU (Tj j) (fun W hW => (hTjfin j W hW).1)
  choose μ' hμ'mass hμ'ex hμ'id using
    fun j => hR2 P m U hU (Tj j).boundary (fun W hW => (hTjfin j W hW).2)
  have hmeasLt : ∀ s : ℝ, MeasurableSet {x | x ∈ U ∧ d₀ x < s} := fun s =>
    hU.measurableSet.inter (measurableSet_lt hd₀cont.measurable measurable_const)
  -- the slice mass bound on `(r₀/2, r₀)` with `W := U`, `L_W := 1`
  have hg : ∀ j, ∃ g : ℝ → ℝ≥0∞, Measurable g ∧
      (∀ t ∈ Ioo (r₀ / 2) r₀, (S j t).massOn U ≤ g t) ∧
      ∫⁻ t in Ioo (r₀ / 2) r₀, g t ≤ Λ₀ := by
    intro j
    have hmeasA : MeasurableSet {x | x ∈ U ∧ r₀ / 2 < d₀ x ∧ d₀ x < r₀} :=
      hU.measurableSet.inter ((measurableSet_lt measurable_const hd₀cont.measurable).inter
        (measurableSet_lt hd₀cont.measurable measurable_const))
    obtain ⟨R, hR⟩ := hμex j _ hmeasA
    obtain ⟨g, hgm, hgle, hgint⟩ :=
      hSmass j U hU subset_rfl 1 hfderiv (r₀ / 2) r₀ (half_lt_self hr₀pos) R hR
    refine ⟨g, hgm, hgle, hgint.trans ?_⟩
    rw [hμid j _ R hR U hU subset_rfl, ENNReal.coe_one, one_mul]
    calc μ j (U ∩ {x | x ∈ U ∧ r₀ / 2 < d₀ x ∧ d₀ x < r₀})
        ≤ μ j (ball ξ₀ (2 * r₀)) := by
          refine measure_mono fun x hx => ?_
          have h1 : d₀ x < r₀ := hx.2.2.2
          rw [hd₀] at h1
          exact h1.trans (lt_two_mul_self hr₀pos)
      _ = (Tj j).massOn (ball ξ₀ (2 * r₀)) := (hμmass j).2 _ hW₀cc
      _ ≤ Λ₀ := le_self_add.trans (hΛ₀le j)
  choose g hgm hgle hgint using hg
  -- Step 3: Helly selection for the restrictions to the balls `{d₀ < s}`
  have hsupW₀ : (⨆ j, (Tj j).massOn (ball ξ₀ (2 * r₀))) < ∞ :=
    lt_of_le_of_lt (iSup_le fun j => le_self_add.trans (hΛ₀le j)) hΛ₀fin
  obtain ⟨ψ, E, hψ, hEc, hRWLprop⟩ :=
    Submission.iwl_restriction_weak_limit P (m + 1) U hU Tj T (ball ξ₀ (2 * r₀)) d₀ hconv
      isOpen_ball hW₀U hsupW₀ hd₀cont.continuousOn
  -- Steps 4–5: Fatou and the choice of a good radius `r`
  obtain ⟨r, hrI, hrE, hrIM, C, σ, hCfin, hσ, hgC⟩ :=
    h_iwl_loc_good_radius (r₀ / 2) r₀ (half_lt_self hr₀pos) (fun j => g (ψ j)) Λ₀ E
      (fun j t => IsIntegerMultiplicity (S (ψ j) t)) (fun j => hgm (ψ j))
      (fun j => hgint (ψ j)) hΛ₀fin hEc (fun j => hSim (ψ j) (hTj (ψ j)).1)
  -- Step 6: `A_j = T_{ψσ(j)} ⌞ B_r(ξ₀)` (i.e. `R' (σ j)`) and `A = T ⌞ B_r(ξ₀)`
  choose R' B' hR' hB' hSAB using fun j => hSslice (ψ j) r
  obtain ⟨μT, hμTmass, hμTex, hμTid⟩ := hR2 P (m + 1) U hU T hTfin
  obtain ⟨A, hA⟩ := hμTex {x | x ∈ U ∧ d₀ x < r} (hmeasLt r)
  have hK₀c : IsCompact (closedBall ξ₀ r) := isCompact_closedBall ξ₀ r
  have hK₀W₀ : closedBall ξ₀ r ⊆ ball ξ₀ (2 * r₀) :=
    closedBall_subset_ball (hrI.2.trans (lt_two_mul_self hr₀pos))
  have hK₀U : closedBall ξ₀ r ⊆ U := hK₀W₀.trans hW₀U
  have hBrK₀ : {x | x ∈ U ∧ d₀ x < r} ⊆ closedBall ξ₀ r := fun x hx => by
    have h1 : d₀ x < r := hx.2
    rw [hd₀] at h1
    exact h1.le
  have hlevel : {x | x ∈ U ∧ d₀ x ≤ r} ⊆ closedBall ξ₀ r := fun x hx => by
    have h1 : d₀ x ≤ r := hx.2
    rw [hd₀] at h1
    exact h1
  have hR'conv : WeaklyConvergesOn R' A :=
    (hRWLprop r hrE R' A hR' hA).2 _ hK₀c hK₀W₀ hlevel
  -- (a) integrality of `A_j` and `∂A_j = S_j + B_j`
  have hAjim : ∀ j, IsIntegerMultiplicity (R' (σ j)) := fun j =>
    hIMb P (m + 1) U hU _ _ _ (hTj (ψ (σ j))).1 (hR' (σ j))
  have hBjim : ∀ j, IsIntegerMultiplicity (B' (σ j)) := fun j =>
    hIMb P m U hU _ _ _ (hTj (ψ (σ j))).2 (hB' (σ j))
  have hAjbim : ∀ j, IsIntegerMultiplicity (R' (σ j)).boundary := fun j =>
    hIMc P m U hU (S (ψ (σ j)) r) (B' (σ j)) (R' (σ j)).boundary 1 1 (hrIM (σ j)) (hBjim j)
      (fun ω => by rw [hSAB (σ j) ω, Int.cast_one, one_mul, one_mul, sub_add_cancel])
  -- (c) mass bounds
  have hball_sub : U ∩ {x | x ∈ U ∧ d₀ x < r} ⊆ ball ξ₀ (2 * r₀) := fun x hx =>
    hK₀W₀ (hBrK₀ hx.2)
  have hAjmass : ∀ j, (R' (σ j)).mass ≤ Λ₀ := fun j => by
    calc (R' (σ j)).mass = μ (ψ (σ j)) (U ∩ {x | x ∈ U ∧ d₀ x < r}) :=
          hμid (ψ (σ j)) _ _ (hR' (σ j)) U hU subset_rfl
      _ ≤ μ (ψ (σ j)) (ball ξ₀ (2 * r₀)) := measure_mono hball_sub
      _ = (Tj (ψ (σ j))).massOn (ball ξ₀ (2 * r₀)) := (hμmass (ψ (σ j))).2 _ hW₀cc
      _ ≤ Λ₀ := le_self_add.trans (hΛ₀le _)
  have hBjmass : ∀ j, (B' (σ j)).mass ≤ Λ₀ := fun j => by
    calc (B' (σ j)).mass = μ' (ψ (σ j)) (U ∩ {x | x ∈ U ∧ d₀ x < r}) :=
          hμ'id (ψ (σ j)) _ _ (hB' (σ j)) U hU subset_rfl
      _ ≤ μ' (ψ (σ j)) (ball ξ₀ (2 * r₀)) := measure_mono hball_sub
      _ = (Tj (ψ (σ j))).boundary.massOn (ball ξ₀ (2 * r₀)) := (hμ'mass (ψ (σ j))).2 _ hW₀cc
      _ ≤ Λ₀ := le_add_self.trans (hΛ₀le _)
  have hAjbmass : ∀ j, (R' (σ j)).boundary.mass ≤ C + Λ₀ := fun j => by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have heq : (R' (σ j)).boundary ω = S (ψ (σ j)) r ω + B' (σ j) ω := by
      rw [hSAB (σ j) ω, sub_add_cancel]
    show ENNReal.ofReal ((R' (σ j)).boundary ω) ≤ C + Λ₀
    rw [heq]
    exact (ENNReal.ofReal_add_le).trans (add_le_add
      (((S (ψ (σ j)) r).le_massOn hω).trans ((hgle (ψ (σ j)) r hrI).trans (hgC j)))
      (((B' (σ j)).le_massOn hω).trans (hBjmass j)))
  have hAmass : A.massOn U < ∞ := by
    calc A.massOn U = μT (U ∩ {x | x ∈ U ∧ d₀ x < r}) := hμTid _ _ hA U hU subset_rfl
      _ ≤ μT (ball ξ₀ (2 * r₀)) := measure_mono hball_sub
      _ = T.massOn (ball ξ₀ (2 * r₀)) := hμTmass.2 _ hW₀cc
      _ < ∞ := hTfin _ hW₀cc
  -- Step 7: a cutoff `χ = 1` near `K₀ = B̄_r(ξ₀)` and the extensions `Z ↦ Z(χ ·)` to `ℝ^P`
  obtain ⟨χ, hχ, -, hχU, hχ01, N, hN, hK₀N, hχN⟩ := exists_cutoff hU hK₀c hK₀U
  obtain ⟨cutMul, hcoe⟩ : ∃ cutMul : ∀ j : ℕ,
      TestFormOn (univ : Set (Eucl P)) j →ₗ[ℝ] TestFormOn U j,
      ∀ (j : ℕ) (w : TestFormOn (univ : Set (Eucl P)) j),
        ((cutMul j w : TestFormOn U j) : DifferentialForm (Eucl P) j) =
          fun x => χ x • (w : DifferentialForm (Eucl P) j) x :=
    ⟨fun j =>
      { toFun := fun w => ⟨fun x => χ x • (w : DifferentialForm (Eucl P) j) x,
          cut_mem χ hχ hχU w⟩
        map_add' := fun w η => Subtype.ext (funext fun x => smul_add (χ x) _ _)
        map_smul' := fun c w => Subtype.ext (funext fun x => smul_comm (χ x) c _) },
      fun _ _ => rfl⟩
  have hcutle : ∀ (j : ℕ) (w : TestFormOn (univ : Set (Eucl P)) j) (x : Eucl P),
      covectorEuclideanNorm ((cutMul j w : DifferentialForm (Eucl P) j) x) ≤
        covectorEuclideanNorm ((w : DifferentialForm (Eucl P) j) x) := fun j w x => by
    rw [hcoe]; exact covectorEuclideanNorm_smul_le (hχ01 x) _
  have hcutAd : ∀ {j : ℕ} {W : Set (Eucl P)} (w : TestFormOn (univ : Set (Eucl P)) j),
      w ∈ massAdmissibleOn univ j W → cutMul j w ∈ massAdmissibleOn U j U := fun w hw =>
    ⟨(cutMul _ w).property.2, fun x => (hcutle _ w x).trans (hw.2 x)⟩
  have hK₀1 : ∀ x ∈ closedBall ξ₀ r, χ x = 1 := fun x hx => hχN x (hK₀N hx)
  -- `χ dw = d(χ w) = dw` on `N ⊇ K₀`
  have hcutd : ∀ (w : TestFormOn (univ : Set (Eucl P)) m) (x : Eucl P), x ∈ N →
      ((cutMul (m + 1) (exteriorDerivativeTestOn univ m w) : TestFormOn U (m + 1)) :
        DifferentialForm (Eucl P) (m + 1)) x =
      ((exteriorDerivativeTestOn U m (cutMul m w) : TestFormOn U (m + 1)) :
        DifferentialForm (Eucl P) (m + 1)) x := by
    intro w x hx
    have hev : (fun y => χ y • (w : DifferentialForm (Eucl P) m) y) =ᶠ[𝓝 x]
        (w : DifferentialForm (Eucl P) m) := by
      filter_upwards [hN.mem_nhds hx] with y hy
      rw [hχN y hy, one_smul]
    rw [hcoe]
    show χ x • extDeriv (w : DifferentialForm (Eucl P) m) x =
      extDeriv ((cutMul m w : TestFormOn U m) : DifferentialForm (Eucl P) m) x
    rw [hcoe, hev.extDeriv_eq, hχN x hx, one_smul]
  choose Xj hXj using fun j => ext_current (cutMul (m + 1)) (hcutle (m + 1)) (R' (σ j))
    ((hAjmass j).trans_lt hΛ₀fin)
  obtain ⟨Ã, hÃ⟩ := ext_current (cutMul (m + 1)) (hcutle (m + 1)) A hAmass
  have hXjb : ∀ j (w : TestFormOn (univ : Set (Eucl P)) m),
      (Xj j).boundary w = (R' (σ j)).boundary (cutMul m w) := fun j w => by
    rw [GeometricCurrentOn.boundary_apply, hXj, GeometricCurrentOn.boundary_apply]
    exact restr_congr (hR' (σ j)) _ _ fun x hx => hcutd w x (hK₀N (hBrK₀ hx))
  -- `A_j` and `∂A_j` vanish on test forms supported off `K₀`
  have hAjvan : ∀ j (ω : TestFormOn U (m + 1)),
      tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ U \ closedBall ξ₀ r →
      R' (σ j) ω = 0 := fun j ω hω =>
    (restr_congr (hR' (σ j)) ω 0 fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => (hω h).2 (hBrK₀ hx)).trans (map_zero _)
  have hAjbvan : ∀ j (ω : TestFormOn U m),
      tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U \ closedBall ξ₀ r →
      (R' (σ j)).boundary ω = 0 := fun j ω hω => by
    rw [GeometricCurrentOn.boundary_apply]
    exact (restr_congr (hR' (σ j)) _ 0 fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      (hω (tsupport_exteriorDerivative_subset _ h)).2 (hBrK₀ hx)).trans (map_zero _)
  -- supports, masses, integrality and convergence of the extensions `X_j`
  have hsuppK₀ : ∀ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
      (∀ w : TestFormOn (univ : Set (Eucl P)) (m + 1),
        (∀ x ∈ closedBall ξ₀ r, (w : DifferentialForm (Eucl P) (m + 1)) x = 0) → Y w = 0) →
      Y.support ⊆ closedBall ξ₀ r := by
    intro Y hY x hx
    by_contra hxK
    obtain ⟨ε', hε', hball'⟩ := Metric.isOpen_iff.1 isClosed_closedBall.isOpen_compl x hxK
    apply hx.2
    refine Set.mem_sUnion.2 ⟨ball x (ε' / 2), ⟨isOpen_ball, ?_, subset_univ _, fun w hw => ?_⟩,
      mem_ball_self (half_pos hε')⟩
    · rw [closure_ball x (half_pos hε').ne']
      exact isCompact_closedBall x _
    · refine hY w fun y hy => image_eq_zero_of_notMem_tsupport fun h => ?_
      exact hball' (ball_subset_ball (half_le_self hε'.le) (hw h)) hy
  have hXsupp : ∀ j, (Xj j).support ⊆ closedBall ξ₀ r := fun j =>
    hsuppK₀ (Xj j) fun w hw => (hXj j w).trans ((restr_congr (hR' (σ j)) _ 0 fun x hx => by
      rw [hcoe]
      show χ x • (w : DifferentialForm (Eucl P) (m + 1)) x = 0
      rw [hw x (hBrK₀ hx), smul_zero]).trans (map_zero _))
  have hXmass : ∀ j, (Xj j).mass ≤ Λ₀ := fun j => by
    refine (sSup_le ?_).trans (hAjmass j)
    rintro _ ⟨w, hw, rfl⟩
    show ENNReal.ofReal (Xj j w) ≤ (R' (σ j)).massOn U
    rw [hXj]
    exact (R' (σ j)).le_massOn (hcutAd w hw)
  have hXbmass : ∀ j, (Xj j).boundary.mass ≤ C + Λ₀ := fun j => by
    refine (sSup_le ?_).trans (hAjbmass j)
    rintro _ ⟨w, hw, rfl⟩
    show ENNReal.ofReal ((Xj j).boundary w) ≤ (R' (σ j)).boundary.massOn U
    rw [hXjb]
    exact (R' (σ j)).boundary.le_massOn (hcutAd w hw)
  have hXint : ∀ j, IsIntegralCurrent (Xj j) := fun j =>
    ⟨extension_im P (m + 1) U _ χ hU hK₀c hK₀U hK₀1 (R' (σ j)) (Xj j) (cutMul (m + 1))
        (fun w x => congrFun (hcoe _ w) x) (hAjim j) (hAjvan j) (hXj j),
      extension_im P m U _ χ hU hK₀c hK₀U hK₀1 (R' (σ j)).boundary (Xj j).boundary (cutMul m)
        (fun w x => congrFun (hcoe _ w) x) (hAjbim j) (hAjbvan j) (hXjb j)⟩
  have hXbd : (⨆ j, ((Xj j).mass + (Xj j).boundary.mass)) < ∞ :=
    lt_of_le_of_lt (iSup_le fun j => add_le_add (hXmass j) (hXbmass j))
      (ENNReal.add_lt_top.2 ⟨hΛ₀fin, ENNReal.add_lt_top.2 ⟨hCfin, hΛ₀fin⟩⟩)
  have hXconv : WeaklyConvergesOn Xj Ã := fun w => by
    rw [hÃ]
    exact ((hR'conv (cutMul (m + 1) w)).comp hσ.tendsto_atTop).congr fun j => (hXj j w).symm
  -- Step 8: the compact case
  have hÃim : IsIntegerMultiplicity Ã :=
    hCpt (closedBall ξ₀ r) hK₀c Xj Ã hXint hXsupp hXbd hXconv
  -- Step 9: back to `U`
  have hAim : IsIntegerMultiplicity A :=
    restrict_domain_im P (m + 1) univ U (subset_univ U) hU Ã A hÃim fun ω => by
      rw [hÃ]
      refine restr_congr hA _ _ fun x hx => ?_
      rw [hcoe]
      show _ = χ x • (ω : DifferentialForm (Eucl P) (m + 1)) x
      rw [hK₀1 x (hBrK₀ hx), one_smul]
  -- Steps 10–11: `T = A` on test forms supported in `B_r(ξ₀)`, then patching
  refine ⟨ball ξ₀ r, isOpen_ball, mem_ball_self ((half_pos hr₀pos).trans hrI.1),
    ball_subset_closedBall.trans hK₀U, A, hAim, fun ω hω => ?_⟩
  obtain ⟨-, μ₁, v₁, hrep, hAω⟩ := hA
  rw [hAω, (hrep ω).2]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  have hxω : x ∉ tsupport (ω : DifferentialForm (Eucl P) (m + 1)) := fun hxt =>
    hx ⟨hK₀U (ball_subset_closedBall (hω hxt)), (hd₀ x).trans_lt (hω hxt)⟩
  rw [image_eq_zero_of_notMem_tsupport hxω, map_zero]
/-- **Reduction to cycles** in the proof of Simon Ch. 6, Theorem 8.2 (p. 176, the paragraph
before (2)): the general case follows from the case `∂T = 0`.  Let `T_j ⇀ T` with `T_j, ∂T_j`
integer multiplicity, `spt T_j ⊆ K` compact and `Λ = sup_j (M(T_j) + M(∂T_j)) < ∞`.  By the
boundary hypothesis (BLI), `∂T` is integer multiplicity.  All supports lie in a ball
`B̄_R(0) ⊇ K`, and the cones `C_j = 0 ⨯ ∂T_j`, `C = 0 ⨯ ∂T` are integer multiplicity with
`∂C_j = ∂T_j`, `spt C_j ⊆ B̄_R(0)`, `M(C_j) ≤ cR M(∂T_j)` and `C_j ⇀ C`.  Hence the
`T'_j = T_j - C_j` are integer multiplicity cycles in `B̄_R(0)` with `M(T'_j) ≤ (1 + cR) Λ` and
`T'_j ⇀ T' = T - C`, so `T'` is integer multiplicity by the cycle hypothesis (Cyc), and so is
`T = T' + C`. -/
theorem Submission.iwl_cycle_reduction : ∀ (P m : ℕ), LipschitzPushforwardIntegerMultiplicity → (∀ (Yj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Yj j).boundary) → (⨆ j, (Yj j).boundary.mass) < ∞ → WeaklyConvergesOn (fun j => (Yj j).boundary) Y.boundary → IsIntegerMultiplicity Y.boundary) → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ j, (Tj j).boundary = 0) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, (Tj j).mass) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, ((Tj j).mass + (Tj j).boundary.mass)) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) := by
  -- The cone lemmas (children) and the siblings `iwl_im_closure`, `iwl_smooth_pushforward`.
  have hsupp_lem := Submission.iwl_cr_support_lemmas
  have hcone_ex := Submission.iwl_cr_cone_exists
  have hcone_est := Submission.iwl_cr_cone_estimates
  have hcone_bd := Submission.iwl_cr_cone_boundary
  have hcone_im := Submission.iwl_cr_cone_integer_multiplicity
  have him := Submission.iwl_im_closure
  have hpush := Submission.iwl_smooth_pushforward
  intro P m hLip hBLI hCyc K hK Tj T hInt hsupp hmass hconv
  set Λ := ⨆ j, ((Tj j).mass + (Tj j).boundary.mass)
  have hTjΛ : ∀ j, (Tj j).mass ≤ Λ := fun j =>
    le_self_add.trans (le_iSup (fun j => (Tj j).mass + (Tj j).boundary.mass) j)
  have hTjbΛ : ∀ j, (Tj j).boundary.mass ≤ Λ := fun j =>
    le_add_self.trans (le_iSup (fun j => (Tj j).mass + (Tj j).boundary.mass) j)
  -- Step 6: `∂T_j ⇀ ∂T`, every `∂T_j` is integer multiplicity and `sup_j M(∂T_j) ≤ Λ < ∞`,
  -- so (BLI) with `Y_j := T_j`, `Y := T` makes `∂T` integer multiplicity.
  have hbconv : WeaklyConvergesOn (fun j => (Tj j).boundary) T.boundary := hconv.boundary
  have hTb : IsIntegerMultiplicity T.boundary :=
    hBLI Tj T (fun j => (hInt j).2) ((iSup_le hTjbΛ).trans_lt hmass) hbconv
  -- Step 7: all supports lie in one closed ball `B̄_R(0) ⊇ K`.
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : Eucl P)).1 hK.isBounded
  obtain ⟨R, hR0, hKR⟩ : ∃ R : ℝ, 0 ≤ R ∧ K ⊆ closedBall (0 : Eucl P) R :=
    ⟨max r 0, le_max_right r 0, hr.trans (closedBall_subset_closedBall (le_max_left r 0))⟩
  have hTjR : ∀ j, (Tj j).support ⊆ closedBall (0 : Eucl P) R := fun j => (hsupp j).trans hKR
  have hTjbR : ∀ j, (Tj j).boundary.support ⊆ closedBall (0 : Eucl P) R := fun j =>
    (hsupp_lem.1 P m univ (Tj j)).trans (hTjR j)
  have hTR : T.support ⊆ closedBall (0 : Eucl P) R :=
    hsupp_lem.2.1 P (m + 1) univ isOpen_univ (closedBall 0 R) Tj T isClosed_closedBall hTjR hconv
  have hTbR : T.boundary.support ⊆ closedBall (0 : Eucl P) R :=
    (hsupp_lem.1 P m univ T).trans hTR
  -- Step 8: the cones `C_j := 0 ⨯ ∂T_j` and `C := 0 ⨯ ∂T`.
  choose Cj hCj using fun j => hcone_ex P m R (Tj j).boundary (hTjbR j)
  obtain ⟨C, hC⟩ := hcone_ex P m R T.boundary hTbR
  -- Cones over integer multiplicity currents are integer multiplicity; the push-forward by
  -- `h(t, x) = t x` they need is the sibling `iwl_smooth_pushforward` on `U = ℝ^{P+1}`, `V = ℝ^P`.
  have hconeIM := hcone_im P m fun Z f hZ hf hprop => by
    obtain ⟨S, hS, hSZ, -⟩ := hpush hLip (P + 1) P m univ univ isOpen_univ isOpen_univ Z f hZ hf
      (mapsTo_univ f univ) fun K' hK' _ => hprop K' hK'
    exact ⟨S, hS, hSZ⟩
  have hCjIM : ∀ j, IsIntegerMultiplicity (Cj j) := fun j =>
    hconeIM R (Tj j).boundary (Cj j) (hInt j).2 (hTjbR j) (hCj j)
  have hCIM : IsIntegerMultiplicity C := hconeIM R T.boundary C hTb hTbR hC
  -- `∂C_j = ∂T_j`.
  have hCjbd : ∀ j, (Cj j).boundary = (Tj j).boundary := fun j =>
    hcone_bd P m R (Tj j) (Cj j) (hTjR j) (hCj j)
  -- Supports in `B̄_R(0)`, `M(C_j) ≤ cR · M(∂T_j)` and `C_j ⇀ C`.
  obtain ⟨c, -, hcR⟩ := hcone_est P m
  obtain ⟨hcone1, hconeseq⟩ := hcR R hR0
  have hCjR : ∀ j, (Cj j).support ⊆ closedBall (0 : Eucl P) R := fun j =>
    (hcone1 _ _ (hTjbR j) (hCj j)).1
  have hCjmass : ∀ j, (Cj j).mass ≤ ENNReal.ofReal (c * R) * (Tj j).boundary.mass := fun j =>
    (hcone1 _ _ (hTjbR j) (hCj j)).2 ((hTjbΛ j).trans_lt hmass)
  have hCconv : WeaklyConvergesOn Cj C :=
    hconeseq (fun j => (Tj j).boundary) T.boundary Cj C hTjbR hTbR hCj hC hbconv
  -- Step 9: the cycles `T'_j := T_j - C_j` and `T' := T - C`.  Differences of currents are
  -- currents (`T(ω_l) → 0` and `C(ω_l) → 0` whenever `ω_l → 0`).
  have hsub : ∀ A B : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
      ∃ D : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
        ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), D ω = A ω - B ω := fun A B =>
    ⟨⟨A.toCurrent - B.toCurrent, fun ωs hωs => by
      simpa only [LinearMap.sub_apply, sub_zero] using
        (A.continuous' ωs hωs).sub (B.continuous' ωs hωs)⟩, fun ω => rfl⟩
  -- `M(A - B) ≤ M(A) + M(B)`, since `-ω` is mass-admissible together with `ω`.
  have hmass_sub : ∀ A B D : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
      (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), D ω = A ω - B ω) →
        D.mass ≤ A.mass + B.mass := by
    intro A B D hD
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have hneg : -ω ∈ massAdmissibleOn (univ : Set (Eucl P)) (m + 1) univ :=
      ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
    have hBneg : B (-ω) = -B ω := B.toCurrent.map_neg ω
    calc ENNReal.ofReal (D ω) = ENNReal.ofReal (A ω + B (-ω)) := by
          rw [hD, hBneg, sub_eq_add_neg]
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.mass + B.mass := add_le_add (A.le_massOn hω) (B.le_massOn hneg)
  choose Tj' hTj' using fun j => hsub (Tj j) (Cj j)
  obtain ⟨T', hT'⟩ := hsub T C
  have hTj'IM : ∀ j, IsIntegerMultiplicity (Tj' j) := fun j =>
    him.2.2 P (m + 1) univ isOpen_univ (Tj j) (Cj j) (Tj' j) 1 (-1) (hInt j).1 (hCjIM j)
      fun ω => by rw [hTj' j ω]; push_cast; ring
  have hTj'bd : ∀ j, (Tj' j).boundary = 0 := by
    intro j
    ext ω
    have h : (Cj j).boundary ω = (Tj j).boundary ω := by rw [hCjbd j]
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply] at h
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply, hTj' j, h, sub_self]
  have hTj'R : ∀ j, (Tj' j).support ⊆ closedBall (0 : Eucl P) R := fun j =>
    (hsupp_lem.2.2 P (m + 1) univ isOpen_univ (Tj j) (Cj j) (Tj' j) 1 (-1)
      fun ω => by rw [hTj' j ω]; ring).trans (union_subset (hTjR j) (hCjR j))
  have hTj'mass : (⨆ j, (Tj' j).mass) < ∞ := by
    have hbound : ∀ j, (Tj' j).mass ≤ Λ + ENNReal.ofReal (c * R) * Λ := fun j =>
      (hmass_sub _ _ _ (hTj' j)).trans
        (add_le_add (hTjΛ j) ((hCjmass j).trans (mul_le_mul_right (hTjbΛ j) _)))
    exact (iSup_le hbound).trans_lt
      (ENNReal.add_lt_top.2 ⟨hmass, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass⟩)
  have hTj'conv : WeaklyConvergesOn Tj' T' := fun ω => by
    have h := (hconv ω).sub (hCconv ω)
    rw [← hT' ω] at h
    exact h.congr fun j => (hTj' j ω).symm
  -- Step 10: (Cyc) on the compact ball `B̄_R(0)` makes `T'` integer multiplicity.
  have hT'IM : IsIntegerMultiplicity T' :=
    hCyc (closedBall 0 R) (isCompact_closedBall 0 R) Tj' T' hTj'IM hTj'bd hTj'R hTj'mass hTj'conv
  -- Step 11: `T = T' + C` with `T'` and `C` integer multiplicity.
  exact him.2.2 P (m + 1) univ isOpen_univ T' C T 1 1 hT'IM hCIM fun ω => by
    rw [hT' ω]; push_cast; ring
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
