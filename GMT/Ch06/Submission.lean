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
