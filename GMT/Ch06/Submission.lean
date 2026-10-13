import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

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

/-- Simon Ch. 6, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of an integer multiplicity
`Y = τ(M, θ, ξ) ∈ 𝒟ₖ(U)` to an open `W ⊆ U` is the integer multiplicity current
`τ(M ∩ W, θ, ξ)`. -/
theorem Submission.br_restrictDomain_isIntegerMultiplicity :
    ∀ (P k : ℕ) (U W : Set (Eucl P)) (hWU : W ⊆ U), IsOpen W →
      ∀ Y : GeometricCurrentOn U k, IsIntegerMultiplicity Y →
        IsIntegerMultiplicity (Y.restrictDomain hWU) := by
  rintro P k U W hWU hW Y ⟨M, θ, ξ, hM, hθ, hY⟩
  have hMW : NullMeasurableSet (M ∩ W) (μHE[k] : Measure (Eucl P)) :=
    hM.nullMeasurableSet.inter hW.measurableSet.nullMeasurableSet
  refine ⟨M ∩ W, θ, ξ,
    { subset := inter_subset_right
      nullMeasurableSet := hMW
      countablyRectifiable := hM.countablyRectifiable.mono inter_subset_left
      pos := fun x hx => hM.pos x hx.1
      integrableOn := fun K hK hKW =>
        (hM.integrableOn K hK (hKW.trans hWU)).mono_set fun y hy => ⟨hy.1.1, hy.2⟩
      aestronglyMeasurable := hM.aestronglyMeasurable.mono_set inter_subset_left
      orients := ?_ }, fun x hx => hθ x hx.1, fun ω => ?_⟩
  · -- `M` and `M ∩ W` agree in the open set `W`, so they have the same weighted approximate
    -- tangent spaces at points of `W`.
    have hnull : symmDiff M (M ∩ W) ∩ W = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_symmDiff, mem_empty_iff_false, iff_false]
      tauto
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hM.orients,
      ae_restrict_mem₀ hMW] with x hxM hx
    obtain ⟨τ, hτ, hTx, hξ⟩ := hxM
    exact ⟨τ, hτ, Submission.br_weightedTangent_congr P k M (M ∩ W) θ θ x W hW hx.2
      (by rw [hnull, measure_empty]) (ae_of_all _ fun _ => rfl) rfl _ hTx, hξ⟩
  · -- A test form on `W` vanishes off `W`, so the integrals over `M` and `M ∩ W` agree.
    have h0 : ∀ x, x ∉ W → θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x) = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (ω.property.2 h), map_zero, mul_zero]
    rw [GeometricCurrentOn.restrictDomain_apply, hY]
    simp only [tauAction, testFormOnInclusion_coe]
    rw [inter_comm M W, ← Measure.restrict_restrict hW.measurableSet,
      setIntegral_eq_integral_of_forall_compl_eq_zero h0]
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
/-- Simon Ch. 6, proof of 8.2 (p. 179), `p_# S̃_j` and display (10): if `p` is linear with
`‖p‖ ≤ 1` and proper on `F`, integer multiplicity `X_k ∈ 𝒟_{m+1}(U)` with `spt X_k ⊆ F` push
forward (by the smooth push-forward, `f := p`) to integer multiplicity `S_k ∈ 𝒟_{m+1}(V)` with
`S_k(ω) = X_k(p^#ω)`, `M_W(S_k) ≤ M(X_k)` and `M_W(∂S_k) ≤ M(∂X_k)`. -/
theorem Submission.ind_pi_pl_linear_pushforward_family :
    LipschitzPushforwardIntegerMultiplicity →
    (LipschitzPushforwardIntegerMultiplicity →
      ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
      ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q),
        IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V →
        (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) →
        ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧
          (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)),
            (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
              (η : DifferentialForm (Eucl P) (k + 1)) x =
                ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap
                  (fderiv ℝ f x)) →
            S ω = X η) ∧
          (∀ (ω : TestFormOn V k) (η : TestFormOn U k),
            (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
              (η : DifferentialForm (Eucl P) k) x =
                ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap
                  (fderiv ℝ f x)) →
            S.boundary ω = X.boundary η) ∧
          ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q),
            S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧
            S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) →
    ∀ (P Q m : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (F : Set (Eucl P))
      (p : Eucl P →L[ℝ] Eucl Q) (X : ℕ → GeometricCurrentOn U (m + 1)),
      IsOpen U → IsOpen V → ‖p‖ ≤ 1 → MapsTo p U V →
      (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (p ⁻¹' K ∩ F) ∧ p ⁻¹' K ∩ F ⊆ U) →
      (∀ k, IsIntegerMultiplicity (X k)) → (∀ k, (X k).support ⊆ F) →
      ∃ S : ℕ → GeometricCurrentOn V (m + 1), (∀ k, IsIntegerMultiplicity (S k)) ∧
        (∀ (k : ℕ) (ω : TestFormOn V (m + 1)) (η : TestFormOn U (m + 1)),
          (∃ N : Set (Eucl P), IsOpen N ∧ (X k).support ⊆ N ∧ ∀ x ∈ N,
            (η : DifferentialForm (Eucl P) (m + 1)) x =
              ((ω : DifferentialForm (Eucl Q) (m + 1)) (p x)).compContinuousLinearMap p) →
          S k ω = X k η) ∧
        ∀ (k : ℕ) (W : Set (Eucl Q)),
          (S k).massOn W ≤ (X k).mass ∧ (S k).boundary.massOn W ≤ (X k).boundary.mass := by
  intro hLPF hSPF P Q m U V F p X hU hV hp hpUV hprop hX hXF
  -- 1. `p` is `C^∞` and `fderiv ℝ p x = p`, so `‖fderiv ℝ p x‖ ≤ 1`.
  have hpd : ∀ x, fderiv ℝ p x = p := fun x => p.fderiv
  have hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p := p.contDiff
  -- 2. `p` is proper on `spt X_k`: `p⁻¹(K) ∩ spt X_k = (p⁻¹(K) ∩ F) \ zeroRegion X_k`.
  have hpk : ∀ k, ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      IsCompact (p ⁻¹' K ∩ (X k).support) := by
    intro k K hK hKV
    obtain ⟨hKc, hKU⟩ := hprop K hK hKV
    have heq : p ⁻¹' K ∩ (X k).support = (p ⁻¹' K ∩ F) \ (X k).zeroRegion := by
      ext y
      constructor
      · rintro ⟨hy, hys⟩
        exact ⟨⟨hy, hXF k hys⟩, hys.2⟩
      · rintro ⟨hyF, hyZ⟩
        exact ⟨hyF.1, hKU hyF, hyZ⟩
    rw [heq]
    exact hKc.diff (X k).isOpen_zeroRegion
  -- 3. The smooth push-forward by `p` of each `X_k`; choose `S_k`.
  choose S hSi hSa _ hSm using fun k => hSPF hLPF P Q m U V hU hV (X k) p (hX k) hps hpUV (hpk k)
  refine ⟨S, hSi, ?_, ?_⟩
  · -- 4. `S_k(ω) = X_k(η)` when `η = p^#ω` near `spt X_k`, as `fderiv ℝ p x = p`.
    rintro k ω η ⟨N, hN, hXN, hη⟩
    exact hSa k ω η ⟨N, hN, hXN, fun x hx => by rw [hpd x]; exact hη x hx⟩
  · -- 5. The mass bounds at `c = 1`, then `M_{p⁻¹(W) ∩ U} ≤ M_U = M`.
    intro k W
    obtain ⟨hm, hbm⟩ := hSm k 1 zero_le_one (fun x => by rw [hpd x]; exact hp) W
    simp only [one_pow, ENNReal.ofReal_one, one_mul] at hm hbm
    exact ⟨hm.trans ((X k).massOn_mono inter_subset_right),
      hbm.trans ((X k).boundary.massOn_mono inter_subset_right)⟩
/-- Geometry of an orthonormal frame `τ` in `ℝ^P`: with `π y = ∑ ⟪τᵢ, y⟫ τᵢ`, `p y = (⟪τᵢ, y⟫)ᵢ`
and `d y = ‖y − π y‖`, Pythagoras gives `‖y‖² = ‖p y‖² + d(y)²`; hence `‖p‖ ≤ 1`, `d` is
`1`-Lipschitz, `p` inverts `a ↦ ∑ aᵢ τᵢ`, `d = 0` on `span τ`, the cylinder
`{‖p‖ < 1, d < 3/4}` lies in `closedBall 0 (5/4) ⊆ B₂(0)`, and `p⁻¹(K) ∩ {d ≤ γ}` is a compact
subset of it for compact `K ⊆ B₁(0)` and `γ < 3/4`. -/
theorem Submission.ind_pi_frame_geometry :
    ∀ (P n : ℕ) (τ : Fin n → Eucl P) (p : Eucl P →L[ℝ] Eucl n) (d : Eucl P → ℝ), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → LipschitzWith 1 d ∧ (∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2) ∧ ‖p‖ ≤ 1 ∧ (∀ a : Eucl n, p (∑ i, a i • τ i) = a) ∧ (∀ i, p (τ i) = EuclideanSpace.single i (1 : ℝ)) ∧ (∀ z ∈ Submodule.span ℝ (Set.range τ), d z = 0) ∧ CompactlyContainedOpen {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (ball (0 : Eucl P) 2) ∧ ∀ γ : ℝ, γ < 3 / 4 → ∀ K : Set (Eucl n), IsCompact K → K ⊆ ball (0 : Eucl n) 1 → IsCompact (p ⁻¹' K ∩ {y | d y ≤ γ}) ∧ p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} := by
  intro P n τ p d hτ hp hd
  -- The orthogonal projection `π y = ∑ ⟪τᵢ, y⟫ τᵢ` onto `span τ`, so `d y = ‖y − π y‖`.
  obtain ⟨π, hπ⟩ : ∃ π : Eucl P → Eucl P, ∀ y, π y = ∑ i, inner ℝ (τ i) y • τ i :=
    ⟨_, fun _ => rfl⟩
  have hdπ : ∀ y, d y = ‖y - π y‖ := fun y => by rw [hd, hπ]
  -- Step 1: `⟪τⱼ, π y⟫ = ⟪τⱼ, y⟫`.
  have h1 : ∀ y j, inner ℝ (τ j) (π y) = inner ℝ (τ j) y := fun y j => by
    rw [hπ]
    exact hτ.inner_right_fintype (fun i => inner ℝ (τ i) y) j
  have hπinner : ∀ y v, inner ℝ (π y) v = ∑ i, inner ℝ (τ i) y * inner ℝ (τ i) v := by
    intro y v
    rw [hπ, sum_inner]
    simp only [real_inner_smul_left]
  -- Step 2: `π y ⊥ y − π y`.
  have h2 : ∀ y, inner ℝ (π y) (y - π y) = 0 := by
    intro y
    rw [hπinner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sub_right, h1, sub_self, mul_zero]
  -- Step 3: `‖p y‖² = ‖π y‖² = ∑ ⟪τᵢ, y⟫²` and Pythagoras.
  have hpπ : ∀ y, ‖p y‖ ^ 2 = ‖π y‖ ^ 2 := by
    intro y
    rw [EuclideanSpace.real_norm_sq_eq, ← real_inner_self_eq_norm_sq, hπinner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, hp, sq]
  have hb : ∀ y, ‖y‖ ^ 2 = ‖p y‖ ^ 2 + d y ^ 2 := by
    intro y
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (h2 y)
    rw [add_sub_cancel] at h
    rw [hpπ, hdπ, sq, sq, sq, h]
  -- Step 4: `0 ≤ d y ≤ ‖y‖` and `‖p y‖ ≤ ‖y‖`.
  have hd0 : ∀ y, 0 ≤ d y := fun y => by rw [hdπ]; exact norm_nonneg _
  have hdle : ∀ y, d y ≤ ‖y‖ := by
    intro y
    have := hb y
    nlinarith [hd0 y, norm_nonneg y, sq_nonneg ‖p y‖]
  have hple : ∀ y, ‖p y‖ ≤ ‖y‖ := by
    intro y
    have := hb y
    nlinarith [norm_nonneg (p y), norm_nonneg y, sq_nonneg (d y)]
  -- Step 5: `π` is additive, so `d x ≤ d y + d (x − y) ≤ d y + dist x y`.
  have hπsub : ∀ x y, π (x - y) = π x - π y := by
    intro x y
    simp only [hπ, inner_sub_right, sub_smul, Finset.sum_sub_distrib]
  have hLip : LipschitzWith 1 d := by
    refine LipschitzWith.of_le_add fun x y => ?_
    have e : x - π x = (y - π y) + ((x - y) - π (x - y)) := by rw [hπsub]; abel
    calc d x = ‖(y - π y) + ((x - y) - π (x - y))‖ := by rw [hdπ, e]
      _ ≤ ‖y - π y‖ + ‖(x - y) - π (x - y)‖ := norm_add_le _ _
      _ = d y + d (x - y) := by rw [hdπ, hdπ]
      _ ≤ d y + ‖x - y‖ := by gcongr; exact hdle _
      _ = d y + dist x y := by rw [dist_eq_norm]
  -- The cylinder `{‖p‖ ≤ 1, d ≤ 3/4}` lies in `closedBall 0 (5/4)`.
  have hball : ∀ y, ‖p y‖ ≤ 1 → d y ≤ 3 / 4 → y ∈ closedBall (0 : Eucl P) (5 / 4) := by
    intro y hpy hdy
    rw [mem_closedBall_zero_iff]
    have h := hb y
    have hp0 := norm_nonneg (p y)
    have hd0' := hd0 y
    nlinarith [norm_nonneg y]
  refine ⟨hLip, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (c) `‖p‖ ≤ 1`.
  · exact p.opNorm_le_bound zero_le_one fun y => by rw [one_mul]; exact hple y
  -- (d) `p (∑ aᵢ τᵢ) = a`.
  · intro a
    ext j
    rw [hp]
    exact hτ.inner_right_fintype (fun i => a i) j
  -- (e) `p τᵢ = eᵢ`.
  · intro i
    ext j
    rw [hp, PiLp.single_apply, orthonormal_iff_ite.mp hτ j i]
  -- (f) `d = 0` on `span τ`.
  · intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
    have hc : ∀ i, inner ℝ (τ i) (∑ j, c j • τ j) = c i := fun i => hτ.inner_right_fintype c i
    rw [hd]
    simp only [hc, sub_self, norm_zero]
  -- (g) `{‖p‖ < 1, d < 3/4} ⊂⊂ B₂(0)`.
  · have hcl : closure {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ⊆ closedBall (0 : Eucl P) (5 / 4) := by
      refine (closure_minimal (t := {y : Eucl P | ‖p y‖ ≤ 1 ∧ d y ≤ 3 / 4})
        (fun y hy => ⟨hy.1.le, hy.2.le⟩) ?_).trans fun y hy => hball y hy.1 hy.2
      exact (isClosed_le p.continuous.norm continuous_const).inter
        (isClosed_le hLip.continuous continuous_const)
    refine ⟨?_, ?_, ?_⟩
    · exact (isOpen_lt p.continuous.norm continuous_const).inter
        (isOpen_lt hLip.continuous continuous_const)
    · exact (isCompact_closedBall (0 : Eucl P) (5 / 4)).of_isClosed_subset isClosed_closure hcl
    · exact hcl.trans (closedBall_subset_ball (by norm_num))
  -- (h) `p⁻¹(K) ∩ {d ≤ γ}` is compact and lies in the cylinder.
  · intro γ hγ K hK hKB
    have hsub : p ⁻¹' K ∩ {y | d y ≤ γ} ⊆ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} := by
      intro y hy
      exact ⟨mem_ball_zero_iff.mp (hKB hy.1), lt_of_le_of_lt hy.2 hγ⟩
    refine ⟨?_, hsub⟩
    refine (isCompact_closedBall (0 : Eucl P) (5 / 4)).of_isClosed_subset ?_
      fun y hy => hball y (hsub hy).1.le (hsub hy).2.le
    exact (hK.isClosed.preimage p.continuous).inter (isClosed_le hLip.continuous continuous_const)
/-- Simon Ch. 6, proof of 8.2: for an orthonormal frame `τ₁, …, τₙ` of `Q = span τ ⊆ ℝ^P`, the
parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is a linear isometry `ℝⁿ → ℝ^P` with range `Q`, so it pushes
Lebesgue measure on `ℝⁿ` (`= Hⁿ`) forward to `Hⁿ ⌞ Q`.  As a closed, hence measurable, embedding
it gives `∫_Q h dHⁿ = ∫_{ℝⁿ} h(ι(a)) da` for every `h`, and `(Hⁿ ⌞ Q)(K) = Lⁿ(ι⁻¹ K) < ∞` for
compact `K`. -/
theorem Submission.ind_pi_span_integral :
    ∀ (P n : ℕ) (τ : Fin n → Eucl P), Orthonormal ℝ τ → (∀ h : Eucl P → ℝ, ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), h z ∂(μHE[n] : Measure (Eucl P)) = ∫ a : Eucl n, h (∑ i, a i • τ i)) ∧ ∀ K : Set (Eucl P), IsCompact K → ((μHE[n] : Measure (Eucl P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Eucl P))) K < ∞ := by
  intro P n τ hτ
  -- The parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is linear.
  let ι : Eucl n →ₗ[ℝ] Eucl P :=
    { toFun := fun a => ∑ i, a i • τ i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.smul_sum, smul_smul] }
  have hι : ∀ a : Eucl n, ι a = ∑ i, a i • τ i := fun a => rfl
  -- `ι` is an isometry: `‖ι a‖² = ∑ᵢ aᵢ² = ‖a‖²` by orthonormality.
  have hiso : Isometry ι := by
    refine AddMonoidHomClass.isometry_of_norm ι fun a => ?_
    have hsq : ‖ι a‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [hι, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  -- `range ι = span τ`.
  have hrange : Set.range ι = (Submodule.span ℝ (Set.range τ) : Set (Eucl P)) := by
    ext z
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨fun i => a i, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨WithLp.toLp 2 c, by simp [hι]⟩
  -- `ι` is a closed, hence measurable, embedding.
  have hemb : MeasurableEmbedding ι := hiso.isClosedEmbedding.measurableEmbedding
  -- `ι` pushes Lebesgue measure `= Hⁿ` on `ℝⁿ` forward to `Hⁿ ⌞ span τ`.
  have hmap : (volume : Measure (Eucl n)).map ι =
      (μHE[n] : Measure (Eucl P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Eucl P)) := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, hiso.map_euclideanHausdorffMeasure,
      hrange]
  refine ⟨fun h => ?_, fun K hK => ?_⟩
  · rw [← hmap, hemb.integral_map]
    rfl
  · rw [← hmap, hemb.map_apply]
    exact (hiso.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
/-- Simon Ch. 6, (2.7) (p. 136) for a constant `n`-vector: if `μ` is finite on compact sets and
`w ∈ Λₙ(ℝ^P)`, then `T(ω) = ∫ ⟨ω(x), w⟩ dμ(x)` defines a current `T ∈ 𝒟ₙ(U)` with
representation `(μ, w)`. -/
theorem Submission.ind_pi_constant_vector_current :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (w : NVector (Eucl P) n),
      (∀ K : Set (Eucl P), IsCompact K → μ K < ∞) →
      ∃ T : GeometricCurrentOn U n, IsMeasureRepresentation T μ (fun _ => w) := by
  intro P n U μ w hμ
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ K hK⟩
  -- `x ↦ ⟨ω(x), w⟩` is continuous with compact support (`w 0 = 0`), hence `μ`-integrable.
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => w ((ω : DifferentialForm (Eucl P) n) x)) μ := fun ω =>
    (w.continuous.comp ω.property.1.1.continuous).integrable_of_hasCompactSupport
      (ω.property.1.2.comp_left (map_zero w))
  -- The linear functional `L(ω) = ∫ ⟨ω, w⟩ dμ`.
  let L : CurrentOn U n :=
    { toFun := fun ω => ∫ x, w ((ω : DifferentialForm (Eucl P) n) x) ∂μ
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => ⟨hint ω, rfl⟩⟩
  -- Sequential continuity: the `ω_j` are supported in one compact `K` and `ω_j → 0` uniformly
  -- on `K`, so `|L(ω_j)| ≤ ‖w‖ · sup_K ‖ω_j‖ · μ(K) → 0`.
  obtain ⟨K, hK, -, hsupp, -, hderiv⟩ := hωs
  have hunif := Metric.tendstoUniformlyOn_iff.1 (hderiv 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hm : 0 ≤ μ.real K := measureReal_nonneg
  have hC : 0 < ‖w‖ * μ.real K + 1 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / (‖w‖ * μ.real K + 1)) (div_pos hε hC))
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_zero_right]
  change ‖∫ x, w ((ωs j : DifferentialForm (Eucl P) n) x) ∂μ‖ < ε
  -- The integrand vanishes off `K ⊇ tsupport ω_j`.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h), map_zero]]
  -- On `K`, `|⟨ω_j(x), w⟩| ≤ ‖w‖ ‖ω_j(x)‖ ≤ ‖w‖ · ε / (‖w‖ μ(K) + 1)`.
  have hbound : ∀ x ∈ K, ‖w ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
      ‖w‖ * (ε / (‖w‖ * μ.real K + 1)) := by
    intro x hx
    have h := (hN j hj x hx).le
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      Function.comp_apply, LinearIsometryEquiv.dist_map, ZeroMemClass.coe_zero, Pi.zero_apply,
      dist_zero_left] at h
    exact (w.le_opNorm _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg w))
  refine (norm_setIntegral_le_of_norm_le_const (hμ K hK) hbound).trans_lt ?_
  rw [show ‖w‖ * (ε / (‖w‖ * μ.real K + 1)) * μ.real K =
      ε * (‖w‖ * μ.real K / (‖w‖ * μ.real K + 1)) by ring]
  exact mul_lt_of_lt_one_right hε ((div_lt_one hC).2 (lt_add_one _))
/-- **Restriction of an integer multiplicity current to an open set** (Simon Ch. 6, (2.9) and 3.1,
pp. 136, 146; used for the restrictions to open sets in the proof of 8.2, pp. 176–179).  If
`X = τ(M, θ, ξ)` is integer multiplicity and `R = X ⌞ A` with `A` open, then
`R = τ(M ∩ A, θ, ξ)` is integer multiplicity.  With smooth cutoffs `φ_j → 1_A` pointwise,
`X(φ_j ω)` tends both to `∫_A ⟨ω, v⟩ dμ = R(ω)` and to `τ(M ∩ A, θ, ξ)(ω)` (dominated
convergence); and the weighted tangent planes of `(M, θ)` at `x ∈ A` are those of `(M ∩ A, θ)`,
since the blow-ups of `M` and `M ∩ A` agree near the origin. -/
theorem Submission.ind_pi_restriction_open_im :
    ∀ (P k : ℕ) (U A : Set (Eucl P)) (X R : GeometricCurrentOn U k), IsOpen U → IsOpen A →
      IsIntegerMultiplicity X → IsRestriction X A R → IsIntegerMultiplicity R := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k U A X R hU hA hX hR
  obtain ⟨M, θ, ξ, hT, hθN, hXτ⟩ := hX
  obtain ⟨hAm, μ, v, hrep, hRv⟩ := hR
  -- `|⟨α, ξ(x)⟩| ≤ ‖α‖` for `Hᵏ⌞M`-a.e. `x`, since `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ` orthonormal.
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
  -- `θ ⟨ω, ξ⟩` is `Hᵏ`-integrable on `M` for every test form `ω`: on `M ∩ spt ω` it is `θ` times
  -- a measurable function bounded by `sup ‖ω‖`, and it vanishes on `M \ spt ω`.
  have hint : ∀ ω : TestFormOn U k, IntegrableOn
      (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)) M
      (μHE[k] : Measure (Eucl P)) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Eucl P) k) := ContDiff.continuous ω.2.1.1
    have hωs : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
    obtain ⟨C, hC⟩ := hωc.bounded_above_of_compact_support hωs
    have hle : (μHE[k] : Measure (Eucl P)).restrict
        (M ∩ tsupport (ω : DifferentialForm (Eucl P) k)) ≤
        (μHE[k] : Measure (Eucl P)).restrict M :=
      Measure.restrict_mono Set.inter_subset_left le_rfl
    have hmeas : AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Eucl P) k) x))
        ((μHE[k] : Measure (Eucl P)).restrict M) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hT.aestronglyMeasurable.prodMk hωc.aestronglyMeasurable)
    have hK : IntegrableOn (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x))
        (M ∩ tsupport (ω : DifferentialForm (Eucl P) k)) (μHE[k] : Measure (Eucl P)) := by
      refine (hT.integrableOn _ hωs ω.2.2).mul_bdd (c := C) (hmeas.mono_measure hle) ?_
      filter_upwards [ae_mono hle hunit] with x hx
      exact (hx _).trans (hC x)
    refine hK.of_ae_sdiff_eq_zero hT.nullMeasurableSet
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ∉ tsupport (ω : DifferentialForm (Eucl P) k) := fun h => hx.2 ⟨hx.1, h⟩
    rw [image_eq_zero_of_notMem_tsupport hx', map_zero, mul_zero]
  -- Smooth cutoffs `φ_j → 1_A` pointwise, `0 ≤ φ_j ≤ 1`: `φ_j = s(j f)` with `f ≥ 0` smooth,
  -- `{f ≠ 0} = A`, and `s` the smooth transition (`s = 0` on `(-∞, 0]`, `s = 1` on `[1, ∞)`).
  obtain ⟨φ, hφs, hφb, hφlim⟩ : ∃ φ : ℕ → Eucl P → ℝ,
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ j)) ∧
      (∀ j x, ‖φ j x‖ ≤ 1) ∧ ∀ (g : Eucl P → ℝ) (x : Eucl P),
        Tendsto (fun j => φ j x * g x) atTop (𝓝 (A.indicator g x)) := by
    obtain ⟨f, hfA, hfs, hfr⟩ := hA.exists_contDiff_support_eq (n := ⊤)
    refine ⟨fun j x => Real.smoothTransition (j * f x), fun j =>
      Real.smoothTransition.contDiff.comp (contDiff_const.mul hfs), fun j x => ?_, fun g x => ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    by_cases hx : x ∈ A
    · have hfx : 0 < f x := by
        have hne : f x ≠ 0 := by rw [← Function.mem_support, hfA]; exact hx
        exact lt_of_le_of_ne (hfr ⟨x, rfl⟩).1 (Ne.symm hne)
      rw [Set.indicator_of_mem hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈(f x)⁻¹⌉₊] with j hj
      rw [Real.smoothTransition.one_of_one_le, one_mul]
      calc (1 : ℝ) = (f x)⁻¹ * f x := (inv_mul_cancel₀ hfx.ne').symm
        _ ≤ j * f x :=
          mul_le_mul_of_nonneg_right ((Nat.le_ceil _).trans (by exact_mod_cast hj)) hfx.le
    · have hfx : f x = 0 := by rw [← Function.notMem_support, hfA]; exact hx
      rw [Set.indicator_of_notMem hx]
      simp only [hfx, mul_zero, Real.smoothTransition.zero, zero_mul]
      exact tendsto_const_nhds
  -- `R = τ(M ∩ A, θ, ξ)`: with `ω_j = φ_j ω`, `X(ω_j) → ∫_A ⟨ω, v⟩ dμ = R(ω)` and
  -- `X(ω_j) = τ(M, θ, ξ)(ω_j) → τ(M ∩ A, θ, ξ)(ω)` by dominated convergence.
  have hRτ : ∀ ω : TestFormOn U k, R ω = tauAction k (M ∩ A) θ ξ ω := by
    intro ω
    have hωsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) := ω.2.1.1
    have hωcs : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
    have hωU : tsupport (ω : DifferentialForm (Eucl P) k) ⊆ U := ω.2.2
    have hcut : ∀ j : ℕ, ∃ ω' : TestFormOn U k, (ω' : DifferentialForm (Eucl P) k) =
        fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x := by
      intro j
      have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x) := (hφs j).smul hωsm
      have hcs : HasCompactSupport (fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x) :=
        hωcs.mono fun x hx h0 => hx (by simp only [h0, smul_zero])
      have hsU : tsupport (fun x => φ j x • (ω : DifferentialForm (Eucl P) k) x) ⊆ U :=
        (tsupport_smul_subset_right _ _).trans hωU
      exact ⟨⟨_, ⟨⟨hsm, hcs⟩, hsU⟩⟩, rfl⟩
    choose ωj hωj using hcut
    have hval : ∀ j x, (ωj j : DifferentialForm (Eucl P) k) x =
        φ j x • (ω : DifferentialForm (Eucl P) k) x := fun j x => congrFun (hωj j) x
    have h1 : Tendsto (fun j => X (ωj j)) atTop (𝓝 (R ω)) := by
      rw [hRv ω, ← integral_indicator hAm]
      have hX1 : (fun j => X (ωj j)) =
          fun j => ∫ x, v x ((ωj j : DifferentialForm (Eucl P) k) x) ∂μ :=
        funext fun j => (hrep (ωj j)).2
      rw [hX1]
      refine tendsto_integral_of_dominated_convergence
        (fun x => ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖)
        (fun j => (hrep (ωj j)).1.aestronglyMeasurable) (hrep ω).1.norm
        (fun j => Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => ?_)
      · rw [hval, map_smul, smul_eq_mul, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφb j x)
      · refine (hφlim (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) x).congr
          (fun j => ?_)
        rw [hval, map_smul, smul_eq_mul]
    have h2 : Tendsto (fun j => X (ωj j)) atTop (𝓝 (tauAction k (M ∩ A) θ ξ ω)) := by
      have hX2 : (fun j => X (ωj j)) = fun j => ∫ x in M,
          θ x * ξ x ((ωj j : DifferentialForm (Eucl P) k) x) ∂(μHE[k] : Measure (Eucl P)) :=
        funext fun j => hXτ (ωj j)
      rw [hX2, tauAction, ← setIntegral_indicator hAm]
      refine tendsto_integral_of_dominated_convergence
        (fun x => ‖θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)‖)
        (fun j => (hint (ωj j)).aestronglyMeasurable) (hint ω).norm
        (fun j => Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => ?_)
      · rw [hval, map_smul, smul_eq_mul, mul_left_comm, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφb j x)
      · refine (hφlim (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) k) x)) x).congr
          (fun j => ?_)
        rw [hval, map_smul, smul_eq_mul, mul_left_comm]
    exact tendsto_nhds_unique h1 h2
  -- Locality of weighted tangent planes (Simon Ch. 3, 1.7): for `x ∈ A`, if `g = 0` off
  -- `B_ρ(0)` and `B_δ(x) ⊆ A`, then for `0 < r < δ / ρ` the blow-up integrands vanish off
  -- `W = η_{x,r}(A)`, and `W ∩ η_{x,r}(M) = W ∩ η_{x,r}(M ∩ A)`.
  have htan : ∀ x ∈ A, ∀ L : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x L := by
    intro x hxA L hL
    refine ⟨hL.1, fun g => (hL.2 g).congr' ?_⟩
    obtain ⟨ρ, hρ, hgρ⟩ := g.hasCompactSupport.exists_pos_le_norm
    obtain ⟨δ, hδ, hδA⟩ := Metric.isOpen_iff.mp hA x hxA
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hρ)] with r hr
    obtain ⟨hr0, hrρ⟩ := hr
    have hcont : Continuous fun y : Eucl P => x + r • y :=
      continuous_const.add (continuous_const_smul r)
    set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' A with hW
    have hWm : MeasurableSet W := (hA.preimage hcont).measurableSet
    have hvan : ∀ y, y ∉ W → g y * θ (x + r • y) = 0 := by
      intro y hy
      have hgy : g y = 0 := by
        apply hgρ
        have h1 : x + r • y ∉ ball x δ := fun h => hy (hδA h)
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr0, not_lt] at h1
        rw [lt_div_iff₀ hρ] at hrρ
        exact le_of_lt (lt_of_mul_lt_mul_left (hrρ.trans_le h1) hr0.le)
      rw [hgy, zero_mul]
    have hcutW : ∀ S : Set (Eucl P),
        ∫ y in blowUpMap x r '' S, g y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
          ∫ y in W ∩ blowUpMap x r '' S, g y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
      intro S
      rw [← Measure.restrict_restrict hWm, setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
    have hset : W ∩ blowUpMap x r '' M = W ∩ blowUpMap x r '' (M ∩ A) := by
      ext y
      constructor
      · rintro ⟨hyW, z, hzM, rfl⟩
        refine ⟨hyW, z, ⟨hzM, ?_⟩, rfl⟩
        have hz : x + r • blowUpMap x r z = z := by
          simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, add_sub_cancel]
        have hzW : x + r • blowUpMap x r z ∈ A := hyW
        rwa [hz] at hzW
      · rintro ⟨hyW, z, ⟨hzM, -⟩, rfl⟩
        exact ⟨hyW, z, hzM, rfl⟩
    rw [hcutW M, hcutW (M ∩ A), hset]
  -- `(M ∩ A, θ, ξ)` is a rectifiable triple with integer multiplicity representing `R`.
  refine ⟨M ∩ A, θ, ξ, ⟨Set.inter_subset_left.trans hT.subset,
    hT.nullMeasurableSet.inter hAm.nullMeasurableSet,
    hT.countablyRectifiable.mono Set.inter_subset_left,
    fun x hx => hT.pos x hx.1,
    fun K hK hKU => (hT.integrableOn K hK hKU).mono_set
      (Set.inter_subset_inter_left K Set.inter_subset_left),
    hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl),
    ?_⟩, fun x hx => hθN x hx.1, hRτ⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hT.orients,
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (ae_restrict_mem hAm)]
    with x hx hxA
  obtain ⟨τ, hτ, hτL, hξ⟩ := hx
  exact ⟨τ, hτ, htan x hxA _ hτL, hξ⟩
theorem Submission.ind_pi_ss_cycle_slice_boundary : ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ) (t : ℝ) (S : GeometricCurrentOn U m), IsOpen U → T.boundary = 0 → IsSlice T f t S → ∃ A : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ f x < t} A ∧ A.boundary = S := by
  intro P m U T f t S hU hT hSl
  -- Unfold `IsSlice` (4.6): `S = ∂A − B` with `A = T ⌞ Aₜ`, `B = (∂T) ⌞ Aₜ`, where
  -- `Aₜ = {x ∈ U : f x < t}` and `B ω = ∫_{Aₜ} ⟨ω, v⟩ dμ` for a representation `(μ, v)` of `∂T`.
  obtain ⟨A, B, hA, ⟨hmeas, μ, v, hrep, hB⟩, hS⟩ := hSl
  -- `B = 0`, i.e. uniqueness of restrictions for the zero current `∂T`: testing `∂T = 0` with
  -- `g ω` (`g ∈ C_c^∞(U)`) shows that `⟨ω, v⟩` integrates to zero against every such `g`, so it
  -- vanishes `μ`-a.e. on `U ⊇ Aₜ`.
  have hB0 : ∀ ω : TestFormOn U m, B ω = 0 := by
    intro ω
    have hae : ∀ᵐ x ∂μ, x ∈ U → v x ((ω : DifferentialForm (Eucl P) m) x) = 0 := by
      refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hrep ω).1.locallyIntegrable.locallyIntegrableOn U) (fun g hg hgc hgU => ?_)
      let gω : TestFormOn U m := ⟨fun x => g x • (ω : DifferentialForm (Eucl P) m) x,
        ⟨hg.smul ω.property.1.1, hgc.smul_right⟩,
        (tsupport_smul_subset_left _ _).trans hgU⟩
      calc ∫ x, g x • v x ((ω : DifferentialForm (Eucl P) m) x) ∂μ
          = ∫ x, v x ((gω : DifferentialForm (Eucl P) m) x) ∂μ := by
            congr 1
            funext x
            exact (map_smul (v x) (g x) _).symm
        _ = T.boundary gω := ((hrep gω).2).symm
        _ = 0 := by rw [hT, GeometricCurrentOn.zero_apply]
    rw [hB ω]
    exact integral_eq_zero_of_ae
      ((ae_restrict_iff' hmeas).2 (hae.mono fun x hx hxA => hx hxA.1))
  -- Hence `S = ∂A − 0 = ∂A`, with `A` the restriction of `T` to `Aₜ`.
  refine ⟨A, hA, GeometricCurrentOn.ext fun ω => ?_⟩
  rw [hS ω, hB0 ω, sub_zero]
/-- Simon Ch. 6, (2.8)–(2.9): for `W ⊂⊂ U` and `S = X ⌞ A`, `M_W(S) ≤ M_W(X)`.  For an
admissible `ω`, `S(ω) = ∫_A ⟨ω, v⟩ dμ`.  By regularity of the finite measure `|⟨ω, v⟩| μ` there
are a closed `F ⊆ A` and an open `G ⊇ A` with `∫_{G \ F} |⟨ω, v⟩| dμ < ε`; a smooth
`ψ : ℝ^P → [0, 1]` equal to `1` on `F` with support `G` makes `ψ ω` admissible and
`S(ω) ≤ X(ψ ω) + ε ≤ M_W(X) + ε`. -/
theorem Submission.ind_pi_ss_restriction_massOn_le : ∀ (P k : ℕ) (U W A : Set (Eucl P)) (X S : GeometricCurrentOn U k), IsOpen U → CompactlyContainedOpen W U → IsRestriction X A S → S.massOn W ≤ X.massOn W := by
  intro P k U W A X S _ _ hR
  obtain ⟨hA, μ, v, hrep, hS⟩ := hR
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
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
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  set f : Eucl P → ℝ := fun x => v x ((ω : DifferentialForm (Eucl P) k) x)
  have hfi : Integrable f μ := (hrep ω).1
  -- The finite measure `ν = |f| μ`.
  set ν : Measure (Eucl P) := μ.withDensity (fun x => ‖f x‖ₑ) with hν_def
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfi.2.ne
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by simp [hε.ne']
  obtain ⟨F, hFA, hFc, hνF⟩ := hA.exists_isClosed_sdiff_lt (μ := ν) (measure_ne_top ν A) hε2
  obtain ⟨G, hAG, hGo, -, hνG⟩ := hA.exists_isOpen_sdiff_lt (μ := ν) (measure_ne_top ν A) hε2
  obtain ⟨ψ, hψs, hψr, hψsupp, hψ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hGo hFc (hFA.trans hAG)
  -- The cut-off test form `ψ ω`.
  have hω_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Eucl P) k) :=
    ω.2.1.1
  have hω_cpt : HasCompactSupport (ω : DifferentialForm (Eucl P) k) := ω.2.1.2
  let ω' : TestFormOn U k := ⟨fun x => ψ x • (ω : DifferentialForm (Eucl P) k) x,
    ⟨hψs.smul hω_smooth, HasCompactSupport.smul_left (f := ψ) hω_cpt⟩,
    (tsupport_smul_subset_right _ _).trans ω.2.2⟩
  have hω' : ω' ∈ massAdmissibleOn U k W := by
    refine ⟨(tsupport_smul_subset_right _ _).trans hω.1, fun x => ?_⟩
    change covectorEuclideanNorm (ψ x • (ω : DifferentialForm (Eucl P) k) x) ≤ 1
    have h0 := hψr ⟨x, rfl⟩
    rw [hsmul, abs_of_nonneg h0.1]
    calc ψ x * covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ 1 * 1 :=
          mul_le_mul h0.2 (hω.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hω'f : ∀ x, v x ((ω' : DifferentialForm (Eucl P) k) x) = ψ x * f x := by
    intro x
    change v x (ψ x • (ω : DifferentialForm (Eucl P) k) x) = ψ x * f x
    rw [map_smul, smul_eq_mul]
  have hψf : Integrable (fun x => ψ x * f x) μ := by
    simpa only [hω'f] using (hrep ω').1
  have hXω' : X ω' = ∫ x, ψ x * f x ∂μ := by
    simpa only [hω'f] using (hrep ω').2
  have hGF : MeasurableSet (G \ F) := hGo.measurableSet.diff hFc.measurableSet
  -- Pointwise: `1_A f - ψ f ≤ 1_{G \ F} |f|`.
  have hpt : ∀ x, A.indicator f x - ψ x * f x ≤ (G \ F).indicator (fun x => |f x|) x := by
    intro x
    have h0 := hψr ⟨x, rfl⟩
    have hnn : 0 ≤ (G \ F).indicator (fun x => |f x|) x :=
      Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
    by_cases hxF : x ∈ F
    · rw [Set.indicator_of_mem (hFA hxF), (hψ1 x).1 hxF, one_mul, sub_self]
      exact hnn
    · by_cases hxG : x ∈ G
      · rw [Set.indicator_of_mem (show x ∈ G \ F from ⟨hxG, hxF⟩)]
        by_cases hxA : x ∈ A
        · rw [Set.indicator_of_mem hxA]
          nlinarith [le_abs_self (f x), abs_nonneg (f x), h0.1, h0.2]
        · rw [Set.indicator_of_notMem hxA]
          nlinarith [neg_abs_le (f x), abs_nonneg (f x), h0.1, h0.2]
      · have hψ0 : ψ x = 0 := by
          by_contra h
          exact hxG (hψsupp ▸ (Function.mem_support.mpr h))
        rw [Set.indicator_of_notMem (fun h => hxG (hAG h)), hψ0, zero_mul, sub_zero]
        exact hnn
  have hνGF : ν (G \ F) < ε := by
    calc ν (G \ F) ≤ ν ((G \ A) ∪ (A \ F)) := measure_mono fun x hx => by
          by_cases hxA : x ∈ A
          · exact Or.inr ⟨hxA, hx.2⟩
          · exact Or.inl ⟨hx.1, hxA⟩
      _ ≤ ν (G \ A) + ν (A \ F) := measure_union_le _ _
      _ < (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := ENNReal.add_lt_add hνG hνF
      _ = ε := ENNReal.add_halves _
  have hint : ∫ x in G \ F, |f x| ∂μ ≤ ε := by
    have h1 : ∫ x in G \ F, |f x| ∂μ = (ν (G \ F)).toReal := by
      rw [hν_def, withDensity_apply _ hGF]
      simp_rw [← Real.norm_eq_abs]
      exact integral_norm_eq_lintegral_enorm hfi.aestronglyMeasurable.restrict
    rw [h1]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hνGF.le
  have hest : S ω ≤ X ω' + ε := by
    have hdiff : S ω - X ω' = ∫ x, (A.indicator f x - ψ x * f x) ∂μ := by
      rw [hS ω, hXω', integral_sub (hfi.indicator hA) hψf, integral_indicator hA]
    have hle : ∫ x, (A.indicator f x - ψ x * f x) ∂μ ≤
        ∫ x, (G \ F).indicator (fun x => |f x|) x ∂μ :=
      integral_mono ((hfi.indicator hA).sub hψf) (hfi.abs.indicator hGF) hpt
    rw [integral_indicator hGF] at hle
    linarith
  calc ENNReal.ofReal (S ω) ≤ ENNReal.ofReal (X ω' + ε) := ENNReal.ofReal_le_ofReal hest
    _ ≤ ENNReal.ofReal (X ω') + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (X ω') + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ X.massOn W + ε := by gcongr; exact X.le_massOn hω'
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
/-- Simon Ch. 6, (2.8) (p. 136) for `U = ℝ^P`: a mass measure `μ` of `T` satisfies
`μ(B_r(x)) = M_{B_r(x)}(T)` on every open ball, as `B_r(x) ⊂⊂ ℝ^P`; and `μ(ℝ^P) ≤ M(T)`, by
continuity from below along `ℝ^P = ⋃_k B_k(0)` and `M_{B_k(0)}(T) ≤ M(T)`. -/
theorem Submission.ind_md_mmb_massMeasure_balls : ∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl P)) n) (μ : Measure (Eucl P)), IsMassMeasure T μ → μ univ ≤ T.mass ∧ ∀ (x : Eucl P) (r : ℝ), μ (ball x r) = T.massOn (ball x r) := by
  intro P n T μ hμ
  -- Every open ball is `⊂⊂ ℝ^P`: its closure is a closed subset of a compact closed ball.
  have hball : ∀ (x : Eucl P) (r : ℝ), μ (ball x r) = T.massOn (ball x r) := fun x r =>
    hμ.2 _ ⟨isOpen_ball, (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  refine ⟨?_, hball⟩
  -- Continuity from below along the increasing balls `B_k(0)`, which exhaust `ℝ^P`.
  calc μ univ = μ (⋃ k : ℕ, ball (0 : Eucl P) k) := by rw [iUnion_ball_nat]
    _ = ⨆ k : ℕ, μ (ball (0 : Eucl P) k) :=
      Monotone.measure_iUnion fun _ _ hk => ball_subset_ball (Nat.cast_le.2 hk)
    _ ≤ T.mass := iSup_le fun k => (hball 0 k).trans_le (T.massOn_mono (subset_univ _))

/-- **Mass measure of a current of finite mass on balls** (Step 1, (1a)–(1b), of the proof of the
mass density bound in Simon Ch. 6, 8.2, for one current).  If `T ∈ 𝒟ₙ(ℝ^P)` has `M(T) < ∞`, then
`M_W(T) ≤ M(T) < ∞` for every `W` (`massOn_mono`), so (R2) of the restriction theory (2.7)–(2.9)
with `U = ℝ^P` gives a mass measure `μ` of `T`.  Every mass measure satisfies
`μ(B_r(x)) = M_{B_r(x)}(T)` for all `x, r` and `μ(ℝ^P) ≤ M(T)`. -/
theorem Submission.ind_md_mass_measure_balls : ∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Eucl P)) n), T.mass < ∞ → ∃ μ : Measure (Eucl P), μ univ ≤ T.mass ∧ ∀ (x : Eucl P) (r : ℝ), μ (ball x r) = T.massOn (ball x r) := by
  intro P n T hT
  -- Step 1: local finiteness, `M_W(T) ≤ M_{ℝ^P}(T) = M(T) < ∞`.
  have hloc : ∀ W, CompactlyContainedOpen W (univ : Set (Eucl P)) → T.massOn W < ∞ :=
    fun W _ => (T.massOn_mono (subset_univ W)).trans_lt hT
  -- Step 2: (R2) with `U = ℝ^P` gives a mass measure `μ` of `T`.
  obtain ⟨μ, hμ, -, -⟩ := Submission.iwl_restriction_theory.2.2 P n univ isOpen_univ T hloc
  -- Steps 3–5: `μ(B_r(x)) = M_{B_r(x)}(T)` and `μ(ℝ^P) ≤ M(T)` for this mass measure.
  exact ⟨μ, Submission.ind_md_mmb_massMeasure_balls P n T μ hμ⟩
/-- Simon Ch. 1, 4.16 on the ball `B̄_R(0)` combined with the closed-set half of the portmanteau
theorem: measures `μ_j` on `ℝ^P` with `sup_j μ_j(ℝ^P) < ∞` have a subsequence `μ_{χ(i)}` and a
finite measure `ν` with `limsup_i μ_{χ(i)}(F) ≤ ν(F)` for every closed `F ⊆ B̄_R(0)`.

`ν` is the measure of the content `K ↦ lim_𝒰 μ_j(K)` on compact sets, `𝒰` an ultrafilter finer
than `atTop`; the subsequence is extracted along a countable family of finite unions of closed
balls, and outer regularity of `ν` reduces a closed `F` to such a union. -/
theorem Submission.ind_md_closedBall_weak_subseq : ∀ (P R : ℕ) (μ : ℕ → Measure (Eucl P)), (⨆ j, μ j univ) < ∞ → ∃ (χ : ℕ → ℕ) (ν : Measure (Eucl P)), StrictMono χ ∧ ν univ < ∞ ∧ ∀ F : Set (Eucl P), IsClosed F → F ⊆ closedBall 0 (R : ℝ) → limsup (fun i => μ (χ i) F) atTop ≤ ν F := by
  intro P R μ hμ
  -- An ultrafilter `uf` finer than `atTop`; every sequence in the compact space `[0, ∞]`
  -- converges along it.  `lam A = lim_uf μ_j(A)`.
  obtain ⟨uf, huf⟩ : ∃ uf : Ultrafilter ℕ, (uf : Filter ℕ) ≤ atTop :=
    ⟨Ultrafilter.of atTop, Ultrafilter.of_le atTop⟩
  have hex : ∀ A : Set (Eucl P), ∃ a : ℝ≥0∞, Tendsto (fun j => μ j A) uf (𝓝 a) := by
    intro A
    obtain ⟨a, -, ha⟩ := isCompact_univ.ultrafilter_le_nhds (uf.map fun j => μ j A) (by simp)
    exact ⟨a, by rwa [Ultrafilter.coe_map] at ha⟩
  choose lam hlam using hex
  have hle : ∀ A, lam A ≤ ⨆ j, μ j univ := fun A =>
    le_of_tendsto' (hlam A) fun j =>
      (measure_mono (subset_univ A)).trans (le_iSup (fun j => μ j univ) j)
  have hne : ∀ A, lam A ≠ ∞ := fun A => ((hle A).trans_lt hμ).ne
  have hmono : ∀ A B : Set (Eucl P), A ⊆ B → lam A ≤ lam B := fun A B h =>
    le_of_tendsto_of_tendsto' (hlam A) (hlam B) fun j => measure_mono h
  -- The content `K ↦ lam K` on compact sets and its measure `ν`.
  obtain ⟨c, hc⟩ : ∃ c : Content (Eucl P), ∀ K : TopologicalSpace.Compacts (Eucl P),
      c K = lam K := by
    refine ⟨{ toFun := fun K => (lam K).toNNReal
              mono' := fun K₁ K₂ h => ENNReal.toNNReal_mono (hne _) (hmono _ _ h)
              sup_disjoint' := fun K₁ K₂ hd _ h₂ => ?_
              sup_le' := fun K₁ K₂ => ?_ }, fun K => ENNReal.coe_toNNReal (hne _)⟩
    · have h := tendsto_nhds_unique (hlam ((K₁ : Set (Eucl P)) ∪ K₂))
        (((hlam K₁).add (hlam K₂)).congr fun j => (measure_union hd h₂.measurableSet).symm)
      show (lam ↑(K₁ ⊔ K₂)).toNNReal = (lam K₁).toNNReal + (lam K₂).toNNReal
      rw [TopologicalSpace.Compacts.coe_sup, h, ENNReal.toNNReal_add (hne _) (hne _)]
    · show (lam ↑(K₁ ⊔ K₂)).toNNReal ≤ (lam K₁).toNNReal + (lam K₂).toNNReal
      rw [TopologicalSpace.Compacts.coe_sup, ← ENNReal.toNNReal_add (hne _) (hne _)]
      exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨hne _, hne _⟩)
        (le_of_tendsto_of_tendsto' (hlam _) ((hlam K₁).add (hlam K₂)) fun j =>
          measure_union_le _ _)
  have hν : c.measure univ ≤ ⨆ j, μ j univ := by
    rw [c.measure_apply MeasurableSet.univ, c.outerMeasure_of_isOpen univ isOpen_univ]
    exact iSup₂_le fun K _ => (hc K).trans_le (hle K)
  -- Finite unions `C k` of closed balls with centres in a dense sequence and radii `1/(b+1)`.
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (Eucl P)
  obtain ⟨e, he⟩ := exists_surjective_nat (Finset (ℕ × ℕ))
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Set (Eucl P),
      ∀ k, C k = ⋃ p ∈ e k, closedBall (d p.1) (1 / ((p.2 : ℝ) + 1)) := ⟨_, fun _ => rfl⟩
  have hCc : ∀ k, IsCompact (C k) := fun k => by
    rw [hC]
    exact (e k).isCompact_biUnion fun p _ => isCompact_closedBall _ _
  -- A subsequence with `μ_{χ(n)}(C k) < lam (C k) + 1/n` for all `k ≤ n`.
  have hfreq : ∀ n : ℕ, ∃ᶠ j in atTop,
      ∀ k ∈ Finset.range (n + 1), μ j (C k) < lam (C k) + (n : ℝ≥0∞)⁻¹ := by
    intro n
    refine (Filter.Eventually.frequently ?_).filter_mono huf
    refine (Filter.eventually_all_finset _).2 fun k _ => (hlam (C k)).eventually_lt_const ?_
    exact ENNReal.lt_add_right (hne _) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  obtain ⟨χ, hχ, hχC⟩ := Filter.extraction_forall_of_frequently hfreq
  have hlimC : ∀ k, limsup (fun i => μ (χ i) (C k)) atTop ≤ lam (C k) := by
    intro k
    have h1 : Tendsto (fun n : ℕ => lam (C k) + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (lam (C k))) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := lam (C k))).add ENNReal.tendsto_inv_nat_nhds_zero
    calc limsup (fun i => μ (χ i) (C k)) atTop
        ≤ limsup (fun n : ℕ => lam (C k) + (n : ℝ≥0∞)⁻¹) atTop :=
          limsup_le_limsup (eventually_atTop.2 ⟨k, fun n hn =>
            (hχC n k (Finset.mem_range.2 (Nat.lt_succ_of_le hn))).le⟩)
      _ = lam (C k) := h1.limsup_eq
  refine ⟨χ, c.measure, hχ, hν.trans_lt hμ, fun F hF hFK => ?_⟩
  have hFc : IsCompact F := (isCompact_closedBall 0 (R : ℝ)).of_isClosed_subset hF hFK
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hFfin => ?_
  -- Outer regularity: an open `G ⊇ F` with `ν(G) < ν(F) + ε`.
  obtain ⟨G, hFG, hGo, hGν⟩ := Set.exists_isOpen_lt_of_lt F (c.measure F + ε)
    (ENNReal.lt_add_right hFfin.ne (ENNReal.coe_ne_zero.2 hε.ne'))
  -- Some `C k` lies between `F` and `G`.
  obtain ⟨k, hFC, hCG⟩ : ∃ k, F ⊆ C k ∧ C k ⊆ G := by
    have hcov : F ⊆ ⋃ p ∈ {p : ℕ × ℕ | closedBall (d p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ G},
        ball (d p.1) (1 / ((p.2 : ℝ) + 1)) := by
      intro x hx
      obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 hGo x (hFG hx)
      obtain ⟨b, hb⟩ := exists_nat_one_div_lt (half_pos hr)
      obtain ⟨a, ha⟩ := hd.exists_dist_lt x (Nat.one_div_pos_of_nat (n := b))
      refine mem_iUnion₂.2 ⟨(a, b), fun y hy => hrG ?_, ha⟩
      have hy' : dist y (d a) ≤ 1 / ((b : ℝ) + 1) := hy
      have h3 := dist_triangle y (d a) x
      rw [dist_comm (d a) x] at h3
      rw [mem_ball]
      linarith
    obtain ⟨T, hTsub, hTfin, hFT⟩ := hFc.elim_finite_subcover_image (fun p _ => isOpen_ball) hcov
    obtain ⟨k, hk⟩ := he hTfin.toFinset
    refine ⟨k, fun x hx => ?_, fun y hy => ?_⟩
    · obtain ⟨p, hpT, hxp⟩ := mem_iUnion₂.1 (hFT hx)
      rw [hC, hk]
      exact mem_iUnion₂.2 ⟨p, hTfin.mem_toFinset.2 hpT, ball_subset_closedBall hxp⟩
    · rw [hC, hk] at hy
      obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
      exact hTsub (hTfin.mem_toFinset.1 hp) hyp
  calc limsup (fun i => μ (χ i) F) atTop ≤ limsup (fun i => μ (χ i) (C k)) atTop :=
        limsup_le_limsup (Eventually.of_forall fun i => measure_mono hFC)
    _ ≤ lam (C k) := hlimC k
    _ = c ⟨C k, hCc k⟩ := (hc ⟨C k, hCc k⟩).symm
    _ ≤ c.outerMeasure (C k) := c.le_outerMeasure_compacts ⟨C k, hCc k⟩
    _ = c.measure (C k) := (c.measure_apply (hCc k).measurableSet).symm
    _ ≤ c.measure G := measure_mono hCG
    _ ≤ c.measure F + ε := hGν.le

/-- Diagonal extraction over the closed balls `B̄_R(0)`, `R ∈ ℕ` (Simon Ch. 6, proof of 8.2, steps
(2b)–(2c) and 3, carrying the closed-set `limsup` bound instead of weak convergence).  Apply
`ind_md_closedBall_weak_subseq` to the nested subsequences `p₀ = id`, `p_{R+1} = p_R ∘ χ_{R, p_R}`
and take the diagonal `φ(j) = p_{j+1}(j)`.  For `j ≥ R`, `φ(j) = p_{R+1}(i)` with `i ≥ j`, so the
bound `limsup_i μ_{p_{R+1}(i)}(F) ≤ ν_R(F)` for closed `F ⊆ B̄_R(0)` passes to `φ`. -/
theorem Submission.ind_md_diagonal_weak_subseq : ∀ (P : ℕ) (μ : ℕ → Measure (Eucl P)), (⨆ j, μ j univ) < ∞ → ∃ (φ : ℕ → ℕ) (ν : ℕ → Measure (Eucl P)), StrictMono φ ∧ (∀ R, ν R univ < ∞) ∧ ∀ (R : ℕ) (F : Set (Eucl P)), IsClosed F → F ⊆ closedBall 0 (R : ℝ) → limsup (fun j => μ (φ j) F) atTop ≤ ν R F := by
  intro P μ hμ
  -- Step 1: the sibling lemma for every radius `R` and every subsequence `(μ_{ψ(i)})_i`.
  have hb : ∀ ψ : ℕ → ℕ, (⨆ i, μ (ψ i) univ) < ∞ := fun ψ =>
    lt_of_le_of_lt (iSup_le fun i => le_iSup (fun j => μ j univ) (ψ i)) hμ
  choose χ ν hχ hνfin hν using fun (R : ℕ) (ψ : ℕ → ℕ) =>
    Submission.ind_md_closedBall_weak_subseq P R (fun i => μ (ψ i)) (hb ψ)
  -- Step 2: nested subsequences `p₀ = id`, `p_{R+1} = p_R ∘ χ_{R, p_R}`.
  obtain ⟨p, hp0, hpS⟩ : ∃ p : ℕ → ℕ → ℕ, p 0 = id ∧ ∀ R, p (R + 1) = p R ∘ χ R (p R) :=
    ⟨fun R => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun R q => q ∘ χ R q) R, rfl, fun _ => rfl⟩
  have hp : ∀ R, StrictMono (p R) := by
    intro R
    induction R with
    | zero => rw [hp0]; exact strictMono_id
    | succ R ih => rw [hpS]; exact ih.comp (hχ R (p R))
  -- Step 3: tails, `p_{R+1+d} = p_{R+1} ∘ g` with `g` strictly increasing.
  have htail : ∀ R d, ∃ g : ℕ → ℕ, StrictMono g ∧ p (R + 1 + d) = p (R + 1) ∘ g := by
    intro R d
    induction d with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ d ih =>
      obtain ⟨g, hg, hpg⟩ := ih
      refine ⟨g ∘ χ (R + 1 + d) (p (R + 1 + d)), hg.comp (hχ _ _), ?_⟩
      rw [← add_assoc, hpS, hpg, Function.comp_assoc]
  -- Step 4: the diagonal `φ(j) = p_{j+1}(j)` is strictly increasing.
  have hφ : StrictMono fun j => p (j + 1) j := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    show p (j + 1) j < p (j + 1 + 1) (j + 1)
    rw [hpS (j + 1)]
    exact hp (j + 1) ((Nat.lt_add_one j).trans_le ((hχ (j + 1) (p (j + 1))).id_le (j + 1)))
  -- Step 5: for `R ≤ j`, `φ(j) = p_{R+1}(i)` for some `i ≥ j`.
  have hsub : ∀ R j, R ≤ j → ∃ i, j ≤ i ∧ p (j + 1) j = p (R + 1) i := by
    intro R j hRj
    obtain ⟨g, hg, hpg⟩ := htail R (j - R)
    rw [show R + 1 + (j - R) = j + 1 by omega] at hpg
    exact ⟨g j, hg.id_le j, congrFun hpg j⟩
  -- Steps 6–7: compare the limsups via `limsup = ⨅ N, ⨆ j ≥ N`, then apply step 2.
  refine ⟨fun j => p (j + 1) j, fun R => ν R (p R), hφ, fun R => hνfin R (p R),
    fun R F hF hFR => ?_⟩
  calc limsup (fun j => μ (p (j + 1) j) F) atTop
      ≤ limsup (fun i => μ (p (R + 1) i) F) atTop := by
        rw [limsup_eq_iInf_iSup_of_nat, limsup_eq_iInf_iSup_of_nat]
        refine le_iInf fun N => iInf_le_of_le (max N R) (iSup₂_le fun j hj => ?_)
        obtain ⟨i, hji, hi⟩ := hsub R j (le_of_max_le_right hj)
        rw [hi]
        exact le_iSup₂_of_le i ((le_of_max_le_left hj).trans hji) le_rfl
    _ ≤ ν R (p R) F := by
        rw [hpS]
        exact hν R (p R) F hF hFR
/-- Simon Ch. 1, Theorem 3.3 with `t = ∞`, followed by unpacking the finite upper density: if
`ν(ℝ^P) < ∞`, then for `Hⁿ`-a.e. `x` there are `C` and `r₀ > 0` with `ν(B̄ᵣ(x)) < C rⁿ` for
`0 < r < r₀`.  The infinite-density set `A = {Θ*ⁿ(ν, ·) = ∞}` is `μH[n]`-null: at each scale the
five-times covering lemma selects disjoint balls `B̄ᵣ(x)`, `x ∈ A`, with `M ωₙ rⁿ ≤ ν(B̄ᵣ(x))`
whose enlargements cover `A`, so `M ωₙ μH[n](A) ≤ 10ⁿ ν(ℝ^P)` for every `M ∈ ℕ`. -/
theorem Submission.ind_md_ae_closedBall_growth : ∀ (P n : ℕ) (ν : Measure (Eucl P)), ν univ < ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Ioo (0 : ℝ) r₀, ν (closedBall x r) < ENNReal.ofReal (C * r ^ n) := by
  intro P n ν hν
  obtain ⟨ω, hω⟩ : ∃ ω, Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) = ω := ⟨_, rfl⟩
  have hω0 : ω ≠ 0 :=
    hω ▸ (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
  have hωtop : ω ≠ ∞ := hω ▸ Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
  -- Step 1: the infinite-density set `A` is `μH[n]`-null (Simon Ch. 1, 3.3 with `t = ∞`).
  obtain ⟨A, hA⟩ : ∃ A : Set (Eucl P),
      A = {x | ¬dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x < ∞} := ⟨_, rfl⟩
  have hH : (μH[(n : ℝ)] : Measure (Eucl P)) A = 0 := by
    by_contra hne
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt (mul_ne_zero hω0 hne)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hν.ne :
        (10 : ℝ≥0∞) ^ n * ν univ ≠ ∞)
    -- It suffices to show `M ωₙ μH[n](A) ≤ 10ⁿ ν(ℝ^P)`, scale by scale.
    refine (not_le.mpr hM) ?_
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · simp
    have hHA : (μH[(n : ℝ)] : Measure (Eucl P)) A = ⨆ (δ : ℝ≥0∞) (_ : 0 < δ),
        OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ A := by
      rw [← Measure.toOuterMeasure_apply, Measure.hausdorffMeasure,
        Measure.mkMetric_toOuterMeasure, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
        OuterMeasure.iSup_apply]
      simp only [OuterMeasure.iSup_apply]
    rw [hHA, ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_le fun δ => ?_
    rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_le fun hδ => ?_
    obtain ⟨R, -, hR0, hRδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
    have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
    -- The fine family of closed balls `B̄ᵣ(x)`, `x ∈ A`, `r < R/10`, `M ωₙ rⁿ ≤ ν(B̄ᵣ(x))`.
    let B : Set (Eucl P × ℝ) := {b | b.1 ∈ A ∧ 0 < b.2 ∧ b.2 < R / 10 ∧
      (M : ℝ≥0∞) * (ω * ENNReal.ofReal b.2 ^ (n : ℝ)) ≤ ν (closedBall b.1 b.2)}
    have hfine : ∀ x ∈ A, ∃ r, (x, r) ∈ B := by
      intro x hx
      have hMx : (M : ℝ≥0∞) < dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x := by
        rw [hA, mem_ofPred_eq, not_lt_top_iff] at hx
        rw [hx]
        exact ENNReal.natCast_lt_top M
      obtain ⟨r, hqr, hr⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hMx).and_eventually
        (Ioo_mem_nhdsGT (show (0 : ℝ) < R / 10 by positivity))).exists
      have hnorm0 : ω * ENNReal.ofReal r ^ (n : ℝ) ≠ 0 :=
        mul_ne_zero hω0 (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr.1) ENNReal.ofReal_ne_top).ne'
      have hnormtop : ω * ENNReal.ofReal r ^ (n : ℝ) ≠ ∞ :=
        ENNReal.mul_ne_top hωtop
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
      rw [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient, hω, univ_inter,
        Measure.toOuterMeasure_apply] at hqr
      exact ⟨r, hx, hr.1, hr.2,
        ((ENNReal.lt_div_iff_mul_lt (Or.inl hnorm0) (Or.inl hnormtop)).mp hqr).le⟩
    -- The five-times covering lemma (Simon Ch. 1, 3.4) gives a disjoint subfamily `D`.
    obtain ⟨D, hDB, hdisj, hcover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall B Prod.fst Prod.snd
        (R / 10) (fun b hb => hb.2.2.1.le) 5 (by norm_num)
    have hdisj' : Pairwise (fun i j : D =>
        Disjoint (closedBall i.val.1 i.val.2) (closedBall j.val.1 j.val.2)) :=
      fun i j hij => hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
    have hpos : ∀ b : D, 0 < ν (closedBall b.val.1 b.val.2) := by
      intro b
      have hb := hDB b.property
      exact (pos_iff_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hM0.ne') (mul_ne_zero hω0
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hb.2.1) ENNReal.ofReal_ne_top).ne'))).trans_le
        hb.2.2.2
    have hcount := ν.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
      (fun b : D => measurableSet_closedBall) hdisj'
      (ne_top_of_le_ne_top hν.ne (measure_mono (subset_univ _)))
    have hDc : Countable D := countable_univ_iff.mp (by simpa only [hpos, ofPred_true] using hcount)
    -- Total weight of the disjoint family: `M ∑ ωₙ rⁿ ≤ ∑ ν(B̄ᵣ) ≤ ν(ℝ^P)`.
    have hsum : (M : ℝ≥0∞) * ∑' b : D, ω * ENNReal.ofReal b.val.2 ^ (n : ℝ) ≤ ν univ := by
      rw [← ENNReal.tsum_mul_left]
      calc
        ∑' b : D, (M : ℝ≥0∞) * (ω * ENNReal.ofReal b.val.2 ^ (n : ℝ)) ≤
            ∑' b : D, ν (closedBall b.val.1 b.val.2) :=
          ENNReal.tsum_le_tsum fun b => (hDB b.property).2.2.2
        _ = ν (⋃ b : D, closedBall b.val.1 b.val.2) :=
          (measure_iUnion hdisj' (fun _ => measurableSet_closedBall)).symm
        _ ≤ ν univ := measure_mono (subset_univ _)
    -- The five-times enlargements cover `A`.
    have hAcov : A ⊆ ⋃ b : D, closedBall b.val.1 (5 * b.val.2) := by
      intro x hx
      obtain ⟨r, hr⟩ := hfine x hx
      obtain ⟨b, hbD, hsub⟩ := hcover (x, r) hr
      exact mem_iUnion.mpr ⟨⟨b, hbD⟩, hsub (mem_closedBall_self hr.2.1.le)⟩
    set η := OuterMeasure.mkMetric'.pre (fun s : Set (Eucl P) => ediam s ^ (n : ℝ)) δ
    -- Cost of an enlarged ball at scale `δ`: its diameter is at most `10 r < δ`.
    have hlarge : ∀ b : D, η (closedBall b.val.1 (5 * b.val.2)) ≤
        10 ^ n * ENNReal.ofReal b.val.2 ^ (n : ℝ) := by
      intro b
      have hb := hDB b.property
      have hdiam : ediam (closedBall b.val.1 (5 * b.val.2)) ≤ ENNReal.ofReal (10 * b.val.2) :=
        ediam_le_of_forall_dist_le fun y hy z hz => by
          have hy' := mem_closedBall.mp hy
          have hz' := mem_closedBall.mp hz
          linarith [dist_triangle_right y z b.val.1]
      calc
        η (closedBall b.val.1 (5 * b.val.2)) ≤
            ediam (closedBall b.val.1 (5 * b.val.2)) ^ (n : ℝ) :=
          OuterMeasure.mkMetric'.pre_le (hdiam.trans
            ((ENNReal.ofReal_le_ofReal (by linarith [hb.2.2.1])).trans hRδ.le))
        _ ≤ ENNReal.ofReal (10 * b.val.2) ^ (n : ℝ) := by gcongr
        _ = 10 ^ n * ENNReal.ofReal b.val.2 ^ (n : ℝ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.rpow_natCast, ENNReal.ofReal_ofNat]
    calc
      (M : ℝ≥0∞) * (ω * η A) ≤
          (M : ℝ≥0∞) * (ω * ∑' b : D, 10 ^ n * ENNReal.ofReal b.val.2 ^ (n : ℝ)) := by
        gcongr
        calc
          η A ≤ η (⋃ b : D, closedBall b.val.1 (5 * b.val.2)) := measure_mono hAcov
          _ ≤ ∑' b : D, η (closedBall b.val.1 (5 * b.val.2)) := measure_iUnion_le _
          _ ≤ _ := ENNReal.tsum_le_tsum hlarge
      _ = 10 ^ n * ((M : ℝ≥0∞) * ∑' b : D, ω * ENNReal.ofReal b.val.2 ^ (n : ℝ)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        ring
      _ ≤ 10 ^ n * ν univ := by gcongr
  -- Hence `μHE[n](A) = 0`, as `μHE[n]` is a finite multiple of `μH[n]`.
  have hHE : (μHE[n] : Measure (Eucl P)) A = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Step 2: `Θ*ⁿ(ν, x) < ∞` for `μHE[n]`-a.e. `x`.
  have hae : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)),
      dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x < ∞ := by
    rw [ae_iff, ← hA]
    exact hHE
  filter_upwards [hae] with x hx
  -- Step 3: small radii, `q_x(r) < Θ*ⁿ(ν, x) + 1` on `(0, r₀)`.
  set b : ℝ≥0∞ := dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x + 1 with hb
  have hb_top : b ≠ ∞ := ENNReal.add_ne_top.2 ⟨hx.ne, ENNReal.one_ne_top⟩
  have hΘb : dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x < b :=
    ENNReal.lt_add_right hx.ne one_ne_zero
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient ν.toOuterMeasure (n : ℝ) univ x r
        < b :=
    eventually_lt_of_limsup_lt hΘb
  obtain ⟨r₀, hr₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  -- Steps 4–6: unpack the quotient bound, with the real constant `C = b ωₙ`.
  refine ⟨b.toReal * ω.toReal, r₀, hr₀, ?_⟩
  intro r hr
  have hq := hsub hr
  simp only [mem_ofPred_eq, Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient, univ_inter,
    Measure.coe_toOuterMeasure, hω] at hq
  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hr.1.le] at hq
  have hd0 : ω * ENNReal.ofReal (r ^ n) ≠ 0 :=
    mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hr.1 n)).ne'
  have hdtop : ω * ENNReal.ofReal (r ^ n) ≠ ∞ := ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  rw [ENNReal.div_lt_iff (Or.inl hd0) (Or.inl hdtop)] at hq
  rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb_top,
    ENNReal.ofReal_toReal hωtop, mul_assoc]
  exact hq

/-- **Subsequential mass density bound** (the bound behind "(8) remains valid with `T_{j′}`" in
the proof of Simon Ch. 6, 8.2, p. 178).  If `sup_j M(T_j) < ∞`, then along a subsequence
`T_{φ(j)}`, for `Hⁿ`-a.e. `x` there are `C` and `r₀ > 0` with `M_{B_r(x)}(T_{φ(j)}) ≤ C rⁿ` for
every `r ∈ (0, r₀)` and all large `j`.  The mass measures `μ_j` of the `T_j` have a diagonal
subsequence whose closed-set limsups on every `B̄_R(0)` are bounded by finite measures `ν_R`
(Simon Ch. 1, 4.16), and `ν_R(B̄_r(x)) < C rⁿ` for small `r` at `Hⁿ`-a.e. `x` (Ch. 1, 3.3). -/
theorem Submission.ind_mass_density_bound : ∀ (P n : ℕ) (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) n), (⨆ j, (Tj j).mass) < ∞ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ᶠ j in atTop, (Tj (φ j)).massOn (ball x r) ≤ ENNReal.ofReal (C * r ^ n) := by
  intro P n Tj hTj
  -- Step 1: mass measures `μ j` with `μ j (B_r(x)) = M_{B_r(x)}(T_j)` and `μ j ℝ^P ≤ M(T_j)`.
  choose μ hμ_univ hμ_ball using fun j => Submission.ind_md_mass_measure_balls P n (Tj j)
    ((le_iSup (fun j => (Tj j).mass) j).trans_lt hTj)
  -- Steps 2–3: diagonal subsequence `φ` with `limsup_j μ_{φ j}(F) ≤ ν_R(F)`, `F ⊆ B̄_R(0)` closed.
  obtain ⟨φ, ν, hφ, hν_fin, hν⟩ :=
    Submission.ind_md_diagonal_weak_subseq P μ ((iSup_mono hμ_univ).trans_lt hTj)
  refine ⟨φ, hφ, ?_⟩
  -- Step 4: off one `Hⁿ`-null set, every `ν R` has `n`-dimensional growth on small closed balls.
  have hgrowth : ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), ∀ R : ℕ, ∃ C r₀ : ℝ, 0 < r₀ ∧
      ∀ r ∈ Ioo (0 : ℝ) r₀, ν R (closedBall x r) < ENNReal.ofReal (C * r ^ n) :=
    ae_all_iff.2 fun R => Submission.ind_md_ae_closedBall_growth P n (ν R) (hν_fin R)
  filter_upwards [hgrowth] with x hx
  -- Step 5: with `R = ⌈‖x‖⌉₊ + 1` and `r < 1`, `B̄_r(x) ⊆ B̄_R(0)`.
  obtain ⟨C, r₁, hr₁, hC⟩ := hx (⌈‖x‖⌉₊ + 1)
  refine ⟨C, min r₁ 1, lt_min hr₁ one_pos, fun r hr => ?_⟩
  have hsub : closedBall x r ⊆ closedBall (0 : Eucl P) ((⌈‖x‖⌉₊ + 1 : ℕ) : ℝ) := by
    refine closedBall_subset_closedBall' ?_
    have hx_le : ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil ‖x‖
    have hr_lt : r < 1 := hr.2.trans_le (min_le_right r₁ 1)
    rw [dist_zero_right]
    push_cast
    linarith
  have hlt : limsup (fun j => μ (φ j) (closedBall x r)) atTop < ENNReal.ofReal (C * r ^ n) :=
    (hν _ _ isClosed_closedBall hsub).trans_lt (hC r ⟨hr.1, hr.2.trans_le (min_le_left r₁ 1)⟩)
  filter_upwards [eventually_lt_of_limsup_lt hlt] with j hj
  rw [← hμ_ball]
  exact (measure_mono ball_subset_closedBall).trans hj.le
/-- Simon Ch. 6, proof of 8.2 (the blow-up step): if `Q` is the weighted approximate tangent
space of `(M, θ)` at `x` (Ch. 3, 1.7), then for every continuous compactly supported `f`,
`(rⁿ)⁻¹ ∫_M θ(y) f(r⁻¹(y − x)) dHⁿ(y) → θ(x) ∫_Q f dHⁿ` as `r ↓ 0`.  The change of variables
`z = η_{x,r}(y) = r⁻¹(y − x)` turns the left side into the blow-up integral
`∫_{η_{x,r}(M)} f(z) θ(x + r z) dHⁿ(z)` of the tangent condition. -/
theorem Submission.ind_ab_rescaled_tangent_limit :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)) (f : Eucl P → ℝ), HasWeightedApproximateTangentSpaceAt n M θ x Q → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in M, θ y * f (r⁻¹ • (y - x)) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), f z ∂(μHE[n] : Measure (Eucl P)))) := by
  intro P n M θ x Q f hQ hf hfc
  -- The tangent condition, tested with `f ∈ C_c(ℝ^P)`; both sides agree for every `r > 0`.
  refine (hQ.2 ⟨⟨f, hf⟩, hfc⟩).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  -- `η = blowUpMap x r`, `η y = r⁻¹ • (y - x)`, is a homeomorphism of `ℝ^P`.
  let e : Eucl P ≃ₜ Eucl P :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl P → Eucl P) = Poincare.SimonGMT.Chapter03.blowUpMap x r := by
    funext y
    simp [e, Poincare.SimonGMT.Chapter03.blowUpMap, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (Poincare.SimonGMT.Chapter03.blowUpMap x r) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = x + r • B`.
  have hmp : MeasurePreserving (Poincare.SimonGMT.Chapter03.blowUpMap x r)
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) μHE[n] := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : Poincare.SimonGMT.Chapter03.blowUpMap x r ⁻¹' B =
        (fun z => x + z) '' ((fun z => r • z) '' B) := by
      ext y
      simp only [mem_preimage, mem_image, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · intro hy
        exact ⟨r • r⁻¹ • (y - x), ⟨r⁻¹ • (y - x), hy, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  -- Change of variables: `∫_{η(M)} g dHⁿ = (rⁿ)⁻¹ ∫_M g ∘ η dHⁿ`.
  rw [hmp.setIntegral_image_emb hemb _ M, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  -- `x + r • η y = y`.
  have hy : x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r y = y := by
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hr.ne', add_sub_cancel]
  simp only [hy]
  exact mul_comm _ _
/-- `Hⁿ` scaling law for the dilation `η(y) = r⁻¹(y − x)`, `r > 0`: `η` is a measurable
embedding and pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, i.e. `Hⁿ(η⁻¹(B)) = rⁿ Hⁿ(B)`. -/
theorem Submission.ind_rs_dilation_measurePreserving :
    ∀ (P n : ℕ) (x : Eucl P) (r : ℝ), 0 < r →
      MeasurableEmbedding (fun y : Eucl P => r⁻¹ • (y - x)) ∧
        MeasurePreserving (fun y : Eucl P => r⁻¹ • (y - x))
          (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P)))
          (μHE[n] : Measure (Eucl P)) := by
  intro P n x r hr
  -- `η` is a homeomorphism of `ℝ^P`: translation by `-x`, then dilation by `r⁻¹`.
  let e : Eucl P ≃ₜ Eucl P :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl P → Eucl P) = fun y : Eucl P => r⁻¹ • (y - x) := by
    funext y
    simp [e, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (fun y : Eucl P => r⁻¹ • (y - x)) :=
    he ▸ e.measurableEmbedding
  refine ⟨hemb, hemb.measurable, ?_⟩
  -- `η⁻¹(B) = x + r • B`, and `Hⁿ(x + r • B) = ‖r‖₊ⁿ Hⁿ(B)`.
  ext B hB
  rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
  have hpre : (fun y : Eucl P => r⁻¹ • (y - x)) ⁻¹' B =
      (fun z => x + z) '' ((fun z => r • z) '' B) := by
    ext y
    simp only [mem_preimage, mem_image]
    constructor
    · intro hy
      exact ⟨r • r⁻¹ • (y - x), ⟨r⁻¹ • (y - x), hy, rfl⟩, by
        rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
    · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
      rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
  rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
    Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
    smul_eq_mul, ← mul_assoc]
  have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
      coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
      ENNReal.ofReal_one]
  rw [hc, one_mul]

/-- `τ(M, θ, ξ)` tested against `(rⁿ)⁻¹ ω ∘ η`, `η(y) = r⁻¹(y − x)`, `r > 0`, equals
`τ(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` tested against `ω`: `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ` and
`ξ(y)` is linear. -/
theorem Submission.ind_rs_tauAction_dilation :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
      (x : Eucl P) (r : ℝ) (ω : DifferentialForm (Eucl P) n), 0 < r →
      tauAction n M θ ξ (fun y => (r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) =
        tauAction n ((fun y => r⁻¹ • (y - x)) '' M) (fun z => θ (x + r • z))
          (fun z => ξ (x + r • z)) ω := by
  intro P n M θ ξ x r ω hr
  -- `η(y) = r⁻¹ • (y - x)` is a homeomorphism of `ℝ^P`, hence a measurable embedding.
  let e : Eucl P ≃ₜ Eucl P :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Eucl P → Eucl P) = fun y : Eucl P => r⁻¹ • (y - x) := by
    funext y
    simp [e, sub_eq_add_neg]
  have hemb : MeasurableEmbedding (fun y : Eucl P => r⁻¹ • (y - x)) :=
    he ▸ e.measurableEmbedding
  -- `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`: `η⁻¹(B) = x + r • B`.
  have hmp : MeasurePreserving (fun y : Eucl P => r⁻¹ • (y - x))
      (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) (μHE[n] : Measure (Eucl P)) := by
    refine ⟨hemb.measurable, ?_⟩
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, Measure.smul_apply]
    have hpre : (fun y : Eucl P => r⁻¹ • (y - x)) ⁻¹' B =
        (fun z => x + z) '' ((fun z => r • z) '' B) := by
      ext y
      simp only [mem_preimage, mem_image]
      constructor
      · intro hy
        exact ⟨r • r⁻¹ • (y - x), ⟨r⁻¹ • (y - x), hy, rfl⟩, by
          rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
      · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
        rwa [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    rw [hpre, Isometry.euclideanHausdorffMeasure_image (isometry_add_left x), Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n hr.ne' B, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    have hc : ENNReal.ofReal ((r ^ n)⁻¹) * ((‖r‖₊ ^ n : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), NNReal.coe_pow,
        coe_nnnorm, Real.norm_of_nonneg hr.le, inv_mul_cancel₀ (pow_ne_zero n hr.ne'),
        ENNReal.ofReal_one]
    rw [hc, one_mul]
  -- Change variables on the right; on the left, pull `(rⁿ)⁻¹` out of the linear `ξ(y)`.
  simp only [tauAction]
  rw [hmp.setIntegral_image_emb hemb (fun z => θ (x + r • z) * ξ (x + r • z) (ω z)) M,
    Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, ← integral_const_mul]
  congr 1
  funext y
  simp only [smul_inv_smul₀ hr.ne', add_sub_cancel, map_smul, smul_eq_mul]
  ring

/-- Weighted ball growth at a point with a weighted approximate tangent space `Q`:
`∫_{M ∩ B̄_s(x)} θ dHⁿ ≤ C sⁿ` for all small `s > 0`.  Test the rescaled tangent limit
`(sⁿ)⁻¹ ∫_M θ(y) f₀(s⁻¹(y − x)) dHⁿ(y) → θ(x) ∫_Q f₀ dHⁿ` against the bump
`f₀(z) = max(0, min(1, 2 − ‖z‖))`, which is `1` on `B̄_1(0)` and `0` off `B̄_2(0)`. -/
theorem Submission.ind_ab_weighted_ball_growth :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)),
      NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) →
      (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))) →
      HasWeightedApproximateTangentSpaceAt n M θ x Q →
      ∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤
          C * ENNReal.ofReal (s ^ n) := by
  intro P n M θ x Q hM hθ hint hQ
  -- The bump `f₀`: continuous, `0 ≤ f₀ ≤ 1`, `f₀ = 1` on `B̄_1(0)`, `f₀ = 0` off `B̄_2(0)`.
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Eucl P → ℝ, f₀ = fun z => max 0 (min 1 (2 - ‖z‖)) := ⟨_, rfl⟩
  have hf₀c : Continuous f₀ := by
    rw [hf₀]
    exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hf₀nn : ∀ z, 0 ≤ f₀ z := fun z => by rw [hf₀]; exact le_max_left _ _
  have hf₀le : ∀ z, f₀ z ≤ 1 := fun z => by
    rw [hf₀]; exact max_le zero_le_one (min_le_left _ _)
  have hf₀one : ∀ z : Eucl P, ‖z‖ ≤ 1 → f₀ z = 1 := by
    intro z hz
    rw [hf₀]
    simp only
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hf₀zero : ∀ z : Eucl P, 2 < ‖z‖ → f₀ z = 0 := by
    intro z hz
    rw [hf₀]
    simp only
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  have hf₀cs : HasCompactSupport f₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) 2) (fun z hz => ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hf₀zero z hz
  -- `I(s) = (sⁿ)⁻¹ ∫_M θ(y) f₀(s⁻¹(y − x)) dHⁿ(y) → L`, so eventually `I(s) ≤ L + 1`.
  have hlim := Submission.ind_ab_rescaled_tangent_limit P n M θ x Q f₀ hQ hf₀c hf₀cs
  obtain ⟨L, hL⟩ : ∃ L : ℝ,
      L = θ x * ∫ z in (Q : Set (Eucl P)), f₀ z ∂(μHE[n] : Measure (Eucl P)) := ⟨_, rfl⟩
  rw [← hL] at hlim
  have hev := hlim.eventually (ge_mem_nhds (lt_add_one L))
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hspos
  have hs0 : 0 < s := hspos
  -- `g_s(y) = θ(y) f₀(s⁻¹(y − x))` is integrable on `M ∩ B̄_{2s}(x)` and vanishes off it.
  have hgint : IntegrableOn (fun y => θ y * f₀ (s⁻¹ • (y - x))) M (μHE[n] : Measure (Eucl P)) := by
    have h1 : IntegrableOn (fun y => θ y * f₀ (s⁻¹ • (y - x))) (M ∩ closedBall x (2 * s))
        (μHE[n] : Measure (Eucl P)) := by
      refine Integrable.mul_bdd (c := 1) (hint _ (isCompact_closedBall x (2 * s))) ?_ ?_
      · exact (hf₀c.comp
          (by fun_prop : Continuous fun y : Eucl P => s⁻¹ • (y - x))).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (hf₀nn _)]; exact hf₀le _
    refine h1.of_ae_sdiff_eq_zero hM (Eventually.of_forall fun y hy => ?_)
    have hy2 : y ∉ closedBall x (2 * s) := fun h => hy.2 ⟨hy.1, h⟩
    rw [mem_closedBall, not_le, dist_eq_norm] at hy2
    have h2 : 2 < ‖s⁻¹ • (y - x)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), lt_inv_mul_iff₀ hs0]
      linarith
    show θ y * f₀ (s⁻¹ • (y - x)) = 0
    rw [hf₀zero _ h2, mul_zero]
  have hgnn : 0 ≤ᵐ[(μHE[n] : Measure (Eucl P)).restrict M] fun y => θ y * f₀ (s⁻¹ • (y - x)) := by
    filter_upwards [ae_restrict_mem₀ hM] with y hy
    exact mul_nonneg (hθ y hy) (hf₀nn _)
  have hball : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ closedBall x s)),
      y ∈ closedBall x s :=
    ae_mono (Measure.restrict_mono inter_subset_right le_rfl)
      (ae_restrict_mem measurableSet_closedBall)
  -- On `B̄_s(x)`, `g_s = θ`; so the ball integral is at most `∫_M g_s = sⁿ I(s) ≤ sⁿ (L + 1)`.
  calc ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P))
      = ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y * f₀ (s⁻¹ • (y - x)))
          ∂(μHE[n] : Measure (Eucl P)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hball] with y hy
        rw [mem_closedBall, dist_eq_norm] at hy
        have h1 : ‖s⁻¹ • (y - x)‖ ≤ 1 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs0.le), inv_mul_le_iff₀ hs0]
          linarith
        rw [hf₀one _ h1, mul_one]
    _ ≤ ∫⁻ y in M, ENNReal.ofReal (θ y * f₀ (s⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P)) :=
        lintegral_mono' (Measure.restrict_mono inter_subset_left le_rfl) le_rfl
    _ = ENNReal.ofReal (∫ y in M, θ y * f₀ (s⁻¹ • (y - x)) ∂(μHE[n] : Measure (Eucl P))) :=
        (ofReal_integral_eq_lintegral_ofReal hgint hgnn).symm
    _ ≤ ENNReal.ofReal (s ^ n * (L + 1)) :=
        ENNReal.ofReal_le_ofReal ((inv_mul_le_iff₀ (pow_pos hs0 n)).1 hs)
    _ = (Real.toNNReal (L + 1) : ℝ≥0∞) * ENNReal.ofReal (s ^ n) := by
        rw [ENNReal.ofReal_mul (pow_nonneg hs0.le n), mul_comm]
        rfl
/-- Weighted Lebesgue points of the orientation of a rectifiable triple (Simon Ch. 1, 3.23 with
3.11(3); Steps 1–3 of the proof of Ch. 6, 8.2).  For `Hⁿ⌞M`-a.e. `x`,
`(∫_{M ∩ B̄_s(x)} θ(y) ‖ξ(y) − ξ(x)‖ dHⁿ(y)) / (∫_{M ∩ B̄_s(x)} θ dHⁿ) → 0` as `s ↓ 0`
(`ℝ≥0∞`-valued).  With `λ = (Hⁿ⌞M) ⌞ θ`, `λ(B̄_s(x))` is the denominator, `λ` is locally finite
and mutually absolutely continuous with `Hⁿ⌞M` (`θ > 0` on `M`), and `ξ` is locally
`λ`-integrable as `‖ξ‖ ≤ 1` a.e.; the claim is Lebesgue differentiation of `ξ` with respect to
`λ` along the Besicovitch Vitali family of closed balls. -/
theorem Submission.ind_ab_weighted_lebesgue_point :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) := by
  intro P n M θ ξ h
  -- Step 1: `‖ξ‖ ≤ 1` a.e. on `M`, since `|α(τ)| ≤ ‖α‖ ∏ ‖τᵢ‖ = ‖α‖` for orthonormal `τ`.
  have hunit : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ y‖ ≤ 1 := by
    filter_upwards [h.orients] with y hy
    obtain ⟨τ, hτ, -, hξ⟩ := hy
    have hs : ∀ α : Covector (Eucl P) n, |α τ| ≤ ‖α‖ := by
      intro α
      have h1 := ContinuousAlternatingMap.le_opNorm α τ
      have h2 : ∏ i, ‖τ i‖ = 1 := by simp [hτ.1]
      simpa [h2] using h1
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun α => ?_)
    rw [one_mul]
    rcases hξ with hξ | hξ
    · rw [hξ, simpleNVector_apply, Real.norm_eq_abs]; exact hs α
    · rw [hξ, neg_apply, simpleNVector_apply, norm_neg, Real.norm_eq_abs]
      exact hs α
  -- Step 2: `θ` is a.e.-strongly measurable for `Hⁿ⌞M`, being integrable on each `M ∩ B̄_k(0)`.
  have hθm : AEStronglyMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ k : ℕ, M ∩ closedBall (0 : Eucl P) k := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_ge ‖y‖
        exact ⟨k, hy, hk⟩
      · rintro ⟨k, hy, -⟩
        exact hy
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro k
    exact (h.integrableOn _ (isCompact_closedBall 0 k) (subset_univ _)).aestronglyMeasurable
  have hwm : AEMeasurable (fun y => ENNReal.ofReal (θ y)) ((μHE[n] : Measure (Eucl P)).restrict M) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hθm.aemeasurable
  -- Step 3: the weighted measure `λ = (Hⁿ⌞M) ⌞ θ`, finite on closed balls.
  obtain ⟨lam, hlam⟩ : ∃ lam : Measure (Eucl P),
      lam = ((μHE[n] : Measure (Eucl P)).restrict M).withDensity (fun y => ENNReal.ofReal (θ y)) :=
    ⟨_, rfl⟩
  have hball : ∀ (z : Eucl P) (s : ℝ), lam (closedBall z s) =
      ∫⁻ y in M ∩ closedBall z s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) := by
    intro z s
    rw [hlam, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
  have hfin : ∀ (z : Eucl P) (s : ℝ), lam (closedBall z s) < ⊤ := by
    intro z s
    rw [hball]
    exact (h.integrableOn _ (isCompact_closedBall z s) (subset_univ _)).lintegral_lt_top
  have : IsLocallyFiniteMeasure lam :=
    ⟨fun z => ⟨closedBall z 1, closedBall_mem_nhds z one_pos, hfin z 1⟩⟩
  -- Step 4: `λ ≪ Hⁿ⌞M`, and `Hⁿ⌞M ≪ λ` since `θ > 0` on `M`.
  have hac1 : lam ≪ (μHE[n] : Measure (Eucl P)).restrict M := by
    rw [hlam]; exact withDensity_absolutelyContinuous _ _
  have hac2 : (μHE[n] : Measure (Eucl P)).restrict M ≪ lam := by
    rw [hlam]
    refine withDensity_absolutelyContinuous' hwm ?_
    filter_upwards [ae_restrict_mem₀ h.nullMeasurableSet] with y hy
    exact (ENNReal.ofReal_pos.2 (h.pos y hy)).ne'
  -- Steps 5–6: `ξ` is locally `λ`-integrable; Lebesgue–Besicovitch differentiation.
  have hdiff := VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (E := NVector (Eucl P) n)
    (Besicovitch.vitaliFamily lam) (f := ξ) (by
      intro z
      refine ⟨closedBall z 1, closedBall_mem_nhds z one_pos, ?_⟩
      refine Measure.integrableOn_of_bounded (M := 1) (hfin z 1).ne ?_ ?_
      · exact h.aestronglyMeasurable.mono_ac hac1
      · exact ae_restrict_of_ae (hac1.ae_le hunit))
  filter_upwards [hac2.ae_le hdiff] with x hx
  have hx' := hx.comp (Besicovitch.tendsto_filterAt lam x)
  -- Step 7: the `λ`-quotient over `B̄_s(x)` is the weighted `Hⁿ`-quotient over `M ∩ B̄_s(x)`.
  refine hx'.congr (fun s => ?_)
  simp only [Function.comp]
  rw [hball x s]
  congr 1
  rw [hlam, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hwm.restrict _
      measurableSet_closedBall (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict measurableSet_closedBall, inter_comm]
  rfl
/-- The orientation error term of the blow-up (Simon Ch. 6, proof of 8.2): write
`b(s) = ∫⁻_{M ∩ B̄_s(x)} θ dHⁿ` and `a(s) = ∫⁻_{M ∩ B̄_s(x)} θ ‖ξ - ξ(x)‖ₑ dHⁿ`.  If
`b(s) ≤ C sⁿ` for small `s > 0` and `a(s) / b(s) → 0`, then for every continuous compactly
supported `ω`, `∫_M θ(y) (ξ(y) - ξ(x))(r⁻ⁿ ω(r⁻¹(y - x))) dHⁿ(y) → 0` as `r → 0⁺`.
With `tsupport ω ⊆ B̄_R(0)` and `‖ω‖ ≤ B`, the integral has extended norm at most
`B Rⁿ · a(R r) / (R r)ⁿ`, and `a(s) / sⁿ ≤ C · a(s) / b(s) → 0`. -/
theorem Submission.ind_ab_orientation_error_vanishes :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (x : Eucl P) (ω : Eucl P → Covector (Eucl P) n), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → Continuous ω → HasCompactSupport ω → (∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤ C * ENNReal.ofReal (s ^ n)) → Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
  intro P n M θ ξ x ω hM hθ hω hωc hgrowth hratio
  obtain ⟨C, hC⟩ := hgrowth
  -- An estimate in `[0, ∞]`: if `0 < d < ∞`, `b ≤ c d` and `a / b < 1`, then `a / d ≤ c (a / b)`.
  have key : ∀ (a b d : ℝ≥0∞) (c : ℝ≥0), d ≠ 0 → d ≠ ⊤ → b ≤ c * d → a / b < 1 →
      a / d ≤ c * (a / b) := by
    intro a b d c hd0 hdtop hbd hab
    rw [ENNReal.div_le_iff hd0 hdtop]
    by_cases hb0 : b = 0
    · have ha0 : a = 0 := by
        by_contra hne
        rw [hb0, ENNReal.div_zero hne] at hab
        exact absurd hab (not_lt.2 le_top)
      rw [ha0]; exact zero_le
    · have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hdtop) hbd
      calc a = (a / b) * b := (ENNReal.div_mul_cancel hb0 hbtop).symm
        _ ≤ (a / b) * ((c : ℝ≥0∞) * d) := by gcongr
        _ = (c : ℝ≥0∞) * (a / b) * d := by ring
  -- The normalized error `a(s) / sⁿ` tends to `0`.
  have hε : Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s,
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / ENNReal.ofReal (s ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∫⁻ y in M ∩ closedBall x s,
        ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
          ENNReal.ofReal (s ^ n) ≤
        (C : ℝ≥0∞) * ((∫⁻ y in M ∩ closedBall x s,
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) := by
      filter_upwards [hC, hratio.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from zero_lt_one)),
        self_mem_nhdsWithin] with s hbs hrs hs
      have hs' : (0 : ℝ) < s := hs
      exact key _ _ _ C (ENNReal.ofReal_pos.2 (pow_pos hs' n)).ne' ENNReal.ofReal_ne_top hbs hrs
    have h2 := ENNReal.Tendsto.const_mul hratio (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun _ => zero_le) h1
  -- A radius `R > 0` with `tsupport ω ⊆ B̄_R(0)` and a bound `B` for `‖ω‖`.
  obtain ⟨R₀, hR₀⟩ := (hωc.isCompact.isBounded).subset_closedBall (0 : Eucl P)
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ tsupport ω ⊆ closedBall (0 : Eucl P) R :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos,
      hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨B, hB⟩ := hωc.exists_bound_of_continuous hω
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  -- For `r > 0` the integrand vanishes off `B̄_{Rr}(x)` and is bounded on `M` by
  -- `(rⁿ)⁻¹ B θ ‖ξ - ξ(x)‖`.
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal ((r ^ n)⁻¹ * B) *
          ∫⁻ y in M ∩ closedBall x (R * r), ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ
            ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hpt : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict M),
        ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ ≤
          (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y := by
      filter_upwards [ae_restrict_mem₀ hM] with y hy
      by_cases hyB : y ∈ closedBall x (R * r)
      · rw [indicator_of_mem hyB]
        have hcn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hr.le n)
        have hreal : ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ ≤
            ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by
          rw [norm_mul, Real.norm_of_nonneg (hθ y hy)]
          have hθy := hθ y hy
          calc θ y * ‖(ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖
              ≤ θ y * (‖ξ y - ξ x‖ * ‖(r ^ n)⁻¹ • ω (r⁻¹ • (y - x))‖) := by
                gcongr
                exact (ξ y - ξ x).le_opNorm _
            _ ≤ θ y * (‖ξ y - ξ x‖ * ((r ^ n)⁻¹ * B)) := by
                gcongr
                rw [norm_smul, Real.norm_of_nonneg hcn]
                gcongr
                exact hB _
            _ = ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by ring
        calc ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
            = ENNReal.ofReal ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ :=
              (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal (((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖)) := ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ) := by
              have he : ENNReal.ofReal ‖ξ y - ξ x‖ = ‖ξ y - ξ x‖ₑ :=
                ofReal_norm (E := NVector (Eucl P) n) _
              rw [ENNReal.ofReal_mul (mul_nonneg hcn hB0), ENNReal.ofReal_mul (hθ y hy), he]
      · rw [indicator_of_notMem hyB]
        have hω0 : ω (r⁻¹ • (y - x)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hyB
          have h1 := hRsub hmem
          rw [mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          linarith
        simp [hω0]
    calc ∫⁻ y in M, ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
          ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ y in M, (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y
            ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hpt
      _ = ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)
            ∂(μHE[n] : Measure (Eucl P)) := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Rewrite the bound as `B Rⁿ · a(R r) / (R r)ⁿ`.
  have hbound2 : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal (B * R ^ n) * ((∫⁻ y in M ∩ closedBall x (R * r),
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            ENNReal.ofReal ((R * r) ^ n)) := by
    intro r hr
    refine (hbound r hr).trans (le_of_eq ?_)
    have hRr : 0 < R * r := mul_pos hRpos hr
    have hd0 : ENNReal.ofReal ((R * r) ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hRr n)).ne'
    have hdt : ENNReal.ofReal ((R * r) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
    conv_lhs => rw [← ENNReal.div_mul_cancel hd0 hdt (b := ∫⁻ y in M ∩ closedBall x (R * r),
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)))]
    rw [mul_comm _ (ENNReal.ofReal ((R * r) ^ n)), ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) hB0)]
    congr 2
    rw [mul_pow]
    field_simp
  -- As `r → 0⁺`, `R r → 0⁺`, so the bound tends to `0`.
  have hcomp : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hRpos hr
  have hlim := ENNReal.Tendsto.const_mul (hε.comp hcomp)
    (Or.inr (ENNReal.ofReal_ne_top (r := B * R ^ n)))
  rw [mul_zero] at hlim
  rw [tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound2 r hr

/-- Blow-up of `τ(M, θ, ξ)` at a.e. point (Simon Ch. 6, proof of 8.2, display (7)): for
`Hⁿ`-a.e. `x ∈ M`, every weighted approximate tangent space `Q` of `(M, θ)` at `x` and every
continuous compactly supported `n`-form `ω`,
`τ(M, θ, ξ)(r⁻ⁿ ω ∘ η_{x,r}) → θ(x) ∫_Q ⟨ω, ξ(x)⟩ dHⁿ` as `r ↓ 0`, `η_{x,r}(y) = r⁻¹(y − x)`. -/
theorem Submission.ind_ae_blowup_limit :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
      IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ →
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P),
        HasWeightedApproximateTangentSpaceAt n M θ x Q →
        ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω →
          Tendsto (fun r : ℝ => tauAction n M θ ξ (fun y => (r ^ n)⁻¹ • ω (r⁻¹ • (y - x))))
            (𝓝[>] 0)
            (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), ξ x (ω z) ∂(μHE[n] : Measure (Eucl P)))) := by
  have htan := @Submission.ind_ab_rescaled_tangent_limit
  have hgrowth := @Submission.ind_ab_weighted_ball_growth
  have hleb := @Submission.ind_ab_weighted_lebesgue_point
  have herr := @Submission.ind_ab_orientation_error_vanishes
  intro P n M θ ξ hT
  have hθ0 : ∀ y ∈ M, 0 ≤ θ y := fun y hy => (hT.pos y hy).le
  have hθK : ∀ K : Set (Eucl P), IsCompact K →
      IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    fun K hK => hT.integrableOn K hK (subset_univ K)
  -- `‖ξ‖ ≤ 1` a.e. on `M`: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal.
  have hξ1 : ∀ᵐ y ∂(μHE[n] : Measure (Eucl P)).restrict M, ‖ξ y‖ ≤ 1 := by
    filter_upwards [hT.orients] with y hy
    obtain ⟨τ, hτ, -, hξy⟩ := hy
    have hs : ∀ α : Covector (Eucl P) n, ‖α τ‖ ≤ 1 * ‖α‖ := fun α => by
      rw [one_mul]
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
    rcases hξy with h | h
    · rw [h, simpleNVector_apply]
      exact hs α
    · rw [h, neg_apply, simpleNVector_apply, norm_neg]
      exact hs α
  filter_upwards [hleb P n M θ ξ hT] with x hx
  intro Q hQ ω hω hωc
  -- Growth `∫⁻_{M ∩ B̄_s(x)} θ ≤ C sⁿ`, and the orientation error `E(r) → 0`.
  have hC := hgrowth P n M θ x Q hT.nullMeasurableSet hθ0 hθK hQ
  have hE := herr P n M θ ξ x ω hT.nullMeasurableSet hθ0 hω hωc hC hx
  -- The main term `A(r)`, tested with `f = ⟨ω, ξ(x)⟩ ∈ C_c(ℝ^P)`.
  have hA := htan P n M θ x Q (fun z => ξ x (ω z)) hQ ((ξ x).continuous.comp hω)
    (hωc.comp_left (map_zero (ξ x)))
  have hlim := hA.add hE
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Set.mem_Ioi] at hr
  -- `τ(M, θ, ξ)(ω_r) = A(r) + E(r)` for `r > 0`, `ω_r(y) = r⁻ⁿ ω(r⁻¹(y − x))`.
  obtain ⟨B, hB⟩ := hω.bounded_above_of_compact_support hωc
  set c : ℝ := (r ^ n)⁻¹
  set K : Set (Eucl P) := (fun z => x + r • z) '' tsupport ω
  have hK : IsCompact K := hωc.isCompact.image (by fun_prop)
  have hzero : ∀ y ∉ K, ω (r⁻¹ • (y - x)) = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      hy ⟨r⁻¹ • (y - x), hmem, show x + r • r⁻¹ • (y - x) = y by
        rw [smul_inv_smul₀ hr.ne', add_sub_cancel]⟩
  have hbound : ∀ y, ‖c • ω (r⁻¹ • (y - x))‖ ≤ |c| * B := fun y => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg c)
  have hωr : Continuous fun y => c • ω (r⁻¹ • (y - x)) := by fun_prop
  have hIA : IntegrableOn (fun y => θ y * ξ x (c • ω (r⁻¹ • (y - x)))) M
      (μHE[n] : Measure (Eucl P)) := by
    refine IntegrableOn.of_ae_sdiff_eq_zero (s := M ∩ K) ?_ hT.nullMeasurableSet
      (Eventually.of_forall ?_)
    · refine (hθK K hK).mul_bdd (c := ‖ξ x‖ * (|c| * B)) ?_ (Eventually.of_forall fun y => ?_)
      · exact ((ξ x).continuous.comp hωr).aestronglyMeasurable
      · exact ((ξ x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))
    · rintro y ⟨hyM, hyMK⟩
      have hyK : y ∉ K := fun h => hyMK ⟨hyM, h⟩
      simp [hzero y hyK]
  have hIE : IntegrableOn (fun y => θ y * (ξ y - ξ x) (c • ω (r⁻¹ • (y - x)))) M
      (μHE[n] : Measure (Eucl P)) := by
    refine IntegrableOn.of_ae_sdiff_eq_zero (s := M ∩ K) ?_ hT.nullMeasurableSet
      (Eventually.of_forall ?_)
    · have hξK : ∀ᵐ y ∂(μHE[n] : Measure (Eucl P)).restrict (M ∩ K), ‖ξ y‖ ≤ 1 :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left hξ1
      have hξm : AEStronglyMeasurable (fun y => ξ y - ξ x)
          ((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)) :=
        (hT.aestronglyMeasurable.mono_set inter_subset_left).sub aestronglyMeasurable_const
      refine (hθK K hK).mul_bdd (c := (1 + ‖ξ x‖) * (|c| * B)) ?_ ?_
      · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hξm
          hωr.aestronglyMeasurable
      · filter_upwards [hξK] with y hy
        calc ‖(ξ y - ξ x) (c • ω (r⁻¹ • (y - x)))‖
            ≤ ‖ξ y - ξ x‖ * ‖c • ω (r⁻¹ • (y - x))‖ := (ξ y - ξ x).le_opNorm _
          _ ≤ (1 + ‖ξ x‖) * (|c| * B) := by
            refine mul_le_mul ?_ (hbound y) (norm_nonneg _) (by positivity)
            calc ‖ξ y - ξ x‖ ≤ ‖ξ y‖ + ‖ξ x‖ := norm_sub_le (ξ y) (ξ x)
              _ ≤ 1 + ‖ξ x‖ := by linarith
    · rintro y ⟨hyM, hyMK⟩
      have hyK : y ∉ K := fun h => hyMK ⟨hyM, h⟩
      simp [hzero y hyK]
  have hsplit : (fun y => θ y * ξ y (c • ω (r⁻¹ • (y - x)))) = fun y =>
      θ y * ξ x (c • ω (r⁻¹ • (y - x))) + θ y * (ξ y - ξ x) (c • ω (r⁻¹ • (y - x))) := by
    funext y
    rw [sub_apply]
    ring
  simp only [tauAction]
  rw [hsplit, integral_add hIA hIE, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_smul, smul_eq_mul]
  ring

/-- Weighted approximate tangent spaces (Simon Ch. 3, 1.7) are invariant under the dilation
`η(w) = r⁻¹(w − x)`, `r > 0`: if `Q` is the approximate tangent space of `(M, θ)` at `y`, it is
the approximate tangent space of `(η(M), θ ∘ η⁻¹)` at `η(y)`.  The blow-up of `η(M)` at `η(y)`
with ratio `s` is the blow-up of `M` at `y` with ratio `r s`, and `s ↦ r s` preserves `𝓝[>] 0`. -/
theorem Submission.ind_rs_weightedTangent_dilation :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x y : Eucl P) (r : ℝ)
      (Q : Submodule ℝ (Eucl P)), 0 < r → HasWeightedApproximateTangentSpaceAt n M θ y Q →
        HasWeightedApproximateTangentSpaceAt n ((fun w => r⁻¹ • (w - x)) '' M)
          (fun z => θ (x + r • z)) (r⁻¹ • (y - x)) Q := by
  intro P n M θ x y r Q hr hQ
  -- The new multiplicity at `η(y)` is `θ(y)`.
  have hval : θ (x + r • r⁻¹ • (y - x)) = θ y := by
    rw [smul_inv_smul₀ hr.ne', add_sub_cancel]
  -- Blow-ups of `η(M)` at `η(y)` are blow-ups of `M` at `y` with the ratio multiplied by `r`.
  have hset : ∀ s : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap (r⁻¹ • (y - x)) s '' ((fun w => r⁻¹ • (w - x)) '' M) =
        Poincare.SimonGMT.Chapter03.blowUpMap y (r * s) '' M := by
    intro s
    rw [Set.image_image]
    refine Set.image_congr fun w _ => ?_
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
    rw [← smul_sub, sub_sub_sub_cancel_right, smul_smul, mul_inv_rev]
  have hweight : ∀ (s : ℝ) (u : Eucl P),
      θ (x + r • (r⁻¹ • (y - x) + s • u)) = θ (y + (r * s) • u) := by
    intro s u
    rw [smul_add, smul_inv_smul₀ hr.ne', smul_smul, ← add_assoc, add_sub_cancel]
  -- `s ↦ r s` maps `𝓝[>] 0` to itself.
  have hlim : Tendsto (fun s : ℝ => r * s) (𝓝[>] 0) (𝓝[>] 0) := by
    have h0 : Tendsto (fun s : ℝ => r * s) (𝓝 0) (𝓝 (r * 0)) := (continuous_const_mul r).tendsto 0
    rw [mul_zero] at h0
    exact tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun s hs => mul_pos hr hs⟩
  refine ⟨hQ.1, fun f => ?_⟩
  show Tendsto _ _ (𝓝 (θ (x + r • r⁻¹ • (y - x)) * _))
  rw [hval]
  refine ((hQ.2 f).comp hlim).congr fun s => ?_
  simp only [Function.comp_apply, hset, hweight]

/-- Rectifiable triples are invariant under the dilations `η(y) = r⁻¹(y − x)`, `r > 0`:
`(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` is again a rectifiable triple, where `η⁻¹(z) = x + r z`.
`η` is a measurable embedding pushing `c Hⁿ`, `c = (rⁿ)⁻¹`, forward to `Hⁿ`, so
`Hⁿ(η(S)) = c Hⁿ(S)` for every `S` and `Hⁿ ⌞ η(M) = η_#(c Hⁿ ⌞ M)`; the weighted approximate
tangent spaces of `(η(M), θ ∘ η⁻¹)` at `η(y)` are those of `(M, θ)` at `y`. -/
theorem Submission.ind_rs_rectifiableTriple_dilation :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
      (x : Eucl P) (r : ℝ), 0 < r → IsRectifiableTriple (univ : Set (Eucl P)) n M θ ξ →
      IsRectifiableTriple (univ : Set (Eucl P)) n ((fun y => r⁻¹ • (y - x)) '' M)
        (fun z => θ (x + r • z)) (fun z => ξ (x + r • z)) := by
  intro P n M θ ξ x r hr hT
  obtain ⟨hemb, hmp⟩ := Submission.ind_rs_dilation_measurePreserving P n x r hr
  set η : Eucl P → Eucl P := fun y => r⁻¹ • (y - x)
  set c : ℝ≥0∞ := ENNReal.ofReal ((r ^ n)⁻¹)
  -- `x + r • η(y) = y`, so `θ(x + r • ·) ∘ η = θ` and `ξ(x + r • ·) ∘ η = ξ`.
  have hinv : ∀ y, x + r • η y = y := fun y => by
    show x + r • r⁻¹ • (y - x) = y
    rw [smul_inv_smul₀ hr.ne', add_sub_cancel]
  -- `Hⁿ(η(S)) = c Hⁿ(S)` for every `S`; in particular `η` maps `Hⁿ`-null sets to null sets.
  have hnull : ∀ S : Set (Eucl P), (μHE[n] : Measure (Eucl P)) S = 0 →
      (μHE[n] : Measure (Eucl P)) (η '' S) = 0 := by
    intro S hS
    rw [← hmp.map_eq, hemb.map_apply, preimage_image_eq _ hemb.injective, Measure.smul_apply, hS,
      smul_zero]
  -- `Hⁿ ⌞ η(M) = η_#(c Hⁿ ⌞ M)`.
  have hres : MeasurePreserving η (c • (μHE[n] : Measure (Eucl P)).restrict M)
      ((μHE[n] : Measure (Eucl P)).restrict (η '' M)) := by
    rw [← Measure.restrict_smul]
    exact hmp.restrict_image_emb hemb M
  refine ⟨subset_univ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `η(M) =ᵐ η(B)` for the measurable hull `B` of `M`.
    have hB := hT.nullMeasurableSet.toMeasurable_ae_eq
    rw [ae_eq_set] at hB
    refine (hemb.measurableSet_image.2
      (measurableSet_toMeasurable (μHE[n] : Measure (Eucl P)) M)).nullMeasurableSet.congr ?_
    rw [ae_eq_set, ← image_sdiff hemb.injective, ← image_sdiff hemb.injective]
    exact ⟨hnull _ hB.1, hnull _ hB.2⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `η` Lipschitz.
    obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hT.countablyRectifiable
    have hηL : LipschitzWith ‖r⁻¹‖₊ η := LipschitzWith.of_dist_le_mul fun a b => by
      show dist (r⁻¹ • (a - x)) (r⁻¹ • (b - x)) ≤ ‖r⁻¹‖₊ * dist a b
      rw [dist_smul₀, dist_sub_right, coe_nnnorm]
    refine ⟨η '' M₀, hnull M₀ hM₀, fun j => η ∘ F j, fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨‖r⁻¹‖₊ * K, hηL.comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hMF hy with hy₀ | hy₁
      · exact Or.inl (mem_image_of_mem η hy₀)
      · obtain ⟨j, w, rfl⟩ := mem_iUnion.1 hy₁
        exact Or.inr (mem_iUnion.2 ⟨j, w, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < θ (x + r • η y)
    rw [hinv]
    exact hT.pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))` with `η⁻¹(K)` compact, and `η_#(c Hⁿ) = Hⁿ`.
    intro K hK _
    let e : Eucl P ≃ₜ Eucl P :=
      (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
    have he : (e : Eucl P → Eucl P) = η := by
      funext y
      simp [e, η, sub_eq_add_neg]
    have hK' : IsCompact (η ⁻¹' K) := by
      rw [← he]
      exact e.isCompact_preimage.2 hK
    have hθ : (fun z => θ (x + r • z)) ∘ η = θ := funext fun y => by
      simp only [Function.comp_apply, hinv]
    rw [← image_inter_preimage, hmp.integrableOn_image hemb, hθ, IntegrableOn,
      Measure.restrict_smul]
    exact Integrable.smul_measure (hT.integrableOn _ hK' (subset_univ _)) ENNReal.ofReal_ne_top
  · have hξ : (fun z => ξ (x + r • z)) ∘ η = ξ := funext fun y => by
      simp only [Function.comp_apply, hinv]
    rw [← hres.map_eq, hemb.aestronglyMeasurable_map_iff, hξ]
    exact hT.aestronglyMeasurable.smul_measure c
  · -- At `η(y)` the frame `τ` of `(M, θ, ξ)` at `y` still orients `(η(M), θ', ξ')`.
    rw [← hres.map_eq, hemb.ae_map_iff]
    filter_upwards [Measure.ae_smul_measure hT.orients c] with y hy
    obtain ⟨τ, hτ, htan, hξy⟩ := hy
    refine ⟨τ, hτ, Submission.ind_rs_weightedTangent_dilation P n M θ x y r _ hr htan, ?_⟩
    show ξ (x + r • η y) = _ ∨ ξ (x + r • η y) = _
    rw [hinv]
    exact hξy

/-- Mass bound for a current `Y` obtained from `X` by pull-back along the dilation
`φ(y) = r⁻¹(y − x)`, `r > 0`: if every test form `ω` has a test form `η = (rⁿ)⁻¹ ω ∘ φ` and
`Y ω = X η` for all such pairs, then `M_W(Y) ≤ (rⁿ)⁻¹ M_{φ⁻¹(W)}(X)` for every `W`, since
`rⁿ η = ω ∘ φ` is admissible for `M_{φ⁻¹(W)}(X)` whenever `ω` is admissible for `M_W(Y)`. -/
theorem Submission.ind_rs_massOn_dilation_le :
    ∀ (P n : ℕ) (X Y : GeometricCurrentOn (univ : Set (Eucl P)) n) (x : Eucl P) (r : ℝ), 0 < r →
      (∀ ω : TestFormOn (univ : Set (Eucl P)) n, ∃ η : TestFormOn (univ : Set (Eucl P)) n,
        ∀ y, (η : DifferentialForm (Eucl P) n) y =
          (r ^ n)⁻¹ • (ω : DifferentialForm (Eucl P) n) (r⁻¹ • (y - x))) →
      (∀ ω η : TestFormOn (univ : Set (Eucl P)) n,
        (∀ y, (η : DifferentialForm (Eucl P) n) y =
          (r ^ n)⁻¹ • (ω : DifferentialForm (Eucl P) n) (r⁻¹ • (y - x))) → Y ω = X η) →
      ∀ W : Set (Eucl P),
        Y.massOn W ≤ ENNReal.ofReal ((r ^ n)⁻¹) * X.massOn {y | r⁻¹ • (y - x) ∈ W} := by
  intro P n X Y x r hr hA hB W
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
  apply sSup_le
  rintro _ ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (Y ω) ≤ _
  obtain ⟨η, hη⟩ := hA ω
  -- `rⁿ η = ω ∘ φ` with `φ y = r⁻¹ • (y - x)`.
  have hcomp : (((r ^ n) • η : TestFormOn (univ : Set (Eucl P)) n) :
      DifferentialForm (Eucl P) n) =
        (ω : DifferentialForm (Eucl P) n) ∘ fun y : Eucl P => r⁻¹ • (y - x) := by
    funext y
    rw [Submodule.coe_smul, Pi.smul_apply, hη y, smul_smul, mul_inv_cancel₀ hrn, one_smul,
      Function.comp_apply]
  -- `rⁿ η` is admissible for `M_{φ⁻¹(W)}(X)`.
  have hadm : (r ^ n) • η ∈ massAdmissibleOn univ n {y | r⁻¹ • (y - x) ∈ W} := by
    refine ⟨?_, fun y => ?_⟩
    · rw [hcomp]
      exact (tsupport_comp_subset_preimage _ (by fun_prop)).trans (preimage_mono hω.1)
    · rw [hcomp]
      exact hω.2 _
  -- `Y ω = X η = (rⁿ)⁻¹ X (rⁿ η)`.
  have hY : Y ω = (r ^ n)⁻¹ * X ((r ^ n) • η) := by
    rw [hB ω η hη, map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hrn, one_mul]
  rw [hY, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le n))]
  exact mul_le_mul_right (X.le_massOn hadm) _

/-- Rescaling about `x` by `r > 0`: `Y = η_# X` for the dilation `η(y) = r⁻¹(y − x)`, the
push-forward along the proper affine map `η = b + L` with `L = r⁻¹ • id`, `b = −(r⁻¹ • x)`
(`GeometricCurrentOn.affinePushforward`).  The pull-back of `ω` is `η^# ω = r⁻ⁿ ω ∘ η`, so
`Y(ω) = X(η^# ω)`; `∂Y = η_#(∂X)`; `Y = τ(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` if `X = τ(M, θ, ξ)`; and
`M_W(Y) ≤ r⁻ⁿ M_{η⁻¹(W)}(X)`. -/
theorem Submission.ind_rescaled_current :
    ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P) (r : ℝ),
      0 < r → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1),
        (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
          ∃ η : TestFormOn (univ : Set (Eucl P)) (m + 1), ∀ y,
            (η : DifferentialForm (Eucl P) (m + 1)) y =
              (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x))) ∧
        (∀ ω η : TestFormOn (univ : Set (Eucl P)) (m + 1),
          (∀ y, (η : DifferentialForm (Eucl P) (m + 1)) y =
            (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x))) →
          Y ω = X η) ∧
        (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧
        (X.boundary = 0 → Y.boundary = 0) ∧
        ∀ W : Set (Eucl P),
          Y.massOn W ≤ ENNReal.ofReal ((r ^ (m + 1))⁻¹) * X.massOn {y | r⁻¹ • (y - x) ∈ W} := by
  have hrect := @Submission.ind_rs_rectifiableTriple_dilation
  have htau := @Submission.ind_rs_tauAction_dilation
  have hmass := @Submission.ind_rs_massOn_dilation_le
  intro P m X x r hr
  -- `η(y) = b + L y = r⁻¹ • (y - x)`.
  let L : Eucl P →L[ℝ] Eucl P := r⁻¹ • ContinuousLinearMap.id ℝ (Eucl P)
  let b : Eucl P := -(r⁻¹ • x)
  have hbL : ∀ y, b + L y = r⁻¹ • (y - x) := by
    intro y
    simp only [b, L, smul_apply, ContinuousLinearMap.id_apply, smul_sub]
    abel
  -- `η` is a homeomorphism, hence proper.
  have hproper : IsProperMap (fun y => b + L y) := by
    have he : (fun y => b + L y) = ⇑((Homeomorph.addRight (-x)).trans
        (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))) := by
      funext y
      simp [hbL, sub_eq_add_neg]
    rw [he]
    exact Homeomorph.isProperMap _
  -- `α ∘ L = r⁻ⁿ α` for every `n`-covector `α`.
  have hcov : ∀ α : Covector (Eucl P) (m + 1),
      α.compContinuousLinearMap L = (r ^ (m + 1))⁻¹ • α := by
    intro α
    ext v
    have hv : L ∘ v = fun i => r⁻¹ • v i := by
      funext i
      simp [L]
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hv, α.map_smul_univ,
      ContinuousAlternatingMap.smul_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      inv_pow]
  -- The pull-back `η^# ω ∈ 𝒟ⁿ(ℝ^P)` (`affinePullbackTestOn`) is `r⁻ⁿ ω ∘ η`.
  have hpb : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), ∀ y,
      (affinePullbackTestOn L b hproper univ (m + 1) ω : DifferentialForm (Eucl P) (m + 1)) y =
        (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x)) := by
    intro ω y
    rw [affinePullbackTestOn_coe]
    simp only [affinePullbackForm, hbL, hcov]
  -- `Y = η_# X`, i.e. `Y(ω) = X(η^# ω)`, regarding `X` as a current on `η⁻¹(ℝ^P) = ℝ^P`.
  let X' : GeometricCurrentOn ((fun y => b + L y) ⁻¹' (univ : Set (Eucl P))) (m + 1) := X
  let Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1) :=
    GeometricCurrentOn.affinePushforward L b hproper X'
  have hA : ∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1),
      ∃ η : TestFormOn (univ : Set (Eucl P)) (m + 1), ∀ y,
        (η : DifferentialForm (Eucl P) (m + 1)) y =
          (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x)) :=
    fun ω => ⟨affinePullbackTestOn L b hproper univ (m + 1) ω, hpb ω⟩
  have hB : ∀ ω η : TestFormOn (univ : Set (Eucl P)) (m + 1),
      (∀ y, (η : DifferentialForm (Eucl P) (m + 1)) y =
        (r ^ (m + 1))⁻¹ • (ω : DifferentialForm (Eucl P) (m + 1)) (r⁻¹ • (y - x))) →
      Y ω = X η := by
    intro ω η hη
    change X (affinePullbackTestOn L b hproper univ (m + 1) ω) = X η
    congr 1
    exact Subtype.ext (funext fun y => (hpb ω y).trans (hη y).symm)
  refine ⟨Y, hA, hB, ?_, ?_, hmass P (m + 1) X Y x r hr hA hB⟩
  · -- `X = τ(M, θ, ξ)` gives `Y = τ(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)`.
    rintro ⟨M, θ, ξ, hT, hθ, hX⟩
    refine ⟨(fun y => r⁻¹ • (y - x)) '' M, fun z => θ (x + r • z), fun z => ξ (x + r • z),
      hrect P (m + 1) M θ ξ x r hr hT, ?_, fun ω => ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hθ y hy
      exact ⟨k, by simp only [smul_inv_smul₀ hr.ne', add_sub_cancel, hk]⟩
    · obtain ⟨η, hη⟩ := hA ω
      rw [hB ω η hη, hX η, ← htau P (m + 1) M θ ξ x r ω hr]
      congr 1
      exact funext hη
  · -- `∂Y = η_#(∂X) = 0`.
    intro hX0
    have hX0' : X'.boundary = 0 := hX0
    change (GeometricCurrentOn.affinePushforward L b hproper X').boundary = 0
    rw [GeometricCurrentOn.boundary_affinePushforward, hX0']
    ext ω
    rfl
/-- **Diagonal selection of a weakly convergent sequence with a mass bound** (the selection in the
proof of Simon Ch. 6, Theorem 8.2, p. 176: "(8) remains valid with `T_{j'}` instead of `T`").
Let `closure W` be compact.  Suppose that for every test form `ω` supported in `W`,
`X_{k,j}(ω) → Z_k(ω)` as `j → ∞` and `Z_k(ω) → L(ω)` as `k → ∞`, and that for each `k`,
`M_W(X_{k,j}) ≤ C` for all large `j`.  Then some strictly increasing `φ` gives
`M_W(X_{k,φ(k)}) ≤ C` for every `k` and `X_{k,φ(k)}(ω) → L(ω)` for every such `ω`.  With
`C⁺ = max C 0`, the mass bound gives `|X(ω) - X(ω')| ≤ C⁺ sup |ω - ω'|`, and `Z_k`, `L` inherit
this bound in the limit.  Choose `φ(k)` with `|X_{k,φ(k)}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)` for `i ≤ k`,
where `(ωᵢ)` is a countable sup-norm-dense family.  A four-term estimate then gives convergence
for every `ω`. -/
theorem Submission.ind_diagonal_weak_limit : ∀ (P n : ℕ) (U W : Set (Eucl P)) (X : ℕ → ℕ → GeometricCurrentOn U n) (Z : ℕ → TestFormOn U n → ℝ) (L : TestFormOn U n → ℝ) (C : ℝ), IsCompact (closure W) → (∀ (k : ℕ) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun j => X k j ω) atTop (𝓝 (Z k ω))) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun k => Z k ω) atTop (𝓝 (L ω))) → (∀ k, ∀ᶠ j in atTop, (X k j).massOn W ≤ ENNReal.ofReal C) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, (X k (φ k)).massOn W ≤ ENNReal.ofReal C) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun k => X k (φ k) ω) atTop (𝓝 (L ω)) := by
  intro P n U W X Z L C hW hXZ hZL hmass
  classical
  -- Step 1 (mass estimate): if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ M`
  -- everywhere (Euclidean covector norm), then `|T(ω)| ≤ B M`.
  have hF1 : ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B M : ℝ), 0 ≤ B →
      T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ M) →
      |T ω| ≤ B * M := by
    intro T ω B M hB hM hWω hMω
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
    -- `M ≥ 0`, by evaluating the pointwise bound at `0`.
    have hM0 : 0 ≤ M := (covectorEuclideanNorm_nonneg _).trans (hMω 0)
    -- For every `c > M`, both `±c⁻¹ ω` are mass-admissible for `W`, hence `|T ω| ≤ B c`.
    have key : ∀ c, M < c → |T ω| ≤ B * c := by
      intro c hc
      have hc0 : 0 < c := hM0.trans_lt hc
      have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * T ω ≤ B := by
        intro s hs
        have hadm : s • ω ∈ massAdmissibleOn U n W := by
          refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hWω, fun x => ?_⟩
          change covectorEuclideanNorm (s • (ω : DifferentialForm (Eucl P) n) x) ≤ 1
          rw [hsmul, hs, inv_mul_le_iff₀ hc0, mul_one]
          exact (hMω x).trans hc.le
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
    -- Let `c ↓ M`: take `c = M + ε / (B + 1)`.
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hB1 : 0 < B + 1 := by linarith
    have hδ : 0 < ε / (B + 1) := div_pos hε hB1
    have hBδ : B * (ε / (B + 1)) ≤ ε := by
      calc B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hδ.le
        _ = ε := by field_simp
    have := key (M + ε / (B + 1)) (by linarith)
    calc |T ω| ≤ B * (M + ε / (B + 1)) := this
      _ = B * M + B * (ε / (B + 1)) := by ring
      _ ≤ B * M + ε := by linarith
  -- Step 2 (separability): a countable family `E` of test forms supported in `W` is dense, in the
  -- sup of the Euclidean coefficient norm, among all test forms supported in `W`.  The
  -- coefficient vector `c(α) = (α(e_{I 0}, …, e_{I (n-1)}))_I ∈ ℝ^(Fin n → Fin P)` satisfies
  -- `|α| ≤ √N ‖c(α)‖_∞`; for each accuracy `1/(m+1)` and scale `1/(j+1)`, the forms whose
  -- coefficients oscillate by less than `1/(m+1)` at scale `1/(j+1)` are approximated through
  -- their values on a finite `1/(j+1)`-net of `closure W`.
  have hdense : ∃ E : Set (TestFormOn U n), E.Countable ∧
      (∀ η ∈ E, tsupport (η : DifferentialForm (Eucl P) n) ⊆ W) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → ∀ ε : ℝ, 0 < ε →
        ∃ η ∈ E, ∀ x, covectorEuclideanNorm
          ((ω : DifferentialForm (Eucl P) n) x - (η : DifferentialForm (Eucl P) n) x) ≤ ε := by
    -- The coefficient map `c` and the estimate `|α| ≤ √N ‖c α‖_∞`.
    let c : Covector (Eucl P) n → (Fin n → Fin P) → ℝ :=
      fun α I => α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
    have hc_cont : Continuous c := continuous_pi fun I => by fun_prop
    have hc_sub : ∀ α γ, c (α - γ) = c α - c γ := fun α γ => by funext I; simp [c]
    have hc_zero : c 0 = 0 := by funext I; simp [c]
    set N : ℝ := Real.sqrt (Fintype.card (Fin n → Fin P)) with hN_def
    have hN : 0 ≤ N := Real.sqrt_nonneg _
    have hcmp : ∀ α, covectorEuclideanNorm α ≤ N * ‖c α‖ := by
      intro α
      unfold covectorEuclideanNorm
      rw [hN_def, ← Real.sqrt_sq (norm_nonneg (c α)), ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      calc ∑ I : Fin n → Fin P,
            (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
          ≤ ∑ _I : Fin n → Fin P, ‖c α‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · have h : |c α I| ≤ ‖c α‖ := by
                simpa [Real.norm_eq_abs] using norm_le_pi_norm (c α) I
              calc (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 = |c α I| ^ 2 :=
                    (sq_abs _).symm
                _ ≤ ‖c α‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
            · positivity
        _ = (Fintype.card (Fin n → Fin P) : ℝ) * ‖c α‖ ^ 2 := by simp
    -- Test forms supported in `W` vanish off `closure W`.
    let D : Set (TestFormOn U n) := {ω | tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W}
    have hzero : ∀ ω ∈ D, ∀ x ∉ closure W, (ω : DifferentialForm (Eucl P) n) x = 0 :=
      fun ω hω x hx => image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hω h))
    -- Finite `1/(j+1)`-nets of the compact set `closure W`.
    have hnet : ∀ j : ℕ, ∃ t : Finset (Eucl P),
        closure W ⊆ ⋃ y ∈ t, Metric.ball y (1 / ((j : ℝ) + 1)) := by
      intro j
      obtain ⟨t, -, ht, hcov⟩ := hW.finite_cover_balls (e := 1 / ((j : ℝ) + 1)) (by positivity)
      exact ⟨ht.toFinset, by simpa using hcov⟩
    choose net hnet using hnet
    -- Accuracy `r = 1/(m+1)` at scale `1/(j+1)`: take a countable dense subset of the coefficient
    -- values on the net and choose preimages.
    have key : ∀ m j : ℕ, ∃ E' : Set (TestFormOn U n), E'.Countable ∧ E' ⊆ D ∧
        ∀ ω ∈ D, (∀ x y, dist x y < 1 / ((j : ℝ) + 1) →
            dist (c ((ω : DifferentialForm (Eucl P) n) x)) (c ((ω : DifferentialForm (Eucl P) n) y))
              < 1 / ((m : ℝ) + 1)) →
          ∃ η ∈ E', ∀ x, ‖c ((ω : DifferentialForm (Eucl P) n) x)
            - c ((η : DifferentialForm (Eucl P) n) x)‖ ≤ 3 / ((m : ℝ) + 1) := by
      intro m j
      set r : ℝ := 1 / ((m : ℝ) + 1) with hr_def
      have hr : 0 < r := by positivity
      let Dj : Set (TestFormOn U n) := {ω | ω ∈ D ∧ ∀ x y, dist x y < 1 / ((j : ℝ) + 1) →
        dist (c ((ω : DifferentialForm (Eucl P) n) x))
          (c ((ω : DifferentialForm (Eucl P) n) y)) < r}
      let g : TestFormOn U n → (net j → (Fin n → Fin P) → ℝ) :=
        fun ω y => c ((ω : DifferentialForm (Eucl P) n) y)
      obtain ⟨S, hSA, hSc, hAS⟩ :=
        (TopologicalSpace.IsSeparable.of_separableSpace (g '' Dj)).exists_countable_dense_subset
      have hpre : ∀ s : S, ∃ ω ∈ Dj, g ω = s := fun s => hSA s.2
      choose pick hpickD hpickg using hpre
      have : Countable S := hSc.to_subtype
      refine ⟨Set.range pick, Set.countable_range pick, ?_, ?_⟩
      · rintro _ ⟨s, rfl⟩
        exact (hpickD s).1
      · intro ω hωD hωmod
        obtain ⟨s, hsS, hdist⟩ :=
          Metric.mem_closure_iff.mp (hAS ⟨ω, ⟨hωD, hωmod⟩, rfl⟩) r hr
        set η := pick ⟨s, hsS⟩ with hη_def
        have hηD : η ∈ Dj := hpickD ⟨s, hsS⟩
        have hgη : g η = s := hpickg ⟨s, hsS⟩
        refine ⟨η, ⟨⟨s, hsS⟩, rfl⟩, fun x => ?_⟩
        by_cases hx : x ∈ closure W
        · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hnet j hx)
          have h1 := hωmod x y (Metric.mem_ball.mp hxy)
          rw [← hgη] at hdist
          have h2 : dist (c ((ω : DifferentialForm (Eucl P) n) y))
              (c ((η : DifferentialForm (Eucl P) n) y)) < r :=
            (dist_le_pi_dist (g ω) (g η) ⟨y, hy⟩).trans_lt hdist
          have h3 := hηD.2 y x (by rwa [dist_comm])
          have h4 := dist_triangle4 (c ((ω : DifferentialForm (Eucl P) n) x))
            (c ((ω : DifferentialForm (Eucl P) n) y)) (c ((η : DifferentialForm (Eucl P) n) y))
            (c ((η : DifferentialForm (Eucl P) n) x))
          rw [← dist_eq_norm, show 3 / ((m : ℝ) + 1) = r + r + r by rw [hr_def]; ring]
          linarith
        · rw [hzero ω hωD x hx, hzero η hηD.1 x hx, sub_self, norm_zero]
          positivity
    choose E' hE'c hE'D hE' using key
    refine ⟨⋃ m, ⋃ j, E' m j,
      Set.countable_iUnion fun m => Set.countable_iUnion fun j => hE'c m j, ?_, ?_⟩
    · intro η hη
      obtain ⟨m, j, hη⟩ := Set.mem_iUnion₂.mp hη
      exact hE'D m j hη
    · intro ω hω ε hε
      obtain ⟨m, hm⟩ : ∃ m : ℕ, N * (3 / ((m : ℝ) + 1)) ≤ ε := by
        obtain ⟨m, hm⟩ := exists_nat_gt (3 * N / ε)
        refine ⟨m, ?_⟩
        rw [div_lt_iff₀ hε] at hm
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      -- `c ∘ ω` is continuous with compact support, hence uniformly continuous.
      have huc : UniformContinuous (c ∘ (ω : DifferentialForm (Eucl P) n)) :=
        (ω.property.1.2.comp_left hc_zero).uniformContinuous_of_continuous
          (hc_cont.comp ω.property.1.1.continuous)
      obtain ⟨δ, hδ, hδ'⟩ :=
        Metric.uniformContinuous_iff.mp huc (1 / ((m : ℝ) + 1)) (by positivity)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      obtain ⟨η, hηE, hη⟩ := hE' m j ω hω fun x y hxy => hδ' (hxy.trans hj)
      refine ⟨η, Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨j, hηE⟩⟩, fun x => ?_⟩
      calc covectorEuclideanNorm
            ((ω : DifferentialForm (Eucl P) n) x - (η : DifferentialForm (Eucl P) n) x)
          ≤ N * ‖c ((ω : DifferentialForm (Eucl P) n) x
              - (η : DifferentialForm (Eucl P) n) x)‖ := hcmp _
        _ = N * ‖c ((ω : DifferentialForm (Eucl P) n) x)
              - c ((η : DifferentialForm (Eucl P) n) x)‖ := by rw [hc_sub]
        _ ≤ N * (3 / ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hη x) hN
        _ ≤ ε := hm
  obtain ⟨E, hEc, hEW, hEdense⟩ := hdense
  -- `E` is nonempty (it approximates `0`); enumerate it as `E = {ωᵢ : i ∈ ℕ}`.
  have hEne : E.Nonempty := by
    obtain ⟨η, hη, -⟩ := hEdense 0 (by simp) 1 one_pos
    exact ⟨η, hη⟩
  obtain ⟨e, rfl⟩ := hEc.exists_eq_range hEne
  have heW : ∀ i, tsupport (e i : DifferentialForm (Eucl P) n) ⊆ W := fun i => hEW _ ⟨i, rfl⟩
  -- `C⁺ = max C 0`.
  set C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right C 0
  have hCC' : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal (le_max_left C 0)
  -- If `M_W(T) ≤ C` and `|ω - ω'| ≤ ε` everywhere, then `|T(ω) - T(ω')| = |T(ω - ω')| ≤ C⁺ ε`.
  have hdiff : ∀ (T : GeometricCurrentOn U n) (ω ω' : TestFormOn U n) (ε : ℝ),
      T.massOn W ≤ ENNReal.ofReal C → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      tsupport (ω' : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm
        ((ω : DifferentialForm (Eucl P) n) x - (ω' : DifferentialForm (Eucl P) n) x) ≤ ε) →
      |T ω - T ω'| ≤ C' * ε := by
    intro T ω ω' ε hT hω hω' hε
    have hsupp : tsupport ((ω - ω' : TestFormOn U n) : DifferentialForm (Eucl P) n) ⊆ W :=
      (tsupport_sub _ _).trans (union_subset hω hω')
    have h := hF1 T (ω - ω') C' ε hC'0 (hT.trans hCC') hsupp hε
    have hlin : T (ω - ω') = T ω - T ω' := map_sub T.toCurrent ω ω'
    rwa [hlin] at h
  -- Step 3: the limits inherit the bound, first `Z_k` (`j → ∞`), then `L` (`k → ∞`).
  have hLlip : ∀ (ω ω' : TestFormOn U n) (ε : ℝ), tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      tsupport (ω' : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm
        ((ω : DifferentialForm (Eucl P) n) x - (ω' : DifferentialForm (Eucl P) n) x) ≤ ε) →
      |L ω - L ω'| ≤ C' * ε := by
    intro ω ω' ε hω hω' hε
    have hZ : ∀ k, |Z k ω - Z k ω'| ≤ C' * ε := fun k =>
      le_of_tendsto ((hXZ k ω hω).sub (hXZ k ω' hω')).abs
        ((hmass k).mono fun j hj => hdiff (X k j) ω ω' ε hj hω hω' hε)
    exact le_of_tendsto ((hZL ω hω).sub (hZL ω' hω')).abs (Eventually.of_forall hZ)
  -- Step 4: for each `k`, the mass bound and `|X_{k,j}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)` for all `i ≤ k`
  -- hold for all large `j`; extract a strictly increasing `φ` along them.
  have hev : ∀ k, ∀ᶠ j in atTop, (X k j).massOn W ≤ ENNReal.ofReal C ∧
      ∀ i : Fin (k + 1), |X k j (e i) - Z k (e i)| < 1 / ((k : ℝ) + 1) := by
    intro k
    refine (hmass k).and (Filter.eventually_all.2 fun i => ?_)
    exact (Metric.tendsto_nhds.1 (hXZ k (e i) (heW i)) (1 / ((k : ℝ) + 1)) (by positivity)).mono
      fun j hj => by rwa [Real.dist_eq] at hj
  obtain ⟨φ, hφmono, hφ⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφmono, fun k => (hφ k).1, fun ω hω => ?_⟩
  -- Step 5: fix `δ > 0`; approximate `ω` by some `ωᵢ` within `ε`, where `C⁺ ε < δ / 4`.
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set ε : ℝ := δ / (4 * (C' + 1)) with hε_def
  have hC1 : 0 < C' + 1 := by linarith
  have hε : 0 < ε := by positivity
  have hCε : C' * ε < δ / 4 := by
    have h : (C' + 1) * ε = δ / 4 := by
      rw [hε_def]
      field_simp
    nlinarith
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hEdense ω hω ε hε
  have hL := hLlip ω (e i) ε hω (heW i) hi
  -- For large `k ≥ i`, `|X_{k,φ(k)}(ω) - L(ω)|` is at most `|X_{k,φ(k)}(ω - ωᵢ)| ≤ C⁺ε`, plus
  -- `|X_{k,φ(k)}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)`, plus `|Z_k(ωᵢ) - L(ωᵢ)|`, plus `|L(ωᵢ) - L(ω)| ≤ C⁺ε`;
  -- each of the four terms is `< δ/4`.
  filter_upwards [Filter.eventually_ge_atTop i,
    Metric.tendsto_nhds.1 (hZL (e i) (heW i)) (δ / 4) (by positivity),
    (tendsto_order.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 (δ / 4)
      (by positivity)] with k hik hZk hk
  obtain ⟨hmk, happ⟩ := hφ k
  have h1 := hdiff (X k (φ k)) ω (e i) ε hmk hω (heW i) hi
  have h2 : |X k (φ k) (e i) - Z k (e i)| < 1 / ((k : ℝ) + 1) :=
    happ ⟨i, Nat.lt_succ_of_le hik⟩
  rw [Real.dist_eq] at hZk ⊢
  have h1' := abs_le.1 h1
  have h2' := abs_lt.1 h2
  have h3' := abs_lt.1 hZk
  have h4' := abs_le.1 hL
  rw [abs_lt]
  constructor <;> linarith
/-- **Slices of a cycle (Simon Ch. 6, 4.5(1)–(2), 4.6, 4.10).**  For `X ∈ 𝒟_{m+1}(U)` with
`∂X = 0` and locally finite mass, `d` `L`-Lipschitz and `a < b`, there are restrictions
`A_t = X ⌞ {d < t}` and a measurable `g` with `M_W(∂A_t) ≤ g(t)` on `(a, b)` and
`∫⁻_{(a,b)} g ≤ L · M_W(X)`.  As `M_V(∂X) = M_V(0) = 0`, `SlicingTheorem` gives slices
`S_t = ⟨X, d, t⟩`, and `∂A_t = S_t` by `ind_pi_ss_cycle_slice_boundary`.  The band
`{a < d < b} = {|d - (a + b)/2| < (b - a)/2}` is a sublevel set of an `L`-Lipschitz function, so
the same lemma gives the restriction `R = X ⌞ {a < d < b}` used by the mass clause of 4.10
(`‖Dd‖ ≤ L`); finally `M_W(R) ≤ M_W(X)` by `ind_pi_ss_restriction_massOn_le`. -/
theorem Submission.ind_pi_ss_cycle_slice_family : SlicingTheorem → ∀ (P m : ℕ) (U W : Set (Eucl P)) (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ), IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b → X.boundary = 0 → (∀ V, CompactlyContainedOpen V U → X.massOn V < ∞) → ∃ (A : ℝ → GeometricCurrentOn U (m + 1)) (g : ℝ → ℝ≥0∞), Measurable g ∧ (∀ t, IsRestriction X {x | x ∈ U ∧ d x < t} (A t)) ∧ (∀ t ∈ Ioo a b, (A t).boundary.massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * X.massOn W := by
  intro hST P m U W X d L a b hU hW hd hab hX0 hXfin
  -- Step 1: `M_V(∂X) = M_V(0) = 0`, so `X` satisfies the hypotheses of `SlicingTheorem`.
  have hfin : ∀ V, CompactlyContainedOpen V U →
      X.massOn V < ∞ ∧ X.boundary.massOn V < ∞ := by
    intro V hV
    have h0 : (0 : GeometricCurrentOn U m).massOn V = 0 := by
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, -, rfl⟩
      simp
    rw [hX0, h0]
    exact ⟨hXfin V hV, ENNReal.zero_lt_top⟩
  -- Step 2: the slices `S_t = ⟨X, d, t⟩` and the mass clause of 4.10 for `d`.
  obtain ⟨S, hS, -, -, hSmass⟩ := hST P m U hU X hfin d L hd.lipschitzOnWith
  -- Step 3: `A_t = X ⌞ {d < t}` with `∂A_t = S_t`.
  choose A hAres hAbd using fun t =>
    Submission.ind_pi_ss_cycle_slice_boundary P m U X d t (S t) hU hX0 (hS t)
  -- Step 4: `R = X ⌞ {a < d < b}`, as the band is the sublevel set `{|d - c| < r}` of the
  -- `L`-Lipschitz function `|d - c|`, `c = (a + b)/2`, `r = (b - a)/2`.
  have hc : LipschitzWith L fun x => |d x - (a + b) / 2| := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    calc dist |d x - (a + b) / 2| |d y - (a + b) / 2|
        = |(|d x - (a + b) / 2| - |d y - (a + b) / 2|)| := Real.dist_eq _ _
      _ ≤ |(d x - (a + b) / 2) - (d y - (a + b) / 2)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = dist (d x) (d y) := by rw [sub_sub_sub_cancel_right, Real.dist_eq]
      _ ≤ L * dist x y := hd.dist_le_mul x y
  obtain ⟨S', hS', -⟩ := hST P m U hU X hfin (fun x => |d x - (a + b) / 2|) L hc.lipschitzOnWith
  obtain ⟨R, hR, -⟩ := Submission.ind_pi_ss_cycle_slice_boundary P m U X
    (fun x => |d x - (a + b) / 2|) ((b - a) / 2) (S' ((b - a) / 2)) hU hX0 (hS' _)
  have hRband : IsRestriction X {x | x ∈ U ∧ a < d x ∧ d x < b} R := by
    have hband : {x | x ∈ U ∧ a < d x ∧ d x < b} =
        {x | x ∈ U ∧ |d x - (a + b) / 2| < (b - a) / 2} := by
      ext x
      simp only [mem_ofPred_eq, abs_sub_lt_iff]
      constructor
      · rintro ⟨hx, h₁, h₂⟩
        exact ⟨hx, by linarith, by linarith⟩
      · rintro ⟨hx, h₁, h₂⟩
        exact ⟨hx, by linarith, by linarith⟩
    rw [hband]
    exact hR
  -- Step 5: the mass clause of 4.10 on `W`, with `‖Dd‖ ≤ L` everywhere.
  have hDd : ∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ d x‖₊ ≤ L :=
    ae_of_all _ fun x _ => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_fderiv_le_of_lipschitz ℝ hd
  obtain ⟨g, hg, hgS, hgint⟩ :=
    hSmass W hW.1 (subset_closure.trans hW.2.2) L hDd a b hab R hRband
  -- Step 6: `M_W(∂A_t) = M_W(S_t) ≤ g(t)` and `∫⁻ g ≤ L · M_W(R) ≤ L · M_W(X)`.
  refine ⟨A, g, hg, hAres, fun t ht => ?_, ?_⟩
  · rw [hAbd t]
    exact hgS t ht
  · calc ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * R.massOn W := hgint
      _ ≤ (L : ℝ≥0∞) * X.massOn W := by
        gcongr
        exact Submission.ind_pi_ss_restriction_massOn_le P (m + 1) U W _ X R hU hW hRband
/-- Fatou selection of a good level (the "selection argument as in 6.7(2) of Ch. 2" in the proof
of Simon Ch. 6, 8.2): if `∫⁻_{(a,b)} g_k ≤ C < ∞` for all `k` and `E` is countable, there are
`γ ∈ (a, b) \ E`, a subsequence `σ` and `G < ∞` with `g_{σ(k)}(γ) ≤ G` for all `k`.  By Fatou,
`∫⁻_{(a,b)} liminf_k g_k ≤ C`, so `liminf_k g_k(γ) < ∞` for some `γ ∈ (a, b) \ E` (`E` is
Lebesgue-null); with `G = liminf_k g_k(γ) + 1`, `g_k(γ) < G` for infinitely many `k`. -/
theorem Submission.ind_pi_ss_fatou_level_selection :
    ∀ (g : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (C : ℝ≥0∞) (E : Set ℝ), a < b → (∀ k, Measurable (g k)) →
      C < ∞ → (∀ k, ∫⁻ t in Ioo a b, g k t ≤ C) → E.Countable →
      ∃ (γ : ℝ) (σ : ℕ → ℕ) (G : ℝ≥0∞), γ ∈ Ioo a b ∧ γ ∉ E ∧ StrictMono σ ∧ G < ∞ ∧
        ∀ k, g (σ k) γ ≤ G := by
  intro g a b C E hab hg hC hgC hE
  -- Fatou: `F = liminf_k g_k` is measurable and `∫⁻_{(a,b)} F ≤ liminf_k ∫⁻_{(a,b)} g_k ≤ C`.
  have hF : Measurable fun t => liminf (fun k => g k t) atTop := Measurable.liminf hg
  have hFC : ∫⁻ t in Ioo a b, liminf (fun k => g k t) atTop ≤ C :=
    (lintegral_liminf_le hg).trans (liminf_le_of_frequently_le' (Frequently.of_forall hgC))
  -- For a.e. `t` w.r.t. `volume⌞(a, b)`: `F t < ∞`, `t ∉ E` (`E` is Lebesgue-null), `t ∈ (a, b)`.
  have h₁ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), liminf (fun k => g k t) atTop < ∞ :=
    ae_lt_top hF (hFC.trans_lt hC).ne
  have h₂ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∉ E :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hE.measure_zero volume))
  have h₃ : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∈ Ioo a b := ae_restrict_mem measurableSet_Ioo
  -- `volume (a, b) = b - a > 0`, so the a.e. filter is nontrivial and a good `γ` exists.
  have hne : (ae (volume.restrict (Ioo a b))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.2 hab
  obtain ⟨γ, hγF, hγE, hγ⟩ := (h₁.and (h₂.and h₃)).exists
  -- `G = F(γ) + 1 > liminf_k g_k(γ)`, so `g_k(γ) < G` frequently: extract `σ`.
  have hG : liminf (fun k => g k γ) atTop < liminf (fun k => g k γ) atTop + 1 :=
    ENNReal.lt_add_right hγF.ne one_ne_zero
  obtain ⟨σ, hσ, hσG⟩ := extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (h := hG))
  exact ⟨γ, σ, _, hγ, hγE, hσ, ENNReal.add_lt_top.2 ⟨hγF, ENNReal.one_lt_top⟩,
    fun k => (hσG k).le⟩

/-- Simon Ch. 6, proof of 8.2, display (8) ("by 4.5(1) and a selection argument as in 6.7(2) of
Ch. 2"): for cycles `X_k ⇀ X` with `sup_k M_W(X_k) < ∞` there are a level `γ ∈ (a, b)` and a
subsequence `κ` such that the restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` satisfy
`M_W(R_k) ≤ M_W(X_{κ(k)})`, `sup_k M_W(∂R_k) < ∞` and `R_k(ω) → (X ⌞ {d < γ})(ω)` for
`spt ω ⊆ W`. -/
theorem Submission.ind_pi_good_slice_selection :
    SlicingTheorem → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P))
        (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U →
        (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U →
        ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E,
          ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k),
            (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) →
            IsRestriction X {x | x ∈ U ∧ φ x < s} R →
            (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
              Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧
            (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K →
              WeaklyConvergesOn Rj R)) →
    ∀ (P m : ℕ) (U W : Set (Eucl P)) (Xk : ℕ → GeometricCurrentOn U (m + 1))
      (X : GeometricCurrentOn U (m + 1)) (d : Eucl P → ℝ) (L : ℝ≥0) (a b : ℝ),
      IsOpen U → CompactlyContainedOpen W U → LipschitzWith L d → a < b →
      (∀ k, (Xk k).boundary = 0) →
      (∀ k V, CompactlyContainedOpen V U → (Xk k).massOn V < ∞) →
      (⨆ k, (Xk k).massOn W) < ∞ → WeaklyConvergesOn Xk X →
      ∃ (γ : ℝ) (κ : ℕ → ℕ) (Rk : ℕ → GeometricCurrentOn U (m + 1)) (G : ℝ≥0∞),
        γ ∈ Ioo a b ∧ StrictMono κ ∧ G < ∞ ∧
        (∀ k, IsRestriction (Xk (κ k)) {x | x ∈ U ∧ d x < γ} (Rk k)) ∧
        (∀ k, (Rk k).massOn W ≤ (Xk (κ k)).massOn W) ∧
        (∀ k, (Rk k).boundary.massOn W ≤ G) ∧
        ∀ R : GeometricCurrentOn U (m + 1), IsRestriction X {x | x ∈ U ∧ d x < γ} R →
          ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ W →
            Tendsto (fun k => Rk k ω) atTop (𝓝 (R ω)) := by
  intro hSlice hRWL P m U W Xk X d L a b hU hW hd hab hcycle hmass hsup hconv
  -- Steps 1–4 for each cycle `X_k`: restrictions `A k t` of `X_k` to `{d < t}` with
  -- `M_W(∂(A k t)) ≤ g k t` for `t ∈ (a, b)` and `∫⁻_{(a,b)} g k ≤ L · M_W(X_k)`.
  choose A g hg hA hAg hgi using fun k =>
    Submission.ind_pi_ss_cycle_slice_family hSlice P m U W (Xk k) d L a b hU hW hd hab
      (hcycle k) (hmass k)
  -- Step 5: (RWL) with `φ := d` gives `ψ` and a countable exceptional set `E` of levels.
  obtain ⟨ψ, E, hψ, hE, hlim⟩ := hRWL P (m + 1) U hU Xk X W d hconv hW.1
    (subset_closure.trans hW.2.2) hsup hd.continuous.continuousOn
  -- `∫⁻_{(a,b)} g (ψ k) ≤ L · M_W(X_{ψ k}) ≤ L · sup_j M_W(X_j) < ∞`.
  have hgψ : ∀ k, ∫⁻ t in Ioo a b, g (ψ k) t ≤ (L : ℝ≥0∞) * ⨆ j, (Xk j).massOn W := fun k =>
    (hgi (ψ k)).trans (mul_le_mul_right (le_iSup (fun j => (Xk j).massOn W) (ψ k)) _)
  -- Steps 6–8: a level `γ ∈ (a, b) \ E` and a subsequence `σ` with `g (ψ (σ k)) γ ≤ G`.
  obtain ⟨γ, σ, G, hγ, hγE, hσ, hG, hgG⟩ :=
    Submission.ind_pi_ss_fatou_level_selection (fun k => g (ψ k)) a b
      ((L : ℝ≥0∞) * ⨆ j, (Xk j).massOn W) E hab (fun k => hg (ψ k))
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hsup) hgψ hE
  -- Step 9: `κ := ψ ∘ σ` and `R_k := A (κ k) γ`; convergence passes to the subsequence `σ`.
  refine ⟨γ, ψ ∘ σ, fun k => A (ψ (σ k)) γ, G, hγ, hψ.comp hσ, hG, fun k => hA (ψ (σ k)) γ,
    fun k => Submission.ind_pi_ss_restriction_massOn_le P (m + 1) U W _ _ _ hU hW
      (hA (ψ (σ k)) γ), fun k => (hAg (ψ (σ k)) γ hγ).trans (hgG k), fun R hR ω hω => ?_⟩
  exact ((hlim γ hγE (fun j => A (ψ j) γ) R (fun j => hA (ψ j) γ) hR).1 ω hω).comp
    hσ.tendsto_atTop

/-- Simon Ch. 6, proof of 8.2, displays (8)–(9): localization of the cycles `Y_k ⇀ c [[Q]]`,
`Q = span τ`, to the thin cylinder `W' = {‖p‖ < 1, d < 3/4} ⊂⊂ B₂(0)`.  The current
`X = c [[Q]] ∈ 𝒟ₙ(B₂(0))` has the representation `(Hⁿ ⌞ Q, c τ₁ ∧ ⋯ ∧ τₙ)`, and
`X_k = Y_k|_{B₂(0)}` are integer multiplicity cycles with `X_k ⇀ X`.  A good level
`γ ∈ (1/4, 1/2)` of `d` gives restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` with bounded
`M_{W'}(R_k) + M_{W'}(∂R_k)` and `R_k → X ⌞ {d < γ} = X` on forms supported in `W'` (the
measure of `X` lives on `Q ⊆ {d = 0}`).  Then `Z_k = R_k|_{W'}` are integer multiplicity,
supported in `{d ≤ γ}`, and converge to `c [[Q]]` in `W'`. -/
theorem Submission.ind_pi_localized_cycles :
    SlicingTheorem → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P)) (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U → (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k), (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) → IsRestriction X {x | x ∈ U ∧ φ x < s} R → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K → WeaklyConvergesOn Rj R)) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c : ℝ) (Y : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (p : Eucl P →L[ℝ] Eucl (m + 1)) (d : Eucl P → ℝ), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → (∀ k, IsIntegerMultiplicity (Y k)) → (∀ k, (Y k).boundary = 0) → (⨆ k, (Y k).massOn (ball (0 : Eucl P) 2)) < ∞ → (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ ball (0 : Eucl P) 2 → Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → ∃ (γ : ℝ) (Z : ℕ → GeometricCurrentOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1)), 0 ≤ γ ∧ γ < 3 / 4 ∧ (∀ k, IsIntegerMultiplicity (Z k)) ∧ (∀ k, (Z k).support ⊆ {y | d y ≤ γ}) ∧ (⨆ k, ((Z k).mass + (Z k).boundary.mass)) < ∞ ∧ ∀ ω : TestFormOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1), Tendsto (fun k => Z k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P)))) := by
  intro hSlicing hRWL P m τ c Y p d hτ hp hd hYim hYb hYmass hYlim
  -- Step 0: `d` is `1`-Lipschitz and vanishes on `Q`, `W' ⊂⊂ B = B₂(0)`, `Hⁿ ⌞ Q` is finite on
  -- compact sets, and the finite-dimensional subspace `Q` is closed, hence measurable.
  obtain ⟨hLip, -, -, -, -, hdQ, hW', -⟩ :=
    Submission.ind_pi_frame_geometry P (m + 1) τ p d hτ hp hd
  obtain ⟨-, hQfin⟩ := Submission.ind_pi_span_integral P (m + 1) τ hτ
  set B : Set (Eucl P) := ball (0 : Eucl P) 2
  set W' : Set (Eucl P) := {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4}
  set Q : Set (Eucl P) := (Submodule.span ℝ (Set.range τ) : Set (Eucl P))
  have hW'B : W' ⊆ B := subset_closure.trans hW'.2.2
  have hQmeas : MeasurableSet Q := (Submodule.closed_of_finiteDimensional _).measurableSet
  -- Step 1: `X = c [[Q]] ∈ 𝒟ₙ(B)` with representation `(Hⁿ ⌞ Q, c τ₁ ∧ ⋯ ∧ τₙ)`.
  obtain ⟨X, hX⟩ := Submission.ind_pi_constant_vector_current P (m + 1) B
    ((μHE[m + 1] : Measure (Eucl P)).restrict Q) (c • simpleNVector τ) hQfin
  have hXω : ∀ ω : TestFormOn B (m + 1), X ω = c * ∫ z in Q,
      (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P)) := by
    intro ω
    rw [(hX ω).2, ← integral_const_mul]
    rfl
  -- Step 2: restricting the domain does not increase `M_V` and commutes with `∂`.
  have hmassRD : ∀ {k : ℕ} {U₁ U₂ : Set (Eucl P)} (T : GeometricCurrentOn U₂ k) (h : U₁ ⊆ U₂)
      (V : Set (Eucl P)), (T.restrictDomain h).massOn V ≤ T.massOn V := by
    intro k U₁ U₂ T h V
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    exact T.le_massOn (omega := testFormOnInclusion h k ω) hω
  have hbdRD : ∀ {k : ℕ} {U₁ U₂ : Set (Eucl P)} (T : GeometricCurrentOn U₂ (k + 1))
      (h : U₁ ⊆ U₂), (T.restrictDomain h).boundary = T.boundary.restrictDomain h :=
    fun _ _ => GeometricCurrentOn.ext fun _ => rfl
  -- Step 3: `X_k = Y_k|_B` are integer multiplicity cycles, `M_V(X_k) ≤ C₀ = sup_j M_B(Y_j)` for
  -- `V ⊆ B`, and `X_k ⇀ X` in `B`.
  set Xk : ℕ → GeometricCurrentOn B (m + 1) := fun k => (Y k).restrictDomain (subset_univ B)
  have hXim : ∀ k, IsIntegerMultiplicity (Xk k) := fun k =>
    Submission.br_restrictDomain_isIntegerMultiplicity P (m + 1) univ B (subset_univ B)
      isOpen_ball (Y k) (hYim k)
  have hXb : ∀ k, (Xk k).boundary = 0 := fun k => GeometricCurrentOn.ext fun ω => by
    change (Y k).boundary (testFormOnInclusion (subset_univ B) m ω) = 0
    rw [hYb k]
    rfl
  have hXmass : ∀ k (V : Set (Eucl P)), V ⊆ B → (Xk k).massOn V ≤ ⨆ j, (Y j).massOn B :=
    fun k V hV => ((hmassRD (Y k) (subset_univ B) V).trans ((Y k).massOn_mono hV)).trans
      (le_iSup (fun j => (Y j).massOn B) k)
  have hXloc : ∀ k V, CompactlyContainedOpen V B → (Xk k).massOn V < ∞ :=
    fun k V hV => (hXmass k V (subset_closure.trans hV.2.2)).trans_lt hYmass
  have hXsup : (⨆ k, (Xk k).massOn W') < ∞ :=
    (iSup_le fun k => hXmass k W' hW'B).trans_lt hYmass
  have hXlim : WeaklyConvergesOn Xk X := fun ω => by
    rw [hXω]
    exact hYlim (testFormOnInclusion (subset_univ B) (m + 1) ω) ω.property.2
  -- Step 4: a good level `γ ∈ (1/4, 1/2)` of `d`, restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` with
  -- `M_{W'}(R_k) ≤ M_{W'}(X_{κ(k)})`, `M_{W'}(∂R_k) ≤ G < ∞` and `R_k → X ⌞ {d < γ}` in `W'`.
  obtain ⟨γ, κ, Rk, G, hγ, -, hG, hRres, hRmass, hRbd, hRlim⟩ :=
    Submission.ind_pi_good_slice_selection hSlicing hRWL P m B W' Xk X d 1 (1 / 4) (1 / 2)
      isOpen_ball hW' hLip (by norm_num) hXb hXloc hXsup hXlim
  have hγ0 : 0 < γ := lt_trans (by norm_num) hγ.1
  -- Step 5: `X ⌞ A_γ = X` for the open set `A_γ = {x ∈ B : d x < γ}`: the measure `Hⁿ ⌞ Q` of `X`
  -- lives on `Q ⊆ {d = 0}`, and test forms in `B` vanish on `Q \ A_γ ⊆ Q \ B`.
  have hA : IsOpen {x | x ∈ B ∧ d x < γ} := by
    have h : IsOpen (B ∩ {x | d x < γ}) :=
      isOpen_ball.inter (isOpen_lt hLip.continuous continuous_const)
    exact h
  have hXX : IsRestriction X {x | x ∈ B ∧ d x < γ} X := by
    refine ⟨hA.measurableSet, _, _, hX, fun ω => ?_⟩
    rw [(hX ω).2]
    refine (setIntegral_eq_integral_of_ae_compl_eq_zero
      (ae_restrict_of_forall_mem hQmeas fun x hxQ hxA => ?_)).symm
    have hxB : x ∉ B := fun hxB => hxA ⟨hxB, by rw [hdQ x hxQ]; exact hγ0⟩
    rw [image_eq_zero_of_notMem_tsupport fun h => hxB (ω.property.2 h)]
    exact map_zero _
  -- Step 6: the restrictions `R_k` of the integer multiplicity `X_{κ(k)}` to the open set `A_γ`
  -- are integer multiplicity.
  have hRim : ∀ k, IsIntegerMultiplicity (Rk k) := fun k =>
    Submission.ind_pi_restriction_open_im P (m + 1) B {x | x ∈ B ∧ d x < γ} (Xk (κ k)) (Rk k)
      isOpen_ball hA (hXim (κ k)) (hRres k)
  -- Step 7: `Z_k = R_k|_{W'}`.
  refine ⟨γ, fun k => (Rk k).restrictDomain hW'B, hγ0.le, hγ.2.trans (by norm_num),
    fun k => Submission.br_restrictDomain_isIntegerMultiplicity P (m + 1) B W' hW'B hW'.1 (Rk k)
      (hRim k), fun k => ?_, ?_, fun ω => ?_⟩
  · -- `spt Z_k ⊆ {d ≤ γ}`: `R_k(ω) = ∫_{A_γ} ⟨ω, v⟩ dμ` vanishes if `spt ω ∩ {d ≤ γ} = ∅`.
    refine Submission.fiw_tb_ext_support_subset P (m + 1) W' {y | d y ≤ γ} _ hW'.1
      (isClosed_le hLip.continuous continuous_const) fun ω hω => ?_
    obtain ⟨-, μ, v, -, hRv⟩ := hRres k
    change Rk k (testFormOnInclusion hW'B (m + 1) ω) = 0
    rw [hRv]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hxω : x ∉ tsupport (ω : DifferentialForm (Eucl P) (m + 1)) :=
      fun h => Set.disjoint_left.mp hω h (le_of_lt hx.2)
    rw [testFormOnInclusion_coe, image_eq_zero_of_notMem_tsupport hxω]
    exact map_zero _
  · -- `M(Z_k) ≤ M_{W'}(R_k) ≤ M_{W'}(X_{κ(k)}) ≤ C₀` and `M(∂Z_k) ≤ M_{W'}(∂R_k) ≤ G`.
    have hbound : ∀ k, ((Rk k).restrictDomain hW'B).mass +
        ((Rk k).restrictDomain hW'B).boundary.mass ≤ (⨆ j, (Y j).massOn B) + G := by
      intro k
      refine add_le_add ?_ ?_
      · exact ((hmassRD (Rk k) hW'B W').trans (hRmass k)).trans (hXmass (κ k) W' hW'B)
      · rw [hbdRD]
        exact (hmassRD (Rk k).boundary hW'B W').trans (hRbd k)
    exact (iSup_le hbound).trans_lt (ENNReal.add_lt_top.2 ⟨hYmass, hG⟩)
  · -- `Z_k(ω) = R_k(ω) → X(ω) = c ∫_Q ⟨ω, τ₁ ∧ ⋯ ∧ τₙ⟩ dHⁿ`.
    have h := hRlim X hXX (testFormOnInclusion hW'B (m + 1) ω) ω.property.2
    rw [hXω] at h
    exact h

/-- Simon Ch. 6, proof of 8.2 (display (10) and `p_# S̃_j ⇀ θ [[ℝⁿ]]`): push the localized
currents `Z_k ⇀ c [[Q]]` (`Q = span τ`) in the cylinder `W′ = {‖p‖ < 1, d < 3/4}` forward by
the frame coordinates `p`.  The push-forwards `S′_k = p_# Z_k` are integer multiplicity currents in
`B₁(0) ⊆ ℝⁿ` with `M_W(S′_k) ≤ M(Z_k)` and `M_W(∂S′_k) ≤ M(∂Z_k)`, and `S′_k(ω) = Z_k(η)` for a
cut-off pull-back `η = ζ p^#ω ∈ 𝒟ⁿ(W′)` independent of `k`.  On `Q`, `η(τ) = ω(p ·)(e)`, so
`S′_k(ω) → c ∫_Q ω(p z)(e) dHⁿ(z) = c ∫_{B₁(0)} ω(e) dx = S(ω)`. -/
theorem Submission.ind_pi_projected_limit : LipschitzPushforwardIntegerMultiplicity → (LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c γ : ℝ) (p : Eucl P →L[ℝ] Eucl (m + 1)) (d : Eucl P → ℝ) (Z : ℕ → GeometricCurrentOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1)) (S : GeometricCurrentOn (ball (0 : Eucl (m + 1)) 1) (m + 1)), Orthonormal ℝ τ → (∀ y i, p y i = inner ℝ (τ i) y) → (∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖) → 0 ≤ γ → γ < 3 / 4 → (∀ k, IsIntegerMultiplicity (Z k)) → (∀ k, (Z k).support ⊆ {y | d y ≤ γ}) → (⨆ k, ((Z k).mass + (Z k).boundary.mass)) < ∞ → (∀ ω : TestFormOn {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} (m + 1), Tendsto (fun k => Z k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → (∀ ω : TestFormOn (ball (0 : Eucl (m + 1)) 1) (m + 1), S ω = c * ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ S' : ℕ → GeometricCurrentOn (ball (0 : Eucl (m + 1)) 1) (m + 1), (∀ k, IsIntegerMultiplicity (S' k)) ∧ (∀ W, CompactlyContainedOpen W (ball (0 : Eucl (m + 1)) 1) → (⨆ k, ((S' k).massOn W + (S' k).boundary.massOn W)) < ∞) ∧ WeaklyConvergesOn S' S := by
  intro hLPF hSPF P m τ c γ p d Z S hτ hp hd hγ0 hγ hZim hZspt hZmass hZlim hS
  -- 0. Frame geometry: `W′` is open, `‖p‖ ≤ 1`, `p (∑ aᵢ τᵢ) = a`, `p τᵢ = eᵢ`, `d = 0` on `Q`,
  -- and `p⁻¹(K) ∩ {d ≤ γ}` is a compact subset of `W′` for every compact `K ⊆ B₁(0)`.
  obtain ⟨-, -, hpn, hpι, hpτ, hdQ, hW', hprop⟩ :=
    Submission.ind_pi_frame_geometry P (m + 1) τ p d hτ hp hd
  -- 1–3. The push-forwards `S′_k = p_# Z_k`, with `M_W(S′_k) ≤ M(Z_k)`, `M_W(∂S′_k) ≤ M(∂Z_k)`.
  obtain ⟨S', hS'im, hS'act, hS'mass⟩ :=
    Submission.ind_pi_pl_linear_pushforward_family hLPF hSPF P (m + 1) m _
      (ball (0 : Eucl (m + 1)) 1) {y | d y ≤ γ} p Z hW'.1 isOpen_ball hpn
      (fun y hy => mem_ball_zero_iff.mpr hy.1) (hprop γ hγ) hZim hZspt
  refine ⟨S', hS'im, fun W _ => lt_of_le_of_lt (iSup_mono fun k =>
    add_le_add (hS'mass k W).1 (hS'mass k W).2) hZmass, fun ω => ?_⟩
  obtain ⟨-, hωV⟩ := ω.property
  -- 4–6. A cut-off pull-back `η = ζ p^#ω ∈ 𝒟ⁿ(W′)` equal to `p^#ω` on an open `N ⊇ W′ ∩ {d ≤ γ}`;
  -- as `spt Z_k ⊆ W′ ∩ {d ≤ γ}`, `S′_k(ω) = Z_k(η)` for every `k`.
  obtain ⟨η, -, N, hN, hAN, -, -, hηN, hηt⟩ :=
    Submission.iwl_sp_exists_compatible_testForm P (m + 1) (m + 1) _ (ball (0 : Eucl (m + 1)) 1)
      ({y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ∩ {y | d y ≤ γ}) p hW'.1 inter_subset_left
      p.contDiff (fun K hK hKV => by
        obtain ⟨hKc, hKW⟩ := hprop γ hγ K hK hKV
        rwa [inter_left_comm, inter_eq_right.mpr hKW]) ω
  have hact : ∀ k, S' k ω = Z k η := fun k => hS'act k ω η ⟨N, hN,
    fun y hy => hAN ⟨(Z k).support_subset_domain hy, hZspt k hy⟩,
    fun x hx => by rw [hηN x hx, p.fderiv]⟩
  -- 7. On `Q`: `η(∑ aᵢ τᵢ)(τ) = ω(a)(e)`, since `ζ = 1` there when `a ∈ spt ω`, and both sides
  -- vanish otherwise.
  have hηQ : ∀ a : Eucl (m + 1), (η : DifferentialForm (Eucl P) (m + 1)) (∑ i, a i • τ i) τ =
      (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) a
        (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    intro a
    by_cases ha : a ∈ tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1))
    · have hdz : d (∑ i, a i • τ i) = 0 :=
        hdQ _ ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨fun i => a i, rfl⟩)
      have hz : ∑ i, a i • τ i ∈ {y : Eucl P | ‖p y‖ < 1 ∧ d y < 3 / 4} ∩ {y | d y ≤ γ} := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hpι]
          exact mem_ball_zero_iff.mp (hωV ha)
        · rw [hdz]
          norm_num
        · show d (∑ i, a i • τ i) ≤ γ
          rw [hdz]
          exact hγ0
      rw [hηN _ (hAN hz), p.fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply, hpι]
      congr 1
      funext i
      exact hpτ i
    · have hz : ∑ i, a i • τ i ∉ tsupport (η : DifferentialForm (Eucl P) (m + 1)) := fun hz =>
        ha (by simpa only [mem_preimage, hpι] using hηt hz)
      simp only [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport ha,
        ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  -- `c ∫_Q η(τ) dHⁿ = c ∫ η(∑ aᵢ τᵢ)(τ) da = c ∫ ω(a)(e) da = c ∫_{B₁(0)} ω(e) dx = S(ω)`.
  have hV : ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
      (fun i => EuclideanSpace.single i (1 : ℝ)) =
      ∫ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) := fun h => hx (hωV h)
    simp only [image_eq_zero_of_notMem_tsupport hx', ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply]
  have hlim : c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)),
      (η : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P)) = S ω := by
    rw [hS ω, hV, (Submission.ind_pi_span_integral P (m + 1) τ hτ).1]
    simp only [hηQ]
  -- 8. `S′_k(ω) = Z_k(η) → S(ω)`.
  have h := hZlim η
  rw [hlim] at h
  exact h.congr fun k => (hact k).symm
/-- An orthonormal `n`-frame in `ℝⁿ` has simple `n`-vector `±e₁ ∧ ⋯ ∧ eₙ` (Simon Ch. 6, 3.1 in top
dimension: an orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` is `±e₁ ∧ ⋯ ∧ eₙ`, so `⟨ω, ξ⟩ = ±a` for
`ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, as in the proof of 8.2, p. 179).  `τ` is linearly independent with
`n = dim ℝⁿ` members, hence an orthonormal basis of `ℝⁿ`, as is the standard basis `e`.  An
`n`-covector `α` is an alternating `n`-form on `ℝⁿ`, so `α(τ) = α(e) det_e(τ)`
(`AlternatingMap.eq_smul_basis_det`), and `det_e(τ) = ±1` because the change of basis between
orthonormal bases is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`). -/
theorem Submission.ind_top_orthonormal_frame_sign :
    ∀ (n : ℕ) (τ : Fin n → Eucl n), Orthonormal ℝ τ →
      simpleNVector τ = simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) ∨
        simpleNVector τ = -simpleNVector (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro n τ hτ
  -- Step 1: `τ` spans `ℝⁿ` (`n = 0` included).
  have hspan : Submodule.span ℝ (range τ) = ⊤ :=
    hτ.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  -- Step 2: `τ` and the standard basis `e` are orthonormal bases `bτ`, `be` of `ℝⁿ`.
  let bτ : OrthonormalBasis (Fin n) ℝ (Eucl n) := OrthonormalBasis.mk hτ hspan.ge
  let be : OrthonormalBasis (Fin n) ℝ (Eucl n) := EuclideanSpace.basisFun (Fin n) ℝ
  have hbτ : ⇑bτ = τ := OrthonormalBasis.coe_mk hτ hspan.ge
  have hbe : ⇑be.toBasis = fun i => EuclideanSpace.single i (1 : ℝ) := by
    funext i
    simp [be]
  -- Step 3: `det_e(τ) = ±1`, the change of basis between orthonormal bases being orthogonal.
  have hd : be.toBasis.det τ = 1 ∨ be.toBasis.det τ = -1 := by
    simpa only [hbτ] using be.det_to_matrix_orthonormalBasis_real bτ
  -- Step 4: an `n`-covector `α` is `α(e) • det_e`, so `α(τ) = α(e) * det_e(τ)`.
  have key : ∀ α : Covector (Eucl n) n,
      α τ = α (fun i => EuclideanSpace.single i (1 : ℝ)) * be.toBasis.det τ := by
    intro α
    have h := DFunLike.congr_fun (α.toAlternatingMap.eq_smul_basis_det be.toBasis) τ
    rw [AlternatingMap.smul_apply, smul_eq_mul, hbe] at h
    exact h
  -- Step 5: extensionality, as `simpleNVector v α = α v`.
  rcases hd with hd | hd
  · left
    refine ContinuousLinearMap.ext fun α => ?_
    rw [simpleNVector_apply, simpleNVector_apply, key α, hd, mul_one]
  · right
    refine ContinuousLinearMap.ext fun α => ?_
    rw [_root_.neg_apply, simpleNVector_apply, simpleNVector_apply, key α, hd, mul_neg_one]
/-- Densities of top-degree test-form functionals on an open set are unique a.e. (Simon Ch. 6, end
of the Proof of 8.2, p. 179: `θ ≡ θ(x)` in `B₁ⁿ(0)`, top-dimensional currents acting by
`ω = a dx¹ ∧ ⋯ ∧ dxⁿ ↦ ∫ a θ dLⁿ` as in 2.35 (∗)).  For `a ∈ C_c^∞(U)`, the form `ω = a • vol`
with `vol = dx¹ ∧ ⋯ ∧ dxⁿ` is a test form on `U` with `ω(x)(e₁, …, eₙ) = a(x)`
(`wedgeCovectors_apply_det`: `vol(e) = det 1 = 1`), so the hypothesis gives
`∫ a (u - v) = ∫_U u a - ∫_U v a = 0`.  As `u - v` is locally integrable on the open set `U`, the
fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `u = v` a.e. on `U`. -/
theorem Submission.ind_top_form_density_ae_unique :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (u v : Eucl (m + 1) → ℝ), IsOpen U →
      (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) →
      (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn v K volume) →
      (∀ ω : TestFormOn U (m + 1),
        ∫ x in U, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume =
        ∫ x in U, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) →
      ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x = v x := by
  intro m U u v hU hu hv h
  -- Step 1: the volume covector `vol = dx¹ ∧ ⋯ ∧ dxⁿ` has `vol(e) = det 1 = 1`.
  obtain ⟨vol, hvol⟩ : ∃ vol : Covector (Eucl (m + 1)) (m + 1),
      vol (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), ?_⟩
    rw [wedgeCovectors_apply_det]
    have hI : (Matrix.of fun i j =>
        (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ) (EuclideanSpace.single j (1 : ℝ))) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    rw [hI, Matrix.det_one]
  -- Step 2: `u - v` is integrable on compact subsets of the open set `U`, so it is locally
  -- integrable on `U`.
  have hloc : LocallyIntegrableOn (fun x => u x - v x) U volume := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    exact (hu K hK hKU).sub (hv K hK hKU)
  -- Step 3: the fundamental lemma; it remains to show `∫ a • (u - v) = 0` for `a ∈ C_c^∞(U)`.
  have key : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → u x - v x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun a ha ha_cs ha_sub => ?_
    -- Step 4: `ω = a • vol` is a test form on `U` with `ω(x)(e) = a(x)`.
    let ω : TestFormOn U (m + 1) :=
      ⟨fun x => a x • vol,
        ⟨⟨ha.smul contDiff_const, ha_cs.smul_right⟩,
          (tsupport_smul_subset_left _ _).trans ha_sub⟩⟩
    have hω : ∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) = a x := by
      intro x
      simp [ω, hvol]
    -- Step 5: the hypothesis for `ω` reads `∫_U u a = ∫_U v a`.
    have hua := h ω
    simp only [hω] at hua
    -- Step 6: `w a` is integrable for `w ∈ {u, v}`: it is integrable on the compact set
    -- `tsupport a ⊆ U` and vanishes outside it.
    have hK : IsCompact (tsupport a) := ha_cs
    have hint : ∀ w : Eucl (m + 1) → ℝ,
        (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn w K volume) →
        IntegrableOn (fun x => w x * a x) U volume := by
      intro w hw
      have h1 : IntegrableOn (fun x => w x * a x) (tsupport a) volume :=
        (hw _ hK ha_sub).mul_continuousOn ha.continuous.continuousOn hK
      have h2 : Integrable (fun x => w x * a x) volume := by
        rw [← integrableOn_iff_integrable_of_support_subset]
        · exact h1
        · intro x hx
          apply subset_tsupport
          intro hax
          apply hx
          simp [hax]
      exact h2.integrableOn
    -- Step 7: `a = 0` off `U`, so `∫ a • (u - v) = ∫_U u a - ∫_U v a = 0`.
    have hzero : ∀ x, x ∉ U → a x • (u x - v x) = 0 := by
      intro x hx
      have : a x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (ha_sub hx'))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hsplit : ∀ x, a x • (u x - v x) = u x * a x - v x * a x := by
      intro x
      simp only [smul_eq_mul]
      ring
    simp only [hsplit]
    rw [integral_sub (hint u hu) (hint v hv), hua, sub_self]
  -- Step 8: conclusion.
  filter_upwards [key] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-- A top-dimensional integer multiplicity current has an integer density (Simon Ch. 6, 2.35 (∗),
`T(ω) = ∫ aθ dLⁿ` for `ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, with `θ` integer-valued as at the end of the Proof of
8.2, p. 179).  Write `X = τ(M, θ, ξ)` in `U ⊆ ℝⁿ`, `n = m + 1`, and `e = (e₁, …, eₙ)`; on `ℝⁿ`,
`Hⁿ = μHE[n]` is Lebesgue measure.  By `Submission.ind_top_orthonormal_frame_sign`,
`ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`, so `ξ(x)(α) = σ(x) α(e)` with the sign
`σ(x) = ξ(x)(dx¹ ∧ ⋯ ∧ dxⁿ) = ±1`.  The density is `u = θσ` on `M` and `u = 0` off `M`. -/
theorem Submission.ind_top_dim_integer_density :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (X : GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity X → ∃ u : Eucl (m + 1) → ℝ,
        (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∃ k : ℤ, u x = k) ∧
        (∀ K : Set (Eucl (m + 1)), IsCompact K → K ⊆ U → IntegrableOn u K volume) ∧
        ∀ ω : TestFormOn U (m + 1), X ω = ∫ x in U, u x *
          (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
            (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume := by
  intro m U X hX
  -- Step 1: `X = τ(M, θ, ξ)` with `θ` integer-valued on `M`; `μHE[m + 1]` is `volume`.
  obtain ⟨M, θ, ξ, hT, hθ, hXω⟩ := hX
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  have hM : NullMeasurableSet M volume := by
    simpa only [hvol] using hT.nullMeasurableSet
  have hξ : AEStronglyMeasurable ξ (volume.restrict M) := by
    simpa only [hvol] using hT.aestronglyMeasurable
  have horients := hT.orients
  rw [hvol] at horients
  set e : Fin (m + 1) → Eucl (m + 1) := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- Step 2: the volume covector `vol = dx¹ ∧ ⋯ ∧ dxⁿ` has `vol(e) = det 1 = 1`.
  set vol : Covector (Eucl (m + 1)) (m + 1) :=
    wedgeCovectors (m + 1) fun j => EuclideanSpace.proj j with hvol_def
  have hvol_e : vol e = 1 := by
    rw [hvol_def, wedgeCovectors_apply_det]
    convert Matrix.det_one (n := Fin (m + 1)) (R := ℝ)
    ext i j
    simp [he, Matrix.one_apply]
  -- Step 3: `ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`.
  have hsign : ∀ᵐ x ∂volume.restrict M, ξ x = simpleNVector e ∨ ξ x = -simpleNVector e := by
    filter_upwards [horients] with x hx
    obtain ⟨τ, hτ, -, hξτ⟩ := hx
    rcases Submission.ind_top_orthonormal_frame_sign (m + 1) τ hτ with h | h <;>
      rcases hξτ with hξτ | hξτ
    · exact Or.inl (hξτ.trans h)
    · exact Or.inr (by rw [hξτ, h])
    · exact Or.inr (hξτ.trans h)
    · refine Or.inl (ContinuousLinearMap.ext fun α => ?_)
      rw [hξτ, _root_.neg_apply, h, _root_.neg_apply, neg_neg]
  -- Step 4: the sign `σ(x) = ξ(x)(vol)`; a.e. on `M`, `σ = ±1` and `ξ(x)(α) = σ(x) α(e)`.
  set σ : Eucl (m + 1) → ℝ := fun x => ξ x vol
  have hσm : AEStronglyMeasurable σ (volume.restrict M) :=
    (continuous_eval_const vol).comp_aestronglyMeasurable hξ
  have hσ : ∀ᵐ x ∂volume.restrict M, (σ x = 1 ∨ σ x = -1) ∧
      ∀ α : Covector (Eucl (m + 1)) (m + 1), ξ x α = σ x * α e := by
    filter_upwards [hsign] with x hx
    rcases hx with hx | hx
    · have h1 : σ x = 1 := by
        show ξ x vol = 1
        rw [hx, simpleNVector_apply, hvol_e]
      exact ⟨Or.inl h1, fun α => by rw [h1, one_mul, hx, simpleNVector_apply]⟩
    · have h1 : σ x = -1 := by
        show ξ x vol = -1
        rw [hx, _root_.neg_apply, simpleNVector_apply, hvol_e]
      exact ⟨Or.inr h1, fun α => by
        rw [h1, neg_one_mul, hx, _root_.neg_apply, simpleNVector_apply]⟩
  -- Step 5: `u = θσ` on `M` and `u = 0` off `M`.
  refine ⟨M.indicator fun x => θ x * σ x, ?_, ?_, ?_⟩
  · -- Step 6: `u` is integer-valued a.e.
    filter_upwards [(ae_restrict_iff'₀ hM).1 hσ] with x hx
    by_cases hxM : x ∈ M
    · obtain ⟨k, hk⟩ := hθ x hxM
      rcases (hx hxM).1 with h1 | h1
      · exact ⟨k, by simp [Set.indicator_of_mem hxM, hk, h1]⟩
      · exact ⟨-k, by simp [Set.indicator_of_mem hxM, hk, h1]⟩
    · exact ⟨0, by simp [Set.indicator_of_notMem hxM]⟩
  · -- Step 7: `θ` is integrable on `M ∩ K` and `|σ| ≤ 1`, so `u` is integrable on `K`.
    intro K hK hKU
    rw [integrableOn_indicator_iff hM]
    have hθK : IntegrableOn θ (M ∩ K) volume := by
      simpa only [hvol] using hT.integrableOn K hK hKU
    refine Integrable.mul_bdd (c := 1) hθK
      (hσm.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Set.inter_subset_left : M ∩ K ⊆ M) hσ] with x hx
    rcases hx.1 with h1 | h1 <;> simp [h1]
  · -- Step 8: `X(ω) = ∫_M θσ ω(e) dx = ∫_U u ω(e) dx`.
    intro ω
    have hMU : NullMeasurableSet M (volume.restrict U) := hM.mono Measure.restrict_le_self
    rw [hXω ω, tauAction, hvol]
    calc ∫ x in M, θ x * ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) ∂volume
        = ∫ x in M, θ x * σ x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hσ] with x hx
          rw [hx.2]
          ring
      _ = ∫ x in U, M.indicator (fun x =>
            θ x * σ x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e) x ∂volume := by
          rw [integral_indicator₀ hMU, Measure.restrict_restrict₀ hMU,
            Set.inter_eq_left.2 hT.subset]
      _ = ∫ x in U, M.indicator (fun x => θ x * σ x) x *
            (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x e ∂volume := by
          congr 1
          funext x
          by_cases hx : x ∈ M <;> simp [hx]

/-- A constant multiple `c [[U]]` of a nonempty open `U ⊆ ℝⁿ` is integer multiplicity only if
`c ∈ ℤ` (Simon Ch. 6, end of the proof of 8.2, p. 179: "`θ ≡ θ(x)` in `B₁ⁿ(0)`; thus
`θ(x) ∈ ℤ`").  An integer multiplicity `X ∈ 𝒟ₙ(U)` acts as `X(ω) = ∫_U u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`
with `u` a.e. integer-valued and integrable on compact subsets of `U`; the constant `c` is a
second such density of `X`, so `c = u` a.e. on `U`, and `Lⁿ(U) > 0`. -/
theorem Submission.ind_const_multiple_integer :
    ∀ (m : ℕ) (U : Set (Eucl (m + 1))) (c : ℝ) (X : GeometricCurrentOn U (m + 1)), IsOpen U →
      U.Nonempty → IsIntegerMultiplicity X →
      (∀ ω : TestFormOn U (m + 1),
        X ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume) → ∃ k : ℤ, c = k := by
  intro m U c X hU hne hX hXc
  -- `X(ω) = ∫_U u ω(e) dx` with `u` a.e. integer-valued and integrable on compacts of `U`.
  obtain ⟨u, hu_int, hu_loc, hu_rep⟩ := Submission.ind_top_dim_integer_density m U X hX
  -- The constant `c` is another density of `X`, hence `c = u` a.e. on `U`.
  have hcu : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∈ U → c = u x :=
    Submission.ind_top_form_density_ae_unique m U (fun _ => c) u hU
      (fun K hK _ => integrableOn_const hK.measure_ne_top) hu_loc
      (fun ω => by rw [integral_const_mul, ← hXc]; exact hu_rep ω)
  -- If `c ∉ ℤ`, a.e. point lies outside `U`, contradicting `Lⁿ(U) > 0` for open `U ≠ ∅`.
  by_contra hc
  have hnull : (volume : Measure (Eucl (m + 1))) U = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hcu, hu_int] with x hx ⟨k, hk⟩ hxU
    exact hc ⟨k, (hx hxU).trans hk⟩
  exact (hU.measure_pos volume hne).ne' hnull

/-- **Integrality of a planar weak limit of integer multiplicity cycles** (Simon Ch. 6, Proof of
8.2, displays (8)–(10), and Remark 3.12).  Let `Q = span τ` be the `(m + 1)`-plane spanned by an
orthonormal `τ`, and let `Y_k` be integer multiplicity cycles with `sup_k M_{B_2(0)}(Y_k) < ∞` and
`Y_k ⇀ c[[Q]]` on forms supported in `B_2(0)`.  Then `c ∈ ℤ`.  Take the coordinates
`p(y) = (⟪τ_i, y⟫)_i` and the distance `d` to `Q`.  Slicing by `d` localizes the `Y_k` to integer
multiplicity currents `Z_k` with bounded mass and boundary mass on the cylinder
`{|p| < 1, d < 3/4}` (`ind_pi_localized_cycles`).  Their push-forwards by `p` converge weakly to
`c[[B_1(0)]]` in `ℝ^{m+1}` (`ind_pi_projected_limit`).  So `c[[B_1(0)]]` is integer multiplicity by
the top-dimensional case of 8.2, and `c ∈ ℤ` (`ind_const_multiple_integer`). -/
theorem Submission.ind_plane_multiplicity_integer : SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → (∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Xj : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (W : Set (Eucl P)) (φ : Eucl P → ℝ), WeaklyConvergesOn Xj X → IsOpen W → W ⊆ U → (⨆ j, (Xj j).massOn W) < ∞ → ContinuousOn φ U → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ (Rj : ℕ → GeometricCurrentOn U k) (R : GeometricCurrentOn U k), (∀ j, IsRestriction (Xj (ψ j)) {x | x ∈ U ∧ φ x < s} (Rj j)) → IsRestriction X {x | x ∈ U ∧ φ x < s} R → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → Tendsto (fun j => Rj j ω) atTop (𝓝 (R ω))) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ W → {x | x ∈ U ∧ φ x ≤ s} ⊆ K → WeaklyConvergesOn Rj R)) → (LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)) → (∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → ∀ (P m : ℕ) (τ : Fin (m + 1) → Eucl P) (c : ℝ) (Y : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), Orthonormal ℝ τ → (∀ k, IsIntegerMultiplicity (Y k)) → (∀ k, (Y k).boundary = 0) → (⨆ k, (Y k).massOn (ball (0 : Eucl P) 2)) < ∞ → (∀ ω : TestFormOn (univ : Set (Eucl P)) (m + 1), tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ ball (0 : Eucl P) 2 → Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ z in (Submodule.span ℝ (Set.range τ) : Set (Eucl P)), (ω : DifferentialForm (Eucl P) (m + 1)) z τ ∂(μHE[m + 1] : Measure (Eucl P))))) → ∃ k : ℤ, c = k := by
  intro hST hLPF hRWL hSPF hTOP P m τ c Y hτ hYim hYbd hYmass hYlim
  -- Coordinates `p(y) = (⟪τ_i, y⟫)_i` with respect to `τ`, and the distance `d` to `Q = span τ`.
  obtain ⟨p, hp⟩ : ∃ p : Eucl P →L[ℝ] Eucl (m + 1), ∀ y i, p y i = inner ℝ (τ i) y :=
    ⟨(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi fun i => innerSL ℝ (τ i), fun y i => by simp⟩
  obtain ⟨d, hd⟩ : ∃ d : Eucl P → ℝ, ∀ y, d y = ‖y - ∑ i, inner ℝ (τ i) y • τ i‖ :=
    ⟨_, fun _ => rfl⟩
  -- Steps 1–7 (printed (8)–(9)): slicing by `d` localizes the `Y_k` to the cylinder.
  obtain ⟨γ, Z, hγ0, hγ, hZim, hZsupp, hZmass, hZlim⟩ :=
    Submission.ind_pi_localized_cycles hST hRWL P m τ c Y p d hτ hp hd hYim hYbd hYmass hYlim
  -- The current `S = c[[B_1(0)]]` in `ℝ^{m+1}`, represented by `(Lᵐ⁺¹ ⌞ B_1(0), c e₁ ∧ ⋯ ∧ eₘ₊₁)`.
  obtain ⟨S, hS⟩ := Submission.ind_pi_constant_vector_current (m + 1) (m + 1)
    (ball (0 : Eucl (m + 1)) 1) (volume.restrict (ball (0 : Eucl (m + 1)) 1))
    (c • simpleNVector fun i => EuclideanSpace.single i (1 : ℝ))
    fun K hK => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top
  have hSval : ∀ ω : TestFormOn (ball (0 : Eucl (m + 1)) 1) (m + 1), S ω =
      c * ∫ x in ball (0 : Eucl (m + 1)) 1, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
        (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume := by
    intro ω
    rw [(hS ω).2, ← integral_const_mul]
    simp only [smul_apply, simpleNVector_apply, smul_eq_mul]
  -- Steps 8–9 (printed (10)): the push-forwards `p_# Z_k` converge weakly to `S`.
  obtain ⟨S', hS'im, hS'mass, hS'conv⟩ := Submission.ind_pi_projected_limit hLPF hSPF P m τ c γ
    p d Z S hτ hp hd hγ0 hγ hZim hZsupp hZmass hZlim hSval
  -- Step 10 (Remark 3.12): by the top-dimensional case of 8.2, `S` is integer multiplicity.
  have hSim : IsIntegerMultiplicity S :=
    hTOP m (ball (0 : Eucl (m + 1)) 1) isOpen_ball S' S hS'im hS'mass hS'conv
  -- Step 11: an integer multiplicity `c[[B_1(0)]]` has `c ∈ ℤ`.
  exact Submission.ind_const_multiple_integer m (ball (0 : Eucl (m + 1)) 1) c S isOpen_ball
    ⟨0, mem_ball_self one_pos⟩ hSim hSval
/-- A rectifiable current whose multiplicity is `Hⁿ`-a.e. a natural number on `M` is integer
multiplicity (Simon Ch. 6, proof of 8.2, conclusion).  The exceptional set
`N = {x ∈ M : θ(x) ∉ ℕ}` is `Hⁿ`-null, so `M' = M ∖ N` carries the same current and, as
`Hⁿ(η_{x,r} N) = r⁻ⁿ Hⁿ(N) = 0`, the same weighted approximate tangent spaces. -/
theorem Submission.ind_ae_integer_multiplicity :
    ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P))
      (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ →
      (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) →
      (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∃ k : ℕ, θ x = k) →
      IsIntegerMultiplicity T := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P n U T M θ ξ hM hT hθ
  -- `M' = {x ∈ M : θ(x) ∈ ℕ}` differs from `M` by an `Hⁿ`-null set.
  set M' : Set (Eucl P) := {x | x ∈ M ∧ ∃ k : ℕ, θ x = k}
  have hM'M : M' ⊆ M := fun x hx => hx.1
  have hae : M' =ᵐ[(μHE[n] : Measure (Eucl P))] M := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [(ae_restrict_iff'₀ hM.nullMeasurableSet).mp hθ] with x hx
    exact ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
  have hrestrict : (μHE[n] : Measure (Eucl P)).restrict M' =
      (μHE[n] : Measure (Eucl P)).restrict M :=
    Measure.restrict_congr_set hae
  -- `y ↦ x + r • y` inverts `η_{x,r}`, so `η_{x,r}` is injective.
  have hinv : ∀ (x : Eucl P) (r : ℝ), r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro x r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- `η_{x,r}` maps `Hⁿ`-null sets to `Hⁿ`-null sets: `Hⁿ(η_{x,r} Z) = r⁻ⁿ Hⁿ(Z)`.
  have hnull : ∀ (x : Eucl P) (r : ℝ), r ≠ 0 → ∀ Z : Set (Eucl P),
      (μHE[n] : Measure (Eucl P)) Z = 0 → (μHE[n] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro x r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- The blow-ups `η_{x,r}(M)` and `η_{x,r}(M')` are `Hⁿ`-a.e. equal, so the weighted tangent
  -- spaces of `(M, θ)` and `(M', θ)` agree.
  have htan : ∀ (x : Eucl P) (L : Submodule ℝ (Eucl P)),
      HasWeightedApproximateTangentSpaceAt n M θ x L →
        HasWeightedApproximateTangentSpaceAt n M' θ x L := by
    intro x L hL
    refine ⟨hL.1, fun f => (hL.2 f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hinj : Function.Injective (blowUpMap x r) :=
      Function.LeftInverse.injective (g := fun w => x + r • w) (hinv x r hr.ne')
    refine setIntegral_congr_set ?_
    rw [ae_eq_set, ← Set.image_sdiff hinj, ← Set.image_sdiff hinj]
    exact ⟨hnull x r hr.ne' _ (ae_eq_set.mp hae).2, hnull x r hr.ne' _ (ae_eq_set.mp hae).1⟩
  refine ⟨M', θ, ξ, ⟨hM'M.trans hM.subset, hM.nullMeasurableSet.congr hae.symm,
    hM.countablyRectifiable.mono hM'M, fun x hx => hM.pos x (hM'M hx),
    fun K hK hKU => (hM.integrableOn K hK hKU).mono_set (Set.inter_subset_inter_left K hM'M),
    ?_, ?_⟩, fun x hx => hx.2, fun ω => ?_⟩
  · rw [hrestrict]
    exact hM.aestronglyMeasurable
  · rw [hrestrict]
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, hL, hξ⟩ := hx
    exact ⟨τ, hτ, htan x _ hL, hξ⟩
  · rw [hT ω]
    unfold tauAction
    rw [hrestrict]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
