import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality

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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
