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

/-- The exhaustion function of Simon Ch. 6, 6.2 (p. 169, proof): for open `U ⊆ ℝ^P` there is a
1-Lipschitz `φ` whose superlevel sets `{φ ≥ t}`, `t > 0`, are compact subsets of `U`, and which has
a positive lower bound on every compact `K ⊆ U`.  With `g(x) = 1/(1 + |x|)`, take `φ = g` if
`U = ℝ^P` and `φ = min(dist(·, ℝ^P ∖ U), g)` otherwise. -/
theorem Submission.polyhedral_approx_exhaustion_function : ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ φ : Eucl P → ℝ, LipschitzWith 1 φ ∧ (∀ t : ℝ, 0 < t → IsCompact {x | t ≤ φ x} ∧ {x | t ≤ φ x} ⊆ U) ∧ ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ φ x := by
  intro P U hU
  -- Step 1: `g(x) = 1/(1 + |x|)` is positive and 1-Lipschitz, and `{g ≥ t} ⊆ B̄(0, 1/t)`.
  let g : Eucl P → ℝ := fun x => 1 / (1 + ‖x‖)
  have hg_pos : ∀ x, 0 < g x := fun x => by positivity
  have hg_lip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hx : 0 < 1 + ‖x‖ := by positivity
    have hy : 0 < 1 + ‖y‖ := by positivity
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm,
      div_sub_div _ _ hx.ne' hy.ne', abs_div, abs_of_pos (mul_pos hx hy), div_le_iff₀ (mul_pos hx hy)]
    calc |1 * (1 + ‖y‖) - (1 + ‖x‖) * 1| = |‖y‖ - ‖x‖| := by ring_nf
      _ ≤ ‖y - x‖ := abs_norm_sub_norm_le y x
      _ = ‖x - y‖ := norm_sub_rev y x
      _ ≤ ‖x - y‖ * ((1 + ‖x‖) * (1 + ‖y‖)) :=
        le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [norm_nonneg x, norm_nonneg y])
  have hg_ball : ∀ t : ℝ, 0 < t → ∀ x, t ≤ g x → x ∈ closedBall (0 : Eucl P) (1 / t) := by
    intro t ht x hx
    have h1 : 0 < 1 + ‖x‖ := by positivity
    have h2 : t * (1 + ‖x‖) ≤ 1 := (le_div_iff₀ h1).mp hx
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ ht]
    nlinarith
  -- Steps 2–3 share one argument: a 1-Lipschitz `φ ≤ g`, positive on `U` and `≤ 0` off `U`,
  -- has compact superlevel sets `{φ ≥ t} ⊆ U` and a positive minimum on compact `K ⊆ U`.
  suffices key : ∀ φ : Eucl P → ℝ, LipschitzWith 1 φ → (∀ x, φ x ≤ g x) → (∀ x ∈ U, 0 < φ x) →
      (∀ x, x ∉ U → φ x ≤ 0) → LipschitzWith 1 φ ∧
        (∀ t : ℝ, 0 < t → IsCompact {x | t ≤ φ x} ∧ {x | t ≤ φ x} ⊆ U) ∧
        ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ φ x by
    by_cases hUc : U = univ
    · -- Step 2: `U = ℝ^P`, `φ = g`.
      exact ⟨g, key g hg_lip (fun x => le_rfl) (fun x _ => hg_pos x)
        (fun x hx => absurd (hUc ▸ mem_univ x) hx)⟩
    · -- Step 3: `F = ℝ^P ∖ U` is closed and nonempty, `φ = min(dist(·, F), g)`.
      have hne : (Uᶜ).Nonempty := nonempty_compl.mpr hUc
      have hcl : IsClosed Uᶜ := hU.isClosed_compl
      refine ⟨fun x => min (infDist x Uᶜ) (g x), key _ ?_ (fun x => min_le_right _ _)
        (fun x hx => ?_) (fun x hx => ?_)⟩
      · have h := (lipschitz_infDist_pt Uᶜ).min hg_lip
        rwa [max_self] at h
      · exact lt_min ((hcl.notMem_iff_infDist_pos hne).mp fun h => h hx) (hg_pos x)
      · exact (min_le_left _ _).trans (infDist_zero_of_mem hx).le
  intro φ hφ hφg hφpos hφneg
  refine ⟨hφ, fun t ht => ⟨?_, fun x hx => ?_⟩, fun K hK hKU => ?_⟩
  · -- `{φ ≥ t}` is closed and lies in `B̄(0, 1/t)`.
    exact (isCompact_closedBall (0 : Eucl P) (1 / t)).of_isClosed_subset
      (isClosed_le continuous_const hφ.continuous) fun x hx => hg_ball t ht x (hx.trans (hφg x))
  · -- `φ ≤ 0 < t` off `U`.
    by_contra hxU
    exact absurd (ht.trans_le hx) (not_lt.mpr (hφneg x hxU))
  · -- A positive minimum on `K` (`δ = 1` if `K = ∅`).
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact ⟨1, one_pos, fun x hx => absurd hx (notMem_empty x)⟩
    · obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne hφ.continuous.continuousOn
      exact ⟨φ x₀, hφpos x₀ (hKU hx₀K), fun x hx => hmin hx⟩
/-- Boundary mass transfer through a smooth cut-off (Simon Ch. 6, 6.2, proof): if `X` and `A`
agree on any two test forms that coincide on `V`, where `closure V` is a compact subset of the
open set `W ⊆ U₂`, then `M(∂X) ≤ M_W(∂A)`.  For `ψ` admissible for `M(∂X)` and a smooth cut-off
`χ`, `0 ≤ χ ≤ 1`, `χ = 1` near `closure V` with compact support in `W`, the form `χψ` is
admissible for `M_W(∂A)`, and `d(χψ) = dψ` on `V` gives `∂X(ψ) = X(dψ) = A(d(χψ)) = ∂A(χψ)`. -/
theorem Submission.polyhedral_approx_boundary_mass_cutoff : ∀ (P m : ℕ) (U₁ U₂ W V : Set (Eucl P)) (X : GeometricCurrentOn U₁ (m + 1)) (A : GeometricCurrentOn U₂ (m + 1)), IsOpen W → W ⊆ U₂ → IsCompact (closure V) → closure V ⊆ W → (∀ (η : TestFormOn U₁ (m + 1)) (η' : TestFormOn U₂ (m + 1)), (∀ x ∈ V, (η : DifferentialForm (Eucl P) (m + 1)) x = (η' : DifferentialForm (Eucl P) (m + 1)) x) → X η = A η') → X.boundary.mass ≤ A.boundary.massOn W := by
  intro P m U₁ U₂ W V X A hW hWU hV hVW hXA
  -- Step 1: a compact `C = cthickening δ (closure V) ⊆ W` with `closure V ⊆ interior C`.
  obtain ⟨δ, hδ, hCW⟩ := hV.exists_cthickening_subset_open hW hVW
  have hCc : IsCompact (cthickening δ (closure V)) := hV.cthickening
  have hVC : closure V ⊆ interior (cthickening δ (closure V)) :=
    (self_subset_thickening hδ _).trans
      (interior_maximal (thickening_subset_cthickening δ _) isOpen_thickening)
  -- Step 2: smooth Urysohn: `0 ≤ χ ≤ 1`, `χ = 1` near `closure V`, `χ = 0` off `C`.
  obtain ⟨χ, hχ1, hχ0, hχI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Eucl P)) (n := ⊤) isClosed_closure hVC
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : Eucl P → ℝ) :=
    contMDiff_iff_contDiff.mp χ.contMDiff
  -- Step 3: homogeneity of the Euclidean coefficient norm.
  have hhom : ∀ (c : ℝ) (α : Covector (Eucl P) m),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- Step 7: it suffices to bound each admissible evaluation of `∂X`.
  refine sSup_le ?_
  rintro _ ⟨ψ, hψ, rfl⟩
  -- Step 4: the cut-off form `ψ' = χψ` is admissible for `M_W(∂A)`.
  set ψf : DifferentialForm (Eucl P) m := (ψ : DifferentialForm (Eucl P) m)
  let ψ'f : DifferentialForm (Eucl P) m := fun x => χ x • ψf x
  have hψ'0 : ∀ x ∉ cthickening δ (closure V), ψ'f x = 0 := fun x hx => by
    simp only [ψ'f, hχ0 x hx, zero_smul]
  have hψ'C : tsupport ψ'f ⊆ cthickening δ (closure V) :=
    closure_minimal (Function.support_subset_iff'.mpr hψ'0) isClosed_cthickening
  let ψ' : TestFormOn U₂ m :=
    ⟨ψ'f, ⟨⟨hχs.smul ψ.property.1.1, HasCompactSupport.intro hCc hψ'0⟩, hψ'C.trans (hCW.trans hWU)⟩⟩
  have hψ'adm : ψ' ∈ massAdmissibleOn U₂ m W := by
    refine ⟨hψ'C.trans hCW, fun x => ?_⟩
    change covectorEuclideanNorm (χ x • ψf x) ≤ 1
    rw [hhom, abs_of_nonneg (hχI x).1]
    calc χ x * covectorEuclideanNorm (ψf x) ≤ 1 * 1 :=
          mul_le_mul (hχI x).2 (hψ.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  -- Step 5: `dψ' = dψ` on `V`, since `ψ' = ψ` near every point of `closure V`.
  have hloc : ∀ x ∈ V, extDeriv ψf x = extDeriv ψ'f x := by
    intro x hx
    apply Filter.EventuallyEq.extDeriv_eq
    filter_upwards [nhds_le_nhdsSet (subset_closure hx) hχ1] with y hy
    simp only [ψ'f, hy, one_smul]
  -- Step 6: `∂X(ψ) = X(dψ) = A(dψ') = ∂A(ψ') ≤ M_W(∂A)`.
  have key : X.boundary ψ = A.boundary ψ' := by
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply]
    exact hXA _ _ hloc
  calc ENNReal.ofReal (X.boundary ψ) = ENNReal.ofReal (A.boundary ψ') := by rw [key]
    _ ≤ A.boundary.massOn W := A.boundary.le_massOn hψ'adm
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

/-- **Simon Ch. 6, (2.9) (p. 136).**  Restrictions `T ⌞ A` exist for every measure representation
`(μ, v)` of `T` and Borel `A`, and every restriction has locally finite mass.  For compact
`K ⊆ U`, testing `T` with `χ_K dx^I` (`χ_K` a smooth cut-off equal to `1` on `K`) shows that the
coordinates `v(·)(dx^I)` are `μ`-integrable on `K`; by `polyhedral_approx_pairing_expansion`,
`|⟨α, v(x)⟩| ≤ b ∑_I |v(x)(dx^I)|` whenever every coefficient satisfies `|α_I| ≤ b`.  Taking
`b = ‖α‖` gives the sequential continuity of `ω ↦ ∫_A ⟨ω, v⟩ dμ`; taking `b = 1` bounds `S(ω)` by
`∫_{closure W} ∑_I |v(·)(dx^I)| dμ` for every `ω` admissible for `M_W`. -/
theorem Submission.polyhedral_approx_restriction_exists : ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U n, (∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → ∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U n, IsRestriction T A S) ∧ ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U n), IsRestriction T A S → ∀ W : Set (Eucl P), CompactlyContainedOpen W U → S.massOn W < ∞ := by
  intro P n U hU T
  -- `|α_I| = |α(e_{I 0}, …, e_{I (n-1)})| ≤ ‖α‖`.
  have coord_le : ∀ (α : Covector (Eucl P) n) (I : SimonMultiIndex n P),
      |euclideanCovectorCoordinate α I| ≤ ‖α‖ := by
    intro α I
    calc |euclideanCovectorCoordinate α I|
        = ‖α (fun j => EuclideanSpace.single (I j) (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖α‖ * ∏ j, ‖EuclideanSpace.single (I j) (1 : ℝ)‖ := α.le_opNorm _
      _ = ‖α‖ := by simp
  -- For a representation `(μ, v)` and a compact `K ⊆ U`, the coordinates `v(·)(dx^I)` are
  -- `μ`-integrable on `K`, and `G = ∑_I |v(·)(dx^I)|` dominates the pairing.
  have key : ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
      IsMeasureRepresentation T μ v → ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
      ∃ G : Eucl P → ℝ, (∀ x, 0 ≤ G x) ∧ IntegrableOn G K μ ∧
        ∀ (x : Eucl P) (α : Covector (Eucl P) n) (b : ℝ),
          (∀ I : SimonMultiIndex n P, |euclideanCovectorCoordinate α I| ≤ b) →
            |v x α| ≤ b * G x := by
    intro μ v hrep K hK hKU
    -- A smooth cut-off `χ`, equal to `1` on `K`, with `tsupport χ ⊆ cthickening r K ⊆ U`.
    obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
    obtain ⟨χ, hχ, -, hχs, hχK⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := r) (E := K)) hK.isClosed (self_subset_thickening hr K)
    have hχt : tsupport χ ⊆ cthickening r K := by
      rw [tsupport, hχs]
      exact closure_thickening_subset_cthickening r K
    have hcoord : ∀ I : SimonMultiIndex n P, IntegrableOn
        (fun x => v x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j)))) K μ := by
      intro I
      have hmem : (fun x => χ x • wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) :
          DifferentialForm (Eucl P) n) ∈ testFormOnSubmodule (E := Eucl P) U n :=
        ⟨⟨hχ.smul contDiff_const, hK.cthickening.of_isClosed_subset (isClosed_tsupport _)
            ((tsupport_smul_subset_left _ _).trans hχt)⟩,
          (tsupport_smul_subset_left _ _).trans (hχt.trans hrU)⟩
      refine (hrep ⟨_, hmem⟩).1.integrableOn.congr_fun (fun x hx => ?_)
        hK.isClosed.measurableSet
      show v x (χ x • _) = v x _
      rw [(hχK x).1 hx, one_smul]
    refine ⟨fun x => ∑ I : SimonMultiIndex n P,
        |v x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j)))|,
      fun x => Finset.sum_nonneg fun I _ => abs_nonneg _,
      integrable_finsetSum _ fun I _ => (hcoord I).abs, ?_⟩
    intro x α b hb
    beta_reduce
    rw [(Submission.polyhedral_approx_pairing_expansion P n (v x) α).1, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb I) (abs_nonneg _)
  refine ⟨fun μ v hrep A hA => ?_, fun A S hS W hW => ?_⟩
  · -- (a) `S(ω) = ∫_A ⟨ω, v⟩ dμ` is linear and sequentially continuous.
    let L : TestFormOn U n →ₗ[ℝ] ℝ :=
      { toFun := fun ω => ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ
        map_add' := fun ω η => by
          simp only [Submodule.coe_add, Pi.add_apply, map_add]
          exact integral_add (hrep ω).1.integrableOn (hrep η).1.integrableOn
        map_smul' := fun c ω => by
          simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
          exact integral_const_mul c _ }
    refine ⟨⟨L, fun ωs hconv => ?_⟩, hA, μ, v, hrep, fun ω => rfl⟩
    obtain ⟨K, hK, hKU, hsupp, -, hder⟩ := hconv
    obtain ⟨G, hG0, hGint, hGb⟩ := key μ v hrep K hK hKU
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hC0 : 0 ≤ ∫ x in K, G x ∂μ := setIntegral_nonneg hKm fun x _ => hG0 x
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ : 0 < ε / ((∫ x in K, G x ∂μ) + 1) := div_pos hε (by linarith)
    -- Eventually `‖ω_j(x)‖ < δ` on `K`, and `ω_j = 0` off `K`.
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hder 0) _ hδ] with j hj
    have hbound : ∀ x, ‖v x ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
        ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x := by
      intro x
      by_cases hx : x ∈ K
      · have hjx := hj x hx
        rw [Submodule.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
          norm_iteratedFDeriv_zero] at hjx
        rw [indicator_of_mem hx, Real.norm_eq_abs]
        exact (hGb x _ _ fun I => coord_le _ I).trans
          (mul_le_mul_of_nonneg_right hjx.le (hG0 x))
      · have h0 : (ωs j : DifferentialForm (Eucl P) n) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h)
        rw [h0, map_zero, norm_zero, indicator_of_notMem hx, mul_zero]
    have hint : Integrable (fun x => ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x) μ :=
      (IntegrableOn.integrable_indicator hGint hKm).const_mul _
    rw [dist_zero_right]
    calc ‖∫ x in A, v x ((ωs j : DifferentialForm (Eucl P) n) x) ∂μ‖
        ≤ ∫ x in A, ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x ∂μ :=
          norm_integral_le_of_norm_le hint.integrableOn (ae_of_all _ hbound)
      _ ≤ ∫ x, ε / ((∫ x in K, G x ∂μ) + 1) * K.indicator G x ∂μ :=
          integral_mono_measure Measure.restrict_le_self
            (ae_of_all _ fun x => mul_nonneg hδ.le (indicator_nonneg (fun y _ => hG0 y) x)) hint
      _ = ε / ((∫ x in K, G x ∂μ) + 1) * ∫ x in K, G x ∂μ := by
          rw [integral_const_mul, integral_indicator hKm]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  · -- (b) For `ω` admissible for `M_W`, `S(ω) ≤ ∫_{closure W} G dμ`.
    obtain ⟨-, μ, v, hrep, hSω⟩ := hS
    obtain ⟨-, hWc, hWU⟩ := hW
    obtain ⟨G, hG0, hGint, hGb⟩ := key μ v hrep (closure W) hWc hWU
    have hKm : MeasurableSet (closure W) := isClosed_closure.measurableSet
    have hint : Integrable ((closure W).indicator G) μ :=
      IntegrableOn.integrable_indicator hGint hKm
    refine lt_of_le_of_lt (sSup_le ?_) (ENNReal.ofReal_lt_top (r := ∫ x in closure W, G x ∂μ))
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have hbound : ∀ x, ‖v x ((ω : DifferentialForm (Eucl P) n) x)‖ ≤
        (closure W).indicator G x := by
      intro x
      by_cases hx : x ∈ closure W
      · rw [indicator_of_mem hx, Real.norm_eq_abs]
        have h := hGb x ((ω : DifferentialForm (Eucl P) n) x) 1
          fun I => ((Submission.polyhedral_approx_pairing_expansion P n (v x) _).2 I).trans (hω1 x)
        rwa [one_mul] at h
      · have h0 : (ω : DifferentialForm (Eucl P) n) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (subset_closure (hωW h))
        rw [h0, map_zero, norm_zero, indicator_of_notMem hx]
    rw [hSω ω]
    calc ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ
        ≤ ‖∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ‖ := Real.le_norm_self _
      _ ≤ ∫ x in A, (closure W).indicator G x ∂μ :=
          norm_integral_le_of_norm_le hint.integrableOn (ae_of_all _ hbound)
      _ ≤ ∫ x, (closure W).indicator G x ∂μ :=
          integral_mono_measure Measure.restrict_le_self
            (ae_of_all _ (indicator_nonneg fun y _ => hG0 y)) hint
      _ = ∫ x in closure W, G x ∂μ := integral_indicator hKm

/-- Integer multiplicity truncation to an open `V ⊂⊂ U` (the step `T ⌞ V` of the proof of
Simon Ch. 6, 6.2): for `T = τ(M, θ, ξ)` integer multiplicity in `U`, the current
`X(ω) = ∫_{M ∩ V} θ ⟨ω, ξ⟩ dHⁿ` on `ℝ^P` is integer multiplicity, witnessed by the triple
`(M ∩ V, θ, ξ)`, and has finite mass `M(X) ≤ c_* ∫_{M ∩ V} θ dHⁿ`,
`c_* = ∑_I ‖dx^I‖`. -/
theorem Submission.polyhedral_approx_open_truncation : ∀ (P n : ℕ) (U V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → CompactlyContainedOpen V U → ∃ X : GeometricCurrentOn (univ : Set (Eucl P)) n, IsIntegerMultiplicity X ∧ X.mass < ∞ ∧ ∀ ω : TestFormOn (univ : Set (Eucl P)) n, X ω = tauAction n (M ∩ V) θ ξ ω := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P n U V M θ ξ hT hnat hV
  obtain ⟨hVo, hVc, hVU⟩ := hV
  -- Step 1: `θ` is integrable on `M ∩ closure V`, hence on `M' = M ∩ V`.
  have hθ : IntegrableOn θ (M ∩ V) (μHE[n] : Measure (Eucl P)) :=
    (hT.integrableOn (closure V) hVc hVU).mono_set (inter_subset_inter_right M subset_closure)
  have hθ' : Integrable θ ((μHE[n] : Measure (Eucl P)).restrict (M ∩ V)) := hθ
  have hnm : NullMeasurableSet (M ∩ V) (μHE[n] : Measure (Eucl P)) :=
    hT.nullMeasurableSet.inter hVo.measurableSet.nullMeasurableSet
  have hle : (μHE[n] : Measure (Eucl P)).restrict (M ∩ V) ≤
      (μHE[n] : Measure (Eucl P)).restrict M :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- Step 6: weighted tangent planes of `M` at points of the open set `V` are tangent planes
  -- of `M ∩ V`.  If `f = 0` off `B̄_R(0)` and `B_δ(x) ⊆ V`, then for `0 < r < δ / R` the
  -- blow-ups satisfy `η_{x,r}(M) ∩ B̄_R(0) = η_{x,r}(M ∩ V) ∩ B̄_R(0)`.
  have htan : ∀ x ∈ V, ∀ Q : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt n M θ x Q →
        HasWeightedApproximateTangentSpaceAt n (M ∩ V) θ x Q := by
    intro x hx Q h
    refine ⟨h.1, fun f => (h.2 f).congr' ?_⟩
    obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hVo x hx
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
    obtain ⟨hr0, hrδ⟩ := hr
    have hcut : ∀ S : Set (Eucl P),
        ∫ y in S, f y * θ (x + r • y) ∂(μHE[n] : Measure (Eucl P)) =
          ∫ y in S ∩ closedBall (0 : Eucl P) R, f y * θ (x + r • y)
            ∂(μHE[n] : Measure (Eucl P)) := by
      intro S
      rw [← setIntegral_indicator measurableSet_closedBall]
      congr 1
      funext y
      by_cases hy : y ∈ closedBall (0 : Eucl P) R
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        rw [hfR y hy.le, zero_mul]
    have hset : blowUpMap x r '' M ∩ closedBall (0 : Eucl P) R =
        blowUpMap x r '' (M ∩ V) ∩ closedBall (0 : Eucl P) R := by
      ext y
      constructor
      · rintro ⟨⟨z, hzM, rfl⟩, hyB⟩
        refine ⟨⟨z, ⟨hzM, hball ?_⟩, rfl⟩, hyB⟩
        rw [mem_closedBall, dist_zero_right] at hyB
        simp only [blowUpMap, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr0] at hyB
        rw [inv_mul_le_iff₀ hr0] at hyB
        rw [mem_ball, dist_eq_norm]
        calc ‖z - x‖ ≤ r * R := hyB
          _ < δ / R * R := by gcongr
          _ = δ := div_mul_cancel₀ δ hR.ne'
      · rintro ⟨⟨z, ⟨hzM, -⟩, rfl⟩, hyB⟩
        exact ⟨⟨z, hzM, rfl⟩, hyB⟩
    rw [hcut (blowUpMap x r '' M), hcut (blowUpMap x r '' (M ∩ V)), hset]
  -- Step 7: `(M ∩ V, θ, ξ)` is a rectifiable triple in `ℝ^P`.
  have hT' : IsRectifiableTriple (univ : Set (Eucl P)) n (M ∩ V) θ ξ := by
    refine ⟨subset_univ _, hnm, hT.countablyRectifiable.mono inter_subset_left,
      fun x hx => hT.pos x hx.1, fun K _ _ => hθ.mono_set inter_subset_left,
      hT.aestronglyMeasurable.mono_measure hle, ?_⟩
    filter_upwards [ae_mono hle hT.orients, ae_restrict_mem₀ hnm] with x hx hxMV
    obtain ⟨τ, hτ, hQ, hξ⟩ := hx
    exact ⟨τ, hτ, htan x hxMV.2 _ hQ, hξ⟩
  -- Step 2: `‖ξ(x)‖ ≤ 1` (`‖±τ₁ ∧ ⋯ ∧ τₙ‖ ≤ ∏ᵢ ‖τᵢ‖ = 1`) and, by the coordinate expansion
  -- of the pairing, `|⟨α, ξ(x)⟩| ≤ c_* |α|`, for `Hⁿ`-a.e. `x ∈ M ∩ V`.
  have hunit : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ V)), ‖ξ x‖ ≤ 1 := by
    filter_upwards [hT'.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    have hsimple : ‖simpleNVector τ‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
      rw [simpleNVector_apply, one_mul]
      simpa [hτ.norm_eq_one] using α.le_opNorm τ
    rcases hξ with hξ | hξ
    · rw [hξ]
      exact hsimple
    · rw [hξ]
      exact (norm_neg (simpleNVector τ)).trans_le hsimple
  set c : ℝ := ∑ I : SimonMultiIndex n P,
    ‖(wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) : Covector (Eucl P) n)‖ with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ V)),
      ∀ α : Covector (Eucl P) n, |ξ x α| ≤ c * covectorEuclideanNorm α := by
    filter_upwards [hunit] with x hx α
    obtain ⟨hexp, hcoord⟩ := Submission.polyhedral_approx_pairing_expansion P n (ξ x) α
    rw [hexp, hc, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun I _ => ?_)
    rw [abs_mul, mul_comm (‖_‖)]
    refine mul_le_mul (hcoord I) ?_ (abs_nonneg _) (covectorEuclideanNorm_nonneg α)
    calc |ξ x (wedgeCovectors n (fun j => EuclideanSpace.proj (I j)))|
        ≤ ‖ξ x‖ * ‖(wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) :
            Covector (Eucl P) n)‖ := (ξ x).le_opNorm _
      _ ≤ ‖(wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) : Covector (Eucl P) n)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hx
  have hpt : ∀ ω : DifferentialForm (Eucl P) n,
      ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ V)), ‖ξ x (ω x)‖ ≤ ‖ω x‖ := by
    intro ω
    filter_upwards [hunit] with x hx
    exact ((ξ x).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hx)
  -- Step 3: `F_ω = θ ⟨ω, ξ⟩` is `Hⁿ ⌞ (M ∩ V)`-integrable, and `X(ω) = ∫_{M ∩ V} F_ω dHⁿ` is
  -- linear in `ω`.
  have hint : ∀ ω : TestFormOn (univ : Set (Eucl P)) n,
      Integrable (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x))
        ((μHE[n] : Measure (Eucl P)).restrict (M ∩ V)) := by
    intro ω
    have hcont : Continuous (ω : DifferentialForm (Eucl P) n) := ω.property.1.1.continuous
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support ω.property.1.2
    have hmeas : AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Eucl P) n) x))
        ((μHE[n] : Measure (Eucl P)).restrict (M ∩ V)) :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hT'.aestronglyMeasurable.prodMk hcont.aestronglyMeasurable)
    refine hθ'.mul_bdd hmeas (c := B) ?_
    filter_upwards [hpt (ω : DifferentialForm (Eucl P) n)] with x hx
    exact hx.trans (hB x)
  let L : TestFormOn (univ : Set (Eucl P)) n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => tauAction n (M ∩ V) θ ξ ω
      map_add' := by
        intro ω η
        simp only [tauAction]
        rw [← integral_add (hint ω) (hint η)]
        congr 1
        funext x
        simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add]
      map_smul' := by
        intro a ω
        simp only [tauAction, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  -- Step 4: `ω_j → 0` in `𝒟ⁿ(ℝ^P)` gives `sup ‖ω_j‖ → 0`, and
  -- `|X(ω_j)| ≤ sup ‖ω_j‖ · ∫_{M ∩ V} |θ| dHⁿ`, so `X` is a current.
  have hcontL : ∀ ωs : ℕ → TestFormOn (univ : Set (Eucl P)) n,
      TestFormOnConverges ωs 0 → Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    intro ωs hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    set Θ : ℝ := ∫ x in M ∩ V, |θ x| ∂(μHE[n] : Measure (Eucl P)) with hΘ
    have hΘ0 : 0 ≤ Θ := integral_nonneg fun _ => abs_nonneg _
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (Θ + 1) := div_pos hε (by linarith)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hunif 0) _ hε'] with j hj
    have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Eucl P) n) x‖ ≤ ε / (Θ + 1) := by
      intro x
      by_cases hxK : x ∈ K
      · have h := hj x hxK
        have h0 : iteratedFDeriv ℝ 0
            (((0 : TestFormOn (univ : Set (Eucl P)) n)) : DifferentialForm (Eucl P) n) x = 0 := by
          ext m
          simp
        rw [h0, dist_zero_left, norm_iteratedFDeriv_zero] at h
        exact h.le
      · rw [image_eq_zero_of_notMem_tsupport fun h' => hxK (hsupp j h'), norm_zero]
        exact hε'.le
    have hLj : ‖L (ωs j)‖ ≤ ε / (Θ + 1) * Θ := by
      change ‖∫ x in M ∩ V, θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)
        ∂(μHE[n] : Measure (Eucl P))‖ ≤ ε / (Θ + 1) * Θ
      rw [hΘ, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hθ'.abs.const_mul _) ?_
      filter_upwards [hpt (ωs j : DifferentialForm (Eucl P) n)] with x hx
      rw [norm_mul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hx.trans (hsmall x)) (abs_nonneg _)
    rw [dist_zero_right]
    refine hLj.trans_lt ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  let X : GeometricCurrentOn (univ : Set (Eucl P)) n := ⟨L, hcontL⟩
  have hX : ∀ ω : TestFormOn (univ : Set (Eucl P)) n, X ω = tauAction n (M ∩ V) θ ξ ω :=
    fun ω => rfl
  -- Step 5: `M(X) ≤ c_* ∫_{M ∩ V} |θ| dHⁿ < ∞`, testing with `|ω| ≤ 1`.
  have hmass : X.mass ≤ ENNReal.ofReal
      (c * ∫ x in M ∩ V, |θ x| ∂(μHE[n] : Measure (Eucl P))) := by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hX ω, tauAction, ← integral_const_mul]
    refine (Real.le_norm_self _).trans (norm_integral_le_of_norm_le (hθ'.abs.const_mul c) ?_)
    filter_upwards [hbound] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm c]
    refine mul_le_mul_of_nonneg_left ((hx _).trans ?_) (abs_nonneg _)
    exact mul_le_of_le_one_right hc0 (hω.2 x)
  -- Conclusion: `X = τ(M ∩ V, θ, ξ)` with `θ ∈ ℕ` on `M ∩ V`, and `M(X) < ∞`.
  exact ⟨X, ⟨M ∩ V, θ, ξ, hT', fun x hx => hnat x hx.1, hX⟩,
    hmass.trans_lt ENNReal.ofReal_lt_top, hX⟩

/-- The truncation sequence of Simon Ch. 6, 6.2 (p. 169, second paragraph of the proof): an
integer multiplicity `T ∈ 𝒟_{m+1}(U)` with `M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U` agrees
eventually, on each test form of `U`, with integer multiplicity `X_k ∈ 𝒟_{m+1}(ℝ^P)` such that
`M(X_k) + M(∂X_k) < ∞`.  For the exhaustion function `φ`, `X_k = τ(M ∩ {φ > λ_k}, θ, ξ)` is the
book's `T ⌞ {φ > λ_k}`; the slicing mass bound (4.10) for `f = -φ` picks
`λ_k ∈ (1/(k+2), 1/(k+1))` with `M_{W_k}(⟨T, -φ, -λ_k⟩) < ∞`, `W_k = {φ > 1/(2(k+2))}`.  By (4.6)
and a cut-off, `M(∂X_k) ≤ M_{W_k}(⟨T, -φ, -λ_k⟩) + M_{W_k}((∂T) ⌞ {φ > λ_k})`. -/
theorem Submission.polyhedral_approx_truncation_seq : SlicingTheorem → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∃ X : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), (∀ k, IsIntegerMultiplicity (X k)) ∧ (∀ k, (X k).mass + (X k).boundary.mass < ∞) ∧ ∀ ω : TestFormOn U (m + 1), ∀ᶠ k in atTop, X k (testFormOnInclusion (subset_univ U) (m + 1) ω) = T ω := by
  intro hSlice P m U hU T hTint hTmass
  -- Step 0: `T = τ(M, θ, ξ)` with positive integer multiplicity `θ`.
  obtain ⟨M, θ, ξ, hMθξ, hθ, hT⟩ := hTint
  -- Step 1: the exhaustion function `φ`; `V_t = {φ > t} ⊂⊂ U` for `t > 0`.
  obtain ⟨φ, hφL, hφK, hφδ⟩ := Submission.polyhedral_approx_exhaustion_function P U hU
  have hVo : ∀ t : ℝ, IsOpen {x | t < φ x} := fun t =>
    isOpen_lt continuous_const hφL.continuous
  have hVcl : ∀ t : ℝ, closure {x | t < φ x} ⊆ {x | t ≤ φ x} := fun t =>
    closure_lt_subset_le continuous_const hφL.continuous
  have hVcc : ∀ t : ℝ, 0 < t → CompactlyContainedOpen {x | t < φ x} U := fun t ht =>
    ⟨hVo t, (hφK t ht).1.of_isClosed_subset isClosed_closure (hVcl t),
      (hVcl t).trans (hφK t ht).2⟩
  -- Step 2: the slices `⟨T, -φ, s⟩` (4.6) and the mass bound (4.10) for the 1-Lipschitz `-φ`.
  obtain ⟨S, hSsl, -, -, hSmass⟩ := hSlice P m U hU T hTmass (-φ) 1 hφL.neg.lipschitzOnWith
  -- The restriction in the slice at level `0` provides a representation `(μ, v)` of `T` (2.7).
  obtain ⟨_, _, ⟨_, μ, v, hμv, _⟩, _, _⟩ := hSsl 0
  -- `|D(-φ)| ≤ 1` everywhere.
  have hDf : ∀ W : Set (Eucl P), ∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W →
      ‖fderiv ℝ (-φ) x‖₊ ≤ 1 := fun W => Eventually.of_forall fun x _ => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hφL.neg
  -- Step 3: a level `s_k ∈ (-1/(k+1), -1/(k+2))` whose slice has finite mass in
  -- `W_k = V_{1/(2(k+2))}`.
  have hlev : ∀ k : ℕ, ∃ s ∈ Ioo (-(1 / ((k : ℝ) + 1))) (-(1 / ((k : ℝ) + 2))),
      (S s).massOn {x | 1 / (2 * ((k : ℝ) + 2)) < φ x} < ∞ := by
    intro k
    have hab : -(1 / ((k : ℝ) + 1)) < -(1 / ((k : ℝ) + 2)) :=
      neg_lt_neg (one_div_lt_one_div_of_lt (by positivity) (by linarith))
    have hWcc := hVcc (1 / (2 * ((k : ℝ) + 2))) (by positivity)
    -- `R_k = T ⌞ {a < -φ < b}` has finite mass in `W_k`.
    have hE : MeasurableSet
        {x | x ∈ U ∧ -(1 / ((k : ℝ) + 1)) < (-φ) x ∧ (-φ) x < -(1 / ((k : ℝ) + 2))} :=
      (hU.inter ((isOpen_lt continuous_const hφL.continuous.neg).inter
        (isOpen_lt hφL.continuous.neg continuous_const))).measurableSet
    obtain ⟨R, hR⟩ :=
      (Submission.polyhedral_approx_restriction_exists P (m + 1) U hU T).1 μ v hμv _ hE
    have hRfin := (Submission.polyhedral_approx_restriction_exists P (m + 1) U hU T).2 _ R hR _ hWcc
    obtain ⟨g, hgm, hgS, hgint⟩ :=
      hSmass _ hWcc.1 (subset_closure.trans hWcc.2.2) 1 (hDf _) _ _ hab R hR
    rw [ENNReal.coe_one, one_mul] at hgint
    -- `g < ∞` a.e. on the interval, which has positive length.
    have hne : (volume : Measure ℝ).restrict
        (Ioo (-(1 / ((k : ℝ) + 1))) (-(1 / ((k : ℝ) + 2)))) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero, not_le, sub_pos]
      exact hab
    have := ae_neBot.2 hne
    obtain ⟨s, hs, hgs⟩ := ((ae_restrict_mem measurableSet_Ioo).and
      (ae_lt_top hgm (hgint.trans_lt hRfin).ne)).exists
    exact ⟨s, hs, (hgS s hs).trans_lt hgs⟩
  choose s hs hSs using hlev
  have hsb : ∀ k : ℕ, 1 / ((k : ℝ) + 2) < -s k ∧ -s k < 1 / ((k : ℝ) + 1) := fun k =>
    ⟨by linarith [(hs k).2], by linarith [(hs k).1]⟩
  have hpos : ∀ k : ℕ, 0 < -s k := fun k => lt_trans (by positivity) (hsb k).1
  -- Step 4: `X_k = τ(M ∩ V_{λ_k}, θ, ξ) ∈ 𝒟_{m+1}(ℝ^P)`, `λ_k = -s_k`.
  choose X hXint hXmass hXact using fun k => Submission.polyhedral_approx_open_truncation P (m + 1)
    U {x | -s k < φ x} M θ ξ hMθξ hθ (hVcc _ (hpos k))
  refine ⟨X, hXint, fun k => ?_, fun ω => ?_⟩
  · -- Step 5: `M(∂X_k) ≤ M_{W_k}(∂A) ≤ M_{W_k}(S_{s_k}) + M_{W_k}(B) < ∞`, where
    -- `A = T ⌞ {-φ < s_k}`, `B = (∂T) ⌞ {-φ < s_k}` and `S_{s_k} = ∂A - B` (4.6).
    obtain ⟨A, B, hA, hB, hSAB⟩ := hSsl (s k)
    have hWcc := hVcc (1 / (2 * ((k : ℝ) + 2))) (by positivity)
    -- (a) `A = τ(M ∩ V_{λ_k}, θ, ξ)`, as `M ⊆ U`.
    have hMV : M ∩ {x | x ∈ U ∧ (-φ) x < s k} = M ∩ {x | -s k < φ x} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, Pi.neg_apply]
      constructor
      · rintro ⟨hxM, -, hx⟩
        exact ⟨hxM, by linarith⟩
      · rintro ⟨hxM, hx⟩
        exact ⟨hxM, hMθξ.subset hxM, by linarith⟩
    have hAτ : ∀ η : TestFormOn U (m + 1),
        A η = tauAction (m + 1) (M ∩ {x | -s k < φ x}) θ ξ η := fun η => by
      rw [Submission.polyhedral_approx_restriction_tau P (m + 1) U hU T M θ ξ hMθξ hT _ A hA η,
        hMV]
    -- (b) `M_{W_k}(B) < ∞`; `M_{W_k}(S_{s_k}) < ∞` by Step 3.
    have hBfin :=
      (Submission.polyhedral_approx_restriction_exists P m U hU T.boundary).2 _ B hB _ hWcc
    -- (c)–(e) `X_k` and `A` agree on test forms agreeing on `V_{λ_k}`; cut off inside `W_k`.
    have hMVm : NullMeasurableSet (M ∩ {x | -s k < φ x}) (μHE[m + 1] : Measure (Eucl P)) :=
      hMθξ.nullMeasurableSet.inter (hVo _).measurableSet.nullMeasurableSet
    have hVW : closure {x | -s k < φ x} ⊆ {x | 1 / (2 * ((k : ℝ) + 2)) < φ x} := by
      refine (hVcl _).trans fun x (hx : -s k ≤ φ x) => ?_
      have h2 : 1 / (2 * ((k : ℝ) + 2)) < 1 / ((k : ℝ) + 2) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      exact h2.trans ((hsb k).1.trans_le hx)
    have hbd := Submission.polyhedral_approx_boundary_mass_cutoff P m univ U _ _ (X k) A hWcc.1
      (subset_closure.trans hWcc.2.2) (hVcc _ (hpos k)).2.1 hVW fun η η' hηη' => by
        rw [hXact, hAτ]
        exact setIntegral_congr_fun₀ hMVm fun x hx => by rw [hηη' x hx.2]
    -- (f) `∂A = S_{s_k} + B`, so `M_{W_k}(∂A) ≤ M_{W_k}(S_{s_k}) + M_{W_k}(B)`.
    have hAB : A.boundary.massOn {x | 1 / (2 * ((k : ℝ) + 2)) < φ x} ≤
        (S (s k)).massOn {x | 1 / (2 * ((k : ℝ) + 2)) < φ x} +
          B.massOn {x | 1 / (2 * ((k : ℝ) + 2)) < φ x} := by
      refine sSup_le ?_
      rintro _ ⟨ψ, hψ, rfl⟩
      calc ENNReal.ofReal (A.boundary ψ) = ENNReal.ofReal (S (s k) ψ + B ψ) := by
            rw [hSAB ψ, sub_add_cancel]
        _ ≤ ENNReal.ofReal (S (s k) ψ) + ENNReal.ofReal (B ψ) := ENNReal.ofReal_add_le
        _ ≤ _ := add_le_add ((S (s k)).le_massOn hψ) (B.le_massOn hψ)
    exact ENNReal.add_lt_top.2 ⟨hXmass k,
      hbd.trans_lt (hAB.trans_lt (ENNReal.add_lt_top.2 ⟨hSs k, hBfin⟩))⟩
  · -- Step 6: `tsupport ω ⊆ V_{λ_k}` for large `k`, so `X_k(ω) = T(ω)`.
    obtain ⟨δ, hδ, hδK⟩ :=
      hφδ (tsupport (ω : DifferentialForm (Eucl P) (m + 1))) ω.property.1.2 ω.property.2
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop k₀] with k hk
    have hKV : tsupport (ω : DifferentialForm (Eucl P) (m + 1)) ⊆ {x | -s k < φ x} :=
      fun x hx => calc
        -s k < 1 / ((k : ℝ) + 1) := (hsb k).2
        _ ≤ 1 / ((k₀ : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
        _ < δ := hk₀
        _ ≤ φ x := hδK x hx
    rw [hXact, hT]
    simp only [tauAction, testFormOnInclusion_coe]
    rw [← setIntegral_indicator (hVo (-s k)).measurableSet, indicator_eq_self.2]
    intro x hx
    refine hKV (subset_tsupport _ fun h0 => hx ?_)
    simp [h0]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
