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

/-- Level cut-offs converge to the indicator of `{x ∈ U : f x < t}` under the integral: for
`χ_h = 1` on `(-∞, t - h]`, `χ_h = 0` on `[t, ∞)` and `|χ_h| ≤ 1`,
`∫ χ_h(f) F dν → ∫_{x ∈ U, f x < t} F dν` as `h → 0+` (dominated convergence; Simon 4.11). -/
theorem Submission.slicing_mb_pointwise_cutoff_tendsto :
    ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ (ν : Measure (Eucl P)) (F : Eucl P → ℝ), Integrable F ν → (∀ x, x ∉ U → F x = 0) → ∀ (t : ℝ) (χ : ℝ → ℝ → ℝ), (∀ h : ℝ, 0 < h → Measurable (χ h)) → (∀ h s : ℝ, 0 < h → |χ h s| ≤ 1) → (∀ h s : ℝ, 0 < h → s ≤ t - h → χ h s = 1) → (∀ h s : ℝ, 0 < h → t ≤ s → χ h s = 0) → Tendsto (fun h : ℝ => ∫ x, χ h (f x) * F x ∂ν) (𝓝[>] 0) (𝓝 (∫ x in {x | x ∈ U ∧ f x < t}, F x ∂ν)) := by
  intro P U hU f L hf ν F hF hF0 t χ hχm hχb hχ1 hχ0
  -- McShane extension `g` of `f|U`: globally Lipschitz, hence continuous.
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have hgc : Continuous g := hg.continuous
  -- The limit set `A = U ∩ g⁻¹(-∞, t)` is open, so the set integral is an indicator integral.
  set A : Set (Eucl P) := {x | x ∈ U ∧ f x < t} with hA
  have hAeq : A = U ∩ g ⁻¹' Iio t := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, show g x < t from hfg hx ▸ hfx⟩
    · rintro ⟨hx, hgx⟩
      exact ⟨hx, show f x < t from (hfg hx).symm ▸ hgx⟩
  have hAm : MeasurableSet A := by
    rw [hAeq]
    exact (hU.inter (isOpen_Iio.preimage hgc)).measurableSet
  rw [← integral_indicator hAm]
  -- Off `U` we have `F = 0`, so `f` may be replaced by `g` inside the integrand.
  have hfg' : ∀ h x, χ h (f x) * F x = χ h (g x) * F x := by
    intro h x
    by_cases hx : x ∈ U
    · rw [hfg hx]
    · simp [hF0 x hx]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_ hF.norm ?_
  · -- measurability for `h > 0`
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    have : (fun x => χ h (f x) * F x) = fun x => χ h (g x) * F x := funext (hfg' h)
    rw [this]
    exact ((hχm h hh).comp hgc.measurable).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · -- domination by `‖F‖` for `h > 0`
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs (χ h (f x))]
    calc |χ h (f x)| * ‖F x‖ ≤ 1 * ‖F x‖ := by gcongr; exact hχb h _ hh
      _ = ‖F x‖ := one_mul _
  · -- pointwise convergence at every `x`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ U
    · by_cases hft : f x < t
      · rw [indicator_of_mem (show x ∈ A from ⟨hx, hft⟩)]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hft)] with h hh
        rw [hχ1 h (f x) hh.1 (by linarith [hh.2]), one_mul]
      · rw [indicator_of_notMem (show x ∉ A from fun h => hft h.2)]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
        rw [hχ0 h (f x) hh (not_lt.mp hft), zero_mul]
    · rw [indicator_of_notMem (show x ∉ A from fun h => hx h.1), hF0 x hx]
      simp
/-- Passing `ofReal |X_ε(h)| ≤ ofReal ((1 + ε) / h) · LW · a(h)` to the `liminf` as `h → 0+`
and then letting `ε ↓ 0`, in `[0, ∞]`: if for every `ε > 0` some `X_ε(h) → r` as `h → 0+`
satisfies this bound for all `h > 0`, then `ofReal |r| ≤ LW · liminf_{h → 0+} a(h) / ofReal h`.
For fixed `ε`, `ofReal |r|` is the `liminf` of `ofReal |X_ε(h)|`, and
`ofReal ((1 + ε) / h) · LW · a(h) = (ofReal (1 + ε) · LW) · (a(h) / ofReal h)` for `h > 0`;
the finite constant `ofReal (1 + ε) · LW` commutes with the `liminf`, and
`ofReal (1 + ε) → 1` as `ε → 0+`. -/
theorem Submission.slicing_mb_pointwise_liminf_bound :
    ∀ (a : ℝ → ℝ≥0∞) (LW : ℝ≥0) (r : ℝ),
      (∀ ε : ℝ, 0 < ε → ∃ X : ℝ → ℝ, Tendsto X (𝓝[>] 0) (𝓝 r) ∧
        ∀ h : ℝ, 0 < h →
          ENNReal.ofReal |X h| ≤ ENNReal.ofReal ((1 + ε) / h) * (LW : ℝ≥0∞) * a h) →
      ENNReal.ofReal |r| ≤
        (LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0) := by
  intro a LW r hX
  -- For fixed `ε > 0`: `ofReal |r| ≤ ofReal (1 + ε) · (LW · liminf_{h → 0+} a(h) / ofReal h)`.
  have key : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal |r| ≤ ENNReal.ofReal (1 + ε) *
      ((LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0)) := by
    intro ε hε
    obtain ⟨X, hXr, hXb⟩ := hX ε hε
    -- `ofReal |X(h)| → ofReal |r|`, so `ofReal |r|` is the `liminf` of `ofReal |X(h)|`.
    have hlim : Tendsto (fun h => ENNReal.ofReal |X h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |r|)) :=
      ENNReal.tendsto_ofReal hXr.abs
    -- For `h > 0`: `ofReal ((1 + ε) / h) · LW · a(h) = (ofReal (1 + ε) · LW) · (a(h) / ofReal h)`.
    have hle : ∀ᶠ h in 𝓝[>] (0 : ℝ), ENNReal.ofReal |X h| ≤
        ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) * (a h / ENNReal.ofReal h) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      calc ENNReal.ofReal |X h| ≤ ENNReal.ofReal ((1 + ε) / h) * (LW : ℝ≥0∞) * a h := hXb h hh
        _ = ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) * (a h / ENNReal.ofReal h) := by
          rw [ENNReal.ofReal_div_of_pos hh, div_eq_mul_inv, div_eq_mul_inv]
          ring
    -- Monotonicity of the `liminf` and the `liminf` of a finite constant multiple.
    calc ENNReal.ofReal |r| = liminf (fun h => ENNReal.ofReal |X h|) (𝓝[>] 0) :=
          hlim.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) * (a h / ENNReal.ofReal h))
            (𝓝[>] 0) := liminf_le_liminf hle
      _ = ENNReal.ofReal (1 + ε) * (LW : ℝ≥0∞) *
            liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0) :=
          ENNReal.liminf_const_mul_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.coe_ne_top)
      _ = ENNReal.ofReal (1 + ε) *
            ((LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0)) :=
          mul_assoc _ _ _
  -- `ofReal (1 + ε) · Y → Y` as `ε → 0+` (the limit factor `1` is nonzero), then `ε ↓ 0`.
  have hone : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 (1 + 0)) :=
      ((continuous_const.add continuous_id).tendsto' 0 (1 + 0) rfl).mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [add_zero, ENNReal.ofReal_one] at h2
  have hY := ENNReal.Tendsto.mul_const hone (Or.inl one_ne_zero)
    (b := (LW : ℝ≥0∞) * liminf (fun h : ℝ => a h / ENNReal.ofReal h) (𝓝[>] 0))
  rw [one_mul] at hY
  exact ge_of_tendsto hY (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
/-- Sharp smooth cut-off below the level `t` (the cut-off of the proof of Simon Ch. 6, 4.11,
p. 158, with slope bound `(1 + ε)/h`): for `h, ε > 0` there is a `C^∞` function `χ : ℝ → ℝ` with
`0 ≤ χ ≤ 1`, `χ = 1` on `(-∞, t - h]`, `χ = 0` on `[t, ∞)`, `|χ'| ≤ (1 + ε)/h`, and `χ' = 0` off
`(t - h, t)`.  Take `χ = ρ ⋆ λ`: `λ` is the clamped affine profile equal to `1` on
`(-∞, t - h + κ]`, to `0` on `[t - κ, ∞)` and of slope `-(1 + ε)/h` in between
(`κ = εh/(2(1 + ε))`), and `ρ` is a normalized smooth bump supported in `(-κ/2, κ/2)`. -/
theorem Submission.slicing_mb_cutoff : ∀ (t h ε : ℝ), 0 < h → 0 < ε → ∃ χ : ℝ → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ s, 0 ≤ χ s ∧ χ s ≤ 1) ∧
    (∀ s, s ≤ t - h → χ s = 1) ∧ (∀ s, t ≤ s → χ s = 0) ∧
    (∀ s, |deriv χ s| ≤ (1 + ε) / h) ∧ (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) := by
  intro t h ε hh hε
  -- Slope `K = (1 + ε)/h`, `κ = εh/(2(1 + ε))` (so `(h - 2κ) K = 1`), mollification radius `κ/2`.
  set K : ℝ := (1 + ε) / h with hK_def
  have hK : 0 < K := by positivity
  set κ : ℝ := ε * h / (2 * (1 + ε)) with hκ_def
  have hκ : 0 < κ := by positivity
  have hκK : (h - 2 * κ) * K = 1 := by
    rw [hK_def, hκ_def]; field_simp; ring
  set r : ℝ := κ / 2 with hr_def
  have hr : 0 < r := by positivity
  set Kn : ℝ≥0 := ⟨K, hK.le⟩ with hKn_def
  have hKn : (Kn : ℝ) = K := rfl
  -- The profile `λ`: `1` on `(-∞, t - h + κ]`, `0` on `[t - κ, ∞)`, `K`-Lipschitz.
  set lam : ℝ → ℝ := fun u => min (max 0 ((t - κ - u) * K)) 1 with hlam_def
  have haff_lip : LipschitzWith Kn (fun u : ℝ => (t - κ - u) * K) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, hKn,
      show (t - κ - a) * K - (t - κ - b) * K = -((a - b) * K) by ring, abs_neg, abs_mul,
      abs_of_pos hK, mul_comm]
  have hlam_lip : LipschitzWith Kn lam := (haff_lip.const_max 0).min_const 1
  have hlam_cont : Continuous lam := hlam_lip.continuous
  have hlam01 : ∀ u, 0 ≤ lam u ∧ lam u ≤ 1 := fun u =>
    ⟨le_min (le_max_left _ _) zero_le_one, min_le_right _ _⟩
  have hlam_one : ∀ u, u < t - h + κ → lam u = 1 := by
    intro u hu
    have h1 : 1 < (t - κ - u) * K := by
      rw [← hκK]; exact mul_lt_mul_of_pos_right (by linarith) hK
    simp only [hlam_def]
    rw [max_eq_right (by linarith), min_eq_right h1.le]
  have hlam_zero : ∀ u, t - κ < u → lam u = 0 := by
    intro u hu
    have h1 : (t - κ - u) * K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hK.le
    simp only [hlam_def]
    rw [max_eq_left h1, min_eq_left zero_le_one]
  -- The mollifier `ρ = (∫ φ)⁻¹ φ`, `φ` a smooth bump with support `ball 0 r`.
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hφ_int_pos : 0 < ∫ y, φ y := by
    refine φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero φ.hasCompactSupport
      (fun y => φ.nonneg) (x := 0) ?_
    rw [φ.one_of_mem_closedBall (by simp [φ]; positivity)]
    exact one_ne_zero
  set I : ℝ := ∫ y, φ y with hI_def
  set ρ : ℝ → ℝ := fun y => I⁻¹ * φ y with hρ_def
  have hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := contDiff_const.mul φ.contDiff
  have hρ_cs : HasCompactSupport ρ := φ.hasCompactSupport.mul_left
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hρ_nonneg : ∀ y, 0 ≤ ρ y := fun y => mul_nonneg (inv_nonneg.2 hφ_int_pos.le) φ.nonneg
  have hρ_int : Integrable ρ := hρ_cont.integrable_of_hasCompactSupport hρ_cs
  have hρ_one : ∫ y, ρ y = 1 := by
    simp only [hρ_def]; rw [integral_const_mul]; exact inv_mul_cancel₀ hφ_int_pos.ne'
  have hρ_supp : ∀ y, ρ y ≠ 0 → |y| < r := by
    intro y hy
    have hy' : y ∈ Function.support φ := fun h0 => hy (by simp [hρ_def, h0])
    rw [φ.support_eq, mem_ball, Real.dist_eq, sub_zero] at hy'
    exact hy'
  -- `χ = ρ ⋆ λ`.
  set χ : ℝ → ℝ := convolution ρ lam (ContinuousLinearMap.lsmul ℝ ℝ) volume with hχ_def
  have hχ : ∀ s, χ s = ∫ y, ρ y * lam (s - y) := by
    intro s
    simp only [hχ_def, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hint : ∀ s, Integrable (fun y => ρ y * lam (s - y)) := fun s =>
    Continuous.integrable_of_hasCompactSupport
      (hρ_cont.mul (hlam_cont.comp (continuous_const.sub continuous_id))) hρ_cs.mul_right
  -- `χ = 1` on `(-∞, t - h + r)` and `χ = 0` on `(t - r, ∞)`.
  have hχ_one : ∀ s, s < t - h + r → χ s = 1 := by
    intro s hs
    rw [hχ s, ← hρ_one]
    congr 1
    funext y
    by_cases hy : ρ y = 0
    · simp [hy]
    · have := (abs_lt.1 (hρ_supp y hy)).1
      rw [hlam_one (s - y) (by linarith), mul_one]
  have hχ_zero : ∀ s, t - r < s → χ s = 0 := by
    intro s hs
    rw [hχ s]
    have : (fun y => ρ y * lam (s - y)) = fun _ => 0 := by
      funext y
      by_cases hy : ρ y = 0
      · simp [hy]
      · have := (abs_lt.1 (hρ_supp y hy)).2
        rw [hlam_zero (s - y) (by linarith), mul_zero]
    rw [this, integral_zero]
  -- `χ` is `K`-Lipschitz, since `λ` is and `ρ` is a probability density.
  have hχ_lip : LipschitzWith Kn χ := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, Real.dist_eq, hχ a, hχ b, ← integral_sub (hint a) (hint b),
      ← Real.norm_eq_abs]
    calc ‖∫ y, (ρ y * lam (a - y) - ρ y * lam (b - y))‖ ≤ ∫ y, ρ y * (K * |a - b|) := by
          refine norm_integral_le_of_norm_le (hρ_int.mul_const _)
            (Eventually.of_forall fun y => ?_)
          rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hρ_nonneg y)]
          refine mul_le_mul_of_nonneg_left ?_ (hρ_nonneg y)
          have := hlam_lip.dist_le_mul (a - y) (b - y)
          rw [Real.dist_eq, Real.dist_eq, hKn, sub_sub_sub_cancel_right] at this
          exact this
      _ = ↑Kn * |a - b| := by rw [integral_mul_const, hρ_one, one_mul, hKn]
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ_cs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ_smooth
      hlam_cont.locallyIntegrable
  · intro s
    rw [hχ s]
    refine ⟨integral_nonneg fun y => mul_nonneg (hρ_nonneg y) (hlam01 _).1, ?_⟩
    calc ∫ y, ρ y * lam (s - y) ≤ ∫ y, ρ y :=
          integral_mono (hint s) hρ_int fun y =>
            mul_le_of_le_one_right (hρ_nonneg y) (hlam01 _).2
      _ = 1 := hρ_one
  · intro s hs
    exact hχ_one s (by linarith)
  · intro s hs
    exact hχ_zero s (by linarith)
  · intro s
    have := norm_deriv_le_of_lipschitz (x₀ := s) hχ_lip
    rwa [Real.norm_eq_abs, hKn] at this
  · intro s hs
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · have hev : χ =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds (show s < t - h + r by linarith)] with u hu
        exact hχ_one u hu
      rw [hev.deriv_eq, deriv_const]
    · have hev : χ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (show t - r < s by linarith)] with u hu
        exact hχ_zero u hu
      rw [hev.deriv_eq, deriv_const]
/-- Simon Ch. 6, proof of 4.8–4.9 (p. 158): the integral bounding the right side of 4.11, for a
differentiable approximation `g` of `f` (Simon's `f^{(σ)}`):
`∫ |D(χ ∘ g)| |ω| dμ ≤ c L_W μ(spt ω ∩ {t − h − δ < f < t + δ})` when `|ω| ≤ 1`,
`|g − f| ≤ δ` and `‖Dg‖ ≤ L_W` on `spt ω`, `|χ'| ≤ c` and `χ' = 0` off `(t − h, t)`.
Off `spt ω` the integrand vanishes.  On `spt ω` the chain rule gives
`‖D(χ ∘ g)(x)‖ ≤ |χ'(g x)| ‖Dg(x)‖`; this is `0` unless `t − h < g x < t`, and then
`t − h − δ < f x < t + δ` and the bound is `c L_W`.  Integrate the indicator bound. -/
theorem Submission.slicing_mb_cdb_grad_lintegral_le :
    ∀ (P m : ℕ) (μ : Measure (Eucl P)) (ω : DifferentialForm (Eucl P) m) (f g : Eucl P → ℝ) (LW : ℝ≥0) (χ : ℝ → ℝ) (t h c δ : ℝ), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → Differentiable ℝ g → Differentiable ℝ χ → (∀ x ∈ tsupport ω, |g x - f x| ≤ δ) → (∀ x ∈ tsupport ω, ‖fderiv ℝ g x‖₊ ≤ LW) → (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) → ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) * ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ ≤ ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ)) := by
  intro P m μ ω f g LW χ t h c δ hω hg hχ hgf hDg hc hband
  set E := tsupport ω ∩ f ⁻¹' Ioo (t - h - δ) (t + δ)
  set a : ℝ≥0∞ := ENNReal.ofReal c * (LW : ℝ≥0∞)
  -- `c ≥ |χ'(0)| ≥ 0`.
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- Pointwise bound of the integrand by `1_E · a`.
  have hpt : ∀ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (covectorEuclideanNorm (ω x)) ≤ E.indicator (fun _ => a) x := by
    intro x
    by_cases hxK : x ∈ tsupport ω
    · -- Chain rule: `D(χ ∘ g)(x) = Dχ(g x) ∘ Dg(x)`.
      have hchain : fderiv ℝ (fun y => χ (g y)) x = (fderiv ℝ χ (g x)).comp (fderiv ℝ g x) :=
        fderiv_fun_comp x (hχ (g x)) (hg x)
      by_cases hgx : g x ∈ Ioo (t - h) t
      · -- `t − h < g x < t` and `|g x − f x| ≤ δ` put `x` in `E`.
        have hxE : x ∈ E := by
          refine ⟨hxK, ?_⟩
          have hab := abs_le.mp (hgf x hxK)
          rw [mem_Ioo] at hgx
          rw [mem_preimage, mem_Ioo]
          constructor <;> linarith [hgx.1, hgx.2, hab.1, hab.2]
        rw [indicator_of_mem hxE]
        have hnorm : ‖fderiv ℝ (fun y => χ (g y)) x‖ ≤ c * LW := by
          rw [hchain]
          calc ‖(fderiv ℝ χ (g x)).comp (fderiv ℝ g x)‖
              ≤ ‖fderiv ℝ χ (g x)‖ * ‖fderiv ℝ g x‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ c * LW := by
              apply mul_le_mul _ _ (norm_nonneg _) hc0
              · rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
                exact hc _
              · exact_mod_cast hDg x hxK
        have h1 : (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) ≤ a := by
          calc (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞)
              = ENNReal.ofReal ‖fderiv ℝ (fun y => χ (g y)) x‖ := (ofReal_norm _).symm
            _ ≤ ENNReal.ofReal (c * LW) := ENNReal.ofReal_le_ofReal hnorm
            _ = a := by rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal]
        have h2 : ENNReal.ofReal (covectorEuclideanNorm (ω x)) ≤ 1 :=
          ENNReal.ofReal_le_one.mpr (hω x)
        calc (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (covectorEuclideanNorm (ω x))
            ≤ a * 1 := mul_le_mul' h1 h2
          _ = a := mul_one _
      · -- `χ'(g x) = 0`, so `Dχ(g x) = 0` and `D(χ ∘ g)(x) = 0`.
        have hfd : fderiv ℝ χ (g x) = 0 := by
          rw [← norm_eq_zero, ← norm_deriv_eq_norm_fderiv, hband _ hgx, norm_zero]
        rw [hchain, hfd]
        simp
    · -- Off `spt ω`, `ω x = 0`.
      have h0 : ω x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0]
  calc ∫⁻ x, (‖fderiv ℝ (fun y => χ (g y)) x‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (covectorEuclideanNorm (ω x)) ∂μ
      ≤ ∫⁻ x, E.indicator (fun _ => a) x ∂μ := lintegral_mono hpt
    _ ≤ a * μ E := lintegral_indicator_const_le _ _
/-- Continuity from above for the shrinking level bands (parent proof, Step 6).  With
`δ_j = 1/(j+1)`, the sets `E_j = K ∩ f⁻¹((a − δ_j, b + δ_j))` are Borel (`K` is closed and
`f` is continuous on `K`), decrease in `j`, have intersection `K ∩ f⁻¹([a, b])`, and
`μ(E_0) ≤ μ(K) < ∞`; so `μ(E_j) → μ(K ∩ f⁻¹([a, b]))`. -/
theorem Submission.slicing_mb_cdb_band_measure_tendsto :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (K : Set (Eucl P)) (f : Eucl P → ℝ) (a b : ℝ),
      IsClosed K → ContinuousOn f K → μ K < ∞ →
        Tendsto
          (fun j : ℕ => μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))))
          atTop (𝓝 (μ (K ∩ f ⁻¹' Icc a b))) := by
  intro P μ K f a b hK hf hμK
  -- `E_j = K \ (K ∩ f⁻¹((a − δ_j, b + δ_j)ᶜ))` is Borel.
  have hmeas : ∀ j : ℕ,
      MeasurableSet (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))) := by
    intro j
    have hcl :
        IsClosed (K ∩ f ⁻¹' (Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))ᶜ) :=
      hf.preimage_isClosed_of_isClosed hK isOpen_Ioo.isClosed_compl
    have heq : K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) =
        K \ (K ∩ f ⁻¹' (Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)))ᶜ) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [heq]
    exact hK.measurableSet.diff hcl.measurableSet
  -- `δ_j` decreases, so the bands decrease.
  have hanti : Antitone fun j : ℕ =>
      K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) := by
    intro i j hij x hx
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := Nat.one_div_le_one_div hij
    simp only [mem_inter_iff, mem_preimage, mem_Ioo] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
  -- `⋂_j E_j = K ∩ f⁻¹([a, b])`.
  have hinter :
      ⋂ j : ℕ, K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1)) =
        K ∩ f ⁻¹' Icc a b := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Ioo, mem_Icc]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_, ?_⟩
      · by_contra! hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        linarith [(h j).2.1]
      · by_contra! hlt
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        linarith [(h j).2.2]
    · rintro ⟨hxK, hax, hxb⟩ j
      have hδ : 0 < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
      exact ⟨hxK, by linarith, by linarith⟩
  -- `μ(E_0) ≤ μ(K) < ∞`; continuity from above.
  have hfin : ∃ j : ℕ,
      μ (K ∩ f ⁻¹' Ioo (a - 1 / ((j : ℝ) + 1)) (b + 1 / ((j : ℝ) + 1))) ≠ ∞ :=
    ⟨0, ((measure_mono inter_subset_left).trans_lt hμK).ne⟩
  have h := tendsto_measure_iInter_atTop (fun j => (hmeas j).nullMeasurableSet) hanti hfin
  rw [hinter] at h
  exact h
/-- Dominated convergence for the bounded continuous multipliers `χ(g_j)` against an integrable
density `F` (the limit `σ ↓ 0` in the cutoff defect bound of the slice mass estimate, Simon Ch. 6,
4.9–4.10): if `F` vanishes off `K` and `g_j → f` on `K`, then `∫ χ(g_j) F dν → ∫ χ(f) F dν`.
The integrands are dominated by `|F|` since `|χ| ≤ 1`, and converge everywhere: on `K` by
continuity of `χ`, off `K` because `F = 0`. -/
theorem Submission.slicing_mb_cdb_multiplier_integral_tendsto :
    ∀ (P : ℕ) (ν : Measure (Eucl P)) (F : Eucl P → ℝ) (K : Set (Eucl P)) (f : Eucl P → ℝ)
      (g : ℕ → Eucl P → ℝ) (χ : ℝ → ℝ), Integrable F ν → (∀ x, x ∉ K → F x = 0) →
      (∀ j, Measurable (g j)) → (∀ x ∈ K, Tendsto (fun j => g j x) atTop (𝓝 (f x))) →
      Continuous χ → (∀ s, |χ s| ≤ 1) →
      Tendsto (fun j => ∫ x, χ (g j x) * F x ∂ν) atTop (𝓝 (∫ x, χ (f x) * F x ∂ν)) := by
  intro P ν F K f g χ hF hFK hg hgf hχ hχ1
  refine tendsto_integral_of_dominated_convergence (fun x => ‖F x‖) (fun j => ?_) hF.norm
    (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · -- `χ ∘ g j` is measurable and `F` is integrable.
    exact (hχ.measurable.comp (hg j)).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · -- `|χ| ≤ 1`.
    rw [norm_mul, Real.norm_eq_abs (χ (g j x))]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 _)
  · -- On `K` by continuity of `χ`; off `K` both sides vanish.
    by_cases hx : x ∈ K
    · exact ((hχ.tendsto (f x)).comp (hgf x hx)).mul_const (F x)
    · simp only [hFK x hx, mul_zero]
      exact tendsto_const_nhds
/-- The mollifier behind Simon's `f^{(σ)}` (Ch. 6, §4, p. 158; parent Step 4): a smooth,
nonnegative, compactly supported `ρ` vanishing off `B(0, σ)` with `∫ ρ = 1`.  Take the bump `φ`
centred at `0` with radii `σ/2 < σ`; then `support φ = B(0, σ)`, so `c = ∫ φ > 0` and
`ρ = c⁻¹ φ` works. -/
theorem Submission.slicing_mb_sa_mollifier_exists :
    ∀ (P : ℕ) (σ : ℝ), 0 < σ → ∃ ρ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧ (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) ∧
      ∫ y, ρ y = 1 := by
  intro P σ hσ
  -- The smooth bump `φ` centred at `0` with `support φ = B(0, σ)`.
  let φ : ContDiffBump (0 : Eucl P) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
  have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  -- Its mass `c = ∫ φ` is positive since `B(0, σ)` has positive Lebesgue measure.
  have hc : 0 < ∫ y, φ y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
    exact measure_ball_pos _ _ hσ
  refine ⟨fun y => (∫ y, φ y)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, fun y => mul_nonneg (inv_nonneg.2 hc.le) φ.nonneg,
    fun y hy => mul_eq_zero_of_right _ (φ.zero_of_le_dist (by rwa [dist_zero_right])), ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hc.ne']
/-- **Uniform error of a mollified Lipschitz function** (Simon Ch. 6, 4.11, p. 158: "use
`f^{(σ)}` in place of `f`").  If `F` is `L`-Lipschitz and `ρ ≥ 0` is continuous with compact
support, `ρ(y) = 0` for `|y| ≥ σ` and `∫ ρ = 1`, then `|∫ ρ(y) F(x − y) dy − F(x)| ≤ L σ`.
As `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`, and pointwise
`|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L |y| ≤ ρ(y) L σ`, since `ρ(y) ≠ 0` forces `|y| < σ`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_close : ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ (ρ : Eucl P → ℝ) (σ : ℝ), Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → (∀ y : Eucl P, σ ≤ ‖y‖ → ρ y = 0) → ∫ y, ρ y = 1 → ∀ x : Eucl P, |(∫ y, ρ y * F (x - y)) - F x| ≤ (L : ℝ) * σ := by
  intro P F L hF ρ σ hρc hρs hρ0 hρσ hρ1 x
  -- `ρ` and `y ↦ ρ(y) F(x − y)` are continuous with compact support, hence integrable.
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hgi : Integrable fun y => ρ y * F (x - y) :=
    (hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hρs.mul_right
  -- Since `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`.
  have herr : (∫ y, ρ y * F (x - y)) - F x = ∫ y, ρ y * (F (x - y) - F x) := by
    simp_rw [mul_sub]
    rw [integral_sub hgi (hρi.mul_const (F x)), integral_mul_const, hρ1, one_mul]
  -- Pointwise `|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L σ`.
  have hpt : ∀ y, ‖ρ y * (F (x - y) - F x)‖ ≤ ρ y * ((L : ℝ) * σ) := by
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    -- `ρ(y) ≠ 0` forces `|y| < σ`.
    have hyσ : ‖y‖ ≤ σ := (not_le.mp fun h => hy (hρσ y h)).le
    have hlip : |F (x - y) - F x| ≤ (L : ℝ) * σ := by
      rw [← Real.dist_eq]
      calc dist (F (x - y)) (F x) ≤ (L : ℝ) * dist (x - y) x := hF.dist_le_mul _ _
        _ = (L : ℝ) * ‖y‖ := by rw [dist_self_sub_left]
        _ ≤ (L : ℝ) * σ := mul_le_mul_of_nonneg_left hyσ L.coe_nonneg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
    exact mul_le_mul_of_nonneg_left hlip (hρ0 y)
  -- Integrate the pointwise bound, using `∫ ρ = 1` once more.
  rw [herr, ← Real.norm_eq_abs]
  calc ‖∫ y, ρ y * (F (x - y) - F x)‖ ≤ ∫ y, ρ y * ((L : ℝ) * σ) :=
        norm_integral_le_of_norm_le (hρi.mul_const _) (Eventually.of_forall hpt)
    _ = (L : ℝ) * σ := by rw [integral_mul_const, hρ1, one_mul]
/-- Differentiation under the integral sign for the mollification of a globally Lipschitz `F`
by a continuous compactly supported `ρ`: `D(∫ ρ(y) F(· - y) dy)(x) = ∫ ρ(y) DF(x - y) dy`.
By Rademacher's theorem and the invariance of Lebesgue measure under `y ↦ x - y`, `F` is
differentiable at `x - y` for a.e. `y`; `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz on `ℝ^P`
with integrable majorant `L |ρ|`, so `hasFDerivAt_integral_of_dominated_loc_of_lip` applies
with `s = ℝ^P`. -/
theorem Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt :
    ∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ ρ : Eucl P → ℝ, Continuous ρ →
      HasCompactSupport ρ → ∀ x : Eucl P,
        HasFDerivAt (fun x' : Eucl P => ∫ y, ρ y * F (x' - y))
          (∫ y, ρ y • fderiv ℝ F (x - y)) x := by
  intro P F L hF ρ hρc hρs x
  -- Rademacher, pulled back along the measure-preserving map `y ↦ x - y`.
  have hae : ∀ᵐ y : Eucl P, DifferentiableAt ℝ F (x - y) :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae
      hF.ae_differentiableAt
  -- `y ↦ ρ(y) F(x' - y)` is continuous for every `x'`.
  have hcont : ∀ x' : Eucl P, Continuous fun y : Eucl P => ρ y * F (x' - y) := fun x' =>
    hρc.mul (hF.continuous.comp (continuous_const.sub continuous_id))
  -- `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz for every `y`.
  have hlip : ∀ y : Eucl P,
      LipschitzOnWith (Real.nnabs (L * |ρ y|)) (fun x' : Eucl P => ρ y * F (x' - y)) univ := by
    refine fun y => (LipschitzWith.of_dist_le_mul fun a b => ?_).lipschitzOnWith
    calc dist (ρ y * F (a - y)) (ρ y * F (b - y)) = |ρ y| * dist (F (a - y)) (F (b - y)) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      _ ≤ |ρ y| * (L * dist (a - y) (b - y)) := by gcongr; exact hF.dist_le_mul _ _
      _ = Real.nnabs (L * |ρ y|) * dist a b := by
          rw [dist_sub_right, Real.coe_nnabs, abs_mul, abs_abs, NNReal.abs_eq]; ring
  -- For a.e. `y`, the chain rule gives the derivative `ρ(y) DF(x - y)` at `x`.
  have hderiv : ∀ᵐ y : Eucl P,
      HasFDerivAt (fun x' : Eucl P => ρ y * F (x' - y)) (ρ y • fderiv ℝ F (x - y)) x := by
    filter_upwards [hae] with y hy
    have h := hy.hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) y)
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_mul (ρ y)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip univ_mem
    (Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable)
    ((hcont x).integrable_of_hasCompactSupport hρs.mul_right)
    (hρc.measurable.smul ((measurable_fderiv ℝ F).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
    (Eventually.of_forall hlip)
    ((hρc.abs.integrable_of_hasCompactSupport hρs.abs).const_mul _) hderiv).2

/-- Simon Ch. 6, 4.11 ("use `f^{(σ)}` in place of `f`") on a compact `K ⊆ W`: if `f` is
`L`-Lipschitz on the open set `W` and `‖Df‖ ≤ LW` a.e. on `W`, then some `C^∞` function `g` is
`δ`-close to `f` on `K` with `‖Dg‖ ≤ LW` on `K`.  Here `g = ρ ⋆ F` mollifies a McShane extension
`F` of `f|W` with a kernel supported in a ball small enough that `x - y ∈ W` whenever `x ∈ K` and
`ρ(y) ≠ 0`. -/
theorem Submission.slicing_mb_smooth_approx :
    ∀ (P : ℕ) (W : Set (Eucl P)), IsOpen W → ∀ (f : Eucl P → ℝ) (L : ℝ≥0),
      LipschitzOnWith L f W → ∀ LW : ℝ≥0,
      (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ W → ∀ δ : ℝ, 0 < δ →
      ∃ g : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∀ x ∈ K, |g x - f x| ≤ δ) ∧
        (∀ x ∈ K, ‖fderiv ℝ g x‖₊ ≤ LW) := by
  intro P W hW f L hf LW hLW K hK hKW δ hδ
  -- The closed `r`-neighbourhood of `K` lies in `W`.
  obtain ⟨r, hr, hrW⟩ := hK.exists_cthickening_subset_open hW hKW
  -- McShane extension: `F` is `L`-Lipschitz on `ℝ^P` and `F = f` on `W`.
  obtain ⟨F, hFL, hfF⟩ := hf.extend_real
  -- The mollification radius: `σ ≤ r` keeps `x - y` in `W`, and `L σ ≤ δ`.
  obtain ⟨σ, hσ, hσr, hσδ⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ r ∧ (L : ℝ) * σ ≤ δ := by
    refine ⟨min r (δ / ((L : ℝ) + 1)), lt_min hr (div_pos hδ (by positivity)), min_le_left _ _, ?_⟩
    calc (L : ℝ) * min r (δ / ((L : ℝ) + 1)) ≤ (L : ℝ) * (δ / ((L : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) L.coe_nonneg
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [L.coe_nonneg]
  obtain ⟨ρ, hρ, hρc, hρ0, hρσ, hρ1⟩ := Submission.slicing_mb_sa_mollifier_exists P σ hσ
  have hρi : Integrable ρ (volume : Measure (Eucl P)) :=
    hρ.continuous.integrable_of_hasCompactSupport hρc
  refine ⟨fun x => ∫ y, ρ y * F (x - y), ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- `g = ρ ⋆ F` is `C^∞`: `ρ` is `C^∞` with compact support and `F` is continuous.
    have hconv : (fun x => ∫ y, ρ y * F (x - y)) =
        convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Eucl P)) := by
      funext x
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [hconv]
    exact hρc.contDiff_convolution_left _ hρ hFL.continuous.locallyIntegrable
  · -- `|g - F| ≤ L σ ≤ δ` everywhere, and `F = f` on `K ⊆ W`.
    rw [hfF (hKW hx)]
    exact (Submission.slicing_mb_sa_mollify_lipschitz_close P F L hFL ρ σ hρ.continuous hρc hρ0
      hρσ hρ1 x).trans hσδ
  · -- `Dg(x) = ∫ ρ(y) DF(x - y) dy`; for a.e. `y` with `ρ(y) ≠ 0`, `x - y ∈ W` and
    -- `‖DF(x - y)‖ = ‖Df(x - y)‖ ≤ LW` (`y ↦ x - y` preserves Lebesgue measure).
    have hDg : fderiv ℝ (fun x => ∫ y, ρ y * F (x - y)) x = ∫ y, ρ y • fderiv ℝ F (x - y) :=
      (Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt P F L hFL ρ hρ.continuous hρc
        x).fderiv
    rw [hDg, ← NNReal.coe_le_coe, coe_nnnorm]
    have hae : ∀ᵐ y ∂(volume : Measure (Eucl P)),
        x - y ∈ W → ‖fderiv ℝ f (x - y)‖₊ ≤ LW :=
      ((volume : Measure (Eucl P)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hLW
    have hbd : ∀ᵐ y ∂(volume : Measure (Eucl P)),
        ‖ρ y • fderiv ℝ F (x - y)‖ ≤ ρ y * LW := by
      filter_upwards [hae] with y hy
      rw [norm_smul, Real.norm_of_nonneg (hρ0 y)]
      rcases eq_or_ne (ρ y) 0 with h0 | h0
      · simp [h0]
      have hyσ : ‖y‖ < σ := not_le.mp fun h => h0 (hρσ y h)
      have hxy : x - y ∈ W := hrW (mem_cthickening_of_dist_le _ x r K hx (by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        exact hyσ.le.trans hσr))
      have hD : fderiv ℝ F (x - y) = fderiv ℝ f (x - y) :=
        (hfF.symm.eventuallyEq_of_mem (hW.mem_nhds hxy)).fderiv_eq
      rw [hD]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hy hxy) (hρ0 y)
    calc ‖∫ y, ρ y • fderiv ℝ F (x - y)‖ ≤ ∫ y, ‖ρ y • fderiv ℝ F (x - y)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, ρ y * (LW : ℝ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hρi.mul_const _) hbd
      _ = LW := by rw [integral_mul_const, hρ1, one_mul]
/-- Simon Ch. 6, 4.11 (Leibniz rule, pointwise): `d(ψω)(x) = ψ(x) dω(x) + Dψ(x) ∧ ω(x)`, the
wedge `Dψ(x) ∧ ω(x)` being the alternatization of `h ↦ Dψ(x)(h) ω(x)`.  As `d = Alt ∘ D`
(Mathlib's `extDeriv`), this is the product rule `D(ψω)(x) = ψ(x) Dω(x) + Dψ(x) ⊗ ω(x)`
followed by linearity of `alternatizeUncurryFin`. -/
theorem Submission.slicing_mb_lb_extDeriv_smul :
    ∀ (P m : ℕ) (ψ : Eucl P → ℝ) (ω : DifferentialForm (Eucl P) m) (x : Eucl P), DifferentiableAt ℝ ψ x → DifferentiableAt ℝ ω x → exteriorDerivative (fun y => ψ y • ω y : DifferentialForm (Eucl P) m) x = ψ x • exteriorDerivative ω x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight (ω x)) := by
  intro P m ψ ω x hψ hω
  simp only [exteriorDerivative, extDeriv]
  rw [fderiv_fun_smul hψ hω, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- Multiplication by a smooth function `ψ` maps `𝒟ᵏ(U)` into itself: `ψ φ` is smooth, and
`spt (ψ φ) ⊆ spt φ`, which is compact and contained in `U`. -/
theorem Submission.slicing_mb_lb_smul_testForm :
    ∀ (P k : ℕ) (U : Set (Eucl P)) (φ : TestFormOn U k) (ψ : Eucl P → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ η : TestFormOn U k, ∀ x, (η : DifferentialForm (Eucl P) k) x =
        ψ x • (φ : DifferentialForm (Eucl P) k) x := by
  intro P k U φ ψ hψ
  obtain ⟨⟨hφ, hφc⟩, hφU⟩ := φ.2
  exact ⟨⟨ψ • (φ : DifferentialForm (Eucl P) k), ⟨hψ.smul hφ, hφc.smul_left⟩,
    (tsupport_smul_subset_right ψ _).trans hφU⟩, fun _ => rfl⟩
/-- The wedge `α ∧ ω` of a `C^∞` field `α` of covectors with a test form `ω ∈ 𝒟ᵐ(U)` is a test
form in `𝒟ᵐ⁺¹(U)`, given pointwise by `alternatizeUncurryFin ((α x).smulRight (ω x))`. -/
theorem Submission.slicing_mb_lb_wedge_testForm :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U m) (α : Eucl P → (Eucl P →L[ℝ] ℝ)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α →
      ∃ η : TestFormOn U (m + 1), ∀ x, (η : DifferentialForm (Eucl P) (m + 1)) x =
        ContinuousAlternatingMap.alternatizeUncurryFin
          ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by
  intro P m U ω α hα
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  -- `η` vanishes wherever `ω` does: `(α x).smulRight 0 = 0` and `alternatizeUncurryFin` is linear.
  have hsupp : Function.support (fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ⊆
      Function.support (ω : DifferentialForm (Eucl P) m) := by
    intro x hx h0
    apply hx
    simp only [h0, ContinuousLinearMap.smulRight_zero]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
  -- Hence `η` has compact support and `tsupport η ⊆ tsupport ω ⊆ U`; the formula holds by `rfl`.
  refine ⟨⟨fun x => ContinuousAlternatingMap.alternatizeUncurryFin
      ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x)),
    ⟨?_, hωc.mono hsupp⟩, (closure_mono hsupp).trans hωU⟩, fun x => rfl⟩
  -- Smoothness: `x ↦ (α x).smulRight (ω x)` is `C^∞` (bounded bilinear in `(α x, ω x)`), and
  -- `alternatizeUncurryFin` is the continuous linear map `alternatizeUncurryFinCLM`.
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).contDiff.comp
    (hα.smulRight hωs)
/-- **Mass estimate from a normalized measure representation** (Simon Ch. 6, (2.7)).  If
`T(η) = ∫ ⟨η, v⟩ dμ` for every test form `η` and `|⟨α, v(x)⟩| ≤ |α|` for every `x` and every
`n`-covector `α` (Euclidean coefficient norm), then `|T(η)| ≤ ∫ |η| dμ` in `[0, ∞]`. -/
theorem Submission.slicing_mb_lb_repr_bound : ∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ v → (∀ (x : Eucl P) (α : Covector (Eucl P) n), |v x α| ≤ covectorEuclideanNorm α) → ∀ η : TestFormOn U n, ENNReal.ofReal |T η| ≤ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((η : DifferentialForm (Eucl P) n) x)) ∂μ := by
  intro P n U T μ v hrep hv η
  -- Step 1: `T(η) = ∫ ⟨η(x), v(x)⟩ dμ(x)` by the representation (2.7).
  rw [(hrep η).2, ← Real.enorm_eq_ofReal_abs]
  -- Step 2: `‖∫ g dμ‖ₑ ≤ ∫⁻ ‖g‖ₑ dμ`, which needs no integrability hypothesis.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
  -- Steps 3–4: pointwise `‖⟨η(x), v(x)⟩‖ₑ = ofReal |⟨η(x), v(x)⟩| ≤ ofReal |η(x)|`.
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (hv x _)
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
/-- Every continuous linear functional `α` on `ℝ^P` has an adapted orthonormal basis `u`:
`α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`. -/
theorem Submission.slicing_mb_wn_adapted_onb :
    ∀ (P : ℕ) (α : Eucl P →L[ℝ] ℝ), ∃ u : OrthonormalBasis (Fin P) ℝ (Eucl P),
      ∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then ‖α‖ else 0 := by
  intro P α
  by_cases hα : α = 0
  · -- `α = 0`: the standard basis works, since `‖α‖ = 0`.
    exact ⟨EuclideanSpace.basisFun (Fin P) ℝ, fun j => by simp [hα]⟩
  -- The Riesz vector `a` of `α`: `α z = ⟪a, z⟫` and `‖a‖ = ‖α‖ > 0`.
  set a : Eucl P := (InnerProductSpace.toDual ℝ (Eucl P)).symm α
  have hαa : ∀ z, α z = inner ℝ a z := fun z => InnerProductSpace.toDual_symm_apply.symm
  have hna : ‖a‖ = ‖α‖ := LinearIsometryEquiv.norm_map _ _
  have hpos : 0 < ‖a‖ := hna ▸ norm_pos_iff.mpr hα
  have ha0 : a ≠ 0 := norm_pos_iff.mp hpos
  -- `a ≠ 0` forces `P ≥ 1`, so the index `0` exists.
  have hP : 0 < P := by
    have := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mpr ⟨a, ha0⟩
    rwa [finrank_euclideanSpace_fin] at this
  set i₀ : Fin P := ⟨0, hP⟩
  -- Extend the unit vector `‖a‖⁻¹ • a`, placed at index `i₀`, to an orthonormal basis `u`.
  obtain ⟨u, hu⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := Eucl P) (by simp) (v := fun _ => ‖a‖⁻¹ • a) (s := {i₀})
    (by
      rw [orthonormal_subsingleton_iff]
      intro i
      exact norm_smul_inv_norm ha0)
  have hu₀ : u i₀ = ‖a‖⁻¹ • a := hu i₀ (Set.mem_singleton _)
  have haU : a = ‖a‖ • u i₀ := by rw [hu₀, smul_inv_smul₀ hpos.ne']
  -- `α(uⱼ) = ‖a‖ ⟪u₀, uⱼ⟫`, which is `‖a‖ = ‖α‖` for `j = 0` and `0` otherwise.
  refine ⟨u, fun j => ?_⟩
  rw [hαa, haU, real_inner_smul_left]
  split_ifs with hj
  · have : j = i₀ := Fin.ext hj
    subst this
    rw [real_inner_self_eq_norm_sq, u.orthonormal.norm_eq_one, one_pow, mul_one, hna]
  · have : i₀ ≠ j := fun h => hj (by rw [← h])
    rw [u.orthonormal.inner_eq_zero this, mul_zero]
/-- Coefficient sum of `α ∧ γ` on a family adapted to `α`: if `α (u j)` is `c` for `j = 0` and
`0` otherwise, then `∑_{I increasing} ((α ∧ γ)(u_I))² ≤ c² ∑_{J increasing} γ(u_J)²`, where
`α ∧ γ = alternatizeUncurryFin (α.smulRight γ)`.  The family `u` need not be orthonormal. -/
theorem Submission.slicing_mb_wn_adapted_sum_le :
    ∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m) (u : Fin P → Eucl P) (c : ℝ), (∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then c else 0) → (∑ I : Fin (m + 1) → Fin P, if StrictMono I then (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2 else 0) ≤ c ^ 2 * ∑ I : Fin m → Fin P, if StrictMono I then (γ (fun i => u (I i))) ^ 2 else 0 := by
  intro P m α γ u c hα
  -- Steps 1–2: on a strictly increasing `I`, every term of the wedge formula with `i ≥ 1`
  -- vanishes, because `I i > I 0 ≥ 0` forces `α (u (I i)) = 0`.
  have hval : ∀ I : Fin (m + 1) → Fin P, StrictMono I →
      ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i)) =
        α (u (I 0)) * γ (fun j => u (I j.succ)) := by
    intro I hI
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ,
      Finset.sum_eq_zero fun i _ => ?_, add_zero]
    · simp only [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero,
        ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rfl
    · have h : ((I 0 : Fin P) : ℕ) < (I i.succ : ℕ) := hI (Fin.succ_pos i)
      have h0 : ((I i.succ : Fin P) : ℕ) ≠ 0 := by omega
      simp [hα, h0]
  -- Step 3: the summands of the left side vanish unless `I` is strictly increasing with
  -- `I 0 = 0`, where they equal `c ^ 2 * γ (u ∘ I ∘ succ) ^ 2`.
  have hL : ∀ I : Fin (m + 1) → Fin P,
      (if StrictMono I then
        (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2
        else 0) =
      if StrictMono I ∧ ((I 0 : Fin P) : ℕ) = 0 then
        c ^ 2 * (γ (fun j => u (I j.succ))) ^ 2 else 0 := by
    intro I
    by_cases hI : StrictMono I
    · rw [hval I hI, hα (I 0)]
      by_cases h0 : ((I 0 : Fin P) : ℕ) = 0 <;> simp [hI, h0, mul_pow]
    · simp [hI]
  rw [Finset.sum_congr rfl fun I _ => hL I, ← Finset.sum_filter, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  -- Steps 4–5: `I ↦ I ∘ succ` is injective on `{I | StrictMono I ∧ I 0 = 0}` and maps it into
  -- the strictly increasing `m`-tuples; the remaining summands are nonnegative squares.
  have hinj : Set.InjOn (fun (I : Fin (m + 1) → Fin P) (j : Fin m) => I j.succ)
      (Finset.univ.filter fun I : Fin (m + 1) → Fin P =>
        StrictMono I ∧ ((I 0 : Fin P) : ℕ) = 0) := by
    intro I hI I' hI' h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hI hI'
    funext i
    refine Fin.cases ?_ (fun j => congrFun h j) i
    exact Fin.ext (hI.2.trans hI'.2.symm)
  rw [← Finset.sum_filter,
    ← Finset.sum_image (f := fun J : Fin m → Fin P => (γ (fun i => u (J i))) ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun J _ _ => sq_nonneg _
  intro J hJ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
  obtain ⟨I, ⟨hI, _⟩, rfl⟩ := hJ
  exact hI.comp Fin.strictMono_succ

/-- The wedge estimate behind the bound on the right side of Simon Ch. 6, 4.11 (proof of 4.8–4.9):
for a covector `α` and an `m`-covector `γ` on `ℝ^P`, the Euclidean coefficient norm of
`α ∧ γ = alternatizeUncurryFin (α.smulRight γ)` is at most `‖α‖ |γ|`.  The coefficient norm can
be computed in any orthonormal basis.  In a basis `u` with `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for
`j ≠ 0`, the coefficients of `α ∧ γ` are `‖α‖` times coefficients of `γ` on pairwise distinct
multi-indices, so `|α ∧ γ|² ≤ ‖α‖² |γ|²`. -/
theorem Submission.slicing_mb_wedge_norm_le :
    ∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m),
      covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ)) ≤
        ‖α‖ * covectorEuclideanNorm γ := by
  intro P m α γ
  -- An orthonormal basis adapted to `α`: `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`.
  obtain ⟨u, hu⟩ := Submission.slicing_mb_wn_adapted_onb P α
  refine (sq_le_sq₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (norm_nonneg α) (covectorEuclideanNorm_nonneg γ))).1 ?_
  -- Both squared norms are sums over increasing multi-indices in `u`, and there
  -- `Σ_{I incr} (α ∧ γ)(u_I)² ≤ ‖α‖² Σ_{J incr} γ(u_J)²`.
  rw [mul_pow, Submission.slicing_mb_wn_norm_sq_eq_onb_sum P (m + 1) u,
    Submission.slicing_mb_wn_norm_sq_eq_onb_sum P m u]
  exact Submission.slicing_mb_wn_adapted_sum_le P m α γ u ‖α‖ hu
/-- **Boundary defect of a smooth multiplier** (Simon Ch. 6, 4.11, with the representation
estimate (2.7) and the wedge bound): if `(μ, v)` represents `T ∈ 𝒟ₘ₊₁(U)` with
`|⟨α, v⟩| ≤ |α|`, `ω ∈ 𝒟ᵐ(U)` and `ψ` is `C^∞`, then `η₁ = ψω` and `η₂ = ψ dω` are test forms
with `|∂T(η₁) − T(η₂)| ≤ ∫ |Dψ| |ω| dμ`.  The Leibniz rule `d(ψω) = ψ dω + Dψ ∧ ω` gives
`∂T(η₁) − T(η₂) = T(Dψ ∧ ω)`, bounded by the representation and `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|`. -/
theorem Submission.slicing_mb_leibniz_bound :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
      (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
      ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      ∃ (η₁ : TestFormOn U m) (η₂ : TestFormOn U (m + 1)),
        (∀ x, (η₁ : DifferentialForm (Eucl P) m) x = ψ x • (ω : DifferentialForm (Eucl P) m) x) ∧
        (∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x =
          ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∧
        ENNReal.ofReal |T.boundary η₁ - T η₂| ≤
          ∫⁻ x, (‖fderiv ℝ ψ x‖₊ : ℝ≥0∞) *
            ENNReal.ofReal (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x)) ∂μ := by
  intro P m U T μ v hrep hnorm ω ψ hψ
  -- The test forms `η₁ = ψ ω`, `η₂ = ψ dω` and `η₃ = Dψ ∧ ω` in `U`.
  obtain ⟨η₁, hη₁⟩ := Submission.slicing_mb_lb_smul_testForm P m U ω ψ hψ
  obtain ⟨η₂, hη₂⟩ :=
    Submission.slicing_mb_lb_smul_testForm P (m + 1) U (exteriorDerivativeTestOn U m ω) ψ hψ
  obtain ⟨η₃, hη₃⟩ :=
    Submission.slicing_mb_lb_wedge_testForm P m U ω (fderiv ℝ ψ) (hψ.fderiv_right (by simp))
  have hη₂' : ∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x =
      ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x := hη₂
  refine ⟨η₁, η₂, hη₁, hη₂', ?_⟩
  -- Leibniz rule: `dη₁ = ψ dω + Dψ ∧ ω = η₂ + η₃`.
  have hd : exteriorDerivativeTestOn U m η₁ = η₂ + η₃ := by
    apply Subtype.ext
    funext x
    have h₁ : (η₁ : DifferentialForm (Eucl P) m) =
        fun y => ψ y • (ω : DifferentialForm (Eucl P) m) y := funext hη₁
    change exteriorDerivative (η₁ : DifferentialForm (Eucl P) m) x =
      (η₂ : DifferentialForm (Eucl P) (m + 1)) x + (η₃ : DifferentialForm (Eucl P) (m + 1)) x
    rw [h₁, hη₂', hη₃, Submission.slicing_mb_lb_extDeriv_smul P m ψ
      (ω : DifferentialForm (Eucl P) m) x (hψ.differentiable (by simp) x)
      (ω.2.1.1.differentiable (by simp) x)]
  -- Hence `∂T(η₁) − T(η₂) = T(η₃)`.
  have hb : T.boundary η₁ - T η₂ = T η₃ := by
    rw [GeometricCurrentOn.boundary_apply, hd, map_add, add_sub_cancel_left]
  -- The representation bound for `T(η₃)`, then `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|` pointwise.
  rw [hb]
  refine (Submission.slicing_mb_lb_repr_bound P (m + 1) U T μ v hrep hnorm η₃).trans
    (lintegral_mono fun x => ?_)
  rw [hη₃, ← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Submission.slicing_mb_wedge_norm_le P m _ _)

/-- The cut-off defect bound in the proof of Simon Ch. 6, 4.9 for Lipschitz `f` (4.11 and the
bound of its right side, p. 158, with `f^{(σ)}` in place of `f`, then `σ ↓ 0`).  Let
`K = spt ω ⊆ W`, `|ω| ≤ 1`, `|v| ≤ 1` on covectors, `|Df| ≤ L_W` a.e. on the open `W ⊆ U`, and
`|χ| ≤ 1`, `|χ'| ≤ c`, `χ' = 0` off `(t - h, t)`.  Then
`|∫ χ(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ(f) ⟨dω, v₁⟩ dμ₁| ≤ c L_W μ(K ∩ {t - h ≤ f ≤ t})`, i.e.
`∂T(χ(f) ω) - T(χ(f) dω)` computed through the representations of `∂T` and `T`.  For smooth
`g_j` with `|g_j - f| ≤ 1/(j+1)` and `|Dg_j| ≤ L_W` on `K`, 4.11 for `ψ_j = χ ∘ g_j` gives the
bound with the band `K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)}`; let `j → ∞` by dominated
convergence on the left and continuity from above on the right. -/
theorem Submission.slicing_mb_cutoff_defect_bound :
    ∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) →
      (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
      ∀ (μ₁ : Measure (Eucl P)) (v₁ : Eucl P → NVector (Eucl P) (m + 1)),
      IsMeasureRepresentation T μ₁ v₁ →
      ∀ (μ₂ : Measure (Eucl P)) (v₂ : Eucl P → NVector (Eucl P) m),
      IsMeasureRepresentation T.boundary μ₂ v₂ →
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
      ∀ W : Set (Eucl P), IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Eucl P) m) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x) ≤ 1) →
      ∀ (χ : ℝ → ℝ) (t h c : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → (∀ s, |χ s| ≤ 1) →
      (∀ s, |deriv χ s| ≤ c) → (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0) →
      ENNReal.ofReal |∫ x, χ (f x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ -
        ∫ x, χ (f x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤
      ENNReal.ofReal c * (LW : ℝ≥0∞) *
        μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩ f ⁻¹' Icc (t - h) t) := by
  intro P m U T μ v hμv hμK hv μ₁ v₁ hμ₁ μ₂ v₂ hμ₂ f L hf W hW hWU LW hLW ω hωW hω1 χ t h c hχ
    hχ1 hχc hχ0
  -- `K = spt ω` is compact and `K ⊆ W ⊆ U`.
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) m)) := ω.property.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U := hωW.trans hWU
  -- Smooth `g_j` with `|g_j - f| ≤ 1/(j+1)` and `‖Dg_j‖ ≤ L_W` on `K`.
  choose g hg hgf hgD using fun j : ℕ =>
    Submission.slicing_mb_smooth_approx P W hW f L (hf.mono hWU) LW hLW _ hKc hωW
      (1 / ((j : ℝ) + 1)) (by positivity)
  -- 4.11 for `ψ_j = χ ∘ g_j`, evaluated through the representations of `∂T` and `T`; its right
  -- side is at most `c L_W μ(K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)})`.
  have key : ∀ j : ℕ,
      ENNReal.ofReal |∫ x, χ (g j x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ -
        ∫ x, χ (g j x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| ≤
      ENNReal.ofReal c * (LW : ℝ≥0∞) * μ (tsupport (ω : DifferentialForm (Eucl P) m) ∩
        f ⁻¹' Ioo (t - h - 1 / ((j : ℝ) + 1)) (t + 1 / ((j : ℝ) + 1))) := by
    intro j
    obtain ⟨η₁, η₂, hη₁, hη₂, hle⟩ := Submission.slicing_mb_leibniz_bound P m U T μ v hμv hv ω
      (fun y => χ (g j y)) (hχ.comp (hg j))
    have e₁ : T.boundary η₁ =
        ∫ x, χ (g j x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ := by
      rw [(hμ₂ η₁).2]
      congr 1
      funext x
      rw [hη₁ x, map_smul, smul_eq_mul]
    have e₂ : T η₂ =
        ∫ x, χ (g j x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁ := by
      rw [(hμ₁ η₂).2]
      congr 1
      funext x
      rw [hη₂ x, map_smul, smul_eq_mul]
    rw [← e₁, ← e₂]
    exact hle.trans (Submission.slicing_mb_cdb_grad_lintegral_le P m μ _ f (g j) LW χ t h c
      (1 / ((j : ℝ) + 1)) hω1 ((hg j).differentiable (by simp)) (hχ.differentiable (by simp))
      (hgf j) (hgD j) hχc hχ0)
  -- `g_j → f` pointwise on `K`.
  have hconv : ∀ x ∈ tsupport (ω : DifferentialForm (Eucl P) m),
      Tendsto (fun j => g j x) atTop (𝓝 (f x)) := by
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact hgf j x hx
  -- Left side: dominated convergence in both integrals, whose densities vanish off `K`.
  have hL₂ := Submission.slicing_mb_cdb_multiplier_integral_tendsto P μ₂
    (fun x => v₂ x ((ω : DifferentialForm (Eucl P) m) x)) _ f g χ (hμ₂ ω).1
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    (fun j => (hg j).continuous.measurable) hconv hχ.continuous hχ1
  have hL₁ := Submission.slicing_mb_cdb_multiplier_integral_tendsto P μ₁
    (fun x => v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x)) _ f g χ
    (hμ₁ (exteriorDerivativeTestOn U m ω)).1
    (fun x hx => by
      have hx' : x ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Eucl P) m)) :=
        fun h' => hx (tsupport_exteriorDerivative_subset _ h')
      simp [image_eq_zero_of_notMem_tsupport hx'])
    (fun j => (hg j).continuous.measurable) hconv hχ.continuous hχ1
  -- Right side: continuity from above for the bands, as `μ(K) < ∞`.
  have hR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c * (LW : ℝ≥0∞))
    (Submission.slicing_mb_cdb_band_measure_tendsto P μ _ f (t - h) t (isClosed_tsupport _)
      (hf.continuousOn.mono hKU) (hμK _ hKc hKU))
    (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  exact le_of_tendsto_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp (hL₂.sub hL₁).abs)
    hR key

/-- Simon Ch. 6, 4.9 (p. 158) for the slice `S = ⟨T, f, t₋⟩` of 4.6, `T` represented by `(μ, v)`:
for open `W ⊆ U` with `|Df| ≤ L_W` a.e. on `W`,
`M_W(S) ≤ L_W · liminf_{h ↓ 0} μ(W ∩ {t - h ≤ f ≤ t}) / h`.  For admissible `ω` and the
cut-offs `χ_h` of `slicing_mb_cutoff` (slope at most `(1 + ε)/h`), the defect
`X(h) = ∫ χ_h(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ_h(f) ⟨dω, v₁⟩ dμ₁` of 4.11 tends to `B(ω) - ∂A(ω) = -S(ω)`
as `h ↓ 0` and satisfies `|X(h)| ≤ (1 + ε)/h · L_W · μ(W ∩ {t - h ≤ f ≤ t})`; let `h ↓ 0`,
then `ε ↓ 0`. -/
theorem Submission.slicing_mb_pointwise : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P))
      (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v →
    (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) →
    (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) →
    ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
    ∀ (t : ℝ) (S : GeometricCurrentOn U m), IsSlice T f t S →
    ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ LW : ℝ≥0,
    (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
    S.massOn W ≤ (LW : ℝ≥0∞) *
      liminf (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) := by
  intro P m U hU T μ v hT hμ hv f L hf t S hS W hW hWU LW hLW
  -- `S = ∂A - B`, `A = T ⌞ {f < t}` (represented by `μ₁, v₁`), `B = (∂T) ⌞ {f < t}` (`μ₂, v₂`).
  obtain ⟨A, B, ⟨-, μ₁, v₁, hT₁, hA⟩, ⟨-, μ₂, v₂, hT₂, hB⟩, hSAB⟩ := hS
  -- It suffices to bound `S ω` for every `ω` admissible for `M_W`.
  refine sSup_le ?_
  rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  have hSω : S ω = (∫ x in {x | x ∈ U ∧ f x < t},
        v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁) -
      ∫ x in {x | x ∈ U ∧ f x < t}, v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂ := by
    have := hSAB ω
    rw [GeometricCurrentOn.boundary_apply, hA, hB] at this
    exact this
  -- The integrands `⟨ω, v₂⟩` and `⟨dω, v₁⟩` are integrable and vanish off `U`.
  have hint₂ : Integrable (fun x => v₂ x ((ω : DifferentialForm (Eucl P) m) x)) μ₂ := (hT₂ ω).1
  have hint₁ : Integrable
      (fun x => v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x)) μ₁ :=
    (hT₁ (exteriorDerivativeTestOn U m ω)).1
  have hvan₂ : ∀ x, x ∉ U → v₂ x ((ω : DifferentialForm (Eucl P) m) x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (ω.property.2 hx'), map_zero]
  have hvan₁ : ∀ x, x ∉ U → v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) = 0 :=
    fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hx' =>
        hx (ω.property.2 (tsupport_exteriorDerivative_subset _ hx')), map_zero]
  calc ENNReal.ofReal (S ω) ≤ ENNReal.ofReal |S ω| := ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal |(∫ x in {x | x ∈ U ∧ f x < t},
          v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂) -
        ∫ x in {x | x ∈ U ∧ f x < t},
          v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁| := by
      rw [hSω, abs_sub_comm]
    _ ≤ _ := by
      refine Submission.slicing_mb_pointwise_liminf_bound
        (fun h => μ (W ∩ f ⁻¹' Icc (t - h) t)) LW _ fun ε hε => ?_
      -- The cut-offs `χ_h`, `h > 0`, of slope at most `(1 + ε)/h`.
      choose! χ hχs hχ01 hχ1 hχ0 hχd hχd0 using
        fun h (hh : 0 < h) => Submission.slicing_mb_cutoff t h ε hh hε
      have hχm : ∀ h : ℝ, 0 < h → Measurable (χ h) := fun h hh =>
        (hχs h hh).continuous.measurable
      have hχabs : ∀ h s : ℝ, 0 < h → |χ h s| ≤ 1 := fun h s hh =>
        abs_le.2 ⟨by linarith [(hχ01 h hh s).1], (hχ01 h hh s).2⟩
      refine ⟨fun h => (∫ x, χ h (f x) * v₂ x ((ω : DifferentialForm (Eucl P) m) x) ∂μ₂) -
          ∫ x, χ h (f x) * v₁ x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ₁,
        ?_, fun h hh => ?_⟩
      · -- `X(h) → B(ω) - ∂A(ω)` as `h ↓ 0`.
        exact (Submission.slicing_mb_pointwise_cutoff_tendsto P U hU f L hf μ₂ _ hint₂ hvan₂ t χ
          hχm hχabs (fun h s hh => hχ1 h hh s) (fun h s hh => hχ0 h hh s)).sub
          (Submission.slicing_mb_pointwise_cutoff_tendsto P U hU f L hf μ₁ _ hint₁ hvan₁ t χ
            hχm hχabs (fun h s hh => hχ1 h hh s) (fun h s hh => hχ0 h hh s))
      · -- `|X(h)| ≤ (1 + ε)/h · L_W · μ(spt ω ∩ {t - h ≤ f ≤ t})`, and `spt ω ⊆ W`.
        refine (Submission.slicing_mb_cutoff_defect_bound P m U T μ v hT hμ hv μ₁ v₁ hT₁ μ₂ v₂
          hT₂ f L hf W hW hWU LW hLW ω hωW hω1 (χ h) t h ((1 + ε) / h) (hχs h hh)
          (fun s => hχabs h s hh) (hχd h hh) (hχd0 h hh)).trans ?_
        gcongr
/-- The distribution function `G(r) = ν((a,b) ∩ (-∞, r])` of a measure `ν` on `ℝ` with
`ν((a,b)) < ∞` is nondecreasing and right-continuous. -/
theorem Submission.slicing_mb_dm_distribution_mono_rightcont :
    ∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ →
      Monotone (fun r : ℝ => (ν (Ioo a b ∩ Iic r)).toReal) ∧
      ∀ s : ℝ, ContinuousWithinAt (fun r : ℝ => (ν (Ioo a b ∩ Iic r)).toReal) (Ici s) s := by
  intro ν a b hab
  -- Each `A_r = (a,b) ∩ (-∞, r]` lies in `(a,b)`, so `ν(A_r) < ∞`.
  have hfin : ∀ r : ℝ, ν (Ioo a b ∩ Iic r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top hab (measure_mono inter_subset_left)
  -- `r ↦ A_r` is monotone, hence so is `G`.
  have hsub : ∀ r r' : ℝ, r ≤ r' → Ioo a b ∩ Iic r ⊆ Ioo a b ∩ Iic r' := fun r r' h =>
    inter_subset_inter_right _ (Iic_subset_Iic.2 h)
  refine ⟨fun r r' h => ENNReal.toReal_mono (hfin r') (measure_mono (hsub r r' h)), fun s => ?_⟩
  -- Continuity within `[s, ∞)` is continuity within `(s, ∞)`.
  rw [← continuousWithinAt_Ioi_iff_Ici]
  -- `⋂_{r > s} A_r = A_s`.
  have hinter : (⋂ r > s, Ioo a b ∩ Iic r) = Ioo a b ∩ Iic s := by
    ext x
    simp only [mem_iInter, mem_inter_iff, mem_Iic]
    constructor
    · intro h
      exact ⟨(h (s + 1) (by linarith)).1, le_of_forall_gt_imp_ge_of_dense fun r hr => (h r hr).2⟩
    · intro h r hr
      exact ⟨h.1, h.2.trans hr.le⟩
  -- Continuity of `ν` from above along `r ↓ s`, using `ν(A_{s+1}) < ∞`.
  have hlim : Tendsto (fun r => ν (Ioo a b ∩ Iic r)) (𝓝[>] s) (𝓝 (ν (Ioo a b ∩ Iic s))) := by
    rw [← hinter]
    exact tendsto_measure_biInter_gt (s := fun r => Ioo a b ∩ Iic r)
      (fun r _ => (measurableSet_Ioo.inter measurableSet_Iic).nullMeasurableSet)
      (fun i j _ hij => hsub i j hij) ⟨s + 1, by linarith, hfin (s + 1)⟩
  -- `toReal` is continuous at the finite value `ν(A_s)`.
  exact (ENNReal.tendsto_toReal (hfin s)).comp hlim
/-- The lower left Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` of a
nondecreasing right-continuous `G : ℝ → ℝ` is Borel measurable. -/
theorem Submission.slicing_mb_dm_lowerLeftDini_measurable :
    ∀ G : ℝ → ℝ, Monotone G → (∀ s : ℝ, ContinuousWithinAt G (Ici s) s) →
      Measurable (fun t : ℝ => liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k))
        (𝓝[>] 0)) := by
  intro G hG hG_cont
  -- The intervals `(0, 1/(j+1))`, `j ∈ ℕ`, form a basis of `𝓝[>] 0`.
  have hbasis : (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True)
      (fun j => Ioo 0 (1 / ((j : ℝ) + 1))) := by
    refine (nhdsGT_basis (0 : ℝ)).to_hasBasis (fun δ hδ => ?_) (fun j _ => ?_)
    · obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, trivial, Ioo_subset_Ioo_right hj.le⟩
    · exact ⟨1 / ((j : ℝ) + 1), Nat.one_div_pos_of_nat, subset_rfl⟩
  -- Right-continuity of `G` makes `k ↦ F_t(k)` left-continuous at each `k > 0`.
  have hleft : ∀ t k : ℝ, 0 < k → ContinuousWithinAt
      (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (Iio k) k := by
    intro t k hk
    have hGk : ContinuousWithinAt (fun x : ℝ => G (t - x)) (Iio k) k := by
      have h1 : ContinuousWithinAt G (Ioi (t - k)) (t - k) :=
        continuousWithinAt_Ioi_iff_Ici.2 (hG_cont (t - k))
      refine h1.comp (continuous_const.sub continuous_id).continuousWithinAt ?_
      intro x hx
      simp only [mem_Ioi, mem_Iio] at hx ⊢
      linarith
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_const.sub hGk).div continuousWithinAt_id hk.ne')
  -- The infimum over real `k ∈ (0, δ)` equals the infimum over rational `q ∈ (0, δ)`.
  have hrat : ∀ t δ : ℝ, (⨅ k ∈ Ioo 0 δ, ENNReal.ofReal ((G t - G (t - k)) / k)) =
      ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 δ), ENNReal.ofReal ((G t - G (t - q)) / q) := by
    intro t δ
    refine le_antisymm (le_iInf₂ fun q hq => iInf₂_le (q : ℝ) hq) (le_iInf₂ fun k hk => ?_)
    -- Approximate `k` from the left by rationals `q n ∈ (max 0 (k - 1/(n+1)), k)`.
    have hex : ∀ n : ℕ, ∃ q : ℚ, max 0 (k - 1 / ((n : ℝ) + 1)) < q ∧ (q : ℝ) < k := fun n =>
      exists_rat_btwn (max_lt hk.1 (sub_lt_self k Nat.one_div_pos_of_nat))
    choose q hq_lo hq_hi using hex
    have hq_tendsto : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[<] k) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall hq_hi)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => k - 1 / ((n : ℝ) + 1))
        (h := fun _ => k) ?_ tendsto_const_nhds
        (fun n => (le_max_right _ _).trans (hq_lo n).le) (fun n => (hq_hi n).le)
      simpa using (tendsto_const_nhds (f := (atTop : Filter ℕ)) (x := k)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine ge_of_tendsto' ((hleft t k hk.1).tendsto.comp hq_tendsto) fun n => ?_
    exact iInf₂_le (q n) ⟨(le_max_left _ _).trans_lt (hq_lo n), (hq_hi n).trans hk.2⟩
  -- Hence `D(t) = ⨆ j, ⨅ q ∈ ℚ ∩ (0, 1/(j+1)), F_t(q)`, a countable formula.
  have hformula : (fun t : ℝ => liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k))
      (𝓝[>] 0)) = fun t => ⨆ j : ℕ, ⨅ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 (1 / ((j : ℝ) + 1))),
        ENNReal.ofReal ((G t - G (t - q)) / q) := by
    funext t
    rw [hbasis.liminf_eq_iSup_iInf]
    simp only [iSup_true]
    exact iSup_congr fun j => hrat t _
  -- `G` is monotone, hence measurable, so each `t ↦ F_t(q)` is measurable.
  rw [hformula]
  have hGm : Measurable G := hG.measurable
  refine Measurable.iSup fun j => Measurable.iInf fun q => Measurable.iInf_Prop _ ?_
  exact ENNReal.measurable_ofReal.comp
    ((hGm.sub (hGm.comp (measurable_id.sub_const _))).div_const _)
/-- For nondecreasing `G : ℝ → ℝ` and `a ≤ b`, the lower integral over `(a, b)` of the lower left
Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` is at most `G b - G a`. -/
theorem Submission.slicing_mb_dm_lintegral_lowerLeftDini_le :
    ∀ G : ℝ → ℝ, Monotone G → ∀ a b : ℝ, a ≤ b →
      ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤
        ENNReal.ofReal (G b - G a) := by
  intro G hG a b hab
  -- Step sizes `δ n = 1/(n+1) → 0+`.
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ_pos : ∀ n, 0 < δ n := fun n => Nat.one_div_pos_of_nat
  have hδ_lim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ_tendsto : Tendsto δ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hδ_lim
      (Eventually.of_forall hδ_pos)
  -- Truncated left difference quotients `F n t = 1_{t > a + δ n} ofReal (G t - G (t - δ n)) / δ n`.
  set F : ℕ → ℝ → ℝ≥0∞ := fun n => (Ioi (a + δ n)).indicator
    (fun t => ENNReal.ofReal ((G t - G (t - δ n)) / δ n)) with hF_def
  have hGm : Measurable G := hG.measurable
  have hF_meas : ∀ n, Measurable (F n) := fun n =>
    (ENNReal.measurable_ofReal.comp
      ((hGm.sub (hGm.comp (measurable_id.sub_const _))).div_const _)).indicator measurableSet_Ioi
  -- For `t ∈ (a, b)`: `δ n → 0+`, and `t > a + δ n` eventually, so `D(t) ≤ liminf_n F n t`.
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤
        liminf (fun n => F n t) atTop := by
    intro t ht
    refine hδ_tendsto.liminf_le_liminf_comp.trans_eq (liminf_congr ?_)
    filter_upwards [(tendsto_order.1 hδ_lim).2 _ (sub_pos.2 ht.1)] with n hn
    have hmem : t ∈ Ioi (a + δ n) := by
      simp only [mem_Ioi]
      linarith
    simp only [hF_def, Function.comp_apply, indicator_of_mem hmem]
  -- Each `F n` integrates over `(a, b)` to at most `G b - G a`.
  have hbound : ∀ n, ∫⁻ t in Ioo a b, F n t ≤ ENNReal.ofReal (G b - G a) := by
    intro n
    have hc : 0 < δ n := hδ_pos n
    simp only [hF_def]
    rw [setLIntegral_indicator measurableSet_Ioi, inter_comm, Ioo_inter_Ioi,
      max_eq_right (by linarith : a ≤ a + δ n)]
    rcases le_or_gt b (a + δ n) with hb | hb
    · rw [Ioo_eq_empty (not_lt.2 hb), setLIntegral_empty]
      exact zero_le
    -- On `(a + δ n, b)` the quotient is nonnegative and integrable, and
    -- `∫_{a+δ}^b (G t - G (t - δ)) dt = ∫_{b-δ}^b G - ∫_a^{a+δ} G ≤ δ (G b - G a)`.
    have hGc : Monotone (fun t => G (t - δ n)) := fun x y hxy => hG (by linarith)
    have hint : IntervalIntegrable (fun t => (G t - G (t - δ n)) / δ n) volume (a + δ n) b :=
      (hG.intervalIntegrable.sub hGc.intervalIntegrable).div_const _
    have hintOn : IntegrableOn (fun t => (G t - G (t - δ n)) / δ n) (Ioo (a + δ n) b) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1 hint).mono_set Ioo_subset_Ioc_self
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (a + δ n) b)]
        (fun t => (G t - G (t - δ n)) / δ n) :=
      Eventually.of_forall fun t => div_nonneg (sub_nonneg.2 (hG (by linarith))) hc.le
    have hreal : ∫ t in Ioo (a + δ n) b, (G t - G (t - δ n)) / δ n ≤ G b - G a := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb.le,
        intervalIntegral.integral_div,
        intervalIntegral.integral_sub hG.intervalIntegrable hGc.intervalIntegrable,
        intervalIntegral.integral_comp_sub_right G (δ n), add_sub_cancel_right, div_le_iff₀ hc]
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (μ := volume) (a := a + δ n) (b := b - δ n))
        (hG.intervalIntegrable (μ := volume) (a := b - δ n) (b := b))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (μ := volume) (a := a) (b := a + δ n))
        (hG.intervalIntegrable (μ := volume) (a := a + δ n) (b := b - δ n))
      have h3 : ∫ x in (b - δ n)..b, G x ≤ δ n * G b := by
        have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : b - δ n ≤ b)
          hG.intervalIntegrable intervalIntegrable_const (fun x hx => hG hx.2)
        simpa [intervalIntegral.integral_const] using this
      have h4 : δ n * G a ≤ ∫ x in a..(a + δ n), G x := by
        have := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + δ n)
          intervalIntegrable_const hG.intervalIntegrable (fun x hx => hG hx.1)
        simpa [intervalIntegral.integral_const] using this
      linarith
    calc ∫⁻ t in Ioo (a + δ n) b, ENNReal.ofReal ((G t - G (t - δ n)) / δ n)
        = ENNReal.ofReal (∫ t in Ioo (a + δ n) b, (G t - G (t - δ n)) / δ n) :=
          (ofReal_integral_eq_lintegral_ofReal hintOn hnonneg).symm
      _ ≤ ENNReal.ofReal (G b - G a) := ENNReal.ofReal_le_ofReal hreal
  -- Fatou's lemma.
  calc ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun n => F n t) atTop := setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ liminf (fun n => ∫⁻ t in Ioo a b, F n t) atTop := lintegral_liminf_le hF_meas
    _ ≤ ENNReal.ofReal (G b - G a) := liminf_le_of_frequently_le' (Frequently.of_forall hbound)
/-- **Lower left density versus the lower left Dini derivative** (Simon Ch. 6, p. 158, the step
"4.9 gives 4.10").  Let `ν((a, b)) < ∞`, `G r = ν((a, b) ∩ (-∞, r])` (as a real number) and
`t ∈ (a, b)`.  Then `liminf_{h → 0+} ν([t - h, t]) / h ≤ liminf_{k → 0+} (G t - G (t - k)) / k`.
For `c > 1` and `0 < k < t - a`, `[t - k / c, t] ⊆ (a, b) ∩ (t - k, t]`, a band of mass
`G t - G (t - k)`, so the density at `h = k / c` is at most `c · (G t - G (t - k)) / k`.
Reparametrizing `h = k / c` gives `liminf ≤ c · liminf`, and `c ↓ 1` finishes. -/
theorem Submission.slicing_mb_dm_density_le_lowerLeftDini : ∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ → ∀ t ∈ Ioo a b, liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ liminf (fun k : ℝ => ENNReal.ofReal (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) := by
  intro ν a b hν t ht
  obtain ⟨hat, htb⟩ := ht
  -- Step 1: `A_r = (a, b) ∩ (-∞, r]` has finite measure, so `G r = ν(A_r).toReal` is monotone.
  have hfin : ∀ r : ℝ, ν (Ioo a b ∩ Iic r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top hν (measure_mono inter_subset_left)
  have hmono : ∀ r r' : ℝ, r ≤ r' →
      (ν (Ioo a b ∩ Iic r)).toReal ≤ (ν (Ioo a b ∩ Iic r')).toReal := fun r r' hr =>
    ENNReal.toReal_mono (hfin r') (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hr)))
  -- Step 2: for `s' ≤ s`, `A_s = A_{s'} ⊔ ((a, b) ∩ (s', s])`, so
  -- `ν((a, b) ∩ (s', s]) = G s - G s'`.
  have hincr : ∀ s' s : ℝ, s' ≤ s → ν (Ioo a b ∩ Ioc s' s) =
      ENNReal.ofReal ((ν (Ioo a b ∩ Iic s)).toReal - (ν (Ioo a b ∩ Iic s')).toReal) := by
    intro s' s hs
    have hunion : Ioo a b ∩ Iic s = (Ioo a b ∩ Iic s') ∪ (Ioo a b ∩ Ioc s' s) := by
      ext x
      simp only [mem_inter_iff, mem_union, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨hx, hxs⟩
        by_cases hxs' : x ≤ s'
        · exact Or.inl ⟨hx, hxs'⟩
        · exact Or.inr ⟨hx, lt_of_not_ge hxs', hxs⟩
      · rintro (⟨hx, hxs'⟩ | ⟨hx, -, hxs⟩)
        · exact ⟨hx, hxs'.trans hs⟩
        · exact ⟨hx, hxs⟩
    have hdisj : Disjoint (Ioo a b ∩ Iic s') (Ioo a b ∩ Ioc s' s) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx₁⟩ ⟨-, hx₂, -⟩
      exact absurd hx₁ (not_le.2 hx₂)
    have hB : ν (Ioo a b ∩ Ioc s' s) ≠ ∞ :=
      ne_top_of_le_ne_top hν (measure_mono inter_subset_left)
    have hadd : (ν (Ioo a b ∩ Iic s)).toReal =
        (ν (Ioo a b ∩ Iic s')).toReal + (ν (Ioo a b ∩ Ioc s' s)).toReal := by
      rw [hunion, measure_union hdisj (measurableSet_Ioo.inter measurableSet_Ioc),
        ENNReal.toReal_add (hfin s') hB]
    rw [← ENNReal.ofReal_toReal hB, hadd, add_sub_cancel_left]
  -- Step 3: for `c > 1` and `0 < k < t - a`, `h = k / c` gives `[t - h, t] ⊆ (a, b) ∩ (t - k, t]`,
  -- hence `ν([t - h, t]) / h ≤ c · (G t - G (t - k)) / k`.
  have hband : ∀ c : ℝ, 1 < c → ∀ᶠ k in 𝓝[>] (0 : ℝ),
      ν (Icc (t - k / c) t) / ENNReal.ofReal (k / c) ≤ ENNReal.ofReal c * ENNReal.ofReal
        (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k) := by
    intro c hc
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hat)] with k hk
    obtain ⟨hk0, hkt⟩ := hk
    have hc0 : 0 < c := zero_lt_one.trans hc
    have hhk : k / c < k := div_lt_self hk0 hc
    have hsub : Icc (t - k / c) t ⊆ Ioo a b ∩ Ioc (t - k) t := by
      rintro x ⟨hx₁, hx₂⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, hx₂⟩
    have hΔ0 : 0 ≤ ((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k :=
      div_nonneg (sub_nonneg.2 (hmono _ _ (by linarith))) hk0.le
    apply ENNReal.div_le_of_le_mul
    calc ν (Icc (t - k / c) t) ≤ ν (Ioo a b ∩ Ioc (t - k) t) := measure_mono hsub
      _ = ENNReal.ofReal (c * (((ν (Ioo a b ∩ Iic t)).toReal -
            (ν (Ioo a b ∩ Iic (t - k))).toReal) / k) * (k / c)) := by
        rw [hincr _ _ (by linarith)]
        congr 1
        field_simp
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hc0.le hΔ0), ENNReal.ofReal_mul hc0.le]
  -- Steps 4–5: reparametrize `h = k / c` and factor out the constant `ofReal c`.
  have hc_bound : ∀ c : ℝ, 1 < c →
      liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤
        ENNReal.ofReal c * liminf (fun k : ℝ => ENNReal.ofReal
          (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) := by
    intro c hc
    have hc0 : 0 < c := zero_lt_one.trans hc
    have htend : Tendsto (fun k : ℝ => k / c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun k : ℝ => k / c) (𝓝 0) (𝓝 (0 / c)) := tendsto_id.div_const c
        rw [zero_div] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with k hk
        exact div_pos hk hc0
    calc liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0)
        ≤ liminf (fun k : ℝ => ν (Icc (t - k / c) t) / ENNReal.ofReal (k / c)) (𝓝[>] 0) :=
          htend.liminf_le_liminf_comp
      _ ≤ liminf (fun k : ℝ => ENNReal.ofReal c * ENNReal.ofReal
            (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0) :=
          liminf_le_liminf (hband c hc)
      _ = _ := ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top
  -- Step 6: let `c_n = 1 + 1 / (n + 1) ↓ 1`.
  set D := liminf (fun k : ℝ => ENNReal.ofReal
    (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0)
  rcases eq_or_ne D ∞ with hD | hD
  · rw [hD]
    exact le_top
  · have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * D) atTop (𝓝 D) := by
      simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hD)
    refine ge_of_tendsto h2 (Eventually.of_forall fun n => hc_bound _ ?_)
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The measurable majorant in Simon Ch. 6, 4.10 (`M_W(T ⌞ {f < t})` is increasing in `t`, so
it is differentiable a.e. and its derivative integrates to at most `M_W(T ⌞ {a < f < b})`), for
a Borel measure `ν` on `ℝ`: the lower left density `liminf_{h → 0+} ν([t - h, t]) / h` has a
Borel majorant on `(a, b)` whose integral over `(a, b)` is at most `ν((a, b))`.
If `ν((a, b)) = ∞` the constant `∞` works.  Otherwise the distribution function
`G(r) = ν((a, b) ∩ (-∞, r])` is nondecreasing and right-continuous, and the majorant is `D` on
`(a, b)` and `0` elsewhere, where `D(t) = liminf_{k → 0+} (G(t) - G(t - k)) / k` is the lower
left Dini derivative of `G`: `D` is Borel, it dominates the closed-band density, and by
Lebesgue's theorem for monotone functions `∫_{(a,b)} D ≤ G(b) - G(a) = ν((a, b))`. -/
theorem Submission.slicing_mb_density_majorant :
    ∀ (ν : Measure ℝ) (a b : ℝ), a < b → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧
      (∀ t ∈ Ioo a b,
        liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ g t) ∧
      ∫⁻ t in Ioo a b, g t ≤ ν (Ioo a b) := by
  intro ν a b hab
  -- If `ν((a, b)) = ∞`, take `g ≡ ∞`.
  by_cases hQ : ν (Ioo a b) = ∞
  · exact ⟨fun _ => ∞, measurable_const, fun _ _ => le_top, by rw [hQ]; exact le_top⟩
  obtain ⟨hG_mono, hG_right⟩ := Submission.slicing_mb_dm_distribution_mono_rightcont ν a b hQ
  set G : ℝ → ℝ := fun r => (ν (Ioo a b ∩ Iic r)).toReal
  set D : ℝ → ℝ≥0∞ := fun t =>
    liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0)
  refine ⟨(Ioo a b).indicator D,
    (Submission.slicing_mb_dm_lowerLeftDini_measurable G hG_mono hG_right).indicator
      measurableSet_Ioo, fun t ht => ?_, ?_⟩
  · -- On `(a, b)` the closed-band density is at most `D = g`.
    rw [Set.indicator_of_mem ht]
    exact Submission.slicing_mb_dm_density_le_lowerLeftDini ν a b hQ t ht
  · -- `∫⁻_{(a,b)} g = ∫⁻_{(a,b)} D ≤ G(b) - G(a)`, with `G(a) = 0` and `G(b) = ν((a, b))`.
    have hGa : G a = 0 := by
      have h : Ioo a b ∩ Iic a = ∅ :=
        eq_empty_of_forall_notMem fun x (hx : x ∈ Ioo a b ∩ Iic a) => not_le.2 hx.1.1 hx.2
      simp only [G, h, measure_empty, ENNReal.toReal_zero]
    have hGb : G b = (ν (Ioo a b)).toReal := by
      have h : Ioo a b ∩ Iic b = Ioo a b := inter_eq_left.2 fun x (hx : x ∈ Ioo a b) => hx.2.le
      simp only [G, h]
    rw [setLIntegral_congr_fun measurableSet_Ioo fun t ht => Set.indicator_of_mem ht D]
    calc ∫⁻ t in Ioo a b, D t ≤ ENNReal.ofReal (G b - G a) :=
          Submission.slicing_mb_dm_lintegral_lowerLeftDini_le G hG_mono a b hab.le
      _ = ν (Ioo a b) := by rw [hGa, hGb, sub_zero, ENNReal.ofReal_toReal hQ]
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
/-- Coordinates of a Borel `k`-vector field in an isometric chart `J` of the `k`-covectors:
`u(x) = (v(x)(J⁻¹eᵢ))ᵢ` is Borel, `‖u‖ ≤ 1`, `‖u‖ = 1` `μ`-a.e. and `v(x)(α) = ⟨Jα, u(x)⟩`. -/
theorem Submission.smr_ufd_unit_coord_field :
    ∀ (P k N : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k)
      (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖) →
      (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) →
      (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) →
      (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) →
      ∃ u : Eucl P → EuclideanSpace ℝ (Fin N), Measurable u ∧ (∀ x, ‖u x‖ ≤ 1) ∧
        (∀ᵐ x ∂μ, ‖u x‖ = 1) ∧
        ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x) := by
  intro P k N μ v J hJ hv hmeas hae
  -- Coordinates in the chart `J`: `u(x)ᵢ = v(x)(J⁻¹eᵢ)`.
  let u : Eucl P → EuclideanSpace ℝ (Fin N) := fun x =>
    WithLp.toLp 2 (fun i => v x (J.symm (EuclideanSpace.single i 1)))
  -- Pairing formula `v(x)(α) = ⟨Jα, u(x)⟩`, by expanding `Jα` in the standard basis.
  have hpair : ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x) := by
    intro x α
    have hexp : J α = ∑ i, (J α) i • EuclideanSpace.single i (1 : ℝ) := by
      simpa [EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (J α)).symm
    conv_lhs => rw [← J.symm_apply_apply α, hexp]
    simp [map_sum, map_smul, PiLp.inner_apply, u, mul_comm]
  -- `‖u(x)‖ ≤ 1`: test with `α = J⁻¹u(x)`, so `‖u(x)‖² = v(x)(α) ≤ |α| = ‖u(x)‖`.
  have hle : ∀ x, ‖u x‖ ≤ 1 := by
    intro x
    have h1 : ‖u x‖ ^ 2 ≤ ‖u x‖ := by
      have := hv x (J.symm (u x))
      rw [hpair, hJ, LinearEquiv.apply_symm_apply, real_inner_self_eq_norm_sq] at this
      exact (le_abs_self _).trans this
    by_contra h
    nlinarith [norm_nonneg (u x), not_le.mp h]
  refine ⟨u, ?_, hle, ?_, hpair⟩
  · exact (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp (measurable_pi_iff.mpr fun i => hmeas _)
  -- `‖u(x)‖ = 1` a.e.: by Cauchy–Schwarz, `1 = v(x)(α) = ⟨Jα, u(x)⟩ ≤ |α| ‖u(x)‖ ≤ ‖u(x)‖`.
  · filter_upwards [hae] with x ⟨α, hα, hvα⟩
    refine le_antisymm (hle x) ?_
    have h2 : (1 : ℝ) ≤ ‖J α‖ * ‖u x‖ := by
      rw [← hvα, hpair]
      exact real_inner_le_norm _ _
    rw [← hJ] at h2
    nlinarith [norm_nonneg (u x), covectorEuclideanNorm_nonneg α]
/-- Compact inner approximation inside an open `W ⊆ U`: if `μ` is finite on compact subsets of
`U`, `E` is Borel and `c < μ (W ∩ E)`, then some compact `K ⊆ W ∩ E` has `c < μ K`. -/
theorem Submission.smr_ufd_cl_inner_compact : ∀ (P : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → ∀ E : Set (Eucl P), MeasurableSet E → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < μ (W ∩ E) → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ W ∩ E ∧ c < μ K := by
  intro P U μ hfin E hE W hW hWU c hc
  -- Step 1: compact sets `K j = F j ∩ closedBall 0 j ⊆ W`, increasing, with `⋃ j, K j = W`,
  -- where `F j` are closed, increasing and exhaust `W`.
  obtain ⟨F, hFc, hFW, hFU, hFm⟩ := hW.exists_iUnion_isClosed
  set K : ℕ → Set (Eucl P) := fun j => F j ∩ closedBall 0 j
  have hKc : ∀ j, IsCompact (K j) := fun j => (isCompact_closedBall 0 (j : ℝ)).inter_left (hFc j)
  have hKW : ∀ j, K j ⊆ W := fun j => inter_subset_left.trans (hFW j)
  have hKm : Monotone K := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j, K j = W := by
    refine Subset.antisymm (iUnion_subset hKW) fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i n, hFm (le_max_left i n) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hn.trans (Nat.cast_le.2 (le_max_right i n))
  -- Step 2: continuity from below gives `j` with `c < μ (E ∩ K j)`.
  have hlim : Tendsto (fun j => μ (E ∩ K j)) atTop (𝓝 (μ (W ∩ E))) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun j => E ∩ K j)
      (fun i j hij => inter_subset_inter_right E (hKm hij))
    rwa [← inter_iUnion, hKU, inter_comm E W] at h
  obtain ⟨j, hj⟩ := ((tendsto_order.1 hlim).1 c hc).exists
  -- Step 3: `E' = E ∩ K j` is Borel, `E' ⊆ W ∩ E` and `μ E' ≤ μ (K j) < ∞`.
  set E' := E ∩ K j
  have hE'm : MeasurableSet E' := hE.inter (hKc j).isClosed.measurableSet
  have hE'W : E' ⊆ W ∩ E := fun x hx => ⟨hKW j hx.2, hx.1⟩
  have hE'fin : μ E' < ∞ :=
    (measure_mono inter_subset_right).trans_lt (hfin _ (hKc j) ((hKW j).trans hWU))
  -- Step 4: the finite measure `μ ⌞ E'` on `ℝ^P` is inner regular by compact sets.
  have : IsFiniteMeasure (μ.restrict E') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hE'fin⟩
  have hcE' : c < μ.restrict E' E' := by rwa [Measure.restrict_apply_self]
  obtain ⟨L, hLE', hLc, hL⟩ :=
    hE'm.exists_lt_isCompact_of_ne_top (μ := μ.restrict E') (measure_ne_top _ E') hcE'
  -- Step 5: `L` is compact, `L ⊆ E' ⊆ W ∩ E` and `c < μ L`.
  refine ⟨L, hLc, hLE'.trans hE'W, ?_⟩
  rwa [Measure.restrict_eq_self μ hLE'] at hL
/-- Lusin's theorem with compact sets (Simon Ch. 1, 1.17, applied coordinatewise): if `μ` is a
measure on `ℝ^P`, `u : ℝ^P → ℝ^N` is Borel and `A ⊆ ℝ^P` is Borel with `μ(A) < ∞`, then for every
`ε > 0` there is a compact `C ⊆ A` with `μ(A ∖ C) < ε` and `u|C` continuous. -/
theorem Submission.smr_ufd_cl_vector_lusin : ∀ (P N : ℕ) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable u → ∀ A : Set (Eucl P), MeasurableSet A → μ A ≠ ∞ → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ A ∧ μ (A \ C) < ε ∧ ContinuousOn u C := by
  intro P N μ u hu A hA hAfin ε hε
  -- Step 1: every Borel `S` with `μ(S) < ∞` has, for every `δ > 0`, a compact (hence closed)
  -- `F ⊆ S` with `μ(S ∖ F) < δ`: the finite measure `ν = μ ⌞ S` is regular on `ℝ^P`, and
  -- `ν = μ` on subsets of `S`.
  have hreg : ∀ S : Set (Eucl P), MeasurableSet S → μ S ≠ ∞ → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ S, IsCompact F ∧ IsClosed F ∧ μ (S \ F) < δ := by
    intro S hS hSfin δ hδ
    have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
    have : (μ.restrict S).Regular :=
      Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    obtain ⟨F, hFS, hFc, hFcl, hFlt⟩ :=
      hS.exists_isCompact_isClosed_sdiff_lt (μ := μ.restrict S) (measure_ne_top _ _) hδ
    refine ⟨F, hFS, hFc, hFcl, ?_⟩
    rwa [Measure.restrict_apply (hS.diff hFcl.measurableSet), inter_eq_left.2 sdiff_subset]
      at hFlt
  -- Step 2: an error budget `0 < η < ∞` with `(N + 1) η < ε`.
  obtain ⟨η, hη0, hηε⟩ :=
    ENNReal.exists_pos_mul_lt (a := ((N + 1 : ℕ) : ℝ≥0∞)) (ENNReal.natCast_ne_top _) hε
  have hηtop : η ≠ ∞ := by
    rintro rfl
    rw [ENNReal.top_mul (by exact_mod_cast Nat.succ_ne_zero N)] at hηε
    exact not_top_lt hηε
  -- Step 3: the coordinates `u_i = (u ·) i` are Borel.
  have hui : ∀ i : Fin N, Measurable fun x => u x i := fun i =>
    (EuclideanSpace.proj i).continuous.measurable.comp hu
  -- Step 4: Lusin's theorem (Simon Ch. 1, 1.17) on `A` for a Borel `f : ℝ^P → ℝ`, with the
  -- closed regularity of Step 1.  SimonGMT's `Chapter01.Lusin` is outside the frozen imports, so
  -- it is proved here through a countable basis `(b k)` of `ℝ`: closed `G k ⊆ A ∩ f⁻¹(b k)` and
  -- `H k ⊆ A ∖ f⁻¹(b k)` with defects `< δ k`, `∑ δ k < η / 2`, and `F = ⋂ k, (G k ∪ H k)`.
  have hlusin : ∀ f : Eucl P → ℝ, Measurable f →
      ∃ F ⊆ A, IsClosed F ∧ μ (A \ F) < η ∧ ContinuousOn f F := by
    intro f hf
    obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis ℝ
    have hbo : ∀ k, IsOpen (b k) := fun k => hb.isOpen (mem_range_self k)
    obtain ⟨δ, hδ0, hδη⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hη0.ne').ne' ℕ
    have hδ : ∀ k, ((δ k : ℝ≥0) : ℝ≥0∞) ≠ 0 := fun k => ENNReal.coe_ne_zero.2 (hδ0 k).ne'
    choose G hGA hGc hGcl hGlt using fun k =>
      hreg _ (hA.inter (hf (hbo k).measurableSet))
        (ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)) (δ k) (hδ k)
    choose H hHA hHc hHcl hHlt using fun k =>
      hreg _ (hA.diff (hf (hbo k).measurableSet))
        (ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)) (δ k) (hδ k)
    refine ⟨⋂ k, (G k ∪ H k), ?_, isClosed_iInter fun k => (hGcl k).union (hHcl k), ?_, ?_⟩
    · exact (iInter_subset _ 0).trans
        (union_subset ((hGA 0).trans inter_subset_left) ((hHA 0).trans sdiff_subset))
    -- `A ∖ F ⊆ ⋃ k, ((A ∩ f⁻¹(b k)) ∖ G k ∪ (A ∖ f⁻¹(b k)) ∖ H k)`.
    · calc μ (A \ ⋂ k, (G k ∪ H k))
          ≤ μ (⋃ k, ((A ∩ f ⁻¹' b k) \ G k ∪ (A \ f ⁻¹' b k) \ H k)) := by
            refine measure_mono fun x hx => ?_
            obtain ⟨k, hk⟩ : ∃ k, x ∉ G k ∪ H k := by
              by_contra! h
              exact hx.2 (mem_iInter.2 h)
            refine mem_iUnion.2 ⟨k, ?_⟩
            by_cases hxb : f x ∈ b k
            · exact Or.inl ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inl h)⟩
            · exact Or.inr ⟨⟨hx.1, hxb⟩, fun h => hk (Or.inr h)⟩
        _ ≤ ∑' k, μ ((A ∩ f ⁻¹' b k) \ G k ∪ (A \ f ⁻¹' b k) \ H k) := measure_iUnion_le _
        _ ≤ ∑' k, ((δ k : ℝ≥0∞) + δ k) := ENNReal.tsum_le_tsum fun k =>
            (measure_union_le _ _).trans (add_le_add (hGlt k).le (hHlt k).le)
        _ = ∑' k, (δ k : ℝ≥0∞) + ∑' k, (δ k : ℝ≥0∞) := ENNReal.tsum_add
        _ < η / 2 + η / 2 := ENNReal.add_lt_add hδη hδη
        _ = η := ENNReal.add_halves η
    -- `f⁻¹(b k) ∩ F = (H k)ᶜ ∩ F` is relatively open in `F` for every basic open set `b k`.
    · rw [hb.continuousOn_iff]
      rintro t ⟨k, rfl⟩
      refine ⟨(H k)ᶜ, (hHcl k).isOpen_compl, ?_⟩
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
      constructor
      · rintro ⟨hxb, hxF⟩
        exact ⟨fun hxH => ((hHA k) hxH).2 hxb, hxF⟩
      · rintro ⟨hxH, hxF⟩
        refine ⟨?_, hxF⟩
        rcases mem_iInter.1 hxF k with hxG | hxH'
        · exact ((hGA k) hxG).2
        · exact absurd hxH' hxH
  -- For each coordinate `i`: a closed `F i ⊆ A` with `μ(A ∖ F i) < η` and `u_i` continuous
  -- on `F i`.
  choose F hFA hFcl hFlt hFcont using fun i => hlusin _ (hui i)
  -- Step 5: a compact `K ⊆ A` with `μ(A ∖ K) < η`.
  obtain ⟨K, hKA, hKc, -, hKlt⟩ := hreg A hA hAfin η hη0.ne'
  -- Step 6: `C = K ∩ ⋂ i, F i` is compact and `C ⊆ K ⊆ A`.
  refine ⟨K ∩ ⋂ i, F i, hKc.inter_right (isClosed_iInter hFcl), inter_subset_left.trans hKA,
    ?_, ?_⟩
  -- Step 8: `A ∖ C ⊆ (A ∖ K) ∪ ⋃ i, (A ∖ F i)`, so `μ(A ∖ C) < η + N η = (N + 1) η < ε`.
  · have hsum : ∑ i, μ (A \ F i) ≤ ∑ _i : Fin N, η :=
      Finset.sum_le_sum fun i _ => (hFlt i).le
    have hsum_ne_top : ∑ i, μ (A \ F i) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun _ _ => hηtop) hsum
    calc μ (A \ (K ∩ ⋂ i, F i))
        ≤ μ ((A \ K) ∪ ⋃ i, (A \ F i)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxK : x ∈ K
          · obtain ⟨i, hi⟩ : ∃ i, x ∉ F i := by
              by_contra! h
              exact hx.2 ⟨hxK, mem_iInter.2 h⟩
            exact Or.inr (mem_iUnion.2 ⟨i, hx.1, hi⟩)
          · exact Or.inl ⟨hx.1, hxK⟩
      _ ≤ μ (A \ K) + ∑ i, μ (A \ F i) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
      _ < η + ∑ _i : Fin N, η := ENNReal.add_lt_add_of_lt_of_le hsum_ne_top hKlt hsum
      _ = η * ((N + 1 : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ < ε := hηε
  -- Step 7: every coordinate of `u` is continuous on `C ⊆ F i`, hence so is `u`.
  · have h : ContinuousOn (fun x => WithLp.ofLp (u x)) (K ∩ ⋂ i, F i) :=
      continuousOn_pi.2 fun i => (hFcont i).mono (inter_subset_right.trans (iInter_subset _ i))
    exact (PiLp.continuous_toLp 2 _).comp_continuousOn h

/-- Lusin's theorem with compact sets of large measure (Simon Ch. 1, 1.17, with inner regularity;
used for Ch. 6, 2.7–2.9): let `μ` be finite on compact subsets of `U`, `u : ℝ^P → ℝ^N` Borel,
`E` Borel and `W ⊆ U` open.  If `c < μ(W ∩ E)`, then some compact `C ⊆ W ∩ E` has `c < μ(C)`
and `u|C` continuous. -/
theorem Submission.smr_ufd_compact_lusin_set :
    ∀ (P N : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)),
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → Measurable u →
      ∀ E : Set (Eucl P), MeasurableSet E → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U →
      ∀ c : ℝ≥0∞, c < μ (W ∩ E) →
        ∃ C : Set (Eucl P), IsCompact C ∧ C ⊆ W ∩ E ∧ c < μ C ∧ ContinuousOn u C := by
  intro P N U μ u hfin hu E hE W hW hWU c hc
  -- Inner regularity: a compact `C₀ ⊆ W ∩ E` with `c < μ(C₀)`.
  obtain ⟨C₀, hC₀, hC₀WE, hcC₀⟩ :=
    Submission.smr_ufd_cl_inner_compact P U μ hfin E hE W hW hWU c hc
  -- `C₀` is a compact subset of `W ⊆ U`, so `μ(C₀) < ∞`.
  have hC₀fin : μ C₀ ≠ ∞ := (hfin C₀ hC₀ (hC₀WE.trans (inter_subset_left.trans hWU))).ne
  -- Lusin on `C₀` with error `δ = μ(C₀) - c > 0`: a compact `C ⊆ C₀` with `μ(C₀ ∖ C) < δ` on
  -- which `u` is continuous.
  obtain ⟨C, hC, hCC₀, hC₀C, hu_cont⟩ :=
    Submission.smr_ufd_cl_vector_lusin P N μ u hu C₀ hC₀.measurableSet hC₀fin (μ C₀ - c)
      (tsub_pos_iff_lt.2 hcC₀).ne'
  -- `μ(C₀) - μ(C) ≤ μ(C₀ ∖ C) < μ(C₀) - c`, hence `c < μ(C)`.
  exact ⟨C, hC, hCC₀.trans hC₀WE, lt_of_tsub_lt_tsub_left (le_measure_sdiff.trans_lt hC₀C),
    hu_cont⟩
/-- Tietze extension into the closed unit ball of `ℝ^N`: if `u` is continuous on a closed set
`C ⊆ ℝ^P` with `‖u‖ ≤ 1` on `C`, there is a continuous `w : ℝ^P → ℝ^N` with `‖w‖ ≤ 1` and
`w = u` on `C`.  Off `C`, `w` is a continuous selection (partition of unity) of the convex hulls
of the values of `u` on `C ∩ B(y, 3 d(y, C))`, as in Dugundji's extension theorem. -/
theorem Submission.smr_ufd_ball_tietze :
    ∀ (P N : ℕ) (C : Set (Eucl P)) (u : Eucl P → EuclideanSpace ℝ (Fin N)), IsClosed C →
      ContinuousOn u C → (∀ x ∈ C, ‖u x‖ ≤ 1) →
      ∃ w : Eucl P → EuclideanSpace ℝ (Fin N), Continuous w ∧ (∀ x, ‖w x‖ ≤ 1) ∧
        ∀ x ∈ C, w x = u x := by
  intro P N C u hC hu hu1
  -- Empty `C`: take `w = 0`.
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, continuous_const, fun x => by simp, fun x hx => hx.elim⟩
  -- For `y ∉ C`, `t y` is the convex hull of `u (C ∩ B(y, 3 d(y, C)))`.
  set t : (Cᶜ : Set (Eucl P)) → Set (EuclideanSpace ℝ (Fin N)) := fun y =>
    convexHull ℝ (u '' (C ∩ ball (y : Eucl P) (3 * infDist (y : Eucl P) C)))
  have htc : ∀ y, Convex ℝ (t y) := fun y => convex_convexHull ℝ _
  have hpos : ∀ y : (Cᶜ : Set (Eucl P)), 0 < infDist (y : Eucl P) C := fun y =>
    (hC.notMem_iff_infDist_pos hne).1 y.2
  -- Locally constant selections: `u c` for a point `c ∈ C` with `|y - c| < 2 d(y, C)`.
  have hloc : ∀ y : (Cᶜ : Set (Eucl P)), ∃ v, ∀ᶠ z in 𝓝 y, v ∈ t z := by
    intro y
    obtain ⟨c, hcC, hc⟩ := (infDist_lt_iff hne).1
      (by linarith [hpos y] : infDist (y : Eucl P) C < 2 * infDist (y : Eucl P) C)
    refine ⟨u c, ?_⟩
    have h1 : ContinuousAt (fun z : (Cᶜ : Set (Eucl P)) => dist (z : Eucl P) c) y :=
      (continuous_subtype_val.dist continuous_const).continuousAt
    have h2 : ContinuousAt (fun z : (Cᶜ : Set (Eucl P)) => 3 * infDist (z : Eucl P) C) y :=
      (continuous_const.mul ((continuous_infDist_pt C).comp continuous_subtype_val)).continuousAt
    filter_upwards [h1.eventually_lt h2 (by linarith [hpos y])] with z hz
    exact subset_convexHull ℝ _ ⟨c, ⟨hcC, by rw [mem_ball, dist_comm]; exact hz⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const htc hloc
  -- Every `t y` lies in the closed unit ball.
  have htB : ∀ y, t y ⊆ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := fun y =>
    convexHull_min (by rintro _ ⟨c, hc, rfl⟩; simpa using hu1 c hc.1) (convex_closedBall 0 1)
  classical
  refine ⟨fun x => if hx : x ∈ C then u x else g ⟨x, hx⟩, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ C
    · -- At `x ∈ C`: nearby values of `u` on `C` are close to `u x`, and so are their hulls.
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδu⟩ := Metric.continuousOn_iff.1 hu x hx (ε / 2) (half_pos hε)
      filter_upwards [ball_mem_nhds x (by positivity : 0 < δ / 4)] with y hy
      have hyx : dist y x < δ / 4 := mem_ball.1 hy
      rw [dite_eq_left hx]
      by_cases hyC : y ∈ C
      · rw [dite_eq_left hyC]
        exact (hδu y hyC (by linarith)).trans (half_lt_self hε)
      · rw [dite_eq_right hyC]
        have hsub : t ⟨y, hyC⟩ ⊆ closedBall (u x) (ε / 2) := by
          refine convexHull_min ?_ (convex_closedBall _ _)
          rintro _ ⟨c, ⟨hcC, hcy⟩, rfl⟩
          have hcy' : dist c y < 3 * infDist y C := mem_ball.1 hcy
          have hinf : infDist y C ≤ dist y x := infDist_le_dist_of_mem hx
          have hcx : dist c x < δ := by
            calc dist c x ≤ dist c y + dist y x := dist_triangle _ _ _
              _ < δ := by linarith
          exact mem_closedBall.2 (hδu c hcC hcx).le
        exact lt_of_le_of_lt (mem_closedBall.1 (hsub (hg ⟨y, hyC⟩))) (half_lt_self hε)
    · -- Off `C` the glued map is `g` on the open set `Cᶜ`.
      have hcont : ContinuousOn (fun x => if hx : x ∈ C then u x else g ⟨x, hx⟩) Cᶜ := by
        rw [continuousOn_iff_continuous_domRestrict]
        convert g.continuous using 1
        funext y
        have hy : (y : Eucl P) ∉ C := y.2
        simp [hy]
      exact hcont.continuousAt (hC.isOpen_compl.mem_nhds hx)
  · intro x
    dsimp only
    by_cases hx : x ∈ C
    · rw [dite_eq_left hx]
      exact hu1 x hx
    · rw [dite_eq_right hx]
      simpa using htB _ (hg ⟨x, hx⟩)
  · intro x hx
    exact dite_eq_left hx
/-- **Small cutoff (step of Simon Ch. 6, 2.7–2.9, pp. 136–137).**  If `μ` is finite on compact
subsets of `U`, `C` is compact and `W ⊆ U` is open with `C ⊆ W`, then for every `ε > 0` there is
a continuous compactly supported `ψ : ℝ^P → [0, 1]` with `tsupport ψ ⊆ W`, `ψ = 1` on `C` and
`μ(support ψ ∖ C) < ε`.  Choose `r > 0` with the compact `cthickening r C ⊆ W`; the open
thickenings `O j = thickening (r / (j + 1)) C` decrease to `C`, so by continuity from above
`μ(O j ∖ C) < ε` for some `j`, and Urysohn's lemma for `C` and `(O j)ᶜ` gives `ψ`. -/
theorem Submission.smr_ufd_small_cutoff : ∀ (P : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → ∀ C W : Set (Eucl P), IsCompact C → IsOpen W → C ⊆ W → W ⊆ U → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ ψ : Eucl P → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x ∈ C, ψ x = 1) ∧ μ (Function.support ψ \ C) < ε := by
  intro P U μ hfin C W hC hW hCW hWU ε hε
  -- Step 1: a compact closed thickening `cthickening r C ⊆ W ⊆ U`, of finite measure.
  obtain ⟨r, hr, hrW⟩ := hC.exists_cthickening_subset_open hW hCW
  have hKfin : μ (cthickening r C) < ∞ := hfin _ hC.cthickening (hrW.trans hWU)
  -- Step 2: the open thickenings `O j = thickening (r / (j + 1)) C` contain `C`, decrease, lie in
  -- `cthickening r C`, and `⋂ j, O j ⊆ C`.
  set δ : ℕ → ℝ := fun j => r / ((j : ℝ) + 1) with hδ_def
  set O : ℕ → Set (Eucl P) := fun j => thickening (δ j) C with hO_def
  have hδ_pos : ∀ j, 0 < δ j := fun j => div_pos hr (by positivity)
  have hδ_le : ∀ j, δ j ≤ r := fun j =>
    div_le_self hr.le (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hCO : ∀ j, C ⊆ O j := fun j => self_subset_thickening (hδ_pos j) C
  have hOK : ∀ j, closure (O j) ⊆ cthickening r C := fun j =>
    (closure_thickening_subset_cthickening _ _).trans (cthickening_mono (hδ_le j) C)
  have hO_anti : Antitone O := fun i j hij =>
    thickening_mono (div_le_div_of_nonneg_left hr.le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hij)) C
  have hO_inter : (⋂ j, O j) ⊆ C := by
    intro x hx
    rw [← hC.isClosed.closure_eq, closure_eq_iInter_thickening, mem_iInter₂]
    intro t ht
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (div_pos ht hr)
    have hjt : δ j ≤ t := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [one_div, inv_lt_iff_one_lt_mul₀ h1, div_mul_eq_mul_div, one_lt_div hr] at hj
      rw [hδ_def, div_le_iff₀ h1]
      exact hj.le
    exact thickening_mono hjt C (mem_iInter.1 hx j)
  -- Step 3: continuity from above on the halos `O j ∖ C` (open minus closed, decreasing, the
  -- first of finite measure, empty intersection) gives `j` with `μ (O j ∖ C) < ε`.
  have hD_meas : ∀ j, NullMeasurableSet (O j \ C) μ := fun j =>
    (isOpen_thickening.measurableSet.diff hC.isClosed.measurableSet).nullMeasurableSet
  have hD_anti : Antitone fun j => O j \ C := fun i j hij => sdiff_subset_sdiff_left (hO_anti hij)
  have hD_fin : ∃ j, μ (O j \ C) ≠ ∞ :=
    ⟨0, ((measure_mono (sdiff_subset.trans (subset_closure.trans (hOK 0)))).trans_lt hKfin).ne⟩
  have hD_empty : (⋂ j, O j \ C) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    rw [mem_iInter] at hx
    exact (hx 0).2 (hO_inter (mem_iInter.2 fun j => (hx j).1))
  have hT := tendsto_measure_iInter_atTop hD_meas hD_anti hD_fin
  rw [hD_empty, measure_empty] at hT
  obtain ⟨j, hj⟩ := (hT.eventually (gt_mem_nhds (pos_iff_ne_zero.2 hε))).exists
  -- Step 4: Urysohn's lemma for the compact `C` and the closed `(O j)ᶜ`, disjoint as `C ⊆ O j`.
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hC
    isOpen_thickening.isClosed_compl (disjoint_compl_right_iff_subset.2 (hCO j))
  -- Step 5: `support f ⊆ O j`, so `tsupport f ⊆ closure (O j) ⊆ cthickening r C ⊆ W` and
  -- `μ (support f ∖ C) ≤ μ (O j ∖ C) < ε`.
  have hsupp : Function.support f ⊆ O j := fun x hx => by
    by_contra h
    exact hx (hf0 h)
  refine ⟨f, f.continuous, hfc, (closure_mono hsupp).trans ((hOK j).trans hrW),
    fun x => hf01 x, fun x hx => hf1 hx, ?_⟩
  exact (measure_mono (sdiff_subset_sdiff_left hsupp)).trans_lt hj
/-- Simon Ch. 6, 2.7–2.9 (the final step of the unit-form density argument): if `|g| ≤ 1`, `g = 1`
on `C ⊆ A`, `g = 0` off `S` with `μ(S) < ∞` and `c + μ(S ∖ C) < μ(C)`, then `c < ∫_A g dμ`.  As
`g = 1` on `C` and `g = 0` off `S`, `C ⊆ S`, so all measures involved are finite, and `|g| ≤ 1_S`
makes `g` integrable.  Then `∫_A g = μ(C) + ∫_{A ∖ C} g` and
`|∫_{A ∖ C} g| = |∫_{(A ∖ C) ∩ S} g| ≤ μ(S ∖ C)`, so `∫_A g ≥ μ(C) − μ(S ∖ C) > c`. -/
theorem Submission.smr_ufd_integral_lower_bound :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (g : Eucl P → ℝ) (A C S : Set (Eucl P)) (c : ℝ≥0∞), MeasurableSet A → MeasurableSet C → MeasurableSet S → C ⊆ A → μ S < ∞ → Measurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ C, g x = 1) → (∀ x, x ∉ S → g x = 0) → c + μ (S \ C) < μ C → c < ENNReal.ofReal (∫ x in A, g x ∂μ) := by
  intro P μ g A C S c hA hC hS hCA hSfin hg hg1 hgC hgS hc
  -- Step 1 (finiteness): `C ⊆ S`, so `μ C ≤ μ S < ∞`, and `c`, `μ (S \ C)` are finite.
  have hCS : C ⊆ S := fun x hx => by
    by_contra hxS
    have h := hgC x hx
    rw [hgS x hxS] at h
    exact zero_ne_one h
  have hCfin : μ C ≠ ∞ := ((measure_mono hCS).trans_lt hSfin).ne
  have hsum : c + μ (S \ C) ≠ ∞ := ne_top_of_lt hc
  have hcfin : c ≠ ∞ := (ENNReal.add_ne_top.1 hsum).1
  have hSCfin : μ (S \ C) ≠ ∞ := (ENNReal.add_ne_top.1 hsum).2
  have hreal : c.toReal + μ.real (S \ C) < μ.real C := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add hcfin hSCfin]
    exact (ENNReal.toReal_lt_toReal hsum hCfin).2 hc
  -- Step 2 (integrability): `|g| ≤ 1_S` and `μ S < ∞`.
  have hgint : Integrable g μ := by
    refine ((integrable_indicator_iff hS).2 (integrableOn_const (C := (1 : ℝ)) hSfin.ne)).mono'
      hg.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S
    · simpa [hx, Real.norm_eq_abs] using hg1 x
    · simp [hx, hgS x hx]
  -- Step 3 (splitting): `∫_A g = ∫_C g + ∫_{A \ C} g = μ(C) + ∫_{A \ C} g`.
  have hsplit : ∫ x in A, g x ∂μ = μ.real C + ∫ x in A \ C, g x ∂μ := by
    have hCint : ∫ x in C, g x ∂μ = ∫ _ in C, (1 : ℝ) ∂μ := setIntegral_congr_fun hC hgC
    rw [← integral_inter_add_sdiff (s := A) hC hgint.integrableOn, inter_eq_right.2 hCA, hCint,
      setIntegral_const, smul_eq_mul, mul_one]
  -- Step 4 (remainder): `|∫_{A \ C} g| ≤ μ((A \ C) ∩ S) ≤ μ(S \ C)`.
  have hsub : (A \ C) ∩ S ⊆ S \ C := fun x hx => ⟨hx.2, hx.1.2⟩
  have hrem : |∫ x in A \ C, g x ∂μ| ≤ μ.real (S \ C) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := (A \ C) ∩ S) (hA.diff hC)
      inter_subset_left fun x hx => hgS x fun hxS => hx.2 ⟨hx.1, hxS⟩]
    have h1 : ‖∫ x in (A \ C) ∩ S, g x ∂μ‖ ≤ 1 * μ.real ((A \ C) ∩ S) :=
      norm_setIntegral_le_of_norm_le_const
        ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.2 hSCfin))
        fun x _ => (Real.norm_eq_abs (g x)).trans_le (hg1 x)
    rw [one_mul, Real.norm_eq_abs] at h1
    exact h1.trans (measureReal_mono hsub hSCfin)
  -- Step 5 (conclusion): `∫_A g ≥ μ(C) − μ(S \ C) > c`.
  rw [ENNReal.lt_ofReal_iff_toReal_lt hcfin, hsplit]
  have := neg_abs_le (∫ x in A \ C, g x ∂μ)
  linarith
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
/-- A `k`-covector on `ℝ^P` whose coordinates `α(e_{I(0)}, …, e_{I(k-1)})` vanish for every
increasing multi-index `I` is zero. -/
theorem Submission.smr_ci_covector_eq_zero_of_coord :
    ∀ (P k : ℕ) (α : Covector (Eucl P) k),
      (∀ I : SimonMultiIndex k P, euclideanCovectorCoordinate α I = 0) → α = 0 := by
  intro P k α hα
  classical
  -- By extensionality on the standard basis it suffices to treat injective index tuples `v`.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap, ContinuousAlternatingMap.toAlternatingMap_zero,
    AlternatingMap.zero_apply]
  -- Sorting `v` gives an increasing multi-index `I` with `e_I = e_v ∘ σ`, `σ := Tuple.sort v`.
  have hsm : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  have h := hα (OrderEmbedding.ofStrictMono _ hsm)
  have heq : (fun j => EuclideanSpace.single (OrderEmbedding.ofStrictMono _ hsm j) (1 : ℝ)) =
      (fun i => EuclideanSpace.single (v i) (1 : ℝ)) ∘ Tuple.sort v := rfl
  -- `α(e_I) = sign σ • α(e_v)`, and the sign is a unit.
  rw [euclideanCovectorCoordinate, heq, ← ContinuousAlternatingMap.coe_toAlternatingMap α,
    AlternatingMap.map_perm] at h
  exact (smul_eq_zero_iff_eq _).mp h
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

/-- Simon (6.1.2)–(6.1.5): listing the coefficients `α(e_{I(0)}, …, e_{I(k-1)})` over the
increasing multi-indices `I` is a linear isomorphism `J` of the `k`-covectors on `ℝ^P` onto `ℝ^N`
with `|α| = ‖J α‖` for the Euclidean coefficient norm `|α| = covectorEuclideanNorm α`. -/
theorem Submission.smr_covector_coord_isometry :
    ∀ (P k : ℕ), ∃ (N : ℕ) (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)),
      ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖ := by
  intro P k
  -- Enumerate the increasing multi-indices `I : Fin k ↪o Fin P` by `Fin N`.
  let σ : Fin (Fintype.card (SimonMultiIndex k P)) ≃ SimonMultiIndex k P :=
    (Fintype.equivFin (SimonMultiIndex k P)).symm
  -- The coordinate map `J α = (α(e_{σ n}))_n`, linear because evaluation is.
  obtain ⟨J, hJ⟩ : ∃ J : Covector (Eucl P) k →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (SimonMultiIndex k P))),
      ∀ α n, J α n = euclideanCovectorCoordinate α (σ n) :=
    ⟨{ toFun := fun α => WithLp.toLp 2 fun n => euclideanCovectorCoordinate α (σ n)
       map_add' := fun α β => by
         ext n
         simp [euclideanCovectorCoordinate]
       map_smul' := fun c α => by
         ext n
         simp [euclideanCovectorCoordinate] }, fun _ _ => rfl⟩
  have hbij : Function.Bijective J := by
    refine ⟨(injective_iff_map_eq_zero J).2 fun α hα => ?_, fun y => ?_⟩
    · -- injective: a covector whose coordinates all vanish is zero
      refine Submission.smr_ci_covector_eq_zero_of_coord P k α fun I => ?_
      rw [← σ.apply_symm_apply I, ← hJ, hα, PiLp.zero_apply]
    · -- surjective: `∑_I y_{σ⁻¹ I} dx^I` has coordinates `y`
      refine ⟨∑ I : SimonMultiIndex k P,
        y (σ.symm I) • wedgeCovectors k (fun j => EuclideanSpace.proj (I j)), ?_⟩
      ext n
      rw [hJ, Submission.smr_ci_coord_sum_smul_wedge, σ.symm_apply_apply]
  refine ⟨_, LinearEquiv.ofBijective J hbij, fun α => ?_⟩
  -- Both norms are square roots of the same sum of squares, reindexed along `σ`.
  rw [Submission.smr_ci_norm_eq_sqrt_sum_coord_sq, LinearEquiv.ofBijective_apply,
    EuclideanSpace.norm_eq, ← σ.sum_comp]
  simp only [hJ, Real.norm_eq_abs, sq_abs]
/-- **Mollification step of Simon Ch. 6, 2.7–2.9 (pp. 136–137).**  A continuous compactly
supported `k`-form `φ` with `tsupport φ ⊆ V`, `V` open, is a uniform limit, in the Euclidean
coefficient norm, of test forms supported in `V`.  As `|α| ≤ √M ‖α‖` (`M = #(Fin k → Fin P)`,
`‖α‖` the operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ φ)`:
`ψ ⋆ φ` is the convolution of `φ` with a normalized smooth bump `ψ` supported in a ball whose
radius is a uniform-continuity modulus of `φ`, and `χ` is a smooth cutoff with values in `[0, 1]`,
equal to `1` exactly on `tsupport φ`, whose support `V'` has compact closure in `V`. -/
theorem Submission.smr_exists_testForm_uniform_approx : ∀ (P k : ℕ) (U V : Set (Eucl P)) (φ : Eucl P → Covector (Eucl P) k), IsOpen V → V ⊆ U → Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧ ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ ε := by
  intro P k U V φ hV hVU hφ hφc hφV ε hε
  -- Step 1: `|α| ≤ C ‖α‖` with `C = √M`, since every coefficient satisfies
  -- `|α(e_I)| ≤ ‖α‖ ∏ ‖e_{I j}‖ = ‖α‖`.
  set C : ℝ := Real.sqrt (Fintype.card (Fin k → Fin P)) with hC_def
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hcmp : ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    rw [hC_def, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc ∑ I : Fin k → Fin P,
          (if StrictMono I then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) ^ 2 else 0)
        ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg α)] using h)
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  have hC1 : 0 < C + 1 := by linarith
  set ε' : ℝ := ε / (C + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε hC1
  -- Step 2: an open `V'` with `tsupport φ ⊆ V'` and `closure V' ⊆ V` compact.
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ :=
    exists_open_between_and_isCompact_closure hφc.isCompact hV hφV
  -- Step 3: a smooth cutoff `χ : ℝ^P → [0, 1]` with `support χ = V'` and `χ = 1` exactly on
  -- `tsupport φ`.
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV'o (isClosed_tsupport φ) hKV'
  -- Step 4: mollification.  `φ` is uniformly continuous with modulus `δ` at accuracy `ε'`; `ψ` is
  -- a smooth bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `g = ψ ⋆ φ` is smooth and
  -- `dist (g x) (φ x) ≤ ε'`.
  obtain ⟨δ, hδ, hφδ⟩ :=
    Metric.uniformContinuous_iff.mp (hφc.uniformContinuous_of_continuous hφ) ε' hε'
  obtain ⟨b, hbs, hbc, hbd, hbr, hb0⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
  have hbnn : ∀ y, 0 ≤ b y := fun y => (hbr (mem_range_self y)).1
  have hbint : 0 < ∫ y, b y :=
    hbd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc (fun y => hbnn y)
      (hb0.symm ▸ one_ne_zero : b 0 ≠ 0)
  set ψ : Eucl P → ℝ := fun y => (∫ z, b z)⁻¹ * b y with hψ_def
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hbd
  have hψc : HasCompactSupport ψ := hbc.mul_left
  have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hbint.le) (hbnn y)
  have hψs : Function.support ψ ⊆ ball 0 δ :=
    (Function.support_mul_subset_right _ _).trans ((subset_tsupport b).trans hbs)
  have hψ1 : ∫ y, ψ y = 1 := by
    rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hbint.ne']
  obtain ⟨g, hg, hgd⟩ : ∃ g : Eucl P → Covector (Eucl P) k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x, dist (g x) (φ x) ≤ ε' :=
    ⟨convolution ψ φ (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      hψc.contDiff_convolution_left _ hψd hφ.locallyIntegrable,
      fun x => dist_convolution_le hε'.le hψs hψnn hψ1 hφ.aestronglyMeasurable
        fun y hy => (hφδ (mem_ball.mp hy)).le⟩
  -- Step 5: `η = χ • g` is a test form with `tsupport η ⊆ closure V' ⊆ V ⊆ U`.
  have hη_supp : tsupport (fun x => χ x • g x) ⊆ closure V' := by
    refine (tsupport_smul_subset_left χ g).trans ?_
    rw [tsupport, hχs]
  have hη_cpt : HasCompactSupport (fun x => χ x • g x) :=
    hV'c.of_isClosed_subset (isClosed_tsupport _) hη_supp
  refine ⟨⟨fun x => χ x • g x, ⟨⟨hχ.smul hg, hη_cpt⟩, hη_supp.trans (hV'V.trans hVU)⟩⟩,
    hη_supp.trans hV'V, fun x => ?_⟩
  -- Step 6: `‖φ x - η x‖ ≤ ε'` (on `tsupport φ`, `η = g`; off it, `φ = 0` and `0 ≤ χ ≤ 1`),
  -- hence `|φ x - η x| ≤ C ε' ≤ ε`.
  have hle : ‖φ x - χ x • g x‖ ≤ ε' := by
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1 x).1 hx, one_smul, ← dist_eq_norm, dist_comm]
      exact hgd x
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hgx : ‖g x‖ ≤ ε' := by simpa [h0, dist_eq_norm] using hgd x
      rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hχx.2).trans hgx
  calc covectorEuclideanNorm (φ x - χ x • g x) ≤ C * ‖φ x - χ x • g x‖ := hcmp _
    _ ≤ C * ε' := mul_le_mul_of_nonneg_left hle hC
    _ ≤ ε := by
      rw [hε'_def, mul_div_assoc', div_le_iff₀ hC1]
      nlinarith

/-- Continuous extension of a current of locally finite mass (Simon Ch. 6, 2.7, pp. 136–137,
steps P1–P2): there is `L` on continuous forms with `L = X` on test forms, additive and
homogeneous on continuous compactly supported forms in `U`, and with `|L φ|` bounded on each
compact `K ⊆ U` for `|φ| ≤ 1` (Euclidean coefficient norm).  `L φ` is the limit of `X (ζ j)`
along any sequence of test forms `ζ j`, supported in a common `V ⊂⊂ U`, converging to `φ`
uniformly; the limit exists and is unique by the mass estimate `|X ω| ≤ M_V(X) · sup |ω|`. -/
theorem Submission.smr_exists_continuous_extension :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) →
      ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ,
        (∀ ω : TestFormOn U k, L (ω : DifferentialForm (Eucl P) k) = X ω) ∧
        (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          L (φ + ψ) = L φ + L ψ) ∧
        (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → L (c • φ) = c * L φ) ∧
        ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
          ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → tsupport φ ⊆ K →
            (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → |L φ| ≤ B := by
  intro P k U hU X hX
  -- Step 0: the Euclidean coefficient norm is a norm, via the isometry `J` onto `ℝ^N`.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have hle : ∀ α β : Covector (Eucl P) k,
      covectorEuclideanNorm β ≤ covectorEuclideanNorm α + covectorEuclideanNorm (α - β) := by
    intro α β
    simp only [hJ, map_sub]
    exact norm_le_norm_add_norm_sub _ _
  have htri : ∀ α β γ : Covector (Eucl P) k, covectorEuclideanNorm (β - γ) ≤
      covectorEuclideanNorm (α - β) + covectorEuclideanNorm (α - γ) := by
    intro α β γ
    simp only [hJ, map_sub]
    calc ‖J β - J γ‖ ≤ ‖J β - J α‖ + ‖J α - J γ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖J α - J β‖ + ‖J α - J γ‖ := by rw [norm_sub_rev (J β)]
  have hadd : ∀ α β γ δ : Covector (Eucl P) k, covectorEuclideanNorm (α + β - (γ + δ)) ≤
      covectorEuclideanNorm (α - γ) + covectorEuclideanNorm (β - δ) := by
    intro α β γ δ
    rw [add_sub_add_comm]
    simp only [hJ, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hJ, hJ, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 1: compact subsets of `U` lie in some `V ⊂⊂ U`, and `⊂⊂ U` is closed under unions.
  have hnbhd : ∀ K, IsCompact K → K ⊆ U → ∃ V, CompactlyContainedOpen V U ∧ K ⊆ V := by
    intro K hK hKU
    obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    exact ⟨V, ⟨hVo, hVc, hVU⟩, hKV⟩
  have hunion : ∀ V₁ V₂, CompactlyContainedOpen V₁ U → CompactlyContainedOpen V₂ U →
      CompactlyContainedOpen (V₁ ∪ V₂) U := by
    rintro V₁ V₂ ⟨h₁o, h₁c, h₁U⟩ ⟨h₂o, h₂c, h₂U⟩
    refine ⟨h₁o.union h₂o, ?_, ?_⟩ <;> rw [closure_union]
    · exact h₁c.union h₂c
    · exact union_subset h₁U h₂U
  -- Step 2 (P1): `|X ω| ≤ M_V · C` for `ω` supported in `V ⊂⊂ U` with `|ω| ≤ C`.
  have hmass : ∀ V, CompactlyContainedOpen V U → ∀ (ω : TestFormOn U k) (C : ℝ),
      tsupport (ω : DifferentialForm (Eucl P) k) ⊆ V →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x) ≤ C) →
      |X ω| ≤ (X.massOn V).toReal * C := by
    intro V hV ω C hωV hC
    -- For `s > C`, both `±s⁻¹ ω` are admissible for `M_V(X)`, hence `|X ω| ≤ M_V · s`.
    have key : ∀ s, C < s → |X ω| ≤ (X.massOn V).toReal * s := by
      intro s hs
      have hs0 : 0 < s := ((covectorEuclideanNorm_nonneg _).trans (hC 0)).trans_lt hs
      have hb : ∀ t : ℝ, |t| = s⁻¹ → t * X ω ≤ (X.massOn V).toReal := by
        intro t ht
        have hadm : t • ω ∈ massAdmissibleOn U k V := by
          refine ⟨(tsupport_smul_subset_right (fun _ => t) _).trans hωV, fun x => ?_⟩
          change covectorEuclideanNorm (t • (ω : DifferentialForm (Eucl P) k) x) ≤ 1
          rw [hsmul, ht, inv_mul_le_iff₀ hs0, mul_one]
          exact (hC x).trans hs.le
        have h := (X.le_massOn hadm).trans (ENNReal.ofReal_toReal (hX V hV).ne).ge
        rwa [ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, map_smul, smul_eq_mul] at h
      have h₁ := hb s⁻¹ (abs_of_pos (inv_pos.2 hs0))
      have h₂ := hb (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs0)])
      rw [inv_mul_le_iff₀ hs0, mul_comm] at h₁
      rw [neg_mul_comm, inv_mul_le_iff₀ hs0, mul_comm] at h₂
      exact abs_le.2 ⟨by linarith, h₁⟩
    -- Let `s ↓ C` along `s = C + 1 / (n + 1)`.
    have hlim : Tendsto (fun n : ℕ => (X.massOn V).toReal * (C + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 ((X.massOn V).toReal * C)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add C).const_mul
        (X.massOn V).toReal
    exact ge_of_tendsto' hlim fun n => key _ (lt_add_of_pos_right C Nat.one_div_pos_of_nat)
  -- Test forms supported in `V₁, V₂ ⊂⊂ U` and uniformly close to the same `φ` have close values.
  have hclose : ∀ (φ : Eucl P → Covector (Eucl P) k) V₁ V₂, CompactlyContainedOpen V₁ U →
      CompactlyContainedOpen V₂ U → ∀ (η ζ : TestFormOn U k) (a b : ℝ),
      tsupport (η : DifferentialForm (Eucl P) k) ⊆ V₁ →
      tsupport (ζ : DifferentialForm (Eucl P) k) ⊆ V₂ →
      (∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ a) →
      (∀ x, covectorEuclideanNorm (φ x - (ζ : DifferentialForm (Eucl P) k) x) ≤ b) →
      |X η - X ζ| ≤ (X.massOn (V₁ ∪ V₂)).toReal * (a + b) := by
    intro φ V₁ V₂ hV₁ hV₂ η ζ a b hη hζ ha hb
    rw [← map_sub X.toCurrent η ζ]
    refine hmass _ (hunion V₁ V₂ hV₁ hV₂) (η - ζ) (a + b) ?_ fun x =>
      (htri (φ x) ((η : DifferentialForm (Eucl P) k) x)
        ((ζ : DifferentialForm (Eucl P) k) x)).trans (add_le_add (ha x) (hb x))
    exact (closure_mono (Function.support_sub _ _)).trans
      (closure_union.subset.trans (union_subset_union hη hζ))
  -- Step 4: approximations supported in a common `V ⊂⊂ U` give Cauchy sequences `X (ζ j)`.
  have hconv : ∀ (φ : Eucl P → Covector (Eucl P) k) V, CompactlyContainedOpen V U →
      ∀ (ζ : ℕ → TestFormOn U k) (d : ℕ → ℝ),
      (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) → Tendsto d atTop (𝓝 0) →
      (∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ d j) →
      ∃ r, Tendsto (fun j => X (ζ j)) atTop (𝓝 r) := by
    intro φ V hV ζ d hζV hd hζ
    have hMd : Tendsto (fun j => (X.massOn (V ∪ V)).toReal * d j) atTop (𝓝 0) := by
      simpa using hd.const_mul (X.massOn (V ∪ V)).toReal
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hMd).2 (ε / 2) (half_pos hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    calc |X (ζ n) - X (ζ N)| ≤ (X.massOn (V ∪ V)).toReal * (d n + d N) :=
          hclose φ V V hV hV (ζ n) (ζ N) (d n) (d N) (hζV n) (hζV N) (hζ n) (hζ N)
      _ = (X.massOn (V ∪ V)).toReal * d n + (X.massOn (V ∪ V)).toReal * d N := mul_add _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hN n hn) (hN N le_rfl)
      _ = ε := add_halves ε
  -- `IsLim φ r`: test forms `ζ j`, supported in a common `V ⊂⊂ U`, converge uniformly to `φ`
  -- (errors `d j → 0`) and `X (ζ j) → r`.
  let IsLim : (Eucl P → Covector (Eucl P) k) → ℝ → Prop := fun φ r =>
    ∃ V, CompactlyContainedOpen V U ∧ ∃ (ζ : ℕ → TestFormOn U k) (d : ℕ → ℝ),
      (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) ∧ Tendsto d atTop (𝓝 0) ∧
      (∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤ d j) ∧
      Tendsto (fun j => X (ζ j)) atTop (𝓝 r)
  -- Step 5: the limit does not depend on the approximation.
  have huniq : ∀ φ r s, IsLim φ r → IsLim φ s → r = s := by
    rintro φ r s ⟨V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩ ⟨V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩
    have h0 : Tendsto (fun j => X (ζ₁ j) - X (ζ₂ j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans
        (hclose φ V₁ V₂ hV₁ hV₂ (ζ₁ j) (ζ₂ j) (d₁ j) (d₂ j) (hs₁ j) (hs₂ j) (ha₁ j)
          (ha₂ j))) ?_
      simpa using (hd₁.add hd₂).const_mul (X.massOn (V₁ ∪ V₂)).toReal
    exact sub_eq_zero.1 (tendsto_nhds_unique (hl₁.sub hl₂) h0)
  -- Definition of `L`: the common limit of the approximations (arbitrary if there are none).
  obtain ⟨L, hL⟩ : ∃ L : (Eucl P → Covector (Eucl P) k) → ℝ, ∀ φ r, IsLim φ r → L φ = r :=
    ⟨fun φ => Classical.epsilon (IsLim φ), fun φ r hr =>
      huniq φ _ _ (Classical.epsilon_spec ⟨r, hr⟩) hr⟩
  -- Step 3: uniform approximants `|φ - ζ j| ≤ 1 / (j + 1)` supported in `V`.
  have happ : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
      ∀ V, CompactlyContainedOpen V U → tsupport φ ⊆ V →
      ∃ ζ : ℕ → TestFormOn U k, (∀ j, tsupport (ζ j : DifferentialForm (Eucl P) k) ⊆ V) ∧
        ∀ j x, covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) ≤
          1 / ((j : ℝ) + 1) := by
    intro φ hφ hφc V hV hφV
    choose ζ hζV hζ using fun j : ℕ =>
      Submission.smr_exists_testForm_uniform_approx P k U V φ hV.1
        (subset_closure.trans hV.2.2) hφ hφc hφV (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨ζ, hζV, hζ⟩
  -- Every `φ ∈ CF(U)` has an approximation, hence a limit.
  have hexists : ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∃ r, IsLim φ r := by
    intro φ hφ hφc hφU
    obtain ⟨V, hV, hφV⟩ := hnbhd _ hφc hφU
    obtain ⟨ζ, hζV, hζ⟩ := happ φ hφ hφc V hV hφV
    obtain ⟨r, hr⟩ := hconv φ V hV ζ _ hζV tendsto_one_div_add_atTop_nhds_zero_nat hζ
    exact ⟨r, V, hV, ζ, _, hζV, tendsto_one_div_add_atTop_nhds_zero_nat, hζ, hr⟩
  refine ⟨L, fun ω => ?_, fun φ ψ hφ hφc hφU hψ hψc hψU => ?_,
    fun c φ hφ hφc hφU => ?_, fun K hK hKU => ?_⟩
  · -- (1) The constant approximation `ζ j = ω`.
    obtain ⟨V, hV, hωV⟩ := hnbhd _ ω.2.1.2 ω.2.2
    exact hL _ _ ⟨V, hV, fun _ => ω, fun _ => 0, fun _ => hωV, tendsto_const_nhds,
      fun _ x => by simp, tendsto_const_nhds⟩
  · -- (2) The sum of approximations of `φ` and `ψ`.
    obtain ⟨r₁, V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩ := hexists φ hφ hφc hφU
    obtain ⟨r₂, V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩ := hexists ψ hψ hψc hψU
    rw [hL φ r₁ ⟨V₁, hV₁, ζ₁, d₁, hs₁, hd₁, ha₁, hl₁⟩,
      hL ψ r₂ ⟨V₂, hV₂, ζ₂, d₂, hs₂, hd₂, ha₂, hl₂⟩]
    refine hL _ _ ⟨V₁ ∪ V₂, hunion V₁ V₂ hV₁ hV₂, fun j => ζ₁ j + ζ₂ j,
      fun j => d₁ j + d₂ j, fun j => ?_, by simpa using hd₁.add hd₂, fun j x => ?_, ?_⟩
    · exact (tsupport_add (ζ₁ j : DifferentialForm (Eucl P) k) (ζ₂ j)).trans
        (union_subset_union (hs₁ j) (hs₂ j))
    · exact (hadd (φ x) (ψ x) ((ζ₁ j : DifferentialForm (Eucl P) k) x)
        ((ζ₂ j : DifferentialForm (Eucl P) k) x)).trans (add_le_add (ha₁ j x) (ha₂ j x))
    · simpa only [map_add] using hl₁.add hl₂
  · -- (3) The scalar multiple of an approximation of `φ`.
    obtain ⟨r, V, hV, ζ, d, hs, hd, ha, hl⟩ := hexists φ hφ hφc hφU
    rw [hL φ r ⟨V, hV, ζ, d, hs, hd, ha, hl⟩]
    refine hL _ _ ⟨V, hV, fun j => c • ζ j, fun j => |c| * d j,
      fun j => (tsupport_smul_subset_right (fun _ => c) _).trans (hs j),
      by simpa using hd.const_mul |c|, fun j x => ?_, ?_⟩
    · have e : (c • φ) x - ((c • ζ j : TestFormOn U k) : DifferentialForm (Eucl P) k) x =
          c • (φ x - (ζ j : DifferentialForm (Eucl P) k) x) := (smul_sub c _ _).symm
      rw [e, hsmul]
      exact mul_le_mul_of_nonneg_left (ha j x) (abs_nonneg c)
    · simpa only [map_smul, smul_eq_mul] using hl.const_mul c
  · -- (4) `|L φ| ≤ 2 M_V` for `|φ| ≤ 1` supported in `K ⊆ V ⊂⊂ U`.
    obtain ⟨V, hV, hKV⟩ := hnbhd K hK hKU
    refine ⟨(X.massOn V).toReal * 2, fun φ hφ hφK hφ1 => ?_⟩
    have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hφK
    obtain ⟨ζ, hζV, hζ⟩ := happ φ hφ hφc V hV (hφK.trans hKV)
    obtain ⟨r, hr⟩ := hconv φ V hV ζ _ hζV tendsto_one_div_add_atTop_nhds_zero_nat hζ
    rw [hL φ r ⟨V, hV, ζ, _, hζV, tendsto_one_div_add_atTop_nhds_zero_nat, hζ, hr⟩]
    refine le_of_tendsto' hr.abs fun j => hmass V hV (ζ j) 2 (hζV j) fun x => ?_
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    calc covectorEuclideanNorm ((ζ j : DifferentialForm (Eucl P) k) x)
        ≤ covectorEuclideanNorm (φ x) +
            covectorEuclideanNorm (φ x - (ζ j : DifferentialForm (Eucl P) k) x) := hle _ _
      _ ≤ 1 + 1 := add_le_add (hφ1 x) ((hζ j x).trans h1)
      _ = 2 := one_add_one_eq_two
/-- **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6(v) of `slicing_mass_representation`.  If
`S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, where `|⟨α, v(x)⟩| ≤ |α|` and `μ` is finite on
compact subsets of `U`, then `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)` for every continuous compactly supported
`k`-form `φ` with `spt φ ⊆ W ⊆ U`, `W` open, and `|φ| ≤ 1`.

Take an open `V ⊇ spt φ` whose closure is a compact subset of `W`.  The smooth approximants
`η_j ∈ 𝒟ᵏ(U)` of `smr_exists_testForm_uniform_approx` (`spt η_j ⊆ V`, `|φ - η_j| ≤ δ_j → 0`),
rescaled to `ζ_j = (1 + δ_j)⁻¹ η_j`, are admissible for `M_W(S)` and satisfy
`|ζ_j - φ| ≤ 2 δ_j`; the triangle inequality and homogeneity of `|·|` come from
`smr_covector_coord_isometry`.  Dominated convergence on `μ ⌞ A` with the bound `1_{closure V}`
gives `S(ζ_j) → ∫_A ⟨φ, v⟩ dμ`, and `ofReal (S(ζ_j)) ≤ M_W(S)` passes to the limit. -/
theorem Submission.smr_ofReal_integral_le_massOn : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → ∀ (A : Set (Eucl P)) (S : GeometricCurrentOn U k), (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ W → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) ≤ S.massOn W := by
  intro P k U μ v hint hfin hv A S hS W hW hWU φ hφc hφs hφW hφ1
  -- `|α| = ‖J α‖` for a linear `J`, so `|·|` is subadditive and absolutely homogeneous.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have hadd : ∀ α β : Covector (Eucl P) k,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hJ, hJ, hJ, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (c : ℝ) (α : Covector (Eucl P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hJ, hJ, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 1: an open `V ⊇ tsupport φ` whose closure is a compact subset of `W ⊆ U`.
  obtain ⟨V, hVo, hφV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hφs hW hφW
  have hKU : closure V ⊆ U := hVW.trans hWU
  have hμK : μ (closure V) < ∞ := hfin _ hVc hKU
  have hVU : V ⊆ U := subset_closure.trans hKU
  -- Step 2: test forms `η j` supported in `V` with `|φ - η j| ≤ δ j → 0`, and
  -- `ζ j = (1 + δ j)⁻¹ • η j`.
  obtain ⟨δ, hδpos, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun j => 1 / ((j : ℝ) + 1), fun j => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩
  have hη : ∀ j : ℕ, ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧
      ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ δ j := fun j =>
    Submission.smr_exists_testForm_uniform_approx P k U V φ hVo hVU hφc hφs hφV (δ j) (hδpos j)
  choose η hηV hηφ using hη
  obtain ⟨ζ, hζx⟩ : ∃ ζ : ℕ → TestFormOn U k, ∀ j x,
      (ζ j : DifferentialForm (Eucl P) k) x = (1 + δ j)⁻¹ • (η j : DifferentialForm (Eucl P) k) x :=
    ⟨fun j => (1 + δ j)⁻¹ • η j, fun j x => rfl⟩
  have hpos : ∀ j, 0 < 1 + δ j := fun j => by linarith [hδpos j]
  have hηle : ∀ j x, covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x) ≤ 1 + δ j := by
    intro j x
    calc covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
        = covectorEuclideanNorm (φ x + -(φ x - (η j : DifferentialForm (Eucl P) k) x)) := by
          congr 1
          abel
      _ ≤ covectorEuclideanNorm (φ x) +
            covectorEuclideanNorm (-(φ x - (η j : DifferentialForm (Eucl P) k) x)) := hadd _ _
      _ ≤ 1 + δ j := by
          rw [covectorEuclideanNorm_neg]
          exact add_le_add (hφ1 x) (hηφ j x)
  -- Step 3: every `ζ j` is admissible for `M_W(S)`, so `ofReal (S (ζ j)) ≤ M_W(S)`.
  have hadm : ∀ j, ζ j ∈ massAdmissibleOn U k W := by
    intro j
    refine ⟨?_, fun x => ?_⟩
    · have hfun : (ζ j : DifferentialForm (Eucl P) k) =
          fun x => (1 + δ j)⁻¹ • (η j : DifferentialForm (Eucl P) k) x := funext (hζx j)
      rw [hfun]
      exact (tsupport_smul_subset_right (fun _ => (1 + δ j)⁻¹) _).trans
        ((hηV j).trans (subset_closure.trans hVW))
    · rw [hζx, hsmul, abs_of_pos (inv_pos.mpr (hpos j))]
      calc (1 + δ j)⁻¹ * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
          ≤ (1 + δ j)⁻¹ * (1 + δ j) :=
            mul_le_mul_of_nonneg_left (hηle j x) (inv_nonneg.mpr (hpos j).le)
        _ = 1 := inv_mul_cancel₀ (hpos j).ne'
  -- Step 4: `|ζ j - φ| ≤ 2 δ j` everywhere, and `ζ j` vanishes off `V`.
  have hclose : ∀ j x,
      covectorEuclideanNorm ((ζ j : DifferentialForm (Eucl P) k) x - φ x) ≤ 2 * δ j := by
    intro j x
    have e : (ζ j : DifferentialForm (Eucl P) k) x - φ x =
        ((1 + δ j)⁻¹ - 1) • (η j : DifferentialForm (Eucl P) k) x +
          -(φ x - (η j : DifferentialForm (Eucl P) k) x) := by
      rw [hζx]
      module
    have habs : |(1 + δ j)⁻¹ - 1| = δ j / (1 + δ j) := by
      have h : (1 + δ j)⁻¹ - 1 = -(δ j / (1 + δ j)) := by
        linear_combination mul_inv_cancel₀ (hpos j).ne'
      rw [h, abs_neg, abs_of_pos (div_pos (hδpos j) (hpos j))]
    have h2 : δ j / (1 + δ j) * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
        ≤ δ j :=
      calc δ j / (1 + δ j) * covectorEuclideanNorm ((η j : DifferentialForm (Eucl P) k) x)
          ≤ δ j / (1 + δ j) * (1 + δ j) :=
            mul_le_mul_of_nonneg_left (hηle j x) (div_pos (hδpos j) (hpos j)).le
        _ = δ j := div_mul_cancel₀ _ (hpos j).ne'
    rw [e]
    refine (hadd _ _).trans ?_
    rw [covectorEuclideanNorm_neg, hsmul, habs]
    linarith [hηφ j x]
  have hζ0 : ∀ j x, x ∉ V → (ζ j : DifferentialForm (Eucl P) k) x = 0 := fun j x hx => by
    rw [hζx, image_eq_zero_of_notMem_tsupport fun h => hx (hηV j h), smul_zero]
  -- Steps 5–6: dominated convergence on `μ ⌞ A`, with the integrable bound `1_{closure V}`
  -- (`μ (closure V) < ∞`), gives `S (ζ j) → ∫_A ⟨φ, v⟩ dμ`.
  have hlim : Tendsto (fun j => S (ζ j)) atTop (𝓝 (∫ x in A, v x (φ x) ∂μ)) := by
    simp only [hS]
    refine tendsto_integral_of_dominated_convergence
      (F := fun j x => v x ((ζ j : DifferentialForm (Eucl P) k) x)) (f := fun x => v x (φ x))
      ((closure V).indicator fun _ => (1 : ℝ))
      (fun j => (hint (ζ j)).aestronglyMeasurable.restrict)
      ((integrable_indicator_iff isClosed_closure.measurableSet).mpr
        (integrableOn_const ((Measure.restrict_apply_le A (closure V)).trans_lt hμK).ne))
      (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ V
      · rw [indicator_of_mem (subset_closure hx), Real.norm_eq_abs]
        exact (hv x _).trans ((hadm j).2 x)
      · rw [hζ0 j x hx, map_zero, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) x
    · have h2δ : Tendsto (fun j => 2 * δ j) atTop (𝓝 0) := by
        simpa using hδlim.const_mul 2
      have h0 : Tendsto (fun j => v x ((ζ j : DifferentialForm (Eucl P) k) x) - v x (φ x))
          atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun j => ?_) h2δ
        rw [← map_sub, Real.norm_eq_abs]
        exact (hv x _).trans (hclose j x)
      simpa using h0.add_const (v x (φ x))
  -- Step 7: pass to the limit in `ofReal (S (ζ j)) ≤ M_W(S)`.
  exact le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun j => S.le_massOn (hadm j)
/-- Extension by zero from `↥U` to `ℝ^P` transfers a locally bounded functional `L` on
`CF_N(U)` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`, with `L f = L' (f ∘ ι)`
for every `f ∈ CF_N(U)`. -/
theorem Submission.smr_rb_transfer_functional :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ,
      (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        L (f + g) = L f + L g) →
      (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → L (c • f) = c * L f) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K →
          (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) →
      ∃ L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ,
        (∀ K : Set ↥U, IsCompact K → ∃ B : ℝ,
          ∀ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)),
            (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L' g ≤ B) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U →
          ∃ g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)),
            (∀ y : ↥U, g y = f ↑y) ∧ L f = L' g := by
  intro P N U hU L hadd hsmul hbd
  -- The zero extension `E g = Function.extend Subtype.val g 0` of `g ∈ C_c(↥U, ℝ^N)`.
  set E : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →
      Eucl P → EuclideanSpace ℝ (Fin N) := fun g => Function.extend Subtype.val (⇑g) 0
  have hEval : ∀ g x (hx : x ∈ U), E g x = g ⟨x, hx⟩ := fun g x hx =>
    Subtype.val_injective.extend_apply (⇑g) 0 ⟨x, hx⟩
  have hEout : ∀ g x, x ∉ U → E g x = 0 := fun g x hx =>
    Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)
  -- `E g ∈ CF_N(U)`, with `tsupport (E g) ⊆ ι(tsupport g)`; continuity uses that `U` is open.
  have hEsupp : ∀ g, tsupport (E g) ⊆ Subtype.val '' tsupport g := fun g =>
    g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val
  have hEU : ∀ g, tsupport (E g) ⊆ U := fun g =>
    (hEsupp g).trans (Subtype.coe_image_subset _ _)
  have hEcpt : ∀ g, HasCompactSupport (E g) := fun g =>
    g.hasCompactSupport.extend_zero continuous_subtype_val
  have hEcont : ∀ g, Continuous (E g) := fun g =>
    HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport
  -- The extension is linear.
  have hEadd : ∀ g h, E (g + h) = E g + E h := by
    intro g h; funext x
    by_cases hx : x ∈ U
    · simp only [Pi.add_apply, hEval _ x hx, CompactlySupportedContinuousMap.add_apply]
    · simp only [Pi.add_apply, hEout _ x hx, add_zero]
  have hEsmul : ∀ (c : ℝ) g, E (c • g) = c • E g := by
    intro c g; funext x
    by_cases hx : x ∈ U
    · simp only [Pi.smul_apply, hEval _ x hx, CompactlySupportedContinuousMap.smul_apply]
    · simp only [Pi.smul_apply, hEout _ x hx, smul_zero]
  -- `L' g = L (E g)` is linear by the additivity and homogeneity of `L` on `CF_N(U)`.
  let L' : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ :=
    { toFun := fun g => L (E g)
      map_add' := fun g h => by
        show L (E (g + h)) = L (E g) + L (E h)
        rw [hEadd]
        exact hadd _ _ (hEcont g) (hEcpt g) (hEU g) (hEcont h) (hEcpt h) (hEU h)
      map_smul' := fun c g => by
        show L (E (c • g)) = c * L (E g)
        rw [hEsmul]
        exact hsmul c _ (hEcont g) (hEcpt g) (hEU g) }
  refine ⟨L', fun K hK => ?_, fun f hf hfc hfU => ?_⟩
  · -- The bound for the compact set `ι(K) ⊆ U` serves for `L'` on `K`.
    obtain ⟨B, hB⟩ := hbd (Subtype.val '' K) (hK.image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)
    refine ⟨B, fun g hg hgK => hB (E g) (hEcont g) ((hEsupp g).trans (image_mono hgK)) fun x => ?_⟩
    by_cases hx : x ∈ U
    · rw [hEval g x hx]; exact hg _
    · rw [hEout g x hx, norm_zero]; exact zero_le_one
  · -- `g = f ∘ ι` vanishes off the compact set `ι⁻¹(tsupport f)`, and `E g = f`.
    have hcpt : HasCompactSupport (f ∘ Subtype.val : ↥U → EuclideanSpace ℝ (Fin N)) := by
      refine HasCompactSupport.intro (K := Subtype.val ⁻¹' tsupport f) ?_ fun y hy => ?_
      · exact (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (hfU.trans Subtype.range_coe.symm.subset)).2 hfc
      · exact image_eq_zero_of_notMem_tsupport (f := f) hy
    let g : CompactlySupportedContinuousMap ↥U (EuclideanSpace ℝ (Fin N)) :=
      ⟨⟨f ∘ Subtype.val, hf.comp continuous_subtype_val⟩, hcpt⟩
    refine ⟨g, fun y => rfl, ?_⟩
    show L f = L (E g)
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hEval g x hx]; rfl
    · rw [hEout g x hx]
      exact image_eq_zero_of_notMem_tsupport fun h => hx (hfU h)
/-- Riesz representation (Simon Ch. 1, 4.14) with Borel data on a σ-compact locally compact
Hausdorff space: a locally bounded functional on `C_c(Y, ℝ^N)` is `g ↦ ∫ ⟨g, ν⟩ dm` for a
measure `m` finite on compacts and a Borel field `ν` with `‖ν‖ ≤ 1`, `‖ν‖ = 1` `m`-a.e. -/
theorem Submission.smr_rb_borel_riesz_sigma_compact : ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (N : ℕ) (L : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ), (∀ K : Set Y, IsCompact K → ∃ B : ℝ, ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), (∀ y, ‖g y‖ ≤ 1) → tsupport g ⊆ K → L g ≤ B) → ∃ (m : Measure Y) (ν : Y → EuclideanSpace ℝ (Fin N)), (∀ K : Set Y, IsCompact K → m K < ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ ≤ 1) ∧ (∀ᵐ y ∂m, ‖ν y‖ = 1) ∧ ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)), L g = ∫ y, inner ℝ (g y) (ν y) ∂m := by
  intro Y _ _ _ _ _ _ N L hL
  -- Step 1: a functional on `C_c(Y, ℝ)` bounded above on each order interval `[0, f]` is
  -- dominated on nonnegative functions by a positive functional (its positive part).
  have key : ∀ ℓ : CompactlySupportedContinuousMap Y ℝ →ₗ[ℝ] ℝ,
      (∀ f : CompactlySupportedContinuousMap Y ℝ≥0, ∃ B : ℝ,
        ∀ φ : CompactlySupportedContinuousMap Y ℝ≥0, φ ≤ f → ℓ φ.toReal ≤ B) →
      ∃ Λ : CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ,
        ∀ f : CompactlySupportedContinuousMap Y ℝ, 0 ≤ f → ℓ f ≤ Λ f := by
    intro ℓ hB
    -- `S f = sup {ℓ φ : φ ≤ f}`, the positive part of `ℓ` on nonnegative functions
    let S : CompactlySupportedContinuousMap Y ℝ≥0 → ℝ := fun f =>
      sSup ((fun φ : CompactlySupportedContinuousMap Y ℝ≥0 => ℓ φ.toReal) '' Set.Iic f)
    have hzero : (0 : CompactlySupportedContinuousMap Y ℝ≥0).toReal = 0 := by ext; simp
    have hle : ∀ f φ, φ ≤ f → ℓ φ.toReal ≤ S f := by
      intro f φ hφ
      obtain ⟨B, hB⟩ := hB f
      exact le_csSup ⟨B, by rintro _ ⟨ψ, hψ, rfl⟩; exact hB ψ hψ⟩ ⟨φ, hφ, rfl⟩
    have hsup : ∀ f c, (∀ φ, φ ≤ f → ℓ φ.toReal ≤ c) → S f ≤ c := by
      intro f c h
      exact csSup_le ⟨_, 0, fun y => zero_le, rfl⟩ (by rintro _ ⟨φ, hφ, rfl⟩; exact h φ hφ)
    have hS0 : ∀ f, 0 ≤ S f := fun f => by
      simpa [hzero] using hle f 0 (fun y => zero_le)
    have hadd : ∀ f g, S (f + g) = S f + S g := by
      intro f g
      refine le_antisymm (hsup _ _ fun φ hφ => ?_) ?_
      · obtain ⟨φ₂, hφ₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le
          (inf_le_left : φ ⊓ f ≤ φ)
        have h2 : φ₂ ≤ g := by
          intro y
          have e := DFunLike.congr_fun hφ₂ y
          have hy := hφ y
          simp only [CompactlySupportedContinuousMap.add_apply,
            CompactlySupportedContinuousMap.inf_apply] at e hy
          rcases le_total (φ y) (f y) with h | h
          · rw [inf_eq_left.2 h] at e
            have : φ₂ y = 0 := by simpa using e
            rw [this]; exact zero_le
          · rw [inf_eq_right.2 h] at e
            rw [← e] at hy
            exact le_of_add_le_add_left hy
        calc ℓ φ.toReal = ℓ (φ ⊓ f).toReal + ℓ φ₂.toReal := by
              rw [← map_add, ← CompactlySupportedContinuousMap.toReal_add, hφ₂]
          _ ≤ S f + S g := add_le_add (hle _ _ inf_le_right) (hle _ _ h2)
      · have h1 : ∀ φ, φ ≤ f → ℓ φ.toReal + S g ≤ S (f + g) := by
          intro φ hφ
          have := hsup g (S (f + g) - ℓ φ.toReal) fun ψ hψ => by
            have := hle (f + g) (φ + ψ) fun y => add_le_add (hφ y) (hψ y)
            rw [CompactlySupportedContinuousMap.toReal_add, map_add] at this
            linarith
          linarith
        have := hsup f (S (f + g) - S g) fun φ hφ => by linarith [h1 φ hφ]
        linarith
    have hsmul_le : ∀ (c : ℝ≥0) f, S (c • f) ≤ c * S f := by
      intro c f
      rcases eq_or_ne c 0 with rfl | hc
      · refine hsup _ _ fun φ hφ => ?_
        have : φ = 0 := by
          ext y
          have := hφ y
          simp only [zero_smul, CompactlySupportedContinuousMap.zero_apply] at this
          simpa using le_antisymm this zero_le
        simp [this, hzero]
      · refine hsup _ _ fun φ hφ => ?_
        have h1 : c⁻¹ • φ ≤ f := by
          intro y
          have := hφ y
          simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul] at this ⊢
          rwa [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)]
        have h2 : c • (c⁻¹ • φ) = φ := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        calc ℓ φ.toReal = c * ℓ (c⁻¹ • φ).toReal := by
              conv_lhs => rw [← h2]
              rw [CompactlySupportedContinuousMap.toReal_smul, NNReal.smul_def, map_smul,
                smul_eq_mul]
          _ ≤ c * S f := mul_le_mul_of_nonneg_left (hle _ _ h1) c.2
    have hsmul : ∀ (c : ℝ≥0) f, S (c • f) = c * S f := by
      intro c f
      refine le_antisymm (hsmul_le c f) ?_
      rcases eq_or_ne c 0 with rfl | hc
      · rw [NNReal.coe_zero, zero_mul]; exact hS0 _
      · have := hsmul_le c⁻¹ (c • f)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        calc (c : ℝ) * S f ≤ c * (c⁻¹ * S (c • f)) := mul_le_mul_of_nonneg_left this c.2
          _ = S (c • f) := by
            rw [← mul_assoc, ← NNReal.coe_mul, mul_inv_cancel₀ hc, NNReal.coe_one, one_mul]
    let Λ₀ : CompactlySupportedContinuousMap Y ℝ≥0 →ₗ[ℝ≥0] ℝ≥0 :=
      { toFun := fun f => Real.toNNReal (S f)
        map_add' := fun f g => by rw [hadd, Real.toNNReal_add (hS0 f) (hS0 g)]
        map_smul' := fun c f => by
          rw [hsmul, Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe, RingHom.id_apply, smul_eq_mul] }
    refine ⟨CompactlySupportedContinuousMap.toRealPositiveLinear Λ₀, fun f hf => ?_⟩
    have hf' : f.nnrealPart.toReal = f := by
      ext y
      have hfy : 0 ≤ f y := by simpa using hf y
      simp [hfy]
    rw [← hf', CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
    exact (hle _ _ le_rfl).trans (Real.le_coe_toNNReal _)
  -- Step 2: the coordinate functionals `ψ ↦ L(ψ bᵢ)` for the standard orthonormal basis `b`.
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  let mk : CompactlySupportedContinuousMap Y ℝ → EuclideanSpace ℝ (Fin N) →
      CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)) := fun ψ v =>
    ψ.compLeft ⟨fun t => t • v, continuous_id.smul continuous_const⟩
  have mk_apply : ∀ ψ v y, mk ψ v y = ψ y • v := fun ψ v y =>
    CompactlySupportedContinuousMap.compLeft_apply (by simp) ψ y
  let ℓ : EuclideanSpace ℝ (Fin N) → CompactlySupportedContinuousMap Y ℝ →ₗ[ℝ] ℝ := fun v =>
    { toFun := fun ψ => L (mk ψ v)
      map_add' := fun ψ φ => by
        rw [← map_add]
        congr 1
        exact CompactlySupportedContinuousMap.ext fun y => by simp [mk_apply, add_smul]
      map_smul' := fun c ψ => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        exact CompactlySupportedContinuousMap.ext fun y => by simp [mk_apply, smul_smul] }
  have hbound : ∀ i, ∀ f : CompactlySupportedContinuousMap Y ℝ≥0, ∃ B : ℝ,
      ∀ φ : CompactlySupportedContinuousMap Y ℝ≥0, φ ≤ f → ℓ (b i) φ.toReal ≤ B := by
    intro i f
    obtain ⟨B, hB⟩ := hL (tsupport f) f.hasCompactSupport
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖f.toReal y‖ ≤ C :=
      (map_continuous f.toReal).bounded_above_of_compact_support f.toReal.hasCompactSupport
    have hc : 0 < |C| + 1 := by positivity
    refine ⟨(|C| + 1) * B, fun φ hφ => ?_⟩
    have hφf : ∀ y, (φ y : ℝ) ≤ |C| + 1 := fun y => by
      have h1 : (φ y : ℝ) ≤ f y := NNReal.coe_le_coe.2 (hφ y)
      have h2 := hC y
      rw [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs] at h2
      linarith [le_abs_self C, le_abs_self (f y : ℝ)]
    have hnorm : ∀ y, ‖mk ((|C| + 1)⁻¹ • φ.toReal) (b i) y‖ ≤ 1 := fun y => by
      rw [mk_apply, norm_smul, hb, mul_one, CompactlySupportedContinuousMap.smul_apply,
        CompactlySupportedContinuousMap.toReal_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      rw [inv_mul_le_iff₀ hc, mul_one]
      exact hφf y
    have hsupp : tsupport (mk ((|C| + 1)⁻¹ • φ.toReal) (b i)) ⊆ tsupport f := by
      refine closure_mono fun y hy => ?_
      rw [Function.mem_support] at hy ⊢
      contrapose! hy
      have : φ y = 0 := le_antisymm ((hφ y).trans hy.le) zero_le
      simp [mk_apply, this]
    have h := hB _ hnorm hsupp
    change ℓ (b i) ((|C| + 1)⁻¹ • φ.toReal) ≤ B at h
    rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hc] at h
    exact h
  -- Step 3: Jordan decomposition `ℓᵢ = Λᵢ - Qᵢ` and the Riesz–Markov–Kakutani measures.
  choose Λ hΛ using fun i => key (ℓ (b i)) (hbound i)
  let Q : Fin N → CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ := fun i =>
    PositiveLinearMap.mk₀ ((Λ i).toLinearMap - ℓ (b i)) fun f hf => by
      simpa using hΛ i f hf
  have hℓ : ∀ i ψ, ℓ (b i) ψ =
      ∫ y, ψ y ∂(RealRMK.rieszMeasure (Λ i)) - ∫ y, ψ y ∂(RealRMK.rieszMeasure (Q i)) := by
    intro i ψ
    rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    change _ = _ - ((Λ i) ψ - ℓ (b i) ψ)
    ring
  -- Step 4: the reference measure `μ₀ = ∑ᵢ (μ_{Λᵢ} + μ_{Qᵢ})` and Radon–Nikodym transfer.
  let μ₀ : Measure Y := ∑ i, (RealRMK.rieszMeasure (Λ i) + RealRMK.rieszMeasure (Q i))
  have hμ₀ : ∀ s, μ₀ s = ∑ i, (RealRMK.rieszMeasure (Λ i) s + RealRMK.rieszMeasure (Q i) s) := by
    intro s
    simp only [μ₀, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_add, Pi.add_apply]
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨fun K hK => by
    rw [hμ₀]
    exact ENNReal.sum_lt_top.2 fun i _ =>
      ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  have hPle : ∀ i, RealRMK.rieszMeasure (Λ i) ≤ μ₀ := fun i => Measure.le_iff'.2 fun s => by
    rw [hμ₀]
    exact le_self_add.trans (Finset.single_le_sum
      (f := fun j => RealRMK.rieszMeasure (Λ j) s + RealRMK.rieszMeasure (Q j) s)
      (fun j _ => zero_le) (Finset.mem_univ i))
  have hQle : ∀ i, RealRMK.rieszMeasure (Q i) ≤ μ₀ := fun i => Measure.le_iff'.2 fun s => by
    rw [hμ₀]
    exact le_add_self.trans (Finset.single_le_sum
      (f := fun j => RealRMK.rieszMeasure (Λ j) s + RealRMK.rieszMeasure (Q j) s)
      (fun j _ => zero_le) (Finset.mem_univ i))
  have transfer : ∀ (μ' : Measure Y) [IsFiniteMeasureOnCompacts μ'], μ' ≤ μ₀ →
      ∀ ψ : CompactlySupportedContinuousMap Y ℝ,
        Integrable (fun y => (μ'.rnDeriv μ₀ y).toReal • ψ y) μ₀ ∧
        ∫ y, ψ y ∂μ' = ∫ y, (μ'.rnDeriv μ₀ y).toReal • ψ y ∂μ₀ := by
    intro μ' _ hle ψ
    have hwd : μ₀.withDensity (μ'.rnDeriv μ₀) = μ' := by
      have h := Measure.rnDeriv_add_singularPart μ' μ₀
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        add_zero] at h
    have hint : Integrable ψ (μ₀.withDensity (μ'.rnDeriv μ₀)) := by
      rw [hwd]
      exact (map_continuous ψ).integrable_of_hasCompactSupport ψ.hasCompactSupport
    refine ⟨(integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)).1 hint, ?_⟩
    calc ∫ y, ψ y ∂μ' = ∫ y, ψ y ∂(μ₀.withDensity (μ'.rnDeriv μ₀)) := by rw [hwd]
      _ = _ := integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
          (Measure.rnDeriv_lt_top _ _) _
  -- the vector density `w = ∑ᵢ (dμ_{Λᵢ}/dμ₀ - dμ_{Qᵢ}/dμ₀) bᵢ`
  let a : Fin N → Y → ℝ := fun i y => ((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal -
    ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal
  let w : Y → EuclideanSpace ℝ (Fin N) := fun y => ∑ i, a i y • b i
  have hw : Measurable w := Finset.measurable_sum _ fun i _ =>
    ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sub
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).smul_const _
  -- Step 5: `L g = ∫ ⟨g, w⟩ dμ₀`.
  have hrep : ∀ g : CompactlySupportedContinuousMap Y (EuclideanSpace ℝ (Fin N)),
      L g = ∫ y, inner ℝ (g y) (w y) ∂μ₀ := by
    intro g
    let gc : Fin N → CompactlySupportedContinuousMap Y ℝ := fun i =>
      g.compLeft ⟨fun v => inner ℝ (b i) v, continuous_const.inner continuous_id⟩
    have gc_apply : ∀ i y, gc i y = inner ℝ (b i) (g y) := fun i y =>
      CompactlySupportedContinuousMap.compLeft_apply (by simp) g y
    have hg : g = ∑ i, mk (gc i) (b i) := by
      refine CompactlySupportedContinuousMap.ext fun y => ?_
      rw [CompactlySupportedContinuousMap.sum_apply]
      simp only [mk_apply, gc_apply]
      exact (b.sum_repr' (g y)).symm
    have hP := fun i => transfer _ (hPle i) (gc i)
    have hQ := fun i => transfer _ (hQle i) (gc i)
    calc L g = ∑ i, ℓ (b i) (gc i) := by
          conv_lhs => rw [hg]
          rw [map_sum]
          rfl
      _ = ∑ i, ∫ y, (((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal • gc i y -
            ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal • gc i y) ∂μ₀ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hℓ, (hP i).2, (hQ i).2, integral_sub (hP i).1 (hQ i).1]
      _ = ∫ y, ∑ i, (((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y).toReal • gc i y -
            ((RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y).toReal • gc i y) ∂μ₀ :=
          (integral_finsetSum _ fun i _ => (hP i).1.sub (hQ i).1).symm
      _ = ∫ y, inner ℝ (g y) (w y) ∂μ₀ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [w, a, inner_sum, real_inner_smul_right, gc_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [real_inner_comm]
          ring
  -- Step 6: polar normalization `m = ‖w‖ μ₀`, `ν = ‖w‖⁻¹ w`.
  have hbe : ∀ i, ‖b i‖ₑ = 1 := fun i => by
    rw [← ofReal_norm, hb i, ENNReal.ofReal_one]
  refine ⟨μ₀.withDensity fun y => ‖w y‖ₑ, fun y => ‖w y‖⁻¹ • w y, fun K hK => ?_,
    hw.norm.inv.smul hw, fun y => ?_, ?_, fun g => ?_⟩
  · calc (μ₀.withDensity fun y => ‖w y‖ₑ) K = ∫⁻ y in K, ‖w y‖ₑ ∂μ₀ :=
          withDensity_apply _ hK.isClosed.measurableSet
      _ ≤ ∫⁻ y in K, ∑ i, ((RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y +
            (RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y) ∂μ₀ := by
          refine lintegral_mono fun y =>
            (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [enorm_smul, hbe i, mul_one]
          refine enorm_sub_le.trans (add_le_add ?_ ?_) <;>
            rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg] <;> exact ENNReal.ofReal_toReal_le
      _ = ∑ i, (∫⁻ y in K, (RealRMK.rieszMeasure (Λ i)).rnDeriv μ₀ y ∂μ₀ +
            ∫⁻ y in K, (RealRMK.rieszMeasure (Q i)).rnDeriv μ₀ y ∂μ₀) := by
          rw [lintegral_finsetSum']
          · exact Finset.sum_congr rfl fun i _ =>
              lintegral_add_left (Measure.measurable_rnDeriv _ _) _
          · exact fun i _ => ((Measure.measurable_rnDeriv _ _).add
              (Measure.measurable_rnDeriv _ _)).aemeasurable
      _ < ∞ := ENNReal.sum_lt_top.2 fun i _ => ENNReal.add_lt_top.2
          ⟨((withDensity_apply_le _ _).trans (Measure.le_iff'.1
              (Measure.withDensity_rnDeriv_le _ _) K)).trans_lt hK.measure_lt_top,
            ((withDensity_apply_le _ _).trans (Measure.le_iff'.1
              (Measure.withDensity_rnDeriv_le _ _) K)).trans_lt hK.measure_lt_top⟩
  · show ‖‖w y‖⁻¹ • w y‖ ≤ 1
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖w y‖ 0 with h | h
    · rw [h, inv_zero, zero_mul]
      exact zero_le_one
    · rw [inv_mul_cancel₀ h]
  · refine (ae_withDensity_iff hw.enorm).2 (ae_of_all _ fun y hy => ?_)
    show ‖‖w y‖⁻¹ • w y‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (enorm_ne_zero.1 hy))]
  · rw [hrep g, integral_withDensity_eq_integral_toReal_smul hw.enorm
      (ae_of_all _ fun y => enorm_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show inner ℝ (g y) (w y) = (‖w y‖ₑ).toReal • inner ℝ (g y) (‖w y‖⁻¹ • w y)
    rw [toReal_enorm, smul_eq_mul, real_inner_smul_right]
    rcases eq_or_ne ‖w y‖ 0 with h | h
    · rw [norm_eq_zero.1 h, inner_zero_right, mul_zero, mul_zero]
    · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]
/-- Push-forward of Borel representing data from the open subspace `↥U` to `ℝ^P`: `μ = m.map ι`
and the zero extension `ν` of `ν₁` represent the same integrals against every `f ∈ CF_N(U)`. -/
theorem Submission.smr_rb_pushforward_subtype :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U →
      ∀ (m : Measure ↥U) (ν₁ : ↥U → EuclideanSpace ℝ (Fin N)),
      (∀ K : Set ↥U, IsCompact K → m K < ∞) → Measurable ν₁ → (∀ y, ‖ν₁ y‖ ≤ 1) →
      (∀ᵐ y ∂m, ‖ν₁ y‖ = 1) →
      ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U → Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧
            ∫ x, inner ℝ (f x) (ν x) ∂μ = ∫ y, inner ℝ (f ↑y) (ν₁ y) ∂m := by
  intro P N U hU m ν₁ hm hν₁ hle hae
  -- `ι = Subtype.val : ↥U → ℝ^P` is a measurable embedding since `U` is open.
  have hι : MeasurableEmbedding (Subtype.val : ↥U → Eucl P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  -- The zero extension `ν = Function.extend Subtype.val ν₁ 0` of `ν₁`.
  set ν : Eucl P → EuclideanSpace ℝ (Fin N) := Function.extend Subtype.val ν₁ 0
  have hνval : ∀ y : ↥U, ν y = ν₁ y := fun y => Subtype.val_injective.extend_apply ν₁ 0 y
  have hνout : ∀ x, x ∉ U → ν x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)
  have hνm : Measurable ν := hι.measurable_extend hν₁ measurable_zero
  have hνle : ∀ x, ‖ν x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ U
    · rw [← Subtype.coe_mk x hx, hνval]; exact hle _
    · rw [hνout x hx, norm_zero]; exact zero_le_one
  -- Compact subsets of `U` have finite `m.map ι`-measure.
  have hfin : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → m.map Subtype.val K < ∞ := by
    intro K hK hKU
    rw [hι.map_apply]
    exact hm _ ((Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (hKU.trans Subtype.range_coe.symm.subset)).2 hK)
  refine ⟨m.map Subtype.val, ν, hνm, ?_, hfin, hνle, ?_, fun f hf hfc hfU => ⟨?_, ?_⟩⟩
  · rw [hι.map_apply, Subtype.preimage_coe_compl, measure_empty]
  · exact hι.ae_map_iff.2 (hae.mono fun y hy => by rw [hνval]; exact hy)
  · -- `⟨f, ν⟩` is measurable, bounded, and vanishes off the compact `tsupport f ⊆ U`.
    have hFm : Measurable fun x => inner ℝ (f x) (ν x) :=
      continuous_inner.measurable.comp (hf.measurable.prodMk hνm)
    obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
    have hsupp : Function.support (fun x => inner ℝ (f x) (ν x)) ⊆ tsupport f := by
      intro x hx
      by_contra h
      exact hx (by simp only [image_eq_zero_of_notMem_tsupport h, inner_zero_left])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1
      (Measure.integrableOn_of_bounded (hfin _ hfc hfU).ne hFm.aestronglyMeasurable
        (M := C) (ae_of_all _ fun x => ?_))
    calc ‖inner ℝ (f x) (ν x)‖ ≤ ‖f x‖ * ‖ν x‖ := norm_inner_le_norm _ _
      _ ≤ ‖f x‖ := mul_le_of_le_one_right (norm_nonneg _) (hνle x)
      _ ≤ C := hC x
  · -- Change of variables along the measurable embedding `ι`.
    rw [hι.integral_map]
    simp only [hνval]

/-- Riesz representation (Simon Ch. 1, 4.14) for a locally bounded functional `L` on
`CF_N(U) = {f ∈ C_c(ℝ^P, ℝ^N) : tsupport f ⊆ U}`, `U ⊆ ℝ^P` open: there are a Borel measure `μ`
on `ℝ^P` living on `U`, finite on compact subsets of `U`, and a Borel field `ν` with `‖ν‖ ≤ 1`
and `‖ν‖ = 1` `μ`-a.e., such that `L f = ∫ ⟨f, ν⟩ dμ` for every `f ∈ CF_N(U)`. -/
theorem Submission.smr_riesz_borel_euclidean :
    ∀ (P N : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → EuclideanSpace ℝ (Fin N)) → ℝ,
      (∀ f g : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U →
        L (f + g) = L f + L g) →
      (∀ (c : ℝ) (f : Eucl P → EuclideanSpace ℝ (Fin N)), Continuous f → HasCompactSupport f →
        tsupport f ⊆ U → L (c • f) = c * L f) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ,
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → tsupport f ⊆ K →
          (∀ x, ‖f x‖ ≤ 1) → L f ≤ B) →
      ∃ (μ : Measure (Eucl P)) (ν : Eucl P → EuclideanSpace ℝ (Fin N)), Measurable ν ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ x, ‖ν x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
        ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f → HasCompactSupport f →
          tsupport f ⊆ U →
          Integrable (fun x => inner ℝ (f x) (ν x)) μ ∧
            L f = ∫ x, inner ℝ (f x) (ν x) ∂μ := by
  intro P N U hU L hadd hsmul hbd
  -- Transfer `L` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`.
  obtain ⟨L', hL'bd, hL'f⟩ := Submission.smr_rb_transfer_functional P N U hU L hadd hsmul hbd
  -- `↥U` is locally compact (`U` is open), hence σ-compact (second countable); it carries the
  -- subspace Borel σ-algebra.
  have : LocallyCompactSpace ↥U := hU.locallyCompactSpace
  -- Borel Riesz representation of `L'` on `↥U`.
  obtain ⟨m, ν₁, hmK, hν₁, hν₁le, hν₁ae, hrep⟩ :=
    Submission.smr_rb_borel_riesz_sigma_compact ↥U N L' hL'bd
  -- Push the data forward to `ℝ^P`, extending `ν₁` by zero.
  obtain ⟨μ, ν, hν, hμU, hμK, hνle, hνae, hpush⟩ :=
    Submission.smr_rb_pushforward_subtype P N U hU m ν₁ hmK hν₁ hν₁le hν₁ae
  refine ⟨μ, ν, hν, hμU, hμK, hνle, hνae, fun f hf hfc hfU => ?_⟩
  obtain ⟨hint, hμm⟩ := hpush f hf hfc hfU
  obtain ⟨g, hg, hLg⟩ := hL'f f hf hfc hfU
  -- `L f = L' g = ∫ ⟨g, ν₁⟩ dm = ∫ ⟨f ∘ ι, ν₁⟩ dm = ∫ ⟨f, ν⟩ dμ`.
  refine ⟨hint, ?_⟩
  rw [hLg, hrep g, hμm]
  simp only [hg]

/-- Riesz representation of a locally bounded linear functional `L` on the continuous compactly
supported `k`-forms in `U` (Simon Ch. 6, 2.7, from Ch. 1, 4.14): `L(φ) = ∫ ⟨φ, v⟩ dμ` with
`|v(x)(α)| ≤ |α|` and, `μ`-a.e., `v(x)(α) = 1` for some `|α| ≤ 1`.  The isometry
`J : Λᵏ(ℝ^P) ≅ ℝ^N` of `Submission.smr_covector_coord_isometry` (continuous in finite dimension)
transfers `L` to `L_H(f) = L(J⁻¹ ∘ f)` on `ℝ^N`-valued functions;
`Submission.smr_riesz_borel_euclidean` gives `L_H(f) = ∫ ⟨f, ν⟩ dμ` with Borel `ν`, `‖ν‖ ≤ 1`
and `‖ν‖ = 1` `μ`-a.e.; and `v(x)(α) = ⟨ν(x), Jα⟩`, with unit witness `α = J⁻¹(ν(x))`. -/
theorem Submission.smr_riesz_continuous_forms :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → Covector (Eucl P) k) → ℝ,
      (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
          L (φ + ψ) = L φ + L ψ) →
      (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ →
        tsupport φ ⊆ U → L (c • φ) = c * L φ) →
      (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ, ∀ φ : Eucl P → Covector (Eucl P) k,
        Continuous φ → tsupport φ ⊆ K → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → |L φ| ≤ B) →
      ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
        (∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ →
          tsupport φ ⊆ U → Integrable (fun x => v x (φ x)) μ ∧ L φ = ∫ x, v x (φ x) ∂μ) ∧
        μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) ∧
        (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) ∧
        ∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1 := by
  intro P k U hU L hadd hsmul hbd
  -- Step 1: the coordinate isometry `J`; covectors are finite-dimensional, so `J` and `J⁻¹`
  -- are continuous, and `|J⁻¹ h| = ‖h‖`.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  have : FiniteDimensional ℝ (Covector (Eucl P) k) := J.symm.finiteDimensional
  let Jc : Covector (Eucl P) k ≃L[ℝ] EuclideanSpace ℝ (Fin N) := J.toContinuousLinearEquiv
  have hJsymm : ∀ h, covectorEuclideanNorm (J.symm h) = ‖h‖ := fun h => by
    rw [hJ, J.apply_symm_apply]
  -- Step 2: `f ↦ J⁻¹ ∘ f` maps `CF_N(U)` into `CF(U)`, so `L_H(f) = L(J⁻¹ ∘ f)` is additive,
  -- homogeneous and bounded above by the bound `B` of `L` on each compact `K ⊆ U`.
  have hcont : ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), Continuous f →
      Continuous (fun x => J.symm (f x)) := fun f hf => Jc.symm.continuous.comp hf
  have hcpt : ∀ f : Eucl P → EuclideanSpace ℝ (Fin N), HasCompactSupport f →
      HasCompactSupport (fun x => J.symm (f x)) := fun f hf => hf.comp_left (map_zero J.symm)
  have htsupp : ∀ f : Eucl P → EuclideanSpace ℝ (Fin N),
      tsupport (fun x => J.symm (f x)) ⊆ tsupport f := fun f =>
    tsupport_comp_subset (map_zero J.symm) f
  -- Step 3: Riesz for `L_H`.
  obtain ⟨μ, ν, hν, hμU, hμK, hνle, hνone, hrep⟩ :=
    Submission.smr_riesz_borel_euclidean P N U hU (fun f => L (fun x => J.symm (f x)))
      (by
        intro f g hf hfc hfU hg hgc hgU
        have hfg : (fun x => J.symm ((f + g) x)) =
            (fun x => J.symm (f x)) + (fun x => J.symm (g x)) := by
          funext x
          simp
        rw [hfg]
        exact hadd _ _ (hcont f hf) (hcpt f hfc) ((htsupp f).trans hfU)
          (hcont g hg) (hcpt g hgc) ((htsupp g).trans hgU))
      (by
        intro c f hf hfc hfU
        have hcf : (fun x => J.symm ((c • f) x)) = c • (fun x => J.symm (f x)) := by
          funext x
          simp
        rw [hcf]
        exact hsmul c _ (hcont f hf) (hcpt f hfc) ((htsupp f).trans hfU))
      (by
        intro K hK hKU
        obtain ⟨B, hB⟩ := hbd K hK hKU
        refine ⟨B, fun f hf hfK hf1 => ?_⟩
        exact (le_abs_self _).trans (hB _ (hcont f hf) ((htsupp f).trans hfK)
          (fun x => (hJsymm (f x)).le.trans (hf1 x))))
  -- Step 4: the `k`-vector field `v(x)(α) = ⟨ν(x), Jα⟩`.
  let v : Eucl P → NVector (Eucl P) k := fun x =>
    (innerSL ℝ (ν x)).comp (Jc : Covector (Eucl P) k →L[ℝ] EuclideanSpace ℝ (Fin N))
  have hv : ∀ x α, v x α = inner ℝ (ν x) (J α) := fun x α => rfl
  refine ⟨μ, v, ?_, hμU, hμK, ?_, ?_, ?_⟩
  · -- Step 5: representation, via `f = J ∘ φ ∈ CF_N(U)` with `J⁻¹ ∘ f = φ`.
    intro φ hφ hφc hφU
    obtain ⟨hint, hLf⟩ := hrep (fun x => J (φ x)) (Jc.continuous.comp hφ)
      (hφc.comp_left (map_zero J)) ((tsupport_comp_subset (map_zero J) φ).trans hφU)
    have heq : (fun x => inner ℝ (J (φ x)) (ν x)) = fun x => v x (φ x) := by
      funext x
      rw [hv, real_inner_comm]
    have hLφ : (fun x => J.symm (J (φ x))) = φ := by
      funext x
      exact J.symm_apply_apply (φ x)
    rw [heq] at hint hLf
    rw [hLφ] at hLf
    exact ⟨hint, hLf⟩
  · -- (i) Cauchy–Schwarz with `‖ν(x)‖ ≤ 1`: `|v(x)(α)| ≤ ‖Jα‖ = |α|`.
    intro x α
    rw [hv, hJ]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hνle x))
  · -- (ii) `x ↦ ⟨ν(x), Jα⟩` is Borel since `ν` is.
    intro α
    exact ((continuous_id.inner continuous_const).measurable).comp hν
  · -- (iii) Where `‖ν(x)‖ = 1`, `α = J⁻¹(ν(x))` has `|α| = 1` and `v(x)(α) = ‖ν(x)‖² = 1`.
    filter_upwards [hνone] with x hx
    refine ⟨J.symm (ν x), (hJsymm (ν x)).trans_le hx.le, ?_⟩
    rw [hv, J.apply_symm_apply, real_inner_self_eq_norm_sq, hx, one_pow]
/-- **Restriction of a measure representation is a current (Simon Ch. 6, (2.9), p. 136).**  If
`⟨ω, v⟩` is `μ`-integrable for every test form `ω ∈ 𝒟ᵏ(U)`, `μ(K) < ∞` for every compact `K ⊆ U`
and `|⟨α, v(x)⟩| ≤ |α|` for all `x` and all `k`-covectors `α`, then for every set `A`,
`S(ω) = ∫_A ⟨ω, v⟩ dμ` is a current `S ∈ 𝒟ₖ(U)`.  `S` is linear because every integrand is
integrable.  With `M = #(Fin k → Fin P)`, `|α| ≤ √M ‖α‖` for the operator norm; if `ω_j → 0` in
`𝒟ᵏ(U)`, the supports lie in one compact `K ⊆ U` and `ω_j → 0` uniformly on `K`, so
`|S(ω_j)| ≤ √M μ(K) sup_K ‖ω_j‖ → 0`. -/
theorem Submission.smr_restriction_isCurrent : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → ∀ A : Set (Eucl P), ∃ S : GeometricCurrentOn U k, ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ := by
  intro P k U μ v hint hfin hv A
  -- Step 1: `|α| ≤ √M ‖α‖` for the operator norm, `M = #(Fin k → Fin P)`.
  obtain ⟨C, hC0, hcmp⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ C * ‖α‖ := by
    refine ⟨Real.sqrt (Fintype.card (Fin k → Fin P)), Real.sqrt_nonneg _, fun α => ?_⟩
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ ∑ _I : Fin k → Fin P, ‖α‖ ^ 2 := by
          refine Finset.sum_le_sum fun I _ => ?_
          split_ifs
          · -- `|α(b_{I(0)}, …, b_{I(k-1)})| ≤ ‖α‖` since `‖b_i‖ = 1`
            have h := α.le_opNorm fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
            simp only [EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
              Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h ⊢
            exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
          · positivity
      _ = (Fintype.card (Fin k → Fin P) : ℝ) * ‖α‖ ^ 2 := by simp
  -- Step 2: `S₀(ω) = ∫_A ⟨ω, v⟩ dμ` is linear, every integrand being `μ⌞A`-integrable.
  let S₀ : TestFormOn U k →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω).restrict (hint η).restrict
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  refine ⟨⟨S₀, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 3: sequential continuity.  The supports of the `ω_j` lie in a compact `K ⊆ U` and
  -- `ω_j → 0` uniformly on `K` (order `0`), while `μ(K) < ∞`.
  obtain ⟨K, hKc, hKU, hsupp, -, hunif⟩ := hconv
  have hKm : MeasurableSet K := hKc.measurableSet
  have hμK : μ K < ∞ := hfin K hKc hKU
  set c : ℝ := C * μ.real K + 1 with hc
  have hc0 : 0 < c := add_pos_of_nonneg_of_pos (mul_nonneg hC0 measureReal_nonneg) one_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j₀, hj₀⟩ :=
    (Metric.tendstoUniformlyOn_iff.mp (hunif 0) (ε / c) (div_pos hε hc0)).exists_forall_of_atTop
  refine ⟨j₀, fun j hj => ?_⟩
  -- `|⟨ω_j(x), v(x)⟩| ≤ C ε / c` on `K`, and `ω_j(x) = 0` off `K`.
  have hbound : ∀ x, ‖v x ((ωs j : DifferentialForm (Eucl P) k) x)‖ ≤
      K.indicator (fun _ => C * (ε / c)) x := by
    intro x
    by_cases hx : x ∈ K
    · have hd := hj₀ j hj x hx
      have h00 : iteratedFDeriv ℝ 0
          ((0 : TestFormOn U k) : DifferentialForm (Eucl P) k) x = 0 := by
        simp
      rw [h00, dist_zero_left, norm_iteratedFDeriv_zero] at hd
      rw [indicator_of_mem hx, Real.norm_eq_abs]
      calc |v x ((ωs j : DifferentialForm (Eucl P) k) x)|
          ≤ covectorEuclideanNorm ((ωs j : DifferentialForm (Eucl P) k) x) := hv x _
        _ ≤ C * ‖(ωs j : DifferentialForm (Eucl P) k) x‖ := hcmp _
        _ ≤ C * (ε / c) := mul_le_mul_of_nonneg_left hd.le hC0
    · have hz : (ωs j : DifferentialForm (Eucl P) k) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h)
      rw [indicator_of_notMem hx, hz, map_zero, norm_zero]
  have hgi : Integrable (K.indicator fun _ => C * (ε / c)) (μ.restrict A) :=
    (integrable_indicator_iff hKm).mpr
      (integrableOn_const ((Measure.restrict_apply_le A K).trans_lt hμK).ne)
  have hI := norm_integral_le_of_norm_le hgi (Eventually.of_forall hbound)
  rw [integral_indicator_const _ hKm, smul_eq_mul] at hI
  have hAK : (μ.restrict A).real K ≤ μ.real K :=
    ENNReal.toReal_mono hμK.ne (Measure.restrict_apply_le A K)
  rw [dist_zero_right]
  calc ‖S₀ (ωs j)‖ ≤ (μ.restrict A).real K * (C * (ε / c)) := hI
    _ ≤ μ.real K * (C * (ε / c)) :=
        mul_le_mul_of_nonneg_right hAK (mul_nonneg hC0 (div_pos hε hc0).le)
    _ = C * μ.real K * ε / c := by ring
    _ < ε := by
        rw [div_lt_iff₀ hc0, hc]
        nlinarith

/-- Simon Ch. 6, 2.8–2.9 (pp. 136–137), the step `μ(W ∩ A) ≤ M_W(T ⌞ A)` of the mass formula
for a restriction: continuous unit forms supported in an open `W ⊆ U` detect `μ(W ∩ A)`.  Write
`v(x)(α) = ⟨Jα, u(x)⟩` for an isometry `J` of `(Λᵏ, |·|)` onto `ℝ^N`, so `‖u‖ ≤ 1` and `‖u‖ = 1`
`μ`-a.e.  Take a compact Lusin set `C ⊆ W ∩ A ∩ {‖u‖ = 1}` of `u` with `c < μ(C)`, a continuous
extension `w` of `u|C` with `‖w‖ ≤ 1` (Tietze) and a cutoff `ψ ∈ [0, 1]`, `ψ = 1` on `C`, with
`tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c` (Urysohn).  Then `φ = J⁻¹(ψ w)` has `|φ| ≤ 1`,
and `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C` and `0` off `support ψ`, so `∫_A ⟨φ, v⟩ dμ > c`. -/
theorem Submission.smr_exists_unit_form_gt : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) → (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < μ (W ∩ A) → ∃ φ : Eucl P → Covector (Eucl P) k, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ W ∧ (∀ x, covectorEuclideanNorm (φ x) ≤ 1) ∧ c < ENNReal.ofReal (∫ x in A, v x (φ x) ∂μ) := by
  intro P k U μ v hμK hv hvm hunit A hA W hW hWU c hc
  -- Coordinates `u` of `v` in an isometric chart `J`: `v(x)(α) = ⟨Jα, u(x)⟩`, `‖u‖ = 1` a.e.
  obtain ⟨N, J, hJ⟩ := Submission.smr_covector_coord_isometry P k
  obtain ⟨u, hum, hu1, hu_ae, hvu⟩ :=
    Submission.smr_ufd_unit_coord_field P k N μ v J hJ hv hvm hunit
  -- `{‖u‖ = 1}` is conull, so it does not change `μ(W ∩ A)`; take a compact Lusin set `C` of `u`
  -- inside `W ∩ A ∩ {‖u‖ = 1}` with `c < μ(C)`.
  have hWAG : μ (W ∩ (A ∩ {x | ‖u x‖ = 1})) = μ (W ∩ A) := by
    rw [← Set.inter_assoc]
    exact measure_inter_conull (mem_ae_iff.1 hu_ae)
  obtain ⟨C, hCc, hCsub, hcC, huC⟩ := Submission.smr_ufd_compact_lusin_set P N U μ u hμK hum
    (A ∩ {x | ‖u x‖ = 1}) (hA.inter (measurableSet_eq_fun hum.norm measurable_const)) W hW hWU c
    (by rw [hWAG]; exact hc)
  have hCW : C ⊆ W := hCsub.trans Set.inter_subset_left
  -- Tietze: a continuous `w` with `‖w‖ ≤ 1` and `w = u` on `C`.
  obtain ⟨w, hwc, hw1, hwu⟩ :=
    Submission.smr_ufd_ball_tietze P N C u hCc.isClosed huC fun x _ => hu1 x
  -- Urysohn: `ψ ∈ [0, 1]`, `ψ = 1` on `C`, `tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c`.
  obtain ⟨ψ, hψc, hψcs, hψW, hψ01, hψC, hψS⟩ := Submission.smr_ufd_small_cutoff P U μ hμK C W hCc
    hW hCW hWU (μ C - c) (tsub_pos_of_lt hcC).ne'
  have hψw : ∀ x, ‖ψ x • w x‖ ≤ 1 := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (hψ01 x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hψ01 x).2).trans (hw1 x)
  -- The form `φ = J⁻¹(ψ w)`; `J⁻¹` is continuous since `ℝ^N` is finite-dimensional.
  refine ⟨fun x => J.symm (ψ x • w x),
    (LinearMap.continuous_of_finiteDimensional J.symm.toLinearMap).comp (hψc.smul hwc),
    (hψcs.smul_right (f' := w)).comp_left (map_zero J.symm),
    (tsupport_comp_subset (map_zero J.symm) _).trans ((tsupport_smul_subset_left ψ w).trans hψW),
    fun x => ?_, ?_⟩
  · -- `|φ(x)| = ‖ψ(x) w(x)‖ ≤ 1`.
    change covectorEuclideanNorm (J.symm (ψ x • w x)) ≤ 1
    rw [hJ, LinearEquiv.apply_symm_apply]
    exact hψw x
  · -- `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C ⊆ {‖u‖ = 1}` and `0` off `support ψ`.
    have hg : ∀ x, v x (J.symm (ψ x • w x)) = inner ℝ (ψ x • w x) (u x) := fun x => by
      rw [hvu, LinearEquiv.apply_symm_apply]
    simp only [hg]
    refine Submission.smr_ufd_integral_lower_bound P μ (fun x => inner ℝ (ψ x • w x) (u x)) A C
      (Function.support ψ) c hA hCc.isClosed.measurableSet hψc.isOpen_support.measurableSet
      (fun x hx => (hCsub hx).2.1)
      ((measure_mono (subset_tsupport ψ)).trans_lt (hμK (tsupport ψ) hψcs (hψW.trans hWU)))
      ((continuous_inner (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin N))).measurable.comp
        ((hψc.smul hwc).measurable.prodMk hum))
      (fun x => (abs_real_inner_le_norm _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hψw x)).trans (hu1 x)))
      (fun x hx => ?_) (fun x hx => ?_) (lt_tsub_iff_left.1 hψS)
    · have hx1 : ‖u x‖ = 1 := (hCsub hx).2.2
      simp only [hψC x hx, one_smul, hwu x hx, real_inner_self_eq_norm_sq, hx1, one_pow]
    · simp only [Function.notMem_support.1 hx, zero_smul, inner_zero_left]

/-- **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6 of `slicing_mass_representation`.  Let `μ` be
finite on compact subsets of `U`, `|⟨α, v(x)⟩| ≤ |α|`, `x ↦ ⟨α, v(x)⟩` Borel, and, `μ`-a.e.,
`⟨α, v(x)⟩ = 1` for some `|α| ≤ 1`.  If `S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, `A`
Borel, then `M_W(S) = μ(W ∩ A)` for every open `W ⊆ U`.

`≤`: an admissible `ω` has `‖⟨ω(x), v(x)⟩‖ ≤ 1_{spt ω}(x)`, so
`S(ω) ≤ ∫_A ‖⟨ω, v⟩‖ dμ ≤ μ(spt ω ∩ A) ≤ μ(W ∩ A)`.  `≥`: for `c < μ(W ∩ A)`,
`smr_exists_unit_form_gt` gives a continuous compactly supported `φ` with `spt φ ⊆ W`, `|φ| ≤ 1`
and `c < ∫_A ⟨φ, v⟩ dμ`, and `smr_ofReal_integral_le_massOn` gives `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)`. -/
theorem Submission.smr_restriction_massOn_eq : ∀ (P k : ℕ) (U : Set (Eucl P)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) → (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ S : GeometricCurrentOn U k, (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → S.massOn W = μ (W ∩ A) := by
  intro P k U μ v hint hfin hv hmeas hae A hA S hS W hW hWU
  apply le_antisymm
  · -- Step 1 (`≤`): `ofReal (S ω) ≤ μ(W ∩ A)` for every admissible `ω`; take the supremum.
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    have hωm : MeasurableSet (tsupport (ω : DifferentialForm (Eucl P) k)) :=
      (isClosed_tsupport _).measurableSet
    -- Off `spt ω` the form vanishes; on it `|⟨ω(x), v(x)⟩| ≤ |ω(x)| ≤ 1`.
    have hpt : ∀ x, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ≤
        (tsupport (ω : DifferentialForm (Eucl P) k)).indicator 1 x := by
      intro x
      by_cases hx : x ∈ tsupport (ω : DifferentialForm (Eucl P) k)
      · rw [indicator_of_mem hx, Pi.one_apply, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
        exact (hv x _).trans (hω.2 x)
      · refine le_of_eq ?_
        rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
    calc ENNReal.ofReal (S ω)
        = ENNReal.ofReal (∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) := by
          rw [hS]
      _ ≤ ‖∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ‖ₑ := Real.ofReal_le_enorm _
      _ ≤ ∫⁻ x in A, ‖v x ((ω : DifferentialForm (Eucl P) k) x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in A, (tsupport (ω : DifferentialForm (Eucl P) k)).indicator 1 x ∂μ :=
          lintegral_mono hpt
      _ = μ (tsupport (ω : DifferentialForm (Eucl P) k) ∩ A) := by
          rw [lintegral_indicator_one hωm, Measure.restrict_apply hωm]
      _ ≤ μ (W ∩ A) := measure_mono (inter_subset_inter_left _ hω.1)
  · -- Step 2 (`≥`): each `c < μ(W ∩ A)` is below `ofReal (∫_A ⟨φ, v⟩ dμ) ≤ M_W(S)` for a
    -- continuous unit form `φ` supported in `W`.
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨φ, hφc, hφs, hφW, hφ1, hcφ⟩ :=
      Submission.smr_exists_unit_form_gt P k U μ v hfin hv hmeas hae A hA W hW hWU c hc
    exact hcφ.trans_le (Submission.smr_ofReal_integral_le_massOn P k U μ v hint hfin hv A S hS
      W hW hWU φ hφc hφs hφW hφ1)

/-- **Simon Ch. 6, 2.7–2.9 (pp. 136–137).**  A current `X ∈ 𝒟ₖ(U)` with `M_W(X) < ∞` for every
`W ⊂⊂ U` is represented as `X(ω) = ∫ ⟨ω, v⟩ dμ` (2.7) by a Borel measure `μ` living on `U`,
finite on compact subsets of `U`, with `|⟨α, v(x)⟩| ≤ |α|`; the restrictions
`(X ⌞ A)(ω) = ∫_A ⟨ω, v⟩ dμ` to Borel sets `A` are currents (2.9) with
`M_W(X ⌞ A) = μ(W ∩ A)` for every open `W ⊆ U` (2.8).  `X` extends to continuous compactly
supported forms in `U` (`smr_exists_continuous_extension`); the Riesz representation of the
extension (`smr_riesz_continuous_forms`) gives `(μ, v)`, and the restriction statements are
`smr_restriction_isCurrent` and `smr_restriction_massOn_eq`. -/
theorem Submission.slicing_mass_representation :
    ∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k,
      (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) →
      ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k),
        IsMeasureRepresentation X μ v ∧ μ Uᶜ = 0 ∧
        (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧
        (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) ∧
        (∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U k,
          ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) ∧
        ∀ A : Set (Eucl P), MeasurableSet A → ∀ S : GeometricCurrentOn U k,
          (∀ ω : TestFormOn U k,
            S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) →
          ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → S.massOn W = μ (W ∩ A) := by
  intro P k U hU X hX
  -- Step 2: `X` extends to a linear functional `L` on continuous compactly supported forms in
  -- `U`, bounded on forms with `|φ| ≤ 1` supported in a fixed compact subset of `U`.
  obtain ⟨L, hLX, hLadd, hLsmul, hLbd⟩ :=
    Submission.smr_exists_continuous_extension P k U hU X hX
  -- Steps 3–4: Riesz gives `L φ = ∫ ⟨φ, v⟩ dμ` with (b), (c), (d), Borel coefficients of `v`
  -- and, `μ`-a.e., a covector `α` with `|α| ≤ 1` and `⟨α, v⟩ = 1`.
  obtain ⟨μ, v, hLrep, hμU, hμK, hv, hvmeas, hvunit⟩ :=
    Submission.smr_riesz_continuous_forms P k U hU L hLadd hLsmul hLbd
  -- (a): a test form is a continuous compactly supported form in `U`, on which `L = X`.
  have hrep : IsMeasureRepresentation X μ v := by
    intro ω
    obtain ⟨hint, hL⟩ := hLrep (ω : DifferentialForm (Eucl P) k)
      (ContDiff.continuous ω.property.1.1) ω.property.1.2 ω.property.2
    exact ⟨hint, (hLX ω).symm.trans hL⟩
  have hint : ∀ ω : TestFormOn U k,
      Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) k) x)) μ := fun ω => (hrep ω).1
  -- (e): restrictions are currents (Step 5); (f): their mass on open `W ⊆ U` is `μ (W ∩ A)`
  -- (Step 6).
  exact ⟨μ, v, hrep, hμU, hμK, hv,
    fun A _ => Submission.smr_restriction_isCurrent P k U μ v hint hμK hv A,
    fun A hA S hS W hW hWU => Submission.smr_restriction_massOn_eq P k U μ v hint hμK hv hvmeas
      hvunit A hA S hS W hW hWU⟩
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

/-- **Simon Ch. 6, 4.6 (p. 157).**  The slice `⟨T, f, t₋⟩ = ∂(T ⌞ A_t) − (∂T) ⌞ A_t` exists for
every level `t`.  `A_t = {x ∈ U | f x < t}` is open, as `f` is continuous on the open set `U`;
the representations of `T` and `∂T` from `slicing_mass_representation` restrict to `A_t`, and
`∂(T ⌞ A_t) − (∂T) ⌞ A_t` is again a sequentially continuous functional. -/
theorem Submission.slicing_exists :
    ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ t : ℝ,
        ∃ S : GeometricCurrentOn U m, IsSlice T f t S := by
  intro P m U hU T hT f L hf t
  -- Step 1: `A_t = U ∩ f⁻¹(-∞, t)` is open, hence Borel.
  have hAt : MeasurableSet {x | x ∈ U ∧ f x < t} :=
    (hf.continuousOn.isOpen_inter_preimage hU isOpen_Iio).measurableSet
  -- Step 2: `T ⌞ A_t`, through a representation `(μ, v)` of `T`.
  obtain ⟨μ, v, hrep, -, -, -, hres, -⟩ :=
    Submission.slicing_mass_representation P (m + 1) U hU T fun W hW => (hT W hW).1
  obtain ⟨A, hA⟩ := hres _ hAt
  -- Step 3: `(∂T) ⌞ A_t`, through a representation `(μ', v')` of `∂T`.
  obtain ⟨μ', v', hrep', -, -, -, hres', -⟩ :=
    Submission.slicing_mass_representation P m U hU T.boundary fun W hW => (hT W hW).2
  obtain ⟨B, hB⟩ := hres' _ hAt
  -- Step 4: `S = ∂A − B` is linear, and continuous as a difference of continuous functionals.
  refine ⟨⟨A.boundary.toCurrent - B.toCurrent, fun ωs hωs => ?_⟩,
    A, B, ⟨hAt, μ, v, hrep, hA⟩, ⟨hAt, μ', v', hrep', hB⟩, fun ω => rfl⟩
  simpa using (A.boundary.continuous' ωs hωs).sub (B.continuous' ωs hωs)
/-- **Simon Ch. 6, 4.8 (p. 157).**  Every slice `S = ⟨T, f, t₋⟩` of (4.6) satisfies
`spt S ⊆ spt T ∩ {f = t}`.  With `A_t = {x ∈ U | f x < t}` and representations `(μ, v)` of `T`
and `(μ', v')` of `∂T`, `S(ω) = ∫_{A_t} ⟨dω, v⟩ dμ − ∫_{A_t} ⟨ω, v'⟩ dμ'`.  Both integrals
vanish for `ω` supported where `T = 0` (`slicing_representation_unique` against the zero
representation) or where `f > t`, and both equal `T(dω)` for `ω` supported where `f < t`. -/
theorem Submission.slicing_support_subset :
    ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
      ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
      ∀ (t : ℝ) (S : GeometricCurrentOn U m), IsSlice T f t S →
        S.support ⊆ T.support ∩ {x | f x = t} := by
  intro P m U hU T f L hf t S hS
  -- Step 0: unpack the slice into the formula for `S(ω)` above.
  obtain ⟨A, B, ⟨hAt, μ, v, hrep, hA⟩, ⟨-, μ', v', hrep', hB⟩, hSAB⟩ := hS
  set At : Set (Eucl P) := {x | x ∈ U ∧ f x < t}
  have hS_eq : ∀ ω : TestFormOn U m, S ω =
      (∫ x in At, v x (((exteriorDerivativeTestOn U m ω : TestFormOn U (m + 1)) :
        DifferentialForm (Eucl P) (m + 1)) x) ∂μ) -
      ∫ x in At, v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ' := fun ω => by
    rw [hSAB ω, GeometricCurrentOn.boundary_apply, hA, hB]
  -- Locality: if a represented current vanishes on an open `W`, so does its restriction to
  -- `A_t` (`slicing_representation_unique` against the zero representation).
  have hloc : ∀ {k : ℕ} (X : GeometricCurrentOn U k) (ν : Measure (Eucl P))
      (w : Eucl P → NVector (Eucl P) k), IsMeasureRepresentation X ν w →
      ∀ W : Set (Eucl P), IsOpen W → X.VanishesOn W →
      ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W →
        ∫ x in At, w x ((ω : DifferentialForm (Eucl P) k) x) ∂ν = 0 := by
    intro k X ν w hX W hW hvan ω hω
    simpa using Submission.slicing_representation_unique P k U hU ν 0 w 0 (fun η => (hX η).1)
      (fun _ => integrable_zero_measure) W hW
      (fun η hη => by rw [← (hX η).2, hvan η hη]; simp) At hAt ω hω
  -- Forms vanish off their topological support, and `tsupport dω ⊆ tsupport ω`.
  have hzero : ∀ {k : ℕ} (w : Eucl P → NVector (Eucl P) k) (η : DifferentialForm (Eucl P) k)
      (y : Eucl P), y ∉ tsupport η → w y (η y) = 0 := fun w η y hy => by
    rw [image_eq_zero_of_notMem_tsupport hy, map_zero]
  have hd : ∀ (ω : TestFormOn U m) (W' : Set (Eucl P)),
      tsupport (ω : DifferentialForm (Eucl P) m) ⊆ W' →
      tsupport (((exteriorDerivativeTestOn U m ω : TestFormOn U (m + 1)) :
        DifferentialForm (Eucl P) (m + 1))) ⊆ W' := fun _ _ hω =>
    (tsupport_exteriorDerivative_subset _).trans hω
  -- Step 1: `x ∈ U`, and `S` vanishes on no open `W' ∋ x` with `closure W'` compact in `U`.
  rintro x ⟨hxU, hxS⟩
  have hS_ne : ∀ W' : Set (Eucl P), IsOpen W' → IsCompact (closure W') → closure W' ⊆ U →
      x ∈ W' → S.VanishesOn W' → False := fun W' h1 h2 h3 hxW hvan =>
    hxS ⟨W', ⟨h1, h2, h3, hvan⟩, hxW⟩
  refine ⟨⟨hxU, ?_⟩, ?_⟩
  · -- Step 2: if `T` vanishes on such a `W' ∋ x`, then so do `∂T` and hence `S`.
    rintro ⟨W', ⟨h1, h2, h3, hTvan⟩, hxW⟩
    apply hS_ne W' h1 h2 h3 hxW
    intro ω hω
    have hbvan : T.boundary.VanishesOn W' := fun η hη => by
      rw [GeometricCurrentOn.boundary_apply]
      exact hTvan _ (hd η W' hη)
    rw [hS_eq ω, hloc T μ v hrep W' h1 hTvan _ (hd ω W' hω),
      hloc T.boundary μ' v' hrep' W' h1 hbvan ω hω, sub_self]
  · -- Step 3: `f x = t`, since otherwise `S` vanishes on a small ball around `x`.
    have hcont : ContinuousAt f x := hf.continuousOn.continuousAt (hU.mem_nhds hxU)
    have hball : ∀ p : Eucl P → Prop, (∀ᶠ y in 𝓝 x, p y) → ∃ W' : Set (Eucl P), IsOpen W' ∧
        IsCompact (closure W') ∧ closure W' ⊆ U ∧ x ∈ W' ∧ ∀ y ∈ W', p y := by
      intro p hp
      obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff_ball.1
        ((show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hxU).and hp)
      refine ⟨ball x (r / 2), isOpen_ball, ?_, ?_, mem_ball_self (by linarith), ?_⟩
      · rw [closure_ball x (by positivity)]
        exact isCompact_closedBall x _
      · rw [closure_ball x (by positivity)]
        exact fun y hy => (hr' y (closedBall_subset_ball (by linarith) hy)).1
      · exact fun y hy => (hr' y (ball_subset_ball (by linarith) hy)).2
    rcases lt_trichotomy (f x) t with hlt | heq | hgt
    · -- (a) `f < t` near `x`: both integrals equal `T(dω)`.
      exfalso
      obtain ⟨W', h1, h2, h3, hxW, hW'⟩ :=
        hball (fun y => f y < t) (hcont.eventually (eventually_lt_nhds hlt))
      apply hS_ne W' h1 h2 h3 hxW
      intro ω hω
      have hWA : W' ⊆ At := fun y hy => ⟨h3 (subset_closure hy), hW' y hy⟩
      rw [hS_eq ω, setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => hzero v _ y fun h => hy (hWA (hd ω W' hω h))),
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => hzero v' _ y fun h => hy (hWA (hω h))),
        ← (hrep _).2, ← (hrep' ω).2, GeometricCurrentOn.boundary_apply, sub_self]
    · exact heq
    · -- (b) `f > t` near `x`: both integrals vanish.
      exfalso
      obtain ⟨W', h1, h2, h3, hxW, hW'⟩ :=
        hball (fun y => t < f y) (hcont.eventually (eventually_gt_nhds hgt))
      apply hS_ne W' h1 h2 h3 hxW
      intro ω hω
      have hWA : ∀ y ∈ At, y ∉ W' := fun y hy hyW => lt_asymm hy.2 (hW' y hyW)
      rw [hS_eq ω, setIntegral_eq_zero_of_forall_eq_zero
          (fun y hy => hzero v _ y fun h => hWA y hy (hd ω W' hω h)),
        setIntegral_eq_zero_of_forall_eq_zero
          (fun y hy => hzero v' _ y fun h => hWA y hy (hω h)), sub_self]
/-- **Mass bound for slices (Simon Ch. 6, 4.9–4.10, pp. 157–158).**  For `W ⊆ U` open,
`‖Df‖ ≤ L_W` a.e. on `W` and `a < b`, `t ↦ M_W(⟨T, f, t⟩)` has a measurable majorant `g` on
`(a, b)` with `∫⁻_{(a,b)} g ≤ L_W M_W(T ⌞ {a < f < b})`.  In the normalized representation
`(μ, v)` of `T`, `M_W(T ⌞ {a < f < b}) = μ(W ∩ {a < f < b})`, and (4.9) bounds `M_W(⟨T, f, t⟩)`
by `L_W liminf_{h ↓ 0} h⁻¹ μ(W ∩ f⁻¹[t - h, t])`.  This is `L_W` times the lower left density at
`t` of `ν = f_#(μ ⌞ W)`, which has a measurable majorant with integral `≤ ν(a, b)` (4.10). -/
theorem Submission.slicing_mass_bound : ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → ∀ S : ℝ → GeometricCurrentOn U m, (∀ t, IsSlice T f t (S t)) → ∀ W, IsOpen W → W ⊆ U → ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) → ∀ a b : ℝ, a < b → ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W := by
  intro P m U hU T hT f L hf S hS W hW hWU LW hLW a b hab R hR
  -- Step 1: a normalized representation `(μ, v)` of `T`, finite on compact subsets of `U`.
  obtain ⟨μ, v, hrep, -, hfin, hnorm, -, hmass⟩ :=
    Submission.slicing_mass_representation P (m + 1) U hU T fun W' hW' => (hT W' hW').1
  -- Step 2: `R = T ⌞ A` is also computed in `(μ, v)`, hence `M_W(R) = μ(W ∩ A)`.
  obtain ⟨hA, μR, vR, hrepR, hRA⟩ := hR
  have hR' : ∀ ω : TestFormOn U (m + 1), R ω = ∫ x in {x | x ∈ U ∧ a < f x ∧ f x < b},
      v x ((ω : DifferentialForm (Eucl P) (m + 1)) x) ∂μ := by
    intro ω
    rw [hRA ω]
    exact Submission.slicing_representation_unique P (m + 1) U hU μR μ vR v
      (fun ω => (hrepR ω).1) (fun ω => (hrep ω).1) univ isOpen_univ
      (fun ω _ => (hrepR ω).2.symm.trans (hrep ω).2) _ hA ω (subset_univ _)
  have hRmass : R.massOn W = μ (W ∩ {x | x ∈ U ∧ a < f x ∧ f x < b}) :=
    hmass _ hA R hR' W hW hWU
  -- Step 3: `ν = f_#(μ ⌞ W)`, using that `f` is continuous on the open set `W ⊆ U`.
  have hfm : AEMeasurable f (μ.restrict W) :=
    (hf.continuousOn.mono hWU).aemeasurable hW.measurableSet
  have hν : ∀ s : Set ℝ, MeasurableSet s → (μ.restrict W).map f s = μ (W ∩ f ⁻¹' s) := by
    intro s hs
    rw [Measure.map_apply_of_aemeasurable hfm hs, Measure.restrict_apply' hW.measurableSet,
      inter_comm]
  -- Step 4: (4.10) for `ν`: a measurable majorant `g₀` of the lower left densities of `ν`.
  obtain ⟨g₀, hg₀, hg₀le, hg₀int⟩ :=
    Submission.slicing_mb_density_majorant ((μ.restrict W).map f) a b hab
  refine ⟨fun t => (LW : ℝ≥0∞) * g₀ t, hg₀.const_mul _, fun t ht => ?_, ?_⟩
  · -- Step 5: (4.9) gives `M_W(S t) ≤ L_W liminf_{h ↓ 0} h⁻¹ ν[t - h, t] ≤ L_W g₀(t)`.
    have hden : (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) =
        fun h : ℝ => (μ.restrict W).map f (Icc (t - h) t) / ENNReal.ofReal h := by
      funext h
      rw [hν _ measurableSet_Icc]
    calc (S t).massOn W
        ≤ (LW : ℝ≥0∞) *
            liminf (fun h : ℝ => μ (W ∩ f ⁻¹' Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) :=
          Submission.slicing_mb_pointwise P m U hU T μ v hrep hfin hnorm f L hf t (S t) (hS t)
            W hW hWU LW hLW
      _ ≤ (LW : ℝ≥0∞) * g₀ t := by
          rw [hden]
          exact mul_le_mul_right (hg₀le t ht) _
  · -- Step 6: `∫⁻_{(a,b)} L_W g₀ ≤ L_W ν(a, b) = L_W μ(W ∩ {a < f < b}) = L_W M_W(R)`.
    have hWab : W ∩ f ⁻¹' Ioo a b = W ∩ {x | x ∈ U ∧ a < f x ∧ f x < b} := by
      ext x
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, hWU hx, h⟩
      · rintro ⟨hx, -, h⟩
        exact ⟨hx, h⟩
    calc ∫⁻ t in Ioo a b, (LW : ℝ≥0∞) * g₀ t
        = (LW : ℝ≥0∞) * ∫⁻ t in Ioo a b, g₀ t := lintegral_const_mul _ hg₀
      _ ≤ (LW : ℝ≥0∞) * (μ.restrict W).map f (Ioo a b) := mul_le_mul_right hg₀int _
      _ = (LW : ℝ≥0∞) * R.massOn W := by
          rw [hν _ measurableSet_Ioo, hWab, hRmass]

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
