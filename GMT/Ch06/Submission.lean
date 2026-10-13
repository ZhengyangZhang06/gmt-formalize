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

/-- Mollifying a Lipschitz map, as for Simon's `f^{(σ)} = f ∗ φ^{(σ)}` (Ch. 6, 2.29, p. 141): for
an `L`-Lipschitz `F : ℝ^m → ℝ^{m'}`, `F_σ(x) = ∫ ρ(w) F(x - w) dw`, with `ρ` the mollifier of
`slicing_mb_sa_mollifier_exists` at radius `σ/2`, is smooth, `L`-Lipschitz and `Lσ`-close to `F`.
If `F` is `Λ'`-Lipschitz on `B(x, 2σ)`, then `F_σ` is `Λ'`-Lipschitz on `B(x, σ)`,
`‖DF_σ(x)‖ ≤ Λ'` and `|F_σ(x) - F(x)| ≤ Λ'σ`; a coordinate of `F` constant on `B(x, σ)` keeps
its value at `x`. -/
theorem Submission.dph_sa_mollify_lipschitz :
    ∀ (m m' : ℕ) (F : Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L F → ∀ σ : ℝ, 0 < σ →
      ∃ Fs : Eucl m → Eucl m', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs ∧ LipschitzWith L Fs ∧
        (∀ x, ‖Fs x - F x‖ ≤ (L : ℝ) * σ) ∧
        (∀ (x : Eucl m) (Λ' : ℝ≥0), LipschitzOnWith Λ' F (ball x (2 * σ)) →
          LipschitzOnWith Λ' Fs (ball x σ) ∧ ‖fderiv ℝ Fs x‖ ≤ (Λ' : ℝ) ∧
            ‖Fs x - F x‖ ≤ (Λ' : ℝ) * σ) ∧
        ∀ (x : Eucl m) (i : Fin m') (c : ℝ), (∀ y ∈ ball x σ, F y i = c) → Fs x i = c := by
  intro m m' F L hF σ hσ
  -- The mollifier `ρ ≥ 0`, `∫ ρ = 1`, vanishing off `B(0, σ/2)`.
  obtain ⟨ρ, hρs, hρc, hρ0, hρz, hρ1⟩ :=
    Submission.slicing_mb_sa_mollifier_exists m (σ / 2) (half_pos hσ)
  have hρi : Integrable ρ := hρs.continuous.integrable_of_hasCompactSupport hρc
  -- `F_σ(x) = ∫ ρ(w) • F(x - w) dw`; each integrand is continuous with compact support.
  let Fs : Eucl m → Eucl m' := fun x => ∫ w, ρ w • F (x - w)
  have hint : ∀ x, Integrable (fun w => ρ w • F (x - w)) := fun x =>
    (hρs.continuous.smul (hF.continuous.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport hρc.smul_right
  -- `|∫ ρ • G| ≤ B` once `|G| ≤ B` on `B(0, σ/2)`, outside of which `ρ = 0`.
  have hbound : ∀ (G : Eucl m → Eucl m') (B : ℝ), (∀ w : Eucl m, ‖w‖ < σ / 2 → ‖G w‖ ≤ B) →
      ‖∫ w, ρ w • G w‖ ≤ B := by
    intro G B hG
    calc ‖∫ w, ρ w • G w‖ ≤ ∫ w, ρ w * B := by
          refine norm_integral_le_of_norm_le (hρi.mul_const B) (Eventually.of_forall fun w => ?_)
          by_cases hw : ‖w‖ < σ / 2
          · rw [norm_smul, Real.norm_of_nonneg (hρ0 w)]
            exact mul_le_mul_of_nonneg_left (hG w hw) (hρ0 w)
          · rw [hρz w (not_lt.1 hw), zero_smul, norm_zero, zero_mul]
      _ = B := by rw [integral_mul_const, hρ1, one_mul]
  -- Smoothness: `F_σ = ρ ⋆ F`.
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs := by
    have : Fs = convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext x
      rw [convolution_lsmul]
    rw [this]
    exact hρc.contDiff_convolution_left _ hρs hF.continuous.locallyIntegrable
  -- (E) `|F_σ(y) - F_σ(y')| ≤ Λ'|y - y'|` if `F` is `Λ'`-Lipschitz on a `U` containing
  -- `y - w` and `y' - w` for all `|w| < σ/2`.
  have hE : ∀ (U : Set (Eucl m)) (Λ' : ℝ≥0), LipschitzOnWith Λ' F U → ∀ y y' : Eucl m,
      (∀ w : Eucl m, ‖w‖ < σ / 2 → y - w ∈ U ∧ y' - w ∈ U) →
        ‖Fs y - Fs y'‖ ≤ Λ' * ‖y - y'‖ := by
    intro U Λ' hU y y' hyy'
    have : Fs y - Fs y' = ∫ w, ρ w • (F (y - w) - F (y' - w)) := by
      simp only [Fs, smul_sub]
      rw [integral_sub (hint y) (hint y')]
    rw [this]
    refine hbound _ _ fun w hw => ?_
    obtain ⟨h1, h2⟩ := hyy' w hw
    calc ‖F (y - w) - F (y' - w)‖ ≤ Λ' * ‖(y - w) - (y' - w)‖ := hU.norm_sub_le h1 h2
      _ = Λ' * ‖y - y'‖ := by rw [sub_sub_sub_cancel_right]
  -- (C) `|F_σ(x) - F(x)| ≤ Λ'σ` if `F` is `Λ'`-Lipschitz on a `U` containing `x` and `x - w`
  -- for all `|w| < σ/2`.
  have hC : ∀ (U : Set (Eucl m)) (Λ' : ℝ≥0), LipschitzOnWith Λ' F U → ∀ x : Eucl m, x ∈ U →
      (∀ w : Eucl m, ‖w‖ < σ / 2 → x - w ∈ U) → ‖Fs x - F x‖ ≤ Λ' * σ := by
    intro U Λ' hU x hx hxw
    have h1 : ∫ w, ρ w • F x = F x := by rw [integral_smul_const, hρ1, one_smul]
    have : Fs x - F x = ∫ w, ρ w • (F (x - w) - F x) := by
      simp only [Fs, smul_sub]
      rw [integral_sub (hint x) (hρi.smul_const (F x)), h1]
    rw [this]
    refine hbound _ _ fun w hw => ?_
    calc ‖F (x - w) - F x‖ ≤ Λ' * ‖(x - w) - x‖ := hU.norm_sub_le (hxw w hw) hx
      _ = Λ' * ‖w‖ := by rw [sub_sub_cancel_left, norm_neg]
      _ ≤ Λ' * σ := by gcongr; linarith
  refine ⟨Fs, hsmooth, ?_, ?_, ?_, ?_⟩
  -- Global bounds: `U = ℝ^m`, `Λ' = L`.
  · refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hE univ L hF.lipschitzOnWith y y' fun w _ => ⟨mem_univ _, mem_univ _⟩
  · exact fun x => hC univ L hF.lipschitzOnWith x (mem_univ _) fun w _ => mem_univ _
  -- Local bounds: `U = B(x, 2σ)` contains `y - w` for `y ∈ B(x, σ)`, `|w| < σ/2`.
  · intro x Λ' hΛ
    have hmem : ∀ y ∈ ball x σ, ∀ w : Eucl m, ‖w‖ < σ / 2 → y - w ∈ ball x (2 * σ) := by
      intro y hy w hw
      rw [mem_ball, dist_eq_norm] at hy ⊢
      calc ‖y - w - x‖ = ‖(y - x) - w‖ := by rw [sub_right_comm]
        _ ≤ ‖y - x‖ + ‖w‖ := norm_sub_le _ _
        _ < 2 * σ := by linarith
    have hLoc : LipschitzOnWith Λ' Fs (ball x σ) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      exact hE _ Λ' hΛ y y' fun w hw => ⟨hmem y hy w hw, hmem y' hy' w hw⟩
    refine ⟨hLoc, norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hσ) hLoc, ?_⟩
    exact hC _ Λ' hΛ x (mem_ball_self (by linarith)) (hmem x (mem_ball_self hσ))
  -- Locality of coordinates: `F_σ(x)_i = ∫ ρ(w) F(x - w)_i dw = c ∫ ρ = c`.
  · intro x i c hc
    have h1 : Fs x i = ∫ w, ρ w * F (x - w) i := by
      have := (EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ).integral_comp_comm (hint x)
      simpa [Fs] using this.symm
    rw [h1]
    have h2 : ∀ w, ρ w * F (x - w) i = ρ w * c := by
      intro w
      by_cases hw : ‖w‖ < σ / 2
      · rw [hc (x - w) (by rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; linarith)]
      · rw [hρz w (not_lt.1 hw), zero_mul, zero_mul]
    simp_rw [h2]
    rw [integral_mul_const, hρ1, one_mul]
/-- Multilinear-algebra step of the smoothing argument in the proof of the Deformation Theorem
(Simon Ch. 6, §5): a `k`-covector `γ` on `ℝ^{m'}` with `γ(e_{α(0)}, …, e_{α(k-1)}) = 0` pulls back
to `0` under every linear `T` with image in `span {e_{α(q)}}`.  With `S c = ∑_q c_q e_{α(q)}` on
`ℝ^k`, `T v = S ((T v)_{α(q)})_q`, and the alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes because
its value on the standard basis is `γ(e_{α(0)}, …, e_{α(k-1)}) = 0`. -/
theorem Submission.dph_sa_covector_comp_eq_zero :
    ∀ (m m' k : ℕ) (α : SimonMultiIndex k m') (γ : Eucl m' [⋀^Fin k]→L[ℝ] ℝ) (T : Eucl m →L[ℝ] Eucl m'), γ (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0 → (∀ (v : Eucl m) (i : Fin m'), i ∉ range α → T v i = 0) → γ.compContinuousLinearMap T = 0 := by
  intro m m' k α γ T hγ hT
  -- `S c = ∑_q c_q e_{α(q)}` on `ℝ^k`.
  let S : (Fin k → ℝ) →ₗ[ℝ] Eucl m' :=
    Fintype.linearCombination ℝ fun q => EuclideanSpace.single (α q) (1 : ℝ)
  -- `T` factors through `S`: coordinates in `range α` agree as `α` is injective, the others vanish.
  have hfac : ∀ v, T v = S fun q => T v (α q) := by
    intro v
    refine PiLp.ext fun i => ?_
    simp only [S, Fintype.linearCombination_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ range α
    · obtain ⟨q₀, rfl⟩ := hi
      simp [α.injective.eq_iff]
    · rw [hT v i hi, Finset.sum_eq_zero fun q _ => ite_eq_right fun h => hi ⟨q, h.symm⟩]
  -- The alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes on the standard basis, hence is `0`.
  have h0 : γ.toAlternatingMap.compLinearMap S = 0 := by
    have hb : (fun q => S (Pi.basisFun ℝ (Fin k) q)) =
        fun j => EuclideanSpace.single (α j) (1 : ℝ) := by
      funext q
      simp [S]
    rw [← AlternatingMap.map_basis_eq_zero_iff (Pi.basisFun ℝ (Fin k)),
      AlternatingMap.compLinearMap_apply, ContinuousAlternatingMap.coe_toAlternatingMap, hb]
    exact hγ
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  rw [show ⇑T ∘ v = fun p => S fun q => T (v p) (α q) from funext fun p => hfac (v p)]
  exact AlternatingMap.congr_fun h0 fun p q => T (v p) (α q)

/-- The smoothings `f_σ = f ∗ φ_σ` of Simon Ch. 6, 2.29 (p. 141), for the Lipschitz push-forward
homotopy of the deformation theorem (§5): extend `G` from `A_δ = thickening δ A` to a Lipschitz
`G'` on `ℝ^m` (McShane) and mollify it at the scales `σ_j = (δ / 8) / (j + 1)`.  The
`2σ_j`-balls about points of `A_{δ/2}` stay in `A_δ`, where `G' = G` is `Λ`-Lipschitz, so
`‖D(Gj j)‖ ≤ Λ` there.  Near `A`, wherever `Gj j` meets `spt ω` the normal coordinates
`i ∉ range α` of `G` equal `z i` on a `2σ_j`-ball, so those of `Gj j` are locally constant,
`D(Gj j)` maps into `span e_α`, and `ω` without `e_α`-component pulls back to `0`. -/
theorem Submission.dph_lipschitz_smooth_approx :
    ∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ →
      LipschitzOnWith Λ G (thickening δ A) →
      ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0),
        LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧
        (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧
        TendstoUniformly Gj G' atTop ∧
        (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧
        ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m')
          (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε →
          (∀ x ∈ thickening ε A,
            G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) →
              ∀ i, i ∉ range α → G x i = z i) →
          (∀ y, (ω : DifferentialForm (Eucl m') k) y
            (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) →
          ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A,
            ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap
              (fderiv ℝ (Gj j) x) = 0 := by
  intro m m' G Λ A δ hδ hG
  -- Step 1 (McShane): a global Lipschitz extension `G'` of `G|A_δ`.
  obtain ⟨G', L, hG'L, hG'⟩ : ∃ (G' : Eucl m → Eucl m') (L : ℝ≥0),
      LipschitzWith L G' ∧ EqOn G' G (thickening δ A) :=
    let ⟨G', hG'L, hGG'⟩ := hG.extend_finite_dimension
    ⟨G', _, hG'L, hGG'.symm⟩
  -- The scales `σ_j = (δ / 8) / (j + 1)`: positive, at most `δ / 8`, tending to `0`.
  obtain ⟨σ, hσ, hσδ, hσ0⟩ : ∃ σ : ℕ → ℝ, (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ δ / 8) ∧
      Tendsto σ atTop (𝓝 0) := by
    refine ⟨fun j => δ / 8 * (1 / ((j : ℝ) + 1)), fun j => by positivity, fun j => ?_, ?_⟩
    · dsimp only
      rw [mul_one_div]
      exact div_le_self (by positivity) (by linarith [j.cast_nonneg (α := ℝ)])
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 8)
  -- Step 2: `Gj j` is the mollification of `G'` at scale `σ j`.
  choose Gj hGj hGjL hGjG' hGjloc hGjc using fun j =>
    Submission.dph_sa_mollify_lipschitz m m' G' L hG'L (σ j) (hσ j)
  -- For `x ∈ A_{δ/2}` the ball `B(x, 2σ_j)` lies in `A_δ`, where `G' = G` is `Λ`-Lipschitz.
  have hball : ∀ j, ∀ x ∈ thickening (δ / 2) A, ball x (2 * σ j) ⊆ thickening δ A :=
    fun j x hx => (ball_subset_thickening hx (2 * σ j)).trans
      ((thickening_thickening_subset (2 * σ j) (δ / 2) A).trans
        (thickening_mono (by linarith [hσδ j]) A))
  have hlocal : ∀ j, ∀ x ∈ thickening (δ / 2) A, LipschitzOnWith Λ G' (ball x (2 * σ j)) :=
    fun j x hx => LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => by
      rw [hG' (hball j x hx hy), hG' (hball j x hx hy')]
      exact hG.dist_le_mul y (hball j x hx hy) y' (hball j x hx hy')
  refine ⟨G', Gj, L, hG'L, hG', hGj, hGjL, ?_,
    fun j x hx => (hGjloc j x Λ (hlocal j x hx)).2.1, ?_⟩
  · -- Step 3: `‖Gj j - G'‖ ≤ L σ_j → 0`.
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    have hL := hσ0.const_mul (L : ℝ)
    rw [mul_zero] at hL
    filter_upwards [hL.eventually_lt_const hη] with j hj x
    rw [dist_comm, dist_eq_norm]
    exact (hGjG' j x).trans_lt hj
  -- Step 4 (tangential vanishing) on `A_{μ/4}`, `μ = min ε δ`, once `σ_j < μ / 8` and
  -- `(4Λ + 4) σ_j < ε`.
  intro k α z ω ε hε hH1 hH2
  obtain ⟨μ, hμ, hμε, hμδ⟩ : ∃ μ : ℝ, 0 < μ ∧ μ ≤ ε ∧ μ ≤ δ :=
    ⟨min ε δ, lt_min hε hδ, min_le_left _ _, min_le_right _ _⟩
  have hΛ : (0 : ℝ) ≤ Λ := Λ.2
  refine ⟨μ / 4, by positivity, ?_⟩
  have hc : 0 < min (μ / 8) (ε / (4 * Λ + 4)) := lt_min (by positivity) (by positivity)
  filter_upwards [hσ0.eventually_lt_const hc] with j hj x hx
  have hj1 : σ j < μ / 8 := hj.trans_le (min_le_left _ _)
  have hj2 : σ j * (4 * Λ + 4) < ε :=
    (lt_div_iff₀ (by positivity)).1 (hj.trans_le (min_le_right _ _))
  have hx2 : x ∈ thickening (δ / 2) A := thickening_mono (by linarith) A hx
  have hxδ : x ∈ thickening δ A := thickening_mono (by linarith) A hx
  by_cases hsupp : Gj j x ∈ tsupport (ω : DifferentialForm (Eucl m') k)
  · refine Submission.dph_sa_covector_comp_eq_zero m m' k α _ _ (hH2 _) fun v i hi => ?_
    -- On `B(x, 2σ_j)` the normal coordinates of `G' = G` are those of `z`: such `y` lie in
    -- `A_ε ∩ A_δ`, and `|G y - Gj j x| ≤ 2Λσ_j + Λσ_j < ε` with `Gj j x ∈ spt ω`.
    have hnormal : ∀ y ∈ ball x (2 * σ j), G' y i = z i := by
      intro y hy
      have hyA : y ∈ thickening (2 * σ j + μ / 4) A :=
        thickening_thickening_subset (2 * σ j) (μ / 4) A (ball_subset_thickening hx _ hy)
      have hyδ : y ∈ thickening δ A := thickening_mono (by linarith) A hyA
      rw [hG' hyδ]
      refine hH1 y (thickening_mono (by linarith) A hyA) ?_ i hi
      refine mem_thickening_iff.2 ⟨Gj j x, hsupp, ?_⟩
      have h1 : dist (G y) (G x) ≤ Λ * dist y x := hG.dist_le_mul y hyδ x hxδ
      have h2 : ‖Gj j x - G' x‖ ≤ Λ * σ j := (hGjloc j x Λ (hlocal j x hx2)).2.2
      rw [hG' hxδ, ← dist_eq_norm] at h2
      have h3 : dist y x < 2 * σ j := hy
      calc dist (G y) (Gj j x) ≤ dist (G y) (G x) + dist (Gj j x) (G x) :=
            dist_triangle_right _ _ _
        _ ≤ Λ * (2 * σ j) + Λ * σ j :=
            add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3.le hΛ)) h2
        _ < ε := by nlinarith [mul_nonneg hΛ (hσ j).le, hσ j]
    -- Hence the `i`-th coordinate of `Gj j` is `z i` on `B(x, σ_j)` and `D(Gj j)(x)` has
    -- vanishing `i`-th coordinate.
    have hconst : (EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ) ∘ Gj j =ᶠ[𝓝 x] fun _ => z i :=
      Filter.mem_of_superset (ball_mem_nhds x (hσ j)) fun x' hx' =>
        hGjc j x' i (z i) fun y hy => hnormal y (by
          rw [mem_ball] at hx' hy ⊢
          linarith [dist_triangle y x' x])
    have hD := ((EuclideanSpace.proj i : Eucl m' →L[ℝ] ℝ).hasFDerivAt.comp x
      (((hGj j).differentiable (by simp)).differentiableAt.hasFDerivAt)).unique
      ((hasFDerivAt_const (z i) x).congr_of_eventuallyEq hconst)
    simpa using congrArg (fun T : Eucl m →L[ℝ] ℝ => T v) hD
  · -- Off `spt ω` the covector `ω (Gj j x)` is already `0`.
    rw [image_eq_zero_of_notMem_tsupport hsupp]
    ext v
    simp
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

/-- **Integrality of the Lipschitz push-forward defined by smooth approximation** (step 5.9 of the
push-forward homotopy argument; Simon Ch. 6, 2.29 and Lemma 3.9).  Assume (S5′): `g_# X` is an
integer multiplicity `S'` with `∫_M θ ⟨ω(g_j x), (Dg_j)_# ξ⟩ dHᵏ → S'(ω)` along `C¹` maps
`g_j → g`.  If `S` is the limit of `X(η_n)` for forms `η_n` compatible with smooth approximations
`G_n → G` near `spt X`, then `S` is integer multiplicity.  Take `G_n → Ĝ` from
`dph_lipschitz_smooth_approx` and `η_n` from `iwl_sp_exists_compatible_testForm`.  As
`Hᵏ(M ∖ spt X) = 0` (`iwl_sp_rectifiable_support_null`), `X(η_n)` is the integral for `g_j = G_n`,
so `S = S'`. -/
theorem Submission.dph_lipschitz_pushforward_im : (∀ (P Q k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → (∀ x ∈ M, ∃ j : ℕ, θ x = j) → (∀ ω : TestFormOn (univ : Set (Eucl P)) k, X ω = tauAction k M θ ξ ω) → ∀ (g : Eucl P → Eucl Q) (Λ : ℝ≥0), LipschitzWith Λ g → (∀ K : Set (Eucl Q), IsCompact K → IsCompact (g ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl Q)) k, IsLipschitzPushforward X g S ∧ IsIntegerMultiplicity S ∧ ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : TestFormOn (univ : Set (Eucl Q)) k, Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) ((ω : DifferentialForm (Eucl Q) k) (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (S ω))) → ∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (r : ℝ) (S : GeometricCurrentOn (univ : Set (Eucl m')) k), IsIntegerMultiplicity X → 0 < r → LipschitzOnWith Λ G (thickening r X.support) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → (∀ (Gj : ℕ → Eucl m → Eucl m') (O : Set (Eucl m)) (L : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω))) → IsIntegerMultiplicity S := by
  intro hS5 m m' k X G Λ r S hX hr hGLip hGprop hLipPF
  -- 1. `X = τ(M, θ, ξ)` with `θ` integer-valued.
  obtain ⟨M, θ, ξ, hT, hθ, hXτ⟩ := hX
  -- 2. `Ĝ = G'` is Lipschitz with `Ĝ = G` on `(spt X)_r`; the `C^∞` maps `G_n` are `L`-Lipschitz,
  -- `G_n → Ĝ` uniformly and `‖DG_n‖ ≤ Λ` on `O₀ = (spt X)_{r/2}`, where `G_n → G` uniformly.
  obtain ⟨G', Gj, L, hG'Lip, hG'eq, hGjsmooth, hGjLip, hGjconv, hGjderiv, -⟩ :=
    Submission.dph_lipschitz_smooth_approx m m' G Λ X.support r hr hGLip
  have hsptO : X.support ⊆ thickening (r / 2) X.support := self_subset_thickening (half_pos hr) _
  have hOr : thickening (r / 2) X.support ⊆ thickening r X.support :=
    thickening_mono (half_le_self hr.le) _
  have hsptr : X.support ⊆ thickening r X.support := self_subset_thickening hr _
  have hconvO : TendstoUniformlyOn Gj G atTop (thickening (r / 2) X.support) :=
    hGjconv.tendstoUniformlyOn.congr_right (hG'eq.mono hOr)
  -- 3. `Ĝ` is proper on `spt X` (it equals `G` there), so (S5′) gives an integer multiplicity `S'`
  -- with `I_n(ω) = ∫_M θ ⟨ω(G_n x), (DG_n)_# ξ⟩ dHᵏ → S'(ω)`.
  have hG'prop : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (G' ⁻¹' K ∩ X.support) := by
    intro K hK
    have hEq : G' ⁻¹' K ∩ X.support = G ⁻¹' K ∩ X.support := by
      ext x
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hx, hxs⟩
        exact ⟨hG'eq (hsptr hxs) ▸ hx, hxs⟩
      · rintro ⟨hx, hxs⟩
        exact ⟨(hG'eq (hsptr hxs)).symm ▸ hx, hxs⟩
    rw [hEq]
    exact hGprop K hK
  obtain ⟨S', -, hS'im, hS'lim⟩ := hS5 m m' k X M θ ξ hT hθ hXτ G' L hG'Lip hG'prop
  -- 4. Eventually `dist (G x) (G_n x) < 1` on `spt X`, so `G_n` is proper on the closed `spt X`:
  -- `G_n⁻¹(K) ∩ spt X` is a closed subset of the compact `G⁻¹(cthickening 1 K) ∩ spt X`.
  have hsptClosed : IsClosed X.support := isClosed_univ.sdiff X.isOpen_zeroRegion
  have hprop_ev : ∀ᶠ n in atTop, ∀ K : Set (Eucl m'), IsCompact K →
      IsCompact (Gj n ⁻¹' K ∩ X.support) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconvO.mono hsptO) 1 one_pos] with n hn
    intro K hK
    refine (hGprop (cthickening 1 K) hK.cthickening).of_isClosed_subset
      ((hK.isClosed.preimage (hGjsmooth n).continuous).inter hsptClosed) ?_
    rintro x ⟨hxK, hxs⟩
    exact ⟨Metric.mem_cthickening_of_dist_le (G x) (Gj n x) 1 K hxK (hn x hxs).le, hxs⟩
  -- `Hᵏ(M ∖ spt X) = 0`: `Hᵏ`-a.e. point of `M` lies in `spt X`.
  have hnull := Submission.iwl_sp_rectifiable_support_null m k univ X M θ ξ hT hXτ
  have hspt : ∀ᵐ x ∂((μHE[k] : Measure (Eucl m)).restrict M), x ∈ X.support := by
    rw [ae_restrict_iff'₀ hT.nullMeasurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    by_contra hxX
    exact hx ⟨hxM, hxX⟩
  -- 5. `S(ω) = S'(ω)`: both are limits of `X(η_n) = I_n(ω)`.
  have hSeq : ∀ ω, S ω = S' ω := by
    intro ω
    -- `η_n` is compatible with `(G_n, ω)` near `spt X` whenever `G_n` is proper on `spt X`.
    have hex : ∀ n, ∃ η : TestFormOn (univ : Set (Eucl m)) k,
        (∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ X.support)) →
        ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
          (η : DifferentialForm (Eucl m) k) x =
            ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
              (fderiv ℝ (Gj n) x) := by
      intro n
      by_cases hp : ∀ K : Set (Eucl m'), IsCompact K → IsCompact (Gj n ⁻¹' K ∩ X.support)
      · obtain ⟨η, _ζ, N, hN, hAN, -, -, hηN, -⟩ :=
          Submission.iwl_sp_exists_compatible_testForm m m' k univ univ X.support (Gj n)
            isOpen_univ (subset_univ _) (hGjsmooth n) (fun K hK _ => hp K hK) ω
        exact ⟨η, fun _ => ⟨N, hN, hAN, hηN⟩⟩
      · exact ⟨0, fun h => absurd h hp⟩
    choose ηj hηj using hex
    have hcompat : ∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N,
        (ηj n : DifferentialForm (Eucl m) k) x =
          ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap
            (fderiv ℝ (Gj n) x) :=
      hprop_ev.mono fun n hn => hηj n hn
    -- `LipPF(X, G, S)` for the admissible `(G_n, O₀, Λ)`: `X(η_n) → S(ω)`.
    have hlim1 : Tendsto (fun n => X (ηj n)) atTop (𝓝 (S ω)) :=
      hLipPF Gj (thickening (r / 2) X.support) (Λ : ℝ) isOpen_thickening hsptO hGjsmooth
        (Eventually.of_forall fun n x hx => hGjderiv n x hx) hconvO ω ηj hcompat
    -- Step 3 with `g_n = G_n` (`C^∞` maps are `C¹`): `I_n(ω) → S'(ω)`.
    have hlim2 := hS'lim Gj L (fun n => (hGjsmooth n).of_le (by exact_mod_cast le_top))
      hGjLip hGjconv ω
    -- Eventually `X(η_n) = I_n(ω)`: `η_n = (ω ∘ G_n) ∘ DG_n` on `N ⊇ spt X`, which carries
    -- `Hᵏ ⌞ M`, and `⟨(ω ∘ G_n) ∘ DG_n, ξ⟩ = ⟨ω ∘ G_n, (DG_n)_# ξ⟩` by definition.
    have hevEq : ∀ᶠ n in atTop, X (ηj n) = ∫ x in M, θ x * nVectorPushforward k
        (fderiv ℝ (Gj n) x) (ξ x) ((ω : DifferentialForm (Eucl m') k) (Gj n x))
          ∂(μHE[k] : Measure (Eucl m)) := by
      filter_upwards [hcompat] with n hn
      obtain ⟨N, -, hXN, hηN⟩ := hn
      rw [hXτ, tauAction]
      refine integral_congr_ae ?_
      filter_upwards [hspt] with x hxX
      rw [hηN x (hXN hxX)]
      rfl
    exact tendsto_nhds_unique hlim1 (hlim2.congr' (hevEq.mono fun n h => h.symm))
  -- `S` inherits the integer multiplicity representation of `S'`.
  obtain ⟨M', θ', ξ', hT', hθ', hS'τ⟩ := hS'im
  exact ⟨M', θ', ξ', hT', hθ', fun ω => (hSeq ω).trans (hS'τ ω)⟩

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
