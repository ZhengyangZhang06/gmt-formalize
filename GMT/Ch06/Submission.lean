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

/-- Integer `L¹` density of a top-dimensional integer multiplicity current (Simon Ch. 6, proof
of 5.1, (27)–(28)).  Let `X ∈ 𝒟ₙ(ℝⁿ)` be integer multiplicity with `M(X) < ∞` such that (H) every
representation `X = τ(M, θ, ξ)` has `M(X) = ∫_M θ dHⁿ` and `Hⁿ(M ∖ spt X) = 0`.  Then
`X(ω) = ∫ u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` for a Borel integer-valued `u ∈ L¹(ℝⁿ)` with `∫ |u| = M(X)` and
`u = 0` a.e. off `spt X`.  With `Δ = dx¹ ∧ ⋯ ∧ dxⁿ`, every `n`-covector is `α = α(e) Δ` and
`Δ(τ) = ±1` for orthonormal `τ`, so `⟨ω, ξ⟩ = ω_e s` with `s = ⟨Δ, ξ⟩ = ±1` `Hⁿ`-a.e. on `M`;
`u` is a Borel integer-valued version of `1_{M'} θ s`, `M' ⊆ M` a measurable core of `M`. -/
theorem Submission.fiw_tb_tda_density : ∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsIntegerMultiplicity X → X.mass < ∞ → (∀ (M : Set (Eucl (m + 1))) (θ : Eucl (m + 1) → ℝ) (ξ : Eucl (m + 1) → NVector (Eucl (m + 1)) (m + 1)), IsRectifiableTriple (univ : Set (Eucl (m + 1))) (m + 1) M θ ξ → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = tauAction (m + 1) M θ ξ ω) → X.mass = ∫⁻ x in M, ENNReal.ofReal (θ x) ∂(μHE[m + 1] : Measure (Eucl (m + 1))) ∧ (μHE[m + 1] : Measure (Eucl (m + 1))) (M \ X.support) = 0) → ∃ u : Eucl (m + 1) → ℝ, Measurable u ∧ (∀ x, ∃ k : ℤ, u x = k) ∧ Integrable u ∧ ∫⁻ x, ENNReal.ofReal |u x| = X.mass ∧ (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), x ∉ X.support → u x = 0) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  classical
  intro m X hX hXm hH
  let _ : MeasureSpace (Eucl (m + 1)) := measureSpaceOfInnerProductSpace
  have hvol : (μHE[m + 1] : Measure (Eucl (m + 1))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume (m + 1)
  -- Step 1: the integer multiplicity triple, with (H) giving `M(X) = ∫_M θ` and
  -- `Hⁿ(M ∖ spt X) = 0`.
  obtain ⟨M, θ, ξ, hT, hθ, hXT⟩ := hX
  obtain ⟨hmass, hsupp⟩ := hH M θ ξ hT hXT
  -- Step 2: a measurable core `M' ⊆ M` with `M' = M` a.e.
  obtain ⟨M', hM'M, hM'm, hM'ae⟩ :=
    (hvol ▸ hT.nullMeasurableSet : NullMeasurableSet M volume).exists_measurable_subset_ae_eq
  have hrM : volume.restrict M' = volume.restrict M := Measure.restrict_congr_set hM'ae
  -- Step 3: the determinant covector `Δ = dx¹ ∧ ⋯ ∧ dxⁿ`: every `n`-covector is `α(e) Δ`, and
  -- `Δ(τ) = ±1` for orthonormal `τ`.
  obtain ⟨Δ, hΔ, hΔτ⟩ : ∃ Δ : Covector (Eucl (m + 1)) (m + 1),
      (∀ (α : Covector (Eucl (m + 1)) (m + 1)) v,
        α v = α (fun i => EuclideanSpace.single i (1 : ℝ)) * Δ v) ∧
      ∀ τ : Fin (m + 1) → Eucl (m + 1), Orthonormal ℝ τ → Δ τ = 1 ∨ Δ τ = -1 := by
    have hdet : ∀ v, wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j) v =
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.det v := by
      intro v
      rw [wedgeCovectors_apply_det, Module.Basis.det_apply]
      congr 1
    have hb : ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis =
        fun i => EuclideanSpace.single i (1 : ℝ) := by
      funext i; simp
    refine ⟨wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj j), fun α v => ?_,
      fun τ hτ => ?_⟩
    · have := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis α.toAlternatingMap)
      simp only [AlternatingMap.smul_apply, ContinuousAlternatingMap.coe_toAlternatingMap,
        smul_eq_mul, hb] at this
      rw [hdet]; exact this
    · rw [hdet]
      have hsp := hτ.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)
      have := OrthonormalBasis.det_to_matrix_orthonormalBasis_real
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (OrthonormalBasis.mk hτ hsp.ge)
      rwa [OrthonormalBasis.coe_mk] at this
  -- Step 4: `s = ξ(·)(Δ) = ±1` a.e. on `M`.
  have hor : ∀ᵐ x ∂(volume.restrict M'), ξ x Δ = 1 ∨ ξ x Δ = -1 := by
    have h := hT.orients
    rw [hvol, ← hrM] at h
    filter_upwards [h] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    rcases hξ with h | h <;> rw [h]
    · exact hΔτ τ hτ
    · rcases hΔτ τ hτ with h' | h' <;> simp [h']
  -- Step 5: measurability of `θ`, `s` and `u₀ = 1_{M'} θ s`.
  have hθm : AEStronglyMeasurable θ (volume.restrict M') := by
    have hU : M' = ⋃ k : ℕ, M' ∩ closedBall 0 k := by
      rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
    rw [hU, aestronglyMeasurable_iUnion_iff]
    intro k
    have h := hT.integrableOn _ (isCompact_closedBall 0 k) (subset_univ _)
    rw [hvol] at h
    exact (h.mono_set (inter_subset_inter_left _ hM'M)).1
  have hsm : AEStronglyMeasurable (fun x => ξ x Δ) (volume.restrict M') := by
    have h := hT.aestronglyMeasurable
    rw [hvol, ← hrM] at h
    exact (ContinuousLinearMap.apply ℝ ℝ Δ).continuous.comp_aestronglyMeasurable h
  have hu₀m : AEStronglyMeasurable (M'.indicator (fun x => θ x * ξ x Δ)) volume :=
    (aestronglyMeasurable_indicator_iff hM'm).2 (hθm.mul hsm)
  -- Step 6: `u₀` is integer valued a.e.
  have hu₀Z : ∀ᵐ x ∂volume, M'.indicator (fun x => θ x * ξ x Δ) x ∈
      Set.range (Int.cast : ℤ → ℝ) := by
    filter_upwards [(ae_restrict_iff' hM'm).1 hor] with x hx
    by_cases hxM : x ∈ M'
    · rw [indicator_of_mem hxM]
      obtain ⟨k, hk⟩ := hθ x (hM'M hxM)
      rcases hx hxM with h1 | h1 <;> rw [h1, hk]
      · exact ⟨k, by simp⟩
      · exact ⟨-k, by simp⟩
    · rw [indicator_of_notMem hxM]; exact ⟨0, by simp⟩
  -- Step 7: the Borel integer-valued representative `u`.
  have hũm : Measurable (hu₀m.mk _) := hu₀m.stronglyMeasurable_mk.measurable
  obtain ⟨u, hu⟩ : ∃ u : Eucl (m + 1) → ℝ, u = fun x =>
      if hu₀m.mk _ x ∈ Set.range (Int.cast : ℤ → ℝ) then hu₀m.mk _ x else 0 := ⟨_, rfl⟩
  have hu_meas : Measurable u := by
    rw [hu]
    exact Measurable.ite (hũm (Set.countable_range _).measurableSet) hũm measurable_const
  have hu_Z : ∀ x, ∃ k : ℤ, u x = k := by
    intro x
    rw [hu]; dsimp only; split_ifs with h
    · obtain ⟨k, hk⟩ := h; exact ⟨k, hk.symm⟩
    · exact ⟨0, by simp⟩
  have hu_ae : u =ᵐ[volume] M'.indicator (fun x => θ x * ξ x Δ) := by
    filter_upwards [hu₀m.ae_eq_mk, hu₀Z] with x h1 h2
    rw [hu]; dsimp only; rw [← h1]; simp only [h2, ite_true]
  -- Step 8: `|u| = 1_{M'} θ` a.e., hence `∫ |u| = M(X)`.
  have habs : (fun x => ENNReal.ofReal |u x|) =ᵐ[volume]
      M'.indicator (fun x => ENNReal.ofReal (θ x)) := by
    filter_upwards [hu_ae, (ae_restrict_iff' hM'm).1 hor] with x h1 h2
    rw [h1]
    by_cases hxM : x ∈ M'
    · rw [indicator_of_mem hxM, indicator_of_mem hxM]
      rcases h2 hxM with h | h <;> rw [h]
      · rw [mul_one, abs_of_pos (hT.pos x (hM'M hxM))]
      · rw [mul_neg_one, abs_neg, abs_of_pos (hT.pos x (hM'M hxM))]
    · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, abs_zero, ENNReal.ofReal_zero]
  have hlint : ∫⁻ x, ENNReal.ofReal |u x| = X.mass := by
    rw [lintegral_congr_ae habs, lintegral_indicator hM'm, hrM, hmass, hvol]
  -- Step 9: integrability.
  have hu_int : Integrable u := by
    refine ⟨hu_meas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [hlint]
    exact hXm
  -- Step 10: `u = 0` a.e. off `spt X`.
  have hsupp' : ∀ᵐ x ∂volume, x ∉ X.support → u x = 0 := by
    have h0 : volume (M \ X.support) = 0 := hvol ▸ hsupp
    filter_upwards [hu_ae, measure_eq_zero_iff_ae_notMem.1 h0] with x hx1 hx2 hxs
    rw [hx1, indicator_of_notMem fun h => hx2 ⟨hM'M h, hxs⟩]
  refine ⟨u, hu_meas, hu_Z, hu_int, hlint, hsupp', fun ω => ?_⟩
  -- Step 11: the representation `X(ω) = ∫ u ω_e`, as `⟨ω, ξ⟩ = ω_e s` (Step 4).
  rw [hXT ω]
  unfold tauAction
  rw [hvol, ← hrM, ← integral_indicator hM'm]
  refine integral_congr_ae ?_
  filter_upwards [hu_ae] with x hx
  rw [hx]
  by_cases hxM : x ∈ M'
  · rw [indicator_of_mem hxM, indicator_of_mem hxM]
    have h : ξ x ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) =
        (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) * ξ x Δ := by
      rw [← smul_eq_mul, ← map_smul]; congr 1; ext v
      rw [hΔ ((ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x) v]; rfl
    rw [h]; ring
  · rw [indicator_of_notMem hxM, indicator_of_notMem hxM, zero_mul]
/-- An integer median of an integer-valued function on a set of positive finite measure (Simon
Ch. 6, proof of 5.1, (31): the choice of `β_F`).  With `A k = F ∩ {u ≤ k}`, `μ (A k)` increases
to `μ F = a` as `k → ∞` and decreases to `0` as `k → -∞` (continuity of `μ` from below and from
above), so there is a least integer `β` with `μ (A β) ≥ a/2`.  Then `μ (A (β - 1)) < a/2`, and since
`u` is integer-valued, `F ⊆ A (β - 1) ∪ (F ∩ {β ≤ u})`, which forces `μ (F ∩ {β ≤ u}) ≥ a/2`. -/
theorem Submission.fiw_tb_tda_im_median_exists :
    ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ),
      MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u →
      (∀ x, ∃ k : ℤ, u x = k) →
      ∃ β : ℤ, ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ β}) ∧
        ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | (β : ℝ) ≤ u x}) := by
  intro α _ μ F a u hF ha hμF hu hint
  -- Step 1: `A k = F ∩ {u ≤ k}` is measurable and monotone in `k`.
  set A : ℤ → Set α := fun k => F ∩ {x | u x ≤ k}
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k => hF.inter (measurableSet_le hu measurable_const)
  have hAmono : Monotone A := fun k l hkl x hx =>
    ⟨hx.1, show u x ≤ (l : ℝ) from (hx.2 : u x ≤ k).trans (Int.cast_le.mpr hkl)⟩
  have hhalf_pos : 0 < ENNReal.ofReal (a / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hhalf_lt : ENNReal.ofReal (a / 2) < ENNReal.ofReal a :=
    (ENNReal.ofReal_lt_ofReal_iff ha).mpr (by linarith)
  have hsum : ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]
  -- Step 2: `⋃ k, A k = F`, so `μ (A k) → μ F = ofReal a` and some `μ (A k₁) > ofReal (a / 2)`.
  have hUnion : (⋃ k, A k) = F := by
    refine Subset.antisymm (iUnion_subset fun k => inter_subset_left) fun x hx => ?_
    exact mem_iUnion.mpr ⟨⌈u x⌉, hx, show u x ≤ (⌈u x⌉ : ℝ) from Int.le_ceil _⟩
  have hlim_top : Tendsto (μ ∘ A) atTop (𝓝 (ENNReal.ofReal a)) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) hAmono
    rwa [hUnion, hμF] at this
  obtain ⟨k₁, hk₁⟩ := (hlim_top.eventually (lt_mem_nhds hhalf_lt)).exists
  -- Step 3: `⋂ j, A (-j) = ∅`, so `μ (A (-j)) → 0` and some `μ (A (-j₀)) < ofReal (a / 2)`.
  have hBanti : Antitone fun j : ℕ => A (-(j : ℤ)) :=
    fun j j' hjj' => hAmono (neg_le_neg (Int.ofNat_le.mpr hjj'))
  have hInter : (⋂ j : ℕ, A (-(j : ℤ))) = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have hx' : u x ≤ ((-((1 - ⌊u x⌋).toNat : ℤ) : ℤ) : ℝ) :=
      (mem_iInter.mp hx (1 - ⌊u x⌋).toNat).2
    have hj : -((1 - ⌊u x⌋).toNat : ℤ) < ⌊u x⌋ := by
      have := Int.self_le_toNat (1 - ⌊u x⌋)
      omega
    exact absurd hx' (not_le.mpr ((Int.cast_lt.mpr hj).trans_le (Int.floor_le _)))
  have hlim_bot : Tendsto (μ ∘ fun j : ℕ => A (-(j : ℤ))) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ) (fun j => (hAmeas _).nullMeasurableSet) hBanti
      ⟨0, ne_top_of_le_ne_top (hμF ▸ ENNReal.ofReal_ne_top) (measure_mono inter_subset_left)⟩
    rwa [hInter, measure_empty] at this
  obtain ⟨j₀, hj₀⟩ := (hlim_bot.eventually (gt_mem_nhds hhalf_pos)).exists
  -- Step 4: `β` is the least integer with `ofReal (a / 2) ≤ μ (A β)`; the set of such integers
  -- contains `k₁` and is bounded below by `-j₀`.
  obtain ⟨β, hβK, hβmin⟩ := Int.exists_least_of_bdd
    (P := fun k => ENNReal.ofReal (a / 2) ≤ μ (A k))
    ⟨-(j₀ : ℤ), fun k hk => not_lt.mp fun hlt =>
      lt_irrefl _ ((hk.trans (measure_mono (hAmono hlt.le))).trans_lt hj₀)⟩
    ⟨k₁, hk₁.le⟩
  -- Step 5: the first inequality is `β ∈ K`.
  refine ⟨β, hβK, ?_⟩
  -- Step 6: `μ (A (β - 1)) < ofReal (a / 2)` by minimality, and `F ⊆ A (β - 1) ∪ (F ∩ {β ≤ u})`
  -- as `u` is integer-valued; subadditivity and `a / 2 + a / 2 = a` give the second inequality.
  have hβ1 : μ (A (β - 1)) < ENNReal.ofReal (a / 2) := by
    by_contra h
    have := hβmin _ (not_lt.mp h)
    omega
  have hcover : F ⊆ A (β - 1) ∪ (F ∩ {x | (β : ℝ) ≤ u x}) := by
    intro x hx
    obtain ⟨k, hk⟩ := hint x
    rcases le_or_gt k (β - 1) with hkb | hkb
    · exact Or.inl ⟨hx, show u x ≤ ((β - 1 : ℤ) : ℝ) by rw [hk]; exact_mod_cast hkb⟩
    · exact Or.inr ⟨hx, show (β : ℝ) ≤ u x by rw [hk]; exact_mod_cast (show β ≤ k by omega)⟩
  by_contra hlt
  have h1 : μ F ≤ μ (A (β - 1)) + μ (F ∩ {x | (β : ℝ) ≤ u x}) :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have h2 := ENNReal.add_lt_add hβ1 (not_le.mp hlt)
  rw [hsum, ← hμF] at h2
  exact lt_irrefl _ (h1.trans_lt h2)
/-- **Size and support bounds for a median** (Simon Ch. 6, 5.1, (31) and (35)).  Let `c` be a
median of a measurable `u` on a measurable `F`: both `F ∩ {u ≤ c}` and `F ∩ {c ≤ u}` have measure
at least `a / 2`, where `a > 0`.  Then `|c| a ≤ 2 ∫_F |u| dμ`, and if `c ≠ 0` then `u` is not
`μ`-a.e. zero on `F`.  On the half-measure set `S = F ∩ {c ≤ u}` (if `c ≥ 0`) or
`S = F ∩ {u ≤ c}` (if `c < 0`) one has `|c| ≤ |u|`, and `u ≠ 0` when `c ≠ 0`. -/
theorem Submission.fiw_tb_tda_im_median_bounds : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a c : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → Measurable u → ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ c}) → ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | c ≤ u x}) → ENNReal.ofReal (|c| * a) ≤ 2 * ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ ∧ (c ≠ 0 → μ (F ∩ {x | u x ≠ 0}) ≠ 0) := by
  intro α _ μ F a c u hF ha hu hle hge
  -- A measurable `S ⊆ F` with `a / 2 ≤ μ S` on which `|c| ≤ |u|`, and `u ≠ 0` if `c ≠ 0`.
  obtain ⟨S, hSm, hSF, hSμ, hSabs, hSne⟩ : ∃ S : Set α, MeasurableSet S ∧ S ⊆ F ∧
      ENNReal.ofReal (a / 2) ≤ μ S ∧ (∀ x ∈ S, |c| ≤ |u x|) ∧ (c ≠ 0 → ∀ x ∈ S, u x ≠ 0) := by
    rcases le_or_gt 0 c with hc | hc
    · refine ⟨F ∩ {x | c ≤ u x}, hF.inter (measurableSet_le measurable_const hu),
        inter_subset_left, hge, fun x hx => ?_, fun hc0 x hx => ?_⟩
      · rw [abs_of_nonneg hc]
        exact (show c ≤ u x from hx.2).trans (le_abs_self _)
      · exact ((lt_of_le_of_ne hc (Ne.symm hc0)).trans_le (show c ≤ u x from hx.2)).ne'
    · refine ⟨F ∩ {x | u x ≤ c}, hF.inter (measurableSet_le hu measurable_const),
        inter_subset_left, hle, fun x hx => ?_, fun _ x hx => ?_⟩
      · rw [abs_of_neg hc]
        exact (neg_le_neg (show u x ≤ c from hx.2)).trans (neg_le_abs _)
      · exact ((show u x ≤ c from hx.2).trans_lt hc).ne
  refine ⟨?_, fun hc0 hnull => ?_⟩
  · -- (M1) `|c| (a / 2) ≤ |c| μ(S) = ∫_S |c| ≤ ∫_S |u| ≤ ∫_F |u|`; multiply by `2`.
    have hS : ENNReal.ofReal |c| * ENNReal.ofReal (a / 2) ≤ ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ :=
      calc ENNReal.ofReal |c| * ENNReal.ofReal (a / 2) ≤ ENNReal.ofReal |c| * μ S := by gcongr
        _ = ∫⁻ _ in S, ENNReal.ofReal |c| ∂μ := (setLIntegral_const S _).symm
        _ ≤ ∫⁻ x in S, ENNReal.ofReal |u x| ∂μ :=
          setLIntegral_mono' hSm fun x hx => ENNReal.ofReal_le_ofReal (hSabs x hx)
        _ ≤ ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ := lintegral_mono_set hSF
    calc ENNReal.ofReal (|c| * a) = 2 * (ENNReal.ofReal |c| * ENNReal.ofReal (a / 2)) := by
          rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul zero_le_two]
          congr 1
          ring
      _ ≤ 2 * ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ := by gcongr
  · -- (M2) `S ⊆ F ∩ {u ≠ 0}` would be null, but `0 < ofReal (a / 2) ≤ μ S`.
    have hSsub : S ⊆ F ∩ {x | u x ≠ 0} := fun x hx => ⟨hSF hx, hSne hc0 x hx⟩
    have hS0 : μ S = 0 := measure_mono_null hSsub hnull
    have hpos : 0 < ENNReal.ofReal (a / 2) := ENNReal.ofReal_pos.mpr (half_pos ha)
    exact (hpos.trans_le (hSμ.trans_eq hS0)).ne rfl
/-- Median minimization: if `c₀` is a median of `u` on `F` (each of `F ∩ {u ≤ c₀}` and
`F ∩ {u ≥ c₀}` has measure at least `a / 2`, where `μ F = a`), then `c₀` minimizes
`c ↦ ∫_F |u - c| dμ`. -/
theorem Submission.fiw_tb_tda_im_median_minimizes :
    ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a c₀ : ℝ) (u : α → ℝ),
      MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → IntegrableOn u F μ →
      ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | u x ≤ c₀}) →
      ENNReal.ofReal (a / 2) ≤ μ (F ∩ {x | c₀ ≤ u x}) →
      ∀ c : ℝ,
        ∫⁻ x in F, ENNReal.ofReal |u x - c₀| ∂μ ≤ ∫⁻ x in F, ENNReal.ofReal |u x - c| ∂μ := by
  intro α _ μ F a c₀ u hF ha hμF hu _ hle hge c
  -- (P2)–(P3): if `μ (F ∩ S) ≥ a / 2`, then `μ (F \ S) = a - μ (F ∩ S) ≤ a / 2 ≤ μ (F ∩ S)`.
  have half : ∀ S : Set α, MeasurableSet S → ENNReal.ofReal (a / 2) ≤ μ (F ∩ S) →
      μ (F \ S) ≤ μ (F ∩ S) := by
    intro S hS hS2
    have ha2 : (0 : ℝ) ≤ a / 2 := by linarith
    have hfin : μ (F ∩ S) ≠ ∞ := ne_top_of_le_ne_top (by rw [hμF]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
    have hsum : μ (F ∩ S) + μ (F \ S) ≤ μ (F ∩ S) + ENNReal.ofReal (a / 2) :=
      calc μ (F ∩ S) + μ (F \ S) = μ F := measure_inter_add_sdiff F hS
        _ = ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) := by
          rw [hμF, ← ENNReal.ofReal_add ha2 ha2, add_halves]
        _ ≤ μ (F ∩ S) + ENNReal.ofReal (a / 2) := by gcongr
    exact ((ENNReal.add_le_add_iff_left hfin).1 hsum).trans hS2
  -- Step 1 (comparison): for `d ≥ 0`, if `|u - c₀| + d ≤ |u - c|` on `S`, `|u - c₀| - d ≤ |u - c|`
  -- off `S` and `μ (F \ S) ≤ μ (F ∩ S)`, integrate over `F ∩ S` and `F \ S`.
  have key : ∀ (S : Set α) (d : ℝ), MeasurableSet S → 0 ≤ d → μ (F \ S) ≤ μ (F ∩ S) →
      (∀ x ∈ S, |u x - c₀| + d ≤ |u x - c|) → (∀ x ∉ S, |u x - c₀| - d ≤ |u x - c|) →
      ∫⁻ x in F, ENNReal.ofReal |u x - c₀| ∂μ ≤ ∫⁻ x in F, ENNReal.ofReal |u x - c| ∂μ := by
    intro S d hS hd hμS hin hout
    have hin' : ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ + ENNReal.ofReal d * μ (F ∩ S) ≤
        ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c| ∂μ :=
      calc ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ + ENNReal.ofReal d * μ (F ∩ S)
          = ∫⁻ x in F ∩ S, (ENNReal.ofReal |u x - c₀| + ENNReal.ofReal d) ∂μ := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c| ∂μ :=
          setLIntegral_mono' (hF.inter hS) fun x hx => by
            rw [← ENNReal.ofReal_add (abs_nonneg _) hd]
            exact ENNReal.ofReal_le_ofReal (hin x hx.2)
    have hout' : ∫⁻ x in F \ S, ENNReal.ofReal |u x - c₀| ∂μ ≤
        ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F ∩ S) :=
      calc ∫⁻ x in F \ S, ENNReal.ofReal |u x - c₀| ∂μ
          ≤ ∫⁻ x in F \ S, (ENNReal.ofReal |u x - c| + ENNReal.ofReal d) ∂μ :=
            setLIntegral_mono' (hF.diff hS) fun x hx =>
              (ENNReal.ofReal_le_ofReal (by linarith [hout x hx.2])).trans ENNReal.ofReal_add_le
        _ = ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F \ S) := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
        _ ≤ ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F ∩ S) := by
            gcongr
    calc ∫⁻ x in F, ENNReal.ofReal |u x - c₀| ∂μ
        = ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ +
            ∫⁻ x in F \ S, ENNReal.ofReal |u x - c₀| ∂μ :=
          (lintegral_inter_add_sdiff (fun x => ENNReal.ofReal |u x - c₀|) F hS).symm
      _ ≤ ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ +
            (∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ + ENNReal.ofReal d * μ (F ∩ S)) := by
          gcongr
      _ = (∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c₀| ∂μ + ENNReal.ofReal d * μ (F ∩ S)) +
            ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ := by
          ring
      _ ≤ ∫⁻ x in F ∩ S, ENNReal.ofReal |u x - c| ∂μ +
            ∫⁻ x in F \ S, ENNReal.ofReal |u x - c| ∂μ := by
          gcongr
      _ = ∫⁻ x in F, ENNReal.ofReal |u x - c| ∂μ :=
          lintegral_inter_add_sdiff (fun x => ENNReal.ofReal |u x - c|) F hS
  rcases le_or_gt c₀ c with hc | hc
  · -- Step 2: `c₀ ≤ c`; take `S = {u ≤ c₀}` and `d = c - c₀`.
    have hS : MeasurableSet {x | u x ≤ c₀} := measurableSet_le hu measurable_const
    refine key _ (c - c₀) hS (by linarith) (half _ hS hle) (fun x hx => ?_) (fun x hx => ?_)
    · have hx : u x ≤ c₀ := hx
      rw [abs_of_nonpos (show u x - c₀ ≤ 0 by linarith),
        abs_of_nonpos (show u x - c ≤ 0 by linarith)]
      linarith
    · have hx : c₀ < u x := not_le.1 hx
      rw [abs_of_pos (show 0 < u x - c₀ by linarith)]
      linarith [le_abs_self (u x - c)]
  · -- Step 3: `c < c₀`; take `S = {c₀ ≤ u}` and `d = c₀ - c`.
    have hS : MeasurableSet {x | c₀ ≤ u x} := measurableSet_le measurable_const hu
    refine key _ (c₀ - c) hS (by linarith) (half _ hS hge) (fun x hx => ?_) (fun x hx => ?_)
    · have hx : c₀ ≤ u x := hx
      rw [abs_of_nonneg (show 0 ≤ u x - c₀ by linarith),
        abs_of_nonneg (show 0 ≤ u x - c by linarith)]
      linarith
    · have hx : u x < c₀ := not_le.1 hx
      rw [abs_of_neg (show u x - c₀ < 0 by linarith)]
      linarith [neg_le_abs (u x - c)]
/-- **Mean deviation bound** (the comparison of `u` with its mean `ū = a⁻¹ ∫_F u dμ` on `F`,
`μ(F) = a`, in the integer-median step that feeds the Poincaré inequality, Simon Ch. 6, (32)).
For each `x`, `u(x) − ū = a⁻¹ ∫_F (u(x) − u(y)) dμ(y)`, so `|u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y)`;
integrating over `x ∈ F` gives `∫_F |u − ū| dμ ≤ a⁻¹ ∫_F ∫_F |u(x) − u(y)| dμ(y) dμ(x)`. -/
theorem Submission.fiw_tb_tda_im_mean_deviation : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → IntegrableOn u F μ → ∫⁻ x in F, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ∂μ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ := by
  intro α _ μ F a u _ ha hμF _ hint
  -- `μ(F) = a` is finite and its real value is `a`.
  have hfin : μ F ≠ ∞ := by rw [hμF]; exact ENNReal.ofReal_ne_top
  have hreal : μ.real F = a := by rw [measureReal_def, hμF, ENNReal.toReal_ofReal ha.le]
  have hainv : 0 < a⁻¹ := inv_pos.mpr ha
  -- Pointwise bound `|u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y)`, read in `ℝ≥0∞`.
  have hpt : ∀ x, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ≤
      ENNReal.ofReal a⁻¹ * ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ := by
    intro x
    -- `y ↦ u(x) − u(y)` is integrable on `F`: a constant minus `u`.
    have hc : IntegrableOn (fun _ : α => u x) F μ := integrableOn_const hfin
    have hsub : IntegrableOn (fun y => u x - u y) F μ := hc.sub hint
    -- `a⁻¹ ∫_F (u(x) − u(y)) dμ(y) = a⁻¹ (a u(x) − ∫_F u dμ) = u(x) − ū`.
    have hmean : u x - a⁻¹ * ∫ y in F, u y ∂μ = a⁻¹ * ∫ y in F, (u x - u y) ∂μ := by
      rw [integral_sub hc hint, setIntegral_const, hreal, smul_eq_mul, mul_sub,
        ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    -- `|∫_F f| ≤ ∫_F |f|` and `a⁻¹ > 0`.
    have habs : |u x - a⁻¹ * ∫ y in F, u y ∂μ| ≤ a⁻¹ * ∫ y in F, |u x - u y| ∂μ := by
      rw [hmean, abs_mul, abs_of_pos hainv]
      exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hainv.le
    calc ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ|
        ≤ ENNReal.ofReal (a⁻¹ * ∫ y in F, |u x - u y| ∂μ) := ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (∫ y in F, |u x - u y| ∂μ) :=
          ENNReal.ofReal_mul hainv.le
      _ = ENNReal.ofReal a⁻¹ * ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ := by
          rw [ofReal_integral_eq_lintegral_ofReal hsub.abs
            (Eventually.of_forall fun y => abs_nonneg _)]
  -- Integrate over `x ∈ F` and pull out the finite constant `ofReal a⁻¹`.
  calc ∫⁻ x in F, ENNReal.ofReal |u x - a⁻¹ * ∫ y in F, u y ∂μ| ∂μ
      ≤ ∫⁻ x in F, ENNReal.ofReal a⁻¹ * ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Integer medians** (Simon Ch. 6, proof of 5.1, (31) and (35), on an arbitrary measure
space).  If `μ(F) = a > 0` and `u` is measurable, integer-valued and integrable on `F`, some
integer `β` has `|β| a ≤ 2 ∫_F |u|`, `β ≠ 0 → μ(F ∩ {u ≠ 0}) ≠ 0` and
`∫_F |u - β| ≤ a⁻¹ ∫_F ∫_F |u(x) - u(y)| dμ(y) dμ(x)`.  Take an integer median `β`, i.e.
`μ(F ∩ {u ≤ β}) ≥ a/2` and `μ(F ∩ {u ≥ β}) ≥ a/2` (`fiw_tb_tda_im_median_exists`).  The first
two estimates hold for every median (`fiw_tb_tda_im_median_bounds`).  A median minimizes
`c ↦ ∫_F |u - c|` (`fiw_tb_tda_im_median_minimizes`), so comparing with the mean
`c = a⁻¹ ∫_F u` (`fiw_tb_tda_im_mean_deviation`) gives the third. -/
theorem Submission.fiw_tb_tda_integer_median : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (F : Set α) (a : ℝ) (u : α → ℝ), MeasurableSet F → 0 < a → μ F = ENNReal.ofReal a → Measurable u → (∀ x, ∃ k : ℤ, u x = k) → IntegrableOn u F μ → ∃ β : ℤ, ENNReal.ofReal (|(β : ℝ)| * a) ≤ 2 * ∫⁻ x in F, ENNReal.ofReal |u x| ∂μ ∧ (β ≠ 0 → μ (F ∩ {x | u x ≠ 0}) ≠ 0) ∧ ∫⁻ x in F, ENNReal.ofReal |u x - β| ∂μ ≤ ENNReal.ofReal a⁻¹ * ∫⁻ x in F, ∫⁻ y in F, ENNReal.ofReal |u x - u y| ∂μ ∂μ := by
  intro α _ μ F a u hF ha hμF hu hZ hui
  -- An integer median: `μ(F ∩ {u ≤ β}) ≥ a/2` and `μ(F ∩ {u ≥ β}) ≥ a/2`.
  obtain ⟨β, hle, hge⟩ := Submission.fiw_tb_tda_im_median_exists μ F a u hF ha hμF hu hZ
  -- (M1) and (M2) hold for every real median `c = β`.
  obtain ⟨hM1, hM2⟩ := Submission.fiw_tb_tda_im_median_bounds μ F a β u hF ha hu hle hge
  refine ⟨β, hM1, fun hβ => hM2 (Int.cast_ne_zero.mpr hβ), ?_⟩
  -- (M4): `∫_F |u - β| ≤ ∫_F |u - ū|` for the mean `ū = a⁻¹ ∫_F u`, then the mean deviation bound.
  exact (Submission.fiw_tb_tda_im_median_minimizes μ F a β u hF ha hμF hu hui hle hge
    (a⁻¹ * ∫ y in F, u y ∂μ)).trans
    (Submission.fiw_tb_tda_im_mean_deviation μ F a u hF ha hμF hu hui)
/-- Top-dimensional lattice cubes in `ℝⁿ`, `n = m + 1`, `ρ > 0`.  The only order embedding
`Fin n ↪o Fin n` is the identity, so `latticeFace ρ F` is the closed cube `ρ (F.1 + [0, 1]ⁿ)`:
it is closed, has volume `ρⁿ` and diameter at most `√n ρ`.  The hyperplanes `{xᵢ = ρ k}` are
null, the cubes cover `ℝⁿ` and two distinct cubes only meet inside these hyperplanes, so
lower integrals and integrals of integrable functions split as sums over the cubes. -/
theorem Submission.fiw_tb_tda_lattice_cubes :
    ∀ (m : ℕ) (ρ : ℝ), 0 < ρ →
      (∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
        {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)}) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F)) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1),
        volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1))) ∧
      (∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F, ∀ y ∈ latticeFace ρ F,
        dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) ∧
      (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) ∧
      (∀ g : Eucl (m + 1) → ℝ≥0∞, ∫⁻ x, g x =
        ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x) ∧
      ∀ f : Eucl (m + 1) → ℝ, Integrable f →
        ∫ x, f x = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x := by
  intro m ρ hρ
  -- (a) A strictly monotone self-map of the finite chain `Fin (m + 1)` is the identity.
  have ha : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j :=
    fun F _ => F.2.strictMono.apply_eq
  -- (b) Every coordinate lies in `range F.2`, so the face is the closed cube.
  have hb : ∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
      {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)} := by
    intro F
    have hr : ∀ i, i ∈ range F.2 := fun i => ⟨i, ha F i⟩
    ext x
    simp only [latticeFace, mem_ofPred_eq, hr, not_true_eq_false, true_implies, false_implies,
      and_true]
  -- The cube is the preimage of a box under the volume-preserving `WithLp.ofLp`.
  have hbox : ∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F =
      WithLp.ofLp ⁻¹' Icc (fun i => ρ * (F.1 i : ℝ)) (fun i => ρ * ((F.1 i : ℝ) + 1)) := by
    intro F
    rw [hb F]
    ext x
    simp [Pi.le_def, forall_and]
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  -- (c) The cube is measurable.
  have hc : ∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F) := by
    intro F
    rw [hbox F]
    exact hvol.measurable measurableSet_Icc
  -- (d) Its volume is `∏ᵢ ρ = ρ^(m + 1)`.
  have hd : ∀ F : LatticeFaceIndex (m + 1) (m + 1),
      volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1)) := by
    intro F
    rw [hbox F, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    have hside : ∀ i : Fin (m + 1), ρ * ((F.1 i : ℝ) + 1) - ρ * (F.1 i : ℝ) = ρ := fun i => by
      ring
    simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hρ.le]
  -- (e) Coordinates of two points of the cube differ by at most `ρ`.
  have he : ∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F,
      ∀ y ∈ latticeFace ρ F, dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ := by
    intro F x hx y hy
    rw [hb F] at hx hy
    have hcoord : ∀ i, dist (x i) (y i) ^ 2 ≤ ρ ^ 2 := by
      intro i
      refine pow_le_pow_left₀ dist_nonneg ?_ 2
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) * ρ ^ 2 := by
      calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin (m + 1), ρ ^ 2 :=
            Finset.sum_le_sum fun i _ => hcoord i
        _ = ((m + 1 : ℕ) : ℝ) * ρ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [EuclideanSpace.dist_eq]
    calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * ρ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hρ.le]
  -- (f) Each hyperplane `{xᵢ = ρ k}` is the `WithLp.ofLp`-preimage of a null hyperplane.
  have hf : ∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro k
    have hnull : (volume : Measure (Eucl (m + 1))) {x | x i = ρ * k} = 0 :=
      hvol.quasiMeasurePreserving.preimage_null
        (Measure.pi_hyperplane (fun _ : Fin (m + 1) => (volume : Measure ℝ)) i (ρ * k))
    rw [ae_iff]
    simpa using hnull
  -- A point of a cube off the hyperplanes determines the lattice point: `⌊xᵢ / ρ⌋ = F.1 i`.
  have hfloor : ∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (x : Eucl (m + 1)),
      x ∈ latticeFace ρ F → (∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) →
        ∀ i, ⌊x i / ρ⌋ = F.1 i := by
    intro F x hx hgood i
    rw [hb F] at hx
    obtain ⟨h1, h2⟩ := hx i
    have h3 : x i ≠ ρ * ((F.1 i + 1 : ℤ) : ℝ) := hgood i (F.1 i + 1)
    push_cast at h3
    have h4 : x i < ρ * ((F.1 i : ℝ) + 1) := lt_of_le_of_ne h2 h3
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hρ]
      linarith
    · rw [div_lt_iff₀ hρ]
      linarith
  -- The cubes cover `ℝ^(m + 1)`: `x` lies in the cube at `(⌊xᵢ / ρ⌋)ᵢ`.
  have hU : (⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    refine ⟨(fun i => ⌊x i / ρ⌋, OrderEmbedding.ofStrictMono id strictMono_id), ?_⟩
    rw [hb]
    intro i
    constructor
    · have h := Int.floor_le (x i / ρ)
      rw [le_div_iff₀ hρ] at h
      linarith
    · have h := Int.lt_floor_add_one (x i / ρ)
      rw [div_lt_iff₀ hρ] at h
      linarith
  -- Distinct cubes have distinct lattice points, so they only meet in the null hyperplanes.
  have hbad : (volume : Measure (Eucl (m + 1)))
      {x | ¬ ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k} = 0 := ae_iff.1 hf
  have hdisj : Pairwise (Function.onFun (AEDisjoint (volume : Measure (Eucl (m + 1))))
      fun F : LatticeFaceIndex (m + 1) (m + 1) => latticeFace ρ F) := by
    intro F G hFG
    refine measure_mono_null (fun x hx => ?_) hbad
    intro hgood
    have h2 : F.2 = G.2 := DFunLike.ext _ _ fun j => (ha F j).trans (ha G j).symm
    have h1 : F.1 ≠ G.1 := fun h => hFG (Prod.ext h h2)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact hi ((hfloor F x hx.1 hgood i).symm.trans (hfloor G x hx.2 hgood i))
  refine ⟨ha, hb, hc, hd, he, hf, ?_, ?_⟩
  -- (g) Lower integrals split over the countable, a.e. disjoint cover.
  · intro g
    calc ∫⁻ x, g x = ∫⁻ x in ⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F, g x := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x :=
          lintegral_iUnion₀ (fun F => (hc F).nullMeasurableSet) hdisj g
  -- (h) So do integrals of integrable functions.
  · intro f hfi
    calc ∫ x, f x = ∫ x in ⋃ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F, f x := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x :=
          integral_iUnion_ae (fun F => (hc F).nullMeasurableSet) hdisj (by
            rw [hU]
            exact hfi.integrableOn)

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
