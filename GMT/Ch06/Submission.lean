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
/-- Eilenberg finiteness: if `f : ℝ^N → ℝ^{m+1}` is Lipschitz and `E ⊆ ℝ^N` is Borel with
`H^{m+1}(E) < ∞`, then `E ∩ f⁻¹{y}` is finite for Lebesgue-a.e. `y ∈ ℝ^{m+1}`. -/
theorem Submission.rectifiability_bf_infinite_fibre_null : ∀ (N m : ℕ) (E : Set (Eucl N)) (f : Eucl N → Eucl (m + 1)) (K : ℝ≥0), MeasurableSet E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → LipschitzWith K f → (volume : Measure (Eucl (m + 1))) {y : Eucl (m + 1) | (E ∩ f ⁻¹' {y}).Infinite} = 0 := by
  intro N m E f K hE hEfin hf
  -- Step 1: `Lᵏ(f '' S) ≤ K ^ k * Hᵏ(S)` (`k = m + 1`), as `μHE[k] = volume` on `ℝᵏ`.
  have himage : ∀ S : Set (Eucl N), (volume : Measure (Eucl (m + 1))) (f '' S) ≤
      (K : ℝ≥0∞) ^ (m + 1) * μHE[m + 1] S := by
    intro S
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (m + 1) (hf.lipschitzOnWith (s := S))
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  -- Step 2: the dyadic cubes `g i ⁻¹' {z}`, `g i x = (⌊2 ^ i * x j⌋)_j`, are Borel, and two
  -- distinct points lie in distinct cubes for all large `i`.
  set g : ℕ → Eucl N → (Fin N → ℤ) := fun i x j => ⌊(2 : ℝ) ^ i * x j⌋ with hg
  have hQm : ∀ i z, MeasurableSet (g i ⁻¹' {z}) := by
    intro i z
    have hQ : g i ⁻¹' {z} =
        ⋂ j, (fun x : Eucl N => (2 : ℝ) ^ i * x j) ⁻¹' Ico (z j : ℝ) (z j + 1) := by
      ext x
      simp [hg, funext_iff, Int.floor_eq_iff]
    rw [hQ]
    exact MeasurableSet.iInter fun j =>
      (by fun_prop : Measurable fun x : Eucl N => (2 : ℝ) ^ i * x j) measurableSet_Ico
  have hsep : ∀ x x' : Eucl N, x ≠ x' → ∀ᶠ i in atTop, g i x ≠ g i x' := by
    intro x x' hne
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ x' j :=
      not_forall.1 fun h => hne (by ext j; exact h j)
    have hc : 0 < |x j - x' j| := abs_pos.2 (sub_ne_zero.2 hj)
    filter_upwards [((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const
      hc).eventually_ge_atTop 1] with i hi heq
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun heq j)
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i)] at h1
    linarith
  -- Step 3: `∑_z Hᵏ(E ∩ g i ⁻¹' {z}) = Hᵏ(E)`.
  have hsplit : ∀ i, ∑' z, (μHE[m + 1] : Measure (Eucl N)) (E ∩ g i ⁻¹' {z}) =
      μHE[m + 1] E := by
    intro i
    have hdisj : Pairwise (Function.onFun Disjoint fun z => E ∩ g i ⁻¹' {z}) := by
      intro z z' hzz'
      refine Set.disjoint_left.2 fun x hx hx' => hzz' ?_
      exact (show g i x = z from hx.2).symm.trans hx'.2
    have hU : (⋃ z, E ∩ g i ⁻¹' {z}) = E := by
      ext x
      simp
    rw [← measure_iUnion hdisj fun z => hE.inter (hQm i z), hU]
  -- Step 4: for Borel hulls `B i z ⊇ f '' (E ∩ g i ⁻¹' {z})`, the counts
  -- `n i = ∑_z 1_{B i z}` satisfy `∫ n i ≤ C := K ^ k * Hᵏ(E) < ∞`.
  set B : ℕ → (Fin N → ℤ) → Set (Eucl (m + 1)) :=
    fun i z => toMeasurable volume (f '' (E ∩ g i ⁻¹' {z})) with hB
  have hBm : ∀ i z, MeasurableSet (B i z) := fun i z => measurableSet_toMeasurable _ _
  set n : ℕ → Eucl (m + 1) → ℝ≥0∞ := fun i y => ∑' z, (B i z).indicator 1 y
  have hnm : ∀ i, Measurable (n i) := fun i =>
    Measurable.tsum fun z => measurable_one.indicator (hBm i z)
  set C : ℝ≥0∞ := (K : ℝ≥0∞) ^ (m + 1) * μHE[m + 1] E
  have hCfin : C < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hEfin
  have hint : ∀ i, ∫⁻ y, n i y ≤ C := by
    intro i
    calc ∫⁻ y, n i y = ∑' z, ∫⁻ y, (B i z).indicator 1 y :=
          lintegral_tsum fun z => (measurable_one.indicator (hBm i z)).aemeasurable
      _ = ∑' z, volume (f '' (E ∩ g i ⁻¹' {z})) := by
          congr 1; ext z; rw [lintegral_indicator_one (hBm i z), hB, measure_toMeasurable]
      _ ≤ ∑' z, (K : ℝ≥0∞) ^ (m + 1) * μHE[m + 1] (E ∩ g i ⁻¹' {z}) :=
          ENNReal.tsum_le_tsum fun z => himage _
      _ = C := by rw [ENNReal.tsum_mul_left, hsplit i]
  -- Step 5: over an infinite fibre, `M ≤ n i y` for all large `i`, since `M` points of the
  -- fibre eventually lie in `M` distinct cubes.
  have hlarge : ∀ y ∈ {y : Eucl (m + 1) | (E ∩ f ⁻¹' {y}).Infinite}, ∀ M : ℕ,
      ∀ᶠ i in atTop, (M : ℝ≥0∞) ≤ n i y := by
    intro y hy M
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hy M
    have hev : ∀ᶠ i in atTop, ∀ p ∈ T ×ˢ T, p.1 ≠ p.2 → g i p.1 ≠ g i p.2 := by
      refine (eventually_all_finset (T ×ˢ T)).2 fun p _ => ?_
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun i h => absurd hp h
      · exact (hsep p.1 p.2 hp).mono fun i hi _ => hi
    filter_upwards [hev] with i hi
    have hinj : InjOn (g i) T := by
      intro x hx x' hx' hxx'
      by_contra hne
      exact hi (x, x') (Finset.mem_product.2 ⟨hx, hx'⟩) hne hxx'
    calc (M : ℝ≥0∞) = ∑ z ∈ T.image (g i), (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_image_of_injOn hinj, hTcard, nsmul_one]
      _ = ∑ z ∈ T.image (g i), (B i z).indicator 1 y := by
          refine Finset.sum_congr rfl fun z hz => ?_
          obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.1 hz
          have hxE : x ∈ E ∩ f ⁻¹' {y} := hTsub (Finset.mem_coe.2 hxT)
          have hyB : y ∈ B i (g i x) := subset_toMeasurable _ _ ⟨x, ⟨hxE.1, rfl⟩, hxE.2⟩
          rw [indicator_of_mem hyB]
          rfl
      _ ≤ n i y := ENNReal.sum_le_tsum _
  -- Step 6: Fatou's lemma gives `∫ F ≤ C` for `F = liminf_i n i`, so `F < ∞` a.e.
  set F : Eucl (m + 1) → ℝ≥0∞ := fun y => liminf (fun i => n i y) atTop
  have hFm : Measurable F := Measurable.liminf hnm
  have hFint : ∫⁻ y, F y ≤ C :=
    (lintegral_liminf_le hnm).trans (liminf_le_of_frequently_le' (Frequently.of_forall hint))
  have hFae : ∀ᵐ y, F y < ∞ := ae_lt_top hFm (hFint.trans_lt hCfin).ne
  -- Step 7: the infinite fibres lie over the null set `{F = ∞}`.
  refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hFae)
  have hFy : F y = ∞ := by
    refine top_unique ?_
    rw [← ENNReal.iSup_natCast]
    exact iSup_le fun M => le_liminf_of_le (by isBoundedDefault) (hlarge y hy M)
  simp [hFy]
/-- **Conical density lemma for purely unrectifiable sets** (Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, 15.13–15.15; Hovila–Järvenpää–Järvenpää–Ledrappier,
arXiv:1104.3453, Lemma 2.2).  Let `k = m + 1`, `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩) ∈ ℝᵏ` and
`X_v(a,r,s) = {x : |x - a| < r, |L_v(x - a)| < s |x - a|}`.  If `E ⊆ ℝ^N` is purely
`k`-unrectifiable, the set of `a ∈ E` at which, for every `η > 0`, some aperture `s ∈ (0,1)`
gives `Hᵏ(E ∩ X_v(a,r,s)) ≤ η (r s)ᵏ` for all `r ∈ (0,δ)` is `Hᵏ`-null.  The three steps of the
proof (the conical density estimate, the uniform density bound forcing measure zero, and the
reduction to rational apertures) are local `have`s of this single declaration. -/
theorem Submission.rectifiability_bf_cone_density : ∀ (N m : ℕ) (E : Set (Eucl N)) (v : Fin (m + 1) → Eucl N) (δ : ℝ), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → 0 < δ → (μHE[m + 1] : Measure (Eucl N)) {a | a ∈ E ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))} = 0 := by
  -- Step 1(a) (Mattila 15.13): a set on which `L_v` is bi-Lipschitz lies in a Lipschitz image of `ℝᵏ`, hence is countably `k`-rectifiable, hence null in the purely unrectifiable `E`.
  have graph_null : ∀ (N m : ℕ) (E F : Set (Eucl N)) (v : Fin (m + 1) → Eucl N) (c : ℝ), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → F ⊆ E → 0 < c → (∀ a ∈ F, ∀ b ∈ F, c * ‖b - a‖ ≤ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖) → (μHE[m + 1] : Measure (Eucl N)) F = 0 := by
    classical
    intro N m E F v c hE hFE hc hbi
    let L : Eucl N → Eucl (m + 1) := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      ext i
      simp only [L, PiLp.sub_apply]
      rw [← inner_sub_right]
    have hinj : InjOn L F := by
      intro a ha b hb hab
      have h1 := hbi a ha b hb
      have h2 : L (b - a) = 0 := by rw [← hLsub, hab, sub_self]
      change c * ‖b - a‖ ≤ ‖L (b - a)‖ at h1
      rw [h2, norm_zero] at h1
      have h3 : ‖b - a‖ ≤ 0 := by nlinarith [norm_nonneg (b - a)]
      exact (sub_eq_zero.1 (norm_le_zero_iff.1 h3)).symm
    let g : Eucl (m + 1) → Eucl N := Function.invFunOn L F
    have hg : ∀ a ∈ F, g (L a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
    have hglip : LipschitzOnWith (Real.toNNReal c⁻¹) g (L '' F) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hg a ha, hg b hb, dist_eq_norm, dist_eq_norm, hLsub,
        Real.coe_toNNReal _ (inv_nonneg.2 hc.le)]
      have h1 : c * ‖a - b‖ ≤ ‖L (a - b)‖ := hbi b hb a ha
      rw [inv_mul_eq_div, le_div_iff₀ hc]
      linarith
    obtain ⟨G, hGlip, hGeq⟩ := hglip.extend_finite_dimension
    have hFrange : F ⊆ range G := fun a ha =>
      ⟨L a, (hGeq (mem_image_of_mem L ha)).symm.trans (hg a ha)⟩
    have hrect : CountablyRectifiable (m + 1) F :=
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hGlip).mono hFrange
    exact hE F hFE hrect
  -- Step 1(b), geometry: with `h = h(a)` and a partner `b` with `3h/4 < |b - a| ≤ h` in the `s/4`-cone, the cylinder `{|L_v(x - a)| < sh/4}` meets `F` inside `X_v(a,2h,s) ∪ X_v(b,2h,s)`.
  have two_cone_cover : ∀ (N m : ℕ) (v : Fin (m + 1) → Eucl N) (F : Set (Eucl N)) (a b : Eucl N) (s h : ℝ), 0 < s → (∀ c ∈ F, ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ < s / 4 * ‖c - a‖ → ‖c - a‖ ≤ h) → ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖ < s / 4 * ‖b - a‖ → 3 * h / 4 < ‖b - a‖ → ‖b - a‖ ≤ h → F ∩ {x | ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * h / 4} ⊆ {x | dist x a < 2 * h ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} ∪ {x | dist x b < 2 * h ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - b)) : Eucl (m + 1))‖ < s * ‖x - b‖} := by
    intro N m v F a b s h hs hmax hb1 hb2 hb3
    have hh : 0 < h := by linarith [norm_nonneg (b - a)]
    have hlin : ∀ c : Eucl N,
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - b)) : Eucl (m + 1)) =
          WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) +
            WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) := by
      intro c
      ext i
      simp only [PiLp.add_apply]
      rw [← inner_add_right]
      congr 1
      abel
    have hneg : ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) : Eucl (m + 1))‖ =
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (b - a)) : Eucl (m + 1))‖ := by
      rw [← norm_neg]
      congr 1
      ext i
      simp only [PiLp.neg_apply]
      rw [← inner_neg_right, neg_sub]
    rintro c ⟨hcF, hc⟩
    change ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ <
      s * h / 4 at hc
    have hca : ‖c - a‖ ≤ h := by
      by_contra hlt
      push Not at hlt
      have hin : ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ <
          s / 4 * ‖c - a‖ := by
        calc _ < s * h / 4 := hc
          _ < s / 4 * ‖c - a‖ := by nlinarith
      linarith [hmax c hcF hin]
    by_cases hfar : h / 4 ≤ ‖c - a‖
    · left
      refine ⟨by rw [dist_eq_norm]; linarith, ?_⟩
      calc _ < s * h / 4 := hc
        _ ≤ s * ‖c - a‖ := by nlinarith
    · right
      push Not at hfar
      have htri1 : ‖b - a‖ ≤ ‖c - b‖ + ‖c - a‖ := by
        calc ‖b - a‖ ≤ ‖b - c‖ + ‖c - a‖ := norm_sub_le_norm_sub_add_norm_sub b c a
          _ = ‖c - b‖ + ‖c - a‖ := by rw [norm_sub_rev b c]
      have htri2 : ‖c - b‖ ≤ ‖c - a‖ + ‖b - a‖ := by
        calc ‖c - b‖ ≤ ‖c - a‖ + ‖a - b‖ := norm_sub_le_norm_sub_add_norm_sub c a b
          _ = ‖c - a‖ + ‖b - a‖ := by rw [norm_sub_rev a b]
      have hcb1 : h / 2 < ‖c - b‖ := by linarith
      have hcb2 : ‖c - b‖ < 2 * h := by linarith
      refine ⟨by rw [dist_eq_norm]; exact hcb2, ?_⟩
      rw [hlin c]
      calc _ ≤ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (c - a)) : Eucl (m + 1))‖ +
            ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (a - b)) : Eucl (m + 1))‖ :=
            norm_add_le _ _
        _ < s * h / 4 + s / 4 * ‖b - a‖ := by rw [hneg]; linarith
        _ ≤ s * h / 2 := by nlinarith
        _ < s * ‖c - b‖ := by nlinarith
  -- Step 1(c): Vitali covering (factor `τ = 2`, so `5r` enlargements) of the projected balls in `ℝᵏ`, countability, and the volume packing bound `Σ ρᵏ ≤ (M + R)ᵏ`.
  have vitali_packing : ∀ (N m : ℕ) (A : Set (Eucl N)) (y : Eucl N → Eucl (m + 1)) (ρ : Eucl N → ℝ) (y₀ : Eucl (m + 1)) (R M : ℝ), (∀ a ∈ A, 0 < ρ a ∧ ρ a ≤ R) → (∀ a ∈ A, dist (y a) y₀ ≤ M) → ∃ I : Set (Eucl N), I ⊆ A ∧ I.Countable ∧ I.PairwiseDisjoint (fun b => ball (y b) (ρ b)) ∧ (∀ a ∈ A, ∃ b ∈ I, ball (y a) (ρ a) ⊆ ball (y b) (5 * ρ b)) ∧ ∑' b : I, ENNReal.ofReal (ρ b ^ (m + 1)) ≤ ENNReal.ofReal ((M + R) ^ (m + 1)) := by
    intro N m A y ρ y₀ R M hρ hy
    obtain ⟨u, huA, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a => ball (y a) (ρ a)) A ρ 2 one_lt_two (fun a ha => (hρ a ha).1.le) R
      (fun a ha => (hρ a ha).2) (fun a ha => nonempty_ball.2 (hρ a ha).1)
    have hucount : u.Countable := hudisj.countable_of_isOpen (fun a _ => isOpen_ball)
      (fun a ha => nonempty_ball.2 (hρ a (huA ha)).1)
    refine ⟨u, huA, hucount, hudisj, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hbu, ⟨z, hza, hzb⟩, hab⟩ := hucov a ha
      refine ⟨b, hbu, fun w hw => ?_⟩
      rw [mem_ball] at hw hza hzb ⊢
      calc dist w (y b) ≤ dist w (y a) + dist (y a) z + dist z (y b) := dist_triangle4 _ _ _ _
        _ < ρ a + ρ a + ρ b := by rw [dist_comm (y a) z]; linarith
        _ ≤ 5 * ρ b := by linarith
    · rcases u.eq_empty_or_nonempty with hu | ⟨b₀, hb₀⟩
      · subst hu
        simp
      have hR : 0 < R := (hρ b₀ (huA hb₀)).1.trans_le (hρ b₀ (huA hb₀)).2
      have hM : 0 ≤ M := dist_nonneg.trans (hy b₀ (huA hb₀))
      set μ : Measure (Eucl (m + 1)) := volume with hμ
      have hω0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
      have hωtop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
      have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
      have hsub : (⋃ b ∈ u, ball (y b) (ρ b)) ⊆ ball y₀ (M + R) := by
        intro w hw
        obtain ⟨b, hbu, hwb⟩ := mem_iUnion₂.1 hw
        rw [mem_ball] at hwb ⊢
        calc dist w y₀ ≤ dist w (y b) + dist (y b) y₀ := dist_triangle _ _ _
          _ < ρ b + M := by linarith [hy b (huA hbu)]
          _ ≤ M + R := by linarith [(hρ b (huA hbu)).2]
      have key : (∑' b : u, ENNReal.ofReal (ρ b ^ (m + 1))) * μ (ball 0 1) ≤
          ENNReal.ofReal ((M + R) ^ (m + 1)) * μ (ball 0 1) := by
        rw [← ENNReal.tsum_mul_right]
        calc ∑' b : u, ENNReal.ofReal (ρ b ^ (m + 1)) * μ (ball 0 1)
            = ∑' b : u, μ (ball (y b) (ρ b)) := by
              congr 1
              funext b
              rw [Measure.addHaar_ball_of_pos μ _ (hρ b (huA b.2)).1, hfin]
          _ = μ (⋃ b ∈ u, ball (y b) (ρ b)) :=
              (measure_biUnion hucount hudisj (fun b _ => measurableSet_ball)).symm
          _ ≤ μ (ball y₀ (M + R)) := measure_mono hsub
          _ = ENNReal.ofReal ((M + R) ^ (m + 1)) * μ (ball 0 1) := by
              rw [Measure.addHaar_ball μ _ (by linarith), hfin]
      exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key
  -- Step 1 (Mattila 15.14): the conical density estimate `Hᵏ(B ∩ B(x₀,δ′/6)) ≤ C₁ λ δ′ᵏ`, `C₁ = 2(20/3)ᵏ(‖L_v‖ + 1)ᵏ`.
  have conical_density_estimate : ∀ (N m : ℕ) (E : Set (Eucl N)) (v : Fin (m + 1) → Eucl N), Poincare.SimonGMT.Chapter03.PurelyUnrectifiable (m + 1) E → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (B : Set (Eucl N)) (s δ' l : ℝ), B ⊆ E → 0 < s → s < 1 → 0 < δ' → 0 ≤ l → (∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ δ' → (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (l * (r * s) ^ (m + 1))) → ∀ x₀ : Eucl N, (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₀ (δ' / 6)) ≤ ENNReal.ofReal (C₁ * l * δ' ^ (m + 1)) := by
    intro N m E v hE
    -- the linear map `L_v` and an operator-norm bound `Λ`
    let Lₗ : Eucl N →ₗ[ℝ] Eucl (m + 1) :=
      { toFun := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
        map_add' := fun x y => by
          ext i
          simp [inner_add_right]
        map_smul' := fun c x => by
          ext i
          simp [inner_smul_right] }
    let Lc : Eucl N →L[ℝ] Eucl (m + 1) := LinearMap.toContinuousLinearMap Lₗ
    let L : Eucl N → Eucl (m + 1) := fun x => WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x)
    have hLc : ∀ x, Lc x = L x := fun x => rfl
    set Λ : ℝ := ‖Lc‖ with hΛ
    have hΛ0 : 0 ≤ Λ := norm_nonneg _
    have hLsub : ∀ x y, L x - L y = L (x - y) := fun x y => by
      rw [← hLc, ← hLc, ← hLc]; exact (map_sub Lc x y).symm
    have hLbound : ∀ x, ‖L x‖ ≤ Λ * ‖x‖ := fun x => by
      rw [← hLc]; exact Lc.le_opNorm x
    have hL0 : L 0 = 0 := by rw [← hLc]; exact map_zero Lc
    refine ⟨2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1), by positivity, ?_⟩
    intro B s δ' l hBE hs0 hs1 hδ' hl hcone x₀
    set F : Set (Eucl N) := B ∩ ball x₀ (δ' / 6) with hFdef
    have hFB : F ⊆ B := inter_subset_left
    have hFE : F ⊆ E := hFB.trans hBE
    have hFdist : ∀ a ∈ F, ∀ b ∈ F, ‖b - a‖ < δ' / 3 := by
      intro a ha b hb
      have h1 : dist a x₀ < δ' / 6 := ha.2
      have h2 : dist b x₀ < δ' / 6 := hb.2
      rw [← dist_eq_norm]
      calc dist b a ≤ dist b x₀ + dist a x₀ := dist_triangle_right b a x₀
        _ < δ' / 6 + δ' / 6 := add_lt_add h2 h1
        _ = δ' / 3 := by ring
    -- the partition `F = F₀ ∪ F₁`
    set F₀ : Set (Eucl N) := {a | a ∈ F ∧ ∀ b ∈ F, s / 4 * ‖b - a‖ ≤ ‖L (b - a)‖} with hF₀def
    set F₁ : Set (Eucl N) := {a | a ∈ F ∧ ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖} with hF₁def
    have hFsplit : F ⊆ F₀ ∪ F₁ := by
      intro a ha
      by_cases h : ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖
      · exact Or.inr ⟨ha, h⟩
      · push Not at h
        exact Or.inl ⟨ha, h⟩
    -- (a) graph part
    have hF₀null : (μHE[m + 1] : Measure (Eucl N)) F₀ = 0 :=
      graph_null N m E F₀ v (s / 4) hE (fun a ha => hFE ha.1)
        (by positivity) (fun a ha b hb => ha.2 b hb.1)
    -- (b) the function `h`
    let hfun : Eucl N → ℝ := fun a =>
      sSup ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖})
    have hbdd : ∀ a ∈ F,
        BddAbove ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖}) := by
      intro a ha
      refine ⟨δ' / 3, ?_⟩
      rintro t ⟨b, hb, rfl⟩
      exact (hFdist a ha b hb.1).le
    have hS_le : ∀ a ∈ F, ∀ c ∈ F, ‖L (c - a)‖ < s / 4 * ‖c - a‖ → ‖c - a‖ ≤ hfun a := by
      intro a ha c hc hc'
      exact le_csSup (hbdd a ha) ⟨c, ⟨hc, hc'⟩, rfl⟩
    have hpos : ∀ a ∈ F₁, 0 < hfun a := by
      rintro a ⟨ha, b, hb, hlt⟩
      have hba : b ≠ a := by
        rintro rfl
        simp only [sub_self, hL0, norm_zero, mul_zero, lt_self_iff_false] at hlt
      have : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hba)
      exact this.trans_le (hS_le a ha b hb hlt)
    have hle : ∀ a ∈ F₁, hfun a ≤ δ' / 3 := by
      rintro a ⟨ha, b, hb, hlt⟩
      refine csSup_le ⟨‖b - a‖, ⟨b, ⟨hb, hlt⟩, rfl⟩⟩ ?_
      rintro t ⟨c, hc, rfl⟩
      exact (hFdist a ha c hc.1).le
    have hpartner : ∀ a ∈ F₁, ∃ b ∈ F, ‖L (b - a)‖ < s / 4 * ‖b - a‖ ∧
        3 * hfun a / 4 < ‖b - a‖ ∧ ‖b - a‖ ≤ hfun a := by
      intro a haF₁
      have hp := hpos a haF₁
      obtain ⟨ha, b, hb, hlt⟩ := haF₁
      have hne : ((fun b => ‖b - a‖) '' {b | b ∈ F ∧ ‖L (b - a)‖ < s / 4 * ‖b - a‖}).Nonempty :=
        ⟨‖b - a‖, ⟨b, ⟨hb, hlt⟩, rfl⟩⟩
      obtain ⟨t, ⟨c, hc, rfl⟩, htc⟩ := exists_lt_of_lt_csSup hne
        (show 3 * hfun a / 4 < hfun a by linarith)
      exact ⟨c, hc.1, hc.2, htc, hS_le a ha c hc.1 hc.2⟩
    -- two cones cover each cylinder
    have hcyl : ∀ a ∈ F₁, (μHE[m + 1] : Measure (Eucl N)) (F ∩ {x | ‖L (x - a)‖ < s * hfun a / 4}) ≤
        2 * ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) := by
      intro a haF₁
      obtain ⟨b, hbF, hb1, hb2, hb3⟩ := hpartner a haF₁
      have haF : a ∈ F := haF₁.1
      have hincl := two_cone_cover N m v F a b s (hfun a) hs0
        (hS_le a haF) hb1 hb2 hb3
      have h2h0 : 0 < 2 * hfun a := by linarith [hpos a haF₁]
      have h2hle : 2 * hfun a ≤ δ' := by linarith [hle a haF₁]
      calc (μHE[m + 1] : Measure (Eucl N)) (F ∩ {x | ‖L (x - a)‖ < s * hfun a / 4})
          ≤ (μHE[m + 1] : Measure (Eucl N))
              ((E ∩ {x | dist x a < 2 * hfun a ∧ ‖L (x - a)‖ < s * ‖x - a‖}) ∪
                (E ∩ {x | dist x b < 2 * hfun a ∧ ‖L (x - b)‖ < s * ‖x - b‖})) := by
            apply measure_mono
            intro x hx
            rcases hincl hx with h | h
            · exact Or.inl ⟨hFE hx.1, h⟩
            · exact Or.inr ⟨hFE hx.1, h⟩
        _ ≤ (μHE[m + 1] : Measure (Eucl N))
              (E ∩ {x | dist x a < 2 * hfun a ∧ ‖L (x - a)‖ < s * ‖x - a‖}) +
            (μHE[m + 1] : Measure (Eucl N))
              (E ∩ {x | dist x b < 2 * hfun a ∧ ‖L (x - b)‖ < s * ‖x - b‖}) :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) +
            ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) :=
            add_le_add (hcone a (hFB haF) _ h2h0 h2hle) (hcone b (hFB hbF) _ h2h0 h2hle)
        _ = 2 * ENNReal.ofReal (l * (2 * hfun a * s) ^ (m + 1)) := (two_mul _).symm
    -- (c) Vitali covering of the projected balls
    obtain ⟨I, hIF₁, hIcount, -, hIcover, hIsum⟩ :=
      vitali_packing N m F₁ L (fun a => s * hfun a / 20) (L x₀)
        (s * δ' / 60) (Λ * δ' / 6)
        (fun a ha => by
          have h1 := hpos a ha
          have h2 := hle a ha
          refine ⟨by positivity, ?_⟩
          calc s * hfun a / 20 ≤ s * (δ' / 3) / 20 := by gcongr
            _ = s * δ' / 60 := by ring)
        (fun a ha => by
          have hax : ‖a - x₀‖ < δ' / 6 := by
            have := ha.1.2
            rwa [mem_ball, dist_eq_norm] at this
          rw [dist_eq_norm, hLsub]
          calc ‖L (a - x₀)‖ ≤ Λ * ‖a - x₀‖ := hLbound _
            _ ≤ Λ * (δ' / 6) := mul_le_mul_of_nonneg_left hax.le hΛ0
            _ = Λ * δ' / 6 := by ring)
    -- (d) covering of `F`
    have hcover : F ⊆ F₀ ∪ ⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4}) := by
      intro a ha
      rcases hFsplit ha with h0 | h1
      · exact Or.inl h0
      · right
        obtain ⟨b, hbI, hsub⟩ := hIcover a h1
        have hmem : L a ∈ ball (L a) (s * hfun a / 20) := by
          have := hpos a h1
          exact mem_ball_self (by positivity)
        have hab := hsub hmem
        rw [mem_ball, dist_eq_norm, hLsub] at hab
        refine mem_iUnion₂.2 ⟨b, hbI, ha, ?_⟩
        show ‖L (a - b)‖ < s * hfun b / 4
        linarith
    -- (e) the estimate
    have hsum' : ∑' b : I, ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) ≤
        ENNReal.ofReal ((Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) := hIsum
    calc (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₀ (δ' / 6))
        = (μHE[m + 1] : Measure (Eucl N)) F := rfl
      _ ≤ (μHE[m + 1] : Measure (Eucl N))
            (F₀ ∪ ⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4})) := measure_mono hcover
      _ ≤ (μHE[m + 1] : Measure (Eucl N)) F₀ + (μHE[m + 1] : Measure (Eucl N))
            (⋃ b ∈ I, (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4})) := measure_union_le _ _
      _ ≤ 0 + ∑' b : I, (μHE[m + 1] : Measure (Eucl N))
            (F ∩ {x | ‖L (x - b)‖ < s * hfun b / 4}) := by
          rw [hF₀null]
          gcongr
          exact measure_biUnion_le _ hIcount _
      _ ≤ ∑' b : I, 2 * ENNReal.ofReal (l * (2 * hfun b * s) ^ (m + 1)) := by
          rw [zero_add]
          exact ENNReal.tsum_le_tsum fun b => hcyl b (hIF₁ b.2)
      _ = ∑' b : I, ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) := by
          congr 1
          funext b
          have hreal : 2 * l * 40 ^ (m + 1) * (s * hfun b / 20) ^ (m + 1) =
              2 * (l * (2 * hfun b * s) ^ (m + 1)) := by
            rw [show 2 * hfun b * s = 40 * (s * hfun b / 20) by ring, mul_pow]
            ring
          have h40 : (0 : ℝ) ≤ 2 * l * 40 ^ (m + 1) := mul_nonneg (mul_nonneg (by norm_num) hl) (by positivity)
          rw [← ENNReal.ofReal_mul h40, hreal, ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ∑' b : I, ENNReal.ofReal ((s * hfun b / 20) ^ (m + 1)) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * l * 40 ^ (m + 1)) *
            ENNReal.ofReal ((Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) := by gcongr
      _ = ENNReal.ofReal (2 * l * 40 ^ (m + 1) * (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)) :=
          (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) hl) (by positivity))).symm
      _ ≤ ENNReal.ofReal (2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1) * l * δ' ^ (m + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : Λ * δ' / 6 + s * δ' / 60 ≤ (Λ + 1) * δ' / 6 := by nlinarith
          have h2 : (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1) ≤ ((Λ + 1) * δ' / 6) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) h1 _
          calc 2 * l * 40 ^ (m + 1) * (Λ * δ' / 6 + s * δ' / 60) ^ (m + 1)
              ≤ 2 * l * 40 ^ (m + 1) * ((Λ + 1) * δ' / 6) ^ (m + 1) := by gcongr
            _ = 2 * (20 / 3) ^ (m + 1) * (Λ + 1) ^ (m + 1) * l * δ' ^ (m + 1) := by
                rw [show (Λ + 1) * δ' / 6 = (Λ + 1) * δ' * (1 / 6) by ring, mul_pow, mul_pow,
                  show (20 / 3 : ℝ) = 40 * (1 / 6) by norm_num, mul_pow]
                ring
  -- Step 2 (Mattila 6.2(1), uniform form): `Hᵏ(B ∩ B̄(x,ρ)) ≤ (c_k/2) ρᵏ` for `x ∈ B`, `ρ ≤ ρ₀` forces `Hᵏ(B) = 0`, where `μHE[k] = c_k • μH[k]`.
  have uniform_density_null : ∀ (N m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (B : Set (Eucl N)) (ρ₀ : ℝ), 0 < ρ₀ → (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → (μHE[m + 1] : Measure (Eucl N)) (B ∩ closedBall x ρ) ≤ ENNReal.ofReal (c * ρ ^ (m + 1))) → (μHE[m + 1] : Measure (Eucl N)) B = 0 := by
    intro N m
    set κ : ℝ≥0 := Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      (μH[((m + 1 : ℕ) : ℝ)] : Measure (EuclideanSpace ℝ (Fin (m + 1)))) with hκ
    have hκ0 : κ ≠ 0 := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (m + 1)
    have hκ0' : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0
    have hdef : ∀ S : Set (Eucl N), (μHE[m + 1] : Measure (Eucl N)) S =
        (κ : ℝ≥0∞) * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) S := by
      intro S
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have hκpos : (0 : ℝ) < κ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ0)
    refine ⟨(κ : ℝ) / 2, div_pos hκpos two_pos, ?_⟩
    intro B ρ₀ hρ₀ hB
    set c : ℝ := (κ : ℝ) / 2 with hc
    have hc0 : 0 < c := div_pos hκpos two_pos
    have : NullSingletonClass (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) :=
      Measure.nullSingletonClass_hausdorff (Eucl N) (by positivity)
    -- local claim on balls of radius `ρ₀ / 2`
    have hloc : ∀ x₁ ∈ B, (μHE[m + 1] : Measure (Eucl N)) (B ∩ ball x₁ (ρ₀ / 2)) = 0 := by
      intro x₁ hx₁
      set B' : Set (Eucl N) := B ∩ ball x₁ (ρ₀ / 2) with hB'
      have hfin : (μHE[m + 1] : Measure (Eucl N)) B' < ⊤ := by
        calc (μHE[m + 1] : Measure (Eucl N)) B'
            ≤ (μHE[m + 1] : Measure (Eucl N)) (B ∩ closedBall x₁ (ρ₀ / 2)) :=
              measure_mono (inter_subset_inter_right _ ball_subset_closedBall)
          _ ≤ ENNReal.ofReal (c * (ρ₀ / 2) ^ (m + 1)) :=
              hB x₁ hx₁ _ (by positivity) (by linarith)
          _ < ⊤ := ENNReal.ofReal_lt_top
      have hcov : ∀ t : ℕ → Set (Eucl N), B' ⊆ ⋃ n, t n →
          (∀ n, ediam (t n) ≤ ENNReal.ofReal ρ₀) →
          (μHE[m + 1] : Measure (Eucl N)) B' ≤
            ENNReal.ofReal c * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
        intro t ht hdiam
        have hterm : ∀ n, (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n) ≤
            ENNReal.ofReal c * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
          intro n
          rcases (B' ∩ t n).eq_empty_or_nonempty with he | ⟨x, hxB', hxt⟩
          · rw [he, measure_empty]
            exact zero_le
          · have hne : (t n).Nonempty := ⟨x, hxt⟩
            rw [iSup_pos hne]
            have hdfin : ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
            set d : ℝ := (ediam (t n)).toReal with hd
            have hdeq : ENNReal.ofReal d = ediam (t n) := ENNReal.ofReal_toReal hdfin
            have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
            have hdle : d ≤ ρ₀ := by
              rw [← ENNReal.ofReal_le_ofReal_iff hρ₀.le, hdeq]
              exact hdiam n
            have hpow : ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) = ENNReal.ofReal (d ^ (m + 1)) := by
              rw [← hdeq, ENNReal.rpow_natCast, ENNReal.ofReal_pow hd0]
            rw [hpow, ← ENNReal.ofReal_mul hc0.le]
            rcases hd0.eq_or_lt with hd0' | hdpos
            · have hsub : B' ∩ t n ⊆ {x} := by
                rintro z ⟨-, hz⟩
                have h1 : edist z x ≤ ediam (t n) := edist_le_ediam_of_mem hz hxt
                rw [← hdeq, ← hd0', ENNReal.ofReal_zero, nonpos_iff_eq_zero, edist_eq_zero] at h1
                exact h1
              calc (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n)
                  ≤ (μHE[m + 1] : Measure (Eucl N)) {x} := measure_mono hsub
                _ = 0 := by rw [hdef, measure_singleton, mul_zero]
                _ ≤ _ := zero_le
            · have hsub : B' ∩ t n ⊆ B ∩ closedBall x d := by
                rintro z ⟨hzB', hz⟩
                refine ⟨hzB'.1, ?_⟩
                rw [mem_closedBall, ← ENNReal.ofReal_le_ofReal_iff hd0, ← edist_dist, hdeq]
                exact edist_le_ediam_of_mem hz hxt
              exact (measure_mono hsub).trans (hB x hxB'.1 d hdpos hdle)
        calc (μHE[m + 1] : Measure (Eucl N)) B'
            ≤ (μHE[m + 1] : Measure (Eucl N)) (⋃ n, B' ∩ t n) := by
              refine measure_mono fun x hx => ?_
              obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hx)
              exact mem_iUnion.2 ⟨n, hx, hn⟩
          _ ≤ ∑' n, (μHE[m + 1] : Measure (Eucl N)) (B' ∩ t n) := measure_iUnion_le _
          _ ≤ ∑' n, ENNReal.ofReal c * ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) :=
              ENNReal.tsum_le_tsum hterm
          _ = ENNReal.ofReal c * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) :=
              ENNReal.tsum_mul_left
      have hc' : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc0).ne'
      have hle : (μHE[m + 1] : Measure (Eucl N)) B' ≤
          ENNReal.ofReal c * (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' := by
        have hinf : (μHE[m + 1] : Measure (Eucl N)) B' ≤ ENNReal.ofReal c *
            ⨅ (t : ℕ → Set (Eucl N)) (_ : B' ⊆ ⋃ n, t n)
              (_ : ∀ n, ediam (t n) ≤ ENNReal.ofReal ρ₀),
              ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (((m + 1 : ℕ) : ℝ)) := by
          rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top)]
          refine le_iInf fun t => le_iInf fun ht => le_iInf fun hdiam => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hc') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
          exact hcov t ht hdiam
        refine hinf.trans ?_
        gcongr
        rw [Measure.hausdorffMeasure_apply]
        exact le_iSup₂_of_le (ENNReal.ofReal ρ₀) (ENNReal.ofReal_pos.2 hρ₀) le_rfl
      rw [hdef] at hle hfin ⊢
      have hμHfin : (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.mul_top hκ0'] at hfin
        exact lt_irrefl _ hfin
      by_contra hne
      have hμH0 : (μH[((m + 1 : ℕ) : ℝ)] : Measure (Eucl N)) B' ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hκle : (κ : ℝ≥0∞) ≤ ENNReal.ofReal c := (ENNReal.mul_le_mul_iff_left hμH0 hμHfin).1 hle
      have hlt : ENNReal.ofReal c < κ := by
        rw [hc, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat]
        exact ENNReal.half_lt_self hκ0' ENNReal.coe_ne_top
      exact absurd hκle (not_le.2 hlt)
    -- globalize with a countable subcover
    obtain ⟨T, hTB, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable B
      (fun x => ball x (ρ₀ / 2)) (fun _ _ => isOpen_ball)
    have hcover : B ⊆ ⋃ x ∈ T, (B ∩ ball x (ρ₀ / 2)) := by
      intro z hz
      have hz' : z ∈ ⋃ x ∈ B, ball x (ρ₀ / 2) := mem_iUnion₂.2 ⟨z, hz, mem_ball_self (by positivity)⟩
      rw [← hTU] at hz'
      obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.1 hz'
      exact mem_iUnion₂.2 ⟨x, hxT, hz, hzx⟩
    exact measure_mono_null hcover ((measure_biUnion_null_iff hTc).2 fun x hx => hloc x (hTB hx))
  -- Step 3: rational apertures, then Steps 1 and 2 on each `B_q`.
  intro N m E v δ hE hδ
  obtain ⟨c, hc, hudn⟩ := uniform_density_null N m
  obtain ⟨C₁, hC₁, hcde⟩ := conical_density_estimate N m E v hE
  set η₀ : ℝ := c / (C₁ * 24 ^ (m + 1)) with hη₀
  have hη₀pos : 0 < η₀ := by positivity
  -- the sets `B_{s'}` for rational apertures `s'`
  set Bq : ℚ → Set (Eucl N) := fun q => {a | a ∈ E ∧ ∀ r ∈ Ioo (0 : ℝ) δ,
    (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
      ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
        (q : ℝ) * ‖x - a‖}) ≤ ENNReal.ofReal (2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1))} with hBq
  -- Step 3(a)
  have hsub : {a | a ∈ E ∧ ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ,
      (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
          s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))} ⊆
      ⋃ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) < 1), Bq q := by
    rintro a ⟨haE, ha⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := ha η₀ hη₀pos
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s / 2 < s by linarith)
    have hq0 : (0 : ℝ) < q := by linarith
    refine mem_iUnion₂.2 ⟨q, ⟨hq0, by linarith⟩, haE, fun r hr => ?_⟩
    calc (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            (q : ℝ) * ‖x - a‖})
        ≤ (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖}) := by
          refine measure_mono (inter_subset_inter_right _ fun x hx => ⟨hx.1, hx.2.trans_le ?_⟩)
          exact mul_le_mul_of_nonneg_right hq2.le (norm_nonneg _)
      _ ≤ ENNReal.ofReal (η₀ * (r * s) ^ (m + 1)) := hs r hr
      _ ≤ ENNReal.ofReal (2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have hr0 : 0 ≤ r := hr.1.le
          have h1 : (r * s) ^ (m + 1) ≤ (2 * (r * q)) ^ (m + 1) := by
            apply pow_le_pow_left₀ (by positivity)
            nlinarith
          calc η₀ * (r * s) ^ (m + 1) ≤ η₀ * (2 * (r * q)) ^ (m + 1) :=
                mul_le_mul_of_nonneg_left h1 hη₀pos.le
            _ = 2 ^ (m + 1) * η₀ * (r * q) ^ (m + 1) := by rw [mul_pow]; ring
  -- Step 3(b)
  have hnull : ∀ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < 1 → (μHE[m + 1] : Measure (Eucl N)) (Bq q) = 0 := by
    rintro q ⟨hq0, hq1⟩
    apply hudn (Bq q) (δ / 13) (by positivity)
    intro x hx ρ hρ hρle
    have hcd := hcde (Bq q) q (12 * ρ) (2 ^ (m + 1) * η₀) (fun a ha => ha.1) hq0 hq1
      (by positivity) (by positivity) (fun a ha r hr0 hrle => ha.2 r ⟨hr0, by linarith⟩) x
    calc (μHE[m + 1] : Measure (Eucl N)) (Bq q ∩ closedBall x ρ)
        ≤ (μHE[m + 1] : Measure (Eucl N)) (Bq q ∩ ball x (12 * ρ / 6)) :=
          measure_mono (inter_subset_inter_right _ (closedBall_subset_ball (by linarith)))
      _ ≤ ENNReal.ofReal (C₁ * (2 ^ (m + 1) * η₀) * (12 * ρ) ^ (m + 1)) := hcd
      _ = ENNReal.ofReal (c * ρ ^ (m + 1)) := by
          congr 1
          have h24 : (24 : ℝ) ^ (m + 1) = 2 ^ (m + 1) * 12 ^ (m + 1) := by
            rw [← mul_pow]; norm_num
          rw [hη₀, mul_pow, h24]
          field_simp
  apply measure_mono_null hsub
  refine measure_iUnion_null fun q => measure_iUnion_null fun hq => hnull q hq
/-- The upper limit of `f : ℝ → [0,∞]` at `0⁺` is computed along the radii `1/(n+1)`:
`limsup_{t→0⁺} f(t) = inf_{n ∈ ℕ} sup_{0<t<1/(n+1)} f(t)`.  The intervals `(0, ε)`, `ε > 0`, form
a basis of `𝓝[>] 0`, so the upper limit is `inf_{ε>0} sup_{(0,ε)} f`; each radius `1/(n+1)` is
admissible, and every `ε > 0` exceeds some `1/(n+1)`, below which the supremum is smaller. -/
theorem Submission.rectifiability_mickle_rado_limsup_eq_iInf :
    ∀ f : ℝ → ℝ≥0∞, limsup f (𝓝[>] (0 : ℝ)) =
      ⨅ n : ℕ, ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), f t := by
  intro f
  rw [(nhdsGT_basis (0 : ℝ)).limsup_eq_iInf_iSup]
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact iInf₂_le (1 / ((n : ℝ) + 1)) (by positivity)
  · refine le_iInf₂ fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine (iInf_le _ n).trans ?_
    exact biSup_mono fun t ht => ⟨ht.1, ht.2.trans hn⟩
theorem Submission.rectifiability_mickle_rado_sup_lsc : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))), (∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ')) → ∀ r : ℝ, LowerSemicontinuous (fun c : Eucl (m + 1) => ⨆ t ∈ Ioo (0 : ℝ) r, ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) := by
  intro m ψ hball r
  -- step 1: `c ↦ ψ (ball c τ)` is lower semicontinuous, by inner continuity on balls
  have hlsc : ∀ τ : ℝ, LowerSemicontinuous (fun c : Eucl (m + 1) => ψ (ball c τ)) := by
    intro τ c a ha
    change a < ψ (ball c τ) at ha
    rw [hball c τ] at ha
    obtain ⟨τ', hτ', hlt⟩ := lt_biSup_iff.1 ha
    filter_upwards [ball_mem_nhds c (sub_pos.2 hτ'.2)] with c' hc'
    refine hlt.trans_le (measure_mono ?_)
    intro z hz
    rw [mem_ball] at hz hc' ⊢
    calc dist z c' ≤ dist z c + dist c c' := dist_triangle _ _ _
      _ < τ' + (τ - τ') := by rw [dist_comm c c']; exact add_lt_add hz hc'
      _ = τ := by ring
  -- step 2: divide by the positive finite `tᵏ`, then take the supremum over `t ∈ (0, r)`
  apply lowerSemicontinuous_biSup
  intro t ht
  have hden : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht.1 _)).ne'
  exact (ENNReal.continuous_div_const _ hden).comp_lowerSemicontinuous (hlsc t)
    (fun _ _ h => ENNReal.div_le_div_right h _)
/-- Vitali covering estimate off a `ψ`-null closed set, a covering step for the Mickle–Radó
density theorem (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439).  If `K` is closed,
`ψ K = 0` and `ψ(B(z,τ)) ≤ C τᵏ` for `z ∈ K`, `0 < τ < r` (`k = m + 1`), then
`ψ(B(c₀,t)) · Lᵏ(B(0,1)) ≤ C 6ᵏ Lᵏ(B(c₀,2t) ∖ K)` for `c₀ ∈ K`, `0 < t`, `6t ≤ r`.  The balls
`B(z, d z)`, `d z = dist(z,K)`, `z ∈ B(c₀,t) ∖ K`, miss `K` and lie in `B(c₀,2t)`.  A disjoint
(hence countable) Vitali subfamily has `5`-fold enlargements covering `B(c₀,t) ∖ K`, and
`B(b, 5 d b) ⊆ B(z'_b, 6 d b)` for a nearest point `z'_b ∈ K` of `b`, where `6 d b < 6t ≤ r`. -/
theorem Submission.rectifiability_mickle_rado_vitali_bound : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ c₀ ∈ K, ∀ t : ℝ, 0 < t → 6 * t ≤ r → ψ (ball c₀ t) * (volume : Measure (Eucl (m + 1))) (ball 0 1) ≤ C * 6 ^ (m + 1) * (volume : Measure (Eucl (m + 1))) (ball c₀ (2 * t) \ K) := by
  intro m ψ K C r hK hψK hbound c₀ hc₀ t ht htr
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  set ω := μ (ball 0 1) with hω
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  have hKne : K.Nonempty := ⟨c₀, hc₀⟩
  -- step 1: `ψ(B(c₀,t)) ≤ ψ(B(c₀,t) ∖ K) + ψ(K) = ψ(B(c₀,t) ∖ K)`
  have h1 : ψ (ball c₀ t) ≤ ψ (ball c₀ t \ K) := by
    calc ψ (ball c₀ t) ≤ ψ ((ball c₀ t \ K) ∪ K) := measure_mono (fun x hx => by
          by_cases h : x ∈ K
          · exact Or.inr h
          · exact Or.inl ⟨hx, h⟩)
      _ ≤ ψ (ball c₀ t \ K) + ψ K := measure_union_le _ _
      _ = ψ (ball c₀ t \ K) := by rw [hψK, add_zero]
  set T := ball c₀ t \ K with hT
  -- step 2: on `T`, the radius `d z = dist(z, K)` satisfies `0 < d z ≤ dist(z, c₀) < t`
  set d : Eucl (m + 1) → ℝ := fun z => infDist z K with hd
  have hd_pos : ∀ z ∈ T, 0 < d z := fun z hz => (hK.notMem_iff_infDist_pos hKne).1 hz.2
  have hd_lt : ∀ z ∈ T, d z < t := fun z hz =>
    (infDist_le_dist_of_mem hc₀).trans_lt (mem_ball.1 hz.1)
  -- steps 3–4: a disjoint, hence countable, Vitali subfamily `u ⊆ T` with enlargement factor `5`
  obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    T (fun z => z) d t (fun z hz => (hd_lt z hz).le) 5 (by norm_num)
  have hu_count : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun z hz => ⟨z, mem_ball_self (hd_pos z (huT hz))⟩)
  -- step 5: recentre at nearest points `z' b ∈ K`, so that `T ⊆ ⋃_{b ∈ u} B(z' b, 6 d b)`
  have hnear : ∀ z, ∃ y ∈ K, infDist z K = dist z y := fun z => hK.exists_infDist_eq_dist hKne z
  choose z' hz'K hz'd using hnear
  have hcover : T ⊆ ⋃ b ∈ u, ball (z' b) (6 * d b) := by
    intro a ha
    obtain ⟨b, hbu, hab⟩ := hcov a ha
    have hab' : a ∈ ball b (5 * d b) := hab (mem_ball_self (hd_pos a ha))
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hab' ⊢
    have hbz : dist b (z' b) = d b := (hz'd b).symm
    calc dist a (z' b) ≤ dist a b + dist b (z' b) := dist_triangle _ _ _
      _ < 5 * d b + d b := by rw [hbz]; linarith
      _ = 6 * d b := by ring
  -- steps 6–7: as `0 < 6 d b < 6t ≤ r`, `ψ(T) ≤ ∑_{b ∈ u} C 6ᵏ (d b)ᵏ`
  have h2 : ψ T ≤ ∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
    calc ψ T ≤ ψ (⋃ b ∈ u, ball (z' b) (6 * d b)) := measure_mono hcover
      _ ≤ ∑' b : u, ψ (ball (z' b) (6 * d b)) := measure_biUnion_le ψ hu_count _
      _ ≤ ∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        have hb : (b : Eucl (m + 1)) ∈ T := huT b.2
        have hpos := hd_pos b hb
        have hlt := hd_lt b hb
        calc ψ (ball (z' b) (6 * d b)) ≤ C * ENNReal.ofReal ((6 * d b) ^ (m + 1)) :=
              hbound (z' b) (hz'K b) (6 * d b) ⟨by linarith, by linarith⟩
          _ = C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1)) := by
            rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
            simp [mul_assoc]
  -- step 8: for the disjoint balls `B(b, d b) ⊆ B(c₀,2t) ∖ K`,
  -- `∑_{b ∈ u} (d b)ᵏ ω = Lᵏ(⋃_{b ∈ u} B(b, d b)) ≤ Lᵏ(B(c₀,2t) ∖ K)`
  have h3 : ∑' b : u, ENNReal.ofReal ((d b) ^ (m + 1)) * ω ≤ μ (ball c₀ (2 * t) \ K) := by
    have heq : ∀ b : u,
        ENNReal.ofReal ((d b) ^ (m + 1)) * ω = μ (ball (b : Eucl (m + 1)) (d b)) := by
      intro b
      rw [Measure.addHaar_ball μ _ (hd_pos b (huT b.2)).le, hfin]
    simp_rw [heq]
    rw [← measure_biUnion hu_count hdisj (fun _ _ => measurableSet_ball)]
    apply measure_mono
    intro y hy
    obtain ⟨b, hbu, hyb⟩ := mem_iUnion₂.1 hy
    have hbT := huT hbu
    refine ⟨?_, ?_⟩
    · rw [mem_ball] at hyb ⊢
      have hbc := mem_ball.1 hbT.1
      have := hd_lt b hbT
      calc dist y c₀ ≤ dist y b + dist b c₀ := dist_triangle _ _ _
        _ < 2 * t := by linarith
    · intro hyK
      exact Set.disjoint_left.1 (disjoint_ball_infDist (x := b) (s := K)) hyb hyK
  -- step 9: combine, pulling the constants out of the sums
  calc ψ (ball c₀ t) * ω
      ≤ (∑' b : u, C * 6 ^ (m + 1) * ENNReal.ofReal ((d b) ^ (m + 1))) * ω := by
        gcongr; exact h1.trans h2
    _ = C * 6 ^ (m + 1) * ∑' b : u, ENNReal.ofReal ((d b) ^ (m + 1)) * ω := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, mul_assoc]
    _ ≤ C * 6 ^ (m + 1) * μ (ball c₀ (2 * t) \ K) := by gcongr

/-- Mickle–Radó density step (Mattila, Thm 18.5, step 3 with `ε ↓ 0`): if `ψ(B(z,τ)) ≤ C τᵏ`
for `z ∈ K`, `0 < τ < r`, where `K` is closed and `ψ(K) = 0`, then the upper `k`-density of `ψ`
vanishes at `Lᵏ`-a.e. point of `K`.  At a Lebesgue density point `c ∈ K` of `K`, the Vitali
estimate `ψ(B(c,t))·ω ≤ C·6ᵏ·Lᵏ(B(c,2t) ∖ K)` together with
`Lᵏ(B̄(c,2t) ∖ K) = (2t)ᵏ·ω·(1 − R_c(2t))`, `R_c(ρ) = Lᵏ(K ∩ B̄(c,ρ))/Lᵏ(B̄(c,ρ)) → 1`, gives
`ψ(B(c,t))/tᵏ ≤ C·12ᵏ·(1 − R_c(2t)) → 0`. -/
theorem Submission.rectifiability_mickle_rado_density_zero : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (K : Set (Eucl (m + 1))) (C : ℝ≥0∞) (r : ℝ), IsClosed K → ψ K = 0 → C ≠ ⊤ → 0 < r → (∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) r, ψ (ball z τ) ≤ C * ENNReal.ofReal (τ ^ (m + 1))) → ∀ᵐ c ∂((volume : Measure (Eucl (m + 1))).restrict K), limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) = 0 := by
  intro m ψ K C r hK hψK hC hr hbound
  set μ : Measure (Eucl (m + 1)) := volume with hμ
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ K, ae_restrict_mem hK.measurableSet]
    with c hc hcK
  apply Tendsto.limsup_eq
  set ω := μ (ball 0 1) with hω
  have hω0 : ω ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hωtop : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hfin : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  -- the density ratio at radius 2t
  have hR2 : Tendsto (fun t : ℝ => μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))
      (𝓝[>] 0) (𝓝 1) := by
    refine hc.comp ?_
    have h2 : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] (2 * 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_const.mul continuous_id).tendsto' _ _ rfl |>.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mem_Ioi.2 (by simpa using ht))
    simpa using h2
  have hlim : Tendsto (fun t : ℝ => C * 12 ^ (m + 1) *
      (1 - μ (K ∩ closedBall c (2 * t)) / μ (closedBall c (2 * t)))) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.sub tendsto_const_nhds hR2 (Or.inl ENNReal.one_ne_top)
    have h12 : C * 12 ^ (m + 1) ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.pow_ne_top (by norm_num))
    have h2 := ENNReal.Tendsto.const_mul (a := C * 12 ^ (m + 1)) h1 (Or.inr h12)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r / 6 by positivity)] with t ht
  have ht0 : 0 < t := ht.1
  have h0 := Submission.rectifiability_mickle_rado_vitali_bound m ψ K C r hK hψK hbound c hcK t ht0
    (by linarith [ht.2])
  -- measure of the complement in the closed ball
  set V := μ (closedBall c (2 * t)) with hV
  set A := μ (K ∩ closedBall c (2 * t)) with hA
  have hVball : V = ENNReal.ofReal ((2 * t) ^ (m + 1)) * ω := by
    rw [hV, Measure.addHaar_closedBall μ c (by positivity), hfin]
  have hV0 : V ≠ 0 := by
    rw [hVball]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hω0
  have hVtop : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hAle : A ≤ V := measure_mono inter_subset_right
  have hdiff : μ (ball c (2 * t) \ K) ≤ V * (1 - A / V) := by
    have hsplit : μ (closedBall c (2 * t) \ K) + A = V := by
      rw [hA, inter_comm]; exact measure_sdiff_add_inter _ hK.measurableSet
    have h1 : μ (ball c (2 * t) \ K) ≤ μ (closedBall c (2 * t) \ K) :=
      measure_mono (sdiff_subset_sdiff_left ball_subset_closedBall)
    have h2 : μ (closedBall c (2 * t) \ K) = V - A :=
      ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top hVtop hAle) hsplit
    have h3 : V * (1 - A / V) = V - A := by
      rw [ENNReal.mul_sub (fun _ _ => hVtop), mul_one, ENNReal.mul_div_cancel hV0 hVtop]
    rw [h3, ← h2]; exact h1
  -- conclude
  have hpowt : ENNReal.ofReal (t ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
  rw [ENNReal.div_le_iff_le_mul (Or.inl hpowt) (Or.inl ENNReal.ofReal_ne_top)]
  have h2t : ENNReal.ofReal ((2 * t) ^ (m + 1)) = 2 ^ (m + 1) * ENNReal.ofReal (t ^ (m + 1)) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  have key : ψ (ball c t) * ω ≤
      (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
    calc ψ (ball c t) * ω ≤ C * 6 ^ (m + 1) * μ (ball c (2 * t) \ K) := h0
      _ ≤ C * 6 ^ (m + 1) * (V * (1 - A / V)) := by gcongr
      _ = (C * 12 ^ (m + 1) * (1 - A / V) * ENNReal.ofReal (t ^ (m + 1))) * ω := by
        rw [hVball, h2t]
        have : (12 : ℝ≥0∞) ^ (m + 1) = 6 ^ (m + 1) * 2 ^ (m + 1) := by
          rw [← mul_pow]; norm_num
        rw [this]; ring
  exact (ENNReal.mul_le_mul_iff_left hω0 hωtop).1 key

/-- **Mickle–Radó density theorem** (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439;
Mattila, Thm 18.5).  Let `ψ` be an outer measure on `ℝᵏ`, `k = m + 1`, inner continuous on open
balls, and `D` a Borel set with `ψ(D) = 0`.  Then the upper density
`ϑ(c) = limsup_{t↓0} ψ(B(c,t))/tᵏ` lies in `{0, ∞}` at `Lᵏ`-a.e. point of `D`.  With
`g_n(c) = sup_{0<t<1/(n+1)} ψ(B(c,t))/tᵏ`, each `g_n` is lower semicontinuous and `ϑ = inf_n g_n`,
so `ϑ` is Borel.  The set `{c ∈ D : 0 < ϑ(c) < ∞}` is covered by the Borel sets
`S_n = {c ∈ D : (n+1)⁻¹ < ϑ(c), g_n(c) ≤ n+1}`.  If `Lᵏ(S_n) > 0`, a compact `K ⊆ S_n` with
`Lᵏ(K) > 0` has `ψ(K) = 0` and `ψ(B(z,τ)) ≤ (n+1)τᵏ` for `z ∈ K`, `0 < τ < 1/(n+1)`; hence
`ϑ = 0` at `Lᵏ`-a.e. point of `K`, contradicting `ϑ > (n+1)⁻¹` on `K`. -/
theorem Submission.rectifiability_mickle_rado : ∀ (m : ℕ) (ψ : OuterMeasure (Eucl (m + 1))) (D : Set (Eucl (m + 1))), (∀ (c : Eucl (m + 1)) (τ : ℝ), ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ')) → MeasurableSet D → ψ D = 0 → (volume : Measure (Eucl (m + 1))) {c | c ∈ D ∧ 0 < limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) < ⊤} = 0 := by
  intro m ψ D hball hD hψD
  let g : ℕ → Eucl (m + 1) → ℝ≥0∞ := fun n c =>
    ⨆ t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))
  let ϑ : Eucl (m + 1) → ℝ≥0∞ := fun c =>
    limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0)
  -- step 1: `ϑ = inf_n g_n` with every `g_n` lower semicontinuous, so `ϑ` is Borel
  have hϑ : ∀ c, ϑ c = ⨅ n, g n c := fun c =>
    Submission.rectifiability_mickle_rado_limsup_eq_iInf
      (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1)))
  have hg_meas : ∀ n, Measurable (g n) := fun n =>
    (Submission.rectifiability_mickle_rado_sup_lsc m ψ hball _).measurable
  have hϑ_meas : Measurable ϑ := by
    have h : ϑ = fun c => ⨅ n, g n c := funext hϑ
    rw [h]
    exact Measurable.iInf hg_meas
  have hg_anti : ∀ c, Antitone (fun n => g n c) := by
    intro c n n' hnn'
    apply biSup_mono
    intro t ht
    refine ⟨ht.1, lt_of_lt_of_le ht.2 ?_⟩
    have h1 : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
    gcongr
  -- step 2: `{c ∈ D : 0 < ϑ c < ∞} ⊆ ⋃_n S_n` for the Borel sets `S_n`
  let S : ℕ → Set (Eucl (m + 1)) := fun n =>
    {c | c ∈ D ∧ ((n : ℝ≥0∞) + 1)⁻¹ < ϑ c ∧ g n c ≤ (n : ℝ≥0∞) + 1}
  have hS_meas : ∀ n, MeasurableSet (S n) := by
    intro n
    exact hD.inter ((measurableSet_lt measurable_const hϑ_meas).inter
      (measurableSet_le (hg_meas n) measurable_const))
  have hsub : {c | c ∈ D ∧ 0 < limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) < ⊤} ⊆ ⋃ n, S n := by
    rintro c ⟨hcD, hpos, hfin⟩
    change ϑ c < ⊤ at hfin
    change 0 < ϑ c at hpos
    rw [hϑ c] at hfin
    obtain ⟨n₀, hn₀⟩ := iInf_lt_iff.1 hfin
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hn₀.ne
    obtain ⟨n₁, hn₁⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    set n := max n₀ (max N n₁) with hn
    refine mem_iUnion.2 ⟨n, hcD, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hn₁
      apply ENNReal.inv_le_inv.2
      have : n₁ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
      have : (n₁ : ℝ≥0∞) ≤ n := by exact_mod_cast this
      exact this.trans le_self_add
    · calc g n c ≤ g n₀ c := hg_anti c (le_max_left _ _)
        _ ≤ N := hN.le
        _ ≤ (n : ℝ≥0∞) := by
          have : N ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
          exact_mod_cast this
        _ ≤ (n : ℝ≥0∞) + 1 := le_self_add
  -- step 3: `Lᵏ(S_n) = 0`, via a compact `K ⊆ S_n` and the density-zero step on `K`
  have hS_null : ∀ n, (volume : Measure (Eucl (m + 1))) (S n) = 0 := by
    intro n
    by_contra hne
    obtain ⟨K, hKS, hKc, hKpos⟩ := (hS_meas n).exists_lt_isCompact (pos_iff_ne_zero.2 hne)
    have hψK : ψ K = 0 := measure_mono_null (fun x hx => (hKS hx).1) hψD
    have hbound : ∀ z ∈ K, ∀ τ ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ψ (ball z τ) ≤ ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (τ ^ (m + 1)) := by
      intro z hz τ hτ
      have h1 : ψ (ball z τ) / ENNReal.ofReal (τ ^ (m + 1)) ≤ g n z :=
        le_iSup₂ (f := fun t (_ : t ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))) =>
          ψ (ball z t) / ENNReal.ofReal (t ^ (m + 1))) τ hτ
      have h2 := h1.trans (hKS hz).2.2
      rwa [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.ofReal_pos.2 (pow_pos hτ.1 _)).ne')
        (Or.inl ENNReal.ofReal_ne_top)] at h2
    have hae := Submission.rectifiability_mickle_rado_density_zero m ψ K ((n : ℝ≥0∞) + 1)
      (1 / ((n : ℝ) + 1)) hKc.isClosed hψK (by simp) (by positivity) hbound
    obtain ⟨c, hcK, hc0⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hKpos.ne' hae
    have h3 : ((n : ℝ≥0∞) + 1)⁻¹ < ϑ c := (hKS hcK).2.1
    change _ < limsup _ _ at h3
    rw [hc0] at h3
    exact (ENNReal.not_lt_zero h3).elim
  exact measure_mono_null hsub (measure_iUnion_null hS_null)

/-- For an s-finite `μ` and measurable sets `G r s ⊆ Z × Y`, increasing in `s` and with
`G r s = ⋃_{0<r'<r} G r' s` for `r > 0`, the map
`z ↦ limsup_{s→0⁺} sup_{0<r<δ} μ{y | (z, y) ∈ G r s} / (r s)ᵏ` is measurable.  Each section
measure is measurable in `z` (Tonelli).  By continuity from below along rational `r' < r` the
supremum over `r` may be taken over rational `r`, and since `F(s) ≤ (s'/s)ᵏ F(s')` for
`0 < s ≤ s'`, the supremum over `s ∈ (0, ε)` may be taken over rational `s`.  Computing the upper
limit along the radii `1/(n+1)` then gives a countable `inf`–`sup` of measurable functions. -/
theorem Submission.rectifiability_bf_limsup_sup_measurable :
    ∀ (Z Y : Type) [MeasurableSpace Z] [MeasurableSpace Y] (k : ℕ) (μ : Measure Y) (δ : ℝ)
      (G : ℝ → ℝ → Set (Z × Y)), SFinite μ → (∀ r s, MeasurableSet (G r s)) →
      (∀ r s s', s ≤ s' → G r s ⊆ G r s') →
      (∀ r s, 0 < r → G r s = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' s) →
      Measurable (fun z : Z => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ,
        μ {y | (z, y) ∈ G r s} / ENNReal.ofReal ((r * s) ^ k)) (𝓝[>] 0)) := by
  intro Z Y _ _ k μ δ G hμ hG hmono hcont
  -- `g z r s` is the section measure and `F z s` the supremum over `r ∈ (0, δ)`
  let g : Z → ℝ → ℝ → ℝ≥0∞ := fun z r s => μ {y | (z, y) ∈ G r s}
  let F : Z → ℝ → ℝ≥0∞ := fun z s => ⨆ r ∈ Ioo (0 : ℝ) δ, g z r s / ENNReal.ofReal ((r * s) ^ k)
  show Measurable fun z => limsup (F z) (𝓝[>] 0)
  have hgm : ∀ r s, Measurable fun z => g z r s := fun r s =>
    measurable_measure_prodMk_left (hG r s)
  -- `G` is monotone in `r` on `(0, ∞)`
  have hGr : ∀ s r₁ r₂, 0 < r₁ → r₁ ≤ r₂ → G r₁ s ⊆ G r₂ s := by
    intro s r₁ r₂ h1 h12
    rcases h12.lt_or_eq with h | rfl
    · rw [hcont r₂ s (h1.trans h)]
      exact subset_biUnion_of_mem (u := fun r' => G r' s) ⟨h1, h⟩
    · exact le_rfl
  -- the supremum over `r` is a supremum over rational `r`
  have hFq : ∀ z s, 0 < s → F z s = ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
      g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := by
    intro z s hs
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      have hU : {y | (z, y) ∈ G r s} =
          ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, {y | (z, y) ∈ G (q.1 : ℝ) s} := by
        ext y
        simp only [mem_iUnion, mem_ofPred_eq]
        constructor
        · intro hy
          rw [hcont r s hr.1] at hy
          simp only [mem_iUnion] at hy
          obtain ⟨r', hr', hy'⟩ := hy
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr'.2
          exact ⟨⟨q, hr'.1.trans hq1, hq2⟩, hGr s r' q hr'.1 hq1.le hy'⟩
        · rintro ⟨q, hy⟩
          exact hGr s q r q.2.1 q.2.2.le hy
      have hdir : Directed (· ⊆ ·)
          (fun q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r} => {y | (z, y) ∈ G (q.1 : ℝ) s}) := by
        intro q₁ q₂
        refine ⟨⟨max q₁.1 q₂.1, ?_, ?_⟩, ?_, ?_⟩
        · exact lt_of_lt_of_le q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1)
        · rw [Rat.cast_max]; exact max_lt q₁.2.2 q₂.2.2
        · intro y hy
          exact hGr s q₁.1 _ q₁.2.1 (by exact_mod_cast le_max_left q₁.1 q₂.1) hy
        · intro y hy
          exact hGr s q₂.1 _ q₂.2.1 (by exact_mod_cast le_max_right q₁.1 q₂.1) hy
      have hgr : g z r s = ⨆ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}, g z (q.1 : ℝ) s := by
        show μ {y | (z, y) ∈ G r s} = _
        rw [hU]
        exact hdir.measure_iUnion
      rw [hgr, ENNReal.iSup_div]
      refine iSup_le fun q => ?_
      refine le_trans ?_ (le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ) =>
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k)) q.1 ⟨q.2.1, q.2.2.trans hr.2⟩)
      apply ENNReal.div_le_div_left
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (mul_pos q.2.1 hs).le
      exact mul_le_mul_of_nonneg_right q.2.2.le hs.le
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) => g z r s / ENNReal.ofReal ((r * s) ^ k))
        (q : ℝ) hq
  have hFm : ∀ s, 0 < s → Measurable fun z => F z s := by
    intro s hs
    have : (fun z => F z s) = fun z => ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) δ),
        g z q s / ENNReal.ofReal (((q : ℝ) * s) ^ k) := funext fun z => hFq z s hs
    rw [this]
    exact Measurable.iSup fun q => Measurable.iSup fun _ => (hgm q s).div_const _
  -- scaling in `s`: `F z s ≤ (s'/s)ᵏ F z s'` for `0 < s ≤ s'`
  have hscale : ∀ z s s', 0 < s → s ≤ s' → F z s ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
    intro z s s' hs hss'
    refine iSup₂_le fun r hr => ?_
    have hs' : 0 < s' := hs.trans_le hss'
    have h1 : g z r s ≤ g z r s' := measure_mono (fun y hy => hmono r s s' hss' hy)
    have hA : ENNReal.ofReal ((r * s') ^ k) =
        ENNReal.ofReal ((s' / s) ^ k) * ENNReal.ofReal ((r * s) ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
      congr 2
      field_simp
    have hc0 : ENNReal.ofReal ((s' / s) ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    calc g z r s / ENNReal.ofReal ((r * s) ^ k)
        ≤ g z r s' / ENNReal.ofReal ((r * s) ^ k) := ENNReal.div_le_div_right h1 _
      _ = ENNReal.ofReal ((s' / s) ^ k) * (g z r s' / ENNReal.ofReal ((r * s') ^ k)) := by
          rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal ((s' / s) ^ k) * F z s' := by
          gcongr
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            g z r s' / ENNReal.ofReal ((r * s') ^ k)) r hr
  -- the supremum over `s ∈ (0, ε)` is a supremum over rational `s`
  have hsupq : ∀ z (ε : ℝ), 0 < ε → ⨆ s ∈ Ioo (0 : ℝ) ε, F z s =
      ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
    intro z ε hε
    apply le_antisymm
    · refine iSup₂_le fun s hs => ?_
      have hn : ∀ n : ℕ, F z s ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
          ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
        intro n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        have hlt : s < min ε (s * (1 + 1 / ((n : ℝ) + 1))) := by
          refine lt_min hs.2 ?_
          have := mul_pos hs.1 hpos
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        have hqε : (q : ℝ) < ε := hq2.trans_le (min_le_left _ _)
        have hq0 : 0 < (q : ℝ) := hs.1.trans hq1
        calc F z s ≤ ENNReal.ofReal (((q : ℝ) / s) ^ k) * F z q := hscale z s q hs.1 hq1.le
          _ ≤ ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k) *
              ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q := by
            gcongr ?_ * ?_
            · apply ENNReal.ofReal_le_ofReal
              apply pow_le_pow_left₀ (div_pos hq0 hs.1).le
              rw [div_le_iff₀ hs.1]
              have := hq2.trans_le (min_le_right _ _)
              linarith
            · exact le_iSup₂ (f := fun (q : ℚ) (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε) => F z q) q
                ⟨hq0, hqε⟩
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 + 1 / ((n : ℝ) + 1)) ^ k)) atTop
          (𝓝 1) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.tendsto_ofReal
        have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1).pow k
        simpa using this
      have htend := ENNReal.Tendsto.mul_const h1
        (Or.inl one_ne_zero) (b := ⨆ q : ℚ, ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) ε), F z q)
      rw [one_mul] at htend
      exact ge_of_tendsto' htend hn
    · refine iSup_le fun q => iSup_le fun hq => ?_
      exact le_iSup₂ (f := fun s (_ : s ∈ Ioo (0 : ℝ) ε) => F z s) (q : ℝ) hq
  -- the upper limit along the radii `1/(n+1)`, with rational `s`
  have hform : ∀ z, limsup (F z) (𝓝[>] 0) = ⨅ n : ℕ, ⨆ q : ℚ,
      ⨆ (_ : (q : ℝ) ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))), F z q := by
    intro z
    rw [Submission.rectifiability_mickle_rado_limsup_eq_iInf (F z)]
    congr 1
    funext n
    exact hsupq z _ (by positivity)
  rw [funext hform]
  exact Measurable.iInf fun n => Measurable.iSup fun q => Measurable.iSup fun hq => hFm q hq.1
/-- The parameter set of fibre witnesses (alternative T3 of the Besicovitch–Federer trichotomy in
the proof of Simon Ch. 6, 8.1) is Borel.  For `E ⊆ ℝ^N` σ-compact, `δ ∈ ℝ` and
`L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`), the set `W` of `(a, v)` admitting `x ∈ E` with
`x ≠ a`, `|x − a| < δ` and `L_v x = L_v a` is measurable.  With `E = ⋃ₙ Kₙ`, `Kₙ` compact,
`W = ⋃_{n,l} π(C_{n,l})`, where `π(x, (a, v)) = (a, v)` and `C_{n,l}` is the compact set of
`(x, (a, v))` with `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)` and
`L_v x = L_v a`. -/
theorem Submission.rectifiability_bf_witness_set_measurable : (∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → MeasurableSet {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))}) := by
  intro N m E δ hE
  -- `E = ⋃ₙ Kₙ` with every `Kₙ` compact.
  obtain ⟨K, hK, hKE⟩ := hE
  -- `(x, (a, v)) ↦ L_v x` and `(x, (a, v)) ↦ L_v a` are continuous.
  have hLc : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner continuous_fst
  have hLc' : Continuous (fun q : Eucl N × (Eucl N × (Fin (m + 1) → Eucl N)) =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp (continuous_snd.comp continuous_snd)).inner
      (continuous_fst.comp continuous_snd)
  -- `C_{n,l}`: `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)`, `L_v x = L_v a`.
  let C : ℕ → ℕ → Set (Eucl N × (Eucl N × (Fin (m + 1) → Eucl N))) := fun n l =>
    (K n ×ˢ closedBall (0 : Eucl N × (Fin (m + 1) → Eucl N)) l) ∩
      ({q | 1 / ((l : ℝ) + 1) ≤ dist q.1 q.2.1} ∩ {q | dist q.1 q.2.1 ≤ δ - 1 / ((l : ℝ) + 1)} ∩
        {q | (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.1) : Eucl (m + 1)) =
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.2.2 i) q.2.1) : Eucl (m + 1))})
  -- A compact set intersected with closed conditions is compact.
  have hCc : ∀ n l, IsCompact (C n l) := by
    intro n l
    refine ((hK n).prod (isCompact_closedBall _ _)).inter_right ?_
    refine ((isClosed_le continuous_const ?_).inter (isClosed_le ?_ continuous_const)).inter
      (isClosed_eq hLc hLc')
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
    · exact continuous_fst.dist (continuous_fst.comp continuous_snd)
  -- `W = ⋃_{n,l} π(C_{n,l})`, choosing `l` by the Archimedean property.
  have key : {p : Eucl N × (Fin (m + 1) → Eucl N) | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) =
        (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))} =
      ⋃ n, ⋃ l : ℕ, Prod.snd '' C n l := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨x, hxE, hxa, hxδ, hL⟩
      rw [← hKE, mem_iUnion] at hxE
      obtain ⟨n, hn⟩ := hxE
      have hd0 : 0 < dist x p.1 := dist_pos.2 hxa
      have hmin : 0 < min (dist x p.1) (δ - dist x p.1) := lt_min hd0 (by linarith)
      obtain ⟨l₁, hl₁⟩ := exists_nat_one_div_lt hmin
      obtain ⟨l₂, hl₂⟩ := exists_nat_ge ‖p‖
      refine ⟨n, max l₁ l₂, (x, p), ?_, rfl⟩
      have hle : 1 / ((max l₁ l₂ : ℕ) + 1 : ℝ) ≤ 1 / ((l₁ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (l₁ : ℝ) ≤ ((max l₁ l₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left l₁ l₂
        linarith
      have h1 := lt_of_le_of_lt hle hl₁
      refine ⟨⟨hn, ?_⟩, ⟨?_, ?_⟩, hL⟩
      · rw [mem_closedBall, dist_zero_right]
        exact hl₂.trans (by exact_mod_cast le_max_right l₁ l₂)
      · exact (h1.trans_le (min_le_left _ _)).le
      · have := h1.trans_le (min_le_right _ _)
        simp only [mem_ofPred_eq]
        linarith
    · rintro ⟨n, l, q, ⟨⟨hq1, -⟩, ⟨hd1, hd2⟩, hL⟩, rfl⟩
      refine ⟨q.1, ?_, ?_, ?_, hL⟩
      · rw [← hKE]; exact mem_iUnion.2 ⟨n, hq1⟩
      · intro h
        have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq, h, dist_self] at hd1
        linarith
      · have : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
        simp only [mem_ofPred_eq] at hd2
        linarith
  -- Each `π(C_{n,l})` is compact, hence Borel; so is the countable union.
  rw [key]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun l =>
    ((hCc n l).image continuous_snd).measurableSet

/-- **Borel measurability of the cone ratio** (step 2(a)–(c) of the Besicovitch–Federer
trichotomy, Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 18.9).  For
`v ∈ (ℝ^N)^k`, `k = m + 1`, let `L_v y = (⟨v₁, y⟩, …, ⟨v_k, y⟩)` and
`X_v(a, r, s) = {x : |x - a| < r, |L_v (x - a)| < s |x - a|}`.  Then
`Φ(a, v) = limsup_{s → 0⁺} sup_{0 < r < δ} μ(X_v(a, r, s)) / (rs)ᵏ` is measurable in `(a, v)`:
the cones are the sections of `G(r, s) = {((a, v), x) : |x - a| < r, |L_v (x - a)| < s |x - a|}`,
which is open, monotone in `s` and left continuous in `r`, so `limsup_sup_measurable` applies. -/
theorem Submission.rectifiability_bf_cone_ratio_measurable : ∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ), SFinite μ → Measurable (fun p : Eucl N × (Fin (m + 1) → Eucl N) => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) := by
  intro N m μ δ hμ
  -- Step 1: the cone `X_v(a, r, s)` is the section of `G(r, s)` at `z = (a, v)`.
  refine Submission.rectifiability_bf_limsup_sup_measurable (Eucl N × (Fin (m + 1) → Eucl N))
    (Eucl N) (m + 1) μ δ (fun r s => {q | dist q.2 q.1.1 < r ∧
      ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) : Eucl (m + 1))‖ <
        s * ‖q.2 - q.1.1‖}) hμ ?_ ?_ ?_
  -- Step 2: `G(r, s)` is open (strict inequalities between continuous functions), hence
  -- measurable in the second-countable product.
  · intro r s
    have hL : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N =>
        ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (q.1.2 i) (q.2 - q.1.1)) :
          Eucl (m + 1))‖ :=
      continuous_norm.comp ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
        ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).inner
          (continuous_snd.sub (continuous_fst.comp continuous_fst))))
    have hd : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N => dist q.2 q.1.1 :=
      by fun_prop
    have hn : Continuous fun q : (Eucl N × (Fin (m + 1) → Eucl N)) × Eucl N =>
        s * ‖q.2 - q.1.1‖ := by fun_prop
    exact ((isOpen_lt hd continuous_const).inter (isOpen_lt hL hn)).measurableSet
  -- Step 3: `G(r, s)` is monotone in `s`, as `s |x - a| ≤ s' |x - a|` for `s ≤ s'`.
  · intro r s s' hss' q hq
    exact ⟨hq.1, hq.2.trans_le (by gcongr)⟩
  -- Step 4: `G(r, s) = ⋃_{0 < r' < r} G(r', s)`; for `|x - a| < r` take `r' = (|x - a| + r) / 2`.
  · intro r s hr
    ext q
    simp only [mem_iUnion, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 q.1.1 + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨-, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
/-- Cone-ratio dichotomy.  Write `L x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`),
`X(r, s) = {x : |x − a| < r, |L(x − a)| < s|x − a|}` and
`Φ = limsup_{s→0⁺} sup_{0<r<δ} μ(X(r, s))/(rs)ᵏ`.  If `Φ = 0`, then for each `η > 0` some
`s ∈ (0, 1)` has `μ(X(r, s)) ≤ η(rs)ᵏ` for all `r ∈ (0, δ)`.  If `Φ = ∞`, then
`X(r, s) ⊆ L⁻¹(B̄(La, rs))`, so the push-forward `L_# μ` has infinite upper `k`-density at
`La`: its density quotients at the radii `rs → 0⁺` are unbounded. -/
theorem Submission.rectifiability_bf_cone_ratio_reduction :
    (∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (v : Fin (m + 1) → Eucl N),
      (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = 0 →
        ∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∧
      (limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧
          ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ <
            s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) = ⊤ →
        dimensionalUpperDensity (Measure.map (fun x : Eucl N =>
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) μ).toOuterMeasure
          ((m + 1 : ℕ) : ℝ) univ
          (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤)) := by
  intro N m μ δ a v
  -- `X r s` is the cone, `F s` the supremum of the ratios `μ(X r s)/(rs)ᵏ` over `r ∈ (0, δ)`
  set X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧
    ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}
  set F : ℝ → ℝ≥0∞ := fun s =>
    ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1)) with hF
  constructor
  · -- `Φ = 0`: eventually `F s < η`; take such an `s ∈ (0, 1)`
    intro h0 η hη
    have hlt : limsup F (𝓝[>] 0) < ENNReal.ofReal η := by
      rw [h0]; exact ENNReal.ofReal_pos.2 hη
    obtain ⟨s, hs1, hs2⟩ :=
      ((eventually_lt_of_limsup_lt hlt).and (Ioo_mem_nhdsGT one_pos)).exists
    refine ⟨s, hs2, fun r hr => ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos (mul_pos hr.1 hs2.1) _
    have h3 : μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1)) < ENNReal.ofReal η :=
      (le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
        μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))) r hr).trans_lt hs1
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 hpos).ne') (Or.inl ENNReal.ofReal_ne_top)]
      at h3
    rw [ENNReal.ofReal_mul hη.le]
    exact h3.le
  · -- `Φ = ∞`: ratios above `b ω_k` at `r < δ`, small `s` give density quotients above `b` at `rs`
    intro htop
    set L : Eucl N → Eucl (m + 1) := fun x =>
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) with hL
    have hLc : Continuous L :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_const.inner continuous_id)
    have hLsub : ∀ x y, L x - L y = L (x - y) := by
      intro x y
      simp only [hL, ← WithLp.toLp_sub]
      congr 1
      funext i
      simp [inner_sub_right]
    set ω := Poincare.SimonGMT.Chapter01.realUnitBallVolume (((m + 1 : ℕ) : ℝ)) with hω
    have hω0 : ω ≠ 0 := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      refine (ENNReal.ofReal_pos.2 (div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
        (Real.Gamma_pos_of_pos ?_))).ne'
      positivity
    have hωt : ω ≠ ⊤ := by
      rw [hω, Poincare.SimonGMT.Chapter01.realUnitBallVolume]
      exact ENNReal.ofReal_ne_top
    -- `δ > 0`, since otherwise `F = 0` and `Φ = 0`
    have hδ : 0 < δ := by
      by_contra hδ
      have hF0 : F = fun _ => 0 := by
        funext s
        rw [hF, Ioo_eq_empty (not_lt.2 (not_lt.1 hδ))]
        simp
      rw [hF0, limsup_const] at htop
      exact ENNReal.zero_ne_top htop
    unfold dimensionalUpperDensity
    refine ENNReal.eq_top_of_forall_nnreal_le fun b => ?_
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    rw [(nhdsGT_basis (0 : ℝ)).frequently_iff]
    intro ρ₀ hρ₀
    have hΛ : (b : ℝ≥0∞) * ω < limsup F (𝓝[>] 0) := by
      rw [htop]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.2 hωt)
    obtain ⟨s, hs1, hs2⟩ := ((frequently_lt_of_lt_limsup (by isBoundedDefault) hΛ).and_eventually
      (Ioo_mem_nhdsGT (div_pos hρ₀ hδ))).exists
    obtain ⟨r, hr, hrs⟩ := lt_biSup_iff.1 hs1
    have hrs0 : 0 < r * s := mul_pos hr.1 hs2.1
    have hrsρ : r * s < ρ₀ := by
      have h1 : r * s < δ * (ρ₀ / δ) := mul_lt_mul'' hr.2 hs2.2 hr.1.le hs2.1.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at h1
    refine ⟨r * s, ⟨hrs0, hrsρ⟩, ?_⟩
    have hpos : 0 < (r * s) ^ (m + 1) := pow_pos hrs0 _
    -- the cone lies in the preimage of the closed ball `B̄(La, rs)`
    have hsub : X r s ⊆ L ⁻¹' closedBall (L a) (r * s) := by
      intro x hx
      simp only [mem_preimage, mem_closedBall, dist_eq_norm, hLsub]
      have h1 : ‖x - a‖ < r := by rw [← dist_eq_norm]; exact hx.1
      calc ‖L (x - a)‖ ≤ s * ‖x - a‖ := hx.2.le
        _ ≤ s * r := by gcongr; exact hs2.1.le
        _ = r * s := mul_comm _ _
    have hmap :
        μ (X r s) ≤ (Measure.map L μ).toOuterMeasure (univ ∩ closedBall (L a) (r * s)) := by
      rw [Measure.coe_toOuterMeasure, univ_inter,
        Measure.map_apply hLc.measurable isClosed_closedBall.measurableSet]
      exact measure_mono hsub
    unfold Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
    rw [ENNReal.ofReal_rpow_of_nonneg hrs0.le (by positivity), Real.rpow_natCast,
      ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 (ENNReal.ofReal_pos.2 hpos).ne'))
        (Or.inl (ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top))]
    refine le_trans ?_ hmap
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at hrs
    rw [← mul_assoc]
    exact hrs.le
/-- Cones versus unions of coordinate fibres (step 4 of the Besicovitch–Federer trichotomy,
Mattila 18.9, used for Simon Ch. 6, 8.1).  Let `k = m + 1`, `L_u(y) = (⟨u₁, y⟩, …, ⟨u_k, y⟩)`,
`X_u(a, r, s) = {x : |x − a| < r, |L_u(x − a)| < s|x − a|}`, `u ⊕_j c = (uᵢ + cᵢ e_j)ᵢ` and
`K_j(t) = {x ≠ a : L_{u ⊕_j c}(x − a) = 0 for some |c| < t}`.  With
`Φ = limsup_{s → 0⁺} sup_{0<r<δ} μ(X_u(a, r, s))/(rs)ᵏ` and
`ϑ_j = limsup_{t → 0⁺} sup_{0<r<δ} μ(B(a, r) ∩ K_j(t))/(rt)ᵏ`, we have `ϑ_j ≤ Φ` for every `j`
and `Φ ≤ (√N)ᵏ Σ_j ϑ_j`.  Since `L_{u ⊕_j c}(y) = L_u(y) + y_j c`,
`B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` and `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(√N s)`. -/
theorem Submission.rectifiability_bf_fibre_cone_comparison :
    ∀ (N m : ℕ) (μ : Measure (Eucl N)) (δ : ℝ) (a : Eucl N) (u : Fin (m + 1) → Eucl N), (∀ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ≤ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)) ∧ limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) := by
  intro N m μ δ a u
  -- `L = L_u`, `K j t = K_j(t)`, `X r s = X_u(a, r, s)`, `F = F`, `Fj j = F_j`.
  let L : Eucl N → Eucl (m + 1) := fun y => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let K : Fin N → ℝ → Set (Eucl N) := fun j t => {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t,
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let X : ℝ → ℝ → Set (Eucl N) := fun r s => {x | dist x a < r ∧ ‖L (x - a)‖ < s * ‖x - a‖}
  let F : ℝ → ℝ≥0∞ := fun s => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
  let Fj : Fin N → ℝ → ℝ≥0∞ := fun j t => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ K j t) / ENNReal.ofReal ((r * t) ^ (m + 1))
  show (∀ j, limsup (Fj j) (𝓝[>] 0) ≤ limsup F (𝓝[>] 0)) ∧
    limsup F (𝓝[>] 0) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, limsup (Fj j) (𝓝[>] 0)
  -- Step 1, fibre identity: `L_{u ⊕_j c}(y) = L_u(y) + y_j c`.
  have hfib : ∀ (j : Fin N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) : Eucl (m + 1)) =
        L y + (y j) • c := by
    intro j c y
    ext i
    simp [L, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  -- Step 2, inclusion (ii): `B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` for `t > 0`.
  have hincl2 : ∀ (j : Fin N) (r t : ℝ), 0 < t → ball a r ∩ K j t ⊆ X r t := by
    rintro j r t ht x ⟨hxr, hxa, c, hc, hx0⟩
    refine ⟨hxr, ?_⟩
    rw [hfib] at hx0
    have hL : L (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left hx0
    rw [hL, norm_neg, norm_smul]
    have hy : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hxa)
    have hc' : ‖c‖ < t := by simpa using hc
    have hyj : ‖(x - a) j‖ ≤ ‖x - a‖ := PiLp.norm_apply_le _ _
    calc ‖(x - a) j‖ * ‖c‖ ≤ ‖x - a‖ * ‖c‖ := by gcongr
      _ < ‖x - a‖ * t := mul_lt_mul_of_pos_left hc' hy
      _ = t * ‖x - a‖ := mul_comm _ _
  refine ⟨fun j => ?_, ?_⟩
  -- Step 3: `F_j ≤ F` on `(0, ∞)`, hence `ϑ_j ≤ Φ`.
  · refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine iSup₂_mono fun r hr => ?_
    exact ENNReal.div_le_div_right (measure_mono (hincl2 j r t ht)) _
  · rcases Nat.eq_zero_or_pos N with hN | hN
    -- Step 4: for `N = 0` every cone is empty, so `Φ = 0`.
    · subst hN
      have hF0 : F = fun _ => 0 := by
        funext s
        have hX : ∀ r, X r s = ∅ := by
          intro r
          ext x
          have hxa : x - a = 0 := Subsingleton.elim _ _
          simp [X, hxa]
        simp [F, hX]
      rw [hF0, limsup_const]
      exact zero_le
    · set σ : ℝ := Real.sqrt (N : ℝ) with hσdef
      have hσ : 0 < σ := Real.sqrt_pos.2 (by exact_mod_cast hN)
      have hσsq : σ ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      -- Step 5, inclusion (i): `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(σ s)` for `s > 0`.
      have hincl1 : ∀ r s, 0 < s → X r s ⊆ ⋃ j, ball a r ∩ K j (σ * s) := by
        rintro r s hs x ⟨hxr, hx⟩
        set y := x - a with hydef
        have hy : 0 < ‖y‖ := by
          rcases (norm_nonneg y).lt_or_eq with h | h
          · exact h
          · exfalso
            rw [← h, mul_zero] at hx
            exact (norm_nonneg _).not_gt hx
        obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖y j‖)
          (Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩)
        have hsq : ‖y‖ ^ 2 ≤ (σ * ‖y j‖) ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2, mul_pow, hσsq]
          calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin N, ‖y j‖ ^ 2 :=
                Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hj i (Finset.mem_univ i)) 2
            _ = (N : ℝ) * ‖y j‖ ^ 2 := by simp
        have hle : ‖y‖ ≤ σ * ‖y j‖ :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
        have hyj : 0 < ‖y j‖ := by
          by_contra hcon
          have : ‖y j‖ = 0 := le_antisymm (not_lt.1 hcon) (norm_nonneg _)
          rw [this, mul_zero] at hle
          linarith
        have hyj0 : y j ≠ 0 := norm_pos_iff.1 hyj
        refine mem_iUnion.2 ⟨j, mem_ball.2 hxr, ?_, (-(y j)⁻¹) • L y, ?_, ?_⟩
        · intro h
          rw [hydef, h, sub_self, norm_zero] at hy
          exact lt_irrefl _ hy
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv]
          rw [inv_mul_lt_iff₀ hyj]
          calc ‖L y‖ < s * ‖y‖ := hx
            _ ≤ s * (σ * ‖y j‖) := by gcongr
            _ = ‖y j‖ * (σ * s) := by ring
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj0, neg_smul, one_smul, add_neg_cancel]
      -- Step 6, pointwise bound: `F(s) ≤ σᵏ Σ_j F_j(σ s)` for `s > 0`.
      have hpt : ∀ s, 0 < s → F s ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by
        intro s hs
        refine iSup₂_le fun r hr => ?_
        have hc0 : ENNReal.ofReal (σ ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
        have hA : ENNReal.ofReal ((r * (σ * s)) ^ (m + 1)) =
            ENNReal.ofReal (σ ^ (m + 1)) * ENNReal.ofReal ((r * s) ^ (m + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
          congr 2
          ring
        calc μ (X r s) / ENNReal.ofReal ((r * s) ^ (m + 1))
            ≤ (∑ j, μ (ball a r ∩ K j (σ * s))) / ENNReal.ofReal ((r * s) ^ (m + 1)) := by
              refine ENNReal.div_le_div_right ?_ _
              exact (measure_mono (hincl1 r s hs)).trans (measure_iUnion_fintype_le μ _)
          _ = ∑ j, ENNReal.ofReal (σ ^ (m + 1)) *
                (μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) := by
              rw [ENNReal.sum_div]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hA, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
          _ ≤ ∑ j, ENNReal.ofReal (σ ^ (m + 1)) * Fj j (σ * s) := by
              refine Finset.sum_le_sum fun j _ => ?_
              gcongr
              exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                μ (ball a r ∩ K j (σ * s)) / ENNReal.ofReal ((r * (σ * s)) ^ (m + 1))) r hr
          _ = ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s) := by rw [Finset.mul_sum]
      -- Step 8: `limsup` is subadditive along `𝓝[>] 0` (direct `ε`-argument).
      have hadd : ∀ (v w : ℝ → ℝ≥0∞), limsup (fun s => v s + w s) (𝓝[>] (0 : ℝ)) ≤
          limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) := by
        intro v w
        refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
        have hv : limsup v (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_self_add hlt
        have hw : limsup w (𝓝[>] (0 : ℝ)) < ⊤ := lt_of_le_of_lt le_add_self hlt
        have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by
          simp [ENNReal.div_eq_zero_iff, hε.ne']
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [eventually_lt_of_limsup_lt (ENNReal.lt_add_right hv.ne hε2),
          eventually_lt_of_limsup_lt (ENNReal.lt_add_right hw.ne hε2)] with x h1 h2
        calc v x + w x ≤ (limsup v (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) + (limsup w (𝓝[>] 0) + (ε : ℝ≥0∞) / 2) :=
              add_le_add h1.le h2.le
          _ = limsup v (𝓝[>] 0) + limsup w (𝓝[>] 0) + ε := by
              rw [add_add_add_comm, ENNReal.add_halves]
      have hsum : ∀ (S : Finset (Fin N)) (h : Fin N → ℝ → ℝ≥0∞),
          limsup (fun s => ∑ j ∈ S, h j s) (𝓝[>] (0 : ℝ)) ≤ ∑ j ∈ S, limsup (h j) (𝓝[>] 0) := by
        intro S h
        induction S using Finset.induction_on with
        | empty => simp
        | insert j S hj ih =>
          simp only [Finset.sum_insert hj]
          exact (hadd (h j) (fun s => ∑ i ∈ S, h i s)).trans (add_le_add le_rfl ih)
      -- Step 9, change of variable `t = σ s`: `s ↦ σ s` maps `𝓝[>] 0` into `𝓝[>] 0`.
      have hT : Tendsto (fun s : ℝ => σ * s) (𝓝[>] 0) (𝓝[>] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun s : ℝ => σ * s) (𝓝 0) (𝓝 (σ * 0)) :=
            ((continuous_const.mul continuous_id).tendsto 0)
          rw [mul_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          exact mul_pos hσ hs
      have hcv : ∀ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ)) ≤ limsup (Fj j) (𝓝[>] 0) := by
        intro j
        calc limsup (fun s => Fj j (σ * s)) (𝓝[>] (0 : ℝ))
            = limsup (Fj j) (map (fun s : ℝ => σ * s) (𝓝[>] 0)) := Filter.limsup_comp (Fj j) _ _
          _ ≤ limsup (Fj j) (𝓝[>] 0) := limsup_le_limsup_of_le hT (by isBoundedDefault) (by isBoundedDefault)
      -- Steps 7 and 10: pull out the constant `σᵏ`, then apply steps 8 and 9.
      calc limsup F (𝓝[>] 0) ≤ limsup (fun s => ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, Fj j (σ * s)) (𝓝[>] 0) := by
            refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
            filter_upwards [self_mem_nhdsWithin] with s hs
            exact hpt s hs
        _ = ENNReal.ofReal (σ ^ (m + 1)) * limsup (fun s => ∑ j, Fj j (σ * s)) (𝓝[>] 0) :=
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (fun s => Fj j (σ * s)) (𝓝[>] 0) := by
            gcongr
            exact hsum Finset.univ (fun j s => Fj j (σ * s))
        _ ≤ ENNReal.ofReal (σ ^ (m + 1)) * ∑ j, limsup (Fj j) (𝓝[>] 0) := by
            gcongr with j
            exact hcv j
/-- **Slice densities of the exceptional parameters** (Mattila, *Geometry of Sets and Measures in
Euclidean Spaces*, Lemma 18.9; for transversal families, Hovila–Järvenpää–Järvenpää–Ledrappier,
arXiv:1104.3453, Lemma 2.5).  Let `k = m + 1`, `L_u y = (⟨u_i, y⟩)_i`,
`w ⊕ c = (w_i + c_i e_j)_i`, `K_w(C) = {x ≠ a : L_{w ⊕ c}(x − a) = 0 for some c ∈ C}` and
`ϑ_j(u) = limsup_{t↓0} sup_{0<r<δ} μ(B(a,r) ∩ K_u(B(0,t)))/(rt)ᵏ`.  Then the set `𝔅_j` of `u`
with `0 < ϑ_j(u) < ∞` and no `x ∈ E` with `0 < |x − a| < δ` and `L_u x = L_u a` is Lebesgue-null.
For fixed `w`, `ψ_w(C) = sup_{0<r<δ} μ(B(a,r) ∩ K_w(C))/rᵏ` is an outer measure on `ℝᵏ`, inner
continuous on open balls, and vanishes on the Borel set `D_w` of those `c` for which `w ⊕ c` has
no such `x`, because `μ(ℝ^N ∖ E) = 0`.  As `K_w(B(c,t)) = K_{w ⊕ c}(B(0,t))`, the upper
`k`-density of `ψ_w` at `c` is `ϑ_j(w ⊕ c)`, so by the Mickle–Radó theorem
`Lᵏ{c : w ⊕ c ∈ 𝔅_j} = 0` for every `w`.  `𝔅_j` is Borel, and Tonelli for `(w, c) ↦ w ⊕ c` in both
orders, with translation invariance, gives `𝓛(𝔅_j) · ∞ = 0`. -/
theorem Submission.rectifiability_bf_slice_density_null : ∀ (N m : ℕ) (μ : Measure (Eucl N)) (E : Set (Eucl N)) (δ : ℝ) (a : Eucl N) (j : Fin N), SFinite μ → IsSigmaCompact E → μ Eᶜ = 0 → (volume : Measure (Fin (m + 1) → Eucl N)) {u : Fin (m + 1) → Eucl N | ¬ (∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) a) : Eucl (m + 1))) ∧ 0 < limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) ∧ limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0) < ⊤} = 0 := by
  intro N m μ E δ a j hμ hE hEc
  let Lu : (Fin (m + 1) → Eucl N) → Eucl N → Eucl (m + 1) := fun u y =>
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) y) : Eucl (m + 1))
  let T3 : (Fin (m + 1) → Eucl N) → Prop := fun u => ∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧
    (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) x) : Eucl (m + 1)) =
      (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i) a) : Eucl (m + 1))
  let Ks : (Fin (m + 1) → Eucl N) → ℝ → Set (Eucl N) := fun u t => {x | x ≠ a ∧
    ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) =>
      inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
  let θ : (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun u => limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ,
    μ (ball a r ∩ Ks u t) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0)
  let B : Set (Fin (m + 1) → Eucl N) := {u | ¬ T3 u ∧ 0 < θ u ∧ θ u < ⊤}
  show (volume : Measure (Fin (m + 1) → Eucl N)) B = 0
  -- step 1(a), 1(c): `L_{u ⊕ c} y = L_u y + y_j c` and `L_v (x - y) = L_v x - L_v y`
  have hfib : ∀ (u : Fin (m + 1) → Eucl N) (c : Eucl (m + 1)) (y : Eucl N),
      (WithLp.toLp 2 (fun i : Fin (m + 1) =>
        inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) y) : Eucl (m + 1)) =
          Lu u y + (y j) • c := by
    intro u c y
    ext i
    simp [Lu, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]
  have hLsub : ∀ (v : Fin (m + 1) → Eucl N) (x y : Eucl N), Lu v (x - y) = Lu v x - Lu v y := by
    intro v x y
    ext i
    simp [Lu, inner_sub_right]
  -- step 1(f): explicit form of `K_{j,u}(t)` for `t > 0`
  have hKs : ∀ u t, 0 < t → Ks u t = {x | ‖Lu u (x - a)‖ < t * ‖(x - a) j‖} ∪
      {x | x ≠ a ∧ (x - a) j = 0 ∧ Lu u (x - a) = 0} := by
    intro u t ht
    ext x
    simp only [Ks, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨hxa, c, hc, h0⟩
      rw [hfib] at h0
      by_cases hyj : (x - a) j = 0
      · right
        refine ⟨hxa, hyj, ?_⟩
        rw [hyj, zero_smul, add_zero] at h0
        exact h0
      · left
        have hL : Lu u (x - a) = -((x - a) j • c) := eq_neg_of_add_eq_zero_left h0
        rw [hL, norm_neg, norm_smul]
        have hc' : ‖c‖ < t := mem_ball_zero_iff.1 hc
        have hpos : 0 < ‖(x - a) j‖ := norm_pos_iff.2 hyj
        calc ‖(x - a) j‖ * ‖c‖ < ‖(x - a) j‖ * t := mul_lt_mul_of_pos_left hc' hpos
          _ = t * ‖(x - a) j‖ := mul_comm _ _
    · rintro (h | ⟨hxa, hyj, h0⟩)
      · have hyj : (x - a) j ≠ 0 := by
          intro h'
          rw [h', norm_zero, mul_zero] at h
          exact (norm_nonneg _).not_gt h
        have hxa : x ≠ a := by
          intro h'
          apply hyj
          rw [h', sub_self]
          rfl
        refine ⟨hxa, (-((x - a) j)⁻¹) • Lu u (x - a), ?_, ?_⟩
        · rw [mem_ball_zero_iff, norm_smul, norm_neg, norm_inv,
            inv_mul_lt_iff₀ (norm_pos_iff.2 hyj)]
          linarith [h]
        · rw [hfib, smul_smul, mul_neg, mul_inv_cancel₀ hyj, neg_smul, one_smul, add_neg_cancel]
      · refine ⟨hxa, 0, mem_ball_self ht, ?_⟩
        rw [hfib, smul_zero, add_zero]
        exact h0
  -- step 8(a): `ϑ_j` is measurable (`limsup_sup_measurable`; `G` is Borel by step 1(f))
  let G : ℝ → ℝ → Set ((Fin (m + 1) → Eucl N) × Eucl N) := fun r t =>
    {q | q.2 ∈ ball a r ∩ Ks q.1 t}
  have hc1 : Continuous fun q : (Fin (m + 1) → Eucl N) × Eucl N => Lu q.1 (q.2 - a) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).comp continuous_fst).inner (continuous_snd.sub continuous_const)
  have hc2 : Continuous fun q : (Fin (m + 1) → Eucl N) × Eucl N => (q.2 - a) j :=
    (PiLp.continuous_apply 2 _ j).comp (continuous_snd.sub continuous_const)
  have hGm : ∀ r t, MeasurableSet (G r t) := by
    intro r t
    rcases le_or_gt t 0 with ht | ht
    · have : G r t = ∅ := by
        ext q
        simp only [G, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨-, -, c, hc, -⟩
        rw [ball_eq_empty.2 ht] at hc
        exact hc
      rw [this]
      exact MeasurableSet.empty
    · have : G r t = {q | dist q.2 a < r} ∩ ({q | ‖Lu q.1 (q.2 - a)‖ < t * ‖(q.2 - a) j‖} ∪
          ({q | q.2 ≠ a} ∩ {q | (q.2 - a) j = 0} ∩ {q | Lu q.1 (q.2 - a) = 0})) := by
        ext q
        simp only [G, mem_ofPred_eq, mem_inter_iff, mem_ball]
        rw [hKs q.1 t ht]
        simp only [mem_union, mem_ofPred_eq, mem_inter_iff, and_assoc]
      rw [this]
      refine (isOpen_lt (continuous_snd.dist continuous_const) continuous_const).measurableSet.inter
        (MeasurableSet.union ?_ ?_)
      · exact (isOpen_lt hc1.norm (continuous_const.mul hc2.norm)).measurableSet
      · exact ((isOpen_ne_fun continuous_snd continuous_const).measurableSet.inter
          (isClosed_eq hc2 continuous_const).measurableSet).inter
          (isClosed_eq hc1 continuous_const).measurableSet
  have hGmono : ∀ r t t', t ≤ t' → G r t ⊆ G r t' := by
    rintro r t t' htt' q ⟨hq1, hxa, c, hc, h0⟩
    exact ⟨hq1, hxa, c, ball_subset_ball htt' hc, h0⟩
  have hGcont : ∀ r t, 0 < r → G r t = ⋃ r' ∈ Ioo (0 : ℝ) r, G r' t := by
    intro r t hr
    ext q
    simp only [G, mem_iUnion, mem_ofPred_eq, mem_inter_iff, mem_ball, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(dist q.2 a + r) / 2, ⟨by positivity, by linarith⟩, by linarith, h2⟩
    · rintro ⟨r', ⟨-, hr'r⟩, h1, h2⟩
      exact ⟨h1.trans hr'r, h2⟩
  have hθm : Measurable θ :=
    Submission.rectifiability_bf_limsup_sup_measurable (Fin (m + 1) → Eucl N) (Eucl N) (m + 1)
      μ δ G hμ hGm hGmono hGcont
  -- step 8(b), 8(c): `𝔅_j` is measurable (`witness_set_measurable`)
  have hW := Submission.rectifiability_bf_witness_set_measurable N m E δ hE
  have hT3m : MeasurableSet {u : Fin (m + 1) → Eucl N | ¬ T3 u} :=
    (measurable_const.prodMk measurable_id) hW.compl
  have hBm : MeasurableSet B :=
    hT3m.inter ((measurableSet_lt measurable_const hθm).inter
      (measurableSet_lt hθm measurable_const))
  -- steps 2–7: `Lᵏ{c : w ⊕ c ∈ 𝔅_j} = 0` for every `w`
  let sh : Eucl (m + 1) → (Fin (m + 1) → Eucl N) := fun c i => c i • EuclideanSpace.single j (1 : ℝ)
  have hsh : Continuous sh :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).smul continuous_const
  have hslice : ∀ w : Fin (m + 1) → Eucl N,
      (volume : Measure (Eucl (m + 1))) {c | w + sh c ∈ B} = 0 := by
    intro w
    let KC : Set (Eucl (m + 1)) → Set (Eucl N) := fun C => {x | x ≠ a ∧ ∃ c ∈ C,
      (WithLp.toLp 2 (fun i : Fin (m + 1) =>
        inner ℝ (w i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}
    -- step 1(d): `K_w` is monotone and commutes with countable unions
    have hKCmono : ∀ C₁ C₂, C₁ ⊆ C₂ → KC C₁ ⊆ KC C₂ := by
      rintro C₁ C₂ h x ⟨hxa, c, hc, h0⟩
      exact ⟨hxa, c, h hc, h0⟩
    have hKCunion : ∀ (s : ℕ → Set (Eucl (m + 1))), KC (⋃ i, s i) = ⋃ i, KC (s i) := by
      intro s
      ext x
      simp only [KC, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxa, c, ⟨i, hci⟩, h0⟩
        exact ⟨i, hxa, c, hci, h0⟩
      · rintro ⟨i, hxa, c, hci, h0⟩
        exact ⟨hxa, c, ⟨i, hci⟩, h0⟩
    -- step 2: the outer measure `ψ_w`
    let ψ : OuterMeasure (Eucl (m + 1)) :=
      { measureOf := fun C =>
          ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC C) / ENNReal.ofReal (r ^ (m + 1))
        empty := by
          have : KC ∅ = ∅ := by
            ext x
            simp [KC]
          simp [this]
        mono := fun {s₁ s₂} h => iSup₂_mono fun r _ =>
          ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _ (hKCmono _ _ h))) _
        iUnion_nat := fun s _ => by
          refine iSup₂_le fun r hr => ?_
          rw [hKCunion, inter_iUnion]
          calc μ (⋃ i, ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1))
              ≤ (∑' i, μ (ball a r ∩ KC (s i))) / ENNReal.ofReal (r ^ (m + 1)) :=
                ENNReal.div_le_div_right (measure_iUnion_le _) _
            _ = ∑' i, μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1)) := by
                simp only [div_eq_mul_inv, ENNReal.tsum_mul_right]
            _ ≤ ∑' i, ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1)) :=
                ENNReal.tsum_le_tsum fun i => le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
                  μ (ball a r ∩ KC (s i)) / ENNReal.ofReal (r ^ (m + 1))) r hr }
    have hψ : ∀ C, ψ C = ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ KC C) / ENNReal.ofReal (r ^ (m + 1)) :=
      fun C => rfl
    -- step 3: inner continuity of `ψ_w` on open balls
    have hball : ∀ (c : Eucl (m + 1)) (τ : ℝ),
        ψ (ball c τ) = ⨆ τ' ∈ Ioo (0 : ℝ) τ, ψ (ball c τ') := by
      intro c τ
      apply le_antisymm
      · rcases le_or_gt τ 0 with hτ | hτ
        · rw [ball_eq_empty.2 hτ, measure_empty]
          exact zero_le
        · rw [hψ]
          refine iSup₂_le fun r hr => ?_
          let τn : ℕ → ℝ := fun n => τ - τ / ((n : ℝ) + 2)
          have hτn_mono : Monotone τn := by
            intro n n' hnn'
            simp only [τn]
            have : τ / ((n' : ℝ) + 2) ≤ τ / ((n : ℝ) + 2) := by
              apply div_le_div_of_nonneg_left hτ.le (by positivity)
              have : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
              linarith
            linarith
          have hτn_mem : ∀ n, τn n ∈ Ioo 0 τ := by
            intro n
            have h1 : τ / ((n : ℝ) + 2) < τ := by
              rw [div_lt_iff₀ (by positivity)]
              have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
              nlinarith
            have h2 : 0 < τ / ((n : ℝ) + 2) := by positivity
            exact ⟨by simp only [τn]; linarith, by simp only [τn]; linarith⟩
          have hballU : ball c τ = ⋃ n, ball c (τn n) := by
            ext c'
            simp only [mem_ball, mem_iUnion]
            constructor
            · intro hd
              obtain ⟨n, hn⟩ := exists_nat_gt (τ / (τ - dist c' c))
              refine ⟨n, ?_⟩
              simp only [τn]
              have hpos : 0 < τ - dist c' c := by linarith
              have : τ / ((n : ℝ) + 2) < τ - dist c' c := by
                rw [div_lt_iff₀ (by positivity)]
                rw [div_lt_iff₀ hpos] at hn
                nlinarith
              linarith
            · rintro ⟨n, hn⟩
              exact hn.trans (hτn_mem n).2
          have hmono_sets : Monotone (fun n => ball a r ∩ KC (ball c (τn n))) := by
            intro n n' hnn'
            exact inter_subset_inter_right _ (hKCmono _ _ (ball_subset_ball (hτn_mono hnn')))
          have hmeas : μ (ball a r ∩ KC (ball c τ)) = ⨆ n, μ (ball a r ∩ KC (ball c (τn n))) := by
            rw [hballU, hKCunion, inter_iUnion]
            exact hmono_sets.measure_iUnion
          rw [hmeas, ENNReal.iSup_div]
          refine iSup_le fun n => ?_
          refine le_trans ?_ (le_iSup₂ (f := fun τ' (_ : τ' ∈ Ioo (0 : ℝ) τ) => ψ (ball c τ'))
            (τn n) (hτn_mem n))
          rw [hψ]
          exact le_iSup₂ (f := fun r (_ : r ∈ Ioo (0 : ℝ) δ) =>
            μ (ball a r ∩ KC (ball c (τn n))) / ENNReal.ofReal (r ^ (m + 1))) r hr
      · exact iSup₂_le fun τ' hτ' => ψ.mono (ball_subset_ball hτ'.2.le)
    -- steps 4–6: `D_w` is Borel and `ψ_w`-null, so Mickle–Radó applies
    let D : Set (Eucl (m + 1)) := {c | ¬ T3 (w + sh c)}
    have hDm : MeasurableSet D :=
      (measurable_const.prodMk (continuous_const.add hsh).measurable) hW.compl
    have hψD : ψ D = 0 := by
      rw [hψ]
      refine le_antisymm (iSup₂_le fun r hr => ?_) zero_le
      have : μ (ball a r ∩ KC D) = 0 := by
        refine measure_mono_null (fun x hx => ?_) hEc
        obtain ⟨hxr, hxa, c, hcD, hx0⟩ := hx
        intro hxE
        apply hcD
        refine ⟨x, hxE, hxa, (mem_ball.1 hxr).trans hr.2, ?_⟩
        have h0 : Lu (w + sh c) (x - a) = 0 := hx0
        rw [hLsub] at h0
        exact sub_eq_zero.1 h0
      rw [this, ENNReal.zero_div]
    have hMR := Submission.rectifiability_mickle_rado m ψ D hball hDm hψD
    -- step 7: `K_w(B(c,t)) = K_{w ⊕ c}(B(0,t))`, so the slice density at `c` is `ϑ_j(w ⊕ c)`
    have hKCtr : ∀ (c : Eucl (m + 1)) (t : ℝ), KC (ball c t) = Ks (w + sh c) t := by
      intro c t
      ext x
      simp only [KC, Ks, mem_ofPred_eq]
      constructor
      · rintro ⟨hxa, c', hc', h0⟩
        refine ⟨hxa, c' - c, ?_, ?_⟩
        · rw [mem_ball_zero_iff, ← mem_ball_iff_norm]
          exact hc'
        · have hv : ∀ i, (w + sh c) i + (c' - c) i • EuclideanSpace.single j (1 : ℝ) =
              w i + c' i • EuclideanSpace.single j (1 : ℝ) := by
            intro i
            simp only [sh, Pi.add_apply, PiLp.sub_apply, sub_smul]
            abel
          simp only [hv]
          exact h0
      · rintro ⟨hxa, c'', hc'', h0⟩
        refine ⟨hxa, c + c'', ?_, ?_⟩
        · rw [mem_ball_iff_norm, add_sub_cancel_left, ← mem_ball_zero_iff]
          exact hc''
        · have hv : ∀ i, w i + (c + c'') i • EuclideanSpace.single j (1 : ℝ) =
              (w + sh c) i + c'' i • EuclideanSpace.single j (1 : ℝ) := by
            intro i
            simp only [sh, Pi.add_apply, PiLp.add_apply, add_smul]
            abel
          simp only [hv]
          exact h0
    have hid : ∀ c : Eucl (m + 1),
        limsup (fun t : ℝ => ψ (ball c t) / ENNReal.ofReal (t ^ (m + 1))) (𝓝[>] 0) =
          θ (w + sh c) := by
      intro c
      apply limsup_congr
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      rw [hψ, ENNReal.iSup_div]
      refine iSup_congr fun r => ?_
      rw [ENNReal.iSup_div]
      refine iSup_congr fun hr => ?_
      rw [hKCtr c t]
      have hr0 : 0 < r := hr.1
      have hA0 : ENNReal.ofReal (r ^ (m + 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
        ← ENNReal.mul_inv (Or.inl hA0) (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    refine le_antisymm (le_trans (measure_mono ?_) hMR.le) zero_le
    intro c hc
    refine ⟨hc.1, ?_, ?_⟩
    · rw [hid c]; exact hc.2.1
    · rw [hid c]; exact hc.2.2
  -- step 9: Tonelli for `(w, c) ↦ w ⊕ c` in both orders
  have hP : MeasurableSet ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) :=
    (continuous_fst.add (hsh.comp continuous_snd)).measurable hBm
  have h1 : ((volume : Measure (Fin (m + 1) → Eucl N)).prod (volume : Measure (Eucl (m + 1))))
      ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) = 0 := by
    rw [Measure.prod_apply hP]
    have : ∀ w : Fin (m + 1) → Eucl N, (volume : Measure (Eucl (m + 1)))
        (Prod.mk w ⁻¹'
          ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B)) = 0 :=
      fun w => hslice w
    simp [this]
  have h2 : ((volume : Measure (Fin (m + 1) → Eucl N)).prod (volume : Measure (Eucl (m + 1))))
      ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B) =
        (volume : Measure (Fin (m + 1) → Eucl N)) B * ⊤ := by
    rw [Measure.prod_apply_symm hP]
    have : ∀ c : Eucl (m + 1), (volume : Measure (Fin (m + 1) → Eucl N))
        ((fun w => (w, c)) ⁻¹'
          ((fun p : (Fin (m + 1) → Eucl N) × Eucl (m + 1) => p.1 + sh p.2) ⁻¹' B)) =
            (volume : Measure (Fin (m + 1) → Eucl N)) B :=
      fun c => measure_preimage_add_right (volume : Measure (Fin (m + 1) → Eucl N)) (sh c) B
    simp only [this]
    rw [lintegral_const, measure_univ_of_isAddLeftInvariant]
  rw [h1] at h2
  rcases mul_eq_zero.1 h2.symm with h | h
  · exact h
  · exact absurd h ENNReal.top_ne_zero

/-- **Besicovitch–Federer trichotomy for almost every linear map** (Mattila, *Geometry of Sets and
Measures in Euclidean Spaces*, Lemma 18.9; Hovila–Järvenpää–Järvenpää–Ledrappier, Geom. Dedicata
161 (2012), Lemma 2.4).  Let `k = m + 1`, `μ = Hᵏ⌞E`, `L_v x = (⟨v_i, x⟩)_i`,
`X_v(a,r,s) = {x : |x − a| < r, |L_v(x − a)| < s|x − a|}` and
`Φ(a,v) = limsup_{s↓0} sup_{0<r<δ} μ(X_v(a,r,s))/(rs)ᵏ`.  Fix `a`.  By Mickle–Radó on the slices
`v ⊕_j c`, for a.e. `v` without a fibre witness (T3) every fibre density `ϑ_j(v)` lies in `{0, ∞}`,
and `ϑ_j ≤ Φ ≤ N^{k/2} Σ_j ϑ_j` puts `Φ(a,v)` in `{0, ∞}`.  The set of such `(a,v)` is Borel, so
Fubini gives the same for a.e. `v` and `μ`-a.e. `a`; `Φ = 0` is (T1) and `Φ = ∞` gives the
infinite projected density (T2). -/
theorem Submission.rectifiability_bf_trichotomy : ∀ (N m : ℕ) (E : Set (Eucl N)) (δ : ℝ), IsSigmaCompact E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → 0 < δ → ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)), ∀ᵐ a ∂((μHE[m + 1] : Measure (Eucl N)).restrict E), (∀ η : ℝ, 0 < η → ∃ s ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Ioo (0 : ℝ) δ, (μHE[m + 1] : Measure (Eucl N)) (E ∩ {x | dist x a < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) (x - a)) : Eucl (m + 1))‖ < s * ‖x - a‖}) ≤ ENNReal.ofReal (η * (r * s) ^ (m + 1))) ∨ dimensionalUpperDensity (Measure.map (fun x : Eucl N => (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1))) ((μHE[m + 1] : Measure (Eucl N)).restrict E)).toOuterMeasure ((m + 1 : ℕ) : ℝ) univ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) = ⊤ ∨ ∃ x ∈ E, x ≠ a ∧ dist x a < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (v i) a) : Eucl (m + 1)) := by
  intro N m E δ hE hEfin _
  -- step 1: `E` is Borel and `μ = Hᵏ⌞E` is a finite measure carried by `E`
  have hEmeas : MeasurableSet E := by
    obtain ⟨K, hK, hKE⟩ := hE
    rw [← hKE]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have : IsFiniteMeasure ((μHE[m + 1] : Measure (Eucl N)).restrict E) :=
    isFiniteMeasure_restrict.2 hEfin.ne
  have hμE : ((μHE[m + 1] : Measure (Eucl N)).restrict E) Eᶜ = 0 := by
    rw [Measure.restrict_apply' hEmeas, compl_inter_self, measure_empty]
  have hμS : ∀ S : Set (Eucl N),
      (μHE[m + 1] : Measure (Eucl N)) (E ∩ S) = ((μHE[m + 1] : Measure (Eucl N)).restrict E) S := by
    intro S
    rw [Measure.restrict_apply' hEmeas, inter_comm]
  set μ : Measure (Eucl N) := (μHE[m + 1] : Measure (Eucl N)).restrict E
  -- step 2: the cone ratio `Φ(a,v)` and the fibre-witness set `W` of (T3) are Borel in `(a,v)`
  set Φ : Eucl N × (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun p => limsup (fun s : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ {x | dist x p.1 < r ∧ ‖(WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) (x - p.1)) : Eucl (m + 1))‖ < s * ‖x - p.1‖} / ENNReal.ofReal ((r * s) ^ (m + 1))) (𝓝[>] 0)
  set W : Set (Eucl N × (Fin (m + 1) → Eucl N)) := {p | ∃ x ∈ E, x ≠ p.1 ∧ dist x p.1 < δ ∧ (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) x) : Eucl (m + 1)) = (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (p.2 i) p.1) : Eucl (m + 1))}
  have hΦ : Measurable Φ := Submission.rectifiability_bf_cone_ratio_measurable N m μ δ inferInstance
  have hW : MeasurableSet W := Submission.rectifiability_bf_witness_set_measurable N m E δ hE
  have hG : MeasurableSet
      {p : Eucl N × (Fin (m + 1) → Eucl N) | (Φ (p.1, p.2) = 0 ∨ Φ (p.1, p.2) = ⊤) ∨ (p.1, p.2) ∈ W} :=
    ((hΦ (measurableSet_singleton 0)).union (hΦ (measurableSet_singleton ⊤))).union hW
  -- step 3: for every `a`, `Φ(a,v) ∈ {0, ∞}` or (T3) holds for a.e. `v`
  have hslice : ∀ a : Eucl N, ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)),
      (Φ (a, v) = 0 ∨ Φ (a, v) = ⊤) ∨ (a, v) ∈ W := by
    intro a
    set ϑ : Fin N → (Fin (m + 1) → Eucl N) → ℝ≥0∞ := fun j u => limsup (fun t : ℝ => ⨆ r ∈ Ioo (0 : ℝ) δ, μ (ball a r ∩ {x | x ≠ a ∧ ∃ c ∈ ball (0 : Eucl (m + 1)) t, (WithLp.toLp 2 (fun i : Fin (m + 1) => inner ℝ (u i + c i • EuclideanSpace.single j (1 : ℝ)) (x - a)) : Eucl (m + 1)) = 0}) / ENNReal.ofReal ((r * t) ^ (m + 1))) (𝓝[>] 0)
    -- Mickle–Radó on the slices: `0 < ϑ_j(v) < ∞` without (T3) only for a null set of `v`
    have hnull : ∀ j : Fin N, ∀ᵐ u ∂(volume : Measure (Fin (m + 1) → Eucl N)),
        ¬ ((a, u) ∉ W ∧ 0 < ϑ j u ∧ ϑ j u < ⊤) := by
      intro j
      filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (Submission.rectifiability_bf_slice_density_null N m μ E δ a j inferInstance hE hμE)]
        with u hu
      exact hu
    filter_upwards [ae_all_iff.2 hnull] with u hu
    by_cases hT3 : (a, u) ∈ W
    · exact Or.inr hT3
    refine Or.inl ?_
    -- cones versus unions of fibres: `ϑ_j ≤ Φ ≤ N^{k/2} Σ_j ϑ_j`
    obtain ⟨hle, hge⟩ := Submission.rectifiability_bf_fibre_cone_comparison N m μ δ a u
    have hle' : ∀ j, ϑ j u ≤ Φ (a, u) := hle
    have hge' : Φ (a, u) ≤ ENNReal.ofReal (Real.sqrt (N : ℝ) ^ (m + 1)) * ∑ j : Fin N, ϑ j u :=
      hge
    have h0top : ∀ j, ϑ j u = 0 ∨ ϑ j u = ⊤ := by
      intro j
      by_contra hcon
      exact hu j ⟨hT3, pos_iff_ne_zero.2 (not_or.1 hcon).1, lt_top_iff_ne_top.2 (not_or.1 hcon).2⟩
    by_cases htop : ∃ j, ϑ j u = ⊤
    · obtain ⟨j, hj⟩ := htop
      have h := hle' j
      rw [hj, top_le_iff] at h
      exact Or.inr h
    · refine Or.inl (nonpos_iff_eq_zero.1 (hge'.trans_eq ?_))
      rw [Finset.sum_eq_zero fun j _ => (h0top j).resolve_right (not_exists.1 htop j), mul_zero]
  -- step 4: Fubini turns `∀ a, ∀ᵐ v` into `∀ᵐ v, ∀ᵐ a ∂μ`
  have hswap : ∀ᵐ v ∂(volume : Measure (Fin (m + 1) → Eucl N)), ∀ᵐ a ∂μ,
      (Φ (a, v) = 0 ∨ Φ (a, v) = ⊤) ∨ (a, v) ∈ W :=
    (Measure.ae_ae_comm (μ := μ) (ν := (volume : Measure (Fin (m + 1) → Eucl N)))
      (p := fun a v => (Φ (a, v) = 0 ∨ Φ (a, v) = ⊤) ∨ (a, v) ∈ W) hG).1
      (Eventually.of_forall hslice)
  -- step 5: `Φ = 0` gives (T1) and `Φ = ∞` gives (T2)
  filter_upwards [hswap] with v hv
  filter_upwards [hv] with a ha
  rcases ha with (h0 | htop) | hT3
  · refine Or.inl fun η hη => ?_
    obtain ⟨s, hs, hsr⟩ :=
      (Submission.rectifiability_bf_cone_ratio_reduction N m μ δ a v).1 h0 η hη
    exact ⟨s, hs, fun r hr => (hμS _).trans_le (hsr r hr)⟩
  · exact Or.inr (Or.inl ((Submission.rectifiability_bf_cone_ratio_reduction N m μ δ a v).2 htop))
  · exact Or.inr (Or.inr hT3)
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

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
