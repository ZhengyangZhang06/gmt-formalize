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

/-- Simon Ch. 6, (3.6): an `n`-vector density `w` that is dominated by an integrable function on
`g⁻¹(K)` for every compact `K ⊆ V` defines a current `ω ↦ ∫ ⟨ω(g x), w x⟩ dμ(x)` in `𝒟ₙ(V)`. -/
theorem Submission.lpf_pic_current_of_dominated_density :
    ∀ (P Q n : ℕ) (V : Set (Eucl Q)) (μ : Measure (Eucl P)) (g : Eucl P → Eucl Q) (w : Eucl P → NVector (Eucl Q) n), AEMeasurable g μ → AEStronglyMeasurable w μ → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∃ h : Eucl P → ℝ, Integrable h μ ∧ ∀ᵐ x ∂μ, g x ∈ K → ‖w x‖ ≤ h x) → ∃ S : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, S ω = ∫ x, w x ((ω : DifferentialForm (Eucl Q) n) (g x)) ∂μ := by
  intro P Q n V μ g w hg hw hdom
  -- Step 1: `x ↦ ⟨η (g x), w x⟩` is a.e. strongly measurable for continuous `η`.
  have hmeas : ∀ η : Eucl Q → Covector (Eucl Q) n, Continuous η →
      AEStronglyMeasurable (fun x => w x (η (g x))) μ := by
    intro η hη
    have hηg : AEStronglyMeasurable (fun x => η (g x)) μ :=
      hη.comp_aestronglyMeasurable hg.aestronglyMeasurable
    have hev : Continuous (Function.uncurry
        fun (φ : NVector (Eucl Q) n) (v : Covector (Eucl Q) n) => φ v) :=
      continuous_fst.clm_apply continuous_snd
    exact hev.comp_aestronglyMeasurable₂ hw hηg
  -- Step 2: if `tsupport η ⊆ K` and `‖η‖ ≤ B`, then `|⟨η ∘ g, w⟩| ≤ B |h|` a.e.
  have hkey : ∀ (η : Eucl Q → Covector (Eucl Q) n) (K : Set (Eucl Q)) (h : Eucl P → ℝ) (B : ℝ),
      Continuous η → tsupport η ⊆ K → Integrable h μ → (∀ᵐ x ∂μ, g x ∈ K → ‖w x‖ ≤ h x) →
      (∀ y, ‖η y‖ ≤ B) →
      Integrable (fun x => w x (η (g x))) μ ∧
        ‖∫ x, w x (η (g x)) ∂μ‖ ≤ B * ∫ x, ‖h x‖ ∂μ := by
    intro η K h B hη hK hh hwh hB
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hbound : ∀ᵐ x ∂μ, ‖w x (η (g x))‖ ≤ B * ‖h x‖ := by
      filter_upwards [hwh] with x hx
      by_cases hgx : g x ∈ K
      · calc ‖w x (η (g x))‖ ≤ ‖w x‖ * ‖η (g x)‖ := (w x).le_opNorm _
          _ ≤ ‖h x‖ * B :=
            mul_le_mul ((hx hgx).trans (Real.le_norm_self _)) (hB _) (norm_nonneg _)
              (norm_nonneg _)
          _ = B * ‖h x‖ := mul_comm _ _
      · rw [image_eq_zero_of_notMem_tsupport fun hx' => hgx (hK hx'), map_zero, norm_zero]
        exact mul_nonneg hB0 (norm_nonneg _)
    have hint : Integrable (fun x => B * ‖h x‖) μ := hh.norm.const_mul B
    refine ⟨hint.mono' (hmeas η hη) hbound, ?_⟩
    calc ‖∫ x, w x (η (g x)) ∂μ‖ ≤ ∫ x, B * ‖h x‖ ∂μ := norm_integral_le_of_norm_le hint hbound
      _ = B * ∫ x, ‖h x‖ ∂μ := integral_const_mul B _
  -- Step 3: the integrand of every test form is integrable.
  have hintω : ∀ ω : TestFormOn V n,
      Integrable (fun x => w x ((ω : DifferentialForm (Eucl Q) n) (g x))) μ := by
    intro ω
    have hcont : Continuous (ω : DifferentialForm (Eucl Q) n) := ContDiff.continuous ω.property.1.1
    have hcs : HasCompactSupport (ω : DifferentialForm (Eucl Q) n) := ω.property.1.2
    obtain ⟨h, hh, hwh⟩ := hdom (tsupport (ω : DifferentialForm (Eucl Q) n)) hcs ω.property.2
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcs
    exact (hkey _ _ h B hcont subset_rfl hh hwh hB).1
  -- Step 4: the linear functional `ω ↦ ∫ ⟨ω (g x), w x⟩ dμ`.
  let S₀ : TestFormOn V n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x, w x ((ω : DifferentialForm (Eucl Q) n) (g x)) ∂μ
      map_add' := by
        intro ω₁ ω₂
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hintω ω₁) (hintω ω₂)
      map_smul' := by
        intro c ω
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  -- Step 5: sequential continuity at `0`, from uniform convergence of the forms themselves.
  refine ⟨⟨S₀, ?_⟩, fun ω => rfl⟩
  intro ωs hconv
  obtain ⟨K, hKc, hKV, hsupp, -, hunif⟩ := hconv
  obtain ⟨h, hh, hwh⟩ := hdom K hKc hKV
  set I := ∫ x, ‖h x‖ ∂μ
  have hI0 : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  have h0 := Metric.tendstoUniformlyOn_iff.1 (hunif 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
  filter_upwards [h0 _ hδ] with j hj
  have hBj : ∀ y, ‖(ωs j : DifferentialForm (Eucl Q) n) y‖ ≤ ε / (I + 1) := by
    intro y
    by_cases hy : y ∈ K
    · have h1 := hj y hy
      have h2 : iteratedFDeriv ℝ 0 ((0 : TestFormOn V n) : DifferentialForm (Eucl Q) n) y = 0 := by
        rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
        simp
      rw [h2, dist_zero_left, norm_iteratedFDeriv_zero] at h1
      exact h1.le
    · rw [image_eq_zero_of_notMem_tsupport fun hy' => hy (hsupp j hy'), norm_zero]
      exact hδ.le
  have hcont : Continuous (ωs j : DifferentialForm (Eucl Q) n) :=
    ContDiff.continuous (ωs j).property.1.1
  have hle := (hkey _ K h _ hcont (hsupp j) hh hwh hBj).2
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith
/-- Measurability of the push-forward density in Simon Ch. 6, (3.6) (p. 147): for a rectifiable
triple `(M, θ, ξ)` in an open `U` and an `Hⁿ⌞M`-a.e. strongly measurable `L`, the density
`x ↦ θ(x) L(x)_# ξ(x)` is `Hⁿ⌞M`-a.e. strongly measurable. -/
theorem Submission.lpf_pic_density_aestronglyMeasurable : ∀ (P Q n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U n M θ ξ → AEStronglyMeasurable L ((μHE[n] : Measure (Eucl P)).restrict M) → AEStronglyMeasurable (fun x => θ x • nVectorPushforward n (L x) (ξ x)) ((μHE[n] : Measure (Eucl P)).restrict M) := by
  intro P Q n U M θ ξ L hU hT hL
  -- `θ` is locally `Hⁿ`-integrable on `M` (compact neighbourhoods inside the open `U`), hence
  -- `Hⁿ⌞M`-a.e. strongly measurable since `ℝ^P` is second countable.
  have hloc : LocallyIntegrableOn θ M (μHE[n] : Measure (Eucl P)) := by
    intro x hx
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU (hT.subset hx)
    exact ⟨M ∩ K, inter_mem_nhdsWithin M (mem_interior_iff_mem_nhds.mp hxK),
      hT.integrableOn K hK hKU⟩
  have hθ : AEStronglyMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) :=
    hloc.aestronglyMeasurable
  -- `(A, v) ↦ A_# v = v ∘ A^#` is continuous, as `A ↦ A^#` and composition are.
  have hΦ : Continuous fun p : (Eucl P →L[ℝ] Eucl Q) × NVector (Eucl P) n =>
      nVectorPushforward n p.1 p.2 :=
    continuous_snd.clm_comp
      (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp continuous_fst)
  -- Compose with `x ↦ (L x, ξ x)` and multiply by `θ`.
  exact hθ.smul (hΦ.comp_aestronglyMeasurable (hL.prodMk hT.aestronglyMeasurable))
/-- **Domination of the push-forward density on a compact preimage (Simon Ch. 6, (3.6)).**  Let
`(M, θ, ξ)` be a rectifiable triple in `U`, `Z ⊆ U` with `Hⁿ(M \ Z) = 0`, `K' = f⁻¹(K) ∩ Z`
compact and `‖L x‖ ≤ C` on `M ∩ K'`.  Then `h = 1_{K'} Cⁿ θ` is `Hⁿ ⌞ M`-integrable (`θ` is
integrable on `M ∩ K'`, as `K' ⊆ U` is compact) and `‖θ(x) L(x)_# ξ(x)‖ ≤ h(x)` for `Hⁿ ⌞ M`-a.e.
`x` with `f x ∈ K`: a.e. such `x` lies in `M ∩ K'`; `‖A_# v‖ ≤ ‖A‖ⁿ ‖v‖` because `A_# v = v ∘ A^#`
and `‖A^# β‖ ≤ ‖A‖ⁿ ‖β‖`; and `‖ξ(x)‖ ≤ 1` because `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal. -/
theorem Submission.lpf_pic_density_dominated : ∀ (P Q n : ℕ) (U Z M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (K : Set (Eucl Q)), IsRectifiableTriple U n M θ ξ → Z ⊆ U → (μHE[n] : Measure (Eucl P)) (M \ Z) = 0 → IsCompact (f ⁻¹' K ∩ Z) → (∃ C : ℝ, ∀ x ∈ M ∩ (f ⁻¹' K ∩ Z), ‖L x‖ ≤ C) → ∃ h : Eucl P → ℝ, Integrable h ((μHE[n] : Measure (Eucl P)).restrict M) ∧ ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), f x ∈ K → ‖θ x • nVectorPushforward n (L x) (ξ x)‖ ≤ h x := by
  rintro P Q n U Z M θ ξ f L K hR hZU hMZ hK ⟨C, hC⟩
  -- (1) `‖A_# v‖ ≤ ‖A‖ⁿ ‖v‖`, from `A_# v = v ∘ A^#` and `‖A^# β‖ ≤ ‖A‖ⁿ ‖β‖`.
  have hpush : ∀ (A : Eucl P →L[ℝ] Eucl Q) (v : NVector (Eucl P) n),
      ‖nVectorPushforward n A v‖ ≤ ‖A‖ ^ n * ‖v‖ := by
    intro A v
    have hA : ‖covectorPullback n A‖ ≤ ‖A‖ ^ n := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun β => ?_
      simpa [covectorPullback, Fintype.card_fin, mul_comm] using
        ContinuousAlternatingMap.norm_compContinuousLinearMap_le β A
    calc ‖nVectorPushforward n A v‖ = ‖v.comp (covectorPullback n A)‖ := rfl
      _ ≤ ‖v‖ * ‖covectorPullback n A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖v‖ * ‖A‖ ^ n := by gcongr
      _ = ‖A‖ ^ n * ‖v‖ := mul_comm _ _
  -- (2) `‖ξ(x)‖ ≤ 1` a.e., since `ξ(x) = ±simpleNVector τ` with `τ` orthonormal.
  have hξ : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ‖ξ x‖ ≤ 1 := by
    filter_upwards [hR.orients] with x hx
    obtain ⟨τ, hτ, -, hx⟩ := hx
    have hs : ‖simpleNVector τ‖ ≤ 1 :=
      calc ‖simpleNVector τ‖ ≤ ∏ i, ‖τ i‖ :=
            LinearMap.mkContinuous_norm_le _ (Finset.prod_nonneg fun i _ => norm_nonneg _) _
        _ = 1 := Finset.prod_eq_one fun i _ => hτ.1 i
    rcases hx with hx | hx
    · rw [hx]
      exact hs
    · rw [hx, norm_neg (simpleNVector τ)]
      exact hs
  -- (3) `Hⁿ ⌞ M`-a.e. point lies in `M ∩ Z`, as `M` is null measurable and `Hⁿ(M \ Z) = 0`.
  have hM : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ M :=
    ae_restrict_mem₀ hR.nullMeasurableSet
  have hZ : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), x ∈ Z := by
    rw [ae_iff, Measure.restrict_apply₀' hR.nullMeasurableSet]
    have hset : {a | ¬a ∈ Z} ∩ M = M \ Z := by
      ext a
      simp [and_comm]
    rw [hset, hMZ]
  -- (4) `h = 1_{K'} Cⁿ θ` is `Hⁿ ⌞ M`-integrable: `K'` is compact (so measurable) and `K' ⊆ U`.
  have hKm : MeasurableSet (f ⁻¹' K ∩ Z) := hK.isClosed.measurableSet
  have hθK : IntegrableOn (fun x => C ^ n * θ x) (f ⁻¹' K ∩ Z)
      ((μHE[n] : Measure (Eucl P)).restrict M) := by
    rw [IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
    exact (hR.integrableOn _ hK fun x hx => hZU hx.2).const_mul _
  refine ⟨(f ⁻¹' K ∩ Z).indicator fun x => C ^ n * θ x, hθK.integrable_indicator hKm, ?_⟩
  -- (5) For a.e. `x` with `f x ∈ K`: `x ∈ M ∩ K'`, so `‖L x‖ ≤ C`, `0 < θ x` and `‖ξ x‖ ≤ 1`.
  filter_upwards [hξ, hM, hZ] with x hξx hxM hxZ hfx
  have hxK : x ∈ f ⁻¹' K ∩ Z := ⟨hfx, hxZ⟩
  have hLC : ‖L x‖ ≤ C := hC x ⟨hxM, hxK⟩
  have hθx : 0 < θ x := hR.pos x hxM
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hLC
  rw [indicator_of_mem hxK]
  calc ‖θ x • nVectorPushforward n (L x) (ξ x)‖
      = ‖θ x‖ * ‖nVectorPushforward n (L x) (ξ x)‖ :=
        (NormedSpace.toNormSMulClass).norm_smul (θ x) (nVectorPushforward n (L x) (ξ x))
    _ = θ x * ‖nVectorPushforward n (L x) (ξ x)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos hθx]
    _ ≤ θ x * (‖L x‖ ^ n * ‖ξ x‖) := by
        gcongr
        exact hpush _ _
    _ ≤ θ x * (C ^ n * 1) := by gcongr
    _ = C ^ n * θ x := by ring

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
